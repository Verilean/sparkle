// SPDX-License-Identifier: GPL-2.0
/*
 * Sparkle BitNet v1a — Linux character-device driver.
 *
 * Exposes the combinational BitNet MMIO peripheral that lives at
 * 0x40000000 on the Sparkle RV32IMA SoC (see IP/RV32/BitNetPeripheral.lean
 * and IP/RV32/SoC.lean). The hardware is intentionally minimal:
 *
 *     0x00  R/W  status   — always 0 in v1a, reserved for future bits
 *     0x04  W    input    — Q16.16 activation; latched on write
 *     0x08  R    output   — combinational result of current input
 *
 * "Inference" of one token = write input, read output. The peripheral
 * has no internal state, no IRQ line, and no DMA buffer; every token
 * is independent. Multi-token loops are driven entirely from userspace.
 *
 * The driver mirrors firmware/bitnet_smoke/main.c at the syscall layer
 * so the same golden vectors validate both the bare-metal and Linux
 * paths.
 */

#include <linux/fs.h>
#include <linux/io.h>
#include <linux/miscdevice.h>
#include <linux/module.h>
#include <linux/mutex.h>
#include <linux/of.h>
#include <linux/platform_device.h>
#include <linux/slab.h>
#include <linux/uaccess.h>

#include <uapi/linux/sparkle-bitnet.h>

#define BITNET_REG_STATUS  0x00
#define BITNET_REG_INPUT   0x04
#define BITNET_REG_OUTPUT  0x08

struct bitnet_dev {
	void __iomem      *base;
	struct miscdevice  misc;
	struct mutex       lock;
};

static struct bitnet_dev *bitnet_from_file(struct file *f)
{
	struct miscdevice *m = f->private_data;
	return container_of(m, struct bitnet_dev, misc);
}

static ssize_t bitnet_read(struct file *f, char __user *buf,
			   size_t count, loff_t *ppos)
{
	struct bitnet_dev *bn = bitnet_from_file(f);
	u32 v;

	if (count < sizeof(v))
		return -EINVAL;

	v = ioread32(bn->base + BITNET_REG_OUTPUT);
	if (copy_to_user(buf, &v, sizeof(v)))
		return -EFAULT;

	return sizeof(v);
}

static ssize_t bitnet_write(struct file *f, const char __user *buf,
			    size_t count, loff_t *ppos)
{
	struct bitnet_dev *bn = bitnet_from_file(f);
	u32 v;

	if (count < sizeof(v))
		return -EINVAL;
	if (copy_from_user(&v, buf, sizeof(v)))
		return -EFAULT;

	iowrite32(v, bn->base + BITNET_REG_INPUT);
	return sizeof(v);
}

static long bitnet_ioctl(struct file *f, unsigned int cmd,
			 unsigned long arg)
{
	struct bitnet_dev *bn = bitnet_from_file(f);
	void __user *uarg = (void __user *)arg;
	u32 v;

	switch (cmd) {
	case BITNET_IOC_INFER:
		if (copy_from_user(&v, uarg, sizeof(v)))
			return -EFAULT;
		mutex_lock(&bn->lock);
		iowrite32(v, bn->base + BITNET_REG_INPUT);
		v = ioread32(bn->base + BITNET_REG_OUTPUT);
		mutex_unlock(&bn->lock);
		if (copy_to_user(uarg, &v, sizeof(v)))
			return -EFAULT;
		return 0;
	default:
		return -ENOTTY;
	}
}

static const struct file_operations bitnet_fops = {
	.owner          = THIS_MODULE,
	.read           = bitnet_read,
	.write          = bitnet_write,
	.unlocked_ioctl = bitnet_ioctl,
	.compat_ioctl   = bitnet_ioctl,
	.llseek         = no_llseek,
};

static ssize_t status_show(struct device *dev,
			   struct device_attribute *attr, char *buf)
{
	struct bitnet_dev *bn = dev_get_drvdata(dev);
	u32 v = ioread32(bn->base + BITNET_REG_STATUS);

	return sysfs_emit(buf, "0x%08x\n", v);
}
static DEVICE_ATTR_RO(status);

static struct attribute *bitnet_attrs[] = {
	&dev_attr_status.attr,
	NULL,
};
ATTRIBUTE_GROUPS(bitnet);

/*
 * Probe-time self test: drive the 8 golden Q16.16 vectors through the
 * peripheral and emit the in/out tokens directly to the Sparkle UART
 * (raw MMIO at 0x10000000). This bypasses printk / console_init so the
 * results are visible even on minimal Linux configs that never reach
 * userspace. The vectors mirror Tests/Integration/BitNetSoCTest.lean
 * lines 43-51 — bit-equality with the Lean spec is the pass criterion.
 *
 * Output format on UART:
 *
 *     BITNET v1a SELFTEST
 *     in=<8hex> out=<8hex> want=<8hex> [PASS|FAIL]
 *     ...
 *     BITNET PASS  (or  BITNET FAIL)
 *
 * Direct UART writes use a kernel-mapped pointer obtained at probe time
 * via ioremap; the Sparkle SoC's ns16550a-compatible TX register is at
 * offset 0 of the same MMIO range we already requested for serial.
 * That mapping is owned by the 8250 driver, so we cannot ioremap the
 * same physical range twice. Instead we rely on the fact that the
 * Linux kernel's identity-mapped region already exposes UART to S-mode
 * via __va arithmetic on the platform's PA window — the Sparkle SoC
 * happens to alias 0x10000000 into the kernel virtual address `(void
 * __iomem *)__va(0x10000000)`. We compute that pointer manually and
 * write 32-bit words to it.
 *
 * If the kernel's mapping doesn't cover 0x10000000 (because no
 * peripherals_paddr-style region was registered), the writes silently
 * page-fault and the self test is invisible — the driver still
 * registers normally for /dev/bitnet0 access from userspace.
 */
static const u32 bitnet_golden[][2] = {
	{0x00010000u, 0x00410000u}, /* 1.0 → 65 (Q16.16) */
	{0x00020000u, 0x02020000u},
	{0x00030000u, 0x06C30000u},
	{0x00040000u, 0x10040000u},
	{0x00080000u, 0x80080000u},
	{0x00000100u, 0x00000100u},
	{0x12345678u, 0x5AD1BC9Au},
	{0x00000000u, 0x00000000u},
};

static void bitnet_uart_putc(char c)
{
	/* Sparkle SoC UART TX register at PA 0x10000000.  Use phys_to_virt
	 * because the platform sets up an identity-style linear map for
	 * the low MMIO region and we cannot ioremap a slot the 8250
	 * driver already owns. */
	volatile u32 *uart = (volatile u32 *)phys_to_virt(0x10000000);

	*uart = (u32)(unsigned char)c;
}

static void bitnet_uart_puts(const char *s)
{
	while (*s)
		bitnet_uart_putc(*s++);
}

static void bitnet_uart_puthex32(u32 v)
{
	static const char d[] = "0123456789abcdef";
	int i;

	for (i = 7; i >= 0; i--)
		bitnet_uart_putc(d[(v >> (i * 4)) & 0xF]);
}

static void bitnet_run_selftest(struct bitnet_dev *bn)
{
	bool all_pass = true;
	size_t i;

	bitnet_uart_puts("\nBITNET v1a SELFTEST\n");

	for (i = 0; i < ARRAY_SIZE(bitnet_golden); i++) {
		u32 in   = bitnet_golden[i][0];
		u32 want = bitnet_golden[i][1];
		u32 got;

		mutex_lock(&bn->lock);
		iowrite32(in, bn->base + BITNET_REG_INPUT);
		got = ioread32(bn->base + BITNET_REG_OUTPUT);
		mutex_unlock(&bn->lock);

		bitnet_uart_puts("  in=0x");
		bitnet_uart_puthex32(in);
		bitnet_uart_puts(" out=0x");
		bitnet_uart_puthex32(got);
		bitnet_uart_puts(" want=0x");
		bitnet_uart_puthex32(want);
		bitnet_uart_puts(got == want ? " PASS\n" : " FAIL\n");

		if (got != want)
			all_pass = false;
	}

	bitnet_uart_puts(all_pass ? "BITNET PASS\n" : "BITNET FAIL\n");
}

static int bitnet_probe(struct platform_device *pdev)
{
	struct device *dev = &pdev->dev;
	struct bitnet_dev *bn;
	int ret;

	bn = devm_kzalloc(dev, sizeof(*bn), GFP_KERNEL);
	if (!bn)
		return -ENOMEM;

	bn->base = devm_platform_ioremap_resource(pdev, 0);
	if (IS_ERR(bn->base))
		return PTR_ERR(bn->base);

	mutex_init(&bn->lock);

	bn->misc.minor  = MISC_DYNAMIC_MINOR;
	bn->misc.name   = "bitnet0";
	bn->misc.fops   = &bitnet_fops;
	bn->misc.parent = dev;
	bn->misc.groups = bitnet_groups;

	ret = misc_register(&bn->misc);
	if (ret)
		return ret;

	platform_set_drvdata(pdev, bn);
	dev_set_drvdata(bn->misc.this_device, bn);

	dev_info(dev, "registered as /dev/%s (regs @ %pR)\n",
		 bn->misc.name, &pdev->resource[0]);

	/* Probe-time self test against 8 golden vectors. The output goes
	 * to UART via raw MMIO; on minimal Linux configs that never reach
	 * userspace this is the only way to see the BitNet token stream. */
	bitnet_run_selftest(bn);

	return 0;
}

static int bitnet_remove(struct platform_device *pdev)
{
	struct bitnet_dev *bn = platform_get_drvdata(pdev);

	misc_deregister(&bn->misc);
	return 0;
}

static const struct of_device_id bitnet_of_match[] = {
	{ .compatible = "sparkle,bitnet-v1a" },
	{},
};
MODULE_DEVICE_TABLE(of, bitnet_of_match);

static struct platform_driver bitnet_driver = {
	.driver = {
		.name           = "sparkle-bitnet",
		.of_match_table = bitnet_of_match,
	},
	.probe  = bitnet_probe,
	.remove = bitnet_remove,
};
module_platform_driver(bitnet_driver);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Sparkle HDL");
MODULE_DESCRIPTION("Sparkle BitNet v1a MMIO accelerator");
