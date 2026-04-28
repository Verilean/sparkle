/* SPDX-License-Identifier: GPL-2.0 */
/*
 * UAPI for the Sparkle BitNet v1a MMIO peripheral.
 *
 * The Level 1a peripheral is a 1-word-in / 1-word-out combinational
 * accelerator (see IP/RV32/BitNetPeripheral.lean in the Sparkle repo).
 * Each "inference" pushes a single Q16.16 activation into the input
 * latch and reads back the corresponding Q16.16 output.
 *
 * Userspace patterns:
 *
 *   write(fd, &u32, 4);   // store input latch  (0x40000004)
 *   read (fd, &u32, 4);   // load output       (0x40000008)
 *
 *   ioctl(fd, BITNET_IOC_INFER, &val);   // atomic write+read pair
 *
 * For multi-token inference loops, repeat the pair. v1a has no DMA,
 * no IRQ, and no internal state — every inference is independent.
 */

#ifndef _UAPI_LINUX_SPARKLE_BITNET_H
#define _UAPI_LINUX_SPARKLE_BITNET_H

#include <linux/ioctl.h>
#include <linux/types.h>

#define BITNET_IOC_MAGIC  'b'

/* Atomic write-input-then-read-output under the per-device mutex.
 * The kernel writes *arg into the input latch, then reads the output
 * register back into *arg. */
#define BITNET_IOC_INFER  _IOWR(BITNET_IOC_MAGIC, 1, __u32)

#endif /* _UAPI_LINUX_SPARKLE_BITNET_H */
