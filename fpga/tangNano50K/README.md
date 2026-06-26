# Tang Nano 50K — USB Web server demo

Brings up a Sparkle-generated HTTP/1.0 server on a Tang Nano
50K, reachable over the board's USB-C port (no Ethernet
hardware needed).  The path is

    PC  ──USB-C──  BL616 (CDC-ACM bridge)  ──UART──  FPGA
                          (Sparkle: SLIP → IPv4 → TCP → HTTP)

so on the host the FPGA appears as `/dev/ttyACM*` (Linux) or
`/dev/cu.usbmodem*` (macOS).  A SLIP wrapper turns that serial
port into a virtual network interface, and the FPGA responds to
`http://192.168.7.2/` with `Hello, Sparkle!`.

## 1. Generate Verilog

From the repo root:

    lake build Tests.IP.Net.UsbWebServerSynth

That elaborates `Sparkle.IP.Net.UsbWebServer.usbWebServer` and
prints the full Verilog module on stdout (look for
`-- Verilog successfully generated!`).  Capture it:

    lake build Tests.IP.Net.UsbWebServerSynth 2>&1 \
      | sed -n '/^module /,/^endmodule/p' \
      > fpga/tangNano50K/build/usb_webserver.v

(The exact `module` header name is the long
`_private_Tests_IP_Net_UsbWebServerSynth_0_…` mangle that
Lean's `#synthesizeVerilog` emits.  Rename it with `sed` or
wrap it in a Verilog shim — see `usb_webserver_top.v` below.)

## 2. Wrap with PLL + constant tie-off

Sparkle's emitted module has port names `clk`, `rst`,
`uart_rx_line`, `bit_div`, `out` (= UART TX).  We want a
top-level that:

* drives `clk` from a 100 MHz PLL clocked off the 27 MHz crystal;
* hardcodes `bit_div = 99` (= 100 MHz / 1 Mbps);
* renames `out` to `uart_tx` to match the `.cst` file.

Create `fpga/tangNano50K/build/usb_webserver_top.v`:

```verilog
module usb_webserver_top(
    input  clk_27,          // 27 MHz crystal
    input  rst,             // active-low push button
    input  uart_rx_line,    // FPGA RX (from BL616 TX)
    output uart_tx          // FPGA TX (to BL616 RX)
);
    wire clk_100, pll_locked;
    rPLL #(.FCLKIN("27"),
           .DEVICE("GW5AT-LV60PG484C"),
           .FBDIV_SEL(99),
           .IDIV_SEL(26),
           .ODIV_SEL(4))
      u_pll(.CLKIN(clk_27),
            .CLKOUT(clk_100),
            .LOCK(pll_locked),
            .CLKFB(1'b0),
            .RESET(~rst),
            .RESET_P(1'b0));

    // Sparkle-generated module; replace the long mangled name
    // with the actual one emitted by #synthesizeVerilog.
    synth_usbWebServer u_core(
        .clk(clk_100),
        .rst(~rst),                      // synchronous, active-high
        .uart_rx_line(uart_rx_line),
        .bit_div(16'd99),
        .out(uart_tx)
    );
endmodule
```

## 3. Build with Gowin EDA

1. Open Gowin EDA → File → New → FPGA Design Project.
2. Device: **GW5AT-LV60PG484C** (Tang Nano 50K).
3. Add files:
    - `usb_webserver.v` (Sparkle-generated)
    - `usb_webserver_top.v` (wrapper above)
    - `usb_webserver.cst` (pin constraints, this directory)
4. Synthesize → Place & Route.  At ~5–10 kLUTs / ~70 DFFs the
   design fits with massive headroom (GW5AT-LV60 has 60 kLUTs).
5. Program SRAM via USB-C (Gowin EDA detects the BL616 bridge
   automatically and uses it as the JTAG transport too).

After programming, the FPGA starts running.  The board's
USB-C port is now exposed as a serial device.

## 4. Bring up SLIP on the host

### macOS

```bash
# Find the device
ls /dev/cu.usbmodem*           # e.g. /dev/cu.usbmodem14101

# Try pppd in SLIP mode
sudo pppd /dev/cu.usbmodem14101 1000000 \
    192.168.7.1:192.168.7.2 \
    noauth nodetach passive local \
    nocrtscts proto slip
```

If `pppd`'s SLIP module is missing on your macOS build, fall
back to a userland serial↔TUN bridge — see
`scripts/usb_slip_bridge.py` (a 100-line Python helper, TBD).

### Linux

```bash
# Find the device
ls /dev/ttyACM*                # e.g. /dev/ttyACM0

# Attach SLIP and bring up the interface
sudo slattach -L -p slip -s 1000000 /dev/ttyACM0 &
sudo ip addr add 192.168.7.1/24 dev sl0
sudo ip link set sl0 up
```

## 5. Test it

```bash
curl http://192.168.7.2/
# → HTTP/1.0 200 OK
#   <blank line>
#   Hello, Sparkle!
```

## Notes / known gaps

* The TCP "state" is intentionally minimal: the FPGA emits a
  response on any frame whose payload starts with `"GET "`.
  Real HTTP/1.x compliance (Host: header, status line, multi-
  request keep-alive) is future work; the current design is a
  proof-of-life that the full UART/SLIP/IPv4/TCP/HTTP pipeline
  composes correctly end-to-end.
* IP checksum is not computed at TX time — the host accepts it
  because Linux's SLIP / pppd doesn't enforce IP-layer
  checksums on RX (TCP doesn't either when both sides are on
  the same SLIP link).  Adding a real TX-side checksum is a
  small Sparkle module hook-in and is left as a follow-up.
* The Lean sim (`lake exe usb-webserver-sim`) verifies the full
  request decode and response framing without any of the host
  setup above.  Reach for it first if anything mysteries on the
  hardware.
