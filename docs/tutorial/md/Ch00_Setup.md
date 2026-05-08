
# Chapter 0 — Setup

Welcome to the Sparkle HDL tutorial.  This chapter has one job:
get you to a working build of the course so the rest of the
chapters run.

There are two paths.  Pick whichever fits your environment:

1. **Docker (recommended for first-timers).**  Everything you
   need — Lean, Lake, xeus-lean, JupyterLab, yosys,
   nextpnr-ice40, nextpnr-ecp5, icestorm, prjtrellis — is
   pre-installed in a single image.  No host-side toolchain
   juggling.

   ```bash
   docker run --rm -p 8888:8888 ghcr.io/verilean/sparkle-tutorial:latest
   ```

   Open `http://localhost:8888` and navigate into the course.

2. **Local install.**  If you want to develop offline or
   contribute upstream, install the same toolchain on your host.
   See [`docs/tutorial/README.md`](https://github.com/Verilean/sparkle/blob/main/docs/tutorial/README.md)
   for the full list and `docs/reference/How_To_Use.md` for
   project layout when you start your own Sparkle project.

## A first sanity check

The cell below typechecks under `lake build TutorialNotebooks`
and evaluates trivially under xeus-lean.  If it works, your
toolchain is alive.


```lean
example : 1 + 1 = 2 := rfl

```

## What's next

- **Ch 1 — Lean 4 for HDL Authors**: the slice of Lean syntax
  we'll use for the rest of the course.  No general-purpose
  Lean tutorial, no Functor / Monad theory; just the constructs
  you'll see in real Sparkle code.
- **Ch 1b — Your First Sparkle Project**: how to start a
  stand-alone project that imports Sparkle as a Lake dependency.
  You don't need to be inside the Sparkle repo to write hardware.
- **Ch 2 onward**: combinational circuits, sequential circuits,
  modules, Verilog generation, proofs, Yosys, FPGA bring-up,
  and a tour of Sparkle's compilation pipeline.

