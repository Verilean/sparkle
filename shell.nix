{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "hdl-dev-shell";

  # Packages to install in the environment
  buildInputs = with pkgs; [
    verilator
    iverilog      # Icarus Verilog for quick simulations
    yosys
    pkg-config
    cmake
    elan
    (python3.withPackages (ps: with ps; [numpy matplotlib pyyaml pandas pip jupytext nbconvert jupyterlab]))
    nodejs
    pkgsCross.riscv32-embedded.buildPackages.gcc
    pkgsCross.riscv32-embedded.buildPackages.binutils
    # Linux kernel cross-toolchain (glibc target). Needed to build the
    # in-tree sparkle-bitnet driver and the rv32 Linux kernel image.
    pkgsCross.riscv64.buildPackages.gcc
    pkgsCross.riscv64.buildPackages.binutils
    # Device-tree compiler — turns sparkle-soc.dts into the .dtb that
    # OpenSBI hands to Linux at boot.
    dtc
    # Kernel build prerequisites
    bc flex bison openssl
    cpio gzip
    nlohmann_json
    libuuid
    zstd.dev
  ];

  # Environment variables
  shellHook = ''
    echo "--- HDL Development Environment ---"
    echo "Verilator version: $(verilator --version)"
    echo "Scala version:     $(scala -version 2>&1 | head -n 1)"
    echo "-----------------------------------"
    
    # Set VERILATOR_ROOT if your build system needs it
    export VERILATOR_ROOT=${pkgs.verilator}/share/verilator
  '';
}
