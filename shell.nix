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
    (python311.withPackages (ps: with ps; [numpy matplotlib pyyaml pandas pip]))
    nodejs
    pkgsCross.riscv32-embedded.buildPackages.gcc
    pkgsCross.riscv32-embedded.buildPackages.binutils
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
