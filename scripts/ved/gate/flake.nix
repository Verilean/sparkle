{
  # Pinned tools for the VED release-gate measurement (circuit size).
  # Used only through `kjob dev` from this directory; not part of the Lean build.
  description = "VED release gate: pinned yosys";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/7c8764b7c7b09b34f632464276218ef9090eaa11";
  outputs = { self, nixpkgs }:
    let pkgs = nixpkgs.legacyPackages.x86_64-linux; in {
      devShells.x86_64-linux.default = pkgs.mkShell {
        packages = [ pkgs.yosys pkgs.python3 ];
      };
    };
}
