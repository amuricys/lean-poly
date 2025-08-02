{

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    lean4-nix.url = "github:lenianiva/lean4-nix";
    lean4-nix.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, flake-utils, lean4-nix, ... }:

    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        poly-lean = pkgs.lean.buildLeanPackage {
          name = "LeanPoly";
          src = ./.;
        };
        pkgs = import nixpkgs { inherit system overlays; };
      in {
        packages = {
          poly-lean = poly-lean.sharedLib;
        };
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.lean.lean-all
            pkgs.python3
            pkgs.python3Packages.pip
          ];
        };
      });
}
