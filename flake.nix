{
  description = "bendworld: a Bend 2 project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    bend = {
      url = "github:bendlang/bend";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, bend }:
    let
      each = f: nixpkgs.lib.genAttrs (builtins.attrNames bend.packages) (system:
        f nixpkgs.legacyPackages.${system} bend.packages.${system}.default);
    in {
      devShells = each (pkgs: bend: {
        default = pkgs.mkShell.override { stdenv = pkgs.clangStdenv; } {
          packages = [ bend pkgs.elan ];
          # `bend --verdict` needs this exact Lean; nixpkgs' lean4 is a different version.
          ELAN_TOOLCHAIN = "leanprover/lean4:v4.34.0";
          buildInputs = pkgs.lib.optionals pkgs.stdenv.hostPlatform.isLinux [
            pkgs.libx11
            pkgs.alsa-lib
          ];
        };
      });

      formatter = each (pkgs: _: pkgs.nixfmt);
    };
}
