{
  description = "";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        packageName = "algorithm-design-with-haskell";
        haskellPackages = pkgs.haskellPackages;
        cabalPackages = haskellPackages.callCabal2nix packageName
          "./algorithm-design-with-haskell.cabal" { };

      in {
        packages.${packageName} = cabalPackages;

        defaultPackage = self.packages.${system}.${packageName};

        devShells.default = pkgs.mkShell {
          buildInputs = [
            # For Haskell
            haskellPackages.haskell-language-server
            haskellPackages.ghcid
            haskellPackages.cabal-install
          ];
        };
      });
}
