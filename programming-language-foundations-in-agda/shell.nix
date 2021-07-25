{ pkgs ? import <nixpkgs> {} }:

let 
  emacs = pkgs.emacsMacport;
  fetchedPlfaSrc = pkgs.fetchFromGitHub {
      owner = "plfa";
      repo = "plfa.github.io";
      rev = "10a3203624f2ea937b3892176db5de825d0c46b4";
      sha256 = "17442ncsggq7dmgqj81ljrm7b48s4b79hy9h4ir28a7zg9n6zih3";
  };
  agda  = pkgs.agda.withPackages (p: [
    p.standard-library 
    (p.mkDerivation {
      pname = "plfa"; # Needed - name Agda uses to write to its libraries file` 
      version = "1.0.0"; 
      src = fetchedPlfaSrc; 
      buildInputs = [p.standard-library emacs]; 
      buildPhase =  ''
        touch foo
      ''; 
      installPhase = ''
        mkdir $out
        cp plfa.agda-lib $out
      '';})
    ]);
in
pkgs.mkShell {
  name = "following-plfa";
  src = ./my-following;
  buildInputs = [ emacs agda ];
  shellHook = ''
    agda-mode setup
    # Not sure what this is supposed to do but it doesn't work
    # agda-mode compile
  '';
}