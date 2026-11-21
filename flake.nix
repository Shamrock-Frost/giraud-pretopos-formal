{
  description = "giraud-pretopos-formal: NBG set theory in Isabelle/HOL, and the diagram localization theorem";

  # A pinned nixpkgs revision, so that the Isabelle version is fixed.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/55bfb4d7437bd4e09ab7cba58a43bd68eb310044";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      packages.${system} = {
        isabelle = pkgs.isabelle;
        default = pkgs.isabelle;
      };

      devShells.${system}.default = pkgs.mkShell {
        packages = [ pkgs.isabelle pkgs.git ];
        shellHook = ''
          echo "giraud-pretopos-formal: Isabelle ${pkgs.isabelle.version}."
          echo "  check everything: isabelle build -D .    editor: isabelle jedit -d . NBG/Axioms.thy"
        '';
      };
    };
}
