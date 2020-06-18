let
  pkgs = import <nixpkgs> {};
in
pkgs.mkShell {
  buildInputs = with pkgs; [
    stack pkgconfig python38Packages.colorama
  ];
}
