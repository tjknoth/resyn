let
  pkgs = import <nixpkgs> {};
in
pkgs.mkShell {
  buildInputs = with pkgs; [
    stack cvc4 pkgconfig
  ];
}
