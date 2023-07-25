{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell rec {
  packages = with pkgs; [
    dune_3
    ocamlPackages.ocaml-lsp
    ocamlPackages.base
    ocamlPackages.ppx_inline_test
    ocamlPackages.ppx_deriving
    ocamlPackages.findlib
    ocamlPackages.menhir
  ];
}
