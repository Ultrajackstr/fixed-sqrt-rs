with import <nixpkgs> {};
mkShell {
  buildInputs = [
    llvm
    rustup
  ];
}
