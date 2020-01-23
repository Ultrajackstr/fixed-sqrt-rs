with import <nixpkgs> {};
mkShell {
  buildInputs = [
    gnuplot
    llvm
    rustup
  ];
}
