{
  inputs = {
    flk.url = "github:numtide/flake-utils";
    qik.url = "github:indypaige/qik";
  };

  outputs        = { flk, qik, ... }:
    flk.lib.eachDefaultSystem (system: {
      packages.default = qik.lib.${system}.haskell.mk {
        tool = pkgs: [ pkgs.llvm_21 pkgs.gdb pkgs.clang ];
        name = "language.indypaige.gay";
        root = ./.;
      };
    });
}
