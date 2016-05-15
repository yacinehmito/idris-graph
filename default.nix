let
  dir = "/home/gpyh/idris/graph";
in

with import <yarnpkgs>;
stdenv.mkDerivation {
  name = "idris-graph";
  buildInputs = [
    haskellPackages.idris
    gmp
  ];
  shellHook = ''
    export PATH=$PATH:${dir}
  '';
}
