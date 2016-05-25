with import <yarnpkgs>;
with pkgs.idrisPackages;
build-idris-package {
  name = "graph";
  propagatedBuildInputs = [ prelude base contrib containers ];
}
