{ stdenv, lib, gmp, idris2-version }:
stdenv.mkDerivation rec {
  pname = "libidris2_suport";
  version = idris2-version;

  src = ../.;

  strictDeps = true;
  buildInputs = [ gmp ];

  makeFlags = [
    "PREFIX=$(out)"
  ] ++ lib.optional stdenv.isDarwin "OS=";

  buildPhase = ''
    make support
  '';

  installTargets = "install-support";

  postInstall = ''
    mv $out/idris2-${version}/lib $out/lib
    mv $out/idris2-${version}/support $out/share
    rmdir $out/idris2-${version}
  '';
}
