{ stdenv, lib, callPackage, chez, clang, gmp, fetchFromGitHub, makeWrapper, idris2-version
, srcRev, gambit, nodejs, zsh, idris2Bootstrap ? null }:

let support = callPackage ./support.nix { inherit idris2-version; };
in
# Uses scheme to bootstrap the build of idris2
stdenv.mkDerivation rec {
  pname = "idris2";
  version = idris2-version;

  src = ../.;

  strictDeps = true;
  nativeBuildInputs = [ makeWrapper clang chez ]
    ++ lib.optional stdenv.isDarwin [ zsh ]
    ++ lib.optional (!(idris2Bootstrap == null)) [ idris2Bootstrap ];
  buildInputs = [ chez gmp support ];

  prePatch = ''
    patchShebangs --build tests
    sed 's/$(GIT_SHA1)/${srcRev}/' -i Makefile
  '';

  makeFlags = [ "PREFIX=$(out)" ] ++ lib.optional stdenv.isDarwin "OS=";

  # The name of the main executable of pkgs.chez is `scheme`
  buildFlags =
    if idris2Bootstrap == null then [ "bootstrap" "SCHEME=scheme" ] else [ ];

  checkInputs = [ gambit nodejs ]; # racket ];
  checkFlags = [ "INTERACTIVE=" ];

  # skip over install-support because we've already
  # installed support as its own derivation so we
  # just need to copy some files from it in postInstall
  installTargets = ''
    install-idris2
    install-libs
  '';

  # TODO: Move this into its own derivation, such that this can be changed
  #       without having to recompile idris2 every time.
  postInstall = let
    name = "${pname}-${version}";
    globalLibraries = [
      "\\$HOME/.nix-profile/lib/${name}"
      "/run/current-system/sw/lib/${name}"
      "$out/${name}"
    ];
    globalLibrariesPath = builtins.concatStringsSep ":" globalLibraries;
  in ''
    # Remove existing idris2 wrapper that sets incorrect LD_LIBRARY_PATH
    rm $out/bin/idris2

    # The only thing we need from idris2_app is the actual binary
    mv $out/bin/idris2_app/idris2.so $out/bin/idris2
    rm $out/bin/idris2_app/*
    rmdir $out/bin/idris2_app

    # We need to snag some support files from the support
    # derivation
    cp -r ${support}/support $out/${name}/support

    # idris2 needs to find scheme at runtime to compile
    # idris2 installs packages with --install into the path given by
    #   IDRIS2_PREFIX. We set that to a default of ~/.idris2, to mirror the
    #   behaviour of the standard Makefile install.
    wrapProgram "$out/bin/idris2" \
      --set-default CHEZ "${chez}/bin/scheme" \
      --run 'export IDRIS2_PREFIX=''${IDRIS2_PREFIX-"$HOME/.idris2"}' \
      --suffix IDRIS2_LIBS ':' "$out/${name}/lib" \
      --suffix IDRIS2_DATA ':' "$out/${name}/support" \
      --suffix IDRIS2_PACKAGE_PATH ':' "${globalLibrariesPath}"
  '';
}
