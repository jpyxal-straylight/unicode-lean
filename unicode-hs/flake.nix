{
  description = "unicode-hs — Haskell port of unicode-lean (UCD 17.0.0 codecs and validators)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # GHC 9.12 across the stack — see project memory + lemma/cabal.project.
        # Pinning explicitly keeps unicode-hs in lockstep with lemma's
        # Haskell toolchain even as nixpkgs' default haskellPackages drifts.
        hsPkgs = pkgs.haskell.packages.ghc912;

        unicode-hs = hsPkgs.callCabal2nix "unicode-hs" ./. {};

        # Force the test suite to run during `nix build`. callCabal2nix
        # defaults vary across nixpkgs revisions; this keeps the
        # conformance test exe on the critical path of every build.
        unicode-hs-checked = pkgs.haskell.lib.doCheck unicode-hs;
      in {
        # ── nix build ──────────────────────────────────────────────
        # Compile the library, then run the test suite.
        packages.default = unicode-hs-checked;
        packages.unicode-hs = unicode-hs-checked;

        # ── nix flake check ────────────────────────────────────────
        # Build + conformance test exe + UCD hash manifest.
        checks.build = unicode-hs-checked;
        checks.ucd-hashes = pkgs.runCommand "unicode-hs-ucd-hashes" {
          src = ./.;
          buildInputs = [ pkgs.bash pkgs.coreutils ];
        } ''
          cp -r $src/* .
          chmod +x scripts/check-ucd-hashes.sh
          bash scripts/check-ucd-hashes.sh
          mkdir -p $out
          touch $out/result
        '';

        # ── nix run ────────────────────────────────────────────────
        # Status report: file count, module count, test-exe count.
        apps.default = {
          type = "app";
          program = toString (pkgs.writeShellScript "unicode-hs-status" ''
            set -euo pipefail
            cd $PWD
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "                // unicode-hs // status //"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo ""

            FILES=$(find src/ test/ -name '*.hs' 2>/dev/null | wc -l)
            MODULES=$(find src/ -name '*.hs' 2>/dev/null | wc -l)
            TEST_EXES=$(find test/ -name '*.hs' 2>/dev/null | wc -l)
            UCD_VERSION=$(grep '^UCD=' data/UCD-VERSION 2>/dev/null | cut -d= -f2 || echo "unknown")
            UCA_VERSION=$(grep '^UCA=' data/UCD-VERSION 2>/dev/null | cut -d= -f2 || echo "unknown")

            echo "  files:        $FILES"
            echo "  modules:      $MODULES"
            echo "  test exes:    $TEST_EXES"
            echo "  UCD:          $UCD_VERSION"
            echo "  UCA:          $UCA_VERSION"
            echo "  GHC target:   9.12.*"
            echo ""

            echo "── phase status ─────────────────────────────────"

            if [ -f src/Unicode/Codec/Utf8.hs ]; then
              echo "  Phase 1 // Strict UTF-8 codec:           shipped"
            else
              echo "  Phase 1 // Strict UTF-8 codec:           not started"
            fi

            for atom in Utf16 Utf32 Bom Noncharacters Identifier ValidatedUtf8 OpaqueBlob; do
              if [ -f "src/Unicode/Codec/$atom.hs" ]; then
                printf "  Phase 2 // Codec.%-18s shipped\n" "$atom:"
              else
                printf "  Phase 2 // Codec.%-18s not started\n" "$atom:"
              fi
            done

            if [ -f src/Unicode/Identifier.hs ]; then
              echo "  Phase 3 // UAX #31 default identifier:   shipped"
            else
              echo "  Phase 3 // UAX #31 default identifier:   not started"
            fi

            if [ -d src/Unicode/Precis ]; then
              echo "  Phase 4 // RFC 8264/8265 PRECIS:         shipped"
            else
              echo "  Phase 4 // RFC 8264/8265 PRECIS:         not started"
            fi

            if [ -f src/Unicode/Codec/Printable.hs ]; then
              echo "  Phase 5 // printable-UTF-8 profile:      shipped"
            else
              echo "  Phase 5 // printable-UTF-8 profile:      not started"
            fi

            echo ""
            echo "── headline guarantees ──────────────────────────"
            echo "  RFC 3629 / strict UTF-8 round-trip:"
            echo "    every valid scalar codepoint encode→decode = id"
            echo "    (exhaustive over 0..0x10FFFF minus surrogates)"
            echo ""
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
          '');
        };

        # ── nix develop ────────────────────────────────────────────
        # GHC 9.12 + cabal + HLS + ghcid. Matches the toolchain
        # lemma and the rest of the Haskell side of the stack use.
        devShells.default = hsPkgs.shellFor {
          packages = _: [ unicode-hs ];
          nativeBuildInputs = [
            hsPkgs.cabal-install
            hsPkgs.ghc
            hsPkgs.haskell-language-server
            pkgs.git
          ];
          shellHook = ''
            echo "// unicode-hs // dev // GHC $(ghc --numeric-version) //"
          '';
        };
      }
    );
}
