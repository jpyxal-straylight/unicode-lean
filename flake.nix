{
  description = "Unicode standard — machine-checked specifications in Lean 4 (UCD 17.0.0)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Lean 4.28.0 toolchain pinned via elan; fetched at build time
        # because no Lean 4.28.0 derivation exists in nixpkgs yet.
        leanShell = pkgs.mkShell {
          packages = [
            pkgs.elan
            pkgs.git
          ];
          shellHook = ''
            export ELAN_HOME="$PWD/.elan"
            export PATH="$ELAN_HOME/bin:$PATH"
            elan toolchain install $(cat lean-toolchain) 2>/dev/null || true
            elan default $(cat lean-toolchain) 2>/dev/null || true
          '';
        };
      in {
        # ── nix build ──────────────────────────────────────────────
        # Builds the full Lean library via lake. Self-contained: no
        # Mathlib, no external Lean dependencies. The Lean toolchain
        # is fetched at build time via elan (network access required
        # on first build; cached thereafter).
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "unicode";
          version = "0.1.0";
          src = ./.;

          nativeBuildInputs = [
            pkgs.elan
            pkgs.git
            pkgs.curl
            pkgs.cacert
          ];

          __noChroot = true;

          buildPhase = ''
            export HOME=$TMPDIR
            export ELAN_HOME=$TMPDIR/.elan
            export PATH=$ELAN_HOME/bin:$PATH
            elan toolchain install $(cat lean-toolchain)
            elan default $(cat lean-toolchain)
            lake build
          '';

          installPhase = ''
            mkdir -p $out
            cp -r .lake/build $out/
          '';
        };

        # ── nix flake check ───────────────────────────────────────
        # Two checks: the build itself, plus a sorry / admit scan
        # that fails on any proof gap.
        checks.no-sorry = pkgs.runCommand "unicode-no-sorry" {
          src = ./.;
        } ''
          cp -r $src/* .
          chmod +x scripts/check-sorry.sh
          ./scripts/check-sorry.sh
          mkdir -p $out
          touch $out/result
        '';

        checks.build = self.packages.${system}.default;

        # ── nix run ────────────────────────────────────────────────
        # Status report: file count, theorem count, sorry count,
        # per-pillar progress.
        apps.default = {
          type = "app";
          program = toString (pkgs.writeShellScript "unicode-status" ''
            set -euo pipefail
            cd $PWD
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "                // unicode // status //"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo ""

            FILES=$(find Unicode/ -name '*.lean' | wc -l)
            DEFS=$(grep -rcE '^def |^structure |^inductive ' --include='*.lean' Unicode/ | \
              awk -F: '{s+=$2} END {print s}')
            THEOREMS=$(grep -rcE '^theorem |^lemma ' --include='*.lean' Unicode/ | \
              awk -F: '{s+=$2} END {print s}')
            SORRY=$(grep -rnE '\bsorry([[:space:]]*$|[;,)}])' --include='*.lean' Unicode/ | \
              grep -cv '^[^:]*:[0-9]*:[[:space:]]*--' || true)

            echo "  files:      $FILES"
            echo "  defs:       $DEFS"
            echo "  theorems:   $THEOREMS"
            echo "  sorry:      $SORRY"
            echo ""

            if [ "$SORRY" -gt 0 ]; then
              echo "  !! sorry found:"
              grep -rnE '\bsorry([[:space:]]*$|[;,)}])' --include='*.lean' Unicode/ | \
                grep -v '^[^:]*:[0-9]*:[[:space:]]*--'
              echo ""
            fi

            echo "── pillar status ────────────────────────────────"
            for pillar in Normalization Precis Bidi Generated; do
              if [ -d "Unicode/$pillar" ]; then
                pf=$(find Unicode/$pillar -name '*.lean' | wc -l)
                pt=$(grep -rcE '^theorem |^lemma ' --include='*.lean' Unicode/$pillar/ | \
                  awk -F: '{s+=$2} END {print s}')
                ps=$(grep -rnE '\bsorry([[:space:]]*$|[;,)}])' --include='*.lean' Unicode/$pillar/ | \
                  grep -cv '^[^:]*:[0-9]*:[[:space:]]*--' || true)
                printf "  %-18s %3d files  %4d theorems  %d sorry\n" "$pillar" "$pf" "$pt" "$ps"
              fi
            done

            echo ""
            echo "── headline theorems ────────────────────────────"
            echo "  UAX #15  / NFC quick-check soundness:"
            echo "    Unicode.Normalization.QuickCheckSoundnessTheorem.quickCheck_sound"
            echo "  RFC 8264 / PRECIS preparation idempotence:"
            echo "    Unicode.Precis.Preparation.precis_idempotent"
            echo "  UAX  #9  / Bidirectional Algorithm pipeline:"
            echo "    Unicode.Bidi.Algorithm.bidiParagraph"
            echo "  UTS #39  / Confusable skeleton equivalence:"
            echo "    Unicode.Confusables.areConfusable_trans"
            echo ""
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
          '');
        };

        # ── nix develop ────────────────────────────────────────────
        # Dev shell with elan + lake + git. First entry installs the
        # pinned toolchain via elan.
        devShells.default = leanShell;
      }
    );
}
