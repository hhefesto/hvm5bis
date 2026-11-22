{
  description = "hvm5bis: HVM4 (HigherOrderCO) ported to Bend 2";

  inputs = {
    # the pinned Bend (2.0.39, with BendTT for --verdict), as bend-json's
    bend-frp.url = "github:hhefesto/bend-frp";
    nixpkgs.follows = "bend-frp/nixpkgs";
    # HVM4 at the commit hvm5bis ports: its runtime (the reference) and its
    # tests; fetched here, not copied into this repository
    hvm4 = {
      url = "github:HigherOrderCO/HVM4/6defdfc7dae2a3cca5dd6e74ed0612385b5646a8";
      flake = false;
    };
  };

  outputs =
    { self, nixpkgs, bend-frp, hvm4 }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      lib = pkgs.lib;
      bend = bend-frp.packages.${system}.bend;
      src = lib.fileset.toSource {
        root = ./.;
        fileset = lib.fileset.unions [ ./src ./tools/Gate.bend ];
      };
      # a Bend program compiled to a native binary (C via clang)
      bendBinary =
        name: entry:
        pkgs.runCommand name { nativeBuildInputs = [ bend ]; } ''
          export HOME=$TMPDIR BEND_NO_TELEMETRY=1
          cp -r ${src} w
          chmod -R u+w w
          mkdir -p $out/bin
          bend w/${entry} -o $out/bin/${name}
        '';
    in
    {
      packages.${system} = {
        # hvm5bis FILE.hvm [-s] [-S] [-C[N]]
        default = bendBinary "hvm5bis" "src/Main.bend";
        # gate HVM HVM5BIS TIMEOUT_MS TEST.hvm...
        gate = bendBinary "gate" "tools/Gate.bend";
        # upstream HVM4, built as its README says
        hvm4 = pkgs.runCommandCC "hvm4" { } ''
          mkdir -p $out/bin
          $CC -O2 -o $out/bin/hvm ${hvm4}/src/hvm.c
        '';
      };

      checks.${system} = {
        # every module type-checks (bend's checker; not a --verdict proof)
        modules = pkgs.runCommand "hvm5bis-modules" { nativeBuildInputs = [ bend ]; } ''
          export HOME=$TMPDIR BEND_NO_TELEMETRY=1
          cp -r ${src} w
          chmod -R u+w w
          for m in w/src/*.bend w/tools/Gate.bend; do
            echo "== $m"
            bend $m --check-only 2>&1 | tee m.log
            grep -qx 'ALL PROOFS CHECK' m.log
          done
          touch $out
        '';
        # HVM4's tests (devs/test, _all_.sh's rules) through upstream HVM4 and
        # hvm5bis: hvm5bis must pass every test upstream passes, with the
        # same output
        gate = pkgs.runCommand "hvm5bis-gate" { } ''
          export HOME=$TMPDIR
          cd ${hvm4}/devs/test
          ${self.packages.${system}.gate}/bin/gate \
            ${self.packages.${system}.hvm4}/bin/hvm \
            ${self.packages.${system}.default}/bin/hvm5bis \
            60000 $(ls *.hvm | grep -v '^_') | tee $TMPDIR/gate.log
          up=$(sed -n 's/^upstream HVM4: \([0-9]*\)\/.*/\1/p' $TMPDIR/gate.log)
          me=$(sed -n 's/^hvm5bis: *\([0-9]*\)\/.*/\1/p' $TMPDIR/gate.log)
          echo "upstream $up, hvm5bis $me"
          ! grep -q '^\[PASS FAIL' $TMPDIR/gate.log
          ! grep -q '^\[PASS PASS DIFF' $TMPDIR/gate.log
          [ "$up" = "$me" ]
          cp $TMPDIR/gate.log $out
        '';
      };
    };
}
