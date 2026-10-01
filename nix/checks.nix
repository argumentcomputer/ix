{
  pkgs,
  system,
  auditSrc,
  blake3-lean,
  mkCheck,
}: let
  nativeArgs =
    pkgs.lib.optionalString (system == "x86_64-linux")
    "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/x86/native_harness.c";
  nativeInputs = pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
  # The pipeline suites link their objects with fixtures/x86/runtime_driver.c
  # (or backend_driver.c) and run them natively with `--cc`; elsewhere they
  # run every Lean level and say that the native runs are skipped.
  native = system == "x86_64-linux";
  ccArg = pkgs.lib.optionalString native "--cc ${pkgs.stdenv.cc}/bin/cc";
in
  {
    # The catalog reader rejects symlinked files, so the fixture commands read
    # the store copy of the source tree rather than the symlinked work tree.
    ixon-v3 = mkCheck "ixon-v3" [] ''
      ./.lake/build/bin/tests-ixon-v3
      ./.lake/build/bin/check-ixon-v3 ${auditSrc}/fixtures/ixon-v3/handoff/accepted.ixe \
        ${auditSrc}/fixtures/ixon-v3/handoff/profile.bin \
        ${auditSrc}/fixtures/ixon-v3/handoff/accepted.claim
      ./.lake/build/bin/check-ixon-v3-catalog ${auditSrc}/fixtures/ixon-v3/catalog/fat.ixc
      ./.lake/build/bin/check-ixon-v3-catalog ${auditSrc}/fixtures/ixon-v3/catalog/chunked.ixc \
        ${auditSrc}/fixtures/ixon-v3/catalog/chunked.ixc/members.json
    '';

    # The admission census must reproduce its reviewed baseline exactly, so
    # per-constant verdicts and budget headroom change only with review.
    census = mkCheck "census" [pkgs.diffutils] ''
      ./.lake/build/bin/census ${auditSrc}/fixtures/ixon-v3/k1/k1.ixe \
        --names ${auditSrc}/fixtures/ixon-v3/k1/equations.json --out census.json
      diff -u ${auditSrc}/fixtures/ixon-v3/k1/census.json census.json
      for name in fib sum-loop ackermann tak gcd; do
        ./.lake/build/bin/census ${auditSrc}/fixtures/ixon-v3/bench-k1/$name.ixe \
          --names ${auditSrc}/fixtures/ixon-v3/bench-k1/$name.equations.json --out $name.census.json
        diff -u ${auditSrc}/fixtures/ixon-v3/bench-k1/$name.census.json $name.census.json
      done
    '';

    aiur = mkCheck "aiur" [] ''
      ./.lake/build/bin/tests-aiur
      ./.lake/build/bin/check-aiur --root ${auditSrc}
    '';

    x86-encoder-decoder = mkCheck "x86-encoder-decoder" [pkgs.binutils] ''
      ./.lake/build/bin/check-x86-encoder --objdump ${pkgs.binutils}/bin/objdump
    '';

    x86-byte-execution = mkCheck "x86-byte-execution" [] ''
      ./.lake/build/bin/check-x86-bytes
    '';

    x86-stream-objects = mkCheck "x86-stream-objects" [] ''
      ./.lake/build/bin/check-x86-streams
    '';

    x86-elf-object = mkCheck "x86-elf-object" ([pkgs.binutils] ++ nativeInputs) ''
      ./.lake/build/bin/check-x86-object \
        --fixture ./.lake/build/bin/x86-object-fixture \
        --readelf ${pkgs.binutils}/bin/readelf \
        --objdump ${pkgs.binutils}/bin/objdump ${nativeArgs}
    '';

    trusted-extern-ledger = mkCheck "trusted-extern-ledger" [] ''
      ./.lake/build/bin/check-trusted-externs \
        --root ${auditSrc} \
        --dependency-root Blake3=${blake3-lean.outPath} \
        --gmp-version ${pkgs.gmp.version}
      ./.lake/build/bin/check-tools-tests \
        --root ${auditSrc} --blake3 ${blake3-lean.outPath}
    '';

    build-graph = mkCheck "build-graph" [] ''
      ./.lake/build/bin/check-build-graph --root ${auditSrc}
    '';

    # The pipeline suites (M3.1, MT.8), run from the shared programs build
    # against the tracked tree. Run one after another they take about 21
    # minutes in the sandbox, which with the rest of the surface exceeds the
    # 30-minute budget at --max-jobs 1, so this one check runs them
    # concurrently, NIX_BUILD_CORES at a time, longest first (docs/ci.md has
    # each suite's measured time and memory). Each suite's complete output is
    # printed under its name with its status and wall time; the check fails
    # if any suite fails, naming each one.
    suites = mkCheck "suites" nativeInputs ''
      ${pkgs.lib.optionalString (!native)
        ''echo "suites: native runs skipped (tests-rt, tests-pipeline, check-backend, tests-corpus, tests-own): ${system} is not x86_64-linux"''}
      mkdir -p suite-logs
      bin=./.lake/build/bin
      parallel=''${NIX_BUILD_CORES:-1}
      [ "$parallel" -ge 1 ] || parallel=1
      names=()
      launch() {
        local name=$1
        shift
        while [ "$(jobs -rp | wc -l)" -ge "$parallel" ]; do wait -n || true; done
        names+=("$name")
        (
          start=$SECONDS
          if "$@" > "suite-logs/$name.log" 2>&1; then status=ok; else status="FAILED (exit $?)"; fi
          echo "$status, $((SECONDS - start)) s" > "suite-logs/$name.status"
        ) &
      }
      # sum-loop's big-step levels run in child processes with a 4 GiB Lean
      # stack (LEAN_STACK_SIZE_KB): about 4.4 GB peak.
      launch tests-pipeline $bin/tests-pipeline ${ccArg}
      launch corpus-check $bin/corpus check
      launch tests-corpus $bin/tests-corpus ${ccArg}
      launch check-backend $bin/check-backend ${ccArg}
      launch check-regalloc $bin/check-regalloc
      launch tests-src $bin/tests-src
      launch tests-rt $bin/tests-rt ${ccArg}
      launch check-xv-select $bin/check-xv-select
      launch tests-lam $bin/tests-lam
      launch tests-fir $bin/tests-fir
      launch check-lir $bin/check-lir
      launch tests-anf $bin/tests-anf
      launch tests-own $bin/tests-own ${ccArg}
      launch tests-shrink $bin/tests-shrink
      launch tests-relevance $bin/tests-relevance
      launch tests-recheck $bin/tests-recheck
      wait
      failed=()
      for name in "''${names[@]}"; do
        status=$(cat "suite-logs/$name.status" 2>/dev/null || echo "FAILED (no status)")
        echo "=== $name: $status"
        cat "suite-logs/$name.log"
        case $status in ok*) ;; *) failed+=("$name") ;; esac
      done
      echo "=== summary"
      for name in "''${names[@]}"; do echo "$name: $(cat "suite-logs/$name.status" 2>/dev/null)"; done
      if [ ''${#failed[@]} -ne 0 ]; then
        echo "suites failed: ''${failed[*]}"
        exit 1
      fi
    '';

    # Deterministic typed-x86 and ByteEval step counts (M3.2, MEAS-3) must
    # equal the reviewed baseline fixtures/ixon-v3/bench-k1/steps.json.
    x86-steps = mkCheck "x86-steps" [] ''
      ./.lake/build/bin/check-steps
    '';
  }
  // pkgs.lib.optionalAttrs (system == "x86_64-linux") {
    # Runs every generated case natively (the harness maps fixed pages and
    # executes code), so it is limited to x86-64 Linux hosts.
    x86-hardware = mkCheck "x86-hardware" [pkgs.stdenv.cc pkgs.llvmPackages.llvm] ''
      cc -O1 -o hw_diff_harness ${auditSrc}/fixtures/x86/hw_diff_harness.c
      ./.lake/build/bin/check-x86-hardware --harness ./hw_diff_harness \
        --llvm-mc ${pkgs.llvmPackages.llvm}/bin/llvm-mc
    '';
  }
