{
  pkgs,
  system,
  ixccLib,
  programs,
  grounding,
  auditSrc,
  ledgerWorkspace,
  blake3-lean,
  mkCheck,
  mkCheckWith,
}: let
  # The one check with a C compiler: `x86-elf-object` links the object
  # writer's fixtures with the C test harnesses in fixtures/x86 and runs them,
  # and links (without running) objects `ixcc compile` writes in the check, so
  # that the system linker accepts IxCC's relocatable objects. No gate runs a
  # compiled program through C. (`x86-hardware` builds its processor harness
  # with the C compiler too.)
  objectArgs =
    pkgs.lib.optionalString (system == "x86_64-linux")
    "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/x86/native_harness.c --ixcc ./.lake/build/bin/ixcc";
  objectInputs = pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
  # The pipeline suites run their objects natively with `--native`, as test
  # executables IxCC writes (no C compiler, C library or linker); elsewhere
  # they run every Lean level and say that the native runs are skipped.
  native = system == "x86_64-linux";
  nativeArg = pkgs.lib.optionalString native "--native";
  # Standalone executables (`ixcc compile --exe`) run natively on x86-64 Linux
  # only: `tests-exe` runs them (and lists their system calls with strace), and
  # `tests-corpus` runs every root of their fragment on its cases.
  exeArgs = pkgs.lib.optionalString native "--run --strace ${pkgs.strace}/bin/strace";
  exeArg = pkgs.lib.optionalString native "--exe";
  exeInputs = pkgs.lib.optionals native [pkgs.strace];
in
  # IxCC's required checks; ix's flake exposes each as `ixcc-<name>`. The
  # trust ledger's `required_checks` lists exactly these attribute names, and
  # `.github/workflows/ixcc.yml` requires the flake's evaluated `ixcc-*` set
  # to equal it (docs/trusted-extern-ledger.md).
  {
    # The production library, and the shared build of every executable and
    # the complete proof and fence collection that the checks below run.
    build = ixccLib;
    proofs = programs;

    # The catalog reader rejects symlinked files, so the fixture commands read
    # the store copy of the source tree rather than the symlinked work tree.
    ixon-v3 = mkCheck "ixon-v3" [] ''
      ./.lake/build/bin/tests-ixon-v3
      ./.lake/build/bin/check-ixon-v3 ${auditSrc}/fixtures/ixon-v4/handoff/accepted.ixe \
        ${auditSrc}/fixtures/ixon-v4/handoff/profile.bin \
        ${auditSrc}/fixtures/ixon-v4/handoff/accepted.claim
      ./.lake/build/bin/check-ixon-v3-catalog ${auditSrc}/fixtures/ixon-v4/catalog/fat.ixc
      ./.lake/build/bin/check-ixon-v3-catalog ${auditSrc}/fixtures/ixon-v4/catalog/chunked.ixc \
        ${auditSrc}/fixtures/ixon-v4/catalog/chunked.ixc/members.json
    '';

    # The admission census must reproduce its reviewed baseline exactly, so
    # per-constant verdicts and budget headroom change only with review.
    census = mkCheck "census" [pkgs.diffutils] ''
      ./.lake/build/bin/census ${auditSrc}/fixtures/ixon-v4/k1/k1.ixe \
        --names ${auditSrc}/fixtures/ixon-v4/k1/equations.json --out census.json
      diff -u ${auditSrc}/fixtures/ixon-v4/k1/census.json census.json
      for name in fib sum-loop ackermann tak gcd; do
        ./.lake/build/bin/census ${auditSrc}/fixtures/ixon-v4/bench-k1/$name.ixe \
          --names ${auditSrc}/fixtures/ixon-v4/bench-k1/$name.equations.json --out $name.census.json
        diff -u ${auditSrc}/fixtures/ixon-v4/bench-k1/$name.census.json $name.census.json
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

    x86-elf-object = mkCheck "x86-elf-object" ([pkgs.binutils] ++ objectInputs) ''
      ./.lake/build/bin/check-x86-object \
        --fixture ./.lake/build/bin/x86-object-fixture \
        --readelf ${pkgs.binutils}/bin/readelf \
        --objdump ${pkgs.binutils}/bin/objdump ${objectArgs}
    '';

    # The ledger audits IxCC in its workspace: «ix-ck» at its recorded path
    # (`../IxCK`), the repository's flake.lock and the workflows it scopes.
    trusted-extern-ledger = mkCheck "trusted-extern-ledger" [] ''
      ./.lake/build/bin/check-trusted-externs \
        --root ${ledgerWorkspace}/IxCC \
        --dependency-root Blake3=${blake3-lean.outPath} \
        --gmp-version ${pkgs.gmp.version}
      ./.lake/build/bin/check-tools-tests \
        --root ${ledgerWorkspace}/IxCC --blake3 ${blake3-lean.outPath}
    '';

    build-graph = mkCheck "build-graph" [] ''
      ./.lake/build/bin/check-build-graph --root ${auditSrc}
    '';

    # Portable RC semantics and driver protocol. All programs come from the
    # same shared build as the other required checks.
    rc-runtime = mkCheck "rc-runtime" [pkgs.findutils] ''
      mkdir -p rc-logs
      show_rc_runtime_logs() {
        find rc-logs -type f \
          \( -name '*.stdout' -o -name '*.stderr' -o -name '*.json' -o -name '*.tsv' \) \
          -exec sh -c 'for file do echo "=== $file"; cat "$file"; done' sh {} +
      }
      trap show_rc_runtime_logs ERR
      timeout --kill-after=5 600 ./.lake/build/bin/tests-rt-rc controls
      timeout --kill-after=5 600 ./.lake/build/bin/tests-rt-rc deep
      timeout --kill-after=5 600 ./.lake/build/bin/tests-cfg-rc
      timeout --kill-after=5 600 ./.lake/build/bin/tests-driver-session
      timeout --kill-after=5 600 ./.lake/build/bin/tests-pipeline-rc levels rc-logs/levels
      timeout --kill-after=5 600 ./.lake/build/bin/tests-pipeline-rc counters rc-logs/counters
      mkdir -p "$out"
      cp -R rc-logs "$out/"
    '';

    # The pipeline suites, run from the shared programs build
    # against the tracked tree. Run one after another they take about 21
    # minutes in the sandbox, which with the rest of the surface exceeds the
    # 30-minute budget at --max-jobs 1, so this one check runs them
    # concurrently, NIX_BUILD_CORES at a time, longest first (docs/ci.md has
    # each suite's measured time and memory). Each suite's complete output is
    # printed under its name with its status and wall time; the check fails
    # if any suite fails, naming each one.
    suites = mkCheck "suites" exeInputs ''
      ${pkgs.lib.optionalString (!native)
        ''echo "suites: native runs skipped (tests-rt, tests-pipeline, check-backend, tests-corpus, tests-own, tests-exe): ${system} is not x86_64-linux"''}
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
      launch tests-pipeline $bin/tests-pipeline ${nativeArg}
      launch corpus-check $bin/corpus check
      launch certified-census-protocol $bin/certified-census --self-test
      launch tests-corpus $bin/tests-corpus ${nativeArg} ${exeArg}
      launch tests-exe $bin/tests-exe ${exeArgs}
      launch check-backend $bin/check-backend ${nativeArg}
      launch check-regalloc $bin/check-regalloc
      launch tests-src $bin/tests-src
      launch tests-rt $bin/tests-rt ${nativeArg}
      launch check-xv-select $bin/check-xv-select
      launch tests-lam $bin/tests-lam
      launch tests-fir $bin/tests-fir
      launch check-lir $bin/check-lir
      launch tests-anf $bin/tests-anf
      launch tests-own $bin/tests-own ${nativeArg}
      launch tests-own-plain $bin/tests-own-plain
      launch tests-shrink $bin/tests-shrink
      launch tests-relevance $bin/tests-relevance
      launch tests-recheck $bin/tests-recheck
      launch tests-recheck-readback $bin/tests-recheck-readback
      launch tests-kernel-front $bin/tests-kernel-front
      launch src-artifacts $bin/gen-src-artifacts --check
      launch recheck-artifacts $bin/gen-recheck-artifacts --check
      launch corpus-kernel-artifacts $bin/corpus kernel-artifacts --check
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

    # The grounding of SrcEval in the kernel's model (`IxCCGrounding`, docs/certification-design.md):
    # building the library checks its axiom fence; `tests-grounding` runs the check its theorems
    # take on the committed closures, conjunct by conjunct, with its negative controls. Its own
    # build (`nix/build.nix`), so the kernel's model never enters the shared program build.
    grounding = mkCheckWith grounding "grounding" [] ''
      ./.lake/build/bin/tests-grounding
    '';

    # Deterministic typed-x86 and ByteEval step counts must
    # equal the reviewed baseline fixtures/ixon-v4/bench-k1/steps.json.
    x86-steps = mkCheck "x86-steps" [] ''
      ./.lake/build/bin/check-steps
    '';
  }
  // pkgs.lib.optionalAttrs (system == "x86_64-linux") {
    # Actual generated runtime procedures and fresh serialized certificate
    # replay with complete native values and same-arena reclamation, in test
    # executables IxCC writes (no C compiler). Keep the independent oracles, child
    # budgets and diagnostics in the required gate.
    rc-native = mkCheck "rc-native" [pkgs.findutils] ''
      mkdir -p rc-logs
      show_rc_logs() {
        find rc-logs -type f \
          \( -name '*.stdout' -o -name '*.stderr' -o -name '*.json' \) \
          -exec sh -c 'for file do echo "=== $file"; cat "$file"; done' sh {} +
      }
      trap show_rc_logs ERR
      timeout --kill-after=5 600 ./.lake/build/bin/tests-rt-rc native rc-logs/runtime
      timeout --kill-after=5 600 ./.lake/build/bin/tests-rc-certificate fresh rc-logs/certificate
      timeout --kill-after=5 600 ./.lake/build/bin/tests-pipeline-rc native rc-logs/levels-native
      timeout --kill-after=5 600 ./.lake/build/bin/tests-pipeline-rc negative rc-logs/negative
      mkdir -p "$out"
      cp -R rc-logs "$out/"
    '';

    # Runs every generated case natively (the harness maps fixed pages and
    # executes code), so it is limited to x86-64 Linux hosts.
    x86-hardware = mkCheck "x86-hardware" [pkgs.stdenv.cc pkgs.llvmPackages.llvm] ''
      cc -O1 -o hw_diff_harness ${auditSrc}/fixtures/x86/hw_diff_harness.c
      ./.lake/build/bin/check-x86-hardware --harness ./hw_diff_harness \
        --llvm-mc ${pkgs.llvmPackages.llvm}/bin/llvm-mc
    '';
  }
