{
  pkgs,
  system,
  auditSrc,
  blake3-lean,
  mkCheck,
}: let
  x86ObjectNativeArgs =
    pkgs.lib.optionalString (system == "x86_64-linux")
    "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/x86/native_harness.c";
in rec {
  testsCheck = mkCheck "tests" [] ''
    for suite in addressing pipeline hpt ixon ixon-v3; do
      ./.lake/build/bin/tests-"$suite"
    done
    ./.lake/build/bin/tests | tee tests.out
    grep -q tests-ok tests.out
  '';

  catalogContactCheck = mkCheck "catalog-contact" [] ''
    test -x ./.lake/build/bin/catalog-contact
  '';

  aiurCheck = mkCheck "aiur" [pkgs.coreutils] ''
    ./.lake/build/bin/tests-aiur
    ./.lake/build/bin/check-aiur --root ${auditSrc}
  '';

  trustedExternCheck = mkCheck "check-trusted-externs" [pkgs.coreutils] ''
    ./.lake/build/bin/check-trusted-externs \
      --root ${auditSrc} \
      --dependency-root Blake3=${blake3-lean.outPath} \
      --gmp-version ${pkgs.gmp.version}
    ./.lake/build/bin/check-tools-tests \
      --root ${auditSrc} --blake3 ${blake3-lean.outPath}
  '';

  x86EncoderCheck = mkCheck "check-x86-encoder" [pkgs.binutils] ''
    ./.lake/build/bin/check-x86-encoder \
      --objdump ${pkgs.binutils}/bin/objdump
  '';

  x86BytesCheck = mkCheck "check-x86-bytes" [] ''
    ./.lake/build/bin/check-x86-bytes
  '';

  x86StreamsCheck = mkCheck "check-x86-streams" [] ''
    ./.lake/build/bin/check-x86-streams
  '';

  x86ObjectCheck = mkCheck "x86-object-fixture" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-x86-object \
      --fixture ./.lake/build/bin/x86-object-fixture \
      --readelf ${pkgs.binutils}/bin/readelf \
      --objdump ${pkgs.binutils}/bin/objdump ${x86ObjectNativeArgs}
  '';

  sourceCoverageCheck = mkCheck "source-coverage" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-source-coverage \
      --fixture ./.lake/build/bin/source-coverage \
      --contact ${auditSrc}/fixtures/ixon-std-contact \
      --upstream ${auditSrc}/fixtures/ixon-upstream \
      --expected ${auditSrc}/fixtures/source-coverage/expected.json \
      --readelf ${pkgs.binutils}/bin/readelf \
      --objdump ${pkgs.binutils}/bin/objdump ${x86ObjectNativeArgs}
  '';

  sourceRecursionCheck = mkCheck "source-recursion" [] ''
    ./.lake/build/bin/check-source-recursion \
      --fixture ./.lake/build/bin/source-recursion \
      --expected ${auditSrc}/fixtures/source-recursion/expected.json
  '';

  sourceCallReuseCheck = mkCheck "source-call-reuse" [] ''
    ./.lake/build/bin/check-source-call-reuse \
      --fixture ./.lake/build/bin/source-call-reuse \
      --expected ${auditSrc}/fixtures/source-call-reuse/expected.json
  '';

  sourceSpaceCheck = mkCheck "source-space" [] ''
    ./.lake/build/bin/check-source-space \
      --fixture ./.lake/build/bin/source-space \
      --expected ${auditSrc}/fixtures/source-space/expected.json
  '';

  sourceModularCheck = mkCheck "source-modular" [] ''
    ./.lake/build/bin/check-source-modular \
      --fixture ./.lake/build/bin/source-modular \
      --expected ${auditSrc}/fixtures/source-modular/expected.json
  '';

  assemblyScalingCheck = mkCheck "assembly-scaling" [] ''
    ./.lake/build/bin/check-assembly-scaling \
      --fixture ./.lake/build/bin/assembly-scaling \
      --expected ${auditSrc}/fixtures/assembly-scaling/expected.json \
      --modular-expected ${auditSrc}/fixtures/source-modular/expected.json
  '';

  sourceEvidenceCheck = mkCheck "source-evidence" [] ''
    ./.lake/build/bin/check-source-evidence \
      --fixture ./.lake/build/bin/source-evidence \
      --expected ${auditSrc}/fixtures/source-evidence/expected.json \
      --modular-expected ${auditSrc}/fixtures/source-modular/expected.json
  '';

  ixbyCheck = mkCheck "source-ixby" [pkgs.coreutils] ''
    ./.lake/build/bin/check-ixby \
      --fixture ./.lake/build/bin/source-ixby \
      --runner ./.lake/build/bin/ixby-run \
      --compiler ./.lake/build/bin/ixon-to-ixby \
      --root ${auditSrc} \
      --expected ${auditSrc}/fixtures/ixby/expected.json \
      --upstream ${auditSrc}/fixtures/ixon-upstream
  '';

  ixbySymbolicCheck = mkCheck "source-ixby-symbolic" [] ''
    ./.lake/build/bin/check-ixby-symbolic \
      --fixture ./.lake/build/bin/source-ixby-symbolic \
      --runner ./.lake/build/bin/ixby-run \
      --compiler ./.lake/build/bin/ixon-to-ixby \
      --expected ${auditSrc}/fixtures/ixby-symbolic/expected.json \
      --upstream ${auditSrc}/fixtures/ixon-upstream
  '';

  ixbyStage2Check = mkCheck "source-ixby-stage2" [pkgs.coreutils pkgs.gzip] ''
    ./.lake/build/bin/check-ixby-stage2 \
      --fixture ./.lake/build/bin/source-ixby-stage2 \
      --source-runner ./.lake/build/bin/stage2-source-run \
      --root ${auditSrc} \
      --inputs ${auditSrc}/fixtures/ixby-stage2 \
      --expected ${auditSrc}/fixtures/ixby-stage2/expected.json
  '';

  ixbyLeanCheck = mkCheck "check-ixby-lean" [pkgs.coreutils pkgs.gzip pkgs.diffutils pkgs.python3] ''
    ./.lake/build/bin/check-ixby-lean
    ./.lake/build/bin/check-ixby-binary binary-cases
    cmp binary-cases/conversions.ixby ${auditSrc}/fixtures/ixby-stage2/conversions-v2/program.ixby
    cmp binary-cases/conversions.ixbi ${auditSrc}/fixtures/ixby-stage2/conversions-v2/input.ixbi
    cmp binary-cases/conversions.ixbo ${auditSrc}/fixtures/ixby-stage2/conversions-v2/output.ixbo
    for artifact in program.ixby input.ixbi output.ixbo profile.ixfp; do
      cmp "binary-cases/runtime-v2/$artifact" "${auditSrc}/fixtures/ixby-stage2/runtime-v2/$artifact"
    done
    for image in binary-cases/*.ixby; do
      python3 scripts/inspect_ixby.py "$image" > /dev/null
    done
    cp ./.lake/build/bin/ixby-exec binary-cases/ixby-exec
    (
      cd binary-cases
      env -u LEAN_PATH ./ixby-exec identity.ixby identity.ixbi actual.ixbo
      cmp identity.ixbo actual.ixbo
      env -u LEAN_PATH ./ixby-exec conversions.ixby conversions.ixbi conversions-actual.ixbo
      cmp conversions.ixbo conversions-actual.ixbo
      env -u LEAN_PATH ./ixby-exec runtime-v2/program.ixby runtime-v2/input.ixbi runtime-v2/actual.ixbo
      cmp runtime-v2/output.ixbo runtime-v2/actual.ixbo
    )
    ./.lake/build/bin/stage2-ixby ${auditSrc}/fixtures/ixby-stage2 compile stage2.ixby
    ./.lake/build/bin/stage2-ixby ${auditSrc}/fixtures/ixby-stage2 compile replay.ixby
    ./.lake/build/bin/stage2-ixby ${auditSrc}/fixtures/ixby-stage2 compile-baseline baseline.ixby
    echo 'd42e546f1dc70d0a57b4e1e882c29eabde7259bcbb2c7a3217d797224c89d965  baseline.ixby' | sha256sum -c
    ./.lake/build/bin/stage2-ixby ${auditSrc}/fixtures/ixby-stage2 compile-no-fri no-fri.ixby
    echo '27479840e64aa13db4b1e2b97f7ae7c9540888a88c5ecaaebabfd5542c6fa962  no-fri.ixby' | sha256sum -c
    cmp stage2.ixby replay.ixby
    cmp stage2.ixby.json replay.ixby.json
    cmp ${auditSrc}/fixtures/ixby-stage2/stage2.ixby stage2.ixby
    diff -u ${auditSrc}/fixtures/ixby-stage2/reference-inventory.json stage2.ixby.json
    python3 scripts/inspect_ixby.py stage2.ixby --expected stage2.ixby.json
  '';

  # Each expensive reference execution has an independent required check.
  # The frontend gate above proves its generated bytes equal this frozen image.
  ixbyStage2BinaryChecks = builtins.listToAttrs (map (name: {
      name = "ixby-stage2-binary-${name}";
      value = mkCheck "ixby-stage2-binary-${name}" [pkgs.gzip] ''
        env -u LEAN_PATH ./.lake/build/bin/stage2-ixby \
          ${auditSrc}/fixtures/ixby-stage2 ${name} \
          ${auditSrc}/fixtures/ixby-stage2/stage2.ixby
      '';
    }) [
      "wrong-claim-kind"
      "trailing-public"
      "empty-proof"
      "malformed-proof"
      "truncated-proof"
      "trailing-proof"
      "claim-mismatch"
      "valid"
    ]);

  ixir2Check = mkCheck "ixir2-fixture" [] ''
    ./.lake/build/bin/check-ixir2 \
      --fixture ./.lake/build/bin/ixir2-fixture \
      --expected ${auditSrc}/fixtures/ixir2/expected.json
  '';

  sourceUniqueReuseCheck = mkCheck "source-unique-reuse" [] ''
    ./.lake/build/bin/check-source-unique-reuse \
      --fixture ./.lake/build/bin/source-unique-reuse \
      --expected ${auditSrc}/fixtures/source-unique-reuse/expected.json
  '';

  sourceNativeUniqueCheck = mkCheck "source-native-unique" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-source-native-unique \
      --fixture ./.lake/build/bin/source-native-unique \
      --expected ${auditSrc}/fixtures/source-native-unique/expected.json \
      --readelf ${pkgs.binutils}/bin/readelf \
      --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-unique/native_harness.c"}
  '';

  sourceNativeRuntimeCheck = mkCheck "source-native-runtime" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-source-native-runtime \
      --fixture ./.lake/build/bin/source-native-runtime \
      --expected ${auditSrc}/fixtures/source-native-runtime/expected.json \
      --readelf ${pkgs.binutils}/bin/readelf \
      --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-runtime/native_harness.c"}
    ./.lake/build/bin/check-source-native-runtime \
      --fixture ./.lake/build/bin/source-native-runtime \
      --variant counter-fold \
      --expected ${auditSrc}/fixtures/source-native-runtime/expected-counter-fold.json \
      --readelf ${pkgs.binutils}/bin/readelf \
      --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-runtime/native_harness.c"}
  '';

  sourceNativeAllocatingCheck = mkCheck "source-native-allocating" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-source-native-allocating \
      --fixture ./.lake/build/bin/source-native-allocating \
      --expected ${auditSrc}/fixtures/source-native-allocating/expected.json \
      --readelf ${pkgs.binutils}/bin/readelf \
      --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-allocating/native_harness.c"}
    ./.lake/build/bin/check-source-native-allocating \
      --fixture ./.lake/build/bin/source-native-allocating \
      --variant counter-fold \
      --expected ${auditSrc}/fixtures/source-native-allocating/expected-counter-fold.json \
      --readelf ${pkgs.binutils}/bin/readelf \
      --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-allocating/native_harness.c"}
  '';

  sourceNativeUpstreamCheck = mkCheck "source-native-upstream" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-source-native-upstream \
      --fixture ./.lake/build/bin/source-native-upstream \
      --expected ${auditSrc}/fixtures/source-native-upstream/expected.json \
      --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-upstream/native_harness.c"}
  '';

  sourceNativeScalarCheck = mkCheck "source-native-scalar" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-source-native-scalar \
      --fixture ./.lake/build/bin/source-native-scalar \
      --expected ${auditSrc}/fixtures/source-native-scalar/expected.json \
      --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-scalar/native_harness.c"}
  '';

  sourceNativePhysicalScalarCheck = mkCheck "source-native-physical-scalar" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-source-native-physical-scalar \
      --fixture ./.lake/build/bin/source-native-physical-scalar \
      --expected ${auditSrc}/fixtures/source-native-physical-scalar/expected.json \
      --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-physical-scalar/native_harness.c"}
  '';

  sourceNativeHeapCheck = mkCheck "source-native-heap" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-source-native-heap \
      --fixture ./.lake/build/bin/source-native-heap \
      --consumer ./.lake/build/bin/heap-snapshot-object \
      --expected ${auditSrc}/fixtures/source-native-heap/expected.json \
      --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-heap/native_harness.c"}
    ./.lake/build/bin/check-source-native-heap \
      --fixture ./.lake/build/bin/source-native-heap \
      --consumer ./.lake/build/bin/heap-snapshot-object \
      --expected ${auditSrc}/fixtures/source-native-heap/expected-shared.json \
      --emission shared \
      --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-heap/native_harness.c"}
    ./.lake/build/bin/check-source-native-heap \
      --fixture ./.lake/build/bin/source-native-heap \
      --consumer ./.lake/build/bin/heap-snapshot-object \
      --expected ${auditSrc}/fixtures/source-native-heap/expected-graph.json \
      --emission graph \
      --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-heap/native_harness.c"}
  '';

  sourceNativeCapturedScalarCheck = mkCheck "source-native-captured-scalar" ([pkgs.binutils]
    ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc]) ''
    ./.lake/build/bin/check-source-native-captured-scalar \
      --fixture ./.lake/build/bin/source-native-captured-scalar \
      --expected ${auditSrc}/fixtures/source-native-captured-scalar/expected.json \
      --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
      ${pkgs.lib.optionalString (system == "x86_64-linux")
      "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-captured-scalar/native_harness.c"}
  '';

  nativeSharingCheck = mkCheck "native-sharing" [pkgs.gcc pkgs.binutils] ''
    ./.lake/build/bin/check-native-sharing \
      --fixture ./.lake/build/bin/native-sharing \
      --consumer ./.lake/build/bin/heap-snapshot-object \
      --expected ${auditSrc}/fixtures/native-sharing/expected.json \
      --cc ${pkgs.gcc}/bin/gcc --harness ${auditSrc}/benchmarks/native/scaling_harness.c \
      --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump
  '';

  nativeGraphCheck = mkCheck "native-graph" [pkgs.gcc pkgs.binutils] ''
    ./.lake/build/bin/check-native-graph \
      --fixture ./.lake/build/bin/native-graph \
      --consumer ./.lake/build/bin/heap-snapshot-object \
      --expected ${auditSrc}/fixtures/native-graph/expected.json \
      --cc ${pkgs.gcc}/bin/gcc --harness ${auditSrc}/benchmarks/native/scaling_harness.c \
      --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump
  '';

  sourceBorrowCheck = mkCheck "source-borrow" [] ''
    ./.lake/build/bin/check-source-borrow \
      --fixture ./.lake/build/bin/source-borrow \
      --expected ${auditSrc}/fixtures/source-borrow/expected.json
  '';

  sourceBorrowRuntimeCheck = mkCheck "source-borrow-runtime" [] ''
    ./.lake/build/bin/check-source-borrow-runtime \
      --fixture ./.lake/build/bin/source-borrow-runtime \
      --expected ${auditSrc}/fixtures/source-borrow-runtime/expected.json
  '';
}
