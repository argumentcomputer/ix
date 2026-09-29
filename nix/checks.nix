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
