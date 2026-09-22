"""Build the frozen replay sources on four CPU cores using the warm Cargo cache."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / "target/blake3-seeds-build"
BASE = ROOT / "target/prover-profile-build"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("kind", choices=["tests", "ffi", "pageable"])
    args = parser.parse_args()
    settings = json.loads((BASE / "build.json").read_text())["environment"]
    settings["PATH"] = ":".join([settings["LEAN_SYSROOT"] + "/bin",
                                "/usr/local/cuda-13.3/bin", os.environ["PATH"]])
    affinity = sorted(os.sched_getaffinity(0))[-28:-24]
    assert len(affinity) == 4
    os.sched_setaffinity(0, affinity)
    env = dict(os.environ, **settings)
    if args.kind == "pageable":
        build_pageable(env, settings, affinity)
        return
    command = ["/home/sam/.cargo/bin/cargo"]
    if args.kind == "tests":
        command += ["test", "--release", "--locked", "-p", "aiur", "--lib",
                    "--features", "parallel,cuda", "--no-run", "--message-format=json"]
    else:
        command += ["build", "--release", "--locked", "-p", "ix-ffi", "--features", "parallel,cuda"]
    metadata = {"environment": settings, "cpu_affinity": affinity, "command": command}
    with (BUILD / f"{args.kind}-build.log").open("w") as log:
        subprocess.run(command, cwd=BUILD / "source/ix", env=env,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    if args.kind == "tests":
        artifacts = []
        for line in (BUILD / "tests-build.log").read_text().splitlines():
            try:
                message = json.loads(line)
            except ValueError:
                continue
            if message.get("reason") == "compiler-artifact" and message.get("executable"):
                artifacts.append(message["executable"])
        assert len(artifacts) == 1, artifacts
        binary = BUILD / "aiur-tests"
        shutil.copy2(artifacts[0], binary)
    else:
        archive = BUILD / "libix_ffi.a"
        shutil.copy2(ROOT / "target/release/libix_ffi.a", archive)
        response = (BASE / "ix.rsp").read_text().replace(str(BASE / "libix_ffi.a"), str(archive))
        (BUILD / "ix.rsp").write_text(response)
        binary = BUILD / "ix-packed"
        subprocess.run([settings["LEAN_SYSROOT"] + "/bin/clang", "-o", str(binary),
                        "@" + str(BUILD / "ix.rsp")], env=env, cwd=ROOT, check=True)
    with binary.open("rb") as stream:
        metadata["sha256"] = hashlib.file_digest(stream, "sha256").hexdigest()
    metadata["binary"] = str(binary)
    (BUILD / f"{args.kind}-build.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(binary, metadata["sha256"], flush=True)


def build_pageable(env, settings, affinity):
    source = (BUILD / "source/ix/crates/aiur/cuda/blake3_trace.cu").read_text()
    for old, new in [
        ("    PinnedSeedLease staging;\n", ""),
        ("    if (real) status = staging.acquire();\n", ""),
        ("        std::memcpy(staging.data(), seeds, bytes);\n", ""),
        ("cudaMemcpyAsync(device_seeds, staging.data(), bytes,", "cudaMemcpyAsync(device_seeds, seeds, bytes,"),
    ]:
        assert source.count(old) == 1, old
        source = source.replace(old, new)
    cuda_source = BUILD / "packed-pageable.cu"
    cuda_source.write_text(source)
    members = subprocess.check_output(["ar", "t", str(BUILD / "libix_ffi.a")], text=True).splitlines()
    objects = [name for name in members if name.endswith("_blake3_trace.o")]
    assert len(objects) == 1, objects
    obj = BUILD / objects[0]
    compile_command = ["/usr/local/cuda-13.3/bin/nvcc", "--compile", "--std=c++17",
        "--cudart=static", "--default-stream=per-thread", "-O3", "-lineinfo",
        "--compiler-options=-fPIC", "-gencode=arch=compute_120,code=sm_120",
        "-o", str(obj), str(cuda_source)]
    subprocess.run(compile_command, env=env, check=True)
    archive = BUILD / "libix_ffi_pageable.a"
    shutil.copy2(BUILD / "libix_ffi.a", archive)
    subprocess.run(["ar", "r", str(archive), str(obj)], check=True)
    response = (BUILD / "ix.rsp").read_text().replace(str(BUILD / "libix_ffi.a"), str(archive))
    rsp = BUILD / "pageable.rsp"
    rsp.write_text(response)
    binary = BUILD / "ix-packed-pageable"
    subprocess.run([settings["LEAN_SYSROOT"] + "/bin/clang", "-o", str(binary), "@" + str(rsp)],
                   env=env, cwd=ROOT, check=True)
    with binary.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    metadata = {"environment": settings, "cpu_affinity": affinity, "compile_command": compile_command,
                "binary": str(binary), "sha256": digest,
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "archive_member_replaced": objects[0]}
    (BUILD / "pageable-build.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(binary, digest, flush=True)


if __name__ == "__main__":
    main()
