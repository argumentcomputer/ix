#!/usr/bin/env python3
"""Build the optional BN254 CUDA helper against authenticated local sources."""

import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def run(args, **kwargs):
    return subprocess.run([str(x) for x in args], check=True, **kwargs)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--build-dir", required=True, type=Path)
    parser.add_argument("--sppark", required=True, type=Path)
    parser.add_argument("--blst", required=True, type=Path)
    parser.add_argument("--go", default=os.environ.get("GO", "go"))
    parser.add_argument("--test-binary", action="store_true")
    parser.add_argument("--package", choices=[".", "./internal/cuda"], default=".")
    parser.add_argument("--reuse-native", action="store_true")
    args = parser.parse_args()
    output = args.out.resolve()
    build = args.build_dir.resolve()
    build.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    with (build / ".build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        build_helper(args, output, build)


def build_helper(args, output, build):
    environment = dict(os.environ, GOTOOLCHAIN="local", CGO_ENABLED="1")
    native = build / "native"
    if args.reuse_native:
        specification = importlib.util.spec_from_file_location("ix_plonk_native_build",
            ROOT / "crates/proof-compression/cuda/plonk/build.py")
        native_builder = importlib.util.module_from_spec(specification)
        previous_bytecode_setting = sys.dont_write_bytecode
        try:
            sys.dont_write_bytecode = True
            specification.loader.exec_module(native_builder)
        finally:
            sys.dont_write_bytecode = previous_bytecode_setting
        native_builder.validate_sources(args.sppark.resolve(), args.blst.resolve())
        receipt = json.loads((native / "build-manifest.json").read_text())
        if "patched_sppark" not in receipt:
            raise ValueError("native library needs rebuilding with the pinned sppark patch")
        patched_receipt = native_builder.validate_patched_sppark(Path(receipt["patched_sppark"]["root"]))
        if patched_receipt != receipt["patched_sppark"]:
            raise ValueError("private sppark source identity differs from native build receipt")
        architectures = environment.get("IX_PLONK_CUDA_ARCHS", "120").replace(",", " ").split()
        if architectures != receipt["architectures"]:
            raise ValueError("native library architecture selection changed")
        if digest(native / "libix_plonk_bn254_cuda.so") != receipt["library_sha256"]:
            raise ValueError("native library differs from its build receipt")
        for path, expected in receipt["inputs_sha256"].items():
            if digest(Path(path)) != expected:
                raise ValueError(f"native build input changed: {path}")
    else:
        run(["python3", ROOT / "crates/proof-compression/cuda/plonk/build.py",
             "--sppark", args.sppark.resolve(), "--blst", args.blst.resolve(),
             "--out", native], env=environment)
    header = ROOT / "crates/proof-compression/cuda/plonk"
    native_identity = hashlib.sha256((digest(native / "libix_plonk_bn254_cuda.so")
        + digest(header / "ix_plonk_bn254.h")).encode()).hexdigest()
    # cgo does not track headers outside its package as Go cache inputs.
    environment["CGO_CFLAGS"] = (environment.get("CGO_CFLAGS", "")
        + f" -I{header} -DIX_PLONK_NATIVE_BUILD_{native_identity[:20]}=1").strip()
    library_dir = output.parent.parent / "lib"
    library_dir.mkdir(parents=True, exist_ok=True)
    library = library_dir / "libix_plonk_bn254_cuda.so"
    with tempfile.NamedTemporaryFile(prefix=".plonk-cuda-", dir=library_dir, delete=False) as stream:
        temporary_library = Path(stream.name)
    try:
        shutil.copy2(native / library.name, temporary_library)
        temporary_library.replace(library)
    finally:
        temporary_library.unlink(missing_ok=True)
    environment["CGO_LDFLAGS"] = (environment.get("CGO_LDFLAGS", "")
        + f" -L{library_dir} -Wl,-rpath,$ORIGIN/../lib -lix_plonk_bn254_cuda").strip()
    command = [args.go, "test", "-c"] if args.test_binary else [args.go, "build"]
    temporary_output = output.with_suffix(output.suffix + ".tmp")
    command += ["-buildvcs=false", "-trimpath", "-mod=readonly",
                "-tags", "cuda",
                "-o", str(temporary_output), args.package]
    run(command, cwd=HERE, env=environment)
    temporary_output.replace(output)
    record = {
        "go_mod_sha256": digest(HERE / "go.mod"),
        "go_sum_sha256": digest(HERE / "go.sum"),
        "go_version": subprocess.check_output([args.go, "version"], text=True).strip(),
        "binary": str(output), "binary_sha256": digest(output),
        "library": str(library), "library_sha256": digest(library),
        "native_build_identity": native_identity,
        "native_receipts": [str(p) for p in native.glob("*.json")],
        "go_command": command, "test_binary": args.test_binary,
    }
    output.with_suffix(output.suffix + ".build.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record))


if __name__ == "__main__":
    main()
