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
import stat
import subprocess
import sys
import tempfile


GNARK_VERSION = "v0.16.5-0.20261015185324-262cf453c107"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def run(args, **kwargs):
    return subprocess.run([str(x) for x in args], check=True, **kwargs)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def patch_bytes():
    return b"".join((HERE / "patches" / name).read_bytes() for name in (
        "gnark-cuda-v1.patch", "gnark-cuda-generator-v1.patch"))


def tree_hashes(root):
    result = {}
    for directory, directories, files in os.walk(root):
        for name in directories + files:
            if (Path(directory) / name).is_symlink():
                raise ValueError("symlink in gnark module tree")
        for name in files:
            path = Path(directory) / name
            result[str(path.relative_to(root))] = digest(path)
    return result


def apply_patch(source, vendored=False):
    receipt = json.loads((HERE / "patches/gnark-cuda-v1.json").read_text())
    if receipt["version"] != GNARK_VERSION:
        raise ValueError("CUDA patch targets a different gnark version")
    selected = {}
    for relative, hashes in receipt["files"].items():
        path = source / relative
        if Path(relative).is_absolute() or ".." in Path(relative).parts:
            raise ValueError("invalid path in gnark patch receipt")
        if vendored and not path.exists() and not relative.startswith("backend/plonk/bn254/"):
            continue
        before = hashes["before"]
        if (before is None and path.exists()) or (before is not None and (not path.is_file() or digest(path) != before)):
            raise ValueError(f"gnark source differs from patch receipt: {relative}")
        selected[relative] = hashes
    text = patch_bytes().decode()
    blocks = text.split("diff --git ")
    if blocks[0].strip():
        raise ValueError("gnark patch must use git diff headers")
    filtered = []
    for block in blocks[1:]:
        line = block.splitlines()[0]
        relative = line.split(" b/", 1)[1]
        if relative in selected:
            filtered.append("diff --git " + block)
    if not filtered:
        raise ValueError("no authenticated gnark patch files selected")
    run(["patch", "--batch", "--fuzz=0", "-p1"], cwd=source,
        input="".join(filtered), text=True)
    for relative, hashes in selected.items():
        if digest(source / relative) != hashes["after"]:
            raise ValueError(f"patched gnark digest differs: {relative}")


def patched_module(go, build, environment):
    info = json.loads(subprocess.check_output(
        [go, "list", "-m", "-json", "github.com/consensys/gnark"],
        cwd=HERE, env=environment, text=True))
    if info.get("Version") != GNARK_VERSION or info.get("Replace"):
        raise ValueError("CUDA build requires the pinned, unreplaced gnark module")
    patch_hash = hashlib.sha256(
        patch_bytes()
        + (HERE / "patches/gnark-cuda-v1.json").read_bytes()).hexdigest()
    expected = tree_hashes(Path(info["Dir"]))
    receipt = json.loads((HERE / "patches/gnark-cuda-v1.json").read_text())
    for relative, hashes in receipt["files"].items():
        if expected.get(relative) != hashes["before"]:
            raise ValueError(f"gnark module differs from the pinned patch input: {relative}")
        expected[relative] = hashes["after"]
    destination = build / ("gnark-" + patch_hash[:20])
    if not destination.exists():
        temporary = Path(tempfile.mkdtemp(prefix=".gnark-", dir=build))
        try:
            shutil.copytree(info["Dir"], temporary, dirs_exist_ok=True)
            for directory, _, files in os.walk(temporary):
                Path(directory).chmod(Path(directory).stat().st_mode | stat.S_IWUSR)
                for name in files:
                    path = Path(directory) / name
                    path.chmod(path.stat().st_mode | stat.S_IWUSR)
            apply_patch(temporary)
            temporary.rename(destination)
        finally:
            if temporary.exists():
                shutil.rmtree(temporary)
    else:
        if tree_hashes(destination) != expected:
            raise ValueError("private gnark build copy differs from the complete pinned source tree")
    return destination


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--build-dir", type=Path)
    parser.add_argument("--sppark", type=Path)
    parser.add_argument("--blst", type=Path)
    parser.add_argument("--go", default=os.environ.get("GO", "go"))
    parser.add_argument("--test-binary", action="store_true")
    parser.add_argument("--package", choices=[".", "./internal/cuda"], default=".")
    parser.add_argument("--reuse-native", action="store_true")
    parser.add_argument("--patch-vendor", type=Path)
    args = parser.parse_args()
    if args.patch_vendor:
        apply_patch(args.patch_vendor.resolve(), vendored=True)
        return
    if not all([args.out, args.build_dir, args.sppark, args.blst]):
        parser.error("--out, --build-dir, --sppark and --blst are required")
    output = args.out.resolve()
    build = args.build_dir.resolve()
    build.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    with (build / ".build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        build_helper(args, output, build)


def build_helper(args, output, build):
    environment = dict(os.environ, GOTOOLCHAIN="local", CGO_ENABLED="1")
    source = patched_module(args.go, build, environment)
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
    modfile = build / "cuda.mod"
    modfile.write_text((HERE / "go.mod").read_text()
                      + "\nreplace github.com/consensys/gnark => "
                      + json.dumps(str(source)) + "\n")
    shutil.copyfile(HERE / "go.sum", modfile.with_suffix(".sum"))
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
                "-modfile=" + str(modfile), "-tags", "cuda",
                "-o", str(temporary_output), args.package]
    run(command, cwd=HERE, env=environment)
    temporary_output.replace(output)
    record = {
        "format": "ix-bn254-plonk-cuda-build-v1", "gnark_version": GNARK_VERSION,
        "gnark_patch_sha256": hashlib.sha256(patch_bytes()).hexdigest(),
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
