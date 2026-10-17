#!/usr/bin/env python3
"""Build the standalone BN254 PLONK CUDA library from explicit source roots."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


SPPARK_REVISION = "114feb69ebfe029e2caa5e6c2d372c695e5d4da8"
BLST_CRATE_SHA256 = "dcdb4c7013139a150f9fc55d123186dbfaba0d912817466282c73ac49e71fb45"


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def _validate_tree(root, manifest_path, expected_override=None):
    receipt = json.loads(manifest_path.read_text())
    if receipt.get("format") != "ix-native-source-files/v1":
        raise ValueError(f"unsupported source manifest: {manifest_path}")
    expected = receipt["files_sha256"] if expected_override is None else expected_override
    directories = {"."}
    for relative in expected:
        path = Path(relative)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError(f"invalid source manifest path: {relative}")
        directories.update(str(parent) for parent in path.parents)
    actual = set()
    for current, children, files in os.walk(root, followlinks=False):
        current = Path(current)
        for child in list(children):
            path = current / child
            relative = path.relative_to(root).as_posix()
            if relative == ".git":
                children.remove(child)
                continue
            if path.is_symlink() or relative not in directories:
                raise ValueError(f"unexpected source directory: {path}")
        for child in files:
            path = current / child
            relative = path.relative_to(root).as_posix()
            if relative in (".git", ".cargo-ok"):
                continue
            if path.is_symlink() or not path.is_file() or relative not in expected:
                raise ValueError(f"unexpected source file: {path}")
            actual.add(relative)
    if actual != set(expected):
        raise ValueError(f"missing source files in {root}: {sorted(set(expected) - actual)}")
    for relative, expected_hash in expected.items():
        if digest(root / relative) != expected_hash:
            raise ValueError(f"source digest differs: {root / relative}")
    return {
        "root": str(root), "manifest": str(manifest_path),
        "manifest_sha256": digest(manifest_path),
        "files_sha256": expected,
    }, receipt


def validate_sources(sppark, blst):
    """Authenticate complete dependency trees for builds and native-library reuse."""
    source = Path(__file__).resolve().parent
    sppark = Path(sppark).resolve(strict=True)
    blst = Path(blst).resolve(strict=True)
    sppark_result, sppark_receipt = _validate_tree(sppark, source / "sppark-source-manifest.json")
    if sppark_receipt.get("revision") != SPPARK_REVISION:
        raise ValueError("sppark source receipt revision differs")
    blst_result, blst_receipt = _validate_tree(blst, source / "blst-source-manifest.json")
    if (blst_receipt.get("crate") != "blst" or blst_receipt.get("version") != "0.3.16"
            or blst_receipt.get("crate_sha256") != BLST_CRATE_SHA256
            or blst_receipt.get("subdirectory") != "blst"):
        raise ValueError("blst source receipt identity differs")
    sppark_result["revision"] = SPPARK_REVISION
    blst_result.update(crate="blst", version="0.3.16", crate_sha256=BLST_CRATE_SHA256)
    return {"sppark": sppark_result, "blst": blst_result}


def split_patch():
    source = Path(__file__).resolve().parent
    patch_path = source / "patches/sppark-split-buckets-v1.patch"
    receipt_path = source / "patches/sppark-split-buckets-v1.json"
    patch = patch_path.read_bytes()
    receipt = json.loads(receipt_path.read_text())
    if (receipt.get("format") != "ix-sppark-split-buckets/v1"
            or receipt.get("revision") != SPPARK_REVISION
            or receipt.get("patch_sha256") != hashlib.sha256(patch).hexdigest()):
        raise ValueError("sppark split patch identity differs")
    manifest_path = source / "sppark-source-manifest.json"
    expected = dict(json.loads(manifest_path.read_text())["files_sha256"])
    blocks = patch.decode().split("diff --git ")
    if blocks[0].strip():
        raise ValueError("sppark patch must use git diff headers")
    seen = set()
    for block in blocks[1:]:
        lines = block.splitlines()
        before, relative = lines[0].split(" b/", 1)
        if (before != "a/" + relative or relative in seen
                or relative not in receipt["files"] or Path(relative).is_absolute()
                or ".." in Path(relative).parts):
            raise ValueError("unexpected sppark patch path")
        hashes = receipt["files"][relative]
        if expected.get(relative) != hashes["before"]:
            raise ValueError("sppark patch input differs from pinned source")
        old_header = "--- /dev/null" if hashes["before"] is None else "--- a/" + relative
        if [line for line in lines if line.startswith("--- ")] != [old_header] or [
                line for line in lines if line.startswith("+++ ")] != ["+++ b/" + relative]:
            raise ValueError("sppark patch file headers differ")
        expected[relative] = hashes["after"]
        seen.add(relative)
    if seen != set(receipt["files"]):
        raise ValueError("sppark patch is incomplete")
    return patch, receipt_path, expected


def validate_patched_sppark(root):
    source = Path(__file__).resolve().parent
    patch, receipt_path, expected = split_patch()
    result, _ = _validate_tree(Path(root).resolve(strict=True),
                              source / "sppark-source-manifest.json", expected)
    result.update(patch_sha256=hashlib.sha256(patch).hexdigest(),
                  patch_receipt_sha256=digest(receipt_path))
    return result


def prepare_sppark(sppark, output):
    source = Path(__file__).resolve().parent
    patch, receipt_path, expected = split_patch()
    identity = hashlib.sha256(patch + receipt_path.read_bytes()
                              + (source / "sppark-source-manifest.json").read_bytes()).hexdigest()
    destination = output / ("sppark-" + identity[:20])
    if not destination.exists():
        temporary = Path(tempfile.mkdtemp(prefix=".sppark-", dir=output))
        try:
            pristine = json.loads((source / "sppark-source-manifest.json").read_text())["files_sha256"]
            for relative in pristine:
                path = temporary / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(sppark / relative, path)
            subprocess.run(["patch", "--batch", "--fuzz=0", "-p1"],
                           cwd=temporary, input=patch, check=True)
            validate_patched_sppark(temporary)
            temporary.rename(destination)
        finally:
            if temporary.exists():
                shutil.rmtree(temporary)
    return destination, validate_patched_sppark(destination)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sppark", required=True, type=Path)
    parser.add_argument("--blst", required=True, type=Path,
                        help="blst source root containing src/server.c and build/assembly.S")
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    sppark = args.sppark.resolve(strict=True)
    blst = args.blst.resolve(strict=True)
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    try:
        dependencies = validate_sources(sppark, blst)
        patched_sppark, patched_receipt = prepare_sppark(sppark, output)
    except ValueError as error:
        parser.error(str(error))
    cuda = Path(os.environ.get("CUDA_HOME", os.environ.get("CUDA_PATH", "/usr/local/cuda")))
    nvcc = os.environ.get("NVCC", str(cuda / "bin/nvcc"))
    cc = os.environ.get("CC", "cc")
    architectures = os.environ.get("IX_PLONK_CUDA_ARCHS", "120").replace(",", " ").split()
    if not architectures or any(not item.isdigit() for item in architectures):
        parser.error("IX_PLONK_CUDA_ARCHS must contain numeric CUDA architectures")
    architecture_header = output / "architectures.h"
    architecture_header.write_text(
        "#pragma once\n#define IX_PLONK_CUDA_ARCHITECTURES {" + ",".join(architectures) + "}\n"
    )
    include = [f"-I{patched_sppark}", f"-I{patched_sppark / 'util'}", f"-I{blst / 'src'}", f"-I{source}"]
    common = [nvcc, "--std=c++17", "--cudart=static", "--default-stream=per-thread",
              "-O3", "-lineinfo", "--compiler-options=-fPIC,-fvisibility=hidden",
              "-DFEATURE_BN254", "-DMAX_LG_DOMAIN_SIZE=28", "-D__BLST_PORTABLE__",
              "-include", str(source / "sppark_namespace.h"),
              "-include", str(architecture_header), *include]
    for architecture in architectures:
        common.append(f"-gencode=arch=compute_{architecture},code=sm_{architecture}")
    commands = []

    def run(command):
        commands.append(command)
        print(json.dumps({"command": command}), flush=True)
        subprocess.run(command, check=True)

    native_sources = [source / "plonk.cu", source / "runtime.cpp"]
    objects = []
    for path in native_sources:
        obj = output / (path.stem + ".o")
        run([*common, "-c", str(path), "-o", str(obj)])
        objects.append(obj)
    for path, name in [(blst / "src/server.c", "blst-server.o"),
                       (blst / "build/assembly.S", "blst-assembly.o")]:
        obj = output / name
        run([cc, "-O3", "-fPIC", "-fvisibility=hidden", "-D__BLST_PORTABLE__",
             f"-I{blst / 'src'}", "-c", str(path), "-o", str(obj)])
        objects.append(obj)
    library = output / "libix_plonk_bn254_cuda.so"
    run([nvcc, "--shared", "--cudart=static", *map(str, objects),
         "-Xlinker", f"--version-script={source / 'exports.map'}",
         "-Xlinker", "-z", "-Xlinker", "defs",
         "-Xlinker", "-soname", "-Xlinker", library.name,
         "-o", str(library), "-ldl", "-lrt", "-lpthread"])
    shutil.copyfile(source / "ix_plonk_bn254.h", output / "ix_plonk_bn254.h")
    files = [*native_sources, source / "ix_plonk_bn254.h", source / "sppark_namespace.h",
             source / "exports.map", source / "build.py", source / "sppark-source-manifest.json",
             source / "blst-source-manifest.json", source.parent / "kzg_runtime.cpp",
             source.parent / "kzg_transfer.cuh", blst / "src/server.c", blst / "build/assembly.S",
             source / "patches/sppark-split-buckets-v1.patch", source / "patches/sppark-split-buckets-v1.json"]
    files.extend(patched_sppark / name for name in patched_receipt["files_sha256"])
    metadata = {
        "format": "ix-plonk-bn254-cuda-build/v1", "sppark_revision": SPPARK_REVISION,
        "architectures": architectures, "commands": commands,
        "nvcc": subprocess.check_output([nvcc, "--version"], text=True),
        "dependencies": dependencies,
        "patched_sppark": patched_receipt,
        "inputs_sha256": {str(path): digest(path) for path in files},
        "library_sha256": digest(library),
    }
    if validate_sources(sppark, blst) != dependencies:
        raise ValueError("native dependency source identity changed during compilation")
    if validate_patched_sppark(patched_sppark) != patched_receipt:
        raise ValueError("patched sppark source changed during compilation")
    (output / "build-manifest.json").write_text(json.dumps(metadata, indent=2) + "\n")


if __name__ == "__main__":
    main()
