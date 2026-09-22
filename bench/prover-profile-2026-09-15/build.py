"""Rebuild only Rust and relink the frozen benchmark's Lean objects."""

import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "target/prover-profile-build"
FROZEN = ROOT / "target/shared-execution-build"
LEAN = Path("/home/sam/.elan/toolchains/leanprover--lean4---v4.33.1")


def run(args, **kwargs):
    print("Running:", args, flush=True)
    subprocess.run(args, check=True, **kwargs)


def prepare():
    metadata = json.loads((FROZEN / "build.json").read_text())
    for name in ("ix", "multi-stark"):
        dest = OUT / "source" / name
        dest.mkdir(parents=True, exist_ok=True)
        repo = ROOT if name == "ix" else ROOT.parent / name
        args = ["git", "-C", str(repo), "archive", metadata["source_heads"][name]]
        if name == "ix":
            args += ["Cargo.toml", "Cargo.lock", "crates"]
        archive = subprocess.check_output(args)
        with tarfile.open(fileobj=io.BytesIO(archive)) as stream:
            stream.extractall(dest, filter="data")
        # patch works independently of the surrounding workspace's Git root.
        run(["patch", "-p1", "--batch", "-i", str(FROZEN / f"{name}.patch")], cwd=dest,
            stdout=subprocess.DEVNULL)
    shutil.copytree(FROZEN / "source/crates", OUT / "source/ix/crates", dirs_exist_ok=True)
    shutil.copy2(Path(__file__).with_name("instrumentation.patch"), OUT / "instrumentation.patch")
    run(["patch", "-p1", "--batch", "-i", str(OUT / "instrumentation.patch")],
        cwd=OUT / "source/ix")
    shutil.copy2(ROOT / "crates/ffi/src/profile.rs", OUT / "source/ix/crates/ffi/src/profile.rs")
    (OUT / "source/ix/.cargo").mkdir(exist_ok=True)
    (OUT / "source/ix/.cargo/config.toml").write_text(
        '[build]\nrustflags = ["-Ctarget-cpu=native"]\n'
        f'target-dir = "{ROOT / "target"}"\n'
        '[patch."https://github.com/argumentcomputer/multi-stark.git"]\n'
        f'multi-stark = {{ path = "{OUT / "source/multi-stark"}" }}\n')


def main():
    os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:4])
    OUT.mkdir(parents=True, exist_ok=True)
    if not (OUT / "source/ix/.cargo/config.toml").exists():
        prepare()
    settings = {
        "CARGO_BUILD_JOBS": "4", "CARGO_NET_OFFLINE": "true",
        "LEAN_NUM_THREADS": "4", "RAYON_NUM_THREADS": "4",
        "MULTI_STARK_CUDA_ARCHS": "120", "RUSTUP_TOOLCHAIN": "1.98.1",
        "LEAN_SYSROOT": str(LEAN), "LIBCLANG_PATH": "/usr/lib/x86_64-linux-gnu",
        "CFLAGS": "-std=gnu17",
    }
    env = dict(os.environ, **settings)
    env["PATH"] = str(LEAN / "bin") + ":/usr/local/cuda-13.3/bin:" + env["PATH"]
    with (OUT / "build.log").open("a") as log:
        run(["cargo", "build", "--release", "-p", "ix-ffi", "--features", "parallel,cuda"],
            cwd=OUT / "source/ix", env=env, stdout=log, stderr=subprocess.STDOUT)
        archive = OUT / "libix_ffi.a"
        shutil.copy2(ROOT / "target/release/libix_ffi.a", archive)
        response = (FROZEN / "ix.rsp").read_text()
        for name in ("default", "net"):
            response = response.replace(str(ROOT / f".lake/build/lib/libix_ffi_{name}.a"), str(archive))
        # Bound LLVM's linker parallelism independently of Cargo.
        response += '\n"-Wl,--threads=4"\n'
        (OUT / "ix.rsp").write_text(response)
        run([str(LEAN / "bin/clang"), "-o", str(OUT / "ix-profile"), "@" + str(OUT / "ix.rsp")],
            cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    with (OUT / "ix-profile").open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    (OUT / "build.json").write_text(json.dumps({"environment": settings, "sha256": digest}, indent=2) + "\n")
    print("Built", OUT / "ix-profile", digest, flush=True)


if __name__ == "__main__":
    main()
