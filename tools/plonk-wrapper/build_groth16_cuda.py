#!/usr/bin/env python3
"""Build the terminal helper with BN254 ICICLE acceleration from an explicit installation."""

import argparse
import os
from pathlib import Path
import shlex
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--icicle-root", required=True, type=Path)
    parser.add_argument("--go", default=os.environ.get("GO", "go"))
    parser.add_argument("--plonk-cuda", action="store_true")
    args = parser.parse_args()
    root = args.icicle_root.resolve(strict=True)
    library = root / "lib"
    for name in ["libicicle_device.so", "libicicle_field_bn254.so", "libicicle_curve_bn254.so"]:
        if not (library / name).is_file():
            parser.error(f"missing ICICLE v3.2.2 library: {library / name}")
    backend = library / "backend"
    if not backend.is_dir():
        parser.error("the ICICLE installation has no backend directory")
    output = args.out.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, CGO_ENABLED="1", GOTOOLCHAIN="local")
    env["CGO_LDFLAGS"] = " ".join(filter(None, [env.get("CGO_LDFLAGS", ""),
        f"-L{shlex.quote(str(library))} -Wl,-rpath,{shlex.quote(str(library))}"]))
    tags = "icicle,cuda" if args.plonk_cuda else "icicle"
    linker = "-X " + shlex.quote("main.groth16LibraryDefault=" + str(backend))
    subprocess.run([args.go, "build", "-buildvcs=false", "-trimpath", "-mod=readonly",
                    "-tags", tags, "-ldflags", linker, "-o", str(output), "."],
                   cwd=Path(__file__).resolve().parent, env=env, check=True)


if __name__ == "__main__":
    main()
