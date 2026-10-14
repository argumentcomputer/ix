#!/usr/bin/env python3
"""Isolate the CUDA backends' libstdc++ ABI inside a Rust static archive."""

import argparse
from collections import Counter
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile


FIXED_MEMBERS = ("kzg.o", "kzg_runtime.o", "sppark_ntt.o", "sppark_all_gpus.o")
KERNEL_MEMBER = re.compile(r"tmpxft_[^/]*_kernels\.o\Z")
PRIVATE_PREFIX = "ix_cuda_private_"
ISOLATED_MEMBER = "ix_cuda_runtime.o"
SPPARK_EXPORTS = {
    "cuda_available",
    "drop_gpu_ptr_t",
    "clone_gpu_ptr_t",
    "drop_error_message",
    "sppark_cuda_fail",
}
LIBC_CXA_IMPORTS = {"__cxa_atexit", "__cxa_finalize", "__cxa_thread_atexit_impl"}


class IsolationError(Exception):
    pass


def run(arguments, *, stdout=subprocess.PIPE):
    result = subprocess.run(
        [str(argument) for argument in arguments],
        stdout=stdout,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if result.returncode:
        command = shlex.join(str(argument) for argument in arguments)
        detail = result.stderr.strip() or "no diagnostic output"
        raise IsolationError(f"command failed ({result.returncode}): {command}\n{detail}")
    return result.stdout or ""


def symbols(path, *options):
    entries = []
    for line in run(["nm", "-P", *options, path]).splitlines():
        fields = line.split()
        if len(fields) < 2 or len(fields[1]) != 1:
            raise IsolationError(f"unexpected nm output for {path}: {line}")
        entries.append((fields[0], fields[1]))
    return entries


def is_public(name):
    return name.startswith(("ix_kzg_", "multi_stark_")) or name in SPPARK_EXPORTS


def is_cxx(name):
    return name.startswith(("_Z", "__cxa_", "__gxx_", "DW.ref.")) or name == "__dynamic_cast"


def selected_members(source):
    listing = run(["ar", "t", source]).splitlines()
    for member in FIXED_MEMBERS:
        count = listing.count(member)
        if count != 1:
            raise IsolationError(f"{source} must contain exactly one {member}; found {count}")
    generated = [member for member in listing if KERNEL_MEMBER.fullmatch(member)]
    if len(generated) != 1:
        raise IsolationError(
            f"{source} must contain exactly one tmpxft_*_kernels.o; found {len(generated)}"
        )
    if ISOLATED_MEMBER in listing:
        raise IsolationError(f"{source} already contains {ISOLATED_MEMBER}")
    return listing, [*FIXED_MEMBERS, generated[0]]


def isolate(source, output, runtime):
    for name in ("ar", "ld", "nm", "objcopy"):
        if shutil.which(name) is None:
            raise IsolationError(f"required GNU binutils tool is missing from PATH: {name}")
    for path in (source, runtime):
        if not path.is_file():
            raise IsolationError(f"input file does not exist: {path}")
    if not output.parent.is_dir():
        raise IsolationError(f"output directory does not exist: {output.parent}")
    listing, members = selected_members(source)

    # A sibling temporary directory keeps publication atomic on the output filesystem.
    with tempfile.TemporaryDirectory(prefix=f".{output.name}.cuda-", dir=output.parent) as temporary:
        directory = Path(temporary)
        objects = []
        for member in members:
            path = directory / member
            with path.open("wb") as stream:
                run(["ar", "p", source, member], stdout=stream)
            objects.append(path)

        combined = directory / "combined.o"
        # COMDAT groups must be resolved before localization: a final linker
        # must not coalesce exception metadata with Lean's libc++abi objects.
        run([
            "ld", "-r", "--force-group-allocation", "-o", combined,
            *objects, "--whole-archive", runtime, "--no-whole-archive",
        ])
        definitions = symbols(combined, "-g", "--defined-only")
        public = {name for name, _ in definitions if is_public(name)}
        private = {name for name, _ in definitions if not is_public(name)}
        if any(name.startswith(PRIVATE_PREFIX) for name in private):
            raise IsolationError("native objects already contain isolated C++ runtime symbols")
        optional = {
            name for name, kind in symbols(combined, "-u")
            if kind in {"w", "v"} and is_cxx(name) and name not in LIBC_CXA_IMPORTS
        }
        rename = directory / "rename.txt"
        rename.write_text(
            "".join(f"{name} {PRIVATE_PREFIX}{name}\n" for name in sorted(private | optional)),
            encoding="utf-8",
        )
        localize = directory / "localize.txt"
        # GNU-unique definitions retain their binding, so their names also
        # need a private prefix. Weak DW.ref personality metadata is localized.
        localize.write_text(
            "".join(f"{PRIVATE_PREFIX}{name}\n" for name in sorted(private)),
            encoding="utf-8",
        )
        renamed = directory / "renamed.o"
        isolated = directory / ISOLATED_MEMBER
        run(["objcopy", f"--redefine-syms={rename}", combined, renamed])
        run(["objcopy", f"--localize-symbols={localize}", renamed, isolated])

        leaked_imports = sorted({
            name for name, kind in symbols(isolated, "-u")
            if (is_cxx(name) and name not in LIBC_CXA_IMPORTS)
            or (name.startswith(PRIVATE_PREFIX) and kind not in {"w", "v"})
        })
        if leaked_imports:
            raise IsolationError("unisolated C++ imports: " + ", ".join(leaked_imports))
        globals_after = symbols(isolated, "-g", "--defined-only")
        leaked_definitions = sorted({
            name for name, kind in globals_after
            if not is_public(name) and not (kind == "u" and name.startswith(PRIVATE_PREFIX))
        })
        if leaked_definitions:
            raise IsolationError("unisolated global definitions: " + ", ".join(leaked_definitions))
        public_after = {name for name, _ in globals_after if is_public(name)}
        if public_after != public:
            raise IsolationError("C ABI exports changed during runtime isolation")

        archive = directory / "output.a"
        shutil.copyfile(source, archive)
        run(["ar", "d", archive, *members])
        run(["ar", "r", archive, isolated])
        run(["ar", "s", archive])
        expected = Counter(listing)
        expected.subtract(members)
        expected[ISOLATED_MEMBER] += 1
        if Counter(run(["ar", "t", archive]).splitlines()) != +expected:
            raise IsolationError("archive member validation failed after runtime isolation")
        os.replace(archive, output)
    print(f"Isolated {len(private)} C++ runtime symbols in {output}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path, help="Cargo-produced Rust static archive")
    parser.add_argument("--output", required=True, type=Path, help="archive to publish atomically")
    parser.add_argument("--runtime", required=True, type=Path, help="matching host compiler's libstdc++.a")
    args = parser.parse_args()
    try:
        isolate(args.source.absolute(), args.output.absolute(), args.runtime.absolute())
    except (IsolationError, OSError) as error:
        print(f"isolate_runtime.py: error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
