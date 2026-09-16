#!/usr/bin/env python3
"""Build the observer against an already built Compilatrix ixby-exec target."""
import argparse
import json
import os
from pathlib import Path
import shlex
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compilatrix", required=True, type=Path)
    parser.add_argument("--lean-root", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--lld", type=Path)
    args = parser.parse_args()
    project = args.compilatrix.resolve()
    lean = args.lean_root.resolve()
    output = args.out.resolve()
    source = Path(__file__).resolve().with_name("ExecutionProfile.lean")
    trace = json.loads((project / ".lake/build/ir/IxbyExec.c.o.export.trace").read_text())
    compile_command = next(
        entry["message"][3:]
        for entry in trace["log"]
        if entry.get("message", "").startswith(".> ") and " -c " in entry["message"]
    )
    old_c = str(project / ".lake/build/ir/IxbyExec.c")
    old_object = old_c + ".o.export"
    new_c = str(output / "ExecutionProfile.c")
    new_object = new_c + ".o.export"
    compile_args = shlex.split(compile_command)
    link_args = shlex.split((project / ".lake/build/bin/ixby-exec.rsp").read_text())
    if compile_args.count(old_c) != 1 or compile_args.count(old_object) != 1 or link_args.count(old_object) != 1:
        raise ValueError("existing ixby-exec build layout does not match the expected target")
    output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env["LEAN_SYSROOT"] = str(lean)
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [
        project / ".lake/build/lib/lean",
        project / ".lake/packages/Blake3/.lake/build/lib/lean",
    ])
    subprocess.run([str(lean / "bin/lean"), "--root=" + str(source.parent), "-c", new_c, str(source)], cwd=output, env=env, check=True)
    replacements = {old_c: new_c, old_object: new_object}
    subprocess.run([replacements.get(arg, arg) for arg in compile_args], cwd=output, env=env, check=True)
    replacements = {old_object: new_object}
    if args.lld:
        replacements["-fuse-ld=lld"] = "-fuse-ld=" + str(args.lld.resolve())
    subprocess.run([str(lean / "bin/clang"), "-o", str(output / "execution-profile"), *[replacements.get(arg, arg) for arg in link_args]], cwd=output, env=env, check=True)


if __name__ == "__main__":
    main()
