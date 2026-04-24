#!/usr/bin/env python3
"""Mechanical orphan migration: move theorems listed in orphan_list to Scratch.lean.

For each FQN in tools/orphans_to_move.txt:
  - locate the theorem decl in Ix/Aiur/Proofs/*.lean
  - extract the block (decl + preceding docstring)
  - cut from source, append to Scratch.lean
  - build-test per file batch
  - restore-on-break

Run: python3 tools/migrate_orphans.py [--dry-run] [--limit N]
"""
from __future__ import annotations
import argparse, re, subprocess, sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROOFS = ROOT / "Ix" / "Aiur" / "Proofs"
SCRATCH = PROOFS / "Scratch.lean"
ORPHAN_LIST = ROOT / "tools" / "orphans_to_move.txt"

# Theorem decl regex (column 0 only).
DECL_RE = re.compile(
    r"^(?:private\s+|@\[[^\]]*\]\s+)*(?:theorem|lemma)\s+([A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*)\s",
    re.MULTILINE,
)
# Boundary regex (any top-level decl keyword at column 0 or one indent).
# NOTE: `@\[` not included — attributes can appear in tactic blocks.
# Boundaries must include leading-attribute lines explicitly via lookahead.
BOUNDARY_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*\n)*[ \t]*"
    r"(?:private\s+|protected\s+|public\s+|@\[[^\]]*\]\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom|namespace|end|mutual)\b",
    re.MULTILINE,
)
# Docstring block.
DOCSTRING_RE = re.compile(r"/--.*?-/\s*$", re.DOTALL | re.MULTILINE)


_PRIVATE_PREFIX_RE = re.compile(r"^_private\.Ix\.Aiur\.Proofs\.([A-Za-z_][\w]*)\.\d+\.(.+)$")


def parse_fqn(fqn: str) -> tuple[str, str | None]:
    """Return (user_facing_name, module_hint) for an FQN.

    For `_private.Ix.Aiur.Proofs.<Module>.<idx>.<core>`, return (core, Module).
    For `Aiur.<core>` or `<core>`, return (core_stripped, None).
    """
    m = _PRIVATE_PREFIX_RE.match(fqn)
    if m is not None:
        module_hint = m.group(1)
        core = m.group(2)
        if core.startswith("Aiur."):
            core = core[5:]
        return (core, module_hint)
    if fqn.startswith("Aiur."):
        return (fqn[5:], None)
    return (fqn, None)


def short_name(fqn: str) -> str:
    """User-facing decl name (no `Aiur.` prefix, no `_private.` mangling)."""
    return parse_fqn(fqn)[0]


def find_decl(source: str, fqn: str) -> tuple[int, int, str] | None:
    """Locate the decl matching `fqn` in `source`. Returns (start, end, block) or None.

    Match strategy: try the FQN's tail-suffixes from longest to shortest.
    The decl line might say `theorem X.Y.foo` or `theorem foo` (when inside namespace).
    """
    candidates: list[str] = []
    name = short_name(fqn)
    parts = name.split(".")
    for k in range(len(parts)):
        candidates.append(".".join(parts[k:]))

    for cand in candidates:
        # Match `theorem <cand> ` or `theorem <cand>(` etc. at column 0.
        pattern = re.compile(
            rf"^[ \t]*(?:private\s+|@\[[^\]]*\]\s+)*(?:theorem|lemma)\s+{re.escape(cand)}\b",
            re.MULTILINE,
        )
        m = pattern.search(source)
        if m is None:
            continue
        # Find decl start (incl. preceding attributes).
        decl_start = m.start()

        # Look back for preceding `/-- ... -/` docstring.
        prefix = source[:decl_start]
        ds_search = re.search(r"/--", prefix[::-1])  # find last /-- before decl
        block_start = decl_start
        # Simpler: scan for `/--` close to decl_start.
        ds_match = list(re.finditer(r"/--.*?-/", source[:decl_start], re.DOTALL))
        if ds_match:
            last_ds = ds_match[-1]
            # Only include docstring if it's immediately before decl (whitespace only between).
            between = source[last_ds.end():decl_start]
            if between.strip() == "":
                block_start = last_ds.start()

        # Find decl end: next BOUNDARY at column 0 after decl_start.
        # Skip the decl_start match itself.
        end_search = source[m.end():]
        nb = BOUNDARY_RE.search(end_search)
        if nb is None:
            decl_end = len(source)
        else:
            decl_end = m.end() + nb.start()

        # Trim trailing block belonging to NEXT decl: if next decl has a
        # `/-- ... -/` docstring immediately before it (only whitespace
        # between), the docstring start is where NEXT decl truly begins.
        next_decl_block = source[:decl_end]
        ds_matches = list(re.finditer(r"/--.*?-/", next_decl_block, re.DOTALL))
        if ds_matches:
            last_ds = ds_matches[-1]
            between = source[last_ds.end():decl_end]
            if between.strip() == "":
                # The trailing docstring belongs to NEXT decl. Move decl_end back.
                # But only if the docstring is AFTER the current decl's body.
                if last_ds.start() > m.end():
                    decl_end = last_ds.start()
                    # Strip trailing whitespace immediately after.
                    while decl_end > m.end() and source[decl_end - 1] in (" ", "\t", "\n"):
                        decl_end -= 1

        return (block_start, decl_end, source[block_start:decl_end])
    return None


def find_file(fqn: str) -> Path | None:
    """Find which Proofs/*.lean file contains the decl."""
    name, module_hint = parse_fqn(fqn)
    parts = name.split(".")
    candidates = [".".join(parts[k:]) for k in range(len(parts))]

    # If we have a module hint from `_private.*` prefix, search that file first.
    search_files: list[Path]
    if module_hint:
        hinted = PROOFS / f"{module_hint}.lean"
        search_files = [hinted] + [p for p in sorted(PROOFS.glob("*.lean")) if p != hinted and p.name != "Scratch.lean"]
    else:
        search_files = [p for p in sorted(PROOFS.glob("*.lean")) if p.name != "Scratch.lean"]

    for path in search_files:
        try:
            src = path.read_text()
        except Exception:
            continue
        for cand in candidates:
            pattern = re.compile(
                rf"^[ \t]*(?:private\s+|@\[[^\]]*\]\s+)*(?:theorem|lemma)\s+{re.escape(cand)}\b",
                re.MULTILINE,
            )
            if pattern.search(src):
                return path
    return None


def append_to_scratch(blocks: list[tuple[str, str]]) -> None:
    """Append blocks (origin, content) to Scratch.lean before `end Aiur.Scratch`."""
    src = SCRATCH.read_text()
    # Find `end Scratch` or `end Aiur.Scratch`.
    end_marker = re.search(r"^end Scratch\s*$", src, re.MULTILINE)
    if end_marker is None:
        end_marker = re.search(r"^end Aiur\.Scratch\s*$", src, re.MULTILINE)
    if end_marker is None:
        # Append at end before any final `end`.
        insert_pos = len(src)
    else:
        insert_pos = end_marker.start()

    chunks: list[str] = []
    for origin, content in blocks:
        chunks.append(f"\n-- From: {origin}\n{content.strip()}\n")
    new_src = src[:insert_pos] + "".join(chunks) + src[insert_pos:]
    SCRATCH.write_text(new_src)


def lake_build() -> tuple[bool, str]:
    """Run lake build, return (ok, output)."""
    r = subprocess.run(
        ["lake", "build"], cwd=ROOT, capture_output=True, text=True, timeout=600
    )
    return (r.returncode == 0, r.stdout + r.stderr)


def parse_failing_constants(build_output: str) -> list[str]:
    """Extract constant names from lake-build error messages."""
    # Common patterns:
    #   error: ... unknown identifier 'Foo.bar'
    #   error: ... unknown constant 'Foo.bar'
    pats = [
        re.compile(r"unknown identifier '([^']+)'"),
        re.compile(r"unknown constant '([^']+)'"),
        re.compile(r"`([A-Z][A-Za-z0-9_.]+)`.*not found", re.IGNORECASE),
    ]
    names = set()
    for line in build_output.splitlines():
        for p in pats:
            for m in p.finditer(line):
                names.add(m.group(1))
    return sorted(names)


def attempt_batch(file_path: Path, fqns: list[str]) -> bool:
    """Attempt to move a batch of orphans for one file. Returns True if build green."""
    src = file_path.read_text()
    blocks_to_move: list[tuple[str, str]] = []
    cuts: list[tuple[int, int]] = []

    for fqn in fqns:
        result = find_decl(src, fqn)
        if result is None:
            continue
        start, end, content = result
        line_no = src[:start].count("\n") + 1
        origin = f"{file_path.name}:L{line_no}"
        blocks_to_move.append((origin, content))
        cuts.append((start, end))

    if not cuts:
        return True

    original_src = src
    original_scratch = SCRATCH.read_text()
    cuts.sort(reverse=True)
    new_src = src
    for s, e in cuts:
        new_src = new_src[:s] + new_src[e:]
    file_path.write_text(new_src)
    append_to_scratch(blocks_to_move)
    ok, _ = lake_build()
    if ok:
        return True
    # Revert.
    file_path.write_text(original_src)
    SCRATCH.write_text(original_scratch)
    return False


def process_file(file_path: Path, fqns: list[str], dry_run: bool) -> tuple[int, list[str]]:
    """Process all orphans for a single file. Recursively binary-split on break."""
    if dry_run:
        # Dry run: just count located decls.
        src = file_path.read_text()
        cnt = sum(1 for fqn in fqns if find_decl(src, fqn) is not None)
        return (cnt, [])

    if not fqns:
        return (0, [])

    # Try the whole batch first.
    if attempt_batch(file_path, fqns):
        # Compute moved count by checking Scratch growth.
        return (len(fqns), [])

    # Failed. If small, drop it (avoid slow per-singleton builds).
    if len(fqns) <= 4:
        return (0, fqns)

    # Binary split.
    mid = len(fqns) // 2
    first = fqns[:mid]
    second = fqns[mid:]
    moved_a, restored_a = process_file(file_path, first, dry_run)
    moved_b, restored_b = process_file(file_path, second, dry_run)
    return (moved_a + moved_b, restored_a + restored_b)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--limit", type=int, default=None, help="Process at most N files")
    ap.add_argument("--file", type=str, default=None, help="Process only this source file")
    args = ap.parse_args()

    fqns = ORPHAN_LIST.read_text().splitlines()
    fqns = [f.strip() for f in fqns if f.strip() and not f.strip().startswith("#")]
    print(f"Total orphans to migrate: {len(fqns)}", file=sys.stderr)

    # Group by file.
    by_file: dict[Path, list[str]] = defaultdict(list)
    unfound: list[str] = []
    for fqn in fqns:
        f = find_file(fqn)
        if f is None:
            unfound.append(fqn)
        else:
            by_file[f].append(fqn)

    print(f"Located in {len(by_file)} files; unfound: {len(unfound)}", file=sys.stderr)
    if unfound[:5]:
        print(f"  unfound sample: {unfound[:5]}", file=sys.stderr)

    # Process smallest files first.
    sorted_files = sorted(by_file.items(), key=lambda kv: len(kv[1]))
    if args.file:
        sorted_files = [(p, fs) for p, fs in sorted_files if p.name == args.file]
    if args.limit:
        sorted_files = sorted_files[: args.limit]

    total_moved = 0
    total_restored = 0
    for path, fs in sorted_files:
        print(f"Processing {path.name}: {len(fs)} orphans...", file=sys.stderr)
        moved, restored = process_file(path, fs, args.dry_run)
        total_moved += moved
        total_restored += len(restored)
        print(f"  moved={moved}, restored={len(restored)}", file=sys.stderr)

    print(f"\nDone. Total moved: {total_moved}, restored: {total_restored}", file=sys.stderr)


if __name__ == "__main__":
    main()
