#!/usr/bin/env python3
"""Fail-closed coverage check for docs/trusted-externs.json.

The ledger is intentionally hand-reviewed. This script derives the current
foreign/build surface from source and lock metadata and rejects drift; it does
not generate or silently refresh the ledger.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path
from typing import NoReturn


class LedgerError(Exception):
    pass


def reject(message: str) -> NoReturn:
    raise LedgerError(message)


def need(condition: bool, message: str) -> None:
    if not condition:
        reject(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(path: Path) -> dict:
    try:
        with path.open("r", encoding="utf-8") as stream:
            value = json.load(stream)
    except (OSError, json.JSONDecodeError) as error:
        reject(f"cannot read JSON {path}: {error}")
    need(isinstance(value, dict), f"{path} must contain a JSON object")
    return value


def parse_dependency_roots(values: list[str]) -> dict[str, Path]:
    roots: dict[str, Path] = {}
    for value in values:
        name, separator, raw_path = value.partition("=")
        need(bool(separator and name and raw_path), f"bad --dependency-root {value!r}; use NAME=PATH")
        need(name not in roots, f"duplicate --dependency-root for {name}")
        roots[name] = Path(raw_path).resolve()
    return roots


def strip_lean_comments(text: str, *, blank_strings: bool = False) -> str:
    """Blank `--` line comments and nested `/- ... -/` blocks, preserving text
    length and newlines so line numbers survive. String literals are kept
    (extern symbols live inside them) unless blank_strings is set. This is a
    pragmatic scanner, not a Lean parser; downstream checks fail closed on
    anything it surfaces."""
    out: list[str] = []
    index = 0
    length = len(text)
    depth = 0
    in_string = False

    def blank(span: str) -> None:
        out.append("".join(char if char == "\n" else " " for char in span))

    while index < length:
        char = text[index]
        pair = text[index : index + 2]
        if depth > 0:
            if pair == "/-":
                depth += 1
                blank(pair)
                index += 2
            elif pair == "-/":
                depth -= 1
                blank(pair)
                index += 2
            else:
                blank(char)
                index += 1
            continue
        if in_string:
            if char == "\\" and index + 1 < length:
                span = text[index : index + 2]
                blank(span) if blank_strings else out.append(span)
                index += 2
                continue
            if char == '"':
                in_string = False
                out.append(char)
                index += 1
                continue
            blank(char) if blank_strings else out.append(char)
            index += 1
            continue
        if char == '"':
            in_string = True
            out.append(char)
            index += 1
            continue
        if text[index : index + 3] == "'\"'":
            # A double-quote character literal must not toggle string state.
            out.append("' '" if blank_strings else "'\"'")
            index += 3
            continue
        if pair == "/-":
            depth += 1
            blank(pair)
            index += 2
            continue
        if pair == "--":
            end = text.find("\n", index)
            end = length if end == -1 else end
            blank(text[index:end])
            index = end
            continue
        out.append(char)
        index += 1
    return "".join(out)


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


LEAN_NAME = r"[A-Za-z_][A-Za-z0-9_.'!?]*"
IMPORT_PATTERN = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)", re.MULTILINE)
# Any attribute list mentioning extern, in @[...] or attribute [...] form.
EXTERN_ATTRIBUTE_PATTERN = re.compile(
    r"@\[[^\]]*\bextern\b[^\]]*\]|\battribute\s*\[[^\]]*\bextern\b[^\]]*\]"
)
EXTERN_SYMBOL_PATTERN = re.compile(r"\bextern\b\s*(?:[0-9]+\s+)?\"([^\"]+)\"")
EXTERN_DECLARATION_PATTERN = re.compile(
    r"@\[(?P<attributes>[^\]]*\bextern\b[^\]]*)\]\s*"
    r"(?:(?:public|protected|private|unsafe|partial|noncomputable|meta)\s+)*"
    r"(?:opaque|def)\s+(?P<name>" + LEAN_NAME + r")"
)
EXTERN_ATTRIBUTE_COMMAND_PATTERN = re.compile(
    r"\battribute\s*\[(?P<attributes>[^\]]*\bextern\b[^\]]*)\]"
    r"(?P<names>(?:[ \t]+" + LEAN_NAME + r")+)"
)


def extern_declarations(path: Path, text: str) -> list[tuple[str, str]]:
    """Every (foreign symbol, declared Lean name) bound by an `@[extern ...]`
    opaque/def declaration or an `attribute [extern ...]` command in
    comment-stripped source. An extern attribute this scan cannot account for
    is rejected rather than skipped."""
    declarations: list[tuple[str, str]] = []
    explained: set[int] = set()

    def symbol_of(attributes: str, offset: int) -> str:
        match = EXTERN_SYMBOL_PATTERN.search(attributes)
        need(
            match is not None,
            f"{path}:{line_of(text, offset)}: extern attribute without an explicit symbol string is not auditable",
        )
        return match.group(1)

    for match in EXTERN_DECLARATION_PATTERN.finditer(text):
        declarations.append((symbol_of(match.group("attributes"), match.start()), match.group("name")))
        explained.add(match.start())
    for match in EXTERN_ATTRIBUTE_COMMAND_PATTERN.finditer(text):
        symbol = symbol_of(match.group("attributes"), match.start())
        declarations.extend((symbol, name) for name in match.group("names").split())
        explained.add(match.start())
    for match in EXTERN_ATTRIBUTE_PATTERN.finditer(text):
        need(
            match.start() in explained,
            f"{path}:{line_of(text, match.start())}: unrecognized extern attribute form "
            f"(not an opaque/def declaration or an attribute command): {match.group(0)!r}",
        )
    return declarations


LAKE_TARGET_PATTERN = re.compile(
    r"^[ \t]*(?P<kind>lean_lib|lean_exe)\s+"
    r"(?P<name>«[^»]+»|[A-Za-z_][A-Za-z0-9_'-]*)(?:\s+where)?",
    re.MULTILINE,
)
LAKE_MODULE_PATTERN = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*)")


def lakefile_roots(root: Path) -> list[tuple[str, str]]:
    """Read the controlled `lean_lib`/`lean_exe` subset of lakefile.lean.

    The configuration file is itself integrity-pinned. We still derive the
    source roots from its target declarations so a new executable or top-level
    library cannot escape the Lean source inventory after a reviewed pin
    update. Unsupported or empty root spellings fail closed.
    """
    lakefile = root / "lakefile.lean"
    need(lakefile.is_file(), f"lakefile.lean is missing under {root}")
    text = strip_lean_comments(lakefile.read_text(encoding="utf-8"))
    matches = list(LAKE_TARGET_PATTERN.finditer(text))
    need(matches, "lakefile.lean declares no lean_lib/lean_exe roots; refusing an empty source inventory")
    need(
        len(matches) == len(re.findall(r"\b(?:lean_lib|lean_exe)\b", text)),
        "lakefile.lean contains a lean_lib/lean_exe declaration outside the auditable syntax",
    )

    roots: list[tuple[str, str]] = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        section = text[match.end() : end]
        name = match.group("name").removeprefix("«").removesuffix("»")
        source_match = re.search(r'\bsrcDir\s*:=\s*"([^"\n]+)"', section)
        source_dir = source_match.group(1) if source_match else "."
        roots_match = re.search(r"\broots\s*:=\s*#\[(.*?)\]", section, re.DOTALL)
        root_match = re.search(r"\broot\s*:=\s*`([A-Za-z_][A-Za-z0-9_'.]*)", section)
        need(
            not (roots_match and root_match),
            f"lakefile.lean target {name} declares both root and roots",
        )
        if roots_match:
            modules = LAKE_MODULE_PATTERN.findall(roots_match.group(1))
            need(modules, f"lakefile.lean target {name} has an empty or unsupported roots field")
        elif root_match:
            modules = [root_match.group(1)]
        else:
            need(
                re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name) is not None,
                f"lakefile.lean target {name!r} needs an explicit root",
            )
            modules = [name]
        roots.extend((source_dir, module) for module in modules)
    return roots


def lean_sources(root: Path) -> list[Path]:
    sources: set[Path] = set()
    for source_dir, module in lakefile_roots(root):
        base = root / source_dir
        relative = Path(module.replace(".", "/"))
        module_file = base / relative.with_suffix(".lean")
        module_dir = base / relative
        found: list[Path] = [module_file] if module_file.is_file() else []
        if module_dir.is_dir():
            found.extend(module_dir.rglob("*.lean"))
        need(
            bool(found),
            f"lakefile.lean root {module} has no Lean sources ({module_file} or {module_dir}/)",
        )
        sources.update(found)
    need(bool(sources), f"no Lean sources found below {root}")
    return sorted(sources)


def source_texts(paths: list[Path]) -> dict[Path, str]:
    return {path: path.read_text(encoding="utf-8") for path in paths}


AXIOM_DECLARATION_PATTERN = re.compile(
    r"\s*(?:(?:public|protected|private|scoped|local|unsafe|meta|noncomputable)\s+)*axiom\b"
)
SORRY_TOKEN_PATTERN = re.compile(r"(?<![A-Za-z0-9_'.])sorry(?![A-Za-z0-9_'])")
NATIVE_DECIDE_TOKEN_PATTERN = re.compile(r"(?<![A-Za-z0-9_'.])native_decide(?![A-Za-z0-9_'])")


def validate_source_hygiene(root: Path, texts: dict[Path, str]) -> None:
    """Tripwire, not a parser: no declaration-level axiom, standalone sorry
    token, or native_decide may appear in checked sources outside comments and
    string literals."""
    for path in sorted(texts):
        relative = path.relative_to(root)
        stripped = strip_lean_comments(texts[path], blank_strings=True)
        for number, line in enumerate(stripped.splitlines(), start=1):
            need(
                AXIOM_DECLARATION_PATTERN.match(line) is None,
                f"{relative}:{number}: declaration-level axiom is not allowed in checked sources",
            )
            need(
                SORRY_TOKEN_PATTERN.search(line) is None,
                f"{relative}:{number}: sorry is not allowed in checked sources",
            )
            need(
                NATIVE_DECIDE_TOKEN_PATTERN.search(line) is None,
                f"{relative}:{number}: native_decide is not allowed in checked sources",
            )


def validate_shape(ledger: dict) -> tuple[list[dict], list[dict]]:
    need(ledger.get("schema_version") == 2, "unsupported or missing ledger schema_version")
    interfaces = ledger.get("native_interfaces")
    seeds = ledger.get("seed_and_build_trust")
    need(isinstance(interfaces, list) and interfaces, "native_interfaces must be nonempty")
    need(isinstance(seeds, list) and seeds, "seed_and_build_trust must be nonempty")

    ids: list[str] = []
    for entry in interfaces:
        for field in (
            "id",
            "status",
            "owner",
            "source_kind",
            "lean_module",
            "semantics_assumed",
            "proof_effect",
            "trust_basis",
            "tests",
            "retirement",
        ):
            need(entry.get(field), f"native interface is missing nonempty {field}: {entry!r}")
        source_kind = entry["source_kind"]
        need(source_kind in {"dependency", "project"}, f"{entry['id']} has unknown source_kind {source_kind!r}")
        if source_kind == "dependency":
            for field in ("lake_package", "import_root", "pins"):
                need(entry.get(field), f"dependency native interface {entry['id']} lacks {field}")
        else:
            for field in ("foreign_source", "source_sha256"):
                need(entry.get(field), f"project native interface {entry['id']} lacks {field}")
        retirement = entry["retirement"]
        need(retirement.get("milestone"), f"{entry['id']} has no retirement milestone")
        need(retirement.get("replacement"), f"{entry['id']} has no retirement replacement")
        need(retirement.get("exit_criteria"), f"{entry['id']} has no retirement exit criteria")
        symbols = entry.get("foreign_symbols")
        need(isinstance(symbols, list) and symbols, f"{entry['id']} has no foreign_symbols")
        for symbol in symbols:
            for field in ("lean_name", "symbol", "module", "reachability"):
                need(symbol.get(field), f"{entry['id']} symbol lacks {field}: {symbol!r}")
        ids.append(entry["id"])

    for entry in seeds:
        for field in (
            "id",
            "status",
            "owner",
            "version",
            "current_role",
            "assumption",
            "trust_basis",
            "retirement",
        ):
            need(entry.get(field), f"seed/build entry is missing nonempty {field}: {entry!r}")
        ids.append(entry["id"])

    need(len(ids) == len(set(ids)), "ledger entry ids must be unique")
    modeled = ledger.get("modeled_oracles")
    need(isinstance(modeled, list) and modeled, "modeled_oracles must be nonempty")
    modeled_ids: list[str] = []
    for oracle in modeled:
        for field in ("id", "address", "declaration", "scope", "semantics"):
            need(oracle.get(field), f"modeled oracle is missing nonempty {field}: {oracle!r}")
        need(isinstance(oracle.get("arity"), int), f"modeled oracle has non-integer arity: {oracle!r}")
        coherence = oracle.get("address_coherence")
        need(isinstance(coherence, dict), f"modeled oracle lacks address_coherence: {oracle!r}")
        need(
            coherence.get("status") in {"proved", "stable-key", "unsupported"},
            f"modeled oracle has unknown address-coherence status: {oracle!r}",
        )
        need(coherence.get("evidence"), f"modeled oracle lacks coherence evidence: {oracle!r}")
        if coherence["status"] != "unsupported":
            need(coherence.get("fixture"), f"modeled oracle lacks a coherence fixture: {oracle!r}")
        need(oracle.get("native_code") is False, f"modeled oracle is marked native: {oracle!r}")
        need(oracle.get("production_approved") is False, f"modeled oracle is production-approved: {oracle!r}")
        modeled_ids.append(oracle["id"])
    need(len(modeled_ids) == len(set(modeled_ids)), "modeled oracle ids must be unique")
    need(not set(ids) & set(modeled_ids), "modeled oracle ids overlap trusted interface/build ids")
    return interfaces, seeds


def validate_integrity(root: Path, ledger: dict) -> None:
    integrity = ledger.get("integrity", {})
    tracked = integrity.get("tracked_files")
    need(isinstance(tracked, dict) and tracked, "integrity.tracked_files must be nonempty")
    for relative, expected in sorted(tracked.items()):
        path = root / relative
        need(path.is_file(), f"integrity input is missing: {relative}")
        actual = sha256(path)
        need(actual == expected, f"{relative} changed: ledger {expected}, actual {actual}")

    lock = read_json(root / "flake.lock")
    actual_nodes = {
        name: node["locked"]["rev"]
        for name, node in lock.get("nodes", {}).items()
        if isinstance(node, dict)
        and isinstance(node.get("locked"), dict)
        and isinstance(node["locked"].get("rev"), str)
    }
    expected_nodes = integrity.get("flake_nodes")
    need(actual_nodes == expected_nodes, f"flake node/revision inventory drifted:\nledger={expected_nodes}\nactual={actual_nodes}")


def validate_lake_and_imports(root: Path, ledger: dict, interfaces: list[dict], texts: dict[Path, str]) -> None:
    manifest = read_json(root / "lake-manifest.json")
    packages = manifest.get("packages", [])
    actual_packages = {package["name"]: package.get("rev") for package in packages}
    dependency_interfaces = [entry for entry in interfaces if entry["source_kind"] == "dependency"]
    expected_packages = {
        entry["lake_package"]: entry["pins"].get("lake_rev")
        for entry in dependency_interfaces
    }
    need(
        actual_packages == expected_packages,
        f"Lake dependency inventory drifted:\nledger={expected_packages}\nactual={actual_packages}",
    )

    local_roots = set(ledger.get("policy", {}).get("local_import_roots", []))
    need(local_roots, "policy.local_import_roots must be nonempty")
    actual_external_roots = {
        module.split(".", 1)[0]
        for text in texts.values()
        for module in IMPORT_PATTERN.findall(text)
        if module.split(".", 1)[0] not in local_roots
    }
    expected_external_roots = {entry["import_root"] for entry in dependency_interfaces}
    need(
        actual_external_roots == expected_external_roots,
        f"external Lean import roots drifted:\nledger={expected_external_roots}\nactual={actual_external_roots}",
    )

    all_source = "\n".join(texts.values())
    for entry in interfaces:
        module = entry["lean_module"]
        call_pattern = re.compile(rf"\b{re.escape(module)}\.[A-Za-z_][A-Za-z0-9_]*")
        actual_calls = set(call_pattern.findall(all_source))
        expected_calls = set(entry.get("project_entrypoints", []))
        need(
            actual_calls == expected_calls,
            f"qualified uses of {module} drifted:\nledger={expected_calls}\nactual={actual_calls}",
        )


def dependency_root(
    project_root: Path,
    manifest: dict,
    overrides: dict[str, Path],
    package: str,
) -> Path:
    if package in overrides:
        return overrides[package]
    packages_dir = manifest.get("packagesDir", ".lake/packages")
    return (project_root / packages_dir / package).resolve()


C_COMMENT_OR_LITERAL_PATTERN = re.compile(
    r"//[^\n]*|/\*.*?\*/|\"(?:\\.|[^\"\\])*\"|'(?:\\.|[^'\\])*'",
    re.DOTALL,
)
C_EXPORT_PATTERN = re.compile(
    r"\bLEAN_EXPORT\b(?:(?![;{}]).)*?\b([A-Za-z_][A-Za-z0-9_]*)\s*\(",
    re.DOTALL,
)


def strip_c_comments_and_literals(text: str) -> str:
    return C_COMMENT_OR_LITERAL_PATTERN.sub(
        lambda match: "".join(char if char == "\n" else " " for char in match.group(0)),
        text,
    )


def validate_reachability(entry: dict, imported_modules: set[str]) -> None:
    for symbol in entry["foreign_symbols"]:
        claims_import = symbol["reachability"].startswith("imported")
        claims_unimported = symbol["reachability"].startswith("present, unimported")
        need(
            claims_import or claims_unimported,
            f"{entry['id']} symbol {symbol['symbol']} reachability must start with "
            f"'imported' or 'present, unimported': {symbol['reachability']!r}",
        )
        need(
            claims_import == (symbol["module"] in imported_modules),
            f"{entry['id']} symbol {symbol['symbol']} reachability disagrees with project imports "
            f"of {symbol['module']}: {symbol['reachability']!r}",
        )


def validate_native_interfaces(
    root: Path,
    ledger: dict,
    interfaces: list[dict],
    texts: dict[Path, str],
    overrides: dict[str, Path],
) -> None:
    manifest = read_json(root / "lake-manifest.json")
    flake_lock = read_json(root / "flake.lock")
    stripped_texts = {path: strip_lean_comments(text) for path, text in texts.items()}
    project_interfaces = [entry for entry in interfaces if entry["source_kind"] == "project"]
    dependency_interfaces = [entry for entry in interfaces if entry["source_kind"] == "dependency"]

    actual_project_symbols: set[tuple[str, str, str]] = set()
    for path, text in stripped_texts.items():
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        for symbol, declared_name in extern_declarations(path, text):
            lean_name = declared_name if "." in declared_name else f"{module}.{declared_name}"
            actual_project_symbols.add((module, lean_name, symbol))
    expected_project_symbols = {
        (symbol["module"], symbol["lean_name"], symbol["symbol"])
        for entry in project_interfaces
        for symbol in entry["foreign_symbols"]
    }
    need(
        actual_project_symbols == expected_project_symbols,
        "project extern inventory drifted:\n"
        f"ledger={sorted(expected_project_symbols)}\nactual={sorted(actual_project_symbols)}",
    )

    imported_modules = {
        module for text in stripped_texts.values() for module in IMPORT_PATTERN.findall(text)
    }

    lakefile_text = strip_lean_comments((root / "lakefile.lean").read_text(encoding="utf-8"))
    actual_foreign_sources = set(re.findall(r'"([^"\n]+\.c)"', lakefile_text))
    expected_foreign_sources = {entry["foreign_source"] for entry in project_interfaces}
    need(
        actual_foreign_sources == expected_foreign_sources,
        "project foreign-source inventory drifted:\n"
        f"ledger={sorted(expected_foreign_sources)}\nactual={sorted(actual_foreign_sources)}",
    )
    for entry in project_interfaces:
        module_path = root / (entry["lean_module"].replace(".", "/") + ".lean")
        need(module_path.is_file(), f"project native module source is missing: {module_path}")
        source_path = (root / entry["foreign_source"]).resolve()
        need(root == source_path or root in source_path.parents, f"foreign source escapes project root: {source_path}")
        need(source_path.is_file(), f"project foreign source is missing: {source_path}")
        need(
            sha256(source_path) == entry["source_sha256"],
            f"foreign source hash drifted for {entry['id']}: actual {sha256(source_path)}",
        )
        need(
            entry["foreign_source"] in lakefile_text,
            f"project foreign source is not referenced by lakefile.lean: {entry['foreign_source']}",
        )
        actual_exports = set(C_EXPORT_PATTERN.findall(strip_c_comments_and_literals(
            source_path.read_text(encoding="utf-8")
        )))
        expected_exports = {symbol["symbol"] for symbol in entry["foreign_symbols"]}
        need(
            actual_exports == expected_exports,
            f"{entry['id']} C export inventory drifted:\n"
            f"ledger={sorted(expected_exports)}\nactual={sorted(actual_exports)}",
        )
        validate_reachability(entry, imported_modules)

    for entry in dependency_interfaces:
        package_root = dependency_root(root, manifest, overrides, entry["lake_package"])
        need(package_root.is_dir(), f"dependency source is missing for {entry['lake_package']}: {package_root}")
        module_path = package_root / (entry["lean_module"].replace(".", "/") + ".lean")
        need(module_path.is_file(), f"native module source is missing: {module_path}")

        # Audit the entire package source tree, not just the imported entry
        # module: a sibling module's externs are one lakefile line from
        # linkable and must not drift silently.
        package_files = sorted(
            path
            for path in package_root.rglob("*.lean")
            if not any(part.startswith(".") for part in path.relative_to(package_root).parts)
        )
        need(bool(package_files), f"no Lean sources found in dependency {entry['lake_package']}: {package_root}")
        actual_symbols: set[tuple[str, str, str]] = set()
        for path in package_files:
            module = ".".join(path.relative_to(package_root).with_suffix("").parts)
            declarations = extern_declarations(
                path, strip_lean_comments(path.read_text(encoding="utf-8"))
            )
            for symbol, declared_name in declarations:
                lean_name = declared_name if "." in declared_name else f"{module}.{declared_name}"
                actual_symbols.add((module, lean_name, symbol))
        expected_symbols = {
            (symbol["module"], symbol["lean_name"], symbol["symbol"])
            for symbol in entry["foreign_symbols"]
        }
        need(
            actual_symbols == expected_symbols,
            f"{entry['lake_package']} package-tree extern inventory drifted:\n"
            f"ledger={sorted(expected_symbols)}\nactual={sorted(actual_symbols)}",
        )

        validate_reachability(entry, imported_modules)

        cargo = entry.get("cargo_lock")
        if cargo:
            cargo_path = package_root / cargo["path"]
            need(cargo_path.is_file(), f"Cargo lockfile is missing: {cargo_path}")
            need(
                sha256(cargo_path) == cargo["sha256"],
                f"Cargo lockfile hash drifted for {entry['id']}: actual {sha256(cargo_path)}",
            )
            with cargo_path.open("rb") as stream:
                cargo_data = tomllib.load(stream)
            package_records = cargo_data.get("package", [])
            names = [record["name"] for record in package_records]
            need(len(names) == len(set(names)), "Cargo graph now has duplicate package names; ledger schema must record name+version keys")
            actual_packages = {record["name"]: record["version"] for record in package_records}
            need(
                actual_packages == cargo["packages"],
                f"Cargo package inventory drifted for {entry['id']}:\nledger={cargo['packages']}\nactual={actual_packages}",
            )
            by_name = {record["name"]: record for record in package_records}
            need(by_name["blake3"]["version"] == entry["pins"]["blake3_version"], "BLAKE3 crate version pin drifted")
            lean_ffi_source = by_name["lean-ffi"].get("source", "")
            need(entry["pins"]["lean_ffi_rev"] in lean_ffi_source, "lean-ffi Cargo revision pin drifted")

        node_name = entry["pins"].get("flake_node")
        node = flake_lock.get("nodes", {}).get(node_name, {})
        need(node.get("locked", {}).get("rev") == entry["pins"]["lake_rev"], f"flake/Lake pin mismatch for {entry['id']}")
        upstream = flake_lock.get("nodes", {}).get("blake3", {})
        need(
            upstream.get("locked", {}).get("rev") == entry["pins"]["blake3_upstream_rev"],
            "upstream BLAKE3 source revision pin drifted",
        )


def validate_seed_versions(root: Path, seeds: list[dict], gmp_version: str | None) -> None:
    by_id = {entry["id"]: entry for entry in seeds}
    toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    match = re.fullmatch(r"leanprover/lean4:v(.+)", toolchain)
    need(match is not None, f"unrecognized lean-toolchain format: {toolchain!r}")
    need(by_id["lean-seed-runtime"]["version"] == match.group(1), "Lean seed version disagrees with lean-toolchain")
    if gmp_version is not None:
        need(by_id["gmp-seed"]["version"] == gmp_version, f"GMP ledger version differs from Nix: {gmp_version}")


def validate_ci(root: Path, ledger: dict) -> None:
    workflows = sorted((root / ".github" / "workflows").glob("*.y*ml"))
    need(bool(workflows), "no CI workflows found")
    uses_pattern = re.compile(r"^\s*(?:-\s+)?uses:\s*(.+?)\s*$")
    commit_pattern = re.compile(r"[0-9a-f]{40}")
    actual: set[tuple[str, str]] = set()
    for workflow in workflows:
        relative = workflow.relative_to(root)
        for number, line in enumerate(workflow.read_text(encoding="utf-8").splitlines(), start=1):
            match = uses_pattern.match(line)
            if match is None:
                continue
            reference = re.sub(r"\s+#.*$", "", match.group(1)).strip().strip("\"'")
            repository, separator, commit = reference.partition("@")
            need(
                bool(repository) and bool(separator) and commit_pattern.fullmatch(commit) is not None,
                f"{relative}:{number}: CI action reference is not pinned to a 40-hex commit: {reference!r}",
            )
            actual.add((repository, commit))
    expected = {(entry["repository"], entry["commit"]) for entry in ledger.get("ci_actions", [])}
    need(actual == expected, f"CI action inventory drifted:\nledger={expected}\nactual={actual}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="project source root")
    parser.add_argument(
        "--dependency-root",
        action="append",
        default=[],
        metavar="NAME=PATH",
        help="override a Lake dependency source root (repeatable)",
    )
    parser.add_argument("--gmp-version", help="Nix-evaluated pkgs.gmp.version")
    arguments = parser.parse_args()

    root = arguments.root.resolve()
    try:
        ledger = read_json(root / "docs" / "trusted-externs.json")
        interfaces, seeds = validate_shape(ledger)
        sources = lean_sources(root)
        texts = source_texts(sources)
        validate_integrity(root, ledger)
        validate_source_hygiene(root, texts)
        validate_lake_and_imports(root, ledger, interfaces, texts)
        validate_native_interfaces(
            root,
            ledger,
            interfaces,
            texts,
            parse_dependency_roots(arguments.dependency_root),
        )
        validate_seed_versions(root, seeds, arguments.gmp_version)
        validate_ci(root, ledger)
    except (LedgerError, OSError, KeyError, TypeError, tomllib.TOMLDecodeError) as error:
        print(f"trusted-extern ledger check failed: {error}", file=sys.stderr)
        return 1

    symbol_count = sum(len(entry["foreign_symbols"]) for entry in interfaces)
    cargo_count = sum(len(entry.get("cargo_lock", {}).get("packages", {})) for entry in interfaces)
    print(
        "trusted-extern ledger ok: "
        f"{len(interfaces)} native interface, {symbol_count} symbols, "
        f"{cargo_count} Cargo packages, {len(seeds)} seed/build entries"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
