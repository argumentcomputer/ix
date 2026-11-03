#!/usr/bin/env python3
"""Inventory the source port; semantic differences require human review.

This is a reproducibility and coverage check, not an equivalence theorem.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

import adapt
import modules


def functions(source):
    hidden, saved = adapt.strings(adapt.uncomments(source))
    out = {}
    for match in re.finditer(r'\b(?:inline )?fn (\w+)\b[^{}]*\{', hidden):
        body = hidden[match.start():adapt.balance_end(hidden, match.end()-1)]
        for i, value in enumerate(saved):
            body = body.replace(f'"STRING_{i}"', value)
        if match[1] in out:
            raise ValueError(f'duplicate function {match[1]}')
        out[match[1]] = body
    return out


def tokens(source):
    return re.findall(r'"(?:[^"\\]|\\.)*"|\w+|[^\s]', adapt.uncomments(source))


def libraries():
    """Inventory the shared implementations, including checked table maps."""
    inventory, definitions = [], {}
    for module, filename in [('UInt8', 'U8'), ('UInt32', 'U32'), ('UInt64', 'U64'),
                             ('Blake3', 'Blake3'), ('Lists', 'List'), ('Fields', 'Field'),
                             ('WordLists', 'List/Word'), ('Bytes', 'Bytes'),
                             ('Goldilocks', 'Field/Goldilocks')]:
        path = f'Aiur/Aiur/Library/{filename}.lean'
        raw = (adapt.ROOT / path).read_text()
        start = re.search(rf'module {module}(?:\s*:\s*\w+)?\s*\{{', raw)
        assert start, f'missing module {module} in {path}'
        source = raw[start.start():]
        end = re.search(r'\n\}\s*"#?', source)
        assert end, f'missing end of embedded module in {path}'
        source = source[:end.start() + 2]
        assert 'ptr_val(' not in source and not re.search(r'[#@]\w+\(', source)
        bodies = functions(source)
        bodies.update({m[1]: m[0] for m in re.finditer(r'\bmap (\w+)\b[^;]*;', source)})
        for name, body in bodies.items():
            definitions[f'{module}::{name}'] = (path, body)
        inventory.append(dict(path=path, sha256=hashlib.sha256(raw.encode()).hexdigest(),
                              functions_and_maps=sorted(bodies)))
    return inventory, definitions


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ix', type=Path, default=adapt.ROOT)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    parts, files, origins = [], [], {}
    for name in adapt.FILES:
        path = adapt.source_path(name)
        raw = subprocess.check_output(['git', '-C', str(args.ix), 'show', f'{adapt.REVISION}:{path}'], text=True)
        text = raw.split('⟦', 1)[1].split('⟧', 1)[0]
        parts.append(text)
        for fn in functions(text):
            if fn in origins:
                raise ValueError(f'duplicate source function {fn}')
            origins[fn] = path
        files.append(dict(path=path, sha256=hashlib.sha256(raw.encode()).hexdigest()))
    raw = '\n'.join(parts)
    old = functions(raw)
    lexical = functions(adapt.adapt(raw, semantic=False))
    # Audit the semantic adaptation independently of namespace relocation.
    # The actual modular bundle and extracted library bodies must reproduce it.
    port_text, _, owners = adapt.source(args.ix)
    groups, renames = modules.partition(port_text, owners, 'IxVM', adapt.ROOTS)
    modules.emit(adapt.ROOT / 'IxVM/IxVM', groups, 'IxVM', 'Program', renames, check=True)
    modules.check_shared(port_text)
    port = functions(port_text)
    rebuilt, _ = adapt.prune(adapt.adapt(raw) + (adapt.ROOT / 'IxVM/IxVM/Compatibility.aiur').read_text() + (adapt.ROOT / 'IxVM/IxVM/PortCases.aiur').read_text(),
                            adapt.ROOTS)
    assert tokens(port_text) == tokens(rebuilt), 'generated source is stale'
    assert 'ptr_val(' not in port_text and not re.search(r'[#@]\w+\(', port_text)
    rows, diffs = [], []
    for name, body in port.items():
        status = 'adapter' if name not in old else ('lexical-only' if tokens(body) == tokens(lexical[name]) else 'semantic-adaptation')
        calls = re.findall(r'([#@]?)\b(\w+)\s*(?:‹[^›]*›)?\(', old.get(name, ''))
        rows.append(dict(name=name, target=renames.get('IxVM::' + name), origin=origins.get(name), status=status,
                         pointer_comparisons=old.get(name, '').count('ptr_val('),
                         unconstrained_callees=sorted({n for mode, n in calls if mode == '#'}),
                         inlined_callees=sorted({n for mode, n in calls if mode == '@'})))
        if status == 'semantic-adaptation':
            diffs.extend(difflib.unified_diff([x.strip()+'\n' for x in lexical[name].splitlines()], [x.strip()+'\n' for x in body.splitlines()],
                                            fromfile=f'Ix/{name}', tofile=f'new/{name}', n=0))
            diffs.append('\n')
    library_files, definitions = libraries()
    replacements = []
    for name, target in (adapt.LIBRARY_FUNCTIONS | modules.SHARED).items():
        path, body = definitions[target]  # Fail if an adapter names a missing library operation.
        replacements.append(dict(name=name, target=target, origin=origins.get(name), library=path,
                                 definition_sha256=hashlib.sha256(body.encode()).hexdigest()))
        if name in lexical:
            diffs.extend(difflib.unified_diff(
                [x.strip()+'\n' for x in lexical[name].splitlines()],
                [x.strip()+'\n' for x in body.splitlines()],
                fromfile=f'Ix/{name}', tofile=f'{path}:{target}', n=0))
            diffs.append('\n')
    report = dict(source_revision=adapt.REVISION, files=files, functions=rows,
                  library_files=library_files, library_replacements=replacements,
                  totals={s: sum(r['status'] == s for r in rows) for s in ['lexical-only', 'semantic-adaptation', 'adapter']},
                  pointer_operations=0, unconstrained_call_sites=0,
                  note='lexical-only is after normalizing call annotations; unconstrained/inlined call changes are recorded separately; shared replacements are inventoried and diffed, not claimed equivalent by this audit')
    (args.out / 'source-audit.json').write_text(json.dumps(report, indent=2)+'\n')
    (args.out / 'semantic-adaptations.diff').write_text(''.join(diffs).rstrip()+'\n')
    print(json.dumps(report['totals']))
    print('Changed:', ', '.join(r['name'] for r in rows if r['status'] == 'semantic-adaptation'))


if __name__ == '__main__':
    main()
