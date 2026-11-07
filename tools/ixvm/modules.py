"""Split the reviewed legacy adaptation into ordinary Aiur modules.

This is source organization, not an Aiur compiler pass. Definitions retain
their bodies, type/constructor order, and inline markers. The inverse rename
is checked for every declaration. The certified module linker then checks all
cross-module references. Source manifests are also consumed by the exporters.
"""
from collections import OrderedDict
from dataclasses import dataclass
import json
from pathlib import Path
import re

import adapt


@dataclass
class Declaration:
    kind: str
    name: str
    source: str


def declarations(source):
    hidden, saved = adapt.strings(adapt.uncomments(source))
    result = []
    pattern = r'(?m)^\s*(?:inline )?(fn|enum|type|table|map|const) (\w+)'
    end = 0
    for m in re.finditer(pattern, hidden):
        if m.start() < end:
            continue
        if m[1] in ('type', 'map', 'const'):
            end, depth = m.end(), 0
            while end < len(hidden):
                if hidden[end] in '([':
                    depth += 1
                elif hidden[end] in ')]':
                    depth -= 1
                elif hidden[end] == ';' and depth == 0:
                    break
                end += 1
            end += 1
        else:
            end = adapt.balance_end(hidden, hidden.index('{', m.end()))
        body = hidden[m.start():end].strip()
        for i, text in enumerate(saved):
            body = body.replace(f'"STRING_{i}"', text)
        result.append(Declaration(m[1], m[2], body))
    names = [d.name for d in result]
    if len(names) != len(set(names)):
        raise ValueError('duplicate declaration in source bundle')
    return result


# These bodies are shared verbatim, modulo names, with the application ports.
SHARED = {
    **{'list_' + n: 'Lists::' + n for n in
       ['length', 'concat', 'lookup', 'lookup_or_default', 'drop', 'take',
        'snoc', 'reverse', 'reverse_acc']},
    'checked_depth_succ': 'WordLists::checked_depth_succ',
    'list_depth_checked': 'WordLists::depth_checked',
    'list_length_u64': 'WordLists::length_u64',
    'list_lookup_u64': 'WordLists::lookup_u64',
    'b3_pack_w': 'Blake3::pack_word',
    'b3_pack': 'Blake3::pack_digest',
    'address_eq': 'Bytes::address_eq',
    'address_eq_tail': 'Bytes::address_eq_tail',
    **{name: 'Goldilocks::' + name for name in
       ['gl_val', 'gl_lt_p', 'gl_to_bytes', 'gl_inverse',
        'eg_add', 'eg_sub', 'eg_neg', 'eg_mul', 'eg_inverse', 'eg_div', 'eg_eq']},
}

SHARED_TYPES = {
    'List': 'Lists::List', 'Option': 'Options::Option',
    'U8': 'UInt8::U8', 'U32': 'UInt32::U32', 'U64': 'UInt64::U64',
    'Layer': 'Blake3::Layer', 'Addr': 'Bytes::AddressRef', 'ByteStream': 'Bytes::Stream',
    'Goldilocks': 'Goldilocks::Goldilocks', 'ExtGoldilocks': 'Goldilocks::ExtGoldilocks',
}


def origins(parts):
    """Retain the original subsystem ownership through the lexical adapter."""
    result = {}
    for module, source in parts:
        for m in re.finditer(r'(?m)^\s*(?:inline )?(?:fn|enum|type|table|map) (\w+)',
                             adapt.uncomments(source)):
            result[m[1]] = module
    return result


def tokens(source):
    return re.findall(r'"(?:[^"\\]|\\.)*"|\w+|[^\s]', adapt.uncomments(source))


def native_memory(source):
    """Eliminate the legacy syntax adapters `load`/`store`, both inline
    identity wrappers around Aiur's existing `*`/`&` constructs."""
    hidden, saved = adapt.strings(source)
    # Work inside out so nested calls do not need a recursive Python parser.
    while matches := list(re.finditer(r'(?<![\w:])\b(load|store)\(', hidden)):
        m = matches[-1]
        end, depth = m.end(), 1
        while depth:
            if hidden[end] == '(':
                depth += 1
            elif hidden[end] == ')':
                depth -= 1
            end += 1
        op = '*' if m[1] == 'load' else '&'
        hidden = hidden[:m.start()] + '(' + op + hidden[m.end()-1:end] + ')' + hidden[end:]
    for i, text in enumerate(saved):
        hidden = hidden.replace(f'"STRING_{i}"', text)
    return hidden


def relocate(decl, names, owner):
    """Only global type paths and call sites change; locals/strings do not.

    The reviewed input uses uppercase type names and lowercase callables.
    Refuse type-parameter shadowing instead of guessing how to rewrite it.
    """
    hidden, saved = adapt.strings(decl.source)
    match = re.match(r'(?:inline )?\w+ (\w+)', hidden)
    assert match and match[1] == decl.name
    header, body = hidden[:match.end()], hidden[match.end():]
    constructors = set()
    if decl.kind == 'enum':
        depth, want = 0, False
        for token in re.finditer(r'\w+|[^\s]', body[body.index('{'):]):
            at = body.index('{') + token.start()
            if token[0] == '{':
                want = True
            elif token[0] == '(':
                depth += 1
            elif token[0] == ')':
                depth -= 1
            elif token[0] == ',' and depth == 0:
                want = True
            elif want and re.fullmatch(r'\w+', token[0]):
                constructors.add(at)
                want = False
    for name in names:
        if name[0].isupper() and re.search(r'<[^>]*\b' + name + r'\b[^>]*>\s*\(', body):
            # Concrete type arguments in calls are fine; only the declaration's
            # own type parameters could shadow a global type.
            params = re.match(r'<([^>]*)>', body)
            if params and name in re.findall(r'\w+', params[1]):
                raise ValueError(f'type parameter shadows {name} in {decl.name}')

    def replacement(m):
        name = m[0]
        if m.start() in constructors:
            return name
        target = names.get(name)
        if target is None:
            return name
        # Uppercase identifiers are type/constructor paths. Lowercase names
        # must be called, not e.g. a let-bound variable named like a function.
        if not name[0].isupper() and not re.match(r'\s*(?:::<[^>]*>)?\(', body[m.end():]):
            return name
        module, member = target.split('::')
        # A module and one of its types may have the same spelling (RBTreeMap).
        # Qualify that type even locally so `Type::Ctor` cannot mean a module
        # constant to the existing frontend.
        return member if module == owner and member != owner else target

    body = re.sub(r'(?<![\w:])\b[A-Za-z_]\w*\b(?!\w)', replacement, body)
    member = names[decl.name].split('::')[1]
    output = header[:match.start(1)] + member + body
    for i, text in enumerate(saved):
        output = output.replace(f'"STRING_{i}"', text)
    return output


def restore(decl, relocated, names, owner):
    """Independent round-trip guard: preserve every non-name source token."""
    hidden, saved = adapt.strings(relocated)
    replacements = {}
    for old, target in names.items():
        module, member = target.split('::')
        replacements[target] = old
        if module == owner:
            replacements[member] = old
    pattern = r'(?<![\w:])(?:' + '|'.join(re.escape(s) for s in
        sorted(replacements, key=len, reverse=True)) + r')(?!\w)'
    restored = re.sub(pattern, lambda m: replacements[m[0]], hidden)
    for i, text in enumerate(saved):
        restored = restored.replace(f'"STRING_{i}"', text)
    original, original_strings = adapt.strings(decl.source)
    original = re.sub(pattern, lambda m: replacements[m[0]], original)
    for i, text in enumerate(original_strings):
        original = original.replace(f'"STRING_{i}"', text)
    if tokens(restored) != tokens(original):
        raise ValueError(f'relocation changed more than names in {decl.name}')


def partition(source, owners, root, entries):
    decls = declarations(source)
    names = {d.name: (SHARED[d.name] if d.name in SHARED else
             SHARED_TYPES[d.name] if d.name in SHARED_TYPES else
             f'{root if d.name in entries else owners.get(d.name, root + "Compat")}::{d.name}')
             for d in decls if d.name not in ('load', 'store')}
    groups = OrderedDict()
    for decl in decls:
        if decl.name in ('load', 'store'):
            continue
        owner = names[decl.name].split('::')[0]
        body = relocate(decl, names, owner)
        restore(decl, body, names, owner)
        if decl.name in SHARED or decl.name in SHARED_TYPES:
            continue
        groups.setdefault(owner, []).append(native_memory(body))
    return groups, {f'{root}::{name}': target for name, target in names.items()}


def render(module, bodies):
    body = '\n\n'.join(bodies)
    # Remove blank lines left by legacy comments, preserving diagnostic strings.
    body = re.sub(r'\n\s*\n\s*\n', '\n\n', body)
    return ('// Generated by tools/ixvm; edit the reviewed adapter or its source.\n'
            f'module {module} {{\n' + '\n'.join('  ' + line if line else ''
            for line in body.splitlines()) + '\n}\n')


def write(path, text, check):
    if check:
        if not path.exists() or path.read_text() != text:
            raise RuntimeError(f'{path} is stale; regenerate the Aiur port')
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


def emit(directory, groups, root, manifest, names, check=False):
    files = []
    for module, bodies in groups.items():
        path = f'{manifest}.aiur' if module == root else f'Modules/{module}.aiur'
        write(directory / path, render(module, bodies), check)
        files.append(path)
    write(directory / f'{manifest}.sources',
          '# Ordered Aiur source bundle; paths are relative to this file.\n' +
          '\n'.join(files) + '\n', check)
    write(directory / f'{manifest}.names.json', json.dumps(names, indent=2, sort_keys=True) + '\n', check)


def read_bundle(path):
    path = Path(path)
    return '\n'.join((path.parent / line.strip()).read_text()
                     for line in path.read_text().splitlines()
                     if line.strip() and not line.strip().startswith('#'))


def shared_bodies(source):
    """Extract reviewed helpers once when creating the shared library."""
    decls = declarations(source)
    names = {d.name: SHARED.get(d.name, 'Source::' + d.name) for d in decls
             if d.name not in ('load', 'store')}
    # Transparent aliases retain their representation at the library boundary.
    names.update(SHARED_TYPES)
    return {d.name: native_memory(relocate(d, names, SHARED[d.name].split('::')[0]))
            for d in decls if d.name in SHARED}


def check_shared(source):
    """The extraction is a refactor: reject drift from the reviewed bodies."""
    paths = {'Lists': 'List', 'WordLists': 'List/Word', 'Blake3': 'Blake3', 'Bytes': 'Bytes',
             'Goldilocks': 'Field/Goldilocks'}
    actual = {}
    for module, path in paths.items():
        text = (adapt.ROOT / f'Aiur/Aiur/Library/{path}.lean').read_text()
        start = text.index(f'module {module} {{')
        end = adapt.balance_end(text, text.index('{', start))
        for decl in declarations(text[start:end]):
            actual[f'{module}::{decl.name}'] = decl.source
    for old, expected in shared_bodies(source).items():
        if tokens(expected) != tokens(actual[SHARED[old]]):
            raise ValueError(f'shared helper drifted from reviewed port: {old}')
