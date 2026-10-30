#!/usr/bin/env python3
"""Reproduce the recursive verifier with the certified Aiur frontend.

No pointer identities or unconstrained calls survive. Arithmetic advice is
ordinary typed hint data; all original verification assertions remain.
"""
import argparse
import re
import subprocess
from pathlib import Path

import adapt
import modules

ROOT = adapt.ROOT
FILES = ['LegacyAiur/Library/' + name + '.lean' for name in ['Core', 'ByteStream', 'Blake3']]
FILES += ['LegacyMultiStark/' + name + '.lean' for name in
          ['Goldilocks', 'Deserialize', 'SystemDeserialize', 'Pcs', 'Verifier']]
FILES += ['LegacyMultiStark.lean']


def source(aggregate=False):
    parts = []
    for path in FILES + (['Ix/Aggr/Circuit.lean'] if aggregate else []):
        text = subprocess.check_output(['git', '-C', str(ROOT), 'show',
                                       f'{adapt.REVISION}:{path}'], text=True)
        parts.append(text.split('⟦', 1)[1].split('⟧', 1)[0])
    raw = adapt.uncomments('\n'.join(parts))
    if aggregate:
        for name, byte in [('aggr_parse_tree_body', 'tag'), ('aggr_fold_path', 'side'),
                           ('aggr_discharge_choice', 'choice'), ('aggr_get_opt_address', 'tag'),
                           ('ix_aggr', 'shape')]:
            raw = adapt.transform_body(raw, name, lambda s, byte=byte:
                s.replace(f'match {byte} {{', f'match to_field({byte}) {{'))
        raw = re.sub(r'assert_eq!\((tag|format|validator), (0x[0-9a-fA-F]+|\d+)u8,',
                     r'assert_eq!(to_field(\1), \2,', raw)
        raw = raw.replace('assert_eq!(aggr_claim_field(claim, 0), 0,',
                          'assert_eq!(aggr_claim_field(claim, 0), 1,')
        raw = re.sub(r'@b3_pack_w\((\[a\[\d+\], a\[\d+\], a\[\d+\], a\[\d+\]\])\)',
                     r'@b3_pack_w(UInt32::from_bytes(\1))', raw)
        raw = raw.replace('io_get_info(5, raw)',
                          'hint::<(G, G)>("stark.io.address", (5, Blake3::address_to_fields(raw)))')
        raw = raw.replace('io_get_info(6, load(candidate))',
                          'hint::<(G, G)>("stark.io.address", (6, Blake3::address_to_fields(load(candidate))))')
        raw = raw.replace('io_get_info(4, digest)',
                          'hint::<(G, G)>("stark.io.digest", digest)')
    raw = adapt.use_opaque_words(raw)
    raw = raw.replace('unconstrained_g_to_bytes(v)', 'hint::<[G; 8]>("bytes_le", v)')
    raw = re.sub(r'unconstrained_g_inverse\((\w+)\)',
                 r'hint::<G>("goldilocks.inverse", \1)', raw)
    raw = re.sub(r'io_read\((\w+), (\w+), (1|8|64)\)',
                 r'hint::<[G; \3]>("stark.io.read\3", (\1, \2))', raw)
    raw = re.sub(r'io_get_info\((\d+), \[(\w+)\]\)',
                 r'hint::<(G, G)>("stark.io.info", (\1, \2))', raw)
    raw = adapt.replace_body(raw, 'read_byte_stream', '''
      match len {
        0 => store(ListNode.Nil),
        _ =>
          let [byte] = hint::<[G; 1]>("stark.io.read1", (channel, idx));
          let tail = read_byte_stream(channel, idx + 1, len - 1);
          store(ListNode.Cons(u8_from_field_unsafe(byte), tail)),
      }''')
    for name in ['read_preprocessed', 'read_opt_commit']:
        raw = adapt.transform_body(raw, name, lambda s:
            s.replace('match tag {', 'match to_field(tag) {'))
    raw = re.sub(r'assert_eq!\(load\((\w+)\), ListNode\.Nil(?:,\s*"[^"]*")?\)',
                 r'let ListNode.Nil = load(\1)', raw)
    raw = adapt.transform_body(raw, 'b3_w4_onto', lambda s:
        s.replace('{', '{\n    let w = UInt32::to_bytes(w);', 1))
    raw = adapt.transform_body(raw, 'b3_to_digest', lambda s:
        s.replace('{', '{\n    let h = [' + ', '.join(
            f'UInt32::to_bytes(h[{i}])' for i in range(8)) + '];', 1))
    # Word construction at the byte boundary, including MMCS and IO blocks.
    for name in ['b3_lane_chunks', 'b3_io_chunks', 'b3_io', 'b3_lanes',
                 'mmcs_compress', 'b3_rows_chunks', 'b3_rows']:
        def words(body):
            # Every four-element byte array here is a Blake3 word.
            atom = r'(?:\w+\[\d+\](?:\[\d+\])?|\d+u8|u8_from_field_unsafe\(\w+\))'
            pattern = r'\[\s*' + atom + (r'\s*,\s*' + atom) * 3 + r'\s*\]'
            body = re.sub(pattern, lambda m: f'UInt32::from_bytes({m[0]})', body)
            body = body.replace('[[0u8; 4]; 16]', '[UInt32::ZERO; 16]')
            return re.sub(r'match load\(chunk_count\) \{\s*\[0, 0, 0, 0, 0, 0, 0, 0\] =>',
                          'match u64_is_zero(load(chunk_count)) { 1 =>', body)
        raw = adapt.transform_body(raw, name, words)
    raw = raw.replace('eq_zero(ptr_val(list_lookup(cap, capidx)) - ptr_val(root))',
                      'digest_eq(list_lookup(cap, capidx), root)')
    raw = raw.replace('eq_zero(ptr_val(list_lookup(cap, capidx)) - ptr_val(digest))',
                      'digest_eq(list_lookup(cap, capidx), digest)')
    raw = raw.replace('assert_eq!(ptr_val(xd), ptr_val(yd))', 'assert_eq!(digest_eq(xd, yd), 1)')
    raw = raw.replace('assert_eq!(ptr_val(xr), ptr_val(yr))', 'assert_eq!(assert_same_claims(xr, yr), 1)')
    raw = re.sub(r'assert_eq!\(ptr_val\(select_rows_le\(ar, lhs, next_lh\)\),\s*'
                 r'ptr_val\(select_rows_le\(br, lhs, next_lh\)\)\)',
                 'assert_eq!(assert_same_claims(select_rows_le(ar, lhs, next_lh), '
                 'select_rows_le(br, lhs, next_lh)), 1)', raw)
    # These nonrecursive arithmetic helpers were inline in the old verifier.
    for name in ['gl_val', 'gl_lt_p', 'gl_inverse', 'eg_add', 'eg_sub', 'eg_neg',
                 'eg_mul', 'eg_inverse', 'eg_div', 'eg_eq', 'b3_pack', 'b3_pack_w']:
        adapt.INLINE_HELPERS.add(name)
    result = adapt.adapt(raw, semantic=False)
    result += (ROOT / 'MultiStark/MultiStark/Compatibility.aiur').read_text()
    result, names = adapt.prune(result, ['ix_aggr' if aggregate else 'verify_multi_stark_proof'],
                                module='MultiStark', raw_bytes=False)
    if re.search(r'\b(?:ptr_val|unconstrained_\w+|io_read|io_get_info)\(', result):
        raise RuntimeError('recursive verifier retained a native-only operation')
    result = '// Generated by tools/ixvm/recursion.py from the pinned Ix verifier.\n' + result
    return '\n'.join(line.rstrip() for line in result.splitlines()) + '\n', names


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--aggregate', action='store_true')
    args = parser.parse_args()
    # Both roots use one copy of every verifier subsystem. --aggregate is kept
    # for existing automation; either invocation checks/generates both bundles.
    parts = []
    for path in FILES + ['Ix/Aggr/Circuit.lean']:
        text = subprocess.check_output(['git', '-C', str(ROOT), 'show',
                                       f'{adapt.REVISION}:{path}'], text=True)
        component = {'Core': 'StarkCore', 'ByteStream': 'StarkIO', 'Blake3': 'StarkHash',
                     'Goldilocks': 'Goldilocks', 'Deserialize': 'ProofDeserialize',
                     'SystemDeserialize': 'SystemDeserialize', 'Pcs': 'Pcs',
                     'Verifier': 'StarkVerifier', 'LegacyMultiStark': 'MultiStark',
                     'Circuit': 'Aggregation'}[Path(path).stem]
        parts.append((component, text.split('⟦', 1)[1].split('⟧', 1)[0]))
    owners = modules.origins(parts)
    for name in owners:
        if name.startswith('b3_') or name in ('digest_eq',):
            owners[name] = 'StarkHash'
        elif name.startswith('ch_') or name in ('pcs_sample_ext', 'batch_fiat_shamir', 'shard_fiat_shamir'):
            owners[name] = 'Transcript'
        elif name.startswith(('mmcs_', 'frontier_')):
            owners[name] = 'Mmcs'
    standalone, _ = source(False)
    aggregate, _ = source(True)
    modules.check_shared(standalone)
    modules.check_shared(aggregate)
    sg, sn = modules.partition(standalone, owners, 'MultiStark', ['verify_multi_stark_proof'])
    ag, an = modules.partition(aggregate, owners, 'MultiStark', ['ix_aggr'])
    for module in sg.keys() & ag.keys() - {'MultiStark'}:
        common = {}
        for body in sg[module] + ag[module]:
            decl = modules.declarations(body)[0]
            if decl.name in common and modules.tokens(common[decl.name]) != modules.tokens(body):
                raise ValueError(f'different verifier bodies for {module}::{decl.name}')
            common[decl.name] = body
        sg[module] = ag[module] = list(common.values())
    directory = ROOT / 'MultiStark/MultiStark'
    modules.emit(directory, sg, 'MultiStark', 'Program', sn, args.check)
    modules.emit(directory, ag, 'MultiStark', 'Aggregate', an, args.check)
    print(f'{len(sg)} verifier modules; {len(ag)} aggregation modules')


if __name__ == '__main__':
    main()
