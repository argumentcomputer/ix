#!/usr/bin/env python3
"""Reproduce the stage-one source port from a pinned revision of Ix.

Only lexical syntax translation is automatic. The semantic replacements are
explicit below and in Compatibility.aiur; no unconstrained pointer values enter
this program. The retained function set is the ordinary static call closure.
"""
from pathlib import Path
import argparse
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
LIBRARY_REVISION = '827550579ea660a4749c520968ad6f58be63acf4'
REVISION = '05cc396fc953d4282c01bf15a887be23fe0f49cc'
FILES = ['Core', 'ByteStream', 'Blake3', 'RBTreeMap', 'Ixon', 'IxonSerialize',
         'IxonDeserialize', 'KernelTypes', 'Kernel/Klimbs', 'Kernel/NatPrim',
         'Convert', 'Ingress', 'Kernel/Levels', 'Kernel/Subst',
         'Kernel/RoleSpec', 'Kernel/Roles', 'Kernel/Whnf',
         'Kernel/InferOnly', 'Kernel/DefEq', 'Kernel/Infer',
         'Kernel/Check', 'Kernel/Claim', 'Kernel/Eval']
ROOTS = ['verify_claim', 'verify_constant', 'verify_transitive', 'verify_serde',
         'verify_check_env', 'check_primitives', 'check_port_cases']

CANON_ADDR_CMP_HELPERS = '''
  fn canon_ord_cmp_g(a: G, b: G) -> G {
    match a - b {
      0 => 1,
      _ =>
        match u32_less_than(a, b) {
          1 => 0,
          0 => 2,
        },
    }
  }

  fn canon_ord_then(a: G, b: G) -> G {
    match a {
      1 => b,
      _ => a,
    }
  }

  fn canon_addr_cmp(x: Addr, y: Addr) -> G {
    let xa = load(x);
    let ya = load(y);
    canon_ord_then(canon_addr_chunk(to_field(xa[0]), to_field(xa[1]), to_field(xa[2]), to_field(xa[3]),
                                    to_field(ya[0]), to_field(ya[1]), to_field(ya[2]), to_field(ya[3])),
      canon_ord_then(canon_addr_chunk(to_field(xa[4]), to_field(xa[5]), to_field(xa[6]), to_field(xa[7]),
                                      to_field(ya[4]), to_field(ya[5]), to_field(ya[6]), to_field(ya[7])),
        canon_ord_then(canon_addr_chunk(to_field(xa[8]), to_field(xa[9]), to_field(xa[10]), to_field(xa[11]),
                                        to_field(ya[8]), to_field(ya[9]), to_field(ya[10]), to_field(ya[11])),
          canon_ord_then(canon_addr_chunk(to_field(xa[12]), to_field(xa[13]), to_field(xa[14]), to_field(xa[15]),
                                          to_field(ya[12]), to_field(ya[13]), to_field(ya[14]), to_field(ya[15])),
            canon_ord_then(canon_addr_chunk(to_field(xa[16]), to_field(xa[17]), to_field(xa[18]), to_field(xa[19]),
                                            to_field(ya[16]), to_field(ya[17]), to_field(ya[18]), to_field(ya[19])),
              canon_ord_then(canon_addr_chunk(to_field(xa[20]), to_field(xa[21]), to_field(xa[22]), to_field(xa[23]),
                                              to_field(ya[20]), to_field(ya[21]), to_field(ya[22]), to_field(ya[23])),
                canon_ord_then(canon_addr_chunk(to_field(xa[24]), to_field(xa[25]), to_field(xa[26]), to_field(xa[27]),
                                                to_field(ya[24]), to_field(ya[25]), to_field(ya[26]), to_field(ya[27])),
                               canon_addr_chunk(to_field(xa[28]), to_field(xa[29]), to_field(xa[30]), to_field(xa[31]),
                                                to_field(ya[28]), to_field(ya[29]), to_field(ya[30]), to_field(ya[31])))))))))
  }

  fn canon_addr_chunk(x0: G, x1: G, x2: G, x3: G,
                      y0: G, y1: G, y2: G, y3: G) -> G {
    let xv = x0 * 16777216 + x1 * 65536 + x2 * 256 + x3;
    let yv = y0 * 16777216 + y1 * 65536 + y2 * 256 + y3;
    canon_ord_cmp_g(xv, yv)
  }
'''

ROLE_MAP_HELPERS = '''
  enum RoleMap‹V› {
    Nil,
    Node(G, G, V, &RoleMap‹V›, &RoleMap‹V›)
  }

  fn role_map_lookup_or_default‹V›(key: G, tree: RoleMap‹V›, default: V) -> V {
    match tree {
      RoleMap.Nil => default,
      RoleMap.Node(_, k, v, left, right) =>
        let eq = key - k;
        match eq {
          0 => v,
          _ =>
            match u32_less_than(key, k) {
              1 => role_map_lookup_or_default(key, load(left), default),
              _ => role_map_lookup_or_default(key, load(right), default),
            },
        },
    }
  }

  fn role_ctx_limit(rc: RoleCtx) -> G {
    match load(rc) {
      RoleCtxNode.Assumed(_, _) => 0,
      RoleCtxNode.Mk(_, limit, _) => limit,
    }
  }
'''


def source_ref(name):
    if name in ('Core', 'ByteStream', 'Blake3'):
        return f'{LIBRARY_REVISION}:LegacyAiur/Library/{name}.lean'
    return f'{REVISION}:Ix/IxVM/{name}.lean'


# Shared implementations live in Aiur/Library, rather than in the generated VM.
LIBRARY_FUNCTIONS = {
    'to_field': 'UInt8::to_field', 'u8_from_field_unsafe': 'UInt8::from_field',
    'u8_bit_decomposition': 'UInt8::bit_decomposition', 'u8_range_check': 'UInt8::from_fields',
    **{'u8_' + op: 'UInt8::' + op for op in
       ['xor', 'and', 'or', 'less_than', 'add', 'sub', 'mul', 'xor_split4', 'xor_split7']},
    **{'u32_' + op: 'UInt32::' + op for op in
       ['add', 'add3', 'xor', 'and', 'rotr8', 'rotr16', 'xor_rotr7', 'xor_rotr12']},
    'u32_less_than': 'UInt32::less_than_fields',
    'memo_u32_less_than': 'UInt32::less_than_fields',
    **{'u64_' + op: 'UInt64::' + op for op in
       ['is_zero', 'eq', 'add', 'sub_with_borrow', 'mul', 'mul_column', 'and', 'or']},
    'u64_xor_kbits': 'UInt64::xor', 'relaxed_u64_succ': 'UInt64::wrapping_succ',
    'relaxed_u64_pred': 'UInt64::saturating_pred', 'flatten_u64': 'UInt64::to_field',
    'idx_to_u64': 'UInt64::from_field',
    'blake3': 'Blake3::hash', 'verify_bytes_against': 'Blake3::verify_bytes_against',
    'bytes_to_addr': 'Blake3::bytes_to_addr', 'bytes_to_block': 'Blake3::bytes_to_block',
    'pad_block': 'Blake3::pad_block',
    **{'blake3_' + op: 'Blake3::' + op for op in
       ['next_layer', 'compress_layer', 'compress_chunks', 'finish', 'compress_block',
        'g_function', 'compress_inner_j', 'compress_init', 'compress', 'digest_bytes']},
    'address_fields': 'Blake3::address_to_fields', 'checked_address': 'Blake3::address_from_fields',
    'list_is_empty': 'Lists::is_empty', 'eq_zero': 'Fields::is_zero',
}

# Ix uses @ at every retained call site of these helpers. Match those boundaries
# with Aiur's proved declaration-level inlining. Their inline dependencies are
# acyclic; recursive calls through retained functions remain ordinary calls.
# General mixed inline/ordinary call-site selection is not part of this adapter.
INLINE_HELPERS = {
    'blake3_g_function',
    'blake3_compress_inner_j', 'blake3_compress_init', 'blake3',
    'get_constant_info', 'get_sharing', 'get_refs', 'get_univs',
    'k_infer_only_core', 'try_string_lit_pair', 'is_nat_prim_addr',
    'try_nat_dispatch', 'ctx_reachable', 'whnf_core', 'whnf_nd_core',
    'build_flat_originals', 'primary_parent_block_of',
    'infer_let_var_type', 'infer_let_var_value', 'get_recursor_rule',
    'ctor_parent_ind_ci', 'build_major_args_for_self',
    'build_major_args_for_member', 'canon_build_ctx', 'canon_sort_members',
    'u64_mul_column',
}


def uncomments(s):
    # Preserve string contents, including comment-like text in diagnostics.
    out, i, depth = [], 0, 0
    while i < len(s):
        if s[i] == '"':
            j = i + 1
            while j < len(s):
                if s[j] == '\\': j += 2
                elif s[j] == '"': j += 1; break
                else: j += 1
            out.append(s[i:j]); i = j
        elif s.startswith('--', i) or s.startswith('//', i):
            j = s.find('\n', i)
            if j == -1: break
            out.append('\n'); i = j + 1
        elif s.startswith('/-', i):
            depth = 1; i += 2
            while depth:
                if s.startswith('/-', i): depth += 1; i += 2
                elif s.startswith('-/', i): depth -= 1; i += 2
                else:
                    if s[i] == '\n': out.append('\n')
                    i += 1
        else: out.append(s[i]); i += 1
    return ''.join(out)


def strings(s):
    saved = []
    def hide(m):
        saved.append(m[0]); return f'"STRING_{len(saved)-1}"'
    return re.sub(r'"(?:[^"\\]|\\.)*"', hide, s), saved


def balance_end(s, pos, opening='{', closing='}'):
    depth = 1; i = pos + 1
    while depth:
        if s[i] == opening: depth += 1
        elif s[i] == closing: depth -= 1
        i += 1
    return i


def replace_body(s, name, body):
    m = re.search(r'\bfn ' + name + r'\b[^{}]*\{', s)
    if not m: raise ValueError(f'missing override {name}')
    begin = m.end()-1; end = balance_end(s, begin)
    return s[:begin] + '{\n' + body + '\n  }' + s[end:]


def transform_body(s, name, transform):
    m = re.search(r'\bfn ' + name + r'\b[^{}]*\{', s)
    if not m: raise ValueError(f'missing body {name}')
    begin = m.end()-1; end = balance_end(s, begin)
    return s[:begin] + transform(s[begin:end]) + s[end:]


def inline_only_helpers(source):
    """Match legacy's @-only call boundaries using ordinary proved inlining.

    No helper reached through ordinary or unconstrained calls is selected.
    Reject cycles conservatively, including cycles through retained helpers.
    This translates source annotations, not native execution code.
    """
    hidden, _ = strings(uncomments(source))
    bodies = {}
    for match in re.finditer(r'\bfn (\w+)\b[^{}]*\{', hidden):
        bodies[match[1]] = hidden[match.end():balance_end(hidden, match.end() - 1) - 1]
    calls = {name: re.findall(r'([@#]?)(\b[a-z_]\w*)\s*(?:‹[^›]*›)?\(', body)
             for name, body in bodies.items()}
    uses = {name: set() for name in bodies}
    for sites in calls.values():
        for prefix, callee in sites:
            if callee in uses:
                uses[callee].add(prefix)

    def cyclic(name):
        seen, todo = set(), [callee for _, callee in calls[name]]
        while todo:
            callee = todo.pop()
            if callee == name:
                return True
            if callee not in seen:
                seen.add(callee)
                todo.extend(child for _, child in calls.get(callee, []))
        return False

    return {name for name in bodies if uses[name] == {'@'} and not cyclic(name)}


def use_opaque_words(s):
    # Word values stay opaque throughout the hash state, digests and ROM.
    # Remove the old implementations rather than retaining byte-array adapters
    # at every arithmetic call. The library owns all word operations.
    operations = ['add', 'add3', 'xor', 'and', 'rotr8', 'rotr16',
                  'xor_rotr7', 'xor_rotr12']
    for operation in operations:
        name = 'u32_' + operation
        m = re.search(r'\bfn ' + name + r'\b[^{}]*\{', s)
        if not m: raise ValueError(f'missing word operation {name}')
        s = s[:m.start()] + s[balance_end(s, m.end()-1):]
        s = re.sub(r'[@#]?\b' + name + r'\(', f'UInt32::{operation}(', s)
    s = re.sub(r'\[U8;\s*4\]', 'U32', s)

    # Known bytes become words once, at initialization or block decoding.
    byte = r'(?:0x[0-9a-fA-F]+|\d+)u8'
    word = r'\[\s*' + byte + (r'\s*,\s*' + byte) * 3 + r'\s*\]'
    for name in ['blake3', 'blake3_next_layer', 'blake3_compress_block']:
        s = transform_body(s, name, lambda body:
            re.sub(word, lambda m: f'UInt32::from_bytes({m[0]})', body))
    s = transform_body(s, 'bytes_to_block', lambda body:
        re.sub(r'\[b\d+, b\d+, b\d+, b\d+\]',
            lambda m: f'UInt32::from_bytes({m[0]})', body))
    s = transform_body(s, 'blake3_compress_init', lambda body:
        re.sub(r'(let (?:IV[0-3]|counter_low|counter_high|block_len_u32|flags_u32) = )([^;]+);',
            r'\1UInt32::from_bytes(\2);', body))
    s = transform_body(s, 'blake3_finish', lambda body:
        body.replace('[[0u8; 4]; 16]', '[UInt32::ZERO; 16]'))
    s = replace_body(s, 'b3_pack_w', '    UInt32::compact_field(UInt32::compact(w))')

    # Only the content-address boundary exposes a digest as 32 bytes.
    for name in ['verify_bytes_against', 'bytes_to_addr']:
        s = transform_body(s, name, lambda body:
            re.sub(r'\[(?:h\[\d\]\[\d\],?\s*)+\]', 'blake3_digest_bytes(h)', body))
    return s


def remove_fast_path(s, name, equal_result='1', precheck=False):
    m = re.search(r'\bfn ' + name + r'\b[^{}]*\{', s)
    if not m: raise ValueError(f'missing pointer fast path function {name}')
    start = m.end()-1; end = balance_end(s, start)
    body = s[start:end]
    match = re.search(r'match ptr_val\((\w+)\) - ptr_val\((\w+)\) \{\s*0 => '
                      + re.escape(equal_result) + r',\s*_ =>', body)
    if not match: raise ValueError(f'changed pointer fast path in {name}')
    if precheck:
        # Pointer identity implies structural identity, so an exact structural
        # comparison accepts every pair the legacy shortcut did (and identical
        # copies too). It may answer only "equal"; any other outcome falls
        # through to the unchanged def-eq tiers.
        body = (body[:match.start()] + f'match kexpr_struct_eq({match[1]}, {match[2]}) {{'
                + f'\n      1 => {equal_result},\n      _ =>' + body[match.end():])
        return s[:start] + body + s[end:]
    # Elsewhere keep only the fallback: either the function is itself the
    # structural comparison, or its identity test follows a reduction whose
    # cost a precheck cannot avoid and precedes tiers that reach one.
    opening = body.index('{', match.start())
    close = balance_end(body, opening)
    fallback = body[match.end():close-1].strip().removesuffix(',')
    body = body[:match.start()] + fallback + body[close:]
    return s[:start] + body + s[end:]


def wrap_arms(s):
    # Old Aiur permits a sequence directly after =>. New Aiur has ordinary
    # expression arms, so retain the entire sequence as an explicit block.
    inserts = []
    for m in re.finditer(r'=>', s):
        i = m.end(); j = i; depth = 0
        while j < len(s):
            c = s[j]
            if c in '([{‹': depth += 1
            elif c in ')]}›':
                if depth == 0: break
                depth -= 1
            elif c == ',' and depth == 0: break
            j += 1
        inserts += [(i, ' { '), (j, ' } ')]
    for pos, text in sorted(inserts, reverse=True): s = s[:pos] + text + s[pos:]
    return s


def adapt(s, semantic=True):
    INLINE_HELPERS.update(inline_only_helpers(s))
    s, saved = strings(uncomments(s))
    if semantic:
        s = s.replace('read_checked_byte_stream(', 'read_finite_byte_stream(')
        s = s.replace('#read_byte_stream_unchecked(', '#read_byte_stream(')
        # Disambiguate role-indexed maps (key: Field in 0..102) from address-keyed RBTreeMap.
        s = s.replace('RBTreeMap‹Addr›', 'RoleMap‹Addr›')
        s = s.replace('RBTreeMap‹List‹RoleEvidence››', 'RoleMap‹List‹RoleEvidence››')
        for name in ['read_role_bindings', 'read_role_evidence']:
            s = transform_body(s, name, lambda body:
                body.replace('RBTreeMap.Nil', 'RoleMap.Nil')
                    .replace('RBTreeMap.Node(', 'RoleMap.Node('))
        s = s.replace('rbtree_map_lookup_or_default(r, by_role,',
                      'role_map_lookup_or_default(r, by_role,')
        s = s.replace('rbtree_map_lookup_or_default(r, evidence,',
                      'role_map_lookup_or_default(r, evidence,')
        s = s.replace('rbtree_map_lookup_or_default(ptr_val(a),',
                      'rbtree_map_lookup_or_default(a,')
        s = s.replace('rbtree_map_insert(ptr_val(a),',
                      'rbtree_map_insert(a,')
        s = s.replace(
            'let half = to_field(u8_shift_right(u8_from_field_unsafe(count)));',
            'let [b0, _, _, _, _, _, _, _] = UInt8::raw_bit_decomposition(count);\n'
            '        let half = (count - b0) / 2;')
        s = transform_body(s, 'load_role_table', lambda body:
            body.replace('assert_eq!(t0, 0xE8u8,', 'assert_eq!(to_field(t0), 0xE8,')
                .replace('assert_eq!(t1, 0x03u8,', 'assert_eq!(to_field(t1), 0x03,'))
        s = transform_body(s, 'read_evidence_entries', lambda body:
            body.replace('match tag {', 'match to_field(tag) {'))
        s = transform_body(s, 'env_walk_refs_all', lambda body:
            body.replace('match ptr_val(wc) - ptr_val(rc) {',
                         'match role_ctx_limit(wc) - role_ctx_limit(rc) {'))
        # Address-set keys are values, never prover-chosen ROM addresses.
        # Preserve the balanced tree and compare all 32 address bytes.
        s = s.replace('Node(G, G, V, &RBTreeMap', 'Node(G, Addr, V, &RBTreeMap')
        for name in ['rbtree_map_balance', 'rbtree_map_balance_fix', 'rbtree_map_ins',
                     'rbtree_map_insert', 'rbtree_map_lookup', 'rbtree_map_lookup_or_default']:
            s = re.sub(r'(fn ' + name + r'‹V›\([^{}]*?)key: G', r'\1key: Addr', s)
            s = transform_body(s, name, lambda body:
                body.replace('u32_less_than(key, k)', 'eq_zero(canon_addr_cmp(key, k))')
                    .replace('let eq = key - k;', 'let eq = canon_addr_cmp(key, k) - 1;'))
        s = s.replace('rbtree_map_insert(ptr_val(a), 1, acc)', 'rbtree_map_insert(a, 1, acc)')
        s = s.replace('rbtree_map_lookup_or_default(ptr_val(a), tree, 0)',
                      'rbtree_map_lookup_or_default(a, tree, 0)')
        s = transform_body(s, 'run_claim', lambda body:
            body.replace('io_get_info(0, digest)',
                         'hint::<(G, G)>("ixvm.io.claim", digest)')
                .replace('match variant {', 'match to_field(variant) {'))
        s = transform_body(s, 'parse_atree_body', lambda body:
            body.replace('match tag {', 'match to_field(tag) {'))
        # Opaque words expose equality through their public, checked interface.
        # Comparing the packed field for a u64 would lose information modulo p.
        s = transform_body(s, 'load_assumption_tree', lambda body:
            body.replace('assert_eq!(tag, 0xE2u8,', 'assert_eq!(to_field(tag), 0xE2,')
                .replace('assert_eq!(computed_arr, raw,',
                         'assert_eq!(address_fields(computed_arr), address_fields(raw),'))
        s = transform_body(s, 'check_opt_u64', lambda body:
            body.replace('assert_eq!(real, claimed,', 'assert_eq!(u64_eq(real, claimed), 1,'))
        for name, first in [('check_opt_addr', 'real'), ('check_opt_expr_addr', 'computed')]:
            s = transform_body(s, name, lambda body, first=first:
                body.replace(f'assert_eq!(load({first}), load(claimed),',
                             f'assert_eq!(address_eq({first}, claimed), 1,'))
        s = transform_body(s, 'check_recr_rules', lambda body:
            body.replace('assert_eq!(c_idx, pos,', 'assert_eq!(u64_eq(c_idx, pos), 1,')
                .replace('assert_eq!(r_fields, c_fields,', 'assert_eq!(u64_eq(r_fields, c_fields), 1,'))
        for name, byte in [('get_opt_addr', 'tag'), ('get_opt_def_kind_masked', 'b'),
                           ('get_opt_def_safety_masked', 'b'), ('get_opt_quot_kind_masked', 'b'),
                           ('get_reveal_mut_const_info', 'variant'), ('get_reveal_info', 'variant')]:
            s = transform_body(s, name, lambda body, byte=byte:
                body.replace(f'match {byte} {{', f'match to_field({byte}) {{'))
        s = transform_body(s, 'run_claim', lambda body:
            re.sub(r'assert_eq!\((format|validator), (\d+)u8,',
                   r'assert_eq!(to_field(\1), \2,', body))
        s = transform_body(s, 'eval_output', lambda body:
            body.replace('assert_eq!(output_type, input_type,',
                         'assert_eq!(kexpr_struct_eq(output_type, input_type), 1,'))
        s = transform_body(s, 'run_eval', lambda body:
            body.replace('assert_eq!(result, expected,',
                         'assert_eq!(kexpr_struct_eq(result, expected), 1,'))
        # Without pointer identity, identical terms that legacy settled at once
        # would otherwise unfold, and can reach eager whnf of large Nat
        # computations (Batteries `Char.all.eq_1` evaluates `Nat.all 1056767`).
        # The precheck sites are the def-eq entry, the slow tier, the bounded
        # structural tier and each lazy delta step.
        for name, result, precheck in [
            ('level_struct_eq', '1', False),
            ('kexpr_struct_eq', '1', False),
            ('k_is_def_eq', '1', True),
            ('k_is_def_eq_slow_nd', '1', False),
            ('k_is_def_eq_slow_nd_after_core', '1', False),
            ('k_is_def_eq_slow2', '1', True),
            ('k_is_def_eq_struct_bounded', '(1, credit)', True),
            ('k_is_def_eq_struct_spend', '(1, rest)', False),
            ('slow2_eager_fallback', '1', False),
            ('lazy_delta_loop', '(1, a, b)', True),
            ('assert_type_meets', '()', False),
        ]:
            s = remove_fast_path(s, name, result, precheck)
        # Without the identity shortcut, equal variables must be decided before
        # the inference tiers. Canonical recursor rules compare open bodies under
        # an empty context deliberately: their stored binder types are untrusted.
        s, count = re.subn(
            r'(fn k_is_def_eq_struct_safe\([^{}]+\{\s*match load\(a\) \{)',
            r'''\1
          KExprNode.BVar(i) =>
            match load(b) {
              KExprNode.BVar(j) => eq_zero(i - j),
              _ => 0,
            },''', s)
        if count != 1: raise ValueError('changed quick structural comparison')
        # Extend the existing spine congruence to variable heads as well. These
        # occur in the same context-free recursor bodies; recurse on the arguments
        # directly. The structural identity precheck above already accepts
        # identical trees; this congruence covers equal heads whose arguments
        # are equal only up to def-eq.
        const_head = 'KExprNode.Const(a_addr, al) =>'
        if s.count(const_head) != 1: raise ValueError('changed application congruence')
        s = s.replace(const_head, '''KExprNode.BVar(i) =>
                    match load(bh) {
                      KExprNode.BVar(j) =>
                        match i - j {
                          0 => de_args(rc, aa, bb, types),
                          _ => 0,
                        },
                      _ => 0,
                    },
                  ''' + const_head)
        # The same rules may also differ only inside binders, which def-eq enters
        # by pushing their domains. Those domains refer to the peeled rule
        # binders, which the empty context cannot close, so def-eq of an honest
        # rule would abort in `ctx_next_cut` (Nat.gcd_comm). An honest rule
        # equals its reconstruction syntactically; accept that case with the
        # context-free structural comparison before def-eq. This runs once per
        # recursor rule, not on the def-eq hot path.
        s = transform_body(s, 'compare_rules', lambda body: re.sub(
            r'assert_eq!\(k_is_def_eq\((rc, )?stored_body, cbody,\s*store\(ListNode\.Nil\)\), 1,'
            r'\s*("STRING_\d+")\);',
            r'''match kexpr_struct_eq(stored_body, cbody) {
                      1 => (),
                      _ => assert_eq!(k_is_def_eq(\1stored_body, cbody,
                          store(ListNode.Nil)), 1, \2); (),
                    };''', body, count=1))
        if 'match kexpr_struct_eq(stored_body, cbody)' not in s:
            raise ValueError('changed recursor rule comparison')
        s = replace_body(s, 'k_is_def_eq_core', '    k_is_def_eq_ordered(rc, a, b, types)')
        # Canonical recursor rules compare open bodies under an empty context.
        # Entering a higher-order induction hypothesis (e.g. Acc.rec) pushes
        # open binder types whose loose range reaches past the partial context.
        s = replace_body(s, 'ctx_close_cut', '''    match l {
      0 => 0,
      _ =>
        match load(rest) {
          ListNode.Nil => 0,
          ListNode.Cons(_, _) =>
            let c = ctx_next_cut(rest);
            match u32_less_than(c, l) {
              0 => c,
              1 => c + ctx_close_cut(list_drop(rest, c), l - c),
            },
        },
    }''')
        # This identity test is a progress guard, not an equality shortcut: Nat
        # literals always expand to Const/App, while Str literals stay unchanged.
        # Inspect the literal tag instead of traversing the two expression trees.
        s, count = re.subn(
            r'let a_ctor = nat_lit_to_ctor_or_self\(rc, a\);\s*'
            r'match ptr_val\(a_ctor\) - ptr_val\(a\) \{\s*0 => 0,\s*'
            r'_ => k_is_def_eq_struct_go\(rc, a_ctor, b, types\),\s*\}',
            '''match la {
                  KLiteral.Nat(_) =>
                    k_is_def_eq_struct_go(rc, nat_lit_to_ctor_or_self(rc, a), b, types),
                  KLiteral.Str(_) => 0,
                }''', s)
        if count != 1: raise ValueError('changed literal-expansion progress guard')
        # Address equality selects a semantic case or enforces a type assertion;
        # it is not an optional early return. Keep these comparisons by contents.
        def compare_addresses(m):
            if not all(name.endswith('_addr') for name in (m[1], m[2])):
                raise ValueError(f'unreviewed pointer comparison: {m[0]}')
            return f'(1 - address_eq({m[1]}, {m[2]}))'
        s = re.sub(r'ptr_val\((\w+)\) - ptr_val\((\w+)\)', compare_addresses, s)
        s = re.sub(r'assert_eq!\(ptr_val\((\w+)\), ptr_val\((\w+)\),',
            r'assert_eq!(address_eq(\1, \2), 1,', s)
        # Pointer-containing values cannot use assert_eq!. Nil is a refutable
        # pattern; arbitrary limb equality uses the existing structural comparator.
        s = re.sub(r'assert_eq!\(load\((\w+)\), ListNode\.Nil(?:,\s*"STRING_\d+")?\)',
            r'let ListNode.Nil = load(\1)', s)
        s = s.replace('assert_eq!(lhs, rhs,', 'assert_eq!(klimbs_eq(lhs, rhs), 1,')
        s = replace_body(s, 'load_constant_hint', '    hint::<Field>("ixvm.io.tag", (3, address_fields(load(addr))))')
        # The old quotient hint contains pointers. Ordinary long division replaces
        # it; Compatibility.aiur supplies it using checked limb arithmetic.
        s = s.replace('unconstrained_big_uint_div_mod(a, b)', 'ordinary_div_mod(a, b)')
        s = replace_body(s, 'read_byte_stream', '''
        match len {
          0 => store(ListNode.Nil),
          _ => let byte = hint::<Field>("ixvm.io.read", (channel, idx));
               let tail = read_byte_stream(channel, idx + 1, len - 1);
               store(ListNode.Cons(UInt8::from_field(byte), tail)),
        }''')
        for name in ['u64_is_zero', 'blake3_finish']:
            s = transform_body(s, name, lambda body:
                body.replace('[0, 0, 0, 0, 0, 0, 0, 0]', '[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]'))
        for name in ['relaxed_u64_succ', 'relaxed_u64_pred']:
            s = transform_body(s, name, lambda body:
                re.sub(r'match (b[0-7]) \{', r'match to_field(\1) {', body))
        for name, byte in [('unpack_def_kind_safety', 'byte'), ('get_quot_kind', 'byte'),
                           ('get_mut_const', 'tag'), ('klimbs_succ', 'carry'),
                           ('klimbs_mul_single', 'carry_out')]:
            s = transform_body(s, name, lambda body, byte=byte:
                body.replace(f'match {byte} {{', f'match to_field({byte}) {{'))
        s = transform_body(s, 'verify_bytes_against', lambda body:
            body.replace('assert_eq!(', 'assert_eq!(address_fields(')
                .replace('],\n      expected,', ']),\n      address_fields(expected),'))
        s = transform_body(s, 'u64_mul', lambda body:
            body.replace('assert_eq!(c6[2], 0u8,', 'assert_eq!(to_field(c6[2]), 0,'))
        # Recomposition of advice stays constrained, but its arithmetic need not
        # run in Rust. Keep hint/range calls and all semantic validation checks.
        # idx_to_u64 deliberately keeps its flatten_u64 query (ordinary call).
        for name in ['u64_mul_column', 'klimbs_from_g', 'idx_to_u64']:
            s = transform_body(s, name, lambda body:
                body.replace('assert_eq!(', 'constrain_eq!('))
        # Ordinary division already returns checked limbs, unlike the old raw
        # quotient/remainder hint. Its output must not be reinterpreted as fields.
        s = transform_body(s, 'klimbs_div_mod', lambda body:
            body.replace('glimbs_to_klimbs(q_hint)', 'q_hint')
                .replace('glimbs_to_klimbs(r_hint)', 'r_hint'))
        s = use_opaque_words(s)
    s = re.sub(r'\bset\((\w+), (\d+), ([^()]+?)\)', r'(\1 with { [\2] = \3 })', s)
    s = wrap_arms(s)
    s = s.replace('‹', '<').replace('›', '>')
    s = re.sub(r'\b([A-Z]\w*)\.(\w+)', r'\1::\2', s)
    s = re.sub(r'\bG\b', 'Field', s)
    s = re.sub(r'\b(0x[0-9a-fA-F]+|\d+)u8\b',
        lambda m: f'UInt32::BYTE_{int(m[1], 16 if m[1].startswith("0x") else 10)}', s)
    s = re.sub(r'\b0x[0-9a-fA-F]+\b', lambda m: str(int(m[0], 16)), s)
    s = re.sub(r'([#@])(?=[a-zA-Z_]\w*\()', '', s)
    s = re.sub(r'\bpub fn\b', 'fn', s)
    s = re.sub(r'\bfn (\w+)', lambda m: ('inline ' if m[1] in INLINE_HELPERS else '') + m[0], s)
    # Alias declarations in old Aiur are newline-terminated.
    s = re.sub(r'(^[ \t]*type [^\n]+)(?=\n)', lambda m: m[0].rstrip().rstrip(';') + ';', s, flags=re.M)
    # All new function signatures state the unit return type explicitly.
    s = re.sub(r'\bfn [^{}]+\{', lambda m: m[0] if '->' in m[0] else m[0][:-1].rstrip() + ' -> () {', s)
    for i, text in enumerate(saved): s = s.replace(f'"STRING_{i}"', text)
    return re.sub(r'\n\s*\n\s*\n+', '\n\n', s)


def use_raw_byte_operations(s):
    # When the next operation already checks both raw operands, use its map
    # directly instead of first calling the checked byte constructor. Keep
    # standalone constructors: hinted/serialized bytes need them.
    replacements = {
        'put_tagn_tail': [
            ('UInt8::add(v[0], UInt8::from_field(256 - 2 * h))',
             'UInt8::raw_add(UInt8::to_field(v[0]), 256 - 2 * h)'),
        ],
        'get_tagn_tail': [
            ('UInt8::less_than(UInt8::from_field(q), UInt8::from_field(h))',
             'UInt8::raw_lt(q, h)'),
            ('UInt8::add(lo, UInt8::from_field(2 * h))',
             'UInt8::raw_add(UInt8::to_field(lo), 2 * h)'),
        ],
        'klimbs_from_g': [
            (f'UInt8::xor(UInt8::from_field(rb{i}), UInt8::BYTE_0)',
             f'UInt8::from_field(rb{i})') for i in range(4)
        ],
        'utf8_encode_prepend': [
            (f'UInt8::xor(UInt8::from_field(g{i}), UInt8::BYTE_0)',
             f'UInt8::from_field(g{i})') for i in range(4)
        ],
    }
    for name, changes in replacements.items():
        def rewrite(body):
            for before, after in changes:
                if body.count(before) != 1:
                    raise ValueError(f'changed byte operation in {name}: {before}')
                body = body.replace(before, after)
            return body
        s = transform_body(s, name, rewrite)
    return s


def prune(s, roots, module='IxVM', raw_bytes=True):
    # Keep the original call boundaries for shared non-inline functions.
    # In particular, raw byte conversion is a checked lookup in UInt8.
    for name in LIBRARY_FUNCTIONS:
        m = re.search(r'\b(?:inline )?fn ' + name + r'\b[^{}]*\{', s)
        if m:
            s = s[:m.start()] + s[balance_end(s, m.end()-1):]
    for name, target in LIBRARY_FUNCTIONS.items():
        s = re.sub(r'(?<![:\w])' + name + r'(?=\s*(?:::<[^>]*>)?\()', target, s)
    for name in ['ListNode', 'LayerNode', 'MaybeDigest']:
        m = re.search(r'\benum ' + name + r'\b[^{}]*\{', s)
        if m:
            s = s[:m.start()] + s[balance_end(s, m.end()-1):]
    s = re.sub(r'\btype Layer = [^;]+;', 'type Layer = Blake3::Layer;', s)
    s = s.replace('type List<T> = &ListNode<T>;', 'type List<T> = Lists::List<T>;')
    s = s.replace('type U64 = [U8; 8];', 'type U64 = UInt64::U64;')
    s = s.replace('ListNode::', 'Lists::Node::')
    s = s.replace('LayerNode::', 'Blake3::LayerNode::').replace('MaybeDigest::', 'Blake3::MaybeDigest::')
    s = s.replace('UInt32::U8', 'UInt8::U8').replace('UInt32::BYTE_', 'UInt8::BYTE_')
    if raw_bytes:
        s = use_raw_byte_operations(s)
    # Identify top-level definitions, ignoring braces in diagnostic strings.
    hidden, saved = strings(s)
    functions = {}; types = []
    for m in re.finditer(r'(?m)^\s*(?:inline )?(fn|enum|type|table|map) (\w+)', hidden):
        kind, name = m[1], m[2]
        if kind in ('type', 'map'):
            end = m.end(); depth = 0
            while end < len(hidden):
                if hidden[end] in '([': depth += 1
                elif hidden[end] in ')]': depth -= 1
                elif hidden[end] == ';' and depth <= 0: break
                end += 1
            end += 1
        else:
            begin = hidden.index('{', m.end()); end = balance_end(hidden, begin)
        body = hidden[m.start():end]
        if kind == 'fn': functions[name] = body
        else: types.append(body)
    reachable = set(); todo = list(roots)
    while todo:
        name = todo.pop()
        if name in reachable: continue
        if name not in functions: continue
        reachable.add(name)
        todo += re.findall(r'\b(\w+)\s*(?:::<[^>]*>)?\(', functions[name])
    out = f'module {module} {{\n' + '\n'.join(types + [body for name, body in functions.items() if name in reachable]) + '\n}\n'
    for i, text in enumerate(saved): out = out.replace(f'"STRING_{i}"', text)
    return out, reachable


def source(ix=ROOT):
    import modules
    import user_axioms
    parts = []
    owned = []
    for name in FILES:
        ref = source_ref(name)
        text = subprocess.check_output(['git', '-C', str(ix), 'show', ref], text=True)
        part = user_axioms.apply(name, text.split('⟦', 1)[1].split('⟧', 1)[0])
        if name == 'RBTreeMap':
            part += CANON_ADDR_CMP_HELPERS
        elif name == 'Kernel/Roles':
            part += ROLE_MAP_HELPERS
        parts.append(part)
        component = {'Core': 'IxCore', 'ByteStream': 'IxByteStream',
                     'Blake3': 'IxHash'}.get(name, name.replace('/', ''))
        owned.append((component, part))
    source = adapt('\n'.join(parts))
    source += (ROOT / 'IxVM/IxVM/Compatibility.aiur').read_text()
    source += (ROOT / 'IxVM/IxVM/PortCases.aiur').read_text()
    output, names = prune(source, ROOTS)
    output = ('// Generated by tools/ixvm/adapt.py; local adapters are in Compatibility.aiur.\n'
              '// Shared byte, word, list and hash implementations are in Aiur/Library.\n' + output)
    output = '\n'.join(line.rstrip() for line in output.splitlines()) + '\n'
    return output, names, modules.origins(owned)


def main():
    import modules
    parser = argparse.ArgumentParser()
    parser.add_argument('--ix', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true', help='check generated source without writing')
    args = parser.parse_args()
    output, names, owners = source(args.ix)
    modules.check_shared(output)
    groups, renames = modules.partition(output, owners, 'IxVM', ROOTS)
    modules.emit(ROOT / 'IxVM/IxVM', groups, 'IxVM', 'Program', renames, args.check)
    calls = set(re.findall(r'(?<![:\w])([a-z_]\w*)\(', output))
    maps = set(re.findall(r'\bmap (\w+)', output))
    print(f'{len(names)} functions; unresolved call names: {sorted(calls - names - maps - {"hint"})}')
    if 'ptr_val(' in output or re.search(r'[#@]\w+\(', output):
        raise RuntimeError('port retained a pointer identity or unconstrained operation')
    if re.search(r'\[U8;\s*4\]', output):
        raise RuntimeError('port retained a byte-array word type')


if __name__ == '__main__': main()
