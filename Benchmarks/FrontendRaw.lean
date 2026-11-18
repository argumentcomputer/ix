import Ix.Aiur.Library.Core
import Ix.Aiur.Library.ByteStream
import Ix.Aiur.Library.Blake3
import Ix.Aiur.Compiler

/-!
A direct Aiur frontend experiment, with no Lean frontend in its execution path.
Supported: one namespace, one homogeneous Type-parameterized record, definitions
and theorems with grouped explicit/implicit binders, applications, projections,
record literals, let, Eq and by rfl, and ! / !1 binder contracts. Definitions
are elaborated on demand, permitting acyclic forward references. The core uses
de Bruijn indices; Eq, records and contracts have dedicated core nodes.

This is deliberately NOT a port of the full Ix frontend: no general metavariables,
universe polymorphism, recursor generation, prelude seeding, or resource checking.
The implicit solver handles one leading Type parameter determined by the first
explicit argument. Unsupported syntax is rejected. Parsing, elaborator type
inference/checking, substitution and reduction run as constrained Aiur functions;
this is not separate kernel validation. A reduction
has a 512-step depth limit; declaration recursion is bounded by declaration count.

The raw subset requires the namespace/record scaffold (so excludes empty modules),
rejects duplicate declarations and mismatched end names, enforces record parameter
universes, and requires theorem results to be propositions. The upstream frontend
currently accepts the five corresponding test cases; that observation is about
elaboration only, not kernel validation. See RAW_STRICT_CHECK in the harness.

Core Pi fields are binder-info (0 explicit / 1 implicit), binder flags
(2 unique / 3 linear+unique), result uniqueness, domain and codomain. Lam preserves
binder-info/flags. These encode metadata, not a proof of resource usage. Record
nodes refer to the module's single record descriptor. The benchmark independently
checks its name/fields and the expected types/bodies of swap, swap_fst and keep;
it does not create or check generated recursor declarations.
-/
namespace FrontendRawBench

def frontend := ⟦
  enum RTok { Word(ByteStream), Sym(G) }
  type RTokens = List‹RTok›
  enum RSyn {
    Name(ByteStream), Universe, App(&RSyn, &RSyn), Dot(&RSyn, ByteStream),
    Let(ByteStream, &RSyn, &RSyn), Record(List‹(ByteStream, &RSyn)›), Rfl
  }
  type RS = &RSyn
  enum RBinder { Mk(ByteStream, G, G, RS) }
  enum RDecl { Mk(G, ByteStream, List‹RBinder›, G, RS, RS) }
  enum RRecord { Mk(ByteStream, List‹ByteStream›) }
  enum RModule { Mk(ByteStream, RRecord, List‹RDecl›) }

  fn r_word_eq(a: ByteStream, b: ByteStream) -> G {
    match load(a) {
      ListNode.Nil => match load(b) { ListNode.Nil => 1, _ => 0, },
      ListNode.Cons(x, xs) => match load(b) {
        ListNode.Nil => 0,
        ListNode.Cons(y, ys) => match to_field(x) - to_field(y) {
          0 => r_word_eq(xs, ys), _ => 0,
        },
      },
    }
  }

  -- Basic Greek letters (U+0391..03A1, 03A3..03C9), ASCII letters and '_'.
  -- Greek continuation bytes are checked in r_scan_word, not accepted alone.
  fn r_letter(c: G) -> G {
    match c { 95 => 1, 206 => 1, 207 => 1, _ =>
      (1 - u32_less_than(c, 65)) * u32_less_than(c, 91) +
      (1 - u32_less_than(c, 97)) * u32_less_than(c, 123), }
  }
  fn r_ident(c: G) -> G {
    r_letter(c) + (1 - u32_less_than(c, 48)) * u32_less_than(c, 58)
  }
  fn r_scan_word(src: ByteStream) -> (ByteStream, ByteStream) {
    match load(src) {
      ListNode.Nil => (store(ListNode.Nil), src),
      ListNode.Cons(c, rest) => match r_ident(to_field(c)) {
        0 => (store(ListNode.Nil), src),
        1 => match to_field(c) {
          206 => r_scan_greek(c, rest),
          207 => r_scan_greek(c, rest),
          _ => let (w, tail) = r_scan_word(rest); (store(ListNode.Cons(c, w)), tail),
        },
      },
    }
  }
  fn r_scan_greek(c: U8, rest: ByteStream) -> (ByteStream, ByteStream) {
    let ListNode.Cons(d, rest) = load(rest);
    let valid = match to_field(c) {
      206 => (1 - u32_less_than(to_field(d), 145)) * u32_less_than(to_field(d), 162) +
        (1 - u32_less_than(to_field(d), 163)) * u32_less_than(to_field(d), 192),
      207 => (1 - u32_less_than(to_field(d), 128)) * u32_less_than(to_field(d), 138),
    };
    assert_eq!(valid,
      1, "invalid Greek UTF-8");
    let (w, tail) = r_scan_word(rest);
    (store(ListNode.Cons(c, store(ListNode.Cons(d, w)))), tail)
  }
  fn r_lex(src: ByteStream) -> RTokens {
    match load(src) {
      ListNode.Nil => store(ListNode.Cons(RTok.Sym(0), store(ListNode.Nil))),
      ListNode.Cons(c, rest) => match to_field(c) {
        32 => r_lex(rest), 9 => r_lex(rest), 10 => r_lex(rest), 13 => r_lex(rest),
        40 => r_symbol(40, rest), 41 => r_symbol(41, rest),
        123 => r_symbol(123, rest), 125 => r_symbol(125, rest),
        44 => r_symbol(44, rest), 46 => r_symbol(46, rest),
        59 => r_symbol(59, rest),
        58 => match load(rest) {
          ListNode.Cons(d, tail) => match to_field(d) {
            61 => r_symbol(256, tail), _ => r_symbol(58, rest),
          },
          _ => r_symbol(58, rest),
        },
        33 => match load(rest) {
          ListNode.Cons(d, tail) => match to_field(d) {
            49 => r_symbol(257, tail), _ => r_symbol(33, rest),
          },
          _ => r_symbol(33, rest),
        },
        _ =>
          assert_eq!(r_letter(to_field(c)), 1, "unsupported source byte");
          let (w, tail) = r_scan_word(src);
          store(ListNode.Cons(r_keyword(w), r_lex(tail))),
      },
    }
  }
  fn r_symbol(n: G, rest: ByteStream) -> RTokens {
    store(ListNode.Cons(RTok.Sym(n), r_lex(rest)))
  }
  fn r_word_namespace() -> ByteStream {
    store(ListNode.Cons(110u8,
      store(ListNode.Cons(97u8,
      store(ListNode.Cons(109u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Cons(115u8,
      store(ListNode.Cons(112u8,
      store(ListNode.Cons(97u8,
      store(ListNode.Cons(99u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Nil)))))))))))))))))))
  }
  fn r_word_end() -> ByteStream {
    store(ListNode.Cons(101u8,
      store(ListNode.Cons(110u8,
      store(ListNode.Cons(100u8,
      store(ListNode.Nil)))))))
  }
  fn r_word_structure() -> ByteStream {
    store(ListNode.Cons(115u8,
      store(ListNode.Cons(116u8,
      store(ListNode.Cons(114u8,
      store(ListNode.Cons(117u8,
      store(ListNode.Cons(99u8,
      store(ListNode.Cons(116u8,
      store(ListNode.Cons(117u8,
      store(ListNode.Cons(114u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Nil)))))))))))))))))))
  }
  fn r_word_where() -> ByteStream {
    store(ListNode.Cons(119u8,
      store(ListNode.Cons(104u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Cons(114u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Nil)))))))))))
  }
  fn r_word_def() -> ByteStream {
    store(ListNode.Cons(100u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Cons(102u8,
      store(ListNode.Nil)))))))
  }
  fn r_word_theorem() -> ByteStream {
    store(ListNode.Cons(116u8,
      store(ListNode.Cons(104u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Cons(111u8,
      store(ListNode.Cons(114u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Cons(109u8,
      store(ListNode.Nil)))))))))))))))
  }
  fn r_word_type() -> ByteStream {
    store(ListNode.Cons(84u8,
      store(ListNode.Cons(121u8,
      store(ListNode.Cons(112u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Nil)))))))))
  }
  fn r_word_let() -> ByteStream {
    store(ListNode.Cons(108u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Cons(116u8,
      store(ListNode.Nil)))))))
  }
  fn r_word_by() -> ByteStream {
    store(ListNode.Cons(98u8,
      store(ListNode.Cons(121u8,
      store(ListNode.Nil)))))
  }
  fn r_word_rfl() -> ByteStream {
    store(ListNode.Cons(114u8,
      store(ListNode.Cons(102u8,
      store(ListNode.Cons(108u8,
      store(ListNode.Nil)))))))
  }
  fn r_word_mk() -> ByteStream {
    store(ListNode.Cons(109u8,
      store(ListNode.Cons(107u8,
      store(ListNode.Nil)))))
  }
  fn r_word_equality() -> ByteStream {
    store(ListNode.Cons(69u8,
      store(ListNode.Cons(113u8,
      store(ListNode.Nil)))))
  }
  fn r_word_demo() -> ByteStream {
    store(ListNode.Cons(68u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Cons(109u8,
      store(ListNode.Cons(111u8,
      store(ListNode.Nil)))))))))
  }
  fn r_word_pair() -> ByteStream {
    store(ListNode.Cons(80u8,
      store(ListNode.Cons(97u8,
      store(ListNode.Cons(105u8,
      store(ListNode.Cons(114u8,
      store(ListNode.Nil)))))))))
  }
  fn r_word_fst() -> ByteStream {
    store(ListNode.Cons(102u8,
      store(ListNode.Cons(115u8,
      store(ListNode.Cons(116u8,
      store(ListNode.Nil)))))))
  }
  fn r_word_snd() -> ByteStream {
    store(ListNode.Cons(115u8,
      store(ListNode.Cons(110u8,
      store(ListNode.Cons(100u8,
      store(ListNode.Nil)))))))
  }
  fn r_word_swap() -> ByteStream {
    store(ListNode.Cons(115u8,
      store(ListNode.Cons(119u8,
      store(ListNode.Cons(97u8,
      store(ListNode.Cons(112u8,
      store(ListNode.Nil)))))))))
  }
  fn r_word_swap_fst() -> ByteStream {
    store(ListNode.Cons(115u8,
      store(ListNode.Cons(119u8,
      store(ListNode.Cons(97u8,
      store(ListNode.Cons(112u8,
      store(ListNode.Cons(95u8,
      store(ListNode.Cons(102u8,
      store(ListNode.Cons(115u8,
      store(ListNode.Cons(116u8,
      store(ListNode.Nil)))))))))))))))))
  }
  fn r_word_keep() -> ByteStream {
    store(ListNode.Cons(107u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Cons(101u8,
      store(ListNode.Cons(112u8,
      store(ListNode.Nil)))))))))
  }
  fn r_keyword(w: ByteStream) -> RTok {
    match r_word_eq(w, r_word_namespace()) {
      1 => RTok.Sym(300),
      0 => match r_word_eq(w, r_word_end()) {
        1 => RTok.Sym(301),
        0 => match r_word_eq(w, r_word_structure()) {
          1 => RTok.Sym(302),
          0 => match r_word_eq(w, r_word_where()) {
            1 => RTok.Sym(303),
            0 => match r_word_eq(w, r_word_def()) {
              1 => RTok.Sym(304),
              0 => match r_word_eq(w, r_word_theorem()) {
                1 => RTok.Sym(305),
                0 => match r_word_eq(w, r_word_type()) {
                  1 => RTok.Sym(306),
                  0 => match r_word_eq(w, r_word_let()) {
                    1 => RTok.Sym(307),
                    0 => match r_word_eq(w, r_word_by()) {
                      1 => RTok.Sym(308),
                      0 => match r_word_eq(w, r_word_rfl()) {
                        1 => RTok.Sym(309),
                        0 => RTok.Word(w),
                      },
                    },
                  },
                },
              },
            },
          },
        },
      },
    }
  }
  fn r_expect(ts: RTokens, sym: G) -> RTokens {
    let ListNode.Cons(RTok.Sym(n), rest) = load(ts);
    assert_eq!(n, sym, "unexpected token"); rest
  }
  fn r_name(ts: RTokens) -> (ByteStream, RTokens) {
    let ListNode.Cons(RTok.Word(w), rest) = load(ts); (w, rest)
  }
  fn r_is_sym(ts: RTokens, sym: G) -> G {
    let ListNode.Cons(t, _) = load(ts);
    match t { RTok.Sym(n) => match n - sym { 0 => 1, _ => 0, }, _ => 0, }
  }
  fn r_term(ts: RTokens) -> (RS, RTokens) {
    let ListNode.Cons(t, rest) = load(ts);
    match t {
      RTok.Sym(307) =>
        let (name, rest) = r_name(rest);
        let rest = r_expect(rest, 256);
        let (value, rest) = r_term(rest);
        let rest = r_expect(rest, 59);
        let (body, rest) = r_term(rest);
        (store(RSyn.Let(name, value, body)), rest),
      RTok.Sym(308) => (store(RSyn.Rfl), r_expect(rest, 309)),
      _ => let (head, rest) = r_atom(ts); r_apps(head, rest),
    }
  }
  fn r_atom(ts: RTokens) -> (RS, RTokens) {
    let ListNode.Cons(t, rest) = load(ts);
    let (e, rest) = match t {
      RTok.Word(w) => (store(RSyn.Name(w)), rest),
      RTok.Sym(306) => (store(RSyn.Universe), rest),
      RTok.Sym(40) => let (e, rest) = r_term(rest); (e, r_expect(rest, 41)),
      RTok.Sym(123) => let (fields, rest) = r_fields(rest);
        (store(RSyn.Record(fields)), rest),
    };
    r_dots(e, rest)
  }
  fn r_dots(e: RS, ts: RTokens) -> (RS, RTokens) {
    match r_is_sym(ts, 46) {
      0 => (e, ts),
      1 => let (name, rest) = r_name(r_expect(ts, 46));
        r_dots(store(RSyn.Dot(e, name)), rest),
    }
  }
  fn r_apps(head: RS, ts: RTokens) -> (RS, RTokens) {
    let ListNode.Cons(t, _) = load(ts);
    let more = match t {
      RTok.Word(_) => 1, RTok.Sym(40) => 1,
      RTok.Sym(123) => 1, RTok.Sym(306) => 1, _ => 0,
    };
    match more {
      0 => (head, ts),
      1 => let (arg, rest) = r_atom(ts); r_apps(store(RSyn.App(head, arg)), rest),
    }
  }
  fn r_fields(ts: RTokens) -> (List‹(ByteStream, RS)›, RTokens) {
    let (name, ts) = r_name(ts);
    let (e, ts) = r_term(r_expect(ts, 256));
    match r_is_sym(ts, 44) {
      0 => (store(ListNode.Cons((name, e), store(ListNode.Nil))), r_expect(ts, 125)),
      1 => let (tail, rest) = r_fields(r_expect(ts, 44));
        (store(ListNode.Cons((name, e), tail)), rest),
    }
  }
  fn r_binder_names(ts: RTokens) -> (List‹ByteStream›, RTokens) {
    let (name, ts) = r_name(ts);
    match r_is_sym(ts, 58) {
      1 => (store(ListNode.Cons(name, store(ListNode.Nil))), ts),
      0 => let (tail, ts) = r_binder_names(ts);
        (store(ListNode.Cons(name, tail)), ts),
    }
  }
  fn r_make_binders(names: List‹ByteStream›, bi: G, flags: G, ty: RS) -> List‹RBinder› {
    match load(names) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(name, rest) => store(ListNode.Cons(RBinder.Mk(name, bi, flags, ty),
        r_make_binders(rest, bi, flags, ty))),
    }
  }
  fn r_binders(ts: RTokens) -> (List‹RBinder›, RTokens) {
    let ListNode.Cons(t, rest) = load(ts);
    let kind = match t { RTok.Sym(40) => 1, RTok.Sym(123) => 2, _ => 0, };
    match kind {
      0 => (store(ListNode.Nil), ts),
      _ =>
        let ListNode.Cons(t, tail) = load(rest);
        let (flags, rest) = match t {
          RTok.Sym(33) => (2, tail), RTok.Sym(257) => (3, tail), _ => (0, rest),
        };
        let (names, rest) = r_binder_names(rest);
        let (ty, rest) = r_term(r_expect(rest, 58));
        let close = match kind { 1 => 41, 2 => 125, };
        let (tail, rest) = r_binders(r_expect(rest, close));
        (list_concat(r_make_binders(names, kind - 1, flags, ty), tail), rest),
    }
  }
  fn r_record_fields(ts: RTokens, param: ByteStream) -> (List‹ByteStream›, RTokens) {
    let ListNode.Cons(t, _) = load(ts);
    match t {
      RTok.Word(_) =>
        let (name, ts) = r_name(ts);
        let (ty, ts) = r_name(r_expect(ts, 58));
        assert_eq!(r_word_eq(ty, param), 1, "only homogeneous record fields supported");
        let (rest, ts) = r_record_fields(ts, param);
        assert_eq!(r_member(name, rest), 0, "duplicate field");
        (store(ListNode.Cons(name, rest)), ts),
      _ => (store(ListNode.Nil), ts),
    }
  }
  fn r_member(name: ByteStream, names: List‹ByteStream›) -> G {
    match load(names) {
      ListNode.Nil => 0,
      ListNode.Cons(w, rest) => match r_word_eq(name, w) {
        1 => 1, 0 => r_member(name, rest),
      },
    }
  }
  fn r_declarations(ts: RTokens) -> (List‹RDecl›, RTokens) {
    let ListNode.Cons(t, rest) = load(ts);
    let kind = match t { RTok.Sym(304) => 1, RTok.Sym(305) => 2, _ => 0, };
    match kind {
      0 => (store(ListNode.Nil), ts),
      _ =>
        let (name, rest) = r_name(rest);
        let (binders, rest) = r_binders(rest);
        let rest = r_expect(rest, 58);
        let unique = r_is_sym(rest, 33);
        let rest = match unique { 1 => r_expect(rest, 33), 0 => rest, };
        let (ty, rest) = r_term(rest);
        let (value, rest) = r_term(r_expect(rest, 256));
        let (tail, rest) = r_declarations(rest);
        (store(ListNode.Cons(RDecl.Mk(kind - 1, name, binders, unique, ty, value), tail)), rest),
    }
  }
  fn r_parse(src: ByteStream) -> RModule {
    let (ns, ts) = r_name(r_expect(r_lex(src), 300));
    let (name, ts) = r_name(r_expect(ts, 302));
    let (param, ts) = r_name(r_expect(ts, 40));
    let ts = r_expect(r_expect(r_expect(ts, 58), 306), 41);
    let ts = r_expect(r_expect(r_expect(ts, 58), 306), 303);
    let (fields, ts) = r_record_fields(ts, param);
    let ListNode.Cons(_, _) = load(fields);
    let (decls, ts) = r_declarations(ts);
    let (endName, ts) = r_name(r_expect(ts, 301));
    assert_eq!(r_word_eq(ns, endName), 1, "namespace mismatch");
    let ts = r_expect(ts, 0);
    let ListNode.Nil = load(ts);
    RModule.Mk(ns, RRecord.Mk(name, fields), decls)
  }
  enum RCore {
    Universe(G), Var(G), Const(ByteStream), App(&RCore, &RCore),
    Pi(G, G, G, &RCore, &RCore), Lam(G, G, &RCore, &RCore),
    Let(&RCore, &RCore, &RCore), RecTy(&RCore),
    Ctor(&RCore, List‹&RCore›), Proj(G, &RCore),
    Equality(&RCore, &RCore, &RCore), Refl(&RCore, &RCore)
  }
  type RC = &RCore
  type RCtx = List‹(ByteStream, RC)›
  enum REntry { Mk(G, ByteStream, RC, RC) }

  fn r_shift(e: RC, cutoff: G, amount: G) -> RC {
    match load(e) {
      RCore.Universe(_) => e, RCore.Const(_) => e,
      RCore.Var(i) => match u32_less_than(i, cutoff) {
        1 => e, 0 => store(RCore.Var(i + amount)),
      },
      RCore.App(f, x) => store(RCore.App(r_shift(f, cutoff, amount), r_shift(x, cutoff, amount))),
      RCore.Pi(bi, fl, ru, a, b) => store(RCore.Pi(bi, fl, ru,
        r_shift(a, cutoff, amount), r_shift(b, cutoff + 1, amount))),
      RCore.Lam(bi, fl, a, b) => store(RCore.Lam(bi, fl,
        r_shift(a, cutoff, amount), r_shift(b, cutoff + 1, amount))),
      RCore.Let(a, v, b) => store(RCore.Let(r_shift(a, cutoff, amount),
        r_shift(v, cutoff, amount), r_shift(b, cutoff + 1, amount))),
      RCore.RecTy(a) => store(RCore.RecTy(r_shift(a, cutoff, amount))),
      RCore.Ctor(a, xs) => store(RCore.Ctor(r_shift(a, cutoff, amount), r_shift_list(xs, cutoff, amount))),
      RCore.Proj(i, x) => store(RCore.Proj(i, r_shift(x, cutoff, amount))),
      RCore.Equality(a, l, r) => store(RCore.Equality(r_shift(a, cutoff, amount),
        r_shift(l, cutoff, amount), r_shift(r, cutoff, amount))),
      RCore.Refl(a, l) => store(RCore.Refl(r_shift(a, cutoff, amount), r_shift(l, cutoff, amount))),
    }
  }
  fn r_shift_list(xs: List‹RC›, cutoff: G, amount: G) -> List‹RC› {
    match load(xs) {
      ListNode.Nil => xs,
      ListNode.Cons(x, rest) => store(ListNode.Cons(r_shift(x, cutoff, amount),
        r_shift_list(rest, cutoff, amount))),
    }
  }
  fn r_subst(e: RC, arg: RC, depth: G) -> RC {
    match load(e) {
      RCore.Universe(_) => e, RCore.Const(_) => e,
      RCore.Var(i) => match u32_less_than(i, depth) {
        1 => e,
        0 => match i - depth {
          0 => r_shift(arg, 0, depth), _ => store(RCore.Var(i - 1)),
        },
      },
      RCore.App(f, x) => store(RCore.App(r_subst(f, arg, depth), r_subst(x, arg, depth))),
      RCore.Pi(bi, fl, ru, a, b) => store(RCore.Pi(bi, fl, ru,
        r_subst(a, arg, depth), r_subst(b, arg, depth + 1))),
      RCore.Lam(bi, fl, a, b) => store(RCore.Lam(bi, fl,
        r_subst(a, arg, depth), r_subst(b, arg, depth + 1))),
      RCore.Let(a, v, b) => store(RCore.Let(r_subst(a, arg, depth),
        r_subst(v, arg, depth), r_subst(b, arg, depth + 1))),
      RCore.RecTy(a) => store(RCore.RecTy(r_subst(a, arg, depth))),
      RCore.Ctor(a, xs) => store(RCore.Ctor(r_subst(a, arg, depth), r_subst_list(xs, arg, depth))),
      RCore.Proj(i, x) => store(RCore.Proj(i, r_subst(x, arg, depth))),
      RCore.Equality(a, l, r) => store(RCore.Equality(r_subst(a, arg, depth),
        r_subst(l, arg, depth), r_subst(r, arg, depth))),
      RCore.Refl(a, l) => store(RCore.Refl(r_subst(a, arg, depth), r_subst(l, arg, depth))),
    }
  }
  fn r_subst_list(xs: List‹RC›, arg: RC, depth: G) -> List‹RC› {
    match load(xs) {
      ListNode.Nil => xs,
      ListNode.Cons(x, rest) => store(ListNode.Cons(r_subst(x, arg, depth), r_subst_list(rest, arg, depth))),
    }
  }
  fn r_num_eq(x: G, y: G) -> G { match x - y { 0 => 1, _ => 0, } }
  -- Structural equality: never use pointer inequality as evidence of inequality.
  fn r_core_eq(a: RC, b: RC) -> G {
    match load(a) {
      RCore.Universe(i) => match load(b) { RCore.Universe(j) => r_num_eq(i, j), _ => 0, },
      RCore.Var(i) => match load(b) { RCore.Var(j) => r_num_eq(i, j), _ => 0, },
      RCore.Const(n) => match load(b) { RCore.Const(m) => r_word_eq(n, m), _ => 0, },
      RCore.App(f, x) => match load(b) {
        RCore.App(g, y) => r_core_eq(f, g) * r_core_eq(x, y), _ => 0,
      },
      RCore.Pi(bi, fl, ru, x, y) => match load(b) {
        RCore.Pi(bj, fm, rv, z, w) => r_num_eq(bi, bj) * r_num_eq(fl, fm) *
          r_num_eq(ru, rv) * r_core_eq(x, z) * r_core_eq(y, w), _ => 0,
      },
      RCore.Lam(bi, fl, x, y) => match load(b) {
        RCore.Lam(bj, fm, z, w) => r_num_eq(bi, bj) * r_num_eq(fl, fm) *
          r_core_eq(x, z) * r_core_eq(y, w), _ => 0,
      },
      RCore.Let(t, v, x) => match load(b) {
        RCore.Let(u, w, y) => r_core_eq(t, u) * r_core_eq(v, w) * r_core_eq(x, y), _ => 0,
      },
      RCore.RecTy(x) => match load(b) { RCore.RecTy(y) => r_core_eq(x, y), _ => 0, },
      RCore.Ctor(t, xs) => match load(b) {
        RCore.Ctor(u, ys) => r_core_eq(t, u) * r_core_list_eq(xs, ys), _ => 0,
      },
      RCore.Proj(i, x) => match load(b) {
        RCore.Proj(j, y) => r_num_eq(i, j) * r_core_eq(x, y), _ => 0,
      },
      RCore.Equality(t, l, r) => match load(b) {
        RCore.Equality(u, m, s) => r_core_eq(t, u) * r_core_eq(l, m) * r_core_eq(r, s), _ => 0,
      },
      RCore.Refl(t, l) => match load(b) {
        RCore.Refl(u, m) => r_core_eq(t, u) * r_core_eq(l, m), _ => 0,
      },
    }
  }
  fn r_core_list_eq(xs: List‹RC›, ys: List‹RC›) -> G {
    match load(xs) {
      ListNode.Nil => match load(ys) { ListNode.Nil => 1, _ => 0, },
      ListNode.Cons(x, xs) => match load(ys) {
        ListNode.Cons(y, ys) => r_core_eq(x, y) * r_core_list_eq(xs, ys), _ => 0,
      },
    }
  }
  fn r_local(name: ByteStream, ctx: RCtx, depth: G) -> Option‹(RC, RC)› {
    match load(ctx) {
      ListNode.Nil => Option.None,
      ListNode.Cons((n, ty), rest) => match r_word_eq(name, n) {
        1 => Option.Some((store(RCore.Var(depth)), r_shift(ty, 0, depth + 1))),
        0 => r_local(name, rest, depth + 1),
      },
    }
  }
  fn r_find_decl(name: ByteStream, ds: List‹RDecl›) -> RDecl {
    let ListNode.Cons(d, rest) = load(ds);
    let RDecl.Mk(_, n, _, _, _, _) = d;
    match r_word_eq(name, n) { 1 => d, 0 => r_find_decl(name, rest), }
  }
  fn r_field_index(name: ByteStream, fields: List‹ByteStream›) -> G {
    let ListNode.Cons(n, rest) = load(fields);
    match r_word_eq(name, n) { 1 => 0, 0 => 1 + r_field_index(name, rest), }
  }
  fn r_spine(e: RS, args: List‹RS›) -> (RS, List‹RS›) {
    match load(e) {
      RSyn.App(f, a) => r_spine(f, store(ListNode.Cons(a, args))),
      _ => (e, args),
    }
  }
  fn r_elab_decl(d: RDecl, rec: RRecord, ds: List‹RDecl›, fuel: G) -> REntry {
    assert_eq!(u32_less_than(0, fuel), 1, "cyclic declaration dependency");
    let RDecl.Mk(kind, name, binders, unique, ty, body) = d;
    let (ty, value) = r_elab_binders(binders, kind, unique, ty, body, store(ListNode.Nil), rec, ds, fuel - 1);
    REntry.Mk(kind, name, ty, value)
  }
  fn r_elab_binders(bs: List‹RBinder›, kind: G, unique: G, ty: RS, body: RS,
      ctx: RCtx, rec: RRecord, ds: List‹RDecl›, fuel: G) -> (RC, RC) {
    match load(bs) {
      ListNode.Nil =>
        let (ty, sort) = r_infer(ty, ctx, rec, ds, fuel);
        let RCore.Universe(level) = load(r_whnf(sort, rec, ds, fuel, 512));
        assert_eq!(kind * level, 0, "theorem must prove a proposition");
        (ty, r_check(body, ty, ctx, rec, ds, fuel)),
      ListNode.Cons(RBinder.Mk(name, bi, flags, dom), rest) =>
        let a = r_type(dom, ctx, rec, ds, fuel);
        let (b, v) = r_elab_binders(rest, kind, unique, ty, body,
          store(ListNode.Cons((name, a), ctx)), rec, ds, fuel);
        let ru = list_is_empty(rest) * unique;
        (store(RCore.Pi(bi, flags, ru, a, b)), store(RCore.Lam(bi, flags, a, v))),
    }
  }
  fn r_type(s: RS, ctx: RCtx, rec: RRecord, ds: List‹RDecl›, fuel: G) -> RC {
    let (e, t) = r_infer(s, ctx, rec, ds, fuel);
    let RCore.Universe(_) = load(r_whnf(t, rec, ds, fuel, 512));
    e
  }
  fn r_infer(s: RS, ctx: RCtx, rec: RRecord, ds: List‹RDecl›, fuel: G) -> (RC, RC) {
    match load(s) {
      RSyn.Universe => (store(RCore.Universe(1)), store(RCore.Universe(2))),
      RSyn.Name(n) => match r_local(n, ctx, 0) {
        Option.Some(result) => result,
        Option.None =>
          let REntry.Mk(_, _, ty, _) = r_elab_decl(r_find_decl(n, ds), rec, ds, fuel);
          (store(RCore.Const(n)), ty),
      },
      RSyn.App(_, _) => let (head, args) = r_spine(s, store(ListNode.Nil));
        r_infer_app(head, args, ctx, rec, ds, fuel),
      RSyn.Dot(e, field) =>
        let (e, ty) = r_infer(e, ctx, rec, ds, fuel);
        let RCore.RecTy(a) = load(r_whnf(ty, rec, ds, fuel, 512));
        let RRecord.Mk(_, fields) = rec;
        (store(RCore.Proj(r_field_index(field, fields), e)), a),
      RSyn.Let(name, v, body) =>
        let (v, ty) = r_infer(v, ctx, rec, ds, fuel);
        let (b, bt) = r_infer(body, store(ListNode.Cons((name, ty), ctx)), rec, ds, fuel);
        (store(RCore.Let(ty, v, b)), r_subst(bt, v, 0)),
    }
  }
  fn r_infer_app(head: RS, args: List‹RS›, ctx: RCtx,
      rec: RRecord, ds: List‹RDecl›, fuel: G) -> (RC, RC) {
    let RRecord.Mk(recordName, fields) = rec;
    match load(head) {
      RSyn.Name(n) => match r_local(n, ctx, 0) {
        Option.Some((f, ty)) => r_apply(f, ty, args, ctx, rec, ds, fuel),
        Option.None => match r_word_eq(n, recordName) {
          1 =>
            let ListNode.Cons(a, rest) = load(args);
            let ListNode.Nil = load(rest);
            let a = r_check(a, store(RCore.Universe(1)), ctx, rec, ds, fuel);
            (store(RCore.RecTy(a)), store(RCore.Universe(1))),
          0 => match r_word_eq(n, r_word_equality()) {
            1 =>
              let ListNode.Cons(l, rest) = load(args);
              let ListNode.Cons(r, rest) = load(rest);
              let ListNode.Nil = load(rest);
              let (l, a) = r_infer(l, ctx, rec, ds, fuel);
              let r = r_check(r, a, ctx, rec, ds, fuel);
              (store(RCore.Equality(a, l, r)), store(RCore.Universe(0))),
            0 => let (f, ty) = r_infer(head, ctx, rec, ds, fuel);
              r_apply(f, ty, args, ctx, rec, ds, fuel),
          },
        },
      },
      RSyn.Dot(base, field) => match load(base) {
        RSyn.Name(n) => match r_word_eq(n, recordName) * r_word_eq(field, r_word_mk()) {
          1 =>
            let ListNode.Cons(first, _) = load(args);
            let (_, a) = r_infer(first, ctx, rec, ds, fuel);
            assert_eq!(list_length(args), list_length(fields), "constructor arity");
            assert_eq!(r_defeq(r_core_type(a, ctx, rec, ds, fuel), store(RCore.Universe(1)), rec, ds, fuel),
              1, "constructor parameter universe");
            let values = r_check_args(args, a, ctx, rec, ds, fuel);
            (store(RCore.Ctor(a, values)), store(RCore.RecTy(a))),
          0 => let (f, ty) = r_infer(head, ctx, rec, ds, fuel);
            r_apply(f, ty, args, ctx, rec, ds, fuel),
        },
        _ => let (f, ty) = r_infer(head, ctx, rec, ds, fuel);
          r_apply(f, ty, args, ctx, rec, ds, fuel),
      },
      _ => let (f, ty) = r_infer(head, ctx, rec, ds, fuel);
        r_apply(f, ty, args, ctx, rec, ds, fuel),
    }
  }
  fn r_check_args(args: List‹RS›, a: RC, ctx: RCtx, rec: RRecord,
      ds: List‹RDecl›, fuel: G) -> List‹RC› {
    match load(args) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(x, rest) => store(ListNode.Cons(r_check(x, a, ctx, rec, ds, fuel),
        r_check_args(rest, a, ctx, rec, ds, fuel))),
    }
  }
  -- Restricted implicit solver, not a general metavariable/unification engine.
  fn r_solve(pattern: RC, actual: RC) -> RC {
    match load(pattern) {
      RCore.Var(0) => actual,
      RCore.RecTy(p) => let RCore.RecTy(a) = load(actual); r_solve(p, a),
    }
  }
  fn r_apply(f: RC, ty: RC, args: List‹RS›, ctx: RCtx,
      rec: RRecord, ds: List‹RDecl›, fuel: G) -> (RC, RC) {
    match load(args) {
      ListNode.Nil => (f, ty),
      ListNode.Cons(arg, rest) =>
        let RCore.Pi(bi, _, _, dom, body) = load(r_whnf(ty, rec, ds, fuel, 512));
        match bi {
          1 =>
            let RCore.Universe(1) = load(dom);
            let RCore.Pi(0, _, _, pattern, _) = load(body);
            let (_, actual) = r_infer(arg, ctx, rec, ds, fuel);
            let implicit = r_solve(pattern, actual);
            assert_eq!(r_defeq(r_core_type(implicit, ctx, rec, ds, fuel), dom, rec, ds, fuel),
              1, "implicit argument universe");
            r_apply(store(RCore.App(f, implicit)), r_subst(body, implicit, 0), args, ctx, rec, ds, fuel),
          0 =>
            let arg = r_check(arg, dom, ctx, rec, ds, fuel);
            r_apply(store(RCore.App(f, arg)), r_subst(body, arg, 0), rest, ctx, rec, ds, fuel),
        },
    }
  }
  fn r_field_value(name: ByteStream, fields: List‹(ByteStream, RS)›) -> RS {
    let ListNode.Cons((n, v), rest) = load(fields);
    match r_word_eq(name, n) { 1 => v, 0 => r_field_value(name, rest), }
  }
  fn r_record_values(names: List‹ByteStream›, fields: List‹(ByteStream, RS)›,
      a: RC, ctx: RCtx, rec: RRecord, ds: List‹RDecl›, fuel: G) -> List‹RC› {
    match load(names) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(name, rest) => store(ListNode.Cons(
        r_check(r_field_value(name, fields), a, ctx, rec, ds, fuel),
        r_record_values(rest, fields, a, ctx, rec, ds, fuel))),
    }
  }
  fn r_check(s: RS, expected: RC, ctx: RCtx, rec: RRecord,
      ds: List‹RDecl›, fuel: G) -> RC {
    match load(s) {
      RSyn.Record(fields) =>
        let RCore.RecTy(a) = load(r_whnf(expected, rec, ds, fuel, 512));
        let RRecord.Mk(_, names) = rec;
        -- Every distinct required field is found, and lengths agree: no extras or duplicates.
        assert_eq!(list_length(names), list_length(fields), "record field count");
        store(RCore.Ctor(a, r_record_values(names, fields, a, ctx, rec, ds, fuel))),
      RSyn.Rfl =>
        let RCore.Equality(a, l, r) = load(r_whnf(expected, rec, ds, fuel, 512));
        assert_eq!(r_defeq(l, r, rec, ds, fuel), 1, "rfl failed");
        store(RCore.Refl(a, l)),
      RSyn.Let(name, v, body) =>
        let (v, ty) = r_infer(v, ctx, rec, ds, fuel);
        let b = r_check(body, r_shift(expected, 0, 1),
          store(ListNode.Cons((name, ty), ctx)), rec, ds, fuel);
        store(RCore.Let(ty, v, b)),
      _ =>
        let (e, actual) = r_infer(s, ctx, rec, ds, fuel);
        assert_eq!(r_defeq(actual, expected, rec, ds, fuel), 1, "type mismatch");
        e,
    }
  }
  fn r_whnf(e: RC, rec: RRecord, ds: List‹RDecl›, fuel: G, steps: G) -> RC {
    assert_eq!(u32_less_than(0, steps), 1, "reduction limit");
    match load(e) {
      RCore.Const(n) =>
        let REntry.Mk(_, _, _, v) = r_elab_decl(r_find_decl(n, ds), rec, ds, fuel);
        r_whnf(v, rec, ds, fuel, steps - 1),
      RCore.Let(_, v, body) => r_whnf(r_subst(body, v, 0), rec, ds, fuel, steps - 1),
      RCore.App(f, a) =>
        let f = r_whnf(f, rec, ds, fuel, steps - 1);
        match load(f) {
          RCore.Lam(_, _, _, body) => r_whnf(r_subst(body, a, 0), rec, ds, fuel, steps - 1),
          _ => store(RCore.App(f, a)),
        },
      RCore.Proj(i, x) =>
        let x = r_whnf(x, rec, ds, fuel, steps - 1);
        match load(x) {
          RCore.Ctor(_, fields) => r_whnf(list_lookup(fields, i), rec, ds, fuel, steps - 1),
          _ => store(RCore.Proj(i, x)),
        },
      _ => e,
    }
  }
  fn r_defeq(a: RC, b: RC, rec: RRecord, ds: List‹RDecl›, fuel: G) -> G {
    match r_core_eq(a, b) {
      1 => 1,
      0 =>
        let a = r_whnf(a, rec, ds, fuel, 512);
        let b = r_whnf(b, rec, ds, fuel, 512);
        match load(a) {
          RCore.App(f, x) => match load(b) {
            RCore.App(g, y) => r_defeq(f, g, rec, ds, fuel) * r_defeq(x, y, rec, ds, fuel), _ => 0,
          },
          RCore.RecTy(x) => match load(b) {
            RCore.RecTy(y) => r_defeq(x, y, rec, ds, fuel), _ => 0,
          },
          RCore.Proj(i, x) => match load(b) {
            RCore.Proj(j, y) => r_num_eq(i, j) * r_defeq(x, y, rec, ds, fuel), _ => 0,
          },
          _ => r_core_eq(a, b),
        },
    }
  }
  fn r_elab_all(todo: List‹RDecl›, rec: RRecord, all: List‹RDecl›, fuel: G) -> List‹REntry› {
    match load(todo) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(d, rest) => store(ListNode.Cons(r_elab_decl(d, rec, all, fuel),
        r_elab_all(rest, rec, all, fuel))),
    }
  }
  fn r_decl_names(ds: List‹RDecl›, rec: RRecord) -> List‹ByteStream› {
    match load(ds) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(RDecl.Mk(_, name, _, _, _, _), rest) =>
        let names = r_decl_names(rest, rec);
        let RRecord.Mk(recordName, _) = rec;
        assert_eq!(r_member(name, names), 0, "duplicate declaration");
        assert_eq!(r_word_eq(name, recordName), 0, "record name collision");
        assert_eq!(r_word_eq(name, r_word_equality()), 0, "reserved Eq name");
        store(ListNode.Cons(name, names)),
    }
  }
  fn r_elaborate(m: RModule) -> List‹REntry› {
    let RModule.Mk(_, rec, ds) = m;
    assert_eq!(list_length(r_decl_names(ds, rec)), list_length(ds), "declaration names");
    r_elab_all(ds, rec, ds, list_length(ds) + 1)
  }
  fn r_source(digest: [U8; 32]) -> ByteStream {
    let (idx, len) = io_get_info(0, digest);
    let src = read_checked_byte_stream(0, idx, len);
    verify_bytes_against(src, digest);
    src
  }
  pub fn raw_hash(digest: [U8; 32]) -> G {
    let _ = r_source(digest);
    1
  }
  pub fn raw_parse(digest: [U8; 32]) -> G {
    let RModule.Mk(_, _, ds) = r_parse(r_source(digest));
    assert_eq!(list_length(ds) + 3, 6, "expected six module commands");
    1
  }
  pub fn raw_validate(digest: [U8; 32]) -> G {
    let m = r_parse(r_source(digest));
    let RModule.Mk(_, _, ds) = m;
    assert_eq!(list_length(r_elaborate(m)), list_length(ds), "elaboration count");
    1
  }

  -- Infer the type of a generated core term when validating an implicit record
  -- parameter. In particular, Pair.mk Type Type must not create Pair Type.
  fn r_core_type(e: RC, ctx: RCtx, rec: RRecord, ds: List‹RDecl›, fuel: G) -> RC {
    match load(e) {
      RCore.Universe(n) => store(RCore.Universe(n + 1)),
      RCore.Var(i) => let (_, ty) = list_lookup(ctx, i); r_shift(ty, 0, i + 1),
      RCore.Const(n) =>
        let REntry.Mk(_, _, ty, _) = r_elab_decl(r_find_decl(n, ds), rec, ds, fuel); ty,
      RCore.RecTy(a) =>
        assert_eq!(r_defeq(r_core_type(a, ctx, rec, ds, fuel), store(RCore.Universe(1)), rec, ds, fuel),
          1, "record parameter must inhabit Type");
        store(RCore.Universe(1)),
      RCore.App(f, a) =>
        let RCore.Pi(_, _, _, dom, body) = load(r_whnf(r_core_type(f, ctx, rec, ds, fuel), rec, ds, fuel, 512));
        assert_eq!(r_defeq(r_core_type(a, ctx, rec, ds, fuel), dom, rec, ds, fuel), 1, "core application type");
        r_subst(body, a, 0),
      RCore.Proj(_, x) => let RCore.RecTy(a) = load(r_core_type(x, ctx, rec, ds, fuel)); a,
      RCore.Ctor(a, _) => store(RCore.RecTy(a)),
      RCore.Let(ty, v, b) => r_subst(r_core_type(b,
        store(ListNode.Cons((store(ListNode.Nil), ty), ctx)), rec, ds, fuel), v, 0),
      RCore.Equality(_, _, _) => store(RCore.Universe(0)),
    }
  }
  fn r_entry(name: ByteStream, es: List‹REntry›) -> REntry {
    let ListNode.Cons(e, rest) = load(es);
    let REntry.Mk(_, n, _, _) = e;
    match r_word_eq(name, n) { 1 => e, 0 => r_entry(name, rest), }
  }
  fn r_expect_entry(name: ByteStream, kind: G, ty: RC, value: RC, es: List‹REntry›) {
    let REntry.Mk(k, _, actualTy, actualValue) = r_entry(name, es);
    assert_eq!(k, kind, "declaration kind mismatch");
    assert_eq!(r_core_eq(actualTy, ty), 1, "elaborated type mismatch");
    assert_eq!(r_core_eq(actualValue, value), 1, "elaborated value mismatch");
  }
  fn r_two(a: RC, b: RC) -> List‹RC› {
    store(ListNode.Cons(a, store(ListNode.Cons(b, store(ListNode.Nil)))))
  }
  -- Independent expected de Bruijn terms mirror FrontendRepresentative.lean.
  -- Record/Eq nodes encode their corresponding fully applied Ix constants.
  fn r_expect_output(m: RModule, es: List‹REntry›) {
    let RModule.Mk(ns, RRecord.Mk(name, fields), _) = m;
    assert_eq!(r_word_eq(ns, r_word_demo()), 1, "namespace");
    assert_eq!(r_word_eq(name, r_word_pair()), 1, "record name");
    let ListNode.Cons(fst, tail) = load(fields);
    let ListNode.Cons(snd, tail) = load(tail);
    let ListNode.Nil = load(tail);
    assert_eq!(r_word_eq(fst, r_word_fst()), 1, "first field");
    assert_eq!(r_word_eq(snd, r_word_snd()), 1, "second field");
    let s = store(RCore.Universe(1));
    let v0 = store(RCore.Var(0));
    let v1 = store(RCore.Var(1));
    let v2 = store(RCore.Var(2));
    let p0 = store(RCore.RecTy(v0));
    let p1 = store(RCore.RecTy(v1));
    let swapTy = store(RCore.Pi(1, 0, 0, s, store(RCore.Pi(0, 0, 0, p0, p1))));
    let swapValue = store(RCore.Lam(1, 0, s, store(RCore.Lam(0, 0, p0,
      store(RCore.Let(v1, store(RCore.Proj(0, v0)),
        store(RCore.Ctor(v2, r_two(store(RCore.Proj(1, v1)), v0)))))))));
    r_expect_entry(r_word_swap(), 0, swapTy, swapValue, es);
    let lhs = store(RCore.Proj(0, store(RCore.App(
      store(RCore.App(store(RCore.Const(r_word_swap())), v2)),
      store(RCore.Ctor(v2, r_two(v1, v0)))))));
    let thmTy = store(RCore.Pi(1, 0, 0, s, store(RCore.Pi(0, 0, 0, v0,
      store(RCore.Pi(0, 0, 0, v1, store(RCore.Equality(v2, lhs, v0))))))));
    let thmValue = store(RCore.Lam(1, 0, s, store(RCore.Lam(0, 0, v0,
      store(RCore.Lam(0, 0, v1, store(RCore.Refl(v2, lhs))))))));
    r_expect_entry(r_word_swap_fst(), 1, thmTy, thmValue, es);
    let keepTy = store(RCore.Pi(1, 0, 0, s, store(RCore.Pi(0, 3, 1, v0, v1))));
    let keepValue = store(RCore.Lam(1, 0, s, store(RCore.Lam(0, 3, v0, v0))));
    r_expect_entry(r_word_keep(), 0, keepTy, keepValue, es);
  }
  pub fn raw_frontend(digest: [U8; 32]) -> G {
    let m = r_parse(r_source(digest));
    r_expect_output(m, r_elaborate(m));
    1
  }

⟧

def toplevel : Except String Aiur.Source.Toplevel := do
  let tl ← (Aiur.Library.core.merge Aiur.Library.byteStream).mapError toString
  let tl ← (tl.merge Aiur.Library.blake3).mapError toString
  let tl ← (tl.merge frontend).mapError toString
  return tl.prune [`raw_hash, `raw_parse, `raw_validate, `raw_frontend]

end FrontendRawBench
