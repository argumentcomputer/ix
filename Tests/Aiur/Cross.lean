module

public import LSpec
public import Ix.Aiur
public import Ix.Aiur.Meta

/-!
End-to-end pipeline cross-tests for `Ix/Aiur`.

A single `toplevel` collects every Aiur surface-language program needed
by the test corpus (datatypes, type aliases, mutually-recursive
functions, etc.). The `runAgreement` helper evaluates one entry point
through both the source-level reference evaluator (`Source.Eval`) and
the lowered bytecode evaluator (`Bytecode.Eval`), asserting that the
flat-encoded return value and the `IOBuffer` agree.
-/

public section

open LSpec Aiur

namespace AiurTests.Cross

/-- Single shared toplevel for every cross-test. Functions are entry
points iff prefixed `pub fn`. -/
def toplevel : Source.Toplevel := ⟦
  -- Type aliases
  type MyField = G
  type Pair‹T› = (T, T)

  -- Datatypes
  enum MyOpt { Some(G), None }
  enum MyOpt2 { Some2(MyOpt), None2 }
  enum Wrap { W(MyOpt2) }
  enum APair { Mk(G, G) }
  enum MyList { Nil, Cons(G, &MyList) }

  -- Arithmetic + control flow
  pub fn add_one(x: G) -> G { x + 1 }

  pub fn arith(a: G, b: G) -> G {
    let s = a + b;
    let p = s * 2;
    p - 1
  }

  pub fn fst(p: (G, G)) -> G { proj(p, 0) }
  pub fn second(a: [G; 3]) -> G { a[1] }

  pub fn roundtrip(x: G) -> G {
    let p = store(x);
    load(p)
  }

  -- Function calls
  fn helper(x: G) -> G { x * x }
  pub fn call_helper(x: G) -> G { helper(x) + 1 }

  -- u8 / u32 ops
  pub fn xor_bytes(a: G, b: G) -> G { u8_xor(a, b) }
  pub fn add8(a: G, b: G) -> (G, G) { u8_add(a, b) }
  pub fn lt32(a: G, b: G) -> G { u32_less_than(a, b) }

  -- Slice / set
  pub fn middle(a: [G; 4]) -> [G; 2] { a[1..3] }
  pub fn set_mid(a: [G; 3]) -> [G; 3] { set(a, 1, 99) }

  -- Assertions / IO / pointer ops
  pub fn assert_same(x: G, y: G) -> G { assert_eq!(x, y); x }
  pub fn io_roundtrip(x: G) -> [G; 1] {
    io_write([x]); io_read(0, 1)
  }
  pub fn ptr_index(x: G) -> G {
    let p = store(x);
    ptr_val(p)
  }

  -- Nested expressions
  pub fn dot(a: (G, G), b: (G, G)) -> G {
    let a0 = proj(a, 0);
    let a1 = proj(a, 1);
    let b0 = proj(b, 0);
    let b1 = proj(b, 1);
    (a0 * b0) + (a1 * b1)
  }

  pub fn deep_chain(x: G) -> G {
    let a = x + 1;
    let b = a + 1;
    let c = b + 1;
    let d = c + 1;
    let e = d + 1;
    e
  }

  -- Type aliases
  pub fn aliased(x: MyField) -> MyField { x + 1 }
  pub fn pair_sum(p: Pair‹G›) -> G {
    match p { (a, b) => a + b, }
  }

  pub fn factorial(n: G) -> G {
    match n {
      0 => 1,
      _ => n * factorial(n - 1),
    }
  }

  -- Unconstrained call: same semantics as constrained, exercises the
  -- `unconstrained` flag through the pipeline.
  pub fn call_helper_unc(x: G) -> G { #helper(x) + 1 }

  -- Recursion
  pub fn fib(n: G) -> G {
    let z = eq_zero(n);
    match z {
      1 => 0,
      _ => let z1 = eq_zero(n - 1);
           match z1 {
             1 => 1,
             _ => fib(n - 1) + fib(n - 2),
           },
    }
  }

  -- Mutual recursion
  pub fn is_even(n: G) -> G {
    let z = eq_zero(n);
    match z {
      1 => 1,
      _ => is_odd(n - 1),
    }
  }
  pub fn is_odd(n: G) -> G {
    let z = eq_zero(n);
    match z {
      1 => 0,
      _ => is_even(n - 1),
    }
  }

  -- Match end-to-end (single-level, .or, nested, .pointer, mixed,
  -- non-`.var` scrutinee)
  pub fn unwrap_or(opt: MyOpt, dflt: G) -> G {
    match opt {
      MyOpt.Some(x) => x,
      MyOpt.None    => dflt,
    }
  }

  pub fn sum_pair(p: APair) -> G {
    match p { APair.Mk(a, b) => a + b, }
  }

  pub fn fst_field(p: APair) -> G {
    match p { APair.Mk(a, _) => a, }
  }

  fn mk_some(x: G) -> MyOpt { MyOpt.Some(x) }
  pub fn unwrap_call(x: G) -> G {
    match mk_some(x) {
      MyOpt.Some(v) => v,
      MyOpt.None    => 0,
    }
  }

  pub fn or_match(x: G) -> G {
    match x {
      0 | 1 => 42,
      _     => x,
    }
  }

  -- Active branch differs from default depending on value
  pub fn match_mul(x: G) -> G {
    match x {
      0 => 0,
      _ => x * x * x,
    }
  }

  pub fn multi_match(x: G) -> G {
    match x {
      0 => 100,
      1 => 200,
      2 => 300,
      _ => 999,
    }
  }

  pub fn early_ret(x: G) -> G {
    match x {
      0 => return 100,
      _ => x + 1,
    }
  }

  pub fn deep(o: MyOpt2) -> G {
    match o {
      MyOpt2.Some2(MyOpt.Some(x)) => x,
      _                           => 99,
    }
  }

  pub fn tag_lookup(a: G, b: G) -> G {
    match (a, b) {
      (x, 1) => x,
      (_, y) => y,
    }
  }

  pub fn nested_match(opt: MyOpt, fb: MyOpt) -> G {
    match opt {
      MyOpt.Some(x) => x,
      MyOpt.None    => match fb {
        MyOpt.Some(y) => y,
        MyOpt.None    => 0,
      },
    }
  }

  pub fn dot_pair(p: (G, G)) -> G {
    match p { (a, b) => a * b, }
  }

  pub fn arr_fst(a: [G; 3]) -> G {
    match a { [x, _, _] => x, }
  }

  pub fn deref_match(x: G) -> G {
    let p = store(x);
    match p { &v => v + 10, }
  }

  pub fn deep_deep(w: Wrap) -> G {
    match w {
      Wrap.W(MyOpt2.Some2(MyOpt.Some(x))) => x,
      _                                   => 7,
    }
  }

  enum Nat { Zero, Succ(&Nat) }
  pub fn pointer_match() -> G {
    let two = Nat.Succ(store(Nat.Succ(store(Nat.Zero))));
    match two {
      Nat.Succ(&Nat.Succ(&Nat.Zero)) => 1,
      _                              => 0,
    }
  }

  -- Multi-element tuple destructuring + projection
  pub fn projections(a: (G, G, G, G, G)) -> (G, G) {
    (proj(a, 1), proj(a, 3))
  }

  -- Slice + array index combined
  pub fn slice_and_get(a: [G; 5]) -> [G; 2] {
    let left = a[0..2];
    let right = a[3..5];
    [left[1], right[0]]
  }

  -- Full IO: get_info + read + write + set_info
  pub fn read_write_io() {
    let (idx, len) = io_get_info([0]);
    let xs: [G; 4] = io_read(idx, 4);
    io_write(xs);
    io_set_info([1], idx, len + 4);
  }

  -- u8 shifts + bit decomposition chain
  pub fn shr_shr_shl_decompose(byte: G) -> [G; 8] {
    let s1 = u8_shift_right(byte);
    let s2 = u8_shift_right(s1);
    let s3 = u8_shift_left(s2);
    u8_bit_decomposition(s3)
  }

  -- u8_add and u8_xor combined
  pub fn u8_add_xor(i: G, j: G) -> ((G, G), (G, G)) {
    let xor = u8_xor(i, j);
    (u8_add(xor, i), u8_add(xor, j))
  }

  -- `set` on an array of tuples — exercises set with multi-G elements
  pub fn array_set(arr: [(G, G); 3]) -> [(G, G); 3] {
    set(arr, 1, (0, 0))
  }

  -- `proj` on a mixed-size tuple — offset arithmetic with non-uniform
  -- element sizes
  pub fn proj_mixed(t: (G, (G, G), G)) -> (G, G) {
    proj(t, 1)
  }

  -- `let` with non-trivial pattern → simplifier hoists into match
  pub fn deconstruct_tuple(as: (G, G, G, G, G)) -> (G, G) {
    let (_, b, _, d, _) = as;
    (b, d)
  }

  pub fn deconstruct_array(as: [G; 5]) -> [G; 2] {
    let [_, b, _, d, _] = as;
    [b, d]
  }

  -- Array return assembled from multiple eq_zero calls
  pub fn eq_zero_dummy(a: G, b: G) -> [G; 4] {
    let c = 0;
    let d = 101;
    [eq_zero(a), eq_zero(b), eq_zero(c), eq_zero(d)]
  }

  -- Datatype with multiple-arity constructors (similar to a Shape ADT)
  enum Shape {
    Circle(G),
    Rect(G, G),
    Tri(G, G, G)
  }
  pub fn shape_area(s: Shape) -> G {
    match s {
      Shape.Circle(r)    => r * r,
      Shape.Rect(w, h)   => w * h,
      Shape.Tri(a, b, c) => a + b + c,
    }
  }

  -- Nested match with field patterns
  pub fn nested_match2(x: G, y: G) -> G {
    match x {
      0 => match y {
        0 => 10,
        _ => 20,
      },
      _ => match y {
        0 => 30,
        _ => x + y,
      },
    }
  }

  -- Recursive datatype via pointer indirection
  fn sum_list(l: MyList) -> G {
    match l {
      MyList.Nil          => 0,
      MyList.Cons(h, t)   => h + sum_list(load(t)),
    }
  }

  pub fn run() -> G {
    let p0 = store(MyList.Nil);
    let p1 = store(MyList.Cons(3, p0));
    let p2 = store(MyList.Cons(2, p1));
    sum_list(MyList.Cons(1, p2))
  }

  -- ----- Direct ports from Tests/Aiur/Aiur.lean ---------------------------

  -- Trivial arithmetic
  pub fn id(n: G) -> G { n }
  pub fn proj1(a: G, _b: G) -> G { a }
  pub fn sum(x: G, y: G) -> G { x + y }
  pub fn prod(x: G, y: G) -> G { x * y }
  pub fn sum_prod(x: G, y: G, z: G) -> G { (x + y) * z }

  -- Assertion (returns unit)
  pub fn assert_eq_trivial() {
    assert_eq!([1, 2, 3], [1, 2, 3]);
  }

  -- Store/load named like Aiur
  pub fn store_and_load(x: G) -> G {
    load(store(x))
  }

  -- u8 op single-call wrappers
  pub fn u8_sub_function(i: G, j: G) -> (G, G) { u8_sub(i, j) }
  pub fn u8_less_than_function(i: G, j: G) -> G { u8_less_than(i, j) }
  pub fn u8_and_function(i: G, j: G) -> G { u8_and(i, j) }
  pub fn u8_or_function(i: G, j: G) -> G { u8_or(i, j) }

  -- u32 less-than wrapper (named to match Aiur)
  pub fn u32_less_than_function(x: G, y: G) -> G { u32_less_than(x, y) }

  -- EqZero degree-tracking regression
  pub fn eq_zero_degree_desync(x: G) -> G {
    let a = eq_zero(x);
    let b = 100;
    let c = x * x;
    let d = c * c;
    a + b + d
  }

  -- Array get + set boundary cases on array-of-tuples
  pub fn array_get_set(arr: [(G, G); 3]) -> [(G, G); 3] {
    let p = arr[2];
    set(arr, 0, p)
  }

  -- Unconstrained recursion mirroring `fib`
  pub fn unconstrained_fibonacci(n: G) -> G {
    let z = eq_zero(n);
    match z {
      1 => 0,
      _ => let z1 = eq_zero(n - 1);
           match z1 {
             1 => 1,
             _ => #unconstrained_fibonacci(n - 1) + unconstrained_fibonacci(n - 2),
           },
    }
  }

  -- Sel-gating: polynomial constraints (Mul, EqZero, AssertEq)
  -- Non-exhaustive match on field literal; only the 0 arm is reachable here.
  pub fn match_poly_ops(x: G) -> (G, G) {
    match 0 {
      0 => assert_eq!([x], [x]); (x * x, eq_zero(x)),
      1 => assert_eq!([0], [1]); ((x + 1) * (x + 1), eq_zero(x + 1)),
    }
  }

  -- Sel-gating: function and memory lookup multiplicity
  pub fn match_lookup_ops(x: G) -> (G, G) {
    match 0 {
      0 => (id(x), load(store(x))),
      1 => (id(x), load(store(x))),
    }
  }

  -- Nested type aliases
  type U8 = G
  type U16 = (U8, U8)
  type U32 = (U16, U16)
  type U64 = [U8; 8]

  pub fn alias_conversion(x: U64) -> U32 {
    ((x[0], x[1]), (x[2], x[3]))
  }

  -- Mutual recursion on `Nat` datatype (structural, pointer-based)
  fn nat_even(m: Nat) -> G {
    match m {
      Nat.Zero    => 1,
      Nat.Succ(m) => nat_odd(load(m)),
    }
  }
  fn nat_odd(m: Nat) -> G {
    match m {
      Nat.Zero    => 0,
      Nat.Succ(m) => nat_even(load(m)),
    }
  }

  pub fn is_0_even() -> G { nat_even(Nat.Zero) }
  pub fn is_1_even() -> G { nat_even(Nat.Succ(store(Nat.Zero))) }
  pub fn is_2_even() -> G {
    nat_even(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))
  }
  pub fn is_0_odd() -> G { nat_odd(Nat.Zero) }
  pub fn is_1_odd() -> G { nat_odd(Nat.Succ(store(Nat.Zero))) }

  -- Non-tail match (match bound to let, used afterwards)
  pub fn ntm_basic(a: G) -> G {
    let y = match a { 0 => 100, 1 => 200, _ => a * a, };
    y + 1
  }

  pub fn ntm_sequential(a: G, b: G) -> G {
    let x = match a { 0 => 1, 1 => 2, _ => a, };
    let y = match b { 0 => 10, 1 => 20, _ => b, };
    x + y
  }

  pub fn ntm_then_tail_match(a: G, b: G) -> G {
    let x = match a { 0 => 100, _ => a, };
    match b { 0 => x, _ => x + b, }
  }

  -- Non-tail match inside a tail match branch
  pub fn ntm_inside_tail_match(flag: G, a: G) -> G {
    match flag {
      0 =>
        let x = match a { 0 => 100, 1 => 200, _ => a * a, };
        x + 1,
      _ => a,
    }
  }

  -- Non-tail match with store/load in branches (lookup gating)
  pub fn ntm_store_load(a: G) -> G {
    let x = match a { 0 => load(store(42)), _ => load(store(a)), };
    x + 1
  }

  -- Non-tail match with function calls in branches
  fn ntm_helper(x: G) -> G { x * x + 1 }
  pub fn ntm_call_in_branch(a: G) -> G {
    let x = match a { 0 => ntm_helper(5), _ => ntm_helper(a), };
    x + 1
  }

  -- Pre-branch constant multiplied in a branch (no default)
  pub fn ntm_const_mul(a: G) -> G {
    let c = 5;
    let x = match a { 0 => c * c, 1 => c * c * c, };
    x + 1
  }

  -- Non-tail match returning a tuple (multi-output merge)
  pub fn ntm_tuple(a: G) -> (G, G) {
    let (x, y) = match a { 0 => (10, 20), 1 => (30, 40), _ => (a, a * a), };
    (x + 1, y + 1)
  }

  -- Non-tail match with early return
  pub fn ntm_early_ret(a: G) -> G {
    let y = match a { 0 => return 999, _ => a + a, };
    y * y
  }

  -- Nested non-tail match
  pub fn ntm_nested(a: G, b: G) -> G {
    let x = match a {
      0 => match b { 0 => return 0, _ => 42, },
      _ => 99,
    };
    x + 1
  }

  -- Large non-tail match (8 branches, no default)
  pub fn ntm_large(a: G) -> G {
    let x = match a {
      0 => 10, 1 => 20, 2 => 30, 3 => 40,
      4 => 50, 5 => 60, 6 => 70, 7 => 80,
    };
    x + 1
  }

  -- Refutable pattern let with stored enum (Shape through pointer)
  pub fn ntm_shape_let() -> G {
    let s = store(Shape.Rect(3, 4));
    let Shape.Rect(w, h) = load(s);
    w + h
  }

  -- Templates (parametric datatypes + functions)
  enum Wrapper‹A› { MkW(A) }

  fn unwrap‹A›(w: Wrapper‹A›) -> A {
    match w {
      Wrapper.MkW(x) => x,
    }
  }

  pub fn template_basic() -> G {
    let w = Wrapper.MkW(42);
    unwrap(w)
  }

  enum TOpt‹A› { TSome(A), TNone }

  fn t_unwrap_or‹A›(opt: TOpt‹A›, default: A) -> A {
    match opt {
      TOpt.TSome(x) => x,
      TOpt.TNone    => default,
    }
  }

  pub fn template_unwrap_some() -> G {
    let opt = TOpt.TSome(42);
    t_unwrap_or(opt, 0)
  }

  pub fn template_unwrap_none() -> G {
    let opt = TOpt.TNone;
    t_unwrap_or(opt, 99)
  }

  enum TPair‹A, B› { TMk(A, B) }

  fn tpair_first‹A, B›(p: TPair‹A, B›) -> A {
    match p { TPair.TMk(a, _) => a, }
  }
  fn tpair_second‹A, B›(p: TPair‹A, B›) -> B {
    match p { TPair.TMk(_, b) => b, }
  }

  pub fn template_pair() -> (G, G) {
    let p = TPair.TMk(10, 20);
    (tpair_first(p), tpair_second(p))
  }

  pub fn template_nested() -> G {
    let inner = TPair.TMk(3, 4);
    let opt = TOpt.TSome(inner);
    let p = t_unwrap_or(opt, TPair.TMk(0, 0));
    tpair_first(p) + tpair_second(p)
  }

  -- Template function calling another template function: exercises the
  -- worklist's transitive specialization (unwrap_pair on Wrapper‹TPair‹G,G››).
  fn unwrap_pair‹A, B›(w: Wrapper‹TPair‹A, B››) -> (A, B) {
    let p = unwrap(w);
    (tpair_first(p), tpair_second(p))
  }

  pub fn template_trans() -> G {
    let p = TPair.TMk(7, 8);
    let w = Wrapper.MkW(p);
    let (a, b) = unwrap_pair(w);
    a + b
  }

  -- Same template instantiated with different concrete types in one program:
  -- mono map must produce distinct monomorphic copies for `Wrapper‹G›` and
  -- `Wrapper‹TPair‹G, G››`.
  pub fn template_multi() -> G {
    let w1 = Wrapper.MkW(11);
    let w2 = Wrapper.MkW(TPair.TMk(3, 5));
    let v1 = unwrap(w1);
    let p = unwrap(w2);
    v1 + tpair_first(p) + tpair_second(p)
  }

  -- Template instantiated at an array type: exercises `Typ.appendNameLimbs`
  -- on the `[G; n]` arm (mangles to `G_3`).
  pub fn template_array() -> G {
    let w = Wrapper.MkW([10, 20, 30]);
    let arr = unwrap(w);
    arr[0] + arr[1] + arr[2]
  }

  -- Template with tuple arg type-argument.
  pub fn template_tuple_arg() -> G {
    let w = Wrapper.MkW((4, 5));
    let p = unwrap(w);
    proj(p, 0) + proj(p, 1)
  }

  -- Template with pointer arg type-argument: Wrapper‹&G›.
  pub fn template_pointer_arg() -> G {
    let p = store(77);
    let w = Wrapper.MkW(p);
    let p' = unwrap(w);
    load(p')
  }

  -- Mutual-recursive templated datatype fields: exercises the worklist's
  -- iterative discovery through recursive type references.
  enum TMaybe‹A› { TJust(A), TNothing }
  fn t_or_default‹A›(m: TMaybe‹A›, d: A) -> A {
    match m {
      TMaybe.TJust(x) => x,
      TMaybe.TNothing => d,
    }
  }
  pub fn template_chain() -> G {
    -- Three specialisations of TMaybe: on G, on (G,G), on [G;2].
    let m1 = TMaybe.TJust(42);
    let m2 = TMaybe.TJust((3, 5));
    let m3 = TMaybe.TNothing;
    let v1 = t_or_default(m1, 0);
    let p  = t_or_default(m2, (0, 0));
    let arr : [G; 2] = t_or_default(m3, [10, 20]);
    v1 + proj(p, 0) + proj(p, 1) + arr[0] + arr[1]
  }

  -- Non-templated function consuming a specialised template (non-recursive): exercises
  -- the worklist seeding from a non-template function's input type.
  fn first_elt_g(l: TList‹G›) -> G {
    match l {
      TList.TNil       => 0,
      TList.TCons(h, _) => h,
    }
  }

  pub fn template_simple_consumer() -> G {
    let l0 : TList‹G› = TList.TNil;
    let l1 : TList‹G› = TList.TCons(42, store(l0));
    first_elt_g(l1)
  }


  -- Recursive templated datatype: TList‹A› with a pointer-back to itself.
  -- Exercises the worklist on self-referential type arguments.
  enum TList‹A› { TNil, TCons(A, &TList‹A›) }

  fn tlist_len‹A›(l: TList‹A›) -> G {
    match l {
      TList.TNil       => 0,
      TList.TCons(_, t) => 1 + tlist_len(load(t)),
    }
  }

  -- Reproduce the bug: recursive non-templated consumer of specialised template.
  fn tlist_sum_g(l: TList‹G›) -> G {
    match l {
      TList.TNil       => 0,
      TList.TCons(h, t) => h + tlist_sum_g(load(t)),
    }
  }

  pub fn template_rec_consumer() -> G {
    let l0 : TList‹G› = TList.TNil;
    let l1 : TList‹G› = TList.TCons(5, store(l0));
    tlist_sum_g(l1)
  }

  -- Two distinct specialisations of the same recursive template in one program.
  pub fn template_multi_rec() -> G {
    let l0g : TList‹G› = TList.TNil;
    let l1g : TList‹G› = TList.TCons(7, store(l0g));
    let l2g : TList‹G› = TList.TCons(8, store(l1g));
    let l0p : TList‹(G, G)› = TList.TNil;
    let l1p : TList‹(G, G)› = TList.TCons((1, 2), store(l0p));
    tlist_sum_g(l2g) + tlist_len(l1p)
  }

  -- Non-templated match on a tuple-arg specialisation: the fresh match
  -- compiler vars for `h` get type `(G, G)` (via the A=(G,G) substitution).
  fn tlist_first_pair(l: TList‹(G, G)›) -> G {
    match l {
      TList.TNil       => 0,
      TList.TCons(p, _) => proj(p, 0) + proj(p, 1),
    }
  }

  pub fn template_tuple_match() -> G {
    let l0 : TList‹(G, G)› = TList.TNil;
    let l1 : TList‹(G, G)› = TList.TCons((3, 4), store(l0));
    tlist_first_pair(l1)
  }

  -- Refutable-let on a templated constructor: flows through simplify's
  -- match compiler, which is where the `constructorArgTypes` bug lived.
  pub fn template_refutable_let() -> G {
    let l : TList‹G› = TList.TCons(77, store(TList.TNil));
    let TList.TCons(h, _) = l;
    h
  }

  -- Pointer-deref pattern on a template: `TList.TCons(_, &rest) => ...`
  -- uses pointer sub-patterns inside a templated constructor.
  fn tlist_second(l: TList‹G›) -> G {
    match l {
      TList.TNil       => 0,
      TList.TCons(_, &rest) =>
        match rest {
          TList.TNil       => 0,
          TList.TCons(h, _) => h,
        },
    }
  }

  pub fn template_pointer_pat() -> G {
    let l0 : TList‹G› = TList.TNil;
    let l1 : TList‹G› = TList.TCons(20, store(l0));
    let l2 : TList‹G› = TList.TCons(10, store(l1));
    tlist_second(l2)
  }

  -- Template embedded in another template: Wrapper‹TList‹G››.
  pub fn template_nested_rec() -> G {
    let inner : TList‹G› = TList.TCons(42, store(TList.TNil));
    let w = Wrapper.MkW(inner);
    let inner' = unwrap(w);
    match inner' {
      TList.TNil       => 0,
      TList.TCons(h, _) => h,
    }
  }

  -- Mutually recursive non-templated functions over a templated type.
  fn tlist_mut_a(l: TList‹G›) -> G {
    match l {
      TList.TNil       => 0,
      TList.TCons(h, t) => h + tlist_mut_b(load(t)),
    }
  }
  fn tlist_mut_b(l: TList‹G›) -> G {
    match l {
      TList.TNil       => 0,
      TList.TCons(h, t) => h * 2 + tlist_mut_a(load(t)),
    }
  }
  pub fn template_mutual_rec() -> G {
    let l0 : TList‹G› = TList.TNil;
    let l1 : TList‹G› = TList.TCons(1, store(l0));
    let l2 : TList‹G› = TList.TCons(2, store(l1));
    let l3 : TList‹G› = TList.TCons(3, store(l2));
    tlist_mut_a(l3)
  }

  -- Two templated args in one function: TPair‹A, B›-style through a template.
  fn tpair_of_wrappers‹A, B›(w1: Wrapper‹A›, w2: Wrapper‹B›) -> (A, B) {
    (unwrap(w1), unwrap(w2))
  }
  pub fn template_dual_args() -> G {
    let w1 = Wrapper.MkW(11);
    let w2 = Wrapper.MkW((3, 4));
    let p = tpair_of_wrappers(w1, w2);
    proj(p, 0) + proj(proj(p, 1), 0) + proj(proj(p, 1), 1)
  }

  -- Unconstrained call to a template: `#unwrap(w)`.
  pub fn template_unconstrained() -> G {
    let w = Wrapper.MkW(99);
    #unwrap(w)
  }

  -- Nested refutable lets with pointer deref, on a templated type.
  pub fn template_nested_refutable() -> G {
    let inner : TList‹G› = TList.TCons(7, store(TList.TNil));
    let wrapped = TList.TCons(5, store(inner));
    let TList.TCons(h1, &rest) = wrapped;
    let TList.TCons(h2, _) = rest;
    h1 + h2
  }

  pub fn template_rec_list() -> G {
    let l0 : TList‹G› = TList.TNil;
    let l1 : TList‹G› = TList.TCons(10, store(l0));
    let l2 : TList‹G› = TList.TCons(20, store(l1));
    let l3 : TList‹G› = TList.TCons(30, store(l2));
    tlist_len(l3)
  }



  -- Deeper nesting: Wrapper‹TMaybe‹G››.
  pub fn template_deep_nest() -> G {
    let inner = TMaybe.TJust(100);
    let w = Wrapper.MkW(inner);
    let m = unwrap(w);
    t_or_default(m, 0)
  }

  -- ----- Further ports from Tests/Aiur/Aiur.lean ---------------------------

  -- Fibonacci using the let-then-match style (distinct from the inline `fib`
  -- above): catches simplifier regressions around let-bound scrutinees.
  pub fn fibonacci(n: G) -> G {
    match n {
      0 => 1,
      _ =>
        let n_minus_1 = n - 1;
        match n_minus_1 {
          0 => 1,
          _ =>
            let n_minus_2 = n_minus_1 - 1;
            fibonacci(n_minus_1) + fibonacci(n_minus_2),
        },
    }
  }

  -- Non-tail match returning a tuple that's then destructured: exercises the
  -- multi-output merge + subsequent projection.
  fn ntm_tuple_sum(a: G) -> G {
    let (x, y) = ntm_tuple(a);
    x + y
  }

  -- Refutable-pattern let destructuring a `Nat` through a pointer.
  fn ntm_ctor_let(n: Nat) -> G {
    let Nat.Succ(&inner) = n;
    match inner { Nat.Zero => 1, Nat.Succ(_) => 2, }
  }

  -- Non-tail match branches with asymmetric lookup counts; continuation also
  -- has a lookup. Exercises `sharedLookups` layout computation.
  fn ntm_mixed_lookups(a: G) -> G {
    let x = match a {
      0 => 42,
      _ => load(store(a)),
    };
    load(store(x + 1))
  }

  -- Asymmetric function-call lookups across branches (heavy vs light callee).
  fn ntm_heavy_calls(a: G) -> G { load(store(load(store(a)))) }
  fn ntm_light_calls(a: G) -> G { a + 1 }
  fn ntm_asymmetric_lookups(a: G, b: G) -> G {
    let x = match a {
      0 => ntm_heavy_calls(b),
      1 => ntm_light_calls(b),
      _ => b,
    };
    load(store(x))
  }

  -- 8-branch non-tail match inside a tail-match branch with multiple outer
  -- arms: stresses sharedAux over-count under nested matches.
  fn ntm_large_inside_tail(outer: G, inner: G) -> G {
    match outer {
      0 => inner,
      1 => inner + 1,
      2 =>
        let x = match inner {
          0 => 10, 1 => 20, 2 => 30, 3 => 40,
          4 => 50, 5 => 60, 6 => 70, 7 => 80,
        };
        x + 1,
      _ => inner * inner,
    }
  }

  -- Refutable-pattern let (through pointer) nested inside a tail match.
  fn ntm_refutable_let_in_match(flag: G) -> G {
    let list = store(Nat.Succ(store(Nat.Zero)));
    match flag {
      0 =>
        let Nat.Succ(&inner) = load(list);
        match inner { Nat.Zero => 42, _ => 99, },
      _ => 0,
    }
  }

  -- Heavy-explicit branches: some constructor arms have pointer derefs that
  -- generate load ops, while others don't. Used to be a sharedAux watermark
  -- regression in the v1 pipeline.
  enum CKind {
    A(G),
    B(G, &Nat),
    C(G),
    D(G, G),
    E(G, &Nat),
    F(G)
  }

  fn ntm_heavy_explicit(flag: G, kind: CKind) -> G {
    match flag {
      0 =>
        let val = match kind {
          CKind.A(x) => x,
          CKind.B(x, &extra) =>
            match extra { Nat.Zero => x, Nat.Succ(_) => x + 10, },
          CKind.C(x) => x * x,
          CKind.D(x, y) => x + y,
          CKind.E(x, &extra) =>
            match extra { Nat.Zero => x * x, Nat.Succ(_) => x + 100, },
          CKind.F(x) => x,
        };
        val + 1,
      _ => 0,
    }
  }

  -- 6-branch match with mixed per-branch lookup profiles, feeding a recursive
  -- outer call: replicates the convert_all pattern from IxVM.
  fn ntm_cv_a2(x: G) -> G { x + 1 }
  fn ntm_cv_b2(x: G, extra: Nat) -> G {
    match extra { Nat.Zero => x, Nat.Succ(_) => x + 10, }
  }
  fn ntm_cv_c2(x: G) -> G { x * x }
  fn ntm_cv_d2(x: G, y: G) -> G { x + y }
  fn ntm_cv_e2(x: G, extra: Nat) -> G {
    match extra { Nat.Zero => x * x, Nat.Succ(_) => x + 100, }
  }
  fn ntm_cv_f2(x: G) -> G { load(store(x)) }

  fn ntm_convert_all(inputs: Nat, kind: CKind) -> G {
    match inputs {
      Nat.Zero => 0,
      Nat.Succ(&rest) =>
        let ci = match kind {
          CKind.A(x) => ntm_cv_a2(x),
          CKind.B(x, &extra) => ntm_cv_b2(x, extra),
          CKind.C(x) => ntm_cv_c2(x),
          CKind.D(x, y) => ntm_cv_d2(x, y),
          CKind.E(x, &extra) => ntm_cv_e2(x, extra),
          CKind.F(x) => ntm_cv_f2(x),
        };
        let _ = store(ci);
        ci + ntm_convert_all(rest, kind),
    }
  }

  -- Exercise all 6 CKind branches + both Nil/Cons paths of the outer match.
  pub fn ntm_recursive_test() -> G {
    let zero = Nat.Zero;
    let one = Nat.Succ(store(Nat.Zero));
    let two = Nat.Succ(store(Nat.Succ(store(Nat.Zero))));
    let r1 = ntm_convert_all(two, CKind.A(10));
    let r2 = ntm_convert_all(one, CKind.B(5, store(Nat.Succ(store(Nat.Zero)))));
    let r3 = ntm_convert_all(two, CKind.C(3));
    let r4 = ntm_convert_all(one, CKind.D(2, 3));
    let r5 = ntm_convert_all(one, CKind.E(7, store(Nat.Zero)));
    let r6 = ntm_convert_all(two, CKind.F(4));
    let r7 = ntm_convert_all(zero, CKind.A(99));
    r1 + r2 + r3 + r4 + r5 + r6 + r7
  }

  -- Large end-to-end entry aggregating the whole ntm_* family.
  pub fn non_tail_match() -> G {
    let r1 = ntm_basic(0) + ntm_basic(5);
    let r2 = ntm_early_ret(0) + ntm_early_ret(3);
    let r3 = ntm_sequential(1, 1);
    let r4 = ntm_nested(0, 1) + ntm_nested(1, 0);
    let r5 = ntm_const_mul(0);
    let r6 = ntm_tuple_sum(0);
    let r7 = ntm_then_tail_match(0, 3);
    let r8 = ntm_call_in_branch(0);
    let r9 = ntm_store_load(0);
    let r10 = ntm_large(0);
    let r11 = ntm_ctor_let(Nat.Succ(store(Nat.Zero)));
    let r12 = ntm_mixed_lookups(0);
    let r13 = ntm_shape_let();
    let r14 = ntm_asymmetric_lookups(1, 10);
    let r15 = ntm_inside_tail_match(0, 0) + ntm_inside_tail_match(0, 1)
            + ntm_inside_tail_match(1, 5);
    let r16 = ntm_large_inside_tail(2, 0) + ntm_large_inside_tail(2, 3)
            + ntm_large_inside_tail(2, 7) + ntm_large_inside_tail(0, 5)
            + ntm_large_inside_tail(1, 5) + ntm_large_inside_tail(3, 4);
    let r17 = ntm_heavy_explicit(0, CKind.B(5, store(Nat.Succ(store(Nat.Zero)))))
            + ntm_heavy_explicit(0, CKind.A(7)) + ntm_heavy_explicit(1, CKind.A(99));
    let r18 = ntm_refutable_let_in_match(0);
    let r19 = ntm_recursive_test();
    let r20 = ntm_nested(0, 0);
    r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10
    + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19 + r20
  }
⟧

/-- Generic helper: run both evaluators on `entryName` with `inputs` as
the source-level argument list, asserting that the flat-encoded return
value and the `IOBuffer` agree. An optional `io` arg seeds both evaluators
with a pre-populated `IOBuffer`. -/
def runAgreement
    (label : String) (entryName : String)
    (inputs : List Value) (io : IOBuffer := default) (fuel : Nat := 1000) :
    TestSeq := Id.run do
  let globalName : Global := .init entryName
  match toplevel.mkDecls with
  | .error _ => pure (test s!"{label}: mkDecls" false)
  | .ok decls =>
    match Source.Eval.runFunction decls globalName inputs io fuel with
    | .error e => pure (test s!"{label}: Source.Eval ({repr e})" false)
    | .ok (srcVal, srcIo) =>
      match toplevel.compile with
      | .error e => pure (test s!"{label}: Compile ({e})" false)
      | .ok ct =>
        let funIdx := ct.getFuncIdx (.mkSimple entryName) |>.getD 0
        let funcIdx := fun g => ct.nameMap[g]?
        let flatArgs : Array Aiur.G := inputs.foldl
          (fun acc v => acc ++ flattenValue decls funcIdx v) #[]
        match Bytecode.Eval.runFunction ct.bytecode funIdx flatArgs io fuel with
        | .error e => pure (test s!"{label}: Bytecode.Eval ({repr e})" false)
        | .ok (bcOut, bcIo) =>
          let srcFlat := flattenValue decls funcIdx srcVal
          let valTest := test s!"{label}: values agree (src={srcFlat}, bc={bcOut})"
            (srcFlat == bcOut)
          let ioTest  := test s!"{label}: io agree" (srcIo == bcIo)
          pure (valTest ++ ioTest)

private def myOpt (limb : String) : Global := Global.init "MyOpt" |>.pushNamespace limb
private def myOpt2 (limb : String) : Global := Global.init "MyOpt2" |>.pushNamespace limb
private def wrap (limb : String) : Global := Global.init "Wrap" |>.pushNamespace limb
private def apair (limb : String) : Global := Global.init "APair" |>.pushNamespace limb

def tests : TestSeq :=
  -- Arithmetic + simple control flow
  runAgreement "add_one(41)" "add_one" [41] ++
  runAgreement "arith(3,4)" "arith" [3, 4] ++
  runAgreement "fst((7,9))" "fst"
    [.tuple #[7, 9]] ++
  runAgreement "second(#[10,20,30])" "second"
    [.array #[10, 20, 30]] ++
  runAgreement "roundtrip(99)" "roundtrip" [99] ++
  runAgreement "call_helper(5)" "call_helper" [5] ++
  runAgreement "call_helper_unc(5)" "call_helper_unc" [5] ++
  runAgreement "deep_chain(0)" "deep_chain" [0] ++
  runAgreement "dot((3,4),(5,6))" "dot"
    [.tuple #[3, 4], .tuple #[5, 6]] ++
  -- u8 / u32 / slice / set / asserts / IO
  runAgreement "xor_bytes(0xAA,0x55)" "xor_bytes" [0xAA, 0x55] ++
  runAgreement "add8(200,100)" "add8" [200, 100] ++
  runAgreement "lt32(3,5)" "lt32" [3, 5] ++
  runAgreement "lt32(5,3)" "lt32" [5, 3] ++
  runAgreement "middle(#[1,2,3,4])" "middle"
    [.array #[1, 2, 3, 4]] ++
  runAgreement "set_mid(#[1,2,3])" "set_mid"
    [.array #[1, 2, 3]] ++
  runAgreement "assert_same(7,7)" "assert_same" [7, 7] ++
  runAgreement "io_roundtrip(55)" "io_roundtrip" [55] ++
  runAgreement "ptr_index(77)" "ptr_index" [77] ++
  -- Type aliases
  runAgreement "aliased(41)" "aliased" [41] ++
  runAgreement "pair_sum((4,5))" "pair_sum"
    [.tuple #[4, 5]] ++
  -- Recursion + mutual recursion
  runAgreement "fib(5)" "fib" [5] ++
  runAgreement "fib(6)" "fib" [6] ++
  runAgreement "factorial(5)" "factorial" [5] ++
  runAgreement "factorial(6)" "factorial" [6] ++
  runAgreement "is_even(4)" "is_even" [4] ++
  runAgreement "is_even(5)" "is_even" [5] ++
  runAgreement "is_odd(3)" "is_odd" [3] ++
  -- Pattern matching
  runAgreement "unwrap_or(Some 7, 0)" "unwrap_or"
    [.ctor (myOpt "Some") #[7], 0] ++
  runAgreement "unwrap_or(None, 99)" "unwrap_or"
    [.ctor (myOpt "None") #[], 99] ++
  runAgreement "sum_pair(Mk 10 20)" "sum_pair"
    [.ctor (apair "Mk") #[10, 20]] ++
  runAgreement "fst_field(Mk 42 99)" "fst_field"
    [.ctor (apair "Mk") #[42, 99]] ++
  runAgreement "unwrap_call(13)" "unwrap_call" [13] ++
  runAgreement "or_match(0)" "or_match" [0] ++
  runAgreement "or_match(1)" "or_match" [1] ++
  runAgreement "or_match(5)" "or_match" [5] ++
  runAgreement "match_mul(0)" "match_mul" [0] ++
  runAgreement "match_mul(2)" "match_mul" [2] ++
  runAgreement "match_mul(3)" "match_mul" [3] ++
  runAgreement "multi_match(0)" "multi_match" [0] ++
  runAgreement "multi_match(1)" "multi_match" [1] ++
  runAgreement "multi_match(2)" "multi_match" [2] ++
  runAgreement "multi_match(5)" "multi_match" [5] ++
  runAgreement "multi_match(7)" "multi_match" [7] ++
  runAgreement "early_ret(0)" "early_ret" [0] ++
  runAgreement "early_ret(5)" "early_ret" [5] ++
  runAgreement "deep(Some2(Some 7))" "deep"
    [.ctor (myOpt2 "Some2") #[.ctor (myOpt "Some") #[7]]] ++
  runAgreement "deep(Some2(None))" "deep"
    [.ctor (myOpt2 "Some2") #[.ctor (myOpt "None") #[]]] ++
  runAgreement "deep(None2)" "deep"
    [.ctor (myOpt2 "None2") #[]] ++
  runAgreement "tag_lookup(7,1)" "tag_lookup" [7, 1] ++
  runAgreement "tag_lookup(7,2)" "tag_lookup" [7, 2] ++
  runAgreement "nested_match(Some 5, Some 99)" "nested_match"
    [.ctor (myOpt "Some") #[5], .ctor (myOpt "Some") #[99]] ++
  runAgreement "nested_match(None, Some 99)" "nested_match"
    [.ctor (myOpt "None") #[], .ctor (myOpt "Some") #[99]] ++
  runAgreement "nested_match(None, None)" "nested_match"
    [.ctor (myOpt "None") #[], .ctor (myOpt "None") #[]] ++
  runAgreement "dot_pair((6,7))" "dot_pair"
    [.tuple #[6, 7]] ++
  runAgreement "arr_fst(#[11,22,33])" "arr_fst"
    [.array #[11, 22, 33]] ++
  runAgreement "deref_match(15)" "deref_match" [15] ++
  runAgreement "deep_deep(W (Some2 (Some 42)))" "deep_deep"
    [.ctor (wrap "W")
      #[.ctor (myOpt2 "Some2")
          #[.ctor (myOpt "Some") #[42]]]] ++
  runAgreement "deep_deep(W (Some2 None))" "deep_deep"
    [.ctor (wrap "W")
      #[.ctor (myOpt2 "Some2") #[.ctor (myOpt "None") #[]]]] ++
  runAgreement "deep_deep(W None2)" "deep_deep"
    [.ctor (wrap "W") #[.ctor (myOpt2 "None2") #[]]] ++
  runAgreement "pointer_match()" "pointer_match" [] ++
  runAgreement "projections((1,2,3,4,5))" "projections"
    [.tuple #[1, 2, 3, 4, 5]] ++
  runAgreement "slice_and_get(#[10,20,30,40,50])" "slice_and_get"
    [.array #[10, 20, 30, 40, 50]] ++
  runAgreement "shr_shr_shl_decompose(0xCA)" "shr_shr_shl_decompose"
    [0xCA] ++
  runAgreement "u8_add_xor(0xAA,0x55)" "u8_add_xor" [0xAA, 0x55] ++
  runAgreement "array_set" "array_set"
    [.array #[.tuple #[1, 2], .tuple #[3, 4], .tuple #[5, 6]]] ++
  runAgreement "proj_mixed((1,(2,3),4))" "proj_mixed"
    [.tuple #[1, .tuple #[2, 3], 4]] ++
  runAgreement "deconstruct_tuple(1..5)" "deconstruct_tuple"
    [.tuple #[1, 2, 3, 4, 5]] ++
  runAgreement "deconstruct_array(#[1..5])" "deconstruct_array"
    [.array #[1, 2, 3, 4, 5]] ++
  runAgreement "eq_zero_dummy(0,5)" "eq_zero_dummy" [0, 5] ++
  runAgreement "eq_zero_dummy(0,37)" "eq_zero_dummy" [0, 37] ++
  runAgreement "shape_area(Circle 5)" "shape_area"
    [.ctor (Global.init "Shape" |>.pushNamespace "Circle") #[5]] ++
  runAgreement "shape_area(Rect 3 7)" "shape_area"
    [.ctor (Global.init "Shape" |>.pushNamespace "Rect") #[3, 7]] ++
  runAgreement "shape_area(Tri 1 2 3)" "shape_area"
    [.ctor (Global.init "Shape" |>.pushNamespace "Tri") #[1, 2, 3]] ++
  runAgreement "nested_match2(0,0)" "nested_match2" [0, 0] ++
  runAgreement "nested_match2(0,1)" "nested_match2" [0, 1] ++
  runAgreement "nested_match2(0,5)" "nested_match2" [0, 5] ++
  runAgreement "nested_match2(2,0)" "nested_match2" [2, 0] ++
  runAgreement "nested_match2(2,3)" "nested_match2" [2, 3] ++
  runAgreement "nested_match2(3,0)" "nested_match2" [3, 0] ++
  runAgreement "nested_match2(3,4)" "nested_match2" [3, 4] ++
  -- Recursive datatype + pointer
  runAgreement "sum_list[1,2,3]" "run" [] ++
  -- ----- Direct ports from Tests/Aiur/Aiur.lean -----------------------------
  runAgreement "id(42)" "id" [42] ++
  runAgreement "proj1(42,64)" "proj1" [42, 64] ++
  runAgreement "sum(3,5)" "sum" [3, 5] ++
  runAgreement "prod(3,5)" "prod" [3, 5] ++
  runAgreement "sum_prod(2,3,4)" "sum_prod" [2, 3, 4] ++
  runAgreement "assert_eq_trivial" "assert_eq_trivial" [] ++
  runAgreement "store_and_load(42)" "store_and_load" [42] ++
  runAgreement "u8_sub_function(45,131)" "u8_sub_function" [45, 131] ++
  runAgreement "u8_less_than_function(45,131)" "u8_less_than_function" [45, 131] ++
  runAgreement "u8_less_than_function(131,45)" "u8_less_than_function" [131, 45] ++
  runAgreement "u8_and_function(45,131)" "u8_and_function" [45, 131] ++
  runAgreement "u8_or_function(45,131)" "u8_or_function" [45, 131] ++
  runAgreement "u32_less_than_function(300,500)" "u32_less_than_function" [300, 500] ++
  runAgreement "u32_less_than_function(500,300)" "u32_less_than_function" [500, 300] ++
  runAgreement "u32_less_than_function(500,500)" "u32_less_than_function" [500, 500] ++
  runAgreement "eq_zero_degree_desync(3)" "eq_zero_degree_desync" [3] ++
  runAgreement "array_get_set" "array_get_set"
    [.array #[.tuple #[1, 1], .tuple #[2, 2], .tuple #[3, 3]]] ++
  runAgreement "unconstrained_fibonacci(6)" "unconstrained_fibonacci" [6] ++
  runAgreement "match_poly_ops(42)" "match_poly_ops" [42] ++
  runAgreement "match_lookup_ops(42)" "match_lookup_ops" [42] ++
  runAgreement "alias_conversion[1..8]" "alias_conversion"
    [.array #[1, 2, 3, 4, 5, 6, 7, 8]] ++
  runAgreement "is_0_even" "is_0_even" [] ++
  runAgreement "is_1_even" "is_1_even" [] ++
  runAgreement "is_2_even" "is_2_even" [] ++
  runAgreement "is_0_odd" "is_0_odd" [] ++
  runAgreement "is_1_odd" "is_1_odd" [] ++
  -- Non-tail match tests
  runAgreement "ntm_basic(0)" "ntm_basic" [0] ++
  runAgreement "ntm_basic(5)" "ntm_basic" [5] ++
  runAgreement "ntm_sequential(1,1)" "ntm_sequential" [1, 1] ++
  runAgreement "ntm_then_tail_match(0,3)" "ntm_then_tail_match" [0, 3] ++
  runAgreement "ntm_inside_tail_match(0,0)" "ntm_inside_tail_match" [0, 0] ++
  runAgreement "ntm_inside_tail_match(0,1)" "ntm_inside_tail_match" [0, 1] ++
  runAgreement "ntm_inside_tail_match(1,5)" "ntm_inside_tail_match" [1, 5] ++
  runAgreement "ntm_store_load(0)" "ntm_store_load" [0] ++
  runAgreement "ntm_call_in_branch(0)" "ntm_call_in_branch" [0] ++
  runAgreement "ntm_const_mul(0)" "ntm_const_mul" [0] ++
  runAgreement "ntm_tuple(0)" "ntm_tuple" [0] ++
  runAgreement "ntm_early_ret(0)" "ntm_early_ret" [0] ++
  runAgreement "ntm_early_ret(3)" "ntm_early_ret" [3] ++
  runAgreement "ntm_nested(0,0)" "ntm_nested" [0, 0] ++
  runAgreement "ntm_nested(0,5)" "ntm_nested" [0, 5] ++
  runAgreement "ntm_nested(3,0)" "ntm_nested" [3, 0] ++
  runAgreement "ntm_large(0)" "ntm_large" [0] ++
  runAgreement "ntm_large(5)" "ntm_large" [5] ++
  runAgreement "ntm_shape_let" "ntm_shape_let" [] ++
  runAgreement "read_write_io" "read_write_io" []
    (io := { data := #[1, 2, 3, 4], map := .ofList [(#[0], ⟨0, 4⟩)] }) ++
  runAgreement "template_basic" "template_basic" [] ++
  runAgreement "template_unwrap_some" "template_unwrap_some" [] ++
  runAgreement "template_unwrap_none" "template_unwrap_none" [] ++
  runAgreement "template_pair" "template_pair" [] ++
  runAgreement "template_nested" "template_nested" [] ++
  runAgreement "template_trans" "template_trans" [] ++
  runAgreement "template_multi" "template_multi" [] ++
  runAgreement "template_array" "template_array" [] ++
  runAgreement "template_tuple_arg" "template_tuple_arg" [] ++
  runAgreement "template_pointer_arg" "template_pointer_arg" [] ++
  runAgreement "template_chain" "template_chain" [] ++
  runAgreement "template_rec_list" "template_rec_list" [] ++
  runAgreement "template_rec_consumer" "template_rec_consumer" [] ++
  runAgreement "template_multi_rec" "template_multi_rec" [] ++
  runAgreement "template_tuple_match" "template_tuple_match" [] ++
  runAgreement "template_refutable_let" "template_refutable_let" [] ++
  runAgreement "template_pointer_pat" "template_pointer_pat" [] ++
  runAgreement "template_nested_rec" "template_nested_rec" [] ++
  runAgreement "template_mutual_rec" "template_mutual_rec" [] ++
  runAgreement "template_dual_args" "template_dual_args" [] ++
  runAgreement "template_unconstrained" "template_unconstrained" [] ++
  runAgreement "template_nested_refutable" "template_nested_refutable" [] ++
  runAgreement "template_simple_consumer" "template_simple_consumer" [] ++
  runAgreement "template_deep_nest" "template_deep_nest" [] ++
  -- Fibonacci (let-then-match style, distinct from `fib`)
  runAgreement "fibonacci(0)" "fibonacci" [0] ++
  runAgreement "fibonacci(1)" "fibonacci" [1] ++
  runAgreement "fibonacci(6)" "fibonacci" [6] ++
  -- End-to-end non-tail match entry aggregating many ntm_* helpers
  runAgreement "ntm_recursive_test" "ntm_recursive_test" [] ++
  runAgreement "non_tail_match" "non_tail_match" []

end AiurTests.Cross

end
