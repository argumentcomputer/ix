module

public import Ix.IxVM.Toplevel
public import Tests.Aiur.Common

public section
namespace Tests.Ix.IxVM.SubstProjection
open Aiur LSpec

/-- Frozen pre-projection walker. It shares lifting/lowering, not the new
prefix summary or projected recursion. Test-only, pruned from production. -/
private def reference := ⟦
  fn legacy_inst_many(e: KExpr, substs: List‹KExpr›, depth: G) -> KExpr {
    let n = list_length(substs);
    match n {
      0 => e,
      _ =>
        let l = expr_lbr(e);
        match memo_u32_less_than(depth, l) {
          0 => e,
          1 =>
            match has_bvar_in_range(e, depth, depth + n) {
              1 => legacy_inst_many_walk(e, substs, depth),
              _ => expr_lower(e, n, depth + n),
            },
        },
    }
  }

  -- Cold BVar arm of `legacy_inst_many_walk`, split into its own circuit so the
  -- hot App/Lam/… walk stays narrow (the `list_length` / `list_lookup` /
  -- `expr_lift` machinery only charges the BVar rows). Mirror the hot/cold
  -- split pattern used for `address_eq` / `whnf_with_spine`.
  --
  -- The walk invariant gives `lbr(BVar i) = i + 1 > depth`, i.e.
  -- `i ≥ depth`, so the window test reduces to one comparison on the
  -- offset. A sub-`depth` index (invariant violation) wraps in the field
  -- and fails the u32 range decomposition — no silent path.
  fn legacy_inst_many_bvar(i: G, substs: List‹KExpr›, depth: G) -> KExpr {
    let n = list_length(substs);
    let ofs = i - depth;
    match memo_u32_less_than(ofs, n) {
      1 => expr_lift(list_lookup(substs, ofs), depth, 0),
      0 => store(KExprNode.BVar(i - n)),
    }
  }

  fn legacy_inst_many_walk(e: KExpr, substs: List‹KExpr›, depth: G) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) => legacy_inst_many_bvar(i, substs, depth),
      KExprNode.Srt(l) => store(KExprNode.Srt(l)),
      KExprNode.Const(idx, lvls) => store(KExprNode.Const(idx, lvls)),
      KExprNode.App(f, a) =>
        store(KExprNode.App(
          legacy_inst_many(f, substs, depth),
          legacy_inst_many(a, substs, depth))),
      KExprNode.Lam(ty, body) =>
        store(KExprNode.Lam(
          legacy_inst_many(ty, substs, depth),
          legacy_inst_many(body, substs, depth + 1))),
      KExprNode.Forall(ty, body) =>
        store(KExprNode.Forall(
          legacy_inst_many(ty, substs, depth),
          legacy_inst_many(body, substs, depth + 1))),
      KExprNode.Let(ty, val, body) =>
        legacy_inst_many_let(ty, val, body, substs, depth),
      KExprNode.Lit(lit) => store(KExprNode.Lit(lit)),
      KExprNode.Proj(tidx, fidx, e1) =>
        store(KExprNode.Proj(tidx, fidx, legacy_inst_many(e1, substs, depth))),
    }
  }

  -- Cold-extracted Let arm (same pattern as `expr_lbr_let`).
  fn legacy_inst_many_let(ty: KExpr, val: KExpr, body: KExpr,
      substs: List‹KExpr›, depth: G) -> KExpr {
    store(KExprNode.Let(
      legacy_inst_many(ty, substs, depth),
      legacy_inst_many(val, substs, depth),
      legacy_inst_many(body, substs, depth + 1)))
  }
⟧

/-! Independent Nat-indexed de Bruijn model. The theorem below proves that
trimming a sufficiently long prefix preserves substitution when the original
removal count is kept. It does not certify the entire Aiur compiler. -/
private inductive Expr where
  | var : Nat → Expr
  | sort : Nat → Expr
  | app : Expr → Expr → Expr
  | lam : Expr → Expr → Expr
  | all : Expr → Expr → Expr
  | letE : Expr → Expr → Expr → Expr
  | proj : Expr → Expr
  | constE
  | lit
  deriving BEq, Repr, Inhabited

private def lift : Expr → Nat → Nat → Expr
  | .var i, shift, cutoff => .var (if i < cutoff then i else i + shift)
  | .app f a, s, c => .app (lift f s c) (lift a s c)
  | .lam t b, s, c => .lam (lift t s c) (lift b s (c + 1))
  | .all t b, s, c => .all (lift t s c) (lift b s (c + 1))
  | .letE t v b, s, c => .letE (lift t s c) (lift v s c) (lift b s (c + 1))
  | .proj e, s, c => .proj (lift e s c)
  | e, _, _ => e

private def subst : Expr → List Expr → Nat → Nat → Expr
  | .var i, ss, n, d =>
    if i < d then .var i else if i < d + n then
      lift (ss[i-d]?.getD (.sort 0)) d 0 else .var (i - n)
  | .app f a, ss, n, d => .app (subst f ss n d) (subst a ss n d)
  | .lam t b, ss, n, d => .lam (subst t ss n d) (subst b ss n (d + 1))
  | .all t b, ss, n, d => .all (subst t ss n d) (subst b ss n (d + 1))
  | .letE t v b, ss, n, d => .letE (subst t ss n d) (subst v ss n d) (subst b ss n (d + 1))
  | .proj e, ss, n, d => .proj (subst e ss n d)
  | e, _, _, _ => e

private def needed : Expr → Nat → Nat → Nat
  | .var i, d, n => if i < d then 0 else if i < d + n then i - d + 1 else 0
  | .app f a, d, n => max (needed f d n) (needed a d n)
  | .lam t b, d, n | .all t b, d, n => max (needed t d n) (needed b (d + 1) n)
  | .letE t v b, d, n => max (max (needed t d n) (needed v d n)) (needed b (d + 1) n)
  | .proj e, d, n => needed e d n
  | _, _, _ => 0

private theorem needed_le_count (e : Expr) (d n : Nat) : needed e d n ≤ n := by
  induction e generalizing d with
  | var i => simp only [needed]; split <;> (try split) <;> omega
  | sort _ | constE | lit => simp [needed]
  | app f a ihf iha => exact Nat.max_le.mpr ⟨ihf d, iha d⟩
  | lam t b iht ihb | all t b iht ihb => exact Nat.max_le.mpr ⟨iht d, ihb (d + 1)⟩
  | letE t v b iht ihv ihb => exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨iht d, ihv d⟩, ihb (d + 1)⟩
  | «proj» e ih => exact ih d

private theorem projected_subst_eq (e : Expr) (ss : List Expr) (n d k : Nat)
    (h : needed e d n ≤ k) : subst e (ss.take k) n d = subst e ss n d := by
  induction e generalizing ss n d k with
  | var i =>
    by_cases hlocal : i < d
    · simp [subst, hlocal]
    · by_cases inside : i < d + n
      · have slot : i - d < k := by simp [needed, hlocal, inside] at h; omega
        simp [subst, hlocal, inside, slot]
      · simp [subst, hlocal, inside]
  | sort _ | constE | lit => rfl
  | app f a ihf iha =>
    simp only [needed, Nat.max_le] at h
    simp only [subst, ihf ss n d k h.1, iha ss n d k h.2]
  | lam t b iht ihb | all t b iht ihb =>
    simp only [needed, Nat.max_le] at h
    simp only [subst, iht ss n d k h.1, ihb ss n (d + 1) k h.2]
  | letE t v b iht ihv ihb =>
    simp only [needed, Nat.max_le] at h
    simp only [subst, iht ss n d k h.1.1, ihv ss n d k h.1.2, ihb ss n (d + 1) k h.2]
  | «proj» e ih => simp only [needed] at h; simp only [subst, ih ss n d k h]

private def fixtures := ⟦
  fn projection_read_expr(offset: G) -> (KExpr, G) {
    let [tag] = io_read(0, offset, 1);
    match tag {
      0 => let [i] = io_read(0, offset + 1, 1);
        (store(KExprNode.BVar(i)), offset + 2),
      1 => let [i] = io_read(0, offset + 1, 1);
        (store(KExprNode.Srt(store(KLevelNode.Param(i)))), offset + 2),
      2 => let (f, next) = projection_read_expr(offset + 1);
        let (a, after) = projection_read_expr(next);
        (store(KExprNode.App(f, a)), after),
      3 => let (t, next) = projection_read_expr(offset + 1);
        let (b, after) = projection_read_expr(next);
        (store(KExprNode.Lam(t, b)), after),
      4 => let (t, next) = projection_read_expr(offset + 1);
        let (b, after) = projection_read_expr(next);
        (store(KExprNode.Forall(t, b)), after),
      5 => let (t, next) = projection_read_expr(offset + 1);
        let (v, next) = projection_read_expr(next);
        let (b, after) = projection_read_expr(next);
        (store(KExprNode.Let(t, v, b)), after),
      6 => let (e, after) = projection_read_expr(offset + 1);
        let addr = store([0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
          0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
          0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
          0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        (store(KExprNode.Proj(addr, 2, e)), after),
      7 => let addr = store([0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
          0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
          0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
          0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        (store(KExprNode.Const(addr, store(ListNode.Nil))), offset + 1),
      8 => (store(KExprNode.Lit(KLiteral.Nat(store(ListNode.Nil)))), offset + 1),
    }
  }

  fn projection_read_substs(n: G, offset: G) -> (List‹KExpr›, G) {
    match n {
      0 => (store(ListNode.Nil), offset),
      _ => let (e, next) = projection_read_expr(offset);
        let (rest, after) = projection_read_substs(n - 1, next);
        (store(ListNode.Cons(e, rest)), after),
    }
  }

  fn projection_batch_loop(mode: G, ncases: G, offset: G) {
    match ncases {
      0 => (),
      _ => let [depth, n, k] = io_read(0, offset, 3);
        let (e, next) = projection_read_expr(offset + 3);
        let (substs, next) = projection_read_substs(n, next);
        let (expected, after) = projection_read_expr(next);
        match mode {
          0 => assert_eq!(expr_inst_many(e, substs, depth), expected, "projected substitution"); (),
          1 => assert_eq!(legacy_inst_many(e, substs, depth), expected, "reference substitution"); (),
          2 =>
            assert_eq!(expr_inst_prefix_len(e, depth, depth + n), k, "referenced prefix length");
            assert_eq!(expr_inst_many(e, substs, depth), expected, "projected substitution");
            assert_eq!(legacy_inst_many(e, substs, depth), expected, "reference substitution"); (),
        };
        projection_batch_loop(mode, ncases - 1, after),
    }
  }

  pub fn projection_batch(mode: G, ncases: G) -> G {
    projection_batch_loop(mode, ncases, 0);
    1
  }
⟧

private def source : Except Global Source.Toplevel := do
  let vm ← IxVM.ixVMFull
  let vm ← vm.merge reference
  let vm ← vm.merge fixtures
  pure (vm.prune [`projection_batch])

private def encode : Expr → List Nat
  | .var i => [0, i]
  | .sort i => [1, i]
  | .app f a => 2 :: (encode f ++ encode a)
  | .lam t b => 3 :: (encode t ++ encode b)
  | .all t b => 4 :: (encode t ++ encode b)
  | .letE t v b => 5 :: (encode t ++ encode v ++ encode b)
  | .proj e => 6 :: encode e
  | .constE => [7]
  | .lit => [8]

private structure Case where
  e : Expr
  ss : List Expr
  depth : Nat := 0

private def encodeCase (c : Case) : List Nat :=
  [c.depth, c.ss.length, needed c.e c.depth c.ss.length] ++ encode c.e ++
    c.ss.flatMap encode ++ encode (subst c.e c.ss c.ss.length c.depth)

private def testCase (cases : List Case) (mode : Nat) (label : String) : AiurTestCase :=
  let data := (cases.flatMap encodeCase).toArray.map G.ofNat
  let io : IOBuffer := { data := ({} : Std.HashMap _ _).insert 0 data, map := {} }
  { functionName := `projection_batch, label, input := #[G.ofNat mode, G.ofNat cases.length],
    expectedOutput := #[1], inputIOBuffer := io, expectedIOBuffer := io,
    withProof := false }

private def boundaryCases : List Case := Id.run do
  let mut cases := []
  for d in [0, 1, 3] do
    for n in [0, 1, 2, 5] do
      let ss := (List.range n).map fun i =>
        if i % 2 == 0 then Expr.app (.var i) (.sort (17 + i))
        else .lam (.sort i) (.app (.var 0) (.var (i + 1)))
      for i in [0, d, d + n, d + n + 7] do
        let e := Expr.app (.var i) (.app (.var d) (.var (d + n + 7)))
        for body in [e, .lam (.var d) e, .all e (.lam (.sort 0) e),
            .letE (.var d) e (.app (.var 0) e), .proj e] do
          cases := cases ++ [{ e := body, ss, depth := d }]
      for e in [Expr.sort 0, .constE, .lit] do
        cases := cases ++ [{ e, ss, depth := d }]
  return cases

private def sharingCases (variants nodes : Nat) : List Case :=
  let e := (List.range nodes).foldl (fun e i => Expr.app (.sort i) e) (.var 0)
  (List.range variants).map fun i =>
    { e, ss := [.app (.var 0) (.sort 777), .sort (1000+i), .sort (2000+i), .sort (3000+i)] }

private def familyRows (env : AiurTestEnv) (qc : Array QueryCount) (legacy : Bool) : Nat :=
  let names := if legacy then
    [`legacy_inst_many, `legacy_inst_many_walk, `legacy_inst_many_bvar, `legacy_inst_many_let]
  else [`expr_inst_many, `expr_inst_many_projected, `expr_inst_many_walk,
    `expr_inst_many_bvar, `expr_inst_many_let, `expr_inst_prefix_len,
    `expr_inst_prefix_walk, `expr_inst_prefix_let]
  names.foldl (fun total name => match env.compiled.getFuncIdx name with
    | some idx => total + (qc[idx]?.map (·.uniqueRows)).getD 0
    | none => total) 0

private def sharingTests (env : AiurTestEnv) : IO TestSeq := do
  let mut seq := .done
  for (variants, nodes) in [(8, 16), (32, 64)] do
    let cases := sharingCases variants nodes
    let some idx := env.compiled.getFuncIdx `projection_batch | return test "entry missing" false
    let current := testCase cases 0 "projected sharing"
    let previous := testCase cases 1 "reference sharing"
    match env.compiled.bytecode.execute idx current.input current.inputIOBuffer,
        env.compiled.bytecode.execute idx previous.input previous.inputIOBuffer with
    | .ok (_, _, now), .ok (_, _, old) =>
      let rows := familyRows env now false
      let oldRows := familyRows env old true
      let fft := (computeStats env.compiled now env.shapes).totalFftCost
      let oldFft := (computeStats env.compiled old env.shapes).totalFftCost
      IO.println s!"[subst-projection] variants={variants} nodes={nodes} family_rows={rows}/{oldRows} FFT={fft}/{oldFft} (new/old)"
      seq := seq ++ test s!"{variants}/{nodes}: fewer substitution and summary rows" (rows < oldRows)
        ++ test s!"{variants}/{nodes}: total fixture FFT improves" (fft < oldFft)
    | _, _ => seq := seq ++ test s!"sharing fixture {variants}/{nodes} executes" false
  return seq

def run : IO UInt32 := do
  let .ok env := AiurTestEnv.build source
    | IO.eprintln "substitution projection fixture build failed"; return 1
  let cases := boundaryCases
  let mut status := 0
  for i in [: (cases.length + 15) / 16] do
    let batch := (cases.drop (i * 16)).take 16
    let r ← lspecEachIO [testCase batch 2 s!"substitution boundary batch {i}"]
      fun tc => pure (env.runTestCase tc)
    if r != 0 then status := r
  let shares ← sharingTests env
  let r ← lspecIO (.ofList [("ixvm-subst-projection", [shares])]) []
  if r != 0 then status := r
  let proofCases : List Case := [
    { e := .app (.var 0) (.var 9), ss := [.var 1, .sort 7, .sort 8] },
    { e := .lam (.var 1) (.app (.var 0) (.app (.var 2) (.var 12))),
      ss := [.var 1, .sort 7, .sort 8], depth := 1 },
    { e := .letE (.var 0) (.var 0) (.proj (.app (.var 1) (.var 8))),
      ss := [.all (.sort 1) (.var 2), .sort 2] }]
  for (c, i) in proofCases.zipIdx do
    let tc := { testCase [c] 2 s!"substitution projection proof {i}" with withProof := true }
    let r ← lspecEachIO [tc] fun tc => pure (env.runTestCase tc)
    if r != 0 then status := r
  return status

end Tests.Ix.IxVM.SubstProjection
end
