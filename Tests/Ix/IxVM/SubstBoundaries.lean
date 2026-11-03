import Ix.IxVM.Toplevel
import Ix.Aiur.Compiler
import Ix.Aiur.Protocol

/-! Regression controls for the substitution circuits' scope guards. The
reference functions retain the former control flow. Execute both through the
constrained bytecode backend, including field values outside the u32 range:
the comparison gadgets' refusals are part of the expected behavior.

The probe entrypoints are test-only and are absent from production IxVM. -/

namespace Tests.Ix.IxVM.SubstBoundaries

open Aiur

private def probes := ⟦
  fn boundary_lower_ref(e: KExpr, shift: G, cutoff: G) -> KExpr {
    match shift {
      0 => e,
      _ =>
        let l = expr_lbr(e);
        match memo_u32_less_than(cutoff, l) {
          0 => e,
          1 => boundary_lower_walk_ref(e, shift, cutoff),
        },
    }
  }

  fn boundary_lower_walk_ref(e: KExpr, shift: G, cutoff: G) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) =>
        let lt = u32_less_than(i, cutoff);
        match lt {
          1 => e,
          0 => store(KExprNode.BVar(i - shift)),
        },
      KExprNode.Srt(l) => store(KExprNode.Srt(l)),
      KExprNode.Const(idx, lvls) => store(KExprNode.Const(idx, lvls)),
      KExprNode.App(f, a) =>
        store(KExprNode.App(
          boundary_lower_ref(f, shift, cutoff),
          boundary_lower_ref(a, shift, cutoff))),
      KExprNode.Lam(ty, body) =>
        store(KExprNode.Lam(
          boundary_lower_ref(ty, shift, cutoff),
          boundary_lower_ref(body, shift, cutoff + 1))),
      KExprNode.Forall(ty, body) =>
        store(KExprNode.Forall(
          boundary_lower_ref(ty, shift, cutoff),
          boundary_lower_ref(body, shift, cutoff + 1))),
      KExprNode.Let(ty, val, body) =>
        store(KExprNode.Let(
          boundary_lower_ref(ty, shift, cutoff),
          boundary_lower_ref(val, shift, cutoff),
          boundary_lower_ref(body, shift, cutoff + 1))),
      KExprNode.Lit(lit) => store(KExprNode.Lit(lit)),
      KExprNode.Proj(tidx, fidx, e1) =>
        store(KExprNode.Proj(tidx, fidx, boundary_lower_ref(e1, shift, cutoff))),
    }
  }

  fn boundary_range_ref(e: KExpr, lo: G, hi: G) -> G {
    match load(e) {
      KExprNode.BVar(i) =>
        match u32_less_than(i, lo) {
          1 => 0,
          0 => u32_less_than(i, hi),
        },
      KExprNode.Srt(_) => 0,
      KExprNode.Const(_, _) => 0,
      KExprNode.Lit(_) => 0,
      KExprNode.App(f, a) =>
        match boundary_range_ref(f, lo, hi) {
          1 => 1,
          0 => boundary_range_ref(a, lo, hi),
        },
      KExprNode.Lam(ty, body) => boundary_range_ref_binder(ty, body, lo, hi),
      KExprNode.Forall(ty, body) => boundary_range_ref_binder(ty, body, lo, hi),
      KExprNode.Let(ty, val, body) => boundary_range_ref_let(ty, val, body, lo, hi),
      KExprNode.Proj(_, _, e1) => boundary_range_ref(e1, lo, hi),
    }
  }

  -- Cold-extracted binder arm (same pattern as `expr_lbr_let`): the
  -- two-call arm would otherwise widen every row of the hot walk.
  fn boundary_range_ref_binder(ty: KExpr, body: KExpr, lo: G, hi: G) -> G {
    match boundary_range_ref(ty, lo, hi) {
      1 => 1,
      0 => boundary_range_ref(body, lo + 1, hi + 1),
    }
  }

  fn boundary_range_ref_let(ty: KExpr, val: KExpr, body: KExpr, lo: G, hi: G) -> G {
    match boundary_range_ref(ty, lo, hi) {
      1 => 1,
      0 =>
        match boundary_range_ref(val, lo, hi) {
          1 => 1,
          0 => boundary_range_ref(body, lo + 1, hi + 1),
        },
    }
  }

  fn boundary_expr(i: G, j: G) -> KExpr {
    let x = store(KExprNode.BVar(i));
    let y = store(KExprNode.BVar(j));
    store(KExprNode.Let(x, store(KExprNode.App(x, y)), store(KExprNode.Lam(x, y))))
  }

  fn boundary_read(e: KExpr) -> [G; 5] {
    let KExprNode.Let(a, b, c) = load(e);
    let KExprNode.BVar(a1) = load(a);
    let KExprNode.App(b1, b2) = load(b);
    let KExprNode.BVar(b1) = load(b1);
    let KExprNode.BVar(b2) = load(b2);
    let KExprNode.Lam(c1, c2) = load(c);
    let KExprNode.BVar(c1) = load(c1);
    let KExprNode.BVar(c2) = load(c2);
    [a1, b1, b2, c1, c2]
  }

  pub fn boundary_lower(i: G, shift: G, cutoff: G) -> G {
    let KExprNode.BVar(j) = load(expr_lower(store(KExprNode.BVar(i)), shift, cutoff));
    j
  }
  pub fn boundary_lower_reference(i: G, shift: G, cutoff: G) -> G {
    let KExprNode.BVar(j) = load(boundary_lower_ref(store(KExprNode.BVar(i)), shift, cutoff));
    j
  }
  pub fn boundary_lower_let(i: G, j: G, shift: G, cutoff: G) -> [G; 5] {
    boundary_read(expr_lower(boundary_expr(i, j), shift, cutoff))
  }
  pub fn boundary_lower_let_reference(i: G, j: G, shift: G, cutoff: G) -> [G; 5] {
    boundary_read(boundary_lower_ref(boundary_expr(i, j), shift, cutoff))
  }
  pub fn boundary_range(i: G, lo: G, hi: G) -> G {
    has_bvar_in_range(store(KExprNode.BVar(i)), lo, hi)
  }
  pub fn boundary_range_reference(i: G, lo: G, hi: G) -> G {
    boundary_range_ref(store(KExprNode.BVar(i)), lo, hi)
  }
  pub fn boundary_range_let(i: G, j: G, lo: G, hi: G) -> G {
    has_bvar_in_range(boundary_expr(i, j), lo, hi)
  }
  pub fn boundary_range_let_reference(i: G, j: G, lo: G, hi: G) -> G {
    boundary_range_ref(boundary_expr(i, j), lo, hi)
  }
⟧

private def entries : List Lean.Name := [
  `boundary_lower, `boundary_lower_reference,
  `boundary_lower_let, `boundary_lower_let_reference,
  `boundary_range, `boundary_range_reference,
  `boundary_range_let, `boundary_range_let_reference]

private def compareCase (compiled : CompiledToplevel) (actual reference : Lean.Name)
    (args : Array Nat) : Except String Bool := do
  let input := args.map G.ofNat
  let some actualIdx := compiled.getFuncIdx actual | throw s!"missing {actual}"
  let some referenceIdx := compiled.getFuncIdx reference | throw s!"missing {reference}"
  let lhs := (compiled.bytecode.execute actualIdx input default).map (·.1)
  let rhs := (compiled.bytecode.execute referenceIdx input default).map (·.1)
  match lhs, rhs with
  | .ok a, .ok r =>
    unless a == r do throw s!"output mismatch {actual} {args}: {a} vs {r}"
    return true
  | .error _, .error _ => return false
  | .ok a, .error r => throw s!"lost refusal {actual} {args}: {a} vs {r}"
  | .error a, .ok r => throw s!"new refusal {actual} {args}: {a} vs {r}"

/-- All cutoff boundaries, zero shifts, u32 overflow and field wraparound,
including traversal under both a let and a lambda. -/
def checks : Except String (Nat × Nat) := do
  let source ← (IxVM.ixVMFull >>= (·.merge probes)).mapError toString
  let compiled ← (source.prune entries).compile
  let p := 18446744069414584321
  let indices := [0, 1, 2, 3, 17, 4294967293, 4294967294, 4294967295, 4294967296,
    72057594037927935, p - 2, p - 1]
  let cutoffs := [0, 1, 2, 17, 4294967294, 4294967295, 4294967296, p - 1]
  let shifts := [0, 1, 2, 4294967295, p - 1]
  let mut accepted := 0
  let mut refused := 0
  for i in indices do
    for cutoff in cutoffs do
      for shift in shifts do
        if ← compareCase compiled `boundary_lower `boundary_lower_reference #[i, shift, cutoff] then
          accepted := accepted + 1
        else refused := refused + 1
      for shift in [0, 1, 2] do
        if ← compareCase compiled `boundary_lower_let `boundary_lower_let_reference #[i, 4, shift, cutoff] then
          accepted := accepted + 1
        else refused := refused + 1
      for hi in cutoffs do
        if ← compareCase compiled `boundary_range `boundary_range_reference #[i, cutoff, hi] then
          accepted := accepted + 1
        else refused := refused + 1
        if ← compareCase compiled `boundary_range_let `boundary_range_let_reference #[i, 4, cutoff, hi] then
          accepted := accepted + 1
        else refused := refused + 1
  unless accepted > 0 && refused > 0 && accepted + refused == 2304 do
    throw s!"boundary coverage changed: {accepted} successes, {refused} refusals"
  return (accepted, refused)

def runSuite : IO UInt32 := do
  match checks with
  | .error error => IO.eprintln error; return 1
  | .ok (accepted, refused) =>
    IO.println s!"substitution boundaries: {accepted} successes and {refused} refusals match"
    return 0

end Tests.Ix.IxVM.SubstBoundaries
