import IxVMRefinement.Subst.Basic

/-! # The substitution family at any keying

The substitution family's functions never read a constant's key, and never hash: their specs
hold at every keying `κ` of addresses and need only the calls' ROM bound. This file restates
each registry spec of the family (`Core/Specs/Subst.lean`) at a keying `κ` and with `Bounded`
in place of `Good` (`G.<f>`), and closes the family's own induction (`gall`): the family's
functions call one another, and outside the family only library functions with lemmas of their
own (`UInt32::less_than_fields`, `Lists`, the level operations).

At `κ = c.κ` each `G.<f>` is the registry spec with `Good c calls` weakened to its bound, so the
registry step lemmas are instances (`Subst/Steps.lean`); at the keying of a ghost it gives the
statement's `Terms`. -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency (Bounded)
open Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)

set_option linter.unusedVariables false

/-- A spec of the family at a fixed keying. -/
abbrev GSpecFn : Type :=
  List (SourceValue F) → Heap F → SourceValue F → Heap F → List (Call F) → Prop

namespace G
variable (κ : _root_.Address → KKey)

def expr_lbr : GSpecFn := fun args h r h' calls =>
  ∀ e, args = [e] → Bounded calls → h' = h ∧
    ∀ d Γ k E, Tm κ d Γ h k E e →
      ∃ b : Nat, r = .field (b : F) ∧ b ≤ idxBound ∧ b ≤ k + d ∧ IdxLt h b e ∧
        (∀ b', b' < b → ¬ IdxLt h b' e) ∧ LbrLeK κ h e k E b

def expr_lbr_let : GSpecFn := fun args h r h' calls =>
  ∀ ty val body, args = [ty, val, body] → Bounded calls → h' = h ∧
    ∀ d Γ k T V B, Tm κ d Γ h k T ty → Tm κ d Γ h k V val → Tm κ d Γ h (k + 1) B body →
      ∃ b : Nat, r = .field (b : F) ∧ b ≤ idxBound ∧ b ≤ k + d ∧
        IdxLt h b ty ∧ IdxLt h b val ∧ IdxLt h (b + 1) body ∧
        ∀ b', b' < b → ¬ (IdxLt h b' ty ∧ IdxLt h b' val ∧ IdxLt h (b' + 1) body)

def lbr_max : GSpecFn := fun args h r h' calls =>
  ∀ x y : F, args = [.field x, .field y] → Bounded calls → h' = h ∧
    ZMod.val x < 4294967296 ∧ ZMod.val y < 4294967296 ∧
    r = .field (if ZMod.val x < ZMod.val y then y else x)

def lbr_dec : GSpecFn := fun args h r h' calls =>
  ∀ x : F, args = [.field x] → Bounded calls → h' = h ∧ r = .field ((ZMod.val x - 1 : Nat) : F)

def lbr_min : GSpecFn := fun args h r h' calls =>
  ∀ x y : F, args = [.field x, .field y] → Bounded calls → h' = h ∧
    ZMod.val x < 4294967296 ∧ ZMod.val y < 4294967296 ∧
    r = .field (if ZMod.val x < ZMod.val y then x else y)

def has_bvar_in_range : GSpecFn := fun args h r h' calls =>
  ∀ e (lo hi : F), args = [e, .field lo, .field hi] → Bounded calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k E, Tm κ d Γ h k E e → NoIdxF h (ZMod.val lo) (ZMod.val hi) e)

def has_bvar_in_range_bvar : GSpecFn := fun args h r h' calls =>
  ∀ i lo hi : F, args = [.field i, .field lo, .field hi] → Bounded calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ZMod.val i < ZMod.val lo ∨ ZMod.val hi ≤ ZMod.val i)

def has_bvar_in_range_binder : GSpecFn := fun args h r h' calls =>
  ∀ ty body (lo hi : F), args = [ty, body, .field lo, .field hi] → Bounded calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k T B, Tm κ d Γ h k T ty → Tm κ d Γ h (k + 1) B body →
      NoIdxF h (ZMod.val lo) (ZMod.val hi) ty ∧
      NoIdxF h (ZMod.val lo + 1) (ZMod.val hi + 1) body)

def has_bvar_in_range_let : GSpecFn := fun args h r h' calls =>
  ∀ ty val body (lo hi : F), args = [ty, val, body, .field lo, .field hi] → Bounded calls →
    h' = h ∧ (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k T V B, Tm κ d Γ h k T ty → Tm κ d Γ h k V val →
      Tm κ d Γ h (k + 1) B body →
      NoIdxF h (ZMod.val lo) (ZMod.val hi) ty ∧ NoIdxF h (ZMod.val lo) (ZMod.val hi) val ∧
      NoIdxF h (ZMod.val lo + 1) (ZMod.val hi + 1) body)

def expr_has_bvar_at : GSpecFn := fun args h r h' calls =>
  ∀ e (j : F), args = [e, .field j] → Bounded calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k E, Tm κ d Γ h k E e → NoIdx h (ZMod.val j) (ZMod.val j + 1) e)

def expr_has_bvar_at_binder : GSpecFn := fun args h r h' calls =>
  ∀ ty body (j : F), args = [ty, body, .field j] → Bounded calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k T B, Tm κ d Γ h k T ty → Tm κ d Γ h (k + 1) B body →
      NoIdx h (ZMod.val j) (ZMod.val j + 1) ty ∧
      NoIdx h (ZMod.val j + 1) (ZMod.val j + 2) body)

def expr_has_bvar_at_let : GSpecFn := fun args h r h' calls =>
  ∀ ty val body (j : F), args = [ty, val, body, .field j] → Bounded calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k T V B, Tm κ d Γ h k T ty → Tm κ d Γ h k V val →
      Tm κ d Γ h (k + 1) B body →
      NoIdx h (ZMod.val j) (ZMod.val j + 1) ty ∧ NoIdx h (ZMod.val j) (ZMod.val j + 1) val ∧
      NoIdx h (ZMod.val j + 1) (ZMod.val j + 2) body)

def expr_glb : GSpecFn := fun args h r h' calls =>
  ∀ e (cut : F), args = [e, .field cut] → Bounded calls → ZMod.val cut < 4294967296 → h' = h ∧
    ∃ g : Nat, r = .field (g : F) ∧ g < 4294967296 ∧
      ∀ d Γ E, Tm κ d Γ h (ZMod.val cut) E e → NoIdx h (ZMod.val cut) (ZMod.val cut + g) e

def expr_glb_walk : GSpecFn := fun args h r h' calls =>
  ∀ e (cut : F), args = [e, .field cut] → Bounded calls → ZMod.val cut + 1 < 4294967296 →
    h' = h ∧ ∃ g : Nat, r = .field (g : F) ∧ g < 4294967296 ∧
      ∀ d Γ E, Tm κ d Γ h (ZMod.val cut) E e → NoIdx h (ZMod.val cut) (ZMod.val cut + g) e

def expr_glb_binder : GSpecFn := fun args h r h' calls =>
  ∀ ty body (cut : F), args = [ty, body, .field cut] → Bounded calls →
    ZMod.val cut + 1 < 4294967296 → h' = h ∧
    ∃ g : Nat, r = .field (g : F) ∧ g < 4294967296 ∧
      ∀ d Γ T B, Tm κ d Γ h (ZMod.val cut) T ty → Tm κ d Γ h (ZMod.val cut + 1) B body →
        NoIdx h (ZMod.val cut) (ZMod.val cut + g) ty ∧
        NoIdx h (ZMod.val cut + 1) (ZMod.val cut + 1 + g) body

def expr_glb_let : GSpecFn := fun args h r h' calls =>
  ∀ ty val body (cut : F), args = [ty, val, body, .field cut] → Bounded calls →
    ZMod.val cut + 1 < 4294967296 → h' = h ∧
    ∃ g : Nat, r = .field (g : F) ∧ g < 4294967296 ∧
      ∀ d Γ T V B, Tm κ d Γ h (ZMod.val cut) T ty → Tm κ d Γ h (ZMod.val cut) V val →
        Tm κ d Γ h (ZMod.val cut + 1) B body →
        NoIdx h (ZMod.val cut) (ZMod.val cut + g) ty ∧
        NoIdx h (ZMod.val cut) (ZMod.val cut + g) val ∧
        NoIdx h (ZMod.val cut + 1) (ZMod.val cut + 1 + g) body

def expr_lift : GSpecFn := fun args h r h' calls =>
  ∀ e (s cut : F), args = [e, .field s, .field cut] → Bounded calls →
    ZMod.val s < 4611686018427387904 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ E, Tm κ d Γ h (ZMod.val cut) E e →
      Tm κ (d + s₂) Γ h' (ZMod.val cut + s₁) E r

def expr_lift_walk : GSpecFn := fun args h r h' calls =>
  ∀ e (s cut : F), args = [e, .field s, .field cut] → Bounded calls →
    ZMod.val s < 4611686018427387904 → ZMod.val cut < 4294967296 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ E, Tm κ d Γ h (ZMod.val cut) E e →
      Tm κ (d + s₂) Γ h' (ZMod.val cut + s₁) E r

def expr_lift_bvar : GSpecFn := fun args h r h' calls =>
  ∀ i s cut : F, args = [.field i, .field s, .field cut] → Bounded calls →
    ZMod.val s < 4611686018427387904 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ E, BVarIm d Γ (ZMod.val cut) (ZMod.val i) E →
      Tm κ (d + s₂) Γ h' (ZMod.val cut + s₁) E r

def expr_lift_let : GSpecFn := fun args h r h' calls =>
  ∀ ty val body (s cut : F), args = [ty, val, body, .field s, .field cut] → Bounded calls →
    ZMod.val s < 4611686018427387904 → ZMod.val cut < 4294967296 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ T V B, Tm κ d Γ h (ZMod.val cut) T ty →
      Tm κ d Γ h (ZMod.val cut) V val → Tm κ d Γ h (ZMod.val cut + 1) B body →
      Tm κ (d + s₂) Γ h' (ZMod.val cut + s₁) (instShift V 0 B) r

def expr_lower : GSpecFn := fun args h r h' calls =>
  ∀ e (s cut : F), args = [e, .field s, .field cut] → Bounded calls →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → s₁ ≤ ZMod.val cut → ∀ d Γ E, s₂ ≤ d →
      Tm κ d Γ h (ZMod.val cut) E e → NoIdx h (ZMod.val cut - s₁) (ZMod.val cut + s₂) e →
      Tm κ (d - s₂) Γ h' (ZMod.val cut - s₁) E r

def expr_lower_walk : GSpecFn := fun args h r h' calls =>
  ∀ e (s cut : F), args = [e, .field s, .field cut] → Bounded calls →
    ZMod.val cut < 4294967296 → ¬ IdxLt h (ZMod.val cut) e →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → s₁ ≤ ZMod.val cut → ∀ d Γ E, s₂ ≤ d →
      Tm κ d Γ h (ZMod.val cut) E e → NoIdx h (ZMod.val cut - s₁) (ZMod.val cut + s₂) e →
      Tm κ (d - s₂) Γ h' (ZMod.val cut - s₁) E r

def expr_lower_let : GSpecFn := fun args h r h' calls =>
  ∀ ty val body (s cut : F), args = [ty, val, body, .field s, .field cut] → Bounded calls →
    ZMod.val cut < 4294967296 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → s₁ ≤ ZMod.val cut → ∀ d Γ T V B, s₂ ≤ d →
      Tm κ d Γ h (ZMod.val cut) T ty → Tm κ d Γ h (ZMod.val cut) V val →
      Tm κ d Γ h (ZMod.val cut + 1) B body →
      NoIdx h (ZMod.val cut - s₁) (ZMod.val cut + s₂) ty →
      NoIdx h (ZMod.val cut - s₁) (ZMod.val cut + s₂) val →
      NoIdx h (ZMod.val cut + 1 - s₁) (ZMod.val cut + 1 + s₂) body →
      Tm κ (d - s₂) Γ h' (ZMod.val cut - s₁) (instShift V 0 B) r

def expr_inst1 : GSpecFn := fun args h r h' calls =>
  ∀ e arg (j : F), args = [e, arg, .field j] → Bounded calls →
    ∀ d Γ B A, Tm κ d Γ h (ZMod.val j + 1) B e → Tm κ d Γ h 0 A arg →
      Tm κ d Γ h' (ZMod.val j) (B.instantiate1 A (ZMod.val j)) r

def expr_inst1_walk : GSpecFn := fun args h r h' calls =>
  ∀ e arg (j : F), args = [e, arg, .field j] → Bounded calls → ZMod.val j < 4294967296 →
    ∀ d Γ B A, Tm κ d Γ h (ZMod.val j + 1) B e → Tm κ d Γ h 0 A arg →
      Tm κ d Γ h' (ZMod.val j) (B.instantiate1 A (ZMod.val j)) r

def expr_inst1_bvar : GSpecFn := fun args h r h' calls =>
  ∀ (i : F) arg (j : F), args = [.field i, arg, .field j] → Bounded calls →
    ∀ d Γ B A, BVarIm d Γ (ZMod.val j + 1) (ZMod.val i) B → Tm κ d Γ h 0 A arg →
      Tm κ d Γ h' (ZMod.val j) (B.instantiate1 A (ZMod.val j)) r

def expr_inst1_let : GSpecFn := fun args h r h' calls =>
  ∀ ty val body arg (j : F), args = [ty, val, body, arg, .field j] → Bounded calls →
    ZMod.val j < 4294967296 →
    ∀ d Γ T V B A, Tm κ d Γ h (ZMod.val j + 1) T ty → Tm κ d Γ h (ZMod.val j + 1) V val →
      Tm κ d Γ h (ZMod.val j + 2) B body → Tm κ d Γ h 0 A arg →
      Tm κ d Γ h' (ZMod.val j) ((instShift V 0 B).instantiate1 A (ZMod.val j)) r

def expr_inst_many : GSpecFn := fun args h r h' calls =>
  ∀ e substs (j : F), args = [e, substs, .field j] → Bounded calls →
    ∀ d Γ B As, Tm κ d Γ h (ZMod.val j + As.length) B e → TmL κ d Γ h As substs →
      Tm κ d Γ h' (ZMod.val j) (B.instantiateList As (ZMod.val j)) r

def expr_inst_many_bvar : GSpecFn := fun args h r h' calls =>
  ∀ (i : F) substs (j : F), args = [.field i, substs, .field j] → Bounded calls →
    ZMod.val j < 4294967296 →
    ∀ d Γ B As, BVarIm d Γ (ZMod.val j + As.length) (ZMod.val i) B → TmL κ d Γ h As substs →
      Tm κ d Γ h' (ZMod.val j) (B.instantiateList As (ZMod.val j)) r

def expr_inst_many_walk : GSpecFn := fun args h r h' calls =>
  ∀ e substs (j : F), args = [e, substs, .field j] → Bounded calls → ZMod.val j < 4294967296 →
    ∀ d Γ B As, Tm κ d Γ h (ZMod.val j + As.length) B e → TmL κ d Γ h As substs →
      Tm κ d Γ h' (ZMod.val j) (B.instantiateList As (ZMod.val j)) r

def expr_inst_many_let : GSpecFn := fun args h r h' calls =>
  ∀ ty val body substs (j : F), args = [ty, val, body, substs, .field j] → Bounded calls →
    ZMod.val j < 4294967296 →
    ∀ d Γ T V B As, Tm κ d Γ h (ZMod.val j + As.length) T ty →
      Tm κ d Γ h (ZMod.val j + As.length) V val →
      Tm κ d Γ h (ZMod.val j + As.length + 1) B body → TmL κ d Γ h As substs →
      Tm κ d Γ h' (ZMod.val j) ((instShift V 0 B).instantiateList As (ZMod.val j)) r

def ctx_trim : GSpecFn := fun args h r h' calls =>
  ∀ types base, args = [types, base] → Bounded calls →
    ∀ Γ d, (TypesRep κ Γ h d types ∧ GhostScoped Γ d) → (TypesRep κ Γ h' d r ∧ GhostScoped Γ d)

def ctx_reachable : GSpecFn := fun args h r h' calls =>
  ∀ types base, args = [types, base] → Bounded calls → ∃ x : F, r = .field x

def ctx_seek_cut : GSpecFn := fun args h r h' calls =>
  ∀ types need, args = [types, need] → Bounded calls → ∃ x : F, r = .field x

def ctx_next_cut : GSpecFn := fun args h r h' calls =>
  ∀ types, args = [types] → Bounded calls → ∃ x : F, r = .field x

def ctx_close_cut : GSpecFn := fun args h r h' calls =>
  ∀ rest l, args = [rest, l] → Bounded calls → ∃ x : F, r = .field x

def collect_spine : GSpecFn := fun args h r h' calls =>
  ∀ e, args = [e] → Bounded calls → ∀ d Γ k E, Tm κ d Γ h k E e →
    ∃ hd sp H As, r = .tuple [hd, sp] ∧ Tm κ d Γ h' k H hd ∧
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h' As sp ∧
      E = Ix.Kernel.Expr.mkAppN H As

def expr_inst_levels : GSpecFn := fun args h r h' calls =>
  ∀ e params, args = [e, params] → Bounded calls →
    ∀ Γ k E us, Tm κ 0 Γ h k E e → LvListRep h us params →
      Tm κ 0 Γ h' k (E.instantiateLevelParams (List.range us.length) us) r

def expr_inst_levels_walk : GSpecFn := fun args h r h' calls =>
  ∀ e params, args = [e, params] → Bounded calls →
    ∀ Γ k E us, Tm κ 0 Γ h k E e → LvListRep h us params →
      Tm κ 0 Γ h' k (E.instantiateLevelParams (List.range us.length) us) r

end G

/-- Each function's spec at the keying `κ`. -/
def gspec (κ : _root_.Address → KKey) : Specs.Subst.Fn → GSpecFn
  | .expr_lbr => G.expr_lbr κ
  | .expr_lbr_let => G.expr_lbr_let κ
  | .lbr_max => G.lbr_max
  | .lbr_dec => G.lbr_dec
  | .lbr_min => G.lbr_min
  | .has_bvar_in_range => G.has_bvar_in_range κ
  | .has_bvar_in_range_bvar => G.has_bvar_in_range_bvar
  | .has_bvar_in_range_binder => G.has_bvar_in_range_binder κ
  | .has_bvar_in_range_let => G.has_bvar_in_range_let κ
  | .expr_has_bvar_at => G.expr_has_bvar_at κ
  | .expr_has_bvar_at_binder => G.expr_has_bvar_at_binder κ
  | .expr_has_bvar_at_let => G.expr_has_bvar_at_let κ
  | .expr_glb => G.expr_glb κ
  | .expr_glb_walk => G.expr_glb_walk κ
  | .expr_glb_binder => G.expr_glb_binder κ
  | .expr_glb_let => G.expr_glb_let κ
  | .expr_lift => G.expr_lift κ
  | .expr_lift_walk => G.expr_lift_walk κ
  | .expr_lift_bvar => G.expr_lift_bvar κ
  | .expr_lift_let => G.expr_lift_let κ
  | .expr_lower => G.expr_lower κ
  | .expr_lower_walk => G.expr_lower_walk κ
  | .expr_lower_let => G.expr_lower_let κ
  | .expr_inst1 => G.expr_inst1 κ
  | .expr_inst1_walk => G.expr_inst1_walk κ
  | .expr_inst1_bvar => G.expr_inst1_bvar κ
  | .expr_inst1_let => G.expr_inst1_let κ
  | .expr_inst_many => G.expr_inst_many κ
  | .expr_inst_many_bvar => G.expr_inst_many_bvar κ
  | .expr_inst_many_walk => G.expr_inst_many_walk κ
  | .expr_inst_many_let => G.expr_inst_many_let κ
  | .ctx_trim => G.ctx_trim κ
  | .ctx_reachable => G.ctx_reachable
  | .ctx_seek_cut => G.ctx_seek_cut
  | .ctx_next_cut => G.ctx_next_cut
  | .ctx_close_cut => G.ctx_close_cut
  | .collect_spine => G.collect_spine κ
  | .expr_inst_levels => G.expr_inst_levels κ
  | .expr_inst_levels_walk => G.expr_inst_levels_walk κ

/-- **The family's induction hypothesis**: every function of the family meets its spec at the
keying `κ` on every observed derivation with fewer calls. -/
def GIH (κ : _root_.Address → KKey) (calls : List (Call F)) : Prop :=
  ∀ (f : Specs.Subst.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
    (h' : Heap F) (cs : List (Call F)), cs.length < calls.length →
      ObsFn W f.name args h r h' cs → gspec κ f args h r h' cs

theorem GIH.get {κ : _root_.Address → KKey} {calls : List (Call F)} (ih : GIH κ calls)
    (f : Specs.Subst.Fn) {args : List (SourceValue F)} {h : Heap F} {r : SourceValue F}
    {h' : Heap F} {cs : List (Call F)} (hlt : cs.length < calls.length)
    (ev : ObsFn W f.name args h r h' cs) : gspec κ f args h r h' cs :=
  ih f args h r h' cs hlt ev

/-- **The family's harness**: one step per function gives every function's spec. -/
theorem ginduction (κ : _root_.Address → KKey)
    (step : ∀ (f : Specs.Subst.Fn) (args : List (SourceValue F)) (h : Heap F)
      (r : SourceValue F) (h' : Heap F) (cs : List (Call F)),
      ObsFn W f.name args h r h' cs → GIH κ cs → gspec κ f args h r h' cs) :
    ∀ (f : Specs.Subst.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W f.name args h r h' cs →
      gspec κ f args h r h' cs := by
  have key := ObsFn.strong_induction (world := W)
    (fun n args h r h' cs => ∀ f : Specs.Subst.Fn, f.name = n → gspec κ f args h r h' cs)
    (fun n args h r h' cs ev ihn f hf => by
      subst hf
      exact step f args h r h' cs ev
        (fun f' args' h₁ r' h₂ cs' hlt ev' => ihn _ _ _ _ _ _ hlt ev' f' rfl))
  exact fun f args h r h' cs ev => key _ _ _ _ _ _ ev f rfl

end IxVM.Refinement.Core.SubstAux
