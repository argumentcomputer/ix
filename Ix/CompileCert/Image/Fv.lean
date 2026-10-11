import Ix.CompileCert.Image.Sim
import Batteries.Tactic.OpenPrivate

/-!
# M7 L2a-syn: the free variables of the construction's terms

`FvAll P e`: every free variable of `e` satisfies `P`. The helpers of the image construction never
create a free variable: their results' free variables are among their inputs' (instantiation adds
the instantiated values' variables, abstraction removes some). These lemmas carry the invariant
"every free variable met is a fresh name below the bound" through a run, which the renaming
simulation needs for `==` to be kept.
-/

open private Ix.Compile.Canon.liftLoose.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Canon.lowerLoose.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Image.abstractFVars.go from Ix.Compile.Image.Expr

namespace Ix.CompileCert.Img

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose instantiateRevAt instantiateRev)

section
variable {P : Name → Prop}

theorem FvAll.mkApp {f a : Expr} (hf : FvAll P f) (ha : FvAll P a) : FvAll P (Expr.mkApp f a) := ⟨hf, ha⟩
theorem FvAll.mkLam (n : Name) {t b : Expr} (bi : Lean.BinderInfo) (ht : FvAll P t) (hb : FvAll P b) :
    FvAll P (Expr.mkLam n t b bi) := ⟨ht, hb⟩
theorem FvAll.mkForallE (n : Name) {t b : Expr} (bi : Lean.BinderInfo) (ht : FvAll P t)
    (hb : FvAll P b) : FvAll P (Expr.mkForallE n t b bi) := ⟨ht, hb⟩
theorem FvAll.mkLetE (n : Name) {t v b : Expr} (nd : Bool) (ht : FvAll P t) (hv : FvAll P v)
    (hb : FvAll P b) : FvAll P (Expr.mkLetE n t v b nd) := ⟨ht, hv, hb⟩
theorem FvAll.mkMData (d : Array (Name × Ix.DataValue)) {x : Expr} (hx : FvAll P x) :
    FvAll P (Expr.mkMData d x) := hx
theorem FvAll.mkProj (s : Name) (i : Nat) {x : Expr} (hx : FvAll P x) : FvAll P (Expr.mkProj s i x) := hx
theorem FvAll.mkConst (n : Name) (us : Array Level) : FvAll P (Expr.mkConst n us) := trivial
theorem FvAll.mkBVar (i : Nat) : FvAll P (Expr.mkBVar i) := trivial
theorem FvAll.mkFVar {n : Name} (h : P n) : FvAll P (Expr.mkFVar n) := h

/-- All elements of a list satisfy `FvAll P`. -/
def LFv (P : Name → Prop) (l : List Expr) : Prop := ∀ a ∈ l, FvAll P a

theorem foldl_mkApp_fv : ∀ {as : List Expr} {f : Expr}, FvAll P f → LFv P as →
    FvAll P (as.foldl Expr.mkApp f)
  | [], _, h, _ => h
  | _ :: _, _, h, ha => by
    simp only [List.foldl_cons]
    exact foldl_mkApp_fv (FvAll.mkApp h (ha _ List.mem_cons_self))
      fun x hx => ha x (List.mem_cons_of_mem _ hx)

theorem mkAppN_fv {f : Expr} {as : Array Expr} (hf : FvAll P f) (ha : LFv P as.toList) :
    FvAll P (mkAppN f as) := by
  simp only [mkAppN, ← Array.foldl_toList]; exact foldl_mkApp_fv hf ha

theorem getAppFnArgs_fv : ∀ {e : Expr}, FvAll P e →
    FvAll P (getAppFnArgs e).1 ∧ LFv P (getAppFnArgs e).2.toList
  | .app f a _, h => by
    obtain ⟨g1, g2⟩ := getAppFnArgs_fv h.1
    simp only [getAppFnArgs, Array.toList_push]
    refine ⟨g1, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact g2 x hx
    · exact h.2
  | .bvar .., h | .fvar .., h | .mvar .., h | .sort .., h | .const .., h | .lam .., h
  | .forallE .., h | .letE .., h | .lit .., h | .mdata .., h | .proj .., h =>
    ⟨h, fun x hx => by simp [getAppFnArgs] at hx⟩

theorem liftLoose_go_fv (n : Nat) : ∀ {e : Expr} (c : Nat), FvAll P e →
    FvAll P (Ix.Compile.Canon.liftLoose.go n e c)
  | .bvar .., c, _ => by simp only [Ix.Compile.Canon.liftLoose.go]; split <;> trivial
  | .fvar .., _, h | .mvar .., _, h | .sort .., _, h | .const .., _, h | .lit .., _, h => h
  | .app .., c, h => ⟨liftLoose_go_fv n c h.1, liftLoose_go_fv n c h.2⟩
  | .lam .., c, h | .forallE .., c, h => ⟨liftLoose_go_fv n c h.1, liftLoose_go_fv n (c + 1) h.2⟩
  | .letE .., c, h =>
    ⟨liftLoose_go_fv n c h.1, liftLoose_go_fv n c h.2.1, liftLoose_go_fv n (c + 1) h.2.2⟩
  | .mdata _ x _, c, h => liftLoose_go_fv n (e := x) c h
  | .proj _ _ x _, c, h => liftLoose_go_fv n (e := x) c h

theorem liftLoose_fv {e : Expr} (h : FvAll P e) (n c : Nat) : FvAll P (liftLoose e n c) := by
  unfold liftLoose; split
  · exact h
  · exact liftLoose_go_fv n c h

theorem lowerLoose_go_fv (n : Nat) : ∀ {e : Expr} (c : Nat), FvAll P e →
    FvAll P (Ix.Compile.Canon.lowerLoose.go n e c)
  | .bvar .., c, _ => by simp only [Ix.Compile.Canon.lowerLoose.go]; split <;> trivial
  | .fvar .., _, h | .mvar .., _, h | .sort .., _, h | .const .., _, h | .lit .., _, h => h
  | .app .., c, h => ⟨lowerLoose_go_fv n c h.1, lowerLoose_go_fv n c h.2⟩
  | .lam .., c, h | .forallE .., c, h => ⟨lowerLoose_go_fv n c h.1, lowerLoose_go_fv n (c + 1) h.2⟩
  | .letE .., c, h =>
    ⟨lowerLoose_go_fv n c h.1, lowerLoose_go_fv n c h.2.1, lowerLoose_go_fv n (c + 1) h.2.2⟩
  | .mdata _ x _, c, h => lowerLoose_go_fv n (e := x) c h
  | .proj _ _ x _, c, h => lowerLoose_go_fv n (e := x) c h

theorem lowerLoose_fv {e : Expr} (h : FvAll P e) (n c : Nat) : FvAll P (lowerLoose e n c) := by
  unfold lowerLoose; split
  · exact h
  · exact lowerLoose_go_fv n c h

theorem instantiateRevAt_fv {args : Array Expr} (ha : LFv P args.toList) :
    ∀ {e : Expr} (d : Nat), FvAll P e → FvAll P (instantiateRevAt args e d)
  | .bvar i .., d, _ => by
    simp only [instantiateRevAt]
    split
    · split
      · rename_i h1 h2
        exact liftLoose_fv (ha _ (by simp)) d 0
      · trivial
    · trivial
  | .fvar .., _, h | .mvar .., _, h | .sort .., _, h | .const .., _, h | .lit .., _, h => h
  | .app .., d, h => ⟨instantiateRevAt_fv ha d h.1, instantiateRevAt_fv ha d h.2⟩
  | .lam .., d, h | .forallE .., d, h =>
    ⟨instantiateRevAt_fv ha d h.1, instantiateRevAt_fv ha (d + 1) h.2⟩
  | .letE .., d, h =>
    ⟨instantiateRevAt_fv ha d h.1, instantiateRevAt_fv ha d h.2.1, instantiateRevAt_fv ha (d + 1) h.2.2⟩
  | .mdata _ x _, d, h => instantiateRevAt_fv ha (e := x) d h
  | .proj _ _ x _, d, h => instantiateRevAt_fv ha (e := x) d h

theorem instantiateRev_fv {args : Array Expr} (ha : LFv P args.toList) {e : Expr} (h : FvAll P e) :
    FvAll P (instantiateRev e args) := by
  unfold instantiateRev; split
  · exact h
  · exact instantiateRevAt_fv ha 0 h

theorem instLocals_fv {args : Array Expr} (ha : LFv P args.toList) {e : Expr} (h : FvAll P e) :
    FvAll P (Ix.Compile.Image.instLocals e args) :=
  instantiateRev_fv (by intro x hx; simp only [Array.toList_reverse, List.mem_reverse] at hx; exact ha x hx) h

theorem abstractFVars_go_fv (xs : Array Name) : ∀ {e : Expr} (d : Nat), FvAll P e →
    FvAll P (Ix.Compile.Image.abstractFVars.go xs e d)
  | .fvar n _, d, h => by
    simp only [Ix.Compile.Image.abstractFVars.go]; split
    · trivial
    · exact h
  | .bvar .., _, h | .mvar .., _, h | .sort .., _, h | .const .., _, h | .lit .., _, h => h
  | .app .., d, h => ⟨abstractFVars_go_fv xs d h.1, abstractFVars_go_fv xs d h.2⟩
  | .lam .., d, h | .forallE .., d, h => ⟨abstractFVars_go_fv xs d h.1, abstractFVars_go_fv xs (d + 1) h.2⟩
  | .letE .., d, h =>
    ⟨abstractFVars_go_fv xs d h.1, abstractFVars_go_fv xs d h.2.1, abstractFVars_go_fv xs (d + 1) h.2.2⟩
  | .mdata _ x _, d, h => abstractFVars_go_fv xs (e := x) d h
  | .proj _ _ x _, d, h => abstractFVars_go_fv xs (e := x) d h

theorem abstractFVars_fv (xs : Array Name) {e : Expr} (h : FvAll P e) :
    FvAll P (Ix.Compile.Image.abstractFVars xs e) := by
  unfold Ix.Compile.Image.abstractFVars; split
  · exact h
  · exact abstractFVars_go_fv xs 0 h

theorem mkBinders_fv (isLam : Bool) (xs : Array Ix.Compile.Image.Local) (hx : ∀ l ∈ xs, FvAll P l.type)
    {b : Expr} (hb : FvAll P b) : FvAll P (Ix.Compile.Image.mkBinders isLam xs b) := by
  rw [mkBinders_eq, ← Array.foldr_toList]
  have : ∀ (L : List (Ix.Compile.Image.Local × Nat)), (∀ p ∈ L, FvAll P p.1.type) →
      FvAll P (L.foldr (binderStep isLam (xs.map (·.fvar))) (Ix.Compile.Image.abstractFVars (xs.map (·.fvar)) b)) := by
    intro L
    induction L with
    | nil => intro _; exact abstractFVars_fv _ hb
    | cons p L ih =>
      intro h
      simp only [List.foldr_cons]
      unfold binderStep
      have h1 := abstractFVars_fv ((xs.map (·.fvar)).extract 0 p.2) (h p List.mem_cons_self)
      have h2 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
      cases isLam
      · exact ⟨h1, h2⟩
      · exact ⟨h1, h2⟩
  apply this
  intro p hp
  simp only [Array.mem_toList_iff] at hp
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hp
  simp only [Array.getElem_zipIdx]
  exact hx _ (Array.getElem_mem _)

theorem stripMdata_fv : ∀ {e : Expr}, FvAll P e → FvAll P (Ix.Compile.Canon.stripMdata e)
  | .mdata _ x _, h => by simp only [Ix.Compile.Canon.stripMdata]; exact stripMdata_fv (e := x) h
  | .bvar .., h | .fvar .., h | .mvar .., h | .sort .., h | .const .., h | .lit .., h | .app .., h
  | .lam .., h | .forallE .., h | .letE .., h | .proj .., h => by
    simp only [Ix.Compile.Canon.stripMdata]; exact h

theorem peelForalls_fv : ∀ (n : Nat) {e : Expr} {acc : Array Ix.Compile.Canon.Binder},
    FvAll P e → (∀ b ∈ acc, FvAll P b.2.1) →
    (∀ b ∈ (Ix.Compile.Canon.peelForalls n e acc).1, FvAll P b.2.1) ∧
      FvAll P (Ix.Compile.Canon.peelForalls n e acc).2
  | 0, _, _, h, ha => ⟨ha, h⟩
  | n + 1, e, acc, h, ha => by
    simp only [Ix.Compile.Canon.peelForalls]
    have hs := stripMdata_fv h
    generalize Ix.Compile.Canon.stripMdata e = e' at hs
    cases e' with
    | forallE nm t b bi _ =>
      simp only
      apply peelForalls_fv n hs.2
      intro x hx
      simp only [Array.mem_push] at hx
      rcases hx with hx | rfl
      · exact ha x hx
      · exact hs.1
    | _ => exact ⟨ha, hs⟩

theorem instForall_fv {e : Expr} {vs : Array Expr} (he : FvAll P e) (hv : LFv P vs.toList) {r : Expr}
    (h : Ix.Compile.Image.instForall e vs = .ok r) : FvAll P r := by
  unfold Ix.Compile.Image.instForall at h
  have hp := peelForalls_fv vs.size he (acc := #[]) (by simp)
  generalize Ix.Compile.Canon.peelForalls vs.size e #[] = p at hp h
  obtain ⟨bs, body⟩ := p
  simp only at h hp
  split at h
  · cases h
  · cases h; exact instLocals_fv hv hp.2

theorem etaReduce_fv : ∀ {e : Expr}, FvAll P e → FvAll P (Ix.Compile.Image.etaReduce e)
  | .lam n d b bi _, h => by
    rw [etaReduce_lam]
    have hb := etaReduce_fv (e := b) h.2
    generalize Ix.Compile.Image.etaReduce b = x at hb
    unfold etaStep
    split
    · rename_i f h1 h2
      split
      · exact lowerLoose_fv (show FvAll P f from hb.1) 1 0
      · exact ⟨h.1, hb⟩
    · exact ⟨h.1, hb⟩
  | .bvar .., h | .fvar .., h | .mvar .., h | .sort .., h | .const .., h | .lit .., h | .app .., h
  | .forallE .., h | .letE .., h | .mdata .., h | .proj .., h => by
    simp only [Ix.Compile.Image.etaReduce]; exact h

end

end Ix.CompileCert.Img
