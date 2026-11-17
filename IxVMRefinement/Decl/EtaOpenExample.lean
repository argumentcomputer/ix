import IxVMRefinement.Decl.EtaOpen

/-! # A structure with a parameter: η typing at open and closed spines

`Box : Type → Type` with the constructor `Box.mk : (α : Type) → α → Box α`, η-capable, stored
with its constructor (the keys are placeholders: two role keys of no other use here). At this
environment:

* the block route's statement fails (`not_etaTypeOpen`), and so do `EtaStable` and the typing
  clause of `EtaUseFacts` as stated (`not_etaStable`): `Box.mk (bvar 0) (sort 0)` infers
  `Box (sort 0)`, which does not reduce to `Box (bvar 0)`;
* the stored family has its shape (`etaShape`), so the closed form holds at every extension
  (`etaStableC`), and its conclusion is reached at a closed spine (`closed_instance`).
-/

namespace IxVM.Refinement.Decl.EtaOpenExample

open IxVM.Refinement.Core IxVM.Refinement.Decl
open Ix.Kernel (Env Expr Level ConstantVal ConstantInfo IndCaps BinderMeta Key)
open Ix.Kernel.Rules (Red Infer)

/-- A binder never a proposition. -/
def nb : BinderMeta := { pw := .never }

/-- The family's key (a placeholder). -/
def boxKey : KKey := .role .string

/-- The constructor's key (a placeholder). -/
def mkKey : KKey := .role .stringOfList

/-- `Box : Type → Type`. -/
def boxCV : ConstantVal .anon := ⟨boxKey, [], .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) nb⟩

/-- `Box.mk : (α : Type) → α → Box α`. -/
def mkCV : ConstantVal .anon :=
  ⟨mkKey, [], .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.app (.const boxKey []) (.bvar 1)) nb) nb⟩

/-- η-capable, one parameter, one field, never a proposition. -/
def boxCaps : IndCaps .anon :=
  { eta := true, etaCtor := some mkKey, etaParams := 1, etaFields := 1, sortZ := .never }

/-- The environment storing the family and its constructor. -/
def boxEnv : Env .anon := ⟨[.ctorInfo mkCV 1 1, .indInfo boxCV boxCaps]⟩

theorem find_mk : boxEnv.find? mkKey = some (.ctorInfo mkCV 1 1) := rfl

theorem find_box : boxEnv.find? boxKey = some (.indInfo boxCV boxCaps) := rfl

theorem mem_boxEnv {k : KKey} {c : ConstantInfo .anon} (h : boxEnv.find? k = some c) :
    c = .ctorInfo mkCV 1 1 ∨ c = .indInfo boxCV boxCaps := by
  have hm := List.mem_of_find?_eq_some h
  simpa [boxEnv] using hm

/-- No definition and no recursor is stored. -/
theorem bclosed : BClosedStore boxEnv where
  defn := fun hf => by rcases mem_boxEnv hf with h | h <;> exact nomatch h
  rhs := fun hf => by rcases mem_boxEnv hf with h | h <;> exact nomatch h

theorem mk_strip :
    mkCV.type.stripPis (1 + 1) =
      some ([(.sort (.succ .zero), nb), (.bvar 0, nb)],
        Expr.mkAppN (.const boxKey (mkCV.levelParams.map .param)) (Ix.Kernel.structPsAt 1 1)) :=
  rfl

theorem mk_never : ∀ b ∈ ([(.sort (.succ .zero), nb), (.bvar 0, nb)] : List (KExpr × BinderMeta)),
    (Level.substPW mkCV.levelParams [] b.2.pw).isNever = true := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;> rfl

/-- **The block route's statement is false.** -/
theorem not_etaTypeOpen : ¬ EtaTypeOpenStmt := by
  intro h
  obtain ⟨args, ty, hlen, hinf, hnot⟩ :=
    etaType_open_false bclosed find_mk rfl mk_strip (us := []) rfl mk_never (Nat.le_refl 1)
      (Nat.le_refl 2) boxKey 0
  exact hnot (h boxEnv boxKey mkKey mkCV 1 1 _ find_mk List.nodup_nil mk_strip 0 [] args ty hlen
    hinf)

/-- **`EtaStable` and the typing clause of `EtaUseFacts` fail here.** -/
theorem not_etaStable :
    ¬ EtaStable boxEnv ∧ ¬ EtaUseFacts boxEnv boxKey mkKey boxCV boxCaps 1 1 :=
  not_etaStable_of_param bclosed find_box rfl rfl find_mk rfl mk_strip (us := []) rfl mk_never
    (Nat.le_refl 1) (Nat.le_refl 2)

/-- The stored family has its shape. -/
theorem etaShape : EtaShape boxEnv := by
  intro T cvT caps hT heta
  have hname := List.find?_some hT
  rcases mem_boxEnv hT with h | h
  · exact nomatch h
  · cases h
    have hT' : boxKey = T := by
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal, boxCV] using hname
    subst hT'
    refine ⟨⟨[(.sort (.succ .zero), nb)], .succ .zero, rfl, rfl⟩, ?_⟩
    intro kc cvc nP nF hkc hC
    have hkc' : kc = mkKey := (Option.some.inj hkc).symm
    subst hkc'
    rw [find_mk] at hC
    cases hC
    exact ⟨List.nodup_nil, rfl, rfl, rfl, _, mk_strip⟩

theorem etaStableC : EtaStableC boxEnv := etaStableC_of_etaShape etaShape

/-- **The closed form's conclusion is reached**: `Box.mk (sort 0) x : Box (sort 0)` for an opened
variable `x : sort 0`. -/
theorem closed_instance :
    ∃ ty, Infer boxEnv .io 1 (Expr.mkAppN (.const mkKey []) [.sort .zero, .fvar 0 (.sort .zero)]) ty ∧
      Red boxEnv 1 ty (Expr.mkAppN (.const boxKey []) [.sort .zero]) := by
  have hconst : Infer boxEnv .io 1 (.const mkKey [])
      (mkCV.type.instantiateLevelParams mkCV.levelParams []) :=
    Ix.Kernel.Rules.Infer.const (ci := .ctorInfo mkCV 1 1) find_mk rfl rfl
  have hst := stripPis_ilp mkCV.levelParams [] (1 + 1) mk_strip
  have hinf := infer_spine_skip' [.sort .zero, .fvar 0 (.sort .zero)] rfl hconst hst (by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb
    exact mk_never b₀ hb₀)
  exact ⟨_, hinf, etaStableC boxKey mkKey boxCV mkCV boxCaps 1 1 find_box rfl rfl find_mk boxEnv
    (Ix.Kernel.EnvExt.refl _) 1 [] _ _ rfl (by simp [Expr.looseBVarsBounded]) hinf⟩

end IxVM.Refinement.Decl.EtaOpenExample
