import IxCCGrounding.Apply
import IxCCGrounding.Lits
import IxCC.Src.Proof.Unfold
import IxCC.Sem.Bind

/-!
# Support for the fundamental lemma (`IxCCGrounding.Support`), step (f)

Generic lemmas the assembly uses and nothing else does: access to related lists by index, take
and drop; the `RelEnv` lookup; that kernel levels corresponding to Src universes evaluate as Src
evaluates them, so a constant used at corresponding levels is read at an assignment that agrees
with SrcEval's instantiation (`lvAt_inst`); that a `Fits` shorter than a stored telescope leaves a
`∀` (`fits_pi_of_lt`); the two semantic site conditions the assembly passes around
(`AppChain`, `LastSiteOk`); literal values and their sets.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Result)

universe w

/-! ## Results -/

theorem ofOption_eq_ok {α : Type} {o : Option α} {x : α} :
    Result.ofOption o = .ok x ↔ o = some x := by
  cases o <;> simp [Result.ofOption]

theorem ok_inj {α : Type} {x y : α} (h : (Result.ok x : Result α) = .ok y) : x = y := by
  cases h; rfl

/-! ## Levels -/

theorem univCorr_eval {φ : LevelParam → Nat} {lps : List Nat} {ls : Levels} (hlv : LvAt φ lps ls) :
    ∀ {u : IxCC.Ixon.Univ} {l : Level}, UnivCorr lps u l → Level.eval φ l = IxCC.Src.evalUniv ls u
  | _, _, .zero => rfl
  | _, _, .succ h => by simp only [Level.eval, IxCC.Src.evalUniv, univCorr_eval hlv h]
  | _, _, .max h1 h2 => by
    simp only [Level.eval, IxCC.Src.evalUniv, univCorr_eval hlv h1, univCorr_eval hlv h2]
  | _, _, @UnivCorr.imax _ _ b _ _ h1 h2 => by
    simp only [Level.eval, IxCC.Src.evalUniv, univCorr_eval hlv h1, univCorr_eval hlv h2]
    by_cases h : IxCC.Src.evalUniv ls b = 0
    · simp [h]
    · simp [h]
  | _, _, .var h => by simp only [Level.eval, IxCC.Src.evalUniv]; exact hlv _ _ h

theorem substFn_at (φ : LevelParam → Nat) :
    ∀ (ks : List LevelParam) (vs : List Level) (i : Nat) (p : LevelParam) (l : Level),
      ks.Nodup → ks[i]? = some p → vs[i]? = some l → Level.substFn φ ks vs p = Level.eval φ l
  | [], _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h => by simp at h
  | k :: ks, v :: vs, 0, p, l, _, hk, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk hv
    subst hk hv
    simp [Level.substFn]
  | k :: ks, v :: vs, i + 1, p, l, hnd, hk, hv => by
    simp only [List.getElem?_cons_succ] at hk hv
    have hne : k ≠ p := by
      intro he
      subst he
      exact (List.nodup_cons.mp hnd).1 (List.mem_of_getElem? hk)
    simp only [Level.substFn, hne, ↓reduceIte]
    exact substFn_at φ ks vs i p l (List.nodup_cons.mp hnd).2 hk hv

/-- **A constant used at corresponding levels is read at an assignment agreeing with SrcEval's
instantiation**: the kernel term `.const n ls'` denotes `cval n (substFn φ lpsC ls')`, and that
assignment agrees on the constant's parameters `lpsC` with `us.map (evalUniv ls)`, the levels
SrcEval unfolds the constant at. Needs the parameters distinct (a stored-shape fact). -/
theorem lvAt_inst {φ : LevelParam → Nat} {lps : List Nat} {ls : Levels} (hlv : LvAt φ lps ls)
    {lpsC : List Nat} (hnd : lpsC.Nodup) {us : List IxCC.Ixon.Univ} {ls' : List Level}
    (hlen : us.length = ls'.length) (hlen' : ls'.length = lpsC.length)
    (hcorr : ∀ (i : Nat) (u : IxCC.Ixon.Univ) (l : Level), us[i]? = some u → ls'[i]? = some l →
      UnivCorr lps u l) :
    LvAt (Level.substFn φ lpsC ls') lpsC (us.map (IxCC.Src.evalUniv ls)) := by
  intro i p hp
  have hi : i < lpsC.length := by
    rcases (List.getElem?_eq_some_iff.mp hp) with ⟨h, _⟩; exact h
  have hi' : i < ls'.length := by omega
  have hiu : i < us.length := by omega
  rw [substFn_at φ lpsC ls' i p ls'[i] hnd hp (List.getElem?_eq_getElem hi'),
    univCorr_eval hlv (hcorr i us[i] ls'[i] (List.getElem?_eq_getElem hiu)
      (List.getElem?_eq_getElem hi'))]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hiu]

/-! ## Telescopes -/

theorem fits_length_pis {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}
    {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ σ : BVarIdx → V}
    {T R : KExpr} {xs : List V} (h : Fits cval env φ ρ T xs σ R) :
    kPis T = xs.length + kPis R := by
  induction h with
  | nil => simp
  | cons _ _ _ ih => simp only [kPis, ih, List.length_cons]; omega

/-- A `Fits` shorter than the stored telescope leaves a `∀`. -/
theorem fits_pi_of_lt {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}
    {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ σ : BVarIdx → V}
    {T R : KExpr} {xs : List V} (h : Fits cval env φ ρ T xs σ R) (hl : xs.length < kPis T) :
    ∃ D B m, R = .forallE D B m := by
  have := fits_length_pis h
  cases R with
  | forallE D B m => exact ⟨D, B, m, rfl⟩
  | _ => simp only [kPis] at this; omega

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-! ## The two semantic site conditions -/

/-- `X` applied to `Ys` one at a time, each application at a graph-regime site: what `applyAll`
needs of a function and its arguments. -/
inductive AppChain : V → List V → Prop
  | nil {X : V} : AppChain X []
  | cons {X y : V} {ys : List V} {v : Nat} {A : V} {B : V → V} :
      v ≠ 0 → X ∈ˢ piR v A B → y ∈ˢ A → AppChain (app X y) ys → AppChain X (y :: ys)

/-- The last of the arguments `As` (if any) was applied to the others at a graph-regime site: what
SrcEval's saturating application of a special head gives `fire`. F5 reads the regime of the
binder that site filled from it (`last_regime`). -/
def LastSiteOk (H : V) (As : List V) : Prop :=
  ∀ (As' : List V) (y : V), As = As' ++ [y] →
    ∃ (v : Nat) (A : V) (B : V → V), v ≠ 0 ∧ As'.foldl app H ∈ˢ piR v A B ∧ y ∈ˢ A

theorem lastSiteOk_nil (H : V) : LastSiteOk H [] := by
  intro As' y h
  exact absurd h.symm (by simp)

theorem lastSiteOk_snoc {H : V} {As : List V} {y : V} {v : Nat} {A : V} {B : V → V}
    (hv : v ≠ 0) (hX : As.foldl app H ∈ˢ piR v A B) (hy : y ∈ˢ A) : LastSiteOk H (As ++ [y]) := by
  intro As' y' h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, and_true] at h2
  subst h1 h2
  exact ⟨v, A, B, hv, hX, hy⟩

/-! ## Related lists -/

variable {M : Model V env} {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
  {Ok : CId → Levels → Prop}

theorem relEnv_get : ∀ {ρ : IxCC.Src.Env} {ρk : BVarIdx → V} {i : Nat} {s : Slot},
    RelEnv M κ lpsOf S Ok ρ ρk → ρ[i]? = some s → RelSlot M κ lpsOf S Ok s (ρk i)
  | [], _, _, _, _, h => by simp at h
  | _ :: _, _, 0, _, he, h => by
    cases he with
    | cons hs _ => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact hs
  | _ :: _, ρk, i + 1, _, he, h => by
    cases he with
    | cons _ hrest =>
      simp only [List.getElem?_cons_succ] at h
      exact relEnv_get (ρk := fun j => ρk (j + 1)) hrest h

theorem relSlots_get : ∀ {ss : List Slot} {Xs : List V} {i : Nat} {s : Slot},
    RelSlots M κ lpsOf S Ok ss Xs → ss[i]? = some s → ∃ X, Xs[i]? = some X ∧ RelSlot M κ lpsOf S Ok s X
  | [], _, _, _, _, h => by simp at h
  | _ :: _, _, 0, _, hr, h => by
    cases hr with
    | cons hs _ =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      exact ⟨_, rfl, hs⟩
  | _ :: _, _, i + 1, _, hr, h => by
    cases hr with
    | cons _ hrest =>
      simp only [List.getElem?_cons_succ] at h ⊢
      exact relSlots_get hrest h

theorem relSlots_get' : ∀ {ss : List Slot} {Xs : List V} {i : Nat} {X : V},
    RelSlots M κ lpsOf S Ok ss Xs → Xs[i]? = some X → ∃ s, ss[i]? = some s ∧ RelSlot M κ lpsOf S Ok s X
  | _, [], _, _, _, h => by simp at h
  | _, _ :: _, 0, _, hr, h => by
    cases hr with
    | cons hs _ =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      exact ⟨_, rfl, hs⟩
  | _, _ :: _, i + 1, _, hr, h => by
    cases hr with
    | cons _ hrest =>
      simp only [List.getElem?_cons_succ] at h ⊢
      exact relSlots_get' hrest h

theorem relVs_get : ∀ {vs : List Value} {Xs : List V} {i : Nat} {v : Value},
    RelVs M κ lpsOf S Ok vs Xs → vs[i]? = some v → ∃ X, Xs[i]? = some X ∧ RelV M κ lpsOf S Ok v X
  | [], _, _, _, _, h => by simp at h
  | _ :: _, _, 0, _, hr, h => by
    cases hr with
    | cons hs _ =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      exact ⟨_, rfl, hs⟩
  | _ :: _, _, i + 1, _, hr, h => by
    cases hr with
    | cons _ hrest =>
      simp only [List.getElem?_cons_succ] at h ⊢
      exact relVs_get hrest h

theorem relVs_length : ∀ {vs : List Value} {Xs : List V}, RelVs M κ lpsOf S Ok vs Xs →
    Xs.length = vs.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    cases h with
    | cons _ h' => simp [relVs_length h']

theorem relSlots_take : ∀ (n : Nat) {ss : List Slot} {Xs : List V},
    RelSlots M κ lpsOf S Ok ss Xs → RelSlots M κ lpsOf S Ok (ss.take n) (Xs.take n)
  | 0, _, _, _ => .nil
  | _ + 1, [], _, h => by cases h; exact .nil
  | n + 1, _ :: _, _, h => by
    cases h with
    | cons hs h' => exact .cons hs (relSlots_take n h')

theorem relSlots_drop : ∀ (n : Nat) {ss : List Slot} {Xs : List V},
    RelSlots M κ lpsOf S Ok ss Xs → RelSlots M κ lpsOf S Ok (ss.drop n) (Xs.drop n)
  | 0, _, _, h => h
  | _ + 1, [], _, h => by cases h; exact .nil
  | n + 1, _ :: _, _, h => by
    cases h with
    | cons _ h' => exact relSlots_drop n h'

theorem relVs_nil_right {vs : List Value} (h : RelVs M κ lpsOf S Ok vs ([] : List V)) : vs = [] := by
  cases h; rfl

theorem relVs_single_right {vs : List Value} {X : V} (h : RelVs M κ lpsOf S Ok vs [X]) :
    ∃ v, vs = [v] ∧ RelV M κ lpsOf S Ok v X := by
  cases h with
  | cons hv h' => cases h'; exact ⟨_, rfl, hv⟩

/-! ## Literals -/

/-- A literal value relates to the literal's set, at any assignment (level-parameter irrelevance
only). -/
theorem relV_lit_eq_cv (hcv : CvalParams M) (hS : NatBasis env) (φ : LevelParam → Nat)
    {n : Nat} {X : V} (h : RelV M κ lpsOf S Ok (.lit n) X) : X = litSet M φ n := by
  cases h with
  | @lit _ _ φ' ρ' hd =>
    rw [(lit_den M (natFacts M hS φ') ρ' n X).mp hd]
    exact litSet_indep_cv M hcv hS φ' φ n

/-- A literal value relates to the literal's set, at any assignment. -/
theorem relV_lit_eq (hL : LawsCore M) (hS : NatBasis env) (φ : LevelParam → Nat)
    {n : Nat} {X : V} (h : RelV M κ lpsOf S Ok (.lit n) X) : X = litSet M φ n :=
  relV_lit_eq_cv hL.cval_params hS φ h

theorem relV_lit_intro (hS : NatBasis env) (φ : LevelParam → Nat) (n : Nat) :
    RelV M κ lpsOf S Ok (.lit n) (litSet M φ n) :=
  .lit (φ := φ) (ρ := fun _ => empty) ((lit_den M (natFacts M hS φ) _ n _).mpr rfl)

end Sem

/-! ## Small facts about SrcEval's data -/

theorem litArgs_some : ∀ {vs : List Value} {ns : List Nat}, IxCC.Src.litArgs vs = some ns →
    vs = ns.map .lit
  | [], ns, h => by simp [IxCC.Src.litArgs] at h; subst h; rfl
  | .lit n :: vs, ns, h => by
    simp only [IxCC.Src.litArgs, Option.map_eq_some_iff] at h
    obtain ⟨ns', h', rfl⟩ := h
    rw [litArgs_some h']
    rfl
  | .str _ :: _, _, h | .con .. :: _, _, h | .clo .. :: _, _, h | .pap .. :: _, _, h
  | .irr .. :: _, _, h => by simp [IxCC.Src.litArgs] at h

theorem evalLits_some {op : IxCC.Src.PrimOp} {ns : List Nat} {res : IxCC.Src.PrimResult}
    (h : op.evalLits ns = some res) :
    (∃ a, ns = [a] ∧ op.arity = 1 ∧ res = op.eval2 a 0) ∨
      (∃ a b, ns = [a, b] ∧ op.arity = 2 ∧ res = op.eval2 a b) := by
  match ns, h with
  | [a], h =>
    simp only [IxCC.Src.PrimOp.evalLits] at h
    split at h
    · rename_i ha; left; exact ⟨a, rfl, by simpa using ha, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  | [a, b], h =>
    simp only [IxCC.Src.PrimOp.evalLits] at h
    split at h
    · rename_i ha; right; exact ⟨a, b, rfl, by simpa using ha, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  | [], h => simp [IxCC.Src.PrimOp.evalLits] at h
  | _ :: _ :: _ :: _, h => simp [IxCC.Src.PrimOp.evalLits] at h

theorem single_ctor {cs : List CId} {c : CId}
    (h : (cs.length == 1 && cs.head? == some c) = true) : cs = [c] := by
  match cs, h with
  | [c'], h => simp at h; subst h; rfl
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

theorem mentions_app_left {f a : Term} {m : IxCC.Src.Mode} {r : IxCC.Src.Rel} {S : CId → Prop}
    (h : ConstsIn S (.app f a m r)) : ConstsIn S f :=
  fun c hc => h c (by simp [Term.mentions, hc])

theorem mentions_app_right {f a : Term} {m : IxCC.Src.Mode} {r : IxCC.Src.Rel} {S : CId → Prop}
    (h : ConstsIn S (.app f a m r)) : ConstsIn S a :=
  fun c hc => h c (by simp [Term.mentions, hc])

theorem mentions_proj {s i : Nat} {e : Term} {S : CId → Prop} (h : ConstsIn S (.proj s i e)) :
    S s ∧ ConstsIn S e :=
  ⟨h s (by simp [Term.mentions]), fun c hc => h c (by simp [Term.mentions, hc])⟩

theorem mentions_const {c : CId} {us : List IxCC.Ixon.Univ} {S : CId → Prop}
    (h : ConstsIn S (.const c us)) : S c :=
  h c (by simp [Term.mentions])

end IxCC.Grounding
