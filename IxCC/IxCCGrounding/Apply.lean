import IxCCGrounding.Relation

/-!
# The application lemma (`IxCCGrounding.Apply`), step (e) of the spike

SrcEval's `apply` on a function value `f` and a slot `s` (rules A1 and A2). At an application site
in the graph regime (`SiteOk`: the function's denotation `X` lies in a product `piR v A B` with
`v ≠ 0` whose domain holds the argument's denotation `Y`):

* **A1, a closure** (`apply_clo`): `X` is what the closure's λ denotes; its regime is not `0`
  (a proof is not a member of a graph-regime product), so it is a graph over the λ's domain;
  that domain is `A` (`lamR_dom_eq`), so `Y` lies in it, `app X Y` is the body's denotation with
  `Y` bound, and the extended environments are related and satisfy the extended context. The
  fundamental lemma then runs the body (its induction hypothesis at the next clock).
* **A2, a partial application** (`apply_pap`): `X` is the head's denotation applied to arguments
  that fit the head's stored type; the remaining type is a `∀` (the head's telescope is long
  enough), whose denotation also contains `X`, so its domain is `A`, and the new argument extends
  `Fits`. Firing a saturated head (F1, F5, F6) is a separate lemma per head kind; `natCases_*`
  is F5's.

No typing derivation is consumed here beyond `SiteOk` at the site; the arguments' fit comes from
the stored type and `mem` of the head.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-! ## Facts about stored constants and `Fits` (step (d)) -/

theorem find_name {n : KKey} {ci : ConstantInfo .anon} (h : env.find? n = some ci) :
    ci.toConstantVal.name = n := by
  have := List.find?_some h
  simpa [ConstantInfo.name] using this

/-- `mem`, read at a key: a stored constant's `cval` lies in its stored type's denotation. -/
theorem mem_key (M : Model V env) {n : KKey} {ci : ConstantInfo .anon}
    (hf : env.find? n = some ci) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ T, Denotes M.cval env φ ρ ci.toConstantVal.type T ∧ M.cval n φ ∈ˢ T := by
  obtain ⟨T, hT, hm⟩ := M.mem ci (find_mem hf) φ ρ
  refine ⟨T, hT, ?_⟩
  simp only [ConstantInfo.name] at hm
  rwa [find_name hf] at hm

theorem head_mem (M : Model V env) {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
    {h : IxCC.Src.Head}
    {ls : Levels} {φ : LevelParam → Nat} {k : KKey} {T : KExpr}
    (hh : HeadAt M κ lpsOf S h ls φ k T) (ρ : BVarIdx → V) :
    ∃ TT, Denotes M.cval env φ ρ T TT ∧ M.cval k φ ∈ˢ TT := by
  cases hh with
  | ctor _ _ hf => exact mem_key M hf φ ρ
  | cases _ _ hf => exact mem_key M hf φ ρ
  | prim hf _ _ => exact mem_key M hf φ ρ

/-- Arguments that fit a telescope, applied to a member of its denotation, land in the remainder's. -/
theorem fits_app_mem {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {ρ σ : BVarIdx → V} {T R : KExpr} {xs : List V} (h : Fits cval env φ ρ T xs σ R) :
    ∀ {f TT : V}, Denotes cval env φ ρ T TT → f ∈ˢ TT →
      ∃ RR, Denotes cval env φ σ R RR ∧ xs.foldl app f ∈ˢ RR := by
  induction h with
  | nil => intro f TT hT hf; exact ⟨TT, hT, hf⟩
  | cons hA hx _ ih =>
    intro f TT hT hf
    obtain ⟨B, hB, hm⟩ := app_mem_den_pi hT hA hf hx
    exact ih hB hm

/-- `Fits`, extended by one argument in the next domain. -/
theorem fits_snoc {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {ρ σ : BVarIdx → V} {T R : KExpr} {xs : List V} (h : Fits cval env φ ρ T xs σ R) :
    ∀ {D Bk : KExpr} {m : BinderMeta} {DD y : V}, R = .forallE D Bk m →
      Denotes cval env φ σ D DD → y ∈ˢ DD → Fits cval env φ ρ T (xs ++ [y]) (push y σ) Bk := by
  induction h with
  | nil => intro D Bk m DD y hR hD hy; subst hR; exact .cons hD hy .nil
  | cons hA hx _ ih => intro D Bk m DD y hR hD hy; exact .cons hA hx (ih hR hD hy)

/-- A λ's graph determines its domain: if it lies in a graph-regime product, that product's
domain is the λ's. -/
theorem lamR_dom_eq {r v : Nat} {Ad A : V} {G B : V → V} (hr : r ≠ 0) (hv : v ≠ 0)
    (h : lamR r Ad G ∈ˢ piR v A B) : A = Ad :=
  piR_dom_unique hv hr h (lamR_mem (B := fun x => sing (G x)) fun _ _ => mem_sing.mpr rfl)

omit [Ix.Kernel.SetTheory V] in
theorem push_tail (Y : V) (ρk : BVarIdx → V) : (fun i => push Y ρk (i + 1)) = ρk :=
  funext fun _ => rfl

section Rel

variable {M : Model V env} {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
  {Ok : CId → Levels → Prop}

theorem relSlots_length : ∀ {ss : List Slot} {Xs : List V}, RelSlots M κ lpsOf S Ok ss Xs →
    Xs.length = ss.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    cases h with
    | cons _ h' => simp [relSlots_length h']

theorem relSlots_snoc : ∀ {ss : List Slot} {Xs : List V} {s : Slot} {X : V},
    RelSlots M κ lpsOf S Ok ss Xs → RelSlot M κ lpsOf S Ok s X →
    RelSlots M κ lpsOf S Ok (ss ++ [s]) (Xs ++ [X])
  | [], _, _, _, h, hs => by cases h; exact .cons hs .nil
  | _ :: _, _, _, _, h, hs => by
    cases h with
    | cons h1 h' => exact .cons h1 (relSlots_snoc h' hs)

/-! ## The application lemma -/

/-- **A1: applying a closure** at a graph-regime site. -/
theorem apply_clo {b : IxCC.Src.Binder} {dom body : Term} {ρ : IxCC.Src.Env} {ls : Levels}
    {X Y : V} {s : Slot}
    (hv : RelV M κ lpsOf S Ok (.clo b dom body ρ ls) X) (hs : RelSlot M κ lpsOf S Ok s Y)
    {v : Nat} {A : V} {B : V → V} (hvz : v ≠ 0) (hX : X ∈ˢ piR v A B) (hY : Y ∈ˢ A) :
    ∃ (φ : LevelParam → Nat) (lps : List Nat) (Γ : List KExpr) (ρk : BVarIdx → V)
      (Ak Bk : KExpr) (Z : V),
      LvAt φ lps ls ∧ RelEnv M κ lpsOf S Ok (s :: ρ) (push Y ρk) ∧
      CtxSat M φ (Ak :: Γ) (push Y ρk) ∧ Runs M κ Ok lps ls φ (Ak :: Γ) body Bk ∧
      ConstsIn S body ∧ Denotes M.cval env φ (push Y ρk) Bk Z ∧ app X Y = Z := by
  cases hv with
  | @clo _ _ _ _ _ φ lps Γ ρk Ak Bk m _ hlv henv hctx hruns hcs hden =>
    cases hruns with
    | lam _ hbody _ =>
      obtain ⟨Ad, G, hAd, hG, _, hXe⟩ := den_lam.mp hden
      subst hXe
      have hr : regime φ m.pw ≠ 0 := by
        intro h0
        rw [h0, lamR_zero] at hX
        exact not_pt_mem_piR_pos hvz hX
      have hYd : Y ∈ˢ Ad := lamR_dom_eq hr hvz hX ▸ hY
      refine ⟨φ, lps, Γ, ρk, Ak, Bk, G Y, hlv, ?_, ?_, hbody, ?_, hG Y hYd, app_lamR_pos hr hYd⟩
      · exact .cons hs (by rw [push_tail]; exact henv)
      · exact .cons (by rw [push_tail]; exact hctx) (by rw [push_tail]; exact hAd) hYd
      · intro c hc
        exact hcs c (by simp [Term.mentions, hc])

/-- **A2: extending a partial application** at a graph-regime site, when the head's telescope is
long enough (`htele`, a fact about the stored type: a special head's stored type is a `∀`
telescope at least as long as its arity, and SrcEval never over-applies one). -/
theorem apply_pap {h : IxCC.Src.Head} {ls : Levels} {args : List Slot} {X Y : V} {s : Slot}
    (hv : RelV M κ lpsOf S Ok (.pap h ls args) X) (hs : RelSlot M κ lpsOf S Ok s Y)
    {v : Nat} {A : V} {B : V → V} (hvz : v ≠ 0) (hX : X ∈ˢ piR v A B) (hY : Y ∈ˢ A)
    (htele : ∀ (φ : LevelParam → Nat) (k : KKey) (T : KExpr) (ρ σ : BVarIdx → V) (R : KExpr)
      (As : List V), HeadAt M κ lpsOf S h ls φ k T → Fits M.cval env φ ρ T As σ R →
      As.length = args.length → ∃ D Bk m, R = .forallE D Bk m) :
    ∃ (φ : LevelParam → Nat) (k : KKey) (T : KExpr) (As : List V) (ρ σ : BVarIdx → V) (R : KExpr),
      HeadAt M κ lpsOf S h ls φ k T ∧ RelSlots M κ lpsOf S Ok (args ++ [s]) (As ++ [Y]) ∧
      Fits M.cval env φ ρ T (As ++ [Y]) σ R ∧ X = As.foldl app (M.cval k φ) ∧
      app X Y = (As ++ [Y]).foldl app (M.cval k φ) := by
  cases hv with
  | @pap _ _ _ φ k T As ρ σ R hhead hslots hfits =>
    obtain ⟨D, Bk, m, rfl⟩ := htele φ k T ρ σ R As hhead hfits (relSlots_length hslots)
    obtain ⟨TT, hTT, hHm⟩ := head_mem M hhead ρ
    obtain ⟨RR, hRR, hXm⟩ := fits_app_mem hfits hTT hHm
    obtain ⟨DD, BB, hDD, _, _, hRe⟩ := den_pi.mp hRR
    subst hRe
    have hrm : regime φ m.pw ≠ 0 := by
      intro h0
      rw [h0] at hXm
      rw [eq_pt_of_mem_piR_zero hXm] at hX
      exact not_pt_mem_piR_pos hvz hX
    have hYd : Y ∈ˢ DD := piR_dom_unique hvz hrm hX hXm ▸ hY
    refine ⟨φ, k, T, As, ρ, push Y σ, Bk, hhead, relSlots_snoc hslots hs,
      fits_snoc hfits rfl hDD hYd, rfl, ?_⟩
    rw [List.foldl_append]
    rfl

end Rel

end IxCC.Grounding
