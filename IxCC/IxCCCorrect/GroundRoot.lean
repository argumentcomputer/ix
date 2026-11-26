import IxCCGrounding.PcProp

/-!
# The grounding root theorem at a canonical result (`IxCCCorrect.GroundRoot`)

The grounding library's root theorem (`IxCC.Grounding.rootSound_678AGpWPP_of_check`) reads the
result of SrcEval through `Src.readbackAll` and a per-result condition (`ResultTag`, "checked per
observed tag after the run"), and concludes an implication: *if* the root applied to its arguments
denotes `X`, the observation's term denotes `X`. A compiler pipeline has neither a run nor a model
at hand, so this module restates the theorem in the form the composition with the compiler needs:

* **the result is a canonical form** (`CanonAt`): a literal at `Nat`, a constructor value without
  fields whose constructor the program declares for the result enumeration without parameter or
  field. With the constructor known to belong to the enumeration, `ResultTag` is not needed: the
  enumeration's own stored facts (`EnumStored`, part of `RootFacts`) say which listed constructor it
  is. This is what a progress proof supplies (`IxCCCorrect.Shape1`, `ValOk.nat_inv` and
  `ValOk.enum_inv`), and what `NeverWrong` alone does not: see `IxCCCorrect.Compose`;
* **the application denotes** (`Grounded.app_denotes`, link G4 of the inventory): the root is stored
  without level parameters and a literal denotes by `NatBasis`, so `∃ X` holds outright;
* **one statement** (`Grounded.same`): in every model, the root applied to literals and the
  canonical form's term denote, and denote the same set.

`Grounded` packages the decided hypotheses of the Pc-Prop root theorem (the five checks on
`selEnv` and `RootFacts`); `IxCCCorrect.GroundCheck` decides it.

The proof of `rootCanon_coreWK` is `IxCC.Grounding.rootSound_coreWK`'s up to the readback; the
chain above it (`Grounded.canon_sound`) is the Pc-Prop chain (`rootSound_678ASWPP`,
`rootSound_678AGWPP`, `rootSound_678AGWPP_of_check`, `rootSound_678AGpWPP_of_check`) in one step.
No grounding module is edited.
-/

set_option autoImplicit false

namespace IxCC.Correct

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Result)
open IxCC.Grounding

universe w

/-! ## Canonical forms of a first-order result -/

/-- **A canonical form of a first-order result type**: a literal at `Nat`; at an enumeration `D`,
a constructor value without fields whose constructor the program declares for `D`, with no
parameter and no field. -/
def CanonAt (p : Program) : FoTy → Value → Prop
  | .nat, v => ∃ n : Nat, v = .lit n
  | .enum D, v => ∃ (c : CId) (ls : Levels) (ps : List Slot) (s : Bool) (lv i : Nat) (ty : Term),
      v = .con c ls ps [] ∧ p.decl? c = some (.ctor s lv D i 0 0 ty)

/-- The kernel term a canonical form names: the literal, or the constructor's constant. -/
def canonTerm (κ : CId → KKey) : Value → KExpr
  | .lit n => litE n
  | .con c _ _ _ => .const (κ c) []
  | _ => litE 0

/-! ## The arguments: literals -/

/-- `Nat` literals are first-order arguments at `Nat`, with the literals as their kernel terms. -/
theorem foArgs_nats (p : Program) (κ : CId → KKey) : ∀ ns : List Nat,
    FoArgs p κ (List.replicate ns.length FoTy.nat) (ns.map Value.lit)
      (ns.map fun n => (litE n : KExpr))
  | [] => FoArgs.nil
  | n :: ns => by
    simp only [List.length_cons, List.replicate_succ, List.map_cons]
    exact FoArgs.cons (FoVal.nat n) (foArgs_nats p κ ns)

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- Literals denote, one by one, where `Nat` and its constructors are stored. -/
theorem denotesList_lits (M : Model V env) {φ : LevelParam → Nat} (hF : NatFacts M φ)
    (ρ : BVarIdx → V) : ∀ ns : List Nat,
    DenotesList M.cval env φ ρ (ns.map fun n => (litE n : KExpr)) (ns.map (litSet M φ))
  | [] => .nil
  | n :: ns => by
    simp only [List.map_cons]
    exact .cons ((lit_den M hF ρ n _).mpr rfl) (denotesList_lits M hF ρ ns)

/-! ## The root theorem's core, at a canonical result -/

/-- **`rootSound_coreWK` at a canonical result**: its statement with `readbackAll`, `ResultTag` and
`FoObs` replaced by `CanonAt`, and the observation's term by `canonTerm`. The proof is
`rootSound_coreWK`'s up to the value relation of the result; a literal's set is the literal's, and
a constructor of the result enumeration is the listed one at its declared index (`EnumStored`'s
last clause, at a member of `Sl`, which the value relation gives). -/
theorem rootCanon_coreWK {M : Model V env} (hL : LawsCore M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {R Wd : Prop} {Kd : CId → Prop}
    (hG : GroundFactsWithK R Wd Kd p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {Ok' : CId → Levels → Prop} (hAllK : ∀ k, AllP M p κ lpsOf (· ∈ Sl) Ok' k)
    (hOkR : Ok' root [])
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hcan : CanonAt p res v) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ (canonTerm κ v) X := by
  have hN := hG.natBasis
  have hF0 := natFacts M hN φ
  have hAll := hAllK k
  obtain ⟨ci, hfr, hlr, htr⟩ := hR.stored
  -- δ on the root
  rw [IxCC.Src.run_eq] at hrun
  obtain ⟨f, hf, happ⟩ := Result.bind_eq_ok_iff.mp hrun
  obtain ⟨ci2, hf2, hlps⟩ := hG.faith.stored root hR.mem
  rw [hfr] at hf2
  cases hf2
  have hlv : LvAt φ (lpsOf root) [] := by rw [← hlps, hlr]; intro i q h; simp at h
  have hrelf := hAll.evalConst [] root f φ hf hR.mem hOkR hlv
  -- the arguments
  obtain ⟨F, Es, hFd, hEs, rfl⟩ := (den_mkAppN es).mp hX
  obtain rfl : F = M.cval (κ root) φ := (den_const0 hfr hlr).mp hFd
  have hargs : ∀ {ts : List FoTy} {xs : List Value} {es : List KExpr} {Es : List V},
      (∀ D, FoTy.enum D ∈ ts → FoTy.enum D ∈ args) → FoArgs p κ ts xs es →
      DenotesList M.cval env φ ρ es Es →
      RelSlots M p κ lpsOf (· ∈ Sl) Ok' (xs.map .val) Es ∧
        ∀ (E : BVarIdx → V), Fits M.cval env φ E
          (piTele (ts.map fun t => (t.kexpr κ, { pw := PropWhen.never })) (res.kexpr κ)) Es
          (pushAll Es E) (res.kexpr κ) := by
    intro ts xs es Es hsub hA hEs
    induction hA generalizing Es with
    | nil => cases hEs; exact ⟨.nil, fun E => by rw [pushAll_nil]; exact .nil⟩
    | @cons t ts x xs e es hv _ ih =>
      cases hEs with
      | @cons _ _ Y Ys hY hYs =>
      obtain ⟨ih1, ih2⟩ := ih (fun D h => hsub D (List.mem_cons_of_mem _ h)) hYs
      have hYrel : RelV M p κ lpsOf (· ∈ Sl) Ok' x Y ∧
          ∀ ρ' Z, Denotes M.cval env φ ρ' (t.kexpr κ) Z → Y ∈ˢ Z := by
        cases hv with
        | nat n =>
          rw [(lit_den M hF0 ρ n Y).mp hY]
          exact ⟨relV_lit_intro hN φ n, fun ρ' Z hZ => by
            rw [(hF0.natD ρ' Z).mp hZ]; exact lit_mem M hF0 n⟩
        | @enum D c i safe cs ty hd hc =>
          have hE := hR.enums D (Or.inl (hsub D (List.mem_cons_self ..)))
          obtain ⟨hrel, hden, hmem⟩ := enum_argWK (M := M) (Ok' := Ok') hG.faith hE hd hc φ
          rw [(hden ρ Y).mp hY]
          exact ⟨hrel, fun ρ' Z hZ => hmem ρ' Z hZ⟩
      refine ⟨.cons (.val hYrel.1) ih1, fun E => ?_⟩
      obtain ⟨Z, hZ⟩ : ∃ Z, Denotes M.cval env φ E (t.kexpr κ) Z := by
        cases t with
        | nat => exact ⟨_, (hF0.natD E _).mpr rfl⟩
        | enum D =>
          obtain ⟨_, _, _, _, ⟨ciD, hfD, hlD⟩, _⟩ := hR.enums D (Or.inl (hsub D (List.mem_cons_self ..)))
          exact ⟨_, (den_const0 hfD hlD).mpr rfl⟩
      have h2 := ih2 (push Y E)
      rw [← pushAll_cons] at h2
      exact .cons hZ (hYrel.2 E Z hZ) (by simpa using h2)
  obtain ⟨hrelEs, hfitEs⟩ := hargs (fun D h => h) hA hEs
  -- the chain of applications, at graph-regime sites
  obtain ⟨TT, hTT, hmem⟩ := mem_key M hfr φ ρ
  rw [htr] at hTT
  have hchain : AppChain (M.cval (κ root) φ) Es :=
    appChain_of_fits _ _ hTT hmem (hfitEs ρ) (by
      have := denotesList_length hEs
      have hl := foArgs_length hA
      simp; omega) (fun b hb => by
        simp only [List.mem_map] at hb
        obtain ⟨_, _, rfl⟩ := hb
        simp [regime])
  have hrelv := hAll.applyAll f (xs.map .val) v _ Es happ hrelf hrelEs hchain
  -- the canonical form
  cases res with
  | nat =>
    obtain ⟨w, rfl⟩ := hcan
    rw [relV_lit_eq hL hN φ hrelv]
    exact (lit_den M hF0 ρ w _).mpr rfl
  | enum D =>
    obtain ⟨c, ls, ps, s, lv, i, tyc, rfl, hdc⟩ := hcan
    have hE := hR.enums D (Or.inr rfl)
    obtain ⟨safe, ty, cs, hd, -, hctors, hback⟩ := hR.enums D (Or.inr rfl)
    generalize hXv : Es.foldl app (M.cval (κ root) φ) = Xv at hrelv ⊢
    cases hrelv with
    | @con _ _ _ _ ψ cvC np nf Ps Fs ρc σc Rc hSc _ hfc' hPl hFl _ hfs _ =>
    have hc : cs[i]? = some c := hback c hSc s lv i 0 0 tyc hdc
    obtain ⟨_, hden, _⟩ := enum_argWK (M := M) (Ok' := Ok') hG.faith hE hd hc φ
    obtain ⟨_, _, cvc, hfc, hlc, _⟩ := hctors i c hc
    obtain rfl := List.eq_nil_of_length_eq_zero (relVs_length hfs)
    have hnf : nf = 0 := by simpa using hFl.symm
    subst hnf
    rw [hfc] at hfc'
    simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfc'
    obtain ⟨rfl, rfl, -⟩ := hfc'
    obtain rfl := List.eq_nil_of_length_eq_zero hPl
    rw [List.nil_append, List.foldl_nil,
      hL.cval_params _ _ hfc ψ φ (by simp [ConstantInfo.toConstantVal, hlc])]
    exact (hden ρ _).mpr rfl

/-! ## The decided hypotheses, and the theorem over them -/

/-- **The decided hypotheses of the Pc-Prop root theorem** at a root: the family's check, the
canonicity-free fact, the literal definitions, the instance set and the per-spine typing, each on
`selEnv` of the reading and the closure `Sl`; and the root's facts (in `Sl`, `Ok` at no level,
stored without level parameters at the first-order type `args → res`, its enumerations stored).
Every field is a Boolean check's value or follows from one (`rootFacts_of_check`). -/
structure Grounded (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) (Inst : List (CId × Levels)) (root : CId)
    (args : List FoTy) (res : FoTy) : Prop where
  check : groundCheckWPP p (selEnv p env κ Sl) κ lpsOf ann Sl = true
  noCanon : noCanonAB p (selEnv p env κ Sl) κ Sl = true
  litDefs : litDefsB (selEnv p env κ Sl) = true
  inst : instCheckB p (selEnv p env κ Sl) κ lpsOf [root] Inst = true
  headRegime : headRegimeSB p (selEnv p env κ Sl) κ lpsOf ann Sl = true
  root : RootFacts p (selEnv p env κ Sl) κ ann (· ∈ Sl) root args res

variable {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
  {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {Inst : List (CId × Levels)} {root : CId}
  {args : List FoTy} {res : FoTy}

/-- **The Pc-Prop root theorem at a canonical result**, for the reading: in every model of `env`,
if SrcEval runs the root on first-order arguments to a canonical form of the result type, the root
applied to the arguments' terms denotes only what the canonical form's term denotes. -/
theorem Grounded.canon_sound (h : Grounded p env κ lpsOf ann Sl Inst root args res)
    (M : Model V env) {k : Nat} {xs : List Value} {es : List KExpr} {v : Value}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hcan : CanonAt p res v) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ (canonTerm κ v) X := by
  have hS := selRetype_selEnv p env κ Sl
  obtain ⟨M', hc⟩ := model_selRetype M hS
  have hden := denotes_selRetype hS M.cval φ
  have hwp := groundCheckWP_of_WPP h.check
  obtain ⟨hseeds, hI, hU⟩ := instFacts_of_check h.inst
  have hG := groundFactsWP_of_check hwp
  have hC := caseFactsReadP_of_checkWP hwp
  have hPU := punitPropFacts_of_checkWPP h.check
  have hNC := noCanonA_of_check h.noCanon
  have hLD := litDefs_of_check h.litDefs
  have hroot : (root, ([] : Levels)) ∈ Inst := hseeds root (List.mem_singleton_self _)
  have hH := headRegimeS_of_sansK (sansK_of_checkWP hwp) h.headRegime
  have hT := sitesOk_of_headRegime M'.defn_value M'.graded hH
  have hLN := lawsNoCanon_of_model M' hLD
  have hres := rootCanon_coreWK (M := M') hLN.core hG h.root
    (allPK (fundHypsK_of_instWPP hLN.core (.inr hNC.recs) hG hT hI hU
      (caseFires_of_instWP hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hG.natBasis hC
        hNC hU)
      (caseSubFires_of_instWPP hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hC hNC hPU)
      (wordFires_of_facts hLN.core M'.proj_law M'.graded hG.natBasis hG.faith.words)))
    ⟨h.root.ok, hroot⟩ hA hrun hcan φ ρ X (by rw [hc, hden]; exact hX)
  rw [hc, hden] at hres
  exact hres

/-- **The root applied to literals denotes** (link G4): the root is stored without level
parameters, and a literal denotes where `Nat` and its constructors are stored (`NatBasis`, a
conjunct of the check). -/
theorem Grounded.app_denotes {ns : List Nat}
    (h : Grounded p env κ lpsOf ann Sl Inst root (List.replicate ns.length FoTy.nat) res)
    (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ X, Denotes M.cval env φ ρ
      (Expr.mkAppN (.const (κ root) []) (ns.map fun n => (litE n : KExpr))) X := by
  have hS := selRetype_selEnv p env κ Sl
  obtain ⟨M', hc⟩ := model_selRetype M hS
  have hden := denotes_selRetype hS M.cval φ
  have hG := groundFactsWP_of_check (groundCheckWP_of_WPP h.check)
  have hF0 := natFacts M' hG.natBasis φ
  obtain ⟨ci, hfr, hlr, -⟩ := h.root.stored
  have hd : Denotes M'.cval (selEnv p env κ Sl) φ ρ
      (Expr.mkAppN (.const (κ root) []) (ns.map fun n => (litE n : KExpr)))
      ((ns.map (litSet M' φ)).foldl app (M'.cval (κ root) φ)) :=
    (den_mkAppN _).mpr ⟨_, _, (den_const0 hfr hlr).mpr rfl, denotesList_lits M' hF0 ρ ns, rfl⟩
  rw [hc, hden] at hd
  exact ⟨_, hd⟩

/-- **The root on literals and its canonical result denote the same set**, in every model of the
reading, at every level assignment and variable environment: the existence form the target
statement `SameDenotation` asks for. -/
theorem Grounded.same {ns : List Nat}
    (h : Grounded p env κ lpsOf ann Sl Inst root (List.replicate ns.length FoTy.nat) res)
    (M : Model V env) {k : Nat} {v : Value}
    (hrun : IxCC.Src.run p k root (ns.map Value.lit) = .ok v) (hcan : CanonAt p res v)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ X, Denotes M.cval env φ ρ
        (Expr.mkAppN (.const (κ root) []) (ns.map fun n => (litE n : KExpr))) X ∧
      Denotes M.cval env φ ρ (canonTerm κ v) X := by
  obtain ⟨X, hX⟩ := h.app_denotes M φ ρ
  exact ⟨X, hX, h.canon_sound M (foArgs_nats p κ ns) hrun hcan φ ρ X hX⟩

end Sem

end IxCC.Correct
