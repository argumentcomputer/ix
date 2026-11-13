import IxCCGrounding.WordCheck
import IxCCGrounding.SelRetype

/-!
# The word family's root theorem (`IxCCGrounding.WordRoot`, step W)

The widest family (#678's six fields: `Laws678` and `graded`, `rootSound_678AGp_of_check`) refuses
every program whose closure reaches a word entry, by its conjunct `noWord`. **The word family's check
`groundCheckW`** is the same check with `noWord` replaced by the decided word conjunct `word`
(`wordB`, `IxCCGrounding.WordCheck`): every other conjunct, `letWit` included, is `checkParts`' own,
so the two checks agree on every program without a word entry.

**`rootSound_678AGpW_of_check`**: `rootSound_678AGp_of_check`'s statement with `groundCheckW` for
`groundCheck`, the same laws and the same other hypotheses, the same conclusion. The chain is the
six-field family's (`rootSound_678AS` → `rootSound_678AG` → `_of_check` → over `selEnv`), each link
taking the word clause `WordFacts` in its checked facts (`GroundFactsW`) and F6w's meaning from it
(`wordFires_of_facts`): `rootSound_678ASW` → `rootSound_678AGW` → `rootSound_678AGW_of_check` →
`rootSound_678AGpW_of_check`. The landed links are untouched.

What the word family proves of a word: SrcEval's F6w returns the tower of `WordOp.eval`'s number on
words below their width's size, and the model's operation on the bridge's towers is that tower. So
adequacy has no boundary at `2^63` or any other number: the boundary is the object's, whose word
representation returns no value at or above it (a resource failure, never a wrong value).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

/-! ## The word family's check -/

/-- **The conjuncts of the word family's check**: `checkParts`, `noWord` replaced by `word`. -/
def checkPartsW (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : List (String × Bool) :=
  (checkParts p env κ lpsOf ann Sl).map fun nb =>
    if nb.1 = "noWord" then ("word", wordB p env κ lpsOf Sl) else nb

/-- **The word family's check.** -/
def groundCheckW (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  (checkPartsW p env κ lpsOf ann Sl).all (·.2)

section Check

variable {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat}
  {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}

/-- Every conjunct of the check but `noWord` holds where the word family's check does. -/
theorem sans_of_checkW (h : groundCheckW p env κ lpsOf ann Sl = true) :
    CheckSans p env κ lpsOf ann Sl := by
  intro name b hm hn
  apply List.all_eq_true.mp h (name, b)
  exact List.mem_map.mpr ⟨(name, b), hm, by simp [hn]⟩

/-- The word conjunct holds where the word family's check does. -/
theorem word_of_checkW (h : groundCheckW p env κ lpsOf ann Sl = true) :
    wordB p env κ lpsOf Sl = true := by
  have hm : ("word", wordB p env κ lpsOf Sl) ∈ checkPartsW p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("noWord", Sl.all (noWordB p)), by simp [checkParts, checkPartsWith],
      by simp⟩
  exact List.all_eq_true.mp h _ hm

/-- **The word family's check is sound**: every fact `GroundFacts` names, the word clause
`WordFacts` for `NoWord`. -/
theorem groundFactsW_of_check (h : groundCheckW p env κ lpsOf ann Sl = true) :
    GroundFactsW (WordFacts p env κ lpsOf (· ∈ Sl)) p env κ lpsOf ann (· ∈ Sl) :=
  groundFactsW_of_sans (sans_of_checkW h) (wordFacts_of_check (word_of_checkW h))

end Check

/-! ## The root theorem -/

section Root

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- `rootSound_678AS` over the word clause: F6w's meaning from `WordFacts` (`wordFires_of_facts`,
which reads `graded` and `proj_law`). -/
theorem rootSound_678ASW (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFactsW (WordFacts p env κ lpsOf (· ∈ Sl)) p env κ lpsOf ann (· ∈ Sl))
    (hC : CaseFactsRead p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  have hLN := lawsNoCanon_of_678 hL hLD
  rootSound_coreW hLN.core hG hR
    (allP (fundHyps_of_instW hLN.core (.inr hNC.recs) hG hT hI
      (caseFires_of_instW hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hG.natBasis hC hNC
        hU)
      (wordFires_of_facts hLN.core hL.proj_law hgr hG.natBasis hG.faith.words)))
    ⟨hR.ok, hroot⟩ hA hrun hrb hRT hO φ ρ X hX

/-- `rootSound_678AG` over the word clause: every site typed from `graded`. -/
theorem rootSound_678AGW (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFactsW (WordFacts p env κ lpsOf (· ∈ Sl)) p env κ lpsOf ann (· ∈ Sl))
    (hC : CaseFactsRead p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hH : HeadRegime p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678ASW hL hgr hG hC hNC hLD hI hU hroot hR
    (sitesOk_of_headRegime hL.defnValue hgr hH) hA hrun hrb hRT hO φ ρ X hX

/-- `rootSound_678AG_of_check` with the word family's check `groundCheckW` for `groundCheck`. -/
theorem rootSound_678AGW_of_check (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheckW p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p env κ lpsOf ann Sl = true)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  obtain ⟨hseeds, hI, hU⟩ := instFacts_of_check hinst
  exact rootSound_678AGW hL hgr (groundFactsW_of_check hchk)
    (caseFactsRead_of_sans (sans_of_checkW hchk)) (noCanonA_of_check hnc) (litDefs_of_check hld)
    hI hU (hseeds root (List.mem_singleton_self _)) (headRegimeS_of_sans (sans_of_checkW hchk) hhr)
    hR hA hrun hrb hRT hO φ ρ X hX

/-- **The word family's root theorem**: `rootSound_678AGp_of_check`'s statement, with the word
family's check `groundCheckW` (`noWord` replaced by the decided word facts) for `groundCheck`: every
check on `selEnv`, the conclusion for the reading. -/
theorem rootSound_678AGpW_of_check (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheckW p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hnc : noCanonAB p (selEnv p env κ Sl) κ Sl = true)
    (hld : litDefsB (selEnv p env κ Sl) = true)
    (hinst : instCheckB p (selEnv p env κ Sl) κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hR : RootFacts p (selEnv p env κ Sl) κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o)
    (hRT : ResultTag p (selEnv p env κ Sl) κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  have hS := selRetype_selEnv p env κ Sl
  obtain ⟨M', hc⟩ := model_selRetype M hL.defnValue hgr hS
  have hden := denotes_selRetype hS M.cval φ
  have h := rootSound_678AGW_of_check (M := M') (laws678_selRetype hL hS hc)
    (hc ▸ gradedLaw_selRetype hL.defnValue hgr hS) hchk hnc hld hinst hhr hR hA hrun hrb hRT hO
    φ ρ X (by rw [hc, hden]; exact hX)
  rw [hc, hden] at h
  exact h

end Root

end IxCC.Grounding
