import IxCCGrounding.Root
import IxCCGrounding.CaseLevels

/-!
# The root theorem at `case` entries over level-polymorphic families (`IxCCGrounding.RootInst`)

`rootSound_678` (the canonicity-free family over #678's fields) asks every `case` entry's family to
have no level parameter (`NoCanon`). `rootSound_678A` drops that for `case` entries (`NoCanonA`:
their rules blind) and asks instead a verified instance set (`InstClosed`, `InstUniform`, the root
in it): the fundamental lemma runs at `Ok := OkIn p ann Inst`, and F5 at such an entry is
`caseFires_of_agree` (`IxCCGrounding.CaseLevels`). Its conclusion is `rootSound_678`'s word for word.

**Where a `let` goes.** The instance walk, and `InstClosed`, read `evalConsts`, which reads a `let`'s
value wherever the `let` is relevant (dead or not) and its body. That covers what the theorem uses:
`Runs.const` asks `Ok` at a subset of `evalConsts` (nothing of a dead `let`'s value), so the walk and
`instCheckB` read every position SrcEval evaluates, and stay fail-closed.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- **The run terms run at `OkIn`**, over any recursor and word clauses and any `case` kinds (steps
W, Pc). -/
theorem runs_of_sitesInWK (hL : LawsCore M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop} {Inst : List (CId × Levels)} {R Wd : Prop}
    {Kd : CId → Prop} (hG : GroundFactsWithK R Wd Kd p env κ lpsOf ann S)
    (hT : SitesOk M p κ lpsOf ann S) (hI : InstClosed p Inst)
    {c : CId} {ls : Levels} {t : Term} {e : KExpr} (hS : S c) (hOk : OkIn p ann Inst c ls)
    (hrp : RunPair p env κ c t e) {φ : LevelParam → Nat} (hlv : LvAt φ (lpsOf c) ls) :
    Runs M κ (OkIn p ann Inst) (lpsOf c) ls φ [] [] t e := by
  have hcorr : TermCorrS κ (lpsOf c) [] t e := by
    cases hrp with
    | value hr hd hf => exact hG.values c _ _ _ _ _ _ hS hr hd hf
    | eqn hr hsh => exact (hG.eqns c _ _ hS hr).2 _ hsh
  have hden : DenotesIn M φ [] e := by
    intro ρ _
    cases hrp with
    | value _ _ hf => exact ⟨_, hL.defn_value _ _ _ (find_mem hf) φ ρ⟩
    | eqn _ hsh => exact ⟨_, eqn_den M hsh φ ρ⟩
  have hterm : t ∈ runTerms p c := by
    cases hrp with
    | value hr hd _ => simp [runTerms, hr, hd]
    | eqn hr _ => simp [runTerms, hr]
  exact runs_of_corr hcorr hden (hT c ls t e hS hOk.1 hrp φ hlv)
    (fun d us h => ⟨hG.okClosed c ls hS hOk.1 t hterm d us h,
      hI c ls hOk.2 t (List.mem_append_left _ hterm) d us h⟩) (hG.wits c t e hS hrp)

/-- **The run terms run at `OkIn`**: `runs_of_sites`, each constant a run term evaluates `Ok` by
`okClosed` and in `Inst` by `InstClosed`; over any word clause (step W; `runs_of_sitesIn` at the
landed one). -/
theorem runs_of_sitesInW (hL : LawsCore M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop} {Inst : List (CId × Levels)} {Wd : Prop}
    (hG : GroundFactsW Wd p env κ lpsOf ann S) (hT : SitesOk M p κ lpsOf ann S) (hI : InstClosed p Inst)
    {c : CId} {ls : Levels} {t : Term} {e : KExpr} (hS : S c) (hOk : OkIn p ann Inst c ls)
    (hrp : RunPair p env κ c t e) {φ : LevelParam → Nat} (hlv : LvAt φ (lpsOf c) ls) :
    Runs M κ (OkIn p ann Inst) (lpsOf c) ls φ [] [] t e :=
  runs_of_sitesInWK hL hG hT hI hS hOk hrp hlv

/-- **The run terms run at `OkIn`**: `runs_of_sites`, each constant a run term evaluates `Ok` by
`okClosed` and in `Inst` by `InstClosed`. -/
theorem runs_of_sitesIn (hL : LawsCore M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop} {Inst : List (CId × Levels)}
    (hG : GroundFacts p env κ lpsOf ann S) (hT : SitesOk M p κ lpsOf ann S) (hI : InstClosed p Inst)
    {c : CId} {ls : Levels} {t : Term} {e : KExpr} (hS : S c) (hOk : OkIn p ann Inst c ls)
    (hrp : RunPair p env κ c t e) {φ : LevelParam → Nat} (hlv : LvAt φ (lpsOf c) ls) :
    Runs M κ (OkIn p ann Inst) (lpsOf c) ls φ [] [] t e :=
  runs_of_sitesInW hL hG hT hI hS hOk hrp hlv

/-- **The fundamental lemma's hypotheses at `OkIn`, over a word clause** (step W): F6w's meaning
`WordFires` given. -/
theorem fundHyps_of_instW (hL : LawsCore M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop}
    {Inst : List (CId × Levels)} {Wd : Prop}
    (hcanon : CtorCanon M ∨ ∀ r, S r →
      (recClassB p env κ r = some .flat ∨ recClassB p env κ r = some .noParams) →
        RecNoLevels env (κ r))
    (hG : GroundFactsW Wd p env κ lpsOf ann S) (hT : SitesOk M p κ lpsOf ann S)
    (hI : InstClosed p Inst)
    (hcases : ∀ c r, S c → p.table.resolveOf c = some (.case r) →
      p.table.recKindOf r = some .ordinary → CaseFires M p κ lpsOf S (OkIn p ann Inst) c)
    (hW : WordFires M p κ lpsOf S (OkIn p ann Inst)) :
    FundHyps M p κ lpsOf S (OkIn p ann Inst) where
  laws := hL
  canon := hcanon
  natBasis := hG.natBasis
  faith := hG.faith.monoW fun _ => trivial
  words := hW
  cases := hcases
  eqn := fun c thm body hS hr => by
    obtain ⟨⟨d, hsh⟩, _⟩ := hG.eqns c thm body hS hr
    exact ⟨d.body, fun φ ρ X hX => Denotes_functional (eqn_den M hsh φ ρ) hX,
      fun ls φ hOk hlv => runs_of_sitesInW hL hG hT hI hS hOk (.eqn hr hsh) hlv⟩
  value := fun c ls _ _ _ _ _ _ hS hOk hr hd hf φ hlv =>
    runs_of_sitesInW hL hG hT hI hS hOk (.value hr hd hf) hlv

/-- **The fundamental lemma's hypotheses at `OkIn`** (as `fundHyps_of_core`). -/
theorem fundHyps_of_inst (hL : LawsCore M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop}
    {Inst : List (CId × Levels)}
    (hcanon : CtorCanon M ∨ ∀ r, S r →
      (recClassB p env κ r = some .flat ∨ recClassB p env κ r = some .noParams) →
        RecNoLevels env (κ r))
    (hG : GroundFacts p env κ lpsOf ann S) (hT : SitesOk M p κ lpsOf ann S) (hI : InstClosed p Inst)
    (hcases : ∀ c r, S c → p.table.resolveOf c = some (.case r) →
      p.table.recKindOf r = some .ordinary → CaseFires M p κ lpsOf S (OkIn p ann Inst) c) :
    FundHyps M p κ lpsOf S (OkIn p ann Inst) :=
  fundHyps_of_instW hL hcanon hG hT hI hcases (wordFires_of_noWord hG.faith.words)

/-- **The root theorem over #678's fields, at `case` entries over level-polymorphic families**:
`rootSound_678` with `NoCanonA` for `NoCanon`, the `case` shapes the check reads
(`CaseFactsRead`, which gives `CaseFacts`), and a verified instance set (closed, uniform, the root in
it at no level). Its conclusion is `rootSound_678`'s word for word. The instance walk reads a relevant
`let`'s value, dead or not (`evalConsts`), a superset of what `Runs.const` asks. -/
theorem rootSound_678A (hL : Laws678 M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFactsRead p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  have hLN := lawsNoCanon_of_678 hL hLD
  rootSound_core hLN.core hG hR
    (allP (fundHyps_of_inst hLN.core (.inr hNC.recs) hG (sitesOk_of_res hLN.core hG hT) hI
      (caseFires_of_inst hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hG.natBasis hC hNC
        hU)))
    ⟨hR.ok, hroot⟩ hA hrun hrb hRT hO φ ρ X hX

/-- **The same from the Boolean checks**: `groundCheck`, `noCanonAB`, `litDefsB`, `instCheckB` with
the root as its seed, and the root's facts. -/
theorem rootSound_678A_of_check (hL : Laws678 M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  obtain ⟨hseeds, hI, hU⟩ := instFacts_of_check hinst
  exact rootSound_678A hL (groundFacts_of_check hchk) (caseFactsRead_of_check hchk)
    (noCanonA_of_check hnc) (litDefs_of_check hld) hI hU (hseeds root (List.mem_singleton_self _))
    hR hT hA hrun hrb hRT hO φ ρ X hX

end IxCC.Grounding
