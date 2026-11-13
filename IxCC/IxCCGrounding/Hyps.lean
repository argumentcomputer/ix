import IxCCGrounding.Facts
import IxCCGrounding.Support

/-!
# What the fundamental lemma assumes (`IxCCGrounding.Hyps`)

Three kinds of hypothesis, kept apart because they are discharged differently:

* **Stored-shape and program facts** (`Faith`, `NatBasis`, in `IxCCGrounding.Syntax`): decided by
  the check (`IxCCGrounding.Check`) on the program and the kernel's reading.
* **`CaseFires`, per `case` constant**: F5's meaning; the generic `case` lemma derives it from a
  checked shape.
* **`WordFires`, at the word entries** (step W): F6w's meaning, derived from the checked word facts
  (`IxCCGrounding.WordFire`), vacuous where there is no word entry (`wordFires_of_noWord`). The
  faithfulness clauses are taken here at the word clause `True` because the word entries' facts
  reach the lemma through `words` instead: `True` drops nothing the lemma reads (no step reads
  `NoWord`), and `Faith` itself keeps `NoWord`.
* **The run terms run** (`FundHyps.value`, the `Runs` half of `FundHyps.eqn`): `IxCCGrounding.Runs`
  derives them from the checks and the typing hypothesis `SitesOk`, which
  `IxCCGrounding.Direct.Sites` derives in turn from typing at the sites the direct route refuses
  (`SitesOkRes`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **F5 at the `case` constant `c`**: whenever SrcEval's F5 selects rule `j` with field slots
`fields` for a major value related to the major argument's set, the key applied to the arguments
is the selected minor's set applied to sets related to the fields, through graph-regime sites.
Per inductive; `NatFire` proves it at `Nat.casesOn`. -/
def CaseFires (M : Model V env) (p : Program) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) (Ok : CId → Levels → Prop) (c : CId) : Prop :=
  ∀ (r : CId) (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId)
    (rules : List IxCC.Src.Rule) (ty : Term),
    p.table.resolveOf c = some (.case r) →
    p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
    ∀ (ls : Levels) (φ : LevelParam → Nat) (T : KExpr) (ρ σ : BVarIdx → V) (R : KExpr)
      (As : List V),
      HeadAt M p κ lpsOf S Ok (.cases c) ls φ (κ c) T → Fits M.cval env φ ρ T As σ R →
      As.length = np + 1 + ni + 1 + nmin → LastSiteOk (M.cval (κ c) φ) As →
      ∀ (Tm : V) (mv : Value) (j : Nat) (fields : List Slot),
        As[np + 1 + ni]? = some Tm → RelV M p κ lpsOf S Ok mv Tm →
        p.selectRule ind np mv = some (j, fields) →
        ∃ (Mn : V) (Ys : List V), As[np + 1 + ni + 1 + j]? = some Mn ∧
          RelSlots M p κ lpsOf S Ok fields Ys ∧
          As.foldl app (M.cval (κ c) φ) = Ys.foldl app Mn ∧ AppChain Mn Ys

/-- **F6w at the word entries of `S`** (step W): the stored constant is a head (stored without level
parameters, a binder for every argument), and whenever F6w returns a value on forced arguments
related to sets `As`, the key applied to `As` is related to it. `wordFires_of_facts`
(`IxCCGrounding.WordFire`) proves it from the checked word facts; in the families landed before
the word case it is vacuous (`wordFires_of_noWord`). -/
def WordFires (M : Model V env) (p : Program) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) (Ok : CId → Levels → Prop) : Prop :=
  ∀ c w op thm, S c → p.table.resolveOf c = some (.word w op thm) →
    (∃ ci : ConstantInfo .anon, env.find? (κ c) = some ci ∧ ci.toConstantVal.levelParams = [] ∧
      op.arity ≤ kPis ci.toConstantVal.type) ∧
    ∀ (φ : LevelParam → Nat) (vs : List Value) (As : List V) (v : Value),
      RelVs M p κ lpsOf S Ok vs As → p.wordValue w op vs = .ok v →
      RelV M p κ lpsOf S Ok v (As.foldl app (M.cval (κ c) φ))

/-- With no word entry in `S`, `WordFires` holds vacuously. -/
theorem wordFires_of_noWord {M : Model V env} {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop} (h : NoWord p S) :
    WordFires M p κ lpsOf S Ok :=
  fun c w op thm hS hr => absurd hr (h c w op thm hS)

/-- **Everything the fundamental lemma assumes.** -/
structure FundHyps (M : Model V env) (p : Program) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) (Ok : CId → Levels → Prop) : Prop where
  /-- the laws other than canonicity (δ, ι, level-parameter irrelevance, the projection law, the
  `Nat` accelerations) -/
  laws : LawsCore M
  /-- canonicity, where a `flat` or `noParams` recursor of `S` has a rule over a constructor with
  level parameters (`ctorImage_canon`, `ctorFields_canon`): the law, or no such constructor
  (`RecNoLevels`). The `case` entries' canonicity is inside `cases`. -/
  canon : CtorCanon M ∨ ∀ r, S r →
    (recClassB p env κ r = some .flat ∨ recClassB p env κ r = some .noParams) →
      RecNoLevels env (κ r)
  /-- the `Nat` basis the literal reading uses is stored as the kernel's reading stores it -/
  natBasis : NatBasis env
  /-- the stored-shape and program facts (the word clause apart: `words`) -/
  faith : FaithWith (RecFacts p env κ lpsOf S) True p env κ lpsOf S
  /-- F6w's meaning at every word entry of `S` (step W) -/
  words : WordFires M p κ lpsOf S Ok
  /-- F5's meaning at every `case` constant of `S` whose recursor is of kind `ordinary` (at kind
  `empty` SrcEval traps, so F5 is never asked: step E0) -/
  cases : ∀ c r, S c → p.table.resolveOf c = some (.case r) → p.table.recKindOf r = some .ordinary →
    CaseFires M p κ lpsOf S Ok c
  /-- an `eqn` entry's function denotes the kernel term `e` its body corresponds to (the `eqn`
  lemma), and its body runs (typing) -/
  eqn : ∀ c thm body, S c → p.table.resolveOf c = some (.eqn thm body) → ∃ e : KExpr,
    (∀ φ ρ X, Denotes M.cval env φ ρ e X → M.cval (κ c) φ = X) ∧
    ∀ ls φ, Ok c ls → LvAt φ (lpsOf c) ls → Runs M κ Ok (lpsOf c) ls φ [] [] body e
  /-- **typing**: the stored value of a definition SrcEval unfolds by δ runs, at every instance
  `Ok` admits -/
  value : ∀ c ls lvls ty v cv val hint, S c → Ok c ls → p.table.resolveOf c = none →
    p.decl? c = some (.defn .defn .safe lvls ty v) →
    env.find? (κ c) = some (.defnInfo cv val hint) →
    ∀ φ, LvAt φ (lpsOf c) ls → Runs M κ Ok (lpsOf c) ls φ [] [] v val

/-- **Everything the fundamental lemma assumes, with the `case` kinds read per instance** (step
Pc): `FundHyps` with the faithfulness clauses at any kinds (`True`: the lemma reads only their
arity), the kind read instead at each `Ok` instance (`kindAt`: `ordinary` at its levels, or
`empty`), and F5's meaning asked at every `case` constant with an `Ok` instance at which the kind
is `ordinary`. `FundHyps.toK` gives it from `FundHyps`; the Pc family gives it at `OkIn` from the
decided instance condition `pcInstB`, so that a `case` entry of kind `subsingleton` whose
condition fails at every instance is fired by F5 as SrcEval fires it there. -/
structure FundHypsK (M : Model V env) (p : Program) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) (Ok : CId → Levels → Prop) : Prop where
  laws : LawsCore M
  canon : CtorCanon M ∨ ∀ r, S r →
    (recClassB p env κ r = some .flat ∨ recClassB p env κ r = some .noParams) →
      RecNoLevels env (κ r)
  natBasis : NatBasis env
  faith : FaithWithK (RecFacts p env κ lpsOf S) True (fun _ => True) p env κ lpsOf S
  words : WordFires M p κ lpsOf S Ok
  /-- at every `Ok` instance of a `case` entry, its recursor's kind at the instance's levels is
  `ordinary` (SrcEval forces the major and fires F5), or its kind is `empty` (SrcEval traps) -/
  kindAt : ∀ c r ls, S c → p.table.resolveOf c = some (.case r) → Ok c ls →
    (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary ∨
      p.table.recKindOf r = some .empty
  cases : ∀ c r, S c → p.table.resolveOf c = some (.case r) →
    (∃ ls, Ok c ls ∧ (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary) →
    CaseFires M p κ lpsOf S Ok c
  eqn : ∀ c thm body, S c → p.table.resolveOf c = some (.eqn thm body) → ∃ e : KExpr,
    (∀ φ ρ X, Denotes M.cval env φ ρ e X → M.cval (κ c) φ = X) ∧
    ∀ ls φ, Ok c ls → LvAt φ (lpsOf c) ls → Runs M κ Ok (lpsOf c) ls φ [] [] body e
  value : ∀ c ls lvls ty v cv val hint, S c → Ok c ls → p.table.resolveOf c = none →
    p.decl? c = some (.defn .defn .safe lvls ty v) →
    env.find? (κ c) = some (.defnInfo cv val hint) →
    ∀ φ, LvAt φ (lpsOf c) ls → Runs M κ Ok (lpsOf c) ls φ [] [] v val

/-- `FundHyps` gives `FundHypsK`: the static kind (`ordinary` or `empty`) is the kind at every
level. -/
theorem FundHyps.toK {M : Model V env} {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {S : CId → Prop} {Ok : CId → Levels → Prop} (H : FundHyps M p κ lpsOf S Ok) :
    FundHypsK M p κ lpsOf S Ok where
  laws := H.laws
  canon := H.canon
  natBasis := H.natBasis
  faith := FaithWithK.monoK (fun _ _ => trivial) H.faith
  words := H.words
  kindAt := fun c r _ hS hr _ => by
    rcases (H.faith.caseRec c r hS hr).1 with hk | hk
    · exact .inl (by rw [hk]; rfl)
    · exact .inr hk
  cases := fun c r hS hr ⟨ls, _, hk⟩ => by
    rcases (H.faith.caseRec c r hS hr).1 with hk' | hk'
    · exact H.cases c r hS hr hk'
    · rw [hk'] at hk
      simp [IxCC.Src.RecKind.atLevels] at hk
  eqn := H.eqn
  value := H.value

end Sem

end IxCC.Grounding
