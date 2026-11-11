import IxCCGrounding.Support

/-!
# What the fundamental lemma assumes (`IxCCGrounding.Hyps`)

Three kinds of hypothesis, kept apart because they are discharged differently:

* **Stored-shape and program facts** (`Faith`, `NatBasis`, in `IxCCGrounding.Syntax`): decided by
  the check (`IxCCGrounding.Check`) on the program and the kernel's reading.
* **`CaseFires`, per `case` constant**: F5's meaning; the generic `case` lemma derives it from a
  checked shape.
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
      HeadAt M κ lpsOf S (.cases c) ls φ (κ c) T → Fits M.cval env φ ρ T As σ R →
      As.length = np + 1 + ni + 1 + nmin → LastSiteOk (M.cval (κ c) φ) As →
      ∀ (Tm : V) (mv : Value) (j : Nat) (fields : List Slot),
        As[np + 1 + ni]? = some Tm → RelV M κ lpsOf S Ok mv Tm →
        p.selectRule ind np mv = some (j, fields) →
        ∃ (Mn : V) (Ys : List V), As[np + 1 + ni + 1 + j]? = some Mn ∧
          RelSlots M κ lpsOf S Ok fields Ys ∧
          As.foldl app (M.cval (κ c) φ) = Ys.foldl app Mn ∧ AppChain Mn Ys

/-- **Everything the fundamental lemma assumes.** -/
structure FundHyps (M : Model V env) (p : Program) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) (Ok : CId → Levels → Prop) : Prop where
  /-- the laws (δ, ι, level-parameter irrelevance, the projection law, the `Nat` accelerations) -/
  laws : Laws M
  /-- the `Nat` basis the literal reading uses is stored as the kernel's reading stores it -/
  natBasis : NatBasis env
  /-- the stored-shape and program facts -/
  faith : Faith p env κ lpsOf S
  /-- F5's meaning at every `case` constant of `S` -/
  cases : ∀ c r, S c → p.table.resolveOf c = some (.case r) → CaseFires M p κ lpsOf S Ok c
  /-- an `eqn` entry's function denotes the kernel term `e` its body corresponds to (the `eqn`
  lemma), and its body runs (typing) -/
  eqn : ∀ c thm body, S c → p.table.resolveOf c = some (.eqn thm body) → ∃ e : KExpr,
    (∀ φ ρ X, Denotes M.cval env φ ρ e X → M.cval (κ c) φ = X) ∧
    ∀ ls φ, Ok c ls → LvAt φ (lpsOf c) ls → Runs M κ Ok (lpsOf c) ls φ [] body e
  /-- **typing**: the stored value of a definition SrcEval unfolds by δ runs, at every instance
  `Ok` admits -/
  value : ∀ c ls lvls ty v cv val hint, S c → Ok c ls → p.table.resolveOf c = none →
    p.decl? c = some (.defn .defn .safe lvls ty v) →
    env.find? (κ c) = some (.defnInfo cv val hint) →
    ∀ φ, LvAt φ (lpsOf c) ls → Runs M κ Ok (lpsOf c) ls φ [] v val

end Sem

end IxCC.Grounding
