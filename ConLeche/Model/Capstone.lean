module

import ConLeche.Model.Install
public import ConLeche.Model.Tiers
import ConLeche.Model.NatStep

public section

/-!
# The P capstone's shape (task #161, P4 — frozen early, per the ruling)

Two deliverables, both statement-sensitive and frozen here before the
harvest layer builds toward them:

* **the business end, proved now**: `no_constant_of_Empty` — an
  environment carrying the P invariant stores no constant of type
  `Empty`.  The membership is `mem_type` (the `denoteMeta` reading, bit
  numerals), the reading of `.const emptyName []` is the leaf by the
  `denoteMeta` constant clause, and the leaf's `interp` value is the
  empty set by erasure injectivity at the constant constructor +
  `EnvS.empty_pinned` — the same three-move argument as
  `no_constant_of_Empty_2`, one currency over.
* **the final statement, frozen** (checked against the goal's letter —
  consistency of the checker on sort-annotated syntax, hypothesis
  minimal, the #16 precedent):

  `no_proof_of_Empty_pure : ∀ (V) [SetTheory V] {μ}, μ.verifiedChecks = true →
   ∀ {F ds env'}, checkDeclsPure μ (fueledOps μ F) pins ds = .ok env' →
   ∀ c ∈ env'.consts, c.toConstantVal.type = .const emptyName [] →
   False`

  Input-level hypotheses ONLY: the accepted run, the stored constant,
  its type — plus the validating mode, which is part of the goal's
  letter (the annotated checker IS the verified mode; `--trusted`
  ignores annotations by design).  No residue hypotheses: the
  intermediate, install-tier-conditional form is a *milestone shape*,
  never the close (the conditional-forms ruling).

**The semantic bill is empty** (task #161, ENDGAME A).  This file used
to carry `SemTierInputsP`, the ∀-environment form of the env-fixed
bundle's non-env-tier fields.  The four semantic tiers emptied it —
literal, caps, the proj/str install rows, iota — and its last field,
`accepted_reads`, is now `acceptedReads_of` (`Model/Tiers.lean`): a
syntactic totality walk over `inferBody`'s clauses, where every
`denoteMeta` failure mode is one of the front door's own acceptance
guards.  So the structure is deleted, and the harvest
layer proves: accepted stream ⇒ `Nonempty (EnvModelM …)` at the final
environment, with only the *install-tier* bundles as premises; this
file's `no_constant_of_Empty` then closes the capstone.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The Empty pin, at the core carrier -/

/-- The annotated `Empty` leaf is the pinned constant
(`acval_empty_pinned` at the denoteAnnot-free carrier).

**The pin is now a PREMISE** (task #161 S3): the core no longer
contains an `EnvS`, so `EnvS.empty_pinned` is not available from it.
The premise is stated in exactly the shape the census's §1.5 P-native
carrier field takes (`∀ ψ, ∃ u, cvalE emptyName ψ = emptyT u`), so S7
discharges it by projection when the field lands; until then the fold
layer supplies it from its v1 residue. -/
theorem acval_empty_pinnedC (m : EnvModel V env) {n : Name}
    (hpin : ∀ ψ : Name → Nat, ∃ u, m.cvalE n ψ = emptyT u)
    (ψ : Name → Nat) :
    ∃ u, m.acval n ψ = .const .empty [u] := by
  obtain ⟨u, hu⟩ := hpin ψ
  exact ⟨u, erase_eq_const (by rw [m.acval_erase, hu]; rfl)⟩

/-- …so its `interp` reading is the empty set, at every
assignment.  Stated at any name whose leaf is an `emptyT` pin (task
#181): `Empty`'s is `emptyT 1`, `False`'s is `emptyT 0`. -/
theorem interp_acval_emptyC (m : EnvModel V env) {n : Name}
    (hpin : ∀ ψ : Name → Nat, ∃ u, m.cvalE n ψ = emptyT u)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (m.acval n ψ) = SetTheory.empty := by
  obtain ⟨u, hu⟩ := acval_empty_pinnedC m hpin ψ
  rw [hu, interp_const]
  rfl

/-- **The empty-pin argument, at any pinned name** (task #181): an
environment carrying the P invariant stores no constant whose type is
a reserved constant whose direct pin is `emptyT u` — the membership is
`mem_type` at the `denoteMeta` reading, the reading of `.const n []` is
the leaf by the constant clause, and the leaf's `interp` value is the
empty set by erasure injectivity plus `basis_pinnedL`.  The `Empty` and
`False` capstones are its two instances. -/
theorem no_constant_of_emptyPin (mp : EnvModelM V μ env) {n : Name} {u : Nat}
    (hres : ConLeche.reservedBasisNames.contains n = true)
    (hpin : ∀ ψ : Name → Nat,
      ConLeche.Verify.pinnedStructT n ψ = some (emptyT u))
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const n []) : False := by
  obtain ⟨ta, hta0⟩ := mp.type_reads c hc (fun _ => 0)
  have hta := hta0
  rw [hty] at hta
  cases hf : env.find? n with
  | none => rw [denoteMeta, hf] at hta; exact nomatch hta
  | some ci =>
    by_cases hlen :
        ([] : List Level).length = ci.toConstantVal.levelParams.length
    · rw [denoteMeta_const hf hlen] at hta
      obtain rfl : ta = mp.base2.acval n
          (Level.substFn (fun _ => 0)
            ci.toConstantVal.levelParams []) :=
        (Option.some.inj hta).symm
      have hmem := mp.mem_type c hc (fun _ => 0) _ hta0
        (fun _ => (SetTheory.empty : V))
      rw [interp_acval_emptyC mp.base2 (fun ψ =>
        ⟨u, EnvModel.cvalE_pinned mp.base2 hres
          (by rw [hf]; rfl) ψ (hpin ψ)⟩)] at hmem
      exact not_mem_empty _ hmem
    · rw [denoteMeta, hf] at hta
      dsimp only at hta
      rw [if_neg hlen] at hta
      exact nomatch hta

/-- **The capstone's business end**: an environment carrying the P
invariant stores no constant of type `Empty` — the membership read
entirely at the validated-annotation tier (`mem_type` over
`denoteMeta`/`interp`). -/
theorem no_constant_of_Empty (mp : EnvModelM V μ env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False :=
  -- **the pin, discharged by the carrier itself** (task #161 S7):
  -- `Empty` is stored, so `basis_pinnedL` — the core's own field since
  -- S3 — gives the leaf its direct pin.  This is the S3 seal's
  -- prediction cashed: the premise dies with `EnvModelM.base`, it is
  -- not replaced.
  no_constant_of_emptyPin mp (u := 1) (by decide)
    (fun ψ => by simp +decide [ConLeche.Verify.pinnedStructT, ConLeche.Term.emptyT])
    c hc hty

/-- **The capstone's business end, about `False`** (task #181): an
environment carrying the P invariant stores no constant of type
`False` — the pinned `False` block's leaf is `emptyT 0`, the empty set
at `Prop`. -/
theorem no_constant_of_False (mp : EnvModelM V μ env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const falseName []) : False :=
  no_constant_of_emptyPin mp (u := 0) (by decide)
    (fun ψ => by simp +decide [ConLeche.Verify.pinnedStructT, ConLeche.Term.emptyT])
    c hc hty

/-! ## The remaining bill: none

**`SemTierInputsP` is gone.**  The structure named the env-fixed
bundle's non-env-tier fields in ∀-environment form, and the four
semantic tiers emptied it one by one — literal, caps, the proj/str
install rows and iota, each in the `Model/Steps/*` row the design
record names (that tier is itself gone since the task #305 closing;
what the soundness reads about the environment is now
`Rules.RulesInputs`, `Model/Rules/Inputs.lean`).  Its last field,
`accepted_reads`, is `acceptedReads_of` (`Model/Tiers.lean`), so the
bundle has nothing left to carry and
is **deleted** rather than left as an empty structure: an empty
hypothesis is still a hypothesis in every downstream signature, and
the milestone capstone's census is read off those signatures. -/

/-- **The rules tier's environment inputs, from the fold's
invariant**: seven fields are `EnvModelM` projections
(`RulesInputs.ofEnvModelM`, `Model/Rules/Inputs.lean`) and the two
literal rows are this file's own imports — `natSuccRow_of`/
`natOpRow_of` (`Model/NatStep.lean`), which stand on the numeral
transports and so cannot be projections down there.  Successor of
`Rules.RulesInputs.ofSem` (task #305 closing). -/
theorem Rules.RulesInputs.ofSem (mp : EnvModelM V μ env) (φ : Name → Nat) :
    Rules.RulesInputs V mp.base2 φ :=
  Rules.RulesInputs.ofEnvModelM mp (natSuccRow_of mp φ) (natOpRow_of mp φ)

end ConLeche.Model
