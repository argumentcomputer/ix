module

public import ConLeche.Model.Annot.Laws
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.BitClosed
public import ConLeche.Semantics.EnvFacts
import ConLeche.Verify.Denote
import ConLeche.Verify.Denote.VClosed

public section

/-!
# `EnvModelM` — the P-tier environment invariant (task #161, P4)

The install tier's target, per the P4 design note in DESIGN.md: the
denoteAnnot-free environment carrier (`EnvModel`) *contained*, plus the
fields the P bundles read.  (Batch 8 slimmed the containment from
`EnvModelUM` to `EnvModel` — the FINDING in `Annot/EnvModel.lean`: the
P fold stores `denoteMeta`-numeraled leaves and so can never supply the
denoteAnnot-currency fields, which the P surface never reads.)

**The laws the fields are stated over live in `Model/Annot/Laws.lean`**
since task #305 closing — `NatOps`, `DivMod`, `EqLaw`, `ReduceOps`, the
caps kit, the iota kit and the tower kit were in this file until then,
and were moved out (unchanged, docstrings included) so that the rules
tier's inputs can name them without importing the establishment
surface below.  This file keeps the structure, its namespace, the empty
model, and the `Nat`-op guard law the literal tier reads.

The deltas against the canonical fields, each a payoff of the fuel-free
reading:

* **existence, not uniqueness** — `defn_reads` is `AcvalDefnInst`
  (batch 4): a stored definition's or theorem's value *reads*, to the
  constant's own leaf.  The canonical `acval_defn` retreated to a
  uniqueness form because all-fuel existence is refutable
  (`envS2_defn_lam_refuted` — `denoteAnnot` fails on binders at small
  fuel); `denoteMeta` has no fuel, and a checked value is never out of
  fragment.
* **the stored types read, are graded, and are inhabited** —
  `type_reads`/`type_wellDenotedV`/`mem_type`, at the *uninstantiated* type
  over every ground assignment; `denotePInstLevels` (an equality)
  delivers every instantiated form, so no arity or fuel bookkeeping
  appears anywhere.
* **the leaves are bit-valid** — `acval_validV`, `acval_wellDenoted`'s
  `AnnotValid` companion; establishment at install is the P2 front
  door's own validation, transported by the claims.

The bundle-supplying layer below (`constTypeP_of` the worked example;
its siblings follow the same three-field read) is what the quarter
induction (`checkSoundP_of_inputs`) consumes — the structure exists so
that a `Nonempty (EnvModelM …)` carried through the declaration fold
makes the induction's hypotheses *facts*.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps projFnName RecRule)

universe w

variable (V : Type w) [SetTheory V]

/-- **The P-tier environment invariant, at one mode** (see the module
docstring). -/
structure EnvModelM (μ : CheckMode) (env : Env) where
  /-- the denoteAnnot-free environment carrier, contained (batch 8: the
  P fold stores `denoteMeta`-numeraled leaves, so it can never supply the
  denoteAnnot-currency fields `EnvModelUM` carries — and the P surface reads
  none of them) -/
  base2 : EnvModel V env
  /-- every leaf is bit-valid (`acval_wellDenoted`'s `AnnotValid` half) -/
  acval_validV : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotValid V ρ (base2.acval n ψ)
  /-- every stored type reads, at every ground assignment -/
  type_reads : ∀ c ∈ env.consts, ∀ ψ : Name → Nat,
    ∃ ta : AnnotTerm,
      denoteMeta base2.acval env ψ 0 c.toConstantVal.type = some ta
  /-- the stored types' readings are graded -/
  type_wellDenotedV : ∀ c ∈ env.consts, ∀ (ψ : Name → Nat) (ta : AnnotTerm),
    denoteMeta base2.acval env ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, WellDenotedV V ρ ta
  /-- stored constants inhabit their types' readings (task #175 S1:
  a projection table's constant type is the closed dummy `Sort 1`
  and its leaf is `Sort 0`, so the row holds of tables too — the
  W4c-era `isTowerEntry` guard is gone; that a table is not a term is
  `inferTypeCore`'s own rejection of a `.const` naming one) -/
  mem_type : ∀ c ∈ env.consts,
    ∀ (ψ : Name → Nat) (ta : AnnotTerm),
    denoteMeta base2.acval env ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V,
      interp V ρ (base2.acval c.name ψ) ∈ˢ interp V ρ ta
  /-- stored definition and theorem values read, to the constant's own
  leaf (existence — the fuel-free upgrade of `acval_defn`) -/
  defn_reads : AcvalDefnInst base2
  /-- the two `Nat`-literal head facts, at every assignment -/
  nat_heads : ∀ φ : Name → Nat, NatHeads base2 φ
  /-- the structural-`Nat` recurrence laws at every assignment (the
  literal tier's supplier; established at the operations' own installs
  from the recorded runs — `Interp/NatEqsP.lean`) -/
  nat_ops : ∀ φ : Name → Nat, NatOps base2 φ
  /-- the pin-certified WF operations' guarded clauses at every
  assignment (the literal tier's other supplier; established at the
  operations' own installs from the recorded certificate runs —
  `Interp/DivModCertP.lean`) -/
  div_mod : ∀ φ : Name → Nat, DivMod base2 φ
  /-- the pinned `Eq` spine's value and grading (an *environment law*,
  as `EnvS.eq_lawV` is: the `Eq` leaf is fixed by the basis install and
  by nothing else, so the supplier is the P basis install —
  `BasisStepPB`, routed.  Consumed by the WF operations' certificate
  frame) -/
  eq_law : EqLaw base2
  /-- the stored families' fired capability laws (`CapsOkV`'s mirror;
  an *environment law* for the same reason `eq_law` is — an
  η-capable family's leaf value is fixed by the inductive install and
  by nothing else, so the supplier is `IndStepPB`).  Consumed by the
  structure-η and unit-like rules' soundness
  (`Model/Rules/DefEqSound.lean`, through `RulesInputs.caps_ok`) -/
  caps_ok : CapsOk base2
  /-- the stored recursors' fired modeled-iota contracts (`RecRulesV`'s
  mirror; an *environment law* for the same reason `caps_ok` is — a
  recursor's rules are fixed by the inductive install and by nothing
  else, so the supplier is `IndStepPB`).  Consumed by the ι rule's
  soundness (`Model/Rules/IotaSound.lean`, through
  `RulesInputs.rec_rules`) -/
  rec_rules : ∀ φ : Name → Nat, RecRules base2 φ
  /-- every stored compiler-trust opaque is the identity on its
  element type (`EnvS.reduce_ops`'s mirror; an *environment law* for
  the same reason `eq_law` is — the opaque's leaf is fixed by its own
  install's identity certificate and by nothing else, so the supplier
  is `harvestOpaque`.  Consumed by the `ofReduce*` axiom branch) -/
  reduce_ops : ReduceOps base2
  /-- the stored tower-backed projection entries' typing and iota
  laws (task #175 wiring W5; an *environment law* for the same reason
  `rec_rules` is — a direct structure's entries are fixed by its
  install and by nothing else, so the supplier is the direct install
  step.  Consumed by the `.proj` rows' tower branches) -/
  tower_ok : ∀ φ : Name → Nat, TowerOk base2 φ

namespace EnvModelM

variable {V}
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The leaf bit-validity residue, read off the field. -/
theorem acvalValid (m : EnvModelM V μ env) : AcvalValid m.base2 :=
  m.acval_validV

/-- **The `const` residue, derived — the worked example of the
bundle-supplying layer.**  The three type fields at the composed
assignment `Level.substFn φ ks us`, carried to the instantiated form
by `denotePInstLevels` (an equality: no arity premise, no fuel). -/
theorem constType (m : EnvModelM V μ env) : ConstType m.base2 φ := by
  intro d n ci us hf _hnt hlen
  have hmem := ConLeche.Semantics.Env.find?_mem hf
  have hname := ConLeche.Semantics.Env.find?_name hf
  obtain ⟨ta, hta⟩ :=
    m.type_reads ci hmem (Level.substFn φ ci.toConstantVal.levelParams us)
  have hwf := m.base2.wf ci hmem
  -- the reading is closed, hence depth-free
  have hcl : ∀ k : Nat, ta.liftN 1 k = ta := fun k =>
    denoteMeta_closed m.base2.acval_erase m.base2.cval_closed
      hwf.1 hwf.2.2.2.1 hta 1 k
  have hdepth :
      denoteMeta m.base2.acval env
          (Level.substFn φ ci.toConstantVal.levelParams us) d
          ci.toConstantVal.type = some ta :=
    denoteMeta_depth_of_closed m.base2.acval_closed hwf.1 hcl hta d
  -- the instantiated type's reading, by the crossing
  have hcross :
      denoteMeta m.base2.acval env φ d
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us)
        = denoteMeta m.base2.acval env
            (Level.substFn φ ci.toConstantVal.levelParams us) d
            ci.toConstantVal.type :=
    denotePInstLevels m.base2 φ ci.toConstantVal.levelParams us d
      ci.toConstantVal.type
  refine ⟨ta, ?_, m.type_wellDenotedV ci hmem _ ta hta, ?_⟩
  · rw [hcross]; exact hdepth
  · have := m.mem_type ci hmem _ ta hta
    rwa [hname] at this

/-- **The bridge invariant, from the P invariant** (task #161 S7,
Wall C step (e)) — `EnvS.toEnvFacts`'s P-side twin, and the last thing
`EnvModelM.base` was for.  Every field is a projection:

| `EnvFacts` field | source |
|---|---|
| `cval`, `cval_closed`, `wf`, `proj_ok` | `base2`'s own |
| `val_params` | `acval_params`, erased |
| `ty_denotes` | `type_reads` through `denoteMeta_erase` |
| `defn_eq` | `defn_reads` through `denoteMeta_erase` (definitions only: a theorem is opaque to reduction, and the invariant keeps no equation for its value) |
| `rec_rhs_denotes`, `rec_params_le` | `rec_rules`' `RecRuleLaw`, whose first two components are exactly those two facts |
| `nat_op_guard` | `nat_ops`/`div_mod` through `natOpStored_inv` |

Nothing of the collapsed model is consulted, and the P lane's
`checkDeclR_ofEnvRE` runs on this. -/
def toEnvFacts {V : Type w} [SetTheory V] {μ : CheckMode}
    {env : Env} (m : EnvModelM V μ env) : ConLeche.Semantics.EnvFacts env where
  cval := m.base2.cvalE
  cval_closed := m.base2.cval_closed
  wf := m.base2.wf
  val_params := fun n ci hf φ₁ φ₂ hp =>
    congrArg AnnotTerm.erase (m.base2.acval_params n ci hf φ₁ φ₂ hp)
  ty_denotes := fun c hc ψ => by
    obtain ⟨ta, hta⟩ := m.type_reads c hc ψ
    exact ⟨ta.erase,
      denoteMeta_erase m.base2.acval_erase 0 c.toConstantVal.type hta⟩
  defn_eq := fun cv value hint hmem ψ =>
    denoteMeta_erase m.base2.acval_erase 0 value
      (m.defn_reads ψ cv value ⟨hint, hmem⟩)
  rec_rhs_denotes := fun n cv mI rP rules hf r hr hfire us ψ hlen => by
    obtain ⟨-, hus⟩ := m.rec_rules ψ n cv mI rP rules hf r hr hfire
    obtain ⟨Ra, hRa, -, -⟩ := hus us hlen
    exact ⟨Ra.erase, denoteMeta_erase m.base2.acval_erase 0 _ hRa⟩
  rec_params_le := fun n cv mI rP rules hf r hr hfire =>
    (m.rec_rules (fun _ => 0) n cv mI rP rules hf r hr hfire).1
  proj_ok := m.base2.proj_ok
  nat_op_guard := fun c hmem hst => by
    obtain ⟨cv, v, hh, hf⟩ := ConLeche.natOpStored_inv hst
    rcases hmem with hm | hm
    · exact (m.nat_ops (fun _ => 0) c hm cv v hh hf).1
    · exact (m.div_mod (fun _ => 0) c hm cv v hh hf).1

end EnvModelM

/-- The empty environment carries the P invariant (the fold's base
case): the core is the mode-indexed empty's projection, and every P
field is vacuous — no constants, guards false, and the empty leaf
`.const .empty [0]` is bit-valid because a constant leaf carries no
binder. -/
@[expose] noncomputable def EnvModelM.empty (V : Type w) [SetTheory V]
    (μ : CheckMode) : EnvModelM V μ Env.empty where
  base2 := EnvModel.empty
  acval_validV := fun _ _ _ => by
    show AnnotValid V _ (.const .empty [0])
    simp
  type_reads := fun c hc => nomatch hc
  type_wellDenotedV := fun c hc => nomatch hc
  mem_type := fun c hc => nomatch hc
  defn_reads := fun ψ cv value hmem => by
    obtain ⟨hint, hdt⟩ := hmem
    exact nomatch hdt
  nat_heads := fun φ hg => by
    rw [show ConLeche.natLitSupported Env.empty = false from rfl] at hg
    exact nomatch hg
  nat_ops := fun φ c _ cv v hint hf => by
    rw [show Env.empty.find? c = none from rfl] at hf
    exact nomatch hf
  div_mod := fun φ c _ cv v hint hf => by
    rw [show Env.empty.find? c = none from rfl] at hf
    exact nomatch hf
  eq_law := fun hf => by
    rw [show Env.empty.find? eqName = none from rfl] at hf
    exact nomatch hf
  caps_ok := by
    refine ⟨fun T cvT caps hf => ?_, fun T cvT caps hf => ?_⟩ <;>
      · rw [show Env.empty.find? T = none from rfl] at hf
        exact nomatch hf
  rec_rules := fun _ n _ _ _ _ hf => by
    rw [show Env.empty.find? n = none from rfl] at hf
    exact nomatch hf
  reduce_ops := fun c _ cv hf => by
    rw [show Env.empty.find? c = none from rfl] at hf
    exact nomatch hf
  tower_ok := fun _ T i entry hf => by
    have : Env.empty.findProj? T i = none := rfl
    rw [this] at hf
    exact nomatch hf

/-! ## The `Nat`-op guard law -/

section
variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The install fold's `Nat`-op invariant, in the form the literal
tier reads it** (task #161 de-gating item B3, harvest site 37 / list
entry P7).  `reduceNat` tests `natOpStored` — one `Env.find?` — where
it used to re-derive `natOpGuard` per literal hit; the guard is what
the leaf analysis below needs (`natLitSupported` for the numeral
shapes, the two `Bool` constructors for the comparison shapes), and it
is carried by `NatOps`/`DivMod`, whose statement is exactly "stored
as a `defnInfo` → guard ∧ the recurrences".  So the tier reads the
guard off the environment, and nothing about the shapes changes.
(from `Model/Steps/Nat.lean`, task #305 closing) -/
@[expose] def NatOpGuardLaw (env : Env) : Prop :=
  ∀ c, (c ∈ ConLeche.natOpNames ∨ c ∈ ConLeche.natDivModNames) →
    ConLeche.natOpStored env c = true → ConLeche.natOpGuard env c = true

/-- `EnvModelM` supplies it, from `nat_ops` and `div_mod`.
(from `Model/Steps/Nat.lean`, task #305 closing) -/
theorem natOpGuardLaw_of (mp : EnvModelM V μ env) : NatOpGuardLaw env := by
  intro c hmem hst
  obtain ⟨cv, v, hh, hf⟩ := ConLeche.natOpStored_inv hst
  rcases hmem with hm | hm
  · exact (mp.nat_ops (fun _ => 0) c hm cv v hh hf).1
  · exact (mp.div_mod (fun _ => 0) c hm cv v hh hf).1

end

end ConLeche.Model
