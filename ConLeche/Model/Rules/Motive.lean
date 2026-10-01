module

public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Rules.Rel
public import ConLeche.Model.Annot.BitLemmas

public section

/-!
# The soundness motives: derivation ⇒ P currency (task #305)

One motive per relation of the rules tier, in the currency of
`Model/Claims.lean` (`interp` equality, `WellDenotedV` grading,
membership), with the claims' own premises — the subject's frame
(`WScoped`, `looseBVarsBounded`, `LeavesBounded`), its `CtxOk`, its
reading, its grading where the claim takes it — and with THREE
deliberate strengthenings over the claim statements, all forced by the
recursive-structure rules (ruling 1):

1. **Existence form.**  `RedSem` and the two `InferSem`s conclude the
   reduct's / the type's reading (`∃ ea', denoteMeta … e' = some ea'`)
   instead of taking it as a premise.  A rule like `DefEq.redL` needs
   the middle term's reading to apply the continuation's motive, and
   nothing else can supply it: this is where the whole `*Reads` /
   `*Exists` totality family of `Model/Steps/Reads.lean` dissolves into
   the main statements.  The dual-success claims follow by
   `Option.some.inj`.
2. **The frame in the conclusion.**  `RedSem` and `InferSem` also
   conclude the reduct's / the type's frame and leaf inclusion, so the
   continuation's `CtxOk` is `CtxOk.of_subset` — the run lemmas
   `whnfCore_WScoped`/`inferTypeCore_fvarLeaves` become conjuncts of
   the semantic induction rather than a second induction.
3. **The grade splits the inference motive**: full grade establishes
   the subject's grading (`InferClaim`'s shape), io grade consumes it
   (`InferClaimIO`'s premise form) — the establishment/consumption
   asymmetry, verbatim.

The motives are `@[expose]` because the per-rule lemma files and the
master induction unfold them.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V]

/-- A subject's syntactic frame — the three scoping premises every
claim carries. -/
@[expose] def Frame (d : Nat) (e : Expr) : Prop :=
  Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded e

/-- A reading is graded under every satisfying valuation. -/
@[expose] def Graded (V : Type w) [SetTheory V] (Δa : List AnnotTerm)
    (ea : AnnotTerm) : Prop :=
  ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea

/-- No new free-variable leaf. -/
@[expose] def LeavesSub (e' e : Expr) : Prop :=
  ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves

/-- **`Red`'s motive**: a reduction of a framed, graded, readable
subject preserves the frame, reads, is graded, and has the same
interpretation. -/
@[expose] def RedSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (e e' : Expr) : Prop :=
  Frame d e →
  ∀ {Δa : List AnnotTerm} {ea : AnnotTerm},
    CtxOk m φ d Δa e →
    denoteMeta m.acval env φ d e = some ea →
    Graded V Δa ea →
    Frame d e' ∧ LeavesSub e' e ∧
      ∃ ea', denoteMeta m.acval env φ d e' = some ea' ∧
        Graded V Δa ea' ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea'

/-- **`DefEq`'s motive**: `DefEqClaim`'s conclusion under its premises. -/
@[expose] def DefEqSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (a b : Expr) : Prop :=
  Frame d a → Frame d b →
  ∀ {Δa : List AnnotTerm} {aa ba : AnnotTerm},
    CtxOk m φ d Δa a → CtxOk m φ d Δa b →
    denoteMeta m.acval env φ d a = some aa →
    denoteMeta m.acval env φ d b = some ba →
    Graded V Δa aa → Graded V Δa ba →
    ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **`Infer`'s motive at the full grade** — establishment: the
subject's grading is a conclusion. -/
@[expose] def InferSemFull {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (e t : Expr) : Prop :=
  Frame d e →
  ∀ {Δa : List AnnotTerm} {ea : AnnotTerm},
    CtxOk m φ d Δa e →
    denoteMeta m.acval env φ d e = some ea →
    Frame d t ∧ LeavesSub t e ∧
      ∃ ta, denoteMeta m.acval env φ d t = some ta ∧
        Graded V Δa ea ∧ Graded V Δa ta ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ∈ˢ interp V ρ ta

/-- **`Infer`'s motive at the io grade** — consumption: the subject's
grading is a premise (`InferClaimIO`'s premise form). -/
@[expose] def InferSemIO {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (e t : Expr) : Prop :=
  Frame d e →
  ∀ {Δa : List AnnotTerm} {ea : AnnotTerm},
    CtxOk m φ d Δa e →
    denoteMeta m.acval env φ d e = some ea →
    Graded V Δa ea →
    Frame d t ∧ LeavesSub t e ∧
      ∃ ta, denoteMeta m.acval env φ d t = some ta ∧
        Graded V Δa ta ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ∈ˢ interp V ρ ta

/-- The grade-dispatched inference motive. -/
@[expose] def InferSem {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Grade → Nat → Expr → Expr → Prop
  | .full, d, e, t => InferSemFull m φ d e t
  | .io, d, e, t => InferSemIO m φ d e t

/-- **`Certs`' motive**: the certified spine fits the telescope's
reading, substitution-peeling (`certs_telePA` / `certs_teleLic`,
`Model/Steps/IotaKit.lean:246`, `IotaGate.lean:123`).  At a licensed
walk the skipped slots are recovered from the spine's own grading and
the head's membership (`iota_slot_transfer`), which are therefore
premises exactly there. -/
@[expose] def CertsSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (lic : Bool) (ty : Expr) (args : List Expr) : Prop :=
  Frame d ty →
  ∀ {Δa : List AnnotTerm} {Ta fa : AnnotTerm} {vs : List AnnotTerm},
    CtxOk m φ d Δa ty →
    denoteMeta m.acval env φ d ty = some Ta →
    Graded V Δa Ta →
    (∀ x ∈ args, Frame d x ∧ CtxOk m φ d Δa x) →
    DenoteMetaSpine m.acval env φ d args vs →
    (∀ x ∈ vs, Graded V Δa x) →
    (lic = true →
      Graded V Δa (AnnotTerm.mkAppN fa vs) ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ fa ∈ˢ interp V ρ Ta) →
    ∃ resta : AnnotTerm,
      (∀ ρ : Nat → V, Sat V Δa ρ → TeleFitPA V ρ Ta vs resta) ∧
        Graded V Δa resta

/-- **`DefEqList`'s motive**: the walk's LENGTH, and pointwise `interp`
equality (`map_interp_of_defEqListFueled`, `Model/Steps/Stuck.lean:223`,
with `defEqListFueled_length`).  The length is a conclusion of its own
because the pointwise equality is only available once both lists have
been handed over as read spines — and a consumer (`Red.iota_sound`'s
`.nested` pin block) needs the length to BUILD the second spine. -/
@[expose] def DefEqListSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (as bs : List Expr) : Prop :=
  as.length = bs.length ∧
  ∀ {Δa : List AnnotTerm} {asa bsa : List AnnotTerm},
    (∀ x ∈ as, Frame d x ∧ CtxOk m φ d Δa x) →
    (∀ x ∈ bs, Frame d x ∧ CtxOk m φ d Δa x) →
    DenoteMetaSpine m.acval env φ d as asa →
    DenoteMetaSpine m.acval env φ d bs bsa →
    (∀ x ∈ asa, Graded V Δa x) →
    (∀ x ∈ bsa, Graded V Δa x) →
    ∀ ρ : Nat → V, Sat V Δa ρ →
      asa.map (interp V ρ) = bsa.map (interp V ρ)

/-- **`EtaProjCerts`' motive**: each certified field slot is a stored
projection function whose telescope the type's arguments and the
stuck side fit — `CertsSem` at every listed index. -/
@[expose] def EtaProjCertsSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (T : Name) (us' : List Level) (targs : List Expr) (b : Expr)
    (lpsT : List Name) (idxs : List Nat) : Prop :=
  ∀ i ∈ idxs, ∃ (cvp : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    env.find? (projFnName T i) = some (.recInfo cvp mI rP rules) ∧
    cvp.levelParams = lpsT ∧
    (cvp.type.stripPis (targs.length + 1)).isSome = true ∧
    CertsSem m φ d false (cvp.type.instantiateLevelParams cvp.levelParams us')
      (targs ++ [b])

end ConLeche.Model.Rules
