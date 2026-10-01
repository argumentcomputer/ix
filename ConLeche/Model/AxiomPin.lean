module

import ConLeche.Semantics.DeclRun
public import ConLeche.Model.AxiomMem

public section

/-!
# The pin tier, at the validated-annotation currency (task #161,
ENDGAME A part 2)

`DeclAxiomR`'s four branches at the P invariant.  Two of them land
here; the other two are blocked on one named fact, and the block is
recorded rather than papered over.

## What a branch owes

`harvestAxiom` (`Interp/HarvestP.lean`) is the wrapper: the *type*
side is harvested from `ConstantValR`'s own run (`accepted_reads` is a
theorem since part 1, so nothing is routed), and what the branch must
supply is the leaf `A` with

* `hAerase`/`hAclosed`/`hAparams` — syntactic, from the branch key and
  the `EnvModel` fields;
* `hAok`/`hAvalid` — free at a `BConst` or `acval` leaf (`WellDenoted`'s
  and `AnnotValid`'s `.const`/`.prf` clauses are `True`, and an
  `acval` leaf carries both as invariant fields);
* `hmemA` — **the semantic content**: `interp` of the leaf inhabits
  `interp` of the *stored* type's `denoteMeta` reading.

## THE WALL, named: the stored type's reading is not the pin's

`hmemA` speaks about the reading of `type'`, the *stored* annotated
type.  Every branch key knows the type only through `matchesPin`,
which compares `erasePw` — so the pin fixes the stored
type **up to binder names and binder `pw` data**.

At v1 that costs nothing: `denote` reads neither, so
`denote_matchesPin` (`Verify/Denote/Inst.lean:422`) turns a pin hit
into an equality of denotations and every consumer computes on the
pin.  **At the P currency the analogue is FALSE**, and not marginally:
`denoteMeta`'s binder clauses read `pwBit φ mb.pw`, and `erasePw`
normalizes every datum to `.never`, whose bit is `1`.  So
`denoteMeta (e.erasePw) = denoteMeta e` fails at the very first Prop-codomain
binder, and with it any `denoteP_erasePw`/`denoteP_pinEq`/
`denoteP_matchesPin` chain stated the v1 way.  This is the erasePw
RULING's own point 2, met: the P tier must take the bits from the
front door's recorded run, never from the match verdict.

Concretely, what each remaining branch needs is:

> **`pwBitsAgree`**: at `μ.verifiedChecks`, for each binder of the stored
> type, `pwBit φ` of the stored datum equals `pwBit φ` of the pin's
> generated datum.

and the route is fixed by the ruling: `ConstantValR`'s run conjunct
(H1) gives `inferTypeCore μ env F 0 type' = .ok stype`; inverting it
through `inferTypeCore_forall_inv` once per binder yields the
validation conjunct `Level.zeronessOf v = mb.pw`, hence
(`pwBit_zeronessOf`) `pwBit φ mb.pw = 0 ↔ Level.eval φ v = 0`;
the pin's datum is that same zero-ness *by construction*, so the two
bits agree **once `Level.eval φ v` is known**.

And that last step is the content that is not yet in the tree: `v` is
`ensureSort` of the inferred type of the *opened body*, so knowing it
means executing the checker's inference symbolically along the pinned
telescope (for `propext`: that `a = b` infers to `Prop`, from the
stored `Eq`'s own pinned type).  The telescope collapse makes it one
fact per pin rather than one per binder — `imax x y = 0 ↔ y = 0`, so
every binder of a chain carries the innermost codomain's bit — but it
is one genuine symbolic-inference lemma per pinned family.

That lemma is `AxiomBitsP`'s, and the two standard axioms' memberships
are `AxiomMemP`'s, so `axiomStd` below closes the branch that record
named.  Read the ENDGAME C seal for what the memberships actually cost:
the *companions'* bits are not reachable by any bit lemma, and two of
the three obstructions that follow from that were removed
(`pi_sort_bit_ne_zero`, the vacuous minor) rather than assumed.

## THE SECOND WALL: `ofReduce*` needs a `ReduceOps` field

`ofReduceNat`/`ofReduceBool` are **not** blocked on their bits.  Their
bits are the easy half: the pin's innermost body is
`Eq.{1} E (op a) b`, an `Eq`-spine over the *nose-pinned* `Eq`
(`ofReduceAxOk`'s own first conjunct), so `inferTypeCore_eqSpineS`
applies verbatim and `propext_bits`'s three moves transpose
unchanged — all three binders carry bit `0`.  (The ENDGAME B seal
predicted "their move 2 goes through the stored `Nat`/`Bool` families";
it does not — the codomain is the `Eq`, and `Nat`/`Bool` appear only as
the spine's *type* argument, which `inferTypeCore_eqSpineS` never
looks at.)

The block is the **membership**, and it is an invariant gap.  With all
three bits `0` the reading's products are truth values, the witness is
forced to `pt`, and the innermost obligation is

> for every `a`, `b` in the element type, `eqv (op a) b` inhabited must
> force `eqv a b` inhabited — that is, `op a = a`.

That is exactly `EnvS.reduce_ops` (`ReduceOpsV`, `EnvS.lean:138`): *the
trusted operation is the identity on its element type*.  The field
exists, at the **v1 currency** — `interp`, `cval` — and `EnvModelM` has
no mirror.  Nor can one be derived: the transfer would be an erasure
factoring of `interp` through `interp`, refuted at exactly the λ-nodes
the operation's leaf is made of (the literal-tier seal II finding 1,
the same refutation that makes `eq_law` a field rather than a
theorem).

**STOP-AND-NAME**: `ofReduceNat`/`ofReduceBool` are blocked on a
`ReduceOps` field of `EnvModelM` — `ReduceOpsV`'s mirror at `interp`
and `acval` — established wherever `reduce_ops` is, and on nothing
else.  This is the same species as ENDGAME B's `rec_rules` wall and as
`eq_law`/`caps_ok`'s own existence: an environment law whose only
supplier is the install that fixes the leaf.  Recorded rather than
assumed; a premise for it would be a conditional form, and
`axiomStepPB_of` is therefore **not stated**.

## What lands here

* **the tolerated skip** — `axiomSkip`: the environment does not
  move, so the P invariant is the one already held;
* **`Lean.trustCompiler`** — `axiomTrustCompiler`: the one pinned
  axiom whose type is a **bare constant**.  `.const` carries no binder
  and therefore no datum, so `erasePw`'s forgiveness is empty on it
  and the pin fixes `type' = .const trueName []` **on the nose**
  (`erasePw_const_invS`; its `eraseNames` twin went with the names,
  task #205).  The wall above
  simply is not there, and the branch goes through: the leaf is the
  stored `True.intro`'s annotated valuation and `hmemA` is
  `EnvModelM.mem_type` at that constant, both readings being the same
  `acval trueName ψ`.

That is also why this branch was landed first: it exercises the whole
`harvestAxiom` bill end to end — extension, agreement, the four
syntactic leaf facts and the membership — so the remaining branches
inherit tested scaffolding;
* **the two standard axioms** — `axiomStd`, both halves, on
  `AxiomBitsP`'s bits and `AxiomMemP`'s memberships.

Three of `DeclAxiomR`'s four branches, then.  The fourth is the second
WALL above.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-! ## The tolerated skip -/

/-- **The tolerated-axiom skip.**  `DeclAxiomR`'s fourth branch stores
nothing (`env₂ = env`), so there is no leaf, no extension and no
crossing: the P invariant at the successor environment *is* the one
held at the prefix. -/
theorem axiomSkip (mp : EnvModelM V μ env) :
    Nonempty (EnvModelM V μ env) := ⟨mp⟩

/-! ## `Lean.trustCompiler` -/

/-- **The `trustCompiler` branch, discharged.**

The pin fixes the axiom's type to the stored `True` *on the nose* —
`ConstantVal.matchesPin` compares through `erasePw`, and
neither erasure moves a `.const` — so this is the one pinned axiom
whose `denoteMeta` reading is computable from the pin alone (see the
module docstring's WALL).  The leaf is the stored `True.intro`'s
annotated valuation, and the membership is that constant's own
`mem_type`, whose type reads to the same `acval trueName ψ` the
axiom's does. -/
theorem axiomTrustCompiler (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValRun μ F env cv type')
    (hname : cv.name = ConLeche.trustCompilerName)
    (hok : ConLeche.trustCompilerOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    Nonempty (EnvModelM V μ
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩) := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  -- the guard's two pin hits, unpacked exactly as `trustCompilerKeyS`
  -- unpacks them
  have hokc := hok
  simp only [ConLeche.trustCompilerOk, Bool.and_eq_true] at hokc
  obtain ⟨⟨hT, hTi⟩, hA⟩ := hokc
  cases hfT : env.find? ConLeche.trueName with
  | none => rw [hfT] at hT; exact nomatch hT
  | some ciT =>
  cases hfTi : env.find? ConLeche.trueIntroName with
  | none => rw [hfTi] at hTi; exact nomatch hTi
  | some ciTi =>
  rw [hfT] at hT
  rw [hfTi] at hTi
  have hlpT : ciT.toConstantVal.levelParams = [] := by
    cases ciT with
    | indInfo cvT caps =>
      simp only [ConstantVal.matchesPin, Bool.and_eq_true,
        decide_eq_true_eq] at hT
      exact hT.1.2
    | _ => exact nomatch hT
  obtain ⟨hlpTi, htyTi⟩ : ciTi.toConstantVal.levelParams = [] ∧
      ciTi.toConstantVal.type = .const ConLeche.trueName [] := by
    cases ciTi with
    | ctorInfo cvTi nP nF =>
      match nP, nF, hTi with
      | 0, 0, hTi =>
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq] at hTi
        exact ⟨hTi.1.2, erasePw_const_invS hTi.2⟩
    | _ => exact nomatch hTi
  -- **the pin bites on the nose**: a `.const` has no binder, so
  -- `erasePw` forgives nothing here
  have htyA : type' = .const ConLeche.trueName [] := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hA
    exact erasePw_const_invS hA.2
  have hnameTi : ciTi.name = ConLeche.trueIntroName := Env.find?_name hfTi
  -- the leaf: the stored `True.intro`'s *annotated* valuation
  refine harvestAxiom (V := V) hμ mp hcv
    (A := fun ψ => mp.base2.acval ConLeche.trueIntroName ψ)
    (fun ψ => mp.base2.cval_closedL _ ψ) ?_ ?_ ?_ ?_ ?_
    -- `trustCompiler` is not a compiler-trust *operation*: the pin
    -- fixes the name, and the two operations are installed as opaques
    (by rw [hname]; decide)
  · -- `hAclosed`
    exact fun ψ k => mp.base2.acval_closed _ ψ k
  · -- `hAparams`: `True.intro` is level-monomorphic, so the premise is
    -- vacuous
    intro ψ₁ ψ₂ _
    exact mp.base2.acval_params _ ciTi hfTi ψ₁ ψ₂ (by
      rw [hlpTi]; intro p hp; exact nomatch hp)
  · exact fun ψ ρ => mp.base2.acval_wellDenoted _ ψ ρ
  · exact fun ψ ρ => mp.acval_validV _ ψ ρ
  · -- `hmemA`: the axiom's type and `True.intro`'s stored type are the
    -- *same* bare constant, so they have the same reading, and the
    -- membership is that constant's own `mem_type`
    intro ψ ta hta ρ
    rw [htyA, denoteMeta_levelless_const hfT hlpT] at hta
    obtain rfl : ta = mp.base2.acval ConLeche.trueName ψ :=
      (Option.some.inj hta).symm
    have hmem := mp.mem_type ciTi (Env.find?_mem hfTi) ψ
      (mp.base2.acval ConLeche.trueName ψ)
      (by rw [htyTi]; exact denoteMeta_levelless_const hfT hlpT) ρ
    rwa [hnameTi] at hmem

/-! ## The two standard axioms

`DeclAxiomR`'s first branch, both halves.  The bits come from
`AxiomBitsP` (the axiom's *own* recorded run) and the memberships from
`AxiomMemP`; the v1 extension is `extendAxiomS` at the **named**
witness, which `StdAxiomKey.lean`'s `propextKeyS_mem`/`choiceKeyS_mem`
now expose — the `trustCompiler` branch's lesson, that the key's `∃` is
one currency too coarse for a P leaf, generalized. -/

/-- **The standard-axiom branch, discharged.**  The leaf is the layer's
own constant in both halves, so every syntactic obligation is `rfl` or
a `const` clause, and the whole content is the membership. -/
theorem axiomStd (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValRun μ F env cv type')
    (hok : ConLeche.stdAxiomOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    Nonempty (EnvModelM V μ
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩) := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  obtain ⟨stype, usort, hst, hens⟩ := hrunT
  have hwfc : ConLeche.EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf
      ⟨htf', htp, Expr.constsResolve_mono htr, hbt', ?_, ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro tbl heq; exact nomatch heq
    · intro cv2 caps heq; exact nomatch heq
  by_cases hn : cv.name = propextName
  · refine harvestAxiom (V := V) hμ mp hcv
      (A := fun _ => .const .propext []) (fun _ => trivial)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => by simp)
      (fun _ _ => by simp) ?_ (by rw [hn]; decide)
    intro ψ ta hta ρ
    exact propext_mem hμ mp hok hn hst ψ ta hta ρ
  · by_cases hn2 : cv.name = choiceName
    · -- the pin fixes the axiom's one level parameter, so both the v1
      -- witness and the P leaf read only `ψ uN`
      have huN : ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → ψ₁ uN = ψ₂ uN := by
        intro ψ₁ ψ₂ hp
        obtain ⟨-, -, -, hApin⟩ := nonempty_shapes hok hn2
        have hlpA : cv.levelParams = choiceA.levelParams :=
          (matchesPin_invT hApin).2
        refine hp uN ?_
        rw [hlpA, show choiceA.levelParams = [uN] from rfl]
        exact List.Mem.head _
      refine harvestAxiom (V := V) hμ mp hcv
        (A := fun ψ => .const .choice [ψ uN])
        (fun _ => trivial)
        (fun _ _ => rfl)
        (fun ψ₁ ψ₂ hp => by
          show AnnotTerm.const .choice [ψ₁ uN] = AnnotTerm.const .choice [ψ₂ uN]
          rw [huN ψ₁ ψ₂ hp])
        (fun _ _ => by simp) (fun _ _ => by simp) ?_
        (by rw [hn2]; decide)
      intro ψ ta hta ρ
      exact choice_mem hμ mp hok hn2 hst ψ ta hta ρ
    · exfalso
      unfold ConLeche.stdAxiomOk at hok
      rw [show (⟨cv.name, cv.levelParams, type'⟩ : ConstantVal).name
        = cv.name from rfl] at hok
      rw [if_neg hn, if_neg hn2] at hok
      exact nomatch hok

end ConLeche.Model
