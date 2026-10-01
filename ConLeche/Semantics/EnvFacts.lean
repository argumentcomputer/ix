module

public import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
public import ConLeche.Verify.Denote.Levels
public import ConLeche.Verify.EnvPreds
import ConLeche.Verify.Denote
import ConLeche.Verify.Denote.OpenVars
public import ConLeche.Verify.Denote.VClosed

@[expose] public section

/-!
# `EnvFacts`: the environment facts the bridge consumes (task #148, T3)

**Relocated to the base at task #161 S6** (whole-module move of
`ConLeche/SetR/Bridge/Env.lean`, statements byte-unchanged, namespace
`ConLeche.SetR` kept).  The file never had a lane: the docstring below
already said every field is V-free, and its four imports were base
already.  What forced the move is that **both** lanes now build an
`EnvFacts` — the R lane by `EnvS.toEnvFacts`, the P lane by `EnvModelM.toEnvFacts`
— and the P lane may not import `ConLeche/SetR/*`.

The bridge (`ConLeche/SetR/Bridge/*`) turns a successful `--verified`
checker run into a derivation of the relation family
(`ConLeche/SetR/Rel.lean`).  Doing so needs a handful of facts about the
environment it runs against, and **all of them are V-free**: the bridge
never mentions a set, a membership or an interpretation.  They are
collected here rather than taken as loose hypotheses because there are
seven of them and every clause lemma would otherwise carry all seven.

**This is an interface, not a new invariant.**  Each field below is
either literally a field of `ConLeche/TTVerify/EnvTT.lean`'s `EnvTT` or an
immediate consequence of one, and each is listed in the campaign
design's §2 among `EnvS`'s *syntactic* fields ("verbatim from `EnvTT`,
all mode-independent").  When T5 builds `EnvS`, it supplies an `EnvFacts`
by projection — one adapter, written once; nothing in the bridge has to
change, and nothing in the bridge depends on a semantic field.

The one field that is *not* a verbatim `EnvTT` field is `ty_denotes`,
and it is deliberately the **weakest** form that works: `EnvTT.has_type`
and `EnvS.mem_type` both say "the stored type denotes **and** the
constant's valuation inhabits it"; the bridge only ever uses the first
conjunct (the `.const` inference clause and the iota clause's stored
telescopes need a denotation to name, never a typing).  Taking the
weaker fact keeps the bridge free of any semantic content, which is the
whole point of the factoring.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- The environment facts the bridge consumes: a constant valuation,
its closedness, the syntactic well-formedness of the store, level
insensitivity, denotability of stored types, and the two unfolding
equations (which are what make delta steps invisible — design §7.2).

Every field is V-free and mode-independent. -/
structure EnvFacts (env : Env) where
  /-- The type-theory term of each constant (the same `TConstVal` the
  denotation and `EnvTT` use). -/
  cval : TConstVal
  /-- Every constant denotes to a closed term.  Consumed by every
  lifting step (`denote_weaken_top`, `denote_lift`) and by M1. -/
  cval_closed : ∀ (n : Name) (ψ : Name → Nat), Term.Closed (cval n ψ)
  /-- Stored declarations are syntactically well-formed.  Consumed by
  the frame-condition lemmas of `ConLeche/Verify/*`. -/
  wf : EnvWF env
  /-- A constant's term only depends on its own level parameters.
  Consumed by the same-head spine short-circuit. -/
  val_params : ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂
  /-- **Every stored constant's type denotes.**  The weakest form of
  `EnvTT.has_type` / `EnvS.mem_type` the bridge needs: it names the
  `Term` the `.const` rule's `denoteClosed` side condition asks for,
  and nothing else. -/
  ty_denotes : ∀ c ∈ env.consts, ∀ ψ : Name → Nat,
    ∃ t, denoteClosed cval env ψ c.toConstantVal.type = some t
  /-- Every definition is denoted by its body — the fact that makes a
  delta step an *identity* of denotations, hence contributes no rule to
  the family (design §7.2, R17). -/
  defn_eq : ∀ cv value hint,
    ConstantInfo.defnInfo cv value hint ∈ env.consts → ∀ ψ : Name → Nat,
      denoteClosed cval env ψ value = some (cval cv.name ψ)
  /-- **Every stored fireable recursor rule's right-hand side denotes**,
  at every instantiation of the recursor's level parameters.

  `ty_denotes` covers stored *types*; a rule's `rhs` is not one.
  `EnvWF` gives it `hasFvar = false`, `constsResolve` and
  `looseBVarsBounded 0`, but `constsResolve` records *existence* of the
  referenced constants, not the level-arity matches `denote`'s `.const`
  clause tests — so denotability is a genuinely extra fact.
  `EnvS.rec_rules` carries it; consumed by R11's `denoteClosed` side
  condition (batch g). -/
  rec_rhs_denotes : ∀ n cv mI rP rules,
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules, RecRule.fire r ≠ .inert →
      ∀ (us : List Level) (ψ : Name → Nat),
        us.length = cv.levelParams.length →
        ∃ R, denoteClosed cval env ψ
          (r.rhs.instantiateLevelParams cv.levelParams us) = some R
  /-- **A stored recursor's parameter count does not exceed its major
  index.**  The bridge-side half of the D3 split: `EnvWF` concludes
  `rP ≤ mI` only inside the `.nested` branch, so R11's *nested* premise
  carries it, while R11's *index* side condition needs it on `.plain`
  fires too (premise 6's length disjunct is otherwise open at
  `mI < rP`).  The soundness side takes the same fact from
  `EnvS.rec_rules`' first component; this field is backed by it. -/
  rec_params_le : ∀ n cv mI rP rules,
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules, RecRule.fire r ≠ .inert → rP ≤ mI
  /-- Every stored native projection-table entry is a pinned pair entry
  with its block stored (`ProjOkT`).  Syntactic; the bridge's I9 and R6
  clauses need it to identify the entry's type as a *concrete* closed
  expression (`ConLeche/SetR/ProjPins.lean`), which is what makes their
  denotation and residual walks computations.  `EnvS` carries the same
  field. -/
  proj_ok : ProjOkT env
  /-- **The install fold's `Nat`-op invariant, narrowed to what the
  literal fast path reads** (task #161 de-gating item B3, harvest site
  37 / list entry P7): a *stored* one of the sixteen accelerated
  operations is a *guarded* one.

  `reduceNat` used to re-derive `natOpGuard` at every literal hit — a
  dozen `Env.find?`s and a dependency-list build; it now tests
  `natOpStored`, one lookup.  This field is what turns that test back
  into the guard the R9/R10 premises name, and it is not new evidence:
  `EnvS.nat_ops`/`EnvS.div_mod` state exactly this under their
  `defnInfo` hypothesis (they are what `checkDecl` establishes, by
  declining a stream that stores one of these names unguarded), and
  `EnvS.toEnvFacts` supplies the field from them.  V-free, like every other
  field here. -/
  nat_op_guard : ∀ c, (c ∈ natOpNames ∨ c ∈ natDivModNames) →
    natOpStored env c = true → natOpGuard env c = true

/-! ## Two `find?` readings, at the base

Both lanes use them everywhere (the P lane at twenty-one files), and
they were declared in `SetR/EnvS.lean` only because that is where
`EnvS` needed them first.  Relocated verbatim at task #161 S7, Wall C
— names unchanged. -/

/-- A `find?` hit names the stored constant. -/
theorem Env.find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  unfold ConLeche.Env.find? at h
  have := List.find?_some h
  simpa using this

/-- A `find?` hit is a stored constant. -/
theorem Env.find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts := by
  unfold ConLeche.Env.find? at h
  exact List.mem_of_find?_eq_some h

end ConLeche.Semantics
