module

public import ConLeche.Model.CtxOkKit
public import ConLeche.Model.Rules.Recompose
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.BetaGate
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Semantics.Frame

public section

/-!
# The tiers surface (task #305 closing)

The tiers surface: what the declaration fold and the install rows read
about the checker beyond the four claims — the run-stated readability
facts.  Everything semantic is `Model/Rules/Recompose.lean`'s
`checkSoundAtP5` (re-exported here); what remains is stated over runs
of `inferTypeCore` and cannot be in the rules tier: `InferReads` (the
inferred type reads — derived from the rules tier's existence-form
motive), `SortSemAt`, and `acceptedReads_of` (whatever `inferTypeCore`
accepts, `denoteMeta` reads — a fuel induction over the checker's own
clause structure, the subject side, which no derivation supplies
because the motives take the subject's reading as a premise).
Successor of `Model/Steps/Tiers.lean` (task #305 closing).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level whnf inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

-- The recomposition, re-exported under the names the fold has always
-- used (`Model/Rules/Recompose.lean`): `checkSoundAtP5` is the five
-- claims at every fuel, `checkSoundAt` its four-way projection.
export ConLeche.Model.Rules (checkSoundAtP5 checkSoundAt)

/-! ## The inferred type reads -/

/-- **The infer quarter's totality residue**: an accepted subject's
inferred type reads.  Conditioned exactly as the claims are: the run,
the subject's scoping package, the subject's CONTEXT, and the
subject's own reading.

The `Model/Steps/Infer.lean` statement this succeeds took a
`LeafReads m φ d e` premise instead of the context — the residue of a
separate four-way readability walk (`Model/Steps/Reads.lean`), and
batch 8's repair of a refutable statement (the `.fvar` clause returns
the leaf's stored annotation, which the subject's reading never
mentions).  In the rules tier readability is the motive's existence
form, whose premise IS the context, and every consumer held one
(`LeafReads.of_ctxOk hC` at each call site, now just `hC`);
`LeafReads` retires with the Steps tier (task #305 closing). -/
@[expose] def InferReads {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AnnotTerm} {ea : AnnotTerm},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOk m φ d Δa e →
    denoteMeta m.acval env φ d e = some ea →
    ∃ ta, denoteMeta m.acval env φ d t = some ta

/-- **`InferReads`, discharged from the rules tier** (task #305
closing): the bridge turns the run into a derivation and the infer
motive CONCLUDES the type's reading — the shape `Recompose.lean`'s
fourth case destructures. -/
theorem inferReads_of (hμ : μ.verifiedChecks = true)
    {m : EnvModel V env} (hin : Rules.RulesInputs V m φ) :
    InferReads m μ φ fuel := by
  intro d e t Δa ea hrun hws hb hLb hC hea
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  obtain ⟨-, -, ta, hta, -, -, -⟩ :=
    Rules.infer_sound hin (Rules.inferTypeCore_bridge hrun)
      ⟨hws, hb, hLb⟩ hC hea
  exact ⟨ta, hta⟩

/-! ## The derived sort fact (`Model/Steps/Infer.lean:74`, `:798`) -/

/-- **The sort fact, at the induction's own fuel** (`SortSem2`'s
successor).  The canonical lane ROUTES `SortSem2` — "the top-level
induction is where it becomes available", and in-tree it never does:
the annotation fuel made its runs off-induction, and it stands among
`Capstone2E`'s fifteen.  In the P tier the annotation fuel is gone,
every use in the quarter is at the induction-bounded checker fuel,
and `sortSemAt_of_claims` *derives* the fact from the claims one
level down — another canonical-frontier residue dissolved.  The
subject's scoping package is carried so the claims can be applied. -/
@[expose] def SortSemAt {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {u : Level} {Δa : List AnnotTerm}
    {ea : AnnotTerm},
    CtxOk m φ d Δa e →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    inferTypeCore μ env fuel d e = .ok t →
    whnf μ env fuel d t = .ok (.sort u) →
    denoteMeta m.acval env φ d e = some ea →
    ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V)

/-- `denoteMeta` at a sort (the `denote2_sortQ` mirror). -/
theorem denoteMeta_sortQ {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {u : Level} :
    denoteMeta acval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denoteMeta]

/-- **`SortSem2`'s discharge** (impossible in the canonical lane): the
sort fact at `fuel` from the claims at `fuel` plus the one totality
factor — infer the type (`hreads` says it reads), grade both readings
(`ihi`), then walk the type to its sort (`ihw`) and the membership
lands in the universe. -/
theorem sortSemAt_of_claims {env : Env} {m : EnvModel V env}
    {fuel : Nat}
    (ihw : WhnfClaim μ m φ fuel) (ihi : InferClaim μ m φ fuel)
    (hreads : InferReads m μ φ fuel) :
    SortSemAt m μ φ fuel := by
  intro d e t u Δa ea hC hws hb hLb hi hw hea
  obtain ⟨ta, hta⟩ :=
    hreads hi hws hb hLb hC hea
  obtain ⟨hokE, hokT, hmem⟩ := ihi hi hws hb hLb hC hea hta
  have hwt : Expr.WScoped d t :=
    inferTypeCore_WScoped m.wf fuel hi hws
  have hbt : t.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hi hws hb hLb
  have hLt : Expr.LeavesBounded t := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel hi hws l hl)
  have hCt : CtxOk m φ d Δa t :=
    hC.of_subset (inferTypeCore_fvarLeaves m.wf fuel hi hws)
  obtain ⟨-, heq⟩ := ihw hw hwt hbt hLt hCt hta denoteMeta_sortQ hokT
  intro ρ hρ
  refine ⟨hokE ρ hρ, ?_⟩
  have hm := hmem ρ hρ
  rw [heq ρ hρ, interp_sort] at hm
  exact hm

/-! ## The subject-side totality walk (`Model/Steps/Accepted.lean`)

**Whatever `inferTypeCore` accepts, `denoteMeta` reads.**  A plain fuel
induction over the checker's own clause structure, every clause a
*coincidence of guards*: `denoteMeta` fails on exactly four things, and
at each of them the front door has already checked the same condition.

| `denoteMeta` failure | the front door's guard |
| --- | --- |
| a loose `.bvar` | outside the fragment (`.notImplemented`); also excluded by the subject's own `looseBVarsBounded 0` |
| `.const` unfindable / mis-arity | `env.find?` + `us.length = cv.levelParams.length`, the two `throw`s of the `.const` clause |
| a literal without its basis | `natLitSupported` / `strLitSupported`, the literal clauses' guards |
| `.proj i` with `2 ≤ i` (the decoder `AnnotTerm.projPair?`'s `none`) | the projection table: a `native` entry is one of the two pinned pair entries, so `i < 2` (`projPinsP`) |

The `.fvar` clause reads **unconditionally** — `denoteMeta` never looks
at the leaf's stored annotation; that asymmetry is what made
`InferReads` refutable without its context premise and what makes
*this* statement free of a leaf premise.

`inferBody`'s `letE` arm is a positive `.internal` error (task #241) —
the official `infer_let` triple lives in `annotateBody`, which returns
the ζ *reduct* (task #217), so inference only ever sees let-free
expressions; `inferTypeCore_letE_inv` turns the run hypothesis into
`False`.

No environment field is consulted: the walk is a statement about the
*checker*, not about the model, which is why it is a theorem at
`EnvModel` rather than a bundle entry. -/

/-! ### The three run inversions the walk adds

`Verify/InferLemmas.lean` has the binder, application, `letE` (the
vacuous one) and projection inversions already; the `.const` one
there drops the arity equation (it is consumed inside its own
`split`) and the two literal clauses have none.  All three are one
`simp only [inferBody, …]` deep. -/

/-- **The `.const` clause's arity guard, recorded.**
`inferTypeCore_const_inv` returns the stored type; this returns the
equation the clause's second `throw` tests — which is precisely
`denoteMeta`'s `.const` guard. -/
theorem inferTypeCore_const_inv_len {fuel d : Nat}
    {n : Name} {us : List Level} {t : Expr}
    (h : inferTypeCore μ env fuel d (.const n us) = .ok t) :
    ∃ ci, env.find? n = some ci ∧
      us.length = ci.toConstantVal.levelParams.length := by
  match fuel, h with
  | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [ConLeche.inferTypeCore_succ] at h
    simp only [ConLeche.inferBody, pure, Except.pure,
      Bind.bind, Except.bind] at h
    revert h
    cases hf : env.find? n with
    | none => intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
    | some ci =>
      intro h
      dsimp only at h
      by_cases hlen : us.length = ci.toConstantVal.levelParams.length
      · exact ⟨ci, rfl, hlen⟩
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The `Nat`-literal clause's guard, recorded** — `denoteMeta`'s own
literal guard, verbatim. -/
theorem inferTypeCore_natLit_inv {fuel d k : Nat} {t : Expr}
    (h : inferTypeCore μ env fuel d (.lit (.natVal k)) = .ok t) :
    ConLeche.natLitSupported env = true := by
  match fuel, h with
  | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [ConLeche.inferTypeCore_succ] at h
    simp only [ConLeche.inferBody, pure, Except.pure] at h
    by_cases hg : ConLeche.natLitSupported env = true
    · exact hg
    · rw [if_neg hg] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The string-literal clause's guard, recorded.** -/
theorem inferTypeCore_strLit_inv {fuel d : Nat} {s : String} {t : Expr}
    (h : inferTypeCore μ env fuel d (.lit (.strVal s)) = .ok t) :
    ConLeche.strLitSupported env = true := by
  match fuel, h with
  | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [ConLeche.inferTypeCore_succ] at h
    simp only [ConLeche.inferBody, pure, Except.pure] at h
    by_cases hg : ConLeche.strLitSupported env = true
    · exact hg
    · rw [if_neg hg] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The walk -/

/-- The walk, with the fuel explicit (the induction's own shape). -/
private theorem acceptedReads_aux (m : EnvModel V env) (φ : Name → Nat) :
    ∀ (F : Nat) {d : Nat} {e t : Expr},
      inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denoteMeta m.acval env φ d e = some ea := by
  intro F
  induction F with
  | zero =>
    intro d e t h _ _ _
    rw [ConLeche.inferTypeCore_zero] at h
    exact nomatch h
  | succ F ih =>
    intro d e t h hws hb hL
    match e with
    | .bvar i =>
      simp only [Expr.looseBVarsBounded] at hb
      exact absurd (of_decide_eq_true hb) (Nat.not_lt_zero i)
    | .sort u => exact ⟨_, denoteMeta_sort _ _ _⟩
    | .fvar idx ty => exact ⟨_, denoteMeta_fvar _ _ _ _⟩
    | .const n us =>
      obtain ⟨ci, hf, hlen⟩ := inferTypeCore_const_inv_len h
      exact ⟨_, denoteMeta_const hf hlen⟩
    | .lit (.natVal k) =>
      exact ⟨_, denoteMeta_natLit (inferTypeCore_natLit_inv h)⟩
    | .lit (.strVal s) =>
      -- the reading is the (long) pinned character spine; name it by
      -- case analysis rather than transcribing it
      rcases hd : denoteMeta m.acval env φ d (.lit (.strVal s)) with _ | ea
      · rw [denoteMeta, if_pos (inferTypeCore_strLit_inv h)] at hd
        exact nomatch hd
      · exact ⟨ea, rfl⟩
    | .app f a =>
      obtain ⟨tf, _, _, _, htf, -, -, ta, hta, -⟩ :=
        ConLeche.inferTypeCore_app_inv h
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨fa, hfa⟩ := ih htf hws.1 hb.1 (fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl]))
      obtain ⟨aa, haa⟩ := ih hta hws.2 hb.2 (fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl]))
      exact ⟨_, by rw [denoteMeta_app, hfa, haa]; rfl⟩
    | .forallE ty body mb =>
      obtain ⟨tty, u, bt, v, htty, -, hbt, -, -, -⟩ :=
        ConLeche.inferTypeCore_forall_inv h
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hLty : Expr.LeavesBounded ty := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      have hLbd : Expr.LeavesBounded body := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      obtain ⟨hwo, hbo, hLo⟩ :=
        frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbd
      obtain ⟨ta, hta⟩ := ih htty hws.1 hb.1 hLty
      obtain ⟨ba, hba⟩ := ih hbt hwo hbo hLo
      exact ⟨_, by rw [denoteMeta_forallE, hta, hba]; rfl⟩
    | .lam ty body mb =>
      obtain ⟨tty, u, bt, htty, -, hbt, -, -, -⟩ :=
        ConLeche.inferTypeCore_lam_inv h
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hLty : Expr.LeavesBounded ty := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      have hLbd : Expr.LeavesBounded body := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      obtain ⟨hwo, hbo, hLo⟩ :=
        frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbd
      obtain ⟨ta, hta⟩ := ih htty hws.1 hb.1 hLty
      obtain ⟨ba, hba⟩ := ih hbt hwo hbo hLo
      exact ⟨_, by rw [denoteMeta_lam, hta, hba]; rfl⟩
    | .proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, htpe, -, -, hfe, -, -, -, -,
        hsn⟩ := ConLeche.inferTypeCore_proj_inv h
      subst hsn
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded] at hb
      obtain ⟨pa, hpa⟩ := ih htpe hws hb (fun l hl =>
        hL l (by simpa [Expr.fvarLeaves] using hl))
      exact ⟨_, denoteMeta_proj_tower hfe hpa⟩
    | .letE ty val body =>
      exact (ConLeche.inferTypeCore_letE_inv h).elim

/-- **`accepted_reads`, discharged** — the statement `SemTierInputsP`
carried as its last field, now a theorem.  Whatever the front door's
inference accepts, the validated-annotation reading reads.  See the
module docstring for the guard table and for the vacuous `letE`
clause. -/
theorem acceptedReads_of (m : EnvModel V env) (φ : Name → Nat)
    {F d : Nat} {e t : Expr}
    (h : inferTypeCore μ env F d e = .ok t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e) :
    ∃ ea, denoteMeta m.acval env φ d e = some ea :=
  acceptedReads_aux m φ F h hws hb hL

end ConLeche.Model
