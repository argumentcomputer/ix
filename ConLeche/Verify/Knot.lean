module

import ConLeche.Kernel.TypeChecker
public import ConLeche.Kernel.CoreIO
public import ConLeche.Verify.BetaGate

public section

/-!
# Knot equations

The definitional bridges between the fueled entry-point spellings
(`whnfCore mode env fuel d e`, …) and the core bodies applied to the knot
one level down.  Inversion and claims lemmas are stated against the
bodies with an abstract record; instantiating the record with
`pureFns mode env fuel` and rewriting with these equations recovers the
fueled statements the higher layers consume.
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## Loop step budgets

The reduction and lazy-delta loops (task #106) run on their own step
budgets, kept `irreducible` so that the `rfl` knot equations above do
not try to evaluate them.  Proofs that need to peel one iteration use
these positivity witnesses instead. -/

theorem whnfLoopFuel_succ : ∃ n, whnfLoopFuel = n + 1 :=
  ⟨99999, by unfold whnfLoopFuel; rfl⟩


@[simp] theorem pureFns_whnfCore (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env (f + 1)).whnfCore d e =
      whnfCoreBody mode (pureFns mode env f) env d e := rfl

@[simp] theorem pureFns_whnf (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env (f + 1)).whnf d e = whnfBody (pureFns mode env f) env d e := rfl

@[simp] theorem pureFns_infer (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env (f + 1)).infer d e = inferBody mode (pureFns mode env f) env d e := rfl

@[simp] theorem pureFns_defeq (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns mode env (f + 1)).defeq d a b =
      defeqBody mode (pureFns mode env f) env d a b := rfl

@[simp] theorem pureFns_annotate (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env (f + 1)).annotate d e =
      annotateBody (pureFns mode env f) env d e := rfl

theorem whnfCore_succ (env : Env) (f d : Nat) (e : Expr) :
    whnfCore mode env (f + 1) d e = whnfCoreBody mode (pureFns mode env f) env d e := rfl

theorem whnf_succ (env : Env) (f d : Nat) (e : Expr) :
    whnf mode env (f + 1) d e = whnfBody (pureFns mode env f) env d e := rfl

theorem inferTypeCore_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCore mode env (f + 1) d e = inferBody mode (pureFns mode env f) env d e := rfl

theorem isDefEqCore_succ (env : Env) (f d : Nat) (a b : Expr) :
    isDefEqCore mode env (f + 1) d a b = defeqBody mode (pureFns mode env f) env d a b := rfl

theorem annotateCore_succ (env : Env) (f d : Nat) (e : Expr) :
    annotateCore mode env (f + 1) d e = annotateBody (pureFns mode env f) env d e := rfl

/-! ## The io lane (task #161 stage 2)

The io knot is a *leaf* lane: its reduction and definitional-equality
fields are the full knot's at the same fuel, so the equations below
fold them straight back to the full spellings and the io claims family
consumes the sealed four unchanged. -/

@[simp] theorem pureFnsIO_whnfCore (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsIO mode env f).whnfCore d e = whnfCore mode env f d e := by
  cases f <;> rfl

@[simp] theorem pureFnsIO_whnf (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsIO mode env f).whnf d e = whnf mode env f d e := by
  cases f <;> rfl

@[simp] theorem pureFnsIO_defeq (env : Env) (f d : Nat) (a b : Expr) :
    (pureFnsIO mode env f).defeq d a b = isDefEqCore mode env f d a b := by
  cases f <;> rfl

@[simp] theorem pureFnsIO_annotate (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsIO mode env f).annotate d e = annotateCore mode env f d e := by
  cases f <;> rfl

theorem ensureSortIO_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFnsIO mode env f) env d e = ensureSortCore mode env f d e := by
  cases f <;> rfl

@[simp] theorem pureFnsIO_infer (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsIO mode env (f + 1)).infer d e =
      inferBodyIO mode (pureFnsIO mode env f) env d e := rfl

theorem inferTypeCoreIO_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCoreIO mode env (f + 1) d e =
      inferBodyIO mode (pureFnsIO mode env f) env d e := rfl

theorem inferIO_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsIO mode env f).infer d e = inferTypeCoreIO mode env f d e := rfl

theorem inferTypeCoreIO_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCoreIO mode env 0 d e =
      throw (.internal "fuel exhausted: infer") := rfl

/-! ## The io slot (task #172 B4)

The executable knot's `inferIO` slot, related to the two named lanes:
at a gate-off mode it **is** `inferTypeCore` (`inferTypeIO_off` — the
task-#170 R clause, "infer_only is just equivalent to infer"), and at
the gated mode it **is** the leaf-lane `inferTypeCoreIO` the io claims
are stated at (`inferTypeIO_on`).  Between them every internal-infer
inversion below can expose `inferTypeIO` runs and let each tower
collapse them to its own lane. -/

@[simp] theorem pureFns_inferIO (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env (f + 1)).inferIO d e =
      if mode.betaGate then
        inferBodyIO mode (CoreFns.ioView (pureFns mode env f)) env d e
      else inferBody mode (pureFns mode env f) env d e := rfl

theorem inferTypeIO_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeIO mode env (f + 1) d e =
      if mode.betaGate then
        inferBodyIO mode (CoreFns.ioView (pureFns mode env f)) env d e
      else inferBody mode (pureFns mode env f) env d e := rfl

theorem inferTypeIO_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).inferIO d e = inferTypeIO mode env f d e := rfl

theorem inferTypeIO_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeIO mode env 0 d e =
      throw (.internal "fuel exhausted: infer") := rfl

/-- **The gate-off collapse**: at a mode whose β/io gate bit is off the
io slot is full inference, definitionally after one rewrite — the
task-#170 R clause as a theorem.  This is what keeps every R-tower
statement verbatim: an inversion exposing an `inferTypeIO` run hands
the R side an `inferTypeCore` run through this equation. -/
theorem inferTypeIO_off (hg : mode.betaGate = false) (env : Env)
    (f d : Nat) (e : Expr) :
    inferTypeIO mode env f d e = inferTypeCore mode env f d e := by
  cases f with
  | zero => rfl
  | succ f => rw [inferTypeIO_succ, hg]; rfl

/-- `inferBodyIO` reads exactly three fields of its record (`whnf`,
`infer`, `defeq`); two records agreeing there run it identically. -/
theorem inferBodyIO_congr {r₁ r₂ : CoreFns CheckM} {env : Env}
    (hw : r₁.whnf = r₂.whnf) (hi : r₁.infer = r₂.infer)
    (hd : r₁.defeq = r₂.defeq) (d : Nat) (e : Expr) :
    inferBodyIO mode r₁ env d e = inferBodyIO mode r₂ env d e := by
  cases r₁; cases r₂
  dsimp only at hw hi hd
  subst hw; subst hi; subst hd
  rfl

/-- **The gated-mode identification**: at the gated mode the executable
io slot runs the leaf-lane `inferTypeCoreIO` — the io claims' stated
subject — level for level.  (The two ties differ only in which record
carries the io recursion: `CoreFns.ioView` of the knot versus the leaf
knot; `inferBodyIO_congr` plus this induction identifies them.) -/
theorem inferTypeIO_on (hg : mode.betaGate = true) (env : Env) :
    ∀ (f d : Nat) (e : Expr),
      inferTypeIO mode env f d e = inferTypeCoreIO mode env f d e
  | 0, _, _ => rfl
  | f + 1, d, e => by
    rw [inferTypeIO_succ, hg, if_pos rfl, inferTypeCoreIO_succ]
    exact inferBodyIO_congr (mode := mode)
      (r₁ := (pureFns mode env f).ioView) (r₂ := pureFnsIO mode env f)
      (funext fun d' => funext fun e' => (pureFnsIO_whnf env f d' e').symm)
      (funext fun d' => funext fun e' => by
        show inferTypeIO mode env f d' e' = (pureFnsIO mode env f).infer d' e'
        rw [inferTypeIO_on hg env f d' e']
        exact (inferIO_def (mode := mode) env f d' e').symm)
      (funext fun d' => funext fun a => funext fun b =>
        (pureFnsIO_defeq env f d' a b).symm) d e

theorem whnfCore_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).whnfCore d e = whnfCore mode env f d e := rfl

theorem whnf_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).whnf d e = whnf mode env f d e := rfl

theorem infer_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).infer d e = inferTypeCore mode env f d e := rfl

theorem defeq_def (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns mode env f).defeq d a b = isDefEqCore mode env f d a b := rfl

theorem annotate_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).annotate d e = annotateCore mode env f d e := rfl

/-- Fuel-zero spellings throw. -/
theorem whnfCore_zero (env : Env) (d : Nat) (e : Expr) :
    whnfCore mode env 0 d e = throw (.internal "fuel exhausted: whnfCore") := rfl

theorem whnf_zero (env : Env) (d : Nat) (e : Expr) :
    whnf mode env 0 d e = throw (.internal "fuel exhausted: whnf") := rfl

theorem inferTypeCore_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCore mode env 0 d e = throw (.internal "fuel exhausted: infer") := rfl

theorem isDefEqCore_zero (env : Env) (d : Nat) (a b : Expr) :
    isDefEqCore mode env 0 d a b = throw (.internal "fuel exhausted: defeq") := rfl

theorem annotateCore_zero (env : Env) (d : Nat) (e : Expr) :
    annotateCore mode env 0 d e =
      throw (.internal "fuel exhausted: annotate") := rfl

theorem ensureSort_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFns mode env f) env d e = ensureSortCore mode env f d e := rfl

/-! Fueled spellings for the record-parameterized helpers: the body one
level up calls them with `pureFns mode env fuel`, so their facts appear in
inversions at the same fuel as the entry-point facts. -/

abbrev iotaRecFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := iotaRec mode (pureFns mode env fuel) env

abbrev iotaCertsFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Bool → Expr →
    List Expr → CheckM Bool := iotaCerts (pureFns mode env fuel) env

abbrev iotaIndexOkFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Nat → Nat → Nat →
    Expr → List Expr → List Expr → CheckM Bool := iotaIndexOk (pureFns mode env fuel) env

abbrev defEqListFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → List Expr →
    List Expr → CheckM Bool := defEqList (pureFns mode env fuel) env

abbrev proofIrrelFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := proofIrrel (pureFns mode env fuel) env

abbrev propIrrelFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := propIrrel (pureFns mode env fuel) env

abbrev stuckIrrelFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := stuckIrrel mode (pureFns mode env fuel) env

abbrev structEtaCertFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := structEtaCert mode (pureFns mode env fuel) env

abbrev structEtaCertWithFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    Expr → CheckM Bool := structEtaCertWith mode (pureFns mode env fuel) env

abbrev structEtaProjCertsFueled (mode : CheckMode) (env : Env) (fuel : Nat) (d : Nat) (T : Name)
    (us' : List Level) (targs : List Expr) (b : Expr) (lpsT : List Name) :
    List Nat → CheckM Bool :=
  structEtaProjCerts (pureFns mode env fuel) env d T us' targs b lpsT

abbrev structUnitCertFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := structUnitCert (pureFns mode env fuel) env

abbrev etaCertFueled (mode : CheckMode) (env : Env) (fuel : Nat) (d : Nat)
    (ty body : Expr) (mb : BinderMeta) (b : Expr) : CheckM Bool :=
  etaCert mode (pureFns mode env fuel) env d ty body mb b

abbrev majorToCtorFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Name →
    List RecRule → Expr → CheckM Expr := majorToCtor mode (pureFns mode env fuel) env

abbrev litMajorToCtorFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM Expr := litMajorToCtor (pureFns mode env fuel) env

abbrev prepareMajorFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Name →
    List RecRule → Expr → CheckM Expr := prepareMajor mode (pureFns mode env fuel) env

abbrev projLitToCtorFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM Expr := projLitToCtor (pureFns mode env fuel) env

abbrev projCertFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Bool → Name →
    List Level → List Expr → CheckM Bool := projCert (pureFns mode env fuel) env
abbrev projCertAtFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Bool → Bool → Name →
    List Level → List Expr → CheckM Bool := projCertAt (pureFns mode env fuel) env

abbrev reduceNatFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := reduceNat (pureFns mode env fuel) env

abbrev boolTrueShortcutFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM Bool := boolTrueShortcut (pureFns mode env fuel)

abbrev defeqSpineFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := defeqSpine (pureFns mode env fuel) env

/-! Folding rewrites: record-applied helper spellings into their fueled
`P` names (used right after unfolding a body in an inversion proof). -/

theorem iotaRec_fold (env : Env) (fuel : Nat) :
    iotaRec mode (pureFns mode env fuel) env = iotaRecFueled mode env fuel := rfl
theorem iotaCerts_fold (env : Env) (fuel : Nat) :
    iotaCerts (pureFns mode env fuel) env = iotaCertsFueled mode env fuel := rfl
theorem iotaIndexOk_fold (env : Env) (fuel : Nat) :
    iotaIndexOk (pureFns mode env fuel) env = iotaIndexOkFueled mode env fuel := rfl
theorem defEqList_fold (env : Env) (fuel : Nat) :
    defEqList (pureFns mode env fuel) env = defEqListFueled mode env fuel := rfl
theorem proofIrrel_fold (env : Env) (fuel : Nat) :
    proofIrrel (pureFns mode env fuel) env = proofIrrelFueled mode env fuel := rfl
theorem propIrrel_fold (env : Env) (fuel : Nat) :
    propIrrel (pureFns mode env fuel) env = propIrrelFueled mode env fuel := rfl
theorem stuckIrrel_fold (env : Env) (fuel : Nat) :
    stuckIrrel mode (pureFns mode env fuel) env = stuckIrrelFueled mode env fuel := rfl
theorem structEtaCert_fold (env : Env) (fuel : Nat) :
    structEtaCert mode (pureFns mode env fuel) env = structEtaCertFueled mode env fuel := rfl
theorem structEtaCertWith_fold (env : Env) (fuel : Nat) :
    structEtaCertWith mode (pureFns mode env fuel) env =
      structEtaCertWithFueled mode env fuel := rfl
theorem structEtaProjCerts_fold (env : Env) (fuel : Nat) :
    structEtaProjCerts (pureFns mode env fuel) env =
      structEtaProjCertsFueled mode env fuel := rfl
theorem structUnitCert_fold (env : Env) (fuel : Nat) :
    structUnitCert (pureFns mode env fuel) env = structUnitCertFueled mode env fuel := rfl
theorem etaCert_fold (env : Env) (fuel : Nat) :
    etaCert mode (pureFns mode env fuel) env = etaCertFueled mode env fuel := rfl
theorem majorToCtor_fold (env : Env) (fuel : Nat) :
    majorToCtor mode (pureFns mode env fuel) env = majorToCtorFueled mode env fuel := rfl
theorem litMajorToCtor_fold (env : Env) (fuel : Nat) :
    litMajorToCtor (pureFns mode env fuel) env = litMajorToCtorFueled mode env fuel := rfl
theorem prepareMajor_fold (env : Env) (fuel : Nat) :
    prepareMajor mode (pureFns mode env fuel) env = prepareMajorFueled mode env fuel := rfl
theorem projLitToCtor_fold (env : Env) (fuel : Nat) :
    projLitToCtor (pureFns mode env fuel) env = projLitToCtorFueled mode env fuel := rfl
theorem projCertAt_fold (env : Env) (fuel : Nat) :
    projCertAt (pureFns mode env fuel) env = projCertAtFueled mode env fuel := rfl
theorem reduceNat_fold (env : Env) (fuel : Nat) :
    reduceNat (pureFns mode env fuel) env = reduceNatFueled mode env fuel := rfl
theorem boolTrueShortcut_fold (env : Env) (fuel : Nat) :
    boolTrueShortcut (pureFns mode env fuel) = boolTrueShortcutFueled mode env fuel := rfl
theorem defeqSpine_fold (env : Env) (fuel : Nat) :
    defeqSpine (pureFns mode env fuel) env = defeqSpineFueled mode env fuel := rfl

end ConLeche
