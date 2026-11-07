module

public import IxCK.Kernel.Cached.Installed

@[expose] public section

/-!
# The axiom policy: the strict fold and the fold that admits user axioms

The certified fold `checkDecls` (`IxCK/Kernel/Cached/Installed.lean`) admits an
axiom only as one of the pinned standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) or the tolerated `sorryAx`; any other axiom
declines. The **axiom policy** (`AxiomPolicy`) is the one parameter that
tells this fold apart from the fold that also admits *user axioms*:

* `strict` is `checkDecls` itself (`checkDeclsUnder_strict`);
* `allowUser` also admits an `.axiomDecl` under an eligible key
  (`Key.isCustomAxiomEligible`: an input key that names no role), with its
  header and type checked and installed as `.axiomInfo`, unless its type
  restates an axiom role's pinned specification (`axiomRoleSpecHit?`): that
  is a role's own axiom read under an input key because the role table does
  not bind the role, and it declines.

An accept under `allowUser` is conditional on the user axioms of its records,
`userAxiomsOfDecls` (`IxCK/Kernel/Roles.lean`), which are read off the
declarations, not the environment: the fold installs an opaque as
`.axiomInfo` too. The main theorem's model (`Ix.Kernel.model_exists`) is the
strict fold's; under `allowUser` this module proves that **without user
axioms the two folds are the same function**
(`checkDeclsUnder_eq_checkDecls`), so an accept that admitted none carries
every theorem of the strict fold (`IxCK/Kernel/Verify/Cached/PolicyC.lean`
proves the converse and `MainC`/`MainTheorem` the soundness letters).

The policy enters at exactly one place, the axiom arm (`checkAxiomDeclC`).
Everything else of a step is the strict fold's: `annotStepUnderC` overrides
`annotStepC` at `.axiomDecl` only, and `annotDeclStepUnder` and
`checkDeclsUnder` are `annotDeclStep` and `checkDecls` over it. The strict
definitions keep their own bodies, which the frozen runtime closures and the
proof towers read; that `strict` is them is proved here
(`checkDeclC_axiomDecl`, `annotStepUnderC_strict`, `annotDeclStepUnder_strict`,
`checkDeclsUnder_strict`), so the two can never drift apart. Like the fold's
own lemmas these use nothing but the definitions, so they live beside them.
-/

namespace Ix.Kernel.Cached

open Ix.Kernel

/-! ## The policy and the axiom roles' specifications -/

/-- **The axiom policy** a fold runs under: `strict` admits only the pinned
standard axioms and the tolerated `sorryAx` (`checkDecls`); `allowUser` also
admits user axioms under eligible keys (`AxiomPolicy.admits`). -/
inductive AxiomPolicy where
  | strict
  | allowUser
  deriving DecidableEq, Repr, Inhabited

/-- Whether `policy` admits an axiom under the key `k` as a user axiom:
never under `strict`; under `allowUser`, exactly at an eligible key
(`Key.isCustomAxiomEligible`). -/
def AxiomPolicy.admits (policy : AxiomPolicy) (k : Key md) : Bool :=
  match policy with
  | .strict => false
  | .allowUser => k.isCustomAxiomEligible

@[simp] theorem AxiomPolicy.admits_strict (k : Key md) :
    AxiomPolicy.strict.admits k = false := rfl

@[simp] theorem AxiomPolicy.admits_allowUser (k : Key md) :
    AxiomPolicy.allowUser.admits k = k.isCustomAxiomEligible := rfl

/-- No policy admits an ineligible key. -/
theorem AxiomPolicy.admits_of_not_eligible (policy : AxiomPolicy) {k : Key md}
    (h : k.isCustomAxiomEligible = false) : policy.admits k = false := by
  cases policy
  · rfl
  · exact h

/-- **The axiom roles' pinned specifications**, each under its role's key:
the roles whose specification is a typed axiom (`Role.spec`: `propext`,
`Classical.choice`, `sorryAx`), at the role's level count, and `Quot.sound`,
the quotient block's axiom (`quotSoundRaw`). -/
def axiomRolePins : List (Role × ConstantVal md) :=
  ([Role.propext, .choice, .sorryAx].filterMap fun r =>
    match (Role.spec (md := md)) r with
    | .axiom n (some ty) => some (r, { name := .role r, levelParams := List.range n, type := ty })
    | _ => none) ++
  [(.quotSound, quotSoundRaw.toConstantVal)]

/-- The axiom role whose pinned specification `cv` restates under another key,
if any: the same level count and, up to binder data, the same type
(`ConstantVal.matchesPin` at the role's key). -/
def axiomRoleSpecHit? (cv : ConstantVal md) : Option Role :=
  (axiomRolePins.find? fun p => ConstantVal.matchesPin { cv with name := p.2.name } p.2).map (·.1)

/-! ## The axiom arm, under a policy -/

variable (mode : CheckMode)

/-- **The strict axiom arm**: `checkDeclC`'s `.axiomDecl` arm, verbatim
(`checkDeclC_axiomDecl`). `Quot.sound` is compared with the pinned quotient
block's member and installs nothing; `propext` and `Classical.choice` install
when their environment and type are the pins' (`stdAxiomOkF`) and decline
otherwise; `sorryAx` is tolerated and installs nothing; any other axiom
declines. -/
def checkStdAxiomDeclC (fe : FEnv md) (cv : ConstantVal md) : (CheckCM md) (FEnv md) :=
  if cv.name = quotSoundName then
    (if ConstantInfo.canonEq (.axiomInfo cv) (quotBasis.getD 4 (.axiomInfo default)) then
      pure fe
    else
      throw (.notImplemented "quotient soundness axiom mismatch"))
  else do
    let (cvA, _) ← checkConstantValC mode fe cv
    if stdAxiomOkF fe cvA then
      pure (fe.push (.axiomInfo cvA))
    else if cvA.name = propextName ∨ cvA.name = choiceName then
      throw (.notImplemented msg!"standard axiom shape mismatch ({cv.name})")
    else if cvA.name = sorryAxName then
      pure fe
    else
      throw (.notImplemented msg!"non-standard axiom ({cv.name})")

/-- **The user axiom arm**: the header and type checked (`checkConstantValC`)
and the axiom installed as `.axiomInfo`, unless its type restates an axiom
role's pinned specification (`axiomRoleSpecHit?`), which declines: such an
axiom is the role's own (Lean's `sorryAx`, say) read under an input key
because the role table leaves the role unbound. -/
def checkUserAxiomDeclC (fe : FEnv md) (cv : ConstantVal md) : (CheckCM md) (FEnv md) := do
  let (cvA, _) ← checkConstantValC mode fe cv
  match axiomRoleSpecHit? cvA with
  | some r => throw (.notImplemented
      msg!"user axiom {cv.name} restates the specification of {(roleKey r : Key md)}, which the role table does not bind")
  | none => pure (fe.push (.axiomInfo cvA))

/-- **The axiom arm under a policy**: the user arm at a key the policy admits
(`AxiomPolicy.admits`), the strict arm otherwise. This is the only place the
policy is read. -/
def checkAxiomDeclC (policy : AxiomPolicy) (fe : FEnv md) (cv : ConstantVal md) :
    (CheckCM md) (FEnv md) :=
  if policy.admits cv.name then checkUserAxiomDeclC mode fe cv else checkStdAxiomDeclC mode fe cv

/-- `checkDeclStepC` at an axiom, under a policy: from the empty memo state
(`resetC`), the axiom arm. -/
def checkAxiomDeclStepC (policy : AxiomPolicy) (fe : FEnv md) (cv : ConstantVal md) :
    (CheckCM md) (FEnv md) := do
  resetC
  checkAxiomDeclC mode policy fe cv

/-- **Phase A's step body under a policy**: `annotStepC`, with the axiom arm
under the policy (`annotStepUnderC_strict`). -/
def annotStepUnderC (policy : AxiomPolicy) (ev : Evidences md) (i : Nat) (fe : FEnv md)
    (pend : Array (PendingCheck md)) :
    (Declaration md) → (CheckCM md) (FEnv md × Array (PendingCheck md))
  | .axiomDecl cv => do
    pure (← checkAxiomDeclStepC mode policy fe cv, pend)
  | pd => annotStepC mode ev i fe pend pd

/-- **Phase A's step under a policy**: `annotDeclStep` over `annotStepUnderC`
(the anchors validated first, the position carried and the error tagged). -/
def annotDeclStepUnder (policy : AxiomPolicy) (ev : Evidences md)
    (p : Nat × FEnv md × Array (PendingCheck md)) (pd : Declaration md) :
    StateT (CState md) (Except (CheckError md × Nat)) (Nat × FEnv md × Array (PendingCheck md)) :=
  fun s =>
    match pd.anchorMismatch? with
    | some k => .error (.notImplemented msg!"role specification mismatch ({k})", p.1)
    | none =>
      match annotStepUnderC mode policy ev p.1 p.2.1 p.2.2 pd s with
      | .ok ((fe', pend'), s') => .ok ((p.1 + 1, fe', pend'), s')
      | .error e => .error (e, p.1)

/-- **The declaration fold under a policy**: `checkDecls` over
`annotDeclStepUnder` (install every record, check every recorded declaration
on tasks, check units, return the environment). At `strict` it is
`checkDecls` (`checkDeclsUnder_strict`). -/
def checkDeclsUnder (mode : CheckMode) (policy : AxiomPolicy) (ev : Evidences md)
    (ds : Array (Declaration md)) :
    Except (CheckError md × Nat) (Env md) := do
  let (p, _) ← (ds.foldlM (annotDeclStepUnder mode policy ev) (0, mkFEnv Env.empty, #[])) {}
  checkPendingTasks mode p.2.1 p.2.2
  checkUnits ds
  pure p.2.1.env

/-- **Phase A's step with user axioms admitted** (`allowUser`): the step the
host's record-by-record driver runs. -/
def annotDeclStepWithUserAxioms (ev : Evidences md)
    (p : Nat × FEnv md × Array (PendingCheck md)) (pd : Declaration md) :
    StateT (CState md) (Except (CheckError md × Nat)) (Nat × FEnv md × Array (PendingCheck md)) :=
  annotDeclStepUnder mode .allowUser ev p pd

/-- **The declaration fold with user axioms admitted**: `checkDeclsUnder` at
`allowUser`. An accept is conditional on `userAxiomsOfDecls ds.toList`; with
none it is `checkDecls`'s (`checkDeclsWithUserAxioms_eq_checkDecls`). -/
def checkDeclsWithUserAxioms (mode : CheckMode) (ev : Evidences md)
    (ds : Array (Declaration md)) :
    Except (CheckError md × Nat) (Env md) :=
  checkDeclsUnder mode .allowUser ev ds

/-! ## `strict` is the certified fold -/

/-- `checkDeclC`'s axiom arm is the strict arm. -/
theorem checkDeclC_axiomDecl (ev : Evidences md) (fe : FEnv md) (cv : ConstantVal md) :
    checkDeclC mode ev fe (.axiomDecl cv) = checkStdAxiomDeclC mode fe cv := rfl

/-- The axiom arm at `strict` is the strict arm. -/
theorem checkAxiomDeclC_strict (fe : FEnv md) (cv : ConstantVal md) :
    checkAxiomDeclC mode .strict fe cv = checkStdAxiomDeclC mode fe cv := rfl

/-- At `strict`, the step body is `annotStepC`. -/
theorem annotStepUnderC_strict (ev : Evidences md) (i : Nat) (fe : FEnv md)
    (pend : Array (PendingCheck md)) (pd : Declaration md) :
    annotStepUnderC mode .strict ev i fe pend pd = annotStepC mode ev i fe pend pd := by
  cases pd <;> rfl

/-- At `strict`, the step is `annotDeclStep`. -/
theorem annotDeclStepUnder_strict (ev : Evidences md) :
    annotDeclStepUnder mode .strict ev = annotDeclStep mode ev := by
  funext p pd s
  unfold annotDeclStepUnder annotDeclStep
  simp only [annotStepUnderC_strict]
  rfl

/-- **At `strict`, the fold is `checkDecls`**, so every theorem about the
certified fold is a theorem about `checkDeclsUnder _ .strict`. -/
theorem checkDeclsUnder_strict (ev : Evidences md) (ds : Array (Declaration md)) :
    checkDeclsUnder mode .strict ev ds = checkDecls mode ev ds := by
  unfold checkDeclsUnder checkDecls
  rw [annotDeclStepUnder_strict]

/-! ## Without user axioms, the policies agree

A policy is read only at an axiom's key. Two policies that admit the same
there take the same step (`annotDeclStepUnder_congr`), so over records none of
which is a user axiom (`userAxiomsOfDecls`, an eligible `.axiomDecl`) every
policy's fold is the strict one: `checkDeclsUnder_eq_checkDecls`. -/

/-- Two policies that admit the same at an axiom's key take the same step
body there, and every policy takes `annotStepC`'s at any other record. -/
theorem annotStepUnderC_congr {p₁ p₂ : AxiomPolicy} (ev : Evidences md) (i : Nat)
    (fe : FEnv md) (pend : Array (PendingCheck md)) (pd : Declaration md)
    (h : ∀ cv, pd = .axiomDecl cv → p₁.admits cv.name = p₂.admits cv.name) :
    annotStepUnderC mode p₁ ev i fe pend pd = annotStepUnderC mode p₂ ev i fe pend pd := by
  cases pd with
  | axiomDecl cv =>
    have hc : checkAxiomDeclStepC mode p₁ fe cv = checkAxiomDeclStepC mode p₂ fe cv := by
      unfold checkAxiomDeclStepC checkAxiomDeclC
      rw [h cv rfl]
    show (do pure (← checkAxiomDeclStepC mode p₁ fe cv, pend) :
        (CheckCM md) (FEnv md × Array (PendingCheck md))) =
      (do pure (← checkAxiomDeclStepC mode p₂ fe cv, pend))
    rw [hc]
  | _ => rfl

/-- The step, likewise. -/
theorem annotDeclStepUnder_congr {p₁ p₂ : AxiomPolicy} (ev : Evidences md)
    (p : Nat × FEnv md × Array (PendingCheck md)) (pd : Declaration md)
    (h : ∀ cv, pd = .axiomDecl cv → p₁.admits cv.name = p₂.admits cv.name) :
    annotDeclStepUnder mode p₁ ev p pd = annotDeclStepUnder mode p₂ ev p pd := by
  funext s
  unfold annotDeclStepUnder
  rw [annotStepUnderC_congr mode ev p.1 p.2.1 p.2.2 pd h]

/-- A record that is not a user axiom is admitted alike by every policy. -/
theorem admits_eq_of_userAxiom?_none {p₁ p₂ : AxiomPolicy} {pd : Declaration md}
    (h : pd.userAxiom? = none) :
    ∀ cv, pd = .axiomDecl cv → p₁.admits cv.name = p₂.admits cv.name := by
  intro cv hcv
  subst hcv
  have helig : cv.name.isCustomAxiomEligible = false := by
    cases he : cv.name.isCustomAxiomEligible with
    | false => rfl
    | true =>
      have hsome : (Declaration.axiomDecl cv).userAxiom? = some cv := by
        simp only [Declaration.userAxiom?, he, ↓reduceIte]
      rw [hsome] at h
      exact nomatch h
  rw [AxiomPolicy.admits_of_not_eligible p₁ helig, AxiomPolicy.admits_of_not_eligible p₂ helig]

/-- Folds over a list whose steps agree at every element agree. -/
theorem foldlM_stateT_congr {σ ε α β : Type} {f g : α → β → StateT σ (Except ε) α} :
    ∀ (l : List β), (∀ b ∈ l, ∀ a s, f a b s = g a b s) →
      ∀ (a : α) (s : σ), (l.foldlM f a) s = (l.foldlM g a) s
  | [], _, _, _ => rfl
  | b :: l, h, a, s => by
    have ih := foldlM_stateT_congr l (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
    simp only [List.foldlM_cons, Bind.bind, StateT.bind, h b List.mem_cons_self a s]
    cases g a b s with
    | error e => rfl
    | ok v =>
      obtain ⟨a', s'⟩ := v
      exact ih a' s'

/-- **T1: without user axioms, every policy's fold is the certified fold.**
When no record is a user axiom (`userAxiomsOfDecls ds.toList = []`), the fold
under any policy, `allowUser` included, is `checkDecls`: the same verdict, the
same environment, the same failure and position. -/
theorem checkDeclsUnder_eq_checkDecls (policy : AxiomPolicy) (ev : Evidences md)
    (ds : Array (Declaration md)) (hnone : userAxiomsOfDecls ds.toList = []) :
    checkDeclsUnder mode policy ev ds = checkDecls mode ev ds := by
  rw [← checkDeclsUnder_strict]
  have hstep : ∀ pd ∈ ds.toList, ∀ p s,
      annotDeclStepUnder mode policy ev p pd s = annotDeclStepUnder mode .strict ev p pd s := by
    intro pd hpd p s
    have hnot : pd.userAxiom? = none := by
      cases hu : pd.userAxiom? with
      | none => rfl
      | some cv =>
        have hmem : cv ∈ userAxiomsOfDecls ds.toList :=
          List.mem_filterMap.mpr ⟨pd, hpd, hu⟩
        rw [hnone] at hmem
        exact (List.not_mem_nil hmem).elim
    rw [annotDeclStepUnder_congr mode ev p pd (admits_eq_of_userAxiom?_none hnot)]
  have hfold : ∀ s, (ds.foldlM (annotDeclStepUnder mode policy ev) (0, mkFEnv Env.empty, #[])) s =
      (ds.foldlM (annotDeclStepUnder mode .strict ev) (0, mkFEnv Env.empty, #[])) s := by
    intro s
    rw [← Array.foldlM_toList, ← Array.foldlM_toList]
    exact foldlM_stateT_congr ds.toList hstep _ s
  unfold checkDeclsUnder
  rw [hfold]

/-- **T1 at the user-axiom fold**: with no user axiom among the records,
`checkDeclsWithUserAxioms` is `checkDecls`. -/
theorem checkDeclsWithUserAxioms_eq_checkDecls (ev : Evidences md)
    (ds : Array (Declaration md)) (hnone : userAxiomsOfDecls ds.toList = []) :
    checkDeclsWithUserAxioms mode ev ds = checkDecls mode ev ds :=
  checkDeclsUnder_eq_checkDecls mode .allowUser ev ds hnone

end Ix.Kernel.Cached
