import Ix.Cert.ChangedCone
import Ix.Cert.Quotient
import Ix.Cert.RoleClosure

/-! # Compiler correctness over quotient Source

The final statement of the certification (`CompileCorrect`). Its Source side is
quotient Source at the compiled artifact (`SourceAcceptsQ`): Lean with its alias
fibers collapsed, obtained per artifact from the executed quotient check
(`sourceAcceptsQ_of_check`). Its premises are, besides the compile's own report:

* the artifact's role binding and address map: every published role name sits at
  its role's address in the default table (`PublishedRolesBound`), and every
  published name agrees with the artifact's address map (`PublishedAgree`); both
  are decided on the artifact (`artifactCheck`);
* the pinned role configuration: the table's certificates check on their
  committed closure (`RoleClosure.RoleEvidenceChecks`, a closed proposition about
  the pinned data, decided once by `RoleClosure.roleEvidenceCheck`);
* one validation hypothesis per kind of change (`KindAccepted`), and the Source
  forms of the rewritten records inferring in their compiled closures
  (`SourceFormInfers`). The changed-cone validator discharges both on each
  compile (`ConeValidator.Sound`).

Its conclusion: the compiler published the closure, Ixon accepts the compiled
closure at the reference level, every constant of the closure, a dropped alias
included, reads as a compiled constant (`ReadingCovers`), and for every strong
model of the compiled environment there is one value model of quotient Source,
for the whole closure, all levels and valuations, in which every constant
denotes what its reading denotes (`CommutesStrong`).

On executed checks only (`CompileCorrect.checked`): the computed closure, the
quotient check, the compile with its checks and validator wired
(`compileValidated`), the role table's certificate check and the report's failures
give the conclusion, and with it `IxonCommutesStrongRef`.

The reading takes a role key's address from the role table (`readingAt`). The
older `reading` looks it up by the role's Lean name among the published names,
which misses a representative that the table rule makes a role key when no name
spelling the role's Lean name is published; the two agree wherever `reading` is
defined (`readingAt_of_reading`), so the conclusion gives
`IxonCommutesStrongRef` (`IxonCommutesCovering.toStrongRef`).

The statement is partial correctness: a closure quotient Source does not accept,
a compile that fails, a closure with a failed constant and a compile whose
checks or changed records fail are outside it. Nominal Source reaches it at the
instances where nominal and quotient Source agree (`CompileCorrect.nominal`). -/

namespace Ix.Cert

open Ix.Kernel (Env SetTheory)

universe w

/-! ## The reading at the role table -/

/-- **The address the artifact gives a quotient Source key**: an input key's
published address, by ingress name (`Ix.LeanIngress.sourceAddrs`, the map IxC
renames quotient Source by); a role key's address in the role table `t`, which the
reader keys by the role; none for a derived key. -/
def keyAddress (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) :
    Ix.Kernel.Key .source → Option Address
  | .id n => (Ix.LeanIngress.sourceAddrs ixe)[n]?
  | .role r => t.addressOf? r
  | .aux _ _ => none

/-- **The reading at the role table**: the compiled term the artifact reads the
quotient Source constant `c` as. That is the constant the reader keys `c`'s
address by (`keyAddress`), applied to `c`'s own level parameters by position. -/
def readingAt (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (cx : Ix.Kernel.Reader.Ctx .anon)
    (c : Ix.Kernel.ConstantInfo .source) : Option (Ix.Kernel.Expr .anon) := do
  let a ← keyAddress ixe t c.name
  let k ← (cx.keyAt a).toOption
  pure (.const k (c.toConstantVal.levelParams.map .param))

/-- **Reading totality and alias coverage.** Every constant `n` of the closure
`sub` has a constant in quotient Source's environment under its quotient key (its
alias fiber's representative, `quotientKey`); the artifact publishes `n` at the
address that representative reads at, so a dropped alias name reads as its
representative; and the representative has a reading. -/
def ReadingCovers (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (cx : Ix.Kernel.Reader.Ctx .anon)
    (sub : Ix.Environment) (envQ : Env .source) : Prop :=
  ∀ n ci, sub.consts.get? n = some ci →
    ∃ c ∈ envQ.consts, c.name = quotientKey ixe t n ∧
      keyAddress ixe t c.name = (ixe.named.get? n).map (·.addr) ∧
      (readingAt ixe t cx c).isSome = true

/-- **The compiled closure is accepted, read totally, and commutes**: Ixon accepts,
at the reference level, the compiled closure of the addresses `ixe` publishes for
`sub`, under the default role table, within some resource limits and in some order
that respects its references; in the reader's context of that run, every constant
of `sub` reads (`ReadingCovers`); and every strong model of the compiled environment
gives one value model of quotient Source's `envQ` through the reading
(`CommutesStrong`). -/
def IxonCommutesCovering (ixe : Ixon.Env) (sub : Ix.Environment) (t : Ix.Kernel.RoleTable)
    (envQ : Env .source) : Prop :=
  ∃ binding, Ix.Kernel.Admission.defaultBinding = .ok binding ∧
    ∃ limits order envA cx,
      IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA ∧
      admissionContext binding limits ixe order = some cx ∧
      CommutesStrong.{w} (readingAt ixe t cx) envQ envA ∧
      ReadingCovers ixe t cx sub envQ

/-! ## The statement -/

/-- **Compiler correctness, per root, over quotient Source.** Fix the default role
table `t`. Suppose quotient Source accepts the closure `sub` of `roots` in `env` at
the artifact `ixe`, grouped as the compiler groups it, installing `envQ`;
`compileReport env` returns `ixe` with `failures`; no constant of `sub` failed; the
published role names sit at the table's addresses, the published names agree with
the artifact's address map, and the table's certificates check; every kind of
change passes its validation hypothesis on `sub`; and the Source forms of the
rewritten records infer in their compiled closures. Then `ixe` publishes every
constant of `sub`, and the compiled closure is accepted, reads every constant of
`sub`, and commutes with `envQ` for every strong target model
(`IxonCommutesCovering`). -/
def CompileCorrect : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source),
    Ix.Kernel.Reader.defaultTable = .ok t →
    SourceAcceptsQ blocksOf env roots sub ixe t envQ →
    compileReport env = .ok (ixe, failures) →
    NoFailure failures sub →
    PublishedRolesBound t ixe →
    PublishedAgree ixe →
    RoleClosure.RoleEvidenceChecks →
    (∀ k, KindAccepted k env ixe sub) →
    SourceFormInfers env ixe sub t →
      Published ixe sub ∧ IxonCommutesCovering.{w} ixe sub t envQ

/-! ## The older reading -/

/-- **The two readings agree where the older one is defined**: when every published
name agrees with the artifact's address map and every published role name sits at
its role's address, a constant that `reading` reads is read alike by `readingAt`. -/
theorem readingAt_of_reading {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {cx : Ix.Kernel.Reader.Ctx .anon} (agree : PublishedAgree ixe) (bound : PublishedRolesBound t ixe)
    {c : Ix.Kernel.ConstantInfo .source} {e : Ix.Kernel.Expr .anon} (h : reading ixe cx c = some e) :
    readingAt ixe t cx c = some e := by
  have address : ∀ a, publishedAddress ixe c.name = some a → keyAddress ixe t c.name = some a := by
    intro a hp
    cases hk : c.name with
    | id n =>
      rw [hk] at hp
      unfold publishedAddress at hp
      obtain ⟨⟨m, d⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp hp
      have found := List.find?_some hf
      have inside := List.mem_of_find?_eq_some hf
      simp only [Ix.LeanIngress.nameIs, Bool.and_eq_true] at found
      have hn := (nameIsName_iff m n).mp found.1
      show (Ix.LeanIngress.sourceAddrs ixe)[n]? = some d.addr
      rw [← hn]
      exact agree m d inside
    | role r =>
      rw [hk] at hp
      exact publishedAddress_role bound hp
    | aux k d =>
      rw [hk] at hp
      unfold publishedAddress at hp
      have none : (ixe.named.toList.find? fun (p : Ix.Name × Ixon.Named) =>
          Ix.LeanIngress.nameIs p.1 (.aux k d)) = none :=
        List.find?_eq_none.mpr fun _ _ => by simp [Ix.LeanIngress.nameIs]
      rw [none] at hp
      cases hp
  unfold reading at h
  unfold readingAt
  cases hp : publishedAddress ixe c.name with
  | none => rw [hp] at h; cases h
  | some a =>
    rw [hp] at h
    rw [address a hp]
    exact h

/-- **The conclusion gives the strong reference commutation** with the older
reading, when every published name agrees with the artifact's address map. -/
theorem IxonCommutesCovering.toStrongRef {ixe : Ixon.Env} {sub : Ix.Environment}
    {t : Ix.Kernel.RoleTable} {envQ : Env .source} (agree : PublishedAgree ixe)
    (bound : PublishedRolesBound t ixe) (h : IxonCommutesCovering.{w} ixe sub t envQ) :
    IxonCommutesStrongRef.{w} ixe sub envQ := by
  obtain ⟨binding, pinned, limits, order, envA, cx, accepted, context, values, -⟩ := h
  refine ⟨binding, pinned, limits, order, envA, cx, accepted, context, ?_⟩
  intro V _ M
  obtain ⟨N, hN⟩ := values V M
  exact ⟨N, fun c hc e he φ ρ => hN c hc e (readingAt_of_reading agree bound he) φ ρ⟩

/-! ## The statement on the artifact

With coverage proved (`compileCovers`), the statement hypothesised on the report
(`NoFailure`) and the one hypothesised on the artifact (`Published`) are
equivalent. -/

/-- The statement hypothesised on `Published` instead of `NoFailure`. -/
def CompileCorrectPublished : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (t : Ix.Kernel.RoleTable) (envQ : Env .source),
    Ix.Kernel.Reader.defaultTable = .ok t →
    SourceAcceptsQ blocksOf env roots sub ixe t envQ →
    compile env = .ok ixe →
    Published ixe sub →
    PublishedRolesBound t ixe →
    PublishedAgree ixe →
    RoleClosure.RoleEvidenceChecks →
    (∀ k, KindAccepted k env ixe sub) →
    SourceFormInfers env ixe sub t →
      IxonCommutesCovering.{w} ixe sub t envQ

/-- Under `CompileCovers`, `CompileCorrect` gives the statement hypothesised on
`Published`: the closure is published, so none of it failed. -/
theorem CompileCorrect.published (hcov : CompileCovers) (h : CompileCorrect.{w}) :
    CompileCorrectPublished.{w} := by
  intro env roots sub ixe t envQ table hs hc hp bound agree evidence kinds forms
  obtain ⟨failures, hr⟩ := compile_eq_ok.mp hc
  refine (h env roots sub ixe failures t envQ table hs hr (fun n ci hn => ?_) bound agree evidence
    kinds forms).2
  exact (hcov env ixe failures hr n ci (hs.1.mem_env hn)).mp (hp n ci hn)

/-- Under `CompileCovers`, the statement hypothesised on `Published` gives
`CompileCorrect`: a closure none of whose constants failed is published. -/
theorem CompileCorrect.of_published (hcov : CompileCovers) (h : CompileCorrectPublished.{w}) :
    CompileCorrect.{w} := by
  intro env roots sub ixe failures t envQ table hs hr hf bound agree evidence kinds forms
  have hp : Published ixe sub := fun n ci hn =>
    (hcov env ixe failures hr n ci (hs.1.mem_env hn)).mpr (hf n ci hn)
  exact ⟨hp, h env roots sub ixe t envQ table hs (compile_eq_ok.mpr ⟨failures, hr⟩) hp bound
    agree evidence kinds forms⟩

/-- **`CompileCorrect` on the report is `CompileCorrect` on the artifact**. -/
theorem compileCorrect_iff_published : CompileCorrect.{w} ↔ CompileCorrectPublished.{w} :=
  ⟨CompileCorrect.published compileCovers, CompileCorrect.of_published compileCovers⟩

/-! ## With the checks wired -/

/-- **The statement for the validated compile**: with the artifact checks and a
sound changed-cone validator wired after `compileReport` (`compileValidated`), the
artifact's role binding and address map and the validation hypotheses hold by
construction, and only the Source side, the report's failures and the pinned role
configuration remain. -/
theorem CompileCorrect.validated (h : CompileCorrect.{w}) {v : ConeValidator} (sound : v.Sound)
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Env .source}
    (table : Ix.Kernel.Reader.defaultTable = .ok t)
    (source : SourceAcceptsQ blocksOf env roots sub ixe t envQ)
    (compiled : compileValidated v t env = .ok (ixe, failures))
    (none : NoFailure failures sub) (evidence : RoleClosure.RoleEvidenceChecks) :
    Published ixe sub ∧ IxonCommutesCovering.{w} ixe sub t envQ ∧ PublishedRolesBound t ixe ∧
      PublishedAgree ixe := by
  obtain ⟨report, checked, passed⟩ := compileValidated_ok compiled
  obtain ⟨bound, agree⟩ := artifactCheck_sound checked
  obtain ⟨kinds, forms⟩ := sound env ixe failures report passed roots sub t source.1 table
  exact ⟨(h env roots sub ixe failures t envQ table source report none bound agree evidence kinds
    forms).1, (h env roots sub ixe failures t envQ table source report none bound agree evidence
    kinds forms).2, bound, agree⟩

/-- **The statement on executed checks.** Take the computed closure of `roots`
(`closure`, correct by `closureCorrect`), the default role table, the executed
quotient check of that closure at the artifact, the compile with its artifact checks
and a sound changed-cone validator wired (`compileValidated`), the role table's
certificate check run once (`RoleClosure.roleEvidenceCheck`) and the report's
failures, decided on the closure. Then the closure is published, its compiled
closure is accepted, reads every constant of the closure and commutes with quotient
Source for every strong target model, and it does so with the older reading too
(`IxonCommutesStrongRef`). The set theory `V` is what the checks' refinement walks
run in; the conclusion quantifies over every one. -/
theorem CompileCorrect.checked (h : CompileCorrect.{w}) (V : Type w) [SetTheory V]
    {v : ConeValidator} (sound : v.Sound) (evidence : RoleClosure.roleEvidenceCheck = true)
    {env : Ix.Environment} {roots : List Ix.Name} {ixe : Ixon.Env} {failures : Failures}
    {t : Ix.Kernel.RoleTable} {envQ : Env .source}
    (table : Ix.Kernel.Reader.defaultTable = .ok t)
    (quotient : Ix.LeanIngress.checkSourceCollapsedBundledAt ixe t (closure env roots)
      (blocksOf (closure env roots)) = .ok envQ)
    (compiled : compileValidated v t env = .ok (ixe, failures))
    (none : ((closure env roots).consts.keys.all fun n => !failures.failed n) = true) :
    Published ixe (closure env roots) ∧ IxonCommutesCovering.{w} ixe (closure env roots) t envQ ∧
      IxonCommutesStrongRef.{w} ixe (closure env roots) envQ := by
  have source := sourceAcceptsQ_of_check V (closureCorrect env roots) quotient
  obtain ⟨published, covering, bound, agree⟩ := h.validated sound table source compiled
    ((noFailure_iff failures _).mpr none) (RoleClosure.roleEvidenceChecks_of_check V evidence)
  exact ⟨published, covering, covering.toStrongRef agree bound⟩

/-! ## Nominal Source -/

/-- **Nominal Source, at the instances where it agrees with quotient Source**
(`NominalQuotientAgreeAt`): if nominal Source accepts the closure and the instance
link holds, quotient Source accepts it, and the conclusion holds of the quotient
environment. Where the link fails (the deliberately aliased fixtures of
`NominalQuotientAgreeAt`), this says nothing. -/
theorem CompileCorrect.nominal (h : CompileCorrect.{w}) {env : Ix.Environment}
    {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {t : Ix.Kernel.RoleTable} {envS : Env .source}
    (table : Ix.Kernel.Reader.defaultTable = .ok t)
    (agreeAt : NominalQuotientAgreeAt env roots sub ixe t)
    (nominal : SourceAccepts blocksOf env roots sub envS)
    (compiled : compileReport env = .ok (ixe, failures)) (none : NoFailure failures sub)
    (bound : PublishedRolesBound t ixe) (agree : PublishedAgree ixe)
    (evidence : RoleClosure.RoleEvidenceChecks)
    (kinds : ∀ k, KindAccepted k env ixe sub) (forms : SourceFormInfers env ixe sub t) :
    ∃ envQ, SourceAcceptsQ blocksOf env roots sub ixe t envQ ∧
      Published ixe sub ∧ IxonCommutesCovering.{w} ixe sub t envQ := by
  obtain ⟨envQ, quotient⟩ := agreeAt envS nominal
  exact ⟨envQ, quotient, h env roots sub ixe failures t envQ table quotient compiled none bound
    agree evidence kinds forms⟩

end Ix.Cert
