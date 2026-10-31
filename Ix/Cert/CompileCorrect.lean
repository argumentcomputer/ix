import Ix.Cert.StrongCommutation
import Ix.LeanIngress.Rename
import Ix.Cert.EvidenceCheck
import Ix.Cert.Quotient
import Ix.Cert.RoleClosure
import Ix.Cert.Closure

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
  the pinned data, decided once by `RoleClosure.roleEvidenceCheck`).

Its conclusion: the compiler published the closure, Ixon accepts the compiled
closure at the reference level, the environment Ixon installs from it is quotient
Source's environment with its names renamed injectively to the artifact's addresses,
every constant reading as its own renamed key (`RenamesSource`: the same types and
values, theorem statements and proofs included), every constant of the closure, a
dropped alias included, reads as a compiled constant, except the constants represented
by the inert `sorryAx` role (`sorryAx` and the axioms α-equal to it)
(`ReadingCovers`), and for every strong
model of the compiled environment there is one value model of quotient Source,
for the whole closure, all levels and valuations, in which every constant
denotes what its reading denotes (`CommutesStrong`).

On executed checks only (`CompileCorrect.checked`): the computed closure, the
quotient check, the compile with its checks wired (`compileChecked`), the role
table's certificate check and the report's failures give the conclusion, and with it `IxonCommutesStrongRef`.

The reading takes a role key's address from the role table (`readingAt`). The
older `reading` looks it up by the role's Lean name among the published names,
which misses a representative that the table rule makes a role key when no name
spelling the role's Lean name is published; the two agree wherever `reading` is
defined (`readingAt_of_reading`), so the conclusion gives
`IxonCommutesStrongRef` (`IxonCommutesCovering.toStrongRef`).

The statement is partial correctness: a closure quotient Source does not accept,
a compile that fails, a closure with a failed constant and a compile whose
checks fail are outside it. Nominal Source reaches it at the
instances where nominal and quotient Source agree (`CompileCorrect.nominal`). -/

namespace Ix.Cert

open Ix.Kernel (Env SetTheory)

universe w

/-! ## The reading at the role table -/

/-- **The quotient key of an input name**: its ingress key, renamed onto its
alias fiber's representative under the table rule (`Ix.LeanIngress.fiberAliasAt`
at the table `t`'s inverse), as quotient Source keys it. -/
def quotientKey (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (n : Ix.Name) : Ix.Kernel.Key .source :=
  Ix.LeanIngress.Key.subst (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
    (Ix.LeanIngress.ingressKey n)

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
`sub`, under the name `sub` stores it under, has a constant in quotient Source's
environment under its quotient key (its alias fiber's representative,
`quotientKey`); the artifact publishes `n` at the address that representative
reads at, so a dropped alias name reads as its representative; and the
representative has a reading.

The names are the stored ones (`(n, ci) ∈ sub.consts.toList`), not every name a
lookup answers: `Ix.Name`'s `==` compares stored hashes only, so a lookup of `sub`
also answers every respelling of a stored name that keeps its hash, and the quotient
key reads the spelling. Quantified over those, the coverage would need a published
name for each of infinitely many spellings, and fails at every instance whose closure
is not empty.

The constants represented by `sorryAx`'s role (`quotientKey ixe t n =
Ix.Kernel.sorryAxName`) are left out: the checker accepts their declaration and, by
design, installs nothing for it (an inert role), so neither side has a constant for
them, and this statement says nothing about any constant the artifact publishes at
`sorryAx`'s role address. These are `sorryAx` itself and any axiom α-equal to it, such
as `axiom myAx (α : Sort u) (synthetic := false) : α`, which compiles to `sorryAx`'s
record and so is represented by its role. Any use of one is declined. -/
def ReadingCovers (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (cx : Ix.Kernel.Reader.Ctx .anon)
    (sub : Ix.Environment) (envQ : Env .source) : Prop :=
  ∀ n ci, (n, ci) ∈ sub.consts.toList → quotientKey ixe t n ≠ Ix.Kernel.sorryAxName →
    ∃ c ∈ envQ.consts, c.name = quotientKey ixe t n ∧
      keyAddress ixe t c.name = (ixe.named.get? n).map (·.addr) ∧
      (readingAt ixe t cx c).isSome = true

/-- **The compiled closure is quotient Source, renamed.** Let `f` be the renaming of
quotient Source's names to the artifact's addresses (`Ix.LeanIngress.evAddr` at the
committed quotient bundle `b`: a name the artifact publishes goes to its published address,
a name only the bundle holds to its bundle address). Then:

* `f` is injective on every name `envQ` mentions, and the environment `envA` that Ixon's
  check installs from the compiled closure is exactly `envQ` with every name renamed by `f`
  (`Ix.Kernel.EnvRel`): the same constants in the same order, each with the same type, the
  same value (a definition's, and a theorem's proof), the same inductive, constructor and
  recursor data, and nothing added or dropped;
* every constant `c` of quotient Source reads (`readingAt`, in the reader's context `cx`) as
  its own renamed key `f c.name` at its own level parameters, and `envA` holds `c` renamed
  there.

This is the syntactic half of correctness, and it needs no model. A compiler that published
`theorem foo : True := trivial` for Lean's `theorem foo : 2 + 2 = 4 := rfl` would install a
theorem whose type is `True`, which is not `2 + 2 = 4` renamed. `CommutesStrong` alone does
not exclude that: a proposition denotes a truth value and every proof denotes the proof
point, so it only says that the source statement holds in the model.

Why this form. It is the strongest fact the proof already holds: the composition obtains it
from the reader's streams (`Obligation.ReaderStreams`: the reader's prepared declarations are
quotient Source's, renamed by `f`) through the renamed Source run, and its reading clause from
the reader's keys (`Obligation.ReadingKeys`). It is stated over the installed environment
rather than the reader's declaration stream because that environment is what the acceptance
conjunct (`IxonAcceptsRef`) and the commutation conjunct read, and the stream would put the
reader's prelude and preparation into the statement. "Quotient Source" is Lean's constants
ingressed, renamed onto their alias fibers and lowered by IxC's reader
(`Ix.Kernel.Reader.lowerInductive`, `lowerDefinition`), so the equality is with that lowering,
not with Lean's kernel objects themselves. -/
def RenamesSource (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (cx : Ix.Kernel.Reader.Ctx .anon)
    (envQ : Env .source) (envA : Env .anon) : Prop :=
  ∃ b, Ix.RoleEvidence.quotientBundle () = .ok b ∧
    Ix.Kernel.EnvRel
      (fun n => Ix.LeanIngress.QRepAt ixe (Ix.LeanIngress.roleAtMap t) n ∨
        Ix.LeanIngress.BundleOnly ixe b n)
      (Ix.LeanIngress.evAddr ixe b) envQ envA ∧
    ∀ c ∈ envQ.consts, ∀ e, readingAt ixe t cx c = some e →
      e = .const (c.name.map (Ix.LeanIngress.evAddr ixe b)) (c.toConstantVal.levelParams.map .param) ∧
      envA.find? (c.name.map (Ix.LeanIngress.evAddr ixe b)) =
        some (c.mapKeys (Ix.LeanIngress.evAddr ixe b))

/-- **The compiled closure is accepted, is quotient Source renamed, is read totally, and
commutes**: Ixon accepts, at the reference level, the compiled closure of the addresses `ixe`
publishes for `sub`, under the default role table, within some resource limits and in some
order that respects its references; the environment it installs is quotient Source's `envQ`
renamed to the artifact's addresses, every constant reading as its renamed key
(`RenamesSource`); in the reader's context of that run, every constant of `sub` reads
(`ReadingCovers`); and every strong model of the compiled environment gives one value model
of quotient Source's `envQ` through the reading (`CommutesStrong`). -/
def IxonCommutesCovering (ixe : Ixon.Env) (sub : Ix.Environment) (t : Ix.Kernel.RoleTable)
    (envQ : Env .source) : Prop :=
  ∃ binding, Ix.Kernel.Admission.defaultBinding = .ok binding ∧
    ∃ limits order envA cx,
      IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA ∧
      admissionContext binding limits ixe order = some cx ∧
      RenamesSource ixe t cx envQ envA ∧
      CommutesStrong.{w} (readingAt ixe t cx) envQ envA ∧
      ReadingCovers ixe t cx sub envQ

/-! ## The artifact's role binding and address map

Two facts the final statement reads off the artifact are decided on it, with
proved deciders (`Ix.Cert.publishedRolesBound_iff`, `Ix.Cert.publishedAgree_iff`):
every published role name sits at its role's address in the default role table,
and every published name agrees with the artifact's address map (two published
names with one ingress name share an address). The checked compile
(`compileChecked`) runs them after `compileReport`. An input that holds a
constant under a role's Lean name with other content is refused there. A third check, on the artifact and the committed
role data, makes quotient Source's evidence bundle the role table's evidence there
(`Ix.Cert.EvidenceCheck.evidenceCheck`, sound by `evidenceCheck_sound`). -/

/-- **The artifact checks** at the role table `t`: every published role name sits
at its role's address (`publishedRolesBound`), every published name agrees with
the artifact's address map (`publishedAgree`), and quotient Source's evidence bundle
agrees with the role table's evidence on the artifact (`EvidenceCheck.evidenceCheck`). -/
def artifactCheck (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) : Except String Unit :=
  if publishedRolesBound t ixe then
    if publishedAgree ixe then EvidenceCheck.evidenceCheck t ixe
    else .error "artifact check: two published names with one ingress name are at different addresses"
  else
    .error "artifact check: a published role name is not at its role's address in the role table"

/-- **The artifact checks are sound**: their success gives the three facts. -/
theorem artifactCheck_sound {t : Ix.Kernel.RoleTable} {ixe : Ixon.Env}
    (h : artifactCheck t ixe = .ok ()) :
    PublishedRolesBound t ixe ∧ PublishedAgree ixe ∧ EvidenceCheck.EvidenceAgrees t ixe := by
  unfold artifactCheck at h
  split at h
  · rename_i hb
    split at h
    · rename_i ha
      exact ⟨(publishedRolesBound_iff t ixe).mp hb, (publishedAgree_iff ixe).mp ha,
        EvidenceCheck.evidenceAgrees_of_check h⟩
    · cases h
  · cases h

/-- **The compile with its checks wired**, at the role table `t` (the default one,
`Ix.Kernel.Reader.defaultTable`, where a statement fixes it): `compileReport`, then
the artifact checks (`artifactCheck`); a failure of the checks is the compile's. -/
def compileChecked (t : Ix.Kernel.RoleTable) (env : Ix.Environment) :
    Except String (Ixon.Env × Failures) := do
  let out ← compileReport env
  artifactCheck t out.1
  pure out

/-- A checked compile is a `compileReport` result that the artifact checks passed. -/
theorem compileChecked_ok {t : Ix.Kernel.RoleTable} {env : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} (h : compileChecked t env = .ok (ixe, failures)) :
    compileReport env = .ok (ixe, failures) ∧ artifactCheck t ixe = .ok () := by
  have e : compileChecked t env = Except.bind (compileReport env) fun out =>
      Except.bind (artifactCheck t out.1) fun _ => Except.ok out := rfl
  rw [e] at h
  cases hr : compileReport env with
  | error err => rw [hr] at h; cases h
  | ok out =>
    rw [hr] at h
    change Except.bind (artifactCheck t out.1) (fun _ => Except.ok out) = Except.ok (ixe, failures) at h
    cases hc : artifactCheck t out.1 with
    | error err => rw [hc] at h; cases h
    | ok u =>
      rw [hc] at h
      change Except.ok out = Except.ok (ixe, failures) at h
      cases h
      cases u
      exact ⟨rfl, hc⟩

/-! ## The statement -/

/-- **Compiler correctness, per root, over quotient Source.** Fix the default role
table `t`. Suppose quotient Source accepts the closure `sub` of `roots` in `env` at
the artifact `ixe`, grouped as the compiler groups it, installing `envQ`;
`compileReport env` returns `ixe` with `failures`; no constant of `sub` failed; the
published role names sit at the table's addresses, the published names agree with
the artifact's address map, quotient Source's evidence bundle agrees with the table's
evidence on the artifact (`EvidenceCheck.EvidenceAgrees`); and the table's certificates
check. Then `ixe` publishes every
constant of `sub`, and the compiled closure is accepted, installs `envQ` renamed to the
artifact's addresses, with every type and value its source's (`RenamesSource`), reads every
constant of `sub`, and commutes with `envQ` for every strong target model
(`IxonCommutesCovering`).

The renaming conjunct is what ties each compiled statement to its source statement; the
commutation conjunct alone could not, since propositions denote truth values. It holds
without any model or set theory. The commutation conjunct quantifies over every set theory
`V` with a strong model, which Lean cannot construct: it says something only in a
metatheory with such a `V`. -/
def CompileCorrect : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source),
    Ix.Kernel.Reader.defaultTable = .ok t →
    SourceAcceptsQ blocksOf env roots sub ixe t envQ →
    compileReport env = .ok (ixe, failures) →
    NoFailure failures sub →
    PublishedRolesBound t ixe →
    PublishedAgree ixe →
    EvidenceCheck.EvidenceAgrees t ixe →
    RoleClosure.RoleEvidenceChecks →
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
  obtain ⟨binding, pinned, limits, order, envA, cx, accepted, context, -, values, -⟩ := h
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
    EvidenceCheck.EvidenceAgrees t ixe →
    RoleClosure.RoleEvidenceChecks →
      IxonCommutesCovering.{w} ixe sub t envQ

/-- Under `CompileCovers`, `CompileCorrect` gives the statement hypothesised on
`Published`: the closure is published, so none of it failed. -/
theorem CompileCorrect.published (hcov : CompileCovers) (h : CompileCorrect.{w}) :
    CompileCorrectPublished.{w} := by
  intro env roots sub ixe t envQ table hs hc hp bound agree quotient evidence
  obtain ⟨failures, hr⟩ := compile_eq_ok.mp hc
  refine (h env roots sub ixe failures t envQ table hs hr (fun n ci hn => ?_) bound agree quotient evidence).2
  exact (hcov env ixe failures hr n ci (hs.1.mem_env hn)).mp (hp n ci hn)

/-- Under `CompileCovers`, the statement hypothesised on `Published` gives
`CompileCorrect`: a closure none of whose constants failed is published. -/
theorem CompileCorrect.of_published (hcov : CompileCovers) (h : CompileCorrectPublished.{w}) :
    CompileCorrect.{w} := by
  intro env roots sub ixe failures t envQ table hs hr hf bound agree quotient evidence
  have hp : Published ixe sub := fun n ci hn =>
    (hcov env ixe failures hr n ci (hs.1.mem_env hn)).mpr (hf n ci hn)
  exact ⟨hp, h env roots sub ixe t envQ table hs (compile_eq_ok.mpr ⟨failures, hr⟩) hp bound
    agree quotient evidence⟩

/-- **`CompileCorrect` on the report is `CompileCorrect` on the artifact**. -/
theorem compileCorrect_iff_published : CompileCorrect.{w} ↔ CompileCorrectPublished.{w} :=
  ⟨CompileCorrect.published compileCovers, CompileCorrect.of_published compileCovers⟩

/-! ## With the checks wired -/

/-- **The statement for the checked compile**: with the artifact checks wired
after `compileReport` (`compileChecked`), the artifact's role binding and address
map hold by construction, and only the Source side, the report's failures and the
pinned role configuration remain. -/
theorem CompileCorrect.artifactChecked (h : CompileCorrect.{w})
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Env .source}
    (table : Ix.Kernel.Reader.defaultTable = .ok t)
    (source : SourceAcceptsQ blocksOf env roots sub ixe t envQ)
    (compiled : compileChecked t env = .ok (ixe, failures))
    (none : NoFailure failures sub) (evidence : RoleClosure.RoleEvidenceChecks) :
    Published ixe sub ∧ IxonCommutesCovering.{w} ixe sub t envQ ∧ PublishedRolesBound t ixe ∧
      PublishedAgree ixe := by
  obtain ⟨report, checked⟩ := compileChecked_ok compiled
  obtain ⟨bound, agree, quotient⟩ := artifactCheck_sound checked
  obtain ⟨published, covering⟩ :=
    h env roots sub ixe failures t envQ table source report none bound agree quotient evidence
  exact ⟨published, covering, bound, agree⟩

/-- **The statement on executed checks.** Take the computed closure of `roots`
(`closure`, correct by `closureCorrect`), the default role table, the executed
quotient check of that closure at the artifact, the compile with its artifact checks
wired (`compileChecked`), the role table's certificate check run once
(`RoleClosure.roleEvidenceCheck`) and the report's failures, decided on the closure.
Then the closure is published, its compiled closure is accepted, reads every
constant of the closure and commutes with quotient Source for every strong target
model, and it does so with the older reading too (`IxonCommutesStrongRef`). The set
theory `V` is what the checks' refinement walks run in; the conclusion quantifies
over every one. -/
theorem CompileCorrect.checked (h : CompileCorrect.{w}) (V : Type w) [SetTheory V]
    (evidence : RoleClosure.roleEvidenceCheck = true)
    {env : Ix.Environment} {roots : List Ix.Name} {ixe : Ixon.Env} {failures : Failures}
    {t : Ix.Kernel.RoleTable} {envQ : Env .source}
    (table : Ix.Kernel.Reader.defaultTable = .ok t)
    (quotient : Ix.LeanIngress.checkSourceCollapsedBundledAt ixe t (closure env roots)
      (blocksOf (closure env roots)) = .ok envQ)
    (compiled : compileChecked t env = .ok (ixe, failures))
    (none : ((closure env roots).consts.keys.all fun n => !failures.failed n) = true) :
    Published ixe (closure env roots) ∧ IxonCommutesCovering.{w} ixe (closure env roots) t envQ ∧
      IxonCommutesStrongRef.{w} ixe (closure env roots) envQ := by
  have source := sourceAcceptsQ_of_check V (closureCorrect env roots) quotient
  obtain ⟨published, covering, bound, agree⟩ := h.artifactChecked table source compiled
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
    (evidenceAgrees : EvidenceCheck.EvidenceAgrees t ixe) (evidence : RoleClosure.RoleEvidenceChecks) :
    ∃ envQ, SourceAcceptsQ blocksOf env roots sub ixe t envQ ∧
      Published ixe sub ∧ IxonCommutesCovering.{w} ixe sub t envQ := by
  obtain ⟨envQ, quotient⟩ := agreeAt envS nominal
  exact ⟨envQ, quotient, h env roots sub ixe failures t envQ table quotient compiled none bound
    agree evidenceAgrees evidence⟩

end Ix.Cert
