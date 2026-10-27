import Ix.Cert.CompileCorrect
import Ix.Cert.HookFree
import Ix.Cert.Stream
import IxC.Kernel.Verify.Rename.UnionFold

/-! # The final statement composed from its open obligations

`CompileCorrect` is proved here from named hypotheses, each a `def … : Prop` stated
on the compiler's actual objects (`compileReport`, the driver's fold, the certified
reader, quotient Source's prepared stream), one per open obligation:

1. `Obligation.SourceTotal`: quotient Source drops nothing; every constant of the
   closure has its representative installed, at the address it is published at.
2. The reader against the Source stream:
   * `Obligation.ReaderStreams`: a closure that avoids the changed set reads, record by
     record, as quotient Source's prepared stream renamed to the artifact's addresses,
     in another order;
   * `Obligation.ReadingKeys`: the reader keys every representative as its renaming;
   * `Obligation.RenamedAgree`: a constant the compiler did not rewrite reads as its
     renamed self in every strong model of the compiled environment.
3. `Obligation.ScheduleOwnership`: every state the fold reaches resolves and stores as
   the artifact publishes.
4. `Obligation.PassValues`: a rewritten record (call sites, regenerated auxiliaries,
   image definitions) denotes what its renamed Source form denotes.
5. `Obligation.ImageRules`: the value-level rules of an imaged Source recursor hold at the
   compiled values, from the image computation-rule rows the checker verifies.
6. `Obligation.CliqueRows`: a transported clique member denotes its Source value, by its
   row.
7. Locality: `Obligation.ReorderAccepts` (a closed reordering of an accepted stream is
   accepted), `Obligation.EvidenceTransfer` (the role table's evidence passes where the
   bundle's does), `Obligation.SeedUnion` (accepted seed closures union),
   `Obligation.SourceRestricts` (an unaffected constant lies in an accepted closure that
   avoids the changed set), `Obligation.RootRestricts` (a seed of an accepted closure has
   an accepted closure).
8. `Obligation.Assembly`: per-constant agreement and the laws at the compiled values give
   one Source model with the laws.
9. The laws, at the level of values (`Ix.Cert.SourceLaws`): `Obligation.UnchangedRules` (a
   renamed environment's strong model gives the Source laws) and
   `Obligation.RuleCorrespondence` (the Source laws of recursors that are not imaged, and
   the capability laws, hold at the compiled values).

**The unchanged-closure case** (`compileCorrect_unchanged`) uses obligations 1, 2
(streams and keys), 3, 7 (reordering and evidence) and `UnchangedRules`, with the
existing leaves: the unchanged-closure claims (`HookFree.compileReport_hookFree`), the
renamed quotient Source run (`Ix.LeanIngress.acceptsRef_prepareSourceCollapsedAt`),
the reader's preparation (`Stream.closure_prepares`), coverage (`compileCovers`) and the
pulled-back value model (`ValueModel.pullback`, `ValueRows.ofStrong`).

**The general case** (`compileCorrect_of_obligations`) splits the closure's seeds into the
changed set's roots, accepted by the validation hypotheses (`KindAccepted`), and the
unaffected ones, accepted through the unchanged case; it unions them, and assembles the
Source model from the per-kind agreements. -/

namespace Ix.Cert

open Ix.Kernel (Env SetTheory Denotes LevelParam BVarIdx)
open Ix.Compile.ChangedSet (ChangedSet Cause)

universe w

/-! ## Shared notions -/

/-- **The final statement's premises at one instance**, the validation hypotheses aside. -/
structure Premises (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment)
    (ixe : Ixon.Env) (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source) : Prop where
  table : Ix.Kernel.Reader.defaultTable = .ok t
  source : SourceAcceptsQ blocksOf env roots sub ixe t envQ
  compiled : compileReport env = .ok (ixe, failures)
  none : NoFailure failures sub
  bound : PublishedRolesBound t ixe
  agree : PublishedAgree ixe
  evidence : RoleClosure.RoleEvidenceChecks

/-- **The final statement in the unchanged-closure case**: its conclusion, for a closure
that meets no constant of the changed set. -/
def CompileCorrectUnchanged : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source),
    Premises env roots sub ixe failures t envQ → (changedSetOf env ixe).Avoids sub →
      Published ixe sub ∧ IxonCommutesCovering.{w} ixe sub t envQ

/-- Quotient Source's evidence: the pinned bundle's, renamed onto the representatives. -/
def sourceEvidence (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) : Ix.Kernel.Evidences .source :=
  Ix.LeanIngress.evidenceSubst (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
    (Ix.RoleEvidence.bundleEvidence ())

/-- The reader's context of the compiled closure in `order`, under the table `tA` behind
the prelude `preA` (`Ix.Kernel.Admission.streamContext` at the admission hash). -/
def closureContext (ixe : Ixon.Env) (tA : Ix.Kernel.RoleTable) (preA : Ix.Kernel.Reader.Prelude .anon)
    (order : List Address) : Ix.Kernel.Reader.Ctx .anon :=
  Ix.Kernel.Admission.streamContext Address.admissionHash tA preA (Stream.decodedOf ixe order)
    (blobsOf ixe order) (hintsOf ixe)

/-- **Two environments install the same constants**, and answer every lookup alike. -/
structure SameEnv {md : Ix.Kernel.Mode} (e e' : Env md) : Prop where
  mem : ∀ c, c ∈ e.consts ↔ c ∈ e'.consts
  find : ∀ k, e.find? k = e'.find? k

/-- **Two terms denote one set**: at every level assignment and variable valuation, both
denote, and denote the same set. -/
def DenoteSame {md : Ix.Kernel.Mode} {V : Type w} [SetTheory V]
    (cval : Ix.Kernel.Key md → (LevelParam → Nat) → V) (env : Env md) (e e' : Ix.Kernel.Expr md) : Prop :=
  ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), ∃ X, Denotes cval env φ ρ e X ∧ Denotes cval env φ ρ e' X

/-- An input or role key: not a derived (generated) one. -/
def InputKey {md : Ix.Kernel.Mode} : Ix.Kernel.Key md → Prop
  | .aux _ _ => False
  | _ => True

/-- **A quotient Source constant agrees with the compiled environment under the renaming
`f`**, in the strong model `M`: the compiled environment holds a constant under the
renamed key, with the same level parameters, whose type denotes as the renamed type does,
and, for a definition, a definition whose value denotes as the renamed value does. -/
def ConstantAgrees {V : Type w} [SetTheory V] {envA : Env .anon} (M : Ix.Kernel.Cached.StrongModel V envA)
    (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon) (c : Ix.Kernel.ConstantInfo .source) : Prop :=
  ∃ c', envA.find? (c.name.map f) = some c' ∧
    c'.toConstantVal.levelParams = c.toConstantVal.levelParams ∧
    DenoteSame M.model.cval envA (c.toConstantVal.type.mapKeys f) c'.toConstantVal.type ∧
    ∀ cv v h, c = .defnInfo cv v h →
      ∃ cv' v' h', c' = .defnInfo cv' v' h' ∧ DenoteSame M.model.cval envA (v.mapKeys f) v'

/-- **The value-level recursor rules of `envQ` at the recursors `R` hold at the values
`M` gives the renamed keys** (`RecRuleLaw` at `Ix.Kernel.pullCval f M.model.cval`). -/
def RecLawsAgree {V : Type w} [SetTheory V] {envA : Env .anon} (M : Ix.Kernel.Cached.StrongModel V envA)
    (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon) (envQ : Env .source)
    (R : Ix.Kernel.Key .source → Prop) : Prop :=
  ∀ (c : Ix.Kernel.Key .source) (cv : Ix.Kernel.ConstantVal .source) (mI rP : Nat)
    (rules : List (Ix.Kernel.RecRule .source)),
    envQ.find? c = some (.recInfo cv mI rP rules) → R c → ∀ rl ∈ rules, rl.fire ≠ .inert →
      RecRuleLaw (Ix.Kernel.pullCval f M.model.cval) envQ c cv mI rP rl

/-- **The value-level capability laws of `envQ` hold at the values `M` gives the renamed
keys.** -/
def CapLawsAgree {V : Type w} [SetTheory V] {envA : Env .anon} (M : Ix.Kernel.Cached.StrongModel V envA)
    (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon) (envQ : Env .source) : Prop :=
  CapabilityLaws (Ix.Kernel.pullCval f M.model.cval) envQ

/-- `c` is the representative of the name `n` of the closure `sub`. -/
def RepOf (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (sub : Ix.Environment)
    (c : Ix.Kernel.ConstantInfo .source) (n : Ix.Name) : Prop :=
  (sub.consts.get? n).isSome = true ∧ c.name = quotientKey ixe t n

/-- `c` represents a record whose terms the compiler rewrote. -/
def RewrittenConstant (env : Ix.Environment) (ixe : Ixon.Env) (sub : Ix.Environment)
    (t : Ix.Kernel.RoleTable) (c : Ix.Kernel.ConstantInfo .source) : Prop :=
  ∃ k n a, k.rewritesTerms = true ∧ KindRoot k env ixe sub n a ∧ RepOf ixe t sub c n

/-- `c` represents a member of an input clique, or a lemma carried with one. -/
def CliqueConstant (env : Ix.Environment) (ixe : Ixon.Env) (sub : Ix.Environment)
    (t : Ix.Kernel.RoleTable) (c : Ix.Kernel.ConstantInfo .source) : Prop :=
  ∃ n a, KindRoot .clique env ixe sub n a ∧ RepOf ixe t sub c n

/-- `c` is the key of an imaged Source recursor of the closure. -/
def ImageRecursor (env : Ix.Environment) (ixe : Ixon.Env) (sub : Ix.Environment)
    (t : Ix.Kernel.RoleTable) (c : Ix.Kernel.Key .source) : Prop :=
  ∃ n a, KindRoot .image env ixe sub n a ∧ (sub.consts.get? n).isSome = true ∧ c = quotientKey ixe t n

/-- **A driver state owns the artifact's resolution**: every name it resolves outside its
aux map, and that the compile did not report failed, is published at the address it
resolves to, and every record it stores is the artifact's. -/
def Owned (ixe : Ixon.Env) (failures : Failures) (c : Ix.CompileM.CompileEnv) : Prop :=
  (∀ (n : Ix.Compile.ExactKey.ExactName) (a : Address), c.nameToAddr.get? n = some a →
    c.auxNameToAddr.contains n = false → failures.failed n = false →
      (ixe.named.get? n).map (·.addr) = some a) ∧
  ∀ (a : Address) (b : ByteArray), c.constants.get? a = some b →
    ixe.consts.get? a = some { buf := b, len := b.size }

/-- **The closure's claims, owned**: every name of the closure resolved outside the aux
map is a claim of a block of the closure, compiled with Pass 3's hooks the identity
against a fold state that owns the artifact's resolution. -/
def ClaimsOwned (env : Ix.Environment) (ixe : Ixon.Env) (failures : Failures) (sub : Ix.Environment) :
    Prop :=
  ∃ cenv, compileUnchecked env = .ok (ixe, failures, cenv) ∧
    ∀ (n : Ix.Compile.ExactKey.ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
      cenv.auxNameToAddr.contains n = false → (sub.consts.get? n).isSome = true →
      ∃ (snap : Ix.CompileM.DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (b : ByteArray),
        (compileBlocks env).blocks.get? rep = some all ∧
        (∀ x, all.contains x = true → (sub.consts.get? x).isSome = true) ∧
        ixe.consts.get? a = some { buf := b, len := b.size } ∧
        Resolution.HookFree snap.cenv all (Ix.CompileM.blockKey rep all) ∧
        Resolution.BlockCompiled snap.cenv all (Ix.CompileM.blockKey rep all) n a b ∧
        Owned ixe failures snap.cenv

/-! ## The obligations -/

namespace Obligation

/-- **(1) Source no-drop and totality.** Quotient Source installs each key once, and every
constant of the closure has its representative installed, at the address the artifact
publishes the constant at. -/
def SourceTotal : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source),
    Premises env roots sub ixe failures t envQ →
    (∀ c ∈ envQ.consts, envQ.find? c.name = some c) ∧
    ∀ n ci, sub.consts.get? n = some ci →
      ∃ c ∈ envQ.consts, c.name = quotientKey ixe t n ∧
        keyAddress ixe t c.name = (ixe.named.get? n).map (·.addr)

/-- **(2) The reader against the Source stream, unchanged closures.** For a closure that
avoids the changed set and whose claims are owned, the compiled closure has an order that
respects its references, its records decode canonically, and the reader reads them record
by record under the default table, keeping the prelude; its prepared declarations are
quotient Source's prepared declarations renamed to the artifact's addresses, in another
order that is closed. -/
def ReaderStreams : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (pre : Ix.Kernel.Reader.Prelude .source) (ds : Array (Ix.Kernel.Declaration .source))
    (b : Ix.RoleEvidence.Bundle),
    Premises env roots sub ixe failures t envQ → (changedSetOf env ixe).Avoids sub →
    ClaimsOwned env ixe failures sub →
    Ix.Kernel.Reader.builtinPrelude = .ok pre →
    Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub
      (blocksOf sub) = .ok ds →
    Ix.RoleEvidence.committedBundle () = .ok b →
    ∃ (binding : Ix.Kernel.Admission.Binding) (tA : Ix.Kernel.RoleTable)
      (preA : Ix.Kernel.Reader.Prelude .anon) (order : List Address)
      (st' : Ix.Kernel.Reader.State .anon) (decls : Array (Ix.Kernel.Declaration .anon)),
      Ix.Kernel.Admission.defaultBinding = .ok binding ∧
      Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok tA ∧
      Ix.Kernel.Reader.preludeFor tA = .ok preA ∧
      ClosureOrder ixe (Seed ixe sub) order ∧ Stream.StoredCanonical ixe order ∧
      Ix.Kernel.Reader.StreamRead (closureContext ixe tA preA order) preA.state
        (Stream.decodedOf ixe order) st' decls ∧
      Ix.Kernel.Reader.State.keepsPrelude preA.state st' = true ∧
      (Ix.Kernel.Frontend.preparePrelude preA.ix decls).toList.Perm
        (ds.toList.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b))) ∧
      Ix.Kernel.Closed (Ix.Kernel.Frontend.preparePrelude preA.ix decls).toList

/-- **(2) The reader keys every representative as its renaming.** In the reading context of
an accepted compiled closure, a constant of quotient Source that reads, reads as its
renamed key at its own level parameters, and every representative of the closure reads. -/
def ReadingKeys : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (order : List Address)
    (envA : Env .anon) (b : Ix.RoleEvidence.Bundle),
    Premises env roots sub ixe failures t envQ →
    Ix.Kernel.Admission.defaultBinding = .ok binding →
    IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA →
    Ix.RoleEvidence.committedBundle () = .ok b →
    ∃ cx, admissionContext binding limits ixe order = some cx ∧
      (∀ c ∈ envQ.consts, ∀ e, readingAt ixe t cx c = some e →
        e = .const (c.name.map (Ix.LeanIngress.evAddr ixe b)) (c.toConstantVal.levelParams.map .param)) ∧
      ∀ n ci, sub.consts.get? n = some ci → ∀ c ∈ envQ.consts, c.name = quotientKey ixe t n →
        (readingAt ixe t cx c).isSome = true

/-- **(2) A constant the compiler did not rewrite reads as its renamed self**: in every
strong model of an accepted compiled closure, every input-keyed constant of quotient Source
that represents no rewritten record and no clique member agrees with the compiled
environment under the renaming. -/
def RenamedAgree : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (order : List Address)
    (envA : Env .anon) (b : Ix.RoleEvidence.Bundle) (V : Type w) [SetTheory V]
    (M : Ix.Kernel.Cached.StrongModel V envA),
    Premises env roots sub ixe failures t envQ →
    Ix.Kernel.Admission.defaultBinding = .ok binding →
    IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA →
    Ix.RoleEvidence.committedBundle () = .ok b → (∀ k, KindAccepted k env ixe sub) →
    ∀ c ∈ envQ.consts, InputKey c.name → ¬ RewrittenConstant env ixe sub t c →
      ¬ CliqueConstant env ixe sub t c → ConstantAgrees M (Ix.LeanIngress.evAddr ixe b) c

/-- **(3) Scheduler and global ownership.** Every state the fold of a compile reaches, and
that the final environment follows, owns the artifact's resolution. -/
def ScheduleOwnership : Prop :=
  ∀ (env : Ix.Environment) (ixe : Ixon.Env) (failures : Failures) (cenv cenv₀ : Ix.CompileM.CompileEnv)
    (sched : Ix.CompileM.FoldSchedule),
    compileReport env = .ok (ixe, failures) → compileUnchecked env = .ok (ixe, failures, cenv) →
    Resolution.FoldRun { consts := env.consts } (compileBlocks env) cenv cenv₀ sched →
    ∀ snap, Resolution.Reach (compileBlocks env) (Ix.CompileM.FoldState.init cenv₀ (compileBlocks env) sched).acc
      snap → Resolution.Mono snap.cenv cenv → Owned ixe failures snap.cenv

/-- **(4) Per-pass value preservation.** In every strong model of an accepted compiled
closure whose changed records passed validation, every constant of quotient Source that
represents a rewritten record (its call sites rewritten by the baseline or an occurrence
pass, a regenerated auxiliary, an image) agrees with the compiled environment under the
renaming. -/
def PassValues : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (order : List Address)
    (envA : Env .anon) (b : Ix.RoleEvidence.Bundle) (V : Type w) [SetTheory V]
    (M : Ix.Kernel.Cached.StrongModel V envA),
    Premises env roots sub ixe failures t envQ →
    Ix.Kernel.Admission.defaultBinding = .ok binding →
    IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA →
    Ix.RoleEvidence.committedBundle () = .ok b → (∀ k, KindAccepted k env ixe sub) →
    SourceFormInfers env ixe sub t →
    ∀ c ∈ envQ.consts, RewrittenConstant env ixe sub t c → ConstantAgrees M (Ix.LeanIngress.evAddr ixe b) c

/-- **(5) Image rows.** In every strong model of an accepted compiled closure whose changed
records (the image computation-rule rows among them) passed validation, every fired rule of
every imaged Source recursor holds at the level of values (`RecRuleLaw`), at the values the
strong model gives the renamed keys. This is what the rows must give: for each rule, its
equation at constructor values of fitting arguments. -/
def ImageRules : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (order : List Address)
    (envA : Env .anon) (b : Ix.RoleEvidence.Bundle) (V : Type w) [SetTheory V]
    (M : Ix.Kernel.Cached.StrongModel V envA),
    Premises env roots sub ixe failures t envQ →
    Ix.Kernel.Admission.defaultBinding = .ok binding →
    IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA →
    Ix.RoleEvidence.committedBundle () = .ok b → (∀ k, KindAccepted k env ixe sub) →
    RecLawsAgree M (Ix.LeanIngress.evAddr ixe b) envQ (ImageRecursor env ixe sub t)

/-- **(6) Clique rows.** In every strong model of an accepted compiled closure whose
changed records (the clique rows among them) passed validation, every constant of quotient
Source that represents a clique member or a lemma carried with one agrees with the
compiled environment under the renaming. -/
def CliqueRows : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (order : List Address)
    (envA : Env .anon) (b : Ix.RoleEvidence.Bundle) (V : Type w) [SetTheory V]
    (M : Ix.Kernel.Cached.StrongModel V envA),
    Premises env roots sub ixe failures t envQ →
    Ix.Kernel.Admission.defaultBinding = .ok binding →
    IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA →
    Ix.RoleEvidence.committedBundle () = .ok b → (∀ k, KindAccepted k env ixe sub) →
    ∀ c ∈ envQ.consts, CliqueConstant env ixe sub t c → ConstantAgrees M (Ix.LeanIngress.evAddr ixe b) c

/-- **(7) Locality: reordering.** A reference accept of a stream gives one of every
permutation of it that is closed in its order, installing the same constants. -/
def ReorderAccepts : Prop :=
  ∀ {md : Ix.Kernel.Mode} (μ : Ix.Kernel.CheckMode) (ev : Ix.Kernel.Evidences md)
    (A S : List (Ix.Kernel.Declaration md)) (envS : Env md),
    Ix.Kernel.Cached.AcceptsRef μ ev S envS → A.Perm S → Ix.Kernel.Closed A →
      ∃ envA, Ix.Kernel.Cached.AcceptsRef μ ev A envA ∧ SameEnv envA envS

/-- **(7) Locality: the role table's evidence.** Where quotient Source's run, renamed to
the artifact's addresses, is accepted under the bundle's evidence, it is accepted under the
evidence the reader resolves from the default table for the compiled closure. -/
def EvidenceTransfer : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (pre : Ix.Kernel.Reader.Prelude .source) (ds : Array (Ix.Kernel.Declaration .source))
    (b : Ix.RoleEvidence.Bundle) (binding : Ix.Kernel.Admission.Binding) (tA : Ix.Kernel.RoleTable)
    (preA : Ix.Kernel.Reader.Prelude .anon) (order : List Address) (st' : Ix.Kernel.Reader.State .anon)
    (decls : Array (Ix.Kernel.Declaration .anon)) (envR : Env .anon),
    Premises env roots sub ixe failures t envQ →
    Ix.Kernel.Reader.builtinPrelude = .ok pre →
    Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub
      (blocksOf sub) = .ok ds →
    Ix.RoleEvidence.committedBundle () = .ok b →
    Ix.Kernel.Admission.defaultBinding = .ok binding →
    Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok tA →
    Ix.Kernel.Reader.preludeFor tA = .ok preA →
    Ix.Kernel.Reader.StreamRead (closureContext ixe tA preA order) preA.state
      (Stream.decodedOf ixe order) st' decls →
    Ix.Kernel.Cached.AcceptsRef .verified ((sourceEvidence ixe t).mapKeys (Ix.LeanIngress.evAddr ixe b))
      (ds.toList.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b))) envR →
    Ix.Kernel.Cached.AcceptsRef .verified
      (Ix.Kernel.Reader.evidenceOf (closureContext ixe tA preA order) st' tA)
      (ds.toList.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b))) envR

/-- **(7) Locality: the union of seed closures.** On a compiled artifact, if the compiled
closure of every seed is accepted, so is the compiled closure of all of them. -/
def SeedUnion : Prop :=
  ∀ (env : Ix.Environment) (ixe : Ixon.Env) (binding : Ix.Kernel.Admission.Binding) (S : Address → Prop),
    compile env = .ok ixe → Ix.Kernel.Admission.defaultBinding = .ok binding →
    (∀ a, S a → RootAccepted binding ixe a) →
    ∃ limits order envA, IxonAcceptsRef binding limits ixe S order envA

/-- **(7) Locality: Source restriction.** A constant of an instance's closure that no
change reaches lies in an instance's closure (of the same compile) that avoids the changed
set. -/
def SourceRestricts : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source) (n : Ix.Name),
    Premises env roots sub ixe failures t envQ → (sub.consts.get? n).isSome = true →
    ¬ SelectedRoots.AffectedName env (changedSetOf env ixe) n →
    ∃ roots' sub' envQ', Premises env roots' sub' ixe failures t envQ' ∧
      (changedSetOf env ixe).Avoids sub' ∧ sub'.consts.get? n = sub.consts.get? n

/-- **(7) Locality: restriction to a seed.** A seed of an accepted compiled closure has an
accepted compiled closure. -/
def RootRestricts : Prop :=
  ∀ (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (ixe : Ixon.Env)
    (S : Address → Prop) (order : List Address) (envA : Env .anon) (a : Address),
    IxonAcceptsRef binding limits ixe S order envA → S a → RootAccepted binding ixe a

/-- **(8) Assembly.** For an accepted quotient Source environment and a strong model of the
compiled environment: if every input-keyed constant agrees under the renaming, and the
value-level recursor and capability laws hold at the values the strong model gives the
renamed keys, then one Source model with the laws gives every input key its renamed key's
value. -/
def Assembly : Prop :=
  ∀ (V : Type w) [SetTheory V] (envQ : Env .source) (envA : Env .anon)
    (M : Ix.Kernel.Cached.StrongModel V envA) (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon),
    (∃ ev ds, Ix.Kernel.Cached.AcceptsRef .verified ev ds envQ) →
    (∀ c ∈ envQ.consts, InputKey c.name → ConstantAgrees M f c) →
    RecLawsAgree M f envQ (fun _ => True) → CapLawsAgree M f envQ →
    ∃ N : LawModel V envQ, ∀ k, InputKey k → ∀ φ, N.cval k φ = M.model.cval (k.map f) φ

/-- **(9) The Source laws of a renamed environment.** A strong model of an environment
that installs the constants of a renaming of `envQ` gives `envQ`'s value-level laws at the
pulled-back values: the recursor rules from the strong model's own (`StrongModel.rec_rule`),
the capability laws from its capability and projection-tower laws. -/
def UnchangedRules : Prop :=
  ∀ (V : Type w) [SetTheory V] (P : Ix.Kernel.Mode.Id .source → Prop)
    (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon) (envQ : Env .source) (envR envA : Env .anon)
    (M : Ix.Kernel.Cached.StrongModel V envA),
    Ix.Kernel.EnvRel P f envQ envR → SameEnv envA envR →
      RecRuleLaws (Ix.Kernel.pullCval f M.model.cval) envQ ∧
        CapabilityLaws (Ix.Kernel.pullCval f M.model.cval) envQ

/-- **(9) Rule correspondence under the reader.** In every strong model of an accepted
compiled closure whose changed records passed validation, every fired rule of every Source
recursor that is not imaged, and every capability law, holds at the level of values at the
values the strong model gives the renamed keys. -/
def RuleCorrespondence : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (order : List Address)
    (envA : Env .anon) (b : Ix.RoleEvidence.Bundle) (V : Type w) [SetTheory V]
    (M : Ix.Kernel.Cached.StrongModel V envA),
    Premises env roots sub ixe failures t envQ →
    Ix.Kernel.Admission.defaultBinding = .ok binding →
    IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA →
    Ix.RoleEvidence.committedBundle () = .ok b → (∀ k, KindAccepted k env ixe sub) →
    RecLawsAgree M (Ix.LeanIngress.evAddr ixe b) envQ (fun c => ¬ ImageRecursor env ixe sub t c) ∧
      CapLawsAgree M (Ix.LeanIngress.evAddr ixe b) envQ

end Obligation

/-! ## Helpers -/

/-- The default table passes its well-formedness check. -/
theorem defaultTable_check {t : Ix.Kernel.RoleTable} (h : Ix.Kernel.Reader.defaultTable = .ok t) :
    t.check = .ok () := by
  unfold Ix.Kernel.Reader.defaultTable at h
  generalize Ix.Kernel.Reader.defaultTableBytes = bytes at h
  cases bytes with
  | error e => simp [bind, Except.bind] at h
  | ok bs =>
    simp only [bind, Except.bind] at h
    split at h
    · rename_i t' _
      cases hc : t'.check with
      | error e => simp [hc, Except.mapError] at h
      | ok u =>
        simp [hc, Except.mapError, pure, Except.pure] at h
        subst h
        exact hc
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `findProj?` reads the environment through `find?` only. -/
theorem findProj_sameFind {md : Ix.Kernel.Mode} {e e' : Env md} (hf : ∀ k, e.find? k = e'.find? k)
    (T : Ix.Kernel.Key md) (i : Nat) : e.findProj? T i = e'.findProj? T i := by
  unfold Ix.Kernel.Env.findProj?
  rw [hf]

/-- **A denotation depends on the environment through its lookups only.** -/
theorem Denotes.sameFind {md : Ix.Kernel.Mode} {V : Type w} [SetTheory V]
    {cval : Ix.Kernel.Key md → (LevelParam → Nat) → V} {e e' : Env md} (hf : ∀ k, e.find? k = e'.find? k)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {x : Ix.Kernel.Expr md} {v : V}
    (h : Denotes cval e φ ρ x v) : Denotes cval e' φ ρ x v := by
  induction h with
  | bvar => exact .bvar
  | sort => exact .sort
  | const hfind hlen => exact .const (by rw [← hf]; exact hfind) hlen
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ hP ihA ihF => exact .lam ihA ihF hP
  | pi _ _ hP ihA ihB => exact .pi ihA ihB hP
  | proj_table ht _ ih => exact .proj_table (by rw [← findProj_sameFind hf]; exact ht) ih
  | proj_fst ht _ ih => exact .proj_fst (by rw [← findProj_sameFind hf]; exact ht) ih
  | proj_snd ht _ ih => exact .proj_snd (by rw [← findProj_sameFind hf]; exact ht) ih
  | natLit _ ih => exact .natLit ih
  | strLit _ ih => exact .strLit ih

/-- **A value model moves between environments that install the same constants.** -/
def ValueModel.transfer {md : Ix.Kernel.Mode} {V : Type w} [SetTheory V] {e e' : Env md}
    (h : SameEnv e e') (N : ValueModel V e) : ValueModel V e' where
  cval := N.cval
  mem c hc φ ρ := by
    obtain ⟨T, hT, hm⟩ := N.mem c ((h.mem c).mpr hc) φ ρ
    exact ⟨T, Denotes.sameFind h.find hT, hm⟩
  false_empty φ ρ F hF := N.false_empty φ ρ F (Denotes.sameFind (fun k => (h.find k).symm) hF)
  eq_equality u φ ρ E A a b hE := N.eq_equality u φ ρ E A a b (Denotes.sameFind (fun k => (h.find k).symm) hE)
  defn_value cv v hint hc φ ρ := Denotes.sameFind h.find (N.defn_value cv v hint ((h.mem _).mpr hc) φ ρ)

/-- **A constant at its own level parameters denotes its value at the assignment.** -/
theorem const_denotes {md : Ix.Kernel.Mode} {V : Type w} [SetTheory V] {env : Env md}
    {cval : Ix.Kernel.Key md → (LevelParam → Nat) → V} {k : Ix.Kernel.Key md}
    {c : Ix.Kernel.ConstantInfo md} {lps : List LevelParam} (hf : env.find? k = some c)
    (hl : c.toConstantVal.levelParams = lps) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes cval env φ ρ (.const k (lps.map .param)) (cval k φ) := by
  have hd := Denotes.const (cval := cval) (φ := φ) (ρ := ρ) (us := lps.map .param) hf
    (by rw [hl]; simp)
  have hs : Ix.Kernel.Level.substFn φ lps (lps.map .param) = φ :=
    funext fun _ => Ix.Kernel.Level.substFn_map_param
  rw [hl, hs] at hd
  exact hd

/-- A quotient Source constant that reads has an input or role key (a derived key has no
address). -/
theorem inputKey_of_reading {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable} {cx : Ix.Kernel.Reader.Ctx .anon}
    {c : Ix.Kernel.ConstantInfo .source} {e : Ix.Kernel.Expr .anon} (h : readingAt ixe t cx c = some e) :
    InputKey c.name := by
  unfold readingAt at h
  cases hk : c.name with
  | id _ => trivial
  | role _ => trivial
  | aux _ _ =>
    rw [hk] at h
    simp [keyAddress] at h

/-- **The closure's claims are owned**, from the unchanged-closure claims
(`HookFree.compileReport_hookFree`) and the ownership obligation. -/
theorem claimsOwned (h3 : Obligation.ScheduleOwnership) {env : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {roots : List Ix.Name} {sub : Ix.Environment}
    (compiled : compileReport env = .ok (ixe, failures)) (closure : IsClosure env roots sub)
    (none : NoFailure failures sub) (avoids : (changedSetOf env ixe).Avoids sub) :
    ClaimsOwned env ixe failures sub := by
  obtain ⟨cenv, blocks, cenv₀, sched, hu, hblocks, hrun, claims⟩ :=
    HookFree.compileReport_hookFree compiled closure none avoids
  subst hblocks
  refine ⟨cenv, hu, fun n a hn hnaux hs => ?_⟩
  obtain ⟨-, snap, rep, all, r, c, layout, p, b, hsnap, hall, hmono, hsub, -, -, hstored, hfree,
    hcompiled⟩ := claims n a hn hnaux hs
  exact ⟨snap, rep, all, b, hall, hsub, hstored, hfree, hcompiled,
    h3 env ixe failures cenv cenv₀ sched compiled hu hrun snap hsnap hmono⟩

/-- The renamed key of a constant of a renamed environment, read at its own level
parameters, denotes the pulled-back value. -/
theorem renamed_reading_denotes {V : Type w} [SetTheory V] {P : Ix.Kernel.Mode.Id .source → Prop}
    {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon} {envQ : Env .source} {envR envA : Env .anon}
    (rel : Ix.Kernel.EnvRel P f envQ envR) (same : SameEnv envA envR)
    (unique : ∀ c ∈ envQ.consts, envQ.find? c.name = some c) {c : Ix.Kernel.ConstantInfo .source}
    (hc : c ∈ envQ.consts) (M : Ix.Kernel.Cached.StrongModel V envA) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) :
    Denotes M.model.cval envA φ ρ (.const (c.name.map f) (c.toConstantVal.levelParams.map .param))
      (Ix.Kernel.pullCval f M.model.cval c.name φ) := by
  have hf : envA.find? (c.name.map f) = some (c.mapKeys f) := by
    rw [same.find]
    exact rel.find_some (unique c hc)
  exact const_denotes hf (by simp [Ix.Kernel.ConstantInfo.mapKeys_toConstantVal]) φ ρ

/-- The kind of the changed set's direct cause. -/
def causeKind : Cause → ChangeKind
  | .member => .block
  | .imageHead => .image
  | .caller => .callSite
  | .regenerated => .regenerated
  | .clique => .clique

theorem causeKind_reason (c : Cause) : (causeKind c).reason? = some (.direct c) := by
  cases c <;> rfl

/-- A classified root of a kind's reason is a root of that kind. -/
theorem kindRoot_of_reason {k : ChangeKind} {r : SelectedRoots.Reason} (hk : k.reason? = some r)
    {env : Ix.Environment} {ixe : Ixon.Env} {sub : Ix.Environment} {n : Ix.Name} {a : Address}
    (h : SelectedRoots.ClassifiedRoot env (changedSetOf env ixe) sub ixe ⟨n, a, r⟩) :
    KindRoot k env ixe sub n a := by
  unfold KindRoot
  rw [hk]
  exact h

/-- A root of a kind that passed validation is accepted under the default table. -/
theorem kindAccepted_root {k : ChangeKind} {env : Ix.Environment} {ixe : Ixon.Env} {sub : Ix.Environment}
    {n : Ix.Name} {a : Address} {binding : Ix.Kernel.Admission.Binding}
    (hk : KindAccepted k env ixe sub) (hb : Ix.Kernel.Admission.defaultBinding = .ok binding)
    (hr : KindRoot k env ixe sub n a) : RootAccepted binding ixe a := by
  obtain ⟨-, binding', hb', h⟩ := hk
  rw [hb] at hb'
  cases hb'
  exact h n a hr

/-! ## The unchanged-closure case -/

/-- **The final statement for a closure that avoids the changed set**, from Source
totality, the reader's streams and keys, ownership, reordering, the role table's evidence
and the Source laws of a renamed environment. -/
theorem compileCorrect_unchanged (h1 : Obligation.SourceTotal) (h2 : Obligation.ReaderStreams)
    (h2k : Obligation.ReadingKeys) (h3 : Obligation.ScheduleOwnership)
    (h7a : Obligation.ReorderAccepts) (h7b : Obligation.EvidenceTransfer)
    (h9 : Obligation.UnchangedRules.{w}) : CompileCorrectUnchanged.{w} := by
  intro env roots sub ixe failures t envQ P avoids
  have published : Published ixe sub := fun n ci hn =>
    (compileCovers env ixe failures P.compiled n ci (P.source.1.mem_env hn)).mpr (P.none n ci hn)
  obtain ⟨closure, pre, ds, hpre, prepared, run⟩ := P.source
  -- quotient Source's run, renamed to the artifact's addresses
  obtain ⟨b, hb, envR, runR, rel⟩ := Ix.LeanIngress.acceptsRef_prepareSourceCollapsedAt .verified
    (tableBound_of (defaultTable_check P.table) P.bound) prepared run
  -- the reader's stream of the compiled closure
  obtain ⟨binding, tA, preA, order, st', decls, hbind, admitted, prelude, corder, canonical, reads, keeps,
    perm, closed⟩ := h2 env roots sub ixe failures t envQ pre ds b P avoids
      (claimsOwned h3 P.compiled closure P.none avoids) hpre prepared hb
  -- the role table's evidence, then the reader's order
  have runA := h7b env roots sub ixe failures t envQ pre ds b binding tA preA order st' decls envR P hpre
    prepared hb hbind admitted prelude reads runR
  obtain ⟨envA, accA, same⟩ := h7a .verified _ _ _ envR runA perm closed
  -- the preparation succeeds, so the compiled closure is accepted
  obtain ⟨limits, prep⟩ := Stream.closure_prepares (compile_eq_ok.mpr ⟨failures, P.compiled⟩)
    corder.nodup canonical admitted preA reads keeps
  have acc : IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA :=
    ⟨corder, tA, preA, _, _, admitted, prelude, prep, accA⟩
  obtain ⟨cx, hcx, keys, readsAll⟩ := h2k env roots sub ixe failures t envQ binding limits order envA b P
    hbind acc hb
  obtain ⟨unique, total⟩ := h1 env roots sub ixe failures t envQ P
  refine ⟨published, binding, hbind, limits, order, envA, cx, acc, hcx, ?_, ?_⟩
  · intro V _ M
    obtain ⟨rules, caps⟩ := h9 V _ (Ix.LeanIngress.evAddr ixe b) envQ envR envA M rel same
    let N₀ : ValueModel V envQ := ValueModel.pullback rel ((ValueRows.ofStrong M).transfer same)
    refine ⟨{ N₀ with rec_rule := rules, caps := caps }, fun c hc e he φ ρ => ?_⟩
    rw [keys c hc e he]
    exact renamed_reading_denotes rel same unique hc M φ ρ
  · intro n ci hn
    obtain ⟨c, hc, hname, haddr⟩ := total n ci hn
    exact ⟨c, hc, hname, haddr, readsAll n ci hn c hc hname⟩

/-! ## The general case -/

/-- **The final statement, composed from its open obligations.** -/
theorem compileCorrect_of_obligations (h1 : Obligation.SourceTotal) (h2 : Obligation.ReaderStreams)
    (h2k : Obligation.ReadingKeys) (h2c : Obligation.RenamedAgree.{w}) (h3 : Obligation.ScheduleOwnership)
    (h4 : Obligation.PassValues.{w}) (h5 : Obligation.ImageRules.{w}) (h6 : Obligation.CliqueRows.{w})
    (h7a : Obligation.ReorderAccepts) (h7b : Obligation.EvidenceTransfer) (h7c : Obligation.SeedUnion)
    (h7d : Obligation.SourceRestricts) (h7e : Obligation.RootRestricts) (h8 : Obligation.Assembly.{w})
    (h9u : Obligation.UnchangedRules.{w}) (h9 : Obligation.RuleCorrespondence.{w}) :
    CompileCorrect.{w} := by
  intro env roots sub ixe failures t envQ table source compiled none bound agree evidence kinds forms
  have P : Premises env roots sub ixe failures t envQ :=
    ⟨table, source, compiled, none, bound, agree, evidence⟩
  have published : Published ixe sub := fun n ci hn =>
    (compileCovers env ixe failures compiled n ci (source.1.mem_env hn)).mpr (none n ci hn)
  obtain ⟨binding, hbind, -⟩ := (kinds .cascade).2
  -- every seed's compiled closure is accepted
  have seeds : ∀ a, Seed ixe sub a → RootAccepted binding ixe a := by
    rintro a ⟨n, ci, named, hn, hnamed, haddr⟩
    have pub : SelectedRoots.PublishedIn sub ixe n a := ⟨ci, named, hn, hnamed, haddr⟩
    by_cases hcs : (changedSetOf env ixe).contains n = true
    · -- a direct cause: its kind's validation
      obtain ⟨e, he, hen⟩ :=
        (SelectedRoots.contains_iff_entry env (compileBlocks env) (compileTable env) ixe n).mp hcs
      exact kindAccepted_root (kinds (causeKind e.cause)) hbind
        (kindRoot_of_reason (causeKind_reason e.cause)
          ⟨e, he, rfl, rfl, (SelectedRoots.published_congr hen).mpr pub⟩)
    · by_cases haff : SelectedRoots.AffectedName env (changedSetOf env ixe) n
      · -- the cascade's validation
        exact kindAccepted_root (kinds .cascade) hbind
          (kindRoot_of_reason (k := .cascade) rfl ⟨pub, haff, Bool.eq_false_iff.mpr hcs⟩)
      · -- unaffected: an unchanged closure holds it
        obtain ⟨roots', sub', envQ', P', avoids', hn'⟩ :=
          h7d env roots sub ixe failures t envQ n P (by rw [hn]; rfl) haff
        obtain ⟨-, binding', hb', limits', order', envA', -, acc', -⟩ :=
          compileCorrect_unchanged h1 h2 h2k h3 h7a h7b h9u env roots' sub' ixe failures t envQ' P'
            avoids'
        rw [hbind] at hb'
        cases hb'
        exact h7e binding limits' ixe (Seed ixe sub') order' envA' a acc'
          ⟨n, ci, named, hn'.trans hn, hnamed, haddr⟩
  -- their union is the compiled closure's acceptance
  obtain ⟨limits, order, envA, acc⟩ :=
    h7c env ixe binding (Seed ixe sub) (compile_eq_ok.mpr ⟨failures, compiled⟩) hbind seeds
  obtain ⟨-, pre, ds, -, prepared, run⟩ := source
  obtain ⟨b, hb, -, -, -⟩ := Ix.LeanIngress.acceptsRef_prepareSourceCollapsedAt .verified
    (tableBound_of (defaultTable_check table) bound) prepared run
  obtain ⟨cx, hcx, keys, readsAll⟩ :=
    h2k env roots sub ixe failures t envQ binding limits order envA b P hbind acc hb
  obtain ⟨-, total⟩ := h1 env roots sub ixe failures t envQ P
  refine ⟨published, binding, hbind, limits, order, envA, cx, acc, hcx, ?_, ?_⟩
  · intro V _ M
    have agrees : ∀ c ∈ envQ.consts, InputKey c.name → ConstantAgrees M (Ix.LeanIngress.evAddr ixe b) c := by
      intro c hc hin
      by_cases hr : RewrittenConstant env ixe sub t c
      · exact h4 env roots sub ixe failures t envQ binding limits order envA b V M P hbind acc hb kinds forms
          c hc hr
      · by_cases hq : CliqueConstant env ixe sub t c
        · exact h6 env roots sub ixe failures t envQ binding limits order envA b V M P hbind acc hb kinds
            c hc hq
        · exact h2c env roots sub ixe failures t envQ binding limits order envA b V M P hbind acc hb kinds
            c hc hin hr hq
    obtain ⟨recs, caps⟩ := h9 env roots sub ixe failures t envQ binding limits order envA b V M P hbind acc hb
      kinds
    have images := h5 env roots sub ixe failures t envQ binding limits order envA b V M P hbind acc hb kinds
    have allRecs : RecLawsAgree M (Ix.LeanIngress.evAddr ixe b) envQ (fun _ => True) := by
      intro c cv mI rP rules hfind _ rl hrl hfire
      by_cases hi : ImageRecursor env ixe sub t c
      · exact images c cv mI rP rules hfind hi rl hrl hfire
      · exact recs c cv mI rP rules hfind hi rl hrl hfire
    obtain ⟨N, hN⟩ := h8 V envQ envA M (Ix.LeanIngress.evAddr ixe b) ⟨_, _, run⟩ agrees allRecs caps
    refine ⟨N, fun c hc e he φ ρ => ?_⟩
    have hin := inputKey_of_reading he
    rw [keys c hc e he, hN c.name hin φ]
    obtain ⟨c', hc', hl, -, -⟩ := agrees c hc hin
    exact const_denotes hc' hl φ ρ
  · intro n ci hn
    obtain ⟨c, hc, hname, haddr⟩ := total n ci hn
    exact ⟨c, hc, hname, haddr, readsAll n ci hn c hc hname⟩

end Ix.Cert
