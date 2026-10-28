import Ix.Cert.CompileCorrect
import Ix.Cert.ClosureClaims
import Ix.Cert.Stream
import IxC.Kernel.Verify.Rename.UnionFold

/-! # The final statement composed from its obligations

`CompileCorrect` is proved here from named hypotheses, each a `def … : Prop` stated
on the compiler's actual objects (`compileReport`, the driver's fold, the certified
reader, quotient Source's prepared stream), one per obligation:

1. `Obligation.SourceTotal`: quotient Source drops nothing; every constant of the
   closure has its representative installed, at the address it is published at.
2. The reader against the Source stream:
   * `Obligation.ReaderStreams`: a closure whose claims are owned reads, record by
     record and in the Source stream's order, as quotient Source's prepared stream
     renamed to the artifact's addresses;
   * `Obligation.ReadingKeys`: the reader keys every representative as its renaming.
3. `Obligation.ScheduleOwnership`: every state the fold reaches resolves and stores as
   the artifact publishes.
7. `Obligation.EvidenceTransfer`: the role table's evidence passes where the bundle's
   does.
9. `Obligation.UnchangedRules`: a renamed environment's strong model gives the Source
   laws.

The numbers are the obligations' original ones; the others belonged to the
rewriting compiler and are gone with it.

The compiler publishes every constant as the compile of its Lean declaration, in
Lean's order, so every closure is a renaming of its Source form. `compileCorrect_unchanged`
composes the obligations with the existing leaves: the closure's claims
(`ClosureClaims.compileReport_owned`), the renamed quotient Source run
(`Ix.LeanIngress.acceptsRef_prepareSourceCollapsedAt`), the reader's preparation
(`Stream.closure_prepares`), coverage (`compileCovers`) and the pulled-back value model
(`ValueModel.pullback`, `ValueRows.ofStrong`). -/

namespace Ix.Cert

open Ix.Kernel (Env SetTheory Denotes LevelParam BVarIdx)

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
  quotient : EvidenceCheck.EvidenceAgrees t ixe
  evidence : RoleClosure.RoleEvidenceChecks

/-- Quotient Source's evidence: the quotient bundle's, renamed onto the representatives. -/
def sourceEvidence (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) : Ix.Kernel.Evidences .source :=
  Ix.LeanIngress.evidenceSubst (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
    (Ix.RoleEvidence.quotientEvidence ())

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

/-- An environment installs the same constants as itself. -/
theorem SameEnv.refl {md : Ix.Kernel.Mode} (e : Env md) : SameEnv e e :=
  ⟨fun _ => Iff.rfl, fun _ => rfl⟩

/-- **Two terms denote one set**: at every level assignment and variable valuation, both
denote, and denote the same set. -/
def DenoteSame {md : Ix.Kernel.Mode} {V : Type w} [SetTheory V]
    (cval : Ix.Kernel.Key md → (LevelParam → Nat) → V) (env : Env md) (e e' : Ix.Kernel.Expr md) : Prop :=
  ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), ∃ X, Denotes cval env φ ρ e X ∧ Denotes cval env φ ρ e' X

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
map is a claim of the block compile of a block of the closure, against a fold state that
owns the artifact's resolution. -/
def ClaimsOwned (env : Ix.Environment) (ixe : Ixon.Env) (failures : Failures) (sub : Ix.Environment) :
    Prop :=
  ∃ cenv, compileUnchecked env = .ok (ixe, failures, cenv) ∧
    ∀ (n : Ix.Compile.ExactKey.ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
      cenv.auxNameToAddr.contains n = false → (sub.consts.get? n).isSome = true →
      ∃ (snap : Ix.CompileM.DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (b : ByteArray),
        (compileBlocks env).blocks.get? rep = some all ∧
        (∀ x, all.contains x = true → (sub.consts.get? x).isSome = true) ∧
        ixe.consts.get? a = some { buf := b, len := b.size } ∧
        Resolution.BlockCompiled snap.cenv all (Ix.CompileM.blockKey rep all) n a b ∧
        Owned ixe failures snap.cenv

/-! ## The obligations -/

namespace Obligation

/-- **(1) Source no-drop and totality.** Quotient Source installs each key once, and every
constant of the closure, under the name the closure stores it under, has its
representative installed, at the address the artifact publishes the constant at. As in
`ReadingCovers`, the names are the stored ones (a lookup also answers hash-equal
respellings, for which no artifact can publish every spelling), and the constants
represented by the inert `sorryAx` role, for which the checker installs nothing by
design, are left out: the statement says nothing about a constant published at
`sorryAx`'s role address, `sorryAx` itself or an axiom α-equal to it. -/
def SourceTotal : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source),
    Premises env roots sub ixe failures t envQ →
    (∀ c ∈ envQ.consts, envQ.find? c.name = some c) ∧
    ∀ n ci, (n, ci) ∈ sub.consts.toList → quotientKey ixe t n ≠ Ix.Kernel.sorryAxName →
      ∃ c ∈ envQ.consts, c.name = quotientKey ixe t n ∧
        keyAddress ixe t c.name = (ixe.named.get? n).map (·.addr)

/-- **(2) The reader against the Source stream.** For a closure whose claims are owned,
the compiled closure has an order that
respects its references (the order of quotient Source's stream), its records decode
canonically, and the reader reads them record by record under the default table, keeping
the prelude; its prepared declarations are exactly quotient Source's prepared declarations
renamed to the artifact's addresses, in the same order. The fold reads more than a
declaration mentions (a `Nat` operation's certificate ground, literal support), so two
orders that both respect references need not both be accepted; reading in the Source
stream's order keeps the order the Source run was accepted in. -/
def ReaderStreams : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (pre : Ix.Kernel.Reader.Prelude .source) (ds : Array (Ix.Kernel.Declaration .source))
    (b : Ix.RoleEvidence.Bundle),
    Premises env roots sub ixe failures t envQ → ClaimsOwned env ixe failures sub →
    Ix.Kernel.Reader.builtinPrelude = .ok pre →
    Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub
      (blocksOf sub) = .ok ds →
    Ix.RoleEvidence.quotientBundle () = .ok b →
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
      (Ix.Kernel.Frontend.preparePrelude preA.ix decls).toList =
        ds.toList.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b))

/-- **(2) The reader keys every representative as its renaming.** In the reading context of
an accepted compiled closure, a constant of quotient Source that reads, reads as its
renamed key at its own level parameters, and every representative of a name the closure
stores a constant under reads when its key sits at the name's published address (the
address `SourceTotal` gives it). -/
def ReadingKeys : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (t : Ix.Kernel.RoleTable) (envQ : Env .source)
    (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (order : List Address)
    (envA : Env .anon) (b : Ix.RoleEvidence.Bundle),
    Premises env roots sub ixe failures t envQ →
    Ix.Kernel.Admission.defaultBinding = .ok binding →
    IxonAcceptsRef binding limits ixe (Seed ixe sub) order envA →
    Ix.RoleEvidence.quotientBundle () = .ok b →
    ∃ cx, admissionContext binding limits ixe order = some cx ∧
      (∀ c ∈ envQ.consts, ∀ e, readingAt ixe t cx c = some e →
        e = .const (c.name.map (Ix.LeanIngress.evAddr ixe b)) (c.toConstantVal.levelParams.map .param)) ∧
      ∀ n ci, (n, ci) ∈ sub.consts.toList → ∀ c ∈ envQ.consts, c.name = quotientKey ixe t n →
        keyAddress ixe t c.name = (ixe.named.get? n).map (·.addr) →
        (readingAt ixe t cx c).isSome = true

/-- **(3) Scheduler and global ownership.** Every state the fold of a compile passes through, from
its own start under its own schedule (`Resolution.OnRun`, `Resolution.FoldRun`), owns the
artifact's resolution. -/
def ScheduleOwnership : Prop :=
  ∀ (env : Ix.Environment) (ixe : Ixon.Env) (failures : Failures) (cenv cenv₀ : Ix.CompileM.CompileEnv)
    (sched : Ix.CompileM.FoldSchedule),
    compileReport env = .ok (ixe, failures) → compileUnchecked env = .ok (ixe, failures, cenv) →
    Resolution.FoldRun { consts := env.consts } (compileBlocks env) cenv cenv₀ sched →
    ∀ snap, Resolution.OnRun (compileBlocks env) sched
      (Ix.CompileM.FoldState.init cenv₀ (compileBlocks env) sched) snap → Owned ixe failures snap.cenv

/-- **(7) Locality: the role table's evidence.** Where quotient Source's run, renamed to
the artifact's addresses, is accepted under the bundle's evidence, it is accepted under the
evidence the reader resolves from the default table for the compiled closure: the closure
of the run's seeds, read into the run's declarations. -/
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
    Ix.RoleEvidence.quotientBundle () = .ok b →
    Ix.Kernel.Admission.defaultBinding = .ok binding →
    Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok tA →
    Ix.Kernel.Reader.preludeFor tA = .ok preA →
    ClosureOrder ixe (Seed ixe sub) order →
    Ix.Kernel.Reader.StreamRead (closureContext ixe tA preA order) preA.state
      (Stream.decodedOf ixe order) st' decls →
    (Ix.Kernel.Frontend.preparePrelude preA.ix decls).toList =
      ds.toList.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b)) →
    Ix.Kernel.Cached.AcceptsRef .verified ((sourceEvidence ixe t).mapKeys (Ix.LeanIngress.evAddr ixe b))
      (ds.toList.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b))) envR →
    Ix.Kernel.Cached.AcceptsRef .verified
      (Ix.Kernel.Reader.evidenceOf (closureContext ixe tA preA order) st' tA)
      (ds.toList.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b))) envR

/-- **(9) The Source laws of a renamed environment.** A strong model of an environment
that installs the constants of a renaming of `envQ` gives `envQ`'s laws at the pulled-back
values: the recursor rules through the strong model's own (`StrongModel.rec_rule`) and the
rule correspondence under the renaming, and likewise the capability laws. -/
def UnchangedRules : Prop :=
  ∀ (V : Type w) [SetTheory V] (P : Ix.Kernel.Mode.Id .source → Prop)
    (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon) (envQ : Env .source) (envR envA : Env .anon)
    (M : Ix.Kernel.Cached.StrongModel V envA),
    Ix.Kernel.EnvRel P f envQ envR → SameEnv envA envR →
      RecRuleLaws (Ix.Kernel.pullCval f M.model.cval) envQ ∧
        CapabilityLaws (Ix.Kernel.pullCval f M.model.cval) envQ

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

/-- **The closure's claims are owned**, from the closure's claims
(`ClosureClaims.compileReport_owned`) and the ownership obligation. -/
theorem claimsOwned (h3 : Obligation.ScheduleOwnership) {env : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {roots : List Ix.Name} {sub : Ix.Environment}
    (compiled : compileReport env = .ok (ixe, failures)) (closure : IsClosure env roots sub)
    (none : NoFailure failures sub) : ClaimsOwned env ixe failures sub := by
  obtain ⟨cenv, blocks, cenv₀, sched, hu, hblocks, hrun, claims⟩ :=
    ClosureClaims.compileReport_owned compiled closure none
  subst hblocks
  refine ⟨cenv, hu, fun n a hn hnaux hs => ?_⟩
  obtain ⟨-, snap, rep, all, r, c, layout, b, hsnap, hall, -, hsub, -, -, hstored, hcompiled⟩ :=
    claims n a hn hnaux hs
  exact ⟨snap, rep, all, b, hall, hsub, hstored, hcompiled,
    h3 env ixe failures cenv cenv₀ sched compiled hu hrun snap hsnap⟩

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

/-! ## The unchanged-closure case -/

/-- **The final statement**, for every closure, from Source totality, the reader's streams and keys, ownership, the role table's evidence and the
Source laws of a renamed environment. -/
theorem compileCorrect_unchanged (h1 : Obligation.SourceTotal) (h2 : Obligation.ReaderStreams)
    (h2k : Obligation.ReadingKeys) (h3 : Obligation.ScheduleOwnership)
    (h7b : Obligation.EvidenceTransfer)
    (h9 : Obligation.UnchangedRules.{w}) : CompileCorrect.{w} := by
  intro env roots sub ixe failures t envQ table source compiled none bound agree quotient evidence
  have P : Premises env roots sub ixe failures t envQ :=
    ⟨table, source, compiled, none, bound, agree, quotient, evidence⟩
  have published : Published ixe sub := fun n ci hn =>
    (compileCovers env ixe failures P.compiled n ci (P.source.1.mem_env hn)).mpr (P.none n ci hn)
  obtain ⟨closure, pre, ds, hpre, prepared, run⟩ := P.source
  -- quotient Source's run, renamed to the artifact's addresses
  obtain ⟨b, hb, envR, runR, rel⟩ := Ix.LeanIngress.acceptsRef_prepareSourceCollapsedAt .verified
    (tableBound_of (defaultTable_check P.table) P.bound) prepared run
  -- the reader's stream of the compiled closure
  obtain ⟨binding, tA, preA, order, st', decls, hbind, admitted, prelude, corder, canonical, reads, keeps,
    streams⟩ := h2 env roots sub ixe failures t envQ pre ds b P
      (claimsOwned h3 P.compiled closure P.none) hpre prepared hb
  -- the role table's evidence: the reader's prepared stream is the renamed run's
  have runA := h7b env roots sub ixe failures t envQ pre ds b binding tA preA order st' decls envR P hpre
    prepared hb hbind admitted prelude corder reads streams runR
  have accA : Ix.Kernel.Cached.AcceptsRef .verified
      (Ix.Kernel.Reader.evidenceOf (closureContext ixe tA preA order) st' tA)
      (Ix.Kernel.Frontend.preparePrelude preA.ix decls).toList envR := by
    rw [streams]; exact runA
  -- the preparation succeeds, so the compiled closure is accepted
  obtain ⟨limits, prep⟩ := Stream.closure_prepares (compile_eq_ok.mpr ⟨failures, P.compiled⟩)
    corder.nodup canonical admitted preA reads keeps
  have acc : IxonAcceptsRef binding limits ixe (Seed ixe sub) order envR :=
    ⟨corder, tA, preA, _, _, admitted, prelude, prep, accA⟩
  have same : SameEnv envR envR := SameEnv.refl envR
  obtain ⟨cx, hcx, keys, readsAll⟩ := h2k env roots sub ixe failures t envQ binding limits order envR b P
    hbind acc hb
  obtain ⟨unique, total⟩ := h1 env roots sub ixe failures t envQ P
  refine ⟨published, binding, hbind, limits, order, envR, cx, acc, hcx, ?_, ?_⟩
  · intro V _ M
    obtain ⟨rules, caps⟩ := h9 V _ (Ix.LeanIngress.evAddr ixe b) envQ envR envR M rel same
    let N₀ : ValueModel V envQ := ValueModel.pullback rel ((ValueRows.ofStrong M).transfer same)
    refine ⟨{ N₀ with rec_rule := rules, caps := caps }, fun c hc e he φ ρ => ?_⟩
    rw [keys c hc e he]
    exact renamed_reading_denotes rel same unique hc M φ ρ
  · intro n ci hn hsorry
    obtain ⟨c, hc, hname, haddr⟩ := total n ci hn hsorry
    exact ⟨c, hc, hname, haddr, readsAll n ci hn c hc hname haddr⟩

end Ix.Cert
