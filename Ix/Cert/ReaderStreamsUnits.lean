import Ix.Cert.StreamUnits
import Ix.Cert.ReadingKeys
import Ix.Cert.SourcePrelude

/-! # The reader's streams for a closure read unit by unit

`Obligation.ReaderStreams` asks that the reader, from the anonymous prelude, read an
accepted closure in a closure order of stored canonical records, keep the prelude's
entries, and prepare quotient Source's prepared stream renamed. This module reduces that
conclusion, for one closure, to its order and its units (`readerStreams_of_units`): a
closure order of stored canonical records whose reading matches quotient Source's trace
unit by unit (`UnitsRead`, `StreamUnits.Units`): definitions, axioms and quotient constants
are plain units, an inductive block is its block record's reading and its projection records
read to nothing.

The rest comes from the premises: the default binding admits at the default table
(`DefaultAdmits`), the committed prelude reads alike at both modes (`PreludeAgrees`), quotient
Source's trace keeps the prelude, its declarations name representatives, on which the
renaming to addresses is injective (`evAddr_injOn`), and preparing commutes with the
renaming (`preparePrelude_mapKeys`). -/

namespace Ix.Cert.ReaderStreamsUnits

open Ix.Kernel Ix.Kernel.Reader
open Ix.LeanIngress (evAddr QRepAt roleAtMap fiberAliasAt fiberHintsMap graphCollapsed scheduleOf)

/-- **What remains of the reader's streams for a closure read unit by unit**: a closure
order of stored canonical records whose reading matches quotient Source's trace `rs` unit
by unit. -/
def UnitsRead (ixe : Ixon.Env) (sub : Ix.Environment) (t : RoleTable) (preA : Prelude .anon)
    (b : Ix.RoleEvidence.Bundle) (pre : Prelude .source) (rs : List (Read .source)) : Prop :=
  ∃ order, ClosureOrder ixe (Seed ixe sub) order ∧ Stream.StoredCanonical ixe order ∧
    StreamUnits.Units (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t)))
      (closureContext ixe t preA order) pre.state rs (Stream.decodedOf ixe order)

/-- **The reader's streams of a closure read unit by unit**: the conclusion of
`Obligation.ReaderStreams`, for a closure whose every quotient Source trace has a closure
order read unit by unit. -/
theorem readerStreams_of_units {env : Ix.Environment} {roots : List Ix.Name}
    {sub : Ix.Environment} {ixe : Ixon.Env} {failures : Failures} {t : RoleTable}
    {envQ : Env .source} {pre : Prelude .source} {ds : Array (Declaration .source)}
    {b : Ix.RoleEvidence.Bundle} (P : Premises env roots sub ixe failures t envQ)
    (hpre : builtinPrelude = .ok pre)
    (hds : Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((fiberHintsMap ixe)[·]?) pre sub
      (blocksOf sub) = .ok ds)
    (hb : Ix.RoleEvidence.quotientBundle () = .ok b)
    (units : ∀ (preA : Prelude .anon) rs fin s kb (decls : Array (Declaration .source)), preludeFor t = .ok preA →
      SourcePrelude.Trace (graphCollapsed (fiberAliasAt ixe (roleAtMap t)) ((fiberHintsMap ixe)[·]?)
          sub (blocksOf sub)) pre.state
        (scheduleOf (graphCollapsed (fiberAliasAt ixe (roleAtMap t)) ((fiberHintsMap ixe)[·]?) sub
          (blocksOf sub))).zipIdx.toList rs fin s kb →
      decls.toList = rs.flatMap (·.decls.toList) → ds = Frontend.preparePrelude pre.ix decls →
      UnitsRead ixe sub t preA b pre rs) :
    ∃ (binding : Admission.Binding) (tA : RoleTable) (preA : Prelude .anon) (order : List Address)
      (st' : State .anon) (decls : Array (Declaration .anon)),
      Admission.defaultBinding = .ok binding ∧
      Admission.admitBinding Address.admissionHash binding = .ok tA ∧
      preludeFor tA = .ok preA ∧
      ClosureOrder ixe (Seed ixe sub) order ∧ Stream.StoredCanonical ixe order ∧
      StreamRead (closureContext ixe tA preA order) preA.state (Stream.decodedOf ixe order) st' decls ∧
      State.keepsPrelude preA.state st' = true ∧
      (Frontend.preparePrelude preA.ix decls).toList =
        ds.toList.map (Declaration.mapKeys (evAddr ixe b)) := by
  obtain ⟨-, -, ⟨binding, tA, hbind, hadm⟩, ⟨t', preS, preA, ht', hS, hA, hagree⟩⟩ := P.evidence
  -- the tables: the admitted one and the prelude agreement's are the default table
  have htA : tA = t := ReadingKeys.admitBinding_default P.table hbind hadm
  subst htA
  have ht't : t' = tA := by
    rw [P.table] at ht'
    exact (Except.ok.inj ht').symm
  subst ht't
  -- the Source prelude is the agreement's
  -- (rewritten, never compared definitionally: that would evaluate the committed prelude)
  have bind_ok : ∀ (a : RoleTable) (g : RoleTable → Except String (Prelude .source)),
      ((Except.ok a : Except String RoleTable) >>= g) = g a := fun _ _ => rfl
  have hpre' : preludeFor (md := .source) t' = .ok pre := by
    unfold builtinPrelude at hpre
    rw [P.table, bind_ok] at hpre
    exact hpre
  rw [hS] at hpre'
  cases hpre'
  -- quotient Source's stream: good, at representatives, and its trace keeps the prelude
  obtain ⟨hsrc, b', hb', hgoodQ, -, hd, -⟩ := Ix.LeanIngress.prepareSourceCollapsedAtUsing_good hds
  rw [hb] at hb'
  cases hb'
  obtain ⟨rs, fin, decls, s, kb, -, htrace, -, -, hflat, hdsEq, hkeepAll⟩ :=
    SourcePrelude.prepareSourceCollapsed_prefix hsrc
  obtain ⟨order, hord, hcanon, hunits⟩ := units preA rs fin s kb decls hA htrace hflat hdsEq
  have tb := tableBound_of (defaultTable_check P.table) P.bound
  have hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t')) :=
    (Ix.LeanIngress.evAddr_injOn tb hd).mono fun _ h => Or.inl h
  have hgood : ∀ d ∈ decls, d.Good (QRepAt ixe (roleAtMap t')) := fun d hd' =>
    hgoodQ d (hdsEq ▸ Frontend.mem_preparePrelude hd')
  have hkeep : State.keepsPrelude pre.state (rs.foldl State.commit pre.state) = true := by
    rw [State.keepsPrelude_iff]
    intro k hk
    have := hkeepAll rs.length k hk
    rwa [List.take_length] at this
  obtain ⟨st', declsA, hread, hkeepA, hprep⟩ :=
    StreamUnits.units_conclusion hf hagree hunits hflat hgood hkeep
  exact ⟨binding, t', preA, order, st', declsA, hbind, hadm, hA, hord, hcanon, hread, hkeepA,
    by rw [hprep, hdsEq]⟩

/--
info: 'Ix.Cert.ReaderStreamsUnits.readerStreams_of_units' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms readerStreams_of_units

end Ix.Cert.ReaderStreamsUnits
