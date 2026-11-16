import IxVMRefinement.Assembly.NativeReaderCoverage
import IxVMRefinement.Assembly.NativeRoleKeys
import IxVMRefinement.Assembly.AdmittedKeys
import IxVMRefinement.Decl.ReferenceReplay
import Ix.Cert.RecursorIndex

/-! # Native member presence in the actual role checking prefix

Reader member coverage gives a concrete inductive declaration in the prepared input. The
reference storage trace preserves each of its installed names, including when the checker
normalizes its types. This is name presence only; no raw/normalized type equality is asserted.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

/-- A member emitted by the reader is present after the actual prepared reference trace.
Inductive declarations are unchanged by the theorem-to-definition preprocessing. -/
theorem ReaderInductiveKey.reference_present {input : Array (Declaration .anon)} {key : Key .anon}
    (covered : ReaderInductiveKey input.toList key) (prelude : Frontend.PreludeIx .anon)
    {fuel : Nat} {start target : Env .anon}
    (trace : Decl.ReferenceTrace fuel start
      ((Frontend.preparePrelude prelude input).toList.map IxVM.Refinement.thmToOpaqueDefn) target) :
    (target.find? key).isSome = true := by
  obtain ⟨block, params, member, named⟩ := covered
  have prepared := preparePrelude_input_subset prelude input (.indDecl block params) member
  have referenced : Declaration.indDecl block params ∈
      (Frontend.preparePrelude prelude input).toList.map IxVM.Refinement.thmToOpaqueDefn :=
    List.mem_map.mpr ⟨.indDecl block params, prepared, rfl⟩
  rw [indDecl_names_installs block params] at named
  obtain ⟨constant, installed, nameEq⟩ := List.mem_map.mp named
  have present := trace.declared referenced installed
  rwa [nameEq] at present

/-- The actual admitted reader and reference trace supply former/constructor name presence
for a selected singleton-family block. The successful member-key reads remain concrete inputs. -/
theorem admitted_native_role_prefix_names {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {fuel : Nat} {start target : Env .anon}
    (trace : Decl.ReferenceTrace fuel start
      ((Frontend.preparePrelude witness.prelude.ix witness.fullDecls).toList.map
        IxVM.Refinement.thmToOpaqueDefn) target)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive}
    (selected : owner ∈ witness.order) (record : Ix.Cert.recordAt witness.env owner = some source)
    (kind : source.info = .muts members) (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)]) :
    let cx := ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order
    (∀ key, cx.memberKey (.member owner member) = .ok key → (target.find? key).isSome = true) ∧
    (∀ slot ctor key, ind.ctors[slot]? = some ctor → cx.memberKey (.ctor owner member slot) = .ok key →
      (target.find? key).isSome = true) := by
  let cx := ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order
  let records := Ix.Cert.Stream.decodedOf witness.env witness.order
  have stream : StreamRead cx witness.prelude.state records witness.state witness.fullDecls := by
    simpa only [cx, records, List.toList_toArray] using readRecords_spec witness.read
  have presentArray : (owner, source) ∈ records.toArray :=
    Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩
  have present : (owner, source) ∈ records := by simpa only [List.mem_toArray] using presentArray
  have stored : cx.store owner = some source :=
    ReaderStoreTransfer.selected (table := witness.table) (prelude := witness.prelude) selected record
  have built : ∃ scanned : Array (_root_.Address × Ixon.Constant), cx.index = buildIndex cx.store scanned :=
    ⟨_, rfl⟩
  obtain ⟨scanned, indexBuilt⟩ := built
  have names := IxVM.Refinement.Assembly.StreamRead.native_member_names
    stream indexBuilt present stored kind memberAt one
  exact ⟨fun key named => (names.1 key named).reference_present witness.prelude.ix trace,
    fun slot ctor key found named => (names.2 slot ctor key found named).reference_present witness.prelude.ix trace⟩

/-- Name presence in the actual role prefix excludes freshness in an environment extending it. -/
theorem present_not_fresh_of_extension {roleEnv env : Env .anon} {key : Key .anon}
    (present : (roleEnv.find? key).isSome = true) (extended : EnvExt roleEnv env) :
    env.find? key ≠ none := by
  obtain ⟨constant, found⟩ := Option.isSome_iff_exists.mp present
  rw [extended.find found]
  exact Option.some_ne_none constant

/-- An actual hashed non-trust bound former/constructor projection has its core name in the
checked role prefix, using the real owner read and prepared declaration coverage. -/
theorem admitted_bound_native_name_present {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {fuel : Nat} {start roleEnv : Env .anon}
    (trace : Decl.ReferenceTrace fuel start
      ((Frontend.preparePrelude witness.prelude.ix witness.fullDecls).toList.map
        IxVM.Refinement.thmToOpaqueDefn) roleEnv)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive}
    (selected : owner ∈ witness.order) (record : Ix.Cert.recordAt witness.env owner = some source)
    (kind : source.info = .muts members) (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {extra : List ByteArray}
    (noCollision : ¬ V.HashedCollision extra calls)
    {role : Role} {address : _root_.Address} {bytes : ByteArray} {value : Ixon.Constant}
    {layout : Egress.ProjectionLayout} {target : ConstRef _root_.Address}
    (bound : (role, address) ∈ witness.table.bound.toList)
    (notTrust : IxVM.Refinement.compilerTrust role = false)
    (hashed : Hashed calls bytes) (hashEq : Address.blake3Pure bytes = address)
    (decoded : Ixon.deConstantExact bytes = .ok value)
    (projection : Egress.ProjectionReads value layout target)
    (nativeTarget : target = .member owner member ∨
      ∃ slot ctor, target = .ctor owner member slot ∧ ind.ctors[slot]? = some ctor) :
    (roleEnv.find? (Core.keyOf witness.table address)).isSome = true := by
  have named := admitted_bound_projection_key witness noCollision bound notTrust hashed hashEq decoded projection
  have present := admitted_native_role_prefix_names witness trace selected record kind memberAt one
  rcases nativeTarget with same | ⟨slot, ctor, same, found⟩
  · rw [same] at named
    exact present.1 _ named
  · rw [same] at named
    exact present.2 slot ctor _ found named


end IxVM.Refinement.Assembly
