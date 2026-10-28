import Ix.Cert.FreshSnapshot
import Ix.Cert.BlockWire
import Ix.Cert.BlockRefs

/-! # The artifact facts of a claimed block

What the artifact holds of a block the fold compiled and applied, in the forms the reading of a
definition block takes (`BlockRefs.exactNames_of`):

* `stored`: the block's record decodes to the block;
* `owned`: each member of a block of several definitions is published at its projection, which
  the block owns;
* `apart`: members are published at distinct addresses;
* `published`: a closure name the block's snapshot resolves is published at that address;
* `sameKey`: two closure names with one ingress key are published alike (Source totality).

The block's own facts come from `compileReport_owned_block`, packed as `Published`: the block's
record, and each claim of the block for a name of the closure, are in the artifact. -/

namespace Ix.Cert.BlockPublication

open Ix.CompileM Ix.CompileCert Ix.Cert.Resolution
open Ix.Cert.ClosureLayout (addrOf)
open Ix.Cert.DefinitionDeps (ConstOcc)

/-- **A block's claims, published**: the artifact stores the block's record, and each claim of
the block for a name of the closure is published at its address, with its record stored there
(`compileReport_owned_block`). -/
structure Published (ixe : Ixon.Env) (sub : Ix.Environment) (k : Ix.Name) (r : BlockResult) : Prop where
  block : ixe.consts.get? r.blockAddr = some { buf := r.blockBytes, len := r.blockBytes.size }
  claims : ∀ (m : Ix.Name) (a : Address) (b : ByteArray), (m, a, b) ∈ claimWrites k r →
    (sub.consts.get? m).isSome = true → addrOf ixe m = some a ∧ ixe.consts.get? a = some { buf := b, len := b.size }

/-- **`stored`: the block's record decodes to the block.** -/
theorem stored {ixe : Ixon.Env} {sub : Ix.Environment} {cenv : CompileEnv} {all : Ix.Set Ix.Name}
    {k : Ix.Name} {r : BlockResult} {c : BlockState} (hr : runBlock cenv all k = .ok (r, c)) (pub : Published ixe sub k r) :
    recordAt ixe r.blockAddr = some r.block := by
  have shape := BlockLayout.runBlock_shape hr
  have hb := pub.block
  rw [shape.bytes] at hb
  exact BlockLayout.recordAt_ser (BlockWire.blocksWire _ _ _ _ _ _ hr) hb

/-- **The rows of a block of several definitions**: member `j`'s row is its projection at
index `j`, and the members' count fits the wire. -/
theorem definition_rows {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    {defs : List Ix.Def} (two : 2 ≤ defs.length)
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before = (.ok output, after)) :
    defs.length < UInt64.size ∧ ∀ j (hj : j < defs.length),
      (defs[j].name, MutualProjections.memberProjection output.blockAddr j.toUInt64 (.defn defs[j])) ∈
        MutualProjections.logicalRows output.projections := by
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, _, -, compiled⟩ := bind_ok ran
  unfold compileMutualPayload at compiled
  obtain ⟨payload, middle, payloadRan, finished⟩ := bind_ok compiled
  have nonempty : ∀ members ∈ (defs.map MutConst.defn).map ([·]), members ≠ [] := by
    intro members h
    simp only [List.map_map, List.mem_map, Function.comp_apply] at h
    obtain ⟨_, _, rfl⟩ := h
    simp
  have count := ProjectionLayout.payload_count _ nonempty _ _ _ _ payloadRan
  obtain ⟨members, roots, metadata⟩ := payload
  dsimp only at finished count
  obtain ⟨-, header, built⟩ := ProjectionLayout.finish_mutual_ok _ _ _ _ finished
  have size : members.size = defs.length := by simpa using count
  refine ⟨by rw [← size]; exact header.1, fun j hj => ?_⟩
  unfold buildCompiledMutualBlock at built
  have none : standaloneMutConstInfo? members = none := by
    rcases members with ⟨l⟩
    rcases l with _ | ⟨m, _ | ⟨m₂, rest⟩⟩
    · simp at size; omega
    · simp at size; omega
    · rfl
  rw [none] at built
  obtain ⟨block, -, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
  cases Except.ok.inj returned
  dsimp only [BlockResult.mk']
  rw [MutualProjections.build_rows]
  unfold MutualProjections.expectedRows
  refine List.mem_flatMap.mpr ⟨([.defn defs[j]], j), ?_, ?_⟩
  · rw [List.mem_zipIdx_iff_getElem?]
    simp [hj]
  · simp [MutualProjections.sourceRows, MutConst.name, MutConst.ctors]

/-- A claim of a block for each row of its projections. -/
theorem row_claim {k : Ix.Name} {r : BlockResult} {name : Ix.Name} {proj : Ixon.Constant}
    (h : (name, proj) ∈ MutualProjections.logicalRows r.projections) :
    (name, Address.admissionHash (Ixon.ser proj), Ixon.ser proj) ∈ claimWrites k r := by
  unfold MutualProjections.logicalRows at h
  obtain ⟨p, hp, e⟩ := List.mem_map.mp h
  have hp' : p ∈ r.projections := Array.mem_toList_iff.mp hp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  unfold claimWrites
  have hne : r.projections.isEmpty = false := by
    cases hr : r.projections.isEmpty
    · rfl
    · rw [Array.isEmpty_iff] at hr
      rw [hr] at hp'
      simp at hp'
  rw [hne]
  exact Array.mem_map.2 ⟨p, hp', rfl⟩

/-- **A member of a claimed block of several definitions is published at its projection,
whose record the artifact stores.** -/
theorem member_published {ixe : Ixon.Env} {sub : Ix.Environment} {cenv : CompileEnv} {all : Ix.Set Ix.Name}
    {k : Ix.Name} {r : BlockResult} {c : BlockState} (hr : runBlock cenv all k = .ok (r, c)) (pub : Published ixe sub k r)
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult} {defs : List Ix.Def}
    (two : 2 ≤ defs.length)
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before = (.ok output, after))
    (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output)
    (insub : ∀ j (hj : j < defs.length), (sub.consts.get? defs[j].name).isSome = true) :
    defs.length < UInt64.size ∧ ∀ j (hj : j < defs.length),
      addrOf ixe defs[j].name = some (Address.admissionHash (Ixon.ser
          (MutualProjections.memberProjection r.blockAddr j.toUInt64 (.defn defs[j])))) ∧
        recordAt ixe (Address.admissionHash (Ixon.ser
          (MutualProjections.memberProjection r.blockAddr j.toUInt64 (.defn defs[j])))) =
          some (MutualProjections.memberProjection r.blockAddr j.toUInt64 (.defn defs[j])) := by
  obtain ⟨count, rows⟩ := definition_rows two ran
  simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec
  obtain ⟨-, -, haddr, hproj⟩ := hrec
  have width : r.blockAddr.hash.size = 32 := by
    rw [(BlockLayout.runBlock_shape hr).addr]
    exact Ixon.Authenticated.admissionHash_width _
  refine ⟨count, fun j hj => ?_⟩
  have row := rows j hj
  rw [← haddr] at row
  have row' : (defs[j].name, MutualProjections.memberProjection r.blockAddr j.toUInt64 (.defn defs[j])) ∈
      MutualProjections.logicalRows r.projections := by
    unfold MutualProjections.logicalRows at row ⊢
    rw [← Array.toList_map, hproj, Array.toList_map]
    exact row
  obtain ⟨ha, hb⟩ := pub.claims _ _ _ (row_claim row') (insub j hj)
  exact ⟨ha, BlockLayout.recordAt_ser (MutualProjections.member_wire _ width _ _) hb⟩

/-- **`owned`: each member is published at a record the block owns.** -/
theorem owned {ixe : Ixon.Env} {sub : Ix.Environment} {cenv : CompileEnv} {all : Ix.Set Ix.Name}
    {k : Ix.Name} {r : BlockResult} {c : BlockState} (hr : runBlock cenv all k = .ok (r, c)) (pub : Published ixe sub k r)
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult} {defs : List Ix.Def}
    (two : 2 ≤ defs.length)
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before = (.ok output, after))
    (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output)
    (insub : ∀ j (hj : j < defs.length), (sub.consts.get? defs[j].name).isSome = true) :
    ∀ j (hj : j < defs.length), ∃ P c', addrOf ixe defs[j].name = some P ∧ recordAt ixe P = some c' ∧
      ownerOf P c' = r.blockAddr := by
  intro j hj
  obtain ⟨ha, hrec'⟩ := (member_published hr pub two ran hrec insub).2 j hj
  exact ⟨_, _, ha, hrec', rfl⟩

/-- **`apart`: members are published at distinct addresses**: one address holds one record, and
the members' projections differ in their index. -/
theorem apart {ixe : Ixon.Env} {sub : Ix.Environment} {cenv : CompileEnv} {all : Ix.Set Ix.Name}
    {k : Ix.Name} {r : BlockResult} {c : BlockState} (hr : runBlock cenv all k = .ok (r, c)) (pub : Published ixe sub k r)
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult} {defs : List Ix.Def}
    (two : 2 ≤ defs.length)
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before = (.ok output, after))
    (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output)
    (insub : ∀ j (hj : j < defs.length), (sub.consts.get? defs[j].name).isSome = true) :
    ∀ j (hj : j < defs.length) i (hi : i < defs.length), addrOf ixe defs[j].name = addrOf ixe defs[i].name →
      j = i := by
  intro j hj i hi same
  obtain ⟨count, members⟩ := member_published hr pub two ran hrec insub
  obtain ⟨hj₁, hj₂⟩ := members j hj
  obtain ⟨hi₁, hi₂⟩ := members i hi
  rw [hj₁, hi₁] at same
  have e := Option.some.inj same
  rw [e] at hj₂
  have proj := Option.some.inj (hj₂.symm.trans hi₂)
  simp only [MutualProjections.memberProjection, Ixon.Constant.mk.injEq, Ixon.ConstantInfo.dPrj.injEq,
    and_true] at proj
  have idx := congrArg Ixon.DefinitionProj.idx proj
  dsimp only at idx
  have hj' : j < UInt64.size := Nat.lt_trans hj count
  have hi' : i < UInt64.size := Nat.lt_trans hi count
  have := congrArg UInt64.toNat idx
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt hi'] at this
  exact this

/-- **`published`: a closure name a state of the run resolves is published there**, from `compileReport_owned_block`'s resolution conjunct, at the block's snapshot with
the empty block bindings. -/
theorem published {ixe : Ixon.Env} {sub : Ix.Environment} {acc : DriverAcc}
    (resolved : ∀ (n : Ix.Name) (a : Address), (sub.consts.get? n).isSome = true →
      acc.cenv.nameToAddr.get? n = some a → (ixe.named.get? n).map (·.addr) = some a)
    {bindings : ExpressionState.Bindings} (n : Ix.Name) (a : Address) (hs : (sub.consts.get? n).isSome = true)
    (hlocal : bindings.get? n = none)
    (h : ExpressionState.lookupBinding acc.cenv bindings n = some a) : addrOf ixe n = some a := by
  cases hn : acc.cenv.nameToAddr.get? n with
  | none =>
    simp [ExpressionState.lookupBinding, hlocal, hn] at h
  | some a' =>
    simp only [ExpressionState.lookupBinding, hlocal, hn, Option.orElse_none] at h
    obtain rfl : a' = a := by simpa using h
    exact resolved n a' hs hn

/-- **`sameKey`: two closure names with one ingress key are published alike**, from Source
totality (`Obligation.SourceTotal`'s second conjunct), where their key is not the `sorryAx`
role's. -/
theorem sameKey {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source} {sub : Ix.Environment}
    (total : ∀ n ci, (n, ci) ∈ sub.consts.toList → quotientKey ixe t n ≠ Ix.Kernel.sorryAxName →
      ∃ c ∈ envQ.consts, c.name = quotientKey ixe t n ∧ keyAddress ixe t c.name = (ixe.named.get? n).map (·.addr))
    {n m : Ix.Name} {ci cj : Ix.ConstantInfo} (hn : (n, ci) ∈ sub.consts.toList) (hm : (m, cj) ∈ sub.consts.toList)
    (key : Ix.LeanIngress.ingressKey n = Ix.LeanIngress.ingressKey m)
    (notSorry : quotientKey ixe t m ≠ Ix.Kernel.sorryAxName) : addrOf ixe n = addrOf ixe m := by
  have hq : quotientKey ixe t n = quotientKey ixe t m := by
    unfold quotientKey
    rw [key]
  obtain ⟨c, -, hc, hca⟩ := total n ci hn (hq ▸ notSorry)
  obtain ⟨c', -, hc', hca'⟩ := total m cj hm notSorry
  unfold addrOf
  rw [← hca, ← hca', hc, hc', hq]

/-- **`BlockRefs.exactNames_of` for a claimed block**: its `stored`, `owned` and `apart`
premises from the block's published claims. The block's compile is the fold's (`r`, from
`runBlock`), read as the mutual compile of the group's definitions with the same records. -/
theorem exactNames_of_published (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    {bindings : ExpressionState.Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before) {defs : List Ix.Def} (two : 2 ≤ defs.length)
    (distinct : Canon.KeysDistinct (defs.map MutConst.defn))
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before =
      (.ok output, after))
    (unresolved : ∀ d ∈ defs, bindings.get? d.name = none ∧ context.1.nameToAddr.get? d.name = none)
    {ixe : Ixon.Env} (acyclic : referenceCycle ixe = none)
    {sub : Ix.Environment} {cenv : CompileEnv} {all : Ix.Set Ix.Name} {k : Ix.Name} {r : BlockResult}
    {c : BlockState} (hr : runBlock cenv all k = .ok (r, c)) (pub : Published ixe sub k r)
    (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output)
    (insub : ∀ j (hj : j < defs.length), (sub.consts.get? defs[j].name).isSome = true)
    (published : ∀ n a, ExpressionState.lookupBinding context.1 bindings n = some a → addrOf ixe n = some a)
    (sameKey : ∀ i (hi : i < defs.length) n, (ConstOcc n defs[i].type ∨ ConstOcc n defs[i].value) →
      ∀ j (hj : j < defs.length), Ix.LeanIngress.ingressKey n = Ix.LeanIngress.ingressKey defs[j].name →
        addrOf ixe n = addrOf ixe defs[j].name) :
    ∀ i (hi : i < defs.length) j (hj : j < defs.length) n,
      (ConstOcc n defs[i].type ∨ ConstOcc n defs[i].value) →
        Ix.LeanIngress.ingressKey n = Ix.LeanIngress.ingressKey defs[j].name → n = defs[j].name := by
  have hblock : r.block = output.block := by
    simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec
    exact hrec.1
  exact BlockRefs.exactNames_of context free clean two distinct ran unresolved acyclic
    (hblock ▸ stored hr pub) (owned hr pub two ran hrec insub) (apart hr pub two ran hrec insub) published
    sameKey

/-- info: 'Ix.Cert.BlockPublication.owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms owned

/-- info: 'Ix.Cert.BlockPublication.apart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms apart

/-- info: 'Ix.Cert.BlockPublication.exactNames_of_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exactNames_of_published

end Ix.Cert.BlockPublication
