import IxVMRefinement.Guard.LoadParents
import IxC.Kernel.Model.ProjGuardCert

/-! # A store for a use's own run, and the firing across two stores

A projection use is read inside the registry at an arbitrary good run of an arbitrary context
over the step's store. Nothing ties that store to the records the use's classifier loads, so
the use is read over a store built from the run itself, and compared with the certificate
through a common extension of the two raw dictionaries.

* `exists_runStore`: a run that hashed no two byte strings under one address has a run store
  that holds the records it hashed (`LoadedReads.RunStore`, `LoadedReads.HashedRecordsStored`):
  the two maps the claim phase builds from the calls.
* `runStore_agree`: a run's store agrees with every store the run hashes no collision with, on
  the records and blobs both hold.
* `fireSem_of_cert_use`: a certificate over one store and a use observed over another give the
  rules tier's firing condition, where the two stores agree on what both hold. The raw
  telescopes read from the two stores are then one.
-/

namespace IxVM.Refinement.Guard

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (Expr Level ProjTable ProjGuardCert ProjGuardUse)

/-- **A run store for a run without a collision among what it hashed.** -/
theorem exists_runStore {calls : List (Call F)}
    (hnoColl : ∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂) :
    ∃ E : Ixon.Env, LoadedReads.RunStore calls E ∧ LoadedReads.HashedRecordsStored calls E := by
  let E : Ixon.Env := { consts := Claim.buildAllConsts calls, blobs := Claim.buildBlobs calls }
  refine ⟨E, ⟨⟨fun a lc hget => ?_, fun a bytes hget => ?_⟩, fun a lc hget => ?_,
    fun bytes hh => ?_⟩, fun bytes c hh hsz hde hex => ?_⟩
  · obtain ⟨hh, ha, -⟩ := Claim.buildAllConsts_get?_some_inv calls hget
    exact ⟨hh, ha⟩
  · exact Claim.buildBlobs_get?_some_inv calls hget
  · obtain ⟨-, -, -, c, hc, -, hex⟩ := Claim.buildAllConsts_get?_some_inv calls hget
    exact ⟨c, hc, hex⟩
  · exact Claim.buildBlobs_get?_of_hashed hnoColl hh
  · have hcont := Claim.buildAllConsts_contains_of_hashed calls hh ⟨hsz, hde, hex⟩
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hcont
    obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp hcont
    rw [← Std.HashMap.get?_eq_getElem?] at hlc
    obtain ⟨hh', ha', -, c', hc', -, hex'⟩ := Claim.buildAllConsts_get?_some_inv calls hlc
    have hbytes : lc.rawBytes = bytes := hnoColl _ _ hh' hh ha'
    rw [hbytes] at hex'
    have hsame : c' = c := Except.ok.inj (hex'.symm.trans hex)
    subst hsame
    exact ⟨lc, hlc, hbytes, hc'⟩

/-- **A good run has a run store.** -/
theorem exists_runStore_of_noCollision {calls : List (Call F)} {V : View}
    (hnc : ¬ V.HashedCollision [] calls) :
    ∃ E : Ixon.Env, LoadedReads.RunStore calls E ∧ LoadedReads.HashedRecordsStored calls E := by
  rcases Claim.noColl_or_hashedCollision V [] calls with hcol | hno
  · exact absurd hcol hnc
  · exact exists_runStore hno

/-- **A run's store agrees with a store the run hashes no collision with**, on the records and
on the blobs both hold. -/
theorem runStore_agree {calls : List (Call F)} {E E' : Ixon.Env}
    (hS : LoadedReads.RunStore calls E')
    (hnc : ¬ View.HashedCollision { env := E } [] calls) :
    (∀ a c c', recordOf E a = some c → recordOf E' a = some c' → c = c') ∧
    (∀ a b b', E.blobs.get? a = some b → E'.blobs.get? a = some b' → b = b') := by
  refine ⟨fun a c c' h h' => ?_, fun a b b' h h' => ?_⟩
  · obtain ⟨lc, hget, hdec⟩ := Typing.recordOf_some h
    obtain ⟨lc', hget', hdec'⟩ := Typing.recordOf_some h'
    obtain ⟨hh, ha⟩ := hS.loaded.1 a lc' hget'
    have hbytes := Core.load_escape hget hnc lc'.rawBytes hh ha
    rw [hbytes, hdec] at hdec'
    exact Except.ok.inj hdec'
  · obtain ⟨hh, ha⟩ := hS.loaded.2 a b' h'
    by_cases heq : b' = b
    · exact heq.symm
    · exact absurd (.inl ⟨a, b, b', .inl (.inr (.inl h)), hh, heq, ha⟩) hnc

/-- **The certificate over one store and a use over another give the firing**, where the two
stores agree on the records and blobs both hold: the raw telescopes read from them are one,
and the two raw dictionaries extend to the dictionary of the joint store. -/
theorem fireSem_of_cert_use {E E' : Ixon.Env}
    (hr : ∀ a c c', recordOf E a = some c → recordOf E' a = some c' → c = c')
    (hb : ∀ a b b', E.blobs.get? a = some b → E'.blobs.get? a = some b' → b = b')
    {B : _root_.Address} {i : Nat} {raw raw' cty : Expr .anon} {tbl : ProjTable .anon}
    {f : Nat} {g : Level} {us : List Level}
    (hraw : ctorRaw E B i 0 = some raw)
    (cert : ProjGuardCert (GuardRaw.ofStore E) raw cty tbl)
    (hraw' : ctorRaw E' B i 0 = some raw')
    (use : ProjGuardUse (GuardRaw.ofStore E') raw' cty tbl.numParams f g)
    (hf : f < tbl.numFields)
    (hzero : ∀ φ : Ix.Kernel.LevelParam → Nat,
      Level.eval φ (Level.subst tbl.levelParams us g) = 0) :
    Ix.Kernel.Rules.FireSem (tbl.entry f) us := by
  have common := GuardRaw.common_lookup hr hb
  have lift : ∀ {X : Ixon.Env} {r : Expr .anon},
      (∀ a c, recordOf X a = some c → ReaderReads.storeOver E E' a = some c) →
      (∀ a bs, X.blobs.get? a = some bs → ReaderReads.blobOver E E' a = some bs) →
      ctorRaw X B i 0 = some r →
      (GuardRaw.memberRoot (ReaderReads.storeOver E E') B i (GuardRaw.constructorType 0)).bind
        (GuardRaw.readRoot (ReaderReads.blobOver E E')) = some r := by
    intro X r hs hbl h
    unfold ctorRaw at h
    obtain ⟨root, hroot, hread⟩ := Option.bind_eq_some_iff.mp h
    exact Option.bind_eq_some_iff.mpr
      ⟨root, GuardRaw.memberRoot_mono hs hroot, GuardRaw.readRoot_mono hbl hread⟩
  have left := lift (fun _ _ h => ReaderReads.storeOver_left h)
    (fun _ _ h => ReaderReads.blobOver_left h) hraw
  have right := lift (fun _ _ h => ReaderReads.storeOver_right hr h)
    (fun _ _ h => ReaderReads.blobOver_right hb h) hraw'
  have hsame : raw' = raw := Option.some.inj (right.symm.trans left)
  subst hsame
  exact cert.fireSem common.1 common.2 use hf hzero

end IxVM.Refinement.Guard
