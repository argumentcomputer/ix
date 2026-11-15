import IxVMRefinement.Assembly.RecordReadBare

/-! # Role-aware bare reader bridge and concrete `DeclOrigin` seam (`Bridge`)

Instantiates `WalkedBareBridgeRole` at the concrete declaration-origin predicate `DeclOrigin` (with
zero `Core.LoadFacts` inside `DeclOrigin`, since `LoadFacts` is carried by the prefix fold invariant
`Inv` in `DeclsStrong`) and connects it to `ConsistentReadRole`:

1. **`DeclOriginAt` & `DeclOrigin`**: packages `DeclNonAux`, installed-name `Nodup` and prefix
   freshness in `env_pre`, `TableAdmittedAt` on the admitted role table `b`, `Core.Good`,
   `L1.EnvDecoded`, and `¬ L1.EnvInternalCollision` on the shared store `E_core`, the full bare
   stream witness `StreamReadBare`, `Installs ds_pre env_pre`, and the disjunction between role
   declarations (`preparePrelude pre.ix decls_role`) and walked declarations (`WalkedStepOrigin`,
   carrying `CheckedConstOrigin ∨ CheckedIndOrigin` and prefix `L1.RecordReadsAs` + `StoredAs`).
2. **`walkedBareBridgeRole_declOrigin`**: discharges `WalkedBareBridgeRole DeclOrigin` from
   `RolePreludeInputs` and `SafeRefsInputs` via `walkedStreamReadBare`, `preparePrelude_declNonAux`,
   and `installs_prefix_fresh`.
3. **`consistentReadRole_of_rolePrelude_declsStrong`**: combines `walkedBareBridgeRole_declOrigin`
   with `consistentReadRole_of_declsStrong` to derive `ConsistentReadRole V calls b seeds` from
   `DeclsStrong DeclOrigin`. -/

set_option maxHeartbeats 800000

universe u

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-- Unpacked per-declaration origin witness at fixed stream and store parameters (with zero
`Core.LoadFacts`). -/
structure DeclOriginAt
    (calls : List (Call F)) (env_pre : Ix.Kernel.Env .anon) (d : Ix.Kernel.Declaration .anon)
    (clm : Ix.Claim) (V : IxVM.Refinement.View) (extra : List ByteArray)
    (b : Ix.Kernel.Admission.Binding) (t : Ix.Kernel.RoleTable)
    (E₀ E E_role E_core : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (order order_role seeds : List _root_.Address)
    (envA : Ix.Kernel.Env .anon) (pre : Ix.Kernel.Reader.Prelude .anon)
    (st_role st' : Ix.Kernel.Reader.State .anon)
    (decls_role decls : Array (Ix.Kernel.Reader.CDecl .anon))
    (ds_pre ds_suf : List (Ix.Kernel.Declaration .anon)) : Prop where
  nonAux : DeclNonAux d
  nodup_installs : ((IxVM.Consistency.installs d).map (·.name)).Nodup
  fresh_in_env_pre : ∀ ci₀ ∈ IxVM.Consistency.installs d, env_pre.find? ci₀.name = none
  bounded : IxVM.Consistency.Bounded calls
  inScope : IxVM.Consistency.InScope clm
  claimSeeds : IxVM.Consistency.ClaimSeeds clm V seeds
  readerTable : IxVM.Consistency.ReaderTable clm V b
  tableAdmitted : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role
  loadedBy : IxVM.Consistency.LoadedBy calls E₀
  seedOk : ∀ a ∈ seeds, ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a
  walkedL6 : Claim.WalkedL6 calls t E₀ seeds
  binding_extra : b.bytes ∈ extra
  committed_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra
  noCollision : ¬ V.HashedCollision extra calls
  drawsRole : DrawsRoleLocal E E₀ V.env
  usedClosureOrder :
    IxVM.Consistency.UsedClosureOrderAt t E
      (fun a => a ∈ seeds ∨ IxVM.Refinement.BindingSeeds t a) order
  authentic_consts : ∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a
  authentic_blobs : ∀ a bytes, E.blobs.get? a = some bytes → _root_.Address.blake3Pure bytes = a
  exact_order :
    ∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c
  good_core : Core.Good ⟨E_core, env_pre, t, none⟩ calls
  envDecoded_core : L1.EnvDecoded E_core
  noInternalCollision_core : ¬ L1.EnvInternalCollision E_core
  sub_recordAt_core :
    ∀ x c_x, Ix.Cert.recordAt E x = some c_x → Ix.Cert.recordAt E_core x = some c_x
  fallback_recordAt_core :
    ∀ a c_f, (a, c_f) ∈ pre.records ++ pre.evidence → Ix.Cert.recordAt E_core a = some c_f
  blobs_core : E_core.blobs = E.blobs
  streamReadBare :
    StreamReadBare
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
      pre.state (Ix.Cert.Stream.decodedOf E order) st' decls
  keepsPrelude : Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true
  prepare_split : (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList = ds_pre ++ d :: ds_suf
  inst_pre : IxVM.Consistency.Installs ds_pre env_pre
  origin :
    (∃ ds_role_suf,
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList = ds_pre ++ d :: ds_role_suf) ∨
    WalkedStepOrigin calls b t E₀ E E_core pre order order_role ds_pre env_pre d

/-- Concrete declaration-check seam for `WalkedBareBridgeRole` and `DeclsStrong` (zero
`Core.LoadFacts`). -/
def DeclOrigin (calls : List (Call F)) (env_pre : Ix.Kernel.Env .anon)
    (d : Ix.Kernel.Declaration .anon) : Prop :=
  ∃ clm V extra b t E₀ E E_role E_core limits order order_role seeds
    envA pre st_role st' decls_role decls ds_pre ds_suf,
    DeclOriginAt calls env_pre d clm V extra b t E₀ E E_role E_core limits order order_role seeds
      envA pre st_role st' decls_role decls ds_pre ds_suf

theorem DeclOrigin.nonAux {calls : List (Call F)} {env_pre : Ix.Kernel.Env .anon}
    {d : Ix.Kernel.Declaration .anon} (h : DeclOrigin calls env_pre d) : DeclNonAux d := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ho⟩ := h
  exact ho.nonAux

theorem DeclOrigin.nodup_installs {calls : List (Call F)} {env_pre : Ix.Kernel.Env .anon}
    {d : Ix.Kernel.Declaration .anon} (h : DeclOrigin calls env_pre d) :
    ((IxVM.Consistency.installs d).map (·.name)).Nodup := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ho⟩ := h
  exact ho.nodup_installs

theorem DeclOrigin.fresh_in_env_pre {calls : List (Call F)} {env_pre : Ix.Kernel.Env .anon}
    {d : Ix.Kernel.Declaration .anon} (h : DeclOrigin calls env_pre d) :
    ∀ ci₀ ∈ IxVM.Consistency.installs d, env_pre.find? ci₀.name = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ho⟩ := h
  exact ho.fresh_in_env_pre

/-- **Instantiation of `WalkedBareBridgeRole` at `DeclOrigin`** from `RolePreludeInputs` and
`SafeRefsInputs`. -/
theorem walkedBareBridgeRole_declOrigin
    (hRP : RolePreludeInputs) (hSR : SafeRefsInputs) :
    WalkedBareBridgeRole DeclOrigin := by
  intro calls clm b t E₀ seeds V extra
    hbound hscope hseeds_clm hrt hadmV hadm hload hseedOk hwalk hb_extra hcomm_extra hnoCol
  obtain ⟨E, E_role, E_core, limits, order, order_role, envA, pre, st_role, st',
    decls_role, decls, hadm_at, hdraws, hord, hpre, hauth_rec, hauth_blob, hdec,
    hdec_core, hnoInt_core, hgood_core, hsub_rec, hfb_rec, hblobs_core,
    hreads, hkeeps, hnd_flat, horig, hseeds⟩ :=
    walkedStreamReadBare hRP hSR hbound hadmV hadm hload hseedOk hwalk hcomm_extra hnoCol
  have hna_all : ∀ d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList, DeclNonAux d :=
    preparePrelude_declNonAux hpre hreads
  refine ⟨E, order, pre, st', decls, hdraws, hord, hpre, hauth_rec, hauth_blob, hdec,
    hreads, hkeeps, ?_, hseeds⟩
  intro ds_pre d ds_suf env_pre hsp hinst
  have hd_mem : d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList := by
    rw [hsp]
    simp
  have hd_na : DeclNonAux d := hna_all d hd_mem
  have hdisj :
      ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∀ d₀ ∈ ds_pre, ∀ ci₁ ∈ IxVM.Consistency.installs d₀, ci₁.name ≠ ci₀.name := by
    have hnd := hnd_flat
    rw [hsp, List.flatMap_append, List.flatMap_cons, List.nodup_append] at hnd
    intro ci₀ hci₀ d₀ hd₀ ci₁ hci₁
    exact hnd.2.2 ci₁.name
      (List.mem_flatMap.mpr ⟨d₀, hd₀, List.mem_map.mpr ⟨ci₁, hci₁, rfl⟩⟩)
      ci₀.name
      (List.mem_append_left _ (List.mem_map.mpr ⟨ci₀, hci₀, rfl⟩))
  obtain ⟨hfresh, hnd_d⟩ := installs_prefix_fresh hinst hd_na hdisj
  exact ⟨clm, V, extra, b, t, E₀, E, E_role, E_core, limits, order, order_role, seeds,
    envA, pre, st_role, st', decls_role, decls, ds_pre, ds_suf,
    ⟨hd_na, hnd_d, hfresh, hbound, hscope, hseeds_clm, hrt, hadm_at, hload, hseedOk, hwalk,
      hb_extra, hcomm_extra, hnoCol, hdraws, hord, hauth_rec, hauth_blob, hdec,
      hgood_core env_pre, hdec_core, hnoInt_core, hsub_rec, hfb_rec, hblobs_core,
      hreads, hkeeps, hsp, hinst, horig ds_pre d ds_suf env_pre hsp hinst⟩⟩

/-- **`ConsistentReadRole` from `RolePreludeInputs`, `SafeRefsInputs`, and `DeclsStrong DeclOrigin`**. -/
theorem consistentReadRole_of_rolePrelude_declsStrong
    (hRP : RolePreludeInputs) (hSR : SafeRefsInputs)
    (hStrong : DeclsStrong.{u} DeclOrigin)
    {calls : List (Call F)} {clm : Ix.Claim} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {V : IxVM.Refinement.View} {extra : List ByteArray}
    (hbound : IxVM.Consistency.Bounded calls)
    (hscope : IxVM.Consistency.InScope clm)
    (hseeds_clm : IxVM.Consistency.ClaimSeeds clm V seeds)
    (hrt : IxVM.Consistency.ReaderTable clm V b)
    (hadmV : TableAdmittedComplete V b)
    (hadm : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hseedOk : ∀ a ∈ seeds, ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a)
    (hwalk : Claim.WalkedL6 calls t E₀ seeds)
    (hb_extra : b.bytes ∈ extra)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hnoCol : ¬ V.HashedCollision extra calls) :
    ConsistentReadRole.{u} V calls b seeds :=
  consistentReadRole_of_declsStrong hStrong (walkedBareBridgeRole_declOrigin hRP hSR)
    hbound hscope hseeds_clm hrt hadmV hadm hload hseedOk hwalk hb_extra hcomm_extra hnoCol

end IxVM.Refinement.Assembly
