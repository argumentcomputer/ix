import IxVMRefinement.Assembly.TypingDefnStep

/-! # The step of a definition block

A unit is one record; a block of definitions is one unit, and its step installs the block's
members one at a time. `unitStep_defnBlock` proves the skeleton's `UnitStep` for a block
record every member of which is a definition (`DefnBlock`).

The order is the members' index order. Member `k` is installed by `memberStep` at the
prefix that holds members `0, …, k - 1` on top of the step's environment: its check evidence
at that prefix (`mutsMemberAt_defn_step`), the walked-constant step there
(`Decl.walkedConst_step`), and the reload of the member at the step's store. The references
the block uses are stored at the step's environment, hence at every longer prefix
(`usedRefsStored_append`); the member's key is fresh there because the step's environment
does not store it and the members installed before have other keys: distinct members of a
block the run's store holds have distinct constant addresses (`memberAddr_inj`: their
projection records differ in the index), and keys identify addresses. The constants the
step installs are `[cₛ₋₁, …, c₀]` (`s` the number of members), each at its member's key.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo)

/-- **A block of definitions**: every member is a definition. -/
def DefnBlock (ms : Array Ixon.MutConst) : Prop :=
  ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m → ∃ d : Ixon.Definition, m = .defn d

private theorem toUInt64_toNat_b {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- Two definition members' projection records of one block are equal only at one index. -/
theorem memberIdx_eq {B : _root_.Address} {i j : Nat} {di dj : Ixon.Definition}
    (hi : i < UInt64.size) (hj : j < UInt64.size)
    (h : memberProjection B i (.defn di) = memberProjection B j (.defn dj)) : i = j := by
  have h1 : (memberProjection B i (.defn di)).info = .dPrj ⟨i.toUInt64, B⟩ := rfl
  have h2 : (memberProjection B j (.defn dj)).info = .dPrj ⟨j.toUInt64, B⟩ := rfl
  rw [h, h2] at h1
  injection h1 with h3
  injection h3 with h4
  have h5 := congrArg UInt64.toNat h4
  rw [toUInt64_toNat_b hj, toUInt64_toNat_b hi] at h5
  exact h5.symm

/-- **Distinct definition members of a block the store holds have distinct constant
addresses**: the store holds each member's projection record at its address. -/
theorem memberAddr_inj {E₀ : Ixon.Env} {B : _root_.Address} {i j : Nat}
    {di dj : Ixon.Definition} (hi : i < UInt64.size) (hj : j < UInt64.size)
    (hri : Ix.Cert.recordAt E₀ (memberAddr B i (.defn di)) =
      some (memberProjection B i (.defn di)))
    (hrj : Ix.Cert.recordAt E₀ (memberAddr B j (.defn dj)) =
      some (memberProjection B j (.defn dj)))
    (h : memberAddr B i (.defn di) = memberAddr B j (.defn dj)) : i = j := by
  rw [h, hrj] at hri
  exact memberIdx_eq hi hj (Option.some.inj hri).symm

/-- The references a record uses, stored at an environment, are stored at every longer
prefix. -/
theorem usedRefsStored_append {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {c : Ixon.Constant} (h : Decl.UsedRefsStored t env c) :
    ∀ acc : List (ConstantInfo .anon), Decl.UsedRefsStored t ⟨acc ++ env.consts⟩ c := by
  intro acc
  induction acc with
  | nil => exact h
  | cons cn acc ih => exact LoadedReads.usedRefsStored_cons cn ih

section Block

variable {X : Ix.Kernel.Env .anon → Prop} {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
  {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant}
  {ms : Array Ixon.MutConst} {n : Nat}

/-- **The step of one member of a definition block**, at a prefix with the invariant at the
limit of the member's check, the extra clause, the block's used references stored, and the
member's key fresh: one constant at the member's key, storing a reading of the member's
address, keeps both. -/
theorem memberStep (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hrecB : Ix.Cert.recordAt E₀ B = some cb) (hmuts : cb.info = .muts ms)
    (hlogic : InLogic cb) {k : Nat} {d : Ixon.Definition} (hk : ms[k]? = some (.defn d))
    (hm : MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hkey : Decl.KeyFree (keyOf t (memberAddr B k (.defn d)))) (hX : KeepsValues X)
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t (some n) env) (hXe : X env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (keyOf t (memberAddr B k (.defn d))) = none) :
    ∃ cn ci₀ : ConstantInfo .anon, cn.name = keyOf t (memberAddr B k (.defn d)) ∧
      Reads t E₀ (memberAddr B k (.defn d)) ci₀ ∧ StoredAs cn ci₀ ∧
      Decl.PrefixInv.{u} E t (some n) ⟨cn :: env.consts⟩ ∧ X ⟨cn :: env.consts⟩ := by
  have hbound : Bounded calls := (hst.good env none).2
  obtain ⟨hk64, -, hrecM⟩ := LoadedReads.mutsMember_record hbound hS hcov
    (mutsMemberCheckedAtFull_iff.mpr ⟨n, hm⟩) hk
  obtain ⟨ty₀, val₀, ty', val', hannT, hannV, hall⟩ :=
    mutsMemberAt_defn_step (order_role := []) ht hbound hS hcov hrecB hmuts hk hlogic
      List.not_mem_nil hm E hstored
  obtain ⟨hev, hreads, hreload⟩ := hall (.regular 0)
  have hfreshD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀
      (.regular 0)), env.find? ci₀.name = none := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hfresh
  have hkeyD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀
      (.regular 0)), Decl.KeyFree ci₀.name := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hkey
  obtain ⟨-, htrans⟩ := Decl.walkedConst_step hinv hev (hst.good env none) hfreshD hkeyD
    (fun cv h => absurd h (LoadedReads.defnDecl_ne_axiomDecl _ _ _ _ cv))
  have hprojE : recordOf E (memberAddr B k (.defn d)) =
      some (memberProjection B k (.defn d)) :=
    hst.held (hS.recordOf_of_recordAt hrecM)
  have hblockE : recordOf E B = some cb := hst.held (hS.recordOf_of_recordAt hrecB)
  have hinv' := htrans E (some n) (hreload E hprojE hblockE hst.runBlob) hinv
  rw [LoadedReads.installs_defnDecl] at hinv'
  have hname : (LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)).name = keyOf t (memberAddr B k (.defn d)) :=
    LoadedReads.defnConst_name _ _ _ _
  refine ⟨LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' (.regular 0),
    LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0),
    hname, hreads, storedAs_defnConst _ _ _ _ hannT hannV, hinv', ?_⟩
  exact hX env (LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' (.regular 0)) hXe
    (by rw [hname]; exact hfresh) (isValueConst_defnConst _ _ _ _)

/-- **The members `0, …, m - 1` installed**, in index order, at the front of `env`: the
installed constants `acc` have distinct fresh keys, the prefix keeps the invariant and the
extra clause, each of the members has a constant storing a reading of its address, and each
installed constant is at the key of one of them. -/
structure MembersDone (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (E₀ E : Ixon.Env) (lim : Option Nat) (env : Ix.Kernel.Env .anon) (B : _root_.Address)
    (ms : Array Ixon.MutConst) (m : Nat) (acc : List (ConstantInfo .anon)) : Prop where
  nodup : (acc.map (·.name)).Nodup
  fresh : ∀ ci ∈ acc, env.find? ci.name = none
  inv : Decl.PrefixInv.{u} E t lim ⟨acc ++ env.consts⟩
  extra : X ⟨acc ++ env.consts⟩
  done : ∀ i mi, i < m → ms[i]? = some mi → ∃ ci ∈ acc, ∃ ci₀,
    ci.name = keyOf t (memberAddr B i mi) ∧ Reads t E₀ (memberAddr B i mi) ci₀ ∧
      StoredAs ci ci₀
  named : ∀ ci ∈ acc, ∃ i mi, i < m ∧ ms[i]? = some mi ∧ ci.name = keyOf t (memberAddr B i mi)

/-- **`UnitStep` for a block of definitions.** The run's store `E₀` is a run store that holds
every record the run hashed, and holds the block `cb` at `B`, in Lean's logic, every member a
definition; the walk checked every member under a role context at the limit `n`, the walk's
(`hlim`); every member's key is free; no reference the block uses is an inert axiom's; and at
every environment the skeleton hands the step, the block's other used references are stored.
Then the step at `B` holds against any store `E` the step runs against, for any extra clause
kept by storing a value constant. The members are installed in index order (module
docstring). -/
theorem unitStep_defnBlock {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ B = some cb) (hmuts : cb.info = .muts ms) (hlogic : InLogic cb)
    (hdefs : DefnBlock ms)
    (hchk : ∀ k, k < ms.size → MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hlim : lim = some n)
    (hkey : ∀ i m, ms[i]? = some m → Decl.KeyFree (keyOf t (memberAddr B i m)))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hX : KeepsValues X) :
    UnitStep.{u} X t envT E₀ E lim B cb := by
  subst hlim
  intro env hext hnd hinv hXe href hfresh
  have hbound : Bounded calls := (hst.good env none).2
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hrecB : Ix.Cert.recordAt E₀ B = some cb := (hS.recordOf_eq_recordAt B).symm.trans hc
  have hstored : Decl.UsedRefsStored t env cb :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  have hmem : ∀ i mi, ms[i]? = some mi → i < UInt64.size ∧
      Ix.Cert.recordAt E₀ (memberAddr B i mi) = some (memberProjection B i mi) := by
    intro i mi h
    obtain ⟨h1, -, h3⟩ := LoadedReads.mutsMember_record hbound hS hcov
      (mutsMemberCheckedAtFull_iff.mpr ⟨n, hchk i (Array.getElem?_eq_some_iff.mp h).1⟩) h
    exact ⟨h1, h3⟩
  have hfreshM : ∀ i mi, ms[i]? = some mi → env.find? (keyOf t (memberAddr B i mi)) = none :=
    fun i mi h => hfresh _ (Or.inr ⟨ms, i, mi, hmuts, h, Or.inl rfl⟩)
  have hdistinct : ∀ i j mi mj, ms[i]? = some mi → ms[j]? = some mj →
      keyOf t (memberAddr B i mi) = keyOf t (memberAddr B j mj) → i = j := by
    intro i j mi mj hi hj hk
    obtain ⟨di, rfl⟩ := hdefs i mi hi
    obtain ⟨dj, rfl⟩ := hdefs j mj hj
    obtain ⟨hi64, hri⟩ := hmem i _ hi
    obtain ⟨hj64, hrj⟩ := hmem j _ hj
    exact memberAddr_inj hi64 hj64 hri hrj (keyOf_inj hroles hk)
  have hfold : ∀ m, m ≤ ms.size → ∃ acc, MembersDone.{u} X t E₀ E (some n) env B ms m acc := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨[], List.nodup_nil, (fun _ h => nomatch h), hinv, hXe,
        (fun i mi hi _ => absurd hi (Nat.not_lt_zero _)), (fun _ h => nomatch h)⟩
    | succ m ih =>
      intro hm
      obtain ⟨acc, hacc⟩ := ih (by omega)
      have hlt : m < ms.size := by omega
      obtain ⟨mi, hmi⟩ : ∃ mi, ms[m]? = some mi := ⟨ms[m], Array.getElem?_eq_getElem hlt⟩
      obtain ⟨d, rfl⟩ := hdefs m mi hmi
      have hnotacc : ∀ ci ∈ acc, ci.name ≠ keyOf t (memberAddr B m (.defn d)) := by
        intro ci hci he
        obtain ⟨i, mj, hi, hmj, hn⟩ := hacc.named ci hci
        have hieq := hdistinct i m mj (.defn d) hmj hmi (hn.symm.trans he)
        omega
      have hfreshCur : (⟨acc ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
          (keyOf t (memberAddr B m (.defn d))) = none := by
        apply find_none_of_not_storedAt
        rintro ⟨ci, hci, hn⟩
        have hci' : ci ∈ acc ++ env.consts := hci
        rcases List.mem_append.mp hci' with hca | hce
        · exact hnotacc ci hca hn
        · have hs := find_isSome_of_storedAt (t := t) (env := env)
            (x := memberAddr B m (.defn d)) ⟨ci, hce, hn⟩
          rw [hfreshM m _ hmi] at hs
          simp at hs
      obtain ⟨cn, ci₀, hname, hreads, hsto, hinv', hX'⟩ :=
        memberStep ht hS hcov hst hrecB hmuts hlogic hmi (hchk m hlt) (hkey m _ hmi) hX
          hacc.inv hacc.extra (usedRefsStored_append hstored acc) hfreshCur
      refine ⟨cn :: acc, ?_, ?_, hinv', hX', ?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmemn => ?_, hacc.nodup⟩
        obtain ⟨ci, hci, he⟩ := List.mem_map.mp hmemn
        exact hnotacc ci hci (he.trans hname)
      · intro ci hci
        rcases List.mem_cons.mp hci with hcn | hci'
        · rw [hcn, hname]
          exact hfreshM m _ hmi
        · exact hacc.fresh ci hci'
      · intro i mj hi hmj
        by_cases hi' : i < m
        · obtain ⟨ci, hci, ci₀', h1, h2, h3⟩ := hacc.done i mj hi' hmj
          exact ⟨ci, List.mem_cons_of_mem _ hci, ci₀', h1, h2, h3⟩
        · have hieq : i = m := by omega
          rw [hieq] at hmj
          rw [hmi] at hmj
          rw [hieq, ← Option.some.inj hmj]
          exact ⟨cn, List.mem_cons_self, ci₀, hname, hreads, hsto⟩
      · intro ci hci
        rcases List.mem_cons.mp hci with hcn | hci'
        · rw [hcn]
          exact ⟨m, _, Nat.lt_succ_self m, hmi, hname⟩
        · obtain ⟨i, mj, hi, hmj, hn⟩ := hacc.named ci hci'
          exact ⟨i, mj, Nat.lt_succ_of_lt hi, hmj, hn⟩
  obtain ⟨acc, hacc⟩ := hfold ms.size (Nat.le_refl _)
  refine ⟨acc, hacc.nodup, hacc.fresh, hacc.inv, hacc.extra, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨-, hs⟩ | ⟨ms', i, mi, hms', hmi, hx⟩
    · exact (standalone_not_block hs ⟨ms, hmuts⟩).elim
    · rw [hmuts] at hms'
      have hmm : ms = ms' := Ixon.ConstantInfo.muts.inj hms'
      subst hmm
      rcases hx with hx | ⟨ind, j, hind, -, -⟩
      · rw [hx]
        exact hacc.done i mi (Array.getElem?_eq_some_iff.mp hmi).1 hmi
      · obtain ⟨d, hd⟩ := hdefs i mi hmi
        rw [hd] at hind
        cases hind
  · intro ci hci
    obtain ⟨i, mi, -, hmi, hn⟩ := hacc.named ci hci
    exact Or.inl ⟨memberAddr B i mi, Or.inr ⟨ms, i, mi, hmuts, hmi, Or.inl rfl⟩, hn⟩

/-- **`UnitStep` for a block of definitions, from the walk**: as `unitStep_defnBlock` at the
skeleton's step context, with the cover clause from the walk (`coverAt_of_graph`). -/
theorem unitStep_defnBlock_of_graph {R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {seeds : List _root_.Address} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hctx : StepCtx.{u} calls t R envT E₀ E) (hG : TopGraph t E₀ seeds Top rank) (hT : Top B)
    (hc : recordOf E₀ B = some cb) (hmuts : cb.info = .muts ms) (hlogic : InLogic cb)
    (hdefs : DefnBlock ms)
    (hchk : ∀ k, k < ms.size → MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hlim : lim = some n)
    (hkey : ∀ i m, ms[i]? = some m → Decl.KeyFree (keyOf t (memberAddr B i m)))
    (hinert : InertClause t cb)
    (hneed : ∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
      inertKey (keyOf t x) = false → ¬ Covered t x → NeedOk E₀ x)
    (hX : KeepsValues X) :
    UnitStep.{u} X t envT E₀ E lim B cb := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  exact unitStep_defnBlock ht hS hcov hctx.toStepStore hc hmuts hlogic hdefs hchk hlim hkey
    hinert (coverAt_of_graph hG hctx.shape htwf hT hc hneed) hX

end Block

end IxVM.Refinement.Typing
