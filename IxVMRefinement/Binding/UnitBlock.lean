import IxVMRefinement.Binding.UnitDefn
import IxVMRefinement.Assembly.TypingDefnBlock

/-! # The step of a definition block, in the binding fold

`bUnitStep_defnBlock` proves `BUnitStep` for a block record every member of which is a
definition, from the inputs of the typing skeleton's `unitStep_defnBlock`. The members are
installed in index order at one store `Ec` for `R` (`bMemberStep`, the walked-constant step of
one member), and the fold carries, besides the prefix invariant at `Ec`, the composed transport
to every store for `R` and every limit, and the extra clause at every store for `R`. A member's
record reloads at a store for `R` when `R` holds the block record and the member's projection
record (`hRm`: `R` holds a record at each member's address; it is the projection record, since
`R` holds only records the run loaded).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

section Block

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {R E₀ Ec : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {n : Nat}

/-- **The step of one member of a definition block, in the binding fold**: at a prefix with the
invariant at the store `Ec` and the limit of the member's check, the block's used references
stored, and the member's key fresh, one value constant at the member's key that stores a reading
of the member's address, and the transport of the prefix invariant past it at every store for
`R` and every limit. -/
theorem bMemberStep (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ Ec)
    (hrecB : Ix.Cert.recordAt E₀ B = some cb) (hmuts : cb.info = .muts ms)
    (hlogic : InLogic cb) {k : Nat} {d : Ixon.Definition} (hk : ms[k]? = some (.defn d))
    (hm : MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hkey : Decl.KeyFree (keyOf t (memberAddr B k (.defn d))))
    (hRB : recordOf R B = some cb)
    (hRM : recordOf R (memberAddr B k (.defn d)) = some (memberProjection B k (.defn d)))
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b)
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} Ec t (some n) env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (keyOf t (memberAddr B k (.defn d))) = none) :
    ∃ cn ci₀ : Ix.Kernel.ConstantInfo .anon, cn.name = keyOf t (memberAddr B k (.defn d)) ∧
      Reads t E₀ (memberAddr B k (.defn d)) ci₀ ∧ StoredAs cn ci₀ ∧ IsValueConst cn ∧
      ∀ E, RecordsFor R E → ∀ lim, Decl.PrefixInv.{u} E t lim env →
        Decl.PrefixInv.{u} E t lim ⟨cn :: env.consts⟩ := by
  have hbound : Bounded calls := (hst.good env none).2
  obtain ⟨ty₀, val₀, ty', val', hannT, hannV, hall⟩ :=
    mutsMemberAt_defn_step (order_role := []) ht hbound hS hcov hrecB hmuts hk hlogic
      List.not_mem_nil hm Ec hstored
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
  have hname : (LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)).name = keyOf t (memberAddr B k (.defn d)) :=
    LoadedReads.defnConst_name _ _ _ _
  refine ⟨LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' (.regular 0),
    LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0),
    hname, hreads, storedAs_defnConst _ _ _ _ hannT hannV, isValueConst_defnConst _ _ _ _, ?_⟩
  intro E hE lim h
  have h' := htrans E lim (hreload E (recordOf_of_recordsFor hE hRM)
    (recordOf_of_recordsFor hE hRB) (blob_of_recordsFor hE hblobs)) h
  rw [LoadedReads.installs_defnDecl] at h'
  exact h'

/-- **The members `0, …, m - 1` installed, in the binding fold**, in index order, at the front
of `env`: `MembersDone` with the prefix invariant at the store `Ec`, the transport of the prefix
invariant from `env` at every store for `R` and every limit, the extra clause at every store for
`R`, and every installed constant a value constant. -/
structure BMembersDone (Y : Ixon.Env → Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (R E₀ Ec : Ixon.Env) (n : Nat) (env : Ix.Kernel.Env .anon) (B : _root_.Address)
    (ms : Array Ixon.MutConst) (m : Nat) (acc : List (Ix.Kernel.ConstantInfo .anon)) : Prop where
  nodup : (acc.map (·.name)).Nodup
  fresh : ∀ ci ∈ acc, env.find? ci.name = none
  value : ∀ ci ∈ acc, IsValueConst ci
  inv : Decl.PrefixInv.{u} Ec t (some n) ⟨acc ++ env.consts⟩
  trans : ∀ E, RecordsFor R E → ∀ lim, Decl.PrefixInv.{u} E t lim env →
    Decl.PrefixInv.{u} E t lim ⟨acc ++ env.consts⟩
  extra : ∀ E, RecordsFor R E → Y E ⟨acc ++ env.consts⟩
  done : ∀ i mi, i < m → ms[i]? = some mi → ∃ ci ∈ acc, ∃ ci₀,
    ci.name = keyOf t (memberAddr B i mi) ∧ Reads t E₀ (memberAddr B i mi) ci₀ ∧
      StoredAs ci ci₀
  named : ∀ ci ∈ acc, ∃ i mi, i < m ∧ ms[i]? = some mi ∧ ci.name = keyOf t (memberAddr B i mi)

/-- **`BUnitStep` for a block of definitions.** The inputs about the block and its checks are
`unitStep_defnBlock`'s. About the stores: `Ec` is a store for `R` the checks are read at
(`StepStore`); `R` holds the block record at `B` and a record at each member's address, only
records the run loaded, and every blob the run loaded. -/
theorem bUnitStep_defnBlock {Y : Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {envT : Ix.Kernel.Env .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hRc : RecordsFor R Ec) (hst : StepStore calls t E₀ Ec)
    (hR : recordOf R B = some cb)
    (hRm : ∀ i mi, ms[i]? = some mi → (recordOf R (memberAddr B i mi)).isSome = true)
    (hloaded : ∀ a lc, R.consts.get? a = some lc → E₀.consts.get? a = some lc)
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b)
    (hmuts : cb.info = .muts ms) (hlogic : InLogic cb) (hdefs : DefnBlock ms)
    (hchk : ∀ k, k < ms.size → MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hkey : ∀ i m, ms[i]? = some m → Decl.KeyFree (keyOf t (memberAddr B i m)))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hY : ∀ E, KeepsValues (Y E)) :
    BUnitStep.{u} Y t R envT E₀ n B cb := by
  intro env hext hnd hinv hguard hYe href hfresh
  have hc : recordOf E₀ B = some cb := recordOf_of_loaded hloaded hR
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
  have hRm' : ∀ i mi, ms[i]? = some mi →
      recordOf R (memberAddr B i mi) = some (memberProjection B i mi) := by
    intro i mi h
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (hRm i mi h)
    have h1 := recordOf_of_loaded hloaded hc'
    rw [hS.recordOf_of_recordAt (hmem i mi h).2] at h1
    exact hc'.trans h1.symm
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
  have hfold : ∀ m, m ≤ ms.size → ∃ acc, BMembersDone.{u} Y t R E₀ Ec n env B ms m acc := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨[], List.nodup_nil, (fun _ h => nomatch h), (fun _ h => nomatch h), hinv Ec hRc,
        (fun E hE lim h => h), hYe, (fun i mi hi _ => absurd hi (Nat.not_lt_zero _)),
        (fun _ h => nomatch h)⟩
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
      obtain ⟨cn, ci₀, hname, hreads, hsto, hval, htr⟩ :=
        bMemberStep ht hS hcov hst hrecB hmuts hlogic hmi (hchk m hlt) (hkey m _ hmi) hR
          (hRm' m _ hmi) hblobs hacc.inv (usedRefsStored_append hstored acc) hfreshCur
      refine ⟨cn :: acc, ?_, ?_, ?_, htr Ec hRc (some n) hacc.inv, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmemn => ?_, hacc.nodup⟩
        obtain ⟨ci, hci, he⟩ := List.mem_map.mp hmemn
        exact hnotacc ci hci (he.trans hname)
      · intro ci hci
        rcases List.mem_cons.mp hci with hcn | hci'
        · rw [hcn, hname]
          exact hfreshM m _ hmi
        · exact hacc.fresh ci hci'
      · intro ci hci
        rcases List.mem_cons.mp hci with hcn | hci'
        · rw [hcn]
          exact hval
        · exact hacc.value ci hci'
      · intro E hE lim h
        exact htr E hE lim (hacc.trans E hE lim h)
      · intro E hE
        exact hY E _ cn (hacc.extra E hE) (by rw [hname]; exact hfreshCur) hval
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
  refine ⟨acc, hacc.nodup, hacc.fresh, fun E hE lim h _ => hacc.trans E hE lim h, ?_,
    hacc.extra, ?_, ?_, ?_⟩
  · intro E hE lim
    exact guardAt_append (hguard E hE lim) (hinv E hE) hacc.fresh
      (fun ci hci => noCtorProj_of_isValueConst (hacc.value ci hci))
  · intro ci hci
    obtain ⟨i, mi, -, hmi, hn⟩ := hacc.named ci hci
    rw [hn]
    exact not_mem_opNames_of_keyFree (hkey i mi hmi)
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

end Block

end IxVM.Refinement.Binding
