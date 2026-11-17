import IxVMRefinement.Assembly.LateRegistry
import IxVMRefinement.Decl.LateWalkedConst
import IxVMRefinement.Assembly.TypingDefnBlock

/-! # The step of a definition record, keeping a clause along its declaration step

`unitStep_defn` keeps an extra clause `X` that storing a value constant keeps by itself
(`KeepsValues`). The registry of native families (`LateRegistry`) is not such a clause: it
holds a model of the environment, which the declaration step extends. `unitStep_defnJ` is
`unitStep_defn` for a clause kept along the declaration step (`KeepsValuesJ`); the step is
`Decl.walkedConst_declRunJ` of the same check evidence. `unitStep_defn_late` is it for the
registry together with any clause kept by a value constant alone. `memberStepJ`,
`unitStep_defnBlockJ` and `unitStep_defnBlock_late` are the same for a block of definitions
(`unitStep_defnBlock`, its members installed one at a time).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo)
open Ix.Kernel.Semantics (DeclRunJ IndRoutesJ)
open Ix.Kernel.Model (rulesJ)

/-- **`UnitStep` for a standalone definition, theorem or opaque record, for a clause kept
along the declaration step.** As `unitStep_defn`, with `KeepsValuesJ X` for
`KeepsValues X`. -/
theorem unitStep_defnJ {X : Ix.Kernel.Env .anon → Prop} {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {lim : Option Nat} {bAddr A : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hchk : CheckedAtFullAt calls bAddr t A n) (hlim : lim = some n)
    (hkey : Decl.KeyFree (keyOf t A))
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hX : KeepsValuesJ X) :
    UnitStep.{u} X t envT E₀ E lim A c := by
  subst hlim
  intro env hext hnd hinv hXe href hfresh
  have hbound : Bounded calls := (hst.good env none).2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  obtain ⟨ty₀, val₀, ty', val', hannT, hannV, hall⟩ :=
    checkedAtFullAt_defn_step (order_role := []) ht hbound hS hrec₀ hinfo hlogic
      List.not_mem_nil hchk E hstored
  obtain ⟨hev, hreads, hreload⟩ := hall (.regular 0)
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inl ⟨d, hinfo⟩⟩
  have hfreshA : env.find? (keyOf t A) = none := hfresh A hown
  have hfreshD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0)),
      env.find? ci₀.name = none := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hfreshA
  have hkeyD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0)),
      Decl.KeyFree ci₀.name := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hkey
  have hskip : ∀ cv, LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0) = .axiomDecl cv →
      cv.name = Ix.Kernel.quotSoundName ∨ IxVM.Consistency.inertKey cv.name = true :=
    fun cv h => absurd h (LoadedReads.defnDecl_ne_axiomDecl _ _ _ _ cv)
  obtain ⟨-, htrans⟩ := Decl.walkedConst_step hinv hev (hst.good env none) hfreshD hkeyD hskip
  have hrun := Decl.walkedConst_declRunJ hinv hev (hst.good env none) hfreshD hkeyD hskip
  have hinv' := htrans E (some n) (hreload E (hst.held hc) hst.runBlob) hinv
  rw [LoadedReads.installs_defnDecl] at hinv'
  rw [LoadedReads.installs_defnDecl] at hrun
  have hname : (LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)).name = keyOf t A :=
    LoadedReads.defnConst_name _ _ _ _
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : Ix.Kernel.Declaration .anon,
      DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d₀
        ⟨LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
          (.regular 0) :: env.consts⟩ := by
    rcases hrun with h0 | ⟨d₀, hd₀⟩
    · cases h0
    · exact ⟨d₀, hd₀⟩
  refine ⟨[LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)], List.nodup_singleton _, ?_, hinv', ?_, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    rw [hname]
    exact hfreshA
  · refine hX env (LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)) d₀ hXe (by rw [hname]; exact hfreshA) (isValueConst_defnConst _ _ _ _)
      (fun T => ?_) hd₀
    rw [hname]
    exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t A)
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨_, List.mem_singleton_self _, _, hname, hreads,
        storedAs_defnConst _ _ _ _ hannT hannV⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩

/-- **`UnitStep` for a standalone definition record, keeping the registry of native families**
together with a clause `Y` kept by storing a value constant. -/
theorem unitStep_defn_late {Y : Ix.Kernel.Env .anon → Prop} {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {lim : Option Nat} {bAddr A : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hchk : CheckedAtFullAt calls bAddr t A n) (hlim : lim = some n)
    (hkey : Decl.KeyFree (keyOf t A))
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hY : KeepsValues Y) :
    UnitStep.{u} (fun env => LateRegistry.{u} t E env ∧ Y env) t envT E₀ E lim A c :=
  unitStep_defnJ ht hS hst hc hinfo hlogic hchk hlim hkey hinert hcover
    ((keepsValuesJ_lateRegistry t E).and hY.toJ)

/-! ## A block of definitions -/

section Block

variable {X : Ix.Kernel.Env .anon → Prop} {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
  {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant}
  {ms : Array Ixon.MutConst} {n : Nat}

/-- **The step of one member of a definition block, for a clause kept along the declaration
step**: `memberStep` with `KeepsValuesJ X`. -/
theorem memberStepJ (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hrecB : Ix.Cert.recordAt E₀ B = some cb) (hmuts : cb.info = .muts ms)
    (hlogic : InLogic cb) {k : Nat} {d : Ixon.Definition} (hk : ms[k]? = some (.defn d))
    (hm : MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hkey : Decl.KeyFree (keyOf t (memberAddr B k (.defn d)))) (hX : KeepsValuesJ X)
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
  have hskip : ∀ cv, LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀
      (.regular 0) = .axiomDecl cv →
      cv.name = Ix.Kernel.quotSoundName ∨ IxVM.Consistency.inertKey cv.name = true :=
    fun cv h => absurd h (LoadedReads.defnDecl_ne_axiomDecl _ _ _ _ cv)
  obtain ⟨-, htrans⟩ := Decl.walkedConst_step hinv hev (hst.good env none) hfreshD hkeyD hskip
  have hrun := Decl.walkedConst_declRunJ hinv hev (hst.good env none) hfreshD hkeyD hskip
  have hprojE : recordOf E (memberAddr B k (.defn d)) =
      some (memberProjection B k (.defn d)) :=
    hst.held (hS.recordOf_of_recordAt hrecM)
  have hblockE : recordOf E B = some cb := hst.held (hS.recordOf_of_recordAt hrecB)
  have hinv' := htrans E (some n) (hreload E hprojE hblockE hst.runBlob) hinv
  rw [LoadedReads.installs_defnDecl] at hinv'
  rw [LoadedReads.installs_defnDecl] at hrun
  have hname : (LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)).name = keyOf t (memberAddr B k (.defn d)) :=
    LoadedReads.defnConst_name _ _ _ _
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : Ix.Kernel.Declaration .anon,
      DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d₀
        ⟨LoadedReads.defnConst d.kind
          ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val'
          (.regular 0) :: env.consts⟩ := by
    rcases hrun with h0 | ⟨d₀, hd₀⟩
    · cases h0
    · exact ⟨d₀, hd₀⟩
  refine ⟨LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' (.regular 0),
    LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0),
    hname, hreads, storedAs_defnConst _ _ _ _ hannT hannV, hinv', ?_⟩
  refine hX env (LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' (.regular 0)) d₀
    hXe (by rw [hname]; exact hfresh) (isValueConst_defnConst _ _ _ _) (fun T => ?_) hd₀
  rw [hname]
  exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t (memberAddr B k (.defn d)))

/-- **`UnitStep` for a block of definitions, for a clause kept along the declaration step**:
`unitStep_defnBlock` with `KeepsValuesJ X` (the members installed by `memberStepJ`). -/
theorem unitStep_defnBlockJ {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ B = some cb) (hmuts : cb.info = .muts ms) (hlogic : InLogic cb)
    (hdefs : DefnBlock ms)
    (hchk : ∀ k, k < ms.size → MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hlim : lim = some n)
    (hkey : ∀ i m, ms[i]? = some m → Decl.KeyFree (keyOf t (memberAddr B i m)))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hX : KeepsValuesJ X) :
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
        memberStepJ ht hS hcov hst hrecB hmuts hlogic hmi (hchk m hlt) (hkey m _ hmi) hX
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

/-- **`UnitStep` for a block of definitions, keeping the registry of native families**
together with a clause `Y` kept by storing a value constant. -/
theorem unitStep_defnBlock_late {Y : Ix.Kernel.Env .anon → Prop} {envT : Ix.Kernel.Env .anon}
    {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ B = some cb) (hmuts : cb.info = .muts ms) (hlogic : InLogic cb)
    (hdefs : DefnBlock ms)
    (hchk : ∀ k, k < ms.size → MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hlim : lim = some n)
    (hkey : ∀ i m, ms[i]? = some m → Decl.KeyFree (keyOf t (memberAddr B i m)))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hY : KeepsValues Y) :
    UnitStep.{u} (fun env => LateRegistry.{u} t E env ∧ Y env) t envT E₀ E lim B cb :=
  unitStep_defnBlockJ ht hS hcov hst hc hmuts hlogic hdefs hchk hlim hkey hinert hcover
    ((keepsValuesJ_lateRegistry t E).and hY.toJ)

end Block

end IxVM.Refinement.Typing
