import IxVMRefinement.Assembly.LateRegistry
import IxVMRefinement.Decl.LateWalkedConst

/-! # The step of a definition record, keeping a clause along its declaration step

`unitStep_defn` keeps an extra clause `X` that storing a value constant keeps by itself
(`KeepsValues`). The registry of native families (`LateRegistry`) is not such a clause: it
holds a model of the environment, which the declaration step extends. `unitStep_defnJ` is
`unitStep_defn` for a clause kept along the declaration step (`KeepsValuesJ`); the step is
`Decl.walkedConst_declRunJ` of the same check evidence. `unitStep_defn_late` is it for the
registry together with any clause kept by a value constant alone.
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

end IxVM.Refinement.Typing
