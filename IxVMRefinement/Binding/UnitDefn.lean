import IxVMRefinement.Binding.Steps
import IxVMRefinement.Assembly.TypingDefnStep

/-! # The step of a definition, theorem or opaque record, in the binding fold

`bUnitStep_defn` proves `BUnitStep` for a standalone definition, theorem or opaque record, from
the same inputs as the typing skeleton's `unitStep_defn`. The difference is the store: the
check evidence is read at one store `Ec` for `R` that the run's calls are good for
(`StepStore`), and the walked-constant step (`Decl.walkedConst_step`) run there gives a
transport of the prefix invariant to every store and every limit at which the new record
reloads. At a store `E` for `R` it reloads: `E` decodes its records, holds the record of `R` at
`A`, and holds every blob of the run's store when `R` does.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-! ## Reading the records of a store for `R` -/

/-- A record of a store that holds only what the run loaded is a record of the run's store. -/
theorem recordOf_of_loaded {R E₀ : Ixon.Env}
    (hloaded : ∀ a lc, R.consts.get? a = some lc → E₀.consts.get? a = some lc)
    {a : _root_.Address} {c : Ixon.Constant} (h : recordOf R a = some c) :
    recordOf E₀ a = some c := by
  obtain ⟨lc, hl, hd⟩ := recordOf_some h
  exact recordOf_of_get (hloaded a lc hl) hd

/-- A record of `R` is a record of every store for `R`. -/
theorem recordOf_of_recordsFor {R E : Ixon.Env} (hE : RecordsFor R E) {a : _root_.Address}
    {c : Ixon.Constant} (h : recordOf R a = some c) : recordOf E a = some c :=
  (recordOf_eq_recordAt_of_decoded hE.1 a).trans (hE.2.1 a c h)

/-- A store for `R` holds every blob of the run's store when `R` does. -/
theorem blob_of_recordsFor {R E E₀ : Ixon.Env} (hE : RecordsFor R E)
    (hb : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b) :
    ∀ x b, E₀.blobs.get? x = some b → E.blobs.get? x = some b :=
  fun x b h => hE.2.2.1 x b (hb x b h)

/-! ## The constants a step stores -/

/-- What `new ++ env` stores is a constant of `new` or what `env` stores. -/
theorem find_append_cases {env : Ix.Kernel.Env .anon} {k : Ix.Kernel.Key .anon}
    {ci : Ix.Kernel.ConstantInfo .anon} (new : List (Ix.Kernel.ConstantInfo .anon)) :
    (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some ci →
      ci ∈ new ∨ env.find? k = some ci := by
  induction new with
  | nil => exact fun h => Or.inr h
  | cons c new ih =>
    intro h
    have h' : Ix.Kernel.Env.find? ⟨c :: (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).consts⟩ k =
        some ci := h
    rw [Ix.Kernel.Env.find?_cons] at h'
    split at h'
    · have e : c = ci := Option.some.inj h'
      subst e
      exact Or.inl List.mem_cons_self
    · rcases ih h' with hm | he
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · exact Or.inr he

/-- What `env` stores, `new ++ env` stores, when every constant of `new` is fresh. -/
theorem find_append_of_find {env : Ix.Kernel.Env .anon} {new : List (Ix.Kernel.ConstantInfo .anon)}
    (hfresh : ∀ ci ∈ new, env.find? ci.name = none) {k : Ix.Kernel.Key .anon}
    {ci : Ix.Kernel.ConstantInfo .anon} (h : env.find? k = some ci) :
    (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some ci := by
  have hne : ∀ c ∈ new, c.name ≠ k := by
    intro c hc e
    have h' := hfresh c hc
    rw [e, h] at h'
    cases h'
  rw [Ix.Kernel.EnvExt.find?_append_of_fresh hne]
  exact h

/-- **No constructor and no projection table.** -/
def NoCtorProj (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  (∀ cv nP nF, ci ≠ .ctorInfo cv nP nF) ∧ ∀ tbl, ci ≠ .projInfo tbl

theorem noCtorProj_of_isValueConst {ci : Ix.Kernel.ConstantInfo .anon} (h : IsValueConst ci) :
    NoCtorProj ci := by
  rcases h with ⟨cv, v, hh, rfl⟩ | ⟨cv, v, rfl⟩ | ⟨cv, rfl⟩
  · exact ⟨(fun _ _ _ e => nomatch e), (fun _ e => nomatch e)⟩
  · exact ⟨(fun _ _ _ e => nomatch e), (fun _ e => nomatch e)⟩
  · exact ⟨(fun _ _ _ e => nomatch e), (fun _ e => nomatch e)⟩

/-- A free key is no operation's key. -/
theorem not_mem_opNames_of_keyFree {k : Ix.Kernel.Key .anon} (h : Decl.KeyFree k) :
    k ∉ RoleOps.opNames := by
  intro hm
  rcases RoleOps.mem_opNames.mp hm with h1 | h1
  · have h2 : Ix.Kernel.natOpNames.contains k = true := List.contains_iff_mem.mpr h1
    rw [h.2.1] at h2
    cases h2
  · have h2 : Ix.Kernel.natDivModNames.contains k = true := List.contains_iff_mem.mpr h1
    rw [h.2.2] at h2
    cases h2

/-! ## The step of a standalone definition, theorem or opaque record -/

/-- **`BUnitStep` for a standalone definition, theorem or opaque record.** The inputs about the
record and its check are `unitStep_defn`'s. About the stores: `Ec` is a store for `R` the
step's check is read at (`StepStore`); `R` holds the record at `A`, only records the run loaded,
and every blob the run loaded. The unit installs one constant, the declaration of the record's
canonical annotations at the record's key; its prefix invariant at every store for `R` and every
limit is the walked-constant step's transport, and the extra clause at every store is kept by a
value constant. -/
theorem bUnitStep_defn {Y : Ixon.Env → Ix.Kernel.Env .anon → Prop} {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {R E₀ Ec : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {bAddr A : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hRc : RecordsFor R Ec) (hst : StepStore calls t E₀ Ec)
    (hR : recordOf R A = some c)
    (hloaded : ∀ a lc, R.consts.get? a = some lc → E₀.consts.get? a = some lc)
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b)
    (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hchk : CheckedAtFullAt calls bAddr t A n)
    (hkey : Decl.KeyFree (keyOf t A))
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hY : ∀ E, KeepsValues (Y E)) :
    BUnitStep.{u} Y t R envT E₀ n A c := by
  intro env hext hnd hinv hYe href hfresh
  have hc : recordOf E₀ A = some c := recordOf_of_loaded hloaded hR
  have hbound : Bounded calls := (hst.good env none).2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  obtain ⟨ty₀, val₀, ty', val', hannT, hannV, hall⟩ :=
    checkedAtFullAt_defn_step (order_role := []) ht hbound hS hrec₀ hinfo hlogic
      List.not_mem_nil hchk Ec hstored
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
  obtain ⟨-, htrans⟩ := Decl.walkedConst_step (hinv Ec hRc) hev (hst.good env none) hfreshD
    hkeyD (fun cv h => absurd h (LoadedReads.defnDecl_ne_axiomDecl _ _ _ _ cv))
  have hname : (LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)).name = keyOf t A :=
    LoadedReads.defnConst_name _ _ _ _
  have hval : IsValueConst (LoadedReads.defnConst d.kind
      ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val' (.regular 0)) :=
    isValueConst_defnConst _ _ _ _
  have hfreshN : ∀ ci ∈ [LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩
      val' (.regular 0)], env.find? ci.name = none := by
    intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    rw [hname]
    exact hfreshA
  refine ⟨[LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)], List.nodup_singleton _, hfreshN, ?_, ?_, ?_, ?_, ?_⟩
  · intro E hE lim hinvE
    have h := htrans E lim (hreload E (recordOf_of_recordsFor hE hR)
      (blob_of_recordsFor hE hblobs)) hinvE
    rw [LoadedReads.installs_defnDecl] at h
    exact h
  · intro E hE
    exact hY E env _ (hYe E hE) (by rw [hname]; exact hfreshA) hval
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    rw [hname]
    exact not_mem_opNames_of_keyFree hkey
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

end IxVM.Refinement.Binding
