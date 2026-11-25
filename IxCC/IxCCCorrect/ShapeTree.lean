import IxCCCorrect.ShapeHook

/-!
# Results with fields on the reference-counted path (`IxCCCorrect.ShapeTree`)

The reference-counted front's view reads first-order constructor trees
(`Recheck.RcReplay.treeViewOf`), so a root may return a list or a tree.
`rc_sound_of_shape` (`IxCCCorrect.ShapeHook`) left one hypothesis: the view accepts
every value of the root's result shape. This module decides it.

The observation of a constructor value is three functions deep: erasure
(`Lam.Erase.eraseVal`: the constructor's declaration, unboxing of its inductive at the
profile of the levels the value carries, the fields kept at that profile), the
observation of the erased value (`obsV`), and the tree view (`treeView`: the
constructor's table tag, the signature's field types at that tag). The decision reads
each of them **at a data entry**, once per constructor, on the same inputs:

* `readsOk m σ ty`: `nat` at `.nat`; a data entry at an inductive of the signature it is
  paired with in `m` (a finite map, part of the certificate, untrusted).
* `ctorReads`: for one constructor of an entry paired with inductive `i`: it is a
  constructor declaration whose inductive is not unboxed at the entry's levels, its
  alias has a table tag, the signature lists field types at that tag, and the kept
  fields' shapes are read at them one by one (`fieldsRead`). Fields not kept are not
  looked at.
* `mapReads`: every pair of `m` passes at every constructor of its entry.

`reads_val` (by induction on a bound on the value's size, `reads_lt`, with
`reads_fields` for a constructor's fields): a value of a shape read at
`ty` erases, has an observation, and the tree view accepts it. `rc_view_tree_ok` is the
view's statement; `treeRootOk` the Boolean for a root. `rcEnumRootOk` is the
enumeration root of the immortal path restated for the tree view (`view_enum_ok_any`).
`rcCheckShaped` and `rcCheckShaped_sound` are the check on an artifact the replay made
(what `compile` calls, having run the replay); `rcRunShaped` and `rcRunShaped_sound` the
reference-counted hook, for `Nat`, enumeration and tree results. A root's readback
signature is its own (`Front.tys r`), so the entry maps are per root (`ms[r]`).

The entry's levels matter: erasure reads the profile of the levels a constructor value
carries, so a data entry states them (`DataDecl.ls`) and the value judgment fixes them
(`ValOk.data`).
-/

set_option autoImplicit false

namespace IxCC.Correct.Shape2

open IxCC.Src
open IxCC.Sem (Lang Obs Result)
open IxCC.Lam.Erase (eraseVal eraseKept)
open IxCC.Lam.Erase.Proof (CheckedProgram obsV obsList)
open IxCC.Rt.Rc.Procs.Readback (treeView fieldsView)

/-! ## The decision -/

/-- A shape read at a readback type, under a map from data entries to the signature's
inductives. -/
def readsOk (m : List (Nat × Nat)) : Shape → Rt.FoTy → Bool
  | .nat, .nat => true
  | .data d, .ind i => decide ((d, i) ∈ m)
  | _, _ => false

/-- The kept fields' shapes, from field `i` on, are read at the field types in order. -/
def fieldsRead (kept : Nat → Bool) (m : List (Nat × Nat)) :
    Nat → List Shape → List Rt.FoTy → Bool
  | _, [], tys => tys.isEmpty
  | i, σ :: fl, tys =>
    if kept i then
      match tys with
      | ty :: tys' => readsOk m σ ty && fieldsRead kept m (i + 1) fl tys'
      | [] => false
    else fieldsRead kept m (i + 1) fl tys

/-- One constructor `c` (field shapes `fl`) of an entry at levels `ls`, read at
inductive `i` of the signature `G`. -/
def ctorReads (I : IxCC.Lam.Erase.Input) (T : List Lam.CtorInfo) (G : Rt.Sig)
    (m : List (Nat × Nat)) (ls : Levels) (i : Nat) (c : CId) (fl : List Shape) : Bool :=
  match I.decl? c with
  | some (.ctor _ _ ind _ _ _ _) =>
    (I.unbox? ind (Profile.normalize (profileOf ls) (I.lvls c))).isNone &&
      match Fir.CtorInfo.ofKey T (.src (I.alias c)) with
      | some info =>
        match G.ctor? i info.tag with
        | some tys =>
          fieldsRead (I.kept c (Profile.normalize (profileOf ls) (I.lvls c))) m 0 fl tys
        | none => false
      | none => false
  | _ => false

/-- Every pair of the map passes at every constructor of its entry. -/
def mapReads (I : IxCC.Lam.Erase.Input) (T : List Lam.CtorInfo) (G : Rt.Sig)
    (datas : List DataDecl) (m : List (Nat × Nat)) : Bool :=
  m.all fun e =>
    match datas[e.1]? with
    | some D => D.ctors.all fun k => ctorReads I T G m D.ls e.2 k.1 k.2
    | none => false

/-! ## What "read" means -/

/-- A value is read at `ty`: it erases, the erased value has an observation, and the
tree view accepts the observation. -/
def Reads (I : IxCC.Lam.Erase.Input) (T : List Lam.CtorInfo) (G : Rt.Sig) (v : Value)
    (ty : Rt.FoTy) : Prop :=
  ∃ w o, eraseVal I v = some w ∧ obsV w = some o ∧ (treeView T G ty o).isSome = true

/-- The fields of a constructor are read at `tys`: the kept ones erase, have
observations, and the field view accepts them. -/
def ReadsAll (I : IxCC.Lam.Erase.Input) (T : List Lam.CtorInfo) (G : Rt.Sig) (c : CId)
    (q : Profile) (i : Nat) (fs : List Value) (tys : List Rt.FoTy) : Prop :=
  ∃ ws os, eraseKept I c q i fs = some ws ∧ obsList ws = some os ∧
    (fieldsView T G tys os).isSome = true

/-! ## One step of each function -/

theorem treeView_ctor {T : List Lam.CtorInfo} {G : Rt.Sig} {i cid : Nat} {os : List Obs}
    {info : Fir.CtorInfo} {tys : List Rt.FoTy}
    (hi : Fir.CtorInfo.ofKey T (.src cid) = some info) (ht : G.ctor? i info.tag = some tys)
    (hf : (fieldsView T G tys os).isSome = true) :
    (treeView T G (.ind i) (.ctor cid os)).isSome = true := by
  obtain ⟨vals, hv⟩ := Option.isSome_iff_exists.1 hf
  simp [treeView, hi, ht, hv]

theorem fieldsView_cons {T : List Lam.CtorInfo} {G : Rt.Sig} {ty : Rt.FoTy}
    {tys : List Rt.FoTy} {o : Obs} {os : List Obs} (h1 : (treeView T G ty o).isSome = true)
    (h2 : (fieldsView T G tys os).isSome = true) :
    (fieldsView T G (ty :: tys) (o :: os)).isSome = true := by
  obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨os', hos'⟩ := Option.isSome_iff_exists.1 h2
  simp [fieldsView, ho', hos']

theorem eraseVal_con {I : IxCC.Lam.Erase.Input} {c : CId} {ls : Levels} {ps : List Src.Slot}
    {fs : List Value} {s : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Term}
    (hd : I.decl? c = some (.ctor s lv ind cidx np nf ty))
    (hu : I.unbox? ind (Profile.normalize (profileOf ls) (I.lvls c)) = none) :
    eraseVal I (.con c ls ps fs) =
      (eraseKept I c (Profile.normalize (profileOf ls) (I.lvls c)) 0 fs).map
        (.con (I.ctorKey c)) := by
  simp only [eraseVal, hd, hu]

/-! ## The lemma

By induction on a bound on the value's size: a constructor's fields are smaller than
the constructor, and `reads_fields` takes the bound's induction hypothesis, so there is
no well-founded recursion through `cases`. -/

/-- The fields of a constructor value, from field `i` on, are read at the field types
their kept shapes are read at, given that every value below the bound is read. -/
theorem reads_fields {p : Src.Program} {cert : Cert} {I : IxCC.Lam.Erase.Input}
    {T : List Lam.CtorInfo} {G : Rt.Sig} {m : List (Nat × Nat)} (n : Nat)
    (ih : ∀ (v : Value) (σ : Shape) (ty : Rt.FoTy), sizeOf v < n →
      ValOk p cert.sig v σ → readsOk m σ ty = true → Reads I T G v ty)
    (c : CId) (q : Profile) :
    ∀ (fs : List Value) (fl : List Shape) (i : Nat) (tys : List Rt.FoTy), sizeOf fs < n →
      ValsOk p cert.sig fs fl → fieldsRead (I.kept c q) m i fl tys = true →
      ReadsAll I T G c q i fs tys
  | [], fl, i, tys, _, hfs, hr => by
    cases hfs
    simp only [fieldsRead, List.isEmpty_iff] at hr
    subst hr
    exact ⟨[], [], by simp [eraseKept], by simp [obsList], by simp [fieldsView]⟩
  | v :: vs, fl, i, tys, hn, hfs, hr => by
    cases hfs with
    | cons hv hvs =>
      have hn' : sizeOf v < n ∧ sizeOf vs < n := by
        simp only [List.cons.sizeOf_spec] at hn
        omega
      simp only [fieldsRead] at hr
      by_cases hk : I.kept c q i = true
      · simp only [hk, ↓reduceIte] at hr
        cases tys with
        | nil => simp at hr
        | cons ty tys' =>
          simp only [Bool.and_eq_true] at hr
          obtain ⟨w, o, hw, ho, ht⟩ := ih v _ ty hn'.1 hv hr.1
          obtain ⟨ws, os, hks, hos, hfv⟩ :=
            reads_fields n ih c q vs _ (i + 1) tys' hn'.2 hvs hr.2
          exact ⟨w :: ws, o :: os, by simp [eraseKept, hks, hk, hw],
            by simp [obsList, ho, hos], fieldsView_cons ht hfv⟩
      · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hr
        obtain ⟨ws, os, hks, hos, hfv⟩ := reads_fields n ih c q vs _ (i + 1) tys hn'.2 hvs hr
        exact ⟨ws, os, by simp [eraseKept, hks, hk], hos, hfv⟩

/-- `reads_val` below a size bound. -/
theorem reads_lt {p : Src.Program} {cert : Cert} {I : IxCC.Lam.Erase.Input}
    {T : List Lam.CtorInfo} {G : Rt.Sig} {m : List (Nat × Nat)}
    (hm : mapReads I T G cert.datas m = true) :
    ∀ (n : Nat) (v : Value) (σ : Shape) (ty : Rt.FoTy), sizeOf v < n →
      ValOk p cert.sig v σ → readsOk m σ ty = true → Reads I T G v ty
  | 0, _, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, v, σ, ty, hn, hv, hr => by
    cases σ with
    | nat =>
      cases ty with
      | nat =>
        obtain ⟨k, rfl⟩ := hv.nat_inv
        exact ⟨.lit (.nat k), .nat k, by simp [eraseVal], by simp [obsV], by simp [treeView]⟩
      | ind i => simp [readsOk] at hr
    | data d =>
      cases ty with
      | nat => simp [readsOk] at hr
      | ind i =>
        simp only [readsOk, decide_eq_true_eq] at hr
        obtain ⟨c, ls, ps, fs, D, j, fl, rfl, hD, hc, hls, hfs⟩ := hv.data_inv_ls
        have hfn : sizeOf fs < n := by
          simp only [Value.con.sizeOf_spec] at hn
          omega
        have he := List.all_eq_true.1 hm (d, i) hr
        have hD' : cert.datas[d]? = some D := hD
        simp only [hD'] at he
        have hcr := List.all_eq_true.1 he (c, fl) (List.mem_of_getElem? hc)
        have hcr' : ctorReads I T G m D.ls i c fl = true := hcr
        unfold ctorReads at hcr'
        cases hd : I.decl? c with
        | none => simp [hd] at hcr'
        | some decl =>
          cases decl with
          | ctor s lv ind cidx np nf ty' =>
            simp only [hd, Bool.and_eq_true] at hcr'
            obtain ⟨hu, hrest⟩ := hcr'
            cases hinfo : Fir.CtorInfo.ofKey T (.src (I.alias c)) with
            | none => simp [hinfo] at hrest
            | some info =>
              cases htys : G.ctor? i info.tag with
              | none => simp [hinfo, htys] at hrest
              | some tys =>
                simp only [hinfo, htys] at hrest
                subst hls
                obtain ⟨ws, os, hk, ho, hfv⟩ :=
                  reads_fields n (fun v σ ty h hv hr => reads_lt hm n v σ ty h hv hr) c _ fs fl 0
                    tys hfn hfs hrest
                refine ⟨.con (I.ctorKey c) ws, .ctor (I.alias c) os, ?_, ?_,
                  treeView_ctor hinfo htys hfv⟩
                · rw [eraseVal_con hd (Option.isNone_iff_eq_none.1 hu), hk]
                  rfl
                · simp [obsV, IxCC.Lam.Erase.Input.ctorKey, ho]
          | _ => simp [hd] at hcr'
    | enum _ => cases ty <;> simp [readsOk] at hr
    | irr => cases ty <;> simp [readsOk] at hr
    | fn _ _ => cases ty <;> simp [readsOk] at hr
    | inter _ _ => cases ty <;> simp [readsOk] at hr
    | any => cases ty <;> simp [readsOk] at hr

/-- **A value of a shape read at `ty` is read at `ty`.** -/
theorem reads_val {p : Src.Program} {cert : Cert} {I : IxCC.Lam.Erase.Input}
    {T : List Lam.CtorInfo} {G : Rt.Sig} {m : List (Nat × Nat)}
    (hm : mapReads I T G cert.datas m = true) (v : Value) (σ : Shape) (ty : Rt.FoTy)
    (hv : ValOk p cert.sig v σ) (hr : readsOk m σ ty = true) : Reads I T G v ty :=
  reads_lt hm (sizeOf v + 1) v σ ty (Nat.lt_succ_self _) hv hr

/-! ## The view, a root, and the hook -/

/-- **The tree view accepts every value of a shape read at the root's readback type.**
This is the hypothesis `hview` of `rc_sound_of_shape`. -/
theorem rc_view_tree_ok {f : Recheck.RcReplay.Front} {cert : Cert} {r : Nat} {G : Rt.Sig}
    {ty : Rt.FoTy} {m : List (Nat × Nat)} {ρ : Shape} (hty : f.tys r = some (G, ty))
    (hm : mapReads (IxCC.Lam.Erase.Input.ofProgram f.src f.checked) f.anf.ctors G cert.datas m =
      true)
    (hρ : readsOk m ρ ty = true) (v : Value) (hv : ValOk f.src cert.sig v ρ) :
    f.view r (Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, v) : Lang.Val CheckedProgram)) ≠ none := by
  obtain ⟨w, o, hw, ho, ht⟩ := reads_val hm v ρ ty hv hρ
  have hobs : Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, v) : Lang.Val CheckedProgram) = some o := by
    show (eraseVal _ v).bind obsV = some o
    rw [hw]
    exact ho
  rw [hobs]
  obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 ht
  simp [Recheck.RcReplay.Front.view, Recheck.RcReplay.treeViewOf, hty, ho']

/-- **A tree root of the certificate, on the reference-counted front**: root `r` has an
instance of `n` `Nat` parameters whose result shape is read at the root's readback
type, under an entry map `m` that passes. -/
def treeRootOk (f : Recheck.RcReplay.Front) (sc : Cert) (m : List (Nat × Nat)) (r n : Nat) :
    Bool :=
  match f.src.roots[r]?, f.tys r with
  | some (_, c), some (G, ty) =>
    sc.insts.any fun e =>
      decide (e.1 = c) && decide (e.2.1 = ([] : Levels)) &&
      decide (e.2.2 = arrows (List.replicate n .nat) (resAfter n e.2.2)) &&
      readsOk m (resAfter n e.2.2) ty &&
      mapReads (IxCC.Lam.Erase.Input.ofProgram f.src f.checked) f.anf.ctors G sc.datas m
  | _, _ => false

/-- **Functional progress at a tree root, from the checks.** -/
theorem rc_neverWrong_of_treeRoot {f : Recheck.RcReplay.Front} {sc : Cert}
    {m : List (Nat × Nat)} (h : certOk f.src sc = true) {r : Nat} (ns : List Nat)
    (hn : treeRootOk f sc m r ns.length = true) : NeverWrong f.source (r, ns) := by
  unfold treeRootOk at hn
  cases hroot : f.src.roots[r]? with
  | none => simp [hroot] at hn
  | some e =>
    obtain ⟨addr, c⟩ := e
    cases hty : f.tys r with
    | none => simp [hroot, hty] at hn
    | some gt =>
      obtain ⟨G, ty⟩ := gt
      simp only [hroot, hty] at hn
      obtain ⟨⟨c', ls', σ⟩, hmem, he⟩ := List.any_eq_true.1 hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he
      obtain ⟨⟨⟨⟨hc, hls⟩, hσ⟩, hread⟩, hmap⟩ := he
      subst hc
      subst hls
      have hc' : (c', ([] : Levels),
          arrows (List.replicate ns.length .nat) (resAfter ns.length σ)) ∈ sc.insts := by
        rw [← hσ]
        exact hmem
      exact neverWrong_of_shape_view (sig := sc.sig) (view := f.view) (sigOk_of_cert h) hroot ns
        hc' (rc_view_tree_ok hty hmap hread)

/-- **Any view accepts every value of an enumeration's shape** if it accepts each listed
constructor, none of which has a universe parameter (`view_enum_ok` for any view). -/
theorem view_enum_ok_any {src : Src.Program} {ch : Src.Relevance.Checked} {sig : Sig}
    {view : Nat → Option Obs → Option (Option Obs)} {r : Nat} {B : CId} {cs : List CId}
    (hB : sig.enums B = some cs)
    (hcs : ∀ c, c ∈ cs → (IxCC.Lam.Erase.Input.ofProgram src ch).lvls c = 0 ∧
      view r (Lang.obs (S := CheckedProgram)
        ((IxCC.Lam.Erase.Input.ofProgram src ch, Value.con c [] [] []) :
          Lang.Val CheckedProgram)) ≠ none)
    (v : Value) (hv : ValOk src sig v (.enum B)) :
    view r (Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram src ch, v) : Lang.Val CheckedProgram)) ≠ none := by
  obtain ⟨c, ls, cs', rfl, hB', hc⟩ := hv.enum_inv
  rw [hB] at hB'
  cases hB'
  obtain ⟨hl, hne⟩ := hcs c hc
  have e : Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram src ch, Value.con c ls [] []) :
        Lang.Val CheckedProgram) =
      Lang.obs (S := CheckedProgram)
        ((IxCC.Lam.Erase.Input.ofProgram src ch, Value.con c [] [] []) :
          Lang.Val CheckedProgram) := by
    show (eraseVal _ (Value.con c ls [] [])).bind obsV =
      (eraseVal _ (Value.con c [] [] [])).bind obsV
    rw [eraseVal_enum_levels _ hl]
  rw [e]
  exact hne

/-- **An enumeration root on the reference-counted front** (`enumRootOk` there): the
instance of `n` `Nat` parameters and an enumeration result, none of whose constructors
has a universe parameter and each of which the tree view reads back. -/
def rcEnumRootOk (f : Recheck.RcReplay.Front) (sc : Cert) (r n : Nat) : Bool :=
  match f.src.roots[r]? with
  | some (_, c) =>
    sc.enums.any fun e =>
      decide (lookupEnum sc.enums e.1 = some e.2) &&
      decide ((c, ([] : Levels), arrows (List.replicate n .nat) (.enum e.1)) ∈ sc.insts) &&
      e.2.all fun c' =>
        decide ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked).lvls c' = 0) &&
        (f.view r (Lang.obs (S := CheckedProgram)
          ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, Value.con c' [] [] []) :
            Lang.Val CheckedProgram))).isSome
  | none => false

/-- **Functional progress at an enumeration root of the reference-counted front.** -/
theorem rc_neverWrong_of_enumRoot {f : Recheck.RcReplay.Front} {sc : Cert}
    (h : certOk f.src sc = true) {r : Nat} (ns : List Nat)
    (hn : rcEnumRootOk f sc r ns.length = true) : NeverWrong f.source (r, ns) := by
  unfold rcEnumRootOk at hn
  cases hroot : f.src.roots[r]? with
  | none => simp [hroot] at hn
  | some e =>
    obtain ⟨addr, c⟩ := e
    simp only [hroot] at hn
    obtain ⟨⟨B, cs⟩, -, he⟩ := List.any_eq_true.1 hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨hB, hc⟩, hall⟩ := he
    refine neverWrong_of_shape_view (sig := sc.sig) (view := f.view) (sigOk_of_cert h) hroot ns
      hc (view_enum_ok_any (sig := sc.sig) hB ?_)
    intro c' hc'
    have hc2 := List.all_eq_true.1 hall c' hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2
    refine ⟨hc2.1, ?_⟩
    intro hnone
    have h2 := hc2.2
    rw [hnone] at h2
    exact Bool.noConfusion h2

/-- A root the reference-counted corollaries read: a `Nat` root, an enumeration root, or
a tree root under the entry map `m`. -/
def rcRootOk (f : Recheck.RcReplay.Front) (sc : Cert) (m : List (Nat × Nat)) (r n : Nat) :
    Bool :=
  natRootOk f.src sc r n || rcEnumRootOk f sc r n || treeRootOk f sc m r n

/-- Each root from `r` on is read at its stated parameter count, root `r` under the entry
map `ms[r]` (a root's readback signature is its own, so each root has its own map). -/
def rcRootsOk (f : Recheck.RcReplay.Front) (sc : Cert) (ms : List (List (Nat × Nat))) :
    Nat → List Nat → Bool
  | _, [] => true
  | r, n :: rest => rcRootOk f sc (ms.getD r []) r n && rcRootsOk f sc ms (r + 1) rest

theorem rcRootsOk_get {f : Recheck.RcReplay.Front} {sc : Cert} {ms : List (List (Nat × Nat))} :
    ∀ (arities : List Nat) (r0 : Nat), rcRootsOk f sc ms r0 arities = true →
    ∀ (i n : Nat), arities[i]? = some n → rcRootOk f sc (ms.getD (r0 + i) []) (r0 + i) n = true
  | [], _, _, i, n, hi => by simp at hi
  | k :: rest, r0, h, i, n, hi => by
    simp only [rcRootsOk, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact h.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := rcRootsOk_get rest (r0 + 1) h.2 i n hi
      have e : r0 + (i + 1) = r0 + 1 + i := by omega
      rw [e]
      exact this

/-- **The shape check on a reference-counted artifact**: the certificate checks on the
checked source the replay made, and each root is read at its stated parameter count. -/
def rcCheckShaped (a : Recheck.RcReplay.Artifact) (sc : Cert) (ms : List (List (Nat × Nat)))
    (arities : List Nat) : Bool :=
  certOk a.front.src sc && rcRootsOk a.front sc ms 0 arities

/-- **`RcReplay.sound` with no escape, from the replay and the shape check.** For a
caller that has run the replay already (`compile`'s plain-RC checker). -/
theorem rcCheckShaped_sound {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact} (hrun : Recheck.RcReplay.run cfg P c = .ok a)
    {sc : Cert} {ms : List (List (Nat × Nat))} {arities : List Nat}
    (h : rcCheckShaped a sc ms arities = true) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (r : Nat) (ns : List Nat)
    (hr : arities[r]? = some ns.length) (hi : a.front.Covered c (r, ns)) :
    (∀ k w, Lang.run (a.linked D) (r, ns) k = .ok w →
      ∃ k' v, Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram) (r, ns) k' = .ok v ∧
        a.front.view r (Lang.obs v) = some w) ∧
    (∀ k, ¬ (Lang.run (a.linked D) (r, ns) k).GoesWrong) := by
  simp only [rcCheckShaped, Bool.and_eq_true] at h
  have hn := rcRootsOk_get arities 0 h.2 r ns.length hr
  rw [Nat.zero_add] at hn
  refine rc_sound_of_neverWrong hrun D hD (r, ns) hi ?_
  unfold rcRootOk at hn
  simp only [Bool.or_eq_true] at hn
  rcases hn with (hn | hn) | hn
  · exact rc_neverWrong_of_check h.1 ns hn
  · exact rc_neverWrong_of_enumRoot h.1 ns hn
  · exact rc_neverWrong_of_treeRoot h.1 ns hn

/-- **The reference-counted recheck path with the shape check.** `arities` states, root
by root from root 0, how many `Nat` parameters the root takes; each must be a `Nat`, an
enumeration or a tree root (`rcRootOk`), root `r` under the entry map `ms[r]`. The shape
certificate `sc` and the maps are only checked. -/
def rcRunShaped (cfg : Recheck.Config) (P : Src.Program) (c : Recheck.RcReplay.Cert) (sc : Cert)
    (ms : List (List (Nat × Nat))) (arities : List Nat) :
    Except Refusal Recheck.RcReplay.Artifact :=
  match Recheck.RcReplay.run cfg P c with
  | .error e => .error (.recheck e)
  | .ok a => if rcCheckShaped a sc ms arities then .ok a else .error .shape

/-- **`RcReplay.sound` with no escape, from the checker's acceptance alone**, for roots
with a `Nat` or enumeration result and for roots whose result is a first-order
constructor tree (a list, a pair, a tree of them). -/
theorem rcRunShaped_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.RcReplay.Cert}
    {sc : Cert} {ms : List (List (Nat × Nat))} {arities : List Nat}
    {a : Recheck.RcReplay.Artifact}
    (h : rcRunShaped cfg P c sc ms arities = .ok a) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (r : Nat) (ns : List Nat)
    (hr : arities[r]? = some ns.length) (hi : a.front.Covered c (r, ns)) :
    (∀ k w, Lang.run (a.linked D) (r, ns) k = .ok w →
      ∃ k' v, Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram) (r, ns) k' = .ok v ∧
        a.front.view r (Lang.obs v) = some w) ∧
    (∀ k, ¬ (Lang.run (a.linked D) (r, ns) k).GoesWrong) := by
  unfold rcRunShaped at h
  cases hrun : Recheck.RcReplay.run cfg P c with
  | error e => simp [hrun] at h
  | ok a' =>
    simp only [hrun] at h
    split at h
    · rename_i hc
      cases h
      exact rcCheckShaped_sound hrun hc D hD r ns hr hi
    · cases h

/-! ## The entry map, proposed (untrusted) -/

/-- The pairs the kept fields of a constructor need. -/
def pairsOf (kept : Nat → Bool) : Nat → List Shape → List Rt.FoTy → List (Nat × Nat)
  | _, [], _ => []
  | i, σ :: fl, tys =>
    if kept i then
      match tys with
      | ty :: tys' =>
        (match σ, ty with
          | .data d, .ind j => [(d, j)]
          | _, _ => []) ++ pairsOf kept (i + 1) fl tys'
      | [] => []
    else pairsOf kept (i + 1) fl tys

/-- **A proposed entry map** from the pairs in `todo`: each pair's constructors add the
pairs their kept fields need. Nothing is proved about it; `mapReads` decides. -/
def treeMap (I : IxCC.Lam.Erase.Input) (T : List Lam.CtorInfo) (G : Rt.Sig)
    (datas : List DataDecl) : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, acc => acc
  | _, [], acc => acc
  | fuel + 1, e :: todo, acc =>
    if acc.contains e then treeMap I T G datas fuel todo acc
    else
      let new := match datas[e.1]? with
        | some D => D.ctors.flatMap fun k =>
            match Fir.CtorInfo.ofKey T (.src (I.alias k.1)) with
            | some info =>
              match G.ctor? e.2 info.tag with
              | some tys =>
                pairsOf (I.kept k.1 (Profile.normalize (profileOf D.ls) (I.lvls k.1))) 0 k.2 tys
              | none => []
            | none => []
        | none => []
      treeMap I T G datas fuel (todo ++ new) (acc ++ [e])

end IxCC.Correct.Shape2
