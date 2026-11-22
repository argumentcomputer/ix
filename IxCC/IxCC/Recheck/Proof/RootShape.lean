import IxCC.CompileClaim
import IxCC.Recheck.Proof.Sound
import IxCC.Recheck.Linked
import IxCC.Anf.Proof.Spec.Run
import IxCC.Lam.Erase.Proof.RegBody

/-! # The results an immortal root's declared type describes

A compile claim on the immortal path is accepted only if `checkImmortalRoot`
holds: the root's parameters are `Nat` and its readback type `(sig, ty)` is
`Nat` or an enumeration whose signature row lists only field-less
constructors (`isImmortalViewType`). The top-level theorems let the source go
wrong by returning a value its root's view rejects (the last case of
`Front.GoesWrong`). This module says which results the root's declared type
describes, without reference to the view or the readback, and proves that the
view rejects no such result.

* `ResultShape p c o`: an observation of the kind the declared result type of
  root `c` describes. A `Nat` for a root returning the pinned `Nat`; one of
  the pinned `Bool` constructors, with no fields, for a root returning the
  pinned `Bool`; for a root returning another safe inductive `I` with no
  indices, one of `I`'s constructors with no fields. Decided by
  `resultShape?` (`resultShape?_iff`).
* `ViewShape sig ty o`: the observations `Rt.readback` gives at `ty`
  (`readback_iff_viewShape`): a `Nat`, or a field-less constructor whose tag
  the signature lists without fields.
* **Totality** (`tagify_resultShape`, `Front.view_resultShape`): at a root
  whose readback type passes `isImmortalViewType`, `Rt.tagify` maps every
  observation of a result shape to a `ViewShape` observation, which reads back
  from its word. On the pinned-`Bool` route this needs both pinned `Bool`
  constructors to have a row in the program's constructor table (`BoolRows`),
  which erasure registers for every root returning the pinned `Bool`
  (`erase_boolRow`) and the middle and back ends keep (`pipeline_ctors`):
  `Front.boolRows`.
* **The view's rejections** (`Front.goesWrong_resultShape`,
  `Artifact.goesWrong_immortalRoot`): for a root that `checkImmortalRoot`
  accepts, the case of `Front.GoesWrong` where the view rejects the result
  happens only when the result is not of the root's result shape. On the
  `Nat` route the view rejects exactly the results that are not of the shape
  (`Front.view_none_iff_nat`). On the other routes the converse fails: the
  view relabels a field-less constructor by its table tag and does not check
  which inductive it belongs to, so it accepts a constructor of another
  enumeration whose tag the signature lists.
* **The shape view** (`Front.shapeView`, `Front.ShapeGoesWrong`): the view
  restricted to the root's result shape. On every route it rejects exactly
  the results off the shape (`Front.shapeView_none_iff`,
  `Front.shapeGoesWrong_iff`), and the guarantees stated with the view imply
  the same guarantees stated with it (`Front.sound_shape`, `Front.safe_shape`,
  `Artifact.shapeClaim`).

Not proved: that SrcEval on a well-typed root returns a result of its shape.
That is type preservation for SrcEval, which no theorem states. -/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-! ## Result shapes -/

/-- The result type of declaration `c`: its type after the leading Π
telescope. -/
def resultType? (p : Src.Program) (c : Src.CId) : Option Src.Term :=
  (p.decl? c).map fun d => d.type.pis.2

/-- **The results root `c`'s declared type describes**, as observations
(`Lang.obs` of a SrcEval result), read off the source program alone:
* the result type is the pinned `Nat`, and the observation is a natural
  number;
* the result type is the pinned `Bool` (not also the pinned `Nat`), and the
  observation is the pinned `Bool.false` or `Bool.true` with no fields;
* the result type is headed by a safe inductive `I` with no indices, other
  than the pinned `Nat` and `Bool`, and the observation is one of `I`'s
  constructors with no fields. -/
inductive ResultShape (p : Src.Program) (c : Src.CId) : Obs → Prop
  | nat {N : Src.CId} (n : Nat) (hN : p.known.nat = some N)
      (hres : resultType? p c = some (.const N [])) : ResultShape p c (.nat n)
  | bool {B k : Src.CId} (hB : p.known.bool = some B) (hBN : p.known.nat ≠ some B)
      (hres : resultType? p c = some (.const B []))
      (hk : p.known.boolFalse = some k ∨ p.known.boolTrue = some k) : ResultShape p c (.ctor k [])
  | enum {I k : Src.CId} {t : Src.Term} {us : List Ixon.Univ} {nl np : Nat} {tyI : Src.Term}
      {keys : List Src.CId} (hres : resultType? p c = some t) (hhead : t.spine.1 = .const I us)
      (hIN : p.known.nat ≠ some I) (hIB : p.known.bool ≠ some I)
      (hI : p.decl? I = some (.induct true nl np 0 tyI keys)) (hk : k ∈ keys) :
      ResultShape p c (.ctor k [])

/-- An optional observation (a SrcEval result may observe nothing) of the
root's result shape. -/
def ResultShapeOpt (p : Src.Program) (c : Src.CId) (ov : Option Obs) : Prop :=
  ∃ o, ov = some o ∧ ResultShape p c o

/-- Root `c` returns the pinned `Nat`. -/
def NatResult (p : Src.Program) (c : Src.CId) : Prop :=
  ∃ N, p.known.nat = some N ∧ resultType? p c = some (.const N [])

/-- Root `c` returns the pinned `Bool` (and it is not also the pinned `Nat`). -/
def BoolResult (p : Src.Program) (c : Src.CId) : Prop :=
  ∃ B, p.known.bool = some B ∧ p.known.nat ≠ some B ∧ resultType? p c = some (.const B [])

/-- Both pinned `Bool` constructors have a row in the constructor table `C`. -/
def boolRows? (p : Src.Program) (C : Cfg.Program) : Bool :=
  match p.known.boolFalse, p.known.boolTrue with
  | some f, some t =>
    (Fir.CtorInfo.ofKey C.ctors (.src f)).isSome && (Fir.CtorInfo.ofKey C.ctors (.src t)).isSome
  | _, _ => false

/-- `boolRows?` as a proposition. -/
def BoolRows (p : Src.Program) (C : Cfg.Program) : Prop := boolRows? p C = true

instance (p : Src.Program) (C : Cfg.Program) : Decidable (BoolRows p C) :=
  inferInstanceAs (Decidable (_ = true))

/-- The decision procedure for `ResultShape`. -/
def resultShape? (p : Src.Program) (c : Src.CId) : Obs → Bool
  | .nat _ =>
    match p.known.nat, resultType? p c with
    | some N, some (.const N' []) => N == N'
    | _, _ => false
  | .ctor k [] =>
    match resultType? p c with
    | some t =>
      match t.spine.1 with
      | .const I _ =>
        if p.known.nat == some I then false
        else if p.known.bool == some I then
          (match t with
           | .const _ [] => true
           | _ => false) &&
            (p.known.boolFalse == some k || p.known.boolTrue == some k)
        else
          match p.decl? I with
          | some (.induct true _ _ 0 _ keys) => keys.contains k
          | _ => false
      | _ => false
    | none => false
  | _ => false

theorem resultShape?_iff (p : Src.Program) (c : Src.CId) (o : Obs) :
    resultShape? p c o = true ↔ ResultShape p c o := by
  constructor
  · intro h
    match o, h with
    | .nat n, h =>
      simp only [resultShape?] at h
      split at h
      · next N N' hN hres =>
        have hNN : N = N' := by simpa using h
        subst hNN
        exact .nat n hN hres
      · cases h
    | .ctor k [], h =>
      simp only [resultShape?] at h
      split at h
      · next t hres =>
        split at h
        · next I us hhead =>
          by_cases hn : (p.known.nat == some I) = true
          · simp [hn] at h
          · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
            have hIN : p.known.nat ≠ some I := fun e => hn (by simp [e])
            by_cases hb : (p.known.bool == some I) = true
            · simp only [hb, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
              obtain ⟨ht, hk⟩ := h
              have hB : p.known.bool = some I := by simpa using hb
              split at ht
              · next I' =>
                have : I' = I := by
                  simp only [Src.Term.spine, Src.Term.spine.go, Src.Term.const.injEq] at hhead
                  exact hhead.1
                subst this
                exact .bool hB hIN hres hk
              · cases ht
            · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
              have hIB : p.known.bool ≠ some I := fun e => hb (by simp [e])
              split at h
              · next nl np tyI keys hI =>
                exact .enum hres hhead hIN hIB hI (List.contains_iff_mem.1 h)
              · cases h
        · cases h
      · cases h
    | .ctor _ (_ :: _), h => simp [resultShape?] at h
    | .word _, h => simp [resultShape?] at h
    | .bytes _, h => simp [resultShape?] at h
  · intro h
    cases h with
    | nat n hN hres => simp [resultShape?, hN, hres]
    | bool hB hBN hres hk =>
      rename_i B k
      have hsp : (Src.Term.const B []).spine.1 = .const B [] := rfl
      have hn : (p.known.nat == some B) = false := by simpa using hBN
      simp only [resultShape?, hres, hsp, hn, Bool.false_eq_true, ↓reduceIte, hB, BEq.rfl,
        Bool.true_and, Bool.or_eq_true, beq_iff_eq]
      exact hk
    | enum hres hhead hIN hIB hI hk =>
      rename_i I k t us nl np tyI keys
      have hn : (p.known.nat == some I) = false := by simpa using hIN
      have hb : (p.known.bool == some I) = false := by simpa using hIB
      simp only [resultShape?, hres, hhead, hn, hb, Bool.false_eq_true, ↓reduceIte, hI]
      exact List.contains_iff_mem.2 hk

instance (p : Src.Program) (c : Src.CId) (o : Obs) : Decidable (ResultShape p c o) :=
  decidable_of_iff _ (resultShape?_iff p c o)

/-! ## The readback's own notion -/

/-- **The observations `Rt.readback` gives at an immortal view type**: a
natural number at `Nat`; at inductive `i` of `sig`, a constructor with no
fields whose tag the signature lists without fields. -/
def ViewShape (sig : Rt.Sig) : Rt.FoTy → Obs → Prop
  | .nat, .nat _ => True
  | .ind i, .ctor t [] => sig.ctor? i t = some []
  | _, _ => False

instance (sig : Rt.Sig) (ty : Rt.FoTy) (o : Obs) : Decidable (ViewShape sig ty o) := by
  unfold ViewShape
  split <;> infer_instance

/-- The number an observation carries (a `Nat` or a constructor tag) fits a
tagged word. -/
def WordFits : Obs → Prop
  | .nat n => n < Rt.natLimit
  | .ctor t _ => t < Rt.natLimit
  | _ => True

theorem toNat_shiftRight_one_lt (w : Lir.Word) : (w >>> 1).toNat < Rt.natLimit := by
  rw [UInt64.toNat_shiftRight]
  have := w.toNat_lt
  unfold Rt.natLimit
  simp only [UInt64.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]
  omega

/-- **`ViewShape` is the readback's notion.** At a readback type that passes
`isImmortalViewType`, some word reads back as `o` (from any memory, at any
fuel) exactly when `o` is a `ViewShape` observation whose number fits a
tagged word. -/
theorem readback_iff_viewShape {sig : Rt.Sig} {ty : Rt.FoTy}
    (hv : CompileClaim.isImmortalViewType sig ty = true) (fuel : Nat) (m : X86.Memory) (o : Obs) :
    (∃ w, Rt.readback sig fuel m ty w = some o) ↔ ViewShape sig ty o ∧ WordFits o := by
  constructor
  · rintro ⟨w, hw⟩
    cases ty with
    | nat =>
      simp only [Rt.readback] at hw
      split at hw
      · cases hw
        exact ⟨trivial, toNat_shiftRight_one_lt w⟩
      · cases hw
    | ind i =>
      unfold Rt.readback at hw
      dsimp only at hw
      split at hw
      · split at hw
        · next hc =>
          cases hw
          exact ⟨hc, toNat_shiftRight_one_lt w⟩
        · cases hw
      · exfalso
        split at hw
        · cases hw
        · split at hw
          · cases hw
          · split at hw
            · next tys hc =>
              split at hw
              · next hlen =>
                simp only [CompileClaim.isImmortalViewType] at hv
                simp only [Rt.Sig.ctor?] at hc
                cases hrow : sig.inds[i]? with
                | none => rw [hrow] at hv; cases hv
                | some ctors =>
                  rw [hrow] at hv hc
                  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hv
                  simp only [Option.bind_some] at hc
                  have : tys = [] := hv.2 tys (List.mem_of_getElem? hc)
                  subst this
                  simp at hlen
                  omega
              · cases hw
            · cases hw
  · rintro ⟨hs, hf⟩
    cases ty with
    | nat =>
      match o, hs, hf with
      | .nat n, _, hf =>
        have hw : Rt.natWord n = some (UInt64.ofNat (2 * n + 1)) := by
          have hf' : n < Rt.natLimit := hf
          simp [Rt.natWord, hf']
        exact ⟨_, Rt.readback_nat hw⟩
    | ind i =>
      match o, hs, hf with
      | .ctor t [], hs, hf => exact ⟨_, Rt.readback_ctor0 hf hs⟩

/-! ## Totality on result shapes -/

theorem some_beq_false {a : Src.CId} {b : Option Src.CId} (h : b ≠ some a) :
    (some a == b) = false := by
  cases b with
  | none => rfl
  | some x =>
    simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
    exact fun e => h (by rw [e])

theorem resultType?_some {p : Src.Program} {c : Src.CId} {t : Src.Term}
    (h : resultType? p c = some t) : ∃ d, p.decl? c = some d ∧ d.type.pis.2 = t := by
  simp only [resultType?, Option.map_eq_some_iff] at h
  exact h

/-- At the pinned-`Bool` route's signature, with both pinned `Bool`
constructors in the table, `Rt.tagify` maps either one to a constructor the
signature lists without fields. -/
theorem tagify_bool {p : Src.Program} {C : Cfg.Program}
    (hknown : C.known.boolFalse = p.known.boolFalse.map .src ∧
      C.known.boolTrue = p.known.boolTrue.map .src)
    (hrows : BoolRows p C) {k : Src.CId}
    (hk : p.known.boolFalse = some k ∨ p.known.boolTrue = some k) :
    ∃ w, Rt.tagify C.ctors (boolSig C) (.ind 0) (.ctor k []) = some w ∧
      ViewShape (boolSig C) (.ind 0) w := by
  unfold BoolRows boolRows? at hrows
  split at hrows
  · next bF bT hF hT =>
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hrows
    obtain ⟨⟨iF, hiF⟩, ⟨iT, hiT⟩⟩ := hrows
    have hsigF : (boolSig C).inds = [List.replicate (max iF.tag iT.tag + 1) []] := by
      simp only [boolSig, hknown.1, hknown.2, hF, hT, Option.map_some, Option.bind_some, hiF, hiT]
    have hlist : ∀ (info : Fir.CtorInfo), (info = iF ∨ info = iT) →
        (boolSig C).ctor? 0 info.tag = some [] := by
      intro info hi
      have hlt : info.tag < max iF.tag iT.tag + 1 := by
        rcases hi with rfl | rfl <;> omega
      simp only [Rt.Sig.ctor?, hsigF, List.getElem?_cons_zero, Option.bind_some,
        List.getElem?_replicate, hlt, ↓reduceIte]
    rcases hk with hk | hk
    · rw [hF] at hk; cases hk
      refine ⟨.ctor iF.tag [], ?_, hlist iF (.inl rfl)⟩
      simp only [Rt.tagify, hiF, hlist iF (.inl rfl), ↓reduceIte]
    · rw [hT] at hk; cases hk
      refine ⟨.ctor iT.tag [], ?_, hlist iT (.inr rfl)⟩
      simp only [Rt.tagify, hiT, hlist iT (.inr rfl), ↓reduceIte]
  · cases hrows

/-- **Discovery at an enumeration root.** If `discover` gives `(sig, ty)` for
root `c`, `isImmortalViewType sig ty` holds, and `c`'s declared result type is
headed by a safe inductive `I` other than the pinned `Nat`, then `ty` is an
inductive of `sig` and `Rt.tagify` maps every constructor of `I`, with no
fields, to a field-less constructor the signature lists at its table tag. -/
theorem discover_enum_tagify {p : Src.Program} {C : Cfg.Program} {c : Src.CId}
    {sig : Rt.Sig} {ty : Rt.FoTy} (hd : Readback.discover p C c = .ok (sig, ty))
    (hview : CompileClaim.isImmortalViewType sig ty = true)
    {d : Src.Decl} (hdc : p.decl? c = some d) {I : Src.CId} {us : List Ixon.Univ}
    (hhead : d.type.pis.2.spine.1 = .const I us) (hnat : some I ≠ p.known.nat)
    {nl np : Nat} {tyI : Src.Term} {keys : List Src.CId}
    (hI : p.decl? I = some (.induct true nl np 0 tyI keys)) {k : Src.CId} (hk : k ∈ keys) :
    ∃ idx t, ty = .ind idx ∧ Rt.tagify C.ctors sig ty (.ctor k []) = some (.ctor t []) ∧
      sig.ctor? idx t = some [] := by
  obtain ⟨q, hraw, hv, hsig, hty⟩ := Readback.discover_valid hd
  subst hsig hty
  obtain ⟨d', hd', hroot⟩ := Readback.discoverRaw_root hraw
  rw [hdc] at hd'
  cases hd'
  have hlm : Readback.layoutsMatch p C c q = true := (Bool.and_eq_true_iff.mp hv).2
  unfold Readback.layoutsMatch at hlm
  simp only [Bool.and_eq_true, beq_iff_eq] at hlm
  obtain ⟨⟨⟨⟨_, hsr⟩, _⟩, hlen⟩, hrows⟩ := hlm
  obtain ⟨c', us', hsp, hcase⟩ := Readback.shape?_head hroot
  rw [hhead] at hsp
  cases hsp
  rcases hcase with ⟨_, hn⟩ | ⟨lv, ac, nl', np', ty', keys', hrq, _, _⟩
  · exact absurd hn hnat
  · rw [hrq] at hsr
    simp only [Readback.shapeRef, Option.map_eq_some_iff] at hsr
    obtain ⟨⟨s, idx⟩, hfind, hty⟩ := hsr
    have hs : s = .ind I lv ac := by
      have := List.find?_some hfind
      simpa using this
    have hmem := List.mem_of_find?_eq_some hfind
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    simp only at hmem
    have hidx : idx < q.sig.inds.length := by
      have := (List.getElem?_eq_some_iff.1 hmem).1
      omega
    have hzip : (q.shapes.zip q.sig.inds)[idx]? = some (s, q.sig.inds[idx]) :=
      List.getElem?_zip_eq_some.2 ⟨hmem, List.getElem?_eq_getElem hidx⟩
    have hrow := List.all_eq_true.1 hrows _ (List.mem_of_getElem? hzip)
    simp only at hrow
    obtain ⟨ind, ls, args, nl'', np'', ty'', keys'', hsi, hdi, hall⟩ := Readback.rowMatches_spec hrow
    rw [hs] at hsi
    cases hsi
    rw [hI] at hdi
    cases hdi
    obtain ⟨tag, htag⟩ := List.mem_iff_getElem?.1 hk
    have hzk : (k, tag) ∈ keys.zipIdx := List.mem_zipIdx_iff_getElem?.2 htag
    obtain ⟨emitted, fts, hfilter, hetag, hfts⟩ := hall k tag hzk
    have hrowEmpty : fts = [] := by
      have hv' := hview
      rw [← hty] at hv'
      simp only [CompileClaim.isImmortalViewType, List.getElem?_eq_getElem hidx, Bool.and_eq_true,
        List.all_eq_true, List.isEmpty_iff] at hv'
      exact hv'.2 fts (List.mem_of_getElem? hfts)
    subst hrowEmpty
    have hctor : q.sig.ctor? idx emitted.tag = some [] := by
      simp only [Rt.Sig.ctor?, List.getElem?_eq_getElem hidx, Option.bind_some, hetag, hfts]
    have hfind' : C.ctors.find? (fun r => r.key == .src k) = some emitted := by
      rw [← List.head?_filter, hfilter]; rfl
    refine ⟨idx, emitted.tag, hty.symm, ?_, hctor⟩
    rw [← hty]
    simp only [Rt.tagify, Fir.CtorInfo.ofKey, hfind', Option.map_some, hctor, ↓reduceIte]

/-- **Totality on result shapes.** At root `c` with readback type
`rootTy p C c = some (sig, ty)` passing `isImmortalViewType`, `Rt.tagify` maps
every observation of `c`'s result shape to a `ViewShape` observation. On the
pinned-`Bool` route it needs both pinned `Bool` constructors in the table
(`BoolRows`); `hknown` is what the front half guarantees (`runLir_boolKnown`). -/
theorem tagify_resultShape {p : Src.Program} {C : Cfg.Program} {c : Src.CId}
    {sig : Rt.Sig} {ty : Rt.FoTy} (hty : rootTy p C c = some (sig, ty))
    (hview : CompileClaim.isImmortalViewType sig ty = true)
    (hknown : C.known.boolFalse = p.known.boolFalse.map .src ∧
      C.known.boolTrue = p.known.boolTrue.map .src)
    {o : Obs} (hs : ResultShape p c o) (hb : BoolResult p c → BoolRows p C) :
    ∃ w, Rt.tagify C.ctors sig ty o = some w ∧ ViewShape sig ty w := by
  cases hs with
  | nat n hN hres =>
    obtain ⟨d, hd, hpis⟩ := resultType?_some hres
    have hrt : resultTy p c = some .nat := by
      simp [resultTy, hd, hpis, hN]
    simp only [rootTy, hrt, Option.some.injEq, Prod.mk.injEq] at hty
    obtain ⟨rfl, rfl⟩ := hty
    exact ⟨.nat n, rfl, trivial⟩
  | bool hB hBN hres hk =>
    rename_i B k
    obtain ⟨d, hd, hpis⟩ := resultType?_some hres
    have hn : (some B == p.known.nat) = false := some_beq_false hBN
    have hrt : resultTy p c = some (.ind 0) := by
      simp [resultTy, hd, hpis, hn, hB]
    simp only [rootTy, hrt, Option.some.injEq, Prod.mk.injEq] at hty
    obtain ⟨rfl, rfl⟩ := hty
    exact tagify_bool hknown (hb ⟨B, hB, hBN, hres⟩) hk
  | enum hres hhead hIN hIB hI hk =>
    rename_i I k t us nl np tyI keys
    obtain ⟨d, hd, hpis⟩ := resultType?_some hres
    have hrt : resultTy p c = none := by
      unfold resultTy
      rw [hd]
      simp only
      rw [hpis]
      split
      · next r =>
        simp only [Src.Term.spine, Src.Term.spine.go, Src.Term.const.injEq] at hhead
        obtain ⟨rfl, -⟩ := hhead
        simp [some_beq_false hIN, some_beq_false hIB]
      · rfl
    simp only [rootTy, hrt] at hty
    have hdisc : Readback.discover p C c = .ok (sig, ty) := by
      cases h : Readback.discover p C c with
      | error e => rw [h] at hty; cases hty
      | ok v => rw [h] at hty; cases hty; rfl
    obtain ⟨idx, tag, rfl, htag, hctor⟩ := discover_enum_tagify hdisc hview hd
      (by rw [hpis]; exact hhead) (fun e => hIN e.symm) hI hk
    exact ⟨_, htag, hctor⟩

/-! ## The pins the view's `Bool` route reads -/

/-- Erasure records the program's pins in the Lam program. -/
theorem erase_known {p : Src.Program} {ch : Src.Relevance.Checked} {L : Lam.Program}
    {st : Lam.Erase.Stats} (h : Lam.erase p ch = .ok (L, st)) :
    L.known = (Lam.Erase.Input.ofProgram p ch).lamKnown := by
  unfold Lam.erase at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]

theorem step_known (prm : Anf.Shrink.Params) :
    ∀ (s : Anf.Pipeline.Step) (P Q : Anf.Program), P.WF → s.run prm P = .ok Q → Q.known = P.known
  | .shrink c, P, Q, _, h => by
    simp only [Anf.Pipeline.Step.run] at h
    split at h
    · obtain ⟨x, hs, hc⟩ := Lam.ModesOk.bind_ok h
      rw [Anf.Pipeline.Proof.checkGlobalNodes_ok hc]
      exact (Anf.Shrink.Proof.run_global hs).2.1
    · cases h
  | .inline r, P, Q, _, h => by
    simp only [Anf.Pipeline.Step.run] at h
    split at h
    · obtain ⟨x, hr, hc⟩ := Lam.ModesOk.bind_ok h
      rw [Anf.Pipeline.Proof.checkGlobalNodes_ok hc]
      exact (Anf.Inline.Proof.round_global hr).2.1
    · cases h
  | .specialize c, P, Q, hw, h => by
    simp only [Anf.Pipeline.Step.run] at h
    obtain ⟨x, hspec, hc⟩ := Lam.ModesOk.bind_ok h
    rw [Anf.Pipeline.Proof.checkGlobalNodes_ok hc]
    obtain ⟨st, hi, hQ⟩ := Anf.Specialize.Proof.run_inv hw hspec
    exact Anf.Specialize.Proof.run_known hw hi hQ
  | .prune, P, Q, _, h => by
    simp only [Anf.Pipeline.Step.run] at h
    cases h
    rfl

theorem steps_known (prm : Anf.Shrink.Params) : ∀ (steps : List Anf.Pipeline.Step) (P Q : Anf.Program),
    P.WF → steps.foldlM (fun P s => s.run prm P) P = .ok Q → Q.known = P.known
  | [], P, Q, _, h => by
    simp only [List.foldlM_nil] at h
    cases h
    rfl
  | s :: steps, P, Q, hw, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨P1, h1, h2⟩ := Lam.ModesOk.bind_ok h
    have hw1 := (Anf.Pipeline.Proof.step_correct prm s P P1 (.inr Anf.Pipeline.Proof.spec_correct)
      hw h1).1
    exact (steps_known prm steps P1 Q hw1 h2).trans (step_known prm s P P1 hw h1)

/-- The middle end keeps the Lam program's pins. -/
theorem pipeline_known {cert : Anf.Pipeline.Cert} {L : Lam.Program} {Q : Anf.Program}
    (h : Anf.Pipeline.run cert L = .ok Q) : Q.known = L.known := by
  unfold Anf.Pipeline.run at h
  obtain ⟨P, h1, h2⟩ := Lam.ModesOk.bind_ok h
  obtain ⟨P0, h0, hc⟩ := Lam.ModesOk.bind_ok h1
  obtain ⟨L', hl, h0⟩ := Lam.ModesOk.bind_ok h0
  rw [← Anf.Pipeline.Proof.checkLamNodes_ok hl] at h0
  have hP : P = P0 := Anf.Pipeline.Proof.checkGlobalNodes_ok hc
  rw [hP] at h2
  exact (steps_known cert.shrink cert.steps P0 Q (Anf.Pipeline.Proof.convert_wf h0) h2).trans
    (Anf.Convert.Proof.convert_spec h0).2.2.2.2.1

/-- The middle end with the closures step keeps the Lam program's pinned keys. -/
theorem anfOf_known {c : Cert} {src : Src.Program} {L : Lam.Program} {A : Anf.Program}
    (h : anfOf c src L = .ok A) : A.known = L.known := by
  obtain ⟨pre, hpre, hcl⟩ := anfOf_ok h
  obtain ⟨decl, -, hc⟩ := closuresOf_ok hcl
  exact (Anf.Pipeline.Proof.closures_tables hc).1.trans (pipeline_known hpre)

/-- **The front half carries the source's `Bool` pins to Cfg**, as source
constructor keys. -/
theorem runLir_boolKnown {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (h : runLir cfg P c = .ok f) :
    f.cfg.known.boolFalse = f.src.known.boolFalse.map .src ∧
      f.cfg.known.boolTrue = f.src.known.boolTrue.map .src := by
  obtain ⟨-, ⟨st, her⟩, hanf, hfir, hown, hcfg, -, -⟩ := runLir_spec h
  have hk : f.cfg.known = f.lam.known := by
    rw [hcfg, hown]
    exact ((Fir.Proof.lower_fields hfir).2.2.2).trans (anfOf_known hanf)
  rw [hk, erase_known her]
  exact ⟨rfl, rfl⟩

/-! ## The rows of the pinned `Bool` -/

theorem step_ctors (prm : Anf.Shrink.Params) :
    ∀ (s : Anf.Pipeline.Step) (P Q : Anf.Program), P.WF → s.run prm P = .ok Q → Q.ctors = P.ctors
  | .shrink c, P, Q, _, h => by
    simp only [Anf.Pipeline.Step.run] at h
    split at h
    · obtain ⟨x, hs, hc⟩ := Lam.ModesOk.bind_ok h
      rw [Anf.Pipeline.Proof.checkGlobalNodes_ok hc]
      exact Anf.Shrink.Proof.run_ctors hs
    · cases h
  | .inline r, P, Q, _, h => by
    simp only [Anf.Pipeline.Step.run] at h
    split at h
    · obtain ⟨x, hr, hc⟩ := Lam.ModesOk.bind_ok h
      rw [Anf.Pipeline.Proof.checkGlobalNodes_ok hc]
      exact Anf.Inline.Proof.round_ctors hr
    · cases h
  | .specialize c, P, Q, hw, h => by
    simp only [Anf.Pipeline.Step.run] at h
    obtain ⟨x, hspec, hc⟩ := Lam.ModesOk.bind_ok h
    rw [Anf.Pipeline.Proof.checkGlobalNodes_ok hc]
    obtain ⟨st, hi, hQ⟩ := Anf.Specialize.Proof.run_inv hw hspec
    exact Anf.Specialize.Proof.run_ctors hw hi hQ
  | .prune, P, Q, _, h => by
    simp only [Anf.Pipeline.Step.run] at h
    cases h
    rfl

theorem steps_ctors (prm : Anf.Shrink.Params) : ∀ (steps : List Anf.Pipeline.Step) (P Q : Anf.Program),
    P.WF → steps.foldlM (fun P s => s.run prm P) P = .ok Q → Q.ctors = P.ctors
  | [], P, Q, _, h => by
    simp only [List.foldlM_nil] at h
    cases h
    rfl
  | s :: steps, P, Q, hw, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨P1, h1, h2⟩ := Lam.ModesOk.bind_ok h
    have hw1 := (Anf.Pipeline.Proof.step_correct prm s P P1 (.inr Anf.Pipeline.Proof.spec_correct)
      hw h1).1
    exact (steps_ctors prm steps P1 Q hw1 h2).trans (step_ctors prm s P P1 hw h1)

/-- The middle end keeps the Lam program's constructor table. -/
theorem pipeline_ctors {cert : Anf.Pipeline.Cert} {L : Lam.Program} {Q : Anf.Program}
    (h : Anf.Pipeline.run cert L = .ok Q) : Q.ctors = L.ctors := by
  unfold Anf.Pipeline.run at h
  obtain ⟨P, h1, h2⟩ := Lam.ModesOk.bind_ok h
  obtain ⟨P0, h0, hc⟩ := Lam.ModesOk.bind_ok h1
  obtain ⟨L', hl, h0⟩ := Lam.ModesOk.bind_ok h0
  rw [← Anf.Pipeline.Proof.checkLamNodes_ok hl] at h0
  have hP : P = P0 := Anf.Pipeline.Proof.checkGlobalNodes_ok hc
  rw [hP] at h2
  exact (steps_ctors cert.shrink cert.steps P0 Q (Anf.Pipeline.Proof.convert_wf h0) h2).trans
    (Anf.Convert.Proof.convert_spec h0).2.2.2.1

/-- The middle end with the closures step keeps the Lam program's constructor
table, followed by closure rows. -/
theorem anfOf_ctors {c : Cert} {src : Src.Program} {L : Lam.Program} {A : Anf.Program}
    (h : anfOf c src L = .ok A) : ∃ rs, A.ctors = L.ctors ++ rs ∧ ∀ r ∈ rs, ∃ f j, r.key = .clo f j := by
  obtain ⟨pre, hpre, hcl⟩ := anfOf_ok h
  obtain ⟨decl, -, hc⟩ := closuresOf_ok hcl
  obtain ⟨-, rs, hrs, hk⟩ := Anf.Pipeline.Proof.closures_tables hc
  exact ⟨rs, by rw [hrs, pipeline_ctors hpre], hk⟩

/-- Closure rows appended to a table change no source constructor's row. -/
theorem ofKey_append_src {L rs : List Lam.CtorInfo} (hrs : ∀ r ∈ rs, ∃ f j, r.key = .clo f j) (c : Src.CId) :
    Fir.CtorInfo.ofKey (L ++ rs) (.src c) = Fir.CtorInfo.ofKey L (.src c) := by
  unfold Fir.CtorInfo.ofKey
  rw [List.find?_append]
  cases hf : L.find? (·.key == Key.CtorKey.src c) with
  | some x => rfl
  | none =>
    have : rs.find? (·.key == Key.CtorKey.src c) = none := by
      rw [List.find?_eq_none]
      intro r hr
      obtain ⟨f, j, hk⟩ := hrs r hr
      simp [hk]
    simp [this]

/-- A key of the table relation erasure ends with has a row in the table it
emits. -/
theorem ofKey_of_tabOf {I : Lam.Erase.Input} {s : Lam.Erase.St}
    (hinv : Lam.Erase.Proof.CtorInv I s) {c : Src.CId} {n : Nat}
    (h : Lam.Erase.Proof.tabOf s (.src c) n) :
    (Fir.CtorInfo.ofKey (s.ctorOrder.reverse.filterMap s.ctors.get?) (.src c)).isSome := by
  obtain ⟨c', info, hc', hk, -⟩ := h
  cases hk
  have hmem : info ∈ s.ctorOrder.reverse.filterMap s.ctors.get? :=
    List.mem_filterMap.2 ⟨c, List.mem_reverse.2 ((hinv.order c).2 (by rw [hc']; rfl)), hc'⟩
  have hkey := (hinv.rows c info hc').1
  simp only [Fir.CtorInfo.ofKey, Option.isSome_map]
  exact List.find?_isSome.2 ⟨info, hmem, by simp [hkey]⟩

/-- A pinned `Bool` constructor is among the constructors whose rows a root
returning the pinned `Bool` needs. -/
theorem mem_resultCtors_bool {I : Lam.Erase.Input} {c B k : Src.CId} {d : Src.Decl}
    (hd : I.decl? c = some d) (hres : d.type.pis.2 = .const B []) (hB : I.known.bool = some B)
    (hk : I.known.boolFalse = some k ∨ I.known.boolTrue = some k) :
    k ∈ Lam.Erase.resultCtors I c := by
  unfold Lam.Erase.resultCtors
  rw [hd]
  dsimp only
  rw [hres]
  apply List.mem_append_left
  simp only [Src.Term.spine, Src.Term.spine.go, hB, beq_self_eq_true, ↓reduceIte]
  rcases hk with hk | hk <;> simp [hk]

/-- **Erasure gives both pinned `Bool` constructors a row** at a program with
a root returning the pinned `Bool`: each has a row in the Lam table. -/
theorem erase_boolRow {p : Src.Program} {ch : Src.Relevance.Checked} {L : Lam.Program}
    {st : Lam.Erase.Stats} (h : Lam.erase p ch = .ok (L, st)) {addr : Ixon.Address}
    {c : Src.CId} (hroot : (addr, c) ∈ p.roots) (hb : BoolResult p c) {k : Src.CId}
    (hk : p.known.boolFalse = some k ∨ p.known.boolTrue = some k) :
    (Fir.CtorInfo.ofKey L.ctors (.src k)).isSome := by
  have wf := Lam.Erase.Proof.erase_progWF h
  obtain ⟨s, -, -, -, hctors, hinv, -, -, hrows⟩ := Lam.Erase.Proof.erase_reg h
  obtain ⟨B, hB, -, hres⟩ := hb
  obtain ⟨d, hd, hpis⟩ := resultType?_some hres
  have hmem : k ∈ (Lam.Erase.Input.ofProgram p ch).roots.flatMap
      (Lam.Erase.resultCtors (Lam.Erase.Input.ofProgram p ch)) :=
    List.mem_flatMap.2 ⟨c, List.mem_map.2 ⟨(addr, c), hroot, rfl⟩,
      mem_resultCtors_bool (I := Lam.Erase.Input.ofProgram p ch) hd hpis hB hk⟩
  -- the pinned constructor `k`: no fields, and not a pinned `Decidable` one
  obtain ⟨sf, lv, B', cidx, np, nf, ty, hdk⟩ : ∃ sf lv B' cidx np nf ty,
      (Lam.Erase.Input.ofProgram p ch).decl? k = some (.ctor sf lv B' cidx np nf ty) := by
    rcases hk with hk' | hk'
    · obtain ⟨sf, lv, B', np, ty, hdk, -⟩ := wf.boolFalse hk'
      exact ⟨sf, lv, B', 0, np, 0, ty, hdk⟩
    · obtain ⟨sf, lv, B', np, ty, hdk, -⟩ := wf.boolTrue hk'
      exact ⟨sf, lv, B', 1, np, 0, ty, hdk⟩
  have hne : ∀ d, ((Lam.Erase.Input.ofProgram p ch).known.decIsFalse = some d ∨
      (Lam.Erase.Input.ofProgram p ch).known.decIsTrue = some d) → d ≠ k := by
    intro d hdd e
    subst e
    exact wf.decOther hdd (by rcases hk with h | h; exact .inl h; exact .inr (.inl h)) hdk hdk rfl
  have halias : (Lam.Erase.Input.ofProgram p ch).alias k = k :=
    Lam.Erase.Proof.alias_of_notDec (fun d h => hne d (.inl h)) (fun d h => hne d (.inr h))
  obtain ⟨n, hn⟩ := hrows k hmem _ _ _ _ _ _ _ hdk
  rw [halias] at hn
  rw [hctors]
  exact ofKey_of_tabOf hinv hn

/-- **A root returning the pinned `Bool` has rows for both pinned `Bool`
constructors** in the front half's Cfg table, when either is pinned (the
pins come together). -/
theorem Front.boolRows {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) (hb : BoolResult f.src c) {k : Src.CId}
    (hk : f.src.known.boolFalse = some k ∨ f.src.known.boolTrue = some k) :
    BoolRows f.src f.cfg := by
  obtain ⟨-, ⟨st, her⟩, hanf, -, -, -, -, -⟩ := runLir_spec h
  obtain ⟨rs, hrs, hrk⟩ := anfOf_ctors hanf
  have hct : f.cfg.ctors = f.lam.ctors ++ rs := (runLir_ctors h).trans hrs
  have hroot : (addr, c) ∈ f.src.roots := List.mem_of_getElem? hr
  have wf := Lam.Erase.Proof.erase_progWF her
  obtain ⟨F, T, hF, hT⟩ : ∃ F T, f.src.known.boolFalse = some F ∧ f.src.known.boolTrue = some T := by
    rcases hk with hk | hk
    · obtain ⟨_, _, _, _, _, _, t, ht, _⟩ := wf.boolFalse hk
      exact ⟨k, t, hk, ht⟩
    · obtain ⟨_, _, _, _, _, _, f', hf', _⟩ := wf.boolTrue hk
      exact ⟨f', k, hf', hk⟩
  unfold BoolRows boolRows?
  rw [hF, hT, hct]
  simp only [Bool.and_eq_true, ofKey_append_src hrk]
  exact ⟨erase_boolRow her hroot hb (.inl hF), erase_boolRow her hroot hb (.inr hT)⟩

/-! ## At a root of the front half -/

theorem Front.tys_root {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (_h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) : f.tys r = rootTy f.src f.cfg c := by
  simp [Front.tys, hr]

/-- **Totality at a root, through the view.** At root `r` of the front half,
naming constant `c`, with a readback type that passes `isImmortalViewType`,
the view maps every observation of `c`'s result shape to a `ViewShape`
observation. -/
theorem Front.view_resultShape {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {sig : Rt.Sig} {ty : Rt.FoTy}
    (hty : f.tys r = some (sig, ty)) (hview : CompileClaim.isImmortalViewType sig ty = true)
    {o : Obs} (hs : ResultShape f.src c o) :
    ∃ w, f.view r (some o) = some (some w) ∧ ViewShape sig ty w := by
  -- the pinned-`Bool` route's rows: erasure registers both
  have hb : BoolResult f.src c → BoolRows f.src f.cfg := fun hB => by
    cases hs with
    | bool _ _ _ hk => exact Front.boolRows h hr hB hk
    | nat n hN hres =>
      obtain ⟨B, _, hBN, hres'⟩ := hB
      rw [hres] at hres'
      cases hres'
      exact absurd hN hBN
    | enum hres hhead hIN hIB _ _ =>
      obtain ⟨B, hB, _, hres'⟩ := hB
      rw [hres] at hres'
      cases hres'
      simp only [Src.Term.spine, Src.Term.spine.go, Src.Term.const.injEq] at hhead
      obtain ⟨rfl, -⟩ := hhead
      exact absurd hB hIB
  have hty' := hty
  rw [Front.tys_root h hr] at hty'
  obtain ⟨w, hw, hvs⟩ := tagify_resultShape hty' hview (runLir_boolKnown h) hs hb
  refine ⟨w, ?_, hvs⟩
  simp only [Front.view, Rt.viewOf, hty, Option.bind_some, hw, Option.map_some]

/-- **The view rejects only results off the root's shape.** At such a root,
`Front.GoesWrong` holds only if SrcEval gets stuck or traps, or returns a
result that is not of `c`'s result shape. -/
theorem Front.goesWrong_resultShape {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {sig : Rt.Sig} {ty : Rt.FoTy}
    (hty : f.tys r = some (sig, ty)) (hview : CompileClaim.isImmortalViewType sig ty = true)
    {ns : List Nat} (hgw : f.GoesWrong (r, ns)) :
    (∃ k, (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (r, ns) k).GoesWrong) ∨
      ∃ k v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (r, ns) k = .ok v ∧
        ¬ ResultShapeOpt f.src c (Lang.obs v) := by
  obtain ⟨k, hk | ⟨v, hv, hnone⟩⟩ := hgw
  · exact .inl ⟨k, hk⟩
  · refine .inr ⟨k, v, hv, ?_⟩
    rintro ⟨o, ho, hs⟩
    obtain ⟨w, hw, _⟩ := Front.view_resultShape h hr hty hview hs
    rw [ho, hw] at hnone
    cases hnone

/-- **On the `Nat` route the view rejects exactly the results off the
shape**: at a root returning the pinned `Nat`, the view rejects an
observation iff it is not a natural number. -/
theorem Front.view_none_iff_nat {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) (hnat : NatResult f.src c) (ov : Option Obs) :
    f.view r ov = none ↔ ¬ ResultShapeOpt f.src c ov := by
  obtain ⟨N, hN, hres⟩ := hnat
  obtain ⟨d, hd, hpis⟩ := resultType?_some hres
  have hrt : resultTy f.src c = some .nat := by
    simp [resultTy, hd, hpis, hN]
  have hty : f.tys r = some ({}, .nat) := by
    rw [Front.tys_root h hr]
    simp only [rootTy, hrt]
  constructor
  · intro hnone
    rintro ⟨o, rfl, hs⟩
    cases hs with
    | nat n _ _ =>
      simp [Front.view, Rt.viewOf, hty, Rt.tagify] at hnone
    | bool hB hBN hres' _ =>
      rw [hres] at hres'
      cases hres'
      exact hBN hN
    | enum hres' hhead hIN _ _ _ =>
      rw [hres] at hres'
      cases hres'
      simp only [Src.Term.spine, Src.Term.spine.go, Src.Term.const.injEq] at hhead
      obtain ⟨rfl, -⟩ := hhead
      exact hIN hN
  · intro hns
    cases ov with
    | none => simp [Front.view, Rt.viewOf, hty]
    | some o =>
      cases o with
      | nat n => exact absurd ⟨_, rfl, .nat n hN hres⟩ hns
      | word _ => simp [Front.view, Rt.viewOf, hty, Rt.tagify]
      | ctor _ _ => simp [Front.view, Rt.viewOf, hty, Rt.tagify]
      | bytes _ => simp [Front.view, Rt.viewOf, hty, Rt.tagify]

/-! ## The shape view

On the `Bool` and enumeration routes `Front.view` relabels a field-less
constructor by its table tag without checking that it belongs to the root's
result type, so it also accepts a constructor of another inductive whose tag
the signature lists, and the last case of `Front.GoesWrong` (the view rejects
the result) misses such a result. The shape view first asks that the
observation be of the root's result shape (`resultShape?`), then views it as
`Front.view` does. Its rejections are exactly the results off the shape
(`Front.shapeView_none_iff`), and the guarantees stated with `Front.view`
imply the same guarantees stated with it (`Front.sound_shape`,
`Front.safe_shape`). `Front.view` itself is left as it is: the theorems stated
with it also describe what the object returns where SrcEval returns a value
of another type. -/

/-- **The shape view** at root `r`: `Front.view` on an observation of the
result shape of the constant `r` names, and a rejection (`none`) of any other
observation or at an index with no root. -/
def Front.shapeView (f : Front) (r : Nat) (ov : Option Obs) : Option (Option Obs) :=
  match f.src.roots[r]?, ov with
  | some (_, c), some o => if resultShape? f.src c o then f.view r (some o) else none
  | _, _ => none

/-- **The source goes wrong for the shape view**: SrcEval is stuck or traps
at some clock, or returns a value the shape view rejects. -/
def Front.ShapeGoesWrong (f : Front) (i : Nat × List Nat) : Prop :=
  ∃ k, (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k).GoesWrong ∨
    ∃ v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .ok v ∧
      f.shapeView i.1 (Lang.obs v) = none

/-- What the shape view accepts, the view accepts alike, and it is of the
shape of the root's result. -/
theorem Front.shapeView_some {f : Front} {r : Nat} {ov : Option Obs} {w : Option Obs}
    (h : f.shapeView r ov = some w) :
    f.view r ov = some w ∧ ∃ addr c o, f.src.roots[r]? = some (addr, c) ∧ ov = some o ∧
      ResultShape f.src c o := by
  unfold Front.shapeView at h
  split at h
  · next addr c o hr =>
    split at h
    · next hs => exact ⟨h, addr, c, o, by rw [hr], rfl, (resultShape?_iff _ _ _).1 hs⟩
    · cases h
  · cases h

/-- On the root's result shape the shape view is the view. -/
theorem Front.shapeView_of_shape {f : Front} {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {o : Obs} (hs : ResultShape f.src c o) :
    f.shapeView r (some o) = f.view r (some o) := by
  simp only [Front.shapeView, hr, (resultShape?_iff _ _ _).2 hs, ↓reduceIte]

/-- Off the root's result shape the shape view rejects. -/
theorem Front.shapeView_off_shape {f : Front} {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {ov : Option Obs} (hs : ¬ ResultShapeOpt f.src c ov) :
    f.shapeView r ov = none := by
  cases hw : f.shapeView r ov with
  | none => rfl
  | some w =>
    obtain ⟨-, addr', c', o, hr', rfl, hs'⟩ := Front.shapeView_some hw
    rw [hr] at hr'
    cases hr'
    exact absurd ⟨o, rfl, hs'⟩ hs

/-- A source that goes wrong for the view goes wrong for the shape view. -/
theorem Front.goesWrong_shape {f : Front} {i : Nat × List Nat} (h : f.GoesWrong i) :
    f.ShapeGoesWrong i := by
  obtain ⟨k, hk | ⟨v, hv, hnone⟩⟩ := h
  · exact ⟨k, .inl hk⟩
  · refine ⟨k, .inr ⟨v, hv, ?_⟩⟩
    cases hw : f.shapeView i.1 (Lang.obs v) with
    | none => rfl
    | some w =>
      rw [(Front.shapeView_some hw).1] at hnone
      cases hnone

/-- **The shape view rejects exactly the results off the shape**: at root `r`
of the front half, naming constant `c`, with a readback type that passes
`isImmortalViewType` (the `Nat`, pinned-`Bool` and enumeration routes), the
shape view rejects an observation iff it is not of `c`'s result shape. -/
theorem Front.shapeView_none_iff {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {sig : Rt.Sig} {ty : Rt.FoTy}
    (hty : f.tys r = some (sig, ty)) (hview : CompileClaim.isImmortalViewType sig ty = true)
    (ov : Option Obs) :
    f.shapeView r ov = none ↔ ¬ ResultShapeOpt f.src c ov := by
  constructor
  · rintro hnone ⟨o, rfl, hs⟩
    obtain ⟨w, hw, -⟩ := Front.view_resultShape h hr hty hview hs
    rw [Front.shapeView_of_shape hr hs, hw] at hnone
    cases hnone
  · exact Front.shapeView_off_shape hr

/-- **The source goes wrong for the shape view exactly when SrcEval gets
stuck or traps, or returns a result off the root's shape** (at such a root). -/
theorem Front.shapeGoesWrong_iff {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {sig : Rt.Sig} {ty : Rt.FoTy}
    (hty : f.tys r = some (sig, ty)) (hview : CompileClaim.isImmortalViewType sig ty = true)
    (ns : List Nat) :
    f.ShapeGoesWrong (r, ns) ↔
      (∃ k, (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (r, ns) k).GoesWrong) ∨
        ∃ k v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (r, ns) k = .ok v ∧
          ¬ ResultShapeOpt f.src c (Lang.obs v) := by
  constructor
  · rintro ⟨k, hk | ⟨v, hv, hnone⟩⟩
    · exact .inl ⟨k, hk⟩
    · exact .inr ⟨k, v, hv, (Front.shapeView_none_iff h hr hty hview _).1 hnone⟩
  · rintro (⟨k, hk⟩ | ⟨k, v, hv, hs⟩)
    · exact ⟨k, .inl hk⟩
    · exact ⟨k, .inr ⟨v, hv, (Front.shapeView_none_iff h hr hty hview _).2 hs⟩⟩

/-- **Soundness on the shape view**, from soundness on the view: a value the
object returns is the shape view of a value SrcEval returns, or the source
goes wrong for the shape view. -/
theorem Front.sound_shape {f : Front} {i : Nat × List Nat} {w : Option Obs}
    (h : (∃ k' v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k' = .ok v ∧
      f.view i.1 (Lang.obs v) = some w) ∨ f.GoesWrong i) :
    (∃ k' v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k' = .ok v ∧
      f.shapeView i.1 (Lang.obs v) = some w) ∨ f.ShapeGoesWrong i := by
  rcases h with ⟨k', v, hv, hview⟩ | hg
  · cases hw : f.shapeView i.1 (Lang.obs v) with
    | none => exact .inr ⟨k', .inr ⟨v, hv, hw⟩⟩
    | some w' =>
      rw [(Front.shapeView_some hw).1] at hview
      cases hview
      exact .inl ⟨k', v, hv, hw⟩
  · exact .inr (Front.goesWrong_shape hg)

/-- **Safety on the shape view**, from safety on the view. -/
theorem Front.safe_shape {f : Front} {i : Nat × List Nat} {Q : Prop}
    (h : ¬ f.GoesWrong i → Q) (hs : ¬ f.ShapeGoesWrong i) : Q :=
  h fun hg => hs (Front.goesWrong_shape hg)

/-! ## At the root a claim names -/

theorem rootsOf_get_const {cfg : Config} {p : Src.Program} {C : Cfg.Program} {l : Rt.Lowered} :
    ∀ {rows : List (Nat × (Ixon.Address × Src.CId) × Fir.FunId × (Lir.FunId × String))} {i : Nat}
      {root : Root}, (rootsOf cfg p C l rows)[i]? = some root →
      ∃ j addr fx fn sym, rows[i]? = some (j, (addr, root.const), fx, (fn, sym)) ∧
        root.ty = rootTy p C root.const := by
  intro rows
  induction rows with
  | nil => intro i root h; simp [rootsOf] at h
  | cons row rest ih =>
    obtain ⟨j, ⟨addr, cst⟩, fx, ⟨fn, sym⟩⟩ := row
    intro i root h
    cases i with
    | zero =>
      simp only [rootsOf, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨j, addr, fx, fn, sym, rfl, rfl⟩
    | succ i =>
      simp only [rootsOf, List.getElem?_cons_succ] at h
      exact ih h

/-- **At root 0 of artifact `a` with root record `root`, the source goes wrong
only off the root's shape**: SrcEval gets stuck or traps, or returns a result
that is not of `root.const`'s result shape. -/
def RootWrongOffShape (a : Artifact) (root : Root) : Prop :=
  ∀ ns : List Nat, a.front.GoesWrong (0, ns) →
    (∃ k, (Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (0, ns) k).GoesWrong) ∨
      ∃ k v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (0, ns) k = .ok v ∧
        ¬ ResultShapeOpt a.src root.const (Lang.obs v)

/-- At the first root of an artifact of `Recheck.run`, when it passes
`checkImmortalRoot`: the front half, the source root it names, and its
readback type, which passes `isImmortalViewType`. -/
theorem Artifact.immortalRoot {cfg : Config} {P : Src.Program} {cert : Cert}
    {a : Artifact} (hrun : run cfg P cert = .ok a) {root : Root}
    (hhead : a.roots.head? = some root) (hok : CompileClaim.checkImmortalRoot a.src root = true) :
    runLir cfg P cert = .ok a.front ∧ (∃ addr, a.src.roots[0]? = some (addr, root.const)) ∧
      ∃ sig ty, a.front.tys 0 = some (sig, ty) ∧ CompileClaim.isImmortalViewType sig ty = true := by
  obtain ⟨f, hf, hsrc, hch, hlam, hanf, hfir, hown, hcfg, hlow, hroots⟩ := run_runLir hrun
  have hfront : a.front = f := by
    cases f
    simp only [Artifact.front, hsrc, hch, hlam, hanf, hfir, hown, hcfg, hlow]
  rw [hroots, List.head?_eq_getElem?] at hhead
  obtain ⟨j, addr, fx, fn, sym, hrow, hrty⟩ := rootsOf_get_const hhead
  simp only [List.getElem?_zip_eq_some] at hrow
  obtain ⟨-, hsrc0, -⟩ := hrow
  simp only [CompileClaim.checkImmortalRoot, Bool.and_eq_true] at hok
  obtain ⟨-, hok⟩ := hok
  cases hty : root.ty with
  | none => rw [hty] at hok; cases hok
  | some st =>
    obtain ⟨sig, ty⟩ := st
    rw [hty] at hok
    refine ⟨by rw [hfront]; exact hf, ⟨addr, by rw [hsrc]; exact hsrc0⟩, sig, ty, ?_, hok⟩
    rw [hfront, Front.tys_root hf hsrc0, ← hrty, hty]

/-- **A claim's inputs are covered**: at the first root of a front half's roots
whose declared parameters are its `params` `Nat`s (`rootParamsAllNat`), every
input of exactly `params` arguments is of the declared count, so the
end-to-end theorems cover it (`Artifact.covered_head` on the immortal path,
`RcReplay.Artifact.covered_head` on the plain-RC path). -/
theorem covered_rootsOf_head {cfg : Config} {src : Src.Program} {C : Cfg.Program} {l : Rt.Lowered}
    {mid : Anf.Pipeline.Cert} {lam : Lam.Program} {anf : Anf.Program} {root : Root}
    (hhead : (rootsOf cfg src C l ((List.range src.roots.length).zip
      (src.roots.zip (C.exports.zip l.roots)))).head? = some root)
    (hnat : CompileClaim.rootParamsAllNat src root = true)
    {ns : List Nat} (hlen : ns.length = root.params) : Covered mid src lam anf (0, ns) := by
  rw [List.head?_eq_getElem?] at hhead
  obtain ⟨j, addr, fx, fn, sym, hrow, -⟩ := rootsOf_get_const hhead
  simp only [List.getElem?_zip_eq_some] at hrow
  obtain ⟨-, hsrc0, -⟩ := hrow
  refine .inl fun addr' c hc n hn => ?_
  rw [hsrc0, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨-, rfl⟩ := hc
  unfold CompileClaim.rootParamsAllNat at hnat
  unfold declaredParams at hn
  cases hd : src.decl? root.const with
  | none => rw [hd] at hnat; cases hnat
  | some d =>
    rw [hd] at hnat hn
    simp only [Bool.and_eq_true, beq_iff_eq] at hnat
    simp only [Option.map_some, Option.some.injEq] at hn
    rw [hlen, ← hnat.1.2, hn]

theorem Artifact.covered_head {cfg : Config} {P : Src.Program} {cert : Cert}
    {a : Artifact} (hrun : run cfg P cert = .ok a) {root : Root}
    (hhead : a.roots.head? = some root) (hnat : CompileClaim.rootParamsAllNat a.src root = true)
    {ns : List Nat} (hlen : ns.length = root.params) : a.front.Covered cert (0, ns) := by
  obtain ⟨f, -, hsrc, -, hlam, hanf, -, -, -, -, hroots⟩ := run_runLir hrun
  rw [hroots] at hhead
  rw [hsrc] at hnat
  show Covered cert.mid a.src a.lam a.anf (0, ns)
  rw [hsrc, hlam, hanf]
  exact covered_rootsOf_head hhead hnat hlen

/-- **The view's rejections at an immortal root.** For an artifact of
`Recheck.run` whose first root passes `checkImmortalRoot`, the source goes
wrong at that root only off the root's shape (`RootWrongOffShape`). -/
theorem Artifact.goesWrong_immortalRoot {cfg : Config} {P : Src.Program} {cert : Cert}
    {a : Artifact} (hrun : run cfg P cert = .ok a) {root : Root}
    (hhead : a.roots.head? = some root) (hok : CompileClaim.checkImmortalRoot a.src root = true) :
    RootWrongOffShape a root := by
  intro ns hgw
  obtain ⟨hf, ⟨addr, hsrc0⟩, sig, ty, htys, hview⟩ := Artifact.immortalRoot hrun hhead hok
  exact Front.goesWrong_resultShape hf hsrc0 htys hview hgw

/-- **The guarantees at root 0 of artifact `a`, on the shape view**, for its
object linked with driver `D`, on every input `Recheck.sound` covers under
certificate `cert` (`Front.Covered`): a value the object returns is the shape view
of a value SrcEval returns, or the source goes wrong for the shape view; if
the source does not go wrong for the shape view, the object goes wrong at no
clock; and the source goes wrong for the shape view exactly when SrcEval gets
stuck or traps, or returns a result off `root.const`'s result shape. -/
def ShapeClaim (a : Artifact) (cert : Cert) (root : Root) (D : X86.Driver) : Prop :=
  ∀ ns : List Nat, a.front.Covered cert (0, ns) →
    (∀ k w, Lang.run (a.linked D) (0, ns) k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (0, ns) k' = .ok v ∧
        a.front.shapeView 0 (Lang.obs v) = some w) ∨ a.front.ShapeGoesWrong (0, ns)) ∧
    (¬ a.front.ShapeGoesWrong (0, ns) → ∀ k, ¬ (Lang.run (a.linked D) (0, ns) k).GoesWrong) ∧
    (a.front.ShapeGoesWrong (0, ns) ↔
      (∃ k, (Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (0, ns) k).GoesWrong) ∨
        ∃ k v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (0, ns) k = .ok v ∧
          ¬ ResultShapeOpt a.src root.const (Lang.obs v))

/-- **The shape-view guarantees at an immortal root**, from the guarantees on
the view (`Recheck.sound`, or the zero-RC path's) at root 0. -/
theorem Artifact.shapeClaim {cfg : Config} {P : Src.Program} {cert : Cert}
    {a : Artifact} (hrun : run cfg P cert = .ok a) {root : Root}
    (hhead : a.roots.head? = some root) (hok : CompileClaim.checkImmortalRoot a.src root = true)
    (D : X86.Driver)
    (hview : ∀ ns : List Nat, a.front.Covered cert (0, ns) →
      (∀ k w, Lang.run (a.linked D) (0, ns) k = .ok w →
        (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (0, ns) k' = .ok v ∧
          a.front.view 0 (Lang.obs v) = some w) ∨ a.front.GoesWrong (0, ns)) ∧
      (¬ a.front.GoesWrong (0, ns) → ∀ k, ¬ (Lang.run (a.linked D) (0, ns) k).GoesWrong)) :
    ShapeClaim a cert root D := by
  obtain ⟨hf, ⟨addr, hsrc0⟩, sig, ty, htys, hvt⟩ := Artifact.immortalRoot hrun hhead hok
  intro ns hcov
  exact ⟨fun k w hw => Front.sound_shape (f := a.front) (i := (0, ns)) ((hview ns hcov).1 k w hw),
    Front.safe_shape (f := a.front) (i := (0, ns)) (hview ns hcov).2,
    Front.shapeGoesWrong_iff hf hsrc0 htys hvt ns⟩

end IxCC.Recheck
