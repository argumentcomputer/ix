import IxCC.CompileClaim
import IxCC.Recheck.Proof.Sound
import IxCC.Recheck.Linked
import IxCC.Anf.Proof.Spec.Run

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
  from its word. On the `Nat` route and the enumeration route (readback type
  from `Readback.discover`) this needs nothing more. On the pinned-`Bool` route
  it needs both pinned `Bool` constructors to have a row in the program's
  constructor table (`BoolRows`), which `checkImmortalRoot` does not check: a
  program that never constructs or matches one of them has no row for it.
* **The view's rejections** (`Front.goesWrong_resultShape`,
  `Artifact.goesWrong_immortalRoot`): for a root that `checkImmortalRoot`
  accepts, the case of `Front.GoesWrong` where the view rejects the result
  happens only when the result is not of the root's result shape (or, on the
  `Bool` route, when a pinned `Bool` constructor has no row). On the `Nat`
  route the view rejects exactly the results that are not of the shape
  (`Front.view_none_iff_nat`). On the other routes the converse fails: the
  view relabels a field-less constructor by its table tag and does not check
  which inductive it belongs to, so it accepts a constructor of another
  enumeration whose tag the signature lists.

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

/-- **The front half carries the source's `Bool` pins to Cfg**, as source
constructor keys. -/
theorem runLir_boolKnown {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (h : runLir cfg P c = .ok f) :
    f.cfg.known.boolFalse = f.src.known.boolFalse.map .src ∧
      f.cfg.known.boolTrue = f.src.known.boolTrue.map .src := by
  obtain ⟨-, ⟨st, her⟩, hanf, hfir, hown, hcfg, -, -⟩ := runLir_spec h
  have hk : f.cfg.known = f.lam.known := by
    rw [hcfg, hown]
    exact ((Fir.Proof.lower_fields hfir).2.2.2).trans (pipeline_known hanf)
  rw [hk, erase_known her]
  exact ⟨rfl, rfl⟩

/-! ## At a root of the front half -/

theorem Front.tys_root {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (_h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) : f.tys r = rootTy f.src f.cfg c := by
  simp [Front.tys, hr]

/-- **Totality at a root, through the view.** At root `r` of the front half,
naming constant `c`, with a readback type that passes `isImmortalViewType`,
the view maps every observation of `c`'s result shape to a `ViewShape`
observation (on the pinned-`Bool` route, when both pinned constructors have a
row). -/
theorem Front.view_resultShape {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {sig : Rt.Sig} {ty : Rt.FoTy}
    (hty : f.tys r = some (sig, ty)) (hview : CompileClaim.isImmortalViewType sig ty = true)
    {o : Obs} (hs : ResultShape f.src c o) (hb : BoolResult f.src c → BoolRows f.src f.cfg) :
    ∃ w, f.view r (some o) = some (some w) ∧ ViewShape sig ty w := by
  have hty' := hty
  rw [Front.tys_root h hr] at hty'
  obtain ⟨w, hw, hvs⟩ := tagify_resultShape hty' hview (runLir_boolKnown h) hs hb
  refine ⟨w, ?_, hvs⟩
  simp only [Front.view, Rt.viewOf, hty, Option.bind_some, hw, Option.map_some]

/-- **The view rejects only results off the root's shape.** At such a root,
`Front.GoesWrong` holds only if SrcEval gets stuck or traps, or returns a
result that is not of `c`'s result shape, or (pinned-`Bool` route only) a
pinned `Bool` constructor has no row in the constructor table. -/
theorem Front.goesWrong_resultShape {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runLir cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {sig : Rt.Sig} {ty : Rt.FoTy}
    (hty : f.tys r = some (sig, ty)) (hview : CompileClaim.isImmortalViewType sig ty = true)
    {ns : List Nat} (hgw : f.GoesWrong (r, ns)) :
    (∃ k, (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (r, ns) k).GoesWrong) ∨
      ∃ k v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (r, ns) k = .ok v ∧
        (¬ ResultShapeOpt f.src c (Lang.obs v) ∨ (BoolResult f.src c ∧ ¬ BoolRows f.src f.cfg)) := by
  obtain ⟨k, hk | ⟨v, hv, hnone⟩⟩ := hgw
  · exact .inl ⟨k, hk⟩
  · refine .inr ⟨k, v, hv, ?_⟩
    by_cases hbr : BoolResult f.src c ∧ ¬ BoolRows f.src f.cfg
    · exact .inr hbr
    · left
      rintro ⟨o, ho, hs⟩
      have hb : BoolResult f.src c → BoolRows f.src f.cfg := fun hB =>
        Decidable.byContradiction fun hn => hbr ⟨hB, hn⟩
      obtain ⟨w, hw, _⟩ := Front.view_resultShape h hr hty hview hs hb
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
that is not of `root.const`'s result shape, or (pinned-`Bool` route only) a
pinned `Bool` constructor has no row in the constructor table. -/
def RootWrongOffShape (a : Artifact) (root : Root) : Prop :=
  ∀ ns : List Nat, a.front.GoesWrong (0, ns) →
    (∃ k, (Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (0, ns) k).GoesWrong) ∨
      ∃ k v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (0, ns) k = .ok v ∧
        (¬ ResultShapeOpt a.src root.const (Lang.obs v) ∨
          (BoolResult a.src root.const ∧ ¬ BoolRows a.src a.cfg))

/-- **The view's rejections at an immortal root.** For an artifact of
`Recheck.run` whose first root passes `checkImmortalRoot`, the source goes
wrong at that root only off the root's shape (`RootWrongOffShape`). -/
theorem Artifact.goesWrong_immortalRoot {cfg : Config} {P : Src.Program} {cert : Cert}
    {a : Artifact} (hrun : run cfg P cert = .ok a) {root : Root}
    (hhead : a.roots.head? = some root) (hok : CompileClaim.checkImmortalRoot a.src root = true) :
    RootWrongOffShape a root := by
  intro ns hgw
  obtain ⟨f, hf, hsrc, hch, hlam, hanf, hfir, hown, hcfg, hlow, hroots⟩ := run_runLir hrun
  have hfront : a.front = f := by
    cases f
    simp only [Artifact.front, hsrc, hch, hlam, hanf, hfir, hown, hcfg, hlow]
  rw [hfront] at hgw
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
    have htys : f.tys 0 = some (sig, ty) := by
      rw [Front.tys_root hf hsrc0, ← hrty, hty]
    have := Front.goesWrong_resultShape hf hsrc0 htys hok hgw
    rw [hsrc, hch, hcfg]
    exact this

end IxCC.Recheck
