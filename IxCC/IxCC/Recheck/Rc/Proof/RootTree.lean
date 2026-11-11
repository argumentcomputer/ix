import IxCC.Recheck.Proof.RootShape
import IxCC.Recheck.Rc.Proof.Roots
import IxCC.Recheck.Rc.Proof.SourceSound
import IxCC.Recheck.Rc.Proof.Parts
import IxCC.Cfg.Rc.Proof.Ordinary

/-! # The results a plain-RC root's declared type describes

A compile claim on the plain-RC path is accepted only if `checkPlainRcRoot`
holds: the root's parameters are `Nat` and it has a readback type. Its view
(`RcReplay.Front.view`, `Rt.Rc.Procs.Readback.treeView`) relabels a first-order constructor
tree by table tags, and the plain-RC `GoesWrong` lets the source go wrong by
returning a value the view rejects. This module says which results the root's
declared type describes and proves that the view rejects none of them.

* `TreeShape p s o`: an observation of the ground first-order shape `s`
  (`Readback.Shape`, what `Readback.shape?` makes of a type): a natural number
  at `Nat`; at an inductive instance, one of the inductive's constructors
  whose fields are observations of the shapes of its field types at that
  instance (`Readback.fieldShapes`), recursively. `RootTreeShape p c o`:
  `o` is of the shape of root `c`'s declared result type.
* `PlainShape p c o`: for a root returning the pinned `Nat` or `Bool`, its
  `ResultShape` (the readback type is `Nat`, or the pinned `Bool`'s
  signature); for any other root, `RootTreeShape` (the readback type is the
  one `Readback.discover` finds).
* **Totality** (`discover_treeView`, `RcReplay.Front.view_plainShape`): at
  a root with a readback type, the view accepts every observation of the
  root's `PlainShape`.
* **The view's rejections** (`RcReplay.Front.goesWrong_plainShape`,
  `RcReplay.Artifact.goesWrong_plainRoot`): for a root that
  `checkPlainRcRoot` accepts, the case of the plain-RC `GoesWrong` where the
  view rejects the result happens only when the result is not of the root's
  `PlainShape`.

Not proved: the converse (on a constructor tree, the view does not check
that a constructor belongs to the inductive of its position, so it accepts
some observations off the shape); that the object's heap readback
(`Rt.readback` on the plain-RC heap) reads back every observation of the
shape from some memory; and that SrcEval on a well-typed root returns a
result of its shape (type preservation for SrcEval). -/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-! ## Constructor trees -/

mutual

/-- **An observation of a ground first-order shape**: a natural number at
`Nat`; at an instance of an inductive `ind` with constructors `keys`, its
constructor `k` (at index `tag`) whose fields are observations of the shapes
of `k`'s field types at the instance. -/
inductive TreeShape (p : Src.Program) : Readback.Shape → Obs → Prop
  | nat (n : Nat) : TreeShape p .nat (.nat n)
  | ctor {ind : Src.CId} {ls : List Nat} {args : List Readback.Shape} {nl np : Nat}
      {tyI : Src.Term} {keys : List Src.CId} {tag : Nat} {k : Src.CId}
      {fields : List Readback.Shape} {fs : List Obs}
      (hind : p.decl? ind = some (.induct true nl np 0 tyI keys)) (hk : keys[tag]? = some k)
      (hf : Readback.fieldShapes p (.ind ind ls args) k = .ok (tag, fields))
      (hfs : TreeShapes p fields fs) : TreeShape p (.ind ind ls args) (.ctor k fs)

/-- Observations of a list of shapes, position by position. -/
inductive TreeShapes (p : Src.Program) : List Readback.Shape → List Obs → Prop
  | nil : TreeShapes p [] []
  | cons {s : Readback.Shape} {o : Obs} {ss : List Readback.Shape} {os : List Obs} :
      TreeShape p s o → TreeShapes p ss os → TreeShapes p (s :: ss) (o :: os)

end

/-- **The constructor trees root `c`'s declared type describes**: `c` is
monomorphic, its result type has a ground first-order shape, and `o` is an
observation of it. -/
def RootTreeShape (p : Src.Program) (c : Src.CId) (o : Obs) : Prop :=
  ∃ d s, p.decl? c = some d ∧ d.lvls = 0 ∧ Readback.shape? p 128 [] [] d.type.pis.2 = some s ∧
    TreeShape p s o

/-- **The results a plain-RC root `c`'s declared type describes**: its
`ResultShape` for a root returning the pinned `Nat` or `Bool`, a constructor
tree of its declared type (`RootTreeShape`) for any other root. -/
def PlainShape (p : Src.Program) (c : Src.CId) (o : Obs) : Prop :=
  match resultTy p c with
  | none => RootTreeShape p c o
  | some _ => ResultShape p c o

/-- An optional observation of the root's `PlainShape`. -/
def PlainShapeOpt (p : Src.Program) (c : Src.CId) (ov : Option Obs) : Prop :=
  ∃ o, ov = some o ∧ PlainShape p c o

/-! ## Totality on constructor trees -/

/-- The rows of signature `sig` match the shapes `shapes`, position by
position (what `Readback.layoutsMatch` checks of a discovery candidate). -/
def RowsMatch (p : Src.Program) (C : Cfg.Program) (shapes : List Readback.Shape) (sig : Rt.Sig) :
    Prop :=
  shapes.length = sig.inds.length ∧
    (shapes.zip sig.inds).all (fun (shape, row) => Readback.rowMatches p C shapes shape row) = true

mutual

/-- At a signature whose rows match the shapes `shapes`, the plain-RC view
maps every observation of a shape that `shapes` lists. -/
theorem treeShape_view {p : Src.Program} {C : Cfg.Program} {shapes : List Readback.Shape}
    {sig : Rt.Sig} (hm : RowsMatch p C shapes sig) : ∀ {s : Readback.Shape} {o : Obs},
    TreeShape p s o → ∀ {t : Rt.FoTy}, Readback.shapeRef shapes s = some t →
      ∃ w, Rt.Rc.Procs.Readback.treeView C.ctors sig t o = some w
  | _, _, .nat n, t, ht => by
    simp only [Readback.shapeRef, Option.some.injEq] at ht
    subst ht
    exact ⟨.nat n, by rw [Rt.Rc.Procs.Readback.treeView]⟩
  | _, _, @TreeShape.ctor _ ind ls args _ _ _ keys tag k fields fs hind hk hf hfs, t, ht => by
    obtain ⟨hlen, hrows⟩ := hm
    simp only [Readback.shapeRef, Option.map_eq_some_iff] at ht
    obtain ⟨⟨s', idx⟩, hfind, rfl⟩ := ht
    have hs' : s' = .ind ind ls args := by
      have := List.find?_some hfind
      simpa using this
    subst hs'
    have hmem := List.mem_of_find?_eq_some hfind
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    simp only at hmem
    have hidx : idx < sig.inds.length := by
      have := (List.getElem?_eq_some_iff.1 hmem).1
      omega
    have hzip : (shapes.zip sig.inds)[idx]? = some (.ind ind ls args, sig.inds[idx]) :=
      List.getElem?_zip_eq_some.2 ⟨hmem, List.getElem?_eq_getElem hidx⟩
    have hrow := List.all_eq_true.1 hrows _ (List.mem_of_getElem? hzip)
    simp only at hrow
    obtain ⟨ind', ls', args', nl', np', ty', keys', hsi, hdi, hall⟩ := Readback.rowMatches_fields hrow
    cases hsi
    rw [hind] at hdi
    cases hdi
    have hzk : (k, tag) ∈ keys.zipIdx := List.mem_zipIdx_iff_getElem?.2 hk
    obtain ⟨fields', emitted, fts, hf', hfilter, hetag, hmf, hrowt⟩ := hall k tag hzk
    rw [hf] at hf'
    cases hf'
    obtain ⟨ws, hws⟩ := treeShapes_view ⟨hlen, hrows⟩ hfs hmf
    have hfind' : C.ctors.find? (fun r => r.key == .src k) = some emitted := by
      rw [← List.head?_filter, hfilter]; rfl
    have hctor : sig.ctor? idx emitted.tag = some fts := by
      simp only [Rt.Sig.ctor?, List.getElem?_eq_getElem hidx, Option.bind_some, hetag, hrowt]
    refine ⟨.ctor emitted.tag ws, ?_⟩
    rw [Rt.Rc.Procs.Readback.treeView]
    simp [Fir.CtorInfo.ofKey, hfind', hctor, hws]

/-- `treeShape_view` on a list of fields. -/
theorem treeShapes_view {p : Src.Program} {C : Cfg.Program} {shapes : List Readback.Shape}
    {sig : Rt.Sig} (hm : RowsMatch p C shapes sig) : ∀ {ss : List Readback.Shape} {os : List Obs},
    TreeShapes p ss os → ∀ {ts : List Rt.FoTy}, ss.mapM (Readback.shapeRef shapes) = some ts →
      ∃ ws, Rt.Rc.Procs.Readback.fieldsView C.ctors sig ts os = some ws
  | _, _, .nil, ts, ht => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at ht
    subst ht
    exact ⟨[], by rw [Rt.Rc.Procs.Readback.fieldsView]⟩
  | _, _, .cons h hs, ts, ht => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ht
    obtain ⟨t, ht1, ts', ht2, rfl⟩ := ht
    obtain ⟨w, hw⟩ := treeShape_view hm h ht1
    obtain ⟨ws, hws⟩ := treeShapes_view hm hs ht2
    refine ⟨w :: ws, ?_⟩
    rw [Rt.Rc.Procs.Readback.fieldsView]
    simp [hw, hws]

end

/-- **Discovery's signature relabels every constructor tree of the root's
declared type.** -/
theorem discover_treeView {p : Src.Program} {C : Cfg.Program} {c : Src.CId}
    {sig : Rt.Sig} {ty : Rt.FoTy} (hd : Readback.discover p C c = .ok (sig, ty)) {o : Obs}
    (hs : RootTreeShape p c o) : ∃ w, Rt.Rc.Procs.Readback.treeView C.ctors sig ty o = some w := by
  obtain ⟨q, hraw, hv, hsig, hty⟩ := Readback.discover_valid hd
  subst hsig hty
  obtain ⟨d', hd', hroot⟩ := Readback.discoverRaw_root hraw
  obtain ⟨d, s, hdc, -, hshape, hts⟩ := hs
  rw [hdc] at hd'
  cases hd'
  rw [hshape] at hroot
  cases hroot
  have hlm : Readback.layoutsMatch p C c q = true := (Bool.and_eq_true_iff.mp hv).2
  unfold Readback.layoutsMatch at hlm
  simp only [Bool.and_eq_true, beq_iff_eq] at hlm
  obtain ⟨⟨⟨⟨_, hsr⟩, _⟩, hlen⟩, hrows⟩ := hlm
  exact treeShape_view ⟨hlen, hrows⟩ hts hsr

/-! ## The plain-RC front half -/

namespace RcReplay

theorem runFront_ctors {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runFront cfg P cert = .ok f) : f.cfg.base.ctors = f.anf.ctors := by
  obtain ⟨-, -, -, hfir, -, hgen, -⟩ := runFront_spec h
  have ht := congrArg Own.Tables.ctors (Cfg.Rc.generate_tables hgen)
  exact ht.trans (Fir.Proof.lower_fields hfir).2.2.1

theorem runFront_boolKnown {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runFront cfg P cert = .ok f) :
    f.cfg.base.known.boolFalse = f.src.known.boolFalse.map .src ∧
      f.cfg.base.known.boolTrue = f.src.known.boolTrue.map .src := by
  obtain ⟨-, ⟨st, her⟩, hanf, hfir, -, hgen, -⟩ := runFront_spec h
  have hk : f.cfg.base.known = f.lam.known :=
    (congrArg Own.Tables.known (Cfg.Rc.generate_tables hgen)).trans
      ((Fir.Proof.lower_fields hfir).2.2.2.trans (anfOf_known hanf))
  rw [hk, erase_known her]
  exact ⟨rfl, rfl⟩

/-- A root returning the pinned `Bool` has rows for both pinned `Bool`
constructors in the plain-RC front half's Cfg table. -/
theorem Front.boolRows {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runFront cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) (hb : BoolResult f.src c) {k : Src.CId}
    (hk : f.src.known.boolFalse = some k ∨ f.src.known.boolTrue = some k) :
    BoolRows f.src f.cfg.base := by
  obtain ⟨-, ⟨st, her⟩, hanf, -, -, -, -⟩ := runFront_spec h
  obtain ⟨rs, hrs, hrk⟩ := anfOf_ctors hanf
  have hct : f.cfg.base.ctors = f.lam.ctors ++ rs := (runFront_ctors h).trans hrs
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

theorem isImmortalViewType_boolSig (C : Cfg.Program) :
    CompileClaim.isImmortalViewType (boolSig C) (.ind 0) = true := by
  have key : ∀ n, CompileClaim.isImmortalViewType { inds := [List.replicate (n + 1) []] } (.ind 0) =
      true := by
    intro n
    simp [CompileClaim.isImmortalViewType, List.replicate_succ]
  unfold boolSig
  dsimp only
  split
  · exact key _
  · exact key 1

/-- The plain-RC view of a natural number or a field-less constructor is the
immortal one. -/
theorem treeView_flat (T : List Lam.CtorInfo) (sig : Rt.Sig) (ty : Rt.FoTy) {o : Obs}
    (ho : (∃ n, o = .nat n) ∨ ∃ cid, o = .ctor cid []) :
    Rt.Rc.Procs.Readback.treeView T sig ty o = Rt.tagify T sig ty o := by
  rcases ho with ⟨n, rfl⟩ | ⟨cid, rfl⟩
  · cases ty <;> simp [Rt.Rc.Procs.Readback.treeView, Rt.tagify]
  · cases ty with
    | nat => simp [Rt.Rc.Procs.Readback.treeView, Rt.tagify]
    | ind i =>
      rw [Rt.Rc.Procs.Readback.treeView]
      simp only [Rt.tagify]
      cases Fir.CtorInfo.ofKey T (.src cid) with
      | none => rfl
      | some c =>
        cases h : sig.ctor? i c.tag with
        | none => simp [h]
        | some tys =>
          cases tys with
          | nil => simp [h, Rt.Rc.Procs.Readback.fieldsView]
          | cons t ts => simp [h, Rt.Rc.Procs.Readback.fieldsView]

/-- **Totality at a plain-RC root, through the view.** At root `r` of the
plain-RC front half, naming constant `c`, with a readback type, the view
accepts every observation of `c`'s `PlainShape`. -/
theorem Front.view_plainShape {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runFront cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {sig : Rt.Sig} {ty : Rt.FoTy}
    (hty : f.tys r = some (sig, ty)) {o : Obs} (hs : PlainShape f.src c o) :
    ∃ w, f.view r (some o) = some (some w) := by
  have hty' : rootTy f.src f.cfg.base c = some (sig, ty) := by
    simpa [Front.tys, hr] using hty
  have hct := runFront_ctors h
  unfold PlainShape at hs
  cases hrt : resultTy f.src c with
  | none =>
    rw [hrt] at hs
    have hd : Readback.discover f.src f.cfg.base c = .ok (sig, ty) := by
      simp only [rootTy, hrt] at hty'
      cases hdisc : Readback.discover f.src f.cfg.base c with
      | error e => rw [hdisc] at hty'; cases hty'
      | ok v => rw [hdisc] at hty'; cases hty'; rfl
    obtain ⟨w, hw⟩ := discover_treeView hd hs
    refine ⟨w, ?_⟩
    rw [hct] at hw
    simp only [Front.view, treeViewOf, hty, Option.bind_some, hw, Option.map_some]
  | some t =>
    rw [hrt] at hs
    -- the `Nat` and pinned-`Bool` routes: field-less, as on the immortal path
    have hview : CompileClaim.isImmortalViewType sig ty = true := by
      cases t with
      | nat =>
        simp only [rootTy, hrt, Option.some.injEq, Prod.mk.injEq] at hty'
        obtain ⟨rfl, rfl⟩ := hty'
        rfl
      | ind i =>
        simp only [rootTy, hrt, Option.some.injEq, Prod.mk.injEq] at hty'
        obtain ⟨rfl, rfl⟩ := hty'
        have : i = 0 := by
          unfold resultTy at hrt
          split at hrt
          · split at hrt
            · split at hrt
              · cases hrt
              · split at hrt
                · cases hrt; rfl
                · cases hrt
            · cases hrt
          · cases hrt
        subst this
        exact isImmortalViewType_boolSig _
    have hb : BoolResult f.src c → BoolRows f.src f.cfg.base := fun hB => by
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
    obtain ⟨w, hw, -⟩ := tagify_resultShape hty' hview (runFront_boolKnown h) hs hb
    have htree : Rt.Rc.Procs.Readback.treeView f.anf.ctors sig ty o =
        Rt.tagify f.anf.ctors sig ty o :=
      treeView_flat _ _ _ (by
        cases hs with
        | nat n _ _ => exact .inl ⟨n, rfl⟩
        | bool _ _ _ _ => exact .inr ⟨_, rfl⟩
        | enum _ _ _ _ _ _ => exact .inr ⟨_, rfl⟩)
    refine ⟨w, ?_⟩
    rw [hct] at hw
    simp only [Front.view, treeViewOf, hty, Option.bind_some, htree, hw, Option.map_some]

/-- **The plain-RC view rejects only results off the root's shape.** At such a
root, the plain-RC `GoesWrong` holds only if SrcEval gets stuck or traps, or
returns a result that is not of `c`'s `PlainShape`. -/
theorem Front.goesWrong_plainShape {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (h : runFront cfg P cert = .ok f) {r : Nat} {addr : Ixon.Address} {c : Src.CId}
    (hr : f.src.roots[r]? = some (addr, c)) {sig : Rt.Sig} {ty : Rt.FoTy}
    (hty : f.tys r = some (sig, ty)) {ns : List Nat} (hgw : f.GoesWrong (r, ns)) :
    (∃ k, (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (r, ns) k).GoesWrong) ∨
      ∃ k v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (r, ns) k = .ok v ∧
        ¬ PlainShapeOpt f.src c (Lang.obs v) := by
  obtain ⟨k, hk | ⟨v, hv, hnone⟩⟩ := hgw
  · exact .inl ⟨k, hk⟩
  · refine .inr ⟨k, v, hv, ?_⟩
    rintro ⟨o, ho, hs⟩
    obtain ⟨w, hw⟩ := Front.view_plainShape h hr hty hs
    rw [ho, hw] at hnone
    cases hnone

/-- **At root 0 of plain-RC artifact `a` with root record `root`, the source
goes wrong only off the root's shape**: SrcEval gets stuck or traps, or
returns a result that is not of `root.const`'s `PlainShape`. -/
def RootWrongOffPlainShape (a : Artifact) (root : Root) : Prop :=
  ∀ ns : List Nat, a.front.GoesWrong (0, ns) →
    (∃ k, (Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram) (0, ns) k).GoesWrong) ∨
      ∃ k v, Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram) (0, ns) k = .ok v ∧
        ¬ PlainShapeOpt a.front.src root.const (Lang.obs v)

/-- **A plain-RC claim's inputs are covered** (`Recheck.covered_rootsOf_head`). -/
theorem Artifact.covered_head {cfg : Config} {P : Src.Program} {cert : Cert}
    {a : Artifact} (hrun : run cfg P cert = .ok a) {root : Root}
    (hhead : a.roots.head? = some root) (hnat : CompileClaim.rootParamsAllNat a.front.src root = true)
    {ns : List Nat} (hlen : ns.length = root.params) : a.front.Covered cert (0, ns) := by
  rw [run_roots hrun] at hhead
  exact Recheck.covered_rootsOf_head hhead hnat hlen

/-- **The view's rejections at a plain-RC root.** For an artifact of
`RcReplay.run` whose first root passes `checkPlainRcRoot`, the source goes
wrong at that root only off the root's shape. -/
theorem Artifact.goesWrong_plainRoot {cfg : Config} {P : Src.Program} {cert : Cert}
    {a : Artifact} (hrun : run cfg P cert = .ok a) {root : Root}
    (hhead : a.roots.head? = some root)
    (hok : CompileClaim.checkPlainRcRoot a.front.src root = true) :
    RootWrongOffPlainShape a root := by
  intro ns hgw
  have hf := (run_parts hrun).1
  have hroots := run_roots hrun
  rw [hroots, List.head?_eq_getElem?] at hhead
  obtain ⟨j, addr, fx, fn, sym, hrow, hrty⟩ := rootsOf_get_const hhead
  simp only [List.getElem?_zip_eq_some] at hrow
  obtain ⟨-, hsrc0, -⟩ := hrow
  simp only [CompileClaim.checkPlainRcRoot, Bool.and_eq_true] at hok
  obtain ⟨-, hok⟩ := hok
  cases hty : root.ty with
  | none => rw [hty] at hok; cases hok
  | some st =>
    obtain ⟨sig, ty⟩ := st
    have htys : a.front.tys 0 = some (sig, ty) := by
      simp only [Front.tys, hsrc0, Option.bind_some]
      rw [← hrty, hty]
    exact Front.goesWrong_plainShape hf hsrc0 htys hgw

end RcReplay

end IxCC.Recheck
