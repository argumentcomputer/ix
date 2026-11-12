import IxVMRefinement.L1.Loop

/-! # BLAKE3's tree of chaining values at source level

`Blake3::next_layer` pairs the chaining values of a layer stack, bottom first, and
`Blake3::compress_layer` repeats it until one value is left. On a stack `st` (top first, as
`Stack` holds it) the steps are modeled by `nlM`; `compress_layer_spec` proves that the
circuit computes `Aiur.Library.Blake3.compressLayer` of the layer in order (`st.reverse`):
* `nlM false` is `Aiur.Library.Blake3.nextLayer` with the odd last value left pending
  (`nlM_false_spec`, from `nextLayer_append` on an even prefix);
* the `ROOT` flag only reaches a pair when the layer has exactly two values
  (`nlM_root`), which is `compressLayer`'s two-value case.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

namespace IxVM.Refinement.L1

open IxVM (F)
open IxVM.Refinement.Obs
open Blake3.Pure (CV)
open Aiur.Library.Blake3 (nextLayer compressLayer)

/-! ## The model of a layer step -/

/-- The flags of a parent node: `PARENT`, with `ROOT` for the root. -/
def parentFlags (root : Bool) : UInt32 := if root then 12 else 4

/-- A parent node's chaining value: `compress(IV, left ++ right, 0, 64, flags)`. -/
def parentCV (root : Bool) (l r : CV) : CV :=
  Blake3.Pure.compress Blake3.Pure.iv (l ++ r) 0 64 (parentFlags root)

/-- **`Blake3::next_layer(layer, digest, root)`** on the stack `st` (top first) with `d` above
it: the value left unpaired, if the count is odd, and the new layer (top first). -/
def nlM (root : Bool) : List CV → CV → Option CV × List CV
  | [], d => (some d, [])
  | other :: rest, d =>
    match nlM false rest other with
    | (none, nl) => (some d, nl)
    | (some last, nl) => (none, parentCV (root && nl.isEmpty) last d :: nl)

/-- The layer `compress_layer` continues with: the new layer, with the pending value on top. -/
def resM : Option CV × List CV → List CV
  | (none, nl) => nl
  | (some x, nl) => x :: nl

theorem nlM_none_eq {root : Bool} {other d : CV} {rest nl : List CV}
    (hr : nlM false rest other = (none, nl)) : nlM root (other :: rest) d = (some d, nl) := by
  simp only [nlM, hr]

theorem nlM_some_eq {root : Bool} {other d last : CV} {rest nl : List CV}
    (hr : nlM false rest other = (some last, nl)) :
    nlM root (other :: rest) d = (none, parentCV (root && nl.isEmpty) last d :: nl) := by
  simp only [nlM, hr]

/-- The value is pending exactly when the stack below `d` has odd length, and the new layer
holds half of the values. -/
theorem nlM_shape : ∀ (st : List CV) (d : CV) (root : Bool),
    ((nlM root st d).1 = none ↔ st.length % 2 = 1) ∧
      (nlM root st d).2.length = (st.length + 1) / 2
  | [], d, root => by simp [nlM]
  | other :: rest, d, root => by
    have ih := nlM_shape rest other false
    rcases hr : nlM false rest other with ⟨_ | last, nl⟩
    · rw [hr] at ih
      rw [nlM_none_eq hr]
      simp only [List.length_cons] at ih ⊢
      simp at ih ⊢
      omega
    · rw [hr] at ih
      rw [nlM_some_eq hr]
      simp only [List.length_cons] at ih ⊢
      simp at ih ⊢
      omega

theorem nextLayer_append : ∀ (Z W : List CV), Z.length % 2 = 0 →
    nextLayer (Z ++ W) = nextLayer Z ++ nextLayer W
  | [], W, _ => by simp [nextLayer]
  | [a], W, hz => by simp at hz
  | a :: b :: Z, W, hz => by
    have ih := nextLayer_append Z W (by simp at hz; omega)
    simp only [List.cons_append, nextLayer, ih]

theorem nextLayer_single (x : CV) : nextLayer [x] = [x] := by simp [nextLayer]

theorem nextLayer_pair (l r : CV) : nextLayer [l, r] = [parentCV false l r] := by
  rw [Aiur.Library.Blake3.next_layer_pair_spec]
  rfl

/-- **Without `ROOT`, a layer step is `nextLayer`** of the values in order. -/
theorem nlM_false_spec : ∀ (st : List CV) (d : CV),
    (resM (nlM false st d)).reverse = nextLayer (st.reverse ++ [d])
  | [], d => by simp [nlM, resM, nextLayer]
  | other :: rest, d => by
    have ih := nlM_false_spec rest other
    have sh := (nlM_shape rest other false).1
    rcases hr : nlM false rest other with ⟨_ | last, nl⟩
    · rw [hr] at ih sh
      have hodd : rest.length % 2 = 1 := sh.mp rfl
      rw [nlM_none_eq hr]
      have ih' : nl.reverse = nextLayer (rest.reverse ++ [other]) := by simpa [resM] using ih
      show (d :: nl).reverse = _
      simp only [List.reverse_cons]
      rw [ih', nextLayer_append (rest.reverse ++ [other]) [d] (by simp; omega), nextLayer_single]
    · rw [hr] at ih sh
      have heven : rest.length % 2 = 0 := by simp at sh; omega
      rw [nlM_some_eq hr, Bool.false_and]
      show (parentCV false last d :: nl).reverse = _
      have h2 : nextLayer (rest.reverse ++ [other]) = nextLayer rest.reverse ++ [other] := by
        rw [nextLayer_append _ _ (by simp; omega), nextLayer_single]
      have ih' : nl.reverse ++ [last] = nextLayer rest.reverse ++ [other] := by
        rw [← h2, ← ih]
        simp [resM]
      obtain ⟨e1, e2⟩ := List.append_inj' ih' rfl
      obtain rfl : last = other := by simpa using e2
      simp only [List.reverse_cons]
      rw [e1, List.append_assoc, List.singleton_append,
        nextLayer_append _ [last, d] (by simp; omega), nextLayer_pair]

/-- **`ROOT` is never used on three values or more**: the top pair then has values below it. -/
theorem nlM_root (other : CV) (rest : List CV) (d : CV) (hne : rest ≠ []) :
    nlM true (other :: rest) d = nlM false (other :: rest) d := by
  have sh := (nlM_shape rest other false).2
  rcases hr : nlM false rest other with ⟨_ | last, nl⟩
  · rw [nlM_none_eq hr, nlM_none_eq hr]
  · have hnl : nl ≠ [] := by
      rw [hr] at sh
      intro e
      subst e
      have := List.length_pos_iff.mpr hne
      simp at sh
      omega
    have he : nl.isEmpty = false := List.isEmpty_eq_false_iff.mpr hnl
    simp only [nlM_some_eq hr, he, Bool.and_false]

/-- **A step of `compress_layer` keeps `compressLayer`**: two values give the root parent,
three or more give `nextLayer`, which `compressLayer` recurses on. -/
theorem compressLayer_step (d : CV) (rest : List CV) (hne : rest ≠ []) :
    compressLayer (resM (nlM true rest d)).reverse = compressLayer (d :: rest).reverse := by
  match rest, hne with
  | [], hne => exact absurd rfl hne
  | [l], _ =>
    have e : nlM true [l] d = (none, [parentCV true l d]) := by simp [nlM]
    rw [e]
    show compressLayer [parentCV true l d].reverse = compressLayer [d, l].reverse
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    simp only [compressLayer]
    rfl
  | l :: m :: tl, _ =>
    rw [nlM_root l (m :: tl) d (by simp), nlM_false_spec,
      show (d :: l :: m :: tl).reverse = (l :: m :: tl).reverse ++ [d] from List.reverse_cons]
    have hlen : 3 ≤ ((l :: m :: tl).reverse ++ [d]).length := by simp
    generalize ((l :: m :: tl).reverse ++ [d]) = X at hlen ⊢
    rcases X with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · simp at hlen
    · exact (Aiur.Library.Blake3.compress_layer_step_spec a b c t).symm

/-! ## Values -/

/-- `MaybeDigest`. -/
def maybeV : Option CV → SourceValue F
  | none => .construct "Blake3::MaybeDigest" "None" []
  | some d => .construct "Blake3::MaybeDigest" "Some" [vecV d]

/-- The `root` argument of `next_layer`. -/
def rootF : Bool → F
  | true => 1
  | false => 0

theorem maybeV_none {p : Option CV}
    (h : maybeV p = (.construct "Blake3::MaybeDigest" "None" [] : SourceValue F)) : p = none := by
  cases p with
  | none => rfl
  | some d => simp [maybeV] at h

theorem maybeV_some {p : Option CV} {x : SourceValue F}
    (h : maybeV p = .construct "Blake3::MaybeDigest" "Some" [x]) : ∃ d, p = some d ∧ x = vecV d := by
  cases p with
  | none => simp [maybeV] at h
  | some d =>
    simp only [maybeV, Value.construct.injEq, List.cons.injEq, and_true, true_and] at h
    exact ⟨d, rfl, h.symm⟩

theorem parentFlags_field (root : Bool) :
    (((parentFlags root).toNat : Nat) : F) = 4 + 8 * rootF root := by
  cases root
  · show (((4 : UInt32).toNat : Nat) : F) = 4 + 8 * 0
    norm_num
  · show (((12 : UInt32).toNat : Nat) : F) = 4 + 8 * 1
    norm_num

theorem parentFlags_lt (root : Bool) : (parentFlags root).toNat < 256 := by
  cases root <;> decide

theorem vecV_eight (a : Vector UInt32 8) :
    (vecV a : SourceValue F) =
      .tuple [wv a[0], wv a[1], wv a[2], wv a[3], wv a[4], wv a[5], wv a[6], wv a[7]] := rfl

theorem vecV_append8 (a b : Vector UInt32 8) :
    (vecV (a ++ b) : SourceValue F) =
      .tuple [wv a[0], wv a[1], wv a[2], wv a[3], wv a[4], wv a[5], wv a[6], wv a[7],
        wv b[0], wv b[1], wv b[2], wv b[3], wv b[4], wv b[5], wv b[6], wv b[7]] := by
  rw [show (vecV (a ++ b) : SourceValue F) =
      .tuple [wv (a ++ b)[0], wv (a ++ b)[1], wv (a ++ b)[2], wv (a ++ b)[3], wv (a ++ b)[4],
        wv (a ++ b)[5], wv (a ++ b)[6], wv (a ++ b)[7], wv (a ++ b)[8], wv (a ++ b)[9],
        wv (a ++ b)[10], wv (a ++ b)[11], wv (a ++ b)[12], wv (a ++ b)[13], wv (a ++ b)[14],
        wv (a ++ b)[15]] from rfl]
  simp

/-! ## Stacks -/

theorem stack_push_inv {h : Heap F} {st : List CV} {p a b : SourceValue F} (hs : Stack h st p)
    (ld : loadValue h p = .ok (.construct "Blake3::LayerNode" "Push" [a, b])) :
    ∃ d rest, st = d :: rest ∧ b = vecV d ∧ Stack h rest a := by
  rcases stack_inv hs ld with ⟨-, hv⟩ | ⟨d, rest, q, rfl, hv, hq⟩
  · simp at hv
  · obtain ⟨-, -, hargs⟩ := Value.construct.inj hv
    obtain ⟨rfl, hargs2⟩ := List.cons.inj hargs
    obtain ⟨rfl, -⟩ := List.cons.inj hargs2
    exact ⟨d, rest, rfl, rfl, hq⟩

theorem stack_nil_inv {h : Heap F} {st : List CV} {p : SourceValue F} (hs : Stack h st p)
    (ld : loadValue h p = .ok (.construct "Blake3::LayerNode" "Nil" [])) : st = [] := by
  rcases stack_inv hs ld with ⟨rfl, -⟩ | ⟨d, rest, q, -, hv, -⟩
  · rfl
  · simp at hv

theorem stack_ne_nil {h : Heap F} {st : List CV} {p v : SourceValue F} (hs : Stack h st p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 0 →
      v ≠ .construct "Blake3::LayerNode" "Nil" vs) : st ≠ [] := by
  rcases stack_inv hs ld with ⟨-, hv⟩ | ⟨d, rest, q, rfl, -, -⟩
  · exact absurd hv (hne [] rfl)
  · simp

/-! ## `Blake3::next_layer` -/

/-- **`Blake3::next_layer`** computes `nlM`: the pending value (as a `MaybeDigest`) and a
pointer to the new layer. -/
theorem next_layer_spec : ∀ (st : List CV) {d : CV} {root : Bool} {p r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)},
    Stack h st p →
    ObsFn W "Blake3::next_layer" [p, vecV d, .field (rootF root)] h r h' cs →
    Heap.Extends h h' ∧ ∃ q, r = .tuple [maybeV (nlM root st d).1, q] ∧
      Stack h' (nlM root st d).2 q
  | [], d, root, p, r, h, h', cs, hs, ev => by
    rcases «Blake3::next_layer».obs ev with
      ⟨ld12, he24, he49, -⟩ |
      ⟨x_layer_58, x_other, m70, cs80, x_new_layer, ld12, -⟩ |
      ⟨x_layer_58, x_other, m70, cs80, x_new_layer, v195, m196, cs206, x_x0, x_x1, x_x2, x_x3,
        x_x4, x_x5, x_x6, x_x7, x_x8, x_x9, x_x10, x_x11, x_x12, x_x13, x_x14, x_x15, v470, y479,
        v497, m498, cs508, m566, ld12, -⟩ |
      ⟨x_layer_58, x_other, m70, cs80, x_new_layer, v195, m196, cs206, x_x0, x_x1, x_x2, x_x3,
        x_x4, x_x5, x_x6, x_x7, x_x8, x_x9, x_x10, x_x11, x_x12, x_x13, x_x14, x_x15, v451, v609,
        m610, cs620, m678, ld12, -⟩
    · subst he24 he49
      exact ⟨Heap.Extends.refl _, p, rfl, hs⟩
    all_goals
      obtain ⟨d', rest', he, -, -⟩ := stack_push_inv hs ld12
      cases he
  | other :: rest, d, root, p, r, h, h', cs, hs, ev => by
    rcases «Blake3::next_layer».obs ev with
      ⟨ld12, he24, he49, -⟩ |
      ⟨x_layer_58, x_other, m70, cs80, x_new_layer, ld12, ev82, he139, he164, -⟩ |
      ⟨x_layer_58, x_other, m70, cs80, x_new_layer, v195, m196, cs206, x_x0, x_x1, x_x2, x_x3,
        x_x4, x_x5, x_x6, x_x7, x_x8, x_x9, x_x10, x_x11, x_x12, x_x13, x_x14, x_x15, v470, y479,
        v497, m498, cs508, m566, ld12, ev82, ev208, hv271, ld462, op494, op485, ev510, he555,
        hm574, he594, -⟩ |
      ⟨x_layer_58, x_other, m70, cs80, x_new_layer, v195, m196, cs206, x_x0, x_x1, x_x2, x_x3,
        x_x4, x_x5, x_x6, x_x7, x_x8, x_x9, x_x10, x_x11, x_x12, x_x13, x_x14, x_x15, v451, v609,
        m610, cs620, m678, ld12, ev82, ev208, hv271, ld462, hne596, ev622, he667, hm686, he706, -⟩
    · exact absurd (stack_nil_inv hs ld12) (by simp)
    · -- the layer below pairs evenly: `d` is pending
      obtain ⟨d', rest', he, rfl, hq⟩ := stack_push_inv hs ld12
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      obtain ⟨ext1, q', hq', hst'⟩ :=
        next_layer_spec rest (d := other) (root := false) hq (by exact ev82)
      rcases hr : nlM false rest other with ⟨pend, nl⟩
      rw [hr] at hq' hst'
      dsimp only at hq' hst'
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hq'
      obtain ⟨hm, rfl⟩ := hq'
      obtain rfl := maybeV_none hm.symm
      subst he139 he164
      rw [nlM_none_eq hr]
      exact ⟨ext1, _, rfl, hst'⟩
    · -- a value is left below: pair it with `d`; the new layer was empty
      obtain ⟨d', rest', he, rfl, hq⟩ := stack_push_inv hs ld12
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      obtain ⟨ext1, q', hq', hst'⟩ :=
        next_layer_spec rest (d := other) (root := false) hq (by exact ev82)
      rcases hr : nlM false rest other with ⟨pend, nl⟩
      rw [hr] at hq' hst'
      dsimp only at hq' hst'
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hq'
      obtain ⟨hm, rfl⟩ := hq'
      obtain ⟨last, rfl, hlast⟩ := maybeV_some hm.symm
      obtain ⟨rfl, hm196⟩ := iv_src ev208
      subst m196
      obtain rfl := stack_nil_inv hst' ld462
      rw [vecV_eight] at hlast hv271
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hlast hv271
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hlast
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv271
      obtain rfl := binop_mul op494
      obtain rfl := binop_add op485
      rw [← vecV_append8, ← u64v_zero, ← parentFlags_field root,
        show (64 : F) = ((64 : Nat) : F) by simp] at ev510
      obtain ⟨rfl, hm498⟩ :=
        compress_init_spec' (len := 64) (by norm_num) (parentFlags_lt root) ev510
      subst m498
      subst he555 hm574 he594
      rw [nlM_some_eq hr, List.isEmpty_nil, Bool.and_true]
      exact ⟨ext1.trans (Heap.Extends.snoc _ _), _, rfl, stack_push_snoc hst'⟩
    · -- a value is left below: pair it with `d`, below other parents
      obtain ⟨d', rest', he, rfl, hq⟩ := stack_push_inv hs ld12
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      obtain ⟨ext1, q', hq', hst'⟩ :=
        next_layer_spec rest (d := other) (root := false) hq (by exact ev82)
      rcases hr : nlM false rest other with ⟨pend, nl⟩
      rw [hr] at hq' hst'
      dsimp only at hq' hst'
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hq'
      obtain ⟨hm, rfl⟩ := hq'
      obtain ⟨last, rfl, hlast⟩ := maybeV_some hm.symm
      obtain ⟨rfl, hm196⟩ := iv_src ev208
      subst m196
      have hnl : nl ≠ [] := stack_ne_nil hst' ld462 hne596
      rw [vecV_eight] at hlast hv271
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hlast hv271
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hlast
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv271
      have h4 : (4 : F) = (((parentFlags false).toNat : Nat) : F) := by
        rw [parentFlags_field]
        simp [rootF]
      rw [← vecV_append8, ← u64v_zero, h4, show (64 : F) = ((64 : Nat) : F) by simp] at ev622
      obtain ⟨rfl, hm610⟩ :=
        compress_init_spec' (len := 64) (by norm_num) (parentFlags_lt false) ev622
      subst m610
      subst he667 hm686 he706
      rw [nlM_some_eq hr, List.isEmpty_eq_false_iff.mpr hnl, Bool.and_false]
      exact ⟨ext1.trans (Heap.Extends.snoc _ _), _, rfl, stack_push_snoc hst'⟩

/-! ## `Blake3::compress_layer` -/

/-- The specification of `compress_layer` on a stack (top first). -/
def CLSpec (st : List CV) : Prop :=
  ∀ {p r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    Stack h st p → ObsFn W "Blake3::compress_layer" [p] h r h' cs →
    Heap.Extends h h' ∧ r = vecV (compressLayer st.reverse)

theorem resM_none {p : Option CV × List CV} (h : p.1 = none) : resM p = p.2 := by
  rcases p with ⟨_ | x, nl⟩
  · rfl
  · simp at h

theorem resM_some {p : Option CV × List CV} {x : CV} (h : p.1 = some x) : resM p = x :: p.2 := by
  rcases p with ⟨_ | y, nl⟩
  · simp at h
  · simp at h
    subst h
    rfl

/-- One row of `compress_layer`, given the specification on shorter stacks. -/
theorem cl_core (st : List CV) (ih : ∀ st' : List CV, st'.length < st.length → CLSpec st') :
    CLSpec st := by
  intro p r h h' cs hs ev
  rcases «Blake3::compress_layer».obs ev with
    ⟨x_rest, x_digest, ld11, ld37, he46, he47, -⟩ |
    ⟨x_rest, x_digest, v26, m54, cs64, x_new_merkle, cs122, ld11, ld37, hne49, ev66, ev124, -⟩ |
    ⟨x_rest, x_digest, v26, m54, cs64, x_new_merkle, x_last_141, cs150, m155, ld11, ld37, hne49,
      ev66, hm163, ev152, -⟩
  · -- one value: it is the root
    obtain ⟨d, rest, rfl, rfl, hrest⟩ := stack_push_inv hs ld11
    obtain rfl := stack_nil_inv hrest ld37
    subst he46 he47
    refine ⟨Heap.Extends.refl _, ?_⟩
    rw [List.reverse_singleton, Aiur.Library.Blake3.compress_layer_singleton]
  · -- the step leaves nothing pending
    obtain ⟨d, rest, rfl, rfl, hrest⟩ := stack_push_inv hs ld11
    have hne := stack_ne_nil hrest ld37 hne49
    obtain ⟨ext1, q', hq', hst'⟩ := next_layer_spec rest (d := d) (root := true) hrest
      (by exact ev66)
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hq'
    obtain ⟨hm, rfl⟩ := hq'
    have hnone := maybeV_none hm.symm
    have hlen := (nlM_shape rest d true).2
    have hpos := List.length_pos_iff.mpr hne
    have IH := @ih (nlM true rest d).2 (by simp only [List.length_cons]; omega)
    unfold CLSpec at IH
    obtain ⟨ext2, rfl⟩ := IH hst' ev124
    refine ⟨ext1.trans ext2, ?_⟩
    rw [← compressLayer_step d rest hne, resM_none hnone]
  · -- the step leaves a value pending: push it back on top
    obtain ⟨d, rest, rfl, rfl, hrest⟩ := stack_push_inv hs ld11
    have hne := stack_ne_nil hrest ld37 hne49
    obtain ⟨ext1, q', hq', hst'⟩ := next_layer_spec rest (d := d) (root := true) hrest
      (by exact ev66)
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hq'
    obtain ⟨hm, rfl⟩ := hq'
    obtain ⟨last, hsome, rfl⟩ := maybeV_some hm.symm
    have hlen := (nlM_shape rest d true).2
    have hpar := (nlM_shape rest d true).1
    rw [hsome] at hpar
    have heven : rest.length % 2 = 0 := by simp at hpar; omega
    have hpos := List.length_pos_iff.mpr hne
    subst hm163
    have IH := @ih (last :: (nlM true rest d).2) (by simp only [List.length_cons]; omega)
    unfold CLSpec at IH
    obtain ⟨ext2, rfl⟩ := IH (stack_push_snoc hst') ev152
    refine ⟨ext1.trans ((Heap.Extends.snoc _ _).trans ext2), ?_⟩
    rw [← compressLayer_step d rest hne, resM_some hsome]

theorem compress_layer_le (N : Nat) : ∀ st : List CV, st.length ≤ N → CLSpec st := by
  induction N with
  | zero =>
    intro st hst
    exact cl_core st (fun st' hlt => absurd hlt (by omega))
  | succ N ih =>
    intro st hst
    exact cl_core st (fun st' hlt => ih st' (by omega))

/-- **`Blake3::compress_layer`** computes `Aiur.Library.Blake3.compressLayer` of the layer in
order (the stack reversed). -/
theorem compress_layer_spec (st : List CV) {p r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hs : Stack h st p)
    (ev : ObsFn W "Blake3::compress_layer" [p] h r h' cs) :
    Heap.Extends h h' ∧ r = vecV (compressLayer st.reverse) :=
  compress_layer_le st.length st (Nat.le_refl _) hs ev

end IxVM.Refinement.L1
