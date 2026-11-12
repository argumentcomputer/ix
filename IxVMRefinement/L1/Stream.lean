import IxVMRefinement.L1.Compress
import Ix.IxVM.Refinement.Statement
import Mathlib.Data.List.Forall2

/-! # Byte streams and layer stacks in the heap, and BLAKE3's block reads

* `Stream h bytes p`: the byte stream `p` (`Bytes::Stream`) holds `bytes` in the heap `h`, in
  the form `Hashed` reads (`RepByteStream` over `byteStreamEnum`).
* `Stack h st p`: the layer stack `p` (`Blake3::Layer`) holds the chaining values `st`, its top
  first.
* `Blake3::take_block` and `Blake3::bytes_to_block` (no generated path lemmas: a 64-deep
  match, 64 nested `let`s) are inverted one byte at a time against their elaborated bodies
  (`take_block_body`, `bytes_to_block_body`), and read the block's words
  (`blockWords`); `Blake3::pad_block` prepends zero bytes.
-/

set_option maxHeartbeats 4000000
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
open IxVM.Refinement (byteStreamEnum)
open Aiur.Library.Blake3 (wordOfBytes wordOfBytes_toNat)

/-! ## Heap cells -/

@[simp] theorem type_construct (name ctor : String) (args : List (SourceValue F)) :
    (Value.construct name ctor args : SourceValue F).type = .enum name := by
  rw [Value.type]

theorem load_cell {h : Heap F} {addr : Nat} {name ctor : String} {args : List (SourceValue F)}
    (cell : h[addr]? = some (.construct name ctor args)) :
    loadValue h (.ptr (.enum name) addr) = .ok (.construct name ctor args) := by
  simp [loadValue, cell, type_construct, bind, Except.bind, pure, Except.pure]

theorem loadValue_snoc (h : Heap F) (v : SourceValue F) :
    loadValue (h ++ [v]) (.ptr v.type h.length) = .ok v := by
  simp [loadValue, List.getElem?_concat_length, bind, Except.bind, pure, Except.pure]

theorem cell_extend {h h' : Heap F} (ext : Heap.Extends h h') {a : Nat} {v : SourceValue F}
    (cell : h[a]? = some v) : h'[a]? = some v := by
  obtain ⟨s, rfl⟩ := ext
  have ha : a < h.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at cell
    cases cell
  rw [List.getElem?_append_left ha, cell]

theorem loadValue_extend {h h' : Heap F} (ext : Heap.Extends h h') {p v : SourceValue F}
    (hl : loadValue h p = .ok v) : loadValue h' p = .ok v := by
  cases p with
  | ptr t a =>
    cases hc : h[a]? with
    | none =>
      simp only [loadValue, hc] at hl
      cases hl
    | some w =>
      have hw' := cell_extend ext hc
      simp only [loadValue, hc] at hl
      simp only [loadValue, hw']
      exact hl
  | _ => simp [loadValue] at hl

/-! ## Byte streams -/

/-- **A byte stream** (`Bytes::Stream = &Lists::Node<UInt8::U8>`) holding `bytes` in `h`, as
`Hashed` reads one. -/
abbrev Stream (h : Heap F) (bytes : List UInt8) (ptr : SourceValue F) : Prop :=
  Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes ptr

theorem Stream.mono {h h' : Heap F} (ext : Heap.Extends h h') {bytes : List UInt8}
    {ptr : SourceValue F} (hs : Stream h bytes ptr) : Stream h' bytes ptr :=
  Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext hs

theorem stream_inv {h : Heap F} {bytes : List UInt8} {ptr v : SourceValue F}
    (hs : Stream h bytes ptr) (hl : loadValue h ptr = .ok v) :
    (bytes = [] ∧ v = .construct byteStreamEnum "Nil" []) ∨
    (∃ x xs tail, bytes = x :: xs ∧ v = .construct byteStreamEnum "Cons" [bv x, tail] ∧
      Stream h xs tail) := by
  cases hs with
  | nil cell =>
    rw [load_cell cell] at hl
    cases hl
    exact .inl ⟨rfl, rfl⟩
  | cons cell headRep tailRep =>
    rw [load_cell cell] at hl
    cases hl
    refine .inr ⟨_, _, _, rfl, ?_, tailRep⟩
    rw [headRep]

theorem stream_nil_snoc (h : Heap F) :
    Stream (h ++ [.construct byteStreamEnum "Nil" []]) [] (.ptr (.enum byteStreamEnum) h.length) :=
  .nil (by simp [List.getElem?_concat_length])

theorem stream_cons_snoc {h : Heap F} {x : UInt8} {xs : List UInt8} {tail : SourceValue F}
    (hs : Stream h xs tail) :
    Stream (h ++ [.construct byteStreamEnum "Cons" [bv x, tail]]) (x :: xs)
      (.ptr (.enum byteStreamEnum) h.length) :=
  .cons (by simp [List.getElem?_concat_length]) rfl (hs.mono (Heap.Extends.snoc h _))

/-! ## Layer stacks -/

/-- **The layer stack** (`Blake3::Layer = &LayerNode`) holding the chaining values `st`, its
top first: `LayerNode::Push(rest, cv)` holds `cv :: rest`. -/
inductive Stack (h : Heap F) : List Blake3.Pure.CV → SourceValue F → Prop where
  | nil {addr : Nat} (cell : h[addr]? = some (.construct "Blake3::LayerNode" "Nil" [])) :
      Stack h [] (.ptr (.enum "Blake3::LayerNode") addr)
  | push {addr : Nat} {cv : Blake3.Pure.CV} {st : List Blake3.Pure.CV} {p : SourceValue F}
      (cell : h[addr]? = some (.construct "Blake3::LayerNode" "Push" [p, vecV cv]))
      (rest : Stack h st p) : Stack h (cv :: st) (.ptr (.enum "Blake3::LayerNode") addr)

theorem Stack.mono {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ {st : List Blake3.Pure.CV} {p : SourceValue F}, Stack h st p → Stack h' st p
  | _, _, .nil cell => .nil (cell_extend ext cell)
  | _, _, .push cell rest => .push (cell_extend ext cell) (rest.mono ext)

theorem stack_inv {h : Heap F} {st : List Blake3.Pure.CV} {p v : SourceValue F}
    (hs : Stack h st p) (hl : loadValue h p = .ok v) :
    (st = [] ∧ v = .construct "Blake3::LayerNode" "Nil" []) ∨
    (∃ cv st' q, st = cv :: st' ∧ v = .construct "Blake3::LayerNode" "Push" [q, vecV cv] ∧
      Stack h st' q) := by
  cases hs with
  | nil cell =>
    rw [load_cell cell] at hl
    cases hl
    exact .inl ⟨rfl, rfl⟩
  | push cell rest =>
    rw [load_cell cell] at hl
    cases hl
    exact .inr ⟨_, _, _, rfl, rfl, rest⟩

theorem stack_nil_snoc (h : Heap F) :
    Stack (h ++ [.construct "Blake3::LayerNode" "Nil" []]) [] (.ptr (.enum "Blake3::LayerNode") h.length) :=
  .nil (by simp [List.getElem?_concat_length])

theorem stack_push_snoc {h : Heap F} {cv : Blake3.Pure.CV} {st : List Blake3.Pure.CV}
    {p : SourceValue F} (hs : Stack h st p) :
    Stack (h ++ [.construct "Blake3::LayerNode" "Push" [p, vecV cv]]) (cv :: st)
      (.ptr (.enum "Blake3::LayerNode") h.length) :=
  .push (by simp [List.getElem?_concat_length]) (hs.mono (Heap.Extends.snoc h _))

/-! ## Matching list cells -/

theorem node_ctor : constructorName [] (.named "Lists::Node" [.field]) = byteStreamEnum := by
  decide +kernel

theorem match_nil_nil (h : Heap F) :
    W.matchPattern [] h (.construct (.named "Lists::Node" [.field]) "Nil" [])
      (.construct byteStreamEnum "Nil" []) = .ok (some []) := by
  rw [matchPattern_construct, node_ctor]
  simp [matchListWith]

theorem match_nil_cons (h : Heap F) (u w : SourceValue F) :
    W.matchPattern [] h (.construct (.named "Lists::Node" [.field]) "Nil" [])
      (.construct byteStreamEnum "Cons" [u, w]) = .ok none := by
  rw [matchPattern_construct, node_ctor]
  simp

theorem match_cons_cons (h : Heap F) (b l : String) (u w : SourceValue F) :
    W.matchPattern [] h (.construct (.named "Lists::Node" [.field]) "Cons" [.bind b, .bind l])
      (.construct byteStreamEnum "Cons" [u, w]) = .ok (some [(b, u), (l, w)]) := by
  rw [matchPattern_construct, node_ctor]
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure]

theorem match_cons_nil (h : Heap F) (b l : String) :
    W.matchPattern [] h (.construct (.named "Lists::Node" [.field]) "Cons" [.bind b, .bind l])
      (.construct byteStreamEnum "Nil" []) = .ok none := by
  rw [matchPattern_construct, node_ctor]
  simp

theorem match_consw_cons (h : Heap F) (b : String) (u w : SourceValue F) :
    W.matchPattern [] h (.construct (.named "Lists::Node" [.field]) "Cons" [.bind b, .wildcard])
      (.construct byteStreamEnum "Cons" [u, w]) = .ok (some [(b, u)]) := by
  rw [matchPattern_construct, node_ctor]
  simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure,
    Except.pure]

theorem match_consw_nil (h : Heap F) (b : String) :
    W.matchPattern [] h (.construct (.named "Lists::Node" [.field]) "Cons" [.bind b, .wildcard])
      (.construct byteStreamEnum "Nil" []) = .ok none := by
  rw [matchPattern_construct, node_ctor]
  simp

/-! ## The byte names -/

/-- The byte names of `take_block` and `bytes_to_block`, `b0` … `b63`. -/
def bNames : List String :=
  ["b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7", "b8", "b9", "b10", "b11", "b12", "b13",
    "b14", "b15", "b16", "b17", "b18", "b19", "b20", "b21", "b22", "b23", "b24", "b25", "b26",
    "b27", "b28", "b29", "b30", "b31", "b32", "b33", "b34", "b35", "b36", "b37", "b38", "b39",
    "b40", "b41", "b42", "b43", "b44", "b45", "b46", "b47", "b48", "b49", "b50", "b51", "b52",
    "b53", "b54", "b55", "b56", "b57", "b58", "b59", "b60", "b61", "b62", "b63"]

/-- `bNames` from the last: the order `bytes_to_block` reads them in. -/
def bNamesRev : List String :=
  ["b63", "b62", "b61", "b60", "b59", "b58", "b57", "b56", "b55", "b54", "b53", "b52", "b51",
    "b50", "b49", "b48", "b47", "b46", "b45", "b44", "b43", "b42", "b41", "b40", "b39", "b38",
    "b37", "b36", "b35", "b34", "b33", "b32", "b31", "b30", "b29", "b28", "b27", "b26", "b25",
    "b24", "b23", "b22", "b21", "b20", "b19", "b18", "b17", "b16", "b15", "b14", "b13", "b12",
    "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"]

theorem bNames_length : bNames.length = 64 := rfl

theorem bNames_nodup : bNames.Nodup := by
  first | decide | (simp [bNames]; done) | decide +kernel

theorem l_notMem : "l" ∉ bNames := by
  first | decide | (simp [bNames]; done) | decide +kernel

theorem bNamesRev_eq : bNamesRev = bNames.reverse := by
  first | rfl | decide | (simp [bNames, bNamesRev]; done)

/-- The lookups of the byte names bound so far. -/
abbrev Bound (locals : Environment F Nat) (names : List String) (xs : List UInt8) : Prop :=
  List.Forall₂ (fun n x => locals.find? (·.1 == n) = some (n, bv x)) names xs

theorem bound_skip {locals : Environment F Nat} {names : List String} {xs : List UInt8}
    (pre : Environment F Nat) (hpre : ∀ n ∈ names, ∀ e ∈ pre, e.1 ≠ n)
    (hb : Bound locals names xs) : Bound (pre ++ locals) names xs := by
  induction hb with
  | nil => exact .nil
  | @cons n x ns xs' hx _ ih =>
    refine .cons ?_ (ih (fun n' hn' e he => hpre n' (List.mem_cons_of_mem _ hn') e he))
    rw [List.find?_append]
    have hnone : pre.find? (·.1 == n) = none :=
      List.find?_eq_none.mpr (fun e he => by simpa using hpre n (List.mem_cons_self ..) e he)
    rw [hnone]
    simpa using hx

theorem find_head (b : String) (v : SourceValue F) (rest : Environment F Nat) :
    ((b, v) :: rest).find? (·.1 == b) = some (b, v) := by
  simp [List.find?_cons]

/-! ## The block's words -/

/-- The words of a block, from its byte names four at a time (`UInt32::from_bytes`). -/
def fbCalls : List String → List (Aiur.Generic.Expr F)
  | a :: b :: c :: d :: rest =>
    .call "UInt32::from_bytes" (some []) [.array [.var a, .var b, .var c, .var d]] :: fbCalls rest
  | _ => []

/-- The words of a byte list, four bytes each. -/
def words4 : List UInt8 → List (SourceValue F)
  | a :: b :: c :: d :: rest => w4 a b c d :: words4 rest
  | _ => []

theorem var_lookup {types : List (String × Aiur.Generic.Ty)} {locals : Environment F Nat}
    {n : String} {v : SourceValue F} (hl : locals.find? (·.1 == n) = some (n, v))
    {before after : Heap F} {r : SourceValue F} {c : List (Call F)}
    (d : ObsExpr W types locals (.var n) before r after c) : r = v ∧ after = before := by
  obtain ⟨l, rfl, rfl⟩ := d.var_inv
  exact ⟨((Prod.mk.inj (Option.some.inj (hl.symm.trans l))).2).symm, rfl⟩

theorem fbCall_inv {locals : Environment F Nat} {a b c d : String} {x0 x1 x2 x3 : UInt8}
    (h0 : locals.find? (·.1 == a) = some (a, bv x0)) (h1 : locals.find? (·.1 == b) = some (b, bv x1))
    (h2 : locals.find? (·.1 == c) = some (c, bv x2)) (h3 : locals.find? (·.1 == d) = some (d, bv x3))
    {before after : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsExpr W [] locals
      (.call "UInt32::from_bytes" (some []) [.array [.var a, .var b, .var c, .var d]])
      before r after cs) : r = w4 x0 x1 x2 x3 ∧ after = before := by
  obtain ⟨vs, mid, c1, c2, args, evf, rfl⟩ := ev.call_inv
  rw [instanceName_plain_some] at evf
  obtain ⟨v, vs', m1, c3, c4, rfl, da, an, rfl⟩ := args.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := an.nil_inv
  obtain ⟨ws, aw, rfl⟩ := da.array_inv
  obtain ⟨u0, us0, n0, e0, f0, rfl, d0, a0, rfl⟩ := aw.cons_inv
  obtain ⟨rfl, rfl⟩ := var_lookup h0 d0
  obtain ⟨u1, us1, n1, e1, f1, rfl, d1, a1, rfl⟩ := a0.cons_inv
  obtain ⟨rfl, rfl⟩ := var_lookup h1 d1
  obtain ⟨u2, us2, n2, e2, f2, rfl, d2, a2, rfl⟩ := a1.cons_inv
  obtain ⟨rfl, rfl⟩ := var_lookup h2 d2
  obtain ⟨u3, us3, n3, e3, f3, rfl, d3, a3, rfl⟩ := a2.cons_inv
  obtain ⟨rfl, rfl⟩ := var_lookup h3 d3
  obtain ⟨rfl, rfl, rfl⟩ := a3.nil_inv
  obtain ⟨rfl, rfl⟩ := u32_fromBytes evf
  exact ⟨rfl, rfl⟩

theorem fbCalls_inv {locals : Environment F Nat} : ∀ (names : List String) (xs : List UInt8),
    Bound locals names xs → ∀ {before after : Heap F} {vs : List (SourceValue F)}
    {cs : List (Call F)}, ObsArgs W [] locals (fbCalls names) before vs after cs →
    vs = words4 xs ∧ after = before
  | [], xs, hb, before, after, vs, cs, ev => by
    cases hb
    obtain ⟨rfl, rfl, rfl⟩ := ev.nil_inv
    exact ⟨rfl, rfl⟩
  | [_], xs, hb, before, after, vs, cs, ev => by
    obtain ⟨rfl, rfl, rfl⟩ := ev.nil_inv
    rcases hb with _ | ⟨_, hb⟩
    rcases hb with ⟨⟩
    exact ⟨rfl, rfl⟩
  | [_, _], xs, hb, before, after, vs, cs, ev => by
    obtain ⟨rfl, rfl, rfl⟩ := ev.nil_inv
    rcases hb with _ | ⟨_, hb⟩
    rcases hb with _ | ⟨_, hb⟩
    rcases hb with ⟨⟩
    exact ⟨rfl, rfl⟩
  | [_, _, _], xs, hb, before, after, vs, cs, ev => by
    obtain ⟨rfl, rfl, rfl⟩ := ev.nil_inv
    rcases hb with _ | ⟨_, hb⟩
    rcases hb with _ | ⟨_, hb⟩
    rcases hb with _ | ⟨_, hb⟩
    rcases hb with ⟨⟩
    exact ⟨rfl, rfl⟩
  | a :: b :: c :: d :: rest, xs, hb, before, after, vs, cs, ev => by
    rcases hb with _ | ⟨h0, hb⟩
    rcases hb with _ | ⟨h1, hb⟩
    rcases hb with _ | ⟨h2, hb⟩
    rcases hb with _ | ⟨h3, hb⟩
    obtain ⟨v, vs', m1, c1, c2, rfl, dv, av, rfl⟩ := ev.cons_inv
    obtain ⟨rfl, rfl⟩ := fbCall_inv h0 h1 h2 h3 dv
    obtain ⟨rfl, rfl⟩ := fbCalls_inv rest _ hb av
    exact ⟨rfl, rfl⟩

theorem words4_length_getElem : ∀ (xs : List UInt8) (k : Nat) (h : k * 4 + 3 < xs.length),
    ∃ hk : k < (words4 xs).length,
      (words4 xs)[k] = w4 xs[k * 4] xs[k * 4 + 1] xs[k * 4 + 2] xs[k * 4 + 3]
  | a :: b :: c :: d :: rest, 0, h => ⟨by simp [words4], rfl⟩
  | a :: b :: c :: d :: rest, k + 1, h => by
    obtain ⟨hk, e⟩ := words4_length_getElem rest k (by simp at h; omega)
    refine ⟨by simp [words4]; omega, ?_⟩
    simp only [words4, List.getElem_cons_succ]
    rw [e]
    have i0 : (k + 1) * 4 = k * 4 + 3 + 1 := by omega
    have i1 : (k + 1) * 4 + 1 = (k * 4 + 1) + 3 + 1 := by omega
    have i2 : (k + 1) * 4 + 2 = (k * 4 + 2) + 3 + 1 := by omega
    have i3 : (k + 1) * 4 + 3 = (k * 4 + 3) + 3 + 1 := by omega
    simp only [i0, i1, i2, i3, List.getElem_cons_succ]
  | [], k, h => by simp at h
  | [_], k, h => by simp at h <;> omega
  | [_, _], k, h => by simp at h <;> omega
  | [_, _, _], k, h => by simp at h <;> omega

theorem words4_length : ∀ (xs : List UInt8), (words4 xs).length = xs.length / 4
  | a :: b :: c :: d :: rest => by simp [words4, words4_length rest]; omega
  | [] => by simp [words4]
  | [_] => by simp [words4]
  | [_, _] => by simp [words4]
  | [_, _, _] => by simp [words4]

theorem bytesWord_four (xs : List UInt8) (k : Nat) (hk : k * 4 + 3 < xs.length) :
    Blake3.Pure.bytesWord (Vector.ofFn fun b : Fin 4 => xs.toArray[k * 4 + b.val]?.getD 0) =
      wordOfBytes xs[k * 4] xs[k * 4 + 1] xs[k * 4 + 2] xs[k * 4 + 3] := by
  rw [← Aiur.Library.Blake3.bytesWord_eq_wordOfBytes]
  congr 1
  ext b hb
  simp only [Vector.getElem_ofFn]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
  · simp [List.getElem?_eq_getElem (show k * 4 < xs.length by omega)]
  · simp [List.getElem?_eq_getElem (show k * 4 + 1 < xs.length by omega)]
  · simp [List.getElem?_eq_getElem (show k * 4 + 2 < xs.length by omega)]
  · simp [List.getElem?_eq_getElem (show k * 4 + 3 < xs.length by omega)]

/-- **Sixty-four bytes read four at a time are `blockWords` of them.** -/
theorem words4_eq (xs : List UInt8) (hx : xs.length = 64) :
    (.tuple (words4 xs) : SourceValue F) = vecV (Blake3.Pure.blockWords xs) := by
  rw [vecV]
  congr 1
  apply List.ext_getElem (by simp [words4_length, hx])
  intro k h1 h2
  have hk : k * 4 + 3 < xs.length := by
    rw [words4_length, hx] at h1
    omega
  obtain ⟨-, e⟩ := words4_length_getElem xs k hk
  rw [e, List.getElem_ofFn]
  simp only [Blake3.Pure.blockWords, Vector.getElem_ofFn, Fin.getElem_fin]
  rw [bytesWord_four xs k hk, wv_wordOfBytes]

/-! ## `Blake3::take_block` -/

def nilPat : Aiur.Generic.Pattern F := .construct (.named "Lists::Node" [.field]) "Nil" []

def consPat (b l : String) : Aiur.Generic.Pattern F :=
  .construct (.named "Lists::Node" [.field]) "Cons" [.bind b, .bind l]

/-- `take_block`'s innermost body: the sixteen words and the stream after them. -/
def tbFull : Aiur.Generic.Expr F :=
  .construct "Blake3::BlockRead" (some []) "Full" [.array (fbCalls bNames), .var "l"]

/-- `take_block`'s body from the byte `bs.head`: a match on the next cell. -/
def tbFrom : List String → String → Aiur.Generic.Expr F
  | [], _ => tbFull
  | b :: bs, scr => .matchValue (.load (.var scr))
      [(nilPat, .construct "Blake3::BlockRead" (some []) "Short" []), (consPat b "l", tbFrom bs "l")]

theorem take_block_body : IxVM.Blake3.take_block.body = tbFrom bNames "input" := rfl

theorem tbLevel_inv {locals : Environment F Nat} {scr b : String} {bs : List String}
    {ptr : SourceValue F} {bytes : List UInt8} {h h' : Heap F} {r : SourceValue F}
    {cs : List (Call F)} (hscr : locals.find? (·.1 == scr) = some (scr, ptr))
    (hrep : Stream h bytes ptr) (ev : ObsExpr W [] locals (tbFrom (b :: bs) scr) h r h' cs) :
    (bytes = [] ∧ r = .construct "Blake3::BlockRead" "Short" [] ∧ h' = h) ∨
    (∃ x xs tail cs', bytes = x :: xs ∧ Stream h xs tail ∧
      ObsExpr W [] ([(b, bv x), ("l", tail)] ++ locals) (tbFrom bs "l") h r h' cs') := by
  simp only [tbFrom] at ev
  obtain ⟨v, m1, bnd, body, c1, c2, dx, sel, db, rfl⟩ := ev.matchValue_inv
  obtain ⟨p, dp, ld⟩ := dx.load_inv
  obtain ⟨rfl, rfl⟩ := var_lookup hscr dp
  rcases stream_inv hrep ld with ⟨rfl, rfl⟩ | ⟨x, xs, tail, rfl, rfl, htail⟩
  · rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, -⟩
    · rw [nilPat, match_nil_nil] at mt
      cases mt
      obtain ⟨vs, a, rfl⟩ := db.construct_inv
      obtain ⟨rfl, rfl, rfl⟩ := a.nil_inv
      exact .inl ⟨rfl, by rw [instanceName_plain_some], rfl⟩
    · rw [nilPat, match_nil_nil] at nm
      cases nm
  · rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, sel2⟩
    · rw [nilPat, match_nil_cons] at mt
      cases mt
    · rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨-, sel3⟩
      · rw [consPat, match_cons_cons] at mt2
        cases mt2
        exact .inr ⟨x, xs, tail, _, rfl, htail, db⟩
      · exact (selectArm_nil_inv sel3).elim

theorem tbFull_inv {locals : Environment F Nat} {xs : List UInt8} (hb : Bound locals bNames xs)
    {ptr : SourceValue F} (hl : locals.find? (·.1 == "l") = some ("l", ptr))
    {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsExpr W [] locals tbFull h r h' cs) :
    r = .construct "Blake3::BlockRead" "Full" [.tuple (words4 xs), ptr] ∧ h' = h := by
  obtain ⟨vs, a, rfl⟩ := ev.construct_inv
  obtain ⟨v1, vs1, m1, c1, c2, rfl, d1, a1, rfl⟩ := a.cons_inv
  obtain ⟨ws, aw, rfl⟩ := d1.array_inv
  obtain ⟨rfl, rfl⟩ := fbCalls_inv bNames xs hb aw
  obtain ⟨v2, vs2, m2, c3, c4, rfl, d2, a2, rfl⟩ := a1.cons_inv
  obtain ⟨rfl, rfl⟩ := var_lookup hl d2
  obtain ⟨rfl, rfl, rfl⟩ := a2.nil_inv
  exact ⟨by rw [instanceName_plain_some], rfl⟩

theorem tbFrom_inv : ∀ (bs pre : List String) (ys : List UInt8) {locals : Environment F Nat}
    {scr : String} {ptr : SourceValue F} {bytes : List UInt8} {h h' : Heap F} {r : SourceValue F}
    {cs : List (Call F)},
    pre.reverse ++ bs = bNames → (bs = [] → scr = "l") → Bound locals pre ys →
    locals.find? (·.1 == scr) = some (scr, ptr) → Stream h bytes ptr →
    ObsExpr W [] locals (tbFrom bs scr) h r h' cs →
    h' = h ∧ ((bytes.length < bs.length ∧ r = .construct "Blake3::BlockRead" "Short" []) ∨
      (bs.length ≤ bytes.length ∧ ∃ tail,
        r = .construct "Blake3::BlockRead" "Full"
          [.tuple (words4 (ys.reverse ++ bytes.take bs.length)), tail] ∧
        Stream h (bytes.drop bs.length) tail))
  | [], pre, ys, locals, scr, ptr, bytes, h, h', r, cs, hpre, hscr, hb, hl, hs, ev => by
    obtain rfl := hscr rfl
    simp only [List.append_nil] at hpre
    have hb' : Bound locals bNames ys.reverse := by
      rw [← hpre]
      exact List.forall₂_reverse_iff.mpr hb
    simp only [tbFrom] at ev
    obtain ⟨rfl, rfl⟩ := tbFull_inv hb' hl ev
    refine ⟨rfl, .inr ⟨by simp, ptr, by simp, by simpa using hs⟩⟩
  | b :: bs, pre, ys, locals, scr, ptr, bytes, h, h', r, cs, hpre, hscr, hb, hl, hs, ev => by
    rcases tbLevel_inv hl hs ev with ⟨rfl, rfl, rfl⟩ | ⟨x, xs, tail, cs', rfl, htail, db⟩
    · exact ⟨rfl, .inl ⟨by simp, rfl⟩⟩
    · have hnd : (pre.reverse ++ b :: bs).Nodup := by rw [hpre]; exact bNames_nodup
      have hbpre : b ∉ pre := by
        intro hm
        exact (List.nodup_append.mp hnd).2.2 b (List.mem_reverse.mpr hm) b
          (List.mem_cons_self ..) rfl
      have hbmem : b ∈ bNames := by rw [← hpre]; simp
      have hbl : b ≠ "l" := fun e => l_notMem (e ▸ hbmem)
      have hlpre : "l" ∉ pre := by
        intro hm
        apply l_notMem
        rw [← hpre]
        exact List.mem_append_left _ (List.mem_reverse.mpr hm)
      have hb2 : Bound ([(b, bv x), ("l", tail)] ++ locals) (b :: pre) (x :: ys) := by
        refine .cons (by simp [List.find?_cons]) (bound_skip _ ?_ hb)
        intro n hn e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · intro e'
          simp only at e'
          exact hbpre (e' ▸ hn)
        · intro e'
          simp only at e'
          exact hlpre (e' ▸ hn)
      obtain ⟨rfl, hres⟩ := tbFrom_inv bs (b :: pre) (x :: ys) (by simpa using hpre)
        (fun _ => rfl) hb2 (by simp [List.find?_cons, hbl]) htail db
      refine ⟨rfl, ?_⟩
      rcases hres with ⟨hlt, rfl⟩ | ⟨hle, tl, rfl, htl⟩
      · exact .inl ⟨by simp; omega, rfl⟩
      · refine .inr ⟨by simp; omega, tl, ?_, by simpa using htl⟩
        simp

/-- **`Blake3::take_block`**: the first 64 bytes as `blockWords` and the stream after them, or
`Short` when fewer than 64 are left. -/
theorem take_block_spec {inp r : SourceValue F} {bytes : List UInt8} {h h' : Heap F}
    {cs : List (Call F)} (hs : Stream h bytes inp)
    (ev : ObsFn W "Blake3::take_block" [inp] h r h' cs) :
    h' = h ∧ ((bytes.length < 64 ∧ r = .construct "Blake3::BlockRead" "Short" []) ∨
      (64 ≤ bytes.length ∧ ∃ tail,
        r = .construct "Blake3::BlockRead" "Full"
          [vecV (Blake3.Pure.blockWords (bytes.take 64)), tail] ∧
        Stream h (bytes.drop 64) tail)) := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.Blake3.take_block.lookup
    (by first | rfl | decide | simp [IxVM.Blake3.take_block, ControlLower.hasControl]) ev
  rw [take_block_body] at d0
  obtain ⟨rfl, hres⟩ := tbFrom_inv bNames [] [] (by rfl) (by simp [bNames]) .nil
    (by first | rfl | simp [IxVM.Blake3.take_block]) hs d0
  refine ⟨rfl, ?_⟩
  rw [bNames_length] at hres
  rcases hres with ⟨hlt, rfl⟩ | ⟨hle, tl, rfl, htl⟩
  · exact .inl ⟨hlt, rfl⟩
  · refine .inr ⟨hle, tl, ?_, htl⟩
    rw [List.reverse_nil, List.nil_append, words4_eq (bytes.take 64) (by simp; omega)]

/-! ## `Blake3::bytes_to_block` -/

def conswPat (b : String) : Aiur.Generic.Pattern F :=
  .construct (.named "Lists::Node" [.field]) "Cons" [.bind b, .wildcard]

/-- `bytes_to_block`'s body from the byte `bs.head`: a `let` reading the next cell. -/
def bbFrom : List String → String → Aiur.Generic.Expr F
  | [], _ => .array (fbCalls bNames)
  | b :: bs, scr => match bs with
    | [] => .letValue (conswPat b) (.load (.var scr)) (.array (fbCalls bNames))
    | _ :: _ => .letValue (consPat b "l") (.load (.var scr)) (bbFrom bs "l")

theorem bytes_to_block_body : IxVM.Blake3.bytes_to_block.body = bbFrom bNamesRev "byte_acc" := rfl

theorem bNames_eq_rev : bNamesRev.reverse = bNames := by
  first | rfl | decide | (simp [bNames, bNamesRev]; done)

theorem mem_bNames_of_rev {pre bs : List String} {b : String}
    (h : pre.reverse ++ b :: bs = bNamesRev) : b ∈ bNames := by
  rw [← bNames_eq_rev, ← h]
  simp

theorem bbFrom_inv : ∀ (bs pre : List String) (ys : List UInt8) {locals : Environment F Nat}
    {scr : String} {ptr : SourceValue F} {bytes : List UInt8} {h h' : Heap F} {r : SourceValue F}
    {cs : List (Call F)},
    bs ≠ [] → pre.reverse ++ bs = bNamesRev → Bound locals pre ys →
    locals.find? (·.1 == scr) = some (scr, ptr) → Stream h bytes ptr →
    ObsExpr W [] locals (bbFrom bs scr) h r h' cs →
    h' = h ∧ bs.length ≤ bytes.length ∧
      r = .tuple (words4 ((bytes.take bs.length).reverse ++ ys))
  | [], _, _, _, _, _, _, _, _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | [b], pre, ys, locals, scr, ptr, bytes, h, h', r, cs, _, hpre, hb, hl, hs, ev => by
    simp only [bbFrom] at ev
    obtain ⟨v, m1, bnd, c1, c2, dx, mt, db, rfl⟩ := ev.letValue_inv
    obtain ⟨p, dp, ld⟩ := dx.load_inv
    obtain ⟨rfl, rfl⟩ := var_lookup hl dp
    rcases stream_inv hs ld with ⟨rfl, rfl⟩ | ⟨x, xs, tail, rfl, rfl, htail⟩
    · rw [conswPat, match_consw_nil] at mt
      cases mt
    · rw [conswPat, match_consw_cons] at mt
      cases mt
      have hfull : pre.reverse ++ [b] = bNamesRev := hpre
      have hpre' : b :: pre = bNames := by
        rw [← bNames_eq_rev, ← hfull]
        simp
      have hbpre : b ∉ pre := by
        have hnd : (b :: pre).Nodup := by rw [hpre']; exact bNames_nodup
        exact (List.nodup_cons.mp hnd).1
      have hb2 : Bound ([(b, bv x)] ++ locals) bNames (x :: ys) := by
        rw [← hpre']
        refine .cons (by simp [List.find?_cons]) (bound_skip _ ?_ hb)
        intro n hn e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        intro e'
        simp only at e'
        exact hbpre (e' ▸ hn)
      obtain ⟨ws, aw, rfl⟩ := db.array_inv
      obtain ⟨rfl, rfl⟩ := fbCalls_inv bNames (x :: ys) hb2 aw
      exact ⟨rfl, by simp, by simp⟩
  | b :: c :: bs, pre, ys, locals, scr, ptr, bytes, h, h', r, cs, _, hpre, hb, hl, hs, ev => by
    simp only [bbFrom] at ev
    obtain ⟨v, m1, bnd, c1, c2, dx, mt, db, rfl⟩ := ev.letValue_inv
    obtain ⟨p, dp, ld⟩ := dx.load_inv
    obtain ⟨rfl, rfl⟩ := var_lookup hl dp
    rcases stream_inv hs ld with ⟨rfl, rfl⟩ | ⟨x, xs, tail, rfl, rfl, htail⟩
    · rw [consPat, match_cons_nil] at mt
      cases mt
    · rw [consPat, match_cons_cons] at mt
      cases mt
      have hnd : (pre.reverse ++ b :: c :: bs).Nodup := by
        rw [hpre, bNamesRev_eq]
        exact List.nodup_reverse.mpr bNames_nodup
      have hbpre : b ∉ pre := by
        intro hm
        exact (List.nodup_append.mp hnd).2.2 b (List.mem_reverse.mpr hm) b
          (List.mem_cons_self ..) rfl
      have hbmem : b ∈ bNames := mem_bNames_of_rev hpre
      have hbl : b ≠ "l" := fun e => l_notMem (e ▸ hbmem)
      have hlpre : "l" ∉ pre := by
        intro hm
        apply l_notMem
        rw [← bNames_eq_rev, ← hpre]
        simp [hm]
      have hb2 : Bound ([(b, bv x), ("l", tail)] ++ locals) (b :: pre) (x :: ys) := by
        refine .cons (by simp [List.find?_cons]) (bound_skip _ ?_ hb)
        intro n hn e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · intro e'
          simp only at e'
          exact hbpre (e' ▸ hn)
        · intro e'
          simp only at e'
          exact hlpre (e' ▸ hn)
      obtain ⟨rfl, hle, rfl⟩ := bbFrom_inv (c :: bs) (b :: pre) (x :: ys) (by simp)
        (by simpa using hpre) hb2 (by simp [List.find?_cons, hbl]) htail db
      refine ⟨rfl, by simp at hle ⊢; omega, ?_⟩
      simp

/-- **`Blake3::bytes_to_block`**: the words of the first 64 bytes of the list, last byte first
(`byte_acc` holds a block's bytes in reverse). -/
theorem bytes_to_block_spec {acc r : SourceValue F} {bytes : List UInt8} {h h' : Heap F}
    {cs : List (Call F)} (hs : Stream h bytes acc)
    (ev : ObsFn W "Blake3::bytes_to_block" [acc] h r h' cs) :
    h' = h ∧ 64 ≤ bytes.length ∧ r = vecV (Blake3.Pure.blockWords (bytes.take 64).reverse) := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.Blake3.bytes_to_block.lookup
    (by first | rfl | decide | simp [IxVM.Blake3.bytes_to_block, ControlLower.hasControl]) ev
  rw [bytes_to_block_body] at d0
  obtain ⟨rfl, hle, rfl⟩ := bbFrom_inv bNamesRev [] [] (by simp [bNamesRev]) (by rfl) .nil
    (by first | rfl | simp [IxVM.Blake3.bytes_to_block]) hs d0
  have hlen : bNamesRev.length = 64 := rfl
  rw [hlen] at hle
  refine ⟨rfl, hle, ?_⟩
  rw [hlen, List.append_nil, words4_eq (bytes.take 64).reverse (by simp; omega)]

/-! ## `Blake3::pad_block` -/

theorem bv_zero : (bv 0 : SourceValue F) = .field 0 := by
  first | (simp [bv]; done) | rfl | (simp; done)

/-- **`Blake3::pad_block(acc, n)`** prepends `n` zero bytes. -/
theorem pad_block_spec : ∀ (n : Nat) {acc r : SourceValue F} {bytes : List UInt8} {h h' : Heap F}
    {cs : List (Call F)}, n < 1024 → Stream h bytes acc →
    ObsFn W "Blake3::pad_block" [acc, .field (n : F)] h r h' cs →
    Heap.Extends h h' ∧ Stream h' (List.replicate n 0 ++ bytes) r
  | 0, acc, r, bytes, h, h', cs, hn, hs, ev => by
    rcases «Blake3::pad_block».obs ev with ⟨hv, rfl, rfl, -⟩ | ⟨cs26, v30, m32, hne, -⟩
    · exact ⟨Heap.Extends.refl _, by simpa using hs⟩
    · exact absurd (by simp) hne
  | n + 1, acc, r, bytes, h, h', cs, hn, hs, ev => by
    rcases «Blake3::pad_block».obs ev with ⟨hv, -⟩ | ⟨cs26, v30, m32, hne, rfl, op72, ev28, -⟩
    · exact absurd (IxVM.natCast_inj (b := 0) hn (by omega) (by simpa using Value.field.inj hv))
        (by omega)
    · obtain rfl := binop_sub op72
      have hs1 : Stream (h ++ [.construct byteStreamEnum "Cons" [.field 0, acc]]) (0 :: bytes)
          (.ptr (.enum byteStreamEnum) h.length) := by
        have := stream_cons_snoc (x := 0) hs
        rwa [bv_zero] at this
      have e : ((n + 1 : Nat) : F) - 1 = ((n : Nat) : F) := by push_cast; ring
      rw [e] at ev28
      obtain ⟨ext, hr⟩ := pad_block_spec n (by omega) hs1 ev28
      refine ⟨(Heap.Extends.snoc h _).trans ext, ?_⟩
      simpa [List.replicate_succ'] using hr

end IxVM.Refinement.L1
