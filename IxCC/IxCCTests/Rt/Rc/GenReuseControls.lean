import IxCCTests.Rt.Rc.GenControls
import IxCC.Rt.Rc.Gen.Proof.WriteCell
import IxCC.Own.Rc.Reuse

/-! Executable controls of the in-place reuse lemmas (`Own.Rc.reuseCell_balance`,
`reuseCell_heapOk`, `reuseCell_readback`, `Rt.Rc.Gen.inPlace_ready`) on concrete instances, over
the same definitions the theorems state (`Own.Rc.reuseCell`, `Rt.Rc.Gen.writeCell`). For each
instance: every premise decided (balance on every location up to the heap's size + 4, uniqueness,
the mass condition, order, layout, class, a word for every field), the three abstract conclusions
computed on the abstract heap, and `inPlace_ready`'s conclusion checked on the Lir interpreter in
`GenControls`' memory: every live cell of the new heap a `LiveCell` (header, count word, every
field's word), nothing outside the cell changed (context, bump, all 71 heads, other cells),
`isUnique` 1 on the old and the new cell, and `Gen.dec` of the new cell doing what `dropAll`
does. Negative controls: a scanned field without a word (the premise `hwords` is needed, not only
sufficient), a shared cell rewritten anyway, a cell rewritten at a larger class. Two limits are
recorded as such: a static child (outside the invariant) and a smaller class (outside the
invariant, physically harmless). -/
open IxCC IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc (dynamicHeader maxClass)
open IxCC.Rt.Rc.Gen (layoutOf classOf cellBytesOf scalarWord fieldWord writeCell)
open IxCC.Rt.Rc.Procs (AddressMap)
open IxCCTests.Rt.Rc.GenControls (init rd run mem? vals? freeList decP uniqueP headAt checkCase)

namespace IxCCTests.Rt.Rc.GenReuseControls

abbrev Word := UInt64

/-! ## Constructors, heaps and their placement in memory -/

def ctor (tag nobj nscalar : Nat) : Fir.CtorInfo :=
  { key := .src (100 + tag), tag, nobj, nscalar, fieldKinds := List.replicate nobj .shared }
def nilC : Fir.CtorInfo := { key := .src 6, tag := 0, nobj := 0, fieldKinds := [] }
def nil : RVal := .ctor0 nilC
def nat (n : Nat) : RVal := .lit (.nat n)
def consC : Fir.CtorInfo := ctor 1 2 0
def cons (h : Nat) (t : RVal) : Body := ⟨consC, [nat h, t]⟩

def addrOf (as : List Word) : AddressMap := fun k => as[k]?

/-- A live dynamic cell placed as `LiveCell` describes it; a static cell with an immortal header. -/
def placeCell (m : X86.Memory) (addr : AddressMap) (a : Word) (rc : Nat) (mode : OMode) (b : Body) :
    X86.Memory :=
  let h : Word := match mode with
    | .dyn => dynamicHeader b.ctor.nobj (classOf b.ctor) b.ctor.tag rc
    | .static => UInt64.ofNat (Rt.headerLow b.ctor.nobj 0 b.ctor.tag + 2 ^ 32 * Rt.immortalRc)
  let m := m.write .w64 a h
  (b.fields.zipIdx).foldl (fun m (v, j) =>
    m.write .w64 (a + UInt64.ofNat (8 + 8 * j)) ((fieldWord addr b.ctor j v).getD 0)) m

def place (H : Heap) (addr : AddressMap) : X86.Memory :=
  (H.cells.toList.zipIdx).foldl (fun m (c, k) => match c, addr k with
    | .live rc mode b, some a => placeCell m addr a rc mode b
    | _, _ => m) init

/-! ## Decided forms of the premises and conclusions -/

def balanceUpTo (H : Heap) (external : Nat → Nat) (pending : List RVal) (n : Nat) : Bool :=
  (List.range n).all fun l => dynCount H l == external l + refsIn l pending + edgeCount H l

def heapOkB (H : Heap) : Bool :=
  (List.range H.size).all fun l => match H.cell? l with
    | some (.live rc m b) => m == .dyn && 0 < rc && b.fields.length == b.ctor.arity &&
        0 < b.ctor.arity && b.fields.all (fun | .loc k => k < l | _ => true)
    | _ => true

/-- `LiveCell`'s memory clauses: header, count word, every field's word. -/
def liveCellOk (m : X86.Memory) (addr : AddressMap) (a : Word) (rc : Nat) (b : Body) : Bool :=
  (layoutOf b.ctor).ok && b.fields.length == b.ctor.nobj + b.ctor.nscalar &&
  m.read .w32 a == UInt64.ofNat (Rt.headerLow b.ctor.nobj (classOf b.ctor) b.ctor.tag) &&
  m.read .w32 (a + 4) == UInt64.ofNat (rc - 1) &&
  (b.fields.zipIdx).all fun (v, j) => match fieldWord addr b.ctor j v with
    | some w => m.read .w64 (a + UInt64.ofNat (8 + 8 * j)) == w
    | none => false

/-- `HeapLive.cell`: every live cell dynamic, placed, and a `LiveCell`. -/
def heapLiveOk (H : Heap) (addr : AddressMap) (m : X86.Memory) : Bool :=
  (List.range H.size).all fun k => match H.cell? k with
    | some (.live rc .dyn b) => match addr k with
      | some a => liveCellOk m addr a rc b
      | none => false
    | some (.live _ .static _) => false
    | _ => true

/-- Every word of `[0, 12288)` outside `[a, a + bytes)` unchanged: the context block, the bump and
limit words, all 71 heads, every other cell of the instances. -/
def frameOk (m m' : X86.Memory) (a : Word) (bytes : Nat) : Bool :=
  (List.range (12288 / 8)).all fun i =>
    let w : Word := UInt64.ofNat (8 * i)
    (a ≤ w && w < a + UInt64.ofNat bytes) || rd m w == rd m' w

/-- `Gen.dec` of `a` on the interpreter does what `dropAll` does to location `r`: every cell that
dies is on its class's list, every survivor keeps its header and has `dropAll`'s count, and
nothing else is freed. -/
def releaseOk (H' : Heap) (addr' : AddressMap) (m' : X86.Memory) (r : Nat) (a : Word) : Bool :=
  match dropAll H' [.loc r], mem? (run decP [a] m') with
  | some H'', some m'' =>
    let died := (List.range H'.size).filterMap fun k => match H'.cell? k, H''.cell? k, addr' k with
      | some (.live _ .dyn b), some .dead, some a => some (a, classOf b.ctor)
      | _, _, _ => none
    let survivors := (List.range H'.size).all fun k => match H'.cell? k, H''.cell? k, addr' k with
      | some (.live _ .dyn _), some (.live rc .dyn _), some a =>
        m''.read .w32 (a + 4) == UInt64.ofNat (rc - 1) && m''.read .w32 a == m'.read .w32 a
      | _, _, _ => true
    let freed := (List.range' 1 maxClass).foldl (fun n c =>
      n + ((freeList m'' c).length - (freeList m' c).length)) 0
    survivors && died.all (fun (a, c) => (freeList m'' c).contains a) && freed == died.length
  | _, _ => false

/-! ## Instances -/

structure Inst where
  name : String
  H : Heap
  addr : AddressMap
  l : Nat
  rest : List RVal
  b' : Body
  kept : List RVal

def mk (name : String) (H : Heap) (addr : AddressMap) (l : Nat) (rest : List RVal) (b' : Body)
    (kept : List RVal) : Inst := ⟨name, H, addr, l, rest, b', kept⟩

def Inst.b (i : Inst) : Body := match i.H.cell? i.l with
  | some (.live _ _ b) => b
  | _ => default

def Inst.a (i : Inst) : Word := (i.addr i.l).getD 0
def Inst.mem (i : Inst) : X86.Memory := place i.H i.addr
/-- The memory after the rewrite, at the old cell's class (as `inPlace_ready` states it). -/
def Inst.mem' (i : Inst) : X86.Memory := writeCell i.mem i.addr i.a i.b' (classOf i.b.ctor)
def Inst.addr' (i : Inst) : AddressMap := fun k => if k = i.H.size then some i.a else i.addr k
def Inst.H' (i : Inst) : Heap := reusedHeap i.H i.l i.b'

def Inst.hc (i : Inst) : Bool := i.H.cell? i.l == some (.live 1 .dyn i.b)
def Inst.hb (i : Inst) : Bool := balanceUpTo i.H (fun _ => 0) (.loc i.l :: i.rest) (i.H.size + 4)
def Inst.hmass (i : Inst) : Bool := (List.range (i.H.size + 4)).all fun k =>
  refsIn k (i.b.fields ++ i.rest) == refsIn k (i.b'.fields ++ i.kept)
def Inst.hclass (i : Inst) : Bool := classOf i.b'.ctor == classOf i.b.ctor
def Inst.hwords (i : Inst) : Bool :=
  (i.b'.fields.zipIdx).all fun (v, j) => (fieldWord i.addr i.b'.ctor j v).isSome

/-- Every premise of the four statements except `hwords` (the plan's `inPlace_ready`'s), decided;
`ready` is `HeapLive.cell` of the placed memory. -/
def Inst.planned (i : Inst) : Bool :=
  i.hc && i.hb && i.hmass && heapOkB i.H && i.hclass &&
  i.b'.fields.length == i.b'.ctor.arity && 0 < i.b'.ctor.arity && (layoutOf i.b'.ctor).ok &&
  i.b'.ctor.fieldKinds == List.replicate i.b'.ctor.nobj .shared &&
  (i.b'.fields.zipIdx).all (fun (v, j) => j < i.b'.ctor.nobj || (scalarWord v).isSome) &&
  heapLiveOk i.H i.addr i.mem

/-- The conclusions of `reuseCell_balance`, `reuseCell_heapOk`, `reuseCell_readback`. -/
def Inst.abstractOk (i : Inst) : Bool :=
  match reuseCell i.H i.l i.b' with
  | some (r, H') =>
    r == .loc i.H.size && H' == i.H' &&
    balanceUpTo H' (fun _ => 0) (.loc i.H.size :: i.kept) (i.H.size + 5) &&
    heapOkB H' &&
    (i.rest ++ i.b.fields).all (fun u => H'.value? u == i.H.value? u) &&
    H'.value? r == (i.b'.fields.mapM i.H.value?).map (Fir.Val.ctor i.b'.ctor)
  | none => false

/-- `inPlace_ready`'s conclusion on the interpreter, with its consequences through `isUnique_spec`
and `release_caller_complete`. -/
def Inst.physicalOk (i : Inst) : Bool :=
  heapLiveOk i.H' i.addr' i.mem' && frameOk i.mem i.mem' i.a (cellBytesOf i.b.ctor) &&
  vals? (run uniqueP [i.a] i.mem) == some [1] && vals? (run uniqueP [i.a] i.mem') == some [1] &&
  releaseOk i.H' i.addr' i.mem' i.H.size i.a

/-- `l0 = 1 :: []` (one reference), `l1 = 2 :: l0` (two: `l2`'s field and the caller's token),
`l2 = 3 :: l1` (one, the caller's), class-3 cells placed contiguously from 2048. -/
def heapA : Heap := { cells := #[.live 1 .dyn (cons 1 nil), .live 2 .dyn (cons 2 (.loc 0)),
  .live 1 .dyn (cons 3 (.loc 1))] }
def addrA : AddressMap := addrOf [2048, 2072, 2096]

def same : Inst := mk "A same layout, a shared child moved: 3 :: l1 -> 4 :: l1"
  heapA addrA 2 [.loc 1] (cons 4 (.loc 1)) [.loc 1]
def otherLayout : Inst := mk "B same class, another layout: <1 scanned (l1), 1 scalar 2^40+7>"
  heapA addrA 2 [.loc 1] ⟨ctor 5 1 1, [.loc 1, nat (2 ^ 40 + 7)]⟩ [.loc 1]
def scalarsOnly : Inst := mk "C same class, two scalar words (5, 2^64-1), the child's token kept"
  heapA addrA 2 [.loc 1] ⟨ctor 6 0 2, [nat 5, nat (2 ^ 64 - 1)]⟩ [.loc 1, .loc 1]

/-- Class 33 (40 words): `W = <39 scanned>` with a unique child U (`l1`), a shared child S (`l0`:
`W`'s field and the caller's token), immediates, and a unique child V (`l2`) in its last field;
rewritten as `<32 scanned, 3 scalars>` (36 words, class 33) taking S twice and U, V's token kept by
the caller. V's address stays in the old word past the new cell's words. -/
def heapD : Heap :=
  let wf : List RVal := [.loc 1, .loc 0, nil, .erased] ++ (List.range 34).map (fun j => nat (j + 20)) ++
    [.loc 2]
  { cells := #[.live 2 .dyn (cons 10 nil), .live 1 .dyn (cons 11 nil), .live 1 .dyn (cons 12 nil),
    .live 1 .dyn ⟨ctor 2 39 0, wf⟩] }
def addrD : AddressMap := addrOf [2048, 2072, 2096, 4096]
def wide : Inst :=
  let nf : List RVal := [.loc 0, .loc 1, .erased, nil] ++ (List.range 27).map (fun j => nat (j + 50)) ++
    [.loc 0]
  mk "D class 33, 39 scanned -> 32 scanned + 3 scalars: unique, shared, immediate children, one kept"
    heapD addrD 3 [.loc 0] ⟨ctor 4 32 3, nf ++ [nat 0, nat (2 ^ 63), nat 123]⟩ [.loc 2]

/-- A static child: `s0` static at 2048, `l1 = 3 :: []` unique at 2072 rewritten as `4 :: s0`. -/
def heapE : Heap := { cells := #[.live 1 .static (cons 9 nil), .live 1 .dyn (cons 3 nil)] }
def staticChild : Inst := mk "E static child" heapE (addrOf [2048, 2072]) 1 [] (cons 4 (.loc 0)) []
def staticChildToken : Inst := mk "E' static child, a token claimed for it"
  heapE (addrOf [2048, 2072]) 1 [.loc 0] (cons 4 (.loc 0)) []

/-- A scanned field without a word, every premise of the plan's `inPlace_ready` holding. -/
def noWordStr : Inst := mk "F scanned string literal"
  heapA addrA 2 [.loc 1] ⟨consC, [.lit (.str "s"), .loc 1]⟩ [.loc 1]
def noWordNat : Inst := mk "F' scanned 2^63" heapA addrA 2 [.loc 1] ⟨consC, [nat (2 ^ 63), .loc 1]⟩ [.loc 1]

def shared : Inst := mk "N1 shared cell" heapA addrA 1 [.loc 2] (cons 9 (.loc 0)) [.loc 2]
def staticCell : Inst := mk "N2 static cell" heapE (addrOf [2048, 2072]) 0 [] (cons 4 nil) []
/-- Three contiguous class-3 cells, the last one shared (two tokens); the middle one rewritten at
class 4, then at class 2. -/
def heapN3 : Heap := { cells := #[.live 1 .dyn (cons 1 nil), .live 1 .dyn (cons 2 nil),
  .live 2 .dyn (cons 3 nil)] }
def bigger : Inst := mk "N3 class 3 -> class 4" heapN3 (addrOf [2048, 2072, 2096]) 1
  [.loc 0, .loc 2, .loc 2] ⟨ctor 1 3 0, [nat 4, nat 5, nat 6]⟩ [.loc 0, .loc 2, .loc 2]
def smaller : Inst := mk "N3' class 3 -> class 2" heapN3 (addrOf [2048, 2072, 2096]) 1
  [.loc 0, .loc 2, .loc 2] ⟨ctor 1 1 0, [nat 4]⟩ [.loc 0, .loc 2, .loc 2]

/-- Addresses below 16 unreadable (natively page 0 is unmapped). -/
def lowUnreadable (m : X86.Memory) : X86.Memory := { m with readable := fun a => 16 ≤ a && m.readable a }

def stuckOrTrap : Lir.Outcome → Bool
  | .stuck | .trap => true
  | _ => false

/-! ## The controls -/

def positiveTests : IO Unit := do
  for i in [same, otherLayout, scalarsOnly, wide] do
    checkCase s!"gen reuse {i.name}: every premise holds" (i.planned && i.hwords)
    checkCase s!"gen reuse {i.name}: balance, order and readback kept (the three abstract lemmas)"
      i.abstractOk
    checkCase s!"gen reuse {i.name}: inPlace_ready's state (live cells, frame, isUnique 1, dec = dropAll)"
      i.physicalOk
  checkCase "gen reuse D: the stale word past the new cell is not followed (V kept, S and U freed)"
    (match mem? (run decP [wide.a] wide.mem') with
      | some m => freeList m 33 == [4096] && freeList m 3 == [2048, 2072] &&
          rd m 2096 == dynamicHeader 2 3 1 1 && rd wide.mem' (4096 + 8 * 39) == 2096
      | none => false)

/-- Recorded limits: what the lemmas do not speak about. -/
def limitTests : IO Unit := do
  checkCase "gen reuse E: a static child is outside the invariant (mass or balance fails, HeapOk fails)"
    (staticChild.hc && !staticChild.hmass && !heapOkB staticChild.H &&
      !staticChildToken.hb && !heapOkB staticChildToken.H)
  checkCase "gen reuse E: physically the static child is untouched by the rewrite and the release"
    (match mem? (run decP [2072] staticChild.mem') with
      | some m => rd m 2048 == rd staticChild.mem 2048 && freeList m 3 == [2072] &&
          rd staticChild.mem' 2088 == 2048
      | none => false)
  checkCase "gen reuse N3': a smaller class is outside the invariant (header class 3, layout class 2)"
    (!smaller.hclass && smaller.planned == false && rd smaller.mem' 2072 == dynamicHeader 1 3 1 1 &&
      !heapLiveOk smaller.H' smaller.addr' smaller.mem')
  checkCase "gen reuse N3': physically harmless: the release returns the storage to class 3"
    (match mem? (run decP [2072] smaller.mem') with
      | some m => freeList m 3 == [2072] && freeList m 2 == [] | none => false)

/-- Negative controls: each breaks what the lemmas say when its premise is dropped. -/
def negativeTests : IO Unit := do
  for i in [noWordStr, noWordNat] do
    checkCase s!"negative control {i.name}: the plan's premises hold, hwords fails"
      (i.planned && !i.hwords)
    checkCase s!"negative control {i.name}: the rewrite stores 0, the new cell is not a LiveCell"
      (rd i.mem' 2104 == 0 && !heapLiveOk i.H' i.addr' i.mem')
    checkCase s!"negative control {i.name}: its release takes the 0 for a cell (page 0 unreadable: no return)"
      (stuckOrTrap (run decP [2096] (lowUnreadable i.mem')) &&
        (mem? (run decP [2096] (lowUnreadable same.mem'))).isSome)
  checkCase "negative control N1: a shared cell is not reused (reuseCell none, uniqueOf false, isUnique 0)"
    (reuseCell shared.H 1 shared.b' == none && !uniqueOf shared.H (.loc 1) &&
      vals? (run uniqueP [2072] shared.mem) == some [0])
  checkCase "negative control N1: rewritten anyway, l2's value changes and the caller's release frees the cell l2 names"
    (let forced := setCell heapA 1 (.live 1 .dyn (cons 9 (.loc 0)))
     heapA.value? (.loc 2) != forced.value? (.loc 2) &&
     match mem? (run decP [2072] shared.mem') with
     | some m => rd m (2096 + 16) == 2072 && (freeList m 3).contains 2072
     | none => false)
  checkCase "negative control N2: a static cell is not reused (reuseCell none, isUnique 0)"
    (reuseCell staticCell.H 0 staticCell.b' == none && vals? (run uniqueP [2048] staticCell.mem) == some [0])
  checkCase "negative control N3: at a larger class the premises hold but hclass"
    (bigger.hc && bigger.hb && bigger.hmass && bigger.hwords && !bigger.hclass && bigger.abstractOk)
  checkCase "negative control N3: the rewrite overwrites the shared neighbour's header; isUnique then answers 1 for it"
    (rd bigger.mem 2096 == dynamicHeader 2 3 1 2 && rd bigger.mem' 2096 == 13 &&
      vals? (run uniqueP [2096] bigger.mem) == some [0] && vals? (run uniqueP [2096] bigger.mem') == some [1] &&
      !frameOk bigger.mem bigger.mem' 2072 (cellBytesOf bigger.b.ctor) &&
      !heapLiveOk bigger.H' bigger.addr' bigger.mem')

def tests : IO Unit := do
  positiveTests
  limitTests
  negativeTests

end IxCCTests.Rt.Rc.GenReuseControls
