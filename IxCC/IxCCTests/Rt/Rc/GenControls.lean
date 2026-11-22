import IxCC.Rt.Rc.Gen.Procs
import IxCC.Lir.Semantics
import IxCC.Lir.SplitEdges

/-! Executable controls of the general-layout procedures (`Rt.Rc.Gen`: allocation by layout
`alloc`, the release `dec`, the uniqueness test `isUnique`) over Lir semantics, run as
`Cfg.Rc.Native` emits procedures (critical edges split), with literal addresses and independent
expected free lists; an in-place rewrite of a unique cell; two negative controls (today's release
on a cell with a scalar word, a mutant of the general release) showing that the scalar and
field-order tests have teeth; and the general release's cost pinned in Lir steps, with its
difference from today's release (`Procs.dec`) per freed cell. No native claim (see
`GenNativeControls`). -/
open IxCC
open IxCC.Rt (maxTag headerLow)
open IxCC.Rt.Rc (CellLayout maxCount dynamicHeader maxClass maxCellWords classWords)

namespace IxCCTests.Rt.Rc.GenControls

abbrev Word := UInt64

/-! ## The test memory: context at 64 (bump word at 24, limit at 32, head of class `c` at
`64 + 8c`), readable and writable below 1 MiB. -/

def context : Word := 64
def memSize : Word := 1048576
def memory : X86.Memory :=
  { bytes := fun _ => 0, readable := fun a => a < memSize, writable := fun a => a < memSize }
def put (m : X86.Memory) (a w : Word) : X86.Memory := m.write64 a w
def rd (m : X86.Memory) (a : Word) : Word := m.read64 a
/-- Bump at 4096, limit at the end of the test memory. -/
def init : X86.Memory := put (put memory 24 4096) 32 memSize
def headAt (c : Nat) : Word := context + 8 * UInt64.ofNat c

/-- A cell of layout `L` with `refs` references at `a`: header, scanned words, scalar words
(`refs = 0` writes a static header). -/
def cell (m : X86.Memory) (a : Word) (L : CellLayout) (scanned scalars : List Word) (refs : Nat := 1) :
    X86.Memory :=
  let cls := (L.cls?).getD 0
  let hdr := if refs = 0 then UInt64.ofNat (headerLow L.nobj 0 L.tag + 2 ^ 32 * Rt.immortalRc)
    else dynamicHeader L.nobj cls L.tag refs
  let m := put m a hdr
  let m := (scanned.zipIdx).foldl (fun m (w, j) => put m (a + UInt64.ofNat (8 + 8 * j)) w) m
  (scalars.zipIdx).foldl (fun m (w, j) => put m (a + UInt64.ofNat (8 + 8 * (L.nobj + j))) w) m

/-- The words of class `c`'s free list, following links from its head (at most `n` steps). -/
def freeList (m : X86.Memory) (c : Nat) (n : Nat := 2000) : List Word :=
  go (rd m (headAt c)) n
where go (a : Word) : Nat → List Word
  | 0 => []
  | k + 1 => if a == 0 then [] else a :: go (rd m a) k

def single (f : Lir.Func) : Lir.Program := ({ funcs := #[f], main := 0 } : Lir.Program).splitCriticalEdges
def allocP (L : CellLayout) : Lir.Program := single (Rt.Rc.Gen.alloc L)
def decP : Lir.Program := single Rt.Rc.Gen.dec
def uniqueP : Lir.Program := single Rt.Rc.Gen.isUnique
def todayP : Lir.Program := single Rt.Rc.Procs.dec

def run (p : Lir.Program) (args : List Word) (m : X86.Memory) (clock : Nat := 1000000) : Lir.Outcome :=
  Lir.eval p clock args m context

def mem? : Lir.Outcome → Option X86.Memory
  | .ok (_, m) => some m
  | _ => none

def vals? : Lir.Outcome → Option (List Word)
  | .ok (vs, _) => some vs
  | _ => none

def checkCase (name : String) (b : Bool) : IO Unit := do
  unless b do throw (IO.userError name)
  IO.println ("PASS " ++ name)

def L2 : CellLayout := ⟨2, 0, 1⟩

/-! ## Graphs -/

/-- A 40-field parent (class 34) whose fields are 40 unique two-field children of immediates. -/
def wide40 : X86.Memory :=
  let kids := (List.range 40).map fun j => UInt64.ofNat (16384 + 64 * j)
  let m := kids.foldl (fun m a => cell m a L2 [1, 3] []) init
  cell m 8192 ⟨40, 0, 2⟩ kids []

/-- A chain of `n` cells, each one scanned field (the next cell) and one scalar word (its own
address, which looks like a pointer). -/
def scalarChain (n : Nat) : X86.Memory :=
  (List.range n).foldl (fun m j =>
    let a := UInt64.ofNat (8192 + 32 * j)
    let next : Word := if j + 1 = n then 1 else a + 32
    cell m a ⟨1, 1, 1⟩ [next] [a]) init

/-- Two scanned fields (unique children A at 4096 and B at 6144) and one scalar word naming a live
cell C at 8192, class 4. -/
def mixed : X86.Memory :=
  let m := cell (cell (cell init 4096 L2 [1, 3] []) 6144 L2 [1, 3] []) 8192 L2 [1, 3] []
  cell m 2048 ⟨2, 1, 4⟩ [4096, 6144] [8192]

/-- A mutant of the general release indexing the next field by `remaining` instead of
`scan − remaining`. -/
def mutant : Lir.Func :=
  let b : Lir.Block :=
    { body := #[.assign 12 (.arg (.v 9)),
        .assign 13 (.load .w64 .zero { base := some (.v 8), index := some (12, .eight), disp := 8 }),
        .assign 14 (.bin .sub .w64 (.v 9) (.imm 1)), .store .w32 { base := some (.v 8), disp := 4 } (.v 14)],
      term := .jump ⟨1, [.v 13, .v 8]⟩ }
  { Rt.Rc.Gen.dec with blocks := Rt.Rc.Gen.dec.blocks.set! 8 b }

/-- Today's layouts (class `fields + 1`), for the cost pins: a cell of `fields` at `a`. -/
def todayCell (m : X86.Memory) (a : Word) (fields : List Word) (refs : Nat := 1) : X86.Memory :=
  cell m a ⟨fields.length, 0, 1⟩ fields [] refs

/-- A list of `n` cons cells `[2j + 1, tail]` from 8192 (24 bytes each); its last tail is `last`. -/
def listGraph (n : Nat) (last : Word := 1) (m : X86.Memory := init) : X86.Memory × Word :=
  (List.range n).foldl (fun (m, tail) j =>
    let a := UInt64.ofNat (8192 + 24 * j)
    (todayCell m a [UInt64.ofNat (2 * j + 1), tail], a)) (m, last)

/-- A chain of `n` one-field cells from 8192. -/
def chainGraph (n : Nat) : X86.Memory × Word :=
  (List.range n).foldl (fun (m, tail) j =>
    let a := UInt64.ofNat (8192 + 16 * j)
    (todayCell m a [tail], a)) (init, 1)

/-- A complete binary tree of depth `d`, `k` fields per node (2: `l r`, 3: `l key r`, 4:
`l key val r`), cells allocated upward from `next`. -/
def treeGraph (k : Nat) : Nat → X86.Memory × Word → X86.Memory × Word × Word
  | 0, (m, next) => (m, next, 1)
  | d + 1, (m, next) =>
    let (m, next, l) := treeGraph k d (m, next)
    let (m, next, r) := treeGraph k d (m, next)
    let fields : List Word := match k with
      | 2 => [l, r]
      | 3 => [l, UInt64.ofNat (2 * d + 1), r]
      | _ => [l, UInt64.ofNat (2 * d + 1), 5, r]
    (todayCell m next fields, next + UInt64.ofNat (8 * (k + 1)), next)

def tree (k d : Nat) : X86.Memory × Word :=
  let (m, _, root) := treeGraph k d (init, 8192)
  (m, root)

/-- One cell of 31 immediates. -/
def wide31 : X86.Memory × Word :=
  (todayCell init 8192 ((List.range 31).map fun j => UInt64.ofNat (2 * j + 1)), 8192)

/-- One cell of 31 unique two-field children. -/
def wide31kids : X86.Memory × Word :=
  let kids := (List.range 31).map fun j => UInt64.ofNat (16384 + 24 * j)
  let m := kids.foldl (fun m a => todayCell m a [3, 5]) init
  (todayCell m 8192 kids, 8192)

/-- `n` list cells freed, then a stop at a shared tail (two references). -/
def sharedTail (n : Nat) : X86.Memory × Word :=
  listGraph n 4096 (todayCell init 4096 [7, 1] 2)

/-! ## Step counts -/

/-- The number of interpreter steps (statements and terminators) of a run to its return, and
the final memory; `none` if it does not return. -/
def stepCount (p : Lir.Program) (args : List Word) (m : X86.Memory) (fuel : Nat := 1000000) :
    Option (Nat × X86.Memory) := do
  let s ← Lir.State.initial p args m context
  go s 0 fuel
where
  go (s : Lir.State) (n : Nat) : Nat → Option (Nat × X86.Memory)
    | 0 => none
    | fuel + 1 => match Lir.step p s with
      | .next s' _ => go s' (n + 1) fuel
      | .done _ m => some (n + 1, m)
      | _ => none

def steps (p : Lir.Program) (g : X86.Memory × Word) : Nat :=
  ((stepCount p [g.2] g.1).map (·.1)).getD 0

def sameRun (g : X86.Memory × Word) : Bool :=
  match stepCount decP [g.2] g.1, stepCount todayP [g.2] g.1 with
  | some (_, a), some (_, b) => (List.range' 1 32).all fun c => freeList a c == freeList b c
  | _, _ => false

/-! ## The controls -/

def allocTests : IO Unit := do
  checkCase "gen alloc: 40-field cell is class 34, bump +384, header scan 40 class 34 tag 3"
    (match run (allocP ⟨40, 0, 3⟩) [] init with
      | .ok ([c], m) => c == 4096 && rd m 24 == 4096 + 384 && rd m 4096 == dynamicHeader 40 34 3 1
      | _ => false)
  checkCase "gen alloc: scalar-only box is class 2, 16 bytes"
    (match run (allocP ⟨0, 1, 5⟩) [] init with
      | .ok ([c], m) => c == 4096 && rd m 24 == 4112 && rd m 4096 == dynamicHeader 0 2 5 1
      | _ => false)
  checkCase "gen alloc: pop from class 34's list leaves the bump"
    (let m := put (put (put init (headAt 34) 8192) 8192 12288) 12288 0
     match run (allocP ⟨40, 0, 3⟩) [] m with
      | .ok ([c], m') => c == 8192 && rd m' (headAt 34) == 12288 && rd m' 24 == 4096 &&
          rd m' 8192 == dynamicHeader 40 34 3 1
      | _ => false)
  checkCase "gen alloc: exact fit of the 256-word class at the limit"
    (match run (allocP ⟨254, 1, 7⟩) [] (put init 32 (4096 + 2048)) with
      | .ok ([4096], m) => rd m 24 == 4096 + 2048 | _ => false)
  checkCase "gen alloc: one byte short of the 256-word class fails heap"
    (match run (allocP ⟨254, 1, 7⟩) [] (put init 32 (4096 + 2047)) with
      | .resource .heap => true | _ => false)
  checkCase "gen alloc: field-less, scan 255, tag past maxTag and a cell past 2^26 words trap"
    ([(⟨0, 0, 1⟩ : CellLayout), ⟨255, 0, 1⟩, ⟨1, 0, maxTag + 1⟩, ⟨0, maxCellWords, 1⟩].all
      fun L => match run (allocP L) [] init with | .trap => true | _ => false)
  checkCase "gen alloc: today's layouts give today's procedure"
    ((List.range' 1 31).all fun n => [0, 1, 7, maxTag].all fun t =>
      (Rt.Rc.Gen.alloc (CellLayout.ofFields n t)).blocks == (Rt.Rc.Procs.alloc n t).blocks)

def decTests : IO Unit := do
  checkCase "gen dec: a shared cell keeps its body"
    (match mem? (run decP [2048] (cell init 2048 L2 [7, 1] [] 2)) with
      | some m' => rd m' 2048 == dynamicHeader 2 3 1 1 && rd m' 2056 == 7 && freeList m' 3 == []
      | none => false)
  checkCase "gen dec: static cell and immediate untouched"
    (let m := cell init 2048 L2 [7, 1] [] 0
     match mem? (run decP [2048] m), mem? (run decP [1] m) with
      | some a, some b => rd a 2048 == rd m 2048 && rd b 24 == 4096 && freeList a 3 == []
      | _, _ => false)
  checkCase "gen dec: a repeated child is freed once, then the parent"
    (match mem? (run decP [4096] (cell (cell init 2048 L2 [7, 1] [] 2) 4096 L2 [2048, 2048] [])) with
      | some m' => freeList m' 3 == [4096, 2048]
      | none => false)
  checkCase "gen dec: a child with an outside reference survives"
    (match mem? (run decP [4096] (cell (cell init 2048 L2 [7, 1] [] 3) 4096 L2 [2048, 2048] [])) with
      | some m' => freeList m' 3 == [4096] && rd m' 2048 == dynamicHeader 2 3 1 1 && rd m' 2056 == 7
      | none => false)
  checkCase "gen dec: 40-field parent and 40 children recycled, children in field order"
    (match mem? (run decP [8192] wide40) with
      | some m' => freeList m' 34 == [8192] &&
          freeList m' 3 == ((List.range 40).reverse.map fun j => UInt64.ofNat (16384 + 64 * j))
      | none => false)
  checkCase "gen dec: a scalar-only box naming a live cell is recycled, the cell untouched"
    (let m := cell (cell init 4096 L2 [5, 7] []) 2048 ⟨0, 1, 9⟩ [] [4096]
     match mem? (run decP [2048] m) with
      | some m' => freeList m' 2 == [2048] && freeList m' 3 == [] && rd m' 4096 == dynamicHeader 2 3 1 1
      | none => false)
  checkCase "gen dec: scalar words that look like pointers are never followed"
    (let m := cell (cell (cell init 4096 L2 [5, 7] []) 6144 L2 [5, 7] []) 8192 L2 [1, 1] []
     let m := cell m 2048 ⟨1, 2, 4⟩ [8192] [4096, 6144]
     match mem? (run decP [2048] m) with
      | some m' => freeList m' 4 == [2048] && freeList m' 3 == [8192] &&
          rd m' 4096 == dynamicHeader 2 3 1 1 && rd m' 6144 == dynamicHeader 2 3 1 1
      | none => false)
  checkCase "gen dec: a static child under a freed parent is not written"
    (let m := cell (cell init 4096 L2 [5, 7] [] 0) 2048 L2 [4096, 1] []
     match mem? (run decP [2048] m) with
      | some m' => freeList m' 3 == [2048] && rd m' 4096 == rd m 4096
      | none => false)
  checkCase "gen dec: 254 scanned fields and a scalar word, class 44"
    (let m := cell init 8192 ⟨254, 1, 1⟩ ((List.range 254).map fun _ => 1) [8192]
     match mem? (run decP [8192] m) with
      | some m' => freeList m' 44 == [8192]
      | none => false)
  checkCase "gen dec: a chain of 100 cells with scalar words released iteratively"
    (match mem? (run decP [8192] (scalarChain 100)) with
      | some m' => freeList m' 3 == (List.range 100).map (fun j => UInt64.ofNat (8192 + 32 * j))
      | none => false)
  checkCase "gen dec: a freed cell is the next allocation of its class"
    (let m := cell init 2048 ⟨40, 0, 2⟩ ((List.range 40).map fun _ => 1) []
     match mem? (run decP [2048] m) with
      | some m' => match run (allocP ⟨40, 0, 5⟩) [] m' with
        | .ok ([c], m'') => c == 2048 && freeList m'' 34 == [] && rd m'' 2048 == dynamicHeader 40 34 5 1
        | _ => false
      | none => false)
  checkCase "gen dec: zero clock on a release that resumes a parent times out"
    (match run decP [4096] (cell (cell init 2048 L2 [7, 1] [] 2) 4096 L2 [2048, 2048] []) 0 with
      | .timeout => true | _ => false)

def uniqueTests : IO Unit := do
  let m := cell (cell (cell init 2048 L2 [1, 1] []) 4096 L2 [1, 1] [] 2) 6144 L2 [1, 1] [] 0
  checkCase "gen isUnique: immediate 0, unique 1, shared 0, static 0"
    (vals? (run uniqueP [1] m) == some [0] && vals? (run uniqueP [2048] m) == some [1] &&
      vals? (run uniqueP [4096] m) == some [0] && vals? (run uniqueP [6144] m) == some [0])
  checkCase "gen isUnique: writes nothing"
    ([1, 2048, 4096, 6144].all fun a => (mem? (run uniqueP [a] m)).map
      (fun m' => (List.range 1024).all fun j => rd m' (UInt64.ofNat (8 * j)) == rd m (UInt64.ofNat (8 * j))) == some true)
  checkCase "gen isUnique: the largest count is not unique"
    (vals? (run uniqueP [2048] (cell init 2048 L2 [1, 1] [] maxCount)) == some [0])

/-- The in-place rewrite of a unique cell (`l2 = 3 :: l1` at 6144 becomes `4 :: l1`): the bytes a
fresh allocation would write, nothing else changed, unique, and released with its new fields. -/
def inPlaceTests : IO Unit := do
  let n (k : Nat) : Word := UInt64.ofNat (2 * k + 1)
  let mem0 := cell (cell (cell init 2048 L2 [n 1, 1] []) 4096 L2 [n 2, 2048] [] 2) 6144 L2 [n 3, 4096] []
  let mem1 := cell mem0 6144 L2 [n 4, 4096] []
  checkCase "gen in place: the rewritten cell equals a fresh cell of the new body"
    ((List.range 3).all fun j =>
      rd mem1 (6144 + 8 * UInt64.ofNat j) == rd (cell init 6144 L2 [n 4, 4096] []) (6144 + 8 * UInt64.ofNat j))
  checkCase "gen in place: other cells, the bump word and every head unchanged"
    ((List.range 6).all (fun j => rd mem1 (2048 + 8 * UInt64.ofNat j) == rd mem0 (2048 + 8 * UInt64.ofNat j)) &&
      rd mem1 24 == rd mem0 24 && (List.range' 1 maxClass).all (fun c => rd mem1 (headAt c) == rd mem0 (headAt c)))
  checkCase "gen in place: the rewritten cell is unique"
    (vals? (run uniqueP [6144] mem1) == some [1])
  checkCase "gen in place: releasing it frees it and leaves its tail with one reference"
    (match mem? (run decP [6144] mem1) with
      | some m => freeList m 3 == [6144] && rd m 4096 == dynamicHeader 2 3 1 1 && rd m 2048 == rd mem1 2048
      | none => false)

/-- Negative controls: each fails the test the general release passes. -/
def negativeTests : IO Unit := do
  checkCase "gen dec on two scanned fields and a pointer-like scalar: A and B freed, C untouched"
    (match mem? (run decP [2048] mixed) with
      | some m' => freeList m' 4 == [2048] && freeList m' 3 == [6144, 4096] && rd m' 8192 == dynamicHeader 2 3 1 1
      | none => false)
  checkCase "negative control: today's release follows the scalar word (frees C, leaks B)"
    (match mem? (run todayP [2048] mixed) with
      | some m' => (freeList m' 3).contains 8192 && !(freeList m' 3).contains 6144
      | none => false)
  checkCase "negative control: a release indexing by remaining fails the field-order test"
    (match mem? (run (single mutant) [8192] wide40) with
      | some m' => (freeList m' 3).length == 40 &&
          freeList m' 3 != ((List.range 40).reverse.map fun j => UInt64.ofNat (16384 + 64 * j))
      | none => false)

/-- The general release's cost, pinned: its Lir steps on today's layouts (as emitted, critical
edges split), and the difference from today's release, exactly `3 − n` steps per freed cell of `n`
scanned fields (a branch on the scan byte and a reload of the class byte per freed cell, one
subtraction fewer per field after the first). A change to either procedure fails these pins. -/
def costTests : IO Unit := do
  let graphs : List (String × (X86.Memory × Word) × Nat × Int) :=
    -- name, graph, Gen.dec's steps, steps of Gen.dec minus today's
    [("list 10", (listGraph 10), 325, 10), ("list 100", (listGraph 100), 3205, 100),
     ("chain of 10 one-field cells", chainGraph 10, 215, 20),
     ("chain of 100 one-field cells", chainGraph 100, 2105, 200),
     ("tree of 2-field nodes, depth 6", tree 2 6, 2021, 63),
     ("tree of 3-field nodes, depth 6", tree 3 6, 2714, 0),
     ("tree of 4-field nodes, depth 6", tree 4 6, 3407, -63),
     ("31 immediates", wide31, 356, -28), ("31 unique children", wide31kids, 1348, 3),
     ("shared root", (todayCell init 4096 [7, 1] 2, 4096), 10, 0),
     ("list 10 then a shared tail", sharedTail 10, 330, 10),
     ("list 100 then a shared tail", sharedTail 100, 3210, 100)]
  for (name, g, gen, diff) in graphs do
    let s := steps decP g
    let t := steps todayP g
    checkCase s!"gen dec cost: {name}: {s} steps (today {t}), same free lists"
      (s == gen && (s : Int) - t == diff && sameRun g)
  -- per freed cell: 32 Lir steps for a 2-field cell, 21 for a 1-field cell
  checkCase "gen dec cost per freed cell: 32 steps a list cell, 21 a one-field cell"
    (steps decP (listGraph 100) - steps decP (listGraph 10) == 90 * 32 &&
      steps decP (chainGraph 100) - steps decP (chainGraph 10) == 90 * 21)

def tests : IO Unit := do
  allocTests
  decTests
  uniqueTests
  inPlaceTests
  negativeTests
  costTests

end IxCCTests.Rt.Rc.GenControls
