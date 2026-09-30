import Compilatrix.Fir.Semantics

/-! # The abstract heap

Own's values and heap (design note 03 §3.2), shared with Cfg (03 §7) and
the runtime refinement (04 §8):

* an **immediate** is any value other than `loc`: a literal, a field-less
  constructor (`ctor0`, 06 S4) or □ (`erased`); it has no cell and no RC;
* a cell is `live rc mode body` or `dead`; `alloc` appends, and a dead cell
  is never reused (S3). The mode is `dyn` under the RC policy and `static`
  under the immortal one (`AllocPol`, 03 §4.4), where nothing is freed.

A `ctor0` carries its constructor info (key and tag), so `case` still
selects by key, as Fir does; 04 represents it by its tag (`2·tag + 1`).
Reserved cells (credits) and region cells are Phase 2. -/

namespace Compilatrix.Own

open Compilatrix.Sem (Obs)

inductive RVal where
  | loc (ℓ : Nat)
  | lit (l : Lam.Lit)
  | ctor0 (c : Fir.CtorInfo)
  | erased
  deriving DecidableEq, Repr, Inhabited

inductive OMode where
  | dyn
  | static
  deriving DecidableEq, Repr, Inhabited

structure Body where
  ctor : Fir.CtorInfo
  fields : List RVal
  deriving DecidableEq, Repr, Inhabited

inductive Cell where
  | live (rc : Nat) (m : OMode) (b : Body)
  | dead
  deriving DecidableEq, Repr, Inhabited

/-- Phase 1 allocates immortal (static) cells; Phase 2 counted ones. -/
inductive AllocPol where
  | rc
  | immortal
  deriving DecidableEq, Repr, Inhabited

def AllocPol.mode : AllocPol → OMode
  | .rc => .dyn
  | .immortal => .static

structure Heap where
  cells : Array Cell := #[]
  deriving DecidableEq, Repr, Inhabited

namespace Heap

def cell? (H : Heap) (ℓ : Nat) : Option Cell := H.cells[ℓ]?

/-- A fresh live cell with one reference, in the policy's mode. -/
def alloc (pol : AllocPol) (H : Heap) (b : Body) : RVal × Heap :=
  (.loc H.cells.size, { cells := H.cells.push (.live 1 pol.mode b) })

def size (H : Heap) : Nat := H.cells.size

end Heap

namespace RVal

/-- An immediate: no cell. -/
def isImm : RVal → Bool
  | .loc _ => false
  | _ => true

/-- A value as a constructor: a live cell's body, a field-less constructor,
or a `Nat` literal peeling with the pinned keys; a dead cell is stuck
(03 C5). -/
def asCtor (K : Lam.Known) (H : Heap) : RVal → Option (Key.CtorKey × List RVal)
  | .loc ℓ =>
    match H.cell? ℓ with
    | some (.live _ _ b) => some (b.ctor.key, b.fields)
    | _ => none
  | .ctor0 c => some (c.key, [])
  | .lit (.nat 0) => K.natZero.map (·, [])
  | .lit (.nat (n + 1)) => K.natSucc.map (·, [.lit (.nat n)])
  | _ => none

def shape : RVal → String
  | .loc ℓ => s!"loc {ℓ}"
  | .lit (.nat n) => s!"lit {n}"
  | .lit (.str _) => "str"
  | .ctor0 c => s!"ctor0#{c.tag}"
  | .erased => "erased"

end RVal

/-! ## Readback -/

mutual

/-- The Fir value a heap value denotes (`fuel` bounds the depth; cells only
point to older cells, so the heap size suffices). -/
def toFir (H : Heap) : Nat → RVal → Option Fir.Val
  | _, .lit l => some (.lit l)
  | _, .ctor0 c => some (.ctor c [])
  | _, .erased => some .erased
  | 0, .loc _ => none
  | fuel + 1, .loc ℓ =>
    match H.cell? ℓ with
    | some (.live _ _ b) => (toFirList H fuel b.fields).map (.ctor b.ctor)
    | _ => none

def toFirList (H : Heap) (fuel : Nat) : List RVal → Option (List Fir.Val)
  | [] => some []
  | v :: vs =>
    match toFir H fuel v, toFirList H fuel vs with
    | some w, some ws => some (w :: ws)
    | _, _ => none

end

/-- The Fir value of a heap value. -/
def Heap.value? (H : Heap) (v : RVal) : Option Fir.Val := toFir H (H.size + 1) v

/-- First-order readback, through the Fir value. -/
def Heap.readback (H : Heap) (v : RVal) : Option Obs := (H.value? v).bind Fir.readback

/-! ## The immortal invariant (03 §4.4, `ImmortalHolds`) -/

/-- Every cell is live and static, has as many fields as its constructor,
and its fields are immediates or older cells. -/
def Heap.immortalOk (H : Heap) : Bool :=
  (H.cells.toList.zipIdx).all fun (c, ℓ) =>
    match c with
    | .live _ .static b =>
      b.fields.length == b.ctor.arity && b.ctor.arity > 0 &&
      b.fields.all fun
        | .loc ℓ' => decide (ℓ' < ℓ)
        | _ => true
    | _ => false

end Compilatrix.Own
