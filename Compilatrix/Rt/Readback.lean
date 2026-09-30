import Compilatrix.Rt.Layout
import Compilatrix.X86.State

/-! # Readback (04 §6, the Phase 1 fragment)

`Rt.readback` is the observation of the top theorem: a type-directed Lean
function from a result word and the final memory to `Sem.Obs`. Phase 1
reads first-order results: `Nat`, `Bool` and other enumerations, and
constructor trees in the region (04 §8.1).

* `nat`: an odd word `2n + 1` is `n` (an even one would be a bignat, Phase 4:
  `none`).
* `ind i`: an odd word `2k + 1` is the field-less constructor with tag `k`;
  an even word is a cell whose header (`read64?`, so an unreadable address
  is `none`) gives the tag and the field count, which must match the
  constructor's field types in `sig`; the fields are the words at `8 + 8j`,
  read back at their types. `fuel` bounds the depth (04: `(limit − base)/8`).

The header's `rc` and `cls` are not observed: Phase 1 cells are immortal,
Phase 2's are counted, and the observation is the same.

`Rt.observe` maps a `cx_result` (status and value) to an outcome, and the
text forms below (`FoTy.encode`, `Sig.encode`, `renderObs`) are the runtime
driver's contract (`fixtures/x86/runtime_driver.c` decodes with them). -/

namespace Compilatrix.Rt

open Compilatrix.Lir (Word)
open Compilatrix.Sem (Obs)

/-- First-order types (04 §6), as far as Phase 1 reads them. -/
inductive FoTy where
  | nat
  /-- An inductive of the signature (`Bool` and other enumerations too). -/
  | ind (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The inductives a result may contain: for each, its constructors by tag,
each with its field types in `Obs` order. -/
structure Sig where
  inds : List (List (List FoTy)) := []
  deriving DecidableEq, Repr, Inhabited

def Sig.ctor? (sig : Sig) (i tag : Nat) : Option (List FoTy) := (sig.inds[i]?).bind (·[tag]?)

/-- The observation of a result word (see the module note). -/
def readback (sig : Sig) : Nat → X86.Memory → FoTy → Word → Option Obs
  | _, _, .nat, w => if w &&& 1 == 1 then some (.nat (w >>> 1).toNat) else none
  | fuel, m, .ind i, w =>
    if w &&& 1 == 1 then
      let tag := (w >>> 1).toNat
      match sig.ctor? i tag with
      | some [] => some (.ctor tag [])
      | _ => none
    else
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match m.read64? w with
        | .error _ => none
        | .ok h =>
          let tag := ((h >>> 16) &&& 0xFFFF).toNat
          let scan := (h &&& 0xFF).toNat
          match sig.ctor? i tag with
          | some tys =>
            if tys.length == scan && 0 < scan then
              (tys.zipIdx.mapM fun (t, j) =>
                match m.read64? (w + UInt64.ofNat (8 + 8 * j)) with
                | .ok v => readback sig fuel m t v
                | .error _ => none).map (.ctor tag)
            else none
          | none => none

/-- A `cx_result` as an outcome: status 0 reads the value back; 1–3 are the
resource failures and 4 a trap (04 §6); anything else is `none`. -/
def observe (sig : Sig) (fuel : Nat) (m : X86.Memory) (ty : FoTy) (status value : Word) :
    Option (Sem.Result Obs) :=
  match status.toNat with
  | 0 => (readback sig fuel m ty value).map .ok
  | 1 => some (.resource .heap)
  | 2 => some (.resource .stack)
  | 3 => some (.resource .natOverflow)
  | 4 => some .trap
  | _ => none

/-! ## Text forms (the driver's contract) -/

/-- `n` for `Nat`, `i<k>` for inductive `k`. -/
def FoTy.encode : FoTy → String
  | .nat => "n"
  | .ind i => s!"i{i}"

/-- Inductives separated by `/`, each a run of constructors (by tag) in
parentheses with their field types separated by `,`: `Bool`, `Nat × Nat`
and `Option Nat` are `()()/(n,n)/()(n)`. -/
def Sig.encode (sig : Sig) : String :=
  "/".intercalate (sig.inds.map fun cs =>
    String.join (cs.map fun fs => "(" ++ ",".intercalate (fs.map FoTy.encode) ++ ")"))

mutual

/-- `n` for a `Nat`, `#t` for a field-less constructor, `#t(f,…)` for a
cell; other observations are not first-order results here. -/
def renderObs : Obs → String
  | .nat n => toString n
  | .ctor t [] => s!"#{t}"
  | .ctor t (f :: fs) => s!"#{t}(" ++ renderObs f ++ renderFields fs ++ ")"
  | .word w => s!"w{w.toNat}"
  | .bytes _ => "bytes"

def renderFields : List Obs → String
  | [] => ""
  | f :: fs => "," ++ renderObs f ++ renderFields fs

end

end Compilatrix.Rt
