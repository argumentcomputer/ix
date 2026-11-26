import IxCC.Cfg.Rc.Bounds
import IxCC.Cfg.Rc.Syntax

set_option autoImplicit false
namespace IxCC.Cfg.Rc


def mapEq {α : Type} (eq : α → α → Bool) : Src.NatMap α → Src.NatMap α → Bool
  | .leaf, .leaf => true
  | .node v l r, .node w l' r' =>
    (match v, w with
      | none, none => true
      | some a, some b => eq a b
      | _, _ => false) && mapEq eq l l' && mapEq eq r r'
  | _, _ => false

def funEq (a b : Cfg.Fun) : Bool :=
  decide (a.key = b.key ∧ a.sig = b.sig ∧ a.blocks = b.blocks ∧
    a.regionFrame = b.regionFrame ∧ a.vars = b.vars)

def rawEq (a b : RawLayout) : Bool :=
  mapEq (fun x y => decide (x = y)) a.vars b.vars && decide (a.rets = b.rets)

def programEq (a b : Program) : Bool :=
  mapEq funEq a.base.funs b.base.funs && decide (a.base.size = b.base.size) &&
  decide (a.base.exports = b.base.exports) && decide (a.base.ctors = b.base.ctors) &&
  decide (a.base.known.natZero = b.base.known.natZero ∧
    a.base.known.natSucc = b.base.known.natSucc ∧
    a.base.known.boolFalse = b.base.known.boolFalse ∧
    a.base.known.boolTrue = b.base.known.boolTrue) && mapEq tableEq a.actions b.actions &&
  rawEq a.raw b.raw

/-- Reject a missing numbered source/candidate function, unsafe variable
namespace or malformed complete table before constructing any admitted map. -/
def entries (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code) :
    List Nat → Option (List (Nat × Cfg.Fun × ActionTable))
  | [] => some []
  | f :: rest => do
    let fd ← F.fun? f
    let body ← bodies.get? f
    let first := fd.vars + Own.Plain.slotBound body
    let lowered := lowerFunction F.size f fd body F.ctors
    if !functionBounds F.size first lowered then none else do
      let table ← collect F.size first (instructions lowered)
      let tail ← entries F bodies rest
      some ((f, lowered, table) :: tail)

def generate (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code) (raw : RawLayout := {}) :
    Option Program := do
  let es ← entries F bodies (List.range F.size)
  some {
    base := {
      funs := Src.NatMap.ofList (es.map fun e => (e.1, e.2.1))
      size := F.size
      exports := F.exports
      ctors := F.ctors
      known := F.known }
    actions := Src.NatMap.ofList (es.map fun e => (e.1, e.2.2))
    raw }

def checkProgram (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code) (candidate : Program)
    (borrows : Own.Plain.BorrowSigs := .leaf) (uniqs : Own.Plain.UniqSigs := .leaf) : Bool :=
  Own.Plain.checkOwned F bodies borrows uniqs &&
    match generate F bodies candidate.raw with
    | none => false
    | some expected => programEq expected candidate

end IxCC.Cfg.Rc
