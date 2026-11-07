import IxCC.Cfg.Rc.Check
import IxCC.Rt.Rc.Procs
import IxCC.Rt.Lower
import IxCC.Rt.Switches
import IxCC.Lir.WellFormed

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native


structure Layout where
  sourceCount : Nat
  ctors : List Lam.CtorInfo

def Layout.incWrapper (l : Layout) := l.sourceCount
def Layout.decWrapper (l : Layout) := l.sourceCount + 1
def Layout.allocWrapper (l : Layout) (i : Nat) := l.sourceCount + 2 + i
def Layout.incProc (l : Layout) := l.sourceCount + 2 + l.ctors.length
def Layout.decProc (l : Layout) := l.incProc + 1
def Layout.allocProc (l : Layout) (i : Nat) := l.incProc + 2 + i
def Layout.init (l : Layout) := l.incProc + 2 + l.ctors.length

/-- Second argument is the gate-checked literal one; there is no incMany
implementation hidden here. The dummy result occupies only reserved registers. -/
def incrementWrapper (callee : Nat) : Lir.Func :=
  { name := "rc_marker_inc1", params := [0, 1], results := 1
    blocks := #[{ body := #[.call [] callee [.v 0]], term := .ret [.imm 1] }] }

def decrementWrapper (callee : Nat) : Lir.Func :=
  { name := "rc_marker_dec", params := [0], results := 1
    blocks := #[{ body := #[.call [] callee [.v 0]], term := .ret [.imm 1] }] }

/-- The reserved allocator result is never exposed before all fields have been
published. Field parameters retain their original registers across the call. -/
def allocationWrapper (callee fields : Nat) : Lir.Func :=
  { name := s!"rc_publish_{fields}", params := List.range fields, results := 1
    blocks := #[{
      body := (Lir.Stmt.call [fields] callee [] ::
        (List.range fields).map (fun i => .store .w64
          { base := some (.v fields), disp := Int.ofNat (8 * (i + 1)) } (.v i))).toArray
      term := .ret [.v fields] }] }

def ctorIndex (l : Layout) (key : Key.CtorKey) : Option Nat :=
  (l.ctors.zipIdx.find? fun p => p.1.key == key).map (·.2)

def consume (P : Program) (l : Layout) (i : Instr) : Except String Instr := do
  if reserved P.base.size i then
    match decode P.base.size i with
    | some (_, .inc _ 1) | some (_, .dec _) => return i
    | _ => throw "native RC accepts only well-formed inc1/dec markers"
  match i with
  | .bind x (.alloc c args kind) =>
    unless kind == .shared && c.nscalar == 0 && c.fieldKinds.length == c.nobj &&
        c.fieldKinds.all (· == .shared) && args.length == c.arity &&
        Fir.CtorInfo.ofKey P.base.ctors c.key == some c do
      throw "allocation is not a table-bound fully scanned shared constructor"
    if c.tag > Rt.maxTag then throw "constructor tag exceeds physical header"
    if P.base.known.natZero == some c.key || P.base.known.natSucc == some c.key then
      throw "Nat constructor allocation is not admitted"
    if c.fieldless then return i
    if args.contains (.var x) then throw "allocation overwrites an input field"
    if c.arity > 31 then throw "constructor exceeds first RC size-class fragment"
    let some index := ctorIndex l c.key | throw "missing allocation wrapper"
    return .bind x (.fir (.call (l.allocWrapper index) args))
  | _ => return i

def consumeFunction (P : Program) (l : Layout) (fd : Cfg.Fun) : Except String Cfg.Fun := do
  let blocks ← fd.blocks.mapM fun b => do
    let body ← b.body.mapM (consume P l)
    pure { b with body }
  return { fd with blocks }

/-- First explicit native lowering proposal. The accepted actual Cfg candidate
is consumed directly; source bodies are used only by its admission check. -/
def lower (config : Rt.Config) (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code)
    (P : Program) : Except String Rt.Lowered := do
  unless checkProgram F bodies P do throw "unchecked RC Cfg candidate"
  (Rt.checkSwitches P.base).mapError (·.render)
  let some main := P.base.exports.head? | throw "no exports"
  let l : Layout := ⟨P.base.size, P.base.ctors.filter (fun c => c.arity > 0)⟩
  unless l.ctors.all (fun c => decide (c.arity ≤ 31 ∧ c.tag ≤ Rt.maxTag)) do
    throw "constructor table exceeds first RC layout fragment"
  let pairs ← (List.range P.base.size).mapM fun f => do
    let some fd := P.base.fun? f | throw "missing admitted source function"
    let lowered ← consumeFunction P l fd
    pure (f, lowered)
  let consumed : Cfg.Program := { P.base with funs := Src.NatMap.ofList pairs }
  let named := P.base.exports.zipIdx.map fun (f, i) =>
    (f, Rt.Lower.symbolOf ((config.names[i]?).getD s!"root{i}"))
  let roots := named.map fun (f, symbol) => (f, (named.lookup f).getD symbol)
  let tables := { Rt.Lower.tables consumed with natPow := l.init + 1, natGcd := l.init + 2 }
  let funcs ← (Rt.Lower.functions tables consumed roots (List.range P.base.size)).mapError Rt.Error.render
  let wrappers := [incrementWrapper l.incProc, decrementWrapper l.decProc] ++
    l.ctors.zipIdx.map (fun (c, i) => allocationWrapper (l.allocProc i) c.arity)
  let procedures := [Rt.Rc.Procs.inc, Rt.Rc.Procs.dec] ++
    l.ctors.map (fun c => Rt.Rc.Procs.alloc c.arity c.tag)
  let program : Lir.Program := ({ funcs := (funcs ++ wrappers ++ procedures ++
    [Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd]).toArray, main } : Lir.Program).splitCriticalEdges
  program.check
  return {
    program
    init := l.init
    natPow := l.init + 1
    natGcd := l.init + 2
    roots }

end IxCC.Cfg.Rc.Native
