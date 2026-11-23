import IxCC.Cfg.Rc.Check
import IxCC.Cfg.Rc.Inline
import IxCC.Rt.Lower
import IxCC.Rt.Switches
import IxCC.Lir.WellFormed

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native

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
    if c.arity > Rt.maxFields then throw "constructor exceeds the counted heap's scanned fields"
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
  unless l.ctors.all (fun c => (Rt.Rc.CellLayout.ofFields c.arity c.tag).ok) do
    throw "constructor table has a layout the counted heap does not allocate"
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
  let procedures := [Rt.Rc.Procs.inc, Rt.Rc.Gen.dec] ++
    l.ctors.map (fun c => Rt.Rc.Gen.alloc (Rt.Rc.CellLayout.ofFields c.arity c.tag))
  let raw : Lir.Program := { funcs := (funcs ++ wrappers ++ procedures ++
    [Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd]).toArray, main }
  let program : Lir.Program := (Inline.inlineProgram l raw).splitCriticalEdges
  program.check
  return {
    program
    init := l.init
    natPow := l.init + 1
    natGcd := l.init + 2
    roots }

end IxCC.Cfg.Rc.Native
