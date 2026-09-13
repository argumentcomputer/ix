import Compilatrix.Ixby.Source
import Compilatrix.Ixon.CatalogIO

namespace Compilatrix.Ixby

/-- Record literal uses without expanding the sharing table. Every table entry
is scanned once alongside the declaration bodies. -/
private def literalUses : Nat → Ixon.Expr → Except String (List (Nat × Bool))
  | 0, _ => .error "Ixon literal scan depth limit"
  | fuel + 1, expr => match expr with
    | .nat index => .ok [(index.toNat, false)]
    | .str index => .ok [(index.toNat, true)]
    | .prj _ _ value => literalUses fuel value
    | .app f a | .lam _ f a | .all _ _ f a => do
        return (← literalUses fuel f) ++ (← literalUses fuel a)
    | .letE _ ty value body => do
        return (← literalUses fuel ty) ++ (← literalUses fuel value) ++ (← literalUses fuel body)
    | _ => .ok []

/-- Preserve both interpretations when identical raw bytes occur as a Nat
and a String. Each interpretation has already passed its own decoder. -/
private def mergeLiteral (previous value : Ixon.Eval.Blob) : Option Ixon.Eval.Blob :=
  match previous, value with
  | .natB n, .strB s | .strB s, .natB n => some (.dualB n s)
  | .dualB n s, .natB m | .natB m, .dualB n s =>
      if n == m then some (.dualB n s) else none
  | .dualB n s, .strB t | .strB t, .dualB n s =>
      if s == t then some (.dualB n s) else none
  | _, _ => if previous == value then some previous else none

/-- Interpret the catalog's checked blob bytes using each source occurrence's
literal kind. Raw-byte identity does not include the literal kind, so one
address may retain both checked interpretations. Nat zero is [0]. -/
def catalogBlobs (loaded : Ixon.Catalog.Loaded) (depth : Nat := 10000) :
    Except String (AddressEnv.Index Ixon.Eval.Blob) := do
  let payloads := AddressEnv.build loaded.blobs
  let mut values : Std.HashMap Ixon.Address Ixon.Eval.Blob := {}
  let mut entries := []
  for (_, constant) in loaded.constants do
    let exprs := constant.info.exprs ++ constant.sharing.toList
    for expr in exprs do
      for (index, stringKind) in ← literalUses depth expr do
        let some address := constant.refs[index]? | throw "Ixon literal reference is out of bounds"
        let some bytes := AddressEnv.lookup payloads address | throw s!"Ixon literal blob is missing: {address}"
        let value ← if stringKind then do
            let some value := String.fromUTF8? bytes | throw "Ixon String blob is not UTF-8"
            pure (Ixon.Eval.Blob.strB value)
          else do
            if bytes.isEmpty || (bytes.size > 1 && bytes[bytes.size - 1]! == 0) then
              throw "Ixon Nat blob is not canonical little endian"
            pure (.natB (bytes.data.foldr (fun byte n => n * 256 + byte.toNat) 0))
        if let some previous := values[address]? then
          let some merged := mergeLiteral previous value |
            throw "Ixon blob has conflicting literal values"
          values := values.insert address merged
        else
          entries := (address, value) :: entries
          values := values.insert address value
  return AddressEnv.build (entries.map fun (address, initial) =>
    (address, values.getD address initial))

#guard mergeLiteral (.natB 48) (.strB "0") == some (.dualB 48 "0")
#guard mergeLiteral (.strB "0") (.natB 48) == some (.dualB 48 "0")
#guard mergeLiteral (.dualB 48 "0") (.natB 48) == some (.dualB 48 "0")
#guard mergeLiteral (.dualB 48 "0") (.strB "0") == some (.dualB 48 "0")
#guard mergeLiteral (.dualB 48 "0") (.natB 49) == none
#guard mergeLiteral (.dualB 48 "0") (.strB "1") == none

private def literalFixture (order : List Ixon.Expr) : Ixon.Catalog.Loaded :=
  let address := Ixon.Address.replicate 0x30
  { manifest := {
      membersRoot := address
      contentRoot := address
      members := #[]
      storage := .fat #[] }
    pieces := #[]
    constants := order.map fun value => (address, {
      info := .defn { safety := .safe, kind := .defn, lvls := 0, typ := .sort 0, value }
      refs := #[address], sharing := #[], univs := #[.zero] })
    blobs := [(address, ⟨#[0x30]⟩)]
    stats := {} }

/-- The same raw byte is reached through both literal tags, in either scan
order. Evaluation, erasure, and the certificate checker agree on each value. -/
private def dualLiteralRegression (order : List Ixon.Expr) : Bool := Id.run do
  let .ok index := catalogBlobs (literalFixture order) | return false
  let address := Ixon.Address.replicate 0x30
  let ectx : Ixon.Eval.EvalCtx := {
    resolve := fun _ => none
    blobs := AddressEnv.lookup index }
  let tables : Erase.ETables := { refs := #[address] }
  let frame : Ixon.Eval.Frame := { refs := #[address] }
  let ictx : IxIR0.Ctx := { env := fun _ => none }
  let natEvaluated := match Ixon.Eval.eval ectx 10 frame [] (.nat 0) with
    | .ok (.litV (.natL n)) => n == 48
    | _ => false
  let strEvaluated := match Ixon.Eval.eval ectx 10 frame [] (.str 0) with
    | .ok (.litV (.strL s)) => s == "0"
    | _ => false
  return AddressEnv.lookup index address == some (.dualB 48 "0") &&
    natEvaluated && strEvaluated &&
    (Erase.eraseExpr (EraseValidator.eraseCtxOf ectx) 10 tables [] (.nat 0)).toOption ==
      some (.lit (.nat 48)) &&
    (Erase.eraseExpr (EraseValidator.eraseCtxOf ectx) 10 tables [] (.str 0)).toOption ==
      some (.lit (.str "0")) &&
    (EraseValidator.validateExpr ectx ictx (fun _ => none) none #[address]
      #[] none [] 10 (.nat 0) (.lit (.nat 48))).isOk &&
    (EraseValidator.validateExpr ectx ictx (fun _ => none) none #[address]
      #[] none [] 10 (.str 0) (.lit (.str "0"))).isOk

#guard dualLiteralRegression [.nat 0, .str 0, .nat 0, .str 0]
#guard dualLiteralRegression [.str 0, .nat 0, .str 0, .nat 0]

end Compilatrix.Ixby
