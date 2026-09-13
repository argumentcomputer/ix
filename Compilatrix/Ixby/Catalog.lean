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

/-- Interpret the catalog's checked blob bytes using the source occurrence's
literal kind. The current source evaluator has one kind per address, so mixed
Nat/String uses of the same blob are rejected explicitly. Nat zero is [0]. -/
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
          unless previous == value do throw "Ixon blob is used with conflicting literal kinds"
        else
          entries := (address, value) :: entries
          values := values.insert address value
  return AddressEnv.build entries

end Compilatrix.Ixby
