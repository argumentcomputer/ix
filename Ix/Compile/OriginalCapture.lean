module
public import Ix.CompileM
public import Ix.Compile.OriginalData

public section

namespace Ix.Compile.OriginalData

open Ix.CompileM

/-- Read only the original compilation's hint cache. Non-definition records
have a known absent hint, even when their published image is a definition. -/
def capturedHints (cache : BlockState) (name : Ix.Name) (block record : Ixon.Constant) :
    Option (Option Lean.ReducibilityHints) :=
  let definition (kind : Ix.DefKind) :=
    let hint := cache.defHints.get? name
    if kind == .defn then hint.map some else some hint
  match record.info with
  | .defn d => definition d.kind
  | .dPrj p =>
    match block.info with
    | .muts members =>
      match members[p.idx.toNat]? with
      | some (.defn d) => definition d.kind
      | _ => none
    | _ => none
  | _ => some none

/-- Capture the already-produced bytes without adding them to checked constants.
Only actual projections retain the block, shared across all member receipts.
Collapsed standalone aliases also share the block buffer after a byte comparison.
The callback binds each receipt to the name's successful publication address. -/
def captureOriginals (lo : Ix.Name) (result : BlockResult) (cache : BlockState)
    (published : Ix.Name → Option Address) : OriginalStaging :=
  let block : Ixon.RawBlob := ⟨result.blockAddr, result.blockBytes⟩
  if result.projections.isEmpty then
    (published lo).toArray.map fun addr =>
      { name := lo, published := addr, original := block
        hints := capturedHints cache lo result.block result.block }
  else
    result.projections.filterMap fun (name, record, _) =>
      (published name).map fun addr =>
        let bytes := Ixon.ser record
        let raw := if bytes == block.bytes then block
          else ⟨Address.admissionHash bytes, bytes⟩
        let block? := match record.info with
          | .dPrj _ | .iPrj _ | .cPrj _ | .rPrj _ => some block
          | _ => none
        { name, published := addr, original := raw, block?
          hints := capturedHints cache name result.block record }

end Ix.Compile.OriginalData

end
