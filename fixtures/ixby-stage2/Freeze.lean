module
public import Lean
public import Ix.MultiStark.Verify.Source

/-! Build-time data construction. Every emitted declaration crosses Lean's
ordinary kernel `addDecl`. These commands are absent from the guest closure.
Native Lean code generation is unnecessary for an Ixon source fixture. -/

public section
open Lean Elab Command Term

elab "freeze_stage2_data " name:ident data:str : command => do
  let current ← getCurrNamespace
  let baseName := current ++ name.getId
  let text := data.getString.toUTF8.data
  if text.size % 2 != 0 then throwError "odd frozen byte encoding"
  let digit := fun c : UInt8 =>
    if c.toNat ≥ 48 && c.toNat ≤ 57 then some (c.toNat - 48)
    else if c.toNat ≥ 97 && c.toNat ≤ 102 then some (c.toNat - 87)
    else none
  let mut bytes : Array Nat := #[]
  for i in [:text.size / 2] do
    let some hi := digit text[2 * i]! | throwError "invalid frozen byte"
    let some lo := digit text[2 * i + 1]! | throwError "invalid frozen byte"
    bytes := bytes.push (16 * hi + lo)
  let byteType := Lean.mkConst ``UInt8
  let listType := mkApp (Lean.mkConst ``List [.zero]) byteType
  let cons := mkApp (Lean.mkConst ``List.cons [.zero]) byteType
  let chunks := (bytes.size + 127) / 128
  let mut tail := mkApp (Lean.mkConst ``List.nil [.zero]) byteType
  for chunk in (List.range chunks).reverse do
    let values := bytes.extract (chunk * 128) (min bytes.size ((chunk + 1) * 128))
    let body := values.foldr (fun value rest =>
      mkApp2 cons (Lean.mkConst (current.str s!"b{value}")) rest) tail
    let segment := baseName.str s!"tail{chunk}"
    liftCoreM <| addDecl (.defnDecl {
      name := segment, levelParams := [], type := listType, value := body
      hints := .regular 0, safety := .safe })
    tail := Lean.mkConst segment
  liftCoreM <| addDecl (.defnDecl {
    name := baseName, levelParams := [], type := mkApp (Lean.mkConst ``Array [.zero]) byteType
    value := mkApp2 (Lean.mkConst ``Array.mk [.zero]) byteType tail
    hints := .regular 0, safety := .safe })
  logInfo m!"froze {bytes.size} bytes as kernel-checked data: {baseName}"

elab "stage2_def " name:ident " : " type:term " := " value:term : command => do
  let fullName := (← getCurrNamespace) ++ name.getId
  let (type, value) ← liftTermElabM do
    let type ← elabType type
    let value ← elabTermEnsuringType value type
    synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars type, ← instantiateMVars value)
  liftCoreM <| addDecl (.defnDecl {
    name := fullName, levelParams := [], type, value, hints := .regular 0, safety := .safe })
