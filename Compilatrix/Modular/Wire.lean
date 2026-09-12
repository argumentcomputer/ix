import Compilatrix.Modular.Build

/-! Bounded canonical records. Deserialization never constructs a certificate;
the records still have to pass `checkUnit` or `restore`. -/

namespace Compilatrix.Modular.Wire

open Ixon IxIR

def recordDomain : ByteArray := "compilatrix/source-unit-record/1\x00".toUTF8
def storeDomain : ByteArray := "compilatrix/source-unit-store/1\x00".toUTF8

def recordBytes (record : Record) : ByteArray :=
  recordDomain ++ Encoding.blob record.query ++
    Encoding.list targetEntryBytes record.output ++ Encoding.list Encoding.address record.order

def encodeRecord (limits : Limits) (record : Record) : Except String ByteArray := do
  let _ ← record.preflight limits
  let bytes := recordBytes record
  ensure (bytes.size ≤ limits.record.maxBytes) "source record byte limit"
  return bytes

def getExpr (bounds : Bounded.Limits) : Nat → GetM IxIR0.Expr
  | 0 => throw "source record expression depth limit"
  | depth + 1 => do
      match ← getU8 with
      | 0 => return .var (← Bounded.getNat bounds)
      | 1 => return .ref (← Decode.getAddress)
      | 2 => return .app (← getExpr bounds depth) (← getExpr bounds depth)
      | 3 => return .lam (← IxIR0.getUses) (← getExpr bounds depth)
      | 4 => return .letE (← IxIR0.getUses) (← getExpr bounds depth) (← getExpr bounds depth)
      | 5 => return .proj (← Bounded.getNat bounds) (← getExpr bounds depth)
      | 6 =>
          match ← getU8 with
          | 0 => return .lit (.nat (← Bounded.getNat bounds))
          | 1 => return .lit (.str (← Bounded.getString bounds))
          | _ => throw "source record literal tag"
      | 7 => return .erased
      | _ => throw "source record expression tag"

def getDecl (limits : Limits) : GetM IxIR0.Decl := do
  Decode.expectBytes IxIR0.Decl.addressDomain
  match ← getU8 with
  | 0 => return .defn (← IxIR0.getOwned) (← getExpr limits.record limits.maxExprDepth)
  | 1 => return .ctor (← Bounded.getNat limits.record) (← Bounded.getNat limits.record)
  | 2 =>
      let arity ← Bounded.getNat limits.record
      let natLit ← Decode.getBool
      let rules ← Bounded.getArray limits.record do
        return (⟨← Bounded.getNat limits.record,
          ← getExpr limits.record limits.maxExprDepth⟩ : IxIR0.RecRule)
      return .recursor arity natLit rules
  | 3 => return .extern (← Bounded.getNat limits.record)
  | _ => throw "source record declaration tag"

def getRecord (limits : Limits) : GetM Record := do
  Decode.expectBytes recordDomain
  let query ← Bounded.getBlob limits.record
  let output ← Bounded.getList limits.record do
    let address ← Decode.getAddress
    let bytes ← Bounded.getBlob limits.record
    match Decode.runCanonical (getDecl limits) IxIR0.Decl.preimage bytes with
    | .ok decl => pure (address, decl)
    | .error err => throw err
  let order ← Bounded.getList limits.record Decode.getAddress
  return ⟨query, output, order⟩

def decodeRecord (limits : Limits) (bytes : ByteArray) : Except String Record := do
  ensure (bytes.size ≤ limits.record.maxBytes) "source record byte limit"
  let record ← Decode.runCanonical (getRecord limits) recordBytes bytes
  let _ ← encodeRecord limits record
  return record

def storeBytes (records : List (String × Record)) : ByteArray :=
  storeDomain ++ Encoding.list (fun entry => Encoding.string entry.1 ++
    Encoding.blob (recordBytes entry.2)) records

def encodeStore (limits : Limits) (records : List (String × Record)) : Except String ByteArray := do
  ensure (records.length ≤ limits.maxUnits && (records.map (·.1)).eraseDups.length == records.length)
    "source store count or duplicate-name limit"
  let mut size := storeDomain.size + (Encoding.nat records.length).size
  for (name, record) in records do
    ensure (!name.isEmpty && name.utf8ByteSize ≤ 256) "source store unit name limit"
    let bytes ← encodeRecord limits record
    size := size + (Encoding.string name).size + (Encoding.nat bytes.size).size + bytes.size
    ensure (size ≤ limits.maxBytes) "source store byte limit"
  return storeBytes records

def getStore (limits : Limits) : GetM (List (String × Record)) := do
  Decode.expectBytes storeDomain
  let bounds := { limits.record with
    maxSequence := limits.maxUnits
    maxBlobBytes := limits.record.maxBytes }
  Bounded.getList bounds do
    let name ← Bounded.getString { bounds with maxBlobBytes := 256 }
    let bytes ← Bounded.getBlob bounds
    match decodeRecord limits bytes with
    | .ok record => return (name, record)
    | .error err => throw err

def decodeStore (limits : Limits) (bytes : ByteArray) : Except String (List (String × Record)) := do
  ensure (bytes.size ≤ limits.maxBytes) "source store byte limit"
  let records ← Decode.runCanonical (getStore limits) storeBytes bytes
  let _ ← encodeStore limits records
  return records

def readBounded (path : System.FilePath) (limit : Nat) : IO ByteArray :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    for _ in [:limit + 1] do
      let chunk ← handle.read (min 65536 (limit + 1 - bytes.size)).toUSize
      if chunk.size == 0 then return bytes
      bytes := bytes ++ chunk
      if bytes.size > limit then throw (IO.userError "source store file byte limit")
    throw (IO.userError "source store file byte limit")

end Compilatrix.Modular.Wire
