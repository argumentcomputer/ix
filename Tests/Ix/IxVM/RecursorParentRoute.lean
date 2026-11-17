import Tests.Ix.IxVM.Harness
import IxC.Kernel.Admission
import IxC.Kernel.Cached.Installed
import Ix.Address.Pure

/-! # Native recursor dispatch uses the actual major-premise parent

A Let inside the first motive can hide its last binder from syntactic family discovery.
The native route must still reject a recursor whose actual parent belongs to a modeled
block. Canonical mutual recursors and plain native recursors remain accepted. A native
recursor with a Let in its motive's domain or in its result is refused at its header.
These fixtures construct authenticated Ixon records and execute the complete Aiur checker.
-/

namespace Tests.Ix.IxVM.RecursorParentRoute
open Ix.Kernel Ix.Kernel.Reader Tests.Ix.IxVM

def family (nat : _root_.Address) : Ixon.Constant :=
  let ind : Ixon.Inductive := {
    isUnsafe := false, lvls := 0, params := 0, indices := 1,
    typ := .all (.ref 0 #[]) (.sort 0), ctors := #[] }
  ⟨.muts #[.indc ind, .indc ind], #[], #[nat], #[.succ (.succ (.succ .zero))], #[]⟩

def canonicalType (member : UInt64) : Ixon.Expr :=
  let nat : Ixon.Expr := .ref 2 #[]
  let carrier (member index : UInt64) : Ixon.Expr := .app (.ref member #[]) (.var index)
  let motive (member : UInt64) : Ixon.Expr := .all nat (.all (carrier member 0) (.sort 1))
  let body : Ixon.Expr := .app (.app (.var (3 - member)) (.var 1)) (.var 0)
  .all (motive 0) (.all (motive 1) (.all nat (.all (carrier member 0) body)))

def standaloneType (wrapped : Bool) : Ixon.Expr :=
  let nat : Ixon.Expr := .ref 2 #[]
  let carrier (index : UInt64) : Ixon.Expr := .app (.ref 0 #[]) (.var index)
  let tail : Ixon.Expr := if wrapped then
    .leanLet true nat (.ref 3 #[]) (.all (carrier 1) (.sort 1))
    else .all (carrier 0) (.sort 1)
  let motive : Ixon.Expr := .all nat tail
  let body : Ixon.Expr := .app (.app (.var 2) (.var 1)) (.var 0)
  .all motive (.all nat (.all (carrier 0) body))

def recursor (motives : UInt64) (typ : Ixon.Expr) : Ixon.Recursor := {
  k := false, isUnsafe := false, lvls := 1, params := 0,
  indices := 1, motives := motives, minors := 0, typ := typ, rules := #[] }

def build : Except String (Ixon.Env × _root_.Address × Ixon.Constant × Ixon.Constant) := do
  let env ← IxVM.ClaimHarness.withRoleTable {} (← defaultTableBytes)
  let table ← defaultTable
  let some nat := table.addressOf? .nat | throw "missing Nat"
  let some zero := table.addressOf? .natZero | throw "missing Nat.zero"
  let fam ← IxVM.RecordSections.withSection env (family nat)
  let famAddress := _root_.Address.blake3 (Ixon.ser fam)
  let p : Ixon.Constant := ⟨.iPrj ⟨0, famAddress⟩, #[], #[], #[], #[]⟩
  let q : Ixon.Constant := ⟨.iPrj ⟨1, famAddress⟩, #[], #[], #[], #[]⟩
  let pAddress := _root_.Address.blake3 (Ixon.ser p)
  let qAddress := _root_.Address.blake3 (Ixon.ser q)
  let env := ((env.storeConst famAddress fam).storeConst pAddress p).storeConst qAddress q
  let canonicalRaw : Ixon.Constant :=
    ⟨.muts #[.recr (recursor 2 (canonicalType 0)), .recr (recursor 2 (canonicalType 1))],
      #[], #[pAddress, qAddress, nat, zero], #[.succ .zero, .var 0], #[]⟩
  let canonical ← IxVM.RecordSections.withSection env canonicalRaw
  let canonicalAddress := _root_.Address.blake3 (Ixon.ser canonical)
  let env := env.storeConst canonicalAddress canonical
  let rp : Ixon.Constant := ⟨.rPrj ⟨0, canonicalAddress⟩, #[], #[], #[], #[]⟩
  let rq : Ixon.Constant := ⟨.rPrj ⟨1, canonicalAddress⟩, #[], #[], #[], #[]⟩
  let env := (env.storeConst (_root_.Address.blake3 (Ixon.ser rp)) rp).storeConst
    (_root_.Address.blake3 (Ixon.ser rq)) rq
  let (env, report) ← IxVM.Model.generateReport env
  unless report.advice.size > 0 do
    throw s!"no model advice: {reprStr (report.blocks.map (fun (_, answer) => answer))}"
  let standaloneRaw : Ixon.Constant :=
    ⟨.recr (recursor 1 (standaloneType false)), #[], #[pAddress, qAddress, nat, zero],
      #[.succ .zero, .var 0], #[]⟩
  let plain ← IxVM.RecordSections.withSection env standaloneRaw
  let changed ← IxVM.RecordSections.withSection env
    { standaloneRaw with info := .recr (recursor 1 (standaloneType true)) }
  pure (env, canonicalAddress, plain, changed)

def makeCase (variant : Nat) : Except String Case := do
  let (env, canonicalAddress, plain, changed) ← build
  let (env, address) := if variant == 0 then (env, canonicalAddress) else
    let record := if variant == 1 then plain else changed
    let addr := _root_.Address.blake3 (Ixon.ser record)
    (env.storeConst addr record, addr)
  let context ← Ix.ClaimContext.ofEnv env
  let witness ← IxVM.ClaimHarness.buildClaimWitness env (.check context address none)
  let c : Case := {
    label := if variant == 0 then "canonical two-family recursors" else
      if variant == 1 then "plain standalone one-motive recursor of modeled parent" else
      "motive-Let standalone one-motive recursor of modeled parent"
    accept := variant == 0
    rejectsWith := if variant == 0 then none else if variant == 1 then
      some "model advice: the payload names another recursor family" else
      some "native recursor: the major premise belongs to a modeled block"
    witness := witness }
  -- the canonical family and the plain standalone recursor are recursors of a mutual family:
  -- the program refuses them before it reads a model, while it refuses such recursors
  pure (if variant ≤ 1 then c.throughModeledRecursor else c)

private def nativeType (motiveLet resultLet : Bool) : Ixon.Expr :=
  let nat : Ixon.Expr := .ref 1 #[]
  let carrier (index : UInt64) : Ixon.Expr := .app (.ref 0 #[]) (.var index)
  let motiveTail : Ixon.Expr := if motiveLet then
    .leanLet true nat (.ref 2 #[]) (.all (carrier 1) (.sort 1))
    else .all (carrier 0) (.sort 1)
  let body : Ixon.Expr := if resultLet then
    .leanLet true nat (.ref 2 #[]) (.app (.app (.var 3) (.var 2)) (.var 1))
    else .app (.app (.var 2) (.var 1)) (.var 0)
  .all (.all nat motiveTail) (.all nat (.all (carrier 0) body))

private def nativeCase (motiveLet resultLet : Bool) : Except String Case := do
  let env ← IxVM.ClaimHarness.withRoleTable {} (← defaultTableBytes)
  let table ← defaultTable
  let some nat := table.addressOf? .nat | throw "missing Nat"
  let some zero := table.addressOf? .natZero | throw "missing Nat.zero"
  let ind : Ixon.Inductive := {
    isUnsafe := false, lvls := 0, params := 0, indices := 1,
    typ := .all (.ref 0 #[]) (.sort 0), ctors := #[] }
  let fam ← IxVM.RecordSections.withSection env
    ⟨.muts #[.indc ind], #[], #[nat], #[.succ (.succ (.succ .zero))], #[]⟩
  let familyAddress := _root_.Address.blake3 (Ixon.ser fam)
  let projection : Ixon.Constant := ⟨.iPrj ⟨0, familyAddress⟩, #[], #[], #[], #[]⟩
  let projectionAddress := _root_.Address.blake3 (Ixon.ser projection)
  let env := (env.storeConst familyAddress fam).storeConst projectionAddress projection
  let record ← IxVM.RecordSections.withSection env
    ⟨.recr (recursor 1 (nativeType motiveLet resultLet)), #[],
      #[projectionAddress, nat, zero], #[.succ .zero, .var 0], #[]⟩
  let address := _root_.Address.blake3 (Ixon.ser record)
  let env := env.storeConst address record
  let context ← Ix.ClaimContext.ofEnv env
  let witness ← IxVM.ClaimHarness.buildClaimWitness env (.check context address none)
  pure {
    label := s!"native recursor: motive Let={motiveLet}, result Let={resultLet}"
    accept := !motiveLet && !resultLet
    rejectsWith := if motiveLet then some "recursor header: a let in a motive's domain"
      else if resultLet then some "recursor header: a let in the result" else none
    exercises := if motiveLet || resultLet then none else some "KernelCheck::nat_rec_check"
    witness := witness }

def run : IO UInt32 :=
  Tests.Ix.IxVM.runCases "recursor-parent-route"
    #[fun _ => makeCase 0, fun _ => makeCase 1, fun _ => makeCase 2,
      fun _ => nativeCase false false, fun _ => nativeCase false true,
      fun _ => nativeCase true false, fun _ => nativeCase true true]
    (jobs := 1) (circuit := some true)

end Tests.Ix.IxVM.RecursorParentRoute
