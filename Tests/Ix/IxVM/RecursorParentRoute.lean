import Tests.Ix.IxVM.Harness
import IxCK.Kernel.Admission
import IxCK.Kernel.Cached.Installed
import Ix.Address.Pure

/-! # Native recursor dispatch uses the actual major-premise parent

A Let inside the first motive can hide its last binder from syntactic family discovery.
The native route must still reject a recursor whose actual parent belongs to a modeled
block. Canonical mutual recursors remain accepted. (Native header-let controls live in
`Tests.Ix.IxVM.ShapeGuards`.)
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

def makeCaseFrom (built : Ixon.Env × _root_.Address × Ixon.Constant × Ixon.Constant)
    (variant : Nat) : Except String Case := do
  let (env, canonicalAddress, plain, changed) := built
  let (env, address) := if variant == 0 then (env, canonicalAddress) else
    let record := if variant == 1 then plain else changed
    let addr := _root_.Address.blake3 (Ixon.ser record)
    (env.storeConst addr record, addr)
  let context ← Ix.ClaimContext.ofEnv env true
  let witness ← IxVM.ClaimHarness.buildClaimWitness env (.check context address none)
  pure {
    label := if variant == 0 then "canonical two-family recursors" else
      if variant == 1 then "plain standalone one-motive recursor of modeled parent" else
      "motive-Let standalone one-motive recursor of modeled parent"
    accept := variant == 0
    rejectsWith := if variant == 0 then none else if variant == 1 then
      some "model advice: the payload names another recursor family" else
      some "native recursor: the major premise belongs to a modeled block"
    witness := witness }

def makeCase (variant : Nat) : Except String Case := do
  makeCaseFrom (← build) variant

def run : IO UInt32 := do
  let built ← IO.ofExcept build
  Tests.Ix.IxVM.runCases "recursor-parent-route"
    #[fun _ => makeCaseFrom built 0,
      fun _ => makeCaseFrom built 1,
      fun _ => makeCaseFrom built 2]
    (circuit := some true)

end Tests.Ix.IxVM.RecursorParentRoute
