import IxC.Kernel.Roles
import IxC.Ixon.Codec
import Ix.Address.Pure

/-! # The specification digest

The specification set (`Ix.Kernel.Role.spec`, `Role.block`, `Role.deps`,
`specVersion`; `IxC/Kernel/Roles.lean`) is identified by a digest: BLAKE3
(`Blake3.Pure.hash`) of its canonical encoding (`specBytes`). The kernel
admits no hasher (`Ix.Kernel.Audit.kernelImportAllowlist`), so the digest is
computed here, in the root library. A claim commits to it beside the binding
hash (the role table's section hash, `Ix.Kernel.Admission.Binding`); the
audit below freezes its value, so it changes only on purpose, together with
`specVersion`.

## The encoding

Integers are TagN codes with no flag (`Ixon.putTagN 0`, `N0(n)` in
`docs/Ixon.md`), constructor tags single bytes. A key is a role's index in
`Role.all`: the specifications are closed over role keys, and the encoder
refuses any other key (`specBytes` fails), so the encoding checks the
closedness it relies on. Level parameters are positions; binder data are the
`PropWhen` datum and the two contracts' bits, a let's data its contract.

    specs     := N0(specVersion) N0(#roles) role*            (in `Role.all` order)
    role      := N0(index) spec N0(#block) index* N0(#deps) index*
    spec      := 00 N0(#decls) info*                         block
               | 01 N0(levels) expr                          anchor
               | 02 expr N0(#eqs) (N0(#hyps) expr* expr expr)*   ops
               | 03 N0(levels) (00 | 01 expr)                axiom (inert | typed)
               | 04 expr                                     identity
    info      := 00 val | 01 val expr hint | 02 val expr | 03 val caps
               | 04 val N0 N0 | 05 val N0 N0 N0(#rules) rule* | 06 table
    val       := key N0(#lps) N0* expr
    expr      := 00 N0 | 01 N0 expr | 02 level | 03 key N0(#us) level*
               | 04 expr expr | 05 expr expr binder | 06 expr expr binder
               | 07 expr expr expr let | 08 N0 | 09 N0(#bytes) byte* | 0A key N0 expr
    level     := 00 | 01 level | 02 level level | 03 level level | 04 N0
    binder    := pw contract result
    let       := bool(nonDep) (00 | 01)(value | borrowShared) contract
    pw        := 00 | 01 N0(#ps) N0*                          never | ifAllZero ps

`caps`, `rule`, `hint` and `table` spell their fields in declaration order
(`encInfo`). -/

namespace Ix.SpecDigest

open Ix.Kernel

abbrev EncM := StateT ByteArray (Except String)

def byte (b : UInt8) : EncM Unit := modify (·.push b)

def nat (n : Nat) : EncM Unit := do
  if n ≥ 2 ^ 64 then throw s!"integer {n} out of range"
  let bytes := Ixon.runPut (Ixon.putTagN 0 0 n.toUInt64)
  modify (· ++ bytes)

def bool (b : Bool) : EncM Unit := byte (if b then 1 else 0)

def list {α : Type} (xs : List α) (f : α → EncM Unit) : EncM Unit := do
  nat xs.length
  for x in xs do f x

/-- A role key, by the role's index; any other key is refused. -/
def key : Key md → EncM Unit
  | .role r => nat (Role.all.idxOf r)
  | k => throw s!"the specification mentions {k}, which is not a role key"

def level : Level → EncM Unit
  | .zero => byte 0
  | .succ u => do byte 1; level u
  | .max u v => do byte 2; level u; level v
  | .imax u v => do byte 3; level u; level v
  | .param i => do byte 4; nat i

def propWhen (pw : PropWhen) : EncM Unit :=
  match pw.toList? with
  | none => byte 0
  | some ps => do byte 1; list ps nat

def binder (m : BinderMeta) : EncM Unit := do
  propWhen m.pw
  byte m.contract.toBits
  byte m.result.toBits

def expr : Expr md → EncM Unit
  | .bvar i => do byte 0; nat i
  | .fvar i t => do byte 1; nat i; expr t
  | .sort u => do byte 2; level u
  | .const k us => do byte 3; key k; list us level
  | .app f a => do byte 4; expr f; expr a
  | .lam t b m => do byte 5; expr t; expr b; binder m
  | .forallE t b m => do byte 6; expr t; expr b; binder m
  | .letE t v b l => do
    byte 7; expr t; expr v; expr b
    bool l.contract.nonDep
    byte (match l.contract.kind with | .value => 0 | .borrowShared => 1)
    byte l.contract.binder.toBits
  | .lit (.natVal n) => do byte 8; nat n
  | .lit (.strVal s) => do byte 9; list s.toUTF8.toList byte
  | .proj s i e => do byte 10; key s; nat i; expr e

def val (cv : ConstantVal md) : EncM Unit := do
  key cv.name
  list cv.levelParams nat
  expr cv.type

def hint : ReducibilityHint → EncM Unit
  | .opaque => byte 0
  | .abbrev => byte 1
  | .regular h => do byte 2; nat h

def caps (c : IndCaps md) : EncM Unit := do
  bool c.eta
  match c.etaCtor with
  | none => byte 0
  | some k => do byte 1; key k
  nat c.etaParams
  nat c.etaFields
  bool c.unitlike
  nat c.unitParams
  bool c.ruleK
  propWhen c.sortZ

def fire : RecRuleFire md → EncM Unit
  | .inert => byte 0
  | .plain => byte 1
  | .nested lvls pins => do byte 2; list lvls level; list pins expr

def rule (r : RecRule md) : EncM Unit := do
  key r.ctor
  nat r.nfields
  nat r.ctorParams
  fire r.fire
  expr r.rhs
  bool r.k
  bool r.eta
  bool r.paramsBlind

def encInfo : ConstantInfo md → EncM Unit
  | .axiomInfo cv => do byte 0; val cv
  | .defnInfo cv v h => do byte 1; val cv; expr v; hint h
  | .thmInfo cv v => do byte 2; val cv; expr v
  | .indInfo cv c => do byte 3; val cv; caps c
  | .ctorInfo cv nP nF => do byte 4; val cv; nat nP; nat nF
  | .recInfo cv m p rules => do byte 5; val cv; nat m; nat p; list rules rule
  | .projInfo _ => throw "a projection table in a specification"

def spec : Spec md → EncM Unit
  | .block decls => do byte 0; list decls encInfo
  | .anchor levels type => do byte 1; nat levels; expr type
  | .ops type eqs => do
    byte 2
    expr type
    list eqs fun (hyps, l, r) => do list hyps expr; expr l; expr r
  | .axiom levels type => do
    byte 3
    nat levels
    match type with
    | none => byte 0
    | some t => do byte 1; expr t
  | .identity type => do byte 4; expr type

/-- **The specification set's canonical bytes.** -/
def specBytes : Except String ByteArray := do
  let act : EncM Unit := do
    nat specVersion
    list Role.all fun r => do
      nat (Role.all.idxOf r)
      spec (r.spec (md := .anon))
      list r.block fun s => nat (Role.all.idxOf s)
      list r.deps fun s => nat (Role.all.idxOf s)
  let ((), bytes) ← act.run .empty
  pure bytes

/-- **The specification digest**: BLAKE3 of `specBytes`. -/
def specDigest : Except String Address := do
  pure (Address.blake3Pure (← specBytes))

end Ix.SpecDigest

/-! ## The frozen value

`specVersion` 1. A change to the specification set changes these lines; it
is made on purpose, with `specVersion` (`IxC/Kernel/Audit/Roles.lean`). -/

/-- info: "8863 bytes" -/
#guard_msgs in
#eval match Ix.SpecDigest.specBytes with
  | .ok b => s!"{b.size} bytes"
  | .error e => s!"error: {e}"

/-- info: "70fedb021efa660e13618a7dbaa8f76ee0a91ac95fbd353ce05100248872e1ec" -/
#guard_msgs in
#eval match Ix.SpecDigest.specDigest with
  | .ok a => toString a
  | .error e => s!"error: {e}"
