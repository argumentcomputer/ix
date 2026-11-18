import Ix.IxVM.ClaimHarness
import Ix.KernelCheck.Step
import IxC.Kernel.Checker
import IxC.Kernel.Inductives.NativeInstall
import IxC.Kernel.Ixon.Prelude
import IxVMRefinement.Guard.CtorRaw
import IxVMRefinement.Guard.CertificateExampleData
import Tests.Ix.IxVM.GuardCertificateDefs

/-! # The guard certificate's example against the compiled structure (executed evidence)

`IxVM.Refinement.Guard.QuantifiedField.install_and_use` takes four facts about the structure
`P : Prop` with fields `h : ∀ n : Nat, n = n` and `k : True` as hypotheses: three readings of
the store's raw dictionary, and the success of IxC's table stage at the field sorts
`[imax 1 0, 0]`. This suite compiles the structure with Ix's compiler and checks the four by
evaluation. It is executed evidence, not a kernel proof: nothing here enters a theorem.

* The store is the compiled Ixon environment. `ctorRaw` is the function the theorem names;
  the dictionary's declared-type answer is evaluated through `rawTypeOf`, a compiled copy of
  `GuardRaw.answer` at `GuardRaw.typeRoot`, equal by `rfl` to the function the theorem names
  (`rawTypeOf_eq`). The readings are compared with the transcribed syntax by decidable
  equality of kernel expressions.
* IxC's path is its Ixon reader in the checker's order and the pure checker: the pinned basis
  and the inductive blocks before the structure are installed (definitions, theorems and
  axioms are not: the structure's block depends on none), then `nativeParts?` and
  `checkNativePass` at the block the reader produced, and `checkNativeTable` at the pass's
  record and constructor with the sorts `[imax 1 0, 0]`, on the environment the install
  without a recursor conses the table to. The stored table's guards are compared with
  `structProjGuards` at those sorts. The sorts IxC's own pass computed, and the guards its own
  complete install stores, are printed beside them.

Lines of the report start with `GC`; the exit code is `0` only if every check passed.
-/

namespace Tests.Ix.IxVM.GuardCertificate

open IxVM.Refinement
open IxVM.Refinement.Guard.QuantifiedField (eqType ctorType sorts)
open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-- `GuardRaw.answer`, as a compiled function. -/
def rawAnswer (blob : GuardRaw.Blobs) (root : Option GuardRaw.Root)
    (us : List Ix.Kernel.Level) : Option (Ix.Kernel.Expr .anon) := do
  let root ← root
  if us.length = root.levels then
    (GuardRaw.readRoot blob root).map
      (fun e => e.instantiateLevelParams (List.range root.levels) us)
  else none

theorem rawAnswer_eq : @rawAnswer = @GuardRaw.answer := rfl

/-- The raw dictionary's declared type at an address, as a compiled function. -/
def rawTypeOf (E : Ixon.Env) (a : Address) (us : List Ix.Kernel.Level) :
    Option (Ix.Kernel.Expr .anon) :=
  rawAnswer (fun x => E.blobs.get? x) (GuardRaw.typeRoot (IxVM.Consistency.recordOf E) a) us

/-- The compiled function is the dictionary the certificate is stated over. -/
theorem rawTypeOf_eq (E : Ixon.Env) (a : Address) (us : List Ix.Kernel.Level) :
    rawTypeOf E a us = (GuardRaw.ofStore E).typeOf (.id a) us := rfl

/-- One line of the report. -/
def gcLine (name : String) (ok : Bool) (detail : String) : IO Bool := do
  IO.println s!"GC\t{name}\t{if ok then "PASS" else "FAIL"}\t{detail}"
  return ok

/-- The store's three readings against the transcribed syntax. -/
def storeReadings (ixon : Ixon.Env) (aNat aEq aTrue aP B : Address) (i : Nat) : IO Bool := do
  let raw := Guard.ctorRaw ixon B i 0
  let wantRaw := ctorType aNat aEq aTrue aP
  let ok₁ ← gcLine "ctorRaw R B i 0 = ctorType" (decide (raw = some wantRaw))
    (if raw = some wantRaw then "equal, at the compiled addresses"
     else s!"read {repr raw}; transcribed {repr wantRaw}")
  let eq := rawTypeOf ixon aEq [.succ .zero]
  let wantEq := eqType (.succ .zero)
  let ok₂ ← gcLine "typeOf Eq [1] = eqType 1" (decide (eq = some wantEq))
    (if eq = some wantEq then "equal" else s!"read {repr eq}; transcribed {repr wantEq}")
  let tr := rawTypeOf ixon aTrue []
  let wantTr : Ix.Kernel.Expr .anon := .sort .zero
  let ok₃ ← gcLine "typeOf True [] = Sort 0" (decide (tr = some wantTr))
    (if tr = some wantTr then "equal" else s!"read {repr tr}; transcribed {repr wantTr}")
  return ok₁ && ok₂ && ok₃

/-- IxC's install path at the block the reader produced, and its table stage at the example's
sorts. -/
def tableStage (env : Ix.Kernel.Env .anon) (block : List (Ix.Kernel.ConstantInfo .anon))
    (nP : Nat) : IO Bool := do
  let some p₀ := Ix.Kernel.nativeParts? nP block
    | gcLine "checkNativeTable at [imax 1 0, 0]" false
        "nativeParts? declines the block the reader produced"
  let ops : Ix.Kernel.CheckerOps .anon (Ix.Kernel.CheckM .anon) := Ix.Kernel.pureOps .verified
  match Ix.Kernel.checkNativePass ops env p₀ (Ix.Kernel.nativeRawRec p₀) with
  | .error e => gcLine "checkNativeTable at [imax 1 0, 0]" false s!"checkNativePass: {e}"
  | .ok (q, settled) =>
    IO.println s!"GC\tinfo\tIxC's pass: nP={q.p.nP} nIdx={q.p.nIdx} \
      constructors={q.ctorsA.length} settled={settled}"
    IO.println s!"GC\tinfo\tIxC's own field sorts: {repr q.sortss}; equal to \
      [[imax 1 0, 0]]: {decide (q.sortss = [sorts])}"
    let [cA] := q.ctorsA
      | gcLine "checkNativeTable at [imax 1 0, 0]" false "the block has not one constructor"
    let shape ← gcLine "p.nP = 0, p.nIdx = 0, two fields"
      (q.p.nP == 0 && q.p.nIdx == 0 && cA.2 == 2)
      s!"nP={q.p.nP} nIdx={q.p.nIdx} fields={cA.2}"
    match Ix.Kernel.checkNative ops env p₀ with
    | .error e => IO.println s!"GC\tinfo\tIxC's own complete install: {e}"
    | .ok envN =>
      match envN.find? (Ix.Kernel.projTableName q.p.cvT.name) with
      | some (.projInfo t) =>
        IO.println s!"GC\tinfo\tIxC's own complete install stores the guards {repr t.guards}"
      | _ => IO.println "GC\tinfo\tIxC's own complete install stores no table"
    let envC := Ix.Kernel.consSumCtors q.p.nP q.ctorsA q.env₁
    match Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) q.p q.ctorsA [sorts] envC with
    | .error e => gcLine "checkNativeTable at [imax 1 0, 0]" false s!"{e}"
    | .ok env₂ =>
      match env₂.find? (Ix.Kernel.projTableName q.p.cvT.name) with
      | some (.projInfo tbl) =>
        let want := Ix.Kernel.structProjGuards cA.1.type q.p.nP cA.2 sorts
        let ok ← gcLine "checkNativeTable at [imax 1 0, 0]" (decide (tbl.guards = want))
          s!"ok; stored guards {repr tbl.guards}; structProjGuards at the sorts {repr want}"
        return shape && ok
      | _ => gcLine "checkNativeTable at [imax 1 0, 0]" false "ok, but no table is stored"

/-- A name of the source module. -/
def defName (n : String) : Lean.Name := `Tests.Ix.IxVM.GuardCertificateDefs ++ n.toName

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let names : Array Lean.Name :=
    #[defName "P", defName "P.rec", ``True, ``True.rec, ``Nat, ``Eq]
  let missing := names.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-guard-certificate] not in the environment: {missing}"
    return 1
  let ixon ← IxVM.ClaimHarness.loadSharedIxonEnv names leanEnv
  let addr (n : Lean.Name) : IO Address :=
    match ixon.getAddr? (Ix.Name.fromLeanName n) with
    | some a => pure a
    | none => throw (IO.userError s!"{n} is not compiled")
  let aP ← addr (defName "P")
  let aNat ← addr ``Nat
  let aEq ← addr ``Eq
  let aTrue ← addr ``True
  let some cP := IxVM.Consistency.recordOf ixon aP
    | throw (IO.userError "the record of P does not decode")
  let .iPrj prj := cP.info
    | throw (IO.userError "the record of P is not an inductive projection")
  let B := prj.block
  let i := prj.idx.toNat
  IO.println s!"GC\tinfo\taddresses: P={aP} block={B} member={i} Nat={aNat} Eq={aEq} \
    True={aTrue}"
  let readings ← storeReadings ixon aNat aEq aTrue aP B i
  -- IxC's reader, in the checker's order
  let constsArr := ixon.consts.toList.toArray
  let mut store : RecordStore := Std.HashMap.emptyWithCapacity constsArr.size
  for (address, lazy) in constsArr do
    store := store.insert address (← IO.ofExcept lazy.get)
  let table ← IO.ofExcept defaultTable
  let pre ← IO.ofExcept (preludeFor table)
  let hints := Hints.ofStore store ixon.anonHints
  let s := setup store (ixon.blobs[·]?) table pre hints.lookup
  let kP ← match s.cx.keyAt aP with
    | .ok k => pure k
    | .error _ => throw (IO.userError "the reader has no key for P")
  let ops : Ix.Kernel.CheckerOps .anon (Ix.Kernel.CheckM .anon) := Ix.Kernel.pureOps .verified
  let mut state : Ix.Kernel.Reader.State .anon := {}
  let mut env : Ix.Kernel.Env .anon := Ix.Kernel.Env.empty
  let mut found : Option (Ix.Kernel.Env .anon × List (Ix.Kernel.ConstantInfo .anon) × Nat) :=
    none
  let mut unread := 0
  let mut declined := 0
  let mut installed := 0
  for address in s.ordered do
    if found.isSome then break
    let some record := s.store[address]? | continue
    match readRecord s.cx state address record with
    | .error _ => unread := unread + 1
    | .ok read =>
      state := state.commit read
      for d in read.decls do
        match d with
        | .indDecl block nP =>
          if block.head?.map (·.name) == some kP then
            found := some (env, block, nP)
          else
            match Ix.Kernel.checkDecl .verified ops s.evidence env d with
            | .ok e => env := e; installed := installed + 1
            | .error _ => declined := declined + 1
        | .basisDecl _ =>
          match Ix.Kernel.checkDecl .verified ops s.evidence env d with
          | .ok e => env := e; installed := installed + 1
          | .error _ => declined := declined + 1
        | _ => pure ()
  IO.println s!"GC\tinfo\tbefore the structure: {installed} basis and inductive declarations \
    installed, {declined} declined, {unread} records not read"
  let stage ← match found with
    | none => gcLine "checkNativeTable at [imax 1 0, 0]" false
        "the reader produced no inductive block at the key of P"
    | some (envP, block, nP) => tableStage envP block nP
  let ok := readings && stage
  IO.println s!"[ixvm-guard-certificate] {if ok then "every check passed" else "a check FAILED"} \
    (executed evidence, not a kernel proof)"
  return if ok then 0 else 1

end Tests.Ix.IxVM.GuardCertificate
