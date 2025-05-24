import LSpec

import Ix.Ixon
import Ix.Address
import Ix.Common
import Ix.CompileM
import Ix.DecompileM
import Ix.Meta
import Ix.IR
import Lean
import Tests.Ix.Fixtures
import Lean

open LSpec
open Ix.Compile
open Ix.Decompile


namespace Test.Ix.Inductives

mutual
  unsafe inductive A | a : B → C → A
  unsafe inductive B | b : A → B
  unsafe inductive C | c : A → C
end

end Test.Ix.Inductives


namespace Test.Ix.Mutual


mutual
  unsafe def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + C n + 1

  unsafe def B : Nat → Nat
  | 0 => 0
  | n + 1 => A n + 1

  unsafe def C : Nat → Nat
  | 0 => 0
  | n + 1 => A n + 1
end

end Test.Ix.Mutual


def testMutual : IO TestSeq := do
  let env <- get_env!
  let mut cstt : CompileState := .init env 0
  let all := (env.getDelta.find! `Test.Ix.Mutual.A).all
  let predefs <- all.mapM fun n => match env.getDelta.find! n with
    | .defnInfo d => pure <| Ix.mkPreDefinition d
    | .opaqueInfo d => pure <| Ix.mkPreOpaque d
    | .thmInfo d => pure <| Ix.mkPreTheorem d
    | _ => throw (IO.userError "not a def")
  let (dss, _) <- match (sortDefs predefs).run (.init 200000) cstt with
    | .ok a stt => do
      pure (a, stt)
    | .error e _ => do
      throw (IO.userError (<- e.pretty))
  let res := [[`Test.Ix.Mutual.C, `Test.Ix.Mutual.B],[`Test.Ix.Mutual.A]]
  let nss := dss.map fun ds => ds.map (·.name)
  return test "test mutual" (res == nss)

def testInductives : IO TestSeq := do
  let env <- get_env!
  let mut cstt : CompileState := .init env 0
  --let delta := env.getDelta.filter fun n _ => namesp.isPrefixOf n
  --let consts := env.getConstMap.filter fun n _ => namesp.isPrefixOf n
  let all := (env.getDelta.find! `Test.Ix.Inductives.A).all
  let preinds <- all.mapM fun n => match env.getDelta.find! n with
    | .inductInfo v => match (makePreInductive v).run (.init 200000) cstt with
      | .ok a _ => pure a
      | .error e _ => do throw (IO.userError (<- e.pretty))
    | _ => throw (IO.userError "not an inductive")
  let (dss, _) <- match (sortInds preinds).run (.init 200000) cstt with
    | .ok a stt => do
      pure (a, stt)
    | .error e _ => do
      throw (IO.userError (<- e.pretty))
  let res := [[`Test.Ix.Inductives.C], [`Test.Ix.Inductives.B],[`Test.Ix.Inductives.A]]
  let nss := dss.map fun ds => ds.map (·.name)
  return test "test inductives" (res == nss)

def testRoundtripGetEnv : IO TestSeq := do
  let env <- get_env!
  let mut cstt : CompileState := .init env 0
  --IO.println s!"compiling env"
  for (_, c) in env.getDelta do
    let (_, stt) <- match (compileConst c).run (.init 200000) cstt with
    | .ok a stt => do
      --stt.store.forM fun a c => discard $ (Store.forceWriteConst a c).toIO
      pure (a, stt)
    | .error e _ => do
      IO.println s!"failed {c.name}"
      throw (IO.userError (<- e.pretty))
    let (anon, meta) <- match stt.names.find? c.name with
    | .some (a, m) => pure (a, m)
    | .none => throw (IO.userError "name {n} not in env")
    IO.println s!"✓ {c.name} -> {anon}:{meta}"
    cstt := stt
  IO.println s!"compiled env"
  IO.println s!"decompiling env"
  let denv := DecompileEnv.init cstt.names cstt.store
  let dstt <- match decompileEnv.run denv default with
    | .ok _ s => pure s
      --IO.println s!"✓ {n} @ {anon}:{meta}"
    | .error e _ => do
      throw (IO.userError e.pretty)
  IO.println s!"decompiled env"
  let mut res := true
  for (n, (anon, meta)) in denv.names do
    let c <- match env.constants.find? n with
    | .some c => pure c
    | .none => throw (IO.userError "name {n} not in env")
    match dstt.constants.find? n with
    | .some c2 =>
      if c.stripMData == c2.stripMData
      then
        IO.println s!"✓ {n} @ {anon}:{meta}"
      else
        IO.println s!"× {n} @ {anon}:{meta}"
        IO.FS.writeFile "c.out" s!"{repr c.stripMData}"
        IO.FS.writeFile "c2.out" s!"{repr c2.stripMData}"
        res := false
        break
    | .none => do
      let e' := (DecompileError.unknownName default n).pretty
      throw (IO.userError e')
  IO.println s!"input delta: {env.getDelta.toList.length}"
  IO.println s!"input env: {env.constants.toList.length}"
  IO.println s!"output env: {dstt.constants.toList.length}"
  return test "env compile roundtrip" (res == true)

def Tests.Ix.Compile.suiteIO: List (IO TestSeq) := [
   testMutual,
   testInductives,
   testRoundtripGetEnv
]
