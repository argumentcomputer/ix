import LSpec

import Ix.Ixon
import Ix.Address
import Ix.Common
import Ix.CompileM
import Ix.DecompileM
import Ix.Cronos
import Ix.Meta
import Ix.Store
import Lean
import Tests.Ix.Fixtures
import Tests.Ix.Fixtures.Mutual
import Lean

open LSpec
open Ix
--open Ix.Decompile


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


--def addrOfName (name: Lean.Name) : IO Address := do
--  let env <- get_env!
--  let const := match (env.find? name) with
--    | .some c => c
--    | .none => env.getDelta.find! name
--  let ((a, _), _) <- (Ix.Compile.compileConst const).runIO env
--  return a

--def testUnits : IO TestSeq := do
--  let x <- addrOfName `Nat
--  IO.println s!"Nat is {x}"
--  let x <- addrOfName `Nat.add
--  IO.println s!"Nat.add is {x}"
--  let x <- addrOfName `Peano
--  IO.println s!"Peano is {x}"
--  let x <- addrOfName `Peano.add
--  IO.println s!"Peano.add is {x}"
--  return test "false" (true == false)

def testMutual : IO TestSeq := do
  let env <- get_env!
  let mut cstt : CompileState := .init env 0
  let all := (env.getDelta.find! `Test.Ix.Mutual.A).all
  let consts <- all.mapM fun n => match env.getDelta.find! n with
    | .defnInfo d => pure <| Ix.MutConst.mkDefn d
    | .opaqueInfo d => pure <| Ix.MutConst.mkOpaq d
    | .thmInfo d => pure <| Ix.MutConst.mkTheo d
    | _ => throw (IO.userError "not a def")
  let (dss, _) <- match (<- (sortConsts consts).run .init cstt) with
    | (.ok a, stt) => do
      pure (a, stt)
    | (.error e, _) => do
      throw (IO.userError (<- e.pretty))
  let res := [[`Test.Ix.Mutual.B, `Test.Ix.Mutual.C],[`Test.Ix.Mutual.A]]
  let nss := dss.map fun ds => ds.map (·.name)
  return test "test mutual" (res == nss)

def testInductives : IO TestSeq := do
  let env <- get_env!
  let mut cstt : CompileState := .init env 0
  --let delta := env.getDelta.filter fun n _ => namesp.isPrefixOf n
  --let consts := env.getConstMap.filter fun n _ => namesp.isPrefixOf n
  let all := (env.getDelta.find! `Test.Ix.Inductives.A).all
  let consts <- all.mapM fun n => match env.getDelta.find! n with
    | .inductInfo v => do match (<- (Ix.MutConst.mkIndc v).run .init cstt) with
      | (.ok a, _) => pure a
      | (.error e, _) => do throw (IO.userError (<- e.pretty))
    | _ => throw (IO.userError "not an inductive")
  let (dss, _) <- do match (<- (sortConsts consts).run .init cstt) with
    | (.ok a, stt) => do
      pure (a, stt)
    | (.error e, _) => do
      throw (IO.userError (<- e.pretty))
  let res := [[`Test.Ix.Inductives.C],[`Test.Ix.Inductives.B], [`Test.Ix.Inductives.A]]
  let nss := dss.map fun ds => ds.map (·.name)
  return test "test inductives" (res == nss)

def testEasy : IO TestSeq := do
  let env <- get_env!
  let easy := [
    `Nat.add_comm
  ]
  let mut res := true
  for name in easy do
    IO.println s!"⚙️ Compiling {name}"
    let mut cstt : CompileState := .init env 0
    let start <- IO.monoNanosNow
    let (addr, stt) <- do match (<- (compileConstName name).run .init cstt) with
    | (.ok a, stt) => pure (a, stt)
    | (.error e, _) => IO.println s!"failed {name}" *> throw (IO.userError (<- e.pretty))
    let done <- IO.monoNanosNow
    IO.println s!"✅ {addr}"
    IO.println s!"Elapsed {Cronos.nanoToSec (done - start)}"
  return test "easy compile roundtrip" (res == true)

def testDifficult : IO TestSeq := do
  let env <- get_env!
  let difficult := [
    `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q
  ]
  let mut res := true
  for name in difficult do
    let mut cstt : CompileState := .init env 0
    let (addr, stt) <- do match (<- (compileConstName name).run .init cstt) with
    | (.ok a, stt) => pure (a, stt)
    | (.error e, _) => IO.println s!"failed {name}" *> throw (IO.userError (<- e.pretty))
    IO.println s!"{name} -> {addr}"
    --cstt := stt
    --let mut store : Ixon.Store := {}
    --for (_,(a, b)) in cstt.names do
    --  let a_ixon <- (Store.readConst a).toIO
    --  let b_ixon <- (Store.readConst b).toIO
    --  store := store.insert a a_ixon
    --  store := store.insert b b_ixon
    --let denv := DecompileEnv.init cstt.names store
    --let dstt <- match decompileEnv.run denv default with
    --  | .ok _ s => pure s
    --    --IO.println s!"✓ {n} @ {anon}:{meta}"
    --  | .error e _ => do
    --    throw (IO.userError e.pretty)
    --IO.println s!"decompiled env"
    --for (n, (anon, meta)) in denv.names do
    --  let c <- match env.constants.find? n with
    --  | .some c => pure c
    --  | .none => throw (IO.userError "name {n} not in env")
    --  match dstt.constants.get? n with
    --  | .some c2 =>
    --    if c.stripMData == c2.stripMData
    --    then
    --      IO.println s!"✓ {n} @ {anon}:{meta}"
    --    else
    --      IO.println s!"× {n} @ {anon}:{meta}"
    --      IO.FS.writeFile "c.out" s!"{repr c.stripMData}"
    --      IO.FS.writeFile "c2.out" s!"{repr c2.stripMData}"
    --      res := false
    --      break
    --  | .none => do
    --    let e' := (DecompileError.unknownName default n).pretty
    --    throw (IO.userError e')
  return test "difficult compile roundtrip" (res == true)

def testRoundtripGetEnv : IO TestSeq := do
  IO.println s!"Getting env"
  let env <- get_env!
  let sccStart <- IO.monoNanosNow
  IO.println s!"Building condensation graph of env"
  let numConst := env.constants.map₁.size + env.constants.map₂.stats.numNodes
  let mut cstt : CompileState := .init env 0
  let mut dstt : DecompileState := default
  let sccEnd <- IO.monoNanosNow
  IO.println s!"Condensation graph in {Cronos.nanoToSec (sccEnd - sccStart)}"
  IO.println s!"Compiling env"
  let mut inConst := 1
  let allStart <- IO.monoNanosNow
  for (name, _) in env.constants do
    let start <- IO.monoNanosNow
    let (addr, stt) <- do match (<- (compileConstName name).run .init cstt) with
    | (.ok a, stt) => pure (a, stt)
    | (.error e, _) => do
      IO.println s!"failed {name}"
      throw (IO.userError (<- e.pretty))
    let done <- IO.monoNanosNow
    let pct := ((Float.ofNat inConst) / Float.ofNat numConst)
    let total := done - allStart
    IO.println s!"-> Compiled {pct * 100}%, {inConst}/{numConst},
    Elapsed {Cronos.nanoToSec (done - start)}/{Cronos.nanoToSec total},
    Remaining {((Cronos.nanoToSec total) / pct) / 60} min
    {name}
    {addr}"
    cstt := stt
    let denv := DecompileEnv.init cstt.constCache cstt.store
    let (name', stt) <- match DecompileM.run denv dstt (decompileNamedConst name addr) with
    | .ok (n,_) stt => pure (n, stt)
    | .error e _ => do
      IO.println s!"failed {name}"
      --IO.println s!"denv: {repr denv}"
      --let c := env.constants.find? name
      --IO.println s!"{repr c}"
      throw (IO.userError e.pretty)
    match env.constants.find? name, stt.constants.find? name' with
    | .some c, .some c' => if c == c then pure () else do
        IO.println s!"failed {name} {repr c} {repr c'}"
        throw (IO.userError "decompiled constant not equal")
    | .some _, .none => do
      throw (IO.userError s!"{name'} not found in dstt")
    | .none, _ => do
      throw (IO.userError "{name} not found in env")
    let done2 <- IO.monoNanosNow
    let total2 := done2 - allStart
    IO.println s!"<- Decompiled {pct * 100}%, {inConst}/{numConst},
    Elapsed {Cronos.nanoToSec (done2 - done)}/{Cronos.nanoToSec total},
    Remaining {((Cronos.nanoToSec total2) / pct) / 60} min
    {name}
    {addr}"
    inConst := inConst + 1
    dstt := stt
  let allDone <- IO.monoNanosNow
  IO.println s!"Compiled env in {Cronos.nanoToSec (allDone - allStart)}"
 -- IO.println s!"decompiling env"
 -- let mut store : Ixon.Store := {}
 -- for (_,(a, b)) in cstt.names do
 --   let a_ixon <- (Store.readConst a).toIO
 --   let b_ixon <- (Store.readConst b).toIO
 --   store := store.insert a a_ixon
 --   store := store.insert b b_ixon
 -- let denv := DecompileEnv.init cstt.names store
 -- let dstt <- match decompileEnv.run denv default with
 --   | .ok _ s => pure s
 --     --IO.println s!"✓ {n} @ {anon}:{meta}"
 --   | .error e _ => do
 --     throw (IO.userError e.pretty)
 -- IO.println s!"decompiled env"
 -- let mut res := true
 -- for (n, (anon, meta)) in denv.names do
 --   let c <- match env.constants.find? n with
 --   | .some c => pure c
 --   | .none => throw (IO.userError "name {n} not in env")
 --   match dstt.constants.find? n with
 --   | .some c2 =>
 --     if c.stripMData == c2.stripMData
 --     then
 --       IO.println s!"✓ {n} @ {anon}:{meta}"
 --     else
 --       IO.println s!"× {n} @ {anon}:{meta}"
 --       IO.FS.writeFile "c.out" s!"{repr c.stripMData}"
 --       IO.FS.writeFile "c2.out" s!"{repr c2.stripMData}"
 --       res := false
 --       break
 --   | .none => do
 --     let e' := (DecompileError.unknownName default n).pretty
 --     throw (IO.userError e')
 -- IO.println s!"input delta: {env.getDelta.toList.length}"
 -- IO.println s!"input env: {env.constants.toList.length}"
 -- IO.println s!"output env: {dstt.constants.toList.length}"
  return test "env compile roundtrip" true --(res == true)

--#eval (`_cstage2).isSuffixOf (`f.a._cstage2)
--open Lean Meta
--
--set_option pp.all true
--set_option pp.privateNames true
--set_option pp.fullNames true

--#eval show MetaM _ from do
--  getConstInfo `Lean.Language.instInhabitedDynamicSnapshot._closed_2._cstage2
--
--#eval show MetaM _ from do
--  getConstInfo `Lean.Language.instInhabitedDynamicSnapshot._closed_2._cstage2 
--
--def printPrivate (pre : Name) : CoreM (Array Name) := do
--  let env ← getEnv
--  let mut hits := #[]
--  for (n, _) in env.const2ModIdx do
--    if pre.isPrefixOf n then
--      hits := hits.push n
--  pure hits
--
--#eval do
--  let hits ← printPrivate `_private.Lean.Language.Basic
--  IO.println s!"found:"
--  for n in hits do
--    IO.println s!"{n}"
--
--#eval 
--  IO.println s!"{(mkPrivateNameCore `Lean.Language.Basic `Lean.Language.DynamicSnapShot)}"
--
--#eval show MetaM _ from do
--  let env ← getEnv
--  return env.const2ModIdx.size

def Tests.Ix.Compile.suiteIO: List (IO TestSeq) := [
  --testMutual,
  --testInductives,
  --testDifficult,
  --testUnits,
  --testEasy,
  testRoundtripGetEnv
]
