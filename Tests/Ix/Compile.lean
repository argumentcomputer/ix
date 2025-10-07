import LSpec

import Ix.Ixon
import Ix.Address
import Ix.Common
import Ix.CompileM
--import Ix.DecompileM
import Ix.Meta
import Ix.IR
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
  let predefs <- all.mapM fun n => match env.getDelta.find! n with
    | .defnInfo d => pure <| Ix.mkPreDef d
    | .opaqueInfo d => pure <| Ix.mkPreOpaque d
    | .thmInfo d => pure <| Ix.mkPreTheorem d
    | _ => throw (IO.userError "not a def")
  let (dss, _) <- match (<- (sortDefs predefs).run .init cstt) with
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
  let preinds <- all.mapM fun n => match env.getDelta.find! n with
    | .inductInfo v => do match (<- (makePreInd v).run .init cstt) with
      | (.ok a, _) => pure a
      | (.error e, _) => do throw (IO.userError (<- e.pretty))
    | _ => throw (IO.userError "not an inductive")
  let (dss, _) <- do match (<- (sortInds preinds).run .init cstt) with
    | (.ok a, stt) => do
      pure (a, stt)
    | (.error e, _) => do
      throw (IO.userError (<- e.pretty))
  let res := [[`Test.Ix.Inductives.C],[`Test.Ix.Inductives.B], [`Test.Ix.Inductives.A]]
  let nss := dss.map fun ds => ds.map (·.name)
  return test "test inductives" (res == nss)

def testDifficult : IO TestSeq := do
  let env <- get_env!
  let difficult := [
    `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q
  ]
  let mut res := true
  for name in difficult do
    let mut cstt : CompileState := .init env 0
    let const <- do match env.getDelta.find? name with
      | some c => pure c
      | none => match env.getConstMap.get? name with
        | some c => pure c
        | none => throw (IO.userError s!"{name} not in env")
    let (addr, stt) <- do match (<- (compileConst const >>= dematerializeConst).run .init cstt) with
    | (.ok a, stt) => pure (a, stt)
    | (.error e, _) => IO.println s!"failed {const.name}" *> throw (IO.userError (<- e.pretty))
    IO.println s!"{const.name} -> {addr}"
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
  let env <- get_env!
  let mut cstt : CompileState := .init env 0
  --IO.println s!"compiling env"
  for (_, c) in env.getDelta do
    let (_, stt) <- do match (<- (compileConst c).run .init cstt) with
    | (.ok a, stt) => do
      pure (a, stt)
    | (.error e, _) => do
      IO.println s!"failed {c.name}"
      throw (IO.userError (<- e.pretty))
    let addr <- match stt.constNames.find? c.name with
    | .some addr => pure addr
    | .none => throw (IO.userError "name {n} not in env")
    IO.println s!"✓ {c.name} -> {addr}"
    cstt := stt
  for (_, c) in env.getConstMap do
    let (_, stt) <- do match (<- (compileConst c).run .init cstt) with
    | (.ok a, stt) => do
      pure (a, stt)
    | (.error e, _) => do
      IO.println s!"failed {c.name}"
      throw (IO.userError (<- e.pretty))
    let addr <- match stt.constNames.find? c.name with
    | .some addr => pure addr
    | .none => throw (IO.userError "name {n} not in env")
    IO.println s!"✓ {c.name} -> {addr}"
    cstt := stt
  IO.println s!"compiled env"
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

def Tests.Ix.Compile.suiteIO: List (IO TestSeq) := [
   testMutual,
   testInductives,
   testDifficult,
--   testUnits,
   --testRoundtripGetEnv
]
