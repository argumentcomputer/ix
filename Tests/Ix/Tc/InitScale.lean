module

public import LSpec
public import Ix.Tc
public import Ix.KernelCheck
public import Tests.Ix.Tc.AnonDiff

/-!
Init-scale anon verdict differential (`tc-init`, ignored suite).

Two modes:
- `IX_TC_IXE=<path>` set: run the pure-Lean kernel and the Rust kernel over
  that `.ixe` file directly (developer-local full-Init runs; `.ixe` files
  are gitignored so nothing is assumed committed).
- Unset: compile a broad Init-representative closure through the Rust
  compiler in-memory and diff per-target verdicts, exactly like
  `tc-anon-diff` but at a much larger scale (hundreds of constants across
  Nat/List/Array/String/Fin/Option/Prod/Sum/Decidable/WellFounded/…).

Acceptance (P10): zero verdict mismatches vs `rsCheckAnonFFI`.
-/

namespace Tests.Tc.InitScale

open LSpec
open Ix.Tc

/-- Broad Init-representative seeds: arithmetic, containers, characters,
    strings, well-founded recursion, decidability, structures with
    projections, and higher-order combinators. -/
def initSeeds : List Lean.Name :=
  [ `Nat.add, `Nat.mul, `Nat.pow, `Nat.ble, `Nat.blt, `Nat.decEq,
    `Nat.mod, `Nat.div, `Nat.gcd, `Nat.sub, `Nat.succ_le_succ,
    `Nat.rec, `Nat.strongRecOn,
    `List.map, `List.foldl, `List.foldr, `List.append, `List.reverse,
    `List.length, `List.filter, `List.zip, `List.take, `List.drop,
    `Array.map, `Array.foldl, `Array.push, `Array.size, `Array.get,
    `String.append, `String.length, `Char.ofNat, `Char.toNat,
    `Option.map, `Option.bind, `Option.getD,
    `Prod.fst, `Prod.snd, `Prod.map,
    `Sum.inl, `Sum.inr, `Sum.map,
    `Fin.val, `Fin.mk, `Fin.add,
    `Bool.rec, `Bool.and, `Bool.or, `Bool.not,
    `Decidable.decide, `instDecidableEqNat, `instDecidableEqBool,
    `Eq.refl, `Eq.symm, `Eq.trans, `Eq.mpr, `congrArg, `congrFun,
    `Subtype.val, `Subtype.mk,
    `WellFounded.rec, `WellFounded.fix,
    `Acc.rec, `Acc.intro,
    `PSigma.mk, `Sigma.mk, `Exists.intro,
    `And.intro, `Or.inl, `Iff.intro,
    `Function.comp, `id, `flip ]

def envGatedSuite : TestSeq := Id.run do
  let mut ts : TestSeq := .done
  ts := ts ++ .individualIO "tc-init: anon verdict parity at scale" none (do
    match (← IO.getEnv "IX_TC_IXE") with
    | some path =>
      -- Whole-file differential: Rust verdicts vs pure-Lean verdicts.
      let bytes ← IO.FS.readBinFile path
      let rustRows ← Ix.KernelCheck.rsCheckAnonFFI path true ""
      let rust : Std.HashMap String (Option String) :=
        rustRows.foldl (init := {}) fun acc (addr, err?) =>
          acc.insert addr (err?.map (·.message))
      let leanResults ← match checkIxeBytesAnon bytes with
        | .ok rs => pure rs
        | .error e => return (false, 0, 0, some s!"Lean driver failed: {e}")
      let mut compared := 0
      let mut firstDiff : Option String := none
      for r in leanResults do
        let addrHex := toString r.addr
        match rust[addrHex]? with
        | none =>
          if firstDiff.isNone then
            firstDiff := some s!"{addrHex}: missing from Rust verdicts"
        | some rustErr? =>
          compared := compared + 1
          match rustErr?, r.err? with
          | none, none | some _, some _ => pure ()
          | some re, none =>
            if firstDiff.isNone then
              firstDiff := some s!"{addrHex}: rust FAIL ({re}) but lean PASS"
          | none, some le =>
            if firstDiff.isNone then
              firstDiff := some s!"{addrHex}: rust PASS but lean FAIL ({le})"
      if leanResults.size != rustRows.size && firstDiff.isNone then
        firstDiff := some s!"target counts differ: rust {rustRows.size} vs lean {leanResults.size}"
      return (firstDiff.isNone, compared, 0,
        firstDiff.map (s!"compared {compared}: " ++ ·))
    | none =>
      let env ← get_env!
      let (compared, skipped, diff?) ←
        Tests.Tc.AnonDiff.diffOnSeeds env "init-scale" initSeeds
      let msg := diff?.map (s!"compared {compared}, skipped {skipped}: " ++ ·)
      return (diff?.isNone && skipped == 0, compared, skipped, msg)) .done
  return ts

public def suite : List TestSeq := [envGatedSuite]

end Tests.Tc.InitScale
