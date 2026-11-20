import Lean

/-!
# Declaration extraction for the premise-selection dataset

Run with Lean 4.34.1 (`lean341.sh --run Extract.lean OUT SCOPE-PREFIX MODULE…`), the toolchain
whose Mathlib build `ix compile` addresses. It imports the given modules at the private level, so
theorem bodies are present, and writes one record per line, fields separated by tabs. Names are
written only to be joined with their Ixon addresses (`ix diff` of the compiled `.ixe`); the
dataset itself is keyed by address.

```
mod   IDX NAME IMPORT-IDX,…                     every module, in import order
lib   NAME MOD-IDX DECL-IDX TYPE-CONSTS KINDS HEADS ARITY
                                                every theorem outside Init/Std/Lean
item  NAME PROOF-CONSTS AXIOMS DIRECT-NATIVE     theorems of modules under SCOPE-PREFIX
```

`TYPE-CONSTS` is `name*count,…` over the statement's expression tree, `KINDS` the counts of the
twelve expression node kinds in constructor order (`kindIdx`), `HEADS` the head constants of the
conclusion (under the leading binders) and of its last two arguments, `HEAD,LHS,RHS`, each empty
when not a constant application, `ARITY` the leading binders and how many of them are
non-dependent (hypotheses), `BINDERS,HYPS`, `PROOF-CONSTS` the set of constants in the
proof term, `AXIOMS` the axioms the theorem depends on transitively, and `DIRECT-NATIVE` is `1`
when the statement or proof refers directly to a constant marked `@[extern]` or
`@[implemented_by]`.
-/

open Lean

/-- Counts of constants and node kinds in an expression tree, up to a node budget. -/
structure Shape where
  consts : Std.HashMap Name Nat := {}
  kinds : Array Nat := Array.replicate 12 0
  budget : Nat := 200000

def kindIdx : Expr → Nat
  | .bvar .. => 0 | .fvar .. => 1 | .mvar .. => 2 | .sort .. => 3 | .const .. => 4 | .app .. => 5
  | .lam .. => 6 | .forallE .. => 7 | .letE .. => 8 | .lit .. => 9 | .mdata .. => 10 | .proj .. => 11

partial def Shape.visit (s : Shape) (e : Expr) : Shape := Id.run do
  if s.budget == 0 then return s
  let k := kindIdx e
  let mut s := { s with kinds := s.kinds.modify k (· + 1), budget := s.budget - 1 }
  match e with
  | .const n _ => s := { s with consts := s.consts.insert n (s.consts.getD n 0 + 1) }
  | .app f a => s := (s.visit f).visit a
  | .lam _ t b _ | .forallE _ t b _ => s := (s.visit t).visit b
  | .letE _ t v b _ => s := ((s.visit t).visit v).visit b
  | .mdata _ b => s := s.visit b
  | .proj _ _ b => s := s.visit b
  | _ => pure ()
  return s

/-- The leading binders, the non-dependent ones among them, and the conclusion. -/
def telescope : Expr → Nat → Nat → Nat × Nat × Expr
  | .forallE _ _ b _, n, h => telescope b (n + 1) (if b.hasLooseBVar 0 then h else h + 1)
  | .mdata _ b, n, h => telescope b n h
  | e, n, h => (n, h, e)

def headName (e : Expr) : String :=
  match e.consumeMData.getAppFn with
  | .const n _ => n.toString
  | _ => ""

/-- `HEAD,LHS,RHS` and `BINDERS,HYPS` of a statement. -/
def headsAndArity (t : Expr) : String × String :=
  let (n, h, c) := telescope t 0 0
  let args := c.consumeMData.getAppArgs
  let arg := fun (k : Nat) => if args.size ≥ k then headName args[args.size - k]! else ""
  (s!"{headName c},{arg 2},{arg 1}", s!"{n},{h}")

def isCore (m : Name) : Bool :=
  let r := m.getRoot
  r == `Init || r == `Std || r == `Lean

/-- Transitive axioms of a constant, memoized over the whole environment. -/
partial def axiomsOf (env : Environment) (n : Name) : StateM (Std.HashMap Name (Array Name)) (Array Name) := do
  if let some r := (← get).get? n then return r
  modify (·.insert n #[])
  let some ci := env.find? n | return #[]
  let r ← match ci with
    | .axiomInfo _ => pure #[n]
    | _ => do
      let mut acc : Array Name := #[]
      for c in ci.getUsedConstantsAsSet.toList do
        for a in ← axiomsOf env c do
          unless acc.contains a do acc := acc.push a
      pure acc
  modify (·.insert n r)
  return r

def native (env : Environment) (n : Name) : Bool :=
  isExtern env n || (Compiler.implementedByAttr.getParam? env n).isSome

def main (args : List String) : IO UInt32 := do
  let out :: scope :: mods := args | IO.eprintln "usage: Extract OUT SCOPE MODULE…"; return 2
  let scope := scope.toName
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map ({ module := ·.toName })) {} (loadExts := false)
  let h ← IO.FS.Handle.mk out .write
  let names := env.header.moduleNames
  let idx : Std.HashMap Name Nat := names.foldl (init := ({}, 0))
    (fun (m, i) n => (m.insert n i, i + 1)) |>.1
  for i in [:names.size] do
    let imps := env.header.moduleData[i]!.imports.filterMap (idx.get? ·.module)
    h.putStrLn s!"mod\t{i}\t{names[i]!}\t{",".intercalate (imps.toList.map toString)}"
  let mut memo : Std.HashMap Name (Array Name) := {}
  let mut items := 0
  let mut libs := 0
  for i in [:names.size] do
    if isCore names[i]! then continue
    let inScope := scope.isPrefixOf names[i]!
    let consts := env.header.moduleData[i]!.constNames
    for j in [:consts.size] do
      let n := consts[j]!
      let some (.thmInfo t) := env.find? n | continue
      if n.isInternalDetail then continue
      let s := (Shape.visit {} t.type)
      let tc := ",".intercalate (s.consts.toList.map fun (c, k) => s!"{c}*{k}")
      let ks := ",".intercalate (s.kinds.toList.map toString)
      let (hd, ar) := headsAndArity t.type
      h.putStrLn s!"lib\t{n}\t{i}\t{j}\t{tc}\t{ks}\t{hd}\t{ar}"
      libs := libs + 1
      if inScope then
        let pc := t.value.getUsedConstantsAsSet
        let (ax, m) := (axiomsOf env n).run memo
        memo := m
        let nat := pc.toList.any (native env) || s.consts.toList.any (native env ·.1)
        h.putStrLn s!"item\t{n}\t{",".intercalate (pc.toList.map toString)}\t{",".intercalate (ax.toList.map toString)}\t{if nat then 1 else 0}"
        items := items + 1
  h.flush
  IO.println s!"modules {names.size} library theorems {libs} scope theorems {items}"
  return 0
