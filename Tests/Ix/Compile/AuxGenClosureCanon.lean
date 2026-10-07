/-
  canon-closure-aux: an auxiliary's address does not depend on the
  compile set.

  Every auxiliary kind (`.rec`, `.casesOn`, `.recOn`, `.below`,
  `.brecOn.go`, `.brecOn`, `.brecOn.eq`, `.below.casesOn`) is compiled as
  one Ixon block holding the member of every class (and of every nested
  auxiliary, `_N`), and each name is a projection into it. A closure-only
  environment (`ix compile --consts`, any claim built from a dependency
  closure) holds only the members its seeds reach. Before the fix the
  compiler emitted only the members present, so a closure compile gave
  `A.brecOn` (and `.casesOn`, `.recOn`, `.brecOn.go`, `.brecOn.eq`,
  `.below` of a nested block, and everything that references them: the
  `noConfusion` family, `ctorIdx`, structural-recursion definitions)
  another address than the whole-environment compile. For an alpha-collapsed
  pair it compiled the non-representative's `.casesOn`/`.recOn`/`.brecOn`
  from Lean's source form, which the kernel rejects (`AppTypeMismatch`).

  For each fixture constant (the seed) this compiles the seed's closure and
  checks, for every name the closure output shares with the reference
  compile (the closure of all fixtures, where every family is complete),
  that the address is the reference's; and type-checks the seed with the
  Rust kernel. Two legs:

  - `collectDeps`: the closure producers' closure, which pulls an
    auxiliary's whole family (`Lean.auxFamilySiblings`) and a definition's
    `all`. Every address must match.
  - `raw`: the closure without family completion (`rawDeps`), which tests
    the compiler's per-family block membership on its own. Every address
    must match except a nested block's class `.brecOn.eq`: its canonical
    block holds `<all0>.brecOn_N.eq`, which needs `List.casesOn`, not in
    the raw closure, so the compiler refuses the block with "partial
    auxiliary family" (A0, WB-E3), and those seeds must be refused.
  - `pack`: `ix pack` (`rsPackEnv`) of the reference to each auxiliary
    seed keeps the seed's address and type-checks (`rsCheckIxonFFI`).

  Run with: `lake test -- --ignored canon-closure-aux`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.KernelCheck
import Ix.CompileM
import LSpec

open LSpec
open Ix.KernelCheck (CheckError rsCheckConstsFFI rsCheckIxonFFI)

namespace Tests.Ix.Compile.AuxGenClosureCanon

namespace Fx

-- plain mutual
mutual
inductive A where
  | nil
  | mk : B → A
inductive B where
  | mk : A → B → B
  | leaf
end

-- three-member mutual
mutual
inductive P where
  | p : Q → P
  | p0
inductive Q where
  | q : R → Q
inductive R where
  | r : P → R
  | r0
end

-- nested
inductive T where
  | mk : List T → T

-- mutual and nested
mutual
inductive C where
  | mk : List D → C
inductive D where
  | mk : C → D
  | leaf
end

-- indexed mutual
mutual
inductive Ev : Nat → Type where
  | z : Ev 0
  | s : Od n → Ev (n + 1)
inductive Od : Nat → Type where
  | s : Ev n → Od (n + 1)
end

-- Prop mutual (`.below` is an inductive; `.below.casesOn`)
mutual
inductive PE : Nat → Prop where
  | z : PE 0
  | s : PO n → PE (n + 1)
inductive PO : Nat → Prop where
  | s : PE n → PO (n + 1)
end

-- nested structure
structure Rose where
  val : Nat
  kids : List Rose

-- alpha-collapsing pair (one class)
mutual
inductive A2 where
  | mk : B2 → A2
  | nil
inductive B2 where
  | mk : A2 → B2
  | nil
end

-- Prop nested through a Prop-valued family (`.below_N` is an inductive,
-- `.brecOn_N` a theorem)
inductive Pw (R : Nat → Nat → Prop) : List Nat → List Nat → Prop where
  | nil : Pw R [] []
  | cons : R a b → Pw R as bs → Pw R (a :: as) (b :: bs)
inductive NV : Nat → Nat → Prop where
  | base : NV 0 0
  | node : Pw NV xs ys → NV xs.length ys.length

-- Prop with two nested auxiliaries in a non-canonical order, and
-- structural recursion over it (matchers on the `.below` constructors)
inductive NW : Nat → Nat → Prop where
  | base : NW 0 0
  | node : Pw NW xs ys → NW 0 1 ∧ NW 1 0 → NW xs.length ys.length
mutual
theorem NW.ok : NW a b → True
  | .base => trivial
  | .node h p => (fun _ _ => trivial) (pwNW_ok h) (andNW_ok p)
theorem pwNW_ok : Pw NW xs ys → True
  | .nil => trivial
  | .cons h hs => (fun _ _ => trivial) (NW.ok h) (pwNW_ok hs)
theorem andNW_ok : NW 0 1 ∧ NW 1 0 → True
  | ⟨h1, h2⟩ => (fun _ _ => trivial) (NW.ok h1) (NW.ok h2)
end

-- structural recursion over the mutual pair
mutual
def A.size : A → Nat
  | .nil => 0
  | .mk b => b.size + 1
def B.size : B → Nat
  | .mk a b => a.size + b.size + 1
  | .leaf => 0
end

end Fx

/-- Compile `consts` with the Rust compiler (the `ix compile --consts`
    path: fail-closed) and read the output back. -/
def compileClosure (env : Lean.Environment) (dir : System.FilePath)
    (tag : String) (consts : List (Lean.Name × Lean.ConstantInfo)) :
    IO (Except String Ixon.Env) := do
  let prepared ← IO.ofExcept <| Ix.Compile.prepareRegisteredConstants env consts
  let path := dir / s!"{tag}.ixe"
  let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared path.toString false
  if let some (n, r) := status.ungrounded[0]? then
    return .error s!"compile ({status.ungrounded.size} ungrounded): {n}: {r}"
  return Ixon.rsDeEnv (← IO.FS.readBinFile path)

/-- The closure WITHOUT auxiliary-family completion: `Ix.EnvScope.collectDeps`
    minus `Lean.auxFamilySiblings` (type, value, ctor/inductive links, `all`
    links, recursor rules). This is what the closure producers handed the
    compiler before, and what any other slice producer may still hand it:
    it holds `A.brecOn` without `B.brecOn`, `A2.casesOn` without the
    representative's `B2.casesOn`, `T.brecOn_1.go` without `T.brecOn_1`. -/
partial def rawDeps (env : Lean.Environment) (seeds : List Lean.Name)
    : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut needed : Std.HashSet Lean.Name := {}
  let mut worklist := seeds
  while !worklist.isEmpty do
    match worklist with
    | [] => break
    | n :: rest =>
      worklist := rest
      if needed.contains n then continue
      needed := needed.insert n
      if let some ci := env.constants.find? n then
        let mut refs : Lean.NameSet := ci.type.getUsedConstantsAsSet
        match ci with
        | .defnInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for m in v.all do refs := refs.insert m
        | .thmInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for m in v.all do refs := refs.insert m
        | .opaqueInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for m in v.all do refs := refs.insert m
        | .inductInfo v =>
          for c in v.ctors do
            refs := refs.insert c
            if let some cc := env.constants.find? c then
              for r in cc.type.getUsedConstantsAsSet do refs := refs.insert r
          for m in v.all do refs := refs.insert m
        | .ctorInfo v => refs := refs.insert v.induct
        | .recInfo v =>
          for m in v.all do refs := refs.insert m
          for rule in v.rules do
            for r in rule.rhs.getUsedConstantsAsSet do refs := refs.insert r
        | _ => pure ()
        for r in refs do
          if !needed.contains r then worklist := r :: worklist
  env.constants.toList.filter fun (n, _) => needed.contains n

/-- The compiler's introduced references (`Ix.EnvScope.introducedSupport`: the
    Pass 3 images' packing and rule constants, `PProd`, `And`, `True`, `Eq`, and
    the clique transport's prerequisites) with their closure, added to every
    closure this suite compiles: under Pass 3 (both compilers' only mode since
    M6R slice 6) the image of an alpha-collapsed block's recursor packs motives
    with `PProd`, so a closure without it is refused for a reason this suite
    does not test. (The legacy surgery needed none of them.) -/
def withSupport (env : Lean.Environment) (closure : List (Lean.Name × Lean.ConstantInfo)) :
    List (Lean.Name × Lean.ConstantInfo) :=
  let present : Std.HashSet Lean.Name := closure.foldl (fun s (n, _) => s.insert n) {}
  closure ++ (Ix.EnvScope.collectDeps env (Ix.EnvScope.introducedSupport env)).filter
    (!present.contains ·.1)

/-- One leg: per seed, compile `closureOf seed` (with `withSupport`), compare every shared name's
    address with `ref`, kernel-check the seed. A seed with `refused seed =
    some msg` must instead be refused by the compiler with `msg` in the
    error (and is not kernel-checked: nothing was written). -/
def runLeg (env : Lean.Environment) (dir : System.FilePath) (ref : Ixon.Env)
    (label : String) (seeds : Array Lean.Name)
    (closureOf : Lean.Name → List (Lean.Name × Lean.ConstantInfo))
    (refused : Lean.Name → Option String) : IO Nat := do
  let mut failed := 0
  for seed in seeds do
    let mut errs : Array String := #[]
    let closure := withSupport env (closureOf seed)
    let compiled ← compileClosure env dir s!"{label}-{seed}" closure
    if let some msg := refused seed then
      match compiled with
      | .error e =>
        unless (e.splitOn msg).length > 1 do
          errs := errs.push s!"refused, but without '{msg}': {e}"
      | .ok _ => errs := errs.push s!"expected a refusal with '{msg}', but it compiled"
      if !errs.isEmpty then
        failed := failed + 1
        for e in errs do IO.println s!"[canon-closure-aux] {label} FAIL {seed}: {e}"
      continue
    match compiled with
    | .error e => errs := errs.push e
    | .ok out =>
      do
        for (n, _) in closure do
          let ixn := Ix.Name.fromLeanName n
          match out.getAddr? ixn, ref.getAddr? ixn with
          | some a, some b =>
            if a != b then errs := errs.push s!"{n}: {a} in the closure, {b} in the reference"
          | none, _ => errs := errs.push s!"{n}: not in the closure output"
          | some _, none => pure ()
    let results ← rsCheckConstsFFI closure #[seed] #[true] false
    match results[0]? with
    | some none => pure ()
    | some (some (CheckError.kernelException m)) => errs := errs.push s!"kernel: {m}"
    | some (some (CheckError.compileError m)) => errs := errs.push s!"check-compile: {m}"
    | none => errs := errs.push "no kernel result"
    if !errs.isEmpty then
      failed := failed + 1
      for e in errs[:4] do IO.println s!"[canon-closure-aux] {label} FAIL {seed}: {e}"
      if errs.size > 4 then
        IO.println s!"[canon-closure-aux] {label} FAIL {seed}: … {errs.size - 4} more"
  IO.println s!"[canon-closure-aux] {label}: {seeds.size - failed}/{seeds.size} seeds ok"
  return failed

def suite : List TestSeq := [
  .individualIO "aux addresses are closure-invariant" none (do
    let env ← get_env!
    let fx := `Tests.Ix.Compile.AuxGenClosureCanon.Fx
    let seeds := (env.constants.toList.filterMap fun (n, _) =>
      if fx.isPrefixOf n && n != fx then some n else none).toArray.qsort
        (·.toString < ·.toString)
    let dir ← IO.FS.createTempDir
    let ref ← match ← compileClosure env dir "ref"
        (withSupport env (Ix.EnvScope.collectDeps env seeds.toList)) with
      | .ok e => pure e
      | .error e => throw (IO.userError s!"reference compile: {e}")
    -- Leg 1, the closure producers (`collectDeps`): every address is the
    -- reference's, every seed type-checks.
    let f1 ← runLeg env dir ref "collectDeps" seeds
      (fun s => Ix.EnvScope.collectDeps env [s]) (fun _ => none)
    -- Leg 2, the compiler on family-incomplete slices: same, except a
    -- nested block's class `.brecOn.eq`, whose canonical block needs
    -- `List.casesOn` (not in the raw closure): the compiler refuses the
    -- block, naming it (A0, WB-E3; it used to build the members present
    -- with a warning, at addresses differing from the whole compile).
    let nestedEq (s : Lean.Name) : Bool :=
      s.toString.endsWith ".brecOn.eq" &&
        [`T, `C, `D, `Rose].any (fun c => (fx ++ c).isPrefixOf s)
    let f2 ← runLeg env dir ref "raw" seeds (fun s => rawDeps env [s])
      (fun s => if nestedEq s then some "partial auxiliary family" else none)
    -- Leg 3, the pack-side closure (`ix pack`, `Env::prune_to_closure`):
    -- a block is one Ixon constant, so pruning the reference to an
    -- auxiliary keeps its whole block; the bundle must name the seed at the
    -- reference's address and type-check.
    let auxSeeds := seeds.filter fun s => match s with
      | .str _ last => ["rec", "casesOn", "recOn", "below", "brecOn", "go", "eq"].contains last
          || ["rec_", "below_", "brecOn_"].any (fun p => last.startsWith p)
      | _ => false
    let refPath := (dir / "ref.ixe").toString
    let mut f3 := 0
    for seed in auxSeeds do
      let mut errs : Array String := #[]
      let bundle := (dir / s!"pack-{seed}.ixe").toString
      match ← (Ixon.rsPackEnv refPath (toString seed) #[] bundle false false).toBaseIO with
      | .error e => errs := errs.push s!"pack: {e}"
      | .ok () =>
        match Ixon.rsDeEnv (← IO.FS.readBinFile bundle) with
        | .error e => errs := errs.push s!"read bundle: {e}"
        | .ok b =>
          let ixn := Ix.Name.fromLeanName seed
          if b.getAddr? ixn != ref.getAddr? ixn then
            errs := errs.push s!"bundle address {b.getAddr? ixn} ≠ reference {ref.getAddr? ixn}"
        let results ← rsCheckIxonFFI bundle #[seed] #[true] true ""
        match results[0]? with
        | some none => pure ()
        | some (some (CheckError.kernelException m)) => errs := errs.push s!"kernel: {m}"
        | some (some (CheckError.compileError m)) => errs := errs.push s!"check-compile: {m}"
        | none => errs := errs.push "no kernel result"
      if !errs.isEmpty then
        f3 := f3 + 1
        for e in errs do IO.println s!"[canon-closure-aux] pack FAIL {seed}: {e}"
    IO.println s!"[canon-closure-aux] pack: {auxSeeds.size - f3}/{auxSeeds.size} seeds ok"
    let n := 2 * seeds.size + auxSeeds.size
    let failed := f1 + f2 + f3
    return (failed == 0, n - failed, n,
      if failed == 0 then none else some s!"{failed} seed check(s) failed"))
    .done
]

end Tests.Ix.Compile.AuxGenClosureCanon
