import Ix.Meta
import Ix.EnvScope
import Ix.KernelCheck
import Tests.Ix.Kernel.FocusedLeanCheck
import Ix.CompileM
import Ix.CompileCertified
import Ix.RoleBinding.Compile
import Ix.Resource.Typing
import LSpec

/-!
  canon-closure-aux: an auxiliary's address does not depend on the
  compile set.

  Lean declares every auxiliary kind (`.rec`, `.casesOn`, `.recOn`,
  `.below`, `.brecOn.go`, `.brecOn`, `.brecOn.eq`, `.below.casesOn`) for each
  member of a block (and of every nested auxiliary, `_N`), and the compiler
  compiles them as Lean declares them: the recursors and a Prop `.below`
  family as one Ixon block with each name a projection into it, every
  definition as its own constant. A closure-only environment (any claim
  built from a dependency closure) holds only the members its seeds reach,
  and the auxiliaries it holds must compile to the whole-environment
  compile's addresses, as must everything that references them (the
  `noConfusion` family, `ctorIdx`, structural-recursion definitions).

  For each fixture constant (the seed) this compiles the seed's closure and
  checks, for every name the closure output shares with the reference
  compile, that the address is the reference's. The reference is the
  selected closure of all fixtures (`collectSelectedDeps`, where every
  family is complete), compiled and bound as `ix compile --consts` compiles
  and binds it (`Ix.RoleBinding.Compile.finalize`). Four legs:

  - `collectDeps`: the raw closure producers' closure, which pulls an
    auxiliary's whole family (`Lean.auxFamilySiblings`) and a definition's
    `all`. Every address must match.
  - `raw`: the closure without family completion (`rawDeps`), which tests
    the compiler's per-family block membership on its own. Every address
    must match: the compiler compiles Lean's auxiliaries as Lean declared
    them, so a family-incomplete slice (a nested block's class
    `.brecOn.eq`, whose family holds `<all0>.brecOn_N.eq`) compiles to the
    whole compile's addresses.
  - `selected`: the selected closure (`collectSelectedDeps`, what
    `ix compile --consts` takes: recursors, whole logical units, checker
    and literal support). Every address must match, and the certified
    checker (IxCK, `rsCheckIxonFFI`) accepts or types the seed in that
    artifact.
  - `pack`: `ix pack` (`rsPackEnv`) of the bound reference to each
    auxiliary seed keeps the seed's address, and IxCK accepts or types the
    seed in the bundle.

  And `twin` (`twinRecursorCheck`): a closure that is not closed over its
  recursors can meet the compile's recursor check on alpha-equivalent
  families, which refuses it whole; closed over them it compiles.

  Only the `selected` and `pack` artifacts are type-checked. IxCK reads an
  inductive block together with its recursor and declines it otherwise
  (`reader: inductive block without a recursor in the input`,
  `Ix.EnvScope.ClosureOptions.recursors`), and neither the `collectDeps`
  nor the `raw` closure carries the recursors of the library families it
  reaches (`PProd`, `Nat`, …). The selected closure of either leg's closure
  is the seed's own selected closure (`collectSelectedDeps` is a fixed
  point, and each leg's closure lies inside the seed's), so the `selected`
  leg checks the seed in exactly the closure that makes either leg's input
  self-contained. Likewise `ix pack` carries the recursors of the
  inductives a bundle reaches only for a bound artifact
  (`crates/ixon/src/binding_support.rs`), so the reference is bound. On
  `main` these checks ran the Rust kernel, which needed neither.

  Run with: `lake test -- canon-closure-aux`.
-/

open LSpec
open Ix.KernelCheck (CheckError rsCheckIxonFFI)

namespace Tests.Ix.Compile.AuxiliaryClosureCanon

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

/-- The file `compileClosure` writes for `tag`. -/
def artifactPath (dir : System.FilePath) (tag : String) : System.FilePath :=
  dir / s!"{tag}.ixe"

/-- Compile `consts` with the certified compiler (`ix compile`
    path: fail-closed), write it to `artifactPath dir tag` and read the
    output back. With `bind`, the role support, certificates and binding are
    added first, as `ix compile --consts` adds them
    (`Ix.RoleBinding.Compile.finalize`). -/
def compileClosure (env : Lean.Environment) (dir : System.FilePath)
    (tag : String) (consts : List (Lean.Name × Lean.ConstantInfo)) (bind : Bool := false) :
    IO (Except String Ixon.Env) := do
  let out ← match ← Ix.CompileM.compileCertified env consts with
    | .ok out => pure out
    | .error e => return .error e
  let ungrounded := out.failures.toMap.toArray
  if let some (n, r) := ungrounded[0]? then
    return .error s!"compile ({ungrounded.size} ungrounded): {n.pretty}: {r}"
  let mut artifact := out.env
  if bind then
    try
      artifact ← Ix.RoleBinding.Compile.finalize (Ix.RoleBinding.Compile.certifiedBackend 32) env
        Ix.RoleBinding.Compile.nativeCertSource (Ix.Compile.CompileInput.plain consts) out.env
        Ix.Resource.typingLimits (existing? := out.existing?)
    catch e => return .error s!"finalize: {e}"
  let path := artifactPath dir tag
  let bytes ← IO.ofExcept (Ixon.serEnv artifact)
  IO.FS.writeBinFile path bytes
  return Ixon.rsDeEnv (← IO.FS.readBinFile path)

/-- The certified checker's verdict on `seed` in the artifact at `path`
    (`rsCheckIxonFFI`: `ix check-lean`'s selected check), as failure
    messages: none when IxCK accepts or types it. -/
def checkSeed (path : System.FilePath) (seed : Lean.Name) : IO (Array String) := do
  let results ← rsCheckIxonFFI path.toString #[seed] #[true] true ""
  return match results[0]? with
    | some none => #[]
    | some (some (CheckError.kernelException m)) => #[s!"kernel: {m}"]
    | some (some (CheckError.compileError m)) => #[s!"check-compile: {m}"]
    | none => #["no kernel result"]

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

/-- The library support every selected closure carries
    (`Ix.EnvScope.introducedSupport`: `PProd`, `PUnit`, `And`, `True`, `Eq`)
    with its closure, added to every closure this suite compiles, as the
    selected closure (`ix compile --consts`) carries it; the raw and
    family-completing collectors of the legs below do not. -/
def withSupport (env : Lean.Environment) (closure : List (Lean.Name × Lean.ConstantInfo)) :
    List (Lean.Name × Lean.ConstantInfo) :=
  let present : Std.HashSet Lean.Name := closure.foldl (fun s (n, _) => s.insert n) {}
  closure ++ (Ix.EnvScope.collectDeps env (Ix.EnvScope.introducedSupport env)).filter
    (!present.contains ·.1)

/-- The compile's recursor check on alpha-equivalent families
    (`Ix.Cert.RecursorsOwned`, `twin`): `HAdd` and `HPow` compile to one
    inductive block, and `HAdd.rec`'s record is the one `HPow.rec` would
    compile to. A closure that holds `HAdd.rec` and reaches `HPow` without
    `HPow.rec` is refused whole, since the recursor index files the shared
    record under the block and it is not a published recursor of `HPow`'s
    family; closed over its recursors (`ClosureOptions.recursors`, as every
    selected closure and whole environment is) it compiles. Failure
    messages, none when both hold. -/
def twinRecursorCheck (env : Lean.Environment) : Array String := Id.run do
  let names (c : List (Lean.Name × Lean.ConstantInfo)) := c.map (·.1)
  let without := (Ix.EnvScope.collectDeps env [``HAdd.rec, ``HPow]).filter (·.1 != ``HPow.rec)
  let closed := Ix.EnvScope.collectDeps env (names without) { recursors := true }
  let mut errors : Array String := #[]
  unless (names without).contains ``HAdd.rec && (names closed).contains ``HPow.rec do
    errors := errors.push s!"twin: the closures are not the case: {names without}"
  match Ix.Cert.compileReport (Ix.CompileM.canonInput without.toArray 32) with
  | .error e =>
    let e := toString e
    unless (e.splitOn "recursor check failed").length > 1 && (e.splitOn "HPow").length > 1 do
      errors := errors.push s!"twin: refused, but not by HPow's recursor check: {e}"
  | .ok _ => errors := errors.push "twin: HPow without HPow.rec beside HAdd.rec compiled"
  if let .error e := Ix.Cert.compileReport (Ix.CompileM.canonInput closed.toArray 32) then
    errors := errors.push s!"twin: closed over its recursors, refused: {e}"
  return errors

/-- One leg: per seed, compile `closureOf seed` (with `withSupport`), compare every shared name's
    address with `ref`, and with `check` kernel-check the seed in that
    artifact (`checkSeed`). A seed with `refused seed = some msg` must
    instead be refused by the compiler with `msg` in the error (and is not
    kernel-checked: nothing was written). -/
def runLeg (env : Lean.Environment) (dir : System.FilePath) (ref : Ixon.Env)
    (label : String) (seeds : Array Lean.Name)
    (closureOf : Lean.Name → List (Lean.Name × Lean.ConstantInfo))
    (refused : Lean.Name → Option String) (check : Bool := false) : IO Nat := do
  let t0 ← IO.monoMsNow
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
        if check then
          errs := errs ++ (← checkSeed (artifactPath dir s!"{label}-{seed}") seed)
    if !errs.isEmpty then
      failed := failed + 1
      for e in errs[:4] do IO.println s!"[canon-closure-aux] {label} FAIL {seed}: {e}"
      if errs.size > 4 then
        IO.println s!"[canon-closure-aux] {label} FAIL {seed}: … {errs.size - 4} more"
  IO.println s!"[canon-closure-aux] {label}: {seeds.size - failed}/{seeds.size} seeds ok \
    ({(← IO.monoMsNow) - t0} ms)"
  return failed

def suite : List TestSeq := [
  .individualIO "aux addresses are closure-invariant" none (do
    let env ← get_env!
    let fx := `Tests.Ix.Compile.AuxiliaryClosureCanon.Fx
    let seeds := (env.constants.toList.filterMap fun (n, _) =>
      if fx.isPrefixOf n && n != fx then some n else none).toArray.qsort
        (·.toString < ·.toString)
    let dir ← IO.FS.createTempDir
    -- The reference: every fixture's selected closure, compiled and bound as
    -- `ix compile --consts` compiles and binds it.
    let t0 ← IO.monoMsNow
    let ref ← match ← compileClosure env dir "ref"
        (Ix.EnvScope.collectSelectedDeps env seeds.toList) (bind := true) with
      | .ok e => pure e
      | .error e => throw (IO.userError s!"reference compile: {e}")
    IO.println s!"[canon-closure-aux] reference: {seeds.size} seeds, {ref.named.size} names, \
      bound ({(← IO.monoMsNow) - t0} ms); files in {dir}"
    -- Leg 1, the closure producers (`collectDeps`): every address is the
    -- reference's.
    let f1 ← runLeg env dir ref "collectDeps" seeds
      (fun s => Ix.EnvScope.collectDeps env [s]) (fun _ => none)
    -- Leg 2, the compiler on family-incomplete slices: same, a nested
    -- block's class `.brecOn.eq` included.
    let f2 ← runLeg env dir ref "raw" seeds (fun s => rawDeps env [s]) (fun _ => none)
    -- Leg 3, the selected closure (`ix compile --consts`), self-contained
    -- for IxCK: every address is the reference's, and the seed type-checks.
    let f3 ← runLeg env dir ref "selected" seeds
      (fun s => Ix.EnvScope.collectSelectedDeps env [s]) (fun _ => none) (check := true)
    -- Leg 4, the pack-side closure (`ix pack`, `Env::prune_to_closure`):
    -- a block is one Ixon constant, so pruning the reference to an
    -- auxiliary keeps its whole block; the bundle must name the seed at the
    -- reference's address and type-check. The reference is bound, so the
    -- bundle carries the recursors of the inductives it reaches.
    let auxSeeds := seeds.filter fun s => match s with
      | .str _ last => ["rec", "casesOn", "recOn", "below", "brecOn", "go", "eq"].contains last
          || ["rec_", "below_", "brecOn_"].any (fun p => last.startsWith p)
      | _ => false
    let refPath := (artifactPath dir "ref").toString
    let t4 ← IO.monoMsNow
    let mut f4 := 0
    for seed in auxSeeds do
      let mut errs : Array String := #[]
      let bundle := artifactPath dir s!"pack-{seed}"
      match ← (Ixon.rsPackEnv refPath (toString seed) #[] bundle.toString false false).toBaseIO with
      | .error e => errs := errs.push s!"pack: {e}"
      | .ok () =>
        match Ixon.rsDeEnv (← IO.FS.readBinFile bundle) with
        | .error e => errs := errs.push s!"read bundle: {e}"
        | .ok b =>
          let ixn := Ix.Name.fromLeanName seed
          if b.getAddr? ixn != ref.getAddr? ixn then
            errs := errs.push s!"bundle address {b.getAddr? ixn} ≠ reference {ref.getAddr? ixn}"
        errs := errs ++ (← checkSeed bundle seed)
      if !errs.isEmpty then
        f4 := f4 + 1
        for e in errs do IO.println s!"[canon-closure-aux] pack FAIL {seed}: {e}"
    IO.println s!"[canon-closure-aux] pack: {auxSeeds.size - f4}/{auxSeeds.size} seeds ok \
      ({(← IO.monoMsNow) - t4} ms)"
    -- The recursor check on alpha-equivalent families, which a closure
    -- not closed over its recursors can meet.
    let twinErrors := twinRecursorCheck env
    for e in twinErrors do IO.println s!"[canon-closure-aux] FAIL {e}"
    IO.println s!"[canon-closure-aux] twin: {if twinErrors.isEmpty then "ok" else "FAIL"}"
    let n := 3 * seeds.size + auxSeeds.size + 1
    let failed := f1 + f2 + f3 + f4 + (if twinErrors.isEmpty then 0 else 1)
    if failed == 0 then IO.FS.removeDirAll dir
    return (failed == 0, n - failed, n,
      if failed == 0 then none else some s!"{failed} seed check(s) failed"))
    .done
]

end Tests.Ix.Compile.AuxiliaryClosureCanon
