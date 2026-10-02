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
  Rust kernel.

  Two seed adjustments, both outside this fix:
  - A nested block's class `.brecOn.eq` (`T.brecOn.eq`) belongs to one
    block with `<all0>.brecOn_N.eq`, which is proved by cases on the
    external inductive (`List.casesOn`). `X.brecOn.eq`'s closure does not
    reach it, so the compiler cannot build that block from the slice and
    falls back to the members present: the address differs. Those seeds
    get `List.casesOn` added (a slice closed over block-mates'
    dependencies, which is the slice producer's job).
  - `A.size`/`B.size` (a mutual definition) are not kernel-checked: the
    Rust kernel's ingress needs every member of a mutual definition block
    (`resolve_all: Named entry for '…B.size' missing`), a separate
    `check-rs` limitation. Their addresses are still compared.

  Run with: `lake test -- --ignored canon-closure-aux`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.KernelCheck
import Ix.CompileM
import LSpec

open LSpec
open Ix.KernelCheck (CheckError rsCheckConstsFFI)

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

def suite : List TestSeq := [
  .individualIO "aux addresses are closure-invariant" none (do
    let env ← get_env!
    let fx := `Tests.Ix.Compile.AuxGenClosureCanon.Fx
    let seeds := (env.constants.toList.filterMap fun (n, _) =>
      if fx.isPrefixOf n && n != fx then some n else none).toArray.qsort
        (·.toString < ·.toString)
    let dir ← IO.FS.createTempDir
    let ref ← match ← compileClosure env dir "ref"
        (Ix.EnvScope.collectDeps env seeds.toList) with
      | .ok e => pure e
      | .error e => throw (IO.userError s!"reference compile: {e}")
    let mut failed := 0
    for seed in seeds do
      let mut errs : Array String := #[]
      let nestedEq := seed.toString.endsWith ".brecOn.eq" &&
        [`T, `C, `D, `Rose].any (fun c => (fx ++ c).isPrefixOf seed)
      let closure := Ix.EnvScope.collectDeps env
        (if nestedEq then [seed, ``List.casesOn] else [seed])
      match ← compileClosure env dir s!"{seed}" closure with
      | .error e => errs := errs.push e
      | .ok out =>
        for (n, _) in closure do
          let ixn := Ix.Name.fromLeanName n
          match out.getAddr? ixn, ref.getAddr? ixn with
          | some a, some b =>
            if a != b then errs := errs.push s!"{n}: {a} in the closure, {b} in the reference"
          | none, _ => errs := errs.push s!"{n}: not in the closure output"
          | some _, none => pure ()
      let mutualDef := [`A.size, `B.size].any (fun c => (fx ++ c).isPrefixOf seed)
      if !mutualDef then
        let results ← rsCheckConstsFFI closure #[seed] #[true] false
        match results[0]? with
        | some none => pure ()
        | some (some (CheckError.kernelException m)) => errs := errs.push s!"kernel: {m}"
        | some (some (CheckError.compileError m)) => errs := errs.push s!"check-compile: {m}"
        | none => errs := errs.push "no kernel result"
      if !errs.isEmpty then
        failed := failed + 1
        for e in errs[:4] do IO.println s!"[canon-closure-aux] FAIL {seed}: {e}"
        if errs.size > 4 then
          IO.println s!"[canon-closure-aux] FAIL {seed}: … {errs.size - 4} more"
    let n := seeds.size
    IO.println s!"[canon-closure-aux] {n - failed}/{n} seeds closure-invariant"
    return (failed == 0, n - failed, n,
      if failed == 0 then none else some s!"{failed} seed(s) differ"))
    .done
]

end Tests.Ix.Compile.AuxGenClosureCanon
