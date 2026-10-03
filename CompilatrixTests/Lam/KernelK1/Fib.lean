import CompilatrixTests.Src.Artifacts.Fib
import CompilatrixTests.Lam.KernelK1.Front

/-! The `fib` bench-k1 artifact through the front end in the kernel (M1.K1):
`Src.Recheck.run` (the table's revalidation, the annotation's installation
and check, `Lazify`) and erasure, evaluated by `decide +kernel` on the loaded
program and annotation, then one mutation per recheck step, each rejected
in the kernel. -/

namespace CompilatrixTests.Lam.KernelK1.Fib

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance
open CompilatrixTests.Src.Artifacts.Fib

set_option maxRecDepth 1000000

/-- `fib`'s entry (constant 22) erases to 11 globals rooted at `const 22`. -/
example : facts program ann 11 22 = true := by decide +kernel

/-- The program with one table column changed. -/
noncomputable def withTable (f : Table → Table) : Program :=
  { program with table := f program.table }

-- The table's revalidation. Constant 16 is `Nat.add` (a `prim` entry), 29
-- has an `eqn` entry (theorem 21), 32 is `Nat.casesOn` (a `case` entry over
-- `Nat.rec`, 39), 45 is a subsingleton recursor, and 10 is a `lazy` constant
-- of arity 4.

/-- `Nat.add` claimed to be `Nat.sub`. -/
example : stage (withTable fun t => { t with resolve := t.resolve.insert 16 (.prim .sub) })
    ann = .table := by decide +kernel

/-- An `eqn` body that is not the theorem's right-hand side. -/
example : stage (withTable fun t => { t with resolve := t.resolve.insert 29 (.eqn 21 (.natLit 0)) })
    ann = .table := by decide +kernel

/-- A `case` entry naming another recursor. -/
example : stage (withTable fun t => { t with resolve := t.resolve.insert 32 (.case 45) })
    ann = .table := by decide +kernel

/-- `Nat.rec` claimed empty. -/
example : stage (withTable fun t => { t with recKind := t.recKind.insert 39 .empty })
    ann = .table := by decide +kernel

/-- A `lazy` arity beyond the definition's λs. -/
example : stage (withTable fun t => { t with lazy := t.lazy.insert 10 100 })
    ann = .table := by decide +kernel

/-- An opaque-by-value entry off the allowlist. -/
example : stage (withTable fun t => { t with opaqueByValue := t.opaqueByValue.insert 22 })
    ann = .table := by decide +kernel

/-- `known.nat` naming `Nat.zero`. -/
example : stage { program with known := { program.known with nat := some 7 } }
    ann = .table := by decide +kernel

-- The annotation's installation and check.

/-- An extra tag on every runtime term (installation, S1). -/
example : stage program { ann with nodes := ann.nodes.map fun (k, ts) => (k, ts ++ [.arg .rel]) }
    = .install := by decide +kernel

/-- `Nat.add` annotated as a proof (C5 at its relevant uses). -/
example : stage program { ann with consts := ann.consts.insert 16 { result := Rel.prf, params := [] } }
    = .relevance := by decide +kernel

/-- The unmutated input is accepted (the stage this file's mutations leave). -/
example : stage program ann = .accepted := by decide +kernel

end CompilatrixTests.Lam.KernelK1.Fib
