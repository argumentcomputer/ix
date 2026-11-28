import IxCCTests.Src.Artifacts.Fib
import IxCCTests.Lam.KernelK1.Front

/-! The `fib` bench-k1 artifact through the front end in the kernel:
`Src.Recheck.run` (the table's revalidation, the annotation's installation
and check, `Lazify`) and erasure, evaluated by `decide +kernel` on the loaded
program and annotation, then one mutation per recheck step, each rejected
in the kernel. -/

namespace IxCCTests.Lam.KernelK1.Fib

open IxCC IxCC.Src IxCC.Src.Relevance
open IxCCTests.Src.Artifacts.Fib

set_option maxRecDepth 1000000

/-- `fib`'s entry (`Ids.entry`) erases to `Ids.globals` globals rooted at `const Ids.entry`. -/
example : facts program ann Ids.globals Ids.entry = true := by decide +kernel

/-- The program with one table column changed. -/
noncomputable def withTable (f : Table → Table) : Program :=
  { program with table := f program.table }

-- The table's revalidation, on the constants `Ids` names by their meaning
-- (`gen-src-artifacts` finds them): `Nat.add` (a `prim` entry), a constant with
-- an `eqn` entry and its theorem, `Nat.casesOn` (a `case` entry over `Nat.rec`),
-- a subsingleton recursor and a `lazy` constant.

/-- `Nat.add` claimed to be `Nat.sub`. -/
example : stage (withTable fun t => { t with resolve := t.resolve.insert Ids.natAdd (.prim .sub) })
    ann = .table := by decide +kernel

/-- An `eqn` body that is not the theorem's right-hand side. -/
example : stage (withTable fun t => { t with resolve := t.resolve.insert Ids.eqn (.eqn Ids.eqnTheorem (.natLit 0)) })
    ann = .table := by decide +kernel

/-- A `case` entry naming another recursor. -/
example : stage (withTable fun t => { t with resolve := t.resolve.insert Ids.natCasesOn (.case Ids.subsingletonRec) })
    ann = .table := by decide +kernel

/-- `Nat.rec` claimed empty. -/
example : stage (withTable fun t => { t with recKind := t.recKind.insert Ids.natRec .empty })
    ann = .table := by decide +kernel

/-- A `lazy` arity beyond the definition's λs. -/
example : stage (withTable fun t => { t with lazy := t.lazy.insert Ids.lazy 100 })
    ann = .table := by decide +kernel

/-- An opaque-by-value entry off the allowlist. -/
example : stage (withTable fun t => { t with opaqueByValue := t.opaqueByValue.insert Ids.entry })
    ann = .table := by decide +kernel

/-- `known.nat` naming `Nat.zero`. -/
example : stage { program with known := { program.known with nat := some Ids.natZero } }
    ann = .table := by decide +kernel

-- The annotation's installation and check.

/-- An extra tag on every runtime term (installation, S1). -/
example : stage program { ann with nodes := ann.nodes.map fun (k, ts) => (k, ts ++ [.arg .rel]) }
    = .install := by decide +kernel

/-- `Nat.add` annotated as a proof (C5 at its relevant uses). -/
example : stage program { ann with consts := ann.consts.insert Ids.natAdd { result := Rel.prf, params := [] } }
    = .relevance := by decide +kernel

/-- The unmutated input is accepted (the stage this file's mutations leave). -/
example : stage program ann = .accepted := by decide +kernel

end IxCCTests.Lam.KernelK1.Fib
