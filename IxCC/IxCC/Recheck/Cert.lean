import IxCC.Src.Table.Cert
import IxCC.Src.Admit
import IxCC.Src.Relevance.Syntax
import IxCC.Anf.Pipeline
import IxCC.Xv.Alloc.Output
import IxCC.Xv.Stacking.Frame
import IxCC.X86.Layout.Order
import IxCC.X86.ELF
import IxCC.Xv.XlSemantics

/-! # The compiler's certificate and configuration

The certificate (D17) is the untrusted
data `produce` hands to `Recheck.run`: every oracle decision and every
output a validator re-checks, and nothing else. Its fields are the ones the
Phase 1 passes read today, in pipeline order:

| Field | Pass | Style |
| --- | --- | --- |
| `table` | the unfolding table (`Table.ofCert`) | V |
| `relevance` | installation and the relevance check | V |
| `mid` | P1–P4 and pruning (`Anf.Pipeline.run`) | P, oracle |
| `alloc` | allocation (`Validate.program`, `Alloc.applyProgram`) | V |
| `frames` | frame layouts (`FrameLayout.check` in `Stacking.run`) | V |
| `order` | block order (`Order.check`) | V |

Styles P and V are those of decision D17 (`docs/compiler-design.md`). This
certificate has no field for an Own program (the plain-RC route wraps it with
the proposed ownership code in `Recheck.RcReplay.Cert`), for selection (its rules are deterministic)
or for rel8 choices (every branch is `rel32` or falls through, and linearisation
decides the fall-through). The certificate is plain data, lists in
function and label order; `Recheck.Json` serialises it. -/

namespace IxCC.Recheck

/-- The SysV entry wrapper passes the region and at most five arguments. -/
def maxParams : Nat := 5

structure Config where
  /-- The table checks' configuration (the enabled primitives, the inline cap). -/
  table : Src.Table.Config := {}
  /-- The roots' names, by root position: the exported symbols are
  `cx_<name>` (`Rt.symbolOf`), `root<i>` where a name is missing. -/
  names : List String := []
  /-- The calling convention's clobber sets (allocation, stacking). -/
  env : Xv.Xl.Env := {}
  /-- The object's provenance note; `none` names the first root's address
  (`defaultProvenance`). -/
  provenance : Option X86.ELF.Provenance := none
  /-- The producer's budgets for the middle end's oracles (not read by
  `run`). -/
  budgets : Anf.Pipeline.Budgets := {}
  /-- The producer's admission limits (not read by `run`). -/
  admit : Src.AdmitConfig := {}
  deriving Inhabited

/-- The provenance of an object compiled from the root at `root`: the
Phase 1 pipeline (lowering version 1) under its default pass policy
(version 1). -/
def defaultProvenance (root : Ixon.Address) : X86.ELF.Provenance := .ixir1Policy root 1 1

/-- The certificate: untrusted, linear in the program's size. -/
structure Cert where
  table : Src.Table.TableCert := {}
  relevance : Src.Relevance.Ann := {}
  mid : Anf.Pipeline.Cert := {}
  /-- One allocation per Xv function, in function order. -/
  alloc : List Xv.Alloc.Output := []
  /-- One frame layout per Xl function, in function order. -/
  frames : List Xv.Stacking.FrameLayout := []
  /-- The block order, per layout group. -/
  order : X86.Layout.Order := []
  deriving Inhabited

end IxCC.Recheck
