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

/-! ## Provenance of an object no certificate replay covers

An `ixir1Policy` provenance note ends in two little-endian 32-bit words, the lowering version and
the pass-policy version (`X86.ELF.Provenance.bytes`). Every object the certified routes write has
pass policy 1 and lowering 1 (zero RC, `defaultProvenance`) or 3 (plain RC). An object `ixcc
compile --uncertified` writes, which no certificate replay covers, has the top bit of its
pass-policy word set (`uncertifiedPolicyBit`), so a consumer of the file can tell it apart from
the note alone: with `--opt` its pass policy is 2 (`optPassPolicy`: the Lir SSA optimizer and a
back end run after the replay), on the replay's lowering (1 or 3); with `--bignat` its lowering is
4 (`bigNatLowering`: no certificate at all), pass policy 1, or 2 with `--opt`. The certified
routes' notes are unchanged. -/

/-- The bit of the pass-policy word that marks an object no certificate replay covers. -/
def uncertifiedPolicyBit : UInt32 := 0x80000000

/-- The pass-policy version of an object built by `Backend.compileOpt` (`--opt`). -/
def optPassPolicy : UInt32 := 2

/-- The lowering version of an object built by `Rt.BigNat.lowerRepBig` (`--bignat`). -/
def bigNatLowering : UInt32 := 4

/-- The provenance of an uncertified object compiled from the root at `root`: lowering
`lowering`, pass policy `passPolicy` with `uncertifiedPolicyBit` set. -/
def uncertifiedProvenance (root : Ixon.Address) (lowering passPolicy : UInt32) :
    X86.ELF.Provenance :=
  .ixir1Policy root lowering (passPolicy ||| uncertifiedPolicyBit)

/-- Whether a provenance says the object is covered by certificate replay (its pass-policy word
without `uncertifiedPolicyBit`). -/
def provenanceCovered : X86.ELF.Provenance → Bool
  | .ixir1Policy _ _ passPolicy => passPolicy &&& uncertifiedPolicyBit == 0
  | .ixir2 _ => true

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
