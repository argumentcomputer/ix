import IxVM.Source
import IxVM.ObsNames
import Aiur.Generic.Derive.Elab

/-! # The IxVM program's semantic helpers

The commands that declare the helpers the refinement proofs are written against, derived
from `IxVM.source` where the command is elaborated (`Aiur.Generic.Derive.Elab`):

* `#ixvm_lookup`: the lookup facts (`IxVM.Lookup`);
* `#ixvm_mirrors roots [prior]`: the mirrors of the functions reachable from `roots` and
  their lemmas, in `IxVM.Refinement.Mirrors`, but those reachable from `prior`
  (`IxVM.Mirrors.*`);
* `#ixvm_obs_shared`: what the path lemmas share (`IxVM.Obs.Names`);
* `#ixvm_obs G…`: the path inductives and inversion theorems of the functions of the Aiur
  modules `G…`, in `IxVM.Refinement.Obs`.

`target` says how the declarations name the program, and holds what is particular to it:
the mirrors written by hand, the functions derived under larger caps, and the table of the
path lemmas' names (`IxVM.ObsNames`). -/

namespace IxVM.Derive
open Lean Elab Command
open Aiur.Generic

/-- The mirrors written by hand: of functions whose bodies the mirror deriver does not
read (a hint whose value the mirror computes, a read of several stream cells), each with
the definitions its lemma unfolds besides it. -/
def mirrorOverrides : List (String × String × List String) := [
  ("IxonDeserialize::get_address",
    "def «IxonDeserialize::get_address» : Nat → Heap F → SourceValue F → Option (SourceValue F × Heap F)\n" ++
    "  | 0, _, _ => none\n" ++
    "  | _ + 1, h, x_stream =>\n" ++
    "      (readStreamBytes 32 h x_stream).map fun p =>\n" ++
    "        let v : SourceValue F := .tuple p.1\n" ++
    "        (.tuple [.ptr v.type h.length, p.2], h ++ [v])\n",
    ["readStreamBytes"]),
  ("UInt32::less_than_fields",
    "def «UInt32::less_than_fields» : Nat → Heap F → SourceValue F → SourceValue F → Option (SourceValue F × Heap F)\n" ++
    "  | 0, _, _, _ => none\n" ++
    "  | _ + 1, h, .field a, .field b =>\n" ++
    "      if a.val < 4294967296 ∧ b.val < 4294967296 then\n" ++
    "        some (.field (if a.val < b.val then 1 else 0), h)\n" ++
    "      else none\n" ++
    "  | _ + 1, _, _, _ => none\n", []),
  ("UInt64::from_field",
    "def «UInt64::from_field» : Nat → Heap F → SourceValue F → Option (SourceValue F × Heap F)\n" ++
    "  | 0, _, _ => none\n" ++
    "  | _ + 1, h, .field v =>\n" ++
    "      if v.val < 72057594037927936 then\n" ++
    "        some (.tuple [\n" ++
    "          .field ((v.val % 256 : Nat) : F),\n" ++
    "          .field (((v.val / 256) % 256 : Nat) : F),\n" ++
    "          .field (((v.val / 65536) % 256 : Nat) : F),\n" ++
    "          .field (((v.val / 16777216) % 256 : Nat) : F),\n" ++
    "          .field (((v.val / 4294967296) % 256 : Nat) : F),\n" ++
    "          .field (((v.val / 1099511627776) % 256 : Nat) : F),\n" ++
    "          .field (((v.val / 281474976710656) % 256 : Nat) : F),\n" ++
    "          .field 0], h)\n" ++
    "      else none\n" ++
    "  | _ + 1, _, _ => none\n", []),
  ("UInt64::mul_column",
    "def «UInt64::mul_column» : Nat → Heap F → SourceValue F → Option (SourceValue F × Heap F)\n" ++
    "  | 0, _, _ => none\n" ++
    "  | _ + 1, h, .field x =>\n" ++
    "      if x.val < 1099511627776 then\n" ++
    "        some (.tuple [\n" ++
    "          .tuple [.field ((x.val % 256 : Nat) : F), .field (((x.val / 256) % 256 : Nat) : F)],\n" ++
    "          .tuple [.field (((x.val / 65536) % 256 : Nat) : F),\n" ++
    "                  .field (((x.val / 16777216) % 256 : Nat) : F),\n" ++
    "                  .field (((x.val / 4294967296) % 256 : Nat) : F)]], h)\n" ++
    "      else none\n" ++
    "  | _ + 1, _, _ => none\n", [])]

/-- How the derived declarations name the IxVM program. -/
instance target : Derive.Target F where
  toNat x := x.val
  fieldNamespace := "IxVM"
  program := "IxVM"
  source := "IxVM.source"
  functionName symbol := ((IxVM.Elab.functionName symbol).replacePrefix `IxVM .anonymous).toString
  mirrors := "IxVM.Refinement.Mirrors"
  obs := "IxVM.Refinement.Obs"
  mirrorOverrides := mirrorOverrides
  mirrorPairBind := ["UInt64::mul"]
  -- functions the refinement proofs need whose paths multiply
  obsGenerous := ["KernelWhnf::whnf_nd_const_head", "KernelRoles::basis_pin",
    "KernelModeled::check_family", "KernelModeled::check_proj_pure_defn"]
  obsNames := some obsNames

/-- A part of a derivation: `(i/n)` is the `i`-th of `n`, from 1. The parts are elaborated
by different modules, side by side. -/
syntax ixvmPart := "(" num "/" num ")"

private def partOf? : Option (TSyntax ``ixvmPart) → Option (Nat × Nat)
  | some stx => match stx with
    | `(ixvmPart| ($i / $n)) => some (i.getNat, n.getNat)
    | _ => none
  | none => none

/-- `#ixvm_lookup` declares the program's lookup facts. `#ixvm_lookup (i/n)` declares the
`i`-th of `n` parts of them; the first declares the certificate that the names are
distinct, and the others import it. -/
syntax "#ixvm_lookup" (ppSpace ixvmPart)? : command

elab_rules : command
  | `(#ixvm_lookup $[$part]?) => Derive.deriveLookup IxVM.program (partOf? part)

private unsafe def evalNamesUnsafe (stx : Syntax) : TermElabM (List String) := do
  let type := toTypeExpr (List String)
  let e ← Term.elabTermEnsuringType stx type
  Term.synthesizeSyntheticMVarsNoPostponing
  Meta.evalExpr (List String) type (← instantiateMVars e)

/-- The function names a term of type `List String` denotes. -/
@[implemented_by evalNamesUnsafe]
private opaque evalNames (stx : Syntax) : TermElabM (List String)

/-- `#ixvm_mirrors roots` declares the mirrors of the functions reachable from `roots` (a
`List String`) and their lemmas. `#ixvm_mirrors roots prior` leaves out the mirrors
reachable from `prior`: the roots derived in the modules this one imports. -/
syntax "#ixvm_mirrors " term:max (ppSpace term:max)? : command

elab_rules : command
  | `(#ixvm_mirrors $roots:term $[$prior:term]?) => do
    let roots ← liftTermElabM (evalNames roots)
    let prior ← match prior with
      | some prior => liftTermElabM (evalNames prior)
      | none => pure []
    Derive.deriveMirrors IxVM.source prior roots

/-- `#ixvm_obs_shared` declares what the path lemmas share: the world and the instance
names. `#ixvm_obs_shared (i/n)` declares the `i`-th of `n` parts of them; the first
declares the world and the instances, and the others, which import it, the lemmas about
them. -/
syntax "#ixvm_obs_shared" (ppSpace ixvmPart)? : command

elab_rules : command
  | `(#ixvm_obs_shared $[$part]?) => Derive.deriveObsShared IxVM.source (partOf? part)

/-- `#ixvm_obs G…` declares `«f».Path` and `«f».obs` for every function `G::f` of the Aiur
modules `G…` that the deriver handles. `#ixvm_obs G… (i/n)` declares the `i`-th of `n` parts
of them, so that a large module's path lemmas are checked by several modules side by
side. -/
syntax "#ixvm_obs" (ppSpace ident)+ (ppSpace ixvmPart)? : command

elab_rules : command
  | `(#ixvm_obs $groups* $[$part]?) => do
    let groups := groups.toList.map (·.getId.toString)
    Derive.deriveObs IxVM.source (fun name => groups.contains (Derive.Obs.group name))
      (partOf? part)

end IxVM.Derive
