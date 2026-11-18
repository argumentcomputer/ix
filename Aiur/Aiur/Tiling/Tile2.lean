import Aiur.Tiling.Lower2
import Aiur.Tiling.PeriodicUnroll

/-!
# Assembling a sharded v2 system (unverified)

`lowerCircuit` lowers one circuit, unrolled or not, and returns its template
with the circuit it is checked against: the unrolled circuit with merged
lookups. `busesOf` derives the bus table from the placements (`code = tag +
4·sub`), and `tile2` assembles a sharded system and accepts it only if
`Sharded.check` does.

`compressUnroll` derives the unrolling of `Blake3::compress` as the
prototype's backend does: eight bodies; the self-call's multiplicity column is
fixed to 1 in bodies 0–6 and 0 in body 7, the selector to 1 in every body and
the stage argument to 0 in body 0 and the receive multiplicity column to 1 in
bodies `s > 0`; body `s > 0` reads each receive column as the previous body's
self-call argument, and drops its receive. Every body drops the self-call.
`lowerCircuit` accepts an unrolling only if `Unroll.check` does.
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr)

variable {F : Type} [Field F] [DecidableEq F] [Hashable F]

/-- `g` is only a lowering hint; the template is checked against `C`. -/
def lowerCircuit (W : Nat) (C : Circuit F) (U : Option (Unroll F)) (g : Graph F := Graph.ofCircuit C) :
    Except String (Template2 F × Circuit F × List (List Nat)) := do
  if let some U := U then
    unless U.check C do throw "unrolling is not a checked self-call chain"
  let (T, groups) ← lower2 g ((U.map (·.bodies)).getD [⟨[], [], []⟩]) W
  let wide := match U with
    | some U => U.circuit C
    | none => C
  return (T, wide.mergeBy groups, groups)

def stages : Nat := 8

private def column : ArithExpr F → Option Nat
  | .var c => some c
  | _ => none

/-- The prototype's unrolling of `Blake3::compress`, whose callable id is `fid`. -/
def compressUnroll (C : Circuit F) (fid : Nat) : Except String (Unroll F) := do
  let isConst (e : ArithExpr F) (k : F) : Bool := match e with
    | .const v => decide (v = k)
    | _ => false
  let calls := (List.range C.lookups.length).filter fun j =>
    0 < j && ((C.lookupAt j).args[1]?.map (isConst · (fid : F))).getD false
  let [selfcall] := calls | throw "Blake3::compress: expected one self-call"
  let some selCol := column (C.lookupAt selfcall).multiplicity | throw "self-call multiplicity is not a column"
  let recv := C.lookupAt 0
  let some stageCol := (recv.args[2]?).bind column | throw "stage argument is not a column"
  let actCol := C.width - 2
  let some multCol := (match recv.multiplicity with
      | .sub _ (.var c) => some c
      | _ => none) | throw "receive multiplicity is not -X_m"
  if multCol == actCol || multCol == selCol || multCol == stageCol then
    throw "receive multiplicity column is also a fixed column"
  let rvars ← (recv.args.drop 2).mapM fun a => match a with
    | .var c => pure c
    | _ => throw "compress receive argument is not a column"
  let bodies := (List.range stages).map fun s =>
    let subst : List (Nat × F) := (if s == 0 then [(stageCol, 0)] else [(multCol, 1)]) ++
      [(actCol, 1), (selCol, if s + 1 < stages then 1 else 0)]
    let aliases := if s == 0 then [] else
      (rvars.zipIdx.filter fun (c, _) => (subst.lookup c).isNone).map fun (c, pos) => (c, selfcall, 2 + pos)
    ⟨subst, aliases, if s == 0 then [selfcall] else [selfcall, 0]⟩
  return ⟨C.width, bodies⟩

def busesOf (toNat : F → Nat) (Ts : List (Template2 F)) : Buses F := Id.run do
  let mut out : Buses F := []
  for T in Ts do
    for r in T.rows do
      let uses : List (Nat × Bool) := match r with
        | .gate ls _ => ls.filterMap fun | .message m => some (m, true) | _ => none
        | .message m _ => [(m, false)]
      for (m, lane) in uses do
        if let some (_, tag, sub, _) := T.messages[m]? then
          if (out.lookup (tag, sub)).isNone then
            out := out ++ [((tag, sub), toNat tag + 4 * toNat sub, lane)]
  return out

/-- A sharded system of `shards` copies of one layout of `circuits`, with
`caps` instances each, followed by one layout of `tables` (if any). -/
def tile2 (toNat : F → Nat) (W : Nat) (circuits : List (Circuit F × Option (Unroll F))) (caps : List Nat)
    (shards : Nat) (tables : List (Circuit F) := []) : Except String (Sharded F) := do
  let lowered ← circuits.mapM fun (C, U) => lowerCircuit W C U
  let tabs ← tables.mapM fun C => lowerCircuit W C none
  let chipsL : Layout F := ⟨lowered.map (·.2.1), lowered.map (·.1), caps⟩
  let tableL : Layout F := ⟨tabs.map (·.2.1), tabs.map (·.1), tabs.map fun _ => 1⟩
  let S : Sharded F := {
    width := W
    shards := List.replicate shards chipsL ++ (if tables.isEmpty then [] else [tableL])
    buses := busesOf toNat (lowered.map (·.1) ++ tabs.map (·.1)) }
  unless S.check do throw "sharded system failed validation"
  return S

end Aiur.Tiling.Periodic
