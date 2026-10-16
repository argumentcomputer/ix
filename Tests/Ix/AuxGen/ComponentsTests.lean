module

public import LSpec
public import Ix.AuxGen.CompileAux

/-!
Tests of D6, one constant per auxiliary (`Ix.AuxGen.auxComponents`,
`Ix.CompileM.orderRecursorFamily`), the twins of the Rust tests
`aux_components_are_singletons_unless_cyclic` and
`order_recursor_family_lays_out_flat_order`.

* **Components.** Independent auxiliaries are singleton components in
  least-name order, a dependency comes first, and only a genuine cycle is one
  component (members in input order); references outside the batch are
  ignored.
* **Recursor family order.** `X.rec` sits at its position in `all`,
  `all[0].rec_N` after the members; a malformed `rec_N` suffix, or a position
  that does not fit below `u64::MAX`, has no position, and a block that is not
  all recursors keeps the `sortConsts` order.

Registered in `aux-gen-unit`.
-/

public section

namespace Tests.AuxGen.Components

open LSpec
open Ix (Name Level Expr MutConst RecursorVal)

private def nm (s : String) : Name :=
  (s.splitOn ".").foldl Name.mkStr .mkAnon

private def sort0 : Expr := Expr.mkSort Level.mkZero

/-- A definition named `name` whose value mentions `refs`. -/
private def defn (name : String) (refs : List String) : MutConst :=
  .defn { name := nm name, levelParams := #[], type := sort0, kind := .defn
          value := refs.foldl (fun acc r => Expr.mkApp acc (Expr.mkConst (nm r) #[])) sort0
          hints := .abbrev, safety := .safe, all := #[] }

def componentsAgree : Bool :=
  let batch := #[defn "Z" [], defn "B" ["A"], defn "A" [], defn "D" ["E"],
    defn "E" ["D", "outside"]]
  match Ix.AuxGen.auxComponents batch with
  | .ok comps =>
    comps.map (·.map (·.name.pretty)) == #[#["A"], #["B"], #["D", "E"], #["Z"]]
  | .error _ => false

private def mkRec (name : String) : RecursorVal :=
  { cnst := { name := nm name, levelParams := #[], type := sort0 }
    all := #[nm "A", nm "B"], numParams := 0, numIndices := 0, numMotives := 3,
    numMinors := 0, rules := #[], k := false, isUnsafe := false }

def positionsAgree : Bool :=
  let pos (n : String) := Ix.CompileM.recursorFamilyPosition (mkRec n)
  pos "A.rec" == 0 && pos "B.rec" == 1 && pos "A.rec_1" == 2 && pos "A.rec_3" == 4
    && ["B.rec_1", "A.rec_0", "A.rec_", "A.rec_+1", "A.rec_1_0",
        "A.rec_18446744073709551615"].all
      (pos · == Ix.CompileM.recursorFamilyNoPosition)

def familyOrderAgrees : Bool :=
  let classes : List (List MutConst) :=
    [[.recr (mkRec "A.rec_1")], [.recr (mkRec "B.rec")], [.recr (mkRec "A.rec")]]
  let mixed : List (List MutConst) := [[.recr (mkRec "A.rec_1")], [defn "A.rec" []]]
  (Ix.CompileM.orderRecursorFamily classes).map (·.map (·.name.pretty))
      == [["A.rec"], ["B.rec"], ["A.rec_1"]]
    && (Ix.CompileM.orderRecursorFamily mixed).map (·.map (·.name.pretty))
      == [["A.rec_1"], ["A.rec"]]

def suite : List TestSeq := [
  test "D6: auxiliaries are singleton components unless cyclic, dependencies first"
    componentsAgree
  ++ test "D6: a recursor's flat position in its family" positionsAgree
  ++ test "D6: a recursor block in its family's flat order; a mixed block unchanged"
    familyOrderAgrees
]

end Tests.AuxGen.Components
