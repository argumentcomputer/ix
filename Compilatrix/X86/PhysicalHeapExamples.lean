import Compilatrix.X86.PhysicalHeapObject

namespace Compilatrix.X86.PhysicalHeap.Examples
open Ixon IxIR2

def root : Address := Address.replicate 0xd1
def helper : Address := Address.replicate 0xd2
def cid : CtorId := ⟨Address.replicate 0xd3, 0, 0⟩

def layout (world : Owned) : Wire.Layout :=
  let preimage := IxIR2.Pipeline.baselineLayoutPreimage world cid
  ⟨Address.blake3 preimage, preimage⟩

def block (values : Array ValueCap) (instructions : Array IxIR2.Instr) (terminator : IxIR2.Terminator)
    (credits : Array CreditCap := #[]) : IxIR2.Block :=
  { valueParams := values, creditParams := credits, instructions, terminator }

def function (parameters : Array Owned) (blocks : Array IxIR2.Block) : IxIR2.Function :=
  { signature := { params := parameters.map (fun world => ⟨world, .owned⟩), result := .shared, papSafe := true }, blocks }

def edge (target : Nat) (values : Array IxIR2.Atom) (credits : Array CreditId := #[]) : IxIR2.Edge := ⟨target, values, credits⟩

def allocatingHelper (fields : Nat := 2) : IxIR2.Function := function #[.shared] #[
  block #[.owned .shared] #[.alloc .unique cid (Array.replicate fields (.lit (.nat 19))), .dropUnique (.reg 1)] (.ret (.reg 0))]

/-- Both successors transfer the caller's reservation to a common join. The
successor path swaps scalar fields while returning the Nat predecessor. -/
def uniqueDiamond : IxIR2.Function :=
  let owned := ValueCap.owned
  let credit := CreditCap.required (layout .unique).identity
  function #[.shared, .shared] #[
    block #[owned .shared, owned .shared]
      #[.alloc .unique cid #[.lit (.nat 19), .lit (.nat 23)], .takeUnique (.reg 2) cid,
        .call helper #[.reg 0]]
      (.switchValue (.reg 5) #[] (some ⟨edge 1 #[.reg 1, .reg 4, .reg 3, .reg 5] #[0],
        edge 2 #[.reg 1, .reg 3, .reg 4, .reg 5] #[0]⟩)),
    block #[owned .shared, owned .unique, owned .unique, owned .shared]
      #[.releaseShared (.reg 3)] (.jump (edge 3 #[.reg 0, .reg 1, .reg 2] #[0])) #[credit],
    block #[.scalar, owned .shared, owned .unique, owned .unique, owned .shared]
      #[.releaseShared (.reg 4), .releaseShared (.reg 1)] (.jump (edge 3 #[.reg 0, .reg 3, .reg 2] #[0])) #[credit],
    block #[owned .shared, owned .unique, owned .unique]
      #[.allocWith 0 .unique cid #[.reg 1, .reg 2], .dropUnique (.reg 3)] (.ret (.reg 0)) #[credit]]

/-- A shared leaf remains unaliased. Its optional reset credit survives an
allocating call, is refined by a branch, reused, reset, and discarded. -/
def hotCredit : IxIR2.Function :=
  let body := fun credit => block #[.owned .shared]
    #[.allocWith 0 .shared cid #[.reg 0], .resetShared (.reg 1) cid, .discardCredit 1]
      (.ret (.reg 2)) #[credit]
  function #[.shared] #[
    block #[.owned .shared] #[.alloc .shared cid #[.reg 0], .resetShared (.reg 1) cid, .call helper #[.reg 2]]
      (.branchCredit 0 (edge 1 #[.reg 3] #[0]) (edge 2 #[.reg 3] #[0])),
    body (.required (layout .shared).identity), body (.optional (layout .shared).identity)]

def leafSwitch : IxIR2.Function := function #[.shared] #[
  block #[.owned .shared] #[.alloc .unique cid #[.lit (.nat 19)]]
    (.switchValue (.reg 1) #[⟨cid, edge 1 #[.reg 0, .reg 1]⟩] none),
  block #[.owned .shared, .owned .unique] #[.takeUnique (.reg 1) cid, .discardCredit 0, .dropUnique (.reg 2)] (.ret (.reg 0))]

def eightHelper : IxIR2.Function := function #[] #[block #[]
  ((List.range 8).flatMap fun index => [.alloc .unique cid #[.lit (.nat 19)], .dropUnique (.reg index)]).toArray
    (.ret (.lit (.nat 0)))]

def arenaLimit (extra : Bool := false) : IxIR2.Function := function #[.shared] #[block #[.owned .shared]
  (((List.range 8).flatMap fun index => [IxIR2.Instr.call helper #[], .releaseShared (.reg (index + 1))]) ++
    if extra then [IxIR2.Instr.alloc .unique cid #[.lit (.nat 19)], .dropUnique (.reg 9)] else []).toArray (.ret (.reg 0))]

def artifact (name : String) : Wire.Artifact :=
  let fields := if name == "unique-diamond" then 2 else 1
  let definition := if name == "unique-diamond" then uniqueDiamond
    else if name == "hot-credit" then hotCredit
    else if name == "leaf-switch" then leafSwitch else arenaLimit (name == "arena-overflow")
  let dependencies := if name == "leaf-switch" then [] else [(helper, Decl.fn
    (if name == "arena-limit" || name == "arena-overflow" then eightHelper else allocatingHelper fields))]
  { policy := {
      semantics := Wire.semanticsVersion, validator := Wire.validatorVersion,
      lowering := "physical-leaf-cfg-fixture/1", passes := #[], layout := "baseline-constructor-world/0", credits := .suspendedCallsV1 }
    dependencies := #[], layouts := #[layout .unique, layout .shared]
    schemas := #[⟨.unique, cid, ⟨(layout .unique).identity, Array.replicate fields .unique⟩⟩,
      ⟨.shared, cid, ⟨(layout .shared).identity, Array.replicate fields .shared⟩⟩]
    scalarLeaves := #[]
    program := {
      declarations := dependencies ++ [(root, .fn definition)]
      main := function #[] #[block #[] #[] (.ret (.lit (.nat 0)))] } }

def cfgNames : List String := ["unique-diamond", "hot-credit", "leaf-switch", "arena-limit"]

def rawExpected (name : String) (a b : Nat) : Nat :=
  if name == "unique-diamond" then if a == 0 then b else a - 1 else a

end Compilatrix.X86.PhysicalHeap.Examples
