module

public import Ix.GraphM
public import Ix.Ground
public import Ix.Compile.Parallel
import all IxC.Address.Core
import all Ix.Common
import all Ix.Environment
import all Ix.GraphM
import all Ix.Ground
import Std.Data.HashMap.Lemmas

public section

namespace Ix.Compile.FrontEnd

/-- Bound independent constant checks without tying them to the worker pool. -/
@[expose] def taskCount : Nat := 256

/-- Compute each constant's references independently, then insert them in the
original map iteration order. Every graph walk starts with its own empty memo. -/
@[expose] def graph (env : Environment) : Map Name (Set Name) :=
  (Parallel.map taskCount (fun (name, ci) => (name, (GraphM.run env .init (graphConst ci)).1))
    env.consts.toList.toArray).foldl (fun out (name, refs) => out.insert name refs) {}

/-- Task evaluation preserves the graph's entries and insertion order. -/
@[csimp] theorem graph_eq : @GraphM.envSerial = @graph := by
  funext env
  simp only [graph, Parallel.map_eq, Array.foldl_map]
  unfold GraphM.envSerial
  simp only [Id.run, bind_pure, Std.HashMap.forIn_eq_forIn_toList,
    List.forIn_pure_yield_eq_foldl, List.foldl_toArray']
  rfl

/-- The original immediate-ground scan, before propagation. -/
@[expose] def immediateSerial (env : Environment) : Map Name GroundError := Id.run do
  let mut out : Map Name GroundError := {}
  for (name, ci) in env.consts do
    match groundConstCheck ci env with
    | .error error => out := out.insert name error
    | .ok _ => pure ()
  return out

/-- Check constants independently and replay refusals in the original order.
This preserves both immediate errors and later propagation's worklist order. -/
@[expose] def immediate (env : Environment) : Map Name GroundError :=
  (Parallel.map taskCount (fun (name, ci) => (name, groundConstCheck ci env))
    env.consts.toList.toArray).foldl (fun out (name, result) =>
      match result with
      | .error error => out.insert name error
      | .ok _ => out) {}

theorem immediate_eq (env : Environment) : immediateSerial env = immediate env := by
  simp only [immediate, Parallel.map_eq, Array.foldl_map]
  unfold immediateSerial
  simp only [Id.run, bind_pure, Std.HashMap.forIn_eq_forIn_toList, List.foldl_toArray']
  generalize env.consts.toList = constants
  generalize ({} : Map Name GroundError) = initial
  induction constants generalizing initial with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name, ci⟩ := entry
    simp only [List.forIn_cons, List.foldl_cons]
    cases h : groundConstCheck ci env <;> simpa [h] using ih _

/-- The unchanged propagation, starting with the same ordered immediate errors. -/
@[expose] def ground (env : Environment) (inRefs : Map Name (Set Name)) : Map Name GroundError :=
  proliferateUngrounded (immediate env) inRefs

@[csimp] theorem ground_eq : @groundConsts = @ground := by
  funext env inRefs
  change proliferateUngrounded (immediateSerial env) inRefs =
    proliferateUngrounded (immediate env) inRefs
  rw [immediate_eq]

private theorem compare_address_self (h : Address) : compare h h = .eq :=
  @Std.ReflCmp.compare_self (List UInt8)
    (@compare (List UInt8) (@List.instOrd UInt8 UInt8.instOrd)) _
    h.hash.data.toList

private theorem nameCompare_self (a : Ix.Name) : Ix.nameCompare a a = .eq :=
  compare_address_self a.getHash

private theorem cmpHash_self (h : Address) : Ix.Name.cmpHash h h = .eq := by
  simp [Ix.Name.cmpHash, compare_address_self]

private theorem cmpRaw_self : ∀ (a : Ix.Name), Ix.Name.cmpRaw a a = .eq
  | .anonymous h => cmpHash_self h
  | .str p s h => by simp [Ix.Name.cmpRaw, cmpRaw_self p, cmpHash_self h]
  | .num p i h => by simp [Ix.Name.cmpRaw, cmpRaw_self p, cmpHash_self h]

theorem nameCompareExact_self (a : Ix.Name) : Ix.nameCompareExact a a = .eq := by
  simp [Ix.nameCompareExact, nameCompare_self, cmpRaw_self]

theorem nameCompareExact_self_beq (a : Ix.Name) : (Ix.nameCompareExact a a == .eq) = true := by
  rw [nameCompareExact_self]; decide

end Ix.Compile.FrontEnd
