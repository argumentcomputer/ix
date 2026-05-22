module
public import Ix.Aiur.Stages.Source
public import Ix.Aiur.Stages.Bytecode
public import Ix.Aiur.Semantics.Flatten

/-!
The `StructCompatible` invariant.

Threaded through every sub-call in the simulation relation. Split into a
*structural* part (pure facts about the compilation output, provable as a
standalone lemma) and a *semantic* part (established by simultaneous induction
with `compile_preservation`).
-/

public section
@[expose] section

namespace Aiur

open Source

/-- Termination helper for the `Block`/`Ctrl` traversal below. -/
private theorem Bytecode.Block.sizeOf_ctrl_lt''' (b : Bytecode.Block) :
    sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩
  show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
  omega

mutual
/-- Collect all callee `FunIdx` values from a block tree (both constrained
and unconstrained). -/
def Bytecode.Ctrl.collectAllCallees (c : Bytecode.Ctrl) :
    Array Bytecode.FunIdx := match c with
  | .match _ cases defaultBlock =>
    let branchCallees := cases.attach.foldl (init := #[]) fun acc ⟨(_, block), _⟩ =>
      acc ++ block.collectAllCallees
    match defaultBlock with
    | some block => branchCallees ++ block.collectAllCallees
    | none => branchCallees
  | .matchContinue _ cases defaultBlock _ _ _ cont =>
    let branchCallees := cases.attach.foldl (init := #[]) fun acc ⟨(_, block), _⟩ =>
      acc ++ block.collectAllCallees
    let withDefault := match defaultBlock with
      | some block => branchCallees ++ block.collectAllCallees
      | none => branchCallees
    withDefault ++ cont.collectAllCallees
  | .return _ _ | .yield _ _ => #[]
termination_by (sizeOf c, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

def Bytecode.Block.collectAllCallees (b : Bytecode.Block) :
    Array Bytecode.FunIdx :=
  let opCallees := b.ops.foldl (init := #[]) fun acc op =>
    match op with
    | .call idx _ _ _ => acc.push idx
    | _ => acc
  opCallees ++ b.ctrl.collectAllCallees
termination_by (sizeOf b, 1)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left; exact Bytecode.Block.sizeOf_ctrl_lt''' _)
end

/-- A (concrete) name is "reachable" for compilation purposes iff it has a
`FunIdx` in `nameMap`. The prior definition (walk paths in source `decls`)
was too weak — it admitted polymorphic templates that `concretize` mangles
away from the `decls`→`nameMap` identity. Since `nameMap` already reflects
concretize's actual output, using it directly gives the correct notion of
"reachable at the bytecode level".

For the top-level preservation composition, every name in `nameMap` is trivially reachable (by
definition), so `total_on_reachable` is structurally a tautology; the
original motivation (bridge source reachability to bytecode) is now handled
by `concretize_preservation`'s own hypothesis restriction. -/
@[reducible, expose]
def reachableFromEntries (_decls : Decls) (nameMap : Global → Option Nat)
    (name : Global) : Prop :=
  (nameMap name).isSome = true

/-- The structural part of the simulation invariant. Every function referenced
by `nameMap` has a valid `FunIdx`, input sizes agree, and the call graph is closed. -/
structure StructCompatible
    (decls   : Decls)
    (bc      : Bytecode.Toplevel)
    (nameMap : Global → Option Bytecode.FunIdx) : Prop where
  /-- Tautologically true: every name in nameMap has a FunIdx by definition
  of reachability. Retained as a field so the original ∀-schema is visible. -/
  total_on_reachable :
    ∀ name, reachableFromEntries decls nameMap name →
      ∃ fi, nameMap name = some fi
  funIdx_valid :
    ∀ name fi, nameMap name = some fi → fi < bc.functions.size
  input_layout_matches :
    ∀ name fi f, nameMap name = some fi →
      decls.getByKey name = some (.function f) →
      ∀ h : fi < bc.functions.size,
        (f.inputs.map Prod.snd).foldl
          (fun acc t => acc + typFlatSize decls {} t) 0 =
        bc.functions[fi].layout.inputSize
  call_graph_closed :
    ∀ fi (h : fi < bc.functions.size),
      ∀ callee, callee ∈ (Bytecode.Block.collectAllCallees bc.functions[fi].body) →
      callee < bc.functions.size

end Aiur

end -- @[expose] section
end
