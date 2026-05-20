module
public import Ix.Aiur.Stages.Bytecode
public import Ix.Aiur.Compiler.Layout

/-!
Return-group splitting for Aiur bytecode.

Each `Bytecode.Function` may carry multiple `Ctrl.return` sites tagged with
distinct group names. `Function.split` carves the function into one filtered
sub-function per group — control-flow paths that cannot reach a `return` of
the target group are pruned. The result is a sorted array of
`(groupName, filteredFunction)` pairs with selectors renumbered in
traversal order and `FunctionLayout` recomputed.
-/

public section
@[expose] section

namespace Aiur

namespace Bytecode

/-- Termination helper for the `Block`/`Ctrl` traversal below. -/
private theorem Block.sizeOf_ctrl_lt_split (b : Block) :
    sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩
  show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
  omega

/-! ## Collect return-group names -/

mutual
def Ctrl.collectGroups (c : Ctrl) : Array String := match c with
  | .return _ g _ => #[g]
  | .yield .. => #[]
  | .match _ cases default? =>
    let branchGroups := cases.attach.foldl (init := #[]) fun acc ⟨(_, blk), _⟩ =>
      acc ++ Block.collectGroups blk
    match default? with
    | some blk => branchGroups ++ Block.collectGroups blk
    | none => branchGroups
  | .matchContinue _ cases default? _ _ _ continuation =>
    let branchGroups := cases.attach.foldl (init := #[]) fun acc ⟨(_, blk), _⟩ =>
      acc ++ Block.collectGroups blk
    let withDefault := match default? with
      | some blk => branchGroups ++ Block.collectGroups blk
      | none => branchGroups
    withDefault ++ Block.collectGroups continuation
termination_by (sizeOf c, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

def Block.collectGroups (b : Block) : Array String := Ctrl.collectGroups b.ctrl
termination_by (sizeOf b, 1)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left; exact Block.sizeOf_ctrl_lt_split _)
end

def Function.returnGroups (f : Function) : Std.HashSet String :=
  (Block.collectGroups f.body).foldl (init := ({} : Std.HashSet String))
    fun acc g => acc.insert g

/-! ## Filter control-flow tree by target group

Single (non-mutual) recursion on `Ctrl`. The conditional `Option`-typed
constructor wrap is factored into `mkMatch`/`mkMatchContinue` helpers so
that each match arm of `filterGroup` is a single function-call expression
— Lean can then derive the unfold equation by `rfl`.

`Yield` branches always survive — they're anchored by the surrounding
`MatchContinue`'s continuation, not by terminal returns. -/

def Ctrl.mkMatch (scrut : ValIdx) (cases : Array (G × Block))
    (default? : Option Block) : Option Ctrl :=
  if cases.isEmpty && default?.isNone then none
  else some (.match scrut cases default?)

def Ctrl.mkMatchContinue (scrut : ValIdx) (cases : Array (G × Block))
    (default? : Option Block) (outputSize sharedAux sharedLookups : Nat)
    (cont : Block) : Option Ctrl :=
  if cases.isEmpty && default?.isNone then none
  else some (.matchContinue scrut cases default? outputSize sharedAux sharedLookups cont)

def Ctrl.filterGroup (target : String) : Ctrl → Option Ctrl
  | .return sel g vs => if g = target then some (.return sel g vs) else none
  | .yield sel vs => some (.yield sel vs)
  | .match scrut cases default? =>
    Ctrl.mkMatch scrut
      (cases.attach.foldl (init := (#[] : Array (G × Block))) fun acc ⟨(k, blk), _⟩ =>
        match Ctrl.filterGroup target blk.ctrl with
        | none => acc
        | some c => acc.push (k, { blk with ctrl := c }))
      (match default? with
       | none => none
       | some blk => (Ctrl.filterGroup target blk.ctrl).map ({ blk with ctrl := · }))
  | .matchContinue scrut cases default? outputSize sharedAux sharedLookups cont =>
    (Ctrl.filterGroup target cont.ctrl).bind fun c =>
      Ctrl.mkMatchContinue scrut
        (cases.attach.foldl (init := (#[] : Array (G × Block))) fun acc ⟨(k, blk), _⟩ =>
          match Ctrl.filterGroup target blk.ctrl with
          | none => acc
          | some c => acc.push (k, { blk with ctrl := c }))
        (match default? with
         | none => none
         | some blk => (Ctrl.filterGroup target blk.ctrl).map ({ blk with ctrl := · }))
        outputSize sharedAux sharedLookups
        { cont with ctrl := c }
termination_by c => sizeOf c
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have hb := Array.sizeOf_lt_of_mem ‹_ ∈ _›
       have hc := Block.sizeOf_ctrl_lt_split ‹Block›
       grind)
    | (have := Block.sizeOf_ctrl_lt_split ‹Block›; grind)
    | grind

def Block.filterGroup (target : String) (b : Block) : Option Block :=
  (Ctrl.filterGroup target b.ctrl).map ({ b with ctrl := · })

/-! ## Renumber selectors in traversal order -/

/-- Single recursion on `Ctrl` threading a `Nat` counter for selectors. The
returned pair is `(rewrittenCtrl, nextCounter)`. -/
def Ctrl.fixSelectors : Ctrl → Nat → Ctrl × Nat
  | .return _ g vs, n => (.return n g vs, n + 1)
  | .yield _ vs, n => (.yield n vs, n + 1)
  | .match scrut cases default?, n =>
    let (newCases, n) := cases.attach.foldl
      (init := ((#[] : Array (G × Block)), n))
      fun (acc, n) ⟨(k, blk), _⟩ =>
        let (c', n') := Ctrl.fixSelectors blk.ctrl n
        (acc.push (k, { blk with ctrl := c' }), n')
    let (newDefault, n) : Option Block × Nat := match default? with
      | none => (none, n)
      | some blk =>
        let (c', n') := Ctrl.fixSelectors blk.ctrl n
        (some { blk with ctrl := c' }, n')
    (.match scrut newCases newDefault, n)
  | .matchContinue scrut cases default? outputSize sharedAux sharedLookups cont, n =>
    let (newCases, n) := cases.attach.foldl
      (init := ((#[] : Array (G × Block)), n))
      fun (acc, n) ⟨(k, blk), _⟩ =>
        let (c', n') := Ctrl.fixSelectors blk.ctrl n
        (acc.push (k, { blk with ctrl := c' }), n')
    let (newDefault, n) : Option Block × Nat := match default? with
      | none => (none, n)
      | some blk =>
        let (c', n') := Ctrl.fixSelectors blk.ctrl n
        (some { blk with ctrl := c' }, n')
    let (c', n') := Ctrl.fixSelectors cont.ctrl n
    let newCont : Block := { cont with ctrl := c' }
    (.matchContinue scrut newCases newDefault outputSize sharedAux sharedLookups newCont, n')
termination_by c _ => sizeOf c
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have hb := Array.sizeOf_lt_of_mem ‹_ ∈ _›
       have hc := Block.sizeOf_ctrl_lt_split ‹Block›
       grind)
    | (have := Block.sizeOf_ctrl_lt_split ‹Block›; grind)
    | grind

def Block.fixSelectors (b : Block) (n : Nat) : Block × Nat :=
  let (c', n') := Ctrl.fixSelectors b.ctrl n
  ({ b with ctrl := c' }, n')

/-! ## Layout recompute -/

/-- Recompute the `FunctionLayout` of `f` by replaying `blockLayout` over the
current body. Mirrors `Concrete.Function.compile`: `+1` lookup for the
function's own return lookup. -/
def Function.recomputeLayout (f : Function) : FunctionLayout :=
  let (_, st) := Concrete.Bytecode.blockLayout f.body |>.run
    (.new f.layout.inputSize)
  { st.functionLayout with lookups := st.functionLayout.lookups + 1 }

/-- Renumber selectors via DFS counter, then recompute layout. Intended for
functions produced by `filterGroup`, whose selector indices and layout are
inherited from the pre-filter function. -/
def Function.fix (f : Function) : Function :=
  let (body', _) := Block.fixSelectors f.body 0
  let f := { f with body := body' }
  { f with layout := f.recomputeLayout }

/-! ## Top-level split -/

/-- Carve `f` into one filtered sub-function per return group. Result is sorted
by group name. Panics if a discovered group has no reachable path (cannot
happen for well-formed bytecode). -/
def Function.split (f : Function) : Array (String × Function) :=
  let groups := f.returnGroups.toArray.qsort fun a b => decide (a < b)
  groups.map fun g =>
    match Block.filterGroup g f.body with
    | none => panic! s!"function contains an unreachable group: {g}"
    | some body =>
      let filtered : Function := { f with body }
      (g, filtered.fix)

/-- Populate `t.filteredFunctions` by splitting every function. Idempotent —
overwrites any existing entries. Should run after `deduplicate` and
`needsCircuit` so the split reflects the final function set. -/
def Toplevel.computeFiltered (t : Toplevel) : Toplevel :=
  { t with filteredFunctions := t.functions.map (·.split) }

end Bytecode

end Aiur

end -- @[expose] section
end
