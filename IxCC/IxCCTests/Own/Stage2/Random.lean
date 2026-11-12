import IxCCTests.Own.Owned.Oracle
import IxCCTests.Own.Owned.Mutate

/-! # Heap stage 2: random mutants (probe)

Random edits of one function body, for the probe's random campaign (`Main.campaign`): insert an
`inc`/`dec` of a variable of the body at a random node, delete, move or duplicate an action, move
an `inc x` to another node that uses `x` (another occurrence becomes the "last use"), delete the
`inc` after a projection, delete a `dec` of a variable that a primitive reads. Superseded by the
site-directed campaign (`IxCCTests.Own.Owned.Sites`). -/

set_option autoImplicit false

namespace IxCCTests.Own.Stage2

open IxCC IxCC.Own.Plain IxCCTests.Own.Owned
open IxCC.Own (RVal Heap)
open IxCC.Fir (Var)

/-! ## Edits of one body, by preorder position -/

partial def insertAt (target : Nat) (a : Action) (c : Code) : StateM Nat Code := do
  let i ← get
  set (i + 1)
  let c' ← match c with
    | .act a' k => return .act a' (← insertAt target a k)
    | .bind x r k => return .bind x r (← insertAt target a k)
    | .jp j ps cs r b k => do
      let b' ← insertAt target a b
      return .jp j ps cs r b' (← insertAt target a k)
    | .case x alts d => do
      let alts' ← alts.mapM fun (.mk key b) => do return Alt.mk key (← insertAt target a b)
      let d' ← match d with
        | some b => some <$> insertAt target a b
        | none => pure none
      return .case x alts' d'
    | t => return t
  return if i == target then .act a c' else c'

/-- Delete the `target`-th action (preorder); the state records it. -/
partial def deleteAct (target : Nat) (c : Code) : StateM (Nat × Option Action) Code := do
  match c with
  | .act a k =>
    let (i, found) ← get
    set (i + 1, found)
    let k' ← deleteAct target k
    if i == target then
      modify fun (n, _) => (n, some a)
      return k'
    else return .act a k'
  | .bind x r k => return .bind x r (← deleteAct target k)
  | .jp j ps cs r b k => do
    let b' ← deleteAct target b
    return .jp j ps cs r b' (← deleteAct target k)
  | .case x alts d => do
    let alts' ← alts.mapM fun (.mk key b) => do return Alt.mk key (← deleteAct target b)
    let d' ← match d with
      | some b => some <$> deleteAct target b
      | none => pure none
    return .case x alts' d'
  | t => return t

/-- Preorder facts: node count, the actions in order, and for each node the variables it uses. -/
partial def nodes (c : Code) : StateM (List (Option Action × List Var)) Unit := do
  match c with
  | .act a k => modify (· ++ [(some a, [])]); nodes k
  | .bind x r k => modify (· ++ [(none, x :: rhsUses r)]); nodes k
  | .jp _ ps cs _ b k => modify (· ++ [(none, ps ++ cs)]); nodes b; nodes k
  | .case x alts d =>
    modify (· ++ [(none, [x])])
    for (.mk _ b) in alts do nodes b
    if let some b := d then nodes b
  | .jmp _ args | .tcall _ args => modify (· ++ [(none, argVars args)])
  | .ret a => modify (· ++ [(none, argVars [a])])
  | .trap => modify (· ++ [(none, [])])

partial def primVars : Code → List Var
  | .act _ k => primVars k
  | .bind _ (.prim _ args) k => argVars args ++ primVars k
  | .bind _ _ k => primVars k
  | .jp _ _ _ _ b k => primVars b ++ primVars k
  | .case _ alts d => (alts.flatMap fun (.mk _ b) => primVars b) ++ (d.map primVars).getD []
  | _ => []

instance : Inhabited Action := ⟨.dec 0⟩

inductive Op where
  | insInc | insDec | delete | move | dup | moveIncToUse | dropProjInc | dropPrimArgDec
  deriving Repr, BEq, Inhabited

def Op.all : List Op := [.insInc, .insDec, .delete, .move, .dup, .moveIncToUse, .dropProjInc, .dropPrimArgDec]

def Op.name : Op → String
  | .insInc => "insert-inc" | .insDec => "insert-dec" | .delete => "delete" | .move => "move"
  | .dup => "duplicate" | .moveIncToUse => "move-inc-to-another-use"
  | .dropProjInc => "drop-inc-after-projection" | .dropPrimArgDec => "drop-dec-of-primitive-argument"

/-- One random edit; `none` if the op has no site in this body. -/
def applyOp (op : Op) (params : List Var) (c : Code) (r : Rng) : Option (Code × String) × Rng :=
  let ((), facts) := (nodes c).run []
  let n := facts.length
  let acts := (facts.filterMap (·.1))
  let vars := (params ++ facts.flatMap (·.2)).eraseDups
  let ins (pos : Nat) (a : Action) (c : Code) : Code := ((insertAt pos a c).run 0).1
  let del (i : Nat) (c : Code) : Code × Option Action := let (c', (_, a)) := (deleteAct i c).run (0, none); (c', a)
  match op with
  | .insInc | .insDec =>
    if vars.isEmpty then (none, r) else
    let (x, r) := r.pick vars
    let (pos, r) := r.next n
    let a := if op == .insInc then Action.inc x 1 else .dec x
    (some (ins pos a c, s!"{op.name} {repr a} at node {pos}"), r)
  | .delete =>
    if acts.isEmpty then (none, r) else
    let (i, r) := r.next acts.length
    let (c', a) := del i c
    (some (c', s!"delete action {i} {repr a}"), r)
  | .move =>
    if acts.isEmpty then (none, r) else
    let (i, r) := r.next acts.length
    let (c', a) := del i c
    let (pos, r) := r.next (n - 1)
    match a with
    | some a => (some (ins pos a c', s!"move action {i} {repr a} to node {pos}"), r)
    | none => (none, r)
  | .dup =>
    if acts.isEmpty then (none, r) else
    let (i, r) := r.next acts.length
    let (_, a) := del i c
    let (pos, r) := r.next n
    match a with
    | some a => (some (ins pos a c, s!"duplicate action {i} {repr a} at node {pos}"), r)
    | none => (none, r)
  | .moveIncToUse =>
    let incs := (acts.zipIdx).filter fun (a, _) => match a with | .inc .. => true | _ => false
    if incs.isEmpty then (none, r) else
    let ((a, i), r) := r.pick incs
    let x := match a with | .inc x _ => x | .dec x => x
    let (c', _) := del i c
    let ((), facts') := (nodes c').run []
    let uses := (facts'.zipIdx).filterMap fun ((_, vs), p) => if vs.contains x then some p else none
    if uses.isEmpty then (none, r) else
    let (pos, r) := r.pick uses
    (some (ins pos a c', s!"move inc v{x} (action {i}) before node {pos} using it"), r)
  | .dropProjInc =>
    let (t, r) := r.next 16
    match mutant .borrowedConsumed t params c with
    | some c' => (some (c', s!"drop the inc after projection site {t}"), r)
    | none => (none, r)
  | .dropPrimArgDec =>
    let pv := primVars c
    let decs := (acts.zipIdx).filter fun (a, _) => match a with | .dec x => pv.contains x | _ => false
    if decs.isEmpty then (none, r) else
    let ((a, i), r) := r.pick decs
    let (c', _) := del i c
    (some (c', s!"drop {repr a} (action {i}) of a primitive's argument"), r)


end IxCCTests.Own.Stage2
