import Lean

/-! Metadata on the binder spines an inductive declaration may carry
(`a98663c0`): between a family's parameters and its indices, and around and
inside a constructor field's domain, the positions the kernel admits (an
`mdata` on a parameter spine, or around a constructor's own binders, is
refused by the kernel: "incorrect number of parameters", "invalid return
type"). Both compilers must agree and every checker must accept. Elaboration
never puts metadata there, so the families are declared through `addDecl`,
with Lean's own `recOn`, `casesOn`, `below` and `brecOn`. The compiled bytes
are the same with and without `a98663c0`: the spine walks it repairs only
meet metadata at positions the kernel refuses.

Each `Plain*` family is the valid neighbour: the same family, elaborated
normally. The `rfl` theorems pin values. -/

open Lean Meta

namespace MdataSpine

inductive PlainIdx (α : Type) : Nat → Type where
  | nil : PlainIdx α 0
  | cons {n : Nat} : α → PlainIdx α n → PlainIdx α (n + 1)

inductive PlainW : Type where
  | leaf : PlainW
  | node : (Nat → PlainW) → PlainW

inductive PlainD : Type where
  | leaf : PlainD
  | node : PlainD → PlainD

def mark (e : Expr) : Expr := .mdata (KVMap.empty.insert `ixSpine (.ofBool true)) e

def declare (T : Name) (nParams : Nat) (ty : Expr) (ctors : List (Name × Expr)) : MetaM Unit := do
  let cs := ctors.map fun (n, t) => ({ name := T ++ n, type := t } : Constructor)
  addDecl (.inductDecl [] nParams [{ name := T, type := ty, ctors := cs }] false)
  mkRecOn T
  mkCasesOn T
  mkBelow T
  mkBRecOn T

run_meta do
  let nat := Expr.const ``Nat []
  let succ (e : Expr) := mkApp (.const ``Nat.succ []) e
  -- Idx : (α : Type) → [md] Nat → Type
  let I := `MdataSpine.Idx
  declare I 1 (.forallE `α (.sort 1) (mark (.forallE `idx nat (.sort 1) .default)) .default)
    [(`nil, .forallE `α (.sort 1) (mkApp2 (.const I []) (.bvar 0) (.const ``Nat.zero [])) .implicit),
     (`cons, .forallE `α (.sort 1) (.forallE `n nat (.forallE `a (.bvar 1)
        (.forallE `t (mkApp2 (.const I []) (.bvar 2) (.bvar 1))
          (mkApp2 (.const I []) (.bvar 3) (succ (.bvar 2))) .default) .default) .implicit) .implicit)]
run_meta do
  let nat := Expr.const ``Nat []
  -- W.node : (f : [md] (Nat → [md] W)) → W
  let W := `MdataSpine.W
  declare W 0 (.sort 1)
    [(`leaf, .const W []),
     (`node, .forallE `f (mark (.forallE `k nat (mark (.const W [])) .default)) (.const W []) .default)]
run_meta do
  -- D.node : (t : [md] D) → D
  let D := `MdataSpine.D
  declare D 0 (.sort 1)
    [(`leaf, .const D []), (`node, .forallE `t (mark (.const D [])) (.const D []) .default)]

noncomputable def idxLen {α : Type} : {n : Nat} → Idx α n → Nat
  | _, .nil => 0
  | _, .cons _ t => idxLen t + 1
noncomputable def plainIdxLen {α : Type} : {n : Nat} → PlainIdx α n → Nat
  | _, .nil => 0
  | _, .cons _ t => plainIdxLen t + 1

noncomputable def wDepth (t : W) : Nat := W.rec (motive := fun _ => Nat) 0 (fun _ ih => ih 0 + 1) t
noncomputable def plainWDepth (t : PlainW) : Nat :=
  PlainW.rec (motive := fun _ => Nat) 0 (fun _ ih => ih 0 + 1) t

noncomputable def dDepth : D → Nat
  | .leaf => 0
  | .node t => dDepth t + 1
noncomputable def plainDDepth : PlainD → Nat
  | .leaf => 0
  | .node t => plainDDepth t + 1

theorem idxLen_two : idxLen (Idx.cons 1 (Idx.cons 2 .nil) : Idx Nat 2) = 2 := rfl
theorem plainIdxLen_two : plainIdxLen (PlainIdx.cons 1 (PlainIdx.cons 2 .nil) : PlainIdx Nat 2) = 2 :=
  rfl
theorem wDepth_two : wDepth (.node fun _ => .node fun _ => .leaf) = 2 := rfl
theorem plainWDepth_two : plainWDepth (.node fun _ => .node fun _ => .leaf) = 2 := rfl
theorem dDepth_two : dDepth (.node (.node .leaf)) = 2 := rfl
theorem plainDDepth_two : plainDDepth (.node (.node .leaf)) = 2 := rfl

end MdataSpine
