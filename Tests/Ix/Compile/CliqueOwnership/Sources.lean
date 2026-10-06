/-
  Sources of the clique-ownership regression suite (`clique-ownership`,
  `Tests.Ix.Compile.CliqueOwnership`).

  Each mutual block is ordinary Lean in which a **user** value, binder or
  relation has the shape of the clique's own encoding (the packed type of a
  `partial_fixpoint` clique, a relation over the packing type of a
  well-founded clique, a `brecOn`/`below` over the recursion's inductive),
  with homogeneous components so that a wrong permutation stays well typed.
  Every fixture is given in both member orders (`A`, `B`), so that one of them
  is transported by the compiler whatever the canonical order is.

  This file imports nothing beyond `Init`, so that it can also be compiled as
  a whole file by the compiler (`PASS3_CLIQUES_FILE=<this file>
  lake test -- --ignored pass3-cliques`).
-/
namespace Tests.Ix.Compile.CliqueOwnership.Src

/-! ## Helpers (user code, not part of any clique) -/

abbrev Fns := PProd (Nat → Option Nat) (Nat → Option Nat)

def userFns : Fns := ⟨fun _ => some 17, fun _ => some 29⟩

def applyUserProjection (q : Fns) (select : Fns → (Nat → Option Nat)) (n : Nat) : Option Nat :=
  select q n

structure PFBox where
  val : Fns

def userBox : PFBox := ⟨userFns⟩

def sideRank : PSum Nat Nat → Nat
  | .inl _ => 0
  | .inr _ => 1

set_option warn.classDefReducibility false in
def userWF (α : Type) (rank : α → Nat) : WellFoundedRelation α :=
  invImage rank (inferInstance : WellFoundedRelation Nat)

structure RelBox where
  r : WellFoundedRelation (PSum Nat Nat)

def userRelBox : RelBox := ⟨userWF (PSum Nat Nat) sideRank⟩

/-- A user record with a binary function field over the packing type (the
shape of `WellFoundedRelation.rel`, but not a relation). -/
structure UserFn (α : Type) where
  apply : α → α → Nat

def distinguish : PSum Nat Nat → PSum Nat Nat → Nat
  | .inl _, _ => 17
  | .inr _, _ => 29

def userFn : UserFn (PSum Nat Nat) := ⟨distinguish⟩

/-! Oracles: what a recursive call returns in the one-step evaluation of a
fixpoint's functional (member `j` of a clique answers with `oracleJ`). -/
def pfOracle0 : Nat → Option Nat := fun n => some (1000 + n)
def pfOracle1 : Nat → Option Nat := fun n => some (2000 + n)
def wfPropOracle0 : Nat → Prop := fun n => n = 1000
def wfPropOracle1 : Nat → Prop := fun n => n = 2000
def wfNatOracle0 : Nat → Nat := fun n => 1000 + n
def wfNatOracle1 : Nat → Nat := fun n => 2000 + n

/-! ## Partial fixpoint -/

/-! PF1 (the reproduction of F1): a user lambda over the packed type,
passed to a higher-order function. `first userFns 0 = some 17`. -/
namespace PF1A
mutual
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then applyUserProjection q (fun p => p.fst) n else second q (n - 1)
partial_fixpoint
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
end
end PF1A
namespace PF1B
mutual
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then applyUserProjection q (fun p => p.fst) n else second q (n - 1)
partial_fixpoint
end
end PF1B

/-! PF2: a user value of the packed type under a `let`. -/
namespace PF2A
mutual
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (let p : Fns := q; p.fst n) else second q (n - 1)
partial_fixpoint
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
end
end PF2A
namespace PF2B
mutual
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (let p : Fns := q; p.fst n) else second q (n - 1)
partial_fixpoint
end
end PF2B

/-! PF3: a user value of the packed type inside a proposition (the
condition of an `if`, and its decision procedure). -/
namespace PF3A
mutual
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (if q.fst 0 = some 17 then some 1 else some 2) else second q (n - 1)
partial_fixpoint
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
end
end PF3A
namespace PF3B
mutual
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (if q.fst 0 = some 17 then some 1 else some 2) else second q (n - 1)
partial_fixpoint
end
end PF3B

/-! PF4: a user value of the packed type as a field of a user structure. -/
namespace PF4A
mutual
def first (b : PFBox) (n : Nat) : Option Nat :=
  if n = 0 then b.val.fst n else second b (n - 1)
partial_fixpoint
def second (b : PFBox) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first b (n - 1)
partial_fixpoint
end
end PF4A
namespace PF4B
mutual
def second (b : PFBox) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first b (n - 1)
partial_fixpoint
def first (b : PFBox) (n : Nat) : Option Nat :=
  if n = 0 then b.val.fst n else second b (n - 1)
partial_fixpoint
end
end PF4B

/-! PF2C, PF3C, PF4C: PF2–PF4 with the packed type spelled out (`PProd …`
rather than the abbreviation `Fns`) and the user value bound by a binder or
built in place; the projection is taken unapplied (`let g := p.fst`), the form
in which the shape-based transport sees a path. -/
namespace PF2CA
mutual
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (let p : PProd (Nat → Option Nat) (Nat → Option Nat) := q; let g := p.fst; g n)
  else second q (n - 1)
partial_fixpoint
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
end
end PF2CA
namespace PF2CB
mutual
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (let p : PProd (Nat → Option Nat) (Nat → Option Nat) := q; let g := p.fst; g n)
  else second q (n - 1)
partial_fixpoint
end
end PF2CB
namespace PF3CA
mutual
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then
    (fun p : PProd (Nat → Option Nat) (Nat → Option Nat) =>
      let g := p.fst; if g 0 = some 17 then some 1 else some 2) q
  else second q (n - 1)
partial_fixpoint
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
end
end PF3CA
namespace PF3CB
mutual
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then
    (fun p : PProd (Nat → Option Nat) (Nat → Option Nat) =>
      let g := p.fst; if g 0 = some 17 then some 1 else some 2) q
  else second q (n - 1)
partial_fixpoint
end
end PF3CB
namespace PF4CA
mutual
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (let g := (PFBox.mk q).val.fst; g n) else second q (n - 1)
partial_fixpoint
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
end
end PF4CA
namespace PF4CB
mutual
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (let g := (PFBox.mk q).val.fst; g n) else second q (n - 1)
partial_fixpoint
end
end PF4CB

/-! PF5: the recursive calls themselves inside a user lambda handed to a
higher-order function (the `Option` bind of a `do` block); the encoding's own paths must move. -/
namespace PF5A
mutual
def first (n : Nat) : Option Nat :=
  if n = 0 then some 5 else do
    let v ← second (n - 1)
    pure (v + 1)
partial_fixpoint
def second (n : Nat) : Option Nat :=
  if n = 0 then some 7 else do
    let v ← first (n - 1)
    pure (v + 2)
partial_fixpoint
end
end PF5A
namespace PF5B
mutual
def second (n : Nat) : Option Nat :=
  if n = 0 then some 7 else do
    let v ← first (n - 1)
    pure (v + 2)
partial_fixpoint
def first (n : Nat) : Option Nat :=
  if n = 0 then some 5 else do
    let v ← second (n - 1)
    pure (v + 1)
partial_fixpoint
end
end PF5B

/-! PF6: a user function returning a value of the packed type, projected
unapplied. -/
def userPacked (q : Fns) : Fns := q

namespace PF6A
mutual
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (let g := (userPacked q).fst; g n) else second q (n - 1)
partial_fixpoint
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
end
end PF6A
namespace PF6B
mutual
def second (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first q (n - 1)
partial_fixpoint
def first (q : Fns) (n : Nat) : Option Nat :=
  if n = 0 then (let g := (userPacked q).fst; g n) else second q (n - 1)
partial_fixpoint
end
end PF6B

/-! PF7 (nested cliques): another clique's packed fixpoint, of the same
packed type, used in this clique's body. -/
namespace PF7A
mutual
noncomputable def first (n : Nat) : Option Nat :=
  if n = 0 then (let g := PF5A.first.mutual.fst; g 0) else second (n - 1)
partial_fixpoint
noncomputable def second (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first (n - 1)
partial_fixpoint
end
end PF7A
namespace PF7B
mutual
noncomputable def second (n : Nat) : Option Nat :=
  if n = 0 then some 31 else first (n - 1)
partial_fixpoint
noncomputable def first (n : Nat) : Option Nat :=
  if n = 0 then (let g := PF5A.first.mutual.fst; g 0) else second (n - 1)
partial_fixpoint
end
end PF7B

/-! ## Well-founded -/

/-! WF1 (the reproduction of F2): a user `WellFoundedRelation` over the
packing type. `first 0` is `0 < 1`. -/
namespace WF1A
mutual
def first (n : Nat) : Prop :=
  if n = 0 then (userWF (PSum Nat Nat) sideRank).rel (PSum.inl 0) (PSum.inr 0)
  else second (n - 1)
termination_by n
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
end
end WF1A
namespace WF1B
mutual
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
def first (n : Nat) : Prop :=
  if n = 0 then (userWF (PSum Nat Nat) sideRank).rel (PSum.inl 0) (PSum.inr 0)
  else second (n - 1)
termination_by n
end
end WF1B

/-! WF2: the user relation applied to a user value of the packing type
bound by a `let`. -/
namespace WF2A
mutual
def first (n : Nat) : Prop :=
  if n = 0 then
    (let p : PSum Nat Nat := PSum.inl 0; (userWF (PSum Nat Nat) sideRank).rel p (PSum.inr 0))
  else second (n - 1)
termination_by n
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
end
end WF2A
namespace WF2B
mutual
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
def first (n : Nat) : Prop :=
  if n = 0 then
    (let p : PSum Nat Nat := PSum.inl 0; (userWF (PSum Nat Nat) sideRank).rel p (PSum.inr 0))
  else second (n - 1)
termination_by n
end
end WF2B

/-! WF3: the user relation as a field of a user structure. -/
namespace WF3A
mutual
def first (n : Nat) : Prop :=
  if n = 0 then userRelBox.r.rel (PSum.inl 0) (PSum.inr 0) else second (n - 1)
termination_by n
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
end
end WF3A
namespace WF3B
mutual
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
def first (n : Nat) : Prop :=
  if n = 0 then userRelBox.r.rel (PSum.inl 0) (PSum.inr 0) else second (n - 1)
termination_by n
end
end WF3B

/-! WF4: `InvImage` over the packing type, written by the user. -/
namespace WF4A
mutual
def first (n : Nat) : Prop :=
  if n = 0 then InvImage (· < ·) sideRank (PSum.inl 0) (PSum.inr 0) else second (n - 1)
termination_by n
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
end
end WF4A
namespace WF4B
mutual
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
def first (n : Nat) : Prop :=
  if n = 0 then InvImage (· < ·) sideRank (PSum.inl 0) (PSum.inr 0) else second (n - 1)
termination_by n
end
end WF4B

/-! WF5: the user relation passed whole to a user lambda (the relation is
not applied where the transport could see its arguments). -/
namespace WF5A
mutual
def first (n : Nat) : Prop :=
  if n = 0 then
    (fun r : PSum Nat Nat → PSum Nat Nat → Prop => r (PSum.inl 0) (PSum.inr 0))
      (userWF (PSum Nat Nat) sideRank).rel
  else second (n - 1)
termination_by n
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
end
end WF5A
namespace WF5B
mutual
def second (n : Nat) : Prop :=
  if n = 0 then True else first (n - 1)
termination_by n
def first (n : Nat) : Prop :=
  if n = 0 then
    (fun r : PSum Nat Nat → PSum Nat Nat → Prop => r (PSum.inl 0) (PSum.inr 0))
      (userWF (PSum Nat Nat) sideRank).rel
  else second (n - 1)
termination_by n
end
end WF5B

/-! WF6: data computed from user values of the packing type (no relation),
and recursive calls through the encoding. -/
namespace WF6A
mutual
def first (n : Nat) : Nat :=
  if n = 0 then sideRank (PSum.inl 0) * 10 + sideRank (PSum.inr 0) else second (n - 1) + 1
termination_by n
def second (n : Nat) : Nat :=
  if n = 0 then 31 else first (n - 1) + 2
termination_by n
end
end WF6A
namespace WF6B
mutual
def second (n : Nat) : Nat :=
  if n = 0 then 31 else first (n - 1) + 2
termination_by n
def first (n : Nat) : Nat :=
  if n = 0 then sideRank (PSum.inl 0) * 10 + sideRank (PSum.inr 0) else second (n - 1) + 1
termination_by n
end
end WF6B

/-! WF7: a user record's function field applied to injections of the
packing type, the shape of the relation (ported from the deleted
`clique-transport` control (g) of the shape route, which once changed this
value from 17 to 29). `first 0 = 17`. -/
namespace WF7A
mutual
def first (n : Nat) : Nat :=
  if n = 0 then userFn.apply (PSum.inl 0) (PSum.inr 0) else second (n - 1) + 1
termination_by n
def second (n : Nat) : Nat :=
  if n = 0 then 31 else first (n - 1) + 2
termination_by n
end
end WF7A
namespace WF7B
mutual
def second (n : Nat) : Nat :=
  if n = 0 then 31 else first (n - 1) + 2
termination_by n
def first (n : Nat) : Nat :=
  if n = 0 then userFn.apply (PSum.inl 0) (PSum.inr 0) else second (n - 1) + 1
termination_by n
end
end WF7B

/-! ## Structural -/

/-! S1: a user's own `Nat.brecOn` whose motive has the shape of the clique's
packed motive, projected by field notation (`PProd.fst`). `first 0 = 17`. -/
namespace S1A
mutual
noncomputable def first : Nat → Nat
  | 0 => (Nat.brecOn (motive := fun _ => PProd Nat Nat) 0 (fun _ _ => ⟨17, 29⟩)).fst
  | n + 1 => second n
noncomputable def second : Nat → Nat
  | 0 => 31
  | n + 1 => first n
end
end S1A
namespace S1B
mutual
noncomputable def second : Nat → Nat
  | 0 => 31
  | n + 1 => first n
noncomputable def first : Nat → Nat
  | 0 => (Nat.brecOn (motive := fun _ => PProd Nat Nat) 0 (fun _ _ => ⟨17, 29⟩)).fst
  | n + 1 => second n
end
end S1B

/-! S2: a user binder whose type is a `below` dictionary of the recursion's
inductive with a packed-shaped motive, used through field notation. -/
def userBelow : Nat.below (motive := fun _ => PProd Nat Nat) 1 :=
  PProd.mk (PProd.mk 17 29) PUnit.unit

namespace S2A
mutual
def first : Nat → Nat
  | 0 => (fun (d : Nat.below (motive := fun _ => PProd Nat Nat) 1) =>
      PProd.fst (PProd.fst d)) userBelow
  | n + 1 => second n
def second : Nat → Nat
  | 0 => 31
  | n + 1 => first n
end
end S2A
namespace S2B
mutual
def second : Nat → Nat
  | 0 => 31
  | n + 1 => first n
def first : Nat → Nat
  | 0 => (fun (d : Nat.below (motive := fun _ => PProd Nat Nat) 1) =>
      PProd.fst (PProd.fst d)) userBelow
  | n + 1 => second n
end
end S2B

/-! S3: ordinary structural recursion (no user encoding-shaped term): the
transport must still move it (control for the canonicity cost). -/
namespace S3A
mutual
def first : Nat → Nat
  | 0 => 5
  | n + 1 => second n + 1
def second : Nat → Nat
  | 0 => 7
  | n + 1 => first n + 2
end
end S3A
namespace S3B
mutual
def second : Nat → Nat
  | 0 => 7
  | n + 1 => first n + 2
def first : Nat → Nat
  | 0 => 5
  | n + 1 => second n + 1
end
end S3B

/-! S4: the recursion's dictionary threaded through a nested `match` with an
equation binder (`match h : n`), so the matcher takes extra arguments besides
the dictionary (control: must be transported). -/
namespace S4A
mutual
def first : Nat → Nat
  | 0 => 5
  | n + 1 => match _h : n with
    | 0 => second 0 + 1
    | m + 1 => second (m + 1) + 2
def second : Nat → Nat
  | 0 => 7
  | n + 1 => first n + 3
end
end S4A
namespace S4B
mutual
def second : Nat → Nat
  | 0 => 7
  | n + 1 => first n + 3
def first : Nat → Nat
  | 0 => 5
  | n + 1 => match _h : n with
    | 0 => second 0 + 1
    | m + 1 => second (m + 1) + 2
end
end S4B

/-! ## Recovery (F3b)

R1: two members whose bodies differ only where `second` reads a user's
`below` value (`d.1.2`, the place a dictionary path to `second n` would be)
and `first` calls `second n`. Read as a recursive call, the user's path gives
both members one recovered specification, so the clique order puts them in
one class and O17 would alias `second` to `first`: `first 1 = 5`,
`second 1 = 29`. (The path must be a primitive projection for the recovery to
read it; the test rewrites Lean's `PProd.fst/snd` applications into those.) -/
def userBelowAt : (n : Nat) → Nat.below (motive := fun _ => PProd Nat Nat) n
  | 0 => PUnit.unit
  | n + 1 => PProd.mk (PProd.mk 17 29) (userBelowAt n)

/-- A user's higher-order function taking a `below` value (so that the user's
binder `d` survives elaboration as a lambda argument, not a β-redex). -/
def applyBelow (n : Nat) (b : Nat.below (motive := fun _ => PProd Nat Nat) n)
    (k : Nat.below (motive := fun _ => PProd Nat Nat) n → Nat) : Nat := k b

namespace R1A
mutual
def first : Nat → Nat
  | 0 => 5
  | n + 1 => applyBelow (Nat.succ n) (userBelowAt (Nat.succ n))
      (fun (d : Nat.below (motive := fun _ => PProd Nat Nat) (Nat.succ n)) =>
        second n + 0 * first n + 0 * PProd.fst (PProd.fst d))
def second : Nat → Nat
  | 0 => 5
  | n + 1 => applyBelow (Nat.succ n) (userBelowAt (Nat.succ n))
      (fun (d : Nat.below (motive := fun _ => PProd Nat Nat) (Nat.succ n)) =>
        PProd.snd (PProd.fst d) + 0 * first n + 0 * PProd.fst (PProd.fst d))
end
end R1A

namespace R1B
mutual
def second : Nat → Nat
  | 0 => 5
  | n + 1 => applyBelow (Nat.succ n) (userBelowAt (Nat.succ n))
      (fun (d : Nat.below (motive := fun _ => PProd Nat Nat) (Nat.succ n)) =>
        PProd.snd (PProd.fst d) + 0 * first n + 0 * PProd.fst (PProd.fst d))
def first : Nat → Nat
  | 0 => 5
  | n + 1 => applyBelow (Nat.succ n) (userBelowAt (Nat.succ n))
      (fun (d : Nat.below (motive := fun _ => PProd Nat Nat) (Nat.succ n)) =>
        second n + 0 * first n + 0 * PProd.fst (PProd.fst d))
end
end R1B

end Tests.Ix.Compile.CliqueOwnership.Src
