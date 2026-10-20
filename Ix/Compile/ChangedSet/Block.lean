/- # The change predicate of a compiled inductive block

## Contract
Input: one compiled component (SCC) of a Lean inductive block, as the aux tail
sees it (`Ix.AuxGen.compileMutualAuxTail`, Rust `compile_mutual`) and as the
block's `Muts` record stores it (`Ixon.ConstantMetaInfo.muts`):
* `all`: Lean's block (`InductiveVal.all`, in Lean's order);
* `classes`: the component's classes in canonical order (Pass 1), each
  representative first;
* `layout?`: the component's nested-auxiliary layout (`Ixon.AuxLayout`),
  `none` when the block has no nested auxiliary.

Output: the change predicate `isChanged` (Def 3.1 under the compiler's
rules): fewer classes than Lean's `all`, a class representative out of `all`
order, or a nested auxiliary moved or evaporated. It is the predicate under
which both compilers register call-site plans today, which they still write
inline (`compileMutualAuxTail`'s `userLayoutChanged || auxLayoutChanged`,
Rust's `user_layout_changed || aux_layout_changed` in `compile_mutual`, the
decompile dual `installDecompileCallSitePlans`); the `changed-set` suite
checks it against both compilers' registrations. Pass 3's hook
`editChangedBlock` and the changed set (`Ix.Compile.ChangedSet`) read this
definition. `blockCauses` says why, with typed causes (`BlockCause`), and
refines it exactly: no cause exactly when the component is unchanged
(`blockCauses_isEmpty`).

Only the members of `all` count (`planClasses`): a class is restricted to
them and dropped when that leaves it empty.

## Shape (for the statements)
Pure and total, over arrays; no name is parsed (names are compared, by `==`,
which is equality of the stored hashes). Every definition is exposed.

## Collapse inside a component
Two members of an *inductive* component that share a class are a plan change
(`collapsed`): the component's recursor then has fewer motives than Lean's.
Two members of a *definition* component that share a class (a block-internal
alias fiber, `ALPHA-COLLAPSE.md` §8.4: the `perm` kind, K1) are no plan change
(the aux tail sees no `all` for a definition component, so `isChanged` is
false and the flip's hooks never run on one), but they change the shape of
Source's group: quotient Source collapses only fibers that span groups. The
changed set counts them through `componentChanged` (= `isChanged ||
collapsesInside`) and `componentCauses`; `componentChanged_of_isChanged` and
`collapsesInside_of_componentChanged` say that collapse inside is exactly the
difference. A definition component whose classes are only out of Lean's order
is not a cause (the renaming's order independence, K0).
-/
module
public import Ix.Ixon
@[expose] public section

namespace Ix.Compile.ChangedSet

open Ix (Name)

/-- Why a compiled inductive component is not Lean's block up to names. -/
inductive BlockCause where
  /-- The component holds fewer members of `all` than `all` has: Lean's block
  is spread over several components. -/
  | split
  /-- Two members of `all` share a class (α-collapse inside the block): fewer
  classes than members of `all`. -/
  | collapsed
  /-- As many classes as `all` has members, and a class representative that
  is not Lean's member at its position. -/
  | permuted
  /-- Lean's nested auxiliary at source position `source` (`all₀.rec_{source+1}`)
  is this component's canonical nested auxiliary `canonical ≠ source`. -/
  | nestedMoved (source canonical : Nat)
  /-- This component owns the evaporation of Lean's nested source position
  `source`: the auxiliary is no inductive of the component, and its recursor
  is the external head's. -/
  | nestedEvaporated (source : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

/-- The cause's tag, for reports. -/
def BlockCause.tag : BlockCause → String
  | .split => "split"
  | .collapsed => "collapsed"
  | .permuted => "permuted"
  | .nestedMoved .. => "nested-moved"
  | .nestedEvaporated _ => "nested-evaporated"

/-- `BlockCause` kinds, ignoring the positions. -/
def BlockCause.isNestedMoved : BlockCause → Bool
  | .nestedMoved .. => true
  | _ => false

def BlockCause.isNestedEvaporated : BlockCause → Bool
  | .nestedEvaporated _ => true
  | _ => false

/-- `AuxLayout.perm`'s out-of-component marker (`PERM_OUT_OF_SCC`, `u64::MAX`). -/
def permOut : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- The classes restricted to the members of `all`, empty classes dropped
(`compileMutualAuxTail`'s `planClassNames`). -/
def planClasses (all : Array Name) (classes : Array (Array Name)) : Array (Array Name) :=
  let lookup : Std.HashSet Name := all.foldl (init := {}) (·.insert ·)
  classes.filterMap fun cls =>
    let ns := cls.filter lookup.contains
    if ns.isEmpty then none else some ns

/-- A class representative out of `all` order, with as many classes as `all`
has members. -/
def outOfOrder (all : Array Name) (pc : Array (Array Name)) : Bool :=
  pc.size == all.size && (pc.zip all).any fun (cls, orig) => cls[0]? != some orig

/-- A nested auxiliary moved: a source position that is canonical in this
component at another position. -/
def nestedMoved (l : Ixon.AuxLayout) : Bool :=
  l.perm.zipIdx.any fun (i, j) => i != permOut && i.toNat != j

/-- A nested auxiliary evaporated in this component. -/
def nestedEvaporated (l : Ixon.AuxLayout) : Bool :=
  l.evaporated.any (· != 0)

/-- **The change predicate** (Def 3.1 under the compiler's rules), as the
plan registration computes it: `userLayoutChanged || auxLayoutChanged`. -/
def isChanged (all : Array Name) (classes : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) : Bool :=
  let pc := planClasses all classes
  let userChanged := !all.isEmpty && (pc.size < all.size || outOfOrder all pc)
  let auxChanged := match layout? with
    | some l => nestedEvaporated l || nestedMoved l
    | none => false
  userChanged || auxChanged

/-- The number of members of `all` the restricted classes hold. -/
def memberCount (pc : Array (Array Name)) : Nat :=
  pc.foldl (fun k cls => k + cls.size) 0

/-- The causes from the classes. A component can be both `split` and
`collapsed`; `collapsed` requires fewer classes than `all`, as the predicate
does, so that the causes refine it on every input. -/
def userCauses (all : Array Name) (classes : Array (Array Name)) : Array BlockCause :=
  if all.isEmpty then #[] else
  let pc := planClasses all classes
  let members := memberCount pc
  (if members < all.size then #[.split] else #[]) ++
  (if pc.size < all.size && pc.size < members then #[.collapsed] else #[]) ++
  (if outOfOrder all pc then #[.permuted] else #[])

/-- The causes from the nested layout, by source position. -/
def nestedCauses : Option Ixon.AuxLayout → Array BlockCause
  | none => #[]
  | some l =>
    l.perm.zipIdx.filterMap (fun (i, j) =>
        if i != permOut && i.toNat != j then some (.nestedMoved j i.toNat) else none) ++
    l.evaporated.zipIdx.filterMap (fun (e, j) =>
        if e != 0 then some (.nestedEvaporated j) else none)

/-- **Why the component is changed**: empty exactly when it is not
(`blockCauses_isEmpty`). -/
def blockCauses (all : Array Name) (classes : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) : Array BlockCause :=
  userCauses all classes ++ nestedCauses layout?

/-! ## The causes refine the predicate -/

theorem size_le_memberCount_aux (l : List (Array Name)) (k : Nat)
    (h : ∀ c ∈ l, c.size ≠ 0) :
    k + l.length ≤ l.foldl (fun k cls => k + cls.size) k := by
  induction l generalizing k with
  | nil => simp
  | cons c cs ih =>
    have hc : c.size ≠ 0 := h c (by simp)
    have := ih (k + c.size) (fun d hd => h d (by simp [hd]))
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- Every restricted class is nonempty. -/
theorem planClasses_nonempty (all : Array Name) (classes : Array (Array Name)) :
    ∀ c ∈ planClasses all classes, c.size ≠ 0 := by
  intro c hc
  unfold planClasses at hc
  simp only [Array.mem_filterMap] at hc
  obtain ⟨cls, _, h⟩ := hc
  split at h
  · cases h
  · rename_i hne
    cases h
    simpa [Array.isEmpty_iff_size_eq_zero] using hne

/-- At most as many restricted classes as members they hold. -/
theorem size_le_memberCount (all : Array Name) (classes : Array (Array Name)) :
    (planClasses all classes).size ≤ memberCount (planClasses all classes) := by
  have := size_le_memberCount_aux (planClasses all classes).toList 0
    (fun c hc => planClasses_nonempty all classes c (by simpa using hc))
  unfold memberCount
  rw [← Array.foldl_toList]
  simpa using this

theorem isEmpty_append {α : Type} (a b : Array α) :
    (a ++ b).isEmpty = (a.isEmpty && b.isEmpty) := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  simp only [List.append_toArray, List.isEmpty_toArray]
  cases a <;> cases b <;> rfl

theorem ite_true_false (b : Bool) : (if b = true then true else false) = b := by
  cases b <;> rfl

theorem filterMap_isEmpty {α β : Type} (xs : Array α) (h : α → Option β) :
    (xs.filterMap h).isEmpty = !xs.any (fun p => (h p).isSome) := by
  rcases xs with ⟨l⟩
  simp only [List.any_toArray]
  induction l with
  | nil => simp
  | cons a l ih => cases ha : h a <;> simp_all

theorem any_zipIdx_fst {α : Type} (xs : Array α) (p : α → Bool) :
    xs.zipIdx.any (fun q => p q.1) = xs.any p := by
  have := Array.any_map (f := Prod.fst) (p := p) (xs := xs.zipIdx)
  rw [Array.zipIdx_map_fst] at this
  exact this.symm

theorem filterMap_zipIdx_isEmpty {α β : Type} (xs : Array α) (f : α → Nat → Bool)
    (g : α → Nat → β) :
    (xs.zipIdx.filterMap (fun (x, j) => if f x j then some (g x j) else none)).isEmpty =
      !xs.zipIdx.any (fun (x, j) => f x j) := by
  rw [filterMap_isEmpty]
  congr 1
  congr 1
  funext ⟨x, j⟩
  by_cases hf : f x j <;> simp [hf]

theorem nestedCauses_isEmpty (layout? : Option Ixon.AuxLayout) :
    (nestedCauses layout?).isEmpty =
      !(match layout? with
        | some l => nestedEvaporated l || nestedMoved l
        | none => false) := by
  cases layout? with
  | none => rfl
  | some l =>
    simp only [nestedCauses, isEmpty_append, filterMap_isEmpty, nestedEvaporated, nestedMoved,
      ← any_zipIdx_fst l.evaporated]
    simp only [apply_ite Option.isSome, Option.isSome_some, Option.isSome_none, ite_true_false]
    cases l.evaporated.zipIdx.any (fun q => q.1 != 0) <;>
      cases l.perm.zipIdx.any (fun q => q.1 != permOut && q.1.toNat != q.2) <;> rfl

theorem userCauses_isEmpty (all : Array Name) (classes : Array (Array Name)) :
    (userCauses all classes).isEmpty =
      !(!all.isEmpty && ((planClasses all classes).size < all.size ||
        outOfOrder all (planClasses all classes))) := by
  have hle := size_le_memberCount all classes
  unfold userCauses
  by_cases he : all.isEmpty = true
  · simp [he]
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    rw [isEmpty_append, isEmpty_append]
    generalize memberCount (planClasses all classes) = m at hle
    generalize (planClasses all classes).size = k at hle ⊢
    generalize outOfOrder all (planClasses all classes) = oo
    by_cases h1 : m < all.size <;> by_cases h2 : k < all.size <;> by_cases h3 : k < m <;>
      cases oo <;> simp [h1, h2, h3] <;> omega

/-- **The causes refine the predicate**: no cause exactly when the component
is unchanged. -/
theorem blockCauses_isEmpty (all : Array Name) (classes : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) :
    (blockCauses all classes layout?).isEmpty = !isChanged all classes layout? := by
  unfold blockCauses
  rw [isEmpty_append, userCauses_isEmpty, nestedCauses_isEmpty]
  simp only [isChanged, Bool.not_or]


/-! ## Changed for the set: the plan predicate, and collapse inside a component

The set counts one more shape than the plan predicate: two members of a
component in one class, whatever the component's kind. For an inductive
component that is a plan change already (`collapsed`, with the members of
`all`); for a *definition* component the aux tail passes no `all` (it has no
inductive), so `isChanged` is false there, and the flip's hooks must not run
on it. Collapse inside a definition component is still not a renaming of
Source's group (Source groups definitions by component and collapses only
fibers that span groups), so the set counts it (`componentChanged`), with the
cause `collapsed` (`componentCauses`). A definition component's class order is
not a cause: Source's group order is Lean's name order, which the renaming's
order independence covers. -/

/-- Two members of the component share a class. -/
def collapsesInside (classes : Array (Array Name)) : Bool :=
  classes.any (1 < ·.size)

/-- **Changed for the set**: the plan predicate, or collapse inside the
component. `all` is Lean's block for an inductive component and empty for a
definition component, as the aux tail sees them. -/
def componentChanged (all : Array Name) (classes : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) : Bool :=
  isChanged all classes layout? || collapsesInside classes

/-- Why the component is changed for the set: `blockCauses`, and `collapsed`
when the component collapses inside and `blockCauses` does not say so. -/
def componentCauses (all : Array Name) (classes : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) : Array BlockCause :=
  let cs := blockCauses all classes layout?
  if collapsesInside classes && !cs.contains .collapsed then cs.push .collapsed else cs

/-- Every plan change is a change for the set (the flip's hooks run on a
subset of the set's components). -/
theorem componentChanged_of_isChanged {all : Array Name} {classes : Array (Array Name)}
    {layout? : Option Ixon.AuxLayout} (h : isChanged all classes layout? = true) :
    componentChanged all classes layout? = true := by
  simp [componentChanged, h]

/-- The difference is collapse inside the component: a component the set counts
and the plan predicate does not has two members in one class. -/
theorem collapsesInside_of_componentChanged {all : Array Name} {classes : Array (Array Name)}
    {layout? : Option Ixon.AuxLayout} (h : componentChanged all classes layout? = true)
    (hn : isChanged all classes layout? = false) : collapsesInside classes = true := by
  simpa [componentChanged, hn] using h

/-- A definition component, as the aux tail sees it (no `all`, no nested
layout): changed for the set exactly when it collapses inside, and never a
plan change. -/
theorem componentChanged_definitions (classes : Array (Array Name)) :
    isChanged #[] classes none = false ∧
      componentChanged #[] classes none = collapsesInside classes := by
  simp [componentChanged, isChanged]

/-- **The causes refine the set's predicate**: no cause exactly when the
component is unchanged for the set. -/
theorem componentCauses_isEmpty (all : Array Name) (classes : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) :
    (componentCauses all classes layout?).isEmpty = !componentChanged all classes layout? := by
  unfold componentCauses componentChanged
  have hb := blockCauses_isEmpty all classes layout?
  by_cases hc : collapsesInside classes = true
  · by_cases hk : (blockCauses all classes layout?).contains .collapsed = true
    · have hne : (blockCauses all classes layout?).isEmpty = false := by
        rw [Bool.eq_false_iff]
        intro he
        rw [Array.isEmpty_iff] at he
        simp [he] at hk
      simp [hc, hk, hne]
    · simp [hc, hk]
  · simp [hc, hb]

end Ix.Compile.ChangedSet

end
