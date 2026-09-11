import Ix.Compiler.IxIR1.Mono
import Ix.Compiler.IxIR1.Reclamation
import Ix.Compiler.IxIR1.Sim

/-!
# IxIR₁ evaluation modulo allocation history

Shrinking heap optimizations deliberately change cost counters, leave
different dead holes, and consequently assign different numeric locations to
later allocations.  Literal equality of `Store × RVal` is therefore too
strong for those passes.

`HeapHistoryIso` is the evaluator-facing relation for that boundary.  It is a
finite partial bijection which covers every live location, may retain pairs of
dead locations, and may omit unmatched dead holes.  Corresponding live boxes
agree in world, reference count, node identity, and recursively in their
children.  Cost counters are intentionally absent.

Retaining dead/dead pairs is important: recursive destruction may kill a
parent before traversing its saved children, and stale environment slots may
still name a consumed value even though well-moded code never uses it again.
The relation can preserve those historical names without pretending that a
dead slot is live.
-/

namespace Ix.Compiler.IxIR1.Sim

open Ix.Compiler.Ixon (Owned)

/-- A location relation covering all live nodes and optionally remembering
dead/dead location pairs.  Every related location is an already allocated
slot, which makes extension by fresh allocations unambiguous. -/
structure HeapHistoryIso (left right : Store) where
  locRel : Nat → Nat → Prop
  left_unique : ∀ {l r₁ r₂}, locRel l r₁ → locRel l r₂ → r₁ = r₂
  right_unique : ∀ {l₁ l₂ r}, locRel l₁ r → locRel l₂ r → l₁ = l₂
  left_bound : ∀ {l r}, locRel l r → l < left.nodes.size
  right_bound : ∀ {l r}, locRel l r → r < right.nodes.size
  left_total : ∀ {loc box}, left.get? loc = some box →
    ∃ rightLoc, locRel loc rightLoc
  right_total : ∀ {loc box}, right.get? loc = some box →
    ∃ leftLoc, locRel leftLoc loc
  related : ∀ {leftLoc rightLoc}, locRel leftLoc rightLoc →
    (left.get? leftLoc = none ∧ right.get? rightLoc = none) ∨
      ∃ leftBox rightBox,
        left.get? leftLoc = some leftBox ∧
        right.get? rightLoc = some rightBox ∧
        NodeBoxIso locRel leftBox rightBox

namespace HeapHistoryIso

/-- Canonical self-history: every already allocated slot is paired with
itself, including dead slots.  Closure supplies the corresponding relation
for children of live nodes. -/
def refl (store : Store) (closed : StoreClosed store) :
    HeapHistoryIso store store where
  locRel := fun left right => left = right ∧ left < store.nodes.size
  left_unique := by
    intro left right₁ right₂ h₁ h₂
    exact h₁.1.symm.trans h₂.1
  right_unique := by
    intro left₁ left₂ right h₁ h₂
    exact h₁.1.trans h₂.1.symm
  left_bound := fun h => h.2
  right_bound := by
    intro left right h
    simpa [h.1] using h.2
  left_total := by
    intro location box hget
    have hbound : location < store.nodes.size := by
      unfold Store.get? at hget
      rw [Option.bind_eq_some_iff] at hget
      obtain ⟨slot, hslot, _⟩ := hget
      exact (Array.getElem?_eq_some_iff.mp hslot).1
    exact ⟨location, rfl, hbound⟩
  right_total := by
    intro location box hget
    have hbound : location < store.nodes.size := by
      unfold Store.get? at hget
      rw [Option.bind_eq_some_iff] at hget
      obtain ⟨slot, hslot, _⟩ := hget
      exact (Array.getElem?_eq_some_iff.mp hslot).1
    exact ⟨location, rfl, hbound⟩
  related := by
    intro left right hrel
    obtain ⟨rfl, hbound⟩ := hrel
    cases hget : store.get? left with
    | none => exact .inl ⟨rfl, rfl⟩
    | some box =>
        let live := HeapIso.refl store closed
        have hlive : live.locRel left left := by
          exact ⟨rfl, box, hget⟩
        obtain ⟨leftBox, rightBox, hleft, hright, hbox⟩ :=
          live.related_live hlive
        have hleftBox : leftBox = box := Option.some.inj (hleft.symm.trans hget)
        have hrightBox : rightBox = box :=
          Option.some.inj (hright.symm.trans hget)
        subst leftBox
        subst rightBox
        refine .inr ⟨box, box, rfl, rfl, hbox.mono ?_⟩
        intro childLeft childRight hchild
        obtain ⟨heq, childBox, hchildGet⟩ := hchild
        subst childRight
        have hchildBound : childLeft < store.nodes.size := by
          unfold Store.get? at hchildGet
          rw [Option.bind_eq_some_iff] at hchildGet
          obtain ⟨slot, hslot, _⟩ := hchildGet
          exact (Array.getElem?_eq_some_iff.mp hslot).1
        exact ⟨rfl, hchildBound⟩

private theorem get?_setBox_eq {store : Store} {loc other : Nat}
    {old new : NodeBox} (hget : store.get? loc = some old) :
    (store.setBox loc new).get? other =
      if other = loc then some new else store.get? other := by
  have hlt : loc < store.nodes.size := by
    exact (Array.getElem?_eq_some_iff.mp (nodes_get?_of_get? hget)).1
  by_cases hsame : other = loc
  · subst other
    simp [Store.setBox, Store.get?, Array.set!_eq_setIfInBounds, hlt]
  · have hne : loc ≠ other := Ne.symm hsame
    simp [Store.setBox, Store.get?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, hlt, hne, hsame]

private theorem get?_setBox_eq_of_bound {store : Store} {loc other : Nat}
    {new : NodeBox} (hlt : loc < store.nodes.size) :
    (store.setBox loc new).get? other =
      if other = loc then some new else store.get? other := by
  by_cases hsame : other = loc
  · subst other
    simp [Store.setBox, Store.get?, Array.set!_eq_setIfInBounds, hlt]
  · have hne : loc ≠ other := Ne.symm hsame
    simp [Store.setBox, Store.get?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, hlt, hne, hsame]

private theorem get?_kill_eq {store : Store} {loc other : Nat}
    {box : NodeBox} (hget : store.get? loc = some box) :
    (store.kill loc).get? other =
      if other = loc then none else store.get? other := by
  have hlt : loc < store.nodes.size := by
    exact (Array.getElem?_eq_some_iff.mp (nodes_get?_of_get? hget)).1
  by_cases hsame : other = loc
  · subst other
    simp [Store.kill, Store.get?, Array.set!_eq_setIfInBounds, hlt]
  · have hne : loc ≠ other := Ne.symm hsame
    simp [Store.kill, Store.get?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, hlt, hne, hsame]

private theorem get?_allocNode_eq (store : Store) (world : Owned)
    (node : Node) (loc : Nat) :
    (store.allocNode world node).1.get? loc =
      if loc = store.nodes.size then some ⟨world, 1, node⟩
      else store.get? loc := by
  by_cases hsame : loc = store.nodes.size
  · subst loc
    simp [Store.allocNode, Store.get?]
  · simp [Store.allocNode, Store.get?, Array.getElem?_push, hsame]

/-- Corresponding live boxes can be recovered from a related live location. -/
theorem boxes {left right : Store} (iso : HeapHistoryIso left right)
    {leftLoc rightLoc : Nat} (hrel : iso.locRel leftLoc rightLoc)
    {leftBox : NodeBox} (hleft : left.get? leftLoc = some leftBox) :
    ∃ rightBox,
      right.get? rightLoc = some rightBox ∧
        NodeBoxIso iso.locRel leftBox rightBox := by
  rcases iso.related hrel with hdead | hlive
  · exact False.elim (Option.some_ne_none leftBox (hleft.symm.trans hdead.1))
  · obtain ⟨foundLeft, rightBox, hfound, hright, hbox⟩ := hlive
    have : foundLeft = leftBox := Option.some.inj (hfound.symm.trans hleft)
    subst foundLeft
    exact ⟨rightBox, hright, hbox⟩

private def liveRel {left right : Store}
    (iso : HeapHistoryIso left right) (leftLoc rightLoc : Nat) : Prop :=
  iso.locRel leftLoc rightLoc ∧
    ∃ leftBox, left.get? leftLoc = some leftBox

private theorem RValsIso.liveMono {left right : Store}
    (iso : HeapHistoryIso left right) :
    ∀ {leftValues rightValues : List RVal},
      RValsIso iso.locRel leftValues rightValues →
      (∀ value ∈ leftValues, LiveRVal left value) →
      RValsIso (liveRel iso) leftValues rightValues
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, live => by
      refine .cons ?_ (RValsIso.liveMono iso tail fun value member =>
        live value (by simp [member]))
      cases head with
      | @loc leftLoc rightLoc related =>
          exact .loc ⟨related, live (.loc leftLoc) (by simp)⟩
      | lit => exact .lit
      | erased => exact .erased

private theorem NodeIso.liveMono {left right : Store}
    (iso : HeapHistoryIso left right) :
    ∀ {leftNode rightNode : Node},
      NodeIso iso.locRel leftNode rightNode →
      (∀ value ∈ nodeChildren leftNode, LiveRVal left value) →
      NodeIso (liveRel iso) leftNode rightNode
  | _, _, .ctor fields, live =>
      .ctor (RValsIso.liveMono iso fields fun value member =>
        live value (by simpa [nodeChildren] using member))
  | _, _, .pap arguments, live =>
      .pap (RValsIso.liveMono iso arguments fun value member =>
        live value (by simpa [nodeChildren] using member))

private theorem NodeBoxIso.liveMono {left right : Store}
    (iso : HeapHistoryIso left right) (closed : StoreClosed left)
    {leftLoc : Nat} {leftBox rightBox : NodeBox}
    (leftAt : left.get? leftLoc = some leftBox)
    (boxes : NodeBoxIso iso.locRel leftBox rightBox) :
    NodeBoxIso (liveRel iso) leftBox rightBox :=
  ⟨boxes.world, boxes.rc,
    NodeIso.liveMono iso boxes.node (closed leftAt)⟩

/-- Forget historical dead/dead rows, retaining the exact bijection on live
locations. Closure ensures every child relation of a live node also belongs
to the restricted live relation. -/
def toHeapIso {left right : Store} (iso : HeapHistoryIso left right)
    (closed : StoreClosed left) : HeapIso left right where
  locRel := liveRel iso
  left_unique := fun first second => iso.left_unique first.1 second.1
  right_unique := fun first second => iso.right_unique first.1 second.1
  left_total := by
    intro leftLoc leftBox leftAt
    obtain ⟨rightLoc, related⟩ := iso.left_total leftAt
    exact ⟨rightLoc, related, leftBox, leftAt⟩
  right_total := by
    intro rightLoc rightBox rightAt
    obtain ⟨leftLoc, related⟩ := iso.right_total rightAt
    rcases iso.related related with dead | live
    · exact False.elim
        (Option.some_ne_none rightBox (rightAt.symm.trans dead.2))
    · obtain ⟨leftBox, _foundRight, leftAt, _foundRightAt, _boxes⟩ := live
      exact ⟨leftLoc, related, leftBox, leftAt⟩
  related_live := by
    intro leftLoc rightLoc related
    obtain ⟨historyRelated, leftBox, leftAt⟩ := related
    obtain ⟨rightBox, rightAt, boxes⟩ := iso.boxes historyRelated leftAt
    exact ⟨leftBox, rightBox, leftAt, rightAt,
      NodeBoxIso.liveMono iso closed leftAt boxes⟩

/-- A live historical pair is retained by `toHeapIso`. -/
theorem toHeapIso_rel {left right : Store}
    (iso : HeapHistoryIso left right) (closed : StoreClosed left)
    {leftLoc rightLoc : Nat} (related : iso.locRel leftLoc rightLoc)
    {leftBox : NodeBox} (leftAt : left.get? leftLoc = some leftBox) :
    (iso.toHeapIso closed).locRel leftLoc rightLoc :=
  ⟨related, leftBox, leftAt⟩

/-- Restricting a history relation does not invent location pairs. -/
theorem of_toHeapIso_rel {left right : Store}
    (iso : HeapHistoryIso left right) (closed : StoreClosed left)
    {leftLoc rightLoc : Nat}
    (related : (iso.toHeapIso closed).locRel leftLoc rightLoc) :
    iso.locRel leftLoc rightLoc :=
  related.1

/-- The symmetric evaluator relation. -/
def symm {left right : Store} (iso : HeapHistoryIso left right) :
    HeapHistoryIso right left where
  locRel := fun r l => iso.locRel l r
  left_unique := iso.right_unique
  right_unique := iso.left_unique
  left_bound := iso.right_bound
  right_bound := iso.left_bound
  left_total := iso.right_total
  right_total := iso.left_total
  related := by
    intro rightLoc leftLoc hrel
    rcases iso.related hrel with ⟨hl, hr⟩ | hlive
    · exact .inl ⟨hr, hl⟩
    · obtain ⟨leftBox, rightBox, hl, hr, hbox⟩ := hlive
      exact .inr ⟨rightBox, leftBox, hr, hl, hbox.symm⟩

/-- A heap-history isomorphism cannot introduce a live node on the right when
the left heap has none.  Dead historical slots may differ, so this is stated
through the public live-node observation rather than array equality. -/
theorem right_live_eq_zero {left right : Store}
    (iso : HeapHistoryIso left right) (hleft : left.live = 0) :
    right.live = 0 := by
  apply (Reclamation.Store.live_eq_zero_iff_no_live_slot right).2
  intro rightBox hrightMember
  obtain ⟨rightLoc, hrightSlot⟩ :=
    (Array.mem_iff_getElem?).mp hrightMember
  have hright : right.get? rightLoc = some rightBox := by
    rw [Store.get?, hrightSlot]
    rfl
  obtain ⟨leftLoc, hrel⟩ := iso.right_total hright
  rcases iso.related hrel with hdead | hlive
  · exact Option.some_ne_none rightBox (hright.symm.trans hdead.2)
  · obtain ⟨leftBox, foundRight, hleftGet, hrightGet, _⟩ := hlive
    have hleftMember : some leftBox ∈ left.nodes := by
      apply (Array.mem_iff_getElem?).2
      exact ⟨leftLoc, nodes_get?_of_get? hleftGet⟩
    exact (Reclamation.Store.live_eq_zero_iff_no_live_slot left).1 hleft
      leftBox hleftMember

/-- Symmetric empty-live transport. -/
theorem left_live_eq_zero {left right : Store}
    (iso : HeapHistoryIso left right) (hright : right.live = 0) :
    left.live = 0 :=
  iso.symm.right_live_eq_zero hright

/-- Composition of allocation histories.  A dead/dead row composes only with
another dead/dead row; a live middle location forces both sides to expose the
same middle box, so node isomorphisms compose. -/
def trans {left middle right : Store}
    (first : HeapHistoryIso left middle)
    (second : HeapHistoryIso middle right) : HeapHistoryIso left right where
  locRel := fun leftLoc rightLoc =>
    ∃ middleLoc, first.locRel leftLoc middleLoc ∧
      second.locRel middleLoc rightLoc
  left_unique := by
    intro leftLoc right₁ right₂ h₁ h₂
    obtain ⟨middle₁, hleft₁, hright₁⟩ := h₁
    obtain ⟨middle₂, hleft₂, hright₂⟩ := h₂
    have hmiddle : middle₁ = middle₂ :=
      first.left_unique hleft₁ hleft₂
    subst middle₂
    exact second.left_unique hright₁ hright₂
  right_unique := by
    intro left₁ left₂ rightLoc h₁ h₂
    obtain ⟨middle₁, hleft₁, hright₁⟩ := h₁
    obtain ⟨middle₂, hleft₂, hright₂⟩ := h₂
    have hmiddle : middle₁ = middle₂ :=
      second.right_unique hright₁ hright₂
    subst middle₂
    exact first.right_unique hleft₁ hleft₂
  left_bound := by
    intro leftLoc rightLoc hrel
    exact first.left_bound hrel.choose_spec.1
  right_bound := by
    intro leftLoc rightLoc hrel
    exact second.right_bound hrel.choose_spec.2
  left_total := by
    intro leftLoc leftBox hleft
    obtain ⟨middleLoc, hmiddleRel⟩ := first.left_total hleft
    rcases first.related hmiddleRel with hdead | hlive
    · exact False.elim
        (Option.some_ne_none leftBox (hleft.symm.trans hdead.1))
    · obtain ⟨foundLeft, middleBox, hfoundLeft, hmiddle, _⟩ := hlive
      obtain ⟨rightLoc, hrightRel⟩ := second.left_total hmiddle
      exact ⟨rightLoc, middleLoc, hmiddleRel, hrightRel⟩
  right_total := by
    intro rightLoc rightBox hright
    obtain ⟨middleLoc, hmiddleRel⟩ := second.right_total hright
    rcases second.related hmiddleRel with hdead | hlive
    · exact False.elim
        (Option.some_ne_none rightBox (hright.symm.trans hdead.2))
    · obtain ⟨middleBox, foundRight, hmiddle, hfoundRight, _⟩ := hlive
      obtain ⟨leftLoc, hleftRel⟩ := first.right_total hmiddle
      exact ⟨leftLoc, middleLoc, hleftRel, hmiddleRel⟩
  related := by
    intro leftLoc rightLoc hrel
    obtain ⟨middleLoc, hleftRel, hrightRel⟩ := hrel
    rcases first.related hleftRel with hfirstDead | hfirstLive
    · rcases second.related hrightRel with hsecondDead | hsecondLive
      · exact .inl ⟨hfirstDead.1, hsecondDead.2⟩
      · obtain ⟨middleBox, rightBox, hmiddle, _, _⟩ := hsecondLive
        exact False.elim
          (Option.some_ne_none middleBox (hmiddle.symm.trans hfirstDead.2))
    · obtain ⟨leftBox, middleBox₁, hleft, hmiddle₁, hbox₁⟩ :=
        hfirstLive
      rcases second.related hrightRel with hsecondDead | hsecondLive
      · exact False.elim
          (Option.some_ne_none middleBox₁
            (hmiddle₁.symm.trans hsecondDead.1))
      · obtain ⟨middleBox₂, rightBox, hmiddle₂, hright, hbox₂⟩ :=
          hsecondLive
        have hmiddleBox : middleBox₁ = middleBox₂ :=
          Option.some.inj (hmiddle₁.symm.trans hmiddle₂)
        subst middleBox₂
        exact .inr ⟨leftBox, rightBox, hleft, hright,
          hbox₁.trans hbox₂⟩

/-- Updating corresponding live boxes preserves allocation history. -/
def setBox {left right : Store} (iso : HeapHistoryIso left right)
    {leftLoc rightLoc : Nat} (hrel : iso.locRel leftLoc rightLoc)
    {oldLeft oldRight newLeft newRight : NodeBox}
    (hleft : left.get? leftLoc = some oldLeft)
    (hright : right.get? rightLoc = some oldRight)
    (hnew : NodeBoxIso iso.locRel newLeft newRight) :
    HeapHistoryIso (left.setBox leftLoc newLeft)
      (right.setBox rightLoc newRight) where
  locRel := iso.locRel
  left_unique := iso.left_unique
  right_unique := iso.right_unique
  left_bound := by
    intro l r hrel
    simpa [Store.setBox] using iso.left_bound hrel
  right_bound := by
    intro l r hrel
    simpa [Store.setBox] using iso.right_bound hrel
  left_total := by
    intro loc box hbox
    rw [get?_setBox_eq hleft] at hbox
    by_cases hsame : loc = leftLoc
    · exact ⟨rightLoc, hsame ▸ hrel⟩
    · simp only [hsame, if_false] at hbox
      exact iso.left_total hbox
  right_total := by
    intro loc box hbox
    rw [get?_setBox_eq hright] at hbox
    by_cases hsame : loc = rightLoc
    · exact ⟨leftLoc, hsame ▸ hrel⟩
    · simp only [hsame, if_false] at hbox
      exact iso.right_total hbox
  related := by
    intro l r hlr
    have hlEq := get?_setBox_eq (new := newLeft) hleft (other := l)
    have hrEq := get?_setBox_eq (new := newRight) hright (other := r)
    by_cases hll : l = leftLoc
    · have hrr : r = rightLoc := iso.left_unique hlr (hll ▸ hrel)
      subst l
      subst r
      simp only [if_pos, hlEq, hrEq]
      exact .inr ⟨newLeft, newRight, rfl, rfl, hnew⟩
    · have hrr : r ≠ rightLoc := by
        intro heq
        have := iso.right_unique hlr (heq ▸ hrel)
        exact hll this
      simp only [hll, hrr, if_false, hlEq, hrEq]
      exact iso.related hlr

/-- Reviving corresponding dead historical slots preserves allocation
history.  Physical reuse credits exercise this operation: the pair remains
the same, but its observation changes from dead/dead to related live boxes. -/
def revive {left right : Store} (iso : HeapHistoryIso left right)
    {leftLoc rightLoc : Nat} (hrel : iso.locRel leftLoc rightLoc)
    (hleft : left.get? leftLoc = none)
    (hright : right.get? rightLoc = none)
    {newLeft newRight : NodeBox}
    (hnew : NodeBoxIso iso.locRel newLeft newRight) :
    HeapHistoryIso (left.setBox leftLoc newLeft)
      (right.setBox rightLoc newRight) where
  locRel := iso.locRel
  left_unique := iso.left_unique
  right_unique := iso.right_unique
  left_bound := by
    intro l r related
    simpa [Store.setBox] using iso.left_bound related
  right_bound := by
    intro l r related
    simpa [Store.setBox] using iso.right_bound related
  left_total := by
    intro loc box live
    rw [get?_setBox_eq_of_bound (iso.left_bound hrel)] at live
    by_cases same : loc = leftLoc
    · exact ⟨rightLoc, same ▸ hrel⟩
    · simp only [same, if_false] at live
      exact iso.left_total live
  right_total := by
    intro loc box live
    rw [get?_setBox_eq_of_bound (iso.right_bound hrel)] at live
    by_cases same : loc = rightLoc
    · exact ⟨leftLoc, same ▸ hrel⟩
    · simp only [same, if_false] at live
      exact iso.right_total live
  related := by
    intro l r related
    have leftEq := get?_setBox_eq_of_bound
      (new := newLeft) (iso.left_bound hrel) (other := l)
    have rightEq := get?_setBox_eq_of_bound
      (new := newRight) (iso.right_bound hrel) (other := r)
    by_cases leftSame : l = leftLoc
    · have rightSame : r = rightLoc :=
        iso.left_unique related (leftSame ▸ hrel)
      subst l
      subst r
      simp only [if_pos, leftEq, rightEq]
      exact .inr ⟨newLeft, newRight, rfl, rfl, hnew⟩
    · have rightDifferent : r ≠ rightLoc := by
        intro same
        have := iso.right_unique related (same ▸ hrel)
        exact leftSame this
      simp only [leftSame, rightDifferent, if_false, leftEq, rightEq]
      exact iso.related related

/-- Killing corresponding live locations retains their historical pair as a
dead/dead row.  This is the operation for which live-only heap isomorphism is
not compositional. -/
def kill {left right : Store} (iso : HeapHistoryIso left right)
    {leftLoc rightLoc : Nat} (hrel : iso.locRel leftLoc rightLoc)
    {leftBox rightBox : NodeBox}
    (hleft : left.get? leftLoc = some leftBox)
    (hright : right.get? rightLoc = some rightBox) :
    HeapHistoryIso (left.kill leftLoc) (right.kill rightLoc) where
  locRel := iso.locRel
  left_unique := iso.left_unique
  right_unique := iso.right_unique
  left_bound := by
    intro l r hrel
    simpa [Store.kill] using iso.left_bound hrel
  right_bound := by
    intro l r hrel
    simpa [Store.kill] using iso.right_bound hrel
  left_total := by
    intro loc box hbox
    rw [get?_kill_eq hleft] at hbox
    by_cases hsame : loc = leftLoc
    · simp [hsame] at hbox
    · simp only [hsame, if_false] at hbox
      exact iso.left_total hbox
  right_total := by
    intro loc box hbox
    rw [get?_kill_eq hright] at hbox
    by_cases hsame : loc = rightLoc
    · simp [hsame] at hbox
    · simp only [hsame, if_false] at hbox
      exact iso.right_total hbox
  related := by
    intro l r hlr
    have hlEq := get?_kill_eq hleft (other := l)
    have hrEq := get?_kill_eq hright (other := r)
    by_cases hll : l = leftLoc
    · have hrr : r = rightLoc := iso.left_unique hlr (hll ▸ hrel)
      subst l
      subst r
      exact .inl ⟨get?_kill_same hleft, get?_kill_same hright⟩
    · have hrr : r ≠ rightLoc := by
        intro heq
        have := iso.right_unique hlr (heq ▸ hrel)
        exact hll this
      simp only [hll, hrr, if_false, hlEq, hrEq]
      exact iso.related hlr

/-- Cost-counter ticks do not affect heap history. -/
def rcTick {left right : Store} (iso : HeapHistoryIso left right) :
    HeapHistoryIso left.rcTick right.rcTick where
  locRel := iso.locRel
  left_unique := iso.left_unique
  right_unique := iso.right_unique
  left_bound := by
    intro l r hrel
    simpa [Store.rcTick] using iso.left_bound hrel
  right_bound := by
    intro l r hrel
    simpa [Store.rcTick] using iso.right_bound hrel
  left_total := by
    intro loc box hget
    exact iso.left_total (by simpa [Store.rcTick, Store.get?] using hget)
  right_total := by
    intro loc box hget
    exact iso.right_total (by simpa [Store.rcTick, Store.get?] using hget)
  related := by
    intro l r hrel
    simpa [Store.rcTick, Store.get?] using iso.related hrel

/-- Any update which leaves the node arrays unchanged is invisible to heap
history.  Evaluator cost counters use this boundary. -/
def nodesEq {left right nextLeft nextRight : Store}
    (iso : HeapHistoryIso left right)
    (hleft : nextLeft.nodes = left.nodes)
    (hright : nextRight.nodes = right.nodes) :
    HeapHistoryIso nextLeft nextRight where
  locRel := iso.locRel
  left_unique := iso.left_unique
  right_unique := iso.right_unique
  left_bound := by
    intro l r hrel
    simpa [hleft] using iso.left_bound hrel
  right_bound := by
    intro l r hrel
    simpa [hright] using iso.right_bound hrel
  left_total := by
    intro loc box hget
    apply iso.left_total
    simpa [Store.get?, hleft] using hget
  right_total := by
    intro loc box hget
    apply iso.right_total
    simpa [Store.get?, hright] using hget
  related := by
    intro l r hrel
    simpa [Store.get?, hleft, hright] using iso.related hrel

/-- Corresponding fresh allocations extend the history bijection. -/
def alloc {left right : Store} (iso : HeapHistoryIso left right)
    {world : Owned} {leftNode rightNode : Node}
    (hnode : NodeIso iso.locRel leftNode rightNode) :
    HeapHistoryIso (left.allocNode world leftNode).1
      (right.allocNode world rightNode).1 := by
  let leftLoc := left.nodes.size
  let rightLoc := right.nodes.size
  let extended : Nat → Nat → Prop := fun l r =>
    (l = leftLoc ∧ r = rightLoc) ∨ iso.locRel l r
  have leftFresh : ∀ r, ¬ iso.locRel leftLoc r := by
    intro r hrel
    exact (Nat.lt_irrefl leftLoc) (iso.left_bound hrel)
  have rightFresh : ∀ l, ¬ iso.locRel l rightLoc := by
    intro l hrel
    exact (Nat.lt_irrefl rightLoc) (iso.right_bound hrel)
  refine
    { locRel := extended
      left_unique := ?_
      right_unique := ?_
      left_bound := ?_
      right_bound := ?_
      left_total := ?_
      right_total := ?_
      related := ?_ }
  · intro l r₁ r₂ h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h₁.2.trans h₂.2.symm
    · rw [h₁.1] at h₂
      exact False.elim (leftFresh r₂ h₂)
    · rw [h₂.1] at h₁
      exact False.elim (leftFresh r₁ h₁)
    · exact iso.left_unique h₁ h₂
  · intro l₁ l₂ r h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h₁.1.trans h₂.1.symm
    · rw [h₁.2] at h₂
      exact False.elim (rightFresh l₂ h₂)
    · rw [h₂.2] at h₁
      exact False.elim (rightFresh l₁ h₁)
    · exact iso.right_unique h₁ h₂
  · intro l r hrel
    rcases hrel with ⟨rfl, rfl⟩ | hold
    · simp [leftLoc, Store.allocNode]
    · exact Nat.lt_trans (iso.left_bound hold) (by simp [Store.allocNode])
  · intro l r hrel
    rcases hrel with ⟨rfl, rfl⟩ | hold
    · simp [rightLoc, Store.allocNode]
    · exact Nat.lt_trans (iso.right_bound hold) (by simp [Store.allocNode])
  · intro loc box hbox
    rw [get?_allocNode_eq] at hbox
    by_cases hnew : loc = leftLoc
    · exact ⟨rightLoc, .inl ⟨hnew, rfl⟩⟩
    · simp only [leftLoc, hnew, if_false] at hbox
      obtain ⟨r, hr⟩ := iso.left_total hbox
      exact ⟨r, .inr hr⟩
  · intro loc box hbox
    rw [get?_allocNode_eq] at hbox
    by_cases hnew : loc = rightLoc
    · exact ⟨leftLoc, .inl ⟨rfl, hnew⟩⟩
    · simp only [rightLoc, hnew, if_false] at hbox
      obtain ⟨l, hl⟩ := iso.right_total hbox
      exact ⟨l, .inr hl⟩
  · intro l r hrel
    rcases hrel with hnew | hold
    · obtain ⟨rfl, rfl⟩ := hnew
      refine .inr ⟨⟨world, 1, leftNode⟩, ⟨world, 1, rightNode⟩,
        ?_, ?_, ?_⟩
      · simp [leftLoc, get?_allocNode_eq]
      · simp [rightLoc, get?_allocNode_eq]
      · exact ⟨rfl, rfl, hnode.mono (fun h => .inr h)⟩
    · have hleftOld := get?_allocNode_eq left world leftNode l
      have hrightOld := get?_allocNode_eq right world rightNode r
      have hln : l ≠ leftLoc := by
        intro heq
        exact leftFresh r (heq ▸ hold)
      have hrn : r ≠ rightLoc := by
        intro heq
        exact rightFresh l (heq ▸ hold)
      simp only [leftLoc, hln, if_false] at hleftOld
      simp only [rightLoc, hrn, if_false] at hrightOld
      rcases iso.related hold with hdead | hlive
      · exact .inl ⟨hleftOld.trans hdead.1,
          hrightOld.trans hdead.2⟩
      · obtain ⟨leftBox, rightBox, hl, hr, hbox⟩ := hlive
        exact .inr ⟨leftBox, rightBox, hleftOld.trans hl,
          hrightOld.trans hr, hbox.mono (fun h => .inr h)⟩

/-- The empty evaluator stores have the empty allocation history. -/
def empty : HeapHistoryIso ({} : Store) ({} : Store) where
  locRel := fun _ _ => False
  left_unique h := False.elim h
  right_unique h := False.elim h
  left_bound h := False.elim h
  right_bound h := False.elim h
  left_total := by simp [Store.get?]
  right_total := by simp [Store.get?]
  related h := False.elim h

/-- Allocate and immediately kill a node on the left only.  The fresh dead
slot has no semantic counterpart, so the old history relation remains a
complete relation between the resulting live heaps. -/
def omitDeadAllocLeft {left right : Store}
    (iso : HeapHistoryIso left right) (world : Owned) (node : Node) :
    let allocated := left.allocNode world node
    HeapHistoryIso (allocated.1.kill allocated.2) right := by
  let allocated := left.allocNode world node
  let fresh := allocated.2
  have hfresh : allocated.1.get? fresh = some ⟨world, 1, node⟩ := by
    exact HeapIso.get?_allocNode_new left world node
  have hold (loc : Nat) (hne : loc ≠ fresh) :
      (allocated.1.kill fresh).get? loc = left.get? loc := by
    rw [get?_kill_eq hfresh]
    simp only [hne, if_false]
    rw [get?_allocNode_eq]
    have hne' : loc ≠ left.nodes.size := by
      simpa [fresh, allocated, Store.allocNode] using hne
    simp [hne']
  refine
    { locRel := iso.locRel
      left_unique := iso.left_unique
      right_unique := iso.right_unique
      left_bound := ?_
      right_bound := iso.right_bound
      left_total := ?_
      right_total := iso.right_total
      related := ?_ }
  · intro l r hrel
    have hlt := iso.left_bound hrel
    have hstep : l < left.nodes.size + 1 := Nat.lt_succ_of_lt hlt
    simpa [allocated, Store.allocNode, Store.kill] using hstep
  · intro loc box hbox
    by_cases hnew : loc = fresh
    · subst loc
      rw [get?_kill_eq hfresh] at hbox
      simp at hbox
    · exact iso.left_total ((hold loc hnew).symm.trans hbox)
  · intro l r hrel
    have hne : l ≠ fresh := by
      intro heq
      have hlt := iso.left_bound hrel
      subst l
      exact (Nat.lt_irrefl left.nodes.size) hlt
    rw [hold l hne]
    exact iso.related hrel

end HeapHistoryIso

namespace RValsIso

/-- An in-bounds environment is related to itself by the canonical
allocation-history relation. -/
theorem refl_of_inBounds {store : Store} (closed : StoreClosed store) :
    ∀ {values : List RVal},
      Reclamation.ValuesInBounds store values →
      RValsIso (HeapHistoryIso.refl store closed).locRel values values
  | [], _ => .nil
  | value :: values, hbounds => by
      have htail : Reclamation.ValuesInBounds store values := by
        intro found hfound
        exact hbounds found (by simp [hfound])
      cases value with
      | loc location =>
          have hlocation : location < store.nodes.size :=
            hbounds (.loc location) (by simp)
          exact .cons (.loc ⟨rfl, hlocation⟩)
            (refl_of_inBounds closed htail)
      | lit literal =>
          exact .cons .lit (refl_of_inBounds closed htail)
      | erased =>
          exact .cons .erased (refl_of_inBounds closed htail)

theorem mono {r₁ r₂ : Nat → Nat → Prop}
    (hmono : ∀ {l r}, r₁ l r → r₂ l r) :
    ∀ {left right : List RVal}, RValsIso r₁ left right →
      RValsIso r₂ left right
  | _, _, .nil => .nil
  | _, _, .cons hhead htail =>
      .cons (hhead.mono hmono) (mono hmono htail)

theorem symm {r : Nat → Nat → Prop} :
    ∀ {left right : List RVal}, RValsIso r left right →
      RValsIso (fun rightLoc leftLoc => r leftLoc rightLoc) right left
  | _, _, .nil => .nil
  | _, _, .cons hhead htail => .cons hhead.symm htail.symm

theorem trans {r₁ r₂ : Nat → Nat → Prop} :
    ∀ {left middle right : List RVal},
      RValsIso r₁ left middle → RValsIso r₂ middle right →
      RValsIso (fun leftLoc rightLoc =>
        ∃ middleLoc, r₁ leftLoc middleLoc ∧ r₂ middleLoc rightLoc)
        left right
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hleft hlefts, .cons hright hrights =>
      .cons (hleft.trans hright) (hlefts.trans hrights)

@[simp] theorem lengths {r : Nat → Nat → Prop}
    {left right : List RVal} (h : RValsIso r left right) :
    left.length = right.length := by
  induction h <;> simp_all

theorem append {r : Nat → Nat → Prop}
    {left₁ right₁ left₂ right₂ : List RVal}
    (h₁ : RValsIso r left₁ right₁)
    (h₂ : RValsIso r left₂ right₂) :
    RValsIso r (left₁ ++ left₂) (right₁ ++ right₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hhead _ ih => exact .cons hhead ih

theorem reverse {r : Nat → Nat → Prop}
    {left right : List RVal} (h : RValsIso r left right) :
    RValsIso r left.reverse right.reverse := by
  induction h with
  | nil => exact .nil
  | cons hhead _ ih =>
      simpa only [List.reverse_cons] using
        ih.append (.cons hhead .nil)

theorem take {r : Nat → Nat → Prop}
    {left right : List RVal} (h : RValsIso r left right) (count : Nat) :
    RValsIso r (left.take count) (right.take count) := by
  induction h generalizing count with
  | nil => simpa using (RValsIso.nil (locRel := r))
  | cons hhead htail ih =>
      cases count with
      | zero => exact .nil
      | succ count => exact .cons hhead (ih count)

theorem drop {r : Nat → Nat → Prop}
    {left right : List RVal} (h : RValsIso r left right) (count : Nat) :
    RValsIso r (left.drop count) (right.drop count) := by
  induction h generalizing count with
  | nil => simpa using (RValsIso.nil (locRel := r))
  | cons hhead htail ih =>
      cases count with
      | zero => exact .cons hhead htail
      | succ count => exact ih count

theorem get? {r : Nat → Nat → Prop} {left right : List RVal}
    (h : RValsIso r left right) {index : Nat} {value : RVal}
    (hleft : left[index]? = some value) :
    ∃ other, right[index]? = some other ∧ RValIso r value other := by
  induction h generalizing index value with
  | nil => simp at hleft
  | cons hhead htail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero] at hleft ⊢
          injection hleft with heq
          subst value
          exact ⟨_, rfl, hhead⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at hleft ⊢
          exact ih hleft

/-- Pointwise related scalar lists are literally equal; locations are the
only values whose spelling can differ. -/
theorem eq_of_allScalar {r : Nat → Nat → Prop}
    {left right : List RVal} (h : RValsIso r left right)
    (hscalar : left.all RVal.isScalar = true) : left = right := by
  induction h with
  | nil => rfl
  | @cons left right lefts rights hhead htail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hscalar
      cases hhead with
      | loc hrel => simp [RVal.isScalar] at hscalar
      | lit => simp only [List.cons.injEq, true_and]
               exact ih hscalar.2
      | erased => simp only [List.cons.injEq, true_and]
                  exact ih hscalar.2

end RValsIso

namespace RValIso

/-- A scalar is related to itself under every location relation. -/
theorem refl_of_scalar {r : Nat → Nat → Prop} {value : RVal}
    (hscalar : value.isScalar = true) : RValIso r value value := by
  cases value with
  | loc location => simp [RVal.isScalar] at hscalar
  | lit literal => exact .lit
  | erased => exact .erased

end RValIso

namespace HeapHistoryIso

/-- The output history retains every location pair known on entry. -/
def Extends {left right nextLeft nextRight : Store}
    (before : HeapHistoryIso left right)
    (after : HeapHistoryIso nextLeft nextRight) : Prop :=
  ∀ {l r}, before.locRel l r → after.locRel l r

theorem Extends.refl {left right : Store}
    {heap : HeapHistoryIso left right} : heap.Extends heap :=
  fun h => h

theorem Extends.trans {left right middleLeft middleRight nextLeft nextRight :
      Store}
    {first : HeapHistoryIso left right}
    {middle : HeapHistoryIso middleLeft middleRight}
    {last : HeapHistoryIso nextLeft nextRight}
    (h₁ : first.Extends middle) (h₂ : middle.Extends last) :
    first.Extends last :=
  fun h => h₂ (h₁ h)

theorem Extends.rval {left right nextLeft nextRight : Store}
    {before : HeapHistoryIso left right}
    {after : HeapHistoryIso nextLeft nextRight}
    (h : before.Extends after) {leftValue rightValue : RVal}
    (value : RValIso before.locRel leftValue rightValue) :
    RValIso after.locRel leftValue rightValue :=
  value.mono h

theorem Extends.rvals {left right nextLeft nextRight : Store}
    {before : HeapHistoryIso left right}
    {after : HeapHistoryIso nextLeft nextRight}
    (h : before.Extends after) {leftValues rightValues : List RVal}
    (values : RValsIso before.locRel leftValues rightValues) :
    RValsIso after.locRel leftValues rightValues :=
  values.mono h

end HeapHistoryIso

/-- Successful evaluator results related modulo allocation history.  The
extension field lets a caller keep using values from its older environment
after a callee has allocated or reclaimed nodes. -/
def RunHistoryIso {left right : Store}
    (before : HeapHistoryIso left right)
    (leftOut rightOut : Store × RVal) : Prop :=
  ∃ heap : HeapHistoryIso leftOut.1 rightOut.1,
    before.Extends heap ∧
      RValIso heap.locRel leftOut.2 rightOut.2

/-- Store-only counterpart used by recursive drop operations. -/
def StoreHistoryIso {left right : Store}
    (before : HeapHistoryIso left right)
    (leftOut rightOut : Store) : Prop :=
  ∃ heap : HeapHistoryIso leftOut rightOut, before.Extends heap

namespace StoreHistoryIso

/-- Store-only history refinement preserves the absence of live nodes. -/
theorem right_live_eq_zero {left right leftOut rightOut : Store}
    {before : HeapHistoryIso left right}
    (hstores : StoreHistoryIso before leftOut rightOut)
    (hleft : leftOut.live = 0) : rightOut.live = 0 := by
  obtain ⟨after, _⟩ := hstores
  exact after.right_live_eq_zero hleft

end StoreHistoryIso

namespace RunHistoryIso

/-- A result relation proved from a later entry history is also valid from
any earlier history whose location pairs the later history retains. -/
theorem weaken {left right beforeLeft beforeRight : Store}
    {earlier : HeapHistoryIso left right}
    {before : HeapHistoryIso beforeLeft beforeRight}
    {leftOut rightOut : Store × RVal}
    (hextends : earlier.Extends before)
    (hrun : RunHistoryIso before leftOut rightOut) :
    RunHistoryIso earlier leftOut rightOut := by
  obtain ⟨after, hbefore, hvalue⟩ := hrun
  exact ⟨after, hextends.trans hbefore, hvalue⟩

/-- Sequentially related executions compose their output heaps and values. -/
theorem trans {left middle right : Store}
    {first : HeapHistoryIso left middle}
    {second : HeapHistoryIso middle right}
    {leftOut middleOut rightOut : Store × RVal}
    (hfirst : RunHistoryIso first leftOut middleOut)
    (hsecond : RunHistoryIso second middleOut rightOut) :
    RunHistoryIso (first.trans second) leftOut rightOut := by
  obtain ⟨firstHeap, hfirstExtends, hfirstValue⟩ := hfirst
  obtain ⟨secondHeap, hsecondExtends, hsecondValue⟩ := hsecond
  exact ⟨firstHeap.trans secondHeap,
    (fun hrel =>
      ⟨hrel.choose, hfirstExtends hrel.choose_spec.1,
        hsecondExtends hrel.choose_spec.2⟩),
    hfirstValue.trans hsecondValue⟩

end RunHistoryIso

theorem resolveAtom_historyIso
    {rel : Nat → Nat → Prop} {left right : List RVal}
    (henv : RValsIso rel left right) {atom : Atom} {leftValue : RVal}
    (hleft : resolveAtom left atom = .ok leftValue) :
    ∃ rightValue, resolveAtom right atom = .ok rightValue ∧
      RValIso rel leftValue rightValue := by
  cases atom with
  | var index =>
      simp only [resolveAtom] at hleft ⊢
      cases hget : left[index]? with
      | none => simp [hget] at hleft
      | some value =>
          simp only [hget, Except.ok.injEq] at hleft
          subst value
          obtain ⟨other, hother, hiso⟩ := henv.get? hget
          exact ⟨other, by simp [hother], hiso⟩
  | lit literal =>
      simp only [resolveAtom, Except.ok.injEq] at hleft ⊢
      subst leftValue
      exact ⟨.lit literal, rfl, .lit⟩
  | erased =>
      simp only [resolveAtom, Except.ok.injEq] at hleft ⊢
      subst leftValue
      exact ⟨.erased, rfl, .erased⟩

private theorem List.resolveAtomsFrom_historyIso
    {rel : Nat → Nat → Prop} {left right : List RVal}
    (henv : RValsIso rel left right) :
    ∀ (atoms : List Atom)
      (leftAcc rightAcc leftOut : List RVal),
      RValsIso rel leftAcc rightAcc →
      atoms.foldlM
          (fun acc atom => do pure (acc ++ [← resolveAtom left atom]))
          leftAcc = .ok leftOut →
      ∃ rightOut,
        atoms.foldlM
            (fun acc atom => do pure (acc ++ [← resolveAtom right atom]))
            rightAcc = .ok rightOut ∧
          RValsIso rel leftOut rightOut
  | [], leftAcc, rightAcc, leftOut, hacc, hleft => by
      change (Except.ok leftAcc : Except Err (List RVal)) = .ok leftOut at hleft
      injection hleft with heq
      subst leftOut
      change ∃ rightOut,
        (Except.ok rightAcc : Except Err (List RVal)) = .ok rightOut ∧
          RValsIso rel leftAcc rightOut
      exact ⟨rightAcc, rfl, hacc⟩
  | atom :: atoms, leftAcc, rightAcc, leftOut, hacc, hleft => by
      simp only [List.foldlM_cons] at hleft ⊢
      cases hvalue : resolveAtom left atom with
      | error error =>
          rw [hvalue] at hleft
          simp only [bind, Except.bind] at hleft
          contradiction
      | ok leftValue =>
          simp only [hvalue, bind, Except.bind] at hleft
          obtain ⟨rightValue, hrightValue, hvalueIso⟩ :=
            resolveAtom_historyIso henv hvalue
          rw [hrightValue]
          simp only [bind, Except.bind]
          exact List.resolveAtomsFrom_historyIso henv atoms
            (leftAcc ++ [leftValue]) (rightAcc ++ [rightValue]) leftOut
            (hacc.append (.cons hvalueIso .nil)) hleft

theorem resolveAtoms_historyIso
    {rel : Nat → Nat → Prop} {left right : List RVal}
    (henv : RValsIso rel left right) {atoms : Array Atom}
    {leftValues : List RVal}
    (hleft : resolveAtoms left atoms = .ok leftValues) :
    ∃ rightValues, resolveAtoms right atoms = .ok rightValues ∧
      RValsIso rel leftValues rightValues := by
  unfold resolveAtoms at hleft ⊢
  rw [← Array.foldlM_toList] at hleft ⊢
  exact List.resolveAtomsFrom_historyIso henv atoms.toList [] [] leftValues
    .nil hleft

private theorem RValIso.hasWorld_eq
    {left right : Store} (iso : HeapHistoryIso left right)
    {leftValue rightValue : RVal} (hvalue : RValIso iso.locRel
      leftValue rightValue) (world : Owned) :
    leftValue.hasWorld left world = rightValue.hasWorld right world := by
  cases hvalue with
  | lit => rfl
  | erased => rfl
  | @loc leftLoc rightLoc hrel =>
      simp only [RVal.hasWorld]
      rcases iso.related hrel with hdead | hlive
      · rw [hdead.1, hdead.2]
      · obtain ⟨leftBox, rightBox, hleft, hright, hbox⟩ := hlive
        rw [hleft, hright]
        exact congrArg (fun found => found == world) hbox.world

theorem checkResultWorld_historyIso
    {left right : Store} (iso : HeapHistoryIso left right)
    {leftValue rightValue : RVal}
    (hvalue : RValIso iso.locRel leftValue rightValue)
    (world : Owned)
    (hleft : checkResultWorld world (left, leftValue) =
      .ok (left, leftValue)) :
    checkResultWorld world (right, rightValue) =
      .ok (right, rightValue) := by
  have heq := RValIso.hasWorld_eq iso hvalue world
  unfold checkResultWorld at hleft ⊢
  by_cases hworld : leftValue.hasWorld left world = true
  · have hright : rightValue.hasWorld right world = true := by
      rw [← heq]
      exact hworld
    simp [hworld, hright]
  · simp [hworld] at hleft

theorem dupVals_historyIso
    {left right : Store} (iso : HeapHistoryIso left right) :
    ∀ {leftValues rightValues : List RVal},
      RValsIso iso.locRel leftValues rightValues →
      ∀ {leftOut : Store}, dupVals left leftValues = .ok leftOut →
      ∃ rightOut, dupVals right rightValues = .ok rightOut ∧
        StoreHistoryIso iso leftOut rightOut
  | _, _, .nil, leftOut, hrun => by
      change (Except.ok left : Except Err Store) = .ok leftOut at hrun
      injection hrun with heq
      subst leftOut
      change ∃ rightOut,
        (Except.ok right : Except Err Store) = .ok rightOut ∧
          StoreHistoryIso iso left rightOut
      exact ⟨right, rfl, ⟨iso, fun h => h⟩⟩
  | leftHead :: leftTail, rightHead :: rightTail,
      .cons hhead htail, leftOut, hrun => by
      cases hhead with
      | lit =>
          change dupVals left _ = .ok leftOut at hrun
          change ∃ rightOut, dupVals right _ = .ok rightOut ∧ _
          exact dupVals_historyIso iso htail hrun
      | erased =>
          change dupVals left _ = .ok leftOut at hrun
          change ∃ rightOut, dupVals right _ = .ok rightOut ∧ _
          exact dupVals_historyIso iso htail hrun
      | @loc leftLoc rightLoc hrel =>
          cases hleft : left.get? leftLoc with
          | none =>
              simp [dupVals, hleft] at hrun
              simp only [bind, Except.bind] at hrun
              contradiction
          | some leftBox =>
              obtain ⟨rightBox, hright, hbox⟩ := iso.boxes hrel hleft
              cases hworld : leftBox.world with
              | unique =>
                  simp [dupVals, hleft, hworld] at hrun
                  simp only [bind, Except.bind] at hrun
                  contradiction
              | shared =>
                  have hrightWorld : rightBox.world = .shared := by
                    rw [← hbox.world, hworld]
                  let newLeft : NodeBox :=
                    ⟨.shared, leftBox.rc + 1, leftBox.node⟩
                  let newRight : NodeBox :=
                    ⟨.shared, rightBox.rc + 1, rightBox.node⟩
                  have hrun' : dupVals
                      (left.setBox leftLoc newLeft).rcTick
                      leftTail = .ok leftOut := by
                    have htemp := hrun
                    simp [dupVals, hleft, hworld] at htemp
                    simp only [bind, Except.bind] at htemp
                    simpa [newLeft, dupVals] using htemp
                  let nextLeft :=
                    (left.setBox leftLoc newLeft).rcTick
                  let nextRight :=
                    (right.setBox rightLoc newRight).rcTick
                  have hnew : NodeBoxIso iso.locRel
                      newLeft newRight := by
                    exact ⟨rfl, congrArg (fun n => n + 1) hbox.rc,
                      hbox.node⟩
                  let nextIso : HeapHistoryIso nextLeft nextRight :=
                    (iso.setBox hrel hleft hright hnew).rcTick
                  obtain ⟨rightOut, hrightOut, outIso, hout⟩ :=
                    dupVals_historyIso nextIso
                      (htail.mono (fun h => h)) hrun'
                  have hrightOut' : dupVals right
                      (.loc rightLoc :: rightTail) = .ok rightOut := by
                    simp [dupVals, hright, hrightWorld]
                    simp only [bind, Except.bind]
                    simpa [nextRight, newRight, dupVals] using hrightOut
                  refine ⟨rightOut, hrightOut', outIso, ?_⟩
                  exact fun h => hout h

theorem callScalarOracle_historyIso
    {ctx : Ctx} {function : Ix.Compiler.Ixon.Address}
    {leftValues rightValues : List RVal}
    {rel : Nat → Nat → Prop} (hvalues : RValsIso rel leftValues rightValues)
    {leftValue : RVal}
    (hleft : callScalarOracle ctx function leftValues = .ok leftValue) :
    ∃ rightValue, callScalarOracle ctx function rightValues = .ok rightValue ∧
      RValIso rel leftValue rightValue := by
  by_cases hscalar : leftValues.all RVal.isScalar = true
  · have heq := hvalues.eq_of_allScalar hscalar
    subst rightValues
    exact ⟨leftValue, hleft, by
      unfold callScalarOracle at hleft
      simp only [hscalar, Bool.not_true, Bool.false_eq_true, if_false] at hleft
      cases horacle : ctx.oracle function leftValues with
      | none => simp [horacle] at hleft
      | some value =>
          rw [horacle] at hleft
          cases hvalue : value.isScalar with
          | false => simp [hvalue] at hleft
          | true =>
              simp only [hvalue, if_true, Except.ok.injEq] at hleft
              subst leftValue
              exact RValIso.refl_of_scalar hvalue⟩
  · unfold callScalarOracle at hleft
    simp [hscalar] at hleft

private theorem List.foldl_cons_eq_reverse_append
    (values environment : List RVal) :
    values.foldl (fun current value => value :: current) environment =
      values.reverse ++ environment := by
  induction values generalizing environment with
  | nil => rfl
  | cons value values ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem Array.foldl_cons_historyIso
    {rel : Nat → Nat → Prop} {left right : Array RVal}
    (hvalues : RValsIso rel left.toList right.toList)
    {leftEnvironment rightEnvironment : List RVal}
    (henvironment : RValsIso rel leftEnvironment rightEnvironment) :
    RValsIso rel
      (left.foldl (fun current value => value :: current) leftEnvironment)
      (right.foldl (fun current value => value :: current) rightEnvironment) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList,
    List.foldl_cons_eq_reverse_append,
    List.foldl_cons_eq_reverse_append]
  exact hvalues.reverse.append henvironment

/-- Successful evaluation is equivariant under allocation-history
isomorphism at one common fuel index. -/
private structure EvalHistoryIsoAt (fuel : Nat) : Prop where
  runCode : ∀ (ctx : Ctx) (current : FnDef)
      (left right : Store) (heap : HeapHistoryIso left right)
      (leftEnvironment rightEnvironment : List RVal),
    RValsIso heap.locRel leftEnvironment rightEnvironment →
    ∀ (input : Code) (leftOut : Store × RVal),
      IxIR1.runCode ctx fuel current left leftEnvironment input = .ok leftOut →
      ∃ rightOut,
        IxIR1.runCode ctx fuel current right rightEnvironment input =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut
  runOp : ∀ (ctx : Ctx) (current : FnDef)
      (left right : Store) (heap : HeapHistoryIso left right)
      (leftEnvironment rightEnvironment : List RVal),
    RValsIso heap.locRel leftEnvironment rightEnvironment →
    ∀ (operation : Op) (leftOut : Store × RVal),
      IxIR1.runOp ctx fuel current left leftEnvironment operation = .ok leftOut →
      ∃ rightOut,
        IxIR1.runOp ctx fuel current right rightEnvironment operation =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut
  invoke : ∀ (ctx : Ctx) (function : Ix.Compiler.Ixon.Address)
      (leftArguments rightArguments : List RVal)
      (left right : Store) (heap : HeapHistoryIso left right),
    RValsIso heap.locRel leftArguments rightArguments →
    ∀ (leftOut : Store × RVal),
      IxIR1.invoke ctx fuel function leftArguments left = .ok leftOut →
      ∃ rightOut,
        IxIR1.invoke ctx fuel function rightArguments right = .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut
  applyGo : ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right)
      (leftFunction rightFunction : RVal)
      (leftArguments rightArguments : List RVal),
    RValIso heap.locRel leftFunction rightFunction →
    RValsIso heap.locRel leftArguments rightArguments →
    ∀ (leftOut : Store × RVal),
      IxIR1.applyGo ctx fuel left leftFunction leftArguments = .ok leftOut →
      ∃ rightOut,
        IxIR1.applyGo ctx fuel right rightFunction rightArguments =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut
  dropVal : ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right) (leftValue rightValue : RVal),
    RValIso heap.locRel leftValue rightValue →
    ∀ (leftOut : Store),
      IxIR1.dropVal ctx fuel left leftValue = .ok leftOut →
      ∃ rightOut,
        IxIR1.dropVal ctx fuel right rightValue = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut
  dropMany : ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right)
      (leftValues rightValues : List RVal),
    RValsIso heap.locRel leftValues rightValues →
    ∀ (leftOut : Store),
      IxIR1.dropMany ctx fuel left leftValues = .ok leftOut →
      ∃ rightOut,
        IxIR1.dropMany ctx fuel right rightValues = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut
  dropUVal : ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right) (leftValue rightValue : RVal),
    RValIso heap.locRel leftValue rightValue →
    ∀ (leftOut : Store),
      IxIR1.dropUVal ctx fuel left leftValue = .ok leftOut →
      ∃ rightOut,
        IxIR1.dropUVal ctx fuel right rightValue = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut
  dropManyU : ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right)
      (leftValues rightValues : List RVal),
    RValsIso heap.locRel leftValues rightValues →
    ∀ (leftOut : Store),
      IxIR1.dropManyU ctx fuel left leftValues = .ok leftOut →
      ∃ rightOut,
        IxIR1.dropManyU ctx fuel right rightValues = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut

private structure DropHistoryIsoAt (fuel : Nat) : Prop where
  dropVal : ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right) (leftValue rightValue : RVal),
    RValIso heap.locRel leftValue rightValue →
    ∀ (leftOut : Store),
      IxIR1.dropVal ctx fuel left leftValue = .ok leftOut →
      ∃ rightOut,
        IxIR1.dropVal ctx fuel right rightValue = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut
  dropMany : ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right)
      (leftValues rightValues : List RVal),
    RValsIso heap.locRel leftValues rightValues →
    ∀ (leftOut : Store),
      IxIR1.dropMany ctx fuel left leftValues = .ok leftOut →
      ∃ rightOut,
        IxIR1.dropMany ctx fuel right rightValues = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut
  dropUVal : ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right) (leftValue rightValue : RVal),
    RValIso heap.locRel leftValue rightValue →
    ∀ (leftOut : Store),
      IxIR1.dropUVal ctx fuel left leftValue = .ok leftOut →
      ∃ rightOut,
        IxIR1.dropUVal ctx fuel right rightValue = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut
  dropManyU : ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right)
      (leftValues rightValues : List RVal),
    RValsIso heap.locRel leftValues rightValues →
    ∀ (leftOut : Store),
      IxIR1.dropManyU ctx fuel left leftValues = .ok leftOut →
      ∃ rightOut,
        IxIR1.dropManyU ctx fuel right rightValues = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut

private theorem dropHistoryIsoAt : ∀ fuel, DropHistoryIsoAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [IxIR1.dropVal, IxIR1.dropMany, IxIR1.dropUVal,
          IxIR1.dropManyU] at *
  | succ fuel smaller =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ctx left right heap leftValue rightValue hvalue leftOut hrun
        rw [IxIR1.dropVal.eq_def] at hrun ⊢
        dsimp only at hrun ⊢
        cases hvalue with
        | lit =>
            injection hrun with hout
            subst leftOut
            exact ⟨right, rfl, heap, HeapHistoryIso.Extends.refl⟩
        | erased =>
            injection hrun with hout
            subst leftOut
            exact ⟨right, rfl, heap, HeapHistoryIso.Extends.refl⟩
        | @loc leftLoc rightLoc hrel =>
            cases hleft : left.get? leftLoc with
            | none => simp [hleft] at hrun
            | some leftBox =>
                obtain ⟨rightBox, hright, hbox⟩ := heap.boxes hrel hleft
                rcases leftBox with ⟨leftWorld, leftRc, leftNode⟩
                rcases rightBox with ⟨rightWorld, rightRc, rightNode⟩
                rcases hbox with ⟨hworld, hrc, hnode⟩
                change leftWorld = rightWorld at hworld
                change leftRc = rightRc at hrc
                change NodeIso heap.locRel leftNode rightNode at hnode
                subst rightWorld
                subst rightRc
                simp only [hleft] at hrun
                simp only [hright]
                cases leftWorld with
                | unique => simp at hrun
                | shared =>
                    simp only
                    by_cases hone : leftRc == 1
                    · simp only [hone, if_true] at hrun ⊢
                      have hleftTick :
                          left.rcTick.get? leftLoc =
                            some ⟨.shared, leftRc, leftNode⟩ := by
                        simpa [Store.rcTick, Store.get?] using hleft
                      have hrightTick :
                          right.rcTick.get? rightLoc =
                            some ⟨.shared, leftRc, rightNode⟩ := by
                        simpa [Store.rcTick, Store.get?] using hright
                      let killed := (heap.rcTick).kill hrel
                        hleftTick hrightTick
                      cases hnode with
                      | ctor hfields =>
                          obtain ⟨rightOut, hrightOut, final,
                              hext⟩ :=
                            smaller.dropMany ctx
                              (left.rcTick.kill leftLoc)
                              (right.rcTick.kill rightLoc) killed
                              _ _ hfields leftOut hrun
                          exact ⟨rightOut, hrightOut, final,
                            HeapHistoryIso.Extends.trans
                              (fun h => h) hext⟩
                      | pap harguments =>
                          obtain ⟨rightOut, hrightOut, final,
                              hext⟩ :=
                            smaller.dropMany ctx
                              (left.rcTick.kill leftLoc)
                              (right.rcTick.kill rightLoc) killed
                              _ _ harguments leftOut hrun
                          exact ⟨rightOut, hrightOut, final,
                            HeapHistoryIso.Extends.trans
                              (fun h => h) hext⟩
                    · simp only [hone, Bool.false_eq_true, if_false]
                        at hrun ⊢
                      injection hrun with hout
                      subst leftOut
                      have hleftTick :
                          left.rcTick.get? leftLoc =
                            some ⟨.shared, leftRc, leftNode⟩ := by
                        simpa [Store.rcTick, Store.get?] using hleft
                      have hrightTick :
                          right.rcTick.get? rightLoc =
                            some ⟨.shared, leftRc, rightNode⟩ := by
                        simpa [Store.rcTick, Store.get?] using hright
                      let next := (heap.rcTick).setBox hrel
                        hleftTick hrightTick
                        (⟨rfl, rfl, hnode⟩ : NodeBoxIso heap.locRel
                          ⟨.shared, leftRc - 1, leftNode⟩
                          ⟨.shared, leftRc - 1, rightNode⟩)
                      exact ⟨_, rfl, next, fun h => h⟩
      · intro ctx left right heap leftValues rightValues hvalues
          leftOut hrun
        rw [IxIR1.dropMany.eq_def] at hrun ⊢
        dsimp only at hrun ⊢
        cases hvalues with
        | nil =>
            injection hrun with hout
            subst leftOut
            exact ⟨right, rfl, heap, HeapHistoryIso.Extends.refl⟩
        | @cons leftHead rightHead leftTail rightTail hhead htail =>
            dsimp only at hrun ⊢
            cases hfirst : IxIR1.dropVal ctx fuel left leftHead with
            | error error =>
                rw [hfirst] at hrun
                simp only [bind, Except.bind] at hrun
                contradiction
            | ok middle =>
                rw [hfirst] at hrun
                simp only [bind, Except.bind] at hrun
                obtain ⟨rightMiddle, hrightFirst, middleHeap,
                    hentryMiddle⟩ :=
                  smaller.dropVal ctx left right heap leftHead rightHead
                    hhead middle hfirst
                obtain ⟨rightOut, hrightRest, finalHeap,
                    hmiddleFinal⟩ :=
                  smaller.dropMany ctx middle rightMiddle middleHeap _ _
                    (hentryMiddle.rvals htail) leftOut hrun
                refine ⟨rightOut, ?_, finalHeap,
                  hentryMiddle.trans hmiddleFinal⟩
                rw [hrightFirst]
                simp only [bind, Except.bind]
                exact hrightRest
      · intro ctx left right heap leftValue rightValue hvalue leftOut hrun
        rw [IxIR1.dropUVal.eq_def] at hrun ⊢
        dsimp only at hrun ⊢
        cases hvalue with
        | lit =>
            injection hrun with hout
            subst leftOut
            exact ⟨right, rfl, heap, HeapHistoryIso.Extends.refl⟩
        | erased =>
            injection hrun with hout
            subst leftOut
            exact ⟨right, rfl, heap, HeapHistoryIso.Extends.refl⟩
        | @loc leftLoc rightLoc hrel =>
            cases hleft : left.get? leftLoc with
            | none => simp [hleft] at hrun
            | some leftBox =>
                obtain ⟨rightBox, hright, hbox⟩ := heap.boxes hrel hleft
                rcases leftBox with ⟨leftWorld, leftRc, leftNode⟩
                rcases rightBox with ⟨rightWorld, rightRc, rightNode⟩
                rcases hbox with ⟨hworld, hrc, hnode⟩
                change leftWorld = rightWorld at hworld
                change leftRc = rightRc at hrc
                change NodeIso heap.locRel leftNode rightNode at hnode
                subst rightWorld
                subst rightRc
                simp only [hleft] at hrun
                simp only [hright]
                cases leftWorld with
                | shared => simp at hrun
                | unique =>
                    simp only
                    cases hnode with
                    | pap harguments => simp at hrun
                    | ctor hfields =>
                        let killed := heap.kill hrel hleft hright
                        obtain ⟨rightOut, hrightOut, final,
                            hext⟩ :=
                          smaller.dropManyU ctx (left.kill leftLoc)
                            (right.kill rightLoc) killed _ _ hfields
                            leftOut hrun
                        exact ⟨rightOut, hrightOut, final,
                          HeapHistoryIso.Extends.trans (fun h => h) hext⟩
      · intro ctx left right heap leftValues rightValues hvalues
          leftOut hrun
        rw [IxIR1.dropManyU.eq_def] at hrun ⊢
        dsimp only at hrun ⊢
        cases hvalues with
        | nil =>
            injection hrun with hout
            subst leftOut
            exact ⟨right, rfl, heap, HeapHistoryIso.Extends.refl⟩
        | @cons leftHead rightHead leftTail rightTail hhead htail =>
            dsimp only at hrun ⊢
            cases hfirst : IxIR1.dropUVal ctx fuel left leftHead with
            | error error =>
                rw [hfirst] at hrun
                simp only [bind, Except.bind] at hrun
                contradiction
            | ok middle =>
                rw [hfirst] at hrun
                simp only [bind, Except.bind] at hrun
                obtain ⟨rightMiddle, hrightFirst, middleHeap,
                    hentryMiddle⟩ :=
                  smaller.dropUVal ctx left right heap leftHead rightHead
                    hhead middle hfirst
                obtain ⟨rightOut, hrightRest, finalHeap,
                    hmiddleFinal⟩ :=
                  smaller.dropManyU ctx middle rightMiddle middleHeap _ _
                    (hentryMiddle.rvals htail) leftOut hrun
                refine ⟨rightOut, ?_, finalHeap,
                  hentryMiddle.trans hmiddleFinal⟩
                rw [hrightFirst]
                simp only [bind, Except.bind]
                exact hrightRest

private theorem runCode_case_historyIso
    {fuel : Nat} (smaller : EvalHistoryIsoAt fuel)
    (ctx : Ctx) (current : FnDef) (left right : Store)
    (heap : HeapHistoryIso left right)
    (leftEnvironment rightEnvironment : List RVal)
    (henvironment : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (scrutinee : Atom) (peelNat : Bool) (alternatives : Array Alt)
    (leftOut : Store × RVal)
    (hrun : IxIR1.runCode ctx (fuel + 1) current left leftEnvironment
      (.case scrutinee peelNat alternatives) = .ok leftOut) :
    ∃ rightOut,
      IxIR1.runCode ctx (fuel + 1) current right rightEnvironment
          (.case scrutinee peelNat alternatives) = .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  rw [IxIR1.runCode.eq_def] at hrun ⊢
  dsimp only at hrun ⊢
  cases hleftResolve : resolveAtom leftEnvironment scrutinee with
  | error error =>
      rw [hleftResolve] at hrun
      simp only [bind, Except.bind] at hrun
      contradiction
  | ok leftValue =>
      obtain ⟨rightValue, hrightResolve, hvalue⟩ :=
        resolveAtom_historyIso henvironment hleftResolve
      rw [hleftResolve] at hrun
      rw [hrightResolve]
      simp only [bind, Except.bind] at hrun ⊢
      cases hvalue with
      | erased => simp at hrun
      | @lit literal =>
          cases literal with
          | str value => simp at hrun
          | nat value =>
              cases peelNat with
              | false => simp at hrun
              | true =>
                  cases value with
                  | zero =>
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 0) with
                      | none => simp [hfind] at hrun
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero =>
                                  simp only [hfind] at hrun ⊢
                                  exact smaller.runCode ctx current
                                    left right heap leftEnvironment
                                    rightEnvironment henvironment body
                                    leftOut hrun
                              | succ fields => simp [hfind] at hrun
                  | succ value =>
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 1) with
                      | none => simp [hfind] at hrun
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero => simp [hfind] at hrun
                              | succ fields =>
                                  cases fields with
                                  | zero =>
                                      simp only [hfind] at hrun ⊢
                                      exact smaller.runCode ctx current
                                        left right heap
                                        (.lit (.nat value) ::
                                          leftEnvironment)
                                        (.lit (.nat value) ::
                                          rightEnvironment)
                                        (.cons .lit henvironment) body
                                        leftOut hrun
                                  | succ fields => simp [hfind] at hrun
      | @loc leftLoc rightLoc hrel =>
          cases hleft : left.get? leftLoc with
          | none => simp [hleft] at hrun
          | some leftBox =>
              obtain ⟨rightBox, hright, hbox⟩ := heap.boxes hrel hleft
              rcases leftBox with ⟨leftWorld, leftRc, leftNode⟩
              rcases rightBox with ⟨rightWorld, rightRc, rightNode⟩
              rcases hbox with ⟨hworld, hrc, hnode⟩
              change leftWorld = rightWorld at hworld
              change leftRc = rightRc at hrc
              change NodeIso heap.locRel leftNode rightNode at hnode
              subst rightWorld
              subst rightRc
              simp only [hleft] at hrun
              simp only [hright]
              cases hnode with
              | pap harguments => simp at hrun
              | @ctor cid leftFields rightFields hfields =>
                  simp only
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == cid.cidx) with
                  | none => simp [hfind] at hrun
                  | some alternative =>
                      cases alternative with
                      | mk cidx fieldCount body =>
                          have hsizes : leftFields.size = rightFields.size := by
                            simpa using hfields.lengths
                          by_cases hcount : leftFields.size = fieldCount
                          · have hrightCount :
                                rightFields.size = fieldCount := by
                              rw [← hsizes]
                              exact hcount
                            simp [hfind, hcount, hrightCount] at hrun ⊢
                            obtain ⟨rightOut, hrightOut, hout⟩ :=
                              smaller.runCode ctx current left right heap
                                (leftFields.toList.reverse ++ leftEnvironment)
                                (rightFields.toList.reverse ++ rightEnvironment)
                                (hfields.reverse.append henvironment)
                                body leftOut hrun
                            rcases rightOut with ⟨rightStore, rightValue⟩
                            exact ⟨rightStore, rightValue, hrightOut, hout⟩
                          · have hrightCount :
                                rightFields.size ≠ fieldCount := by
                              intro heq
                              exact hcount (hsizes.trans heq)
                            simp [hfind, hcount, hrightCount] at hrun

private theorem runCode_historyIsoStep {fuel : Nat}
    (smaller : EvalHistoryIsoAt fuel) :
    ∀ (ctx : Ctx) (current : FnDef)
      (left right : Store) (heap : HeapHistoryIso left right)
      (leftEnvironment rightEnvironment : List RVal),
    RValsIso heap.locRel leftEnvironment rightEnvironment →
    ∀ (input : Code) (leftOut : Store × RVal),
      IxIR1.runCode ctx (fuel + 1) current left leftEnvironment input =
        .ok leftOut →
      ∃ rightOut,
        IxIR1.runCode ctx (fuel + 1) current right rightEnvironment input =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  intro ctx current left right heap leftEnvironment rightEnvironment
    henvironment input leftOut hrun
  cases input with
  | ret atom =>
      rw [IxIR1.runCode.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtom leftEnvironment atom with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftValue =>
          obtain ⟨rightValue, hright, hvalue⟩ :=
            resolveAtom_historyIso henvironment hleft
          rw [hleft] at hrun
          simp only [bind, Except.bind, Except.ok.injEq] at hrun
          subst leftOut
          rw [hright]
          exact ⟨(right, rightValue), rfl, heap,
            HeapHistoryIso.Extends.refl, hvalue⟩
  | letOp operation rest =>
      rw [IxIR1.runCode.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hoperation : IxIR1.runOp ctx fuel current left leftEnvironment
          operation with
      | error error =>
          rw [hoperation] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok operationOut =>
          rcases operationOut with ⟨middle, leftValue⟩
          rw [hoperation] at hrun
          simp only [bind, Except.bind] at hrun
          obtain ⟨rightOperationOut, hrightOperation,
              operationHeap, hentryOperation, hvalue⟩ :=
            smaller.runOp ctx current left right heap leftEnvironment
              rightEnvironment henvironment operation (middle, leftValue)
              hoperation
          rcases rightOperationOut with ⟨rightMiddle, rightValue⟩
          obtain ⟨rightOut, hrightRest, finalHeap,
              hoperationFinal, hresult⟩ :=
            smaller.runCode ctx current middle rightMiddle operationHeap
              (leftValue :: leftEnvironment)
              (rightValue :: rightEnvironment)
              (.cons hvalue (hentryOperation.rvals henvironment)) rest
              leftOut hrun
          refine ⟨rightOut, ?_, finalHeap,
            hentryOperation.trans hoperationFinal, hresult⟩
          rw [hrightOperation]
          simp only [bind, Except.bind]
          exact hrightRest
  | case scrutinee peelNat alternatives =>
      exact runCode_case_historyIso smaller ctx current left right heap
        leftEnvironment rightEnvironment henvironment scrutinee peelNat
        alternatives leftOut hrun

private theorem runOp_historyIsoStep {fuel : Nat}
    (smaller : EvalHistoryIsoAt fuel) :
    ∀ (ctx : Ctx) (current : FnDef)
      (left right : Store) (heap : HeapHistoryIso left right)
      (leftEnvironment rightEnvironment : List RVal),
    RValsIso heap.locRel leftEnvironment rightEnvironment →
    ∀ (operation : Op) (leftOut : Store × RVal),
      IxIR1.runOp ctx (fuel + 1) current left leftEnvironment operation =
        .ok leftOut →
      ∃ rightOut,
        IxIR1.runOp ctx (fuel + 1) current right rightEnvironment operation =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  intro ctx current left right heap leftEnvironment rightEnvironment
    henvironment operation leftOut hrun
  cases operation with
  | pure atom =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtom leftEnvironment atom with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftValue =>
          obtain ⟨rightValue, hright, hvalue⟩ :=
            resolveAtom_historyIso henvironment hleft
          rw [hleft] at hrun
          simp only [bind, Except.bind, Except.ok.injEq] at hrun
          subst leftOut
          rw [hright]
          exact ⟨(right, rightValue), rfl, heap,
            HeapHistoryIso.Extends.refl, hvalue⟩
  | alloc world identity arguments =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtoms leftEnvironment arguments with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftValues =>
          obtain ⟨rightValues, hright, hvalues⟩ :=
            resolveAtoms_historyIso henvironment hleft
          rw [hleft] at hrun
          simp only [bind, Except.bind, Except.ok.injEq] at hrun
          subst leftOut
          rw [hright]
          let next := heap.alloc (world := world)
            (leftNode := .ctorN identity leftValues.toArray)
            (rightNode := .ctorN identity rightValues.toArray)
            (.ctor (by simpa using hvalues))
          exact ⟨_, rfl, next, (fun h => .inr h),
            .loc (.inl ⟨rfl, rfl⟩)⟩
  | reuse target identity arguments =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleftArgs : resolveAtoms leftEnvironment arguments with
      | error error =>
          rw [hleftArgs] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftValues =>
          obtain ⟨rightValues, hrightArgs, hvalues⟩ :=
            resolveAtoms_historyIso henvironment hleftArgs
          rw [hleftArgs] at hrun
          rw [hrightArgs]
          simp only [bind, Except.bind] at hrun ⊢
          cases hleftTarget : resolveAtom leftEnvironment target with
          | error error =>
              rw [hleftTarget] at hrun
              simp only [bind, Except.bind] at hrun
              contradiction
          | ok leftTarget =>
              obtain ⟨rightTarget, hrightTarget, htarget⟩ :=
                resolveAtom_historyIso henvironment hleftTarget
              rw [hleftTarget] at hrun
              rw [hrightTarget]
              simp only [bind, Except.bind] at hrun ⊢
              cases htarget with
              | lit => simp at hrun
              | erased => simp at hrun
              | @loc leftLoc rightLoc hrel =>
                  cases hleftBox : left.get? leftLoc with
                  | none => simp [hleftBox] at hrun
                  | some leftBox =>
                      obtain ⟨rightBox, hrightBox, hbox⟩ :=
                        heap.boxes hrel hleftBox
                      rcases leftBox with ⟨leftWorld, leftRc, leftNode⟩
                      rcases rightBox with
                        ⟨rightWorld, rightRc, rightNode⟩
                      rcases hbox with ⟨hworld, hrc, hnode⟩
                      change leftWorld = rightWorld at hworld
                      change leftRc = rightRc at hrc
                      change NodeIso heap.locRel leftNode rightNode at hnode
                      subst rightWorld
                      subst rightRc
                      simp only [hleftBox] at hrun
                      simp only [hrightBox]
                      cases leftWorld with
                      | shared => simp at hrun
                      | unique =>
                          simp only [Except.ok.injEq] at hrun
                          subst leftOut
                          let leftSet := left.setBox leftLoc
                            ⟨.unique, 1, .ctorN identity
                              leftValues.toArray⟩
                          let rightSet := right.setBox rightLoc
                            ⟨.unique, 1, .ctorN identity
                              rightValues.toArray⟩
                          let base := heap.setBox hrel hleftBox hrightBox
                            (⟨rfl, rfl, .ctor (by simpa using hvalues)⟩ :
                              NodeBoxIso heap.locRel
                                ⟨.unique, 1,
                                  .ctorN identity leftValues.toArray⟩
                                ⟨.unique, 1,
                                  .ctorN identity rightValues.toArray⟩)
                          let next := base.nodesEq
                            (nextLeft :=
                              { leftSet with
                                reuses := leftSet.reuses + 1 })
                            (nextRight :=
                              { rightSet with
                                reuses := rightSet.reuses + 1 }) rfl rfl
                          exact ⟨_, rfl, next, (fun h => h), .loc hrel⟩
  | free target =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtom leftEnvironment target with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftTarget =>
          obtain ⟨rightTarget, hright, htarget⟩ :=
            resolveAtom_historyIso henvironment hleft
          rw [hleft] at hrun
          rw [hright]
          simp only [bind, Except.bind] at hrun ⊢
          cases htarget with
          | lit => simp at hrun
          | erased => simp at hrun
          | @loc leftLoc rightLoc hrel =>
              cases hleftBox : left.get? leftLoc with
              | none => simp [hleftBox] at hrun
              | some leftBox =>
                  obtain ⟨rightBox, hrightBox, hbox⟩ :=
                    heap.boxes hrel hleftBox
                  have hworld := hbox.world
                  simp only [hleftBox] at hrun
                  simp only [hrightBox]
                  cases hleftWorld : leftBox.world with
                  | shared => simp [hleftWorld] at hrun
                  | unique =>
                      have hrightWorld : rightBox.world = .unique := by
                        rw [← hworld, hleftWorld]
                      simp only [hleftWorld, hrightWorld,
                        Except.ok.injEq] at hrun ⊢
                      subst leftOut
                      let next := heap.kill hrel hleftBox hrightBox
                      exact ⟨_, rfl, next, (fun h => h), .erased⟩
  | dup target =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtom leftEnvironment target with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftTarget =>
          obtain ⟨rightTarget, hright, htarget⟩ :=
            resolveAtom_historyIso henvironment hleft
          rw [hleft] at hrun
          rw [hright]
          simp only [bind, Except.bind] at hrun ⊢
          cases htarget with
          | lit =>
              simp only [Except.ok.injEq] at hrun
              subst leftOut
              exact ⟨_, rfl, heap, HeapHistoryIso.Extends.refl, .lit⟩
          | erased =>
              simp only [Except.ok.injEq] at hrun
              subst leftOut
              exact ⟨_, rfl, heap, HeapHistoryIso.Extends.refl, .erased⟩
          | @loc leftLoc rightLoc hrel =>
              cases hleftBox : left.get? leftLoc with
              | none => simp [hleftBox] at hrun
              | some leftBox =>
                  obtain ⟨rightBox, hrightBox, hbox⟩ :=
                    heap.boxes hrel hleftBox
                  rcases leftBox with ⟨leftWorld, leftRc, leftNode⟩
                  rcases rightBox with ⟨rightWorld, rightRc, rightNode⟩
                  rcases hbox with ⟨hworld, hrc, hnode⟩
                  change leftWorld = rightWorld at hworld
                  change leftRc = rightRc at hrc
                  change NodeIso heap.locRel leftNode rightNode at hnode
                  subst rightWorld
                  subst rightRc
                  simp only [hleftBox] at hrun
                  simp only [hrightBox]
                  cases leftWorld with
                  | unique => simp at hrun
                  | shared =>
                      simp only [Except.ok.injEq] at hrun
                      subst leftOut
                      let next := (heap.setBox hrel hleftBox hrightBox
                        (⟨rfl, rfl, hnode⟩ : NodeBoxIso heap.locRel
                          ⟨.shared, leftRc + 1, leftNode⟩
                          ⟨.shared, leftRc + 1, rightNode⟩)).rcTick
                      exact ⟨_, rfl, next, (fun h => h), .loc hrel⟩
  | drop target =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtom leftEnvironment target with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftTarget =>
          obtain ⟨rightTarget, hright, htarget⟩ :=
            resolveAtom_historyIso henvironment hleft
          rw [hleft] at hrun
          rw [hright]
          simp only [bind, Except.bind] at hrun ⊢
          cases htarget with
          | lit =>
              simp only [Except.ok.injEq] at hrun
              subst leftOut
              exact ⟨_, rfl, heap, HeapHistoryIso.Extends.refl, .erased⟩
          | erased =>
              simp only [Except.ok.injEq] at hrun
              subst leftOut
              exact ⟨_, rfl, heap, HeapHistoryIso.Extends.refl, .erased⟩
          | @loc leftLoc rightLoc hrel =>
              dsimp only at hrun ⊢
              cases hdrop : IxIR1.dropVal ctx fuel left (.loc leftLoc) with
              | error error =>
                  rw [hdrop] at hrun
                  simp only [bind, Except.bind] at hrun
                  contradiction
              | ok nextLeft =>
                  rw [hdrop] at hrun
                  simp only [bind, Except.bind, Except.ok.injEq] at hrun
                  subst leftOut
                  obtain ⟨nextRight, hrightDrop, nextHeap, hext⟩ :=
                    smaller.dropVal ctx left right heap _ _ (.loc hrel)
                      nextLeft hdrop
                  rw [hrightDrop]
                  exact ⟨_, rfl, nextHeap, hext, .erased⟩
  | dropU target =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtom leftEnvironment target with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftTarget =>
          obtain ⟨rightTarget, hright, htarget⟩ :=
            resolveAtom_historyIso henvironment hleft
          rw [hleft] at hrun
          rw [hright]
          simp only [bind, Except.bind] at hrun ⊢
          cases htarget with
          | lit =>
              simp only [Except.ok.injEq] at hrun
              subst leftOut
              exact ⟨_, rfl, heap, HeapHistoryIso.Extends.refl, .erased⟩
          | erased =>
              simp only [Except.ok.injEq] at hrun
              subst leftOut
              exact ⟨_, rfl, heap, HeapHistoryIso.Extends.refl, .erased⟩
          | @loc leftLoc rightLoc hrel =>
              dsimp only at hrun ⊢
              cases hdrop : IxIR1.dropUVal ctx fuel left (.loc leftLoc) with
              | error error =>
                  rw [hdrop] at hrun
                  simp only [bind, Except.bind] at hrun
                  contradiction
              | ok nextLeft =>
                  rw [hdrop] at hrun
                  simp only [bind, Except.bind, Except.ok.injEq] at hrun
                  subst leftOut
                  obtain ⟨nextRight, hrightDrop, nextHeap, hext⟩ :=
                    smaller.dropUVal ctx left right heap _ _ (.loc hrel)
                      nextLeft hdrop
                  rw [hrightDrop]
                  exact ⟨_, rfl, nextHeap, hext, .erased⟩
  | fetch target field =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtom leftEnvironment target with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftTarget =>
          obtain ⟨rightTarget, hright, htarget⟩ :=
            resolveAtom_historyIso henvironment hleft
          rw [hleft] at hrun
          rw [hright]
          simp only [bind, Except.bind] at hrun ⊢
          cases htarget with
          | lit => simp at hrun
          | erased => simp at hrun
          | @loc leftLoc rightLoc hrel =>
              cases hleftBox : left.get? leftLoc with
              | none => simp [hleftBox] at hrun
              | some leftBox =>
                  obtain ⟨rightBox, hrightBox, hbox⟩ :=
                    heap.boxes hrel hleftBox
                  rcases leftBox with ⟨leftWorld, leftRc, leftNode⟩
                  rcases rightBox with ⟨rightWorld, rightRc, rightNode⟩
                  rcases hbox with ⟨hworld, hrc, hnodeIso⟩
                  change leftWorld = rightWorld at hworld
                  change leftRc = rightRc at hrc
                  change NodeIso heap.locRel leftNode rightNode at hnodeIso
                  subst rightWorld
                  subst rightRc
                  simp only [hleftBox] at hrun
                  simp only [hrightBox]
                  cases hnodeIso with
                  | pap harguments => simp at hrun
                  | @ctor identity leftFields rightFields hfields =>
                      simp only
                      cases hfield : leftFields[field]? with
                      | none => simp [hfield] at hrun
                      | some leftValue =>
                          obtain ⟨rightValue, hrightField, hvalue⟩ :=
                            hfields.get? (by simpa using hfield)
                          simp only [hfield, Except.ok.injEq] at hrun
                          subst leftOut
                          refine ⟨(right, rightValue), ?_, heap,
                            HeapHistoryIso.Extends.refl, hvalue⟩
                          have hrightFieldArray :
                              rightFields[field]? = some rightValue := by
                            simpa using hrightField
                          simp [hrightFieldArray]
  | call function arguments =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtoms leftEnvironment arguments with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftValues =>
          obtain ⟨rightValues, hright, hvalues⟩ :=
            resolveAtoms_historyIso henvironment hleft
          rw [hleft] at hrun
          rw [hright]
          simp only [bind, Except.bind] at hrun ⊢
          exact smaller.invoke ctx function leftValues rightValues left right
            heap hvalues leftOut hrun
  | callSelf arguments =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtoms leftEnvironment arguments with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftValues =>
          obtain ⟨rightValues, hright, hvalues⟩ :=
            resolveAtoms_historyIso henvironment hleft
          rw [hleft] at hrun
          rw [hright]
          simp only [bind, Except.bind] at hrun ⊢
          have hlength := hvalues.lengths
          by_cases harity : leftValues.length = current.arity
          · have hrightArity : rightValues.length = current.arity := by
              rw [← hlength]
              exact harity
            simp [harity] at hrun
            cases hbody : IxIR1.runCode ctx fuel current left
                leftValues.reverse current.body with
            | error error =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                contradiction
            | ok bodyOut =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                have hout := (checkResultWorld_ok hrun).1
                subst leftOut
                obtain ⟨rightBodyOut, hrightBody, bodyHeap,
                    hext, hvalue⟩ :=
                  smaller.runCode ctx current left right heap
                    leftValues.reverse rightValues.reverse hvalues.reverse
                    current.body bodyOut hbody
                rcases bodyOut with ⟨bodyStore, bodyValue⟩
                rcases rightBodyOut with
                  ⟨rightBodyStore, rightBodyValue⟩
                have hrightWorld := checkResultWorld_historyIso bodyHeap
                  hvalue current.result hrun
                refine ⟨_, ?_, bodyHeap, hext, hvalue⟩
                simp [hrightArity, hrightBody, hrightWorld]
          · have hrightArity : rightValues.length ≠ current.arity := by
              intro heq
              exact harity (hlength.trans heq)
            simp [harity, hrightArity] at hrun
  | papp function arguments =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtoms leftEnvironment arguments with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftValues =>
          obtain ⟨rightValues, hright, hvalues⟩ :=
            resolveAtoms_historyIso henvironment hleft
          rw [hleft] at hrun
          rw [hright]
          simp only [bind, Except.bind] at hrun ⊢
          cases hdecl : ctx.decls function with
          | none => simp [hdecl] at hrun
          | some declaration =>
              simp only [hdecl] at hrun ⊢
              by_cases hunder : leftValues.length < declArity declaration
              · have hrightUnder :
                    rightValues.length < declArity declaration := by
                  rw [← hvalues.lengths]
                  exact hunder
                simp only [hunder, hrightUnder, if_true,
                  Except.ok.injEq] at hrun ⊢
                subst leftOut
                let next := heap.alloc (world := .shared)
                  (leftNode := .papN function (declArity declaration)
                    leftValues.toArray)
                  (rightNode := .papN function (declArity declaration)
                    rightValues.toArray)
                  (.pap (by simpa using hvalues))
                exact ⟨_, rfl, next, (fun h => .inr h),
                  .loc (.inl ⟨rfl, rfl⟩)⟩
              · simp [hunder] at hrun
  | apply function arguments =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleftFunction : resolveAtom leftEnvironment function with
      | error error =>
          rw [hleftFunction] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftFunction =>
          obtain ⟨rightFunction, hrightFunction, hfunction⟩ :=
            resolveAtom_historyIso henvironment hleftFunction
          rw [hleftFunction] at hrun
          rw [hrightFunction]
          simp only [bind, Except.bind] at hrun ⊢
          cases hleftArgs : resolveAtoms leftEnvironment arguments with
          | error error =>
              rw [hleftArgs] at hrun
              simp only [bind, Except.bind] at hrun
              contradiction
          | ok leftValues =>
              obtain ⟨rightValues, hrightArgs, hvalues⟩ :=
                resolveAtoms_historyIso henvironment hleftArgs
              rw [hleftArgs] at hrun
              rw [hrightArgs]
              simp only [bind, Except.bind] at hrun ⊢
              exact smaller.applyGo ctx left right heap leftFunction
                rightFunction leftValues rightValues hfunction hvalues
                leftOut hrun
  | extern function arguments =>
      rw [IxIR1.runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hleft : resolveAtoms leftEnvironment arguments with
      | error error =>
          rw [hleft] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok leftValues =>
          obtain ⟨rightValues, hright, hvalues⟩ :=
            resolveAtoms_historyIso henvironment hleft
          rw [hleft] at hrun
          rw [hright]
          simp only [bind, Except.bind] at hrun ⊢
          cases horacle : callScalarOracle ctx function leftValues with
          | error error =>
              rw [horacle] at hrun
              simp only [bind, Except.bind] at hrun
              contradiction
          | ok leftValue =>
              rw [horacle] at hrun
              simp only [bind, Except.bind, Except.ok.injEq] at hrun
              subst leftOut
              obtain ⟨rightValue, hrightOracle, hvalue⟩ :=
                callScalarOracle_historyIso hvalues horacle
              rw [hrightOracle]
              exact ⟨_, rfl, heap, HeapHistoryIso.Extends.refl, hvalue⟩

private theorem invoke_historyIsoStep {fuel : Nat}
    (smaller : EvalHistoryIsoAt fuel) :
    ∀ (ctx : Ctx) (function : Ix.Compiler.Ixon.Address)
      (leftArguments rightArguments : List RVal)
      (left right : Store) (heap : HeapHistoryIso left right),
    RValsIso heap.locRel leftArguments rightArguments →
    ∀ (leftOut : Store × RVal),
      IxIR1.invoke ctx (fuel + 1) function leftArguments left = .ok leftOut →
      ∃ rightOut,
        IxIR1.invoke ctx (fuel + 1) function rightArguments right =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  intro ctx function leftArguments rightArguments left right heap
    harguments leftOut hrun
  rw [IxIR1.invoke.eq_def] at hrun ⊢
  dsimp only at hrun ⊢
  cases hdecl : ctx.decls function with
  | none => simp [hdecl] at hrun
  | some declaration =>
      simp only [hdecl] at hrun ⊢
      cases declaration with
      | extern arity =>
          have hlength := harguments.lengths
          by_cases hsame : leftArguments.length = arity
          · have hrightSame : rightArguments.length = arity := by
              rw [← hlength]
              exact hsame
            simp [hsame] at hrun
            cases horacle : callScalarOracle ctx function leftArguments with
            | error error =>
                rw [horacle] at hrun
                contradiction
            | ok leftValue =>
                rw [horacle] at hrun
                injection hrun with hout
                subst leftOut
                obtain ⟨rightValue, hrightOracle, hvalue⟩ :=
                  callScalarOracle_historyIso harguments horacle
                refine ⟨(right, rightValue), ?_, heap,
                  HeapHistoryIso.Extends.refl, hvalue⟩
                simp [hrightSame, hrightOracle]
          · have hrightSame : rightArguments.length ≠ arity := by
              intro heq
              exact hsame (hlength.trans heq)
            simp [hsame] at hrun
      | fn definition =>
          have hlength := harguments.lengths
          by_cases hsame : leftArguments.length = definition.arity
          · have hrightSame :
                rightArguments.length = definition.arity := by
              rw [← hlength]
              exact hsame
            simp [hsame] at hrun
            cases hbody : IxIR1.runCode ctx fuel definition left
                leftArguments.reverse definition.body with
            | error error =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                contradiction
            | ok bodyOut =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                have hout := (checkResultWorld_ok hrun).1
                subst leftOut
                obtain ⟨rightBodyOut, hrightBody, bodyHeap,
                    hext, hvalue⟩ :=
                  smaller.runCode ctx definition left right heap
                    leftArguments.reverse rightArguments.reverse
                    harguments.reverse definition.body bodyOut hbody
                rcases bodyOut with ⟨bodyStore, bodyValue⟩
                rcases rightBodyOut with
                  ⟨rightBodyStore, rightBodyValue⟩
                have hrightWorld := checkResultWorld_historyIso bodyHeap
                  hvalue definition.result hrun
                refine ⟨_, ?_, bodyHeap, hext, hvalue⟩
                simp [hrightSame, hrightBody]
                simpa only [bind, Except.bind] using hrightWorld
          · have hrightSame :
                rightArguments.length ≠ definition.arity := by
              intro heq
              exact hsame (hlength.trans heq)
            simp [hsame] at hrun

private theorem applyGo_historyIsoStep {fuel : Nat}
    (smaller : EvalHistoryIsoAt fuel) :
    ∀ (ctx : Ctx) (left right : Store)
      (heap : HeapHistoryIso left right)
      (leftFunction rightFunction : RVal)
      (leftArguments rightArguments : List RVal),
    RValIso heap.locRel leftFunction rightFunction →
    RValsIso heap.locRel leftArguments rightArguments →
    ∀ (leftOut : Store × RVal),
      IxIR1.applyGo ctx (fuel + 1) left leftFunction leftArguments =
        .ok leftOut →
      ∃ rightOut,
        IxIR1.applyGo ctx (fuel + 1) right rightFunction rightArguments =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  intro ctx left right heap leftFunction rightFunction leftArguments
    rightArguments hfunction harguments leftOut hrun
  rw [IxIR1.applyGo.eq_def] at hrun ⊢
  dsimp only at hrun ⊢
  cases hfunction with
  | lit => simp at hrun
  | erased =>
      cases hdrop : IxIR1.dropMany ctx fuel left leftArguments with
      | error error =>
          rw [hdrop] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok nextLeft =>
          rw [hdrop] at hrun
          simp only [bind, Except.bind, Except.ok.injEq] at hrun
          subst leftOut
          obtain ⟨nextRight, hrightDrop, nextHeap, hext⟩ :=
            smaller.dropMany ctx left right heap leftArguments rightArguments
              harguments nextLeft hdrop
          rw [hrightDrop]
          exact ⟨_, rfl, nextHeap, hext, .erased⟩
  | @loc leftLoc rightLoc hrel =>
      cases hleftBox : left.get? leftLoc with
      | none => simp [hleftBox] at hrun
      | some leftBox =>
          obtain ⟨rightBox, hrightBox, hbox⟩ :=
            heap.boxes hrel hleftBox
          rcases leftBox with ⟨leftWorld, leftRc, leftNode⟩
          rcases rightBox with ⟨rightWorld, rightRc, rightNode⟩
          rcases hbox with ⟨hworld, hrc, hnode⟩
          change leftWorld = rightWorld at hworld
          change leftRc = rightRc at hrc
          change NodeIso heap.locRel leftNode rightNode at hnode
          subst rightWorld
          subst rightRc
          simp only [hleftBox] at hrun
          simp only [hrightBox]
          cases hnode with
          | ctor hfields => simp at hrun
          | @pap function arity leftCaptured rightCaptured hcaptured =>
              dsimp only at hrun ⊢
              cases hdup : dupVals left leftCaptured.toList with
              | error error =>
                  rw [hdup] at hrun
                  simp only [bind, Except.bind] at hrun
                  contradiction
              | ok duplicatedLeft =>
                  rw [hdup] at hrun
                  simp only [bind, Except.bind] at hrun
                  obtain ⟨duplicatedRight, hrightDup, duplicateHeap,
                      hentryDuplicate⟩ :=
                    dupVals_historyIso heap hcaptured hdup
                  cases hdrop : IxIR1.dropVal ctx fuel duplicatedLeft
                      (.loc leftLoc) with
                  | error error =>
                      rw [hdrop] at hrun
                      simp only [bind, Except.bind] at hrun
                      contradiction
                  | ok readyLeft =>
                      rw [hdrop] at hrun
                      simp only [bind, Except.bind] at hrun
                      obtain ⟨readyRight, hrightDrop, readyHeap,
                          hduplicateReady⟩ :=
                        smaller.dropVal ctx duplicatedLeft duplicatedRight
                          duplicateHeap (.loc leftLoc) (.loc rightLoc)
                          (hentryDuplicate.rval (.loc hrel)) readyLeft hdrop
                      let hentryReady : heap.Extends readyHeap :=
                        HeapHistoryIso.Extends.trans hentryDuplicate
                          hduplicateReady
                      let leftTotal := leftCaptured.toList ++ leftArguments
                      let rightTotal := rightCaptured.toList ++ rightArguments
                      let htotal : RValsIso readyHeap.locRel
                          leftTotal rightTotal :=
                        (hentryReady.rvals hcaptured).append
                          (hentryReady.rvals harguments)
                      have hlength : leftTotal.length = rightTotal.length :=
                        htotal.lengths
                      by_cases hunder : leftTotal.length < arity
                      · have hrightUnder : rightTotal.length < arity := by
                          rw [← hlength]
                          exact hunder
                        have hunderRaw :
                            (leftCaptured.toList ++ leftArguments).length <
                              arity := by
                          simpa [leftTotal] using hunder
                        have hunderSize :
                            leftCaptured.size + leftArguments.length <
                              arity := by
                          simpa [leftTotal] using hunder
                        have hrightUnderRaw :
                            (rightCaptured.toList ++ rightArguments).length <
                              arity := by
                          simpa [rightTotal] using hrightUnder
                        have hrightUnderSize :
                            rightCaptured.size + rightArguments.length <
                              arity := by
                          simpa [rightTotal] using hrightUnder
                        simp only [hunderRaw, if_true,
                          Except.ok.injEq] at hrun
                        subst leftOut
                        let next := readyHeap.alloc (world := .shared)
                          (leftNode := .papN function arity
                            leftTotal.toArray)
                          (rightNode := .papN function arity
                            rightTotal.toArray)
                          (.pap (by simpa using htotal))
                        have hreadyNext : readyHeap.Extends next := by
                          intro l r hknown
                          change (l = readyLeft.nodes.size ∧
                            r = readyRight.nodes.size) ∨
                              readyHeap.locRel l r
                          exact .inr hknown
                        have hfresh : RValIso next.locRel
                            (.loc readyLeft.nodes.size)
                            (.loc readyRight.nodes.size) := by
                          apply RValIso.loc
                          change (readyLeft.nodes.size = readyLeft.nodes.size ∧
                            readyRight.nodes.size = readyRight.nodes.size) ∨
                              readyHeap.locRel _ _
                          exact .inl ⟨rfl, rfl⟩
                        let rightAllocated := readyRight.allocNode .shared
                          (.papN function arity rightTotal.toArray)
                        refine ⟨(rightAllocated.1,
                          .loc rightAllocated.2), ?_, next,
                          hentryReady.trans hreadyNext, ?_⟩
                        · rw [hrightDup]
                          simp only [bind, Except.bind]
                          rw [hrightDrop]
                          simp only [bind, Except.bind]
                          simp [rightTotal, rightAllocated,
                            hrightUnderSize]
                        · simpa [leftTotal, rightTotal, rightAllocated,
                            Store.allocNode] using hfresh
                      · have hrightUnder : ¬ rightTotal.length < arity := by
                          intro hlt
                          exact hunder (lt_of_eq_of_lt hlength hlt)
                        by_cases hexact : leftTotal.length = arity
                        · have hrightExact : rightTotal.length = arity := by
                            rw [← hlength]
                            exact hexact
                          have hunderRaw :
                              ¬ (leftCaptured.toList ++
                                leftArguments).length < arity := by
                            simpa [leftTotal] using hunder
                          have hexactRaw :
                              (leftCaptured.toList ++
                                leftArguments).length = arity := by
                            simpa [leftTotal] using hexact
                          have hrightUnderRaw :
                              ¬ (rightCaptured.toList ++
                                rightArguments).length < arity := by
                            simpa [rightTotal] using hrightUnder
                          have hrightExactRaw :
                              (rightCaptured.toList ++
                                rightArguments).length = arity := by
                            simpa [rightTotal] using hrightExact
                          have hunderSize :
                              ¬ leftCaptured.size + leftArguments.length <
                                arity := by
                            simpa [leftTotal] using hunder
                          have hexactSize :
                              leftCaptured.size + leftArguments.length =
                                arity := by
                            simpa [leftTotal] using hexact
                          have hrightUnderSize :
                              ¬ rightCaptured.size + rightArguments.length <
                                arity := by
                            simpa [rightTotal] using hrightUnder
                          have hrightExactSize :
                              rightCaptured.size + rightArguments.length =
                                arity := by
                            simpa [rightTotal] using hrightExact
                          obtain ⟨definition, hdecl, hpapsafe⟩ :
                              ∃ definition,
                                ctx.decls function = some definition ∧
                                  declPapSafe definition = true := by
                            cases hdecl : ctx.decls function with
                            | none =>
                                simp [hunderSize, hexactSize, hdecl] at hrun
                            | some definition =>
                                cases hpapsafe : declPapSafe definition with
                                | false =>
                                    simp [hunderSize, hexactSize, hdecl,
                                      hpapsafe] at hrun
                                | true => exact ⟨definition, rfl, hpapsafe⟩
                          simp [hunderSize, hexactSize, hdecl,
                            hpapsafe] at hrun
                          have hrunInvoke : IxIR1.invoke ctx fuel function
                              leftTotal readyLeft = .ok leftOut := by
                            simpa [leftTotal] using hrun
                          obtain ⟨rightOut, hrightInvoke, finalHeap,
                              hreadyFinal, hvalue⟩ :=
                            smaller.invoke ctx function leftTotal rightTotal
                              readyLeft readyRight readyHeap htotal leftOut
                              hrunInvoke
                          refine ⟨rightOut, ?_, finalHeap,
                            hentryReady.trans hreadyFinal, hvalue⟩
                          rw [hrightDup]
                          simp only [bind, Except.bind]
                          rw [hrightDrop]
                          simp only [bind, Except.bind]
                          simpa [rightTotal, hrightUnderSize,
                            hrightExactSize, hdecl, hpapsafe] using hrightInvoke
                        · have hrightExact : rightTotal.length ≠ arity := by
                            intro heq
                            exact hexact (hlength.trans heq)
                          have hunderRaw :
                              ¬ (leftCaptured.toList ++
                                leftArguments).length < arity := by
                            simpa [leftTotal] using hunder
                          have hexactRaw :
                              (leftCaptured.toList ++
                                leftArguments).length ≠ arity := by
                            simpa [leftTotal] using hexact
                          have hrightUnderRaw :
                              ¬ (rightCaptured.toList ++
                                rightArguments).length < arity := by
                            simpa [rightTotal] using hrightUnder
                          have hrightExactRaw :
                              (rightCaptured.toList ++
                                rightArguments).length ≠ arity := by
                            simpa [rightTotal] using hrightExact
                          have hunderSize :
                              ¬ leftCaptured.size + leftArguments.length <
                                arity := by
                            simpa [leftTotal] using hunder
                          have hexactSize :
                              leftCaptured.size + leftArguments.length ≠
                                arity := by
                            simpa [leftTotal] using hexact
                          have hrightUnderSize :
                              ¬ rightCaptured.size + rightArguments.length <
                                arity := by
                            simpa [rightTotal] using hrightUnder
                          have hrightExactSize :
                              rightCaptured.size + rightArguments.length ≠
                                arity := by
                            simpa [rightTotal] using hrightExact
                          obtain ⟨definition, hdecl, hpapsafe⟩ :
                              ∃ definition,
                                ctx.decls function = some definition ∧
                                  declPapSafe definition = true := by
                            cases hdecl : ctx.decls function with
                            | none =>
                                simp [hunderSize, hexactSize, hdecl] at hrun
                            | some definition =>
                                cases hpapsafe : declPapSafe definition with
                                | false =>
                                    simp [hunderSize, hexactSize, hdecl,
                                      hpapsafe] at hrun
                                | true => exact ⟨definition, rfl, hpapsafe⟩
                          simp [hunderSize, hexactSize, hdecl,
                            hpapsafe] at hrun
                          cases hinvoke : IxIR1.invoke ctx fuel function
                              (leftTotal.take arity) readyLeft with
                          | error error =>
                              rw [hinvoke] at hrun
                              simp only [bind, Except.bind] at hrun
                              contradiction
                          | ok calledLeft =>
                              rw [hinvoke] at hrun
                              simp only [bind, Except.bind] at hrun
                              obtain ⟨calledRight, hrightInvoke, calledHeap,
                                  hreadyCalled, hcalledValue⟩ :=
                                smaller.invoke ctx function
                                  (leftTotal.take arity)
                                  (rightTotal.take arity) readyLeft readyRight
                                  readyHeap (htotal.take arity) calledLeft
                                  hinvoke
                              rcases calledLeft with
                                ⟨calledLeftStore, calledLeftValue⟩
                              rcases calledRight with
                                ⟨calledRightStore, calledRightValue⟩
                              have hrunApply : IxIR1.applyGo ctx fuel
                                  calledLeftStore calledLeftValue
                                  (leftTotal.drop arity) = .ok leftOut := by
                                simpa [leftTotal] using hrun
                              obtain ⟨rightOut, hrightApply, finalHeap,
                                  hcalledFinal, hresult⟩ :=
                                smaller.applyGo ctx calledLeftStore
                                  calledRightStore calledHeap calledLeftValue
                                  calledRightValue (leftTotal.drop arity)
                                  (rightTotal.drop arity) hcalledValue
                                  (hreadyCalled.rvals (htotal.drop arity))
                                  leftOut hrunApply
                              refine ⟨rightOut, ?_, finalHeap,
                                hentryReady.trans
                                  (hreadyCalled.trans hcalledFinal), hresult⟩
                              rw [hrightDup]
                              simp only [bind, Except.bind]
                              rw [hrightDrop]
                              simp only [bind, Except.bind]
                              simp [hrightUnderSize, hrightExactSize, hdecl,
                                hpapsafe]
                              rw [hrightInvoke]
                              simp only [bind, Except.bind]
                              exact hrightApply

private theorem evalHistoryIsoAt : ∀ fuel, EvalHistoryIsoAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [IxIR1.runCode, IxIR1.runOp, IxIR1.invoke, IxIR1.applyGo,
          IxIR1.dropVal, IxIR1.dropMany, IxIR1.dropUVal,
          IxIR1.dropManyU] at *
  | succ fuel smaller =>
      let drops := dropHistoryIsoAt (fuel + 1)
      exact ⟨runCode_historyIsoStep smaller,
        runOp_historyIsoStep smaller,
        invoke_historyIsoStep smaller,
        applyGo_historyIsoStep smaller,
        drops.dropVal, drops.dropMany, drops.dropUVal, drops.dropManyU⟩

/-- Successful code evaluation commutes with a heap-history isomorphism.
Concrete allocation indices and cost counters may differ, while every live
result and every older related root remains paired. -/
theorem runCode_historyIso {ctx : Ctx} {fuel : Nat} {current : FnDef}
    {left right : Store} (heap : HeapHistoryIso left right)
    {leftEnvironment rightEnvironment : List RVal}
    (henvironment : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    {input : Code} {leftOut : Store × RVal}
    (hrun : IxIR1.runCode ctx fuel current left leftEnvironment input =
      .ok leftOut) :
    ∃ rightOut,
      IxIR1.runCode ctx fuel current right rightEnvironment input =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut :=
  (evalHistoryIsoAt fuel).runCode ctx current left right heap leftEnvironment
    rightEnvironment henvironment input leftOut hrun

theorem runOp_historyIso {ctx : Ctx} {fuel : Nat} {current : FnDef}
    {left right : Store} (heap : HeapHistoryIso left right)
    {leftEnvironment rightEnvironment : List RVal}
    (henvironment : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    {operation : Op} {leftOut : Store × RVal}
    (hrun : IxIR1.runOp ctx fuel current left leftEnvironment operation =
      .ok leftOut) :
    ∃ rightOut,
      IxIR1.runOp ctx fuel current right rightEnvironment operation =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut :=
  (evalHistoryIsoAt fuel).runOp ctx current left right heap leftEnvironment
    rightEnvironment henvironment operation leftOut hrun

theorem invoke_historyIso {ctx : Ctx} {fuel : Nat}
    {function : Ix.Compiler.Ixon.Address}
    {leftArguments rightArguments : List RVal}
    {left right : Store} (heap : HeapHistoryIso left right)
    (harguments : RValsIso heap.locRel leftArguments rightArguments)
    {leftOut : Store × RVal}
    (hrun : IxIR1.invoke ctx fuel function leftArguments left = .ok leftOut) :
    ∃ rightOut,
      IxIR1.invoke ctx fuel function rightArguments right = .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut :=
  (evalHistoryIsoAt fuel).invoke ctx function leftArguments rightArguments
    left right heap harguments leftOut hrun

theorem applyGo_historyIso {ctx : Ctx} {fuel : Nat}
    {left right : Store} (heap : HeapHistoryIso left right)
    {leftFunction rightFunction : RVal}
    {leftArguments rightArguments : List RVal}
    (hfunction : RValIso heap.locRel leftFunction rightFunction)
    (harguments : RValsIso heap.locRel leftArguments rightArguments)
    {leftOut : Store × RVal}
    (hrun : IxIR1.applyGo ctx fuel left leftFunction leftArguments =
      .ok leftOut) :
    ∃ rightOut,
      IxIR1.applyGo ctx fuel right rightFunction rightArguments =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut :=
  (evalHistoryIsoAt fuel).applyGo ctx left right heap leftFunction
    rightFunction leftArguments rightArguments hfunction harguments leftOut
    hrun

theorem dropVal_historyIso {ctx : Ctx} {fuel : Nat}
    {left right : Store} (heap : HeapHistoryIso left right)
    {leftValue rightValue : RVal}
    (hvalue : RValIso heap.locRel leftValue rightValue)
    {leftOut : Store}
    (hrun : IxIR1.dropVal ctx fuel left leftValue = .ok leftOut) :
    ∃ rightOut,
      IxIR1.dropVal ctx fuel right rightValue = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut :=
  (dropHistoryIsoAt fuel).dropVal ctx left right heap leftValue rightValue
    hvalue leftOut hrun

/-- Unique deep destruction commutes with allocation-history isomorphism. -/
theorem dropUVal_historyIso {ctx : Ctx} {fuel : Nat}
    {left right : Store} (heap : HeapHistoryIso left right)
    {leftValue rightValue : RVal}
    (hvalue : RValIso heap.locRel leftValue rightValue)
    {leftOut : Store}
    (hrun : IxIR1.dropUVal ctx fuel left leftValue = .ok leftOut) :
    ∃ rightOut,
      IxIR1.dropUVal ctx fuel right rightValue = .ok rightOut ∧
        StoreHistoryIso heap leftOut rightOut :=
  (dropHistoryIsoAt fuel).dropUVal ctx left right heap leftValue rightValue
    hvalue leftOut hrun
end Ix.Compiler.IxIR1.Sim
