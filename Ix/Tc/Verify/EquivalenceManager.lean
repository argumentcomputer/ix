import Ix.Tc.Verify.Totalization
import Ix.Tc.Verify.Expr
import Batteries.Data.Array.Lemmas
import Std.Data.HashMap.Lemmas

/-!
# Semantic validity of the DefEq equivalence manager

The production manager is a union-find whose reads perform path halving.
This file verifies it once against an arbitrary equivalence relation on
`EqKey`.  The invariant deliberately does not depend on acyclicity or rank
correctness: the bounded `find` may stop early, but every traversed parent
edge remains semantically valid.  That is sufficient for sound positive
queries, root representatives, path compression, and union.
-/

namespace Ix.Tc

namespace EquivManager

private instance : ReflBEq EqKey where
  rfl := by
    intro key
    rcases key with ⟨exprAddr, ctxAddr, lbr, exprLbr⟩
    change ((exprAddr == exprAddr) && (ctxAddr == ctxAddr) &&
      (lbr == lbr) && (exprLbr == exprLbr)) = true
    simp

private instance : LawfulBEq EqKey where
  eq_of_beq := by
    intro left right h
    rcases left with ⟨leftExpr, leftCtx, leftLbr, leftExprLbr⟩
    rcases right with ⟨rightExpr, rightCtx, rightLbr, rightExprLbr⟩
    change ((leftExpr == rightExpr) && (leftCtx == rightCtx) &&
      (leftLbr == rightLbr) && (leftExprLbr == rightExprLbr)) = true at h
    simp only [Bool.and_eq_true] at h
    have hexpr : leftExpr = rightExpr := eq_of_beq h.1.1.1
    have hctx : leftCtx = rightCtx := eq_of_beq h.1.1.2
    have hlbr : leftLbr = rightLbr := eq_of_beq h.1.2
    have hexprLbr : leftExprLbr = rightExprLbr := eq_of_beq h.2
    subst rightExpr
    subst rightCtx
    subst rightLbr
    subst rightExprLbr
    rfl

private instance : LawfulHashable EqKey where
  hash_eq left right h := by
    have heq : left = right := eq_of_beq h
    subst right
    rfl

private theorem Array.getElemBang_setBang
    {α : Type} [Inhabited α] (xs : Array α) (i j : Nat) (v : α)
    (hi : i < xs.size) (hj : j < xs.size) :
    (xs.set! i v)[j]! = if i = j then v else xs[j]! := by
  simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hi, hj,
    Array.getElem_set]

private theorem Array.getElemBang_push
    {α : Type} [Inhabited α] (xs : Array α) (v : α) (i : Nat)
    (hi : i < (xs.push v).size) :
    (xs.push v)[i]! = if h : i < xs.size then xs[i]! else v := by
  by_cases h : i < xs.size
  · simp [getElem!_def, Array.getElem?_push, h, Nat.ne_of_lt h]
  · have hieq : i = xs.size := by
      simp only [Array.size_push] at hi
      omega
    subst i
    simp

/-- Semantic validity of the mutable parent table against fixed node labels.
Every parent stays in bounds and every parent edge denotes the selected
equivalence relation. -/
structure ParentSound (R : EqKey → EqKey → Prop)
    (labels : Array EqKey) (parent : Array Nat) : Prop where
  size_eq : labels.size = parent.size
  parent_lt : ∀ {i}, i < parent.size → parent[i]! < parent.size
  edge : ∀ {i}, i < parent.size →
    R labels[i]! labels[parent[i]!]!

namespace ParentSound

/-- Relation weakening leaves the representation facts untouched. -/
theorem mono {R S : EqKey → EqKey → Prop} {labels : Array EqKey}
    {parent : Array Nat} (hRS : ∀ {a b}, R a b → S a b)
    (h : ParentSound R labels parent) : ParentSound S labels parent :=
  ⟨h.size_eq, h.parent_lt, fun hi => hRS (h.edge hi)⟩

/-- One path-halving write replaces `i → parent(i)` by
`i → parent(parent(i))`; transitivity proves the new edge sound. -/
theorem halve {R : EqKey → EqKey → Prop} (hR : Equivalence R)
    {labels : Array EqKey} {parent : Array Nat}
    (h : ParentSound R labels parent) {i : Nat}
    (hi : i < parent.size) :
    ParentSound R labels (parent.set! i parent[parent[i]!]!) := by
  let p := parent[i]!
  let gp := parent[p]!
  have hp : p < parent.size := h.parent_lt hi
  have hgp : gp < parent.size := h.parent_lt hp
  have hip : R labels[i]! labels[p]! := h.edge hi
  have hpgp : R labels[p]! labels[gp]! := h.edge hp
  have higp : R labels[i]! labels[gp]! := hR.trans hip hpgp
  refine ⟨?_, ?_, ?_⟩
  · simpa [Array.size_set!] using h.size_eq
  · intro j hj
    have hj' : j < parent.size := by simpa [Array.size_set!] using hj
    rw [Array.getElemBang_setBang parent i j gp hi hj']
    split
    · simpa only [Array.size_set!] using hgp
    · simpa only [Array.size_set!] using h.parent_lt hj'
  · intro j hj
    have hj' : j < parent.size := by simpa [Array.size_set!] using hj
    have hlabels : labels.size = parent.size := h.size_eq
    rw [Array.getElemBang_setBang parent i j gp hi hj']
    split
    · next hij =>
      subst j
      exact higp
    · exact h.edge hj'

/-- Repointing one in-bounds node to an in-bounds semantically equivalent
node preserves parent-table soundness. -/
theorem setParent {R : EqKey → EqKey → Prop}
    {labels : Array EqKey} {parent : Array Nat}
    (h : ParentSound R labels parent) {source target : Nat}
    (hsource : source < parent.size) (htarget : target < parent.size)
    (hrel : R labels[source]! labels[target]!) :
    ParentSound R labels (parent.set! source target) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Array.size_set!] using h.size_eq
  · intro i hi
    have hi' : i < parent.size := by
      simpa only [Array.size_set!] using hi
    rw [Array.getElemBang_setBang parent source i target hsource hi']
    split
    · simpa only [Array.size_set!] using htarget
    · simpa only [Array.size_set!] using h.parent_lt hi'
  · intro i hi
    have hi' : i < parent.size := by
      simpa only [Array.size_set!] using hi
    rw [Array.getElemBang_setBang parent source i target hsource hi']
    split
    · next heq =>
      subst i
      exact hrel
    · exact h.edge hi'

/-- The bounded path-halving loop preserves all parent-edge meanings and
relates its input node to the node it returns, even on fuel exhaustion. -/
theorem findGo
    {R : EqKey → EqKey → Prop} (hR : Equivalence R)
    (labels : Array EqKey) (fuel : Nat) (parent : Array Nat) (node : Nat)
    (h : ParentSound R labels parent) (hnode : node < parent.size) :
    let result := EquivManager.find.go parent node fuel
    ParentSound R labels result.2 ∧
      result.1 < result.2.size ∧
      R labels[node]! labels[result.1]! := by
  induction fuel generalizing parent node with
  | zero =>
      simp only [EquivManager.find_go_zero]
      exact ⟨h, hnode, hR.refl _⟩
  | succ fuel ih =>
      rw [EquivManager.find_go_succ]
      split
      · let p := parent[node]!
        let gp := parent[p]!
        let parent' := parent.set! node gp
        have hp : p < parent.size := h.parent_lt hnode
        have hgp : gp < parent.size := h.parent_lt hp
        have hparent' : ParentSound R labels parent' := h.halve hR hnode
        have hsize : parent'.size = parent.size := by
          simp [parent', Array.size_set!]
        have hgp' : gp < parent'.size := by simpa [hsize]
        have hread : parent'[node]! = gp := by
          rw [Array.getElemBang_setBang parent node node gp hnode hnode]
          simp
        have hnext : parent'[node]! < parent'.size := by simpa [hread]
        have hstep : R labels[node]! labels[parent'[node]!]! := by
          exact hparent'.edge (by simpa [hsize] using hnode)
        have hrec := ih parent' parent'[node]! hparent' hnext
        rcases out : EquivManager.find.go parent' parent'[node]! fuel with
          ⟨root, finalParent⟩
        rw [out] at hrec
        exact ⟨hrec.1, hrec.2.1, hR.trans hstep hrec.2.2⟩
      · exact ⟨h, hnode, hR.refl _⟩

end ParentSound

@[simp] theorem find_keyToNode (em : EquivManager) (node : Nat) :
    (em.find node).2.keyToNode = em.keyToNode := by
  rw [EquivManager.find_equation]

@[simp] theorem find_nodeToKey (em : EquivManager) (node : Nat) :
    (em.find node).2.nodeToKey = em.nodeToKey := by
  rw [EquivManager.find_equation]

@[simp] theorem find_rank (em : EquivManager) (node : Nat) :
    (em.find node).2.rank = em.rank := by
  rw [EquivManager.find_equation]

/-- Allocating a key never changes an existing node label. -/
theorem nodeForKey_oldLabel (em : EquivManager) (key : EqKey)
    {i : Nat} (hi : i < em.nodeToKey.size) :
    (em.nodeForKey key).2.nodeToKey[i]! = em.nodeToKey[i]! := by
  unfold EquivManager.nodeForKey
  split
  · rfl
  · rw [Array.getElemBang_push em.nodeToKey key i
      (by simpa using Nat.lt_succ_of_lt hi)]
    simp only [hi, ↓reduceDIte]

/-- Allocating a key preserves the bounds of every existing parent node. -/
theorem nodeForKey_oldBound (em : EquivManager) (key : EqKey)
    {i : Nat} (hi : i < em.parent.size) :
    i < (em.nodeForKey key).2.parent.size := by
  unfold EquivManager.nodeForKey
  split
  · exact hi
  · simp only [Array.size_push]
    exact Nat.lt_succ_of_lt hi

/-- Complete representation invariant for the concrete manager.  Hash-map
lookups resolve to in-bounds nodes carrying the queried key; the parent table
is semantically sound with respect to those immutable labels. -/
structure WF (R : EqKey → EqKey → Prop) (em : EquivManager) : Prop where
  parents : ParentSound R em.nodeToKey em.parent
  keyToNode : ∀ {key node}, em.keyToNode[key]? = some node →
    node < em.parent.size ∧ em.nodeToKey[node]! = key

namespace WF

/-- The empty manager represents every equivalence relation. -/
theorem empty {R : EqKey → EqKey → Prop} : WF R EquivManager.empty := by
  refine ⟨?_, ?_⟩
  · refine ⟨rfl, ?_, ?_⟩ <;>
      simp [EquivManager.empty]
  · simp [EquivManager.empty]

/-- Resetting the manager restores the empty invariant. -/
theorem clear {R : EqKey → EqKey → Prop} (em : EquivManager) :
    WF R em.clear := by
  simpa [EquivManager.clear] using (empty (R := R))

/-- Pointwise strengthening of the semantic relation preserves manager
validity. -/
theorem mono {R S : EqKey → EqKey → Prop} {em : EquivManager}
    (hRS : ∀ {a b}, R a b → S a b) (h : WF R em) : WF S em :=
  ⟨h.parents.mono hRS, h.keyToNode⟩

/-- One justified parent-link update preserves the complete manager
representation. -/
theorem setParent {R : EqKey → EqKey → Prop} {em : EquivManager}
    (h : WF R em) {source target : Nat}
    (hsource : source < em.parent.size) (htarget : target < em.parent.size)
    (hrel : R em.nodeToKey[source]! em.nodeToKey[target]!) :
    WF R {em with parent := em.parent.set! source target} := by
  refine ⟨h.parents.setParent hsource htarget hrel, ?_⟩
  intro key node hlookup
  have hold := h.keyToNode hlookup
  exact ⟨by simpa only [Array.size_set!] using hold.1, hold.2⟩

/-- `find` performs only sound path-halving writes.  Its returned node is in
bounds and semantically related to the requested node. -/
theorem find {R : EqKey → EqKey → Prop} (hR : Equivalence R)
    {em : EquivManager} (h : WF R em) {node : Nat}
    (hnode : node < em.parent.size) :
    let result := em.find node
    WF R result.2 ∧ result.1 < result.2.parent.size ∧
      R em.nodeToKey[node]! result.2.nodeToKey[result.1]! := by
  rw [EquivManager.find_equation]
  have hgo := ParentSound.findGo hR em.nodeToKey em.parent.size em.parent
    node h.parents hnode
  rcases out : EquivManager.find.go em.parent node em.parent.size with
    ⟨root, parent⟩
  rw [out] at hgo
  have hparentSize : parent.size = em.parent.size := by
    rw [← hgo.1.size_eq, ← h.parents.size_eq]
  have hkeyToNode : ∀ {key node}, em.keyToNode[key]? = some node →
      node < parent.size ∧ em.nodeToKey[node]! = key := by
    intro key node hlookup
    have hold := h.keyToNode hlookup
    exact ⟨by simpa [hparentSize] using hold.1, hold.2⟩
  exact ⟨⟨hgo.1, hkeyToNode⟩, hgo.2.1, hgo.2.2⟩

/-- Looking up an existing key leaves the manager unchanged; allocating a
new key appends one reflexive root and records its exact reverse label. -/
theorem nodeForKey {R : EqKey → EqKey → Prop} (hR : Equivalence R)
    {em : EquivManager} (h : WF R em) (key : EqKey) :
    let result := em.nodeForKey key
    WF R result.2 ∧ result.1 < result.2.parent.size ∧
      result.2.nodeToKey[result.1]! = key := by
  unfold EquivManager.nodeForKey
  split
  · next node hlookup =>
    have hnode := h.keyToNode hlookup
    exact ⟨h, hnode.1, hnode.2⟩
  · next hmissing =>
    let node := em.parent.size
    let em' : EquivManager := {
      em with
      parent := em.parent.push node
      rank := em.rank.push 0
      nodeToKey := em.nodeToKey.push key
      keyToNode := em.keyToNode.insert key node }
    have hlabelSize : em.nodeToKey.size = em.parent.size :=
      h.parents.size_eq
    have hparents : ParentSound R em'.nodeToKey em'.parent := by
      refine ⟨?_, ?_, ?_⟩
      · simp [em', hlabelSize]
      · intro i hi
        simp only [em', Array.size_push] at hi ⊢
        rw [Array.getElemBang_push em.parent node i (by simpa using hi)]
        split
        · exact Nat.lt_succ_of_lt (h.parents.parent_lt ‹_›)
        · simpa [node] using hi
      · intro i hi
        simp only [em', Array.size_push] at hi
        change R (em.nodeToKey.push key)[i]!
          (em.nodeToKey.push key)[(em.parent.push node)[i]!]!
        have hparentRead := Array.getElemBang_push em.parent node i
          (by simpa using hi)
        rw [hparentRead]
        split
        · next hiOld =>
          have hlabelsRead := Array.getElemBang_push em.nodeToKey key i
            (by simpa [hlabelSize] using hi)
          rw [hlabelsRead]
          simp only [show i < em.nodeToKey.size by
            simpa [hlabelSize] using hiOld, ↓reduceDIte]
          have hp := h.parents.parent_lt hiOld
          have hpLabel : em.parent[i]! < em.nodeToKey.size := by
            simpa [hlabelSize] using hp
          have hparentLabel := Array.getElemBang_push em.nodeToKey key
            em.parent[i]! (by
              simpa using Nat.lt_succ_of_lt hpLabel)
          rw [hparentLabel]
          simp only [hpLabel, ↓reduceDIte]
          exact h.parents.edge hiOld
        · next hiOld =>
          have hieq : i = node := by
            simp only [node] at hiOld ⊢
            omega
          subst i
          simp [em', node, hlabelSize, hR.refl]
    refine ⟨⟨hparents, ?_⟩, ?_, ?_⟩
    · intro other otherNode hlookup
      rw [Std.HashMap.getElem?_insert] at hlookup
      split at hlookup
      · next heq =>
        have hkey : key = other := eq_of_beq heq
        subst other
        cases hlookup
        constructor
        · simp [em', node]
        · have hlast := Array.getElemBang_push em.nodeToKey key
            em.parent.size (by simp [hlabelSize])
          have hnot : ¬em.parent.size < em.nodeToKey.size := by
            omega
          simp only [hnot, ↓reduceDIte] at hlast
          exact hlast
      · next hne =>
        have hold := h.keyToNode hlookup
        have holdLabel : otherNode < em.nodeToKey.size := by
          simpa [hlabelSize] using hold.1
        constructor
        · simpa [em'] using Nat.lt_succ_of_lt hold.1
        · rw [Array.getElemBang_push em.nodeToKey key otherNode]
          · simp only [holdLabel, ↓reduceDIte]
            exact hold.2
          · simpa [em', hlabelSize] using Nat.lt_succ_of_lt hold.1
    · simp only [Array.size_push]
      omega
    · have hlast := Array.getElemBang_push em.nodeToKey key
        em.parent.size (by simp [hlabelSize])
      have hnot : ¬em.parent.size < em.nodeToKey.size := by
        omega
      simp only [hnot, ↓reduceDIte] at hlast
      simpa only using hlast

/-- Union by rank preserves validity once the two requested nodes are known
semantically equivalent. -/
theorem union {R : EqKey → EqKey → Prop} (hR : Equivalence R)
    {em : EquivManager} (h : WF R em) {a b : Nat}
    (ha : a < em.parent.size) (hb : b < em.parent.size)
    (hab : R em.nodeToKey[a]! em.nodeToKey[b]!) :
    WF R (em.union a b).2 := by
  unfold EquivManager.union
  have hfindA := h.find hR ha
  rcases hfa : em.find a with ⟨ra, em1⟩
  rw [hfa] at hfindA
  have hlabels1 : em1.nodeToKey = em.nodeToKey := by
    have hframe := EquivManager.find_nodeToKey em a
    rw [hfa] at hframe
    exact hframe
  have hb1 : b < em1.parent.size := by
    rw [← hfindA.1.parents.size_eq, hlabels1, h.parents.size_eq]
    exact hb
  have hfindB := hfindA.1.find hR hb1
  rcases hfb : em1.find b with ⟨rb, em2⟩
  rw [hfb] at hfindB
  have hlabels2 : em2.nodeToKey = em1.nodeToKey := by
    have hframe := EquivManager.find_nodeToKey em1 b
    rw [hfb] at hframe
    exact hframe
  have hra : R em.nodeToKey[a]! em.nodeToKey[ra]! := by
    simpa [hlabels1] using hfindA.2.2
  have hrb : R em.nodeToKey[b]! em.nodeToKey[rb]! := by
    simpa [hlabels1, hlabels2] using hfindB.2.2
  have hroots : R em2.nodeToKey[ra]! em2.nodeToKey[rb]! := by
    rw [hlabels2, hlabels1]
    exact hR.trans (hR.symm hra) (hR.trans hab hrb)
  simp only [hfa, hfb]
  split
  · simpa using hfindB.1
  · simp only [Id.run, pure_bind]
    have hraBound : ra < em2.parent.size := by
      rw [← hfindB.1.parents.size_eq, hlabels2,
        hfindA.1.parents.size_eq]
      exact hfindA.2.1
    have hrbBound : rb < em2.parent.size := hfindB.2.1
    split
    · exact hfindB.1.setParent hraBound hrbBound hroots
    · split
      · exact hfindB.1.setParent hrbBound hraBound (hR.symm hroots)
      · have hlinked := hfindB.1.setParent hrbBound hraBound
          (hR.symm hroots)
        exact ⟨hlinked.parents, hlinked.keyToNode⟩

/-- A positive equivalence query is justified by the selected relation, and
path halving preserves the manager invariant on either Boolean result. -/
theorem isEquiv {R : EqKey → EqKey → Prop} (hR : Equivalence R)
    {em : EquivManager} (h : WF R em) (k1 k2 : EqKey) :
    let result := em.isEquiv k1 k2
    WF R result.2 ∧ (result.1 = true → R k1 k2) := by
  unfold EquivManager.isEquiv
  split
  · next hsame =>
    refine ⟨h, fun _ => ?_⟩
    have heq : k1 = k2 := eq_of_beq hsame
    subst k2
    exact hR.refl _
  · next hne =>
    cases hmap1 : em.keyToNode[k1]? with
    | none => simp [hmap1, h]
    | some n1 =>
      cases hmap2 : em.keyToNode[k2]? with
      | none => simp [hmap1, hmap2, h]
      | some n2 =>
        simp only [hmap1, hmap2]
        have hn1 := h.keyToNode hmap1
        have hn2 := h.keyToNode hmap2
        have hfind1 := h.find hR hn1.1
        rcases hf1 : em.find n1 with ⟨r1, em1⟩
        rw [hf1] at hfind1
        have hlabels1 : em1.nodeToKey = em.nodeToKey := by
          have hframe := EquivManager.find_nodeToKey em n1
          rw [hf1] at hframe
          exact hframe
        have hn2' : n2 < em1.parent.size := by
          rw [← hfind1.1.parents.size_eq, hlabels1,
            h.parents.size_eq]
          exact hn2.1
        have hfind2 := hfind1.1.find hR hn2'
        rcases hf2 : em1.find n2 with ⟨r2, em2⟩
        rw [hf2] at hfind2
        simp only [hf1, hf2]
        refine ⟨hfind2.1, fun hroots => ?_⟩
        have hr : r1 = r2 := eq_of_beq hroots
        have hk1 : R k1 em.nodeToKey[r1]! := by
          rw [← hn1.2]
          simpa [hlabels1] using hfind1.2.2
        have hlabels2 : em2.nodeToKey = em1.nodeToKey := by
          have hframe := EquivManager.find_nodeToKey em1 n2
          rw [hf2] at hframe
          exact hframe
        have hk2 : R k2 em.nodeToKey[r2]! := by
          rw [← hn2.2]
          simpa [hlabels1, hlabels2] using hfind2.2.2
        subst r2
        exact hR.trans hk1 (hR.symm hk2)

/-- A returned representative is related to the queried key. -/
theorem findRootKey {R : EqKey → EqKey → Prop} (hR : Equivalence R)
    {em : EquivManager} (h : WF R em) (key : EqKey) :
    let result := em.findRootKey key
    WF R result.2 ∧
      ∀ rootKey, result.1 = some rootKey → R key rootKey := by
  unfold EquivManager.findRootKey
  cases hmap : em.keyToNode[key]? with
  | none => simp [h]
  | some node =>
    simp only
    have hnode := h.keyToNode hmap
    have hfind := h.find hR hnode.1
    rcases hf : em.find node with ⟨root, em1⟩
    rw [hf] at hfind
    simp only [hf]
    refine ⟨hfind.1, ?_⟩
    intro rootKey hroot
    have hrootBound : root < em1.nodeToKey.size := by
      rw [hfind.1.parents.size_eq]
      exact hfind.2.1
    have hrootLabel : em1.nodeToKey[root]! = rootKey := by
      simpa [getElem!_def, hrootBound] using hroot
    have hrel : R key em1.nodeToKey[root]! := by
      rw [← hnode.2]
      exact hfind.2.2
    simpa [hrootLabel] using hrel

/-- Two sequential representative lookups preserve validity and relate each
optional representative to its own queried key.  This is the exact pure
operation used by DefEq's root-cache second chance. -/
theorem findRootKeys {R : EqKey → EqKey → Prop} (hR : Equivalence R)
    {em : EquivManager} (h : WF R em) (left right : EqKey) :
    let result :=
      let (leftRoot, em) := em.findRootKey left
      let (rightRoot, em) := em.findRootKey right
      ((leftRoot, rightRoot), em)
    WF R result.2 ∧
      (∀ root, result.1.1 = some root → R left root) ∧
      (∀ root, result.1.2 = some root → R right root) := by
  have hleft := h.findRootKey hR left
  rcases hleftRun : em.findRootKey left with ⟨leftRoot, em1⟩
  rw [hleftRun] at hleft
  have hright := hleft.1.findRootKey hR right
  rcases hrightRun : em1.findRootKey right with ⟨rightRoot, em2⟩
  rw [hrightRun] at hright
  simp only [hleftRun, hrightRun]
  exact ⟨hright.1, hleft.2, hright.2⟩

/-- Recording one already-justified equivalence preserves manager validity. -/
theorem addEquiv {R : EqKey → EqKey → Prop} (hR : Equivalence R)
    {em : EquivManager} (h : WF R em) {k1 k2 : EqKey}
    (hk : R k1 k2) : WF R (em.addEquiv k1 k2) := by
  unfold EquivManager.addEquiv
  have hnode1 := h.nodeForKey hR k1
  rcases hn1 : em.nodeForKey k1 with ⟨n1, em1⟩
  rw [hn1] at hnode1
  have hnode2 := hnode1.1.nodeForKey hR k2
  rcases hn2 : em1.nodeForKey k2 with ⟨n2, em2⟩
  rw [hn2] at hnode2
  have hn1LabelBound : n1 < em1.nodeToKey.size := by
    rw [hnode1.1.parents.size_eq]
    exact hnode1.2.1
  have hn1Label : em2.nodeToKey[n1]! = k1 := by
    have hframe := EquivManager.nodeForKey_oldLabel em1 k2 hn1LabelBound
    rw [hn2] at hframe
    exact hframe.trans hnode1.2.2
  have hnodes : R em2.nodeToKey[n1]! em2.nodeToKey[n2]! := by
    rw [hn1Label, hnode2.2.2]
    exact hk
  have hn1Bound2 : n1 < em2.parent.size := by
    have hframe := EquivManager.nodeForKey_oldBound em1 k2 hnode1.2.1
    rw [hn2] at hframe
    exact hframe
  simpa only [hn1, hn2] using
    hnode2.1.union hR hn1Bound2 hnode2.2.1 hnodes

end WF

end EquivManager

end Ix.Tc
