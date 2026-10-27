import Ix.CompileCert.InductiveReading

/-! # The reader on a block's recursors

An inductive block's reading reads its recursors from their own records
(`InductiveReading.readRecursors`), in the block shape's motive order: each recursor under its
key, at the recursor's level parameters (`recLps`), its type and its rules' right-hand sides
read by the recursor record's member reader (`recReader`), its rules' constructors under their
keys, its counts from its record and its motive from the recursor index. `readRecursors_ok`
states the reading, given every recursor's index entry, record, key and readings
(`RecursorFacts`). -/

namespace Ix.Cert.RecursorReads

open Ix.Kernel (Mode LevelParam ConstRef RecRule)
open Ix.Kernel.Reader
open Ix.CompileCert.InductiveReading (recursorStep readRecursors)

variable {md : Mode}

/-- The self map the reader reads a recursor record with. -/
def recSelf (cx : Ctx md) (rc : Ixon.Constant) (rOwner : Address) (key : CName md) :
    Nat → Option (ReadM (CName md)) :=
  fun i => match rc.info with
    | .muts rms => if i < rms.size then some (cx.memberKey (.member rOwner i)) else none
    | _ => if (i == 0) = true then some (pure key) else none

/-- The member reader the reader reads a recursor with. -/
def recReader (cx : Ctx md) (rc : Ixon.Constant) (rOwner : Address) (key : CName md)
    (lps : List LevelParam) : MemberReader md :=
  MemberReader.mk' cx rc (recParam lps) (recSelf cx rc rOwner key)

/-- The rules the reader reads, from their constructors' keys and right-hand sides. -/
def ruleReads (ruleKey : Nat → CName md) (rhsOf : Nat → CExpr md) (rules : List (Ixon.RecursorRule × Nat)) :
    List (RecRule md) :=
  rules.map fun x => RecRule.mk (ruleKey x.2) x.1.fields.toNat 0 .inert (rhsOf x.2) false false false

/-- One rule of a recursor, as the reader reads it. -/
def ruleStep (cx : Ctx md) (mr : MemberReader md) (mb : Address) (mi : Nat) :
    Ixon.RecursorRule × Nat → List (RecRule md) → ReadM (ForInStep (List (RecRule md))) :=
  fun x rules => match x with
    | (rule, k) => do
      let ctor ← cx.memberKey (.ctor mb mi k)
      let rhs ← mr.read rule.rhs
      let rules := rules ++ [RecRule.mk ctor rule.fields.toNat 0 .inert rhs false false false]
      pure (ForInStep.yield rules)

theorem rulesLoop_ok (cx : Ctx md) (mr : MemberReader md) (mb : Address) (mi : Nat)
    (ruleKey : Nat → CName md) (rhsOf : Nat → CExpr md) :
    ∀ (l : List (Ixon.RecursorRule × Nat)) (acc : List (RecRule md)),
      (∀ x ∈ l, cx.memberKey (.ctor mb mi x.2) = .ok (ruleKey x.2) ∧ mr.read x.1.rhs = .ok (rhsOf x.2)) →
      forIn l acc (ruleStep cx mr mb mi) = .ok (acc ++ ruleReads ruleKey rhsOf l)
  | [], acc, _ => by simp [ruleReads]; rfl
  | x :: l, acc, h => by
    obtain ⟨keyed, read⟩ := h x List.mem_cons_self
    rw [List.forIn_cons]
    obtain ⟨rule, k⟩ := x
    have hstep : ruleStep cx mr mb mi (rule, k) acc =
        .ok (.yield (acc ++ [RecRule.mk (ruleKey k) rule.fields.toNat 0 .inert (rhsOf k) false false false])) := by
      simp only [ruleStep, keyed, read, bind, Except.bind, pure, Except.pure]
    rw [hstep]
    simp only [bind, Except.bind]
    rw [rulesLoop_ok cx mr mb mi ruleKey rhsOf l _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp [ruleReads]

/-- What the reader reads of one recursor. -/
def recRead (key : CName md) (lps : List LevelParam) (type : CExpr md) (r : Ixon.Recursor) (motive : Nat)
    (ruleKey : Nat → CName md) (rhsOf : Nat → CExpr md) : CVal md × RecCounts × List (RecRule md) :=
  (⟨key, lps, type⟩, ⟨r.params.toNat, r.motives.toNat, r.minors.toNat, r.indices.toNat, r.k, some motive⟩,
    ruleReads ruleKey rhsOf r.rules.toList.zipIdx)

/-- **What the reader needs of one recursor** to read it: its index entry, its record and
member, its safety, key and type reading, its major inductive with as many constructors as it
has rules, and every rule's constructor key and right-hand side reading. -/
structure RecursorFacts (cx : Ctx md) (blockLps : List LevelParam) (ref : ConstRef Address)
    (read : CVal md × RecCounts × List (RecRule md)) : Prop where
  facts : ∃ entry rOwner j rc j' r key type major mb mi ruleKey rhsOf,
    cx.index.recs[ref]? = some entry ∧ ref = .member rOwner j ∧ cx.store rOwner = some rc ∧
    (recursorMembers rc).find? (·.1 == j) = some (j', r) ∧ r.isUnsafe = false ∧
    cx.memberKey ref = .ok key ∧
    (recReader cx rc rOwner key (recLps entry.large blockLps)).read r.typ = .ok type ∧
    inductiveAt cx.store entry.major = some major ∧ major.ctors.size = r.rules.size ∧
    entry.major = .member mb mi ∧
    (∀ x ∈ r.rules.toList.zipIdx, cx.memberKey (.ctor mb mi x.2) = .ok (ruleKey x.2) ∧
      (recReader cx rc rOwner key (recLps entry.large blockLps)).read x.1.rhs = .ok (rhsOf x.2)) ∧
    read = recRead key (recLps entry.large blockLps) type r entry.motive ruleKey rhsOf

theorem recursorStep_ok (cx : Ctx md) (blockLps : List LevelParam) (ref : ConstRef Address)
    (recs : Array (CVal md × RecCounts × List (RecRule md))) {read : CVal md × RecCounts × List (RecRule md)}
    (h : RecursorFacts cx blockLps ref read) :
    recursorStep cx blockLps ref recs = .ok (.yield (recs.push read)) := by
  obtain ⟨entry, rOwner, j, rc, j', r, key, type, major, mb, mi, ruleKey, rhsOf, hentry, rfl, hstore, hfind,
    hsafe, hkey, htype, hmajor, hsize, hmb, hrules, rfl⟩ := h.facts
  unfold recursorStep
  simp only [hentry, hstore, hfind, hsafe, Bool.false_eq_true, ↓reduceIte]
  simp only [hkey, bind, Except.bind]
  split
  · rename_i err heq
    exact absurd (htype.symm.trans heq) (by simp)
  · rename_i v heq
    have hv : v = type := Except.ok.inj (heq.symm.trans htype)
    subst hv
    rw [hmb] at hmajor
    simp only [hmajor, hsize, beq_self_eq_true, ↓reduceIte, hmb]
    rw [← Array.forIn_toList, Array.toList_zipIdx]
    have hloop := rulesLoop_ok cx (recReader cx rc rOwner key (recLps entry.large blockLps)) mb mi ruleKey rhsOf
      r.rules.toList.zipIdx [] (fun x hx => hrules x hx)
    split
    · rename_i err heq2
      exact absurd (hloop.symm.trans heq2) (by simp)
    · rename_i rules heq2
      have hr : rules = [] ++ ruleReads ruleKey rhsOf r.rules.toList.zipIdx :=
        Except.ok.inj (heq2.symm.trans hloop)
      rw [hr]
      rfl

/-- **The reader reads a block's recursors**, recursor by recursor. -/
theorem readRecursors_ok (cx : Ctx md) (blockLps : List LevelParam) :
    ∀ (refs : List (ConstRef Address)) (reads : List (CVal md × RecCounts × List (RecRule md)))
      (acc : Array (CVal md × RecCounts × List (RecRule md))),
      List.Forall₂ (RecursorFacts cx blockLps) refs reads →
      forIn refs acc (recursorStep cx blockLps) = .ok (acc.toList ++ reads).toArray
  | [], [], acc, .nil => by simp; rfl
  | ref :: refs, read :: reads, acc, .cons h rest => by
    rw [List.forIn_cons, recursorStep_ok cx blockLps ref acc h]
    simp only [bind, Except.bind]
    rw [readRecursors_ok cx blockLps refs reads _ rest]
    simp

/--
info: 'Ix.Cert.RecursorReads.readRecursors_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms readRecursors_ok

end Ix.Cert.RecursorReads
