import Ix.CompileCert.ReaderIndex

/-! # The reader's recursor index files every recursor, at one recursor per motive

The reader's recursor index (`Ix.Kernel.Reader.buildIndex`) files a recursor member of its
records under its own reference when its analysis names a block whose inductives its carriers
order, at a motive of that block not yet taken (`candidate`). A second recursor of a block's
motive is not filed, and its record then declines. This module states the converse the
consistency statement needs:

* `Accepted store records ref block motive`: `ref` is a recursor member of a scanned record whose
  analysis passes every guard of `candidate` except the per-motive one, at `block`'s `motive`;
* `OnePerMotive store records`: two references accepted at the same block and motive are the same
  reference;
* `buildIndex_files`: over records that agree with the store (`Coherent`), when there is one
  recursor per block and motive, the index files every accepted reference at its block and motive.
  The records' order does not matter.
-/

namespace Ix.CompileCert.ReaderIndex

open Ix.Kernel.Reader (Store RecIndex RecEntry BlockShape recursorMembers analyseRecursor buildIndex)
open Ix.Kernel (ConstRef)
open Ix.CompileCert.CanonUnivMeaning (StepHolds)

/-! ## The statement -/

/-- **A recursor member the index accepts at a block and motive**: a member of a scanned record
whose analysis names the block by its first carrier, at the motive, and whose carriers order the
block's inductives (every guard of `candidate` but the per-motive one). -/
def Accepted (store : Store) (records : Array (Address × Ixon.Constant)) (ref : ConstRef Address)
    (block : Address) (motive : Nat) : Prop :=
  ∃ owner constant position recursor carriers major firstIndex blockConstant members firstSlot first,
    ref = .member owner position ∧ (owner, constant) ∈ records ∧
    (position, recursor) ∈ recursorMembers constant ∧
    analyseRecursor store owner constant recursor = some (motive, carriers, major) ∧
    carriers[0]? = some (.member block firstIndex) ∧
    store block = some blockConstant ∧ blockConstant.info = .muts members ∧
    (inductives members)[0]? = some (firstSlot, first) ∧
    orderValid firstIndex (inductives members) (orderFor carriers block (inductives members).size) = true

/-- **One recursor per block and motive** among the scanned records: two references the index
accepts at the same block and motive are the same reference. -/
def OnePerMotive (store : Store) (records : Array (Address × Ixon.Constant)) : Prop :=
  ∀ (ref ref' : ConstRef Address) (block : Address) (motive : Nat),
    Accepted store records ref block motive → Accepted store records ref' block motive → ref = ref'

/-- `ref` is filed under `block`'s `motive`. -/
def FiledAt (index : RecIndex) (ref : ConstRef Address) (block : Address) (motive : Nat) : Prop :=
  ∃ entry : RecEntry, index.recs[ref]? = some entry ∧ entry.block = block ∧ entry.motive = motive

/-! ## The accepted references -/

theorem accepted_of_from {store : Store} {records : Array (Address × Ixon.Constant)}
    {ref : ConstRef Address} {entry : RecEntry} (h : From store records ref entry) :
    Accepted store records ref entry.block entry.motive := by
  obtain ⟨owner, constant, position, recursor, carriers, firstIndex, blockConstant, members, firstSlot,
    first, hr, hp, hm, ha, hc, hs, hk, hf, hg, -⟩ := h
  exact ⟨owner, constant, position, recursor, carriers, entry.major, firstIndex, blockConstant, members,
    firstSlot, first, hr, hp, hm, ha, hc, hs, hk, hf, hg⟩

/-- **A reference is accepted at one block and motive**, over records that agree with the store:
the reference names the record and the member, whose analysis is a function of them. -/
theorem accepted_determined {store : Store} {records : Array (Address × Ixon.Constant)}
    (coherent : Coherent store records) {ref : ConstRef Address} {block block' : Address}
    {motive motive' : Nat} (h : Accepted store records ref block motive)
    (h' : Accepted store records ref block' motive') : block = block' ∧ motive = motive' := by
  obtain ⟨o, c, j, r, cs, mj, fi, _, _, _, _, hr, hp, hm, ha, hc, -⟩ := h
  obtain ⟨o', c', j', r', cs', mj', fi', _, _, _, _, hr', hp', hm', ha', hc', -⟩ := h'
  rw [hr] at hr'
  injection hr' with ho hj
  subst ho
  subst hj
  have hcc : c = c' := Option.some.inj ((coherent o c hp).symm.trans (coherent o c' hp'))
  subst hcc
  have hrr : r = r' := member_unique c j r r' hm hm'
  subst hrr
  rw [ha] at ha'
  simp only [Option.some.injEq, Prod.mk.injEq] at ha'
  obtain ⟨rfl, rfl, -⟩ := ha'
  rw [hc] at hc'
  simp only [Option.some.injEq, ConstRef.member.injEq] at hc'
  exact ⟨hc'.1, rfl⟩

/-- **A reference filed earlier is filed at its accepted block and motive.** -/
theorem filed_of_contains {store : Store} {records : Array (Address × Ixon.Constant)}
    (coherent : Coherent store records) {state : BuildState} (valid : Origins store records state)
    {ref : ConstRef Address} {block : Address} {motive : Nat}
    (accepted : Accepted store records ref block motive)
    (contained : state.1.recs.contains ref = true) : FiledAt state.1 ref block motive := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at contained
  obtain ⟨entry, found⟩ := contained
  obtain ⟨hb, hm⟩ := accepted_determined coherent (accepted_of_from (valid.1 ref entry found)) accepted
  exact ⟨entry, found, hb, hm⟩

/-- **A fresh accepted reference finds its motive free**: a filed pair at the block and motive is
an accepted reference there (`FoundMatches`, `Provenance`), so it is the fresh one, which is not
filed. -/
theorem unused_of_unique {store : Store} {records : Array (Address × Ixon.Constant)}
    (unique : OnePerMotive store records) {state : BuildState} (valid : Origins store records state)
    {ref : ConstRef Address} {block : Address} {motive : Nat}
    (accepted : Accepted store records ref block motive)
    (fresh : state.1.recs.contains ref = false) :
    ((state.2.getD block #[]).any (·.1 == motive)) = false := by
  cases hany : (state.2.getD block #[]).any (·.1 == motive) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨pair, present, hit⟩ := Array.any_eq_true'.mp hany
    obtain ⟨entry, stored, hb, hm⟩ := found_getD state valid.2.1 block pair present
    have hacc : Accepted store records pair.2 block motive := by
      have := accepted_of_from (valid.1 pair.2 entry stored)
      rw [hb, hm, beq_iff_eq.mp hit] at this
      exact this
    have same : pair.2 = ref := unique pair.2 ref block motive hacc accepted
    rw [same] at stored
    rw [Std.HashMap.contains_eq_isSome_getElem?, stored] at fresh
    cases fresh

/-! ## One candidate step -/

/-- A candidate step whose reference is filed keeps the state. -/
theorem candidate_contained (store : Store) (owner : Address) (constant : Ixon.Constant)
    (member : Nat × Ixon.Recursor) (before : BuildState)
    (contained : before.1.recs.contains (.member owner member.1) = true) :
    candidate store owner constant member before = .yield before := by
  rcases member with ⟨position, recursor⟩
  rcases before with ⟨idx, found⟩
  unfold candidate
  dsimp only at contained ⊢
  simp only [contained, ↓reduceIte]
  try rfl

/-- A candidate step whose reference is fresh, whose guards pass and whose motive is free files
the reference (`added`). -/
theorem candidate_added (store : Store) (owner : Address) (constant : Ixon.Constant)
    (member : Nat × Ixon.Recursor) (before : BuildState) {motive : Nat}
    {carriers : Array (ConstRef Address)} {major : ConstRef Address} {block : Address}
    {firstIndex : Nat} {blockRecord : Ixon.Constant} {members : Array Ixon.MutConst} {slot : Nat}
    {first : Ixon.Inductive}
    (hFresh : before.1.recs.contains (.member owner member.1) = false)
    (hAn : analyseRecursor store owner constant member.2 = some (motive, carriers, major))
    (hCar : carriers[0]? = some (.member block firstIndex))
    (hSt : store block = some blockRecord) (hKind : blockRecord.info = .muts members)
    (hFirst : (inductives members)[0]? = some (slot, first))
    (hGuard : orderValid firstIndex (inductives members)
      (orderFor carriers block (inductives members).size) = true)
    (hUnused : ((before.2.getD block #[]).any (·.1 == motive)) = false) :
    candidate store owner constant member before =
      .yield (added owner member before motive major block
        (orderFor carriers block (inductives members).size) first) := by
  rcases member with ⟨position, recursor⟩
  rcases before with ⟨idx, found⟩
  dsimp only at hFresh hAn hUnused
  unfold candidate
  dsimp only
  split
  · simp_all
  · split
    · split
      · split
        · split
          · split
            · split
              · split
                · simp_all
                · rename_i _ _ motive' carriers' major' analysed _ block' firstIndex' carrier _ blockRecord'
                    stored _ members' kind _ slot' first' firstFound _ _
                  rw [hAn] at analysed
                  simp only [Option.some.injEq, Prod.mk.injEq] at analysed
                  obtain ⟨rfl, rfl, rfl⟩ := analysed
                  rw [hCar] at carrier
                  simp only [Option.some.injEq, ConstRef.member.injEq] at carrier
                  obtain ⟨rfl, rfl⟩ := carrier
                  rw [hSt] at stored
                  obtain rfl := Option.some.inj stored
                  rw [hKind] at kind
                  obtain rfl := Ixon.ConstantInfo.muts.inj kind
                  rw [hFirst] at firstFound
                  simp only [Option.some.injEq, Prod.mk.injEq] at firstFound
                  obtain ⟨rfl, rfl⟩ := firstFound
                  unfold added
                  dsimp only
                  by_cases contained : idx.blocks.contains block = true <;>
                    simp only [contained, ↓reduceIte] <;> rfl
              · simp_all
            · simp_all
          · simp_all
        · simp_all
      · simp_all
    · simp_all

/-- A candidate step only adds filed references. -/
theorem candidate_extends (store : Store) (owner : Address) (constant : Ixon.Constant)
    (member : Nat × Ixon.Recursor) (before : BuildState) :
    StepHolds (fun after : BuildState => RecsExtend before.1 after.1)
      (candidate store owner constant member before) := by
  obtain ⟨after, ran, step⟩ := candidate_step store owner constant member before
  rw [ran]
  cases step with
  | keep =>
    show RecsExtend before.1 before.1
    intro _ _ h
    exact h
  | add motive carriers major block firstIndex blockRecord members slot first fresh =>
    have growth := recs_insert_extends before.1 (.member owner member.1)
      ⟨block, motive, major, member.2.lvls.toNat == first.lvls.toNat + 1⟩ fresh
    show RecsExtend before.1 (added owner member before motive major block _ first).1
    unfold added
    dsimp only
    split <;> exact growth

theorem recsExtend_trans {a b c : RecIndex} (h₁ : RecsExtend a b) (h₂ : RecsExtend b c) :
    RecsExtend a c :=
  fun ref entry found => h₂ ref entry (h₁ ref entry found)

theorem filedAt_extends {a b : RecIndex} (growth : RecsExtend a b) {ref : ConstRef Address}
    {block : Address} {motive : Nat} (h : FiledAt a ref block motive) : FiledAt b ref block motive := by
  obtain ⟨entry, found, hb, hm⟩ := h
  exact ⟨entry, growth ref entry found, hb, hm⟩

/-- **The candidate step files its member** wherever the member is accepted, given one recursor
per block and motive. -/
theorem candidate_files (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (unique : OnePerMotive store records) (owner : Address)
    (constant : Ixon.Constant) (present : (owner, constant) ∈ records) (member : Nat × Ixon.Recursor)
    (memberPresent : member ∈ recursorMembers constant) (before : BuildState)
    (valid : Origins store records before) :
    ∃ next, candidate store owner constant member before = .yield next ∧
      Origins store records next ∧
      ∀ block motive, Accepted store records (.member owner member.1) block motive →
        FiledAt next.1 (.member owner member.1) block motive := by
  have origins := candidate_origins store records owner constant present member memberPresent before valid
  by_cases contained : before.1.recs.contains (.member owner member.1) = true
  · have ran := candidate_contained store owner constant member before contained
    rw [ran] at origins
    exact ⟨before, ran, origins, fun block motive accepted =>
      filed_of_contains coherent valid accepted contained⟩
  · have fresh : before.1.recs.contains (.member owner member.1) = false := by simpa using contained
    obtain ⟨after, ran, -⟩ := candidate_step store owner constant member before
    rw [ran] at origins
    refine ⟨after, ran, origins, fun block motive accepted => ?_⟩
    -- the accepted member is this one: the record agrees with the store, the member is
    -- found by position
    obtain ⟨o, c, j, r, cs, mj, fi, bc, ms, fs, f, hr, hp, hm, ha, hc, hs, hk, hf, hg⟩ := accepted
    injection hr with ho hj
    subst ho
    subst hj
    have hcc : constant = c :=
      Option.some.inj ((coherent owner constant present).symm.trans (coherent owner c hp))
    subst hcc
    have hrr : member.2 = r := member_unique constant member.1 member.2 r memberPresent hm
    subst hrr
    have hUnused := unused_of_unique unique valid
      ⟨owner, constant, member.1, member.2, cs, mj, fi, bc, ms, fs, f, rfl, hp, hm, ha, hc, hs, hk,
        hf, hg⟩ fresh
    have added_eq := candidate_added store owner constant member before fresh ha hc hs hk hf hg hUnused
    rw [ran] at added_eq
    obtain rfl := ForInStep.yield.inj added_eq
    refine ⟨⟨block, motive, mj, member.2.lvls.toNat == f.lvls.toNat + 1⟩, ?_, rfl, rfl⟩
    unfold added
    dsimp only
    split <;> simp

/-! ## The loops -/

/-- **A loop whose every step yields establishes a fact at each item** that the later steps
keep, under an invariant the steps keep. -/
theorem listLoop_establishes {α β : Type} (P : β → Prop) (Q : α → β → Prop) (items : List α)
    (initial : β) (body : α → β → Id (ForInStep β)) (start : P initial)
    (step : ∀ item ∈ items, ∀ state, P state →
      ∃ next, body item state = .yield next ∧ P next ∧ Q item next)
    (keep : ∀ item ∈ items, ∀ other ∈ items, ∀ state next, P state → Q other state →
      body item state = .yield next → Q other next) :
    ∀ item ∈ items, Q item (forIn items initial body : Id β) := by
  induction items generalizing initial with
  | nil => intro item h; cases h
  | cons x rest ih =>
    obtain ⟨next, ran, good, established⟩ := step x List.mem_cons_self initial start
    have unfolded : (forIn (x :: rest) initial body : Id β) = (forIn rest next body : Id β) := by
      rw [List.forIn_cons, ran]
      rfl
    intro item present
    rw [unfolded]
    rcases List.mem_cons.mp present with same | later
    · rw [same]
      have kept := CanonUnivMeaning.listLoop_preserves (fun state => P state ∧ Q x state) rest next
        body ⟨good, established⟩ (fun y hy state held => by
          obtain ⟨n', r', g', -⟩ := step y (List.mem_cons_of_mem _ hy) state held.1
          rw [r']
          exact And.intro g' (keep y (List.mem_cons_of_mem _ hy) x List.mem_cons_self state n'
            held.1 held.2 r'))
      exact kept.2
    · exact ih next good (fun y hy => step y (List.mem_cons_of_mem _ hy))
        (fun y hy o ho => keep y (List.mem_cons_of_mem _ hy) o (List.mem_cons_of_mem _ ho)) item later

theorem arrayLoop_establishes {α β : Type} (P : β → Prop) (Q : α → β → Prop) (items : Array α)
    (initial : β) (body : α → β → Id (ForInStep β)) (start : P initial)
    (step : ∀ item ∈ items, ∀ state, P state →
      ∃ next, body item state = .yield next ∧ P next ∧ Q item next)
    (keep : ∀ item ∈ items, ∀ other ∈ items, ∀ state next, P state → Q other state →
      body item state = .yield next → Q other next) :
    ∀ item ∈ items, Q item (forIn items initial body : Id β) := by
  intro item present
  rw [← Array.forIn_toList]
  exact listLoop_establishes P Q items.toList initial body start
    (fun y hy => step y (Array.mem_toList_iff.mp hy))
    (fun y hy o ho => keep y (Array.mem_toList_iff.mp hy) o (Array.mem_toList_iff.mp ho))
    item (Array.mem_toList_iff.mpr present)

/-- One record's step yields, keeps the builder's invariants and only adds filed references. -/
theorem recordStep_yields (store : Store) (records : Array (Address × Ixon.Constant))
    (record : Address × Ixon.Constant) (present : record ∈ records) (before : BuildState)
    (valid : Origins store records before) :
    ∃ next, recordStep store record before = .yield next ∧ Origins store records next ∧
      RecsExtend before.1 next.1 := by
  refine ⟨_, rfl, ?_, ?_⟩
  · have := record_origins store records record present before valid
    exact this
  · have := CanonUnivEmit.arrayLoop_preserves
      (fun state : BuildState => Origins store records state ∧ RecsExtend before.1 state.1)
      (recursorMembers record.2) before (candidate store record.1 record.2)
      (And.intro valid (fun _ _ h => h))
      (fun member memberPresent state held => by
        obtain ⟨after, ran, -⟩ := candidate_step store record.1 record.2 member state
        have origins := candidate_origins store records record.1 record.2 present member
          memberPresent state held.1
        have growth := candidate_extends store record.1 record.2 member state
        rw [ran] at origins growth ⊢
        exact And.intro origins (recsExtend_trans held.2 growth))
    exact this.2

/-- **The collection loop files every accepted reference**, one recursor per block and motive. -/
theorem collect_files (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (unique : OnePerMotive store records) :
    ∀ record ∈ records, ∀ position recursor, (position, recursor) ∈ recursorMembers record.2 →
      ∀ block motive, Accepted store records (.member record.1 position) block motive →
        FiledAt (forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)).1
          (.member record.1 position) block motive := by
  intro record present
  refine arrayLoop_establishes (Origins store records)
    (fun record state => ∀ position recursor, (position, recursor) ∈ recursorMembers record.2 →
      ∀ block motive, Accepted store records (.member record.1 position) block motive →
        FiledAt state.1 (.member record.1 position) block motive)
    records ({}, {}) (recordStep store) (origins_empty store records) ?_ ?_ record present
  · intro x xPresent state valid
    obtain ⟨next, ran, good, -⟩ := recordStep_yields store records x xPresent state valid
    refine ⟨next, ran, good, ?_⟩
    have unfolded : next = forIn (m := Id) (recursorMembers x.2) state (candidate store x.1 x.2) := by
      unfold recordStep at ran
      exact (ForInStep.yield.inj ran).symm
    rw [unfolded]
    intro position recursor memberPresent
    exact arrayLoop_establishes (Origins store records)
      (fun member state => ∀ block motive, Accepted store records (.member x.1 member.1) block motive →
        FiledAt state.1 (.member x.1 member.1) block motive)
      (recursorMembers x.2) state (candidate store x.1 x.2) valid
      (fun member mp s v => by
        obtain ⟨n, r, g, f⟩ := candidate_files store records coherent unique x.1 x.2 xPresent member
          mp s v
        exact ⟨n, r, g, f⟩)
      (fun member mp other _ s n v held ran' => by
        intro block motive accepted
        have growth := candidate_extends store x.1 x.2 member s
        rw [ran'] at growth
        exact filedAt_extends growth (held block motive accepted))
      (position, recursor) memberPresent
  · intro x xPresent other _ state next valid held ran
    intro position recursor memberPresent block motive accepted
    obtain ⟨next', ran', -, growth⟩ := recordStep_yields store records x xPresent state valid
    rw [ran] at ran'
    obtain rfl := ForInStep.yield.inj ran'
    exact filedAt_extends growth (held position recursor memberPresent block motive accepted)

/-- **The index files every accepted reference at its block and motive**, over records that
agree with the store and hold one recursor per block and motive. The records' order does not
matter. -/
theorem buildIndex_files (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (unique : OnePerMotive store records)
    {ref : ConstRef Address} {block : Address} {motive : Nat}
    (accepted : Accepted store records ref block motive) :
    FiledAt (buildIndex store records) ref block motive := by
  rw [← run_eq]
  obtain ⟨owner, constant, position, recursor, carriers, major, firstIndex, blockConstant, members,
    firstSlot, first, hr, hp, hm, ha, hc, hs, hk, hf, hg⟩ := accepted
  have filed := collect_files store records coherent unique (owner, constant) hp position recursor
    hm block motive ⟨owner, constant, position, recursor, carriers, major, firstIndex,
      blockConstant, members, firstSlot, first, rfl, hp, hm, ha, hc, hs, hk, hf, hg⟩
  subst hr
  -- the completion phase only sorts the blocks' recursor lists
  have kept : (run store records).recs =
      (forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)).1.recs :=
    CanonUnivMeaning.listLoop_preserves
      (fun index : RecIndex => index.recs =
        (forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)).1.recs)
      (forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)).2.toList
      (forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)).1 completeStep rfl
      (fun _ _ _ same => same)
  obtain ⟨entry, found, hb, hm'⟩ := filed
  refine ⟨entry, ?_, hb, hm'⟩
  rw [kept]
  exact found

end Ix.CompileCert.ReaderIndex
