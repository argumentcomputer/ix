import Ix.Cert.Statement
import Ix.Compile.ChangedSet
import Ix.CompileCert.Canon.QSort
import Ix.CompileCert.Canon.Ref

/-! # A constant outside the changed set (Route A, H1, B9a)

`Ix.Compile.ChangedSet.ofCompile` classifies the input constants whose compiled
form is not a renaming of their source. `ChangedSet.Avoids cs sub` (no constant
of `sub` in the set) selects the unchanged-closure case inside the proof of
`Ix.Cert.CompileCorrect`; the statement itself takes no such hypothesis (the
changed records are validated instead, `Ix.Cert.KindAccepted`). This
module reads it back as per-constant facts (`Unchanged`): a constant of `sub` is

* in no changed component (`member`), and no constructor of a member of a
  changed inductive component (`ctor`);
* no image head of a changed inductive component's Lean block (`head`), and
  in no condensation block whose references hold one (`caller`, at block
  level over the compile's condensation, as the set enters callers);
* in no clique of the input's clique table (`clique`: no member of an input
  clique and no equation lemma carried with one), and in no condensation
  block whose references hold one of Lean's encoding constants of a clique
  (`cliqueCaller`);
* found identical by the compile's aux table, if it is published with an
  original-form compile (`original`: the driver's verdict on bytes,
  `Ix.AuxGen.AuxTable.identical`).

The set's names are compared by `Ix.Name`'s `==`, which compares stored name
hashes, so `Avoids` says more than structural absence: every entry's name has
a different hash. The facts here are the structural consequences. Every
changed component counts, and each changed inductive component's Lean block
gives its image heads directly, so no fact has a side condition.

`original` reads the aux table's verdict, not bytes: since CQ5.2 (b) the set's
`regenerated` cause is the table's (`identical`), so a name outside the set is
one the table finds identical. That a verdict `identical` means the published
record is the compared original form is B9d's part (with `compileReport`'s
check that identity rows agree with the published addresses).

The proofs read `ofCompile` through its stages, restated here as
`memberStage`, `headStage`, `ChangedSet.cliqueStage`, `ChangedSet.callerStage`
and `regenStage`, and identified with it definitionally (`ofCompile_eq`). -/

namespace Ix.Cert.Unchanged

open Ix (Name ConstantInfo)
open Ix.Compile.ChangedSet

/-! ## Loops in `Id` that only grow their state -/

/-- A loop in `Id` whose every step continues to a state related to its input
by a preorder `R` ends related to its start. -/
theorem forIn_grow {α σ : Type} (R : σ → σ → Prop) (refl : ∀ s, R s s)
    (trans : ∀ {a b c : σ}, R a b → R b c → R a c) (f : α → σ → Id (ForInStep σ)) :
    ∀ (l : List α), (∀ x ∈ l, ∀ s, ∃ s', f x s = .yield s' ∧ R s s') →
      ∀ s, R s (forIn (m := Id) l s f) := by
  intro l
  induction l with
  | nil => intro _ s; exact refl s
  | cons x l ih =>
    intro step s
    obtain ⟨s', hs', r⟩ := step x List.mem_cons_self s
    rw [List.forIn_cons, hs']
    exact trans r (ih (fun y hy => step y (List.mem_cons_of_mem _ hy)) s')

/-- Such a loop ends in `P` when some element's step lands in `P` and the
preorder keeps `P`. -/
theorem forIn_hit {α σ : Type} (R : σ → σ → Prop) (refl : ∀ s, R s s)
    (trans : ∀ {a b c : σ}, R a b → R b c → R a c) (f : α → σ → Id (ForInStep σ))
    (P : σ → Prop) (keep : ∀ {s s' : σ}, R s s' → P s → P s') {x : α}
    (lands : ∀ s s', f x s = .yield s' → P s') :
    ∀ (l : List α), (∀ y ∈ l, ∀ s, ∃ s', f y s = .yield s' ∧ R s s') → x ∈ l →
      ∀ s, P (forIn (m := Id) l s f) := by
  intro l
  induction l with
  | nil => intro _ hx; cases hx
  | cons y l ih =>
    intro step hx s
    obtain ⟨s', hs', r⟩ := step y List.mem_cons_self s
    have rest : ∀ z ∈ l, ∀ s, ∃ s', f z s = .yield s' ∧ R s s' :=
      fun z hz => step z (List.mem_cons_of_mem _ hz)
    rw [List.forIn_cons, hs']
    rcases List.mem_cons.mp hx with rfl | hx
    · exact keep (forIn_grow R refl trans f l rest s') (lands s s' hs')
    · exact ih rest hx s'

/-! ## `ofCompile`, loop by loop -/

/-- `ofCompile`'s first loop: the members of the changed components, with the
constructors of an inductive component's members. -/
def memberStage (env : Ix.Environment) (blocks : Array Block) : Array Entry := Id.run do
  let mut entries : Array Entry := #[]
  for b in blocks do
    for cls in b.classes do
      for m in cls do
        entries := entries.push { name := m, cause := .member, ref := b.first }
        if b.kind == .inductiveBlock then
          if let some (.inductInfo v) := env.get? m then
            for c in v.ctors do
              entries := entries.push { name := c, cause := .member, ref := b.first }
  return entries

/-- `ofCompile`'s second loop: the image heads of each changed inductive
component's Lean block. -/
def headStage (env : Ix.Environment) (blocks : Array Block) (entries : Array Entry) :
    Array Entry × Std.HashSet Name := Id.run do
  let mut entries := entries
  let mut heads : Std.HashSet Name := {}
  for b in blocks do
    if b.kind == .inductiveBlock then
      for h in Ix.Compile.Pass.imageKinds env.get? b.all do
        heads := heads.insert h
        entries := entries.push { name := h, cause := .imageHead, ref := b.first }
  return (entries, heads)

/-- `ofCompile`'s last loop: the regenerated auxiliaries, over the published
names. -/
def regenStage (env : Ix.Environment) (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env)
    (entries : Array Entry) : Array Entry := Id.run do
  let mut entries := entries
  for (n, named) in ixe.named do
    if named.original.isSome && (env.get? n).isSome && !table.identical n then
      entries := entries.push { name := n, cause := .regenerated }
  return entries

/-- The stages' entries, in order: members, image heads, the clique stage, the
callers of the heads, the regenerated auxiliaries. -/
abbrev stages (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (table : Ix.AuxGen.AuxTable)
    (ixe : Ixon.Env) : Array Entry :=
  regenStage env table ixe
    (callerStage condensed (headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe))).2
      (cliqueStage env condensed
        (headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe))).1))

/-- **`ofCompile` is its stages**, then the sort and the name set. -/
theorem ofCompile_eq (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (table : Ix.AuxGen.AuxTable)
    (ixe : Ixon.Env) :
    ofCompile env condensed table ixe =
      { blocks := changedBlocks env ixe
        entries := sortEntries (stages env condensed table ixe)
        names := (sortEntries (stages env condensed table ixe)).foldl (fun s e => s.insert e.name) ∅ } :=
  rfl

/-! ## Array forms -/

theorem forIn_grow_array {α σ : Type} (R : σ → σ → Prop) (refl : ∀ s, R s s)
    (trans : ∀ {a b c : σ}, R a b → R b c → R a c) (f : α → σ → Id (ForInStep σ)) (xs : Array α)
    (step : ∀ x ∈ xs, ∀ s, ∃ s', f x s = .yield s' ∧ R s s') (s : σ) :
    R s (forIn (m := Id) xs s f) := by
  rw [← Array.forIn_toList]
  exact forIn_grow R refl trans f xs.toList (fun x hx => step x (Array.mem_toList_iff.mp hx)) s

theorem forIn_hit_array {α σ : Type} (R : σ → σ → Prop) (refl : ∀ s, R s s)
    (trans : ∀ {a b c : σ}, R a b → R b c → R a c) (f : α → σ → Id (ForInStep σ)) (xs : Array α)
    (step : ∀ x ∈ xs, ∀ s, ∃ s', f x s = .yield s' ∧ R s s')
    (P : σ → Prop) (keep : ∀ {s s' : σ}, R s s' → P s → P s') {x : α} (hx : x ∈ xs)
    (lands : ∀ s s', f x s = .yield s' → P s') (s : σ) : P (forIn (m := Id) xs s f) := by
  rw [← Array.forIn_toList]
  exact forIn_hit R refl trans f P keep lands xs.toList (fun y hy => step y (Array.mem_toList_iff.mp hy))
    (Array.mem_toList_iff.mpr hx) s

/-- Entries only grow. -/
def Grows (a b : Array Entry) : Prop := ∀ e ∈ a, e ∈ b

theorem Grows.refl (a : Array Entry) : Grows a a := fun _ h => h
theorem Grows.trans {a b c : Array Entry} (h₁ : Grows a b) (h₂ : Grows b c) : Grows a c :=
  fun e h => h₂ e (h₁ e h)
theorem Grows.push (a : Array Entry) (e : Entry) : Grows a (a.push e) :=
  fun _ h => Array.mem_push_of_mem _ h

/-! ## The loops' bodies, named -/

/-- The constructor loop: a member's constructors as member entries. -/
def ctorLoop (first : Option Name) (ctors : Array Name) (entries : Array Entry) : Array Entry :=
  forIn (m := Id) ctors entries fun c r => .yield (r.push { name := c, cause := .member, ref := first })

/-- One member of a class: its entry, then its constructors' for an inductive
component. -/
def memberBody (env : Ix.Environment) (b : Block) :
    Name → Array Entry → Id (ForInStep (Array Entry)) := fun m r =>
  let r := r.push { name := m, cause := .member, ref := b.first }
  if (b.kind == .inductiveBlock) = true then
    match env.get? m with
    | some (.inductInfo v) => .yield (ctorLoop b.first v.ctors r)
    | _ => .yield r
  else .yield r

/-- One class of a component. -/
def classBody (env : Ix.Environment) (b : Block) :
    Array Name → Array Entry → Id (ForInStep (Array Entry)) := fun cls r =>
  .yield (forIn (m := Id) cls r (memberBody env b))

/-- One changed component. -/
def blockBody (env : Ix.Environment) : Block → Array Entry → Id (ForInStep (Array Entry)) := fun b r =>
  .yield (forIn (m := Id) b.classes r (classBody env b))

theorem memberStage_eq (env : Ix.Environment) (blocks : Array Block) :
    memberStage env blocks = forIn (m := Id) blocks #[] (blockBody env) := rfl

/-- One image head. -/
def headStep (ref : Option Name) :
    Name → Array Entry × Std.HashSet Name → Id (ForInStep (Array Entry × Std.HashSet Name)) :=
  fun h s => .yield (s.1.push { name := h, cause := .imageHead, ref := ref }, s.2.insert h)

/-- One changed component's image heads. -/
def headBody (env : Ix.Environment) :
    Block → Array Entry × Std.HashSet Name → Id (ForInStep (Array Entry × Std.HashSet Name)) :=
  fun b s =>
    if (b.kind == .inductiveBlock) = true then
      .yield (forIn (m := Id) (Ix.Compile.Pass.imageKinds env.get? b.all) s (headStep b.first))
    else .yield s

theorem headStage_eq (env : Ix.Environment) (blocks : Array Block) (entries : Array Entry) :
    headStage env blocks entries = forIn (m := Id) blocks (entries, ∅) (headBody env) := rfl

/-- One name of the clique table: its `clique` entry. -/
def cliqueNameBody : Name × (Array Name × Array Name) → Array Entry → Id (ForInStep (Array Entry)) :=
  fun x r =>
    match x with
    | (n, cl) => .yield (r.push { name := n, cause := .clique, ref := cl.1[0]? })

/-- One member of a block that references a clique's encoding: its `caller`
entry. -/
def encMemberBody (all : Array Name) : Name → Array Entry → Id (ForInStep (Array Entry)) := fun m r =>
  .yield (r.push { name := m, cause := .caller, ref := all[0]? })

/-- One reference of a block: its members' `caller` entries when it is one of
Lean's encoding constants of a clique. -/
def encRefBody (roots : Std.HashMap Name (Array Name)) (mems : Ix.Set Name) :
    Name → Array Entry → Id (ForInStep (Array Entry)) := fun r s =>
  match Ix.Compile.Pass.Clique.encodingOwner? roots r with
  | some all => .yield (forIn (m := Id) mems s (encMemberBody all))
  | _ => .yield s

/-- One condensation block: its references, each through `encRefBody`. -/
def encBlockBody (condensed : Ix.CondensedBlocks) (roots : Std.HashMap Name (Array Name)) :
    Name × Ix.Set Name → Array Entry → Id (ForInStep (Array Entry)) := fun x s =>
  match x with
  | (lo, mems) => .yield (forIn (m := Id) (condensed.blockRefs.getD lo {}) s (encRefBody roots mems))

theorem cliqueStage_eq (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (entries : Array Entry) :
    cliqueStage env condensed entries =
      forIn (m := Id) condensed.blocks (forIn (m := Id) (cliqueTables env condensed).1 entries cliqueNameBody)
        (encBlockBody condensed (cliqueTables env condensed).2) := by
  -- the tables abstracted, so the check never evaluates them
  unfold cliqueStage
  generalize cliqueTables env condensed = t
  rfl

/-- One member of a block whose references hold a head: its `caller` entry,
unless it is a head. -/
def callerMemberBody (heads : Std.HashSet Name) (h : Name) :
    Name → Array Entry → Id (ForInStep (Array Entry)) := fun m r =>
  if (!heads.contains m) = true then .yield (r.push { name := m, cause := .caller, ref := some h })
  else .yield r

/-- One condensation block: its members' `caller` entries when its references
hold a head. -/
def callerBlockBody (condensed : Ix.CondensedBlocks) (heads : Std.HashSet Name) :
    Name × Ix.Set Name → Array Entry → Id (ForInStep (Array Entry)) := fun x r =>
  match x with
  | (rep, mems) =>
    match leastName (condensed.blockRefs.getD rep {}) heads.contains with
    | some h => .yield (forIn (m := Id) mems r (callerMemberBody heads h))
    | _ => .yield r

theorem callerStage_eq (condensed : Ix.CondensedBlocks) (heads : Std.HashSet Name) (entries : Array Entry) :
    callerStage condensed heads entries =
      if heads.isEmpty = true then entries
      else forIn (m := Id) condensed.blocks entries (callerBlockBody condensed heads) := rfl

/-- One published name: its `regenerated` entry, when it has an original
form, is an input name, and the table does not find it identical. -/
def regenBody (env : Ix.Environment) (table : Ix.AuxGen.AuxTable) :
    Name × Ixon.Named → Array Entry → Id (ForInStep (Array Entry)) := fun x r =>
  match x with
  | (n, named) =>
    if (named.original.isSome && (env.get? n).isSome && !table.identical n) = true then
      .yield (r.push { name := n, cause := .regenerated })
    else .yield r

theorem regenStage_eq (env : Ix.Environment) (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env)
    (entries : Array Entry) :
    regenStage env table ixe entries = forIn (m := Id) ixe.named entries (regenBody env table) := rfl

/-! ## The first loop: members -/

theorem kind_beq {k : ComponentKind} : (k == .inductiveBlock) = true ↔ k = .inductiveBlock := by
  cases k <;> decide

theorem ctorLoop_grows (first : Option Name) (ctors : Array Name) (entries : Array Entry) :
    Grows entries (ctorLoop first ctors entries) :=
  forIn_grow_array Grows Grows.refl Grows.trans _ ctors (fun _ _ s => ⟨_, rfl, Grows.push s _⟩) entries

theorem ctorLoop_hit (first : Option Name) {ctors : Array Name} {c : Name} (hc : c ∈ ctors)
    (entries : Array Entry) :
    ({ name := c, cause := .member, ref := first } : Entry) ∈ ctorLoop first ctors entries :=
  forIn_hit_array Grows Grows.refl Grows.trans _ ctors (fun _ _ s => ⟨_, rfl, Grows.push s _⟩)
    (fun r => ({ name := c, cause := .member, ref := first } : Entry) ∈ r) (fun g h => g _ h) hc
    (fun s s' h => by injection h with h; subst h; exact Array.mem_push_self) entries

theorem memberBody_step (env : Ix.Environment) (b : Block) (m : Name) (r : Array Entry) :
    ∃ r', memberBody env b m r = .yield r' ∧ Grows r r' := by
  unfold memberBody
  dsimp only
  split
  · split
    · exact ⟨_, rfl, (Grows.push _ _).trans (ctorLoop_grows _ _ _)⟩
    · exact ⟨_, rfl, Grows.push _ _⟩
  · exact ⟨_, rfl, Grows.push _ _⟩

/-- A member's own entry lands, and a member's step lands its constructors'
entries for an inductive component. -/
theorem memberBody_lands (env : Ix.Environment) (b : Block) (m : Name) {r r' : Array Entry}
    (h : memberBody env b m r = .yield r') :
    ({ name := m, cause := .member, ref := b.first } : Entry) ∈ r' ∧
      ((b.kind == .inductiveBlock) = true → ∀ v, env.get? m = some (.inductInfo v) →
        ∀ c ∈ v.ctors, ({ name := c, cause := .member, ref := b.first } : Entry) ∈ r') := by
  unfold memberBody at h
  dsimp only at h
  split at h
  · split at h
    · rename_i v found
      injection h with h
      subst h
      refine ⟨ctorLoop_grows _ _ _ _ Array.mem_push_self, fun _ v' found' c hc => ?_⟩
      rw [found] at found'
      cases found'
      exact ctorLoop_hit b.first hc _
    · rename_i none
      injection h with h
      subst h
      refine ⟨Array.mem_push_self, fun _ v found c _ => ?_⟩
      exact absurd found (none v)
  · rename_i notInd
    injection h with h
    subst h
    exact ⟨Array.mem_push_self, fun ind => absurd ind notInd⟩

theorem classBody_step (env : Ix.Environment) (b : Block) (cls : Array Name) (r : Array Entry) :
    ∃ r', classBody env b cls r = .yield r' ∧ Grows r r' :=
  ⟨_, rfl, forIn_grow_array Grows Grows.refl Grows.trans _ cls (fun m _ s => memberBody_step env b m s) r⟩

theorem blockBody_step (env : Ix.Environment) (b : Block) (r : Array Entry) :
    ∃ r', blockBody env b r = .yield r' ∧ Grows r r' :=
  ⟨_, rfl, forIn_grow_array Grows Grows.refl Grows.trans _ b.classes
    (fun c _ s => classBody_step env b c s) r⟩

/-- **A member's entry, and its constructors'**, are in the first loop's
entries. -/
theorem member_entry (env : Ix.Environment) {blocks : Array Block} {b : Block} (hb : b ∈ blocks)
    {cls : Array Name} (hc : cls ∈ b.classes) {m : Name} (hm : m ∈ cls) :
    ({ name := m, cause := .member, ref := b.first } : Entry) ∈ memberStage env blocks ∧
      (b.kind = .inductiveBlock → ∀ v, env.get? m = some (.inductInfo v) →
        ∀ c ∈ v.ctors, ({ name := c, cause := .member, ref := b.first } : Entry) ∈ memberStage env blocks) := by
  have hit : ∀ (P : Array Entry → Prop), (∀ {s s'}, Grows s s' → P s → P s') →
      (∀ r r', memberBody env b m r = .yield r' → P r') → P (memberStage env blocks) := by
    intro P keep lands
    rw [memberStage_eq]
    refine forIn_hit_array Grows Grows.refl Grows.trans _ blocks (fun x _ s => blockBody_step env x s) P keep
      hb (fun s s' h => ?_) _
    injection h with h
    subst h
    refine forIn_hit_array Grows Grows.refl Grows.trans _ b.classes (fun c _ s => classBody_step env b c s) P keep
      hc (fun s s' h => ?_) s
    injection h with h
    subst h
    exact forIn_hit_array Grows Grows.refl Grows.trans _ cls (fun m' _ s => memberBody_step env b m' s) P keep
      hm lands s
  refine ⟨hit (fun r => _ ∈ r) (fun g h => g _ h) (fun _ _ h => (memberBody_lands env b m h).1), ?_⟩
  intro ind v found c hc'
  exact hit (fun r => _ ∈ r) (fun g h => g _ h)
    (fun _ _ h => (memberBody_lands env b m h).2 (kind_beq.mpr ind) v found c hc')

/-! ## The second loop: image heads -/

/-- The second loop's heads: each is the name, up to hash, of an entry. -/
def HeadsInv (s : Array Entry × Std.HashSet Name) : Prop :=
  ∀ h, s.2.contains h = true → ∃ e ∈ s.1, (e.name == h) = true

/-- The second loop's growth. -/
def Grows₂ (s s' : Array Entry × Std.HashSet Name) : Prop :=
  Grows s.1 s'.1 ∧ (∀ h, s.2.contains h = true → s'.2.contains h = true) ∧ (HeadsInv s → HeadsInv s')

theorem Grows₂.refl (s : Array Entry × Std.HashSet Name) : Grows₂ s s := ⟨Grows.refl _, fun _ h => h, id⟩

theorem Grows₂.trans {a b c : Array Entry × Std.HashSet Name} (h₁ : Grows₂ a b) (h₂ : Grows₂ b c) :
    Grows₂ a c :=
  ⟨h₁.1.trans h₂.1, fun k h => h₂.2.1 k (h₁.2.1 k h), fun i => h₂.2.2 (h₁.2.2 i)⟩

theorem headStep_step (ref : Option Name) (h : Name) (s : Array Entry × Std.HashSet Name) :
    ∃ s', headStep ref h s = .yield s' ∧ Grows₂ s s' := by
  refine ⟨_, rfl, Grows.push _ _, fun x hx => ?_, fun inv x hx => ?_⟩
  · rw [Std.HashSet.contains_insert, hx, Bool.or_true]
  · rw [Std.HashSet.contains_insert] at hx
    cases same : (h == x) with
    | true => exact ⟨_, Array.mem_push_self, same⟩
    | false =>
      rw [same, Bool.false_or] at hx
      obtain ⟨e, he, beq⟩ := inv x hx
      exact ⟨e, Array.mem_push_of_mem _ he, beq⟩

theorem headBody_step (env : Ix.Environment) (b : Block) (s : Array Entry × Std.HashSet Name) :
    ∃ s', headBody env b s = .yield s' ∧ Grows₂ s s' := by
  unfold headBody
  split
  · exact ⟨_, rfl, forIn_grow_array Grows₂ Grows₂.refl Grows₂.trans _ _
      (fun h _ s => headStep_step b.first h s) s⟩
  · exact ⟨_, rfl, Grows₂.refl s⟩

theorem headStage_grows (env : Ix.Environment) (blocks : Array Block) (entries : Array Entry) :
    Grows₂ (entries, ∅) (headStage env blocks entries) := by
  rw [headStage_eq]
  exact forIn_grow_array Grows₂ Grows₂.refl Grows₂.trans _ _ (fun b _ s => headBody_step env b s) _

/-- **The second loop's heads are entries' names**, up to hash. -/
theorem heads_inv (env : Ix.Environment) (blocks : Array Block) (entries : Array Entry) :
    HeadsInv (headStage env blocks entries) :=
  (headStage_grows env blocks entries).2.2 fun h hh => by
    rw [Std.HashSet.contains_empty] at hh; cases hh

/-- **Every image head of a changed inductive component's Lean block** is an
entry and a head of the second loop. -/
theorem head_entry (env : Ix.Environment) {blocks : Array Block} {b : Block} (hb : b ∈ blocks)
    (ind : b.kind = .inductiveBlock) (entries : Array Entry) {h : Name}
    (hh : h ∈ Ix.Compile.Pass.imageKinds env.get? b.all) :
    ({ name := h, cause := .imageHead, ref := b.first } : Entry) ∈ (headStage env blocks entries).1 ∧
      (headStage env blocks entries).2.contains h = true := by
  rw [headStage_eq]
  refine forIn_hit_array Grows₂ Grows₂.refl Grows₂.trans _ blocks (fun b' _ s => headBody_step env b' s)
    (fun s => ({ name := h, cause := .imageHead, ref := b.first } : Entry) ∈ s.1 ∧ s.2.contains h = true)
    (fun g p => ⟨g.1 _ p.1, g.2.1 _ p.2⟩) hb (fun s s' step => ?_) _
  unfold headBody at step
  split at step
  · injection step with step
    subst step
    refine forIn_hit_array Grows₂ Grows₂.refl Grows₂.trans _ _ (fun h' _ s => headStep_step b.first h' s)
      (fun s => ({ name := h, cause := .imageHead, ref := b.first } : Entry) ∈ s.1 ∧ s.2.contains h = true)
      (fun g p => ⟨g.1 _ p.1, g.2.1 _ p.2⟩) hh (fun s s' step => ?_) s
    injection step with step
    subst step
    refine ⟨Array.mem_push_self, ?_⟩
    rw [Std.HashSet.contains_insert, BEq.rfl, Bool.true_or]
  · rename_i no
    exact absurd (kind_beq.mpr ind) no

/-! ## The clique stage: clique-table names and the callers of an encoding -/

theorem cliqueNameBody_step (x : Name × (Array Name × Array Name)) (r : Array Entry) :
    ∃ r', cliqueNameBody x r = .yield r' ∧ Grows r r' := by
  obtain ⟨n, cl⟩ := x
  exact ⟨_, rfl, Grows.push _ _⟩

theorem encMembers_grows (all : Array Name) (mems : Ix.Set Name) (s : Array Entry) :
    Grows s (forIn (m := Id) mems s (encMemberBody all)) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  exact forIn_grow Grows Grows.refl Grows.trans _ _ (fun _ _ s => ⟨_, rfl, Grows.push s _⟩) s

theorem encRefBody_step (roots : Std.HashMap Name (Array Name)) (mems : Ix.Set Name) (r : Name)
    (s : Array Entry) : ∃ s', encRefBody roots mems r s = .yield s' ∧ Grows s s' := by
  unfold encRefBody
  split
  · exact ⟨_, rfl, encMembers_grows _ mems s⟩
  · exact ⟨_, rfl, Grows.refl _⟩

theorem encRefs_grows (roots : Std.HashMap Name (Array Name)) (mems refs : Ix.Set Name) (s : Array Entry) :
    Grows s (forIn (m := Id) refs s (encRefBody roots mems)) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  exact forIn_grow Grows Grows.refl Grows.trans _ _ (fun r _ s => encRefBody_step roots mems r s) s

theorem encBlockBody_step (condensed : Ix.CondensedBlocks) (roots : Std.HashMap Name (Array Name))
    (x : Name × Ix.Set Name) (s : Array Entry) : ∃ s', encBlockBody condensed roots x s = .yield s' ∧ Grows s s' := by
  obtain ⟨lo, mems⟩ := x
  exact ⟨_, rfl, encRefs_grows roots mems _ s⟩

theorem cliqueNames_grows (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (entries : Array Entry) :
    Grows entries (forIn (m := Id) (cliqueTables env condensed).1 entries cliqueNameBody) := by
  rw [Std.HashMap.forIn_eq_forIn_toList]
  exact forIn_grow Grows Grows.refl Grows.trans _ _ (fun x _ r => cliqueNameBody_step x r) _

theorem encBlocks_grows (condensed : Ix.CondensedBlocks) (roots : Std.HashMap Name (Array Name))
    (s : Array Entry) : Grows s (forIn (m := Id) condensed.blocks s (encBlockBody condensed roots)) := by
  rw [Std.HashMap.forIn_eq_forIn_toList]
  exact forIn_grow Grows Grows.refl Grows.trans _ _ (fun x _ r => encBlockBody_step condensed roots x r) _

theorem cliqueStage_grows (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (entries : Array Entry) :
    Grows entries (cliqueStage env condensed entries) := by
  rw [cliqueStage_eq]
  exact (cliqueNames_grows env condensed entries).trans (encBlocks_grows condensed _ _)

/-- **A name of the clique table has its `clique` entry.** -/
theorem clique_entry (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (entries : Array Entry)
    {n : Name} {cl : Array Name × Array Name} (hn : (n, cl) ∈ (cliqueTables env condensed).1.toList) :
    ({ name := n, cause := .clique, ref := cl.1[0]? } : Entry) ∈ cliqueStage env condensed entries := by
  rw [cliqueStage_eq]
  refine encBlocks_grows condensed _ _ _ ?_
  rw [Std.HashMap.forIn_eq_forIn_toList]
  refine forIn_hit Grows Grows.refl Grows.trans _ (fun r => _ ∈ r) (fun g p => g _ p) (fun r r' step => ?_) _
    (fun x _ r => cliqueNameBody_step x r) hn _
  injection step with step
  subst step
  exact Array.mem_push_self

/-- **A member of a condensation block whose references hold one of Lean's
encoding constants of a clique has its `caller` entry.** -/
theorem encCaller_entry (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (entries : Array Entry)
    {lo : Name} {mems : Ix.Set Name} (hb : (lo, mems) ∈ condensed.blocks.toList) {r : Name}
    (hr : r ∈ (condensed.blockRefs.getD lo {}).toList) {all : Array Name}
    (henc : Ix.Compile.Pass.Clique.encodingOwner? (cliqueTables env condensed).2 r = some all)
    {m : Name} (hm : m ∈ mems.toList) :
    ({ name := m, cause := .caller, ref := all[0]? } : Entry) ∈ cliqueStage env condensed entries := by
  rw [cliqueStage_eq, Std.HashMap.forIn_eq_forIn_toList (m := condensed.blocks)]
  refine forIn_hit Grows Grows.refl Grows.trans _ (fun r => _ ∈ r) (fun g p => g _ p) (fun s s' step => ?_) _
    (fun x _ r => encBlockBody_step condensed _ x r) hb _
  injection step with step
  subst step
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine forIn_hit Grows Grows.refl Grows.trans _ (fun r => _ ∈ r) (fun g p => g _ p) (fun t t' step => ?_) _
    (fun x _ t => encRefBody_step _ mems x t) hr _
  unfold encRefBody at step
  rw [henc] at step
  injection step with step
  subst step
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine forIn_hit Grows Grows.refl Grows.trans _ (fun r => _ ∈ r) (fun g p => g _ p) (fun u u' step => ?_) _
    (fun _ _ u => ⟨_, rfl, Grows.push u _⟩) hm _
  injection step with step
  subst step
  exact Array.mem_push_self

/-! ## The callers of the heads, by block -/

theorem callerMemberBody_step (heads : Std.HashSet Name) (h m : Name) (r : Array Entry) :
    ∃ r', callerMemberBody heads h m r = .yield r' ∧ Grows r r' := by
  unfold callerMemberBody
  split
  · exact ⟨_, rfl, Grows.push _ _⟩
  · exact ⟨_, rfl, Grows.refl _⟩

theorem callerBlockBody_step (condensed : Ix.CondensedBlocks) (heads : Std.HashSet Name)
    (x : Name × Ix.Set Name) (r : Array Entry) : ∃ r', callerBlockBody condensed heads x r = .yield r' ∧ Grows r r' := by
  obtain ⟨rep, mems⟩ := x
  unfold callerBlockBody
  dsimp only
  split
  · refine ⟨_, rfl, ?_⟩
    rw [Std.HashSet.forIn_eq_forIn_toList]
    exact forIn_grow Grows Grows.refl Grows.trans _ _ (fun m _ s => callerMemberBody_step heads _ m s) r
  · exact ⟨_, rfl, Grows.refl _⟩

theorem callerStage_grows (condensed : Ix.CondensedBlocks) (heads : Std.HashSet Name) (entries : Array Entry) :
    Grows entries (callerStage condensed heads entries) := by
  rw [callerStage_eq]
  split
  · exact Grows.refl _
  · rw [Std.HashMap.forIn_eq_forIn_toList]
    exact forIn_grow Grows Grows.refl Grows.trans _ _ (fun x _ r => callerBlockBody_step condensed heads x r) _

/-- **A member of a condensation block whose references hold a head has its
`caller` entry**, unless it is a head. -/
theorem headCaller_entry (condensed : Ix.CondensedBlocks) {heads : Std.HashSet Name} (entries : Array Entry)
    (nonempty : heads.isEmpty = false) {rep : Name} {mems : Ix.Set Name}
    (hb : (rep, mems) ∈ condensed.blocks.toList) {h : Name}
    (least : leastName (condensed.blockRefs.getD rep {}) heads.contains = some h) {m : Name}
    (hm : m ∈ mems.toList) (notHead : heads.contains m = false) :
    ({ name := m, cause := .caller, ref := some h } : Entry) ∈ callerStage condensed heads entries := by
  rw [callerStage_eq, nonempty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Std.HashMap.forIn_eq_forIn_toList]
  refine forIn_hit Grows Grows.refl Grows.trans _ (fun r => _ ∈ r) (fun g p => g _ p) (fun s s' step => ?_) _
    (fun x _ r => callerBlockBody_step condensed heads x r) hb _
  unfold callerBlockBody at step
  dsimp only at step
  rw [least] at step
  injection step with step
  subst step
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine forIn_hit Grows Grows.refl Grows.trans _ (fun r => _ ∈ r) (fun g p => g _ p) (fun t t' step => ?_) _
    (fun x _ t => callerMemberBody_step heads h x t) hm _
  unfold callerMemberBody at step
  rw [notHead] at step
  injection step with step
  subst step
  exact Array.mem_push_self

/-! ## The last loop: regenerated auxiliaries -/

theorem regenBody_step (env : Ix.Environment) (table : Ix.AuxGen.AuxTable) (x : Name × Ixon.Named)
    (r : Array Entry) : ∃ r', regenBody env table x r = .yield r' ∧ Grows r r' := by
  obtain ⟨n, named⟩ := x
  unfold regenBody
  dsimp only
  split
  · exact ⟨_, rfl, Grows.push _ _⟩
  · exact ⟨_, rfl, Grows.refl _⟩

theorem regenStage_grows (env : Ix.Environment) (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env)
    (entries : Array Entry) : Grows entries (regenStage env table ixe entries) := by
  rw [regenStage_eq, Std.HashMap.forIn_eq_forIn_toList]
  exact forIn_grow Grows Grows.refl Grows.trans _ _ (fun x _ r => regenBody_step env table x r) _

/-- **A published name's regenerated entry**, when it has an original-form
compile, is an input name, and the aux table does not find it identical. -/
theorem regenerated_entry (env : Ix.Environment) (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env)
    (entries : Array Entry) {n : Name} {named : Ixon.Named} (hn : (n, named) ∈ ixe.named.toList)
    (regen : (named.original.isSome && (env.get? n).isSome && !table.identical n) = true) :
    ({ name := n, cause := .regenerated } : Entry) ∈ regenStage env table ixe entries := by
  rw [regenStage_eq, Std.HashMap.forIn_eq_forIn_toList]
  refine forIn_hit Grows Grows.refl Grows.trans _ (fun r => _ ∈ r) (fun g p => g _ p) (fun r r' step => ?_) _
    (fun x _ r => regenBody_step env table x r) hn _
  unfold regenBody at step
  dsimp only at step
  simp only [regen, ↓reduceIte] at step
  injection step with step
  subst step
  exact Array.mem_push_self

/-! ## The set's names -/

/-- `sortEntries`' deduplication step. -/
def dedupStep (acc : Array Entry) (e : Entry) : Array Entry :=
  match acc.back? with
  | some p => if p.beq e then acc else acc.push e
  | none => acc.push e

theorem sortEntries_eq (es : Array Entry) :
    ∃ lt : Entry → Entry → Bool, sortEntries es = (es.qsort lt).foldl dedupStep #[] :=
  ⟨_, rfl⟩

theorem dedupStep_spec (acc : Array Entry) (x : Entry) :
    (∀ p ∈ acc, p ∈ dedupStep acc x) ∧ ∃ p ∈ dedupStep acc x, (p.name == x.name) = true := by
  unfold dedupStep
  split
  · rename_i p hp
    split
    · rename_i same
      refine ⟨fun _ h => h, p, Array.mem_of_back? hp, ?_⟩
      simp only [Entry.beq, Bool.and_eq_true] at same
      exact same.1.1
    · exact ⟨fun _ h => Array.mem_push_of_mem _ h, x, Array.mem_push_self, BEq.rfl⟩
  · exact ⟨fun _ h => Array.mem_push_of_mem _ h, x, Array.mem_push_self, BEq.rfl⟩

theorem dedup_keeps : ∀ (l : List Entry) (acc : Array Entry),
    (∀ p ∈ acc, p ∈ l.foldl dedupStep acc) ∧ ∀ x ∈ l, ∃ p ∈ l.foldl dedupStep acc, (p.name == x.name) = true := by
  intro l
  induction l with
  | nil => intro acc; exact ⟨fun _ h => h, fun _ h => by cases h⟩
  | cons y l ih =>
    intro acc
    obtain ⟨kept, here⟩ := dedupStep_spec acc y
    obtain ⟨keepsRest, rest⟩ := ih (dedupStep acc y)
    refine ⟨fun p h => keepsRest p (kept p h), fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨p, hp, same⟩ := here
      exact ⟨p, keepsRest p hp, same⟩
    · exact rest x hx

/-- **The sort keeps every entry's name**, up to hash. -/
theorem sortEntries_keeps {es : Array Entry} {e : Entry} (he : e ∈ es) :
    ∃ p ∈ sortEntries es, (p.name == e.name) = true := by
  obtain ⟨lt, eq⟩ := sortEntries_eq es
  rw [eq, ← Array.foldl_toList]
  exact (dedup_keeps _ #[]).2 e (Array.mem_toList_iff.mpr (Ix.CompileCert.Canon.mem_qsort.mpr he))

theorem names_contains {n : Name} : ∀ (l : List Entry) (S : Std.HashSet Name),
    ((∃ p ∈ l, (p.name == n) = true) ∨ S.contains n = true) →
      (l.foldl (fun s e => s.insert e.name) S).contains n = true := by
  intro l
  induction l with
  | nil =>
    intro S h
    rcases h with ⟨_, hp, _⟩ | h
    · cases hp
    · exact h
  | cons y l ih =>
    intro S h
    rw [List.foldl_cons]
    apply ih
    rcases h with ⟨p, hp, same⟩ | h
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact .inr (by rw [Std.HashSet.contains_insert, same, Bool.true_or])
      · exact .inl ⟨p, hp, same⟩
    · exact .inr (by rw [Std.HashSet.contains_insert, h, Bool.or_true])

/-- **An entry of the stages names a constant of the set**, up to hash. -/
theorem contains_of_entry (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (table : Ix.AuxGen.AuxTable)
    (ixe : Ixon.Env) {e : Entry} (he : e ∈ stages env condensed table ixe) {n : Name}
    (same : (e.name == n) = true) : (ofCompile env condensed table ixe).contains n = true := by
  unfold ChangedSet.contains
  rw [ofCompile_eq]
  dsimp only
  rw [← Array.foldl_toList]
  obtain ⟨p, hp, beq⟩ := sortEntries_keeps he
  exact names_contains _ ∅ (.inl ⟨p, Array.mem_toList_iff.mpr hp, BEq.trans beq same⟩)

/-! ## `leastName` -/

theorem leastName_none {s : Std.HashSet Name} {keep : Name → Bool} (h : leastName s keep = none) :
    ∀ x ∈ s.toList, keep x = false := by
  have step : ∀ (l : List Name) (best : Option Name),
      l.foldl (fun best n => if !keep n then best else match best with
        | some b => if Ix.nameCompare n b == .lt then some n else some b
        | none => some n) best = none → best = none ∧ ∀ x ∈ l, keep x = false := by
    intro l
    induction l with
    | nil => intro best h; exact ⟨h, fun _ hx => by cases hx⟩
    | cons y l ih =>
      intro best h
      rw [List.foldl_cons] at h
      obtain ⟨none', rest⟩ := ih _ h
      cases ky : keep y with
      | false =>
        rw [ky] at none'
        simp only [Bool.not_false, ↓reduceIte] at none'
        refine ⟨none', fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ky
        · exact rest x hx
      | true =>
        rw [ky] at none'
        cases best with
        | none => simp at none'
        | some b =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at none'
          split at none' <;> cases none'
  unfold leastName at h
  rw [Std.HashSet.fold_eq_foldl_toList] at h
  exact (step _ none h).2

/-! ## A constant outside the set -/

/-- A block of a condensation, among its entries. -/
theorem blocks_toList {condensed : Ix.CondensedBlocks} {rep : Name} {mems : Ix.Set Name}
    (h : condensed.blocks.get? rep = some mems) :
    ∃ k, (rep == k) = true ∧ (k, mems) ∈ condensed.blocks.toList := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at h
  exact h

/-- A block's references, read with a default under a `==` key. -/
theorem refs_getD {condensed : Ix.CondensedBlocks} {rep k : Name} {refs : Ix.Set Name}
    (h : condensed.blockRefs.get? rep = some refs) (same : (rep == k) = true) :
    condensed.blockRefs.getD k {} = refs := by
  rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.getElem?_congr same, ← Std.HashMap.get?_eq_getElem?, h]
  rfl

/-- A name a set contains is, up to hash, one of its elements. -/
theorem toList_of_contains {s : Ix.Set Name} {n : Name} (h : s.contains n = true) :
    ∃ m ∈ s.toList, (m == n) = true := by
  rw [← Std.HashSet.contains_toList, List.contains_iff_exists_mem_beq] at h
  obtain ⟨m, hm, beq⟩ := h
  exact ⟨m, hm, BEq.symm beq⟩

/-- **What a constant outside the changed set is not** (B9a), for the changed
set of a compile to `ixe` with the condensation `condensed` and the aux table
`table`. -/
structure Unchanged (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (table : Ix.AuxGen.AuxTable)
    (ixe : Ixon.Env) (n : Name) : Prop where
  /-- In no class of a changed component. -/
  member : ∀ b ∈ changedBlocks env ixe, ∀ cls ∈ b.classes, n ∉ cls
  /-- No constructor of a member of a changed inductive component. -/
  ctor : ∀ b ∈ changedBlocks env ixe, b.kind = .inductiveBlock →
    ∀ cls ∈ b.classes, ∀ m ∈ cls, ∀ v, env.get? m = some (.inductInfo v) → n ∉ v.ctors
  /-- No image head of a changed inductive component's Lean block. -/
  head : ∀ b ∈ changedBlocks env ixe, b.kind = .inductiveBlock → n ∉ Ix.Compile.Pass.imageKinds env.get? b.all
  /-- A member (up to hash) of a condensation block, its block's references
  hold no such head. -/
  caller : ∀ rep mems, condensed.blocks.get? rep = some mems → mems.contains n = true →
    ∀ refs, condensed.blockRefs.get? rep = some refs → ∀ r ∈ refs.toList,
      ∀ b ∈ changedBlocks env ixe, b.kind = .inductiveBlock → r ∉ Ix.Compile.Pass.imageKinds env.get? b.all
  /-- Not in the clique table: no member of an input clique, and no equation
  lemma carried with one. -/
  clique : (cliqueTables env condensed).1.contains n = false
  /-- A member (up to hash) of a condensation block, its block's references
  hold none of Lean's encoding constants of a clique. -/
  cliqueCaller : ∀ rep mems, condensed.blocks.get? rep = some mems → mems.contains n = true →
    ∀ refs, condensed.blockRefs.get? rep = some refs → ∀ r ∈ refs.toList,
      Ix.Compile.Pass.Clique.encodingOwner? (cliqueTables env condensed).2 r = none
  /-- Published (under a name hashing like `n`) with an original-form compile,
  the aux table finds its record identical (the driver's verdict on bytes;
  B9d reads it as bytes). -/
  original : ∀ n' named, (n', named) ∈ ixe.named.toList → (n' == n) = true →
    named.original.isSome = true → (env.get? n').isSome = true → table.identical n' = true

/-- **A name the set does not contain is `Unchanged`.** -/
theorem unchanged_of_not_contains (env : Ix.Environment) (condensed : Ix.CondensedBlocks)
    (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env) {n : Name}
    (absent : (ofCompile env condensed table ixe).contains n = false) : Unchanged env condensed table ixe n := by
  have avoid : ∀ e ∈ stages env condensed table ixe, (e.name == n) = false := fun e he => by
    cases h : (e.name == n) with
    | false => rfl
    | true => rw [contains_of_entry env condensed table ixe he h] at absent; cases absent
  obtain ⟨H, hH⟩ : ∃ H, headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe)) = H :=
    ⟨_, rfl⟩
  have avoid' : ∀ e ∈ regenStage env table ixe (callerStage condensed H.2 (cliqueStage env condensed H.1)),
      (e.name == n) = false := by
    rw [← hH]; exact avoid
  have toK : ∀ e ∈ callerStage condensed H.2 (cliqueStage env condensed H.1), (e.name == n) = false :=
    fun e he => avoid' e (regenStage_grows env table ixe _ e he)
  have toC : ∀ e ∈ cliqueStage env condensed H.1, (e.name == n) = false :=
    fun e he => toK e (callerStage_grows condensed H.2 _ e he)
  have toH : ∀ e ∈ H.1, (e.name == n) = false := fun e he => toC e (cliqueStage_grows env condensed H.1 e he)
  have lifted : ∀ e ∈ memberStage env (changedBlocks env ixe), (e.name == n) = false := fun e he =>
    toH e (by rw [← hH]; exact (headStage_grows env _ _).1 e he)
  have inv : HeadsInv H := by rw [← hH]; exact heads_inv env _ _
  have notHead : ∀ m, (m == n) = true → H.2.contains m = false := fun m same => by
    cases hc : H.2.contains m with
    | false => rfl
    | true =>
      obtain ⟨e, he, beq⟩ := inv m hc
      have := toH e he
      rw [BEq.trans beq same] at this
      cases this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb cls hc hm
    have := lifted _ (member_entry env hb hc hm).1
    rw [BEq.rfl] at this
    cases this
  · intro b hb ind cls hc m hm v found hn
    have := lifted _ ((member_entry env hb hc hm).2 ind v found n hn)
    rw [BEq.rfl] at this
    cases this
  · intro b hb ind hn
    have hentry : ({ name := n, cause := .imageHead, ref := b.first } : Entry) ∈ H.1 := by
      rw [← hH]; exact (head_entry env hb ind _ hn).1
    have := toH _ hentry
    rw [BEq.rfl] at this
    cases this
  · intro rep mems hb hn refs hr r hrr b hb' ind himg
    have hhead : H.2.contains r = true := by rw [← hH]; exact (head_entry env hb' ind _ himg).2
    have nonempty : H.2.isEmpty = false :=
      Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨r, hhead⟩
    obtain ⟨k, rk, hk⟩ := blocks_toList hb
    obtain ⟨m, hm, same⟩ := toList_of_contains hn
    cases hl : leastName (condensed.blockRefs.getD k {}) H.2.contains with
    | none =>
      rw [refs_getD hr rk] at hl
      have := leastName_none hl r hrr
      rw [hhead] at this
      cases this
    | some h =>
      have := toK _ (headCaller_entry condensed _ nonempty hk hl hm (notHead m same))
      rw [same] at this
      cases this
  · cases hc : (cliqueTables env condensed).1.contains n with
    | false => rfl
    | true =>
      rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
      obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp hc
      rw [Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hcl
      obtain ⟨k, nk, hk⟩ := hcl
      have := toC _ (clique_entry env condensed H.1 hk)
      rw [BEq.symm nk] at this
      cases this
  · intro rep mems hb hn refs hr r hrr
    cases henc : Ix.Compile.Pass.Clique.encodingOwner? (cliqueTables env condensed).2 r with
    | none => rfl
    | some all =>
      obtain ⟨k, rk, hk⟩ := blocks_toList hb
      obtain ⟨m, hm, same⟩ := toList_of_contains hn
      have hrr' : r ∈ (condensed.blockRefs.getD k {}).toList := by rw [refs_getD hr rk]; exact hrr
      have := toC _ (encCaller_entry env condensed H.1 hk hrr' henc hm)
      rw [same] at this
      cases this
  · intro n' named hn' same horig hsome
    cases hi : table.identical n' with
    | true => rfl
    | false =>
      have regen : (named.original.isSome && (env.get? n').isSome && !table.identical n') = true := by
        rw [horig, hsome, hi]; rfl
      have := avoid' _ (regenerated_entry env table ixe _ hn' regen)
      rw [same] at this
      cases this

/-- **B9a: a constant of a closure that avoids the changed set is
`Unchanged`.** -/
theorem avoids_unchanged {env : Ix.Environment} {condensed : Ix.CondensedBlocks} {table : Ix.AuxGen.AuxTable}
    {ixe : Ixon.Env} {sub : Ix.Environment} (avoids : (ofCompile env condensed table ixe).Avoids sub)
    {n : Name} {ci : ConstantInfo} (found : sub.consts.get? n = some ci) : Unchanged env condensed table ixe n :=
  unchanged_of_not_contains env condensed table ixe (avoids n ci found)

end Ix.Cert.Unchanged

/-! ## Pass 3's heads are in the changed set (`checkReport`'s eleventh check)

The check reads the regenerated published input names
(`Ix.Cert.regeneratedNames`, under the compile's aux table), each of which has
a `regenerated` entry in the changed set over the input's map, whatever its
changed components (`regenerated_entry`). -/

namespace Ix.Cert

open Ix.Cert.Unchanged

theorem exact_insert_contains {s : Std.HashSet Ix.Compile.ExactKey.ExactName}
    {k n : Ix.Compile.ExactKey.ExactName} (h : (s.insert k).contains n = true) :
    k = n ∨ s.contains n = true := by
  rw [Std.HashSet.contains_insert] at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact .inl (beq_iff_eq.mp h)
  · exact .inr h

/-- A regenerated name is a published input name with an original-form record
that the aux table does not find identical. -/
theorem regeneratedNames_spec {env : Ix.Environment} {table : Ix.AuxGen.AuxTable} {ixe : Ixon.Env}
    {n : Ix.Compile.ExactKey.ExactName} (h : (regeneratedNames env table ixe).contains n = true) :
    ∃ named : Ixon.Named, ((n : Name), named) ∈ ixe.named.toList ∧
      (named.original.isSome && (env.consts.get? n).isSome && !table.identical n) = true := by
  unfold regeneratedNames at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  have key : ∀ (l : List (Name × Ixon.Named)) (s : Std.HashSet Ix.Compile.ExactKey.ExactName),
      (l.foldl (fun s p =>
        if (p.2.original.isSome && (env.consts.get? p.1).isSome && !table.identical p.1) = true then s.insert p.1
        else s) s).contains n = true →
      s.contains n = true ∨ ∃ named : Ixon.Named, ((n : Name), named) ∈ l ∧
        (named.original.isSome && (env.consts.get? n).isSome && !table.identical n) = true := by
    intro l
    induction l with
    | nil => intro s hs; exact .inl hs
    | cons p l ih =>
      intro s hs
      rw [List.foldl_cons] at hs
      rcases ih _ hs with hs | ⟨named, hmem, hd⟩
      · obtain ⟨k, named⟩ := p
        dsimp only at hs
        split at hs
        · rename_i hd
          rcases exact_insert_contains (k := k) hs with hk | hs
          · subst hk
            exact .inr ⟨named, List.mem_cons_self, hd⟩
          · exact .inl hs
        · exact .inl hs
      · exact .inr ⟨named, List.mem_cons_of_mem _ hmem, hd⟩
  rcases key _ ∅ h with h | h
  · simp at h
  · exact h

/-- A name the input's map holds is one the input holds. -/
theorem get?_isSome_of_consts {env : Ix.Environment} {n : Name} (h : (env.consts.get? n).isSome = true) :
    (env.get? n).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
  unfold Ix.Environment.get?
  rw [hci]
  rfl

/-- The input's map, as an environment, reads as the map. -/
theorem consts_get? (consts : Std.HashMap Ix.Name Ix.ConstantInfo) (x : Ix.Name) :
    ({ consts } : Ix.Environment).get? x = consts.get? x := by
  unfold Ix.Environment.get?
  split <;> simp_all

/-- What `foreignHead = none` says first: every key of `heads` is a
regenerated published input name. -/
theorem foreignHead_regenerated {env : Ix.Environment} {table : Ix.AuxGen.AuxTable}
    {heads : Std.HashMap Ix.Compile.ExactKey.ExactName Ix.Name} {ixe : Ixon.Env}
    (h : foreignHead env table heads ixe = none) :
    ∀ (n : Ix.Compile.ExactKey.ExactName) (k : Ix.Name), heads.get? n = some k →
      (regeneratedNames env table ixe).contains n = true := by
  intro n k hn
  unfold foreignHead at h
  have hne : heads.isEmpty = false := by
    rw [Std.HashMap.isEmpty_eq_false_iff_exists_contains_eq_true]
    exact ⟨n, by rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hn]; rfl⟩
  rw [hne] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rw [List.findSome?_eq_none_iff] at h
  have hmem : (n, k) ∈ heads.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hn
  have hfind := h (n, k) hmem
  dsimp only at hfind
  cases hc : (regeneratedNames env table ixe).contains n
  · simp [hc] at hfind
  · rfl

/-- What `foreignHead = none` says: every key of `heads` is in the changed
set, over the input's map, of a compile to `ixe` with the aux table `table`
and any condensation (each is a regenerated published input name,
`foreignHead_regenerated` and `regeneratedNames_spec`, with a `regenerated`
entry in the set, `Unchanged.regenerated_entry`). -/
theorem foreignHead_none {env : Ix.Environment} {table : Ix.AuxGen.AuxTable}
    {heads : Std.HashMap Ix.Compile.ExactKey.ExactName Ix.Name} {ixe : Ixon.Env}
    (h : foreignHead env table heads ixe = none) (condensed : Ix.CondensedBlocks) :
    ∀ (n : Ix.Compile.ExactKey.ExactName) (k : Ix.Name), heads.get? n = some k →
      (Ix.Compile.ChangedSet.ofCompile { consts := env.consts } condensed table ixe).contains n = true := by
  intro n k hn
  obtain ⟨named, hnamed, hd⟩ := regeneratedNames_spec (foreignHead_regenerated h n k hn)
  refine contains_of_entry _ condensed table ixe (regenerated_entry _ table ixe _ hnamed ?_) BEq.rfl
  have e : ({ consts := env.consts } : Ix.Environment).get? (n : Name) = env.consts.get? (n : Name) :=
    consts_get? _ _
  rw [e]
  exact hd

/-- The compile's aux table is the final compile environment's. -/
theorem compileTable_eq {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {cenv : Ix.CompileM.CompileEnv} (h : compileUnchecked env = .ok (ixe, failures, cenv)) :
    compileTable env = cenv.auxReport.table := by
  unfold compileTable
  rw [h]

/-- **Pass 3's heads are in the changed set**: in the driver's final
environment, which `compileUnchecked` returns, every Pass 3 head is in the
changed set of the compile, over the input's map, its condensation and its
aux table (`checkReport`'s eleventh check). -/
theorem headsChanged {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∃ cenv : Ix.CompileM.CompileEnv, compileUnchecked env = .ok (ixe, failures, cenv) ∧
      ∀ (n : Ix.Compile.ExactKey.ExactName) (k : Ix.Name), cenv.p3Heads.get? n = some k →
        (Ix.Compile.ChangedSet.ofCompile { consts := env.consts } (compileBlocks env) (compileTable env)
          ixe).contains n = true := by
  obtain ⟨cenv, hu, hc⟩ := compileReport_ok h
  rw [compileTable_eq hu]
  exact ⟨cenv, hu, foreignHead_none (checkReport_ok hc).2.2.2.2.2.2.2.2.2.2.1 _⟩

end Ix.Cert
