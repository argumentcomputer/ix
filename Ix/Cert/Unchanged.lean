import Ix.Cert.Statement
import Ix.Compile.ChangedSet
import Ix.CompileCert.Canon.QSort
import Ix.CompileCert.Canon.Ref

/-! # A constant outside the changed set (Route A, H1, B9a)

`Ix.Compile.ChangedSet.ofCompile` classifies the input constants whose compiled
form is not a renaming of their source. `ChangedSet.Avoids cs sub` (no constant
of `sub` in the set) is the hypothesis `CompileCorrect` takes under H1. This
module reads it back as per-constant facts (`Unchanged`): a constant of `sub` is

* in no changed component (`member`), and no constructor of a member of a
  changed inductive component (`ctor`);
* no image head of a changed inductive component's Lean block (`head`), and
  references none (`caller`);
* published, if it has an original-form compile, at that compile's address
  (`original`).

The set's names are compared by `Ix.Name`'s `==`, which compares stored name
hashes, so `Avoids` says more than structural absence: every entry's name has
a different hash. The facts here are the structural consequences. Every
changed component counts, and each changed inductive component's Lean block
gives its image heads directly, so no fact has a side condition.

The proofs read `ofCompile` through its three loops, restated here as
`memberStage`, `headStage` and `namedStage` and identified with it
definitionally (`ofCompile_eq`). -/

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

/-- `ofCompile`'s third loop: callers and regenerated auxiliaries, over the
published names. -/
def namedStage (env : Ix.Environment) (ixe : Ixon.Env) (s : Array Entry × Std.HashSet Name) :
    Array Entry := Id.run do
  let mut entries := s.1
  let heads := s.2
  for (n, named) in ixe.named do
    if !heads.isEmpty && !heads.contains n then
      if let some ci := env.get? n then
        if let some h := leastName (Ix.Compile.Canon.refsConst ci) heads.contains then
          entries := entries.push { name := n, cause := .caller, ref := some h }
    if let some (orig, _) := named.original then
      if orig != named.addr && (env.get? n).isSome then
        entries := entries.push { name := n, cause := .regenerated }
  return entries

/-- The three loops' entries, in order. -/
abbrev stages (env : Ix.Environment) (ixe : Ixon.Env) : Array Entry :=
  namedStage env ixe (headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe)))

/-- **`ofCompile` is its three loops**, then the sort and the name set. -/
theorem ofCompile_eq (env : Ix.Environment) (ixe : Ixon.Env) :
    ofCompile env ixe =
      { blocks := changedBlocks env ixe
        entries := sortEntries (stages env ixe)
        names := (sortEntries (stages env ixe)).foldl (fun s e => s.insert e.name) ∅ } := rfl

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

/-- A published name's regenerated entry. -/
def regenStep (env : Ix.Environment) (n : Name) (named : Ixon.Named) (r : Array Entry) :
    Id (ForInStep (Array Entry)) :=
  match named.original with
  | some (orig, _) =>
    if (orig != named.addr && (env.get? n).isSome) = true then .yield (r.push { name := n, cause := .regenerated })
    else .yield r
  | _ => .yield r

/-- One published name: its caller entry, then its regenerated entry. -/
def namedBody (env : Ix.Environment) (heads : Std.HashSet Name) :
    Name × Ixon.Named → Array Entry → Id (ForInStep (Array Entry)) := fun x r =>
  match x with
  | (n, named) =>
    if (!heads.isEmpty && !heads.contains n) = true then
      match env.get? n with
      | some ci =>
        match leastName (Ix.Compile.Canon.refsConst ci) heads.contains with
        | some h => regenStep env n named (r.push { name := n, cause := .caller, ref := some h })
        | _ => regenStep env n named r
      | _ => regenStep env n named r
    else regenStep env n named r

theorem namedStage_eq (env : Ix.Environment) (ixe : Ixon.Env) (s : Array Entry × Std.HashSet Name) :
    namedStage env ixe s = forIn (m := Id) ixe.named s.1 (namedBody env s.2) := rfl

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

/-! ## The third loop: callers and regenerated auxiliaries -/

theorem regenStep_step (env : Ix.Environment) (n : Name) (named : Ixon.Named) (r : Array Entry) :
    ∃ r', regenStep env n named r = .yield r' ∧ Grows r r' := by
  unfold regenStep
  split
  · split
    · exact ⟨_, rfl, Grows.push _ _⟩
    · exact ⟨_, rfl, Grows.refl _⟩
  · exact ⟨_, rfl, Grows.refl _⟩

theorem namedBody_step (env : Ix.Environment) (heads : Std.HashSet Name) (x : Name × Ixon.Named)
    (r : Array Entry) : ∃ r', namedBody env heads x r = .yield r' ∧ Grows r r' := by
  obtain ⟨n, named⟩ := x
  unfold namedBody
  dsimp only
  split
  · split
    · split
      · obtain ⟨r', h, g⟩ := regenStep_step env n named (r.push _)
        exact ⟨r', h, (Grows.push _ _).trans g⟩
      · exact regenStep_step env n named r
    · exact regenStep_step env n named r
  · exact regenStep_step env n named r

/-- The regenerated entry of a published name, when its step lands one. -/
theorem regenStep_lands (env : Ix.Environment) {n : Name} {named : Ixon.Named} {r r' : Array Entry}
    (h : regenStep env n named r = .yield r') {orig : Address} {cmeta : Ixon.ConstantMeta}
    (original : named.original = some (orig, cmeta)) (differs : (orig != named.addr && (env.get? n).isSome) = true) :
    ({ name := n, cause := .regenerated } : Entry) ∈ r' := by
  unfold regenStep at h
  rw [original] at h
  dsimp only at h
  split at h
  · injection h with h
    subst h
    exact Array.mem_push_self
  · rename_i no
    exact absurd differs no

theorem namedStage_grows (env : Ix.Environment) (ixe : Ixon.Env) (s : Array Entry × Std.HashSet Name) :
    Grows s.1 (namedStage env ixe s) := by
  rw [namedStage_eq, Std.HashMap.forIn_eq_forIn_toList]
  exact forIn_grow Grows Grows.refl Grows.trans _ _ (fun x _ r => namedBody_step env s.2 x r) _

/-- **A published name's caller entry**, when it references a head and is
none. -/
theorem caller_entry (env : Ix.Environment) (ixe : Ixon.Env) (s : Array Entry × Std.HashSet Name)
    {n : Name} {named : Ixon.Named} (hn : (n, named) ∈ ixe.named.toList)
    (outside : (!s.2.isEmpty && !s.2.contains n) = true) {ci : ConstantInfo} (found : env.get? n = some ci)
    {h : Name} (least : leastName (Ix.Compile.Canon.refsConst ci) s.2.contains = some h) :
    ({ name := n, cause := .caller, ref := some h } : Entry) ∈ namedStage env ixe s := by
  rw [namedStage_eq, Std.HashMap.forIn_eq_forIn_toList]
  refine forIn_hit Grows Grows.refl Grows.trans _ (fun r => _ ∈ r) (fun g p => g _ p) (fun r r' step => ?_) _
    (fun x _ r => namedBody_step env s.2 x r) hn _
  unfold namedBody at step
  dsimp only at step
  split at step
  · rw [found] at step
    dsimp only at step
    rw [least] at step
    dsimp only at step
    obtain ⟨r'', h'', g⟩ := regenStep_step env n named (r.push { name := n, cause := .caller, ref := some h })
    rw [h''] at step
    injection step with step
    subst step
    exact g _ Array.mem_push_self
  · rename_i no
    exact absurd outside no

/-- **A published name's regenerated entry**, when its original-form address
differs from its address. -/
theorem regenerated_entry (env : Ix.Environment) (ixe : Ixon.Env) (s : Array Entry × Std.HashSet Name)
    {n : Name} {named : Ixon.Named} (hn : (n, named) ∈ ixe.named.toList) {orig : Address}
    {cmeta : Ixon.ConstantMeta} (original : named.original = some (orig, cmeta))
    (differs : (orig != named.addr && (env.get? n).isSome) = true) :
    ({ name := n, cause := .regenerated } : Entry) ∈ namedStage env ixe s := by
  rw [namedStage_eq, Std.HashMap.forIn_eq_forIn_toList]
  refine forIn_hit Grows Grows.refl Grows.trans _ (fun r => _ ∈ r) (fun g p => g _ p) (fun r r' step => ?_) _
    (fun x _ r => namedBody_step env s.2 x r) hn _
  unfold namedBody at step
  dsimp only at step
  split at step
  · split at step
    · split at step
      · exact regenStep_lands env step original differs
      · exact regenStep_lands env step original differs
    · exact regenStep_lands env step original differs
  · exact regenStep_lands env step original differs


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

/-- **An entry of the third loop names a constant of the set**, up to hash. -/
theorem contains_of_entry (env : Ix.Environment) (ixe : Ixon.Env) {e : Entry}
    (he : e ∈ stages env ixe) {n : Name}
    (same : (e.name == n) = true) : (ofCompile env ixe).contains n = true := by
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

/-- **What a constant outside the changed set is not** (B9a). -/
structure Unchanged (env : Ix.Environment) (ixe : Ixon.Env) (n : Name) : Prop where
  /-- In no class of a changed component. -/
  member : ∀ b ∈ changedBlocks env ixe, ∀ cls ∈ b.classes, n ∉ cls
  /-- No constructor of a member of a changed inductive component. -/
  ctor : ∀ b ∈ changedBlocks env ixe, b.kind = .inductiveBlock →
    ∀ cls ∈ b.classes, ∀ m ∈ cls, ∀ v, env.get? m = some (.inductInfo v) → n ∉ v.ctors
  /-- No image head of a changed inductive component's Lean block. -/
  head : ∀ b ∈ changedBlocks env ixe, b.kind = .inductiveBlock → n ∉ Ix.Compile.Pass.imageKinds env.get? b.all
  /-- Published (under a name hashing like `n`), it references no such head. -/
  caller : ∀ n' named ci, (n', named) ∈ ixe.named.toList → (n' == n) = true →
    env.get? n' = some ci → ∀ r, (Ix.Compile.Canon.refsConst ci).contains r = true →
      ∀ b ∈ changedBlocks env ixe, b.kind = .inductiveBlock → r ∉ Ix.Compile.Pass.imageKinds env.get? b.all
  /-- Published with an original-form compile, it is published at that
  compile's address. -/
  original : ∀ n' named orig cmeta, (n', named) ∈ ixe.named.toList → (n' == n) = true →
    named.original = some (orig, cmeta) → (env.get? n').isSome = true → orig = named.addr

/-- **A name the set does not contain is `Unchanged`.** -/
theorem unchanged_of_not_contains (env : Ix.Environment) (ixe : Ixon.Env) {n : Name}
    (absent : (ofCompile env ixe).contains n = false) : Unchanged env ixe n := by
  have avoid : ∀ e ∈ stages env ixe, (e.name == n) = false := fun e he => by
    cases h : (e.name == n) with
    | false => rfl
    | true => rw [contains_of_entry env ixe he h] at absent; cases absent
  have g₂₃ := namedStage_grows env ixe
    (headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe)))
  have g₁₂ := (headStage_grows env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe))).1
  have lifted : ∀ e ∈ memberStage env (changedBlocks env ixe), (e.name == n) = false :=
    fun e he => avoid e (g₂₃ e (g₁₂ e he))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb cls hc hm
    have := lifted _ (member_entry env hb hc hm).1
    rw [BEq.rfl] at this
    cases this
  · intro b hb ind cls hc m hm v found hn
    have := lifted _ ((member_entry env hb hc hm).2 ind v found n hn)
    rw [BEq.rfl] at this
    cases this
  · intro b hb ind hn
    have := avoid _ (g₂₃ _ (head_entry env hb ind _ hn).1)
    rw [BEq.rfl] at this
    cases this
  · intro n' named ci hn' same found r hr b hb ind himg
    have hhead := (head_entry env hb ind (memberStage env (changedBlocks env ixe)) himg).2
    have nonempty : (headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe))).2.isEmpty =
        false := Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨r, hhead⟩
    have notHead :
        (headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe))).2.contains n' = false := by
      cases hc : (headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe))).2.contains n' with
      | false => rfl
      | true =>
        obtain ⟨e, he, beq⟩ := heads_inv env _ _ n' hc
        have := avoid e (g₂₃ e he)
        rw [BEq.trans beq same] at this
        cases this
    cases hl : leastName (Ix.Compile.Canon.refsConst ci)
        (headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe))).2.contains with
    | none =>
      rw [← Std.HashSet.contains_toList, List.contains_iff_exists_mem_beq] at hr
      obtain ⟨x, hx, beq⟩ := hr
      have := leastName_none hl x hx
      rw [← Std.HashSet.contains_congr beq, hhead] at this
      cases this
    | some h =>
      have outside :
          (!(headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe))).2.isEmpty &&
            !(headStage env (changedBlocks env ixe) (memberStage env (changedBlocks env ixe))).2.contains n') =
              true := by
        rw [nonempty, notHead]; rfl
      have := avoid _ (caller_entry env ixe _ hn' outside found hl)
      rw [same] at this
      cases this
  · intro n' named orig cmeta hn' same horig hsome
    cases hb : (orig == named.addr) with
    | true => exact Address.beq_iff_eq.mp hb
    | false =>
      have differs : (orig != named.addr && (env.get? n').isSome) = true := by
        simp only [bne, hb, hsome, Bool.not_false, Bool.and_self]
      have := avoid _ (regenerated_entry env ixe _ hn' horig differs)
      rw [same] at this
      cases this

/-- **B9a: a constant of a closure that avoids the changed set is
`Unchanged`.** -/
theorem avoids_unchanged {env : Ix.Environment} {ixe : Ixon.Env} {sub : Ix.Environment}
    (avoids : (ofCompile env ixe).Avoids sub) {n : Name} {ci : ConstantInfo}
    (found : sub.consts.get? n = some ci) : Unchanged env ixe n :=
  unchanged_of_not_contains env ixe (avoids n ci found)

end Ix.Cert.Unchanged

/-! ## Pass 3's heads are in the changed set (`checkReport`'s eleventh check)

The check reads the regenerated published input names (`Ix.Cert.regeneratedNames`),
each of which has a `regenerated` entry in the changed set whatever its
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

/-- A regenerated name is a published input name whose `Named` entry has an
original-form record at another address. -/
theorem regeneratedNames_spec {env : Ix.Environment} {ixe : Ixon.Env}
    {n : Ix.Compile.ExactKey.ExactName} (h : (regeneratedNames env ixe).contains n = true) :
    ∃ (named : Ixon.Named) (orig : Address) (cmeta : Ixon.ConstantMeta),
      ((n : Name), named) ∈ ixe.named.toList ∧ named.original = some (orig, cmeta) ∧
        (orig != named.addr && (env.consts.get? n).isSome) = true := by
  unfold regeneratedNames at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  have key : ∀ (l : List (Name × Ixon.Named)) (s : Std.HashSet Ix.Compile.ExactKey.ExactName),
      (l.foldl (fun s p => match p.2.original with
        | some (orig, _) => if (orig != p.2.addr && (env.consts.get? p.1).isSome) = true then s.insert p.1 else s
        | none => s) s).contains n = true →
      s.contains n = true ∨ ∃ (named : Ixon.Named) (orig : Address) (cmeta : Ixon.ConstantMeta),
        ((n : Name), named) ∈ l ∧ named.original = some (orig, cmeta) ∧
          (orig != named.addr && (env.consts.get? n).isSome) = true := by
    intro l
    induction l with
    | nil => intro s hs; exact .inl hs
    | cons p l ih =>
      intro s hs
      rw [List.foldl_cons] at hs
      rcases ih _ hs with hs | ⟨named, orig, cmeta, hmem, ho, hd⟩
      · obtain ⟨k, named⟩ := p
        dsimp only at hs
        split at hs
        · rename_i orig cmeta ho
          split at hs
          · rename_i hd
            rcases exact_insert_contains (k := k) hs with hk | hs
            · subst hk
              exact .inr ⟨named, orig, cmeta, List.mem_cons_self, ho, hd⟩
            · exact .inl hs
          · exact .inl hs
        · exact .inl hs
      · exact .inr ⟨named, orig, cmeta, List.mem_cons_of_mem _ hmem, ho, hd⟩
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

/-- What `foreignHead = none` says first: every key of `heads` is a
regenerated published input name. -/
theorem foreignHead_regenerated {env : Ix.Environment}
    {heads : Std.HashMap Ix.Compile.ExactKey.ExactName Ix.Name} {ixe : Ixon.Env}
    (h : foreignHead env heads ixe = none) :
    ∀ (n : Ix.Compile.ExactKey.ExactName) (k : Ix.Name), heads.get? n = some k →
      (regeneratedNames env ixe).contains n = true := by
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
  cases hc : (regeneratedNames env ixe).contains n
  · simp [hc] at hfind
  · rfl

/-- What `foreignHead = none` says: every key of `heads` is in the changed
set of the compile of `env` to `ixe` (each is a regenerated published input
name, `foreignHead_regenerated` and `regeneratedNames_spec`, with a
`regenerated` entry in the set, `Unchanged.regenerated_entry`). -/
theorem foreignHead_none {env : Ix.Environment}
    {heads : Std.HashMap Ix.Compile.ExactKey.ExactName Ix.Name} {ixe : Ixon.Env}
    (h : foreignHead env heads ixe = none) :
    ∀ (n : Ix.Compile.ExactKey.ExactName) (k : Ix.Name), heads.get? n = some k →
      (Ix.Compile.ChangedSet.ofCompile env ixe).contains n = true := by
  intro n k hn
  obtain ⟨named, orig, cmeta, hnamed, ho, hd⟩ := regeneratedNames_spec (foreignHead_regenerated h n k hn)
  rw [Bool.and_eq_true] at hd
  exact contains_of_entry env ixe
    (regenerated_entry env ixe _ hnamed ho (by rw [Bool.and_eq_true]; exact ⟨hd.1, get?_isSome_of_consts hd.2⟩))
    BEq.rfl

/-- **Pass 3's heads are in the changed set**: in the driver's final
environment, which `compileUnchecked` returns, every Pass 3 head is in the
compile's changed set (`checkReport`'s eleventh check). -/
theorem headsChanged {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∃ cenv : Ix.CompileM.CompileEnv, compileUnchecked env = .ok (ixe, failures, cenv) ∧
      ∀ (n : Ix.Compile.ExactKey.ExactName) (k : Ix.Name), cenv.p3Heads.get? n = some k →
        (Ix.Compile.ChangedSet.ofCompile env ixe).contains n = true := by
  obtain ⟨cenv, hu, hc⟩ := compileReport_ok h
  exact ⟨cenv, hu, foreignHead_none (checkReport_ok hc).2.2.2.2.2.2.2.2.2.2.1⟩

end Ix.Cert
