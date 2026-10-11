import Ix.CompileCert.Canon.Ctx

/-!
# M7 L1, the refinement: the code is the pure refinement

`Ix.Compile.Canon.sortClasses` runs the refinement of design document §2.3 in `CmpM` (one
cache across all rounds). This module states the same procedure in `Except` (`refineClassP`,
`refineClassesP`, `sortLoopP`, `sortClassesP`: the comparison of each round is `constOrd`
under that round's context `MutConst.ctx classes`) and proves that the code returns exactly
its classes (`sortClasses_eq`), for `portFixes := true`, an address map that answers alike
for `==` names, and members whose member and constructor names are pairwise distinct.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst MutCtx)

/-! ## The pure refinement -/

/-- The equality test `refineClass` groups with. -/
def eqOf (pc : MutConst → MutConst → Except String Ordering) (a b : MutConst) : Except String Bool := do
  return (← pc a b) == .eq

/-- The representative rule applied to the groups. -/
def repOf (rules : Rules) (groups : List (List MutConst)) : List (List MutConst) :=
  match rules.representative with
  | .leastNameHash => groups.map sortByName
  | .firstInCanonicalOrder => groups

def refineClassP (rules : Rules) (addr? : Name → Option Address) (ctx : MutCtx) :
    List MutConst → Except String (List (List MutConst))
  | [] => .error "empty class in sortConsts"
  | [x] => pure [[x]]
  | xs => do
    let sorted ← xs.sortByM (constOrd rules addr? ctx)
    let groups ← groupAdjP (eqOf (constOrd rules addr? ctx)) sorted
    pure (repOf rules groups)

def refineClassesP (rules : Rules) (addr? : Name → Option Address) (ctx : MutCtx) :
    List (List MutConst) → Except String (List (List MutConst))
  | [] => pure []
  | c :: cs => do
    let gs ← refineClassP rules addr? ctx c
    let rest ← refineClassesP rules addr? ctx cs
    pure (gs ++ rest)

def sortLoopP (rules : Rules) (addr? : Name → Option Address) :
    Nat → Nat → List (List MutConst) → Except String (List (List MutConst) × Nat)
  | 0, _, _ => .error "sortConsts did not converge"
  | fuel + 1, round, classes => do
    let refined ← refineClassesP rules addr? (MutConst.ctx classes) classes
    if classes.length == refined.length then pure (refined, round + 1)
    else sortLoopP rules addr? fuel (round + 1) refined

/-- The initial order of the members. -/
def seedOf (rules : Rules) (sources : List MutConst) : List MutConst :=
  match rules.seed with
  | .byNameHash => sortByName sources
  | .allOrder => sources

def sortClassesP (rules : Rules) (addr? : Name → Option Address) (sources : List MutConst) :
    Except String (List (List MutConst)) := do
  if sources.isEmpty then return []
  let (classes, _) ← sortLoopP rules addr? (sources.length + 1) 0 [seedOf rules sources]
  if classes.any (·.isEmpty) then .error "empty class after sortConsts"
  if sources.length < classes.length then .error "too many classes after sortConsts"
  return classes

/-! ## Name-hash insertion sort permutes -/

theorem insertByName_perm (x : MutConst) : ∀ (l : List MutConst), (insertByName x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertByName
    split
    · exact ((insertByName_perm x ys).cons y).trans (List.Perm.swap x y ys)
    · exact List.Perm.refl _

theorem sortByName_perm : ∀ (l : List MutConst), (sortByName l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => by
    unfold sortByName
    exact (insertByName_perm x _).trans ((sortByName_perm xs).cons x)

theorem seedOf_perm (rules : Rules) (sources : List MutConst) : (seedOf rules sources).Perm sources := by
  unfold seedOf; split
  · exact sortByName_perm _
  · exact List.Perm.refl _

theorem repOf_flatten_perm (rules : Rules) (groups : List (List MutConst)) :
    (repOf rules groups).flatten.Perm groups.flatten := by
  unfold repOf; split
  · induction groups with
    | nil => exact List.Perm.refl _
    | cons g gs ih =>
      simp only [List.map_cons, List.flatten_cons]
      exact (sortByName_perm g).append ih
  · exact List.Perm.refl _

/-! ## Keys and entries -/

theorem ents_names (ms : List MutConst) : (ents ms).map Ent.name = ms.flatMap keysOf := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [ents, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]
    simp [Ent.name, keysOf, Function.comp_def]

theorem pairwise_map_inj {β γ : Type} {f : β → γ} {R : γ → γ → Prop} :
    ∀ {l : List β}, (l.map f).Pairwise R → ∀ a ∈ l, ∀ b ∈ l, ¬ R (f a) (f b) → ¬ R (f b) (f a) → a = b
  | [], _, a, ha, _, _, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, ha, b, hb, h1, h2 => by
    rw [List.map_cons, List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (h.1 (f b) (List.mem_map_of_mem hb')) h1
    · subst hb'; exact absurd (h.1 (f a) (List.mem_map_of_mem ha')) h2
    · exact pairwise_map_inj h.2 a ha' b hb' h1 h2

theorem KeysDistinct.nameInj {ms : List MutConst} (hk : KeysDistinct ms) : NameInj ms := by
  intro e₁ h₁ e₂ h₂ he
  unfold KeysDistinct at hk
  rw [← ents_names] at hk
  exact pairwise_map_inj hk e₁ h₁ e₂ h₂ (fun h => by rw [he] at h; cases h)
    (fun h => by rw [name_beq_symm he] at h; cases h)

/-- The names of a member list, as a run's domain. -/
def domOf (ms : List MutConst) (n : Name) : Bool := (ms.flatMap keysOf).any (· == n)

theorem ctx_dom_perm {classes : List (List MutConst)} {ms : List MutConst} (h : classes.flatten.Perm ms)
    (n : Name) : ((MutConst.ctx classes)[n]?).isSome = domOf ms n := by
  rw [ctx_dom, domOf]
  exact List.Perm.any_eq (List.Perm.flatMap_right keysOf h)

/-! ## Simulation -/

theorem Sim.get_bind {Inv : CmpState → Prop} {α : Type} {k : CmpState → CmpM α}
    {r : Except String α} (h : ∀ s, Sim Inv (k s) r) : Sim Inv (get >>= k) r := by
  intro st hst
  exact h st st hst

theorem Sim.modify_bind {Inv : CmpState → Prop} {α : Type} {f : CmpState → CmpState}
    (hf : ∀ st, Inv st → Inv (f st)) {m : CmpM α} {r : Except String α} (h : Sim Inv m r) :
    Sim Inv (modify f >>= fun _ => m) r := by
  intro st hst
  exact h (f st) (hf st hst)

theorem Sim.error' {Inv : CmpState → Prop} {α : Type} (e : String) :
    Sim Inv (liftE (.error e) : CmpM α) (.error e) := Sim.liftE' _

theorem constOrd_oriented (rules : Rules) {addr? : Name → Option Address} (hA : AddrCongr addr?)
    (ctx : MutCtx) {S : MutConst → Prop} : Oriented S (constOrd rules addr? ctx) := by
  intro a b _ _ o h
  have := (constOrd_total rules hA ctx).swap (a := a) (b := b) trivial trivial (s := true) (o := o)
    (by simp [liftOrd, h, Except.map])
  cases e : constOrd rules addr? ctx b a with
  | error err => rw [e] at this; cases this
  | ok o' => rw [e] at this; simp [liftOrd, Except.map] at this; rw [this]

/-- The perm of one round's output. -/
theorem refineClassP_perm (rules : Rules) {addr? : Name → Option Address} (hA : AddrCongr addr?)
    (ctx : MutCtx) : ∀ (xs : List MutConst) (gs : List (List MutConst)),
      refineClassP rules addr? ctx xs = .ok gs → gs.flatten.Perm xs
  | [], gs, h => by simp [refineClassP] at h
  | [x], gs, h => by
    simp only [refineClassP, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | x :: y :: rest, gs, h => by
    simp only [refineClassP] at h
    obtain ⟨sorted, hs, h⟩ := except_bind_ok.1 h
    obtain ⟨groups, hg, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨hp, -⟩ := sortByM_spec (constOrd_oriented rules hA ctx (S := fun _ => True)) _
      (fun _ _ => trivial) sorted hs
    obtain ⟨-, hf⟩ := groupAdjP_spec _ _ _ hg
    exact (repOf_flatten_perm rules groups).trans (by rw [hf]; exact hp)

theorem refineClassesP_perm (rules : Rules) {addr? : Name → Option Address} (hA : AddrCongr addr?)
    (ctx : MutCtx) : ∀ (classes refined : List (List MutConst)),
      refineClassesP rules addr? ctx classes = .ok refined → refined.flatten.Perm classes.flatten
  | [], refined, h => by
    simp only [refineClassesP, pure, Except.pure, Except.ok.injEq] at h; subst h; exact List.Perm.refl _
  | c :: cs, refined, h => by
    simp only [refineClassesP] at h
    obtain ⟨gs, hgs, h⟩ := except_bind_ok.1 h
    obtain ⟨rest, hr, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    simp only [List.flatten_append, List.flatten_cons]
    exact (refineClassP_perm rules hA ctx c gs hgs).append (refineClassesP_perm rules hA ctx cs rest hr)

section sim
variable {rules : Rules} {addr? : Name → Option Address} {ms : List MutConst}
  (hpf : rules.portFixes = true) (hA : AddrCongr addr?) (hk : KeysDistinct ms)
include hpf hA hk

/-- The run of a refinement over the members `ms`. -/
abbrev runOf (rules : Rules) (addr? : Name → Option Address) (ms : List MutConst) : Run :=
  ⟨rules, addr?, domOf ms⟩

theorem refineClass_sim {ctx : MutCtx} (hdom : ∀ n, (ctx[n]?).isSome = domOf ms n) :
    ∀ (xs : List MutConst), (∀ x ∈ xs, x ∈ ms) →
      Sim (Coh (runOf rules addr? ms) ms) (refineClass rules addr? ctx xs)
        (refineClassP rules addr? ctx xs) := by
  have hsim : ∀ a b, a ∈ ms → b ∈ ms →
      Sim (Coh (runOf rules addr? ms) ms) (compareConst rules addr? ctx a b)
        (constOrd rules addr? ctx a b) := fun a b ha hb =>
    compareConst_sim (A := runOf rules addr? ms) hk.nameInj hA hpf hdom ha hb
  have hor : Oriented (· ∈ ms) (constOrd rules addr? ctx) := constOrd_oriented rules hA ctx
  intro xs hxs
  match xs, hxs with
  | [], _ => exact Sim.liftE' _
  | [x], _ => exact Sim.pure' _
  | x :: y :: rest, hxs =>
    simp only [refineClass, refineClassP]
    refine Sim.bind (sortByM_sim hsim hor _ hxs) fun sorted hs => ?_
    obtain ⟨hp, -⟩ := sortByM_spec hor _ hxs sorted hs
    refine Sim.get_bind fun _ => ?_
    refine Sim.bind (groupAdjacent_sim (S := (· ∈ ms))
      (fun a b ha hb => Sim.bind (hsim a b ha hb) fun _ _ => Sim.pure' _) sorted
      (fun z hz => hxs z (hp.mem_iff.1 hz))) fun _ _ => ?_
    refine Sim.modify_bind ?_ ?_
    · intro st h; exact h
    · exact Sim.congr (Sim.pure' (repOf rules _)) rfl rfl

theorem refineClasses_sim {ctx : MutCtx} (hdom : ∀ n, (ctx[n]?).isSome = domOf ms n) :
    ∀ (classes : List (List MutConst)), (∀ C ∈ classes, ∀ x ∈ C, x ∈ ms) →
      Sim (Coh (runOf rules addr? ms) ms) (refineClasses rules addr? ctx classes)
        (refineClassesP rules addr? ctx classes)
  | [], _ => Sim.pure' _
  | c :: cs, h => by
    simp only [refineClasses, refineClassesP]
    refine Sim.bind (refineClass_sim hpf hA hk hdom c (h c (by simp))) fun _ _ => ?_
    exact Sim.bind (refineClasses_sim hdom cs fun C hC => h C (by simp [hC])) fun _ _ => Sim.pure' _

theorem sortLoop_sim : ∀ (fuel round : Nat) (classes : List (List MutConst)), classes.flatten.Perm ms →
    Sim (Coh (runOf rules addr? ms) ms) (sortLoop rules addr? fuel round classes)
      (sortLoopP rules addr? fuel round classes) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; exact Sim.liftE' _
  | succ fuel ih =>
    intro round classes hp
    simp only [sortLoop, sortLoopP]
    refine Sim.bind (refineClasses_sim hpf hA hk (ctx_dom_perm hp) classes
      (fun C hC x hx => hp.mem_iff.1 (List.mem_flatten.2 ⟨C, hC, hx⟩))) fun refined hr => ?_
    split
    · exact Sim.pure' _
    · exact ih _ refined ((refineClassesP_perm rules hA _ classes refined hr).trans hp)

end sim

/-- **The code's classes are the pure refinement's** (`portFixes := true`). -/
theorem sortClasses_eq {rules : Rules} (hpf : rules.portFixes = true) {addr? : Name → Option Address}
    (hA : AddrCongr addr?) {sources : List MutConst} (hk : KeysDistinct sources) :
    (sortClasses rules addr? sources).map (·.1) = sortClassesP rules addr? sources := by
  unfold sortClasses sortClassesP
  by_cases he : sources.isEmpty = true
  · simp [he, pure, Except.pure, Except.map]
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    cases hs : rules.seed
    · simp only [seedOf, hs]
      obtain ⟨st', -, e⟩ := sortLoop_sim hpf hA hk (sources.length + 1) 0 [sortByName sources]
        (by simpa using sortByName_perm sources) {} (coh_empty _ _)
      rw [e]
      cases sortLoopP rules addr? (sources.length + 1) 0 [sortByName sources] with
      | error err => rfl
      | ok r =>
        obtain ⟨classes, rounds⟩ := r
        simp only [Except.map, bind, Except.bind]
        by_cases h1 : (classes.any fun x => x.isEmpty) = true
        · simp only [h1, ↓reduceIte]
        · by_cases h2 : sources.length < classes.length
          · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
          · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
    · simp only [seedOf, hs]
      obtain ⟨st', -, e⟩ := sortLoop_sim hpf hA hk (sources.length + 1) 0 [sources]
        (by simp) {} (coh_empty _ _)
      rw [e]
      cases sortLoopP rules addr? (sources.length + 1) 0 [sources] with
      | error err => rfl
      | ok r =>
        obtain ⟨classes, rounds⟩ := r
        simp only [Except.map, bind, Except.bind]
        by_cases h1 : (classes.any fun x => x.isEmpty) = true
        · simp only [h1, ↓reduceIte]
        · by_cases h2 : sources.length < classes.length
          · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
          · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]

end Ix.CompileCert.Canon
