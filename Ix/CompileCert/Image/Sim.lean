import Ix.CompileCert.Image.Ren
import Ix.CompileCert.Canon.Ref

/-!
# M7 L2a-syn: two runs of the generator from shifted counters

`Ix.Compile.Image.GenM` names the variables it opens from a counter (`freshName`: the `i`-th is
`_img_fvar.i`, `fresh i`). Run from counter `s` and from `s + d`, a computation opens the same
binders under the names shifted by `d` (`shift s0 d`, the identity below `s0`), so its results are
related by `Ren (shift s0 d)`, provided `==` (hash equality) separates the fresh names involved
(`NamesOK`, a hypothesis about Blake3 on finitely many names, as L1's distinctness hypotheses are).

* `Sim s0 d B R x y`: whenever `x` succeeds from a state with counter `≥ s0` and ends at a counter
  `≤ B`, `y` succeeds from the shifted state with an `R`-related result and the shifted end state;
* `Mono x`: `x` never decreases the counter (needed to compose `Sim` through `bind`);
* the combinators: `pure`, `bind`, `throw`, `liftExcept`, `freshName`, `GenM.trace`, `GenM.idx`,
  loops (`forIn` over lists and arrays).
-/

namespace Ix.CompileCert.Img

open Ix (Name Level Expr)
open Ix.Compile.Image (GenM GenState freshName fvarRoot)

/-- The `i`-th fresh name of the generator. -/
def fresh (i : Nat) : Name := Ix.Name.mkNat fvarRoot i

theorem freshName_run (st : GenState) :
    freshName.run st = .ok (fresh st.next, { st with next := st.next + 1 }) := rfl

/-- The fresh names below `B` are pairwise distinct under `==`. -/
def NamesOK (B : Nat) : Prop := ∀ i j, i < B → j < B → (fresh i == fresh j) = (i == j)

/-- A fresh name below `B`. -/
def FreshBelow (B : Nat) (n : Name) : Prop := ∃ i, i < B ∧ n = fresh i

theorem FreshBelow.mono {B B' : Nat} (h : B ≤ B') {n : Name} (hn : FreshBelow B n) :
    FreshBelow B' n := by
  obtain ⟨i, hi, rfl⟩ := hn; exact ⟨i, by omega, rfl⟩

/-- The shift of the fresh names from `s0` on by `d`; other names are kept. -/
def shift (s0 d : Nat) (n : Name) : Name :=
  match n with
  | .num p i h => if (Ix.Name.num p i h == fresh i) && s0 ≤ i then fresh (i + d) else n
  | n => n

theorem shift_fresh (s0 d i : Nat) :
    shift s0 d (fresh i) = if s0 ≤ i then fresh (i + d) else fresh i := by
  have e : fresh i = Ix.Name.num fvarRoot i (fresh i).getHash := rfl
  conv => lhs; rw [e]
  simp only [shift]
  rw [← e, Ix.CompileCert.Canon.name_beq_refl]
  simp only [Bool.true_and, decide_eq_true_eq]

/-- The shifted index. -/
def shiftIdx (s0 d i : Nat) : Nat := if s0 ≤ i then i + d else i

theorem shift_fresh' (s0 d i : Nat) : shift s0 d (fresh i) = fresh (shiftIdx s0 d i) := by
  rw [shift_fresh]; unfold shiftIdx; split <;> rfl

theorem shiftIdx_lt {s0 d i B : Nat} (h : i < B) : shiftIdx s0 d i < B + d := by
  unfold shiftIdx; split <;> omega

theorem shiftIdx_inj {s0 d i j : Nat} : (shiftIdx s0 d i = shiftIdx s0 d j) ↔ i = j := by
  unfold shiftIdx; constructor
  · intro h; split at h <;> split at h <;> omega
  · intro h; subst h; rfl

/-- **The shift keeps `==` on the fresh names below `B`**, given that the fresh names below
`B + d` are distinct. -/
theorem injOn_shift {s0 d B : Nat} (hok : NamesOK (B + d)) : InjOn (shift s0 d) (FreshBelow B) := by
  rintro a b ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
  rw [shift_fresh', shift_fresh', hok _ _ (shiftIdx_lt hi) (shiftIdx_lt hj),
    hok _ _ (by omega) (by omega)]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, shiftIdx_inj]

/-- With no shift, nothing to keep: the hypothesis of the simulation at `d = 0`. -/
theorem injOn_shift_zero {s0 B : Nat} : InjOn (shift s0 0) (FreshBelow B) := by
  rintro a b ⟨i, -, rfl⟩ ⟨j, -, rfl⟩
  rw [shift_fresh, shift_fresh]
  split <;> split <;> rfl

/-! ## Runs from shifted counters -/

/-- States of the two runs: the second's counter shifted by `d`, the logs equal, the first's
counter at least `s0`. -/
def SR (s0 d : Nat) (st st' : GenState) : Prop :=
  st'.next = st.next + d ∧ st'.log = st.log ∧ s0 ≤ st.next

/-- **Two runs related**: when the first succeeds ending at a counter `≤ B`, the second succeeds
from the related state with an `R`-related result and a related end state. -/
def Sim (s0 d B : Nat) {α β : Type} (R : α → β → Prop) (x : GenM α) (y : GenM β) : Prop :=
  ∀ st st' a st1, SR s0 d st st' → x.run st = .ok (a, st1) → st1.next ≤ B →
    ∃ b st1', y.run st' = .ok (b, st1') ∧ R a b ∧ SR s0 d st1 st1'

/-- The counter never decreases. -/
def Mono {α : Type} (x : GenM α) : Prop := ∀ st a st1, x.run st = .ok (a, st1) → st.next ≤ st1.next

section
variable {s0 d B : Nat}

theorem run_bind {α β : Type} (x : GenM α) (f : α → GenM β) (st : GenState) :
    (x >>= f).run st = (do let (a, st1) ← x.run st; (f a).run st1) := rfl

theorem run_pure {α : Type} (a : α) (st : GenState) : (pure a : GenM α).run st = .ok (a, st) := rfl

theorem Sim.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Sim s0 d B R (Pure.pure a) (Pure.pure b) := by
  intro st st' a' st1 hs hx _
  rw [run_pure] at hx; cases hx
  exact ⟨b, st', run_pure _ _, h, hs⟩

theorem Mono.pure {α : Type} (a : α) : Mono (Pure.pure a : GenM α) := by
  intro st a' st1 h; rw [run_pure] at h; cases h; exact Nat.le_refl _

theorem Mono.bind {α β : Type} {x : GenM α} {f : α → GenM β} (hx : Mono x) (hf : ∀ a, Mono (f a)) :
    Mono (x >>= f) := by
  intro st c st2 h
  rw [run_bind] at h
  cases hxr : x.run st with
  | error e => rw [hxr] at h; cases h
  | ok p =>
    obtain ⟨a, st1⟩ := p
    rw [hxr] at h
    exact Nat.le_trans (hx _ _ _ hxr) (hf a _ _ _ h)

theorem Sim.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : GenM α} {y : GenM β} {f : α → GenM γ} {g : β → GenM δ}
    (hx : Sim s0 d B R x y) (hf : ∀ a b, R a b → Sim s0 d B S (f a) (g b)) (hm : ∀ a, Mono (f a)) :
    Sim s0 d B S (x >>= f) (y >>= g) := by
  intro st st' c st2 hs h hB
  rw [run_bind] at h
  cases hxr : x.run st with
  | error e => rw [hxr] at h; cases h
  | ok p =>
    obtain ⟨a, st1⟩ := p
    rw [hxr] at h
    have h1 := hm a _ _ _ h
    obtain ⟨b, st1', hy, hab, hs1⟩ := hx _ _ _ _ hs hxr (by omega)
    obtain ⟨d', st2', hg, hcd, hs2⟩ := hf a b hab _ _ _ _ hs1 h hB
    refine ⟨d', st2', ?_, hcd, hs2⟩
    rw [run_bind, hy]; exact hg

theorem Sim.throw {α β : Type} {R : α → β → Prop} (e : String) {y : GenM β} :
    Sim s0 d B R (throw e : GenM α) y := by
  intro st st' a st1 _ h; cases h

theorem Mono.throw {α : Type} (e : String) : Mono (throw e : GenM α) := by
  intro st a st1 h; cases h

theorem Sim.liftExcept {α β : Type} {R : α → β → Prop} {x : Except String α} {y : Except String β}
    (h : ExRel R x y) : Sim s0 d B R (Ix.Compile.Image.liftExcept x) (Ix.Compile.Image.liftExcept y) := by
  intro st st' a st1 hs hx _
  cases x with
  | error e => cases hx
  | ok a' =>
    cases y with
    | error e => cases h
    | ok b =>
      have : a' = a ∧ st = st1 := by
        simp only [Ix.Compile.Image.liftExcept] at hx
        cases hx; exact ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨b, st', rfl, h, hs⟩

theorem Mono.liftExcept {α : Type} (x : Except String α) : Mono (Ix.Compile.Image.liftExcept x) := by
  intro st a st1 h
  cases x with
  | error e => cases h
  | ok a' => simp only [Ix.Compile.Image.liftExcept] at h; cases h; exact Nat.le_refl _

theorem Sim.freshName : Sim s0 d B (fun n n' => n' = shift s0 d n ∧ FreshBelow B n) freshName freshName := by
  intro st st' a st1 hs hx hB
  rw [freshName_run] at hx; cases hx
  refine ⟨fresh st'.next, { st' with next := st'.next + 1 }, freshName_run _, ⟨?_, ?_⟩, ?_⟩
  · rw [shift_fresh]; simp only [hs.2.2, ↓reduceIte, hs.1]
  · exact ⟨st.next, by simp at hB; omega, rfl⟩
  · have h1 := hs.1; have h2 := hs.2.2
    exact ⟨by simp [h1]; omega, hs.2.1, by simp; omega⟩

theorem Mono.freshName : Mono freshName := by
  intro st a st1 h; rw [freshName_run] at h; cases h; simp

theorem Sim.trace (s : String) : Sim s0 d B (fun _ _ => True) (Ix.Compile.Image.GenM.trace s)
    (Ix.Compile.Image.GenM.trace s) := by
  intro st st' a st1 hs hx _
  simp only [Ix.Compile.Image.GenM.trace, modify, modifyGet, StateT.run] at hx
  cases hx
  refine ⟨(), { st' with log := st'.log.push s }, rfl, trivial, ?_⟩
  exact ⟨hs.1, by simp [hs.2.1], hs.2.2⟩

theorem Mono.trace (s : String) : Mono (Ix.Compile.Image.GenM.trace s) := by
  intro st a st1 h
  simp only [Ix.Compile.Image.GenM.trace, modify, modifyGet, StateT.run] at h
  cases h; exact Nat.le_refl _

theorem Sim.idx {α β : Type} {R : α → β → Prop} {xs : Array α} {ys : Array β} (hs : xs.size = ys.size)
    (h : ∀ i (h1 : i < xs.size) (h2 : i < ys.size), R xs[i] ys[i]) (i : Nat) (w : String) :
    Sim s0 d B R (Ix.Compile.Image.GenM.idx xs i w) (Ix.Compile.Image.GenM.idx ys i w) := by
  intro st st' a st1 hst hx _
  unfold Ix.Compile.Image.GenM.idx at hx ⊢
  by_cases hi : i < xs.size
  · rw [Array.getElem?_eq_getElem hi] at hx
    rw [Array.getElem?_eq_getElem (by omega)]
    cases hx
    exact ⟨ys[i], st', rfl, h i hi (by omega), hst⟩
  · rw [Array.getElem?_eq_none (by omega)] at hx; cases hx

theorem Mono.idx {α : Type} (xs : Array α) (i : Nat) (w : String) :
    Mono (Ix.Compile.Image.GenM.idx xs i w) := by
  intro st a st1 h
  unfold Ix.Compile.Image.GenM.idx at h
  split at h
  · cases h; exact Nat.le_refl _
  · cases h

/-! ## Loops -/

/-- Two loop steps related. -/
def StepRel {β δ : Type} (R : β → δ → Prop) : ForInStep β → ForInStep δ → Prop
  | .yield b, .yield b' => R b b'
  | .done b, .done b' => R b b'
  | _, _ => False

theorem Mono.forIn_list {α β : Type} {f : α → β → GenM (ForInStep β)} (hf : ∀ a b, Mono (f a b)) :
    ∀ (l : List α) (b : β), Mono (forIn l b f)
  | [], b => by simp only [List.forIn_nil]; exact Mono.pure b
  | a :: l, b => by
    simp only [List.forIn_cons]
    refine Mono.bind (hf a b) fun r => ?_
    cases r with
    | done b' => exact Mono.pure b'
    | yield b' => exact Mono.forIn_list hf l b'

theorem Sim.forIn_list {α γ β δ : Type} {Ra : α → γ → Prop} {R : β → δ → Prop}
    {f : α → β → GenM (ForInStep β)} {g : γ → δ → GenM (ForInStep δ)}
    (hfg : ∀ a c b b', Ra a c → R b b' → Sim s0 d B (StepRel R) (f a b) (g c b'))
    (hm : ∀ a b, Mono (f a b)) :
    ∀ {l : List α} {l' : List γ}, LRel Ra l l' → ∀ {b : β} {b' : δ}, R b b' →
      Sim s0 d B R (forIn l b f) (forIn l' b' g)
  | [], [], .nil, b, b', h => by simp only [List.forIn_nil]; exact Sim.pure h
  | a :: l, c :: l', .cons hac hl, b, b', h => by
    simp only [List.forIn_cons]
    refine Sim.bind (hfg a c b b' hac h) (fun r r' hr => ?_) (fun r => ?_)
    · cases r <;> cases r' <;> simp only [StepRel] at hr
      · exact Sim.pure hr
      · exact Sim.forIn_list hfg hm hl hr
    · cases r with
      | done b'' => exact Mono.pure b''
      | yield b'' => exact Mono.forIn_list hm l b''

theorem Mono.forIn_array {α β : Type} {f : α → β → GenM (ForInStep β)} (hf : ∀ a b, Mono (f a b))
    (xs : Array α) (b : β) : Mono (forIn xs b f) := by
  rw [← Array.forIn_toList]; exact Mono.forIn_list hf _ b

theorem Sim.forIn_array {α γ β δ : Type} {Ra : α → γ → Prop} {R : β → δ → Prop}
    {f : α → β → GenM (ForInStep β)} {g : γ → δ → GenM (ForInStep δ)}
    (hfg : ∀ a c b b', Ra a c → R b b' → Sim s0 d B (StepRel R) (f a b) (g c b'))
    (hm : ∀ a b, Mono (f a b)) {xs : Array α} {ys : Array γ} (hxy : LRel Ra xs.toList ys.toList)
    {b : β} {b' : δ} (h : R b b') : Sim s0 d B R (forIn xs b f) (forIn ys b' g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact Sim.forIn_list hfg hm hxy h

theorem Sim.of_fail {α β : Type} {R : α → β → Prop} {x : GenM α} {y : GenM β}
    (h : ∀ st, ∃ e, x.run st = .error e) : Sim s0 d B R x y := by
  intro st st' a st1 _ hx
  obtain ⟨e, he⟩ := h st
  rw [he] at hx; cases hx

theorem Mono.of_fail {α : Type} {x : GenM α} (h : ∀ st, ∃ e, x.run st = .error e) : Mono x := by
  intro st a st1 hx
  obtain ⟨e, he⟩ := h st
  rw [he] at hx; cases hx

theorem throw_bind_fail {α β : Type} (e : String) (f : α → GenM β) :
    ∀ st, ∃ e', ((throw e : GenM α) >>= f).run st = .error e' := fun _ => ⟨e, rfl⟩

/-- At `d = 0` the two runs are one: the same program from the same state. -/
theorem Sim.refl0 {α : Type} {x : GenM α} (hx : Mono x) : Sim s0 0 B Eq x x := by
  intro st st' a st1 hs h _
  have e : st' = st := by
    obtain ⟨h1, h2, -⟩ := hs
    cases st; cases st'; simp only at h1 h2; simp [h1, h2]
  subst e
  exact ⟨a, st1, h, rfl, rfl, rfl, Nat.le_trans hs.2.2 (hx _ _ _ h)⟩

theorem Mono.get : Mono (get : GenM GenState) := by
  intro st a st1 h; cases h; exact Nat.le_refl _

theorem Sim.get : Sim s0 d B (fun a b => SR s0 d a b) (get : GenM GenState) (get : GenM GenState) := by
  intro st st' a st1 hs h _
  cases h
  exact ⟨st', st', rfl, hs, hs⟩

end

end Ix.CompileCert.Img
