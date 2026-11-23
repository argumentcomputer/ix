import Aiur.Tiling.Ids
import Aiur.Execution.TyCodec

/-!
# The program section reads back what the compiler wrote

`Ixa.getProgram` is a left inverse of `Export.putProgramWithEncoding`: on the
bytes a successful run of the writer appends, the reader returns the same
bytecode (`program_rt`). Interfaces come back as the entries' interfaces, in
entry order, and `dataTypes` is not written.

The proofs are compositional. `RT p g x` says that every successful run of the
writer `p` appends bytes that the reader `g` reads as `x`, whatever follows. A
successful run already carries every bound the grammar needs (TagN integers
below `2 ^ 64`), so the lemmas have no size hypotheses. The scalar encodings
enter through `ScalarCodec`, proved for the narrow (`narrow_scalarCodec`) and
wide (`wide_scalarCodec`) writers.

`program_of_decode` applies it to a package: a file the compiler's package
writer produced and `decodePackage` accepted carries the exported bytecode.
-/

namespace Aiur.Tiling.Ixa

open Aiur.Ixon Aiur.Execution Aiur.Execution.Codec

/-! ## Round trips -/

/-- Every successful run of `p` appends bytes that `g` reads as `x`. -/
def RT {α : Type} (p : PutM Unit) (g : GetM α) (x : α) : Prop :=
  ∀ b b', p b = .ok () b' → ∃ e : List UInt8, b' = b ++ ⟨e.toArray⟩ ∧ Reads g e x

/-- `RT`, appending at least one byte. -/
def RT1 {α : Type} (p : PutM Unit) (g : GetM α) (x : α) : Prop :=
  ∀ b b', p b = .ok () b' → ∃ e : List UInt8, b' = b ++ ⟨e.toArray⟩ ∧ e ≠ [] ∧ Reads g e x

section Framework

variable {α β : Type}

theorem RT1.rt {p : PutM Unit} {g : GetM α} {x : α} (h : RT1 p g x) : RT p g x := by
  intro b b' hp
  obtain ⟨e, he, _, r⟩ := h b b' hp
  exact ⟨e, he, r⟩

theorem bind_unit_ok {p q : PutM Unit} {b b' : ByteArray} (h : (p >>= fun _ => q) b = .ok () b') :
    ∃ b₁, p b = .ok () b₁ ∧ q b₁ = .ok () b' := by
  change EStateM.bind p (fun _ => q) b = _ at h
  simp only [EStateM.bind] at h
  split at h
  · rename_i u b₁ hb
    exact ⟨b₁, hb, h⟩
  · cases h

theorem rt_bind {p q : PutM Unit} {g : GetM α} {f : α → GetM β} {x : α} {y : β}
    (hp : RT p g x) (hq : RT q (f x) y) : RT (p >>= fun _ => q) (g >>= f) y := by
  intro b b' h
  obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok h
  obtain ⟨e₁, rfl, r₁⟩ := hp _ _ h₁
  obtain ⟨e₂, rfl, r₂⟩ := hq _ _ h₂
  exact ⟨e₁ ++ e₂, append_assoc' .., reads_bind r₁ r₂⟩

theorem rt1_bind_l {p q : PutM Unit} {g : GetM α} {f : α → GetM β} {x : α} {y : β}
    (hp : RT1 p g x) (hq : RT q (f x) y) : RT1 (p >>= fun _ => q) (g >>= f) y := by
  intro b b' h
  obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok h
  obtain ⟨e₁, rfl, ne, r₁⟩ := hp _ _ h₁
  obtain ⟨e₂, rfl, r₂⟩ := hq _ _ h₂
  exact ⟨e₁ ++ e₂, append_assoc' .., by simp [ne], reads_bind r₁ r₂⟩

theorem rt1_bind_r {p q : PutM Unit} {g : GetM α} {f : α → GetM β} {x : α} {y : β}
    (hp : RT p g x) (hq : RT1 q (f x) y) : RT1 (p >>= fun _ => q) (g >>= f) y := by
  intro b b' h
  obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok h
  obtain ⟨e₁, rfl, r₁⟩ := hp _ _ h₁
  obtain ⟨e₂, rfl, ne, r₂⟩ := hq _ _ h₂
  exact ⟨e₁ ++ e₂, append_assoc' .., by simp [ne], reads_bind r₁ r₂⟩

/-- A reader step that reads nothing. -/
theorem rt_skip {p : PutM Unit} {g : GetM α} {f : α → GetM β} {x : α} {y : β}
    (hg : Reads g [] x) (hp : RT p (f x) y) : RT p (g >>= f) y := by
  intro b b' h
  obtain ⟨e, rfl, r⟩ := hp b b' h
  exact ⟨e, rfl, reads_bind hg r⟩

theorem rt1_skip {p : PutM Unit} {g : GetM α} {f : α → GetM β} {x : α} {y : β}
    (hg : Reads g [] x) (hp : RT1 p (f x) y) : RT1 p (g >>= f) y := by
  intro b b' h
  obtain ⟨e, rfl, ne, r⟩ := hp b b' h
  exact ⟨e, rfl, ne, reads_bind hg r⟩

/-- The last reader step returns a value computed from what was read. -/
theorem rt1_map {p : PutM Unit} {g : GetM α} {f : α → GetM β} {x : α} {y : β}
    (hp : RT1 p g x) (hf : f x = pure y) : RT1 p (g >>= f) y := by
  intro b b' h
  obtain ⟨e, rfl, ne, r⟩ := hp b b' h
  refine ⟨e, rfl, ne, ?_⟩
  have := reads_bind (e₂ := []) r (hf ▸ reads_pure y)
  simpa using this

theorem rt_map {p : PutM Unit} {g : GetM α} {f : α → GetM β} {x : α} {y : β}
    (hp : RT p g x) (hf : f x = pure y) : RT p (g >>= f) y := by
  intro b b' h
  obtain ⟨e, rfl, r⟩ := hp b b' h
  refine ⟨e, rfl, ?_⟩
  have := reads_bind (e₂ := []) r (hf ▸ reads_pure y)
  simpa using this

theorem rt_pure (x : α) : RT (pure () : PutM Unit) (pure x : GetM α) x := by
  intro b b' h
  cases h
  exact ⟨[], by apply ByteArray.ext; simp [ByteArray.data_append], reads_pure x⟩

theorem rt1_congr {p : PutM Unit} {g : GetM α} {x y : α} (h : RT1 p g x) (e : x = y) : RT1 p g y :=
  e ▸ h

theorem rt_congr {p : PutM Unit} {g : GetM α} {x y : α} (h : RT p g x) (e : x = y) : RT p g y :=
  e ▸ h

theorem reads_unless {c : Bool} (h : c = true) (m : GetM Unit) :
    Reads (unless c do m) [] () := by
  subst h
  exact reads_pure ()

theorem reads_ite_true {c : Prop} [Decidable c] (h : c) (m n : GetM α) {x : α} (hm : Reads m [] x) :
    Reads (if c then m else n) [] x := by
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact hm

end Framework

/-! ## Primitives -/

section Primitives

theorem nat_ok {n : Nat} {b b' : ByteArray} (h : nat n b = .ok () b') : n < 2 ^ 64 := by
  by_contra hn
  have hn' : ¬ n < 18446744073709551616 := hn
  simp [Aiur.Ixon.nat, hn', bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

theorem tagBytes_ne_nil (n : Nat) : tagBytes n ≠ [] := by
  unfold tagBytes
  split_ifs <;> simp

theorem rt1_nat (n : Nat) : RT1 (nat n) getNat n := by
  intro b b' h
  exact ⟨tagBytes n, nat_writes n b b' h, tagBytes_ne_nil n, getNat_reads (nat_ok h)⟩

theorem rt1_tag (what : String) {count : Nat} (x : UInt8) (hx : x.toNat < count) :
    RT1 (u8 x) (getTag what count) x.toNat := by
  intro b b' h
  exact ⟨[x], u8_writes x b b' h, by simp, getTag_reads what hx⟩

theorem rt1_str (s : String) : RT1 (str s) getString s := by
  intro b b' h
  obtain ⟨b₁, h₁, _⟩ := bind_unit_ok h
  have ok := nat_ok h₁
  exact ⟨_, str_writes s b b' h, by simp [tagBytes_ne_nil], getString_reads s ok⟩

theorem rt1_raw8 (bs : ByteArray) (hs : bs.size = 8) : RT1 (raw bs) (getRaw 8) bs := by
  intro b b' h
  refine ⟨bs.data.toList, raw_writes bs b b' h, ?_, ?_⟩
  · intro e
    have := congrArg List.length e
    simp only [Array.length_toList, List.length_nil] at this
    rw [ByteArray.size] at hs
    omega
  · have := getRaw_reads bs.data.toList
    have len : bs.data.toList.length = 8 := by rw [Array.length_toList]; exact hs
    rw [len] at this
    have back : (⟨bs.data.toList.toArray⟩ : ByteArray) = bs := by apply ByteArray.ext; simp
    rwa [back] at this

theorem rt1_bool (x : Bool) : RT1 (bool x) getBool x := by
  have := rt1_tag "bool" (count := 2) (if x then 1 else 0) (by cases x <;> decide)
  refine rt1_map this ?_
  cases x <;> rfl

theorem rt1_option {α β : Type} {o : Option α} {item : α → PutM Unit} {g : GetM β} {f : α → β}
    (h : ∀ x ∈ o, RT1 (item x) g (f x)) : RT1 (option o item) (getOption g) (o.map f) := by
  cases o with
  | none =>
      have := rt1_tag "option" (count := 2) 0 (by decide)
      refine rt1_map this ?_
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
      rfl
  | some x =>
      have := rt1_tag "option" (count := 2) 1 (by decide)
      refine rt1_bind_l this ?_
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))]
      exact (rt1_map (f := fun v => pure (some v)) (y := some (f x)) (h x rfl) rfl).rt

end Primitives

/-! ## Lists -/

section Lists

variable {α β : Type}

/-- A `for` loop whose body runs `item x` and continues appends, item by item,
bytes satisfying `Q`. -/
theorem forIn_rt {f : α → PUnit → PutM (ForInStep PUnit)} {item : α → PutM Unit}
    {Q : α → List UInt8 → Prop} :
    ∀ (xs : List α),
    (∀ x ∈ xs, ∀ b b' s, f x () b = .ok s b' → s = .yield () ∧ item x b = .ok () b') →
    (∀ x ∈ xs, ∀ b b', item x b = .ok () b' → ∃ e : List UInt8, b' = b ++ ⟨e.toArray⟩ ∧ Q x e) →
    ∀ b b', forIn xs () f b = .ok () b' →
      ∃ zs : List (α × List UInt8), zs.map Prod.fst = xs ∧ (∀ z ∈ zs, Q z.1 z.2) ∧
        b' = b ++ ⟨(zs.flatMap Prod.snd).toArray⟩
  | [], _, _, b, b', h => by
      simp only [List.forIn_nil, pure, EStateM.pure] at h
      cases h
      exact ⟨[], rfl, by simp, by apply ByteArray.ext; simp [ByteArray.data_append]⟩
  | x :: xs, hf, hi, b, b', h => by
      simp only [List.forIn_cons, bind, EStateM.bind] at h
      split at h
      · rename_i s b₁ hb
        obtain ⟨rfl, hb'⟩ := hf x (List.mem_cons_self ..) _ _ _ hb
        obtain ⟨e, rfl, q⟩ := hi x (List.mem_cons_self ..) _ _ hb'
        dsimp only at h
        obtain ⟨zs, hzs, hq, rfl⟩ := forIn_rt xs (fun y hy => hf y (List.mem_cons_of_mem _ hy))
          (fun y hy => hi y (List.mem_cons_of_mem _ hy)) _ _ h
        refine ⟨(x, e) :: zs, by simp [hzs], ?_, ?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact q
          · exact hq z hz
        · rw [List.flatMap_cons, append_assoc']
      · cases h

theorem list_body {item : α → PutM Unit} (xs : List α) :
    ∀ x ∈ xs, ∀ b b' s, (do item x; pure (ForInStep.yield PUnit.unit) : PutM (ForInStep PUnit)) b
      = .ok s b' → s = .yield () ∧ item x b = .ok () b' := by
  intro x _ b b' s hrun
  simp only [bind, EStateM.bind] at hrun
  split at hrun
  · rename_i u b₁ hb
    simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, hb⟩
  · cases hrun

/-- `list` with items read by a reader whose result may depend on a bound
(`Q`): the general form behind `rt1_list` and the recursive type readers. -/
theorem list_rt {xs : List α} {item : α → PutM Unit} {Q : α → List UInt8 → Prop} {b b' : ByteArray}
    (hi : ∀ x ∈ xs, ∀ b b', item x b = .ok () b' → ∃ e : List UInt8, b' = b ++ ⟨e.toArray⟩ ∧ Q x e)
    (h : list xs item b = .ok () b') :
    ∃ zs : List (α × List UInt8), zs.map Prod.fst = xs ∧ (∀ z ∈ zs, Q z.1 z.2) ∧
      xs.length < 2 ^ 64 ∧ b' = b ++ ⟨(tagBytes xs.length ++ zs.flatMap Prod.snd).toArray⟩ := by
  obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok h
  have len := nat_ok h₁
  have w₁ := nat_writes _ _ _ h₁
  obtain ⟨b₂, h₂, h₃⟩ := bind_unit_ok h₂
  cases h₃
  obtain ⟨zs, hzs, hq, rfl⟩ := forIn_rt xs (list_body xs) hi _ _ h₂
  exact ⟨zs, hzs, hq, len, by rw [w₁, append_assoc']⟩

theorem getList_reads {g : GetM β} (encs : List (List UInt8 × β))
    (hall : ∀ p ∈ encs, Reads g p.1 p.2) (hne : ∀ p ∈ encs, p.1 ≠ []) (hs : encs.length < 2 ^ 64) :
    Reads (getList g) (tagBytes encs.length ++ encs.flatMap Prod.fst) (encs.map Prod.snd) := by
  have := reads_bind (e₂ := []) (f := fun a => (pure a.toList : GetM (List β)))
    (getArray_reads encs hall hne hs) (reads_pure _)
  simpa [getList] using this

theorem rt1_list {xs : List α} {item : α → PutM Unit} {g : GetM β} {f : α → β}
    (h : ∀ x ∈ xs, RT1 (item x) g (f x)) : RT1 (list xs item) (getList g) (xs.map f) := by
  intro b b' hrun
  obtain ⟨zs, hzs, hq, len, rfl⟩ := list_rt (Q := fun x e => e ≠ [] ∧ Reads g e (f x))
    (fun x hx b b' hr => by
      obtain ⟨e, he, ne, r⟩ := h x hx b b' hr
      exact ⟨e, he, ne, r⟩) hrun
  let encs := zs.map fun z => (z.2, f z.1)
  have elen : encs.length = xs.length := by simp [encs, ← hzs]
  have r := getList_reads (g := g) encs
    (by intro p hp; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp; exact (hq z hz).2)
    (by intro p hp; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp; exact (hq z hz).1)
    (by rw [elen]; exact len)
  have flat : encs.flatMap Prod.fst = zs.flatMap Prod.snd := by simp [encs, List.flatMap_map]
  have vals : encs.map Prod.snd = xs.map f := by simp [encs, ← hzs, List.map_map, Function.comp_def]
  rw [elen, flat, vals] at r
  exact ⟨_, rfl, by simp [tagBytes_ne_nil], r⟩

theorem rt1_list_id {xs : List α} {item : α → PutM Unit} {g : GetM α}
    (h : ∀ x ∈ xs, RT1 (item x) g x) : RT1 (list xs item) (getList g) xs := by
  have := rt1_list (f := id) h
  simpa using this

theorem rt1_nats (xs : List Nat) : RT1 (nats xs) getNats xs :=
  rt1_list_id fun x _ => rt1_nat x

theorem array_eq_list {xs : Array α} {item : α → PutM Unit} : array xs item = list xs.toList item := by
  simp only [Ixon.array, Ixon.list, Array.length_toList, Array.forIn_toList]

theorem rt1_array {xs : Array α} {item : α → PutM Unit} {g : GetM β} {f : α → β}
    (h : ∀ x ∈ xs, RT1 (item x) g (f x)) : RT1 (array xs item) (getArray g) (xs.map f) := by
  rw [array_eq_list]
  have := rt1_list (xs := xs.toList) (g := g) (f := f) (fun x hx => h x (Array.mem_toList_iff.mp hx))
  intro b b' hrun
  obtain ⟨e, he, ne, r⟩ := this b b' hrun
  refine ⟨e, he, ne, ?_⟩
  intro bs pos hat
  have := r bs pos hat
  simp only [getList, EStateM.run, bind, EStateM.bind] at this ⊢
  split at this
  · rename_i a s hs
    simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at this
    obtain ⟨ha, rfl⟩ := this
    rw [hs]
    congr 1
    apply Array.toList_inj.mp
    simpa using ha
  · cases this

end Lists

/-! ## Readers with a nesting bound -/

section Fuel

variable {α β γ : Type}

/-- `RT` for a reader with a nesting bound: any bound at least the number of
bytes written suffices. -/
def RTF (p : PutM Unit) (G : Nat → GetM α) (x : α) : Prop :=
  ∀ b b', p b = .ok () b' → ∃ e : List UInt8, b' = b ++ ⟨e.toArray⟩ ∧
    ∀ fuel, e.length ≤ fuel → Reads (G fuel) e x

/-- `RTF`, appending at least one byte. -/
def RTF1 (p : PutM Unit) (G : Nat → GetM α) (x : α) : Prop :=
  ∀ b b', p b = .ok () b' → ∃ e : List UInt8, b' = b ++ ⟨e.toArray⟩ ∧ e ≠ [] ∧
    ∀ fuel, e.length ≤ fuel → Reads (G fuel) e x

theorem RTF1.rtf {p : PutM Unit} {G : Nat → GetM α} {x : α} (h : RTF1 p G x) : RTF p G x := by
  intro b b' hp
  obtain ⟨e, he, _, r⟩ := h b b' hp
  exact ⟨e, he, r⟩

theorem RT.rtf {p : PutM Unit} {g : GetM α} {x : α} (h : RT p g x) : RTF p (fun _ => g) x := by
  intro b b' hp
  obtain ⟨e, he, r⟩ := h b b' hp
  exact ⟨e, he, fun _ _ => r⟩

theorem RT1.rtf1 {p : PutM Unit} {g : GetM α} {x : α} (h : RT1 p g x) : RTF1 p (fun _ => g) x := by
  intro b b' hp
  obtain ⟨e, he, ne, r⟩ := h b b' hp
  exact ⟨e, he, ne, fun _ _ => r⟩

theorem rtf_bind {p q : PutM Unit} {G : Nat → GetM α} {F : Nat → α → GetM β} {x : α} {y : β}
    (hp : RTF p G x) (hq : RTF q (fun n => F n x) y) :
    RTF (p >>= fun _ => q) (fun n => G n >>= F n) y := by
  intro b b' h
  obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok h
  obtain ⟨e₁, rfl, r₁⟩ := hp _ _ h₁
  obtain ⟨e₂, rfl, r₂⟩ := hq _ _ h₂
  refine ⟨e₁ ++ e₂, append_assoc' .., fun fuel le => ?_⟩
  simp only [List.length_append] at le
  exact reads_bind (r₁ fuel (by omega)) (r₂ fuel (by omega))

theorem rtf1_bind_l {p q : PutM Unit} {G : Nat → GetM α} {F : Nat → α → GetM β} {x : α} {y : β}
    (hp : RTF1 p G x) (hq : RTF q (fun n => F n x) y) :
    RTF1 (p >>= fun _ => q) (fun n => G n >>= F n) y := by
  intro b b' h
  obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok h
  obtain ⟨e₁, rfl, ne, r₁⟩ := hp _ _ h₁
  obtain ⟨e₂, rfl, r₂⟩ := hq _ _ h₂
  refine ⟨e₁ ++ e₂, append_assoc' .., by simp [ne], fun fuel le => ?_⟩
  simp only [List.length_append] at le
  exact reads_bind (r₁ fuel (by omega)) (r₂ fuel (by omega))

theorem rtf_map {p : PutM Unit} {G : Nat → GetM α} {F : Nat → α → GetM β} {x : α} {y : β}
    (hp : RTF p G x) (hf : ∀ n, F n x = pure y) : RTF p (fun n => G n >>= F n) y := by
  intro b b' h
  obtain ⟨e, rfl, r⟩ := hp b b' h
  refine ⟨e, rfl, fun fuel le => ?_⟩
  have := reads_bind (e₂ := []) (r fuel le) ((hf fuel).symm ▸ reads_pure y)
  simpa using this

theorem rtf1_map {p : PutM Unit} {G : Nat → GetM α} {F : Nat → α → GetM β} {x : α} {y : β}
    (hp : RTF1 p G x) (hf : ∀ n, F n x = pure y) : RTF1 p (fun n => G n >>= F n) y := by
  intro b b' h
  obtain ⟨e, rfl, ne, r⟩ := hp b b' h
  refine ⟨e, rfl, ne, fun fuel le => ?_⟩
  have := reads_bind (e₂ := []) (r fuel le) ((hf fuel).symm ▸ reads_pure y)
  simpa using this

/-- One nesting level: a tag byte, then a body read with one less unit of the
bound. -/
theorem rtf_tagged {Aux : Nat → GetM γ} {what : String} {count : Nat} {tag : UInt8}
    (htag : tag.toNat < count) {M : Nat → Nat → GetM γ}
    (hstep : ∀ f, Aux (f + 1) = getTag what count >>= M f) {q : PutM Unit} {y : γ}
    (hq : RTF q (fun f => M f tag.toNat) y) : RTF1 (u8 tag >>= fun _ => q) Aux y := by
  intro b b' h
  obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok h
  obtain ⟨e, rfl, r⟩ := hq _ _ h₂
  have w := u8_writes tag _ _ h₁
  subst w
  refine ⟨tag :: e, by rw [append_assoc']; rfl, by simp, fun fuel le => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at le; omega⟩
  rw [hstep]
  exact reads_bind (e₁ := [tag]) (getTag_reads what htag) (r f (by simp at le; omega))

theorem length_le_flat {α : Type} {zs : List (α × List UInt8)} {z : α × List UInt8} (h : z ∈ zs) :
    z.2.length ≤ (zs.flatMap Prod.snd).length := by
  rw [List.length_flatMap]
  exact le_sum_of_mem' (List.mem_map.mpr ⟨z, h, rfl⟩)

theorem rtf1_array {xs : List α} {item : α → PutM Unit} {G : Nat → GetM β} {f : α → β}
    (h : ∀ x ∈ xs, RTF1 (item x) G (f x)) :
    RTF1 (list xs item) (fun n => getArray (G n)) (xs.map f).toArray := by
  intro b b' hrun
  obtain ⟨zs, hzs, hq, len, rfl⟩ := list_rt
    (Q := fun x e => e ≠ [] ∧ ∀ fuel, e.length ≤ fuel → Reads (G fuel) e (f x))
    (fun x hx b b' hr => by
      obtain ⟨e, he, ne, r⟩ := h x hx b b' hr
      exact ⟨e, he, ne, r⟩) hrun
  refine ⟨_, rfl, by simp [tagBytes_ne_nil], fun fuel le => ?_⟩
  let encs := zs.map fun z => (z.2, f z.1)
  have elen : encs.length = xs.length := by simp [encs, ← hzs]
  simp only [List.length_append] at le
  have r := getArray_reads (item := G fuel) encs
    (by
      intro p hp
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp
      exact (hq z hz).2 fuel (by have := length_le_flat hz; omega))
    (by intro p hp; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp; exact (hq z hz).1)
    (by rw [elen]; exact len)
  have flat : encs.flatMap Prod.fst = zs.flatMap Prod.snd := by simp [encs, List.flatMap_map]
  have vals : encs.map Prod.snd = xs.map f := by simp [encs, ← hzs, List.map_map, Function.comp_def]
  rw [elen, flat, vals] at r
  exact r

theorem rtf1_list {xs : List α} {item : α → PutM Unit} {G : Nat → GetM β} {f : α → β}
    (h : ∀ x ∈ xs, RTF1 (item x) G (f x)) :
    RTF1 (list xs item) (fun n => getList (G n)) (xs.map f) := by
  have := rtf1_map (F := fun _ a => (pure a.toList : GetM (List β))) (rtf1_array h) (fun _ => rfl)
  simpa [getList] using this

/-- A reader whose nesting bound is one more than the remaining bytes. -/
theorem reads_remaining {G : Nat → GetM α} {e : List UInt8} {x : α}
    (h : ∀ fuel, e.length ≤ fuel → Reads (G fuel) e x) :
    Reads (do G ((← remaining) + 1)) e x := by
  intro bs pos hat
  have room := at_le hat
  have r := h (bs.size - pos + 1) (by omega) bs pos hat
  simp only [EStateM.run] at r ⊢
  simp only [bind, EStateM.bind, remaining, get, getThe, MonadStateOf.get, EStateM.get, pure,
    EStateM.pure]
  exact r

theorem RTF1.remaining {p : PutM Unit} {G : Nat → GetM α} {x : α} (h : RTF1 p G x) :
    RT1 p (do G ((← remaining) + 1)) x := by
  intro b b' hp
  obtain ⟨e, he, ne, r⟩ := h b b' hp
  exact ⟨e, he, ne, reads_remaining r⟩

end Fuel

/-! ## Types -/

section Types

theorem getTyAux_succ (f : Nat) : getTyAux (f + 1) = getTag "type" 4 >>= fun tag =>
    match tag with
    | 0 => return .field
    | 1 => return .tuple (← getArray (getTyAux f)).toList
    | 2 => return .ptr (← getTyAux f)
    | _ => return .enum (← getString) := rfl

theorem ty_rtf : ∀ t : Ty, RTF1 (putTy t) getTyAux t
  | .field => by
      intro b b' h
      rw [putTy] at h
      have := rtf_tagged (q := pure ()) (Aux := getTyAux) (tag := 0) (by decide) getTyAux_succ
        (rt_pure Ty.field).rtf
      exact this b b' (by simpa using h)
  | .ptr t => by
      rw [putTy]
      refine rtf_tagged (tag := 2) (by decide) getTyAux_succ ?_
      exact (rtf1_map (F := fun _ x => (pure (Ty.ptr x) : GetM Ty)) (ty_rtf t) (fun _ => rfl)).rtf
  | .enum name => by
      rw [putTy]
      refine rtf_tagged (tag := 3) (by decide) getTyAux_succ ?_
      exact (rtf1_map (F := fun _ x => (pure (Ty.enum x) : GetM Ty)) (rt1_str name).rtf1
        (fun _ => rfl)).rtf
  | .tuple items => by
      rw [putTy]
      refine rtf_tagged (tag := 1) (by decide) getTyAux_succ ?_
      have hi : ∀ x ∈ items.attach, RTF1 ((fun (x : {t // t ∈ items}) => putTy x.1) x) getTyAux x.1 :=
        fun ⟨t, ht⟩ _ => by
          have := List.sizeOf_lt_of_mem ht
          exact ty_rtf t
      have := rtf1_map (F := fun _ a => (pure (Ty.tuple a.toList) : GetM Ty)) (rtf1_array hi)
        (fun _ => rfl)
      simp only [List.map_subtype, List.unattach_attach, List.map_id'] at this
      show RTF _ (fun f => do let a ← getArray (getTyAux f); pure (Ty.tuple a.toList)) _
      exact this.rtf
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem rt1_ty (t : Ty) : RT1 (putTy t) getTy t := (ty_rtf t).remaining

theorem getIOTypeAux_succ (f : Nat) : getIOTypeAux (f + 1) = getTag "io type" 5 >>= fun tag =>
    match tag with
    | 0 => return .field
    | 1 => return .tuple (← getList (getIOTypeAux f))
    | 2 => return .array (← getIOTypeAux f) (← getNat)
    | 3 => return .record (← getString) (← getList (return (← getString, ← getIOTypeAux f)))
    | _ => return .enum (← getString) (← getList (return (← getString, ← getList (getIOTypeAux f)))) :=
  rfl

theorem ioType_rtf : ∀ t : IOType, RTF1 (putIOType t) getIOTypeAux t
  | .field => by
      intro b b' h
      rw [putIOType] at h
      have := rtf_tagged (q := pure ()) (Aux := getIOTypeAux) (tag := 0) (by decide) getIOTypeAux_succ
        (rt_pure IOType.field).rtf
      exact this b b' (by simpa using h)
  | .array element length => by
      rw [putIOType]
      refine rtf_tagged (tag := 2) (by decide) getIOTypeAux_succ ?_
      refine (rtf1_bind_l (ioType_rtf element) ?_).rtf
      exact (rtf1_map (F := fun _ n => (pure (IOType.array element n) : GetM IOType))
        (rt1_nat length).rtf1 (fun _ => rfl)).rtf
  | .tuple items => by
      rw [putIOType]
      refine rtf_tagged (tag := 1) (by decide) getIOTypeAux_succ ?_
      have hi : ∀ x ∈ items.attach,
          RTF1 ((fun (x : {t // t ∈ items}) => putIOType x.1) x) getIOTypeAux x.1 :=
        fun ⟨t, ht⟩ _ => by
          have := List.sizeOf_lt_of_mem ht
          exact ioType_rtf t
      have := rtf1_map (F := fun _ a => (pure (IOType.tuple a) : GetM IOType)) (rtf1_list hi)
        (fun _ => rfl)
      simp only [List.map_subtype, List.unattach_attach, List.map_id'] at this
      exact this.rtf
  | .record name fields => by
      rw [putIOType]
      refine rtf_tagged (tag := 3) (by decide) getIOTypeAux_succ ?_
      refine (rtf1_bind_l (rt1_str name).rtf1 ?_).rtf
      have hi : ∀ x ∈ fields.attach, RTF1
          ((fun (x : {p // p ∈ fields}) => do str x.1.1; putIOType x.1.2) x)
          (fun f => do return (← getString, ← getIOTypeAux f)) x.1 :=
        fun ⟨(field, type), h⟩ _ => by
          have := List.sizeOf_lt_of_mem h
          refine rtf1_bind_l (rt1_str field).rtf1 ?_
          exact (rtf1_map (F := fun _ t => (pure (field, t) : GetM (String × IOType)))
            (ioType_rtf type) (fun _ => rfl)).rtf
      have := rtf1_map (F := fun _ a => (pure (IOType.record name a) : GetM IOType)) (rtf1_list hi)
        (fun _ => rfl)
      simp only [List.map_subtype, List.unattach_attach, List.map_id'] at this
      exact this.rtf
  | .enum name constructors => by
      rw [putIOType]
      refine rtf_tagged (tag := 4) (by decide) getIOTypeAux_succ ?_
      refine (rtf1_bind_l (rt1_str name).rtf1 ?_).rtf
      have hi : ∀ x ∈ constructors.attach, RTF1
          ((fun (x : {p // p ∈ constructors}) => do
            str x.1.1; list x.1.2.attach fun y => putIOType y.1) x)
          (fun f => do return (← getString, ← getList (getIOTypeAux f))) x.1 :=
        fun ⟨(constructor, items), h₁⟩ _ => by
          refine rtf1_bind_l (rt1_str constructor).rtf1 ?_
          have hj : ∀ y ∈ items.attach,
              RTF1 ((fun (y : {t // t ∈ items}) => putIOType y.1) y) getIOTypeAux y.1 :=
            fun ⟨t, h₂⟩ _ => by
              have := List.sizeOf_lt_of_mem h₁
              have := List.sizeOf_lt_of_mem h₂
              simp only at *
              exact ioType_rtf t
          have := rtf1_map (F := fun _ a => (pure (constructor, a) : GetM (String × List IOType)))
            (rtf1_list hj) (fun _ => rfl)
          simp only [List.map_subtype, List.unattach_attach, List.map_id'] at this
          exact this.rtf
      have := rtf1_map (F := fun _ a => (pure (IOType.enum name a) : GetM IOType)) (rtf1_list hi)
        (fun _ => rfl)
      simp only [List.map_subtype, List.unattach_attach, List.map_id'] at this
      exact this.rtf
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (simp only [Prod.mk.sizeOf_spec] at *; omega)

theorem rt1_ioType (t : IOType) : RT1 (putIOType t) getIOType t := (ioType_rtf t).remaining

end Types

/-! ## Scalars -/

section Scalars

/-- The narrow scalar writer is `nat`. -/
theorem rt1_narrow (modulus v : Nat) :
    RT1 (FieldEncoding.putScalar .narrow modulus v) (getScalar false) v := by
  have e : FieldEncoding.putScalar .narrow modulus v = (pure () >>= fun _ => nat v) := rfl
  rw [e]
  intro b b' h
  obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok h
  cases h₁
  exact rt1_nat v b b' h₂

/-- The state of `getWideNat`'s loop after reading `ls` from index `i`. -/
def wideFold : Nat → List Nat → MProd Nat Nat → MProd Nat Nat
  | _, [], acc => acc
  | i, l :: ls, acc => wideFold (i + 1) ls ⟨l, acc.2 + l * 2 ^ (64 * i)⟩

theorem wideLoop_reads {f : Nat → MProd Nat Nat → GetM (ForInStep (MProd Nat Nat))}
    (hf : ∀ i l r, l < 2 ^ 64 → Reads (f i r) (tagBytes l) (.yield ⟨l, r.2 + l * 2 ^ (64 * i)⟩)) :
    ∀ (ls : List Nat) (start : Nat) (acc : MProd Nat Nat), (∀ l ∈ ls, l < 2 ^ 64) →
    Reads (forIn (List.range' start ls.length) acc f) (ls.flatMap tagBytes) (wideFold start ls acc)
  | [], start, acc, _ => by simpa [wideFold] using reads_pure (α := MProd Nat Nat) acc
  | l :: ls, start, acc, h => by
      simp only [List.length_cons, List.range'_succ, List.forIn_cons, List.flatMap_cons, wideFold]
      exact reads_bind (hf start l acc (h l (List.mem_cons_self ..)))
        (wideLoop_reads hf ls (start + 1) _ (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- The limbs `putWideNat` writes. -/
def wideLimbs (value : Nat) : List Nat :=
  (List.dropWhile (fun x => x == 0)
    (List.map (fun i => value / 2 ^ (64 * i) % 2 ^ 64) (List.range 4)).reverse).reverse

theorem putWideNat_eq {value : Nat} (h : value < 2 ^ 256) : putWideNat value = list (wideLimbs value) nat := by
  simp only [putWideNat, h, ↓reduceIte, Ixon.list, wideLimbs]
  rfl

set_option maxRecDepth 10000 in
theorem wideLimbs_spec {v : Nat} (h : v < 2 ^ 256) :
    (wideLimbs v).length ≤ 4 ∧ (∀ l ∈ wideLimbs v, l < 2 ^ 64) ∧
      (wideFold 0 (wideLimbs v) ⟨0, 0⟩).2 = v ∧
      ¬ (decide ((wideLimbs v).length > 0) && (wideFold 0 (wideLimbs v) ⟨0, 0⟩).1 == 0) = true := by
  have hv : v = v % 2 ^ 64 + (v / 2 ^ 64) % 2 ^ 64 * 2 ^ 64 + (v / 2 ^ 128) % 2 ^ 64 * 2 ^ 128 +
      (v / 2 ^ 192) % 2 ^ 64 * 2 ^ 192 := by omega
  have lt : ∀ n, n % 2 ^ 64 < 2 ^ 64 := fun n => Nat.mod_lt _ (by decide)
  simp only [wideLimbs, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one, show 64 * 2 = 128 from rfl,
    show 64 * 3 = 192 from rfl]
  generalize ha : v % 2 ^ 64 = a at hv
  generalize hb : v / 2 ^ 64 % 2 ^ 64 = b at hv
  generalize hc : v / 2 ^ 128 % 2 ^ 64 = c at hv
  generalize hd : v / 2 ^ 192 % 2 ^ 64 = d at hv
  have la := ha ▸ lt v
  have lb := hb ▸ lt (v / 2 ^ 64)
  have lc := hc ▸ lt (v / 2 ^ 128)
  have ld := hd ▸ lt (v / 2 ^ 192)
  subst hv
  by_cases d0 : d = 0
  · subst d0
    by_cases c0 : c = 0
    · subst c0
      by_cases b0 : b = 0
      · subst b0
        by_cases a0 : a = 0
        · subst a0
          simp [List.dropWhile, wideFold]
        · have a0' : (a == 0) = false := by simpa using a0
          simp [List.dropWhile, wideFold, a0']
          omega
      · have b0' : (b == 0) = false := by simpa using b0
        simp [List.dropWhile, wideFold, b0']
        omega
    · have c0' : (c == 0) = false := by simpa using c0
      simp [List.dropWhile, wideFold, c0']
      omega
  · have d0' : (d == 0) = false := by simpa using d0
    simp [List.dropWhile, wideFold, d0']
    omega

theorem wide_reads {v : Nat} (h : v < 2 ^ 256) :
    Reads getWideNat (tagBytes (wideLimbs v).length ++ (wideLimbs v).flatMap tagBytes) v := by
  obtain ⟨len, small, value, top⟩ := wideLimbs_spec h
  have r₁ := getNat_reads (n := (wideLimbs v).length) (by omega)
  refine reads_bind r₁ ?_
  simp only [len, ↓reduceIte]
  refine reads_congr (e := [] ++ ((wideLimbs v).flatMap tagBytes ++ [])) (reads_bind (reads_pure ()) ?_)
    (by simp)
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  refine reads_bind (wideLoop_reads (fun i l r hl => reads_congr (reads_bind (getNat_reads hl)
    (reads_bind (reads_pure PUnit.unit) (reads_pure _))) (by simp)) (wideLimbs v) 0 ⟨0, 0⟩ small) ?_
  generalize hw : wideFold 0 (wideLimbs v) ⟨0, 0⟩ = w at value top
  obtain ⟨high, val⟩ := w
  simp only at value top ⊢
  subst value
  simp only [top, Bool.false_eq_true, ↓reduceIte]
  exact reads_bind (reads_pure ()) (reads_pure _)

theorem rt1_putWideNat (v : Nat) : RT1 (putWideNat v) getWideNat v := by
  intro b b' hrun
  have h256 : v < 2 ^ 256 := by
    by_contra hv
    simp only [putWideNat, hv, ↓reduceIte, bind, EStateM.bind, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw] at hrun
    cases hrun
  have h₂ := hrun
  rw [putWideNat_eq h256] at h₂
  obtain ⟨zs, hzs, hq, _, rfl⟩ := list_rt (Q := fun x e => e = tagBytes x)
    (fun x _ b b' hr => ⟨tagBytes x, nat_writes x b b' hr, rfl⟩) h₂
  have flat : zs.flatMap Prod.snd = (wideLimbs v).flatMap tagBytes := by
    rw [← hzs, List.flatMap_map]
    exact List.flatMap_congr (fun z hz => hq z hz)
  refine ⟨_, rfl, by simp [tagBytes_ne_nil], ?_⟩
  rw [flat]
  exact wide_reads h256

/-- The wide scalar writer, on any value it accepts. -/
theorem rt1_wide (modulus v : Nat) :
    RT1 (FieldEncoding.putScalar .wide modulus v) (getScalar true) v := by
  intro b b' hrun
  by_cases hm : v ≥ modulus
  · have w : (FieldEncoding.wide == FieldEncoding.wide) = true := rfl
    simp only [FieldEncoding.putScalar, hm, w, decide_true, Bool.and_self, ↓reduceIte, bind,
      throw, throwThe, MonadExceptOf.throw] at hrun
    cases hrun
  have e : FieldEncoding.putScalar .wide modulus v = putWideNat v := by
    simp [FieldEncoding.putScalar, hm, FieldEncoding.put]
  rw [e] at hrun
  exact rt1_putWideNat v b b' hrun

/-- The modulus, in either encoding. -/
theorem rt1_modulus (encoding : FieldEncoding) (modulus : Nat) :
    RT1 (encoding.putModulus modulus) (getScalar (encoding == .wide)) modulus := by
  intro b b' hrun
  unfold FieldEncoding.putModulus at hrun
  cases encoding <;> simp only at hrun <;> split at hrun <;>
    (obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok hrun)
  · simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h₁
  · cases h₁
    exact rt1_nat modulus _ _ h₂
  · simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h₁
  · cases h₁
    exact rt1_putWideNat modulus _ _ h₂

end Scalars

/-! ## Instructions -/

section Instructions

variable {F : Type} [NatCast F]

/-- A writer for scalars that `getScalar wide` reads back. -/
def ScalarCodec (putScalar : Nat → PutM Unit) (wide : Bool) : Prop :=
  ∀ v, RT1 (putScalar v) (getScalar wide) v

theorem narrow_scalarCodec (modulus : Nat) :
    ScalarCodec (FieldEncoding.putScalar .narrow modulus) false := rt1_narrow modulus

theorem wide_scalarCodec (modulus : Nat) :
    ScalarCodec (FieldEncoding.putScalar .wide modulus) true := rt1_wide modulus

theorem rt1_tagged {M : Nat → GetM α} {what : String} {count : Nat} {tag : UInt8}
    (htag : tag.toNat < count) {q : PutM Unit} {y : α} (hq : RT q (M tag.toNat) y) :
    RT1 (u8 tag >>= fun _ => q) (getTag what count >>= M) y :=
  rt1_bind_l (rt1_tag what tag htag) hq

variable {putScalar : Nat → PutM Unit} {wide : Bool} {encode : F → Nat}

theorem rt1_tests (hs : ScalarCodec putScalar wide) (hcast : ∀ x, ((encode x : Nat) : F) = x)
    (tests : List (Register × F)) :
    RT1 (list tests fun (register, value) => do nat register; putScalar (encode value))
      (getTests (F := F) wide) tests := by
  refine rt1_congr (rt1_list (f := id) fun ⟨register, value⟩ _ => ?_) (List.map_id _)
  refine rt1_bind_l (rt1_nat register) ?_
  exact (rt1_map (hs (encode value)) (by simp only [hcast]; rfl)).rt

theorem rt1_instruction (hs : ScalarCodec putScalar wide) (hcast : ∀ x, ((encode x : Nat) : F) = x)
    (i : Instruction F) : RT1 (putInstructionWith putScalar encode i) (getInstruction wide) i := by
  cases i with
  | literal dest value =>
      refine rt1_tagged (tag := 0) (by decide) (rt_bind (rt1_nat dest).rt ?_)
      exact (rt1_map (hs (encode value)) (by simp only [hcast])).rt
  | copy dest source =>
      refine rt1_tagged (tag := 1) (by decide) (rt_bind (rt1_nats dest).rt ?_)
      exact rt_map (rt1_nats source).rt rfl
  | neg dest source =>
      refine rt1_tagged (tag := 2) (by decide) (rt_bind (rt1_nat dest).rt ?_)
      exact rt_map (rt1_nat source).rt rfl
  | binary dest op left right =>
      refine rt1_tagged (tag := 3) (by decide) (rt_bind (rt1_nat dest).rt ?_)
      refine rt_bind (rt1_tag "binary op" (count := 4)
        (match op with | .add => 0 | .sub => 1 | .mul => 2 | .div => 3) (by cases op <;> decide)).rt ?_
      refine rt_bind (rt1_nat left).rt ?_
      refine rt_map (rt1_nat right).rt ?_
      cases op <;> rfl
  | guard tests message =>
      refine rt1_tagged (tag := 4) (by decide) (rt_bind (rt1_tests hs hcast tests).rt ?_)
      exact rt_map (rt1_str message).rt rfl
  | branch tests target =>
      refine rt1_tagged (tag := 5) (by decide) (rt_bind (rt1_tests hs hcast tests).rt ?_)
      exact rt_map (rt1_nat target).rt rfl
  | jump target =>
      exact rt1_tagged (tag := 6) (by decide) (rt_map (rt1_nat target).rt rfl)
  | call function args dest =>
      refine rt1_tagged (tag := 7) (by decide) (rt_bind (rt1_nat function).rt ?_)
      refine rt_bind (rt1_nats args).rt ?_
      exact rt_map (rt1_nats dest).rt rfl
  | store type value dest =>
      refine rt1_tagged (tag := 8) (by decide) (rt_bind (rt1_ty type).rt ?_)
      refine rt_bind (rt1_nats value).rt ?_
      exact rt_map (rt1_nat dest).rt rfl
  | load type pointer dest =>
      refine rt1_tagged (tag := 9) (by decide) (rt_bind (rt1_ty type).rt ?_)
      refine rt_bind (rt1_nat pointer).rt ?_
      exact rt_map (rt1_nats dest).rt rfl
  | hint type keyType key dest channel =>
      refine rt1_tagged (tag := 10) (by decide) (rt_bind (rt1_str channel).rt ?_)
      refine rt_bind (rt1_ty type).rt ?_
      refine rt_bind (rt1_ty keyType).rt ?_
      refine rt_bind (rt1_nats key).rt ?_
      exact rt_map (rt1_nats dest).rt rfl
  | assertEq left right assertion =>
      refine rt1_tagged (tag := 11) (by decide) (rt_bind (rt1_nats left).rt ?_)
      refine rt_bind (rt1_nats right).rt ?_
      refine rt_bind (rt1_option (f := id) fun x _ => rt1_str x).rt ?_
      refine rt_map (rt1_bool assertion.runtimeCheck).rt ?_
      rw [Option.map_id]
      rfl
  | ret value =>
      exact rt1_tagged (tag := 12) (by decide) (rt_map (rt1_nats value).rt rfl)
  | fail message =>
      exact rt1_tagged (tag := 13) (by decide) (rt_map (rt1_str message).rt rfl)
  | ptrEq dest left right =>
      refine rt1_tagged (tag := 14) (by decide) (rt_bind (rt1_nat dest).rt ?_)
      refine rt_bind (rt1_nat left).rt ?_
      exact rt_map (rt1_nat right).rt rfl

end Instructions

/-! ## The row pool -/

section RowPool

abbrev PoolIndex := Std.HashMap (List Nat) Nat

/-- One row of `rowPool`'s inner loop: state index, references, rows. -/
def poolRow (row : List Nat) (st : MProd PoolIndex (MProd (Array Nat) (Array (List Nat)))) :
    MProd PoolIndex (MProd (Array Nat) (Array (List Nat))) :=
  match st.1[row]? with
  | some i => ⟨st.1, st.2.1.push i, st.2.2⟩
  | none => ⟨st.1.insert row st.2.2.size, st.2.1.push st.2.2.size, st.2.2.push row⟩

/-- One table of `rowPool`'s outer loop: state index, indices, rows. -/
def poolTable (table : List (List Nat))
    (st : MProd PoolIndex (MProd (Array (List Nat)) (Array (List Nat)))) :
    MProd PoolIndex (MProd (Array (List Nat)) (Array (List Nat))) :=
  let r := table.foldl (fun b a => poolRow a b) ⟨st.1, #[], st.2.2⟩
  ⟨r.1, st.2.1.push r.2.1.toList, r.2.2⟩

theorem forIn_id_yield {α β : Type} {l : List α} {init : β} {f : α → β → Id (ForInStep β)}
    (step : α → β → β) (h : ∀ a b, f a b = .yield (step a b)) :
    forIn l init f = l.foldl (fun b a => step a b) init := by
  have : f = fun a b => pure (.yield (step a b)) := funext fun a => funext fun b => h a b
  subst this
  exact List.forIn_pure_yield_eq_foldl _ _

theorem rowPool_eq (T : List (List (List Nat))) :
    rowPool T = ((T.foldl (fun b a => poolTable a b) ⟨∅, #[], #[]⟩).2.2,
      (T.foldl (fun b a => poolTable a b) ⟨∅, #[], #[]⟩).2.1.toList) := by
  unfold rowPool
  simp only [Id.run]
  rw [forIn_id_yield poolTable ?_]
  · rfl
  intro table st
  obtain ⟨index, indices, rows⟩ := st
  simp only
  rw [forIn_id_yield poolRow ?_]
  · rfl
  intro row st
  obtain ⟨index, refs, rows⟩ := st
  simp only [poolRow]
  cases index[row]? <;> rfl

/-- Every indexed row is at its index. -/
def PoolGood (rows : Array (List Nat)) (index : PoolIndex) : Prop :=
  ∀ (row : List Nat) (i : Nat), index[row]? = some i → rows[i]? = some row

/-- `rows'` keeps every row of `rows` at its index. -/
def PoolExt (rows rows' : Array (List Nat)) : Prop :=
  ∀ (i : Nat) (x : List Nat), rows[i]? = some x → rows'[i]? = some x

theorem poolExt_refl (rows : Array (List Nat)) : PoolExt rows rows := fun _ _ h => h

theorem poolExt_trans {a b c : Array (List Nat)} (h₁ : PoolExt a b) (h₂ : PoolExt b c) : PoolExt a c :=
  fun i x h => h₂ i x (h₁ i x h)

theorem poolExt_push (rows : Array (List Nat)) (row : List Nat) : PoolExt rows (rows.push row) := by
  intro i x h
  rw [Array.getElem?_push]
  have : i < rows.size := by
    by_contra hi
    rw [Array.getElem?_eq_none (by omega)] at h
    cases h
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  exact h

theorem map_lookup_ext {rows rows' : Array (List Nat)} (ext : PoolExt rows rows') :
    ∀ {refs : List Nat} {A : List (List Nat)}, refs.map (rows[·]?) = A.map some →
      refs.map (rows'[·]?) = A.map some
  | [], [], _ => rfl
  | i :: refs, a :: A, h => by
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨ext i a h.1, map_lookup_ext ext h.2⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem poolRow_spec (row : List Nat) (st : MProd PoolIndex (MProd (Array Nat) (Array (List Nat))))
    {A : List (List Nat)} (good : PoolGood st.2.2 st.1)
    (refs : st.2.1.toList.map (st.2.2[·]?) = A.map some) :
    PoolGood (poolRow row st).2.2 (poolRow row st).1 ∧ PoolExt st.2.2 (poolRow row st).2.2 ∧
      (poolRow row st).2.1.toList.map ((poolRow row st).2.2[·]?) = (A ++ [row]).map some ∧
      ∀ x ∈ (poolRow row st).2.2, x ∈ st.2.2 ∨ x = row := by
  obtain ⟨index, rs, rows⟩ := st
  simp only at good refs ⊢
  unfold poolRow
  simp only
  split
  · rename_i i hi
    refine ⟨good, poolExt_refl _, ?_, fun x hx => Or.inl hx⟩
    simp only [Array.toList_push, List.map_append, refs, List.map_cons, List.map_nil, good row i hi]
  · rename_i hi
    have ext := poolExt_push rows row
    refine ⟨?_, ext, ?_, ?_⟩
    · show PoolGood (rows.push row) (index.insert row rows.size)
      intro r i h
      rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i e
        cases h
        have e : row = r := by simpa using e
        subst e
        simp
      · exact ext i r (good r i h)
    · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, map_lookup_ext ext refs]
      simp
    · intro x hx
      rcases Array.mem_push.mp hx with h | h
      · exact Or.inl h
      · exact Or.inr h

theorem poolRows_spec : ∀ (Q : List (List Nat)) (st : MProd PoolIndex (MProd (Array Nat) (Array (List Nat))))
    {A : List (List Nat)}, PoolGood st.2.2 st.1 → st.2.1.toList.map (st.2.2[·]?) = A.map some →
    let r := Q.foldl (fun b a => poolRow a b) st
    PoolGood r.2.2 r.1 ∧ PoolExt st.2.2 r.2.2 ∧ r.2.1.toList.map (r.2.2[·]?) = (A ++ Q).map some ∧
      ∀ x ∈ r.2.2, x ∈ st.2.2 ∨ x ∈ Q
  | [], st, A, good, refs => by
      simp only [List.foldl_nil, List.append_nil]
      exact ⟨good, poolExt_refl _, refs, fun x hx => Or.inl hx⟩
  | row :: Q, st, A, good, refs => by
      obtain ⟨g₁, e₁, r₁, m₁⟩ := poolRow_spec row st good refs
      obtain ⟨g₂, e₂, r₂, m₂⟩ := poolRows_spec Q (poolRow row st) g₁ r₁
      simp only [List.foldl_cons, List.append_assoc, List.singleton_append] at g₂ e₂ r₂ m₂ ⊢
      refine ⟨g₂, poolExt_trans e₁ e₂, r₂, fun x hx => ?_⟩
      rcases m₂ x hx with h | h
      · rcases m₁ x h with h | rfl
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem poolTables_spec : ∀ (T : List (List (List Nat)))
    (st : MProd PoolIndex (MProd (Array (List Nat)) (Array (List Nat)))) {P : List (List (List Nat))},
    PoolGood st.2.2 st.1 →
    List.Forall₂ (fun t ix => ix.map (st.2.2[·]?) = t.map some) P st.2.1.toList →
    (∀ x ∈ st.2.2, ∃ t ∈ P, x ∈ t) →
    let r := T.foldl (fun b a => poolTable a b) st
    List.Forall₂ (fun t ix => ix.map (r.2.2[·]?) = t.map some) (P ++ T) r.2.1.toList ∧
      ∀ x ∈ r.2.2, ∃ t ∈ P ++ T, x ∈ t
  | [], st, P, _, f, m => by simpa using ⟨f, m⟩
  | table :: T, st, P, good, f, m => by
      obtain ⟨g₁, e₁, r₁, m₁⟩ := poolRows_spec table ⟨st.1, #[], st.2.2⟩ (A := []) good (by simp)
      simp only [List.nil_append] at r₁
      have f' : List.Forall₂ (fun t ix => ix.map ((poolTable table st).2.2[·]?) = t.map some)
          (P ++ [table]) (poolTable table st).2.1.toList := by
        simp only [poolTable, Array.toList_push]
        exact List.rel_append (f.imp fun t ix h => map_lookup_ext e₁ h) (List.Forall₂.cons r₁ .nil)
      have m' : ∀ x ∈ (poolTable table st).2.2, ∃ t ∈ P ++ [table], x ∈ t := by
        intro x hx
        rcases m₁ x hx with h | h
        · obtain ⟨t, ht, hx⟩ := m x h
          exact ⟨t, List.mem_append_left _ ht, hx⟩
        · exact ⟨table, by simp, h⟩
      have := poolTables_spec T (poolTable table st) g₁ f' m'
      simpa using this

/-- `rowPool T` lists rows that occur in `T`, and its `j`-th reference list
looks up the rows of the `j`-th table. -/
theorem rowPool_spec (T : List (List (List Nat))) :
    List.Forall₂ (fun t ix => ix.map ((rowPool T).1[·]?) = t.map some) T (rowPool T).2 ∧
      ∀ x ∈ (rowPool T).1, ∃ t ∈ T, x ∈ t := by
  rw [rowPool_eq]
  have := poolTables_spec T ⟨∅, #[], #[]⟩ (P := [])
    (by intro r i h; simp at h) (by simp) (by simp)
  simpa using this

end RowPool

/-! ## The program section -/

section Program

variable {F : Type} [NatCast F]

theorem scalarCodec_of (encoding : FieldEncoding) (modulus : Nat) :
    ScalarCodec (encoding.putScalar modulus) (encoding == .wide) := by
  cases encoding
  · exact narrow_scalarCodec modulus
  · exact wide_scalarCodec modulus

theorem forIn_check_reads {α : Type} {xs : Array α} {body : α → PUnit → GetM (ForInStep PUnit)}
    (h : ∀ x ∈ xs, Reads (body x ()) [] (.yield ())) : Reads (forIn xs () body) [] () := by
  rw [← Array.forIn_toList]
  have h' : ∀ x ∈ xs.toList, Reads (body x ()) [] (.yield ()) := fun x hx => h x (Array.mem_toList_iff.mp hx)
  clear h
  generalize xs.toList = l at h' ⊢
  induction l with
  | nil => exact reads_pure ()
  | cons x xs ih =>
      simp only [List.forIn_cons]
      exact reads_bind (e₂ := []) (h' x (List.mem_cons_self ..))
        (ih fun y hy => h' y (List.mem_cons_of_mem _ hy))

omit [NatCast F] in
theorem mapM_lookup_reads {pool : Array (List Nat)} {onNone : Nat → GetM (List F)}
    {conv : List Nat → List F} :
    ∀ {ix : List Nat} {R : List (List Nat)}, ix.map (pool[·]?) = R.map some →
    Reads (ix.mapM fun i => match pool[i]? with
      | some r => pure (conv r)
      | none => onNone i) [] (R.map conv)
  | [], [], _ => reads_pure _
  | i :: ix, r :: R, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mapM_cons, h.1, List.map_cons]
      exact reads_bind (e₁ := []) (reads_pure _)
        (reads_bind (e₁ := []) (mapM_lookup_reads h.2) (reads_pure _))
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem forall₂_zip_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ p ∈ l₁.zip l₂, R p.1 p.2
  | [], [], _, p, hp => by simp at hp
  | a :: l₁, b :: l₂, .cons h t, p, hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h
      · exact forall₂_zip_mem t p hp

theorem rt_tail {α β : Type} {p : PutM Unit} {g : GetM α} {f : α → GetM β} {x : α} {y : β}
    (hp : RT p g x) (hf : Reads (f x) [] y) : RT p (g >>= f) y := by
  intro b b' h
  obtain ⟨e, rfl, r⟩ := hp b b' h
  exact ⟨e, rfl, by simpa using reads_bind r hf⟩

theorem reads_value {α : Type} {g : GetM α} {e : List UInt8} {x y : α} (h : Reads g e x) (he : x = y) :
    Reads g e y := he ▸ h

theorem rt_if_pos {α : Type} {c : Prop} [Decidable c] {p : PutM Unit} {A B : GetM α} {y : α} (hc : c)
    (h : RT p A y) : RT p (if c then A else B) y := by
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
  exact h

theorem rt_fail {α : Type} {g : GetM α} {x : α} (msg : String) : RT1 (throw msg : PutM Unit) g x := by
  intro b b' h
  simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

/-- The interface the program section carries for `entry`. -/
def entryInterface (exported : Export F) (entry : String × Nat) : Interface :=
  match exported.interfaces.find? (·.name == entry.1) with
  | some i => ⟨entry.1, i.inputs, i.output⟩
  | none => ⟨entry.1, [], none⟩

/-- `getProgram` reads back the program section `Export.putProgramWithEncoding`
wrote: the same bytecode, and the entries' interfaces in entry order. -/
theorem program_rt (exported : Export F) (encoding : FieldEncoding) (modulus : Nat) (encode : F → Nat)
    (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < modulus) :
    RT1 (exported.putProgramWithEncoding encoding modulus encode)
      (getProgram (F := F) (encoding == .wide) modulus)
      { bytecode := exported.bytecode,
        interfaces := exported.bytecode.entries.map (entryInterface exported) } := by
  have hs := scalarCodec_of encoding modulus
  simp only [Export.putProgramWithEncoding, getProgram]
  refine rt1_bind_l (rt1_nat _) (rt_if_pos (by decide) (rt_skip (reads_pure ()) ?_))
  refine rt_bind (rt1_modulus encoding modulus).rt (rt_if_pos (by simp) (rt_skip (reads_pure ()) ?_))
  -- functions
  refine rt_bind (rt1_list_id fun func _ => ?_).rt ?_
  · refine rt1_bind_l (rt1_str func.name) (rt_bind (rt1_list_id fun t _ => rt1_ty t).rt ?_)
    refine rt_bind (rt1_ty func.result).rt (rt_bind (rt1_nat func.registers).rt ?_)
    refine rt_map (rt1_array (f := id) fun i _ => rt1_instruction hs hcast i).rt ?_
    simp only [Array.map_id]
  -- enums
  refine rt_bind (rt1_list_id fun decl _ => ?_).rt ?_
  · refine rt1_bind_l (rt1_str decl.name) ?_
    refine rt_map (rt1_list_id fun c _ => ?_).rt rfl
    refine rt1_bind_l (rt1_str c.name) ?_
    exact rt_map (rt1_list_id fun t _ => rt1_ty t).rt rfl
  -- the row pool
  obtain ⟨spec, members⟩ := rowPool_spec (exported.bytecode.tables.map fun table => table.rows.map (·.map encode))
  refine rt_bind (rt1_array (f := id) fun row _ => rt1_list_id fun v _ => hs v).rt ?_
  simp only [Array.map_id]
  refine rt_skip (forIn_check_reads fun r hr => ?_) ?_
  · obtain ⟨t, ht, hrt⟩ := members r hr
    obtain ⟨table, _, rfl⟩ := List.mem_map.mp ht
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp hrt
    have : (row.map encode).all (· < modulus) = true := by simp [hlt]
    simp only [this, ↓reduceIte]
    exact reads_bind (reads_pure ()) (reads_pure _)
  -- tables
  have rel := List.forall₂_map_left_iff.mp spec
  have len := rel.length_eq
  refine rt_bind (rt_congr (rt1_list (f := Prod.fst) fun p hp => ?_).rt
    (List.map_fst_zip (by omega))) ?_
  · obtain ⟨table, ix⟩ := p
    have hix := forall₂_zip_mem rel _ hp
    simp only at hix
    refine rt1_bind_l (rt1_str table.name) (rt_bind (rt1_ty table.type).rt ?_)
    refine rt_tail (rt1_nats ix).rt (reads_bind (e₁ := []) (mapM_lookup_reads hix) ?_)
    refine reads_value (reads_pure _) ?_
    cases table
    simp only [List.map_map, Function.comp_def]
    congr 1
    refine (List.map_congr_left fun x _ => ?_).trans (List.map_id _)
    simp only [id]
    simp only [List.map_id', List.bind_eq_flatMap, List.pure_def]
    clear * - hcast
    induction x with
    | nil => rfl
    | cons a x ih => simp only [List.map_cons, List.flatMap_cons, hcast, ih, List.singleton_append]
  -- maps
  refine rt_bind (rt1_list_id fun m _ => ?_).rt ?_
  · refine rt1_bind_l (rt1_str m.name) (rt_bind (rt1_list_id fun t _ => rt1_ty t).rt ?_)
    refine rt_bind (rt1_ty m.result).rt (rt_bind (rt1_nat m.input).rt ?_)
    exact rt_map (rt1_nat m.output).rt rfl
  -- entries
  refine rt_map (rt1_list (f := fun e => (e, entryInterface exported e)) fun e _ => ?_).rt ?_
  · obtain ⟨name, function⟩ := e
    simp only
    cases hfind : exported.interfaces.find? (·.name == name) with
    | none => exact rt_fail _
    | some i =>
        refine rt1_bind_l (rt1_str name) (rt_bind (rt1_nat function).rt ?_)
        refine rt_bind (rt1_list_id fun t _ => rt1_ioType t).rt ?_
        refine rt_map (rt1_option (f := id) fun t _ => rt1_ioType t).rt ?_
        simp only [entryInterface, hfind, Option.map_id]
        rfl
  · simp only [List.map_map, Function.comp_def, List.map_id']

end Program

/-! ## Packages -/

section Package

variable {F : Type} [NatCast F]

theorem at_prefix (b : ByteArray) (e rest : List UInt8) :
    At (b ++ ⟨(e ++ rest).toArray⟩) b.size e :=
  (at_append (at_written b (e ++ rest))).1

theorem option_appends (trace : Option ByteArray) {b b' : ByteArray}
    (h : option trace raw b = .ok () b') : ∃ e : List UInt8, b' = b ++ ⟨e.toArray⟩ := by
  cases trace with
  | none => exact ⟨[0], u8_writes 0 b b' h⟩
  | some t =>
      obtain ⟨b₁, h₁, h₂⟩ := bind_unit_ok h
      have w₁ := u8_writes 1 _ _ h₁
      have w₂ := raw_writes t _ _ h₂
      subst w₁ w₂
      exact ⟨_, append_assoc' ..⟩

theorem ok_bind {α β : Type} {x : GetM α} {f : α → GetM β} {s s₁ : Cursor} {a : α}
    (hx : x s = .ok a s₁) : (x >>= f) s = f a s₁ := by
  show EStateM.bind x f s = _
  simp only [EStateM.bind, hx]

theorem estate_bind_ok {σ ε α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β} {s s' : σ} {r : β}
    (h : EStateM.bind x f s = .ok r s') : ∃ a s₁, x s = .ok a s₁ ∧ f a s₁ = .ok r s' := by
  simp only [EStateM.bind] at h
  split at h
  · rename_i a s₁ hx
    exact ⟨a, s₁, hx, h⟩
  · cases h

/-- `getPackage` returns the program it read after the magic and version. -/
theorem decode_program {bytes : ByteArray} {modulus ver p₁ p₂ : Nat} {w : Bool} {prog : Export F}
    {s₃ c : Cursor} {pkg : Package F} (hv : (ver == 2 || ver == 3) = true) (hw : (ver == 3) = w)
    (run₁ : getRaw 8 ⟨bytes, 0⟩ = .ok Artifact.packageMagic ⟨bytes, p₁⟩)
    (run₂ : getNat ⟨bytes, p₁⟩ = .ok ver ⟨bytes, p₂⟩)
    (run₃ : getProgram w modulus ⟨bytes, p₂⟩ = .ok prog s₃)
    (hrun : getPackage modulus { bytes } = .ok pkg c) : pkg.program = prog := by
  have magic : (Artifact.packageMagic.data == Artifact.packageMagic.data) = true := by simp
  unfold getPackage at hrun
  rw [show ({ bytes } : Cursor) = ⟨bytes, 0⟩ from rfl, ok_bind run₁] at hrun
  rw [ite_eq_left_of_eq_true _ _ (eq_true magic)] at hrun
  rw [ok_bind (by rfl)] at hrun
  beta_reduce at hrun
  rw [ok_bind run₂] at hrun
  rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at hrun
  rw [ok_bind (by rfl)] at hrun
  beta_reduce at hrun
  simp only [hw] at hrun
  rw [ok_bind run₃] at hrun
  simp only [bind, EStateM.bind] at hrun
  split at hrun
  case h_2 => cases hrun
  rename_i a s _
  split at hrun
  case h_2 =>
    simp only [fail, throw, throwThe, MonadExceptOf.throw, EStateM.throw, bind, EStateM.bind] at hrun
    split at hrun <;> cases hrun
  obtain ⟨_, _, -, hrun⟩ := estate_bind_ok hrun
  obtain ⟨_, _, -, hrun⟩ := estate_bind_ok hrun
  obtain ⟨_, _, -, hrun⟩ := estate_bind_ok hrun
  simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
  rw [← hrun.1]

/-- A package that the compiler's writer produced and `decodePackage` accepts
carries the exported bytecode in its program section. -/
theorem program_of_decode {encoding : FieldEncoding} {exported : Export F} {modulus : Nat}
    {encode : F → Nat} {trace : Option ByteArray} {bytes : ByteArray} {pkg : Package F}
    (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < modulus)
    (written : Ixon.run (Artifact.putPackageWithEncoding encoding exported modulus encode trace) =
      .ok bytes)
    (decoded : decodePackage modulus bytes = .ok pkg) :
    pkg.program.bytecode = exported.bytecode := by
  -- The bytes, piece by piece.
  unfold Ixon.run at written
  split at written
  case h_2 => cases written
  rename_i u b₀ hput
  cases written
  have size₀ : (ByteArray.emptyWithCapacity (1 <<< 16)).size = 0 := rfl
  unfold Artifact.putPackageWithEncoding at hput
  obtain ⟨b₁, h₁, hput⟩ := bind_unit_ok hput
  obtain ⟨b₂, h₂, hput⟩ := bind_unit_ok hput
  obtain ⟨b₃, h₃, h₄⟩ := bind_unit_ok hput
  obtain ⟨e₁, rfl, _, r₁⟩ := rt1_raw8 Artifact.packageMagic rfl _ _ h₁
  obtain ⟨e₂, rfl, _, r₂⟩ := rt1_nat _ _ _ h₂
  obtain ⟨e₃, rfl, _, r₃⟩ := program_rt exported encoding modulus encode hcast hlt _ _ h₃
  obtain ⟨e₄, rfl⟩ := option_appends trace h₄
  simp only [append_assoc', List.append_assoc] at decoded
  generalize ByteArray.emptyWithCapacity (1 <<< 16) = b₀ at size₀ decoded
  have at₂ := at_append (at_append (at_written b₀ (e₁ ++ (e₂ ++ (e₃ ++ e₄))))).2
  have at₃ := (at_append at₂.2).1
  have run₁ := r₁ _ _ (at_prefix b₀ e₁ (e₂ ++ (e₃ ++ e₄)))
  have run₂ := r₂ _ _ at₂.1
  have run₃ := r₃ _ _ at₃
  simp only [EStateM.run, size₀, Nat.zero_add] at run₁ run₂ run₃
  unfold decodePackage Ixon.decode at decoded
  split at decoded
  case h_2 => cases decoded
  rename_i pkg' cursor hrun
  split at decoded
  case isFalse => cases decoded
  cases decoded
  simp only [EStateM.run] at hrun
  cases encoding
  · rw [decode_program (by decide) rfl run₁ run₂ run₃ hrun]
  · rw [decode_program (by decide) rfl run₁ run₂ run₃ hrun]

end Package

end Aiur.Tiling.Ixa
