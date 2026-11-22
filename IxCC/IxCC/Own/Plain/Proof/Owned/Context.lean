import IxCC.Own.Plain.Owned
import IxCC.Src.Proof.NatMap

/-! # The ownership checker's context algebra

What each context operation does to the five views the proof reads: immediates (`isImm`), tokens
(`tokens`, `total`), borrows (`brw`, `epoch`) and the known variables (`known`). `Tokens Γ toks`
relates the context to a list with one entry per token; the operations act on it as list
operations (`erase` for a consumed token, `cons` for a new one, `filter` for tokens that turn out
to be vacuous). No heap here. -/

set_option autoImplicit false

namespace IxCC.Src.NatMap

theorem get?_erase {α : Type} (m : NatMap α) (k k' : Nat) :
    (m.erase k).get? k' = if k' = k then none else m.get? k' :=
  get?_setF (k + 1) m k none k' (Nat.lt_succ_self k)

theorem get?_ofList_none {α : Type} {xs : List (Nat × α)} (hn : (xs.map (·.1)).Nodup)
    {k : Nat} (hk : k ∉ xs.map (·.1)) : (ofList xs).get? k = none := by
  have h := (get?_foldl_insert (f := fun m (p : Nat × α) => m.insert p.1 p.2) (fun _ _ => rfl)
    xs .leaf hn).1 k hk
  exact h

end IxCC.Src.NatMap

namespace IxCC.Own.Plain

open IxCC.Fir (Var JoinId Arg Rhs)

namespace Ctx

variable (Γ : Ctx) (x y : Var)

theorem tokens_eq : Γ.tokens y = (Γ.own.get? y).getD 0 := rfl

@[simp] theorem isImm_addOwn (n : Nat) : (Γ.addOwn x n).isImm y = Γ.isImm y := rfl
@[simp] theorem brw_addOwn (n : Nat) : (Γ.addOwn x n).brw = Γ.brw := rfl
@[simp] theorem epoch_addOwn (n : Nat) : (Γ.addOwn x n).epoch = Γ.epoch := rfl
@[simp] theorem total_addOwn (n : Nat) : (Γ.addOwn x n).total = Γ.total + n := rfl
theorem tokens_addOwn (n : Nat) :
    (Γ.addOwn x n).tokens y = if y = x then Γ.tokens x + n else Γ.tokens y := by
  simp only [tokens_eq, addOwn, Src.NatMap.get?_insert]
  split <;> simp_all [tokens_eq]
theorem ownHas_addOwn (n : Nat) :
    (Γ.addOwn x n).own.contains y = (decide (y = x) || Γ.own.contains y) := by
  simp only [addOwn, Src.NatMap.contains, Src.NatMap.get?_insert]
  split <;> simp_all

@[simp] theorem isImm_release : Γ.release.isImm y = Γ.isImm y := rfl
@[simp] theorem own_release : Γ.release.own = Γ.own := rfl
@[simp] theorem brw_release : Γ.release.brw = Γ.brw := rfl
@[simp] theorem total_release : Γ.release.total = Γ.total := rfl
@[simp] theorem epoch_release : Γ.release.epoch = Γ.epoch + 1 := rfl
@[simp] theorem tokens_release : Γ.release.tokens y = Γ.tokens y := rfl

@[simp] theorem isImm_setBorrow : (Γ.setBorrow x).isImm y = Γ.isImm y := rfl
@[simp] theorem own_setBorrow : (Γ.setBorrow x).own = Γ.own := rfl
@[simp] theorem total_setBorrow : (Γ.setBorrow x).total = Γ.total := rfl
@[simp] theorem epoch_setBorrow : (Γ.setBorrow x).epoch = Γ.epoch := rfl
@[simp] theorem tokens_setBorrow : (Γ.setBorrow x).tokens y = Γ.tokens y := rfl
theorem brw_setBorrow :
    (Γ.setBorrow x).brw.get? y = if y = x then some Γ.epoch else Γ.brw.get? y := by
  simp only [setBorrow, Src.NatMap.get?_insert]

theorem isImm_setImm : (Γ.setImm x).isImm y = (decide (y = x) || Γ.isImm y) := by
  simp only [isImm, setImm, Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
  split <;> simp_all
theorem tokens_setImm : (Γ.setImm x).tokens y = if y = x then 0 else Γ.tokens y := by
  simp only [tokens_eq, setImm, Src.NatMap.get?_erase]
  split <;> rfl
theorem brw_setImm : (Γ.setImm x).brw.get? y = if y = x then none else Γ.brw.get? y := by
  simp only [setImm, Src.NatMap.get?_erase]
@[simp] theorem epoch_setImm : (Γ.setImm x).epoch = Γ.epoch := rfl
@[simp] theorem total_setImm : (Γ.setImm x).total = Γ.total - Γ.tokens x := rfl
theorem ownHas_setImm : (Γ.setImm x).own.contains y = (!decide (y = x) && Γ.own.contains y) := by
  simp only [setImm, Src.NatMap.contains, Src.NatMap.get?_erase]
  split <;> simp_all

theorem borrowed_eq : Γ.borrowed y = (Γ.brw.get? y == some Γ.epoch) := rfl

theorem avail_eq : Γ.avail y = (Γ.isImm y || decide (0 < Γ.tokens y) || Γ.borrowed y) := rfl

theorem known_eq : Γ.known y =
    (Γ.isImm y || Γ.own.contains y || (Γ.brw.get? y).isSome) := rfl

/-! ## The consuming operations -/

/-- What a successful `take` did. -/
theorem take_ok {Γ Γ' : Ctx} {x : Var} (h : Γ.take x = .ok Γ') :
    (Γ.isImm x = true ∧ Γ' = Γ) ∨
      (Γ.isImm x = false ∧ ∃ n, Γ.own.get? x = some (n + 1) ∧
        Γ' = { Γ with own := Γ.own.insert x n, total := Γ.total - 1 }) := by
  unfold take at h
  cases hi : Γ.isImm x with
  | true => simp only [hi, ↓reduceIte, Except.ok.injEq] at h; exact Or.inl ⟨rfl, h.symm⟩
  | false =>
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    refine Or.inr ⟨rfl, ?_⟩
    split at h
    · next n hn => exact ⟨n, hn, (Except.ok.inj h).symm⟩
    · split at h <;> (try split at h) <;> cases h

/-- A weaker context: the same immediates, borrows and epoch, no more tokens. -/
structure Weaker (Γ' Γ : Ctx) : Prop where
  imm : Γ'.imm = Γ.imm
  brw : Γ'.brw = Γ.brw
  epoch : Γ'.epoch = Γ.epoch
  tokens : ∀ y, Γ'.tokens y ≤ Γ.tokens y
  ownHas : ∀ y, Γ'.own.contains y = true → Γ.own.contains y = true

theorem Weaker.refl (Γ : Ctx) : Weaker Γ Γ := ⟨rfl, rfl, rfl, fun _ => Nat.le_refl _, fun _ h => h⟩

theorem Weaker.trans {Γ₁ Γ₂ Γ₃ : Ctx} (h₁ : Weaker Γ₁ Γ₂) (h₂ : Weaker Γ₂ Γ₃) : Weaker Γ₁ Γ₃ :=
  ⟨h₁.imm.trans h₂.imm, h₁.brw.trans h₂.brw, h₁.epoch.trans h₂.epoch,
    fun y => Nat.le_trans (h₁.tokens y) (h₂.tokens y), fun y h => h₂.ownHas y (h₁.ownHas y h)⟩

theorem Weaker.isImm {Γ' Γ : Ctx} (h : Weaker Γ' Γ) (y : Var) : Γ'.isImm y = Γ.isImm y := by
  simp only [Ctx.isImm, h.imm]

theorem Weaker.borrowed {Γ' Γ : Ctx} (h : Weaker Γ' Γ) (y : Var) : Γ'.borrowed y = Γ.borrowed y := by
  simp only [Ctx.borrowed, h.brw, h.epoch]

theorem Weaker.avail {Γ' Γ : Ctx} (h : Weaker Γ' Γ) {y : Var} (ha : Γ'.avail y = true) :
    Γ.avail y = true := by
  have ht := h.tokens y
  simp only [avail_eq, h.isImm, h.borrowed, Bool.or_eq_true, decide_eq_true_eq] at ha ⊢
  rcases ha with (h1 | h2) | h3
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (Nat.lt_of_lt_of_le h2 ht))
  · exact Or.inr h3

theorem Weaker.known {Γ' Γ : Ctx} (h : Weaker Γ' Γ) {y : Var} (hk : Γ'.known y = true) :
    Γ.known y = true := by
  simp only [known_eq, Bool.or_eq_true] at hk ⊢
  rw [h.isImm y, h.brw] at hk
  rcases hk with (h1 | h2) | h3
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (h.ownHas y h2))
  · exact Or.inr h3

theorem take_weaker {Γ Γ' : Ctx} {x : Var} (h : Γ.take x = .ok Γ') : Weaker Γ' Γ := by
  rcases take_ok h with ⟨_, rfl⟩ | ⟨_, n, hn, rfl⟩
  · exact Weaker.refl _
  · refine ⟨rfl, rfl, rfl, fun y => ?_, fun y hy => ?_⟩
    · simp only [tokens_eq, Src.NatMap.get?_insert]
      split
      · next he => subst he; simp [hn]
      · exact Nat.le_refl _
    · simp only [Src.NatMap.contains, Src.NatMap.get?_insert] at hy ⊢
      split at hy
      · next he => subst he; simp [hn]
      · exact hy

theorem takeArg_weaker {Γ Γ' : Ctx} {a : Arg} (h : Γ.takeArg a = .ok Γ') : Weaker Γ' Γ := by
  cases a with
  | var x => exact take_weaker h
  | lit _ | erased => cases h; exact Weaker.refl _

theorem takeArgs_weaker : ∀ {Γ Γ' : Ctx} {args : List Arg}, Γ.takeArgs args = .ok Γ' → Weaker Γ' Γ
  | Γ, Γ', [], h => by cases h; exact Weaker.refl _
  | Γ, Γ', a :: as, h => by
    simp only [takeArgs] at h
    cases ha : Γ.takeArg a with
    | error e => rw [ha] at h; cases h
    | ok Γ₁ =>
      rw [ha] at h
      exact (takeArgs_weaker h).trans (takeArg_weaker ha)

theorem takeVars_weaker : ∀ {Γ Γ' : Ctx} {xs : List Var}, Γ.takeVars xs = .ok Γ' → Weaker Γ' Γ
  | Γ, Γ', [], h => by cases h; exact Weaker.refl _
  | Γ, Γ', x :: xs, h => by
    simp only [takeVars] at h
    cases hx : Γ.take x with
    | error e => rw [hx] at h; cases h
    | ok Γ₁ =>
      rw [hx] at h
      exact (takeVars_weaker h).trans (take_weaker hx)

theorem need_avail {Γ : Ctx} {x : Var} {what : String} (h : Γ.need x what = .ok ()) :
    Γ.avail x = true := by
  unfold need at h
  split at h
  · assumption
  · split at h <;> cases h

theorem needArgs_avail : ∀ {Γ : Ctx} {args : List Arg}, Γ.needArgs args = .ok () →
    ∀ x, Arg.var x ∈ args → Γ.avail x = true
  | _, [], _, _, hx => by cases hx
  | Γ, a :: as, h, x, hx => by
    cases a with
    | var z =>
      simp only [needArgs] at h
      cases hz : Γ.need z "read by a primitive" with
      | error e => rw [hz] at h; cases h
      | ok u =>
        rw [hz] at h
        rcases List.mem_cons.mp hx with he | hx
        · cases he; exact need_avail hz
        · exact needArgs_avail h x hx
    | lit _ | erased =>
      simp only [needArgs] at h
      rcases List.mem_cons.mp hx with he | hx
      · cases he
      · exact needArgs_avail h x hx

theorem needCaptured_avail : ∀ {Γ : Ctx} {j : JoinId} {cs : List Var},
    Γ.needCaptured j cs = .ok () → ∀ c, c ∈ cs → Γ.avail c = true
  | _, _, [], _, _, hc => by cases hc
  | Γ, j, c :: cs, h, x, hx => by
    simp only [needCaptured] at h
    cases hc : Γ.need c s!"captured by join j{j}" with
    | error e => rw [hc] at h; cases h
    | ok u =>
      rw [hc] at h
      rcases List.mem_cons.mp hx with he | hx
      · subst he; exact need_avail hc
      · exact needCaptured_avail h x hx

/-! ## Increments and decrements -/

theorem inc_ok {Γ Γ' : Ctx} {x : Var} {n : Nat} (h : Γ.inc x n = .ok Γ') :
    n = 1 ∧ ((Γ.isImm x = true ∧ Γ' = Γ) ∨
      (Γ.isImm x = false ∧ 0 < Γ.tokens x ∧ Γ' = Γ.addOwn x 1) ∨
      (Γ.isImm x = false ∧ Γ.tokens x = 0 ∧ Γ.borrowed x = true ∧
        Γ' = ({ Γ with brw := Γ.brw.erase x } : Ctx).addOwn x 1)) := by
  unfold inc at h
  by_cases hn : n = 1
  · subst hn
    refine ⟨rfl, ?_⟩
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    cases hi : Γ.isImm x with
    | true => simp only [hi, ↓reduceIte, Except.ok.injEq] at h; exact Or.inl ⟨rfl, h.symm⟩
    | false =>
      simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
      by_cases ht : 0 < Γ.tokens x
      · simp only [ht, ↓reduceIte, Except.ok.injEq] at h
        exact Or.inr (Or.inl ⟨rfl, ht, h.symm⟩)
      · simp only [ht, ↓reduceIte] at h
        cases hb : Γ.borrowed x with
        | true =>
          simp only [hb, ↓reduceIte, Except.ok.injEq] at h
          exact Or.inr (Or.inr ⟨rfl, by omega, rfl, h.symm⟩)
        | false =>
          simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
          split at h <;> cases h
  · have : (n != 1) = true := by simpa using hn
    simp only [this, ↓reduceIte] at h
    cases h

theorem dec_ok {Γ Γ' : Ctx} {x : Var} (h : Γ.dec x = .ok Γ') :
    ∃ Γ₁, Γ.take x = .ok Γ₁ ∧ Γ' = Γ₁.release := by
  unfold dec at h
  cases ht : Γ.take x with
  | error e => rw [ht] at h; cases h
  | ok Γ₁ => rw [ht] at h; exact ⟨Γ₁, rfl, (Except.ok.inj h).symm⟩

/-! ## Tokens -/

/-- `toks` lists the context's tokens, one entry per token. -/
structure Tokens (Γ : Ctx) (toks : List Var) : Prop where
  count : ∀ y, toks.count y = Γ.tokens y
  total : Γ.total = toks.length

theorem Tokens.mem {Γ : Ctx} {toks : List Var} (h : Tokens Γ toks) {y : Var}
    (hy : 0 < Γ.tokens y) : y ∈ toks := by
  rw [← h.count y] at hy
  exact List.count_pos_iff.mp hy

theorem Tokens.take {Γ Γ' : Ctx} {toks : List Var} {x : Var} (h : Tokens Γ toks)
    (ht : Γ.take x = .ok Γ') (hi : Γ.isImm x = false) :
    x ∈ toks ∧ 0 < Γ.tokens x ∧ Tokens Γ' (toks.erase x) := by
  rcases take_ok ht with ⟨hi', _⟩ | ⟨_, n, hn, rfl⟩
  · rw [hi] at hi'; cases hi'
  · have hpos : 0 < Γ.tokens x := by simp [tokens_eq, hn]
    have hm := h.mem hpos
    refine ⟨hm, hpos, fun y => ?_, ?_⟩
    · simp only [tokens_eq, Src.NatMap.get?_insert]
      by_cases hy : y = x
      · subst hy
        rw [List.count_erase_self, h.count, tokens_eq, hn]
        simp
      · rw [if_neg hy, List.count_erase_of_ne hy, h.count, tokens_eq]
    · rw [List.length_erase_of_mem hm, ← h.total]

theorem Tokens.addOwn {Γ : Ctx} {toks : List Var} (h : Tokens Γ toks) (x : Var) :
    Tokens (Γ.addOwn x 1) (x :: toks) := by
  refine ⟨fun y => ?_, ?_⟩
  · rw [tokens_addOwn, List.count_cons, h.count]
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, Ne.symm hy]
  · simp [h.total]

theorem count_filter_ne (x : Var) : ∀ (zs : List Var) (y : Var),
    (zs.filter (fun z => z != x)).count y = if y = x then 0 else zs.count y
  | [], y => by simp
  | z :: zs, y => by
    have ih := count_filter_ne x zs y
    by_cases hz : z = x
    · subst hz
      have hf : (z :: zs).filter (fun w => w != z) = zs.filter (fun w => w != z) :=
        List.filter_cons_of_neg (by simp)
      rw [hf, ih, List.count_cons]
      by_cases hy : y = z
      · simp [hy]
      · have hzy : (z == y) = false := beq_eq_false_iff_ne.mpr (fun h => hy h.symm)
        simp [hy, hzy]
    · have hf : (z :: zs).filter (fun w => w != x) = z :: zs.filter (fun w => w != x) := by
        simp [List.filter_cons, hz]
      rw [hf, List.count_cons, ih, List.count_cons]
      by_cases hy : y = x
      · have hzy : (z == y) = false := by
          simp only [beq_eq_false_iff_ne]; intro he; exact hz (he.trans hy)
        simp [hy, hzy, hz]
      · simp [hy]

theorem length_filter_ne (x : Var) : ∀ (zs : List Var),
    (zs.filter (fun z => z != x)).length + zs.count x = zs.length
  | [] => by simp
  | z :: zs => by
    have ih := length_filter_ne x zs
    by_cases hz : z = x
    · subst hz
      have hf : (z :: zs).filter (fun w => w != z) = zs.filter (fun w => w != z) :=
        List.filter_cons_of_neg (by simp)
      rw [hf, List.count_cons]
      simp only [beq_self_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have hf : (z :: zs).filter (fun w => w != x) = z :: zs.filter (fun w => w != x) := by
        simp [List.filter_cons, hz]
      have hzx : (z == x) = false := by simpa using hz
      rw [hf, List.count_cons, hzx]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega

theorem count_nodup {y : Var} : ∀ {xs : List Var}, xs.Nodup → xs.count y = if y ∈ xs then 1 else 0
  | [], _ => by simp
  | z :: zs, hn => by
    rw [List.nodup_cons] at hn
    rw [List.count_cons, count_nodup hn.2]
    by_cases hy : y = z
    · subst hy
      have h0 : (y == y) = true := beq_self_eq_true y
      rw [h0, if_neg hn.1, if_pos List.mem_cons_self]
      simp
    · have hzy : (z == y) = false := beq_eq_false_iff_ne.mpr (fun h => hy h.symm)
      rw [hzy]
      by_cases hm : y ∈ zs
      · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]; rfl
      · have hm' : y ∉ z :: zs := by
          intro h; rcases List.mem_cons.mp h with h | h
          · exact hy h
          · exact hm h
        rw [if_neg hm, if_neg hm']; rfl

theorem Tokens.setImm {Γ : Ctx} {toks : List Var} (h : Tokens Γ toks) (x : Var) :
    Tokens (Γ.setImm x) (toks.filter (fun y => y != x)) := by
  refine ⟨fun y => ?_, ?_⟩
  · rw [tokens_setImm, count_filter_ne, h.count]
  · have hl := length_filter_ne x toks
    have hc := h.count x
    simp only [total_setImm, h.total]
    omega

theorem Tokens.same {Γ Γ' : Ctx} {toks : List Var} (h : Tokens Γ toks)
    (ho : Γ'.own = Γ.own) (ht : Γ'.total = Γ.total) : Tokens Γ' toks :=
  ⟨fun y => by rw [h.count]; simp only [tokens_eq, ho], by rw [ht, h.total]⟩

theorem map_fst_pairs (xs : List Var) (n : Nat) :
    (xs.map (fun x => (x, n))).map (fun p => p.1) = xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih => simp only [List.map_cons, ih]

theorem tokens_ofList {xs : List Var} (hn : xs.Nodup) (y : Var) :
    (({ own := Src.NatMap.ofList (xs.map (·, 1)) } : Ctx)).tokens y = if y ∈ xs then 1 else 0 := by
  have hk : ((xs.map (·, 1)).map (·.1)).Nodup := by rw [map_fst_pairs]; exact hn
  by_cases hy : y ∈ xs
  · rw [if_pos hy, tokens_eq]
    rw [Src.NatMap.get?_ofList hk (x := 1) (by simpa using hy)]
    rfl
  · rw [if_neg hy, tokens_eq]
    rw [Src.NatMap.get?_ofList_none hk (by rw [map_fst_pairs]; exact hy)]
    rfl

theorem Tokens.ofList {xs : List Var} (hn : xs.Nodup) (Γ : Ctx)
    (ho : Γ.own = Src.NatMap.ofList (xs.map (·, 1))) (ht : Γ.total = xs.length) : Tokens Γ xs := by
  refine ⟨fun y => ?_, ht⟩
  have := tokens_ofList hn y
  simp only [tokens_eq] at this ⊢
  rw [ho, this, count_nodup hn]

theorem Tokens.enter (Γ : Ctx) (captured params : List Var) (hn : (Γ.entered captured params).Nodup) :
    Tokens (Γ.enter captured params) (Γ.entered captured params) :=
  Tokens.ofList hn _ rfl rfl

theorem Tokens.entry (params : List Var) (hn : params.Nodup) :
    Tokens (Ctx.entry params) params :=
  Tokens.ofList hn _ rfl rfl

end Ctx

end IxCC.Own.Plain
