import IxCC.Rt.Proof.Term

/-!
# The lowering only grows its chunk

`Mono act`: a run of `act` from a state with an open block keeps the block
open and only grows the chunk (`Grows`), keeping labels below `next`. Every
action an instruction's lowering uses is `Mono`, and `Mono` is closed under
`bind`, so each instruction that continues its block is (`instr_mono`).
Terminators finish the block; `term_grows` and `blockCode`'s pieces still
grow the chunk. `rest_grows`: whatever the rest of a block's lowering does
from a state, the state grows into the final one, so the final chunk holds
it (`Grows.ext`).
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-- A run of `act` keeps the block open and grows the chunk. -/
def Mono {α : Type} (act : M α) : Prop :=
  ∀ ⦃st : St⦄ ⦃a : α⦄ ⦃st' : St⦄, act.run st = .ok (a, st') → Labels st → Open st →
    Grows st st' ∧ Labels st' ∧ Open st'

namespace Mono

theorem pure' {α : Type} (a : α) : Mono (pure a : M α) := by
  intro st b st' h hl ho
  simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨Grows.refl _, hl, ho⟩

theorem bind' {α β : Type} {a : M α} {g : α → M β} (ha : Mono a) (hg : ∀ x, Mono (g x)) : Mono (a >>= g) := by
  intro st b st' h hl ho
  obtain ⟨x, st₁, h₁, h₂⟩ := run_bind h
  obtain ⟨hg₁, hl₁, ho₁⟩ := ha h₁ hl ho
  obtain ⟨hg₂, hl₂, ho₂⟩ := hg x h₂ hl₁ ho₁
  exact ⟨hg₁.trans hg₂, hl₂, ho₂⟩

theorem emit' (s : Lir.Stmt) : Mono (emit s) := by
  intro st a st' h hl ho
  rw [emit_run] at h
  cases h
  exact ⟨grows_acc [s] st.fresh (Nat.le_refl _), labels_acc [s] st.fresh hl, open_acc [s] st.fresh ho⟩

theorem freshReg' : Mono freshReg := by
  intro st a st' h hl ho
  have : freshReg.run st = .ok (st.fresh, { st with fresh := st.fresh + 1 }) := rfl
  rw [this] at h
  cases h
  exact ⟨grows_acc [] (st.fresh + 1) (Nat.le_succ _), labels_acc [] _ hl, open_acc [] _ ho⟩

theorem check' (r : Sem.Resource) (mk : PEdge → PEdge → PTerm) : Mono (check r mk) := by
  intro st a st' h hl ho
  rw [check_run] at h
  cases h
  exact ⟨grows_check hl ho r mk, labels_check hl r mk, open_check hl r mk⟩

theorem throw' {α : Type} (e : Error) : Mono (throw e : M α) := by
  intro st a st' h
  exact absurd (by rw [h]; rfl) (throw_not_ok e st)

theorem lift' {α : Type} (x : Except Error α) : Mono (StateT.lift x : M α) := by
  intro st a st' h hl ho
  cases x with
  | error e => simp [StateT.lift, StateT.run, bind, Except.bind] at h
  | ok v =>
    simp only [StateT.lift, StateT.run, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨Grows.refl _, hl, ho⟩

end Mono

/-- Prove `Mono` of a lowering action built from `Mono` pieces. -/
macro "mono" : tactic =>
  `(tactic| repeat (first
    | with_reducible exact Mono.pure' _
    | with_reducible exact Mono.emit' _
    | with_reducible exact Mono.freshReg'
    | with_reducible exact Mono.check' _ _
    | with_reducible exact Mono.throw' _
    | with_reducible exact Mono.lift' _
    | with_reducible apply Mono.bind'
    | with_reducible intro _
    | split
    | unfold assign
    | unfold temp
    | unfold bin))

theorem Mono.untag' (a : Lir.Arg) : Mono (untag a) := by
  cases a <;> simp only [untag] <;> mono

private theorem nat_beq_zero_succ (n : Nat) : ((n + 1 == 0) : Bool) = false := rfl

private theorem nat_beq_zero_zero : ((0 == 0) : Bool) = true := rfl

private theorem natMap_get?_setF {α : Type} :
    ∀ (fuel : Nat) (m : NatMap α) (k : Nat) (x : Option α) (k' : Nat),
      k < fuel → (NatMap.setF fuel m k x).get? k' = if k' = k then x else m.get? k'
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, m, k, x, k', h => by
    have hparts : ∀ (n : NatMap α) (j : Nat),
        n.get? j = if j == 0 then n.parts.1 else if j % 2 == 0 then n.parts.2.1.get? (j / 2)
          else n.parts.2.2.get? (j / 2) := fun n j => by
      cases n with
      | leaf =>
        cases j with
        | zero => rfl
        | succ j1 =>
          change none = if (j1 + 1 == 0) = true then none else if ((j1 + 1) % 2 == 0) = true then none else none
          rw [nat_beq_zero_succ]
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases (j1 + 1) % 2 <;> rfl
      | node v z o => rfl
    rw [hparts m k']
    unfold NatMap.setF
    obtain ⟨v, z, o⟩ := m.parts
    dsimp only
    cases k with
    | zero =>
      rw [nat_beq_zero_zero]
      simp only [↓reduceIte]
      cases k' with
      | zero => rfl
      | succ k'1 =>
        change (if (k'1 + 1 == 0) = true then x else if ((k'1 + 1) % 2 == 0) = true then z.get? ((k'1 + 1) / 2)
          else o.get? ((k'1 + 1) / 2)) = _
        rw [nat_beq_zero_succ]
        simp only [Bool.false_eq_true, Nat.succ_ne_zero k'1, ↓reduceIte]
    | succ k1 =>
      have hk0 : ((k1 + 1 == 0) : Bool) = false := rfl
      have hdiv : (k1 + 1) / 2 < fuel :=
        Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.succ_pos k1) (by decide)) (Nat.le_of_lt_succ h)
      have hmod_eq : ∀ (a b : Nat), a % 2 = b % 2 → (a / 2 = b / 2 ↔ a = b) := fun a b hm =>
        ⟨fun hd => by
          have ha := Nat.div_add_mod a 2
          have hb := Nat.div_add_mod b 2
          rw [hd, hm] at ha
          exact ha.symm.trans hb,
         fun he => congrArg (· / 2) he⟩
      cases hm : (k1 + 1) % 2 with
      | zero =>
        rw [hk0, nat_beq_zero_zero]
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases k' with
        | zero =>
          simp only [Ne.symm (Nat.succ_ne_zero k1), ↓reduceIte]; rfl
        | succ k'1 =>
          change (if (k'1 + 1 == 0) = true then v else if ((k'1 + 1) % 2 == 0) = true then
            (NatMap.setF fuel z ((k1 + 1) / 2) x).get? ((k'1 + 1) / 2) else o.get? ((k'1 + 1) / 2)) = _
          rw [nat_beq_zero_succ]
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hm' : (k'1 + 1) % 2 with
          | zero =>
            rw [nat_beq_zero_zero]
            simp only [↓reduceIte]
            rw [natMap_get?_setF fuel z ((k1 + 1) / 2) x ((k'1 + 1) / 2) hdiv]
            by_cases heq : k'1 + 1 = k1 + 1
            · simp only [heq, ↓reduceIte]
            · have hd : (k'1 + 1) / 2 ≠ (k1 + 1) / 2 := fun h => heq ((hmod_eq _ _ (hm'.trans hm.symm)).mp h)
              simp only [hd, heq, ↓reduceIte]
          | succ r' =>
            rw [nat_beq_zero_succ]
            have hne : k'1 + 1 ≠ k1 + 1 := fun e => by rw [e, hm] at hm'; cases hm'
            simp only [Bool.false_eq_true, hne, ↓reduceIte]
      | succ r =>
        have hk1 : (k1 + 1) % 2 = 1 :=
          match r, hm, Nat.mod_lt (k1 + 1) (by decide : 0 < 2) with
          | 0, hm, _ => hm
          | _ + 1, hm, hlt => absurd (hm ▸ hlt) (Nat.not_lt.mpr (Nat.le_add_left 2 _))
        rw [hk0, nat_beq_zero_succ]
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases k' with
        | zero =>
          simp only [Ne.symm (Nat.succ_ne_zero k1), ↓reduceIte]; rfl
        | succ k'1 =>
          change (if (k'1 + 1 == 0) = true then v else if ((k'1 + 1) % 2 == 0) = true then
            z.get? ((k'1 + 1) / 2) else (NatMap.setF fuel o ((k1 + 1) / 2) x).get? ((k'1 + 1) / 2)) = _
          rw [nat_beq_zero_succ]
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hm' : (k'1 + 1) % 2 with
          | zero =>
            rw [nat_beq_zero_zero]
            have hne : k'1 + 1 ≠ k1 + 1 := fun e => by rw [e, hk1] at hm'; cases hm'
            simp only [hne, ↓reduceIte]
          | succ r' =>
            have hk'1 : (k'1 + 1) % 2 = 1 :=
              match r', hm', Nat.mod_lt (k'1 + 1) (by decide : 0 < 2) with
              | 0, hm', _ => hm'
              | _ + 1, hm', hlt => absurd (hm' ▸ hlt) (Nat.not_lt.mpr (Nat.le_add_left 2 _))
            rw [nat_beq_zero_succ]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [natMap_get?_setF fuel o ((k1 + 1) / 2) x ((k'1 + 1) / 2) hdiv]
            by_cases heq : k'1 + 1 = k1 + 1
            · simp only [heq, ↓reduceIte]
            · have hd : (k'1 + 1) / 2 ≠ (k1 + 1) / 2 := fun h => heq ((hmod_eq _ _ (hk'1.trans hk1.symm)).mp h)
              simp only [hd, heq, ↓reduceIte]

private theorem natMap_get?_insert {α : Type} (m : NatMap α) (k : Nat) (x : α) (k' : Nat) :
    (m.insert k x).get? k' = if k' = k then some x else m.get? k' :=
  natMap_get?_setF (k + 1) m k (some x) k' (Nat.lt_succ_self k)

private theorem nat_ne_add_of_lt {a b k : Nat} (h : a < b) : a ≠ b + k :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right b k))

private theorem nat_add_ne_add {b i j : Nat} (h : i ≠ j) : b + i ≠ b + j :=
  fun e => h (Nat.add_left_cancel e)

theorem Mono.divModVar' (x : Nat) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) :
    Mono (divModVar x o zero a b) := by
  intro st u st' h hl ho
  have hkey : ∀ (nzBody : List Lir.Stmt) (nzTerm : PTerm) (fastBody slowBody : List Lir.Stmt)
      (fastArg slowArg zArg : Lir.Arg) (f' : Nat), st.fresh ≤ f' →
      let curBlk : PBlock :=
        { params := st.params, body := st.acc.reverse,
          term := .br .eq b (.imm 1) (loc (st.next + 3)) (loc st.next) }
      let st₁ : St :=
        { done := ((((st.done.insert st.cur curBlk)
            |>.insert st.next { body := nzBody, term := nzTerm })
            |>.insert (st.next + 1) { body := fastBody, term := .jump ⟨.loc (st.next + 4), [fastArg]⟩ })
            |>.insert (st.next + 2) { body := slowBody, term := .jump ⟨.loc (st.next + 4), [slowArg]⟩, cold := true })
            |>.insert (st.next + 3) { term := .jump ⟨.loc (st.next + 4), [zArg]⟩, cold := true },
          cur := st.next + 4, params := [x], acc := [], next := st.next + 5, fresh := f' }
      Grows st st₁ ∧ Labels st₁ ∧ Open st₁ := by
    intro nzBody nzTerm fastBody slowBody fastArg slowArg zArg f' hfr curBlk st₁
    have hcur := hl.cur
    dsimp only [st₁]
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨Nat.le_add_right st.next 5, hfr, ?_, ?_⟩
      · intro j bj hj
        have hjlt := hl.done hj
        have hjne : j ≠ st.cur := fun e => by subst e; rw [ho] at hj; cases hj
        simp only [natMap_get?_insert]
        rw [if_neg (nat_ne_add_of_lt hjlt), if_neg (nat_ne_add_of_lt hjlt),
          if_neg (nat_ne_add_of_lt hjlt), if_neg (Nat.ne_of_lt hjlt), if_neg hjne]
        exact hj
      · intro _
        refine .inr ⟨curBlk, ?_, rfl, List.prefix_refl _⟩
        simp only [natMap_get?_insert]
        rw [if_neg (nat_ne_add_of_lt hcur), if_neg (nat_ne_add_of_lt hcur),
          if_neg (nat_ne_add_of_lt hcur), if_neg (Nat.ne_of_lt hcur)]
        simp only [↓reduceIte]
    · refine ⟨Nat.lt_succ_self (st.next + 4), ?_⟩
      intro j bj hj
      dsimp only at hj ⊢
      simp only [natMap_get?_insert] at hj
      split at hj
      · rename_i e; subst e; exact Nat.add_lt_add_left (by decide : 3 < 5) st.next
      split at hj
      · rename_i e; subst e; exact Nat.add_lt_add_left (by decide : 2 < 5) st.next
      split at hj
      · rename_i e; subst e; exact Nat.add_lt_add_left (by decide : 1 < 5) st.next
      split at hj
      · rename_i e; subst e; exact Nat.lt_add_of_pos_right (by decide : 0 < 5)
      split at hj
      · rename_i e; subst e; exact Nat.lt_of_lt_of_le hcur (Nat.le_add_right st.next 5)
      exact Nat.lt_of_lt_of_le (hl.done hj) (Nat.le_add_right st.next 5)
    · simp only [Open, natMap_get?_insert]
      rw [if_neg (nat_add_ne_add (by decide : 4 ≠ 3)),
        if_neg (nat_add_ne_add (by decide : 4 ≠ 2)),
        if_neg (nat_add_ne_add (by decide : 4 ≠ 1)),
        if_neg (Ne.symm (Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := st.next) (by decide : 0 < 4)))),
        if_neg (Ne.symm (nat_ne_add_of_lt hcur))]
      cases hq : st.done.get? (st.next + 4) with
      | none => rfl
      | some bj => exact absurd (hl.done hq) (Nat.not_lt.mpr (Nat.le_add_right st.next 4))
  cases a <;> cases b <;>
    (simp only [divModVar, newLabel, close, openAt, untag, bin, temp, freshReg, assign, emit, put, retag,
       StateT.run, bind, StateT.bind, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet,
       StateT.modifyGet, MonadState.modifyGet, Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
     obtain ⟨-, rfl⟩ := h
     refine hkey _ _ _ _ _ _ _ _ ?_
     dsimp only [Lir.VReg]
     repeat (first | exact Nat.le_refl _ | apply Nat.le_succ_of_le))

theorem Mono.divMod' (x : Nat) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) :
    Mono (divMod x o zero a b) := by
  unfold divMod
  repeat (first
    | with_reducible exact Mono.divModVar' _ _ _ _ _
    | with_reducible exact Mono.pure' _
    | with_reducible exact Mono.emit' _
    | with_reducible exact Mono.freshReg'
    | with_reducible exact Mono.check' _ _
    | with_reducible exact Mono.throw' _
    | with_reducible exact Mono.untag' _
    | with_reducible apply Mono.bind'
    | with_reducible intro _
    | split
    | unfold assign
    | unfold temp
    | unfold bin)

theorem Mono.clz64Code' (x : Nat) (u : Lir.Arg) (tagged : Bool) :
    Mono (clz64Code x u tagged) := by
  intro st v st' h hl ho
  have hkey : ∀ (zArg : Lir.Arg) (nzBody : List Lir.Stmt) (nzArg : Lir.Arg) (f' : Nat), st.fresh ≤ f' →
      let curBlk : PBlock :=
        { params := st.params, body := st.acc.reverse,
          term := .br .eq u (.imm 0) (loc st.next) (loc (st.next + 1)) }
      let st₁ : St :=
        { done := ((st.done.insert st.cur curBlk)
            |>.insert st.next { term := .jump ⟨.loc (st.next + 2), [zArg]⟩, cold := true })
            |>.insert (st.next + 1) { body := nzBody, term := .jump ⟨.loc (st.next + 2), [nzArg]⟩ },
          cur := st.next + 2, params := [x], acc := [], next := st.next + 3, fresh := f' }
      Grows st st₁ ∧ Labels st₁ ∧ Open st₁ := by
    intro zArg nzBody nzArg f' hfr curBlk st₁
    have hcur := hl.cur
    dsimp only [st₁]
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨Nat.le_add_right st.next 3, hfr, ?_, ?_⟩
      · intro j bj hj
        have hjlt := hl.done hj
        have hjne : j ≠ st.cur := fun e => by subst e; rw [ho] at hj; cases hj
        simp only [natMap_get?_insert]
        rw [ite_eq_right (nat_ne_add_of_lt hjlt), ite_eq_right (Nat.ne_of_lt hjlt), ite_eq_right hjne]
        exact hj
      · intro _
        refine .inr ⟨curBlk, ?_, rfl, List.prefix_refl _⟩
        simp only [natMap_get?_insert]
        rw [ite_eq_right (nat_ne_add_of_lt hcur), ite_eq_right (Nat.ne_of_lt hcur)]
        simp only [↓reduceIte]
    · refine ⟨Nat.lt_succ_self (st.next + 2), ?_⟩
      intro j bj hj
      dsimp only at hj ⊢
      simp only [natMap_get?_insert] at hj
      split at hj
      · rename_i e; subst e; exact Nat.add_lt_add_left (by decide : 1 < 3) st.next
      split at hj
      · rename_i e; subst e; exact Nat.lt_add_of_pos_right (by decide : 0 < 3)
      split at hj
      · rename_i e; subst e; exact Nat.lt_of_lt_of_le hcur (Nat.le_add_right st.next 3)
      exact Nat.lt_of_lt_of_le (hl.done hj) (Nat.le_add_right st.next 3)
    · simp only [Open, natMap_get?_insert]
      rw [ite_eq_right (nat_add_ne_add (by decide : 2 ≠ 1)),
        ite_eq_right (Ne.symm (Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := st.next) (by decide : 0 < 2)))),
        ite_eq_right (Ne.symm (nat_ne_add_of_lt hcur))]
      cases hq : st.done.get? (st.next + 2) with
      | none => rfl
      | some bj => exact absurd (hl.done hq) (Nat.not_lt.mpr (Nat.le_add_right st.next 2))
  cases tagged <;>
    (simp only [clz64Code, newLabel, close, openAt, put, freshReg, retag, StateT.run, bind,
       StateT.bind, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
       MonadState.modifyGet, Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq,
       Bool.false_eq_true, ↓reduceIte] at h
     obtain ⟨-, rfl⟩ := h
     refine hkey _ _ _ _ ?_
     dsimp only [Lir.VReg]
     repeat (first | exact Nat.le_refl _ | apply Nat.le_succ_of_le))

/-- Closing the open block, adding two blocks at the next two labels and opening the third: the
chunk grows. -/
private theorem grows_three {st : St} (hl : Labels st) (ho : Open st) (t : PTerm) (b0 b1 : PBlock)
    (ps : List Nat) (f' : Nat) (hfr : st.fresh ≤ f') :
    let curBlk : PBlock := { params := st.params, body := st.acc.reverse, term := t }
    let st₁ : St :=
      { done := ((st.done.insert st.cur curBlk).insert st.next b0).insert (st.next + 1) b1,
        cur := st.next + 2, params := ps, acc := [], next := st.next + 3, fresh := f' }
    Grows st st₁ ∧ Labels st₁ ∧ Open st₁ := by
  intro curBlk st₁
  have hcur := hl.cur
  dsimp only [st₁]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Nat.le_add_right st.next 3, hfr, ?_, ?_⟩
    · intro j bj hj
      have hjlt := hl.done hj
      have hjne : j ≠ st.cur := fun e => by subst e; rw [ho] at hj; cases hj
      simp only [natMap_get?_insert]
      rw [ite_eq_right (nat_ne_add_of_lt hjlt), ite_eq_right (Nat.ne_of_lt hjlt), ite_eq_right hjne]
      exact hj
    · intro _
      refine .inr ⟨curBlk, ?_, rfl, List.prefix_refl _⟩
      simp only [natMap_get?_insert]
      rw [ite_eq_right (nat_ne_add_of_lt hcur), ite_eq_right (Nat.ne_of_lt hcur)]
      simp only [↓reduceIte]
  · refine ⟨Nat.lt_succ_self (st.next + 2), ?_⟩
    intro j bj hj
    dsimp only at hj ⊢
    simp only [natMap_get?_insert] at hj
    split at hj
    · rename_i e; subst e; exact Nat.add_lt_add_left (by decide : 1 < 3) st.next
    split at hj
    · rename_i e; subst e; exact Nat.lt_add_of_pos_right (by decide : 0 < 3)
    split at hj
    · rename_i e; subst e; exact Nat.lt_of_lt_of_le hcur (Nat.le_add_right st.next 3)
    exact Nat.lt_of_lt_of_le (hl.done hj) (Nat.le_add_right st.next 3)
  · simp only [Open, natMap_get?_insert]
    rw [ite_eq_right (nat_add_ne_add (by decide : 2 ≠ 1)),
      ite_eq_right (Ne.symm (Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := st.next) (by decide : 0 < 2)))),
      ite_eq_right (Ne.symm (nat_ne_add_of_lt hcur))]
    cases hq : st.done.get? (st.next + 2) with
    | none => rfl
    | some bj => exact absurd (hl.done hq) (Nat.not_lt.mpr (Nat.le_add_right st.next 2))

theorem Mono.divModRaw64' (x : Nat) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) :
    Mono (LowerRep.divModRaw64 x o zero a b) := by
  intro st v st' h hl ho
  simp only [LowerRep.divModRaw64, newLabel, close, openAt, put, freshReg, StateT.run, bind,
    StateT.bind, pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    MonadState.modifyGet, Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact grows_three hl ho _ _ _ _ _ (Nat.le_succ _)

theorem Mono.checked64' (x : Nat) (r : Lir.Arg) : Mono (checked64 x r) := by
  unfold checked64
  mono

/-- The raw 64-bit word operations (`LowerRep.wordRaw64`). -/
theorem Mono.wordRaw64' (f : Fir.FunId) (x : Nat) (op : Src.WordOp) (las : List Lir.Arg) :
    Mono (LowerRep.wordRaw64 f x op las) := by
  unfold LowerRep.wordRaw64
  repeat (first
    | with_reducible exact Mono.divModRaw64' _ _ _ _ _
    | with_reducible exact Mono.clz64Code' _ _ _
    | with_reducible exact Mono.pure' _
    | with_reducible exact Mono.emit' _
    | with_reducible exact Mono.freshReg'
    | with_reducible exact Mono.throw' _
    | with_reducible apply Mono.bind'
    | with_reducible intro _
    | split
    | unfold assign
    | unfold temp
    | unfold bin)

theorem Mono.untagAt' (T : Tables) (f : Fir.FunId) :
    ∀ (as : List Fir.Arg) (las : List Lir.Arg), Mono (untagAt T f as las)
  | [], las => by
    cases las <;> (simp only [untagAt]; exact Mono.pure' _)
  | _ :: _, [] => by simp only [untagAt]; exact Mono.pure' _
  | a :: as, la :: las => by
    simp only [untagAt]
    have rest : ∀ u : Lir.Arg, Mono (do let us ← untagAt T f as las; pure (u :: us)) :=
      fun _ => Mono.bind' (Mono.untagAt' T f as las) (fun _ => Mono.pure' _)
    split
    · exact Mono.bind' (Mono.pure' _) rest
    · refine Mono.bind' ?_ rest
      unfold bin temp assign
      exact Mono.bind' Mono.freshReg' (fun _ => Mono.bind' (Mono.emit' _) (fun _ => Mono.pure' _))

/-- A fixed-width word primitive's expansion (stage W1). -/
theorem Mono.word' (f : Fir.FunId) (x : Nat) (w : Src.Width) (op : Src.WordOp) (las : List Lir.Arg) :
    Mono (Lower.word f x w op las) := by
  unfold Lower.word word64 wordNarrow wordCount checked64
  repeat (first
    | with_reducible exact Mono.divMod' _ _ _ _ _
    | with_reducible exact Mono.clz64Code' _ _ _
    | with_reducible exact Mono.pure' _
    | with_reducible exact Mono.emit' _
    | with_reducible exact Mono.freshReg'
    | with_reducible exact Mono.check' _ _
    | with_reducible exact Mono.throw' _
    | with_reducible exact Mono.untag' _
    | with_reducible apply Mono.bind'
    | with_reducible intro _
    | split
    | unfold assign
    | unfold temp
    | unfold bin)

theorem primitive_mono (f : Fir.FunId) (T : Tables) (x : Nat) (op : Lam.Prim) (las : List Lir.Arg) :
    Mono (primitive f T x op las) := by
  unfold primitive
  dsimp only
  split
  all_goals first
    | with_reducible exact Mono.divMod' _ _ _ _ _
    | with_reducible exact Mono.word' _ _ _ _ _
    | (repeat (first
        | with_reducible exact Mono.pure' _
        | with_reducible exact Mono.emit' _
        | with_reducible exact Mono.freshReg'
        | with_reducible exact Mono.check' _ _
        | with_reducible exact Mono.throw' _
        | with_reducible exact Mono.untag' _
        | with_reducible apply Mono.bind'
        | with_reducible intro _
        | split
        | unfold assign
        | unfold temp
        | unfold bin))


theorem Mono.forM' {α : Type} {g : α → M PUnit} (h : ∀ x, Mono (g x)) : ∀ (l : List α), Mono (l.forM g)
  | [] => Mono.pure' _
  | a :: l => by
    show Mono (g a >>= fun _ => l.forM g)
    exact Mono.bind' (h a) (fun _ => Mono.forM' h l)

theorem alloc_mono (f : Fir.FunId) (T : Tables) (x : Nat) (c : Fir.CtorInfo) (las : List Lir.Arg) :
    Mono (Lower.alloc f T x c las) := by
  unfold Lower.alloc
  repeat (first
    | with_reducible exact Mono.pure' _
    | with_reducible exact Mono.emit' _
    | with_reducible exact Mono.freshReg'
    | with_reducible exact Mono.check' _ _
    | with_reducible exact Mono.throw' _
    | with_reducible apply Mono.bind'
    | with_reducible apply Mono.forM'
    | with_reducible intro _
    | split
    | unfold assign
    | unfold temp
    | unfold bin)

theorem withOperands_mono {f : Fir.FunId} {as : List Fir.Arg} {k : List Lir.Arg → M Unit} (hk : ∀ las, Mono (k las))
    {st st' : St} (h : (withOperands f as k).run st = .ok (true, st')) (hl : Labels st) (ho : Open st) :
    Grows st st' ∧ Labels st' ∧ Open st' := by
  rcases withOperands_run h with ⟨las, -, -, hr⟩ | ⟨-, hb, -⟩
  · exact hk las hr hl ho
  · cases hb

theorem withOperandsAt_mono {f : Fir.FunId} {raw : List Bool} {as : List Fir.Arg} {k : List Lir.Arg → M Unit}
    (hk : ∀ las, Mono (k las)) {st st' : St} (h : (withOperandsAt f raw as k).run st = .ok (true, st'))
    (hl : Labels st) (ho : Open st) : Grows st st' ∧ Labels st' ∧ Open st' := by
  rcases withOperandsAt_run h with ⟨las, -, -, hr⟩ | ⟨-, hb, -⟩
  · exact hk las hr hl ho
  · cases hb

/-- The raw path of a primitive binding, where it continues its block. -/
theorem rawPrimCode_mono {f : Fir.FunId} {T : Tables} {x : Nat} {op : Lam.Prim} {as : List Fir.Arg}
    {st st' : St} (h : (rawPrimCode f T x op as).run st = .ok (true, st')) (hl : Labels st) (ho : Open st) :
    Grows st st' ∧ Labels st' ∧ Open st' := by
  unfold rawPrimCode at h
  split at h
  · unfold rawWord at h
    refine withOperandsAt_mono (fun las => ?_) h hl ho
    refine Mono.bind' (Mono.untagAt' T f _ las) (fun us => ?_)
    split
    · exact Mono.wordRaw64' _ _ _ _
    · exact Mono.bind' Mono.freshReg' (fun _ =>
        Mono.bind' (Mono.wordRaw64' _ _ _ _) (fun _ => Mono.checked64' _ _))
  · exact withOperands_mono (fun las => primitive_mono f T x _ las) h hl ho

/-- **An instruction that continues its block keeps it open and grows the
chunk.** -/
theorem instr_mono {f : Fir.FunId} {T : Tables} {i : Cfg.Instr} {st st' : St}
    (h : (instr f T i).run st = .ok (true, st')) (hl : Labels st) (ho : Open st) :
    Grows st st' ∧ Labels st' ∧ Open st' := by
  match i, h with
  | .bind x (.fir (.arg a)), h =>
    refine withOperandsAt_mono (fun las => ?_) h hl ho
    split
    · unfold assign; exact Mono.emit' _
    · exact Mono.pure' _
  | .bind x (.fir (.prim op as)), h =>
    cases hr : rawPrim T f x op as
    · rw [instr_prim_tagged hr] at h
      exact withOperands_mono (fun las => primitive_mono f T x op las) h hl ho
    · rw [instr_prim_raw hr] at h
      exact rawPrimCode_mono h hl ho
  | .bind x (.fir (.call g as)), h => exact withOperandsAt_mono (fun las => Mono.emit' _) h hl ho
  | .bind x (.alloc c as κ), h => exact withOperands_mono (fun las => alloc_mono f T x c las) h hl ho
  | .bind x (.fir (.ctor ..)), h =>
    simp [instr, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run] at h
  | .bind x (.fir (.proj ..)), h =>
    simp [instr, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run] at h
  | .bind x (.proj y c i), h =>
    have hrun' : (Lower.proj f T x y c i).run st = .ok ((), st') := by
      simp only [instr, bind, StateT.bind, StateT.run, pure, StateT.pure, Except.bind, Except.pure] at h
      revert h
      cases hp : Lower.proj f T x y c i st with
      | error e => simp
      | ok v => intro h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [StateT.run, hp, ← h.2]
    rcases proj_run hrun' with ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, rfl⟩
    · exact ⟨grows_acc _ _ (Nat.le_refl _), labels_acc _ _ hl, open_acc _ _ ho⟩
    · exact ⟨grows_acc _ _ (Nat.le_refl _), labels_acc _ _ hl, open_acc _ _ ho⟩

theorem instrs_cons_run {f : Fir.FunId} {T : Tables} {i : Cfg.Instr} {is : List Cfg.Instr} {st st' : St} {b : Bool}
    (h : (instrs f T (i :: is)).run st = .ok (b, st')) :
    ∃ b₁ st₁, (instr f T i).run st = .ok (b₁, st₁) ∧
      ((b₁ = true ∧ (instrs f T is).run st₁ = .ok (b, st')) ∨ (b₁ = false ∧ b = false ∧ st' = st₁)) := by
  simp only [instrs] at h
  obtain ⟨b₁, st₁, h₁, h₂⟩ := run_bind h
  refine ⟨b₁, st₁, h₁, ?_⟩
  cases b₁ with
  | true => exact .inl ⟨rfl, h₂⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h₂
    exact .inr ⟨rfl, h₂.1.symm, h₂.2.symm⟩

/-- A block's instructions grow the chunk; they keep the block open if
they continue it. -/
theorem instrs_grows {f : Fir.FunId} {T : Tables} :
    ∀ {is : List Cfg.Instr} {st st' : St} {b : Bool}, (instrs f T is).run st = .ok (b, st') → Labels st → Open st →
      Grows st st' ∧ (b = true → Labels st' ∧ Open st') ∧ (b = false → ∃ s, Grows st s ∧ Labels s ∧ Open s ∧
        st' = closeSt s (.fail .natOverflow))
  | [], st, st', b, h, hl, ho => by
    simp only [instrs, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grows.refl _, fun _ => ⟨hl, ho⟩, fun h => by cases h⟩
  | i :: is, st, st', b, h, hl, ho => by
    obtain ⟨b₁, st₁, h₁, ⟨rfl, h₂⟩ | ⟨rfl, rfl, rfl⟩⟩ := instrs_cons_run h
    · obtain ⟨hg₁, hl₁, ho₁⟩ := instr_mono h₁ hl ho
      obtain ⟨hg₂, hb₂, hf₂⟩ := instrs_grows h₂ hl₁ ho₁
      refine ⟨hg₁.trans hg₂, hb₂, fun hb => ?_⟩
      obtain ⟨s, hgs, hls, hos, rfl⟩ := hf₂ hb
      exact ⟨s, hg₁.trans hgs, hls, hos, rfl⟩
    · have := instr_false h₁
      subst this
      exact ⟨grows_close ho _, (fun h => by cases h), fun _ => ⟨st, Grows.refl _, hl, ho, rfl⟩⟩

/-! ## Terminators grow the chunk -/

theorem switch_grows {f : Fir.FunId} {T : Tables} {src x : Nat} {alts : List (Key.CtorKey × Cfg.Edge)}
    {d : Option Cfg.Edge} {st st' : St} (h : (switch f T src x alts d).run st = .ok ((), st')) (hl : Labels st)
    (ho : Open st) : Grows st st' := by
  unfold switch at h
  obtain ⟨es, st₁, h₁, h₂⟩ := run_bind h
  obtain ⟨dd, st₂, h₃, h₄⟩ := run_bind h₂
  obtain ⟨hg₁, hl₁, -, -, -, -, ho₁, -⟩ := alts_run (mapM_run h₁) hl
  obtain ⟨hg₂, hl₂, -, -, -, -, ho₂, -⟩ := dflt_run h₃ hl₁
  have ho₂' := ho₂ (ho₁ ho)
  dsimp only at h₄
  split at h₄
  · split at h₄
    · obtain ⟨t, rfl⟩ := natSwitch_grows h₄
      exact (hg₁.trans hg₂).trans (grows_close ho₂' t)
    · obtain ⟨_, s, h₅, -⟩ := run_bind h₄
      exact absurd (by rw [h₅]; rfl) (throw_not_ok _ _)
  · exact (hg₁.trans hg₂).trans (tagSwitch_grows h₄ hl₂ ho₂')

theorem fusedSwitch_grows {f : Fir.FunId} {T : Tables} {src : Nat} {c : Lir.Cond} {la lb : Lir.Arg}
    {alts : List (Key.CtorKey × Cfg.Edge)} {d : Option Cfg.Edge} {st st' : St}
    (h : (fusedSwitch f T src c la lb alts d).run st = .ok ((), st')) (hl : Labels st) (ho : Open st) :
    Grows st st' := by
  unfold fusedSwitch at h
  obtain ⟨te, st₁, h₁, h₂⟩ := run_bind h
  obtain ⟨fe, st₂, h₃, h₄⟩ := run_bind h₂
  obtain ⟨hg₁, hl₁, -, -, -, -, ho₁, -⟩ := dflt_run h₁ hl
  obtain ⟨hg₂, -, -, -, -, -, ho₂, -⟩ := dflt_run h₃ hl₁
  obtain ⟨t, rfl, -⟩ := fusedClose_run h₄
  exact (hg₁.trans hg₂).trans (grows_close (ho₂ (ho₁ ho)) t)

/-- **A terminator grows the chunk.** -/
theorem term_grows {f : Fir.FunId} {T : Tables} {src : Nat} {t : Cfg.Term} {st st' : St}
    (h : (term f T src t).run st = .ok ((), st')) (hl : Labels st) (ho : Open st) : Grows st st' := by
  match t, h with
  | .jump e, h => obtain ⟨_, _, _, _, hg, _, _⟩ := term_jump h hl ho; exact hg
  | .switch x alts d, h => exact switch_grows h hl ho
  | .ret a, h => exact (term_ret h ho).1
  | .tcall g as, h => exact (term_tcall h ho).1
  | .trap, h => rw [term_trap h]; exact grows_close ho _

end IxCC.Rt.Proof
