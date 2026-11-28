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

theorem mapIsEmpty_get?_none {α : Type} :
    ∀ {m : Src.NatMap α}, mapIsEmpty m = true → ∀ k, m.get? k = none
  | .leaf, _, _ => rfl
  | .node none z o, h, k => by
    simp only [mapIsEmpty, Bool.and_eq_true] at h
    simp only [Src.NatMap.get?]
    split
    · rfl
    · split
      · exact mapIsEmpty_get?_none h.1 _
      · exact mapIsEmpty_get?_none h.2 _
  | .node (some _) _ _, h, _ => by simp [mapIsEmpty] at h

theorem get?_interSet : ∀ (a b : Src.NatSet) (k : Nat),
    (interSet a b).get? k = if a.contains k && b.contains k then some () else none
  | .leaf, _, _ => by simp [interSet, Src.NatMap.get?, Src.NatMap.contains]
  | .node _ _ _, .leaf, _ => by simp [interSet, Src.NatMap.get?, Src.NatMap.contains]
  | .node va za oa, .node vb zb ob, k => by
    simp only [interSet, Src.NatMap.get?, Src.NatMap.contains]
    split
    · rfl
    · split
      · exact get?_interSet za zb (k / 2)
      · exact get?_interSet oa ob (k / 2)

theorem contains_interSet (a b : Src.NatSet) (k : Nat) :
    (interSet a b).contains k = (a.contains k && b.contains k) := by
  simp only [Src.NatMap.contains, get?_interSet]
  by_cases h : ((Src.NatMap.get? a k).isSome && (Src.NatMap.get? b k).isSome) = true <;> simp [h]

theorem ctor0Valid_ok {ctors : List Lam.CtorInfo} {c : Fir.CtorInfo}
    (h : ctor0Valid ctors c = true) :
    ∀ info, Fir.CtorInfo.ofKey ctors c.key = some info → info.arity = 0 := by
  intro info hi
  simp only [ctor0Valid, hi, beq_iff_eq] at h
  exact h

namespace Ctx

variable (Γ : Ctx) (x y : Var)

theorem tokens_eq : Γ.tokens y = (Γ.own.get? y).getD 0 := rfl

@[simp] theorem isImm_addOwn (n : Nat) : (Γ.addOwn x n).isImm y = Γ.isImm y := rfl
@[simp] theorem isPbrw_addOwn (n : Nat) : (Γ.addOwn x n).isPbrw y = Γ.isPbrw y := rfl
@[simp] theorem pbrw_addOwn (n : Nat) : (Γ.addOwn x n).pbrw = Γ.pbrw := rfl
@[simp] theorem brw_addOwn (n : Nat) : (Γ.addOwn x n).brw = Γ.brw := rfl
@[simp] theorem epoch_addOwn (n : Nat) : (Γ.addOwn x n).epoch = Γ.epoch := rfl
@[simp] theorem total_addOwn (n : Nat) : (Γ.addOwn x n).total = Γ.total + n := rfl
@[simp] theorem ctorOf_addOwn (n : Nat) : (Γ.addOwn x n).ctorOf = Γ.ctorOf := rfl
@[simp] theorem projOf_addOwn (n : Nat) : (Γ.addOwn x n).projOf = Γ.projOf := rfl
@[simp] theorem uniq_addOwn (n : Nat) : (Γ.addOwn x n).uniq = Γ.uniq := rfl
@[simp] theorem isUniq_addOwn (n : Nat) : (Γ.addOwn x n).isUniq y = Γ.isUniq y := rfl
@[simp] theorem rset_addOwn (n : Nat) : (Γ.addOwn x n).rset = Γ.rset := rfl
theorem tokens_addOwn (n : Nat) :
    (Γ.addOwn x n).tokens y = if y = x then Γ.tokens x + n else Γ.tokens y := by
  simp only [tokens_eq, addOwn, Src.NatMap.get?_insert]
  split <;> simp_all [tokens_eq]
theorem ownHas_addOwn (n : Nat) :
    (Γ.addOwn x n).own.contains y = (decide (y = x) || Γ.own.contains y) := by
  simp only [addOwn, Src.NatMap.contains, Src.NatMap.get?_insert]
  split <;> simp_all

@[simp] theorem isImm_addUniqOwn : (Γ.addUniqOwn x).isImm y = Γ.isImm y := rfl
@[simp] theorem isPbrw_addUniqOwn : (Γ.addUniqOwn x).isPbrw y = Γ.isPbrw y := rfl
@[simp] theorem pbrw_addUniqOwn : (Γ.addUniqOwn x).pbrw = Γ.pbrw := rfl
@[simp] theorem brw_addUniqOwn : (Γ.addUniqOwn x).brw = Γ.brw := rfl
@[simp] theorem epoch_addUniqOwn : (Γ.addUniqOwn x).epoch = Γ.epoch := rfl
@[simp] theorem total_addUniqOwn : (Γ.addUniqOwn x).total = Γ.total + 1 := rfl
@[simp] theorem ctorOf_addUniqOwn : (Γ.addUniqOwn x).ctorOf = Γ.ctorOf := rfl
@[simp] theorem projOf_addUniqOwn : (Γ.addUniqOwn x).projOf = Γ.projOf := rfl
@[simp] theorem rset_addUniqOwn : (Γ.addUniqOwn x).rset = Γ.rset := rfl
theorem tokens_addUniqOwn :
    (Γ.addUniqOwn x).tokens y = if y = x then Γ.tokens x + 1 else Γ.tokens y :=
  tokens_addOwn Γ x y 1
theorem ownHas_addUniqOwn :
    (Γ.addUniqOwn x).own.contains y = (decide (y = x) || Γ.own.contains y) :=
  ownHas_addOwn Γ x y 1
theorem isUniq_addUniqOwn : (Γ.addUniqOwn x).isUniq y = (decide (y = x) || Γ.isUniq y) := by
  simp only [isUniq, addUniqOwn, Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
  split <;> simp_all

@[simp] theorem isImm_release : Γ.release.isImm y = Γ.isImm y := rfl
@[simp] theorem isPbrw_release : Γ.release.isPbrw y = Γ.isPbrw y := rfl
@[simp] theorem pbrw_release : Γ.release.pbrw = Γ.pbrw := rfl
@[simp] theorem own_release : Γ.release.own = Γ.own := rfl
@[simp] theorem brw_release : Γ.release.brw = Γ.brw := rfl
@[simp] theorem total_release : Γ.release.total = Γ.total := rfl
@[simp] theorem epoch_release : Γ.release.epoch = Γ.epoch + 1 := rfl
@[simp] theorem tokens_release : Γ.release.tokens y = Γ.tokens y := rfl
@[simp] theorem ctorOf_release : Γ.release.ctorOf = Γ.ctorOf := rfl
@[simp] theorem projOf_release : Γ.release.projOf = Γ.projOf := rfl
@[simp] theorem uniq_release : Γ.release.uniq = Γ.uniq := rfl
@[simp] theorem isUniq_release : Γ.release.isUniq y = Γ.isUniq y := rfl
@[simp] theorem rset_release : Γ.release.rset = Γ.rset := rfl

@[simp] theorem isImm_setBorrow : (Γ.setBorrow x).isImm y = Γ.isImm y := rfl
@[simp] theorem isPbrw_setBorrow : (Γ.setBorrow x).isPbrw y = Γ.isPbrw y := rfl
@[simp] theorem pbrw_setBorrow : (Γ.setBorrow x).pbrw = Γ.pbrw := rfl
@[simp] theorem own_setBorrow : (Γ.setBorrow x).own = Γ.own := rfl
@[simp] theorem total_setBorrow : (Γ.setBorrow x).total = Γ.total := rfl
@[simp] theorem epoch_setBorrow : (Γ.setBorrow x).epoch = Γ.epoch := rfl
@[simp] theorem tokens_setBorrow : (Γ.setBorrow x).tokens y = Γ.tokens y := rfl
@[simp] theorem ctorOf_setBorrow : (Γ.setBorrow x).ctorOf = Γ.ctorOf := rfl
@[simp] theorem projOf_setBorrow : (Γ.setBorrow x).projOf = Γ.projOf := rfl
@[simp] theorem uniq_setBorrow : (Γ.setBorrow x).uniq = Γ.uniq := rfl
@[simp] theorem isUniq_setBorrow : (Γ.setBorrow x).isUniq y = Γ.isUniq y := rfl
@[simp] theorem rset_setBorrow : (Γ.setBorrow x).rset = Γ.rset := rfl
theorem brw_setBorrow :
    (Γ.setBorrow x).brw.get? y = if y = x then some Γ.epoch else Γ.brw.get? y := by
  simp only [setBorrow, Src.NatMap.get?_insert]

@[simp] theorem isImm_setPbrw : (Γ.setPbrw x).isImm y = Γ.isImm y := rfl
@[simp] theorem own_setPbrw : (Γ.setPbrw x).own = Γ.own := rfl
@[simp] theorem brw_setPbrw : (Γ.setPbrw x).brw = Γ.brw := rfl
@[simp] theorem total_setPbrw : (Γ.setPbrw x).total = Γ.total := rfl
@[simp] theorem epoch_setPbrw : (Γ.setPbrw x).epoch = Γ.epoch := rfl
@[simp] theorem tokens_setPbrw : (Γ.setPbrw x).tokens y = Γ.tokens y := rfl
@[simp] theorem ctorOf_setPbrw : (Γ.setPbrw x).ctorOf = Γ.ctorOf := rfl
@[simp] theorem projOf_setPbrw : (Γ.setPbrw x).projOf = Γ.projOf := rfl
@[simp] theorem uniq_setPbrw : (Γ.setPbrw x).uniq = Γ.uniq := rfl
@[simp] theorem isUniq_setPbrw : (Γ.setPbrw x).isUniq y = Γ.isUniq y := rfl
@[simp] theorem rset_setPbrw : (Γ.setPbrw x).rset = Γ.rset := rfl
theorem isPbrw_setPbrw : (Γ.setPbrw x).isPbrw y = (decide (y = x) || Γ.isPbrw y) := by
  simp only [isPbrw, setPbrw, Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
  split <;> simp_all

theorem isImm_setImm : (Γ.setImm x).isImm y = (decide (y = x) || Γ.isImm y) := by
  simp only [isImm, setImm, Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
  split <;> simp_all
@[simp] theorem isPbrw_setImm : (Γ.setImm x).isPbrw y = Γ.isPbrw y := rfl
@[simp] theorem pbrw_setImm : (Γ.setImm x).pbrw = Γ.pbrw := rfl
theorem tokens_setImm : (Γ.setImm x).tokens y = if y = x then 0 else Γ.tokens y := by
  simp only [tokens_eq, setImm, Src.NatMap.get?_erase]
  split <;> rfl
theorem brw_setImm : (Γ.setImm x).brw.get? y = if y = x then none else Γ.brw.get? y := by
  simp only [setImm, Src.NatMap.get?_erase]
@[simp] theorem epoch_setImm : (Γ.setImm x).epoch = Γ.epoch := rfl
@[simp] theorem total_setImm : (Γ.setImm x).total = Γ.total - Γ.tokens x := rfl
@[simp] theorem ctorOf_setImm : (Γ.setImm x).ctorOf = Γ.ctorOf := rfl
@[simp] theorem projOf_setImm : (Γ.setImm x).projOf = Γ.projOf := rfl
@[simp] theorem rset_setImm : (Γ.setImm x).rset = Γ.rset := rfl
theorem ownHas_setImm : (Γ.setImm x).own.contains y = (!decide (y = x) && Γ.own.contains y) := by
  simp only [setImm, Src.NatMap.contains, Src.NatMap.get?_erase]
  split <;> simp_all
theorem isUniq_setImm : (Γ.setImm x).isUniq y = (!decide (y = x) && Γ.isUniq y) := by
  simp only [isUniq, setImm, Src.NatMap.contains, Src.NatMap.get?_erase]
  split <;> simp_all

theorem isImm_setImmUniq : (Γ.setImmUniq x).isImm y = (decide (y = x) || Γ.isImm y) :=
  isImm_setImm Γ x y
@[simp] theorem isPbrw_setImmUniq : (Γ.setImmUniq x).isPbrw y = Γ.isPbrw y := rfl
@[simp] theorem pbrw_setImmUniq : (Γ.setImmUniq x).pbrw = Γ.pbrw := rfl
theorem tokens_setImmUniq : (Γ.setImmUniq x).tokens y = if y = x then 0 else Γ.tokens y :=
  tokens_setImm Γ x y
theorem brw_setImmUniq : (Γ.setImmUniq x).brw.get? y = if y = x then none else Γ.brw.get? y :=
  brw_setImm Γ x y
@[simp] theorem epoch_setImmUniq : (Γ.setImmUniq x).epoch = Γ.epoch := rfl
@[simp] theorem total_setImmUniq : (Γ.setImmUniq x).total = Γ.total - Γ.tokens x := rfl
@[simp] theorem ctorOf_setImmUniq : (Γ.setImmUniq x).ctorOf = Γ.ctorOf := rfl
@[simp] theorem projOf_setImmUniq : (Γ.setImmUniq x).projOf = Γ.projOf := rfl
@[simp] theorem rset_setImmUniq : (Γ.setImmUniq x).rset = Γ.rset := rfl
theorem ownHas_setImmUniq : (Γ.setImmUniq x).own.contains y = (!decide (y = x) && Γ.own.contains y) :=
  ownHas_setImm Γ x y
theorem isUniq_setImmUniq : (Γ.setImmUniq x).isUniq y = (decide (y = x) || Γ.isUniq y) := by
  simp only [isUniq, setImmUniq, setImm, Src.NatSet.insert, Src.NatMap.contains,
    Src.NatMap.get?_insert, Src.NatMap.get?_erase]
  split <;> simp_all

@[simp] theorem isImm_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).isImm y = Γ.isImm y := rfl
@[simp] theorem isPbrw_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).isPbrw y = Γ.isPbrw y := rfl
@[simp] theorem pbrw_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).pbrw = Γ.pbrw := rfl
@[simp] theorem own_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).own = Γ.own := rfl
@[simp] theorem brw_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).brw = Γ.brw := rfl
@[simp] theorem epoch_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).epoch = Γ.epoch := rfl
@[simp] theorem total_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).total = Γ.total := rfl
@[simp] theorem tokens_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).tokens y = Γ.tokens y := rfl
@[simp] theorem projOf_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).projOf = Γ.projOf := rfl
@[simp] theorem uniq_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).uniq = Γ.uniq := rfl
@[simp] theorem isUniq_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).isUniq y = Γ.isUniq y := rfl
@[simp] theorem rset_setCtor (key : Key.CtorKey) : (Γ.setCtor x key).rset = Γ.rset := rfl
theorem ctorOf_setCtor (key : Key.CtorKey) :
    (Γ.setCtor x key).ctorOf.get? y = if y = x then some key else Γ.ctorOf.get? y := by
  simp only [setCtor, Src.NatMap.get?_insert]

@[simp] theorem isImm_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).isImm y = Γ.isImm y := rfl
@[simp] theorem isPbrw_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).isPbrw y = Γ.isPbrw y := rfl
@[simp] theorem pbrw_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).pbrw = Γ.pbrw := rfl
@[simp] theorem own_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).own = Γ.own := rfl
@[simp] theorem brw_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).brw = Γ.brw := rfl
@[simp] theorem epoch_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).epoch = Γ.epoch := rfl
@[simp] theorem total_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).total = Γ.total := rfl
@[simp] theorem tokens_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).tokens y = Γ.tokens y := rfl
@[simp] theorem ctorOf_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).ctorOf = Γ.ctorOf := rfl
@[simp] theorem uniq_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).uniq = Γ.uniq := rfl
@[simp] theorem isUniq_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).isUniq y = Γ.isUniq y := rfl
@[simp] theorem rset_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).rset = Γ.rset := rfl
theorem projOf_setProj (z : Var) (key : Key.CtorKey) (idx : Nat) :
    (Γ.setProj x z key idx).projOf.get? y = if y = x then some (z, key, idx) else Γ.projOf.get? y := by
  simp only [setProj, Src.NatMap.get?_insert]

@[simp] theorem isImm_clearUniq : (Γ.clearUniq x).isImm y = Γ.isImm y := rfl
@[simp] theorem isPbrw_clearUniq : (Γ.clearUniq x).isPbrw y = Γ.isPbrw y := rfl
@[simp] theorem pbrw_clearUniq : (Γ.clearUniq x).pbrw = Γ.pbrw := rfl
@[simp] theorem own_clearUniq : (Γ.clearUniq x).own = Γ.own := rfl
@[simp] theorem brw_clearUniq : (Γ.clearUniq x).brw = Γ.brw := rfl
@[simp] theorem epoch_clearUniq : (Γ.clearUniq x).epoch = Γ.epoch := rfl
@[simp] theorem total_clearUniq : (Γ.clearUniq x).total = Γ.total := rfl
@[simp] theorem tokens_clearUniq : (Γ.clearUniq x).tokens y = Γ.tokens y := rfl
@[simp] theorem ctorOf_clearUniq : (Γ.clearUniq x).ctorOf = Γ.ctorOf := rfl
@[simp] theorem projOf_clearUniq : (Γ.clearUniq x).projOf = Γ.projOf := rfl
@[simp] theorem rset_clearUniq : (Γ.clearUniq x).rset = Γ.rset := rfl
theorem isUniq_clearUniq : (Γ.clearUniq x).isUniq y = (!decide (y = x) && Γ.isUniq y) := by
  simp only [isUniq, clearUniq, Src.NatMap.contains, Src.NatMap.get?_erase]
  split <;> simp_all

theorem borrowed_eq : Γ.borrowed y = (Γ.brw.get? y == some Γ.epoch) := rfl

theorem avail_eq : Γ.avail y = (Γ.isImm y || decide (0 < Γ.tokens y) || Γ.borrowed y || Γ.isPbrw y) := rfl

theorem known_eq : Γ.known y =
    (Γ.isImm y || Γ.own.contains y || (Γ.brw.get? y).isSome || Γ.isPbrw y) := rfl

theorem borrowable_eq : Γ.borrowable y = (Γ.isImm y || Γ.isPbrw y || decide (0 < Γ.tokens y)) := rfl

/-! ## The consuming operations -/

/-- What a successful `take` did. -/
theorem take_ok {Γ Γ' : Ctx} {x : Var} (h : Γ.take x = .ok Γ') :
    (Γ.isImm x = true ∧ Γ' = Γ) ∨
      (Γ.isImm x = false ∧ ∃ n, Γ.own.get? x = some (n + 1) ∧
        Γ' = { Γ with own := Γ.own.insert x n, uniq := Γ.uniq.erase x, total := Γ.total - 1 }) := by
  unfold take at h
  cases hi : Γ.isImm x with
  | true => simp only [hi, ↓reduceIte, Except.ok.injEq] at h; exact Or.inl ⟨rfl, h.symm⟩
  | false =>
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    refine Or.inr ⟨rfl, ?_⟩
    split at h
    · next n hn => exact ⟨n, hn, (Except.ok.inj h).symm⟩
    · split at h <;> (try split at h) <;> (try split at h) <;> cases h

/-- A weaker context: the same immediates, borrows, `pbrw`, `ctorOf`, `projOf`, `rset` and epoch,
no more tokens, and no more unique markers. -/
structure Weaker (Γ' Γ : Ctx) : Prop where
  imm : Γ'.imm = Γ.imm
  brw : Γ'.brw = Γ.brw
  pbrw : Γ'.pbrw = Γ.pbrw
  epoch : Γ'.epoch = Γ.epoch
  ctorOf : Γ'.ctorOf = Γ.ctorOf
  projOf : Γ'.projOf = Γ.projOf
  rset : Γ'.rset = Γ.rset
  tokens : ∀ y, Γ'.tokens y ≤ Γ.tokens y
  ownHas : ∀ y, Γ'.own.contains y = true → Γ.own.contains y = true
  isUniq : ∀ y, Γ'.isUniq y = true → Γ.isUniq y = true
  uniqTok : ∀ y, Γ'.isUniq y = true → Γ'.isImm y = false → Γ'.tokens y = Γ.tokens y

theorem Weaker.refl (Γ : Ctx) : Weaker Γ Γ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Nat.le_refl _, fun _ h => h, fun _ h => h,
    fun _ _ _ => rfl⟩

theorem Weaker.trans {Γ₁ Γ₂ Γ₃ : Ctx} (h₁ : Weaker Γ₁ Γ₂) (h₂ : Weaker Γ₂ Γ₃) : Weaker Γ₁ Γ₃ :=
  ⟨h₁.imm.trans h₂.imm, h₁.brw.trans h₂.brw, h₁.pbrw.trans h₂.pbrw, h₁.epoch.trans h₂.epoch,
    h₁.ctorOf.trans h₂.ctorOf, h₁.projOf.trans h₂.projOf, h₁.rset.trans h₂.rset,
    fun y => Nat.le_trans (h₁.tokens y) (h₂.tokens y),
    fun y h => h₂.ownHas y (h₁.ownHas y h), fun y h => h₂.isUniq y (h₁.isUniq y h),
    fun y hu hi => (h₁.uniqTok y hu hi).trans
      (h₂.uniqTok y (h₁.isUniq y hu) (by simp only [Ctx.isImm, ← h₁.imm]; exact hi))⟩

theorem Weaker.isImm {Γ' Γ : Ctx} (h : Weaker Γ' Γ) (y : Var) : Γ'.isImm y = Γ.isImm y := by
  simp only [Ctx.isImm, h.imm]

theorem Weaker.isPbrw {Γ' Γ : Ctx} (h : Weaker Γ' Γ) (y : Var) : Γ'.isPbrw y = Γ.isPbrw y := by
  simp only [Ctx.isPbrw, h.pbrw]

theorem Weaker.borrowed {Γ' Γ : Ctx} (h : Weaker Γ' Γ) (y : Var) : Γ'.borrowed y = Γ.borrowed y := by
  simp only [Ctx.borrowed, h.brw, h.epoch]

theorem Weaker.avail {Γ' Γ : Ctx} (h : Weaker Γ' Γ) {y : Var} (ha : Γ'.avail y = true) :
    Γ.avail y = true := by
  have ht := h.tokens y
  simp only [avail_eq, h.isImm, h.borrowed, h.isPbrw, Bool.or_eq_true, decide_eq_true_eq] at ha ⊢
  rcases ha with ((h1 | h2) | h3) | h4
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inl (Or.inr (Nat.lt_of_lt_of_le h2 ht)))
  · exact Or.inl (Or.inr h3)
  · exact Or.inr h4

theorem Weaker.known {Γ' Γ : Ctx} (h : Weaker Γ' Γ) {y : Var} (hk : Γ'.known y = true) :
    Γ.known y = true := by
  simp only [known_eq, Bool.or_eq_true] at hk ⊢
  rw [h.isImm y, h.brw, h.isPbrw y] at hk
  rcases hk with ((h1 | h2) | h3) | h4
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inl (Or.inr (h.ownHas y h2)))
  · exact Or.inl (Or.inr h3)
  · exact Or.inr h4

theorem take_weaker {Γ Γ' : Ctx} {x : Var} (h : Γ.take x = .ok Γ') : Weaker Γ' Γ := by
  rcases take_ok h with ⟨_, rfl⟩ | ⟨_, n, hn, rfl⟩
  · exact Weaker.refl _
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y => ?_, fun y hy => ?_, fun y hy => ?_,
      fun y hy _ => ?_⟩
    · simp only [tokens_eq, Src.NatMap.get?_insert]
      split
      · next he => subst he; simp [hn]
      · exact Nat.le_refl _
    · simp only [Src.NatMap.contains, Src.NatMap.get?_insert] at hy ⊢
      split at hy
      · next he => subst he; simp [hn]
      · exact hy
    · simp only [isUniq, Src.NatMap.contains, Src.NatMap.get?_erase] at hy ⊢
      split at hy
      · simp at hy
      · exact hy
    · simp only [isUniq, Src.NatMap.contains, Src.NatMap.get?_erase] at hy
      simp only [tokens_eq, Src.NatMap.get?_insert]
      split at hy
      · simp at hy
      · next hne => rw [ite_eq_right hne]

theorem clearUniq_weaker (Γ : Ctx) (x : Var) : Weaker (Γ.clearUniq x) Γ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Nat.le_refl _, fun _ h => h, fun y hy => by
    rw [isUniq_clearUniq, Bool.and_eq_true] at hy; exact hy.2, fun _ _ _ => rfl⟩

theorem clearBorrowedUniq_weaker (Γ : Ctx) (bs : List Bool) (args : List Arg) :
    Weaker (Γ.clearBorrowedUniq bs args) Γ := by
  induction args generalizing Γ bs with
  | nil => simp only [clearBorrowedUniq]; exact Weaker.refl _
  | cons a as ih =>
    cases bs with
    | nil => simp only [clearBorrowedUniq]; exact Weaker.refl _
    | cons b bs =>
      cases b with
      | false => simp only [clearBorrowedUniq]; exact ih Γ bs
      | true =>
        cases a with
        | lit _ | erased => simp only [clearBorrowedUniq]; exact ih Γ bs
        | var x =>
          simp only [clearBorrowedUniq]
          split
          · exact ih Γ bs
          · exact (ih _ bs).trans (clearUniq_weaker Γ x)

theorem clearBorrowedUniq_own (Γ : Ctx) (bs : List Bool) (args : List Arg) :
    (Γ.clearBorrowedUniq bs args).own = Γ.own ∧ (Γ.clearBorrowedUniq bs args).total = Γ.total := by
  induction args generalizing Γ bs with
  | nil => simp [clearBorrowedUniq]
  | cons a as ih =>
    cases bs with
    | nil => simp [clearBorrowedUniq]
    | cons b bs =>
      cases b with
      | false => simp only [clearBorrowedUniq]; exact ih Γ bs
      | true =>
        cases a with
        | lit _ | erased => simp only [clearBorrowedUniq]; exact ih Γ bs
        | var x =>
          simp only [clearBorrowedUniq]
          split
          · exact ih Γ bs
          · exact ih (Γ.clearUniq x) bs

theorem clearBorrowedUniq_avoids (Γ : Ctx) (bs : List Bool) (args : List Arg) {z : Var}
    (hu : (Γ.clearBorrowedUniq bs args).isUniq z = true)
    (hi : (Γ.clearBorrowedUniq bs args).isImm z = false) :
    ∀ a, a ∈ (bs.zip args).filterMap (fun p => if p.1 then some p.2 else none) → a ≠ .var z := by
  induction args generalizing Γ bs with
  | nil => intro _ hm; simp at hm
  | cons a as ih =>
    cases bs with
    | nil => intro _ hm; simp at hm
    | cons b bs =>
      cases b with
      | false =>
        simp only [clearBorrowedUniq] at hu hi
        exact ih Γ bs hu hi
      | true =>
        intro a' hm
        simp only [List.zip_cons_cons, List.filterMap_cons, ↓reduceIte, List.mem_cons] at hm
        cases a with
        | lit _ =>
          simp only [clearBorrowedUniq] at hu hi
          rcases hm with rfl | hm
          · intro h; cases h
          · exact ih Γ bs hu hi a' hm
        | erased =>
          simp only [clearBorrowedUniq] at hu hi
          rcases hm with rfl | hm
          · intro h; cases h
          · exact ih Γ bs hu hi a' hm
        | var x =>
          simp only [clearBorrowedUniq] at hu hi
          split at hu
          · next hix =>
            simp only [hix, ↓reduceIte] at hi
            rcases hm with rfl | hm
            · intro h; cases h
              have hw := clearBorrowedUniq_weaker Γ bs as
              rw [hw.isImm z, hix] at hi; cases hi
            · exact ih Γ bs hu hi a' hm
          · next hix =>
            simp only [hix, ↓reduceIte] at hi
            rcases hm with rfl | hm
            · intro h; cases h
              have hw := clearBorrowedUniq_weaker (Γ.clearUniq z) bs as
              have huz := hw.isUniq z hu
              simp [isUniq_clearUniq] at huz
            · exact ih (Γ.clearUniq x) bs hu hi a' hm

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

theorem takeOwnedArgs_nil (Γ : Ctx) (args : List Arg) :
    Γ.takeOwnedArgs [] args = Γ.takeArgs args := by
  induction args generalizing Γ with
  | nil => rfl
  | cons a as ih =>
    simp only [takeOwnedArgs, takeArgs]
    cases Γ.takeArg a <;> simp [ih]

theorem takeOwnedArgs_weaker {Γ Γ' : Ctx} {bs : List Bool} {args : List Arg}
    (h : Γ.takeOwnedArgs bs args = .ok Γ') : Weaker Γ' Γ := by
  induction args generalizing Γ bs with
  | nil => cases h; exact Weaker.refl _
  | cons a as ih =>
    cases bs with
    | nil =>
      rw [takeOwnedArgs_nil] at h; exact takeArgs_weaker h
    | cons b bs =>
      cases b with
      | true => exact ih h
      | false =>
        simp only [takeOwnedArgs] at h
        cases ha : Γ.takeArg a with
        | error e => rw [ha] at h; cases h
        | ok Γ₁ => rw [ha] at h; exact (ih h).trans (takeArg_weaker ha)

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
      (Γ.isImm x = false ∧ (0 < Γ.tokens x ∨ Γ.isPbrw x = true) ∧ Γ' = (Γ.clearUniq x).addOwn x 1) ∨
      (Γ.isImm x = false ∧ Γ.tokens x = 0 ∧ Γ.isPbrw x = false ∧ Γ.borrowed x = true ∧
        Γ' = ({ Γ with brw := Γ.brw.erase x, uniq := Γ.uniq.erase x } : Ctx).addOwn x 1)) := by
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
        exact Or.inr (Or.inl ⟨rfl, Or.inl ht, h.symm⟩)
      · simp only [ht, ↓reduceIte] at h
        cases hp : Γ.isPbrw x with
        | true =>
          simp only [hp, ↓reduceIte, Except.ok.injEq] at h
          exact Or.inr (Or.inl ⟨rfl, Or.inr rfl, h.symm⟩)
        | false =>
          simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
          cases hb : Γ.borrowed x with
          | true =>
            simp only [hb, ↓reduceIte, Except.ok.injEq] at h
            exact Or.inr (Or.inr ⟨rfl, by omega, rfl, rfl, h.symm⟩)
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

theorem Tokens.setImmUniq {Γ : Ctx} {toks : List Var} (h : Tokens Γ toks) (x : Var) :
    Tokens (Γ.setImmUniq x) (toks.filter (fun y => y != x)) :=
  (h.setImm x).same rfl rfl

theorem Tokens.addUniqOwn {Γ : Ctx} {toks : List Var} (h : Tokens Γ toks) (x : Var) :
    Tokens (Γ.addUniqOwn x) (x :: toks) :=
  (h.addOwn x).same rfl rfl

/-! ## Reset slot keys -/

/-- `skeys` lists the currently live reset slot ids in `Γ.rset`, without duplicates. -/
structure SlotKeys (Γ : Ctx) (skeys : List Nat) : Prop where
  nodup : skeys.Nodup
  mem : ∀ s, s ∈ skeys ↔ Γ.rset.contains s = true

theorem SlotKeys.empty {Γ : Ctx} (hr : Γ.rset = .leaf) : SlotKeys Γ [] :=
  ⟨List.nodup_nil, fun s => by simp [hr, Src.NatMap.contains, Src.NatMap.get?]⟩

theorem SlotKeys.same {Γ Γ' : Ctx} {skeys : List Nat} (h : SlotKeys Γ skeys)
    (hr : Γ'.rset = Γ.rset) : SlotKeys Γ' skeys :=
  ⟨h.nodup, fun s => by rw [hr]; exact h.mem s⟩

theorem SlotKeys.insert {Γ Γ' : Ctx} {skeys : List Nat} {s : Nat} {v : Nat × Bool}
    (h : SlotKeys Γ skeys) (hfresh : Γ.rset.contains s = false)
    (hr : Γ'.rset = Γ.rset.insert s v) : SlotKeys Γ' (s :: skeys) := by
  have hnot : s ∉ skeys := fun hm => by
    have := (h.mem s).mp hm; rw [hfresh] at this; cases this
  refine ⟨List.nodup_cons.mpr ⟨hnot, h.nodup⟩, fun s' => ?_⟩
  rw [hr, List.mem_cons, h.mem s']
  simp only [Src.NatMap.contains, Src.NatMap.get?_insert]
  by_cases he : s' = s
  · simp [he]
  · simp [he]

theorem SlotKeys.erase {Γ Γ' : Ctx} {skeys : List Nat} {s : Nat}
    (h : SlotKeys Γ skeys) (hhas : Γ.rset.contains s = true)
    (hr : Γ'.rset = Γ.rset.erase s) : s ∈ skeys ∧ SlotKeys Γ' (skeys.erase s) := by
  have hm : s ∈ skeys := (h.mem s).mpr hhas
  refine ⟨hm, h.nodup.erase s, fun s' => ?_⟩
  rw [hr, h.nodup.mem_erase_iff, h.mem s']
  simp only [Src.NatMap.contains, Src.NatMap.get?_erase]
  by_cases he : s' = s
  · simp [he]
  · simp [he]

theorem SlotKeys.closed_nil {Γ : Ctx} {skeys : List Nat} (h : SlotKeys Γ skeys)
    (hempty : mapIsEmpty Γ.rset = true) : skeys = [] := by
  cases skeys with
  | nil => rfl
  | cons s rest =>
    have hc := (h.mem s).mp List.mem_cons_self
    have hn := mapIsEmpty_get?_none hempty s
    simp [Src.NatMap.contains, hn] at hc

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

theorem entryOwned_sublist : ∀ (ps : List Var) (bs : List Bool), (entryOwned ps bs).Sublist ps
  | [], _ => .slnil
  | p :: ps, false :: bs => .cons_cons p (entryOwned_sublist ps bs)
  | p :: ps, true :: bs => .cons p (entryOwned_sublist ps bs)
  | p :: ps, [] => .refl (p :: ps)

theorem entryBorrowed_sublist : ∀ (ps : List Var) (bs : List Bool), (entryBorrowed ps bs).Sublist ps
  | [], _ => .slnil
  | p :: ps, true :: bs => .cons_cons p (entryBorrowed_sublist ps bs)
  | p :: ps, false :: bs => .cons p (entryBorrowed_sublist ps bs)
  | p :: ps, [] => List.nil_sublist (p :: ps)

theorem entryOwned_all_false : ∀ (ps : List Var) (bs : List Bool),
    bs.all (!·) = true → entryOwned ps bs = ps
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: ps, b :: bs, h => by
    cases b
    · simp only [entryOwned]; congr 1; exact entryOwned_all_false ps bs (by simpa using h)
    · simp at h

theorem entryBorrowed_all_false : ∀ (ps : List Var) (bs : List Bool),
    bs.all (!·) = true → entryBorrowed ps bs = []
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: ps, b :: bs, h => by
    cases b
    · simp only [entryBorrowed]; exact entryBorrowed_all_false ps bs (by simpa using h)
    · simp at h

theorem entryUnique_sublist_owned : ∀ (ps : List Var) (bs us : List Bool),
    (entryUnique ps bs us).Sublist (entryOwned ps bs)
  | [], _, _ => .slnil
  | _ :: ps, true :: bs, _ :: us => entryUnique_sublist_owned ps bs us
  | _ :: ps, true :: bs, [] => entryUnique_sublist_owned ps bs []
  | p :: ps, false :: bs, true :: us => .cons_cons p (entryUnique_sublist_owned ps bs us)
  | p :: ps, false :: bs, false :: us => .cons p (entryUnique_sublist_owned ps bs us)
  | p :: ps, false :: bs, [] => .cons p (entryUnique_sublist_owned ps bs [])
  | p :: ps, [], true :: us => by
    have h := entryUnique_sublist_owned ps [] us
    rw [entryOwned_all_false ps [] rfl] at h
    exact .cons_cons p h
  | p :: ps, [], false :: us => by
    have h := entryUnique_sublist_owned ps [] us
    rw [entryOwned_all_false ps [] rfl] at h
    exact .cons p h
  | p :: ps, [], [] => List.nil_sublist (p :: ps)

theorem entryUnique_sublist (ps : List Var) (bs us : List Bool) :
    (entryUnique ps bs us).Sublist ps :=
  (entryUnique_sublist_owned ps bs us).trans (entryOwned_sublist ps bs)

theorem entryUnique_all_false : ∀ (ps : List Var) (bs us : List Bool),
    us.all (!·) = true → entryUnique ps bs us = []
  | [], _, _, _ => rfl
  | _ :: _, [], [], _ => rfl
  | _ :: ps, true :: bs, [], _ => entryUnique_all_false ps bs [] rfl
  | _ :: ps, false :: bs, [], _ => entryUnique_all_false ps bs [] rfl
  | _ :: ps, true :: bs, _ :: us, h =>
    entryUnique_all_false ps bs us (by simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2)
  | _ :: ps, false :: bs, b :: us, h => by
    cases b
    · exact entryUnique_all_false ps bs us (by simpa using h)
    · simp at h
  | _ :: ps, [], b :: us, h => by
    cases b
    · exact entryUnique_all_false ps [] us (by simpa using h)
    · simp at h

theorem entryWith_all_false_us (ps : List Var) (bs us : List Bool)
    (hb : bs.all (!·) = true) (hu : us.all (!·) = true) :
    entryWith ps bs us = entry ps := by
  simp [entryWith, entry, entryOwned_all_false ps bs hb, entryBorrowed_all_false ps bs hb,
    entryUnique_all_false ps bs us hu, Src.NatMap.ofList]

theorem entryWith_all_false (ps : List Var) (bs : List Bool) (h : bs.all (!·) = true) :
    entryWith ps bs = entry ps :=
  entryWith_all_false_us ps bs [] h rfl

theorem Tokens.entryWith (params : List Var) (bs : List Bool) (us : List Bool := []) (hn : params.Nodup) :
    Tokens (Ctx.entryWith params bs us) (Ctx.entryOwned params bs) :=
  Tokens.ofList (hn.sublist (entryOwned_sublist params bs)) _ rfl rfl

theorem pbrw_entryWith {params : List Var} {bs : List Bool} (us : List Bool := []) (hn : params.Nodup) (y : Var) :
    (Ctx.entryWith params bs us).isPbrw y = decide (y ∈ Ctx.entryBorrowed params bs) := by
  have hnb : (entryBorrowed params bs).Nodup := hn.sublist (entryBorrowed_sublist params bs)
  have hk : ((entryBorrowed params bs).map (·, ())).map (·.1) = entryBorrowed params bs := by
    simp [List.map_map, Function.comp_def]
  have hnk : (((entryBorrowed params bs).map (·, ())).map (·.1)).Nodup := by rw [hk]; exact hnb
  unfold isPbrw entryWith Src.NatMap.contains
  dsimp only
  by_cases hy : y ∈ entryBorrowed params bs
  · rw [Src.NatMap.get?_ofList hnk (x := ()) (by simpa using hy)]; simp [hy]
  · rw [Src.NatMap.get?_ofList_none hnk (by rw [hk]; exact hy)]; simp [hy]

theorem uniq_entryWith {params : List Var} {bs us : List Bool} (hn : params.Nodup) (y : Var) :
    (Ctx.entryWith params bs us).isUniq y = decide (y ∈ Ctx.entryUnique params bs us) := by
  have hnu : (entryUnique params bs us).Nodup := hn.sublist (entryUnique_sublist params bs us)
  have hk : ((entryUnique params bs us).map (·, ())).map (·.1) = entryUnique params bs us := by
    simp [List.map_map, Function.comp_def]
  have hnk : (((entryUnique params bs us).map (·, ())).map (·.1)).Nodup := by rw [hk]; exact hnu
  unfold isUniq entryWith Src.NatMap.contains
  dsimp only
  by_cases hy : y ∈ entryUnique params bs us
  · rw [Src.NatMap.get?_ofList hnk (x := ()) (by simpa using hy)]; simp [hy]
  · rw [Src.NatMap.get?_ofList_none hnk (by rw [hk]; exact hy)]; simp [hy]

theorem takeOwnedUniqueArgs_nil_us (Γ : Ctx) (bs : List Bool) (args : List Arg) :
    Γ.takeOwnedUniqueArgs bs [] args = Γ.takeOwnedArgs bs args := by
  induction args generalizing Γ bs with
  | nil => rfl
  | cons a as ih =>
    cases bs with
    | nil =>
      simp only [takeOwnedUniqueArgs, takeOwnedArgs]
      cases Γ.takeArg a <;> simp [ih]
    | cons b bs =>
      cases b with
      | true => exact ih Γ bs
      | false =>
        simp only [takeOwnedUniqueArgs, takeOwnedArgs]
        cases Γ.takeArg a <;> simp [ih]

theorem takeOwnedUniqueArgs_weaker {Γ Γ' : Ctx} {bs us : List Bool} {args : List Arg}
    (h : Γ.takeOwnedUniqueArgs bs us args = .ok Γ') : Weaker Γ' Γ := by
  induction args generalizing Γ bs us with
  | nil => cases h; exact Weaker.refl _
  | cons a as ih =>
    cases bs with
    | nil =>
      cases us with
      | nil =>
        simp only [takeOwnedUniqueArgs] at h
        cases ha : Γ.takeArg a with
        | error e => rw [ha] at h; cases h
        | ok Γ₁ => rw [ha] at h; exact (ih h).trans (takeArg_weaker ha)
      | cons u us =>
        cases u with
        | false =>
          simp only [takeOwnedUniqueArgs] at h
          cases ha : Γ.takeArg a with
          | error e => rw [ha] at h; cases h
          | ok Γ₁ => rw [ha] at h; exact (ih h).trans (takeArg_weaker ha)
        | true =>
          cases a with
          | lit _ | erased => exact ih h
          | var x =>
            simp only [takeOwnedUniqueArgs] at h
            cases hu : Γ.isUniq x with
            | false => simp [hu, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
            | true =>
              simp only [hu, ↓reduceIte] at h
              cases ha : Γ.take x with
              | error e => rw [ha] at h; cases h
              | ok Γ₁ => rw [ha] at h; exact (ih h).trans (take_weaker ha)
    | cons b bs =>
      cases b with
      | true =>
        cases us with
        | nil => exact ih h
        | cons _ us => exact ih h
      | false =>
        cases us with
        | nil =>
          simp only [takeOwnedUniqueArgs] at h
          cases ha : Γ.takeArg a with
          | error e => rw [ha] at h; cases h
          | ok Γ₁ => rw [ha] at h; exact (ih h).trans (takeArg_weaker ha)
        | cons u us =>
          cases u with
          | false =>
            simp only [takeOwnedUniqueArgs] at h
            cases ha : Γ.takeArg a with
            | error e => rw [ha] at h; cases h
            | ok Γ₁ => rw [ha] at h; exact (ih h).trans (takeArg_weaker ha)
          | true =>
            cases a with
            | lit _ | erased => exact ih h
            | var x =>
              simp only [takeOwnedUniqueArgs] at h
              cases hu : Γ.isUniq x with
              | false => simp [hu, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
              | true =>
                simp only [hu, ↓reduceIte] at h
                cases ha : Γ.take x with
                | error e => rw [ha] at h; cases h
                | ok Γ₁ => rw [ha] at h; exact (ih h).trans (take_weaker ha)

end Ctx

end IxCC.Own.Plain
