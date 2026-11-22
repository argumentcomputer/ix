import IxCC.Xv.Select.Proof.Pending

/-!
# A selected block

`selectBlock` selects the terminator first, then the statements from last to
first, skipping consumed ones. `selectBlock_spec` describes the result: the
Xv body is one segment per Lir statement (empty for a consumed statement)
followed by the terminator's prefix (`BlockSel`); each segment is a
selection of its statement at its site from a state with fresh registers at
or above the block's first, the terminator likewise; and every consumed
statement is an assignment named by the block's definition sites.
-/

namespace IxCC.Xv.Select.Proof

open IxCC.Lir (VReg Word Env)
open IxCC.Xv.Select

/-! ## The state monad of the driver -/

theorem sbind_ok {α β : Type} {f : StateT St (Except Error) α} {g : α → StateT St (Except Error) β} {st st'' : St}
    {b : β} : (f >>= g) st = .ok (b, st'') ↔ ∃ a st', f st = .ok (a, st') ∧ g a st' = .ok (b, st'') := by
  show (do let (a, s) ← f st; g a s) = _ ↔ _
  cases h : f st with
  | error e => simp [bind, Except.bind]
  | ok p =>
    obtain ⟨a, s⟩ := p
    simp only [bind, Except.bind, Except.ok.injEq]
    constructor
    · intro hg; exact ⟨a, s, rfl, hg⟩
    · rintro ⟨a', s', he, hg⟩
      cases he
      exact hg

@[simp] theorem sget_bind {β : Type} (g : St → StateT St (Except Error) β) (st : St) :
    ((get : StateT St (Except Error) St) >>= g) st = g st st := rfl

@[simp] theorem smodify_bind {β : Type} (f : St → St) (g : PUnit → StateT St (Except Error) β) (st : St) :
    ((modify f : StateT St (Except Error) PUnit) >>= g) st = g ⟨⟩ (f st) := rfl

@[simp] theorem spure_run {α : Type} (a : α) (st : St) : (pure a : StateT St (Except Error) α) st = .ok (a, st) := rfl

/-! ## Block contexts -/

/-- The context `selectBlock` selects a block in. -/
def blockCtx (fn : Lir.FunId) (uses : NatMap Nat) (label : Lir.Label) (body : List Lir.Stmt) : Ctx :=
  { fn, label, size := body.length, uses, defs := defSites body, effects := effectSites body, body }

theorem blockCtx_ok (fn : Lir.FunId) (uses : NatMap Nat) (label : Lir.Label) (body : List Lir.Stmt) :
    BlockCtx (blockCtx fn uses label body) := ⟨rfl, rfl⟩

/-- A statement's selection extends the state with folds of its site. -/
theorem selectStmt_ext {i : Nat} {s : Lir.Stmt} {c : Ctx} {st st' : St} {is : List (Inst VReg)} (hi : c.pos = i)
    (h : selectStmt i s c st = .ok (is, st')) : Ext c st st' := by
  cases s with
  | assign x r => exact (selectStmt_ok hi rfl h).1
  | store w m a => exact (selectStmt_ok hi rfl h).1
  | call rs f as =>
    obtain ⟨_, _, _, hn, hc, -⟩ := selectCall_spec h
    exact Ext.of_le hn hc

theorem zipIdx_take_succ {body : List Lir.Stmt} {k : Nat} {s : Lir.Stmt} (hs : body[k]? = some s) :
    (body.zipIdx.take (k + 1)).reverse = (s, k) :: (body.zipIdx.take k).reverse := by
  rw [List.take_add_one, List.reverse_append]
  have : body.zipIdx[k]? = some (s, k) := by
    simp [List.getElem?_zipIdx, hs]
  rw [this]
  rfl

/-- The selection of a block's statements before position `k`, last first. -/
theorem selectStmts_spec (c : Ctx) :
    ∀ (k : Nat) (out : List (Inst VReg)) (st st' : St) (out' : List (Inst VReg)),
      k ≤ c.body.length →
      selectStmts c ((c.body.zipIdx.take k).reverse) out st = .ok (out', st') →
      ∃ segs : List (List (Inst VReg)), segs.length = k ∧ out' = segs.flatten ++ out ∧ st.next ≤ st'.next ∧
        (∀ j ∈ st.consumed, j ∈ st'.consumed) ∧
        (∀ j ∈ st'.consumed, j ∈ st.consumed ∨ (j < k ∧ ∃ (y : VReg) (r : Lir.Rhs), c.defs[y]? = some (j, r))) ∧
        (∀ i < k, i ∈ st'.consumed → segs[i]? = some []) ∧
        (∀ i s, i < k → c.body[i]? = some s → i ∉ st'.consumed →
          ∃ sti sti' seg, st.next ≤ sti.next ∧ segs[i]? = some seg ∧
            selectStmt i s { c with site := some i } sti = .ok (seg, sti'))
  | 0, out, st, st', out', _, h => by
      simp only [List.take_zero, List.reverse_nil, selectStmts, pure, StateT.pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, by simp, Nat.le_refl _, fun j hj => hj, fun j hj => .inl hj, fun i hi => absurd hi (by omega),
        fun i s hi => absurd hi (by omega)⟩
  | k + 1, out, st, st', out', hk, h => by
      obtain ⟨s, hs⟩ : ∃ s, c.body[k]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [zipIdx_take_succ hs] at h
      simp only [selectStmts] at h
      by_cases hc : st.consumed.contains k = true
      · simp only [sget_bind, hc, ↓reduceIte] at h
        obtain ⟨segs, hlen, rfl, hn, hsub, hnew, hskip, hsel⟩ := selectStmts_spec c k out st st' out' (by omega) h
        refine ⟨segs ++ [[]], by simp [hlen], by simp, hn, hsub, fun j hj => ?_, fun i hi hin => ?_, fun i s' hi hs' hin => ?_⟩
        · rcases hnew j hj with h' | ⟨h', h''⟩
          · exact .inl h'
          · exact .inr ⟨by omega, h''⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [List.getElem?_append_left (by omega)]; exact hskip i hi hin
          · rw [List.getElem?_append_right (by omega), hlen]; simp
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · obtain ⟨sti, sti', seg, hle, hseg, hsl⟩ := hsel i s' hi hs' hin
            exact ⟨sti, sti', seg, hle, by rw [List.getElem?_append_left (by omega)]; exact hseg, hsl⟩
          · exact absurd (hsub _ (by simpa using hc)) hin
      · simp only [sget_bind, hc, Bool.false_eq_true, ↓reduceIte] at h
        rw [sbind_ok] at h
        obtain ⟨insts, st₁, h₁, h⟩ := h
        have hext := selectStmt_ext (c := { c with site := some k }) rfl h₁
        obtain ⟨segs, hlen, rfl, hn, hsub, hnew, hskip, hsel⟩ := selectStmts_spec c k _ st₁ st' out' (by omega) h
        obtain ⟨hn₁, F, hF, hfold⟩ := hext
        have hk₁ : k ∉ st₁.consumed := by
          rw [hF]
          intro hk'
          rcases List.mem_append.1 hk' with hk' | hk'
          · have := (hfold k hk').before; simp [Ctx.pos] at this
          · exact hc (by simpa using hk')
        refine ⟨segs ++ [insts], by simp [hlen], by simp, Nat.le_trans hn₁ hn, fun j hj => hsub j (by rw [hF]; simp [hj]),
          fun j hj => ?_, fun i hi hin => ?_, fun i s' hi hs' hin => ?_⟩
        · rcases hnew j hj with h' | ⟨h', h''⟩
          · rw [hF] at h'
            rcases List.mem_append.1 h' with h' | h'
            · obtain ⟨⟨y, r, hd, -, -⟩, hlt⟩ := hfold j h'
              exact .inr ⟨by simp [Ctx.pos] at hlt; omega, y, r, hd⟩
            · exact .inl h'
          · exact .inr ⟨by omega, h''⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [List.getElem?_append_left (by omega)]; exact hskip i hi hin
          · rcases hnew i hin with h' | ⟨h', -⟩
            · exact absurd h' hk₁
            · omega
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · obtain ⟨sti, sti', seg, hle, hseg, hsl⟩ := hsel i s' hi hs' hin
            exact ⟨sti, sti', seg, Nat.le_trans hn₁ hle, by rw [List.getElem?_append_left (by omega)]; exact hseg, hsl⟩
          · rw [hs] at hs'
            cases hs'
            exact ⟨st, st₁, insts, Nat.le_refl _, by rw [List.getElem?_append_right (by omega), hlen]; simp, h₁⟩


/-- What `selectBlock` selected for a block: one segment per statement (empty
for a consumed statement `i ∈ C`), each a selection at its site, and the
terminator's prefix and terminator; `n₀` bounds the fresh registers below. -/
structure BlockSel (c : Ctx) (n₀ : Nat) (term : Lir.Term) (segs : List (List (Inst VReg)))
    (pre : List (Inst VReg)) (xterm : Term VReg) (C : List Nat) : Prop where
  len : segs.length = c.body.length
  cons : ∀ i ∈ C, ∃ (y : VReg) (r : Lir.Rhs), c.defs[y]? = some (i, r)
  skip : ∀ i < c.body.length, i ∈ C → segs[i]? = some []
  stmt : ∀ i s, c.body[i]? = some s → i ∉ C →
    ∃ sti sti' seg, n₀ ≤ sti.next ∧ segs[i]? = some seg ∧ selectStmt i s { c with site := some i } sti = .ok (seg, sti')
  term : ∃ stT stT', n₀ ≤ stT.next ∧ selectTerm term c stT = .ok ((pre, xterm), stT')

theorem selectBlock_spec {fn : Lir.FunId} {uses : NatMap Nat} {label : Lir.Label} {b : Lir.Block} {st₀ st₁ : St}
    {xb : Block VReg} {dl : List VReg} (h : selectBlock fn uses label b st₀ = .ok ((xb, dl), st₁)) :
    st₀.next ≤ st₁.next ∧ xb.params = b.params ∧ xb.cold = b.cold ∧
      ∃ segs pre C, BlockSel (blockCtx fn uses label b.body.toList) st₀.next b.term segs pre xb.term C ∧
        xb.body.toList = segs.flatten ++ pre ∧ dl = consumedDefs b.body.toList C := by
  unfold selectBlock at h
  simp only [smodify_bind] at h
  rw [sbind_ok] at h
  obtain ⟨⟨pre, term⟩, stT, hT, h⟩ := h
  simp only at h
  rw [sbind_ok] at h
  obtain ⟨out, st₂, hS, h⟩ := h
  simp only [sget_bind, spure_run, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  have hT' : selectTerm b.term (blockCtx fn uses label b.body.toList) { st₀ with consumed := [] } =
      .ok ((pre, term), stT) := hT
  have hextT := (selectTerm_ok hT').1
  have hS' : selectStmts (blockCtx fn uses label b.body.toList)
      (((blockCtx fn uses label b.body.toList).body.zipIdx.take (blockCtx fn uses label b.body.toList).body.length).reverse)
      pre stT = .ok (out, st₂) := by
    simpa [blockCtx, List.take_of_length_le] using hS
  obtain ⟨segs, hlen, rfl, hn, hsub, hnew, hskip, hsel⟩ := selectStmts_spec _ _ pre stT st₂ out (Nat.le_refl _) hS'
  obtain ⟨hnT, F, hF, hfold⟩ := hextT
  refine ⟨Nat.le_trans (by simpa using hnT) hn, rfl, rfl, segs, pre, st₂.consumed, ⟨hlen, ?_, hskip, ?_, ?_⟩,
    by simp, rfl⟩
  · intro i hi
    rcases hnew i hi with h' | ⟨-, h'⟩
    · rw [hF] at h'
      simp only [List.append_nil] at h'
      obtain ⟨⟨y, r, hd, -, -⟩, -⟩ := hfold i h'
      exact ⟨y, r, hd⟩
    · exact h'
  · intro i s hs hin
    obtain ⟨sti, sti', seg, hle, hseg, hsl⟩ := hsel i s (by
      have := (List.getElem?_eq_some_iff.1 hs).1; exact this) hs hin
    exact ⟨sti, sti', seg, Nat.le_trans (by simpa using hnT) hle, hseg, hsl⟩
  · exact ⟨{ st₀ with consumed := [] }, stT, Nat.le_refl _, hT'⟩

end IxCC.Xv.Select.Proof
