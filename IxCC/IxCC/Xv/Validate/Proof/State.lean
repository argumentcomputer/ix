import IxCC.Xv.Validate.State
import IxCC.Xv.Validate.Proof.NatMap
import IxCC.Lir.Semantics

/-!
# The abstract state's meaning

`AState.Agree a ρ ℓ`: every fact `v ∈ a[l]` holds of the matching
runs, `ρ v = ℓ l`, with both defined. This module proves the facts the
soundness argument needs about the validator's state:

- `Agree` is antitone in `≤` (`Agree.antitone`): a certificate only weakens
  what the checker assumes, so a wrong one is rejected, never trusted;
- each transfer function preserves `Agree` for the matching concrete
  update: a move (`Agree.stepMove`), definitions with clobbers
  (`Agree.define`), releasing the outgoing cells (`Agree.clearOutArgs`), and
  an edge's parallel parameter binding (`Agree.bindParams`, regalloc2's
  symbolic parallel move).

Sets are read by list membership; `VSet.mem`, `insert` and `subset` are only
used in the sound direction, and `erase` is a filter, so no sortedness
invariant is needed. -/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Word Env)

/-! ## Sets -/

namespace VSet

theorem mem_sound {x : VReg} : ∀ {s : VSet}, mem x s = true → x ∈ s
  | [], h => by simp [mem] at h
  | y :: ys, h => by
      unfold mem at h
      by_cases e : x = y
      · simp [e]
      · have : (x == y) = false := by simpa using e
        simp only [this, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · simp at h
        · exact List.mem_cons_of_mem _ (mem_sound h)

theorem mem_insert {x y : VReg} : ∀ {s : VSet}, x ∈ insert y s → x = y ∨ x ∈ s
  | [], h => by simpa [insert] using h
  | z :: zs, h => by
      unfold insert at h
      split at h
      · exact .inr h
      · split at h
        · simp only [List.mem_cons] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr (by simpa using h)
        · simp only [List.mem_cons] at h
          rcases h with h | h
          · exact .inr (by simp [h])
          · rcases mem_insert h with h | h
            · exact .inl h
            · exact .inr (List.mem_cons_of_mem _ h)

theorem mem_erase {x y : VReg} {s : VSet} : x ∈ VSet.erase y s ↔ x ∈ s ∧ x ≠ y := by
  unfold VSet.erase
  simp [List.mem_filter]

theorem subset_sound {xs ys : VSet} (h : subset xs ys = true) {x : VReg} (hx : x ∈ xs) :
    x ∈ ys := by
  unfold subset at h
  rw [List.all_eq_true] at h
  exact mem_sound (h x hx)

end VSet

/-! ## Location keys -/

/-- The register with encoding number `n` (a left inverse of `gprIndex`). -/
def gprOfIndex : Nat → X86.GPR
  | 0 => .rax | 1 => .rcx | 2 => .rdx | 3 => .rbx | 4 => .rsp | 5 => .rbp | 6 => .rsi | 7 => .rdi
  | 8 => .r8 | 9 => .r9 | 10 => .r10 | 11 => .r11 | 12 => .r12 | 13 => .r13 | 14 => .r14
  | _ => .r15

theorem gprOfIndex_gprIndex (r : X86.GPR) : gprOfIndex (gprIndex r) = r := by
  cases r <;> rfl

theorem gprIndex_inj {r r' : X86.GPR} (h : gprIndex r = gprIndex r') : r = r' := by
  have := congrArg gprOfIndex h
  rwa [gprOfIndex_gprIndex, gprOfIndex_gprIndex] at this

theorem gprIndex_lt (r : X86.GPR) : gprIndex r < 16 := by
  cases r <;> decide

theorem locKey_inj {l l' : Loc} (h : locKey l = locKey l') : l = l' := by
  cases l <;> cases l' <;> simp only [locKey] at h
  all_goals first
    | (rename_i r r'; rw [gprIndex_inj h])
    | (rename_i r i; have := gprIndex_lt r; omega)
    | (rename_i i r; have := gprIndex_lt r; omega)
    | (congr 1; omega)
    | omega

theorem locKey_eq_iff {l l' : Loc} : locKey l = locKey l' ↔ l = l' :=
  ⟨locKey_inj, fun h => h ▸ rfl⟩

theorem isOutArgKey_iff (k : Nat) : isOutArgKey k = true ↔ 18 ≤ k ∧ (k - 18) % 3 = 0 := by
  unfold isOutArgKey
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨of_decide_eq_true h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨decide_eq_true h1, h2⟩

theorem isOutArgKey_locKey (l : Loc) : isOutArgKey (locKey l) = true ↔ ∃ i, l = .outArg i := by
  rw [isOutArgKey_iff]
  cases l with
  | reg r =>
    have := gprIndex_lt r
    simp only [locKey, reduceCtorEq, exists_false, iff_false]
    omega
  | slot i => simp only [locKey, reduceCtorEq, exists_false, iff_false]; omega
  | inArg i => simp only [locKey, reduceCtorEq, exists_false, iff_false]; omega
  | outArg i => simp [locKey]

/-! ## Reading a state -/

namespace AState

theorem get_set (a : AState) (l : Loc) (vs : VSet) (l' : Loc) :
    (a.set l vs).get l' = if l' = l then vs else a.get l' := by
  unfold set get
  cases vs with
  | nil =>
    rw [NatMap.find?_erase]
    by_cases h : l' = l
    · simp [h]
    · simp [h, locKey_eq_iff]
  | cons v vs =>
    simp only
    rw [NatMap.find?_insert]
    by_cases h : l' = l
    · simp [h]
    · simp [h, locKey_eq_iff]

theorem get_stepMove (a : AState) (dst src l : Loc) :
    (a.stepMove dst src).get l = if l = dst then a.get src else a.get l :=
  get_set _ _ _ _

theorem get_forget (a : AState) (v : VReg) (l : Loc) :
    (a.forget v).get l = VSet.erase v (a.get l) := by
  unfold forget get
  rw [NatMap.find?_filterMap]
  cases a.find? (locKey l) with
  | none => rfl
  | some vs =>
    simp only [Option.bind_some, Option.getD_some]
    split <;> simp_all

theorem get_clear (a : AState) (l l' : Loc) :
    (a.clear l).get l' = if l' = l then [] else a.get l' := by
  unfold clear get
  rw [NatMap.find?_erase]
  by_cases h : l' = l
  · simp [h]
  · simp [h, locKey_eq_iff]

theorem get_clearOutArgs (a : AState) (l : Loc) :
    (a.clearOutArgs).get l = if isOutArgKey (locKey l) then [] else a.get l := by
  unfold clearOutArgs get
  rw [NatMap.find?_filterMap]
  cases a.find? (locKey l) with
  | none => split <;> rfl
  | some vs => by_cases h : isOutArgKey (locKey l) <;> simp [h]

theorem mem_get_le {a b : AState} (h : a.le b = true) {l : Loc} {x : VReg}
    (hx : x ∈ a.get l) : x ∈ b.get l := by
  unfold get at hx ⊢
  cases hk : a.find? (locKey l) with
  | none => simp [hk] at hx
  | some vs =>
    rw [hk, Option.getD_some] at hx
    exact VSet.subset_sound (NatMap.all_find? h hk) hx

theorem mem_get_of_holds {a : AState} {l : Loc} {v : VReg} (h : a.holds l v = true) :
    v ∈ a.get l :=
  VSet.mem_sound h

/-! ### Definitions -/

theorem mem_get_setFold {x : VReg} {l : Loc} :
    ∀ {defs : List (VReg × Loc)} {b : AState},
      x ∈ (defs.foldl (fun a (d : VReg × Loc) => a.set d.2 [d.1]) b).get l →
      (x, l) ∈ defs ∨ (l ∉ defs.map (·.2) ∧ x ∈ b.get l)
  | [], _, h => .inr ⟨by simp, h⟩
  | (v, l') :: rest, b, h => by
      simp only [List.foldl_cons] at h
      rcases mem_get_setFold h with h1 | ⟨hl, h2⟩
      · exact .inl (List.mem_cons_of_mem _ h1)
      · rw [get_set] at h2
        by_cases e : l = l'
        · subst e
          simp only [↓reduceIte, List.mem_singleton] at h2
          subst h2
          exact .inl (by simp)
        · simp only [e, ↓reduceIte] at h2
          refine .inr ⟨?_, h2⟩
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨e, hl⟩

theorem mem_get_clearFold {x : VReg} {l : Loc} :
    ∀ {clobbers : List Loc} {b : AState},
      x ∈ (clobbers.foldl clear b).get l → l ∉ clobbers ∧ x ∈ b.get l
  | [], _, h => ⟨by simp, h⟩
  | c :: rest, b, h => by
      simp only [List.foldl_cons] at h
      obtain ⟨hl, h⟩ := mem_get_clearFold h
      rw [get_clear] at h
      split at h
      · simp at h
      · rename_i e
        exact ⟨by simp [e, hl], h⟩

theorem mem_get_forgetFold {x : VReg} {l : Loc} :
    ∀ {defs : List (VReg × Loc)} {b : AState},
      x ∈ (defs.foldl (fun a (d : VReg × Loc) => a.forget d.1) b).get l →
      x ∈ b.get l ∧ x ∉ defs.map (·.1)
  | [], _, h => ⟨h, by simp⟩
  | (v, l') :: rest, b, h => by
      simp only [List.foldl_cons] at h
      obtain ⟨h, hx⟩ := mem_get_forgetFold h
      rw [get_forget, VSet.mem_erase] at h
      refine ⟨h.1, ?_⟩
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨h.2, hx⟩

theorem mem_get_define {a : AState} {defs : List (VReg × Loc)} {clobbers : List Loc}
    {l : Loc} {x : VReg} (h : x ∈ (a.define defs clobbers).get l) :
    (x, l) ∈ defs ∨
      (l ∉ defs.map (·.2) ∧ l ∉ clobbers ∧ x ∈ a.get l ∧ x ∉ defs.map (·.1)) := by
  unfold define at h
  rcases mem_get_setFold h with h | ⟨hl, h⟩
  · exact .inl h
  · obtain ⟨hc, h⟩ := mem_get_clearFold h
    obtain ⟨h, hx⟩ := mem_get_forgetFold h
    exact .inr ⟨hl, hc, h, hx⟩

/-! ### Parameter binding -/

theorem mem_gainFold {vs : VSet} {x : VReg} :
    ∀ {pairs : List (VReg × VReg)} {s : VSet},
      x ∈ pairs.foldl (fun s (d : VReg × VReg) => if VSet.mem d.2 vs then VSet.insert d.1 s else s) s →
      x ∈ s ∨ ∃ y, (x, y) ∈ pairs ∧ y ∈ vs
  | [], _, h => .inl h
  | (p, y) :: rest, s, h => by
      simp only [List.foldl_cons] at h
      rcases mem_gainFold h with h | ⟨y', hy', hv⟩
      · split at h
        · rename_i hm
          rcases VSet.mem_insert h with h | h
          · subst h
            exact .inr ⟨y, by simp, VSet.mem_sound hm⟩
          · exact .inl h
        · exact .inl h
      · exact .inr ⟨y', List.mem_cons_of_mem _ hy', hv⟩

theorem mem_get_bindParams {a : AState} {params args : List VReg} {l : Loc} {x : VReg}
    (h : x ∈ (a.bindParams params args).get l) :
    (x ∈ a.get l ∧ x ∉ params) ∨ ∃ y, (x, y) ∈ params.zip args ∧ y ∈ a.get l := by
  unfold bindParams get at h
  rw [NatMap.find?_filterMap] at h
  unfold get
  cases hk : a.find? (locKey l) with
  | none => simp [hk] at h
  | some vs =>
    rw [hk, Option.bind_some] at h
    simp only [Option.getD_some]
    have hx : x ∈ (params.zip args).foldl
        (fun s (d : VReg × VReg) => if VSet.mem d.2 vs then VSet.insert d.1 s else s)
        (vs.filter fun v => !params.contains v) := by
      revert h
      dsimp only
      generalize List.foldl _ _ _ = gs
      cases gs <;> simp
    rcases mem_gainFold hx with hx | hx
    · rw [List.mem_filter] at hx
      refine .inl ⟨hx.1, fun hm => ?_⟩
      have := hx.2
      rw [List.contains_iff_mem.2 hm] at this
      simp at this
    · exact .inr hx

end AState

/-! ## Agreement -/

/-- The meaning of an abstract state: each fact `v ∈ a[l]` holds of
the Xv environment `ρ` and the Xl locations `ℓ`, both defined. -/
def AState.Agree (a : AState) (ρ : Env) (ℓ : Loc → Option Word) : Prop :=
  ∀ l v, v ∈ a.get l → ∃ w, ρ[v]? = some w ∧ ℓ l = some w

namespace AState.Agree

variable {a b : AState} {ρ ρ' : Env} {ℓ ℓ' : Loc → Option Word}

theorem holds (h : a.Agree ρ ℓ) {l : Loc} {v : VReg} (hv : a.holds l v = true) :
    ∃ w, ρ[v]? = some w ∧ ℓ l = some w :=
  h l v (mem_get_of_holds hv)

/-- `Agree` is antitone: a state below an agreeing one agrees. -/
theorem antitone (hle : b.le a = true) (h : a.Agree ρ ℓ) : b.Agree ρ ℓ :=
  fun l v hv => h l v (mem_get_le hle hv)

theorem empty : AState.empty.Agree ρ ℓ := fun l v hv => by
  simp [AState.empty, get] at hv

theorem stepMove (h : a.Agree ρ ℓ) {dst src : Loc} (hdst : ℓ' dst = ℓ src)
    (hother : ∀ l, l ≠ dst → ℓ' l = ℓ l) : (a.stepMove dst src).Agree ρ ℓ' := by
  intro l v hv
  rw [get_stepMove] at hv
  split at hv
  · rename_i e
    subst e
    rw [hdst]
    exact h _ _ hv
  · rename_i e
    rw [hother l e]
    exact h _ _ hv

/-- A single fact that holds may be set. -/
theorem set_single (h : a.Agree ρ ℓ) {l : Loc} {v : VReg} (hv : ∃ w, ρ[v]? = some w ∧ ℓ l = some w) :
    (a.set l [v]).Agree ρ ℓ := by
  intro l' x hx
  rw [get_set] at hx
  split at hx
  · rename_i e
    subst e
    simp only [List.mem_singleton] at hx
    subst hx
    exact hv
  · exact h _ _ hx

/-- Definitions and clobbers: each definition `(v, l)` holds after the
instruction, other registers keep their values, and locations other than the
definitions' and the clobbered ones keep theirs. -/
theorem define (h : a.Agree ρ ℓ) {defs : List (VReg × Loc)} {clobbers : List Loc}
    (hdef : ∀ v l, (v, l) ∈ defs → ∃ w, ρ'[v]? = some w ∧ ℓ' l = some w)
    (hρ : ∀ v, v ∉ defs.map (·.1) → ρ'[v]? = ρ[v]?)
    (hℓ : ∀ l, l ∉ defs.map (·.2) → l ∉ clobbers → ℓ' l = ℓ l) :
    (a.define defs clobbers).Agree ρ' ℓ' := by
  intro l x hx
  rcases mem_get_define hx with hx | ⟨hl, hc, hx, hxd⟩
  · exact hdef _ _ hx
  · rw [hρ x hxd, hℓ l hl hc]
    exact h _ _ hx

/-- Releasing the outgoing cells: the other locations keep their values. -/
theorem clearOutArgs (h : a.Agree ρ ℓ) (hℓ : ∀ l, (∀ i, l ≠ .outArg i) → ℓ' l = ℓ l) :
    (a.clearOutArgs).Agree ρ ℓ' := by
  intro l x hx
  rw [get_clearOutArgs] at hx
  split at hx
  · simp at hx
  · rename_i hk
    have : ∀ i, l ≠ .outArg i := fun i e => hk ((isOutArgKey_locKey l).2 ⟨i, e⟩)
    rw [hℓ l this]
    exact h _ _ hx

end AState.Agree

/-! ## Parameter binding -/

/-- Reading registers `args` gives `vals` position by position. -/
theorem mapM_zip {ρ : Env} :
    ∀ {params args : List VReg} {vals : List Word}, args.mapM (ρ[·]?) = some vals →
      ∀ {x y : VReg}, (x, y) ∈ params.zip args → ∃ w, (x, w) ∈ params.zip vals ∧ ρ[y]? = some w
  | [], _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | p :: ps, a :: as, vals, hm, x, y, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hm
      obtain ⟨w, hw, ws, hws, rfl⟩ := hm
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨w, by simp, hw⟩
      · obtain ⟨w', hw', h'⟩ := mapM_zip hws h
        exact ⟨w', List.mem_cons_of_mem _ hw', h'⟩

/-- Binding leaves other registers alone. -/
theorem bindParams_other {x : VReg} :
    ∀ {ρ ρ' : Env} {params : List VReg} {vals : List Word},
      Lir.bindParams ρ params vals = some ρ' → x ∉ params → ρ'[x]? = ρ[x]?
  | _, _, [], [], h, _ => by cases h; rfl
  | _, _, [], _ :: _, h, _ => by simp [Lir.bindParams] at h
  | _, _, _ :: _, [], h, _ => by simp [Lir.bindParams] at h
  | ρ, ρ', p :: ps, v :: vs, h, hx => by
      simp only [Lir.bindParams] at h
      simp only [List.mem_cons, not_or] at hx
      rw [bindParams_other h hx.2, Std.HashMap.getElem?_insert]
      have : (p == x) = false := by simpa [beq_iff_eq] using fun e => hx.1 e.symm
      simp [this]

/-- With distinct parameters, each is bound to its value. -/
theorem bindParams_zip :
    ∀ {ρ ρ' : Env} {params : List VReg} {vals : List Word},
      params.Nodup → Lir.bindParams ρ params vals = some ρ' →
      ∀ {x : VReg} {w : Word}, (x, w) ∈ params.zip vals → ρ'[x]? = some w
  | _, _, [], _, _, _, _, _, h => by simp at h
  | _, _, _ :: _, [], _, _, _, _, h => by simp at h
  | ρ, ρ', p :: ps, v :: vs, hnd, hb, x, w, h => by
      simp only [Lir.bindParams] at hb
      rw [List.nodup_cons] at hnd
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · rw [bindParams_other hb hnd.1]
        simp
      · exact bindParams_zip hnd.2 hb h

theorem bindParams_length :
    ∀ {ρ ρ' : Env} {params : List VReg} {vals : List Word},
      Lir.bindParams ρ params vals = some ρ' → params.length = vals.length
  | _, _, [], [], _ => rfl
  | _, _, [], _ :: _, h => by simp [Lir.bindParams] at h
  | _, _, _ :: _, [], h => by simp [Lir.bindParams] at h
  | _, _, _ :: _, _ :: _, h => by
      simp only [Lir.bindParams] at h
      simp [bindParams_length h]

/-- An edge's parallel binding (regalloc2's symbolic parallel move):
the parameters take the arguments' values, read before any is written. -/
theorem AState.Agree.bindParams {a : AState} {ρ ρ' : Env} {ℓ : Loc → Option Word}
    (h : a.Agree ρ ℓ) {params args : List VReg} {vals : List Word} (hnd : params.Nodup)
    (hargs : args.mapM (ρ[·]?) = some vals) (hbind : Lir.bindParams ρ params vals = some ρ') :
    (a.bindParams params args).Agree ρ' ℓ := by
  intro l x hx
  rcases AState.mem_get_bindParams hx with ⟨hx, hxp⟩ | ⟨y, hxy, hy⟩
  · rw [bindParams_other hbind hxp]
    exact h _ _ hx
  · obtain ⟨w, hw, hyw⟩ := h _ _ hy
    obtain ⟨w', hw', hyw'⟩ := mapM_zip (params := params) hargs hxy
    rw [hw] at hyw'
    cases hyw'
    exact ⟨w, bindParams_zip hnd hbind hw', hyw⟩

end IxCC.Xv.Validate
