import IxCC.Rt.Proof.Mono

/-!
# Blocks: the rest of a block's lowering, and fused comparisons

`restAct … is` is what the lowering of a Cfg block does from its
instructions `is` on: `blockCode` for the whole body (`restAct_body`), an
instruction then `restAct` of the rest (`rest_cons`). In a fused block the
comparison is not lowered: the block's `br` decides it, so `restAct` of
`[cmp]` and of `[]` agree. `rest_grows`: the state at any point grows into
the final one.

`Fused T fd y`: `y` is the comparison a fused block branches on. It has
one use in the function (its switch), so no instruction, edge, `ret` or
`tcall` reads it, and no other switch scrutinises it (`fused_once`); Lir
never assigns it, and the register relation leaves it out.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-! ## Fusable blocks -/

theorem unsnoc_some {α : Type} {l init : List α} {last : α} (h : unsnoc l = some (init, last)) :
    l = init ++ [last] := unsnoc_eq h

/-- What a fusable block is. -/
theorem fusable_some {T : Tables} {uses : NatMap Nat} {b : Cfg.Block} {init : List Cfg.Instr} {c : Lir.Cond}
    {a a' : Fir.Arg} (h : fusable T uses b = some (init, c, a, a')) :
    ∃ x op alts d, b.body = init ++ [.bind x (.fir (.prim op [a, a']))] ∧ compareOf op = some c ∧
      b.term = .switch x alts d ∧ uses.getD x 0 = 1 ∧
      ∀ p ∈ alts, T.known.boolTrue = some p.1 ∨ T.known.boolFalse = some p.1 := by
  unfold fusable at h
  split at h
  · rename_i init' x op a₁ a₁' y alts d' hu ht
    split at h
    · rename_i c' hc
      dsimp only at h
      split at h
      · rename_i hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hcond
        obtain ⟨⟨rfl, hu1⟩, hall⟩ := hcond
        exact ⟨x, op, alts, d', unsnoc_eq hu, hc, ht, hu1, fun p hp => hall p hp⟩
      · cases h
    · cases h
  · cases h

/-! ## The rest of a block -/

/-- The rest of a block's lowering, from its instructions `is` on. -/
def restAct (f : Fir.FunId) (T : Tables) (uses : NatMap Nat) (src : Nat) (b : Cfg.Block)
    (is : List Cfg.Instr) : M Unit :=
  match fusable T uses b with
  | some (_, c, a, a') => do if ← instrs f T is.dropLast then fusedEnd f T src b c a a'
  | none => do if ← instrs f T is then term f T src b.term

theorem restAct_body (f : Fir.FunId) (T : Tables) (uses : NatMap Nat) (src : Nat) (b : Cfg.Block) :
    restAct f T uses src b b.body = blockCode f T uses src b := by
  unfold restAct blockCode
  cases h : fusable T uses b with
  | none => rfl
  | some p =>
    obtain ⟨init, c, a, a'⟩ := p
    obtain ⟨x, op, -, -, hbody, -⟩ := fusable_some h
    simp only [hbody, List.dropLast_concat]

theorem run_bind_of {α β : Type} {a : M α} {g : α → M β} {s s₁ s' : St} {x : α} {r : β}
    (h₁ : a.run s = .ok (x, s₁)) (h₂ : (g x).run s₁ = .ok (r, s')) : (a >>= g).run s = .ok (r, s') := by
  simp only [StateT.run, bind, StateT.bind, Except.bind] at h₁ h₂ ⊢
  rw [h₁]
  exact h₂

/-- Instructions then a continuation: the first instruction, then the
rest. -/
theorem instrs_then {f : Fir.FunId} {T : Tables} {i : Cfg.Instr} {is : List Cfg.Instr} {k : M Unit} {st stF : St}
    (h : (do if ← instrs f T (i :: is) then k : M Unit).run st = .ok ((), stF)) :
    ∃ b₁ st₁, (instr f T i).run st = .ok (b₁, st₁) ∧
      ((b₁ = true ∧ (do if ← instrs f T is then k : M Unit).run st₁ = .ok ((), stF)) ∨
       (b₁ = false ∧ stF = st₁)) := by
  obtain ⟨bb, st₂, h₁, h₂⟩ := run_bind h
  obtain ⟨b₁, st₁, h₃, h₄⟩ := instrs_cons_run h₁
  rcases h₄ with ⟨hb₁, h₄⟩ | ⟨hb₁, hbb, hst⟩
  · exact ⟨b₁, st₁, h₃, .inl ⟨hb₁, run_bind_of h₄ h₂⟩⟩
  · subst hbb
    subst hst
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h₂
    exact ⟨b₁, st₂, h₃, .inr ⟨hb₁, h₂.2.symm⟩⟩

/-- An instruction, then the rest. -/
theorem rest_cons {f : Fir.FunId} {T : Tables} {uses : NatMap Nat} {src : Nat} {b : Cfg.Block}
    {i : Cfg.Instr} {is : List Cfg.Instr} {st stF : St}
    (h : (restAct f T uses src b (i :: is)).run st = .ok ((), stF))
    (hfused : (fusable T uses b).isSome = true → is ≠ []) :
    ∃ b₁ st₁, (instr f T i).run st = .ok (b₁, st₁) ∧
      ((b₁ = true ∧ (restAct f T uses src b is).run st₁ = .ok ((), stF)) ∨ (b₁ = false ∧ stF = st₁)) := by
  unfold restAct at h ⊢
  cases hf : fusable T uses b with
  | none => simp only [hf] at h ⊢; exact instrs_then h
  | some p =>
    obtain ⟨init, c, a, a'⟩ := p
    simp only [hf] at h ⊢
    have hne := hfused (by simp [hf])
    rw [List.dropLast_cons_of_ne_nil hne] at h
    exact instrs_then h

theorem fusedEnd_grows {f : Fir.FunId} {T : Tables} {src : Nat} {b : Cfg.Block} {c : Lir.Cond} {a a' : Fir.Arg}
    {st st' : St} (h : (fusedEnd f T src b c a a').run st = .ok ((), st')) (hl : Labels st) (ho : Open st) :
    Grows st st' := by
  unfold fusedEnd at h
  obtain ⟨o, st₁, h₁, h₂⟩ := run_bind h
  have hst : st₁ = st := by
    simp only [StateT.run, MonadLift.monadLift, liftM, monadLift, StateT.lift, bind, Except.bind] at h₁
    split at h₁
    · cases h₁
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h₁; exact h₁.2.symm
  subst hst
  split at h₂
  · split at h₂
    · exact fusedSwitch_grows h₂ hl ho
    · exact term_grows h₂ hl ho
  · rw [close_run] at h₂
    cases h₂
    exact grows_close ho _

/-- **Whatever remains of a block's lowering grows the chunk.** -/
theorem rest_grows {f : Fir.FunId} {T : Tables} {uses : NatMap Nat} {src : Nat} {b : Cfg.Block}
    {is : List Cfg.Instr} {st stF : St} (h : (restAct f T uses src b is).run st = .ok ((), stF)) (hl : Labels st)
    (ho : Open st) : Grows st stF := by
  unfold restAct at h
  split at h
  · obtain ⟨bb, st₁, h₁, h₂⟩ := run_bind h
    obtain ⟨hg, hb, -⟩ := instrs_grows h₁ hl ho
    cases bb with
    | true =>
      obtain ⟨hl₁, ho₁⟩ := hb rfl
      simp only [↓reduceIte] at h₂
      exact hg.trans (fusedEnd_grows h₂ hl₁ ho₁)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h₂
      exact h₂.2 ▸ hg
  · obtain ⟨bb, st₁, h₁, h₂⟩ := run_bind h
    obtain ⟨hg, hb, -⟩ := instrs_grows h₁ hl ho
    cases bb with
    | true =>
      obtain ⟨hl₁, ho₁⟩ := hb rfl
      simp only [↓reduceIte] at h₂
      exact hg.trans (term_grows h₂ hl₁ ho₁)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h₂
      exact h₂.2 ▸ hg

/-! ## Use counts -/

theorem getD_foldl_count : ∀ (l : List Nat) (m : NatMap Nat) (y : Nat),
    (l.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m).getD y 0 = m.getD y 0 + l.count y
  | [], m, y => by simp
  | x :: l, m, y => by
    rw [List.foldl_cons, getD_foldl_count l _ y, List.count_cons]
    simp only [NatMap.getD, NatMap.get?_insert]
    by_cases h : y = x
    · subst h; simp; omega
    · simp [h, Ne.symm h]

theorem useCounts_getD (fd : Cfg.Fun) (y : Nat) :
    (useCounts fd).getD y 0 = (fd.blocks.flatMap blockUses).count y := by
  unfold useCounts
  rw [getD_foldl_count]
  simp [NatMap.getD, NatMap.get?]

theorem le_sum_map {α : Type} (g : α → Nat) : ∀ {l : List α} {j : Nat} {b : α}, l[j]? = some b →
    g b ≤ (l.map g).sum
  | [], _, _, h => by simp at h
  | c :: l, 0, b, h => by simp at h; subst h; simp
  | c :: l, j + 1, b, h => by
    simp only [List.getElem?_cons_succ] at h
    have := le_sum_map g h
    simp; omega

theorem two_le_sum_map {α : Type} (g : α → Nat) : ∀ {l : List α} {i j : Nat} {a b : α}, i ≠ j → l[i]? = some a →
    l[j]? = some b → g a + g b ≤ (l.map g).sum
  | [], _, _, _, _, _, h, _ => by simp at h
  | c :: l, 0, 0, _, _, hij, _, _ => absurd rfl hij
  | c :: l, 0, j + 1, a, b, _, ha, hb => by
    simp at ha; subst ha
    simp only [List.getElem?_cons_succ] at hb
    have := le_sum_map g hb
    simp; omega
  | c :: l, i + 1, 0, a, b, _, ha, hb => by
    simp at hb; subst hb
    simp only [List.getElem?_cons_succ] at ha
    have := le_sum_map g ha
    simp; omega
  | c :: l, i + 1, j + 1, a, b, hij, ha, hb => by
    simp only [List.getElem?_cons_succ] at ha hb
    have := two_le_sum_map g (fun h => hij (by omega)) ha hb
    simp; omega

/-- A variable read in block `j` is counted there. -/
theorem count_flatMap_ge {fd : Cfg.Fun} {y j : Nat} {bj : Cfg.Block} (hj : fd.blocks[j]? = some bj) :
    (blockUses bj).count y ≤ (fd.blocks.flatMap blockUses).count y := by
  rw [List.count_flatMap]
  exact le_sum_map (fun b => (blockUses b).count y) hj

/-! ## Fused comparisons -/

/-- `y` is the comparison a fused block of `fd` branches on. -/
def Fused (T : Tables) (fd : Cfg.Fun) (y : Nat) : Prop :=
  ∃ (i : Nat) (b : Cfg.Block) (init : List Cfg.Instr) (c : Lir.Cond) (a a' : Fir.Arg)
    (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge), fd.blocks[i]? = some b ∧
    fusable T (useCounts fd) b = some (init, c, a, a') ∧
    b.term = .switch y alts d

/-- The occurrences of a variable in a block's reads, besides its own
switch's scrutinee. -/
def otherUses (b : Cfg.Block) : List Nat :=
  b.body.flatMap instrUses ++
    match b.term with
    | .switch _ alts d => (alts.map (·.2) ++ d.toList).flatMap (Cfg.Check.argVars ·.args)
    | t => Cfg.Check.termVars t

theorem count_blockUses (b : Cfg.Block) (y : Nat) :
    (otherUses b).count y + (match b.term with | .switch z _ _ => if z = y then 1 else 0 | _ => 0) =
      (blockUses b).count y := by
  unfold otherUses blockUses
  cases ht : b.term <;> simp [ht, Cfg.Check.termVars, List.count_cons] <;> split <;> simp_all <;> omega

/-- **A fused comparison has no other use.** -/
theorem fused_once {T : Tables} {fd : Cfg.Fun} {y : Nat} (hD : Fused T fd y) {j : Nat} {bj : Cfg.Block}
    (hj : fd.blocks[j]? = some bj) :
    y ∉ otherUses bj ∧ ∀ alts d, bj.term = .switch y alts d → (fusable T (useCounts fd) bj).isSome = true := by
  obtain ⟨i, b, init, c, a, a', alts, d, hi, hf, ht⟩ := hD
  obtain ⟨x, op, alts', d', -, -, ht', hu, -⟩ := fusable_some hf
  rw [ht] at ht'
  cases ht'
  rw [useCounts_getD] at hu
  have hcount := count_blockUses b y
  rw [ht] at hcount
  simp only [↓reduceIte] at hcount
  have hb_ge := count_flatMap_ge (y := y) hi
  constructor
  · intro hy
    have hpos : 0 < (otherUses bj).count y := List.count_pos_iff.2 hy
    have hcount' := count_blockUses bj y
    by_cases hij : i = j
    · subst hij
      rw [hi] at hj; cases hj
      omega
    · have := two_le_sum_map (fun b => (blockUses b).count y) hij hi hj
      rw [show (fd.blocks.map fun b => (blockUses b).count y).sum = (fd.blocks.flatMap blockUses).count y by
        rw [List.count_flatMap]; rfl] at this
      omega
  · intro alts₂ d₂ ht₂
    by_cases hij : i = j
    · subst hij
      rw [hi] at hj; cases hj
      simp [hf]
    · have hcount' := count_blockUses bj y
      rw [ht₂] at hcount'
      simp only [↓reduceIte] at hcount'
      have := two_le_sum_map (fun b => (blockUses b).count y) hij hi hj
      rw [show (fd.blocks.map fun b => (blockUses b).count y).sum = (fd.blocks.flatMap blockUses).count y by
        rw [List.count_flatMap]; rfl] at this
      omega

end IxCC.Rt.Proof
