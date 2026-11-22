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

theorem Mono.divMod' (x : Nat) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) :
    Mono (divMod x o zero a b) := by
  unfold divMod
  repeat (first
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

/-- A fixed-width word primitive's expansion (stage W1). -/
theorem Mono.word' (f : Fir.FunId) (x : Nat) (w : Src.Width) (op : Src.WordOp) (las : List Lir.Arg) :
    Mono (Lower.word f x w op las) := by
  unfold Lower.word word64 wordNarrow wordCount checked64
  repeat (first
    | with_reducible exact Mono.divMod' _ _ _ _ _
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

/-- **An instruction that continues its block keeps it open and grows the
chunk.** -/
theorem instr_mono {f : Fir.FunId} {T : Tables} {i : Cfg.Instr} {st st' : St}
    (h : (instr f T i).run st = .ok (true, st')) (hl : Labels st) (ho : Open st) :
    Grows st st' ∧ Labels st' ∧ Open st' := by
  match i, h with
  | .bind x (.fir (.arg a)), h =>
    refine withOperands_mono (fun las => ?_) h hl ho
    split
    · unfold assign; exact Mono.emit' _
    · exact Mono.pure' _
  | .bind x (.fir (.prim op as)), h => exact withOperands_mono (fun las => primitive_mono f T x op las) h hl ho
  | .bind x (.fir (.call g as)), h => exact withOperands_mono (fun las => Mono.emit' _) h hl ho
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
