import IxCCGrounding.WordCanon

/-!
# The word operations in the model, from their stored equations (`IxCCGrounding.WordAccel`, step W)

A word entry `c ↦ word w op thm` makes `c` a special head of SrcEval (rule F6w); its meaning is the
stored theorem `thm`, `∀ x y : Nat, op (ofNat x) (ofNat y) = ofNat' (F x y)` (`Table.wordEqnType`,
one binder for a unary operation, `toNat`'s right side the `Nat` formula itself; for `ofNat` the
theorem is the bridge). Its kernel statement over keys is `wordStmtK`, which the check compares
with the stored one.

**The model fact** (`wordAccel_of_eqns`): at words below the size (and any `Nat` for `ofNat`), the
operation's set applied to the bridge's towers of its arguments is the bridge's tower of
`WordOp.eval`'s result (or the literal, for `toNat`). Each instance comes from the stored theorem by
`mem` and `eq_of_inhabited` (`thm_inst1`, `thm_inst2`); the formula is evaluated by `nat_accel`
(`form_den`) and is `WordOp.eval`'s number (`spec_val`); the towers are the bridge's (`ofNat_tow`), at
the operation's width and at its result's. No law beyond `nat_accel` and `Model.mem`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels Width WordOp WordResult)

universe w

/-- `@Eq.{1} T a b`. -/
def eqK (T a b : KExpr) : KExpr := Expr.mkAppN (.const eqName [.succ .zero]) [T, a, b]

/-- **A word entry's statement over keys** (every primitive operation but `ofNat`, whose theorem is
the bridge): `kc` the operation's key, `tk` the width's keys, `tk'` the result width's, `f` the
formula (`spec`); binder data as stored. -/
def wordStmtK (kc : KKey) (op : WordOp) (tk tk' : TowKeys) (f : NForm) (m1 m2 : BinderMeta) :
    KExpr :=
  if op.arity = 2 then
    .forallE natK (.forallE natK (eqK (.const tk'.ty [])
      (.app (.app (.const kc []) (.app (.const tk.ofNat []) (.bvar 1)))
        (.app (.const tk.ofNat []) (.bvar 0)))
      (.app (.const tk'.ofNat []) (f.toK (.bvar 1) (.bvar 0)))) m2) m1
  else if op = .toNat then
    .forallE natK (eqK natK (.app (.const kc []) (.app (.const tk.ofNat []) (.bvar 0)))
      (f.toK (.bvar 0) (.bvar 0))) m1
  else
    .forallE natK (eqK (.const tk'.ty []) (.app (.const kc []) (.app (.const tk.ofNat []) (.bvar 0)))
      (.app (.const tk'.ofNat []) (f.toK (.bvar 0) (.bvar 0)))) m1

/-- A key stored without level parameters. -/
def KeyStored (env : KEnv) (k : KKey) : Prop :=
  ∃ ci : ConstantInfo .anon, env.find? k = some ci ∧ ci.toConstantVal.levelParams = []

/-- **What the model fact reads of one entry's statement** (decided by the check): for `ofNat`, the
operation is the bridge's `ofNat` (its result width its own); otherwise the stored theorem has `wordStmtK`'s statement for the
operation's formula, whose `Nat` operations are stored. -/
def WordStmt (env : KEnv) (kc kThm : KKey) (w : Width) (op : WordOp) (tk tk' : TowKeys) : Prop :=
  op = .ofNat ∧ kc = tk.ofNat ∧ tk' = tk ∨
    op ≠ .ofNat ∧ ∃ f, spec w op = some f ∧ (∀ o ∈ f.ops, KeyStored env (primKey o)) ∧
      ∃ (cv : ConstantVal .anon) (pf : KExpr) (m1 m2 : BinderMeta),
        env.find? kThm = some (.thmInfo cv pf) ∧ cv.type = wordStmtK kc op tk tk' f m1 m2

/-! ## `WordOp.eval`'s shapes -/

theorem eval_word_width {w w' : Width} {op : WordOp} {x y n : Nat}
    (h : op.eval w x y = .word w' n) : w' = op.resultWidth w := by
  cases op <;> simp only [WordOp.eval] at h
  case convert w'' => split at h <;> (cases h; rfl)
  all_goals first | (cases h; rfl) | cases h

theorem eval_nat {w : Width} {op : WordOp} {x y n : Nat} (h : op.eval w x y = .nat n) :
    op = .toNat ∧ n = x := by
  cases op <;> simp only [WordOp.eval] at h
  case toNat => cases h; exact ⟨rfl, rfl⟩
  case convert w'' => split at h <;> cases h
  all_goals cases h

theorem eval_unary {w : Width} {op : WordOp} (h : op.arity = 1) (x y y' : Nat) :
    op.eval w x y = op.eval w x y' := by
  cases op <;> simp [WordOp.arity] at h <;> rfl

theorem arity_cases (op : WordOp) : op.arity = 1 ∨ op.arity = 2 := by
  cases op <;> simp [WordOp.arity]

section Accel

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

theorem KeyStored.den {k : KKey} (h : KeyStored env k) (M : Model V env) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) : Denotes M.cval env φ ρ (.const k []) (M.cval k φ) := by
  obtain ⟨ci, hf, hl⟩ := h
  exact (den_const0 hf hl).mpr rfl

/-- A stored theorem `∀ x : Nat, @Eq T a b`, at a literal: its two sides denote one set. -/
theorem thm_inst1 (M : Model V env) (hN : NatBasis env) (hE : EqBasis env) {kThm : KKey}
    {cv : ConstantVal .anon} {pf : KExpr} (hf : env.find? kThm = some (.thmInfo cv pf))
    {u : Level} {T a b : KExpr} {m1 : BinderMeta}
    (ht : cv.type = .forallE natK (Expr.mkAppN (.const eqName [u]) [T, a, b]) m1)
    (φ : LevelParam → Nat) (x : Nat) :
    ∃ v, Denotes M.cval env φ (push (litSet M φ x) (fun _ => empty)) a v ∧
      Denotes M.cval env φ (push (litSet M φ x) (fun _ => empty)) b v := by
  have hF := natFacts M hN φ
  obtain ⟨TT, hTT, hm⟩ := mem_key M hf φ (fun _ => empty)
  simp only [ConstantInfo.toConstantVal] at hTT
  rw [ht] at hTT
  obtain ⟨B, hB, hmB⟩ := app_mem_den_pi hTT ((hF.natD _ _).mpr rfl) hm (lit_mem M hF x)
  exact eq_of_inhabited M hE hB hmB

/-- A stored theorem `∀ x y : Nat, @Eq T a b`, at two literals. -/
theorem thm_inst2 (M : Model V env) (hN : NatBasis env) (hE : EqBasis env) {kThm : KKey}
    {cv : ConstantVal .anon} {pf : KExpr} (hf : env.find? kThm = some (.thmInfo cv pf))
    {u : Level} {T a b : KExpr} {m1 m2 : BinderMeta}
    (ht : cv.type = .forallE natK (.forallE natK (Expr.mkAppN (.const eqName [u]) [T, a, b]) m2) m1)
    (φ : LevelParam → Nat) (x y : Nat) :
    ∃ v, Denotes M.cval env φ (push (litSet M φ y) (push (litSet M φ x) (fun _ => empty))) a v ∧
      Denotes M.cval env φ (push (litSet M φ y) (push (litSet M φ x) (fun _ => empty))) b v := by
  have hF := natFacts M hN φ
  obtain ⟨TT, hTT, hm⟩ := mem_key M hf φ (fun _ => empty)
  simp only [ConstantInfo.toConstantVal] at hTT
  rw [ht] at hTT
  obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hTT ((hF.natD _ _).mpr rfl) hm (lit_mem M hF x)
  obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 ((hF.natD _ _).mpr rfl) hm1 (lit_mem M hF y)
  exact eq_of_inhabited M hE hB2 hm2

/-- The argument sets of a word operation: `ofNat`'s literal, otherwise the bridge's towers. -/
noncomputable def wordArgs (M : Model V env) (tk : TowKeys) (w : Width) (op : WordOp)
    (φ : LevelParam → Nat) (x y : Nat) : List V :=
  if op = .ofNat then [litSet M φ x]
  else if op.arity = 2 then [towV M tk w.bits w.size φ x, towV M tk w.bits w.size φ y]
  else [towV M tk w.bits w.size φ x]

/-- **The model fact**: at words below the size (any `Nat` for `ofNat`), a primitive operation's set
applied to its argument sets is the bridge's tower of `WordOp.eval`'s word, or the literal of its
`Nat`. -/
theorem wordAccel_of_eqns (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hE : EqBasis env) {kc kThm : KKey} {w : Width} {op : WordOp} {tk tk' : TowKeys}
    (hW : ∃ kB kR kS, BridgeStored env tk w.bits w.size kB kR kS)
    (hW' : ∃ kB kR kS, BridgeStored env tk' (op.resultWidth w).bits (op.resultWidth w).size kB kR kS)
    (hkc : KeyStored env kc) (hst : WordStmt env kc kThm w op tk tk') (φ : LevelParam → Nat)
    {x y : Nat} (hx : op = .ofNat ∨ x < w.size) (hy : y < w.size) :
    (∀ w' n, op.eval w x y = .word w' n →
      (wordArgs M tk w op φ x y).foldl app (M.cval kc φ) = towV M tk' w'.bits w'.size φ n) ∧
    (∀ n, op.eval w x y = .nat n → (wordArgs M tk w op φ x y).foldl app (M.cval kc φ) = litSet M φ n) := by
  have hF := natFacts M hN φ
  obtain ⟨kB, kR, kS, hB⟩ := hW
  obtain ⟨kB', kR', kS', hB'⟩ := hW'
  have hofN : ∀ a, a < w.size →
      app (M.cval tk.ofNat φ) (litSet M φ a) = towV M tk w.bits w.size φ a := fun a ha => by
    rw [ofNat_tow M hacc hN hE hB φ a, Nat.mod_eq_of_lt ha]
  have hkcD := hkc.den M φ
  have hofD : ∀ ρ, Denotes M.cval env φ ρ (.const tk.ofNat []) (M.cval tk.ofNat φ) :=
    hB.den M (by simp) φ
  have hofD' : ∀ ρ, Denotes M.cval env φ ρ (.const tk'.ofNat []) (M.cval tk'.ofNat φ) :=
    hB'.den M (by simp) φ
  rcases hst with ⟨rfl, rfl, rfl⟩ | ⟨hne, f, hf, hops, cv, pf, m1, m2, hfT, htT⟩
  · -- `ofNat`: the bridge
    refine ⟨fun w' n h => ?_, fun n h => absurd (eval_nat h).1 (by decide)⟩
    simp only [WordOp.eval] at h
    cases h
    simp [wordArgs]
    exact ofNat_tow M hacc hN hE hB φ x
  have hx' : x < w.size := hx.resolve_left hne
  have hok := spec_ok w op hf
  have hxt := hofN x hx'
  rcases arity_cases op with h1 | h2
  · -- unary
    have h2 : ¬ op.arity = 2 := by rw [h1]; decide
    have hargs : wordArgs M tk w op φ x y = [towV M tk w.bits w.size φ x] := by
      simp only [wordArgs, ite_eq_right hne, ite_eq_right h2]
    rw [hargs]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← hxt]
    have hval := spec_val w op hf (.inr hx') hx'
    rw [eval_unary h1 x x y] at hval
    let ρ1 : BVarIdx → V := push (litSet M φ x) (fun _ => empty)
    have hfd := form_den M hacc hN (ρ := ρ1) (ex := .bvar 0) (ey := .bvar 0) (vx := x) (vy := x)
      .bvar .bvar f hok hops
    have hlhs : Denotes M.cval env φ ρ1 (.app (.const kc []) (.app (.const tk.ofNat []) (.bvar 0)))
        (app (M.cval kc φ) (app (M.cval tk.ofNat φ) (litSet M φ x))) :=
      .app (hkcD ρ1) (.app (hofD ρ1) .bvar)
    by_cases ht : op = .toNat
    · subst ht
      rw [wordStmtK, ite_eq_right h2, ite_eq_left rfl] at htT
      obtain ⟨v, hv1, hv2⟩ := thm_inst1 M hN hE hfT htT φ x
      have he : app (M.cval kc φ) (app (M.cval tk.ofNat φ) (litSet M φ x)) =
          litSet M φ (f.val x x) :=
        (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 hfd)
      refine ⟨fun w' n h => by simp [WordOp.eval] at h, fun n h => ?_⟩
      rw [he, hval, h]
      rfl
    · rw [wordStmtK, ite_eq_right h2, ite_eq_right ht] at htT
      obtain ⟨v, hv1, hv2⟩ := thm_inst1 M hN hE hfT htT φ x
      have he : app (M.cval kc φ) (app (M.cval tk.ofNat φ) (litSet M φ x)) =
          app (M.cval tk'.ofNat φ) (litSet M φ (f.val x x)) :=
        (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 (.app (hofD' ρ1) hfd))
      refine ⟨fun w' n h => ?_, fun n h => absurd (eval_nat h).1 ht⟩
      have hw' := eval_word_width h
      subst hw'
      have hn := WordOp.eval_word_lt w op x y (.inr hx') hy _ _ h
      rw [he, hval, h]
      simp only [WordResult.val]
      rw [ofNat_tow M hacc hN hE hB' φ n, Nat.mod_eq_of_lt hn]
  · -- binary
    have hyt := hofN y hy
    have hargs : wordArgs M tk w op φ x y =
        [towV M tk w.bits w.size φ x, towV M tk w.bits w.size φ y] := by
      simp only [wordArgs, ite_eq_right hne, ite_eq_left h2]
    rw [hargs]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← hxt, ← hyt]
    rw [wordStmtK, ite_eq_left h2] at htT
    obtain ⟨v, hv1, hv2⟩ := thm_inst2 M hN hE hfT htT φ x y
    let ρ2 : BVarIdx → V := push (litSet M φ y) (push (litSet M φ x) (fun _ => empty))
    have hfd := form_den M hacc hN (ρ := ρ2) (ex := .bvar 1) (ey := .bvar 0) (vx := x) (vy := y)
      .bvar .bvar f hok hops
    have hlhs : Denotes M.cval env φ ρ2
        (.app (.app (.const kc []) (.app (.const tk.ofNat []) (.bvar 1)))
          (.app (.const tk.ofNat []) (.bvar 0)))
        (app (app (M.cval kc φ) (app (M.cval tk.ofNat φ) (litSet M φ x)))
          (app (M.cval tk.ofNat φ) (litSet M φ y))) :=
      .app (.app (hkcD ρ2) (.app (hofD ρ2) .bvar)) (.app (hofD ρ2) .bvar)
    have he := (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 (.app (hofD' ρ2) hfd))
    have hval := spec_val w op hf (.inr hx') hy
    refine ⟨fun w' n h => ?_, fun n h => by
      have := (eval_nat h).1; subst this; simp [WordOp.arity] at h2⟩
    have hw' := eval_word_width h
    subst hw'
    have hn := WordOp.eval_word_lt w op x y (.inr hx') hy _ _ h
    rw [he, hval, h]
    simp only [WordResult.val]
    rw [ofNat_tow M hacc hN hE hB' φ n, Nat.mod_eq_of_lt hn]

end Accel

end IxCC.Grounding
