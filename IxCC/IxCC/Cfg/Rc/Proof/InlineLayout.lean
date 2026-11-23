import IxCC.Cfg.Rc.Inline
import IxCC.Lir.Proof.Steps

/-! # Layout, register-bound, and chunk-cursor lemmas for `Cfg.Rc.Inline`

Establishes:
1. Every register mentioned in a Lir function `F` lies strictly below `freshBase F`,
   so `AgreeBelow (freshBase F)` preserves evaluation of every statement, terminator,
   and edge of `F`.
2. `newLabel l F` is strictly monotone and preserves back-edge polarity across
   each expanded block's chunk (`newLabel_end_le_iff`).
3. `ChunkPos` tracks the correspondence between a raw frame position `(b, rawPos)`
   and its expanded position `(inLbl, inPos)` across arbitrary statements and
   inlined RC sites. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Inline

open IxCC.Cfg.Rc.Native

/-! ## Maximum register bounds (`freshBase`) -/

theorem le_maxList (xs : List Nat) (acc : Nat) : acc ≤ maxList xs acc := by
  induction xs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    unfold maxList at ih ⊢
    exact Nat.le_trans (Nat.le_max_left acc x) (ih (max acc x))

theorem mem_le_maxList {xs : List Nat} {acc x : Nat} (hx : x ∈ xs) : x ≤ maxList xs acc := by
  induction xs generalizing acc with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right acc x) (le_maxList ys (max acc x))
    · exact ih hx

theorem le_argMax (a : Lir.Arg) (acc : Nat) : acc ≤ argMax a acc := by
  cases a with
  | v x => exact Nat.le_max_left acc x
  | imm _ => exact Nat.le_refl _

theorem vreg_le_argMax {x acc : Nat} : x ≤ argMax (.v x) acc :=
  Nat.le_max_right acc x

theorem le_argsMax (as : List Lir.Arg) (acc : Nat) : acc ≤ argsMax as acc := by
  induction as generalizing acc with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
    unfold argsMax at ih ⊢
    exact Nat.le_trans (le_argMax a acc) (ih (argMax a acc))

theorem mem_le_argsMax {as : List Lir.Arg} {acc x : Nat} (hx : .v x ∈ as) : x ≤ argsMax as acc := by
  induction as generalizing acc with
  | nil => cases hx
  | cons a as ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans vreg_le_argMax (le_argsMax as (argMax (.v x) acc))
    · exact ih hx

theorem le_addrMax (m : Lir.Addr) (acc : Nat) : acc ≤ addrMax m acc := by
  unfold addrMax
  have h1 : acc ≤ match m.base with | some (.v x) => max acc x | _ => acc := by
    cases m.base with
    | none => exact Nat.le_refl _
    | some b => cases b with
      | v x => exact Nat.le_max_left _ _
      | ctx => exact Nat.le_refl _
  cases m.index with
  | none => exact h1
  | some p => exact Nat.le_trans h1 (Nat.le_max_left _ _)

theorem base_le_addrMax {m : Lir.Addr} {acc x : Nat} (hb : m.base = some (.v x)) : x ≤ addrMax m acc := by
  unfold addrMax
  rw [hb]
  cases m.index with
  | none => exact Nat.le_max_right _ _
  | some p => exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

theorem index_le_addrMax {m : Lir.Addr} {acc x : Nat} {sc : X86.Scale} (hi : m.index = some (x, sc)) :
    x ≤ addrMax m acc := by
  unfold addrMax
  rw [hi]
  exact Nat.le_max_right _ _

theorem le_limbOpMax (op : Lir.LimbOp) (acc : Nat) : acc ≤ limbOpMax op acc := by
  cases op with
  | mulWide64 a b => exact Nat.le_trans (le_argMax a acc) (le_argMax b _)
  | divWide64 hi lo d =>
    exact Nat.le_trans (le_argMax hi acc) (Nat.le_trans (le_argMax lo _) (le_argMax d _))
  | addCarry64 a b c =>
    exact Nat.le_trans (le_argMax a acc) (Nat.le_trans (le_argMax b _) (le_argMax c _))
  | subBorrow64 a b c =>
    exact Nat.le_trans (le_argMax a acc) (Nat.le_trans (le_argMax b _) (le_argMax c _))

theorem le_rhsMax (r : Lir.Rhs) (acc : Nat) : acc ≤ rhsMax r acc := by
  cases r with
  | arg a => exact le_argMax a acc
  | bin _ _ a b => exact Nat.le_trans (le_argMax a acc) (le_argMax b _)
  | load _ _ m => exact le_addrMax m acc
  | addr m => exact le_addrMax m acc
  | select _ _ a b t f =>
    exact Nat.le_trans (le_argMax a acc)
      (Nat.le_trans (le_argMax b _) (Nat.le_trans (le_argMax t _) (le_argMax f _)))
  | test _ _ a b => exact Nat.le_trans (le_argMax a acc) (le_argMax b _)
  | bsr64 a => exact le_argMax a acc

theorem le_stmtMax (s : Lir.Stmt) (acc : Nat) : acc ≤ stmtMax s acc := by
  cases s with
  | assign x r => exact Nat.le_trans (Nat.le_max_left acc x) (le_rhsMax r _)
  | limb r1 r2 op =>
    exact Nat.le_trans (Nat.le_max_left acc r1)
      (Nat.le_trans (Nat.le_max_left _ r2) (le_limbOpMax op _))
  | store _ m a => exact Nat.le_trans (le_addrMax m acc) (le_argMax a _)
  | call rs _ as => exact Nat.le_trans (le_maxList rs acc) (le_argsMax as _)

theorem le_edgeMax (e : Lir.Edge) (acc : Nat) : acc ≤ edgeMax e acc := le_argsMax e.args acc

theorem le_termMax (t : Lir.Term) (acc : Nat) : acc ≤ termMax t acc := by
  cases t with
  | jump e => exact le_edgeMax e acc
  | br _ _ a b t f =>
    exact Nat.le_trans (le_argMax a acc)
      (Nat.le_trans (le_argMax b _) (Nat.le_trans (le_edgeMax t _) (le_edgeMax f _)))
  | brOvf _ x a b ok ovf =>
    exact Nat.le_trans (Nat.le_max_left acc x)
      (Nat.le_trans (le_argMax a _)
        (Nat.le_trans (le_argMax b _) (Nat.le_trans (le_edgeMax ok _) (le_edgeMax ovf _))))
  | ret as => exact le_argsMax as acc
  | tail _ as => exact le_argsMax as acc
  | fail _ | trap => exact Nat.le_refl _

theorem le_foldl_stmtMax (ss : List Lir.Stmt) (acc : Nat) :
    acc ≤ ss.foldl (fun m s => stmtMax s m) acc := by
  induction ss generalizing acc with
  | nil => exact Nat.le_refl _
  | cons s ss ih => exact Nat.le_trans (le_stmtMax s acc) (ih (stmtMax s acc))

private theorem argMax_mono (x : Lir.Arg) {a b : Nat} (h : a ≤ b) : argMax x a ≤ argMax x b := by
  cases x <;> simp [argMax] <;> omega

private theorem argsMax_mono (xs : List Lir.Arg) {a b : Nat} (h : a ≤ b) :
    argsMax xs a ≤ argsMax xs b := by
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih => exact ih (argMax_mono x h)

private theorem maxList_mono (xs : List Nat) {a b : Nat} (h : a ≤ b) :
    maxList xs a ≤ maxList xs b := by
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih => exact ih (by omega)

private theorem addrMax_mono (m : Lir.Addr) {a b : Nat} (h : a ≤ b) :
    addrMax m a ≤ addrMax m b := by
  unfold addrMax
  have h1 : (match m.base with | some (.v x) => max a x | _ => a) ≤
      (match m.base with | some (.v x) => max b x | _ => b) := by
    cases m.base with
    | none => exact h
    | some base => cases base with | v x => dsimp only; omega | ctx => exact h
  cases m.index with
  | none => exact h1
  | some p => exact Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

private theorem stmtMax_mono (st : Lir.Stmt) {a b : Nat} (h : a ≤ b) :
    stmtMax st a ≤ stmtMax st b := by
  cases st with
  | assign x r =>
    have h1 : max a x ≤ max b x := by omega
    cases r with
    | arg y => exact argMax_mono y h1
    | bin _ _ y z => exact argMax_mono z (argMax_mono y h1)
    | load _ _ m => exact addrMax_mono m h1
    | addr m => exact addrMax_mono m h1
    | select _ _ a1 a2 a3 a4 =>
      exact argMax_mono a4 (argMax_mono a3 (argMax_mono a2 (argMax_mono a1 h1)))
    | test _ _ y z => exact argMax_mono z (argMax_mono y h1)
    | bsr64 y => exact argMax_mono y h1
  | limb r1 r2 op =>
    have h1 : max (max a r1) r2 ≤ max (max b r1) r2 := by omega
    cases op with
    | mulWide64 y z => exact argMax_mono z (argMax_mono y h1)
    | divWide64 y z w => exact argMax_mono w (argMax_mono z (argMax_mono y h1))
    | addCarry64 y z w => exact argMax_mono w (argMax_mono z (argMax_mono y h1))
    | subBorrow64 y z w => exact argMax_mono w (argMax_mono z (argMax_mono y h1))
  | store _ m y => exact argMax_mono y (addrMax_mono m h)
  | call rs _ as => exact argsMax_mono as (maxList_mono rs h)

private theorem termMax_mono (t : Lir.Term) {a b : Nat} (h : a ≤ b) :
    termMax t a ≤ termMax t b := by
  cases t with
  | jump e => exact argsMax_mono e.args h
  | br _ _ x y e1 e2 =>
    exact argsMax_mono e2.args (argsMax_mono e1.args (argMax_mono y (argMax_mono x h)))
  | brOvf _ r x y e1 e2 =>
    exact argsMax_mono e2.args (argsMax_mono e1.args (argMax_mono y (argMax_mono x (by omega))))
  | ret as => exact argsMax_mono as h
  | tail _ as => exact argsMax_mono as h
  | fail _ | trap => exact h

theorem mem_stmtMax_le_foldl {ss : List Lir.Stmt} {s : Lir.Stmt} {acc : Nat} (hs : s ∈ ss) :
    stmtMax s 0 ≤ ss.foldl (fun m s => stmtMax s m) acc := by
  induction ss generalizing acc with
  | nil => cases hs
  | cons s' ss ih =>
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Nat.le_trans (stmtMax_mono s (Nat.zero_le _)) (le_foldl_stmtMax ss (stmtMax s acc))
    · exact ih hs

theorem le_blockMax (b : Lir.Block) (acc : Nat) : acc ≤ blockMax b acc := by
  unfold blockMax
  exact Nat.le_trans (le_maxList b.params acc)
    (Nat.le_trans (le_foldl_stmtMax b.body.toList _) (le_termMax b.term _))

theorem le_foldl_blockMax (bs : List Lir.Block) (acc : Nat) :
    acc ≤ bs.foldl (fun m b => blockMax b m) acc := by
  induction bs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons b bs ih => exact Nat.le_trans (le_blockMax b acc) (ih (blockMax b acc))

theorem blockMax_mono (B : Lir.Block) {a b : Nat} (h : a ≤ b) : blockMax B a ≤ blockMax B b := by
  have monoStmts : ∀ (ss : List Lir.Stmt) (x y : Nat), x ≤ y →
      ss.foldl (fun m s => stmtMax s m) x ≤ ss.foldl (fun m s => stmtMax s m) y := by
    intro ss; induction ss with
    | nil => intro x y hxy; exact hxy
    | cons s ss ih => intro x y hxy; exact ih _ _ (stmtMax_mono s hxy)
  unfold blockMax
  exact termMax_mono B.term (monoStmts B.body.toList _ _ (maxList_mono B.params h))

private theorem mem_blockMax_le_foldl {bs : List Lir.Block} {B : Lir.Block} {init : Nat}
    (hmem : B ∈ bs) : blockMax B 0 ≤ bs.foldl (fun m b => blockMax b m) init := by
  induction bs generalizing init with
  | nil => cases hmem
  | cons b' bs ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Nat.le_trans (blockMax_mono B (Nat.zero_le init)) (le_foldl_blockMax bs _)
    · exact ih hmem

theorem block_le_maxVReg {F : Lir.Func} {b : Lir.Label} {B : Lir.Block} (hb : F.blocks[b]? = some B) :
    blockMax B 0 ≤ maxVReg F :=
  mem_blockMax_le_foldl (List.mem_of_getElem? (by simpa using hb))

theorem stmt_le_maxVReg {F : Lir.Func} {b : Lir.Label} {B : Lir.Block} {s : Lir.Stmt}
    (hb : F.blocks[b]? = some B) (hs : s ∈ B.body.toList) : stmtMax s 0 ≤ maxVReg F := by
  have hbm := block_le_maxVReg hb
  have h1 : stmtMax s 0 ≤ B.body.toList.foldl (fun m s => stmtMax s m) (maxList B.params 0) :=
    mem_stmtMax_le_foldl hs
  have h2 : B.body.toList.foldl (fun m s => stmtMax s m) (maxList B.params 0) ≤ blockMax B 0 :=
    le_termMax B.term _
  omega

theorem term_le_maxVReg {F : Lir.Func} {b : Lir.Label} {B : Lir.Block} (hb : F.blocks[b]? = some B) :
    termMax B.term 0 ≤ maxVReg F := by
  have hbm := block_le_maxVReg hb
  have h1 : termMax B.term 0 ≤ blockMax B 0 := by
    unfold blockMax
    exact termMax_mono B.term (Nat.zero_le _)
  omega

theorem call_args_lt_freshBase {F : Lir.Func} {b : Lir.Label} {B : Lir.Block}
    {rs : List Lir.VReg} {g : Lir.FunId} {as : List Lir.Arg}
    (hb : F.blocks[b]? = some B) (hs : Lir.Stmt.call rs g as ∈ B.body.toList) :
    argsMax as 0 < freshBase F := by
  have h := stmt_le_maxVReg hb hs
  have h1 := argsMax_mono as (Nat.zero_le (maxList rs 0))
  simp only [stmtMax] at h
  unfold freshBase
  omega

/-! ## Environment agreement below a register bound -/

/-- Two Lir environments agree on every register strictly below `bound`. -/
def AgreeBelow (bound : Nat) (e₁ e₂ : Lir.Env) : Prop :=
  ∀ r < bound, e₁[r]? = e₂[r]?

namespace AgreeBelow

theorem refl {bound : Nat} {e : Lir.Env} : AgreeBelow bound e e := fun _ _ => rfl

theorem insert_same {bound : Nat} {e₁ e₂ : Lir.Env} (h : AgreeBelow bound e₁ e₂) (x : Lir.VReg)
    (w : Lir.Word) : AgreeBelow bound (e₁.insert x w) (e₂.insert x w) := by
  intro r hr
  rw [Lir.env_insert_get, Lir.env_insert_get]
  split
  · rfl
  · exact h r hr

theorem insert_ge {bound : Nat} {e₁ e₂ : Lir.Env} (h : AgreeBelow bound e₁ e₂) {t : Lir.VReg}
    (ht : bound ≤ t) (w : Lir.Word) : AgreeBelow bound e₁ (e₂.insert t w) := by
  intro r hr
  rw [Lir.env_insert_ne _ _ (by omega)]
  exact h r hr

theorem bindParams_agree {bound : Nat} : ∀ (ps : List Lir.VReg) (vs : List Lir.Word) {e₁ e₂ : Lir.Env},
    AgreeBelow bound e₁ e₂ →
    (∀ ρ₁, Lir.bindParams e₁ ps vs = some ρ₁ →
      ∃ ρ₂, Lir.bindParams e₂ ps vs = some ρ₂ ∧ AgreeBelow bound ρ₁ ρ₂) ∧
    (∀ ρ₂, Lir.bindParams e₂ ps vs = some ρ₂ →
      ∃ ρ₁, Lir.bindParams e₁ ps vs = some ρ₁ ∧ AgreeBelow bound ρ₁ ρ₂) ∧
    (Lir.bindParams e₁ ps vs = none ↔ Lir.bindParams e₂ ps vs = none)
  | [], [], _, _, h => ⟨fun _ h1 => by cases h1; exact ⟨_, rfl, h⟩,
      fun _ h2 => by cases h2; exact ⟨_, rfl, h⟩, by simp [Lir.bindParams]⟩
  | _ :: _, [], _, _, _ => ⟨fun _ h1 => by simp [Lir.bindParams] at h1,
      fun _ h2 => by simp [Lir.bindParams] at h2, by simp [Lir.bindParams]⟩
  | [], _ :: _, _, _, _ => ⟨fun _ h1 => by simp [Lir.bindParams] at h1,
      fun _ h2 => by simp [Lir.bindParams] at h2, by simp [Lir.bindParams]⟩
  | x :: ps, v :: vs, _, _, h => bindParams_agree ps vs (h.insert_same x v)

theorem arg_eval {bound : Nat} {e₁ e₂ : Lir.Env} (h : AgreeBelow bound e₁ e₂) {a : Lir.Arg}
    (ha : argMax a 0 < bound) : a.eval e₁ = a.eval e₂ := by
  cases a with
  | imm _ => rfl
  | v x => exact h x (Nat.lt_of_le_of_lt vreg_le_argMax ha)

theorem evalArgs_eq {bound : Nat} {e₁ e₂ : Lir.Env} (h : AgreeBelow bound e₁ e₂) :
    ∀ {as : List Lir.Arg}, argsMax as 0 < bound → Lir.evalArgs e₁ as = Lir.evalArgs e₂ as
  | [], _ => rfl
  | a :: as, hb => by
    have ha : argMax a 0 < bound := by
      have := le_argsMax as (argMax a 0)
      change argsMax as (argMax a 0) < bound at hb
      omega
    have has : argsMax as 0 < bound := by
      have := argsMax_mono as (Nat.zero_le (argMax a 0))
      change argsMax as (argMax a 0) < bound at hb
      omega
    have ih : List.mapM (Lir.Arg.eval e₁) as = List.mapM (Lir.Arg.eval e₂) as := evalArgs_eq h has
    simp only [Lir.evalArgs, List.mapM_cons, arg_eval h ha, ih]

theorem addr_eval {bound : Nat} {e₁ e₂ : Lir.Env} (h : AgreeBelow bound e₁ e₂) {m : Lir.Addr}
    (hm : addrMax m 0 < bound) (ctx : Lir.Word) : m.eval e₁ ctx = m.eval e₂ ctx := by
  unfold Lir.Addr.eval
  cases hb : m.base with
  | none =>
    cases hi : m.index with
    | none => rfl
    | some p =>
      rcases p with ⟨x, s⟩
      simp only [h x (Nat.lt_of_le_of_lt (index_le_addrMax hi) hm)]
  | some b =>
    cases b with
    | ctx =>
      cases hi : m.index with
      | none => rfl
      | some p =>
        rcases p with ⟨x, s⟩
        simp only [h x (Nat.lt_of_le_of_lt (index_le_addrMax hi) hm)]
    | v x =>
      have hx := h x (Nat.lt_of_le_of_lt (base_le_addrMax hb) hm)
      cases hi : m.index with
      | none => simp only [hx]
      | some p =>
        rcases p with ⟨y, s⟩
        simp only [hx, h y (Nat.lt_of_le_of_lt (index_le_addrMax hi) hm)]

theorem arg_lt_of_chain {a : Lir.Arg} {acc bound : Nat} (h : argMax a acc < bound) :
    argMax a 0 < bound ∧ acc < bound := by
  cases a with
  | imm _ => simp [argMax] at h ⊢; omega
  | v x => simp [argMax] at h ⊢; omega

theorem edge_lt_of_chain {e : Lir.Edge} {acc bound : Nat} (h : edgeMax e acc < bound) :
    argsMax e.args 0 < bound ∧ acc < bound := by
  have h1 := argsMax_mono e.args (Nat.zero_le acc)
  have h2 := le_argsMax e.args acc
  unfold edgeMax at h
  exact ⟨by omega, by omega⟩

theorem rhs_eval {bound : Nat} {e₁ e₂ : Lir.Env} (h : AgreeBelow bound e₁ e₂) {r : Lir.Rhs}
    (hr : rhsMax r 0 < bound) (mem : X86.Memory) (ctx : Lir.Word) :
    r.eval e₁ mem ctx = r.eval e₂ mem ctx := by
  cases r with
  | arg a => exact arg_eval h hr
  | bin o w a b =>
    obtain ⟨hb, ha⟩ := arg_lt_of_chain hr
    simp only [Lir.Rhs.eval, arg_eval h ha, arg_eval h hb]
  | load w ext m => simp only [Lir.Rhs.eval, addr_eval h hr ctx]
  | addr m => exact addr_eval h hr ctx
  | select c w a b t f =>
    obtain ⟨hf, h1⟩ := arg_lt_of_chain hr
    obtain ⟨ht, h2⟩ := arg_lt_of_chain h1
    obtain ⟨hb, ha⟩ := arg_lt_of_chain h2
    simp only [Lir.Rhs.eval, arg_eval h ha, arg_eval h hb, arg_eval h ht, arg_eval h hf]
  | test c w a b =>
    obtain ⟨hb, ha⟩ := arg_lt_of_chain hr
    simp only [Lir.Rhs.eval, arg_eval h ha, arg_eval h hb]
  | bsr64 a => simp only [Lir.Rhs.eval, arg_eval h hr]

theorem limbOp_eval {bound : Nat} {e₁ e₂ : Lir.Env} (h : AgreeBelow bound e₁ e₂) {op : Lir.LimbOp}
    (hop : limbOpMax op 0 < bound) : op.eval e₁ = op.eval e₂ := by
  cases op with
  | mulWide64 a b =>
    obtain ⟨hb, ha⟩ := arg_lt_of_chain hop
    simp only [Lir.LimbOp.eval, arg_eval h ha, arg_eval h hb]
  | divWide64 hi lo d =>
    obtain ⟨hd, h1⟩ := arg_lt_of_chain hop
    obtain ⟨hlo, hhi⟩ := arg_lt_of_chain h1
    simp only [Lir.LimbOp.eval, arg_eval h hhi, arg_eval h hlo, arg_eval h hd]
  | addCarry64 a b c =>
    obtain ⟨hc, h1⟩ := arg_lt_of_chain hop
    obtain ⟨hb, ha⟩ := arg_lt_of_chain h1
    simp only [Lir.LimbOp.eval, arg_eval h ha, arg_eval h hb, arg_eval h hc]
  | subBorrow64 a b c =>
    obtain ⟨hc, h1⟩ := arg_lt_of_chain hop
    obtain ⟨hb, ha⟩ := arg_lt_of_chain h1
    simp only [Lir.LimbOp.eval, arg_eval h ha, arg_eval h hb, arg_eval h hc]

private theorem rhsMax_zero_le (r : Lir.Rhs) (acc : Nat) : rhsMax r 0 ≤ rhsMax r acc := by
  cases r with
  | arg a => exact argMax_mono a (Nat.zero_le _)
  | bin _ _ a b => exact argMax_mono b (argMax_mono a (Nat.zero_le _))
  | load _ _ m => exact addrMax_mono m (Nat.zero_le _)
  | addr m => exact addrMax_mono m (Nat.zero_le _)
  | select _ _ a b t f =>
    exact argMax_mono f (argMax_mono t (argMax_mono b (argMax_mono a (Nat.zero_le _))))
  | test _ _ a b => exact argMax_mono b (argMax_mono a (Nat.zero_le _))
  | bsr64 a => exact argMax_mono a (Nat.zero_le _)

private theorem limbOpMax_zero_le (op : Lir.LimbOp) (acc : Nat) :
    limbOpMax op 0 ≤ limbOpMax op acc := by
  cases op with
  | mulWide64 a b => exact argMax_mono b (argMax_mono a (Nat.zero_le _))
  | divWide64 hi lo d => exact argMax_mono d (argMax_mono lo (argMax_mono hi (Nat.zero_le _)))
  | addCarry64 a b c => exact argMax_mono c (argMax_mono b (argMax_mono a (Nat.zero_le _)))
  | subBorrow64 a b c => exact argMax_mono c (argMax_mono b (argMax_mono a (Nat.zero_le _)))

theorem stmt_exec {bound : Nat} {e₁ e₂ : Lir.Env} (h : AgreeBelow bound e₁ e₂) {s : Lir.Stmt}
    (hs : stmtMax s 0 < bound) (mem : X86.Memory) (ctx : Lir.Word) :
    (∀ ρ₁ mem', s.exec e₁ mem ctx = some (ρ₁, mem') →
      ∃ ρ₂, s.exec e₂ mem ctx = some (ρ₂, mem') ∧ AgreeBelow bound ρ₁ ρ₂) ∧
    (∀ ρ₂ mem', s.exec e₂ mem ctx = some (ρ₂, mem') →
      ∃ ρ₁, s.exec e₁ mem ctx = some (ρ₁, mem') ∧ AgreeBelow bound ρ₁ ρ₂) ∧
    (s.exec e₁ mem ctx = none ↔ s.exec e₂ mem ctx = none) := by
  cases s with
  | assign x r =>
    have hr : rhsMax r 0 < bound := Nat.lt_of_le_of_lt (rhsMax_zero_le r _) hs
    have heq := rhs_eval h hr mem ctx
    simp only [Lir.Stmt.exec, heq]
    cases r.eval e₂ mem ctx with
    | none => simp
    | some v => exact ⟨fun _ _ h1 => by cases h1; exact ⟨_, rfl, h.insert_same x v⟩,
        fun _ _ h2 => by cases h2; exact ⟨_, rfl, h.insert_same x v⟩, by simp⟩
  | limb r1 r2 op =>
    have hop : limbOpMax op 0 < bound := Nat.lt_of_le_of_lt (limbOpMax_zero_le op _) hs
    have heq := limbOp_eval h hop
    simp only [Lir.Stmt.exec, heq]
    cases op.eval e₂ with
    | none => simp
    | some p =>
      rcases p with ⟨v1, v2⟩
      exact ⟨fun _ _ h1 => by cases h1; exact ⟨_, rfl, (h.insert_same r1 v1).insert_same r2 v2⟩,
        fun _ _ h2 => by cases h2; exact ⟨_, rfl, (h.insert_same r1 v1).insert_same r2 v2⟩, by simp⟩
  | store w m a =>
    obtain ⟨ha, hm⟩ := arg_lt_of_chain hs
    simp only [Lir.Stmt.exec, addr_eval h hm ctx, arg_eval h ha]
    cases m.eval e₂ ctx with
    | none => simp
    | some addr =>
      cases a.eval e₂ with
      | none => simp
      | some v =>
        cases hw : mem.write? w addr v with
        | error _ => simp [hw]
        | ok mem' =>
          exact ⟨fun _ _ h1 => by simp [hw] at h1; rcases h1 with ⟨rfl, rfl⟩; exact ⟨_, by simp [hw], h⟩,
            fun _ _ h2 => by simp [hw] at h2; rcases h2 with ⟨rfl, rfl⟩; exact ⟨_, by simp [hw], h⟩, by simp [hw]⟩
  | call rs f as =>
    simp [Lir.Stmt.exec]

end AgreeBelow

/-! ## `stmtsExtra`, `expandStmts`, `expandBlocks`, and `newLabel` -/

def stmtsExtra (l : Layout) (ss : List Lir.Stmt) : Nat :=
  ss.foldl (fun acc s => acc + stmtExtra l s) 0

theorem stmtsExtra_foldl (l : Layout) (ss : List Lir.Stmt) (acc : Nat) :
    ss.foldl (fun a s => a + stmtExtra l s) acc = acc + stmtsExtra l ss := by
  induction ss generalizing acc with
  | nil => simp [stmtsExtra]
  | cons s ss ih =>
    simp only [List.foldl_cons, stmtsExtra]
    rw [ih (acc + stmtExtra l s), ih (0 + stmtExtra l s)]
    omega

theorem stmtsExtra_nil (l : Layout) : stmtsExtra l [] = 0 := rfl

theorem stmtsExtra_cons (l : Layout) (s : Lir.Stmt) (ss : List Lir.Stmt) :
    stmtsExtra l (s :: ss) = stmtExtra l s + stmtsExtra l ss := by
  simp only [stmtsExtra, List.foldl_cons, Nat.zero_add]
  exact stmtsExtra_foldl l ss (stmtExtra l s)

theorem blockExtra_eq (l : Layout) (b : Lir.Block) : blockExtra l b = stmtsExtra l b.body.toList := rfl

theorem expandStmts_length (l : Layout) (rel : Lir.Label → Lir.Label) (term : Lir.Term) (cold : Bool) :
    ∀ (ss : List Lir.Stmt) (cur nextTmp : Nat) (params : List Lir.VReg) (acc : List Lir.Stmt),
      (expandStmts l rel term cold ss cur nextTmp params acc).1.length = 1 + stmtsExtra l ss ∧
      nextTmp ≤ (expandStmts l rel term cold ss cur nextTmp params acc).2
  | [], _, _, _, _ => ⟨rfl, Nat.le_refl _⟩
  | s :: rest, cur, nextTmp, params, acc => by
    unfold expandStmts
    cases hc : classify l s with
    | none =>
      have ih := expandStmts_length l rel term cold rest cur nextTmp params (s :: acc)
      simpa [stmtsExtra_cons, stmtExtra, hc] using ih
    | some site =>
      cases site with
      | inc dst x =>
        have ih := expandStmts_length l rel term cold rest (cur + 5) (nextTmp + 2) [] [.assign dst (.arg (.imm 1))]
        dsimp only
        refine ⟨?_, by omega⟩
        simp only [List.length_cons, ih.1, stmtsExtra_cons, stmtExtra, hc, siteExtra]
        omega
      | dec dst x =>
        have ih := expandStmts_length l rel term cold rest (cur + 5) (nextTmp + 2) [] [.assign dst (.arg (.imm 1))]
        dsimp only
        refine ⟨?_, by omega⟩
        simp only [List.length_cons, ih.1, stmtsExtra_cons, stmtExtra, hc, siteExtra]
        omega
      | alloc dst idx lay cls args =>
        have ih := expandStmts_length l rel term cold rest (cur + 6) (nextTmp + 5) [dst]
          (Lir.Stmt.store .w64 (cellAddr dst) (.imm (Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1)) ::
            mkFieldStores dst 0 args).reverse
        dsimp only
        refine ⟨?_, by omega⟩
        simp only [List.length_cons, ih.1, stmtsExtra_cons, stmtExtra, hc, siteExtra]
        omega

theorem newLabel_succ (l : Layout) (F : Lir.Func) {i : Nat} {B : Lir.Block} (hi : F.blocks[i]? = some B) :
    newLabel l F (i + 1) = newLabel l F i + 1 + blockExtra l B := by
  have hget : F.blocks.toList[i]? = some B := by simpa using hi
  unfold newLabel
  rw [List.take_add_one, List.sum_append]
  have hmap : (F.blocks.toList.map (blockExtra l))[i]? = some (blockExtra l B) := by
    rw [List.getElem?_map, hget]; rfl
  rw [hmap]
  simp only [Option.toList_some, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

theorem newLabel_mono (l : Layout) (F : Lir.Func) {i j : Nat} (h : i ≤ j) :
    newLabel l F i + (j - i) ≤ newLabel l F j := by
  unfold newLabel
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  rw [List.take_add, List.sum_append]
  omega

theorem newLabel_le_iff (l : Layout) (F : Lir.Func) {i j : Nat} :
    newLabel l F i ≤ newLabel l F j ↔ i ≤ j := by
  constructor
  · intro h
    apply Nat.le_of_not_lt
    intro hlt
    have := newLabel_mono l F (Nat.le_of_lt hlt)
    omega
  · intro h
    have := newLabel_mono l F h
    omega

theorem newLabel_end_le_iff (l : Layout) (F : Lir.Func) {b t : Nat} {B : Lir.Block}
    (hb : F.blocks[b]? = some B) :
    newLabel l F t ≤ newLabel l F b + blockExtra l B ↔ t ≤ b := by
  constructor
  · intro h
    apply Nat.le_of_not_lt
    intro hlt
    have h1 := newLabel_mono l F (Nat.succ_le_of_lt hlt)
    rw [newLabel_succ l F hb] at h1
    omega
  · intro h
    have := newLabel_mono l F h
    omega

theorem expandBlocks_length (l : Layout) (rel : Lir.Label → Lir.Label) :
    ∀ (bs : List Lir.Block) (cur nextTmp : Nat),
      (expandBlocks l rel bs cur nextTmp).length = bs.length + (bs.map (blockExtra l)).sum
  | [], _, _ => rfl
  | b :: bs, cur, nextTmp => by
    unfold expandBlocks
    have h1 := (expandStmts_length l rel b.term b.cold b.body.toList cur nextTmp b.params []).1
    have h2 := expandBlocks_length l rel bs (cur + 1 + blockExtra l b) (expandBlock l rel cur nextTmp b).2
    simp only [List.length_append, List.length_cons, List.map_cons, List.sum_cons, h2]
    change (expandStmts l rel b.term b.cold b.body.toList cur nextTmp b.params []).1.length + _ = _
    rw [h1, ← blockExtra_eq]; omega

theorem expandBlocks_at (l : Layout) (rel : Lir.Label → Lir.Label) :
    ∀ (bs : List Lir.Block) (cur nextTmp i : Nat) (B : Lir.Block),
      bs[i]? = some B →
      ∃ tmp0, nextTmp ≤ tmp0 ∧
        ∀ (k : Nat) (blk : Lir.Block),
          (expandBlock l rel (cur + i + ((bs.map (blockExtra l)).take i).sum) tmp0 B).1[k]? = some blk →
          (expandBlocks l rel bs cur nextTmp)[i + ((bs.map (blockExtra l)).take i).sum + k]? = some blk
  | [], _, _, _, _, h => by simp at h
  | b :: bs, cur, nextTmp, 0, B, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    refine ⟨nextTmp, Nat.le_refl _, fun k blk hk => ?_⟩
    simp only [List.take_zero, List.sum_nil, Nat.add_zero, Nat.zero_add] at hk ⊢
    unfold expandBlocks
    have hlt := (List.getElem?_eq_some_iff.mp hk).1
    rw [List.getElem?_append_left hlt]
    exact hk
  | b :: bs, cur, nextTmp, i + 1, B, h => by
    simp only [List.getElem?_cons_succ] at h
    have hlen := expandStmts_length l rel b.term b.cold b.body.toList cur nextTmp b.params []
    obtain ⟨tmp0, htmp, hrec⟩ :=
      expandBlocks_at l rel bs (cur + 1 + blockExtra l b) (expandBlock l rel cur nextTmp b).2 i B h
    refine ⟨tmp0, Nat.le_trans hlen.2 htmp, fun k blk hk => ?_⟩
    have hcur : cur + (i + 1) + (((b :: bs).map (blockExtra l)).take (i + 1)).sum =
        (cur + 1 + blockExtra l b) + i + ((bs.map (blockExtra l)).take i).sum := by
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons]
      omega
    rw [hcur] at hk
    have hr := hrec k blk hk
    unfold expandBlocks
    have hblen : (expandBlock l rel cur nextTmp b).1.length = 1 + blockExtra l b := hlen.1
    have hidx : (i + 1) + (((b :: bs).map (blockExtra l)).take (i + 1)).sum + k =
        (expandBlock l rel cur nextTmp b).1.length + (i + ((bs.map (blockExtra l)).take i).sum + k) := by
      rw [hblen]
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons]
      omega
    rw [hidx, List.getElem?_append_right (Nat.le_add_right _ _)]
    simpa [Nat.add_sub_cancel_left] using hr

theorem newLabel_oob (l : Layout) (F : Lir.Func) {t : Nat} (ht : F.blocks.size ≤ t) :
    (inlineFunc l F).blocks[newLabel l F t]? = none := by
  apply Array.getElem?_eq_none
  have hlen : (inlineFunc l F).blocks.size =
      F.blocks.size + (F.blocks.toList.map (blockExtra l)).sum := by
    simp [inlineFunc, expandBlocks_length]
  rw [hlen]
  have htake : (F.blocks.toList.map (blockExtra l)).take t = F.blocks.toList.map (blockExtra l) :=
    List.take_of_length_le (by simp [ht])
  unfold newLabel
  rw [htake]; omega

/-! ## `ChunkAt` / `ChunkPos`: suffix-cursor invariant inside an expanded block -/

/-- Explicit witness that raw position `(b, rawPos)` in `F` corresponds to
expanded position `(inLbl, inPos)` in `inlineFunc l F` with expansion state
`(tmp, params, acc, rest)`. -/
structure ChunkAt (l : Layout) (F : Lir.Func) (b : Lir.Label) (B : Lir.Block)
    (rawPos : Nat) (inLbl : Lir.Label) (inPos : Nat)
    (tmp : Nat) (params : List Lir.VReg) (acc rest : List Lir.Stmt) : Prop where
  bLookup : F.blocks[b]? = some B
  tmpGe : freshBase F ≤ tmp
  split : B.body.toList = (B.body.toList.take rawPos) ++ rest
  posLe : rawPos ≤ B.body.size
  blocksMatch : ∀ k blk,
    (expandStmts l (newLabel l F) B.term B.cold rest inLbl tmp params acc).1[k]? = some blk →
    (inlineFunc l F).blocks[inLbl + k]? = some blk
  inPosEq : inPos = acc.length
  endLbl : inLbl + stmtsExtra l rest = newLabel l F b + blockExtra l B

/-- Existential chunk-cursor invariant. -/
def ChunkPos (l : Layout) (F : Lir.Func) (b : Lir.Label) (B : Lir.Block)
    (rawPos : Nat) (inLbl : Lir.Label) (inPos : Nat) : Prop :=
  ∃ tmp params acc rest, ChunkAt l F b B rawPos inLbl inPos tmp params acc rest

namespace ChunkPos

/-- Every original block entry `(b, 0)` corresponds to `(newLabel l F b, 0)`. -/
theorem entry (l : Layout) (F : Lir.Func) {b : Lir.Label} {B : Lir.Block}
    (hb : F.blocks[b]? = some B) : ChunkPos l F b B 0 (newLabel l F b) 0 := by
  have hbList : F.blocks.toList[b]? = some B := by simpa using hb
  obtain ⟨tmp0, htmp, hblk⟩ :=
    expandBlocks_at l (newLabel l F) F.blocks.toList 0 (freshBase F) b B hbList
  refine ⟨tmp0, B.params, [], B.body.toList, {
    bLookup := hb
    tmpGe := htmp
    split := by simp
    posLe := Nat.zero_le _
    blocksMatch := fun k blk hk => by
      have h0 := hblk k blk (by simpa [newLabel, expandBlock] using hk)
      simpa [inlineFunc, newLabel] using h0
    inPosEq := rfl
    endLbl := rfl }⟩

/-- Head block of `expandStmts`: the first emitted block contains `acc.reverse`
as a prefix, keeps `params`, and reveals either the next non-inlined statement
or the relabeled terminator when `ss = []`. -/
theorem firstBlock_of_expandStmts (l : Layout) (rel : Lir.Label → Lir.Label)
    (term : Lir.Term) (cold : Bool) :
    ∀ (ss : List Lir.Stmt) (cur nextTmp : Nat) (params : List Lir.VReg) (acc : List Lir.Stmt),
      ∃ blk post,
        (expandStmts l rel term cold ss cur nextTmp params acc).1[0]? = some blk ∧
        blk.params = params ∧
        blk.body.toList = acc.reverse ++ post ∧
        (∀ s rest', ss = s :: rest' → classify l s = none → post.head? = some s) ∧
        (ss = [] → post = [] ∧ blk.term = relabelTerm rel term)
  | [], cur, nextTmp, params, acc =>
    ⟨_, [], rfl, rfl, (by simp), (fun _ _ h _ => by cases h), (fun _ => ⟨rfl, rfl⟩)⟩
  | s :: rest, cur, nextTmp, params, acc => by
    unfold expandStmts
    cases hc : classify l s with
    | none =>
      obtain ⟨blk, post, h0, hp, hbody, hhead, hnil⟩ :=
        firstBlock_of_expandStmts l rel term cold rest cur nextTmp params (s :: acc)
      refine ⟨blk, s :: post, h0, hp, ?_, ?_, fun h => by cases h⟩
      · simpa [List.reverse_cons, List.append_assoc] using hbody
      · intro s' r' heq _; cases heq; rfl
    | some site =>
      cases site with
      | inc dst x =>
        exact ⟨_, [], rfl, rfl, (by simp),
          (fun _ _ h hnc => by cases h; rw [hc] at hnc; cases hnc), (fun h => by cases h)⟩
      | dec dst x =>
        exact ⟨_, [], rfl, rfl, (by simp),
          (fun _ _ h hnc => by cases h; rw [hc] at hnc; cases hnc), (fun h => by cases h)⟩
      | alloc dst idx lay cls args =>
        exact ⟨_, [.assign nextTmp (.load .w64 .zero (ctxAddr (Int.ofNat (8 * cls))))], rfl, rfl,
          (by simp [List.reverse_cons]),
          (fun _ _ h hnc => by cases h; rw [hc] at hnc; cases hnc), (fun h => by cases h)⟩

/-- The entry of block `b` keeps its exact block parameters. -/
theorem entry_params (l : Layout) (F : Lir.Func) {b : Lir.Label} {B : Lir.Block}
    (hb : F.blocks[b]? = some B) :
    ∃ B', (inlineFunc l F).blocks[newLabel l F b]? = some B' ∧ B'.params = B.params := by
  obtain ⟨tmp, params, acc, rest, cp⟩ := entry l F hb
  obtain ⟨blk, _, hblk, hp, _, _, _⟩ :=
    firstBlock_of_expandStmts l (newLabel l F) B.term B.cold rest (newLabel l F b) tmp params acc
  have hpB : params = B.params := by
    -- entry constructs params = B.params; get directly via expandBlocks_at
    have hbList : F.blocks.toList[b]? = some B := by simpa using hb
    obtain ⟨tmp0, _, hblk0⟩ :=
      expandBlocks_at l (newLabel l F) F.blocks.toList 0 (freshBase F) b B hbList
    obtain ⟨blk0, _, h0, hp0, _, _, _⟩ :=
      firstBlock_of_expandStmts l (newLabel l F) B.term B.cold B.body.toList (newLabel l F b) tmp0 B.params []
    have h1 : (inlineFunc l F).blocks[newLabel l F b]? = some blk := by
      simpa using cp.blocksMatch 0 blk hblk
    have h2 : (inlineFunc l F).blocks[newLabel l F b]? = some blk0 := by
      have := hblk0 0 blk0 (by simpa [newLabel, expandBlock] using h0)
      simpa [inlineFunc, newLabel] using this
    rw [h1] at h2; cases h2; rw [← hp, hp0]
  exact ⟨blk, by simpa using cp.blocksMatch 0 blk hblk, hp.trans hpB⟩

/-- If `rawPos < B.body.size`, then `rest = B.body[rawPos] :: rest'`. -/
theorem rest_cons {l : Layout} {F : Lir.Func} {b : Lir.Label} {B : Lir.Block}
    {rawPos inLbl inPos tmp : Nat} {params : List Lir.VReg} {acc rest : List Lir.Stmt}
    (cp : ChunkAt l F b B rawPos inLbl inPos tmp params acc rest)
    (hlt : rawPos < B.body.size) :
    ∃ rest', rest = B.body[rawPos] :: rest' := by
  have hlen : (B.body.toList.take rawPos).length = rawPos := by
    rw [List.length_take]; simp; omega
  cases hrest : rest with
  | nil =>
    have := congrArg List.length cp.split
    rw [hrest, List.append_nil, hlen] at this
    simp only [Array.length_toList] at this
    omega
  | cons s rest' =>
    have hget : B.body.toList[rawPos]? = some s := by
      rw [cp.split, hrest, List.getElem?_append_right (by omega), hlen]
      simp
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hlt, Option.some.injEq] at hget
    exact ⟨rest', by rw [hget]⟩

/-- If `rawPos = B.body.size`, then `rest = []`. -/
theorem rest_nil {l : Layout} {F : Lir.Func} {b : Lir.Label} {B : Lir.Block}
    {rawPos inLbl inPos tmp : Nat} {params : List Lir.VReg} {acc rest : List Lir.Stmt}
    (cp : ChunkAt l F b B rawPos inLbl inPos tmp params acc rest)
    (heq : rawPos = B.body.size) : rest = [] := by
  have := congrArg List.length cp.split
  rw [List.length_append, List.length_take] at this
  simp only [Array.length_toList] at this
  have h0 : rest.length = 0 := by omega
  exact List.eq_nil_of_length_eq_zero h0

/-- Advance `ChunkAt` past a non-inlined statement `s` (`classify l s = none`). -/
theorem step_normal {l : Layout} {F : Lir.Func} {b : Lir.Label} {B : Lir.Block}
    {rawPos inLbl inPos tmp : Nat} {params : List Lir.VReg} {acc rest : List Lir.Stmt}
    (cp : ChunkAt l F b B rawPos inLbl inPos tmp params acc rest)
    {s : Lir.Stmt} {rest' : List Lir.Stmt} (hrest : rest = s :: rest')
    (hnc : classify l s = none) (hlt : rawPos < B.body.size) (hget : B.body[rawPos] = s) :
    (∃ blk, (inlineFunc l F).blocks[inLbl]? = some blk ∧
      inPos < blk.body.size ∧ blk.body[inPos]? = some s) ∧
    ChunkPos l F b B (rawPos + 1) inLbl (inPos + 1) := by
  obtain ⟨blk, post, h0, _, hbody, hhead, _⟩ :=
    firstBlock_of_expandStmts l (newLabel l F) B.term B.cold rest inLbl tmp params acc
  have hblk : (inlineFunc l F).blocks[inLbl]? = some blk := by
    simpa using cp.blocksMatch 0 blk h0
  have hpost := hhead s rest' hrest hnc
  cases post with
  | nil => simp at hpost
  | cons s' post' =>
    simp only [List.head?_cons, Option.some.injEq] at hpost
    subst s'
    have hsz : inPos < blk.body.size := by
      have := congrArg List.length hbody
      simp only [Array.length_toList, List.length_append, List.length_reverse, List.length_cons] at this
      rw [cp.inPosEq]; omega
    have hstmt : blk.body[inPos]? = some s := by
      rw [← Array.getElem?_toList, hbody, cp.inPosEq,
        List.getElem?_append_right (by simp), List.length_reverse]
      simp
    refine ⟨⟨blk, hblk, hsz, hstmt⟩, tmp, params, s :: acc, rest', {
      bLookup := cp.bLookup
      tmpGe := cp.tmpGe
      split := by
        have htake : B.body.toList.take (rawPos + 1) = B.body.toList.take rawPos ++ [s] := by
          rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hlt, hget]
          simp
        rw [htake, List.append_assoc]
        simpa [hrest] using cp.split
      posLe := by omega
      blocksMatch := fun k blk' hk => by
        apply cp.blocksMatch k blk'
        rw [hrest]; unfold expandStmts; rw [hnc]; exact hk
      inPosEq := by simp [cp.inPosEq]
      endLbl := by
        have := cp.endLbl
        rw [hrest, stmtsExtra_cons, stmtExtra, hnc] at this
        simpa using this }⟩

/-- At the end of a block (`rawPos = B.body.size`), the expanded block has
`inPos = blk.body.size`, `blk.term = relabelTerm (newLabel l F) B.term`,
and `inLbl = newLabel l F b + blockExtra l B`. -/
theorem at_term {l : Layout} {F : Lir.Func} {b : Lir.Label} {B : Lir.Block}
    {rawPos inLbl inPos : Nat} (cp0 : ChunkPos l F b B rawPos inLbl inPos)
    (heq : rawPos = B.body.size) :
    ∃ blk, (inlineFunc l F).blocks[inLbl]? = some blk ∧
      inPos = blk.body.size ∧
      blk.term = relabelTerm (newLabel l F) B.term ∧
      inLbl = newLabel l F b + blockExtra l B := by
  obtain ⟨tmp, params, acc, rest, cp⟩ := cp0
  have hnil := rest_nil cp heq
  obtain ⟨blk, post, h0, _, hbody, _, hend⟩ :=
    firstBlock_of_expandStmts l (newLabel l F) B.term B.cold rest inLbl tmp params acc
  obtain ⟨rfl, hterm⟩ := hend hnil
  have hblk : (inlineFunc l F).blocks[inLbl]? = some blk := by
    simpa using cp.blocksMatch 0 blk h0
  have hsz : inPos = blk.body.size := by
    have := congrArg List.length hbody
    simp only [Array.length_toList, List.append_nil, List.length_reverse] at this
    rw [cp.inPosEq, this]
  have hlbl : inLbl = newLabel l F b + blockExtra l B := by
    have := cp.endLbl
    rw [hnil, stmtsExtra_nil, Nat.add_zero] at this
    exact this
  exact ⟨blk, hblk, hsz, hterm, hlbl⟩

end ChunkPos

end IxCC.Cfg.Rc.Inline
