import IxCC.Anf.Proof.Defun.Translate
import IxCC.Anf.Proof.Defun.Dispatch
import IxCC.Anf.Proof.Rel.Basic

/-! # P8's fundamental lemma

The translation simulates its source at every clock bound (`fund`), by strong
induction on the bound (`FundAt`, as `Anf.Rel.Ident.level`): every construct
but the three P8 rewrites is the generic compatibility lemma of
`Anf.Rel.Basic`; a local function becomes the cell of its lifted global
(`DV.lam`, over the target environment), a function global's value its
field-less cell (`DV.glob`), and an unknown call a call of the dispatcher of
its arity (`dispatch_sim`): the dispatcher's charge is the target's extra one
(`SimUpTo.laterR`); a saturated call enters the lifted body, which by the
renaming lemma (`eval_rename`, `capRen_env`) evaluates as the walk's image
over the closure's environment, related one clock down. -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Anf.Rel (Pw)

variable {X : Setting}

/-! ## Related lists -/

theorem pw_of_dvs : ∀ {vs ws : List Val}, DVs X vs ws → Pw (DV X) vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (pw_of_dvs hs)

theorem dvs_of_pw : ∀ {vs ws : List Val}, Pw (DV X) vs ws → DVs X vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (dvs_of_pw hs)

/-! ## Values -/

theorem dv_atom {ρ ρ' : List Val} (hρ : Pw (DV X) ρ ρ') : ∀ a : Atom,
    (a.eval ρ = none ∧ a.eval ρ' = none) ∨ ∃ v w, a.eval ρ = some v ∧ a.eval ρ' = some w ∧ DV X v w
  | .var i => by simpa [Atom.eval] using hρ.get i
  | .lit _ => .inr ⟨_, _, rfl, rfl, .lit⟩
  | .box => .inr ⟨_, _, rfl, rfl, .box⟩

theorem dv_atoms {ρ ρ' : List Val} (hρ : Pw (DV X) ρ ρ') : ∀ as : List Atom,
    (evalAtoms ρ as = none ∧ evalAtoms ρ' as = none) ∨
      ∃ vs ws, evalAtoms ρ as = some vs ∧ evalAtoms ρ' as = some ws ∧ Pw (DV X) vs ws
  | [] => .inr ⟨[], [], rfl, rfl, .nil⟩
  | a :: as => by
    rw [evalAtoms_cons, evalAtoms_cons]
    rcases dv_atom hρ a with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · left; simp [h1, h2]
    · rcases dv_atoms hρ as with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
      · left; simp [h1, h2, h3, h4]
      · right; exact ⟨v :: vs, w :: ws, by simp [h1, h3], by simp [h2, h4], .cons hvw hvs⟩

theorem natArgs_dv : ∀ {vs ws : List Val}, Pw (DV X) vs ws → natArgs ws = natArgs vs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hvw hvs => by
    cases hvw with
    | @lit l =>
      cases l with
      | nat m => simp [natArgs, natArgs_dv hvs]
      | str s => simp [natArgs]
    | box => simp [natArgs]
    | con _ => simp [natArgs]
    | lam => simp [natArgs]
    | glob => simp [natArgs]

theorem prim_dv {n : Nat} (K : Lam.Known) (p : Lam.Prim) {vs ws : List Val} (h : Pw (DV X) vs ws) :
    SimUpTo (DV X) n (fun _ => primResult K p vs) (fun _ => primResult K p ws) := by
  unfold primResult
  rw [natArgs_dv h]
  cases natArgs vs with
  | none => exact SimUpTo.stuck _
  | some ns =>
    simp only
    cases p.sem ns with
    | none => exact SimUpTo.stuck _
    | some r =>
      cases r with
      | nat m => exact SimUpTo.ok .lit
      | bool b =>
        simp only
        cases (if b then K.boolTrue else K.boolFalse) with
        | none => exact SimUpTo.stuck _
        | some c => exact SimUpTo.ok (.con .nil)

theorem proj_dv {n : Nat} (c : Key.CtorKey) (i : Nat) {v w : Val} (h : DV X v w) :
    SimUpTo (DV X) n (fun _ => projVal c i v) (fun _ => projVal c i w) := by
  cases h with
  | con hvs =>
    simp only [projVal]
    split
    · exact Rel.sim_ofOption ((pw_of_dvs hvs).get i)
    · exact SimUpTo.stuck _
  | lit => exact SimUpTo.stuck _
  | box => exact SimUpTo.stuck _
  | lam => exact SimUpTo.stuck _
  | glob => exact SimUpTo.stuck _

theorem asCtor_dv (K : Lam.Known) {v w : Val} (h : DV X v w) :
    (v.asCtor K = none) ∨ ∃ c fs fs', v.asCtor K = some (c, fs) ∧ w.asCtor K = some (c, fs') ∧ Pw (DV X) fs fs' := by
  cases h with
  | @lit l =>
    cases l with
    | nat m =>
      cases m with
      | zero =>
        cases hz : K.natZero with
        | none => left; simp [Val.asCtor, hz]
        | some z => right; exact ⟨z, [], [], by simp [Val.asCtor, hz], by simp [Val.asCtor, hz], .nil⟩
      | succ m =>
        cases hs : K.natSucc with
        | none => left; simp [Val.asCtor, hs]
        | some s =>
          right
          exact ⟨s, [.lit (.nat m)], [.lit (.nat m)], by simp [Val.asCtor, hs], by simp [Val.asCtor, hs],
            .cons .lit .nil⟩
    | str _ => left; rfl
  | box => left; rfl
  | con hvs => right; exact ⟨_, _, _, rfl, rfl, pw_of_dvs hvs⟩
  | lam => left; rfl
  | glob => left; rfl

/-! ## The translation's image has no local function -/

mutual

theorem tr_fo : ∀ {Γ : Nat} {e e' : Exp}, Tr X Γ e e' → Exp.firstOrder (fun _ => false) e' = true
  | _, _, _, .bind hb he => by simp only [Exp.firstOrder, trB_fo hb, tr_fo he, Bool.and_self]
  | _, _, _, .join hb he => by simp only [Exp.firstOrder, tr_fo hb, tr_fo he, Bool.and_self]
  | _, _, _, .jump => rfl
  | _, _, _, .case ha ho => by simp only [Exp.firstOrder, trAlts_fo ha, trOpt_fo ho, Bool.and_self]
  | _, _, _, .ret => rfl
  | _, _, _, .tick he => by simp only [Exp.firstOrder, tr_fo he]
  | _, _, _, .trap => rfl

theorem trB_fo : ∀ {Γ : Nat} {b b' : Bind}, TrB X Γ b b' → Bind.firstOrder (fun _ => false) b' = true
  | _, _, _, .atom => rfl
  | _, _, _, .con => rfl
  | _, _, _, .proj => rfl
  | _, _, _, .prim => rfl
  | _, _, _, .call => rfl
  | _, _, _, .caf .. => rfl
  | _, _, _, .absent .. => rfl
  | _, _, _, .glob .. => rfl
  | _, _, _, .app0 => rfl
  | _, _, _, .app .. => rfl
  | _, _, _, .fn .. => rfl

theorem trAlts_fo : ∀ {Γ : Nat} {alts alts' : List Alt}, TrAlts X Γ alts alts' →
    Exp.altsFirstOrder (fun _ => false) alts' = true
  | _, _, _, .nil => rfl
  | _, _, _, .cons hb ha => by simp only [Exp.altsFirstOrder, tr_fo hb, trAlts_fo ha, Bool.and_self]

theorem trOpt_fo : ∀ {Γ : Nat} {o o' : Option Exp}, TrOpt X Γ o o' → Exp.optFirstOrder (fun _ => false) o' = true
  | _, _, _, .none => rfl
  | _, _, _, .some he => by simp only [Exp.optFirstOrder, tr_fo he]

end

/-! ## Join closures -/

theorem JRel.get : ∀ {J J' : List JClo}, JRel X J J' → ∀ (j : Nat),
    (J[j]? = none ∧ J'[j]? = none) ∨ ∃ ρ ρ' J0 J0' Γ n b b' r, J[j]? = some (.mk ρ J0 n b r) ∧
      J'[j]? = some (.mk ρ' J0' n b' r) ∧ Tr X (Γ + n) b b' ∧ Γ ≤ ρ.length ∧ DVs X ρ ρ' ∧ JRel X J0 J0'
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons hb hΓ hρ h0 _, 0 => .inr ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, hb, hΓ, hρ, h0⟩
  | _, _, .cons _ _ _ _ h, j + 1 => by simpa using h.get j

/-! ## Clocks -/

theorem later_bind {α β : Type} (k : Nat) (F : Nat → Result α) (G : Nat → α → Result β) :
    (later k F).bind (G k) = later k fun k' => (F k').bind (G (k' + 1)) := by
  cases k <;> rfl

theorem bind_ok_right {α : Type} (r : Result α) : r.bind .ok = r := by
  cases r <;> rfl

theorem clockMono_shift {α : Type} {c : Nat → Result α} (h : ClockMono c) : ClockMono fun k => c (k + 1) :=
  fun _ _ hle hk => h (Nat.succ_le_succ hle) hk

theorem callVal_mono (Q : Program) (D : GDef) (vs : List Val) : ClockMono fun k => callVal Q k D vs := by
  unfold callVal
  split
  · exact ClockMono.later (eval_mono Q _ [] _)
  · exact ClockMono.const _

/-- Both sides one clock up: a simulation to `n + 1` is one to `n` of the
shifted computations. -/
theorem simUpTo_shift {α β : Type} {R : α → β → Prop} {n : Nat} {c : Nat → Result α} {d : Nat → Result β}
    (hm : ClockMono d) (h : SimUpTo R (n + 1) c d) : SimUpTo R n (fun k => c (k + 1)) (fun k => d (k + 1)) where
  fwd k hk hne := by
    obtain ⟨k', h'⟩ := h.fwd (k + 1) (by omega) hne
    by_cases ht : d k' = .timeout
    · rw [ht] at h'
      rcases h'.of_timeout with h'' | h''
      · exact absurd h'' hne
      · exact ⟨0, by show Result.Refines R (c (k + 1)) _; rw [h'']; exact .stuck⟩
    · exact ⟨k', by show Result.Refines R (c (k + 1)) (d (k' + 1)); rw [hm (Nat.le_succ k') ht]; exact h'⟩
  tmo k hk ht := h.tmo (k + 1) (by omega) ht

/-! ## The dispatcher's alternatives, at every clock -/

theorem callVal_dispatcher {Q : Program} {k size m : Nat} {srcs pre post : List Source} {s : Source}
    (hsrcs : srcs = pre ++ s :: post) (hpre : ∀ s' ∈ pre, s'.key ≠ s.key) {j : Nat} (hj : j < s.arity)
    {fs ws : List Val} (hfs : fs.length = s.caps + j) (hws : ws.length = m) :
    callVal Q k (dispatcher size srcs m) (.con (.clo s.key j) fs :: ws) =
      later k fun k => eval Q k (fs.reverse ++ (ws.reverse ++ [.con (.clo s.key j) fs])) [] (altBody size s j m) := by
  have hl : (Val.con (.clo s.key j) fs :: ws).length = (dispatcher size srcs m).ps.length := by
    simp [dispatcher, hws]
  unfold callVal
  rw [ite_eq_left hl]
  congr 1
  funext k'
  rw [List.reverse_cons]
  exact eval_dispatcher hsrcs hpre hj hfs hws

theorem eval_altBody_exact_later {P : Program} {k size m : Nat} {s : Source} {j : Nat} {fs args ρ : List Val}
    {gd : GDef} (hs : P.global? s.id = some gd) (hps : gd.ps.length = s.caps + s.arity) (hj : j < s.arity)
    (hfs : fs.length = s.caps + j) (hargs : args.length = m) (hm : m = s.arity - j) :
    eval P k (fs.reverse ++ (args.reverse ++ ρ)) [] (altBody size s j m) =
      later k fun k => eval P k (fs ++ args).reverse [] gd.body := by
  have hn : (fs ++ args).length = gd.ps.length := by
    rw [List.length_append, hfs, hargs, hps, hm]; omega
  simp only [altBody]
  rw [ite_eq_left hm, eval_bind_ret, evalBind_call_of P k _ hs (evalAtoms_alt hfs hargs) hn]

/-- The fields and the first `r` arguments, read by the over alternative's first call. -/
theorem evalAtoms_alt_take {s : Source} {j m : Nat} {fs args ρ : List Val} (hfs : fs.length = s.caps + j)
    (hargs : args.length = m) (hrm : s.arity - j ≤ m) :
    evalAtoms (fs.reverse ++ (args.reverse ++ ρ))
      (downFrom (s.caps + j - 1) (s.caps + j) ++ (downFrom (s.caps + j + m - 1) m).take (s.arity - j)) =
      some (fs ++ args.take (s.arity - j)) := by
  have henv : fs.reverse ++ (args.reverse ++ ρ) =
      fs.reverse ++ (args.drop (s.arity - j)).reverse ++ ((args.take (s.arity - j)).reverse ++ ρ) := by
    conv => lhs; rw [← List.take_append_drop (s.arity - j) args]
    simp only [List.reverse_append, List.append_assoc]
  have hlt : (args.take (s.arity - j)).length = s.arity - j := by
    rw [List.length_take, hargs]; omega
  have hld : (args.drop (s.arity - j)).length = m - (s.arity - j) := by
    rw [List.length_drop, hargs]
  apply evalAtoms_append
  · have := evalAtoms_downFrom_nil fs (args.reverse ++ ρ)
    rwa [hfs] at this
  · rw [downFrom_take _ _ _ hrm, henv]
    have := evalAtoms_downFrom (fs.reverse ++ (args.drop (s.arity - j)).reverse) (args.take (s.arity - j)) ρ
    rw [List.length_append, List.length_reverse, List.length_reverse, hfs, hld, hlt] at this
    have e : s.caps + j + (m - (s.arity - j)) + (s.arity - j) - 1 = s.caps + j + m - 1 := by omega
    rw [e] at this
    simp only [List.append_assoc] at this ⊢
    exact this

/-- The result and the rest of the arguments, read by the over alternative's second call. -/
theorem evalAtoms_alt_drop {s : Source} {j m : Nat} {fs args ρ : List Val} (hfs : fs.length = s.caps + j)
    (hargs : args.length = m) (hm : s.arity - j < m) (v : Val) :
    evalAtoms (v :: (fs.reverse ++ (args.reverse ++ ρ)))
      (.var 0 :: ((downFrom (s.caps + j + m - 1) m).drop (s.arity - j)).map shiftVar) =
      some (v :: args.drop (s.arity - j)) := by
  have hrm : s.arity - j ≤ m := Nat.le_of_lt hm
  have henv : fs.reverse ++ (args.reverse ++ ρ) =
      fs.reverse ++ (args.drop (s.arity - j)).reverse ++ ((args.take (s.arity - j)).reverse ++ ρ) := by
    conv => lhs; rw [← List.take_append_drop (s.arity - j) args]
    simp only [List.reverse_append, List.append_assoc]
  have hld : (args.drop (s.arity - j)).length = m - (s.arity - j) := by
    rw [List.length_drop, hargs]
  rw [evalAtoms_cons, downFrom_drop _ _ _ hrm,
    downFrom_map_shift (s.caps + j + m - 1 - (s.arity - j)) (m - (s.arity - j)) (by omega), henv]
  have := evalAtoms_downFrom (v :: fs.reverse) (args.drop (s.arity - j)) ((args.take (s.arity - j)).reverse ++ ρ)
  rw [List.length_cons, List.length_reverse, hfs, hld] at this
  have e : s.caps + j + 1 + (m - (s.arity - j)) - 1 = s.caps + j + m - 1 - (s.arity - j) + 1 := by omega
  rw [e] at this
  simp only [List.cons_append, List.append_assoc] at this ⊢
  rw [this]
  all_goals rfl

/-- More arguments than missing, at every clock: the call of `s` on the fields
and the first `r` arguments, then the call of the dispatcher of the remaining
arity on the result and the rest, at the same clock. -/
theorem eval_altBody_over_later {P : Program} {k size m : Nat} {s : Source} {j : Nat} {fs args ρ : List Val}
    {gd D : GDef} (hs : P.global? s.id = some gd) (hps : gd.ps.length = s.caps + s.arity) (hj : j < s.arity)
    (hfs : fs.length = s.caps + j) (hargs : args.length = m) (hm : s.arity - j < m)
    (hd : P.global? (dispId size (m - (s.arity - j))) = some D) (hD : D.ps.length = m - (s.arity - j) + 1) :
    eval P k (fs.reverse ++ (args.reverse ++ ρ)) [] (altBody size s j m) =
      (later k fun k => eval P k (fs ++ args.take (s.arity - j)).reverse [] gd.body).bind fun v =>
        callVal P k D (v :: args.drop (s.arity - j)) := by
  have hlt : (args.take (s.arity - j)).length = s.arity - j := by
    rw [List.length_take, hargs]; omega
  have hld : (args.drop (s.arity - j)).length = m - (s.arity - j) := by
    rw [List.length_drop, hargs]
  have hn1 : (fs ++ args.take (s.arity - j)).length = gd.ps.length := by
    rw [List.length_append, hfs, hlt, hps]; omega
  have hn2 : ∀ v : Val, (v :: args.drop (s.arity - j)).length = D.ps.length := fun v => by
    rw [List.length_cons, hld, hD]
  have hne1 : ¬m = s.arity - j := by omega
  have hne2 : ¬m < s.arity - j := by omega
  simp only [altBody]
  rw [ite_eq_right hne1, ite_eq_right hne2, eval_bind,
    evalBind_call_of P k _ hs (evalAtoms_alt_take hfs hargs (Nat.le_of_lt hm)) hn1]
  congr 1
  funext v
  rw [eval_bind_ret, evalBind_call_of P k _ hd (evalAtoms_alt_drop hfs hargs hm v) (hn2 v)]
  unfold callVal
  rw [ite_eq_left (hn2 v)]

/-! ## Unknown calls -/

/-- **Applying a closure through the dispatcher**: a closure of arity `N`
with `got` supplied, whose cell is `con (clo s.key got.length) fs`, applied to
`vs`, against the dispatcher of `vs`'s arity on the cell and related `ws`; given
that a saturated application simulates one clock down (`hsat`), a partial one
is related (`hunder`), and shorter argument lists simulate (`hrest`). -/
theorem clo_step (hX : Valid X) {n : Nat} {ρ : List Val} {N : Nat} {b : Exp} {got : List Val}
    {s : Source} {fs : List Val} {gd : GDef}
    (hs : s ∈ X.srcs) (har : s.arity = N) (hgot : got.length < N) (hfs : fs.length = s.caps + got.length)
    (hgd : X.Q.global? s.id = some gd) (hps : gd.ps.length = s.caps + N)
    (hsat : ∀ ⦃args args' : List Val⦄, Pw (DV X) args args' → got.length + args.length = N → ∀ m < n,
      SimUpTo (DV X) m (fun k => eval X.P k ((got ++ args).reverse ++ ρ) [] b)
        (fun k => eval X.Q k (fs ++ args').reverse [] gd.body))
    (hunder : ∀ ⦃args args' : List Val⦄, Pw (DV X) args args' → got.length + args.length < N →
      DV X (.clos ρ N b (got ++ args)) (.con (.clo s.key (got.length + args.length)) (fs ++ args')))
    {vs ws : List Val}
    (hrest : ∀ ⦃f g : Val⦄ ⦃vs' ws' : List Val⦄, vs'.length < vs.length → DV X f g → Pw (DV X) vs' ws' →
      vs' ≠ [] → vs'.length ≤ X.M →
      SimUpTo (DV X) n (fun k => applyN X.P k f vs')
        (fun k => callVal X.Q k (dispatcher X.P.size X.srcs vs'.length) (g :: ws')))
    (hvs : Pw (DV X) vs ws) (hne : vs ≠ []) (hm : vs.length ≤ X.M) :
    SimUpTo (DV X) n (fun k => applyN X.P k (.clos ρ N b got) vs)
      (fun k => callVal X.Q k (dispatcher X.P.size X.srcs vs.length) (.con (.clo s.key got.length) fs :: ws)) := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_nodup hX.keys hs
  have hl : ws.length = vs.length := hvs.length
  have hj : got.length < s.arity := by rw [har]; exact hgot
  obtain ⟨v, rest, rfl⟩ : ∃ v rest, vs = v :: rest := by
    cases vs with
    | nil => exact absurd rfl hne
    | cons v rest => exact ⟨v, rest, rfl⟩
  have hT : ∀ k, callVal X.Q k (dispatcher X.P.size X.srcs (v :: rest).length)
      (.con (.clo s.key got.length) fs :: ws) = later k fun k =>
        eval X.Q k (fs.reverse ++ (ws.reverse ++ [.con (.clo s.key got.length) fs])) []
          (altBody X.P.size s got.length (v :: rest).length) :=
    fun k => callVal_dispatcher hsplit hpre hj hfs hl
  have hS : ∀ k, applyN X.P k (.clos ρ N b got) (v :: rest) = later k fun k =>
      if got.length + (v :: rest).length < N then .ok (.clos ρ N b (got ++ v :: rest))
      else enter X.P k ρ N b (got ++ v :: rest) := by
    intro k
    rw [applyN_clos]
    congr 1
    funext k'
    rw [ite_eq_left hgot]
  by_cases hu : got.length + (v :: rest).length < N
  · -- fewer arguments than missing: one charge on each side, related closures
    refine (SimUpTo.later fun _ _ => SimUpTo.ok (hunder hvs hu)).congr (fun k => ?_) (fun k => ?_)
    · rw [hS]
      congr 1
      funext k'
      rw [ite_eq_left hu]
    · rw [hT]
      congr 1
      funext k'
      rw [eval_altBody_under hfs hl (by rw [har]; omega)]
  · by_cases he : got.length + (v :: rest).length = N
    · -- exactly the missing arguments: the dispatcher's charge is the target's extra one
      refine (SimUpTo.later fun i hi => SimUpTo.laterR (eval_mono X.Q _ [] _) (hsat hvs he i (by omega))).congr
        (fun k => ?_) (fun k => ?_)
      · rw [hS]
        congr 1
        funext k'
        rw [ite_eq_right hu]
        have hlen : (got ++ v :: rest).length = N := by rw [List.length_append]; exact he
        unfold enter
        rw [List.take_of_length_le (Nat.le_of_eq hlen), List.drop_of_length_le (Nat.le_of_eq hlen)]
        simp only [applyN_nil', bind_ok_right]
      · rw [hT]
        congr 1
        funext k'
        exact eval_altBody_exact_later hgd (by rw [hps, har]) hj hfs hl (by rw [har]; omega)
    · -- more arguments: the first `r` saturate; the dispatcher of the rest applies the result
      have hr : N - got.length < (v :: rest).length := by omega
      have hrN : s.arity - got.length = N - got.length := by rw [har]
      have hm' : 1 ≤ (v :: rest).length - (N - got.length) := by omega
      have hm'' : (v :: rest).length - (N - got.length) ≤ X.M := by omega
      have hD := hX.disp _ hm' hm''
      rw [Setting.dispId] at hD
      have hDps : (dispatcher X.P.size X.srcs ((v :: rest).length - (N - got.length))).ps.length =
          (v :: rest).length - (N - got.length) + 1 := by simp [dispatcher]
      have htake : (got ++ v :: rest).take N = got ++ (v :: rest).take (N - got.length) := by
        rw [List.take_append, List.take_of_length_le (by omega)]
      have hdrop : (got ++ v :: rest).drop N = (v :: rest).drop (N - got.length) := by
        rw [List.drop_append, List.drop_of_length_le (by omega), List.nil_append]
      have hlenT : got.length + ((v :: rest).take (N - got.length)).length = N := by
        rw [List.length_take]; omega
      have hin : ∀ i, i + 1 ≤ n → SimUpTo (DV X) i
          (fun k => (eval X.P k ((got ++ (v :: rest).take (N - got.length)).reverse ++ ρ) [] b).bind fun x =>
            applyN X.P (k + 1) x ((v :: rest).drop (N - got.length)))
          (fun k => later k fun k => (eval X.Q k (fs ++ ws.take (N - got.length)).reverse [] gd.body).bind fun y =>
            callVal X.Q (k + 1) (dispatcher X.P.size X.srcs ((v :: rest).length - (N - got.length)))
              (y :: ws.drop (N - got.length))) := by
        intro i hi
        refine SimUpTo.laterR (ClockMono.bind (eval_mono X.Q _ [] _) fun y => clockMono_shift (callVal_mono X.Q _ _)) ?_
        refine SimUpTo.bind (d := fun x k => applyN X.P (k + 1) x ((v :: rest).drop (N - got.length)))
          (d' := fun y k => callVal X.Q (k + 1) (dispatcher X.P.size X.srcs ((v :: rest).length - (N - got.length)))
            (y :: ws.drop (N - got.length)))
          (eval_mono X.Q _ [] _) (fun y => clockMono_shift (callVal_mono X.Q _ _))
          (hsat (hvs.take _) hlenT i (by omega)) fun x y hxy => ?_
        have hd : ((v :: rest).drop (N - got.length)).length = (v :: rest).length - (N - got.length) :=
          List.length_drop
        have := hrest (by rw [hd]; omega) hxy (hvs.drop _)
          (List.ne_nil_of_length_pos (by rw [hd]; omega))
          (by rw [hd]; exact hm'')
        rw [hd] at this
        exact simUpTo_shift (callVal_mono X.Q _ _) (this.mono_n hi)
      refine (SimUpTo.later hin).congr (fun k => ?_) (fun k => ?_)
      · rw [hS]
        congr 1
        funext k'
        rw [ite_eq_right hu]
        unfold enter
        rw [htake, hdrop]
      · rw [hT]
        congr 1
        funext k'
        have := eval_altBody_over_later (P := X.Q) (k := k') (size := X.P.size) (ρ := [.con (.clo s.key got.length) fs])
          hgd (by rw [hps, har]) hj hfs hl (by rw [har]; omega) (by rw [hrN]; exact hD) (by rw [hrN]; exact hDps)
        rw [hrN] at this
        rw [this]
        exact later_bind k' _ (fun k x => callVal X.Q k (dispatcher X.P.size X.srcs ((v :: rest).length - (N - got.length)))
          (x :: ws.drop (N - got.length)))


theorem evalAtoms_vars {ρ : List Val} : ∀ {xs : List Nat}, (∀ x ∈ xs, x < ρ.length) →
    evalAtoms ρ (xs.map .var) = some (xs.map fun x => ρ.getD x .box)
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.map_cons, evalAtoms_cons, evalAtoms_vars fun y hy => h y (List.mem_cons_of_mem _ hy)]
    have hx := h x List.mem_cons_self
    show ((ρ[x]?).bind fun v => some (v :: _)) = _
    rw [List.getElem?_eq_getElem hx]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx]

/-- **The dispatcher lemma**: applying related values in the source is calling
the dispatcher of the arguments' arity in the target. -/
theorem dispatch_sim (hX : Valid X) {n : Nat} (hlow : ∀ m < n, FundAt X m) :
    ∀ ⦃f g : Val⦄ ⦃vs ws : List Val⦄, DV X f g → Pw (DV X) vs ws → vs ≠ [] → vs.length ≤ X.M →
      SimUpTo (DV X) n (fun k => applyN X.P k f vs)
        (fun k => callVal X.Q k (dispatcher X.P.size X.srcs vs.length) (g :: ws)) := by
  suffices H : ∀ len, ∀ ⦃f g : Val⦄ ⦃vs ws : List Val⦄, vs.length ≤ len → DV X f g → Pw (DV X) vs ws →
      vs ≠ [] → vs.length ≤ X.M →
      SimUpTo (DV X) n (fun k => applyN X.P k f vs)
        (fun k => callVal X.Q k (dispatcher X.P.size X.srcs vs.length) (g :: ws)) by
    intro f g vs ws hfg hvs hne hm
    exact H _ (Nat.le_refl _) hfg hvs hne hm
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
  intro f g vs ws hlen hfg hvs hne hm
  have hrest : ∀ ⦃f g : Val⦄ ⦃vs' ws' : List Val⦄, vs'.length < vs.length → DV X f g → Pw (DV X) vs' ws' →
      vs' ≠ [] → vs'.length ≤ X.M →
      SimUpTo (DV X) n (fun k => applyN X.P k f vs')
        (fun k => callVal X.Q k (dispatcher X.P.size X.srcs vs'.length) (g :: ws')) :=
    fun f g vs' ws' hlt hfg' hvs' hne' hm' => ih vs'.length (by omega) (Nat.le_refl _) hfg' hvs' hne' hm'
  have hnc : (∀ ρ n b got, f ≠ .clos ρ n b got) →
      SimUpTo (DV X) n (fun k => applyN X.P k f vs)
        (fun k => callVal X.Q k (dispatcher X.P.size X.srcs vs.length) (g :: ws)) := by
    intro hf
    obtain ⟨v, rest, rfl⟩ : ∃ v rest, vs = v :: rest := by
      cases vs with
      | nil => exact absurd rfl hne
      | cons v rest => exact ⟨v, rest, rfl⟩
    exact (SimUpTo.stuck _).congr (fun k => applyN_not_clos X.P k f v rest hf) (fun _ => rfl)
  cases hfg with
  | lit => exact hnc fun _ _ _ _ h => nomatch h
  | box => exact hnc fun _ _ _ _ h => nomatch h
  | con _ => exact hnc fun _ _ _ _ h => nomatch h
  | lam hs har hgot htr hfree hcaps hgd hgps hbody hΓ hρ hgot' =>
    rename_i ρ ρ' N Γ b b' got got' s gd
    have hρl : ρ'.length = ρ.length := (pw_of_dvs hρ).length
    have hgl : got'.length = got.length := (pw_of_dvs hgot').length
    refine clo_step hX hs har hgot (by rw [List.length_append, List.length_map, ← hcaps, hgl]) hgd hgps
      ?_ ?_ hrest hvs hne hm
    · intro args args' hargs hlenN m hm'
      have hal : args'.length = args.length := hargs.length
      have hT : ∀ k, eval X.Q k (((capsOf Γ N b').map fun x => ρ'.getD x .box) ++ got' ++ args').reverse [] gd.body =
          eval X.Q k ((got' ++ args').reverse ++ ρ') [] b' := by
        intro k
        rw [hbody]
        refine eval_rename X.Q _ k (d := 0) (tr_fo htr) (fun x hx => ?_) .nil
        rw [ren_zero_base, List.append_assoc, List.reverse_append]
        refine capRen_env (A := (got' ++ args').reverse) (by rw [List.length_reverse, List.length_append, hgl, hal]; omega)
          (by rw [hρl]; exact hΓ) x ?_
        by_cases hxN : x < N
        · exact .inl hxN
        · right
          have hy : x - N ∈ b'.free N := by
            have := free_shift (d := 0) (k := N) (x := x - N) (e := b') (by rw [Nat.sub_add_cancel (by omega)]; exact hx)
            rwa [Nat.zero_add] at this
          exact captures_mem hy (hfree _ hy)
      refine (hlow m hm' htr ?_ ?_ .nil).congr (fun _ => rfl) (fun k => hT k)
      · rw [List.length_append, List.length_reverse, List.length_append]; omega
      · exact dvs_of_pw (((pw_of_dvs hgot').append hargs).reverse.append (pw_of_dvs hρ))
    · intro args args' hargs hlt
      have := DV.lam hs har (by rw [List.length_append]; omega) htr hfree hcaps hgd hgps hbody hΓ hρ
        (dvs_of_pw ((pw_of_dvs hgot').append hargs))
      rw [List.length_append] at this
      rwa [List.append_assoc]
  | glob hg hlen' hs hgot hq hqps htr hgot' =>
    rename_i h N hd gd got ws0
    have hgl : ws0.length = got.length := (pw_of_dvs hgot').length
    refine clo_step hX hs rfl hgot (by rw [hgl]; exact (Nat.zero_add _).symm) hq (by rw [hqps]; exact (Nat.zero_add _).symm)
      ?_ ?_ hrest hvs hne hm
    · intro args args' hargs hlenN m hm'
      refine (hlow m hm' htr ?_ ?_ .nil).congr (fun k => by rw [List.append_nil]) (fun _ => rfl)
      · dsimp only at hlenN; rw [List.length_reverse, List.length_append]; omega
      · exact dvs_of_pw ((pw_of_dvs hgot').append hargs).reverse
    · intro args args' hargs hlt
      have := DV.glob hg hlen' hs (by rw [List.length_append]; omega) hq hqps htr
        (dvs_of_pw ((pw_of_dvs hgot').append hargs))
      rwa [List.length_append] at this

/-- Calling an input global on related arguments. -/
theorem call_sim (hX : Valid X) {n : Nat} (hlow : ∀ m < n, FundAt X m) (g : GlobalId) ⦃vs ws : List Val⦄
    (hvs : Pw (DV X) vs ws) :
    SimUpTo (DV X) n (fun k => (Result.ofOption (X.P.global? g)).bind (callVal X.P k · vs))
      (fun k => (Result.ofOption (X.Q.global? g)).bind (callVal X.Q k · ws)) := by
  cases hP : X.P.global? g with
  | none => exact (SimUpTo.stuck _).congr (fun k => rfl) (fun _ => rfl)
  | some gd =>
    obtain ⟨gd', hq, hps, htr⟩ := hX.old g gd hP
    rw [hq]
    simp only [Result.ofOption, Result.bind_ok]
    have hvl := hvs.length
    by_cases hl : vs.length = gd.ps.length
    · have hl' : ws.length = gd'.ps.length := by rw [hvl, hl, hps]
      refine (SimUpTo.later fun i hi => hlow i (by omega) htr (Nat.le_of_eq (by rw [List.length_reverse, hl]))
        (dvs_of_pw hvs.reverse) .nil).congr (fun k => ?_) (fun k => ?_)
      · unfold callVal; rw [ite_eq_left hl]
      · unfold callVal; rw [ite_eq_left hl']
    · have hl' : ¬ ws.length = gd'.ps.length := by rw [hvl, hps]; exact hl
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      unfold callVal; rw [ite_eq_right hl]

/-! ## The fundamental lemma -/

theorem fund_bind (hX : Valid X) {n : Nat} (hlow : ∀ m < n, FundAt X m) :
    ∀ {Γ : Nat} {b b' : Bind} {ρ ρ' : List Val}, TrB X Γ b b' → Γ ≤ ρ.length → Pw (DV X) ρ ρ' →
      SimUpTo (DV X) n (fun k => evalBind X.P k ρ b) (fun k => evalBind X.Q k ρ' b')
  | _, _, _, ρ, ρ', @TrB.atom _ _ a, _, hρ =>
    (Rel.sim_ofOption (dv_atom hρ a)).congr (fun k => evalBind_atom X.P k ρ a) (fun k => evalBind_atom X.Q k ρ' a)
  | _, _, _, ρ, ρ', @TrB.con _ _ c as, _, hρ => by
    refine SimUpTo.congr ?_ (fun k => evalBind_con X.P k ρ c as) (fun k => evalBind_con X.Q k ρ' c as)
    rcases dv_atoms hρ as with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
    · rw [h1, h2]; exact SimUpTo.stuck _
    · rw [h1, h2]; exact SimUpTo.ok (.con (dvs_of_pw hvs))
  | _, _, _, ρ, ρ', @TrB.proj _ _ c i x, _, hρ => by
    refine SimUpTo.congr ?_ (fun k => evalBind_proj X.P k ρ c i x) (fun k => evalBind_proj X.Q k ρ' c i x)
    rcases dv_atom hρ x with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · rw [h1, h2]; exact SimUpTo.stuck _
    · rw [h1, h2]; exact proj_dv c i hvw
  | _, _, _, ρ, ρ', @TrB.prim _ _ p as, _, hρ => by
    refine SimUpTo.congr ?_ (fun k => evalBind_prim X.P k ρ p as) (fun k => evalBind_prim X.Q k ρ' p as)
    rcases dv_atoms hρ as with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
    · rw [h1, h2]; exact SimUpTo.stuck _
    · rw [h1, h2, hX.known]; exact prim_dv X.P.known p hvs
  | _, _, _, ρ, ρ', @TrB.call _ _ g as, _, hρ => by
    refine SimUpTo.congr ?_ (fun k => evalBind_call X.P k ρ g as) (fun k => evalBind_call X.Q k ρ' g as)
    rcases dv_atoms hρ as with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
    · refine (SimUpTo.stuck (fun _ => .stuck)).congr (fun k => ?_) (fun k => ?_)
      · rw [h1]; cases X.P.global? g <;> rfl
      · rw [h2]; cases X.Q.global? g <;> rfl
    · refine (call_sim hX hlow g hvs).congr (fun k => ?_) (fun k => ?_)
      · rw [h1]; cases X.P.global? g <;> rfl
      · rw [h2]; cases X.Q.global? g <;> rfl
  | _, _, _, ρ, ρ', @TrB.caf _ _ h hd _ hg hps, _, _ => by
    obtain ⟨gd', hq, hps', htr⟩ := hX.old h hd hg
    rw [hps] at hps' htr
    refine SimUpTo.congr ?_ (fun k => evalBind_glob X.P k ρ h) (fun k => evalBind_glob X.Q k ρ' h)
    rw [hg, hq]
    simp only [Result.ofOption, Result.bind_ok, globVal, hps, hps']
    exact SimUpTo.later fun i hi => hlow i (by omega) htr (Nat.zero_le _) .nil .nil
  | _, _, _, ρ, ρ', @TrB.absent _ _ h _ hg, _, _ =>
    (SimUpTo.stuck _).congr (fun k => by rw [evalBind_glob, hg]; rfl) (fun _ => rfl)
  | _, _, _, ρ, ρ', @TrB.glob _ _ h hd _ hg hps hs, _, _ => by
    obtain ⟨gd', hq, hps', htr⟩ := hX.old h hd hg
    refine (SimUpTo.ok (DV.glob (got := []) hg rfl hs (List.length_pos_iff.2 hps) hq (by rw [hps']) htr .nil)).congr
      (fun k => ?_) (fun k => ?_)
    · rw [evalBind_glob, hg]
      simp only [Result.ofOption, Result.bind_ok, globVal]
      cases hc : hd.ps with
      | nil => exact absurd hc hps
      | cons _ _ => rfl
    · rw [evalBind_con]; rfl
  | _, _, _, ρ, ρ', @TrB.app0 _ _ f, _, hρ => by
    refine SimUpTo.congr ?_ (fun k => evalBind_app X.P k ρ f []) (fun k => evalBind_atom X.Q k ρ' f)
    rcases dv_atom hρ f with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · rw [h1, h2]; exact SimUpTo.stuck _
    · rw [h1, h2]
      simp only [Result.ofOption, Result.bind_ok, evalAtoms_nil]
      exact (SimUpTo.ok hvw).congr (fun k => applyN_nil' X.P k v) (fun _ => rfl)
  | _, _, _, ρ, ρ', @TrB.app _ _ f as hne hm, _, hρ => by
    refine SimUpTo.congr ?_ (fun k => evalBind_app X.P k ρ f as)
      (fun k => evalBind_call X.Q k ρ' (X.dispId as.length) (f :: as))
    rcases dv_atom hρ f with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · rw [h1]; exact SimUpTo.stuck _
    · rcases dv_atoms hρ as with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
      · rw [h1, h3]; exact SimUpTo.stuck _
      · have hal := evalAtoms_length ρ h3
        have hD := hX.disp as.length (List.length_pos_iff.2 hne) hm
        have hfa : evalAtoms ρ' (f :: as) = some (w :: ws) := by rw [evalAtoms_cons, h2, h4]; rfl
        rw [h1, h3, hD, hfa]
        simp only [Result.ofOption, Result.bind_ok]
        rw [← hal]
        exact dispatch_sim hX hlow hvw hvs (by intro h0; rw [h0] at hal; exact hne (List.eq_nil_of_length_eq_zero hal.symm))
          (by rw [hal]; exact hm)
  | _, _, _, ρ, ρ', @TrB.fn _ Γ ps b b' s gd hps htr hfree hs hcaps harity hgd hgps hbody, hΓ, hρ => by
    have hρl : ρ'.length = ρ.length := hρ.length
    have hcl : ∀ x ∈ capsOf Γ ps.length b', x < ρ'.length := fun x hx => by
      rw [hρl]; exact Nat.lt_of_lt_of_le (captures_lt hx) hΓ
    have hv := DV.lam hs harity (by rw [List.length_nil]; exact List.length_pos_iff.2 hps) htr hfree hcaps hgd
      hgps hbody hΓ (dvs_of_pw hρ) .nil
    rw [List.append_nil] at hv
    refine (SimUpTo.ok hv).congr (fun k => evalBind_fn X.P k ρ ps b hps) (fun k => ?_)
    rw [evalBind_con, evalAtoms_vars hcl]
    rfl

mutual

theorem fund_exp (hX : Valid X) {n : Nat} (hlow : ∀ m < n, FundAt X m) :
    ∀ {Γ : Nat} {e e' : Exp} {ρ ρ' : List Val} {J J' : List JClo}, Tr X Γ e e' → Γ ≤ ρ.length →
      Pw (DV X) ρ ρ' → JRel X J J' →
      SimUpTo (DV X) n (fun k => eval X.P k ρ J e) (fun k => eval X.Q k ρ' J' e')
  | _, _, _, _, _, _, _, .bind hb he, hΓ, hρ, hJ =>
    Rel.compat_bind (fund_bind hX hlow hb hΓ hρ) fun _ _ hvw =>
      fund_exp hX hlow he (by rw [List.length_cons]; omega) (.cons hvw hρ) hJ
  | _, _, _, _, _, _, _, .join hb he, hΓ, hρ, hJ =>
    Rel.compat_join (fund_exp hX hlow he hΓ hρ (.cons hb hΓ (dvs_of_pw hρ) hJ hJ))
  | _, _, _, ρ, ρ', J, J', @Tr.jump _ _ j as, _, hρ, hJ => by
    refine SimUpTo.congr ?_ (fun k => eval_jump X.P k ρ J j as) (fun k => eval_jump X.Q k ρ' J' j as)
    rcases hJ.get j with ⟨h1, h2⟩ | ⟨ρj, ρj', J0, J0', Γj, m, b, b', r, h1, h2, hb, hΓj, hρj, hJ0⟩
    · rw [h1]; exact SimUpTo.stuck _
    · rw [h1, h2]
      simp only [Result.ofOption, Result.bind_ok]
      rcases dv_atoms hρ as with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
      · rw [h3]; exact SimUpTo.stuck _
      · rw [h3, h4]
        simp only [Result.bind_ok]
        refine Rel.compat_jumpTo hvs (fun _ _ _ _ _ _ _ _ _ e1 e2 => ?_) (fun _ _ _ _ _ _ _ _ _ _ e1 e2 => ?_)
        · cases e1; cases e2
          refine ⟨rfl, fun i hi hlen => hlow i (by omega) hb
            (by rw [List.length_append, List.length_reverse, hlen]; omega)
            (dvs_of_pw (hvs.reverse.append (pw_of_dvs hρj))) ?_⟩
          cases r
          · exact hJ0
          · exact .cons hb hΓj hρj hJ0 hJ0
        · cases e1; cases e2; rfl
  | _, _, _, ρ, ρ', J, J', @Tr.case _ _ x alts alts' d d' ha ho, hΓ, hρ, hJ => by
    refine SimUpTo.congr ?_ (fun k => eval_case X.P k ρ J x alts d) (fun k => eval_case X.Q k ρ' J' x alts' d')
    rcases dv_atom hρ x with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · rw [h1]; exact SimUpTo.stuck _
    · rw [h1, h2, hX.known]
      simp only [Result.ofOption, Result.bind_ok]
      rcases asCtor_dv X.P.known hvw with h3 | ⟨c, fs, fs', h3, h4, hfs⟩
      · rw [h3]; exact SimUpTo.stuck _
      · rw [h3, h4]
        exact fund_alts hX hlow hΓ hρ hJ c hfs (fund_opt hX hlow ho hΓ hρ hJ) ha
  | _, _, _, ρ, ρ', J, J', @Tr.ret _ _ a, _, hρ, _ =>
    (Rel.sim_ofOption (dv_atom hρ a)).congr (fun k => eval_ret' X.P k ρ J a) (fun k => eval_ret' X.Q k ρ' J' a)
  | _, _, _, _, _, _, _, .tick he, hΓ, hρ, hJ =>
    Rel.compat_tick fun m hm => hlow m (by omega) he hΓ (dvs_of_pw hρ) hJ
  | _, _, _, _, _, _, _, .trap, _, _, _ => Rel.compat_trap

theorem fund_opt (hX : Valid X) {n : Nat} (hlow : ∀ m < n, FundAt X m) :
    ∀ {Γ : Nat} {d d' : Option Exp} {ρ ρ' : List Val} {J J' : List JClo}, TrOpt X Γ d d' → Γ ≤ ρ.length →
      Pw (DV X) ρ ρ' → JRel X J J' →
      (d = none ∧ d' = none) ∨ ∃ e e', d = some e ∧ d' = some e' ∧
        SimUpTo (DV X) n (fun k => eval X.P k ρ J e) (fun k => eval X.Q k ρ' J' e')
  | _, _, _, _, _, _, _, .none, _, _, _ => .inl ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, .some he, hΓ, hρ, hJ => .inr ⟨_, _, rfl, rfl, fund_exp hX hlow he hΓ hρ hJ⟩

theorem fund_alts (hX : Valid X) {n : Nat} (hlow : ∀ m < n, FundAt X m) {Γ : Nat} {ρ ρ' : List Val}
    {J J' : List JClo} (hΓ : Γ ≤ ρ.length) (hρ : Pw (DV X) ρ ρ') (hJ : JRel X J J') (c : Key.CtorKey)
    {fs fs' : List Val} (hfs : Pw (DV X) fs fs') {d d' : Option Exp}
    (hd : (d = none ∧ d' = none) ∨ ∃ e e', d = some e ∧ d' = some e' ∧
      SimUpTo (DV X) n (fun k => eval X.P k ρ J e) (fun k => eval X.Q k ρ' J' e')) :
    ∀ {alts alts' : List Alt}, TrAlts X Γ alts alts' →
      SimUpTo (DV X) n (fun k => evalAlts X.P k ρ J c fs alts d) (fun k => evalAlts X.Q k ρ' J' c fs' alts' d')
  | _, _, .nil => by
    refine SimUpTo.congr ?_ (fun k => evalAlts_nil X.P k ρ J c fs d) (fun k => evalAlts_nil X.Q k ρ' J' c fs' d')
    rcases hd with ⟨rfl, rfl⟩ | ⟨e, e', rfl, rfl, hs⟩
    · exact SimUpTo.stuck _
    · exact hs
  | _, _, @TrAlts.cons _ _ m key b b' as as' hb ha => by
    refine SimUpTo.congr ?_ (fun k => evalAlts_cons X.P k ρ J c fs key m b as d)
      (fun k => evalAlts_cons X.Q k ρ' J' c fs' key m b' as' d')
    have hl := hfs.length
    by_cases hsel : key = c ∧ m = fs.length
    · have hsel' : key = c ∧ m = fs'.length := ⟨hsel.1, by rw [hl]; exact hsel.2⟩
      exact (fund_exp hX hlow hb (by rw [List.length_append, List.length_reverse, ← hsel.2]; omega)
        (hfs.reverse.append hρ) hJ).congr (fun _ => ite_eq_left hsel) (fun _ => ite_eq_left hsel')
    · have hsel' : ¬ (key = c ∧ m = fs'.length) := by rw [hl]; exact hsel
      exact (fund_alts hX hlow hΓ hρ hJ c hfs hd ha).congr (fun _ => ite_eq_right hsel) (fun _ => ite_eq_right hsel')

end

/-- **The fundamental lemma** of the translation, at every clock bound. -/
theorem fund (hX : Valid X) : ∀ n, FundAt X n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro Γ e e' ρ ρ' J J' htr hΓ hρ hJ
  exact fund_exp hX (fun m hm => ih m hm) htr hΓ (pw_of_dvs hρ) hJ

end IxCC.Anf.Defun.Proof
