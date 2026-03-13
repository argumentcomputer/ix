/-
  Ix.Theory.Roundtrip: The NbE eval-quote roundtrip theorems.

  The core correctness property: NbE produces normal forms.

  **NbE Stability**: if a well-formed value quotes to expression `e`,
  then NbE of `e` in the standard fvar environment returns `e` unchanged.

  **NbE Idempotence**: nbe(nbe(e)) = nbe(e).
-/
import Ix.Theory.EvalWF

namespace Ix.Theory

variable {L : Type}

/-! ## Standard fvar environment

  The "open" environment where bvar i maps to fvar(d-1-i).
  This is the identity environment for the NbE roundtrip. -/

/-- Standard fvar environment at depth d: [fvar(d-1), fvar(d-2), ..., fvar(0)]. -/
def fvarEnv (d : Nat) : List (SVal L) :=
  (List.range d).reverse.map (fun i => SVal.neutral (.fvar i) [])

theorem fvarEnv_length : (fvarEnv (L := L) d).length = d := by
  simp [fvarEnv]

theorem fvarEnv_get (h : i < d) : (fvarEnv (L := L) d)[i]? = some (.neutral (.fvar (d - 1 - i)) []) := by
  simp only [fvarEnv]
  rw [List.getElem?_map, List.getElem?_reverse (by simp; exact h)]
  simp [List.length_range, List.getElem?_range (by omega : d - 1 - i < d)]

theorem fvarEnv_succ (d : Nat) :
    SVal.neutral (.fvar d) [] :: fvarEnv (L := L) d = fvarEnv (d + 1) := by
  simp only [fvarEnv, List.range_succ, List.reverse_append, List.map_cons,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]

theorem EnvWF_fvarEnv (d : Nat) : EnvWF (fvarEnv (L := L) d) d := by
  induction d with
  | zero => exact .nil
  | succ d ih =>
    rw [← fvarEnv_succ]
    exact .cons (.neutral (.fvar (by omega)) .nil) (ih.mono (by omega))

/-! ## Bind decomposition helpers -/

-- For Option.bind (used by eval_s equation lemmas which reduce by rfl)
private theorem option_bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp [Option.bind]

-- For Bind.bind / do notation (used by auto-generated quote_s/quoteSpine_s equation lemmas)
private theorem bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  show x.bind f = some b ↔ _
  cases x <;> simp [Option.bind]

/-! ## Fuel monotonicity

  More fuel never changes the result — it only allows more computation.
  Since eval_s/apply_s and quote_s/quoteSpine_s are mutual, we prove
  each pair jointly by induction on fuel. -/

-- eval_s/apply_s equation lemmas (hold by rfl since they reduce definitionally)
private theorem eval_s_zero : eval_s 0 e env = (none : Option (SVal L)) := rfl
private theorem eval_s_bvar : eval_s (n+1) (.bvar idx : SExpr L) env = env[idx]? := rfl
private theorem eval_s_sort : eval_s (n+1) (.sort u : SExpr L) env = some (.sort u) := rfl
private theorem eval_s_const' : eval_s (n+1) (.const c ls : SExpr L) env = some (.neutral (.const c ls) []) := rfl
private theorem eval_s_lit : eval_s (n+1) (.lit l : SExpr L) env = some (.lit l) := rfl
private theorem eval_s_proj : eval_s (n+1) (.proj t i s : SExpr L) env = (none : Option (SVal L)) := rfl
private theorem eval_s_app : eval_s (n+1) (.app fn arg : SExpr L) env =
    (eval_s n fn env).bind fun fv => (eval_s n arg env).bind fun av => apply_s n fv av := rfl
private theorem eval_s_lam : eval_s (n+1) (.lam dom body : SExpr L) env =
    (eval_s n dom env).bind fun dv => some (.lam dv body env) := rfl
private theorem eval_s_forallE : eval_s (n+1) (.forallE dom body : SExpr L) env =
    (eval_s n dom env).bind fun dv => some (.pi dv body env) := rfl
private theorem eval_s_letE : eval_s (n+1) (.letE ty val body : SExpr L) env =
    (eval_s n val env).bind fun vv => eval_s n body (vv :: env) := rfl

private theorem apply_s_zero : apply_s 0 fn arg = (none : Option (SVal L)) := rfl
private theorem apply_s_lam : apply_s (n+1) (.lam dom body fenv : SVal L) arg =
    eval_s n body (arg :: fenv) := rfl
private theorem apply_s_neutral : apply_s (n+1) (.neutral hd spine : SVal L) arg =
    some (.neutral hd (spine ++ [arg])) := rfl

-- quote_s/quoteSpine_s use auto-generated equation lemmas:
-- quote_s.eq_1 : quote_s 0 v d = none
-- quote_s.eq_2 : quote_s (n+1) (.sort u) d = some (.sort u)
-- quote_s.eq_3 : quote_s (n+1) (.lit n) d = some (.lit n)
-- quote_s.eq_4 : quote_s (n+1) (.lam dom body env) d = do ...
-- quote_s.eq_5 : quote_s (n+1) (.pi dom body env) d = do ...
-- quote_s.eq_6 : quote_s (n+1) (.neutral hd spine) d = quoteSpine_s n (quoteHead hd d) spine d
-- quoteSpine_s.eq_1 : quoteSpine_s n acc [] d = some acc
-- quoteSpine_s.eq_2 : quoteSpine_s n acc (arg :: rest) d = do ...

private theorem eval_apply_fuel_mono_aux (n : Nat) :
    (∀ (m : Nat) (e : SExpr L) (env : List (SVal L)) (v : SVal L),
      eval_s n e env = some v → n ≤ m → eval_s m e env = some v) ∧
    (∀ (m : Nat) (fn arg v : SVal L),
      apply_s n fn arg = some v → n ≤ m → apply_s m fn arg = some v) := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ h => by rw [eval_s_zero] at h; exact absurd h nofun,
           fun _ _ _ _ h => by rw [apply_s_zero] at h; exact absurd h nofun⟩
  | succ n0 ih =>
    obtain ⟨ihe, iha⟩ := ih
    constructor
    · intro m e env v hev hle
      cases m with
      | zero => omega
      | succ m0 =>
        have hle' : n0 ≤ m0 := Nat.le_of_succ_le_succ hle
        cases e with
        | bvar idx => rwa [eval_s_bvar] at hev ⊢
        | sort _ => rwa [eval_s_sort] at hev ⊢
        | const _ _ => rwa [eval_s_const'] at hev ⊢
        | lit _ => rwa [eval_s_lit] at hev ⊢
        | proj _ _ _ => rwa [eval_s_proj] at hev ⊢
        | app fn arg =>
          rw [eval_s_app] at hev ⊢
          simp only [option_bind_eq_some] at hev ⊢
          obtain ⟨fv, hfn, av, harg, happ⟩ := hev
          exact ⟨fv, ihe m0 fn env fv hfn hle', av, ihe m0 arg env av harg hle',
                 iha m0 fv av v happ hle'⟩
        | lam dom body =>
          rw [eval_s_lam] at hev ⊢
          simp only [option_bind_eq_some] at hev ⊢
          obtain ⟨dv, hdom, hret⟩ := hev
          exact ⟨dv, ihe m0 dom env dv hdom hle', hret⟩
        | forallE dom body =>
          rw [eval_s_forallE] at hev ⊢
          simp only [option_bind_eq_some] at hev ⊢
          obtain ⟨dv, hdom, hret⟩ := hev
          exact ⟨dv, ihe m0 dom env dv hdom hle', hret⟩
        | letE ty val body =>
          rw [eval_s_letE] at hev ⊢
          simp only [option_bind_eq_some] at hev ⊢
          obtain ⟨vv, hval, hbody⟩ := hev
          exact ⟨vv, ihe m0 val env vv hval hle',
                 ihe m0 body (vv :: env) v hbody hle'⟩
    · intro m fn arg v hap hle
      cases m with
      | zero => omega
      | succ m0 =>
        have hle' : n0 ≤ m0 := Nat.le_of_succ_le_succ hle
        cases fn with
        | lam _dom body fenv =>
          rw [apply_s_lam] at hap ⊢
          exact ihe m0 body (arg :: fenv) v hap hle'
        | neutral hd spine => rwa [apply_s_neutral] at hap ⊢
        | sort _ => exact absurd hap nofun
        | lit _ => exact absurd hap nofun
        | pi _ _ _ => exact absurd hap nofun

theorem eval_fuel_mono {n m : Nat} {e : SExpr L} {env : List (SVal L)} {v : SVal L}
    (h_eval : eval_s n e env = some v) (h_le : n ≤ m) :
    eval_s m e env = some v :=
  (eval_apply_fuel_mono_aux n).1 m e env v h_eval h_le

theorem apply_fuel_mono {n m : Nat} {fn arg v : SVal L}
    (h : apply_s n fn arg = some v) (h_le : n ≤ m) :
    apply_s m fn arg = some v :=
  (eval_apply_fuel_mono_aux n).2 m fn arg v h h_le

private theorem quoteSpine_fuel_mono_of
    (hq : ∀ (m : Nat) (v : SVal L) (d : Nat) (e : SExpr L),
      quote_s n v d = some e → n ≤ m → quote_s m v d = some e)
    {acc : SExpr L} {spine : List (SVal L)} {d : Nat} {e : SExpr L}
    (h : quoteSpine_s n acc spine d = some e)
    {m : Nat} (hle : n ≤ m) :
    quoteSpine_s m acc spine d = some e := by
  induction spine generalizing acc with
  | nil =>
    rwa [quoteSpine_s.eq_1] at h ⊢
  | cons arg rest ih =>
    simp only [quoteSpine_s.eq_2, bind_eq_some] at h ⊢
    obtain ⟨argE, harg, hrest⟩ := h
    exact ⟨argE, hq m arg d argE harg hle, ih hrest⟩

private theorem quote_fuel_mono_aux (n : Nat) :
    ∀ (m : Nat) (v : SVal L) (d : Nat) (e : SExpr L),
      quote_s n v d = some e → n ≤ m → quote_s m v d = some e := by
  induction n with
  | zero => intro _ _ _ _ h; rw [quote_s.eq_1] at h; exact absurd h nofun
  | succ n0 ih =>
    intro m v d e hq hle
    cases m with
    | zero => omega
    | succ m0 =>
      have hle' : n0 ≤ m0 := Nat.le_of_succ_le_succ hle
      cases v with
      | sort _ => rwa [quote_s.eq_2] at hq ⊢
      | lit _ => rwa [quote_s.eq_3] at hq ⊢
      | lam dom body fenv =>
        simp only [quote_s.eq_4, bind_eq_some] at hq ⊢
        obtain ⟨domE, hd, bodyV, hb, bodyE, hbe, he⟩ := hq
        exact ⟨domE, ih m0 dom d domE hd hle', bodyV, eval_fuel_mono hb hle',
               bodyE, ih m0 bodyV (d + 1) bodyE hbe hle', he⟩
      | pi dom body fenv =>
        simp only [quote_s.eq_5, bind_eq_some] at hq ⊢
        obtain ⟨domE, hd, bodyV, hb, bodyE, hbe, he⟩ := hq
        exact ⟨domE, ih m0 dom d domE hd hle', bodyV, eval_fuel_mono hb hle',
               bodyE, ih m0 bodyV (d + 1) bodyE hbe hle', he⟩
      | neutral hd spine =>
        rw [quote_s.eq_6] at hq ⊢
        exact quoteSpine_fuel_mono_of ih hq hle'

theorem quote_fuel_mono {n m : Nat} {v : SVal L} {d : Nat} {e : SExpr L}
    (h_quote : quote_s n v d = some e) (h_le : n ≤ m) :
    quote_s m v d = some e :=
  quote_fuel_mono_aux n m v d e h_quote h_le

theorem quoteSpine_fuel_mono {n m : Nat} {acc : SExpr L} {spine : List (SVal L)} {d : Nat} {e : SExpr L}
    (h : quoteSpine_s n acc spine d = some e) (h_le : n ≤ m) :
    quoteSpine_s m acc spine d = some e :=
  quoteSpine_fuel_mono_of (fun _ _ _ _ hq hle => quote_fuel_mono hq hle) h h_le

/-! ## NbE stability helpers -/

-- Decomposition/construction of nbe_s
private theorem nbe_s_eq {fuel : Nat} {e : SExpr L} {env : List (SVal L)} {d : Nat} {e' : SExpr L} :
    nbe_s fuel e env d = some e' ↔
    ∃ v, eval_s fuel e env = some v ∧ quote_s fuel v d = some e' := by
  simp [nbe_s, option_bind_eq_some]

-- Evaluating a quoted head in fvarEnv gives the neutral
private theorem eval_quoteHead (hhd : HeadWF (L := L) hd d) :
    eval_s 1 (quoteHead hd d) (fvarEnv d) = some (.neutral hd []) := by
  cases hd with
  | fvar level =>
    cases hhd with | fvar hlevel =>
    simp only [quoteHead, levelToIndex, eval_s]
    rw [fvarEnv_get (by omega)]
    have : d - 1 - (d - 1 - level) = level := by omega
    rw [this]
  | const => simp [quoteHead, eval_s]

-- quoteSpine of (xs ++ [v]) = .app (quoteSpine of xs) (quote v)
private theorem quoteSpine_snoc
    (h1 : quoteSpine_s f1 acc xs d = some e1)
    (h2 : quote_s f2 v d = some vE)
    {F : Nat} (hF1 : f1 ≤ F) (hF2 : f2 ≤ F) :
    quoteSpine_s F acc (xs ++ [v]) d = some (.app e1 vE) := by
  induction xs generalizing acc with
  | nil =>
    rw [quoteSpine_s.eq_1] at h1; cases h1
    simp only [List.nil_append, quoteSpine_s.eq_2, bind_eq_some]
    exact ⟨vE, quote_fuel_mono h2 hF2, by rw [quoteSpine_s.eq_1]⟩
  | cons a rest ih =>
    simp only [List.cons_append, quoteSpine_s.eq_2, bind_eq_some] at h1 ⊢
    obtain ⟨aE, harg, hrest⟩ := h1
    exact ⟨aE, quote_fuel_mono harg hF1, ih hrest⟩

-- The neutral spine roundtrip: generalized accumulator version
private theorem nbe_stable_spine
    (d fuel : Nat) (spine : List (SVal L)) (acc : SExpr L)
    (accHd : SHead L) (accVals : List (SVal L))
    (f_eval : Nat) (h_eval : eval_s f_eval acc (fvarEnv d) = some (.neutral accHd accVals))
    (f_quote : Nat) (h_quote : quote_s f_quote (.neutral accHd accVals) d = some acc)
    (hsp : ListWF spine d)
    (ih : ∀ v e, ValWF v d → quote_s fuel v d = some e →
        ∃ fuel', nbe_s fuel' e (fvarEnv (L := L) d) d = some e)
    {e : SExpr L} (hqs : quoteSpine_s fuel acc spine d = some e) :
    ∃ fuel', nbe_s fuel' e (fvarEnv d) d = some e := by
  induction spine generalizing acc accVals f_eval f_quote with
  | nil =>
    rw [quoteSpine_s.eq_1] at hqs; cases hqs
    exact ⟨max f_eval f_quote,
           nbe_s_eq.mpr ⟨_, eval_fuel_mono h_eval (Nat.le_max_left ..), quote_fuel_mono h_quote (Nat.le_max_right ..)⟩⟩
  | cons a rest ih_rest =>
    simp only [quoteSpine_s.eq_2, bind_eq_some] at hqs
    obtain ⟨aE, harg, hrest_qs⟩ := hqs
    cases hsp with | cons ha hsp_rest =>
    -- Each spine element roundtrips via the outer IH
    obtain ⟨fa, h_nbe_a⟩ := ih a aE ha harg
    rw [nbe_s_eq] at h_nbe_a
    obtain ⟨va, h_eval_a, h_quote_a⟩ := h_nbe_a
    -- Build new accumulator eval: eval (.app acc aE) in fvarEnv d = .neutral accHd (accVals ++ [va])
    let K := max f_eval fa + 1
    have h_eval' : eval_s (K + 1) (.app acc aE) (fvarEnv (L := L) d) =
        some (.neutral accHd (accVals ++ [va])) := by
      rw [eval_s_app]
      simp only [option_bind_eq_some]
      exact ⟨.neutral accHd accVals, eval_fuel_mono h_eval (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_succ _)),
             va, eval_fuel_mono h_eval_a (by exact Nat.le_trans (Nat.le_max_right ..) (Nat.le_succ _)),
             by rw [apply_s_neutral]⟩
    -- Build new accumulator quote
    have h_fq_pos : 0 < f_quote := by
      cases f_quote with
      | zero => rw [quote_s.eq_1] at h_quote; exact absurd h_quote nofun
      | succ => omega
    obtain ⟨fq0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f_quote ≠ 0)
    rw [quote_s.eq_6] at h_quote
    let fq := max fq0 fa + 1
    have h_quote' : quote_s fq (.neutral accHd (accVals ++ [va])) d =
        some (.app acc aE) := by
      simp only [fq, quote_s.eq_6]
      exact quoteSpine_snoc h_quote h_quote_a (Nat.le_max_left ..) (Nat.le_max_right ..)
    exact ih_rest (.app acc aE) (accVals ++ [va]) (K + 1) h_eval' fq h_quote' hsp_rest hrest_qs

/-! ## NbE stability

  The corrected roundtrip theorem. If a well-formed value quotes to `e`,
  then NbE of `e` in the standard fvar environment returns `e` unchanged. -/

/-- **NbE Stability**: NbE produces normal forms.
    If a well-formed value quotes to `e`, then running NbE on `e` in the
    standard fvar environment gives back `e`. -/
theorem nbe_stable : ∀ (fuel : Nat) (v : SVal L) (d : Nat) (e : SExpr L),
    ValWF v d → quote_s fuel v d = some e →
    ∃ fuel', nbe_s fuel' e (fvarEnv (L := L) d) d = some e := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ _ h; rw [quote_s.eq_1] at h; exact absurd h nofun
  | succ n ih =>
    intro v d e h_wf h_quote
    cases v with
    | sort u =>
      rw [quote_s.eq_2] at h_quote; cases h_quote
      exact ⟨1, by simp [nbe_s, eval_s, quote_s]⟩
    | lit l =>
      rw [quote_s.eq_3] at h_quote; cases h_quote
      exact ⟨1, by simp [nbe_s, eval_s, quote_s]⟩
    | lam dom body fenv =>
      simp only [quote_s.eq_4, bind_eq_some] at h_quote
      obtain ⟨domE, hd, bodyV, hb, bodyE, hbe, he⟩ := h_quote
      cases he
      cases h_wf with | lam hwf_dom hclosed hwf_env =>
      -- IH on domain
      obtain ⟨fdom, h_nbe_dom⟩ := ih dom d domE hwf_dom hd
      rw [nbe_s_eq] at h_nbe_dom
      obtain ⟨dv, h_eval_dom, h_quote_dom⟩ := h_nbe_dom
      -- bodyV is well-formed at d+1
      have hwf_bodyV := eval_preserves_wf hb hclosed
        (.cons (.neutral (.fvar (by omega : d < d + 1)) .nil) (hwf_env.mono (by omega)))
      -- IH on body
      obtain ⟨fbody, h_nbe_body⟩ := ih bodyV (d + 1) bodyE hwf_bodyV hbe
      rw [nbe_s_eq] at h_nbe_body
      obtain ⟨bv, h_eval_body, h_quote_body⟩ := h_nbe_body
      -- Choose fuel and construct
      refine ⟨max fdom fbody + 1, nbe_s_eq.mpr ⟨.lam dv bodyE (fvarEnv d), ?_, ?_⟩⟩
      · rw [eval_s_lam]; simp only [option_bind_eq_some]
        exact ⟨dv, eval_fuel_mono h_eval_dom (Nat.le_max_left ..), rfl⟩
      · simp only [quote_s.eq_4, bind_eq_some]
        refine ⟨domE, quote_fuel_mono h_quote_dom (Nat.le_max_left ..), bv, ?_, bodyE, quote_fuel_mono h_quote_body (Nat.le_max_right ..), rfl⟩
        rw [fvarEnv_succ]
        exact eval_fuel_mono h_eval_body (Nat.le_max_right ..)
    | pi dom body fenv =>
      simp only [quote_s.eq_5, bind_eq_some] at h_quote
      obtain ⟨domE, hd, bodyV, hb, bodyE, hbe, he⟩ := h_quote
      cases he
      cases h_wf with | pi hwf_dom hclosed hwf_env =>
      obtain ⟨fdom, h_nbe_dom⟩ := ih dom d domE hwf_dom hd
      rw [nbe_s_eq] at h_nbe_dom
      obtain ⟨dv, h_eval_dom, h_quote_dom⟩ := h_nbe_dom
      have hwf_bodyV := eval_preserves_wf hb hclosed
        (.cons (.neutral (.fvar (by omega : d < d + 1)) .nil) (hwf_env.mono (by omega)))
      obtain ⟨fbody, h_nbe_body⟩ := ih bodyV (d + 1) bodyE hwf_bodyV hbe
      rw [nbe_s_eq] at h_nbe_body
      obtain ⟨bv, h_eval_body, h_quote_body⟩ := h_nbe_body
      refine ⟨max fdom fbody + 1, nbe_s_eq.mpr ⟨.pi dv bodyE (fvarEnv d), ?_, ?_⟩⟩
      · rw [eval_s_forallE]; simp only [option_bind_eq_some]
        exact ⟨dv, eval_fuel_mono h_eval_dom (Nat.le_max_left ..), rfl⟩
      · simp only [quote_s.eq_5, bind_eq_some]
        refine ⟨domE, quote_fuel_mono h_quote_dom (Nat.le_max_left ..), bv, ?_, bodyE, quote_fuel_mono h_quote_body (Nat.le_max_right ..), rfl⟩
        rw [fvarEnv_succ]
        exact eval_fuel_mono h_eval_body (Nat.le_max_right ..)
    | neutral hd spine =>
      rw [quote_s.eq_6] at h_quote
      cases h_wf with | neutral hhd hsp =>
      exact nbe_stable_spine d n spine (quoteHead hd d) hd [] 1
        (eval_quoteHead hhd)
        1 (by rw [quote_s.eq_6, quoteSpine_s.eq_1])
        hsp (fun v e hwf hq => ih v d e hwf hq) h_quote

/-! ## NbE idempotence

  Applying NbE twice gives the same result as applying it once.
  This means NbE produces normal forms. -/

/-- **NbE Idempotence**: nbe(nbe(e)) = nbe(e). -/
theorem nbe_idempotent (e : SExpr L) (env : List (SVal L)) (d : Nat) (fuel : Nat)
    (h_wf : EnvWF env d)
    (h_closed : SExpr.ClosedN e env.length)
    (v : SVal L)
    (h_eval : eval_s fuel e env = some v)
    (e' : SExpr L)
    (h_quote : quote_s fuel v d = some e') :
    ∃ fuel', nbe_s fuel' e' (fvarEnv (L := L) d) d = some e' :=
  nbe_stable fuel v d e' (eval_preserves_wf h_eval h_closed h_wf) h_quote

/-! ## Quote-eval correspondence for atoms -/

theorem quote_eval_sort (fuel : Nat) (u : L) (d : Nat) (hf : 0 < fuel) :
    eval_s fuel (.sort u : SExpr L) (fvarEnv d) = some (.sort u) := by
  cases fuel with
  | zero => omega
  | succ n => simp [eval_s]

theorem quote_eval_lit (fuel : Nat) (n d : Nat) (hf : 0 < fuel) :
    eval_s fuel (.lit n : SExpr L) (fvarEnv (L := L) d) = some (.lit n) := by
  cases fuel with
  | zero => omega
  | succ n => simp [eval_s]

theorem quote_eval_const (fuel : Nat) (c : Nat) (ls : List L) (d : Nat) (hf : 0 < fuel) :
    eval_s fuel (.const c ls : SExpr L) (fvarEnv d) = some (.neutral (.const c ls) []) := by
  cases fuel with
  | zero => omega
  | succ n => simp [eval_s]

theorem quote_eval_bvar (fuel : Nat) (i d : Nat) (h : i < d) (hf : 0 < fuel) :
    eval_s fuel (.bvar (levelToIndex d i) : SExpr L) (fvarEnv (L := L) d) =
    some (.neutral (.fvar i) []) := by
  cases fuel with
  | zero => omega
  | succ n =>
    simp [eval_s]
    rw [fvarEnv_get (by simp [levelToIndex]; omega)]
    congr 1
    simp [levelToIndex]
    omega

/-! ## Sanity checks -/

-- NbE stability: roundtrip for concrete values
-- sort roundtrips
#guard (do
  let v : SVal Nat := SVal.sort 1
  let e ← quote_s 20 v 0
  let v' ← eval_s 20 e (fvarEnv 0)
  return v.beq v') == some true

-- lit roundtrips
#guard (do
  let v : SVal Nat := SVal.lit 42
  let e ← quote_s 20 v 0
  let v' ← eval_s 20 e (fvarEnv 0)
  return v.beq v') == some true

-- neutral const roundtrips
#guard (do
  let v : SVal Nat := SVal.neutral (.const 5 []) []
  let e ← quote_s 20 v 0
  let v' ← eval_s 20 e (fvarEnv 0)
  return v.beq v') == some true

-- neutral fvar roundtrips (at depth 3, fvar level 1)
#guard (do
  let v : SVal Nat := SVal.neutral (.fvar 1) []
  let e ← quote_s 20 v 3
  let v' ← eval_s 20 e (fvarEnv 3)
  return v.beq v') == some true

-- lambda roundtrips (NbE stable, not value equal)
#guard (do
  let v : SVal Nat := SVal.lam (.sort 0) (.bvar 0) []
  let e ← quote_s 30 v 0
  let e' ← nbe_s 30 e (fvarEnv (L := Nat) 0) 0
  return e == e') == some true

-- NbE idempotence: nbe(nbe(e)) = nbe(e)
#guard (do
  let e : SExpr Nat := SExpr.app (.lam (.sort 0) (.bvar 0)) (.lit 5)
  let e' ← nbe_s 30 e [] 0
  let e'' ← nbe_s 30 e' (fvarEnv 0) 0
  return e' == e'') == some true

-- NbE idempotence: nested beta
#guard (do
  let e : SExpr Nat := SExpr.app (.app (.lam (.sort 0) (.lam (.sort 0) (.bvar 1))) (.lit 1)) (.lit 2)
  let e' ← nbe_s 40 e [] 0
  let e'' ← nbe_s 40 e' (fvarEnv 0) 0
  return e' == e'') == some true

end Ix.Theory
