/-
  Ix.Theory.NbESoundness: NbE Soundness Bridge.

  Connects the computational NbE specification (eval_s, quote_s) to the
  logical typing judgment (IsDefEq). Phase 5 of the formalization roadmap.

  Key results:
  - `IsDefEq.closedN`: well-typed terms are well-scoped
  - `IsDefEq.nbe_preservation`: conditional NbE type preservation

  Reference: docs/theory/kernel.md Part V (lines 498-563).
-/
import Ix.Theory.TypingLemmas
import Ix.Theory.Roundtrip
import Ix.Theory.EvalSubst

namespace Ix.Theory

open SExpr

/-! ## Lookup gives a bound on the index -/

theorem Lookup.lt_length : Lookup Γ i ty → i < Γ.length := by
  intro h
  induction h with
  | zero => exact Nat.zero_lt_succ _
  | succ _ ih => exact Nat.succ_lt_succ ih

/-! ## Context well-scopedness -/

/-- Each type in the context is well-scoped relative to its position.
    `CtxScoped [A₀, A₁, ..., A_{n-1}]` means `ClosedN A_j j` for each j
    (where position 0 is the most recently bound). -/
def CtxScoped : List TExpr → Prop
  | [] => True
  | A :: Γ => ClosedN A Γ.length ∧ CtxScoped Γ

theorem CtxScoped.tail : CtxScoped (A :: Γ) → CtxScoped Γ :=
  And.right

theorem CtxScoped.head : CtxScoped (A :: Γ) → ClosedN A Γ.length :=
  And.left

/-! ## Lookup preserves closedness -/

theorem Lookup.closedN (hl : Lookup Γ i ty) (hctx : CtxScoped Γ) :
    ClosedN ty Γ.length := by
  induction hl with
  | @zero A Γ₀ =>
    exact hctx.head.liftN
  | @succ Γ₀ n tyInner A _ ih =>
    exact (ih hctx.tail).liftN

/-! ## Well-scopedness from IsDefEq

    Well-typed terms are well-scoped. The context must also be well-scoped
    (CtxScoped), which is maintained through binder cases. -/

theorem IsDefEq.closedN
    {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt_closed : ∀ t i s sType k, ClosedN s k → ClosedN sType k →
      ClosedN (projType t i s sType) k)
    {Γ : List TExpr} {e₁ e₂ A : TExpr}
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A)
    (hctx : CtxScoped Γ) :
    ClosedN e₁ Γ.length ∧ ClosedN e₂ Γ.length ∧ ClosedN A Γ.length := by
  induction h with
  | bvar lookup =>
    exact ⟨lookup.lt_length, lookup.lt_length, lookup.closedN hctx⟩
  | symm _ ih =>
    have ⟨h2, h1, hA⟩ := ih hctx
    exact ⟨h1, h2, hA⟩
  | trans _ _ ih1 ih2 =>
    have ⟨h1, _, hA⟩ := ih1 hctx
    have ⟨_, h3, _⟩ := ih2 hctx
    exact ⟨h1, h3, hA⟩
  | sortDF hwf1 hwf2 _ =>
    simp [ClosedN]
  | constDF hc _ _ _ _ =>
    simp [ClosedN]
    exact ((henv.constClosed _ _ hc).instL _).mono (Nat.zero_le _)
  | appDF _ _ ih_f ih_a =>
    have ⟨hf, hf', hfA⟩ := ih_f hctx
    have ⟨ha, ha', _⟩ := ih_a hctx
    simp [ClosedN] at hfA
    exact ⟨⟨hf, ha⟩, ⟨hf', ha'⟩, hfA.2.inst ha⟩
  | lamDF _ _ ih_A ih_body =>
    have ⟨hA, hA', _⟩ := ih_A hctx
    have hctx' : CtxScoped (_ :: _) := ⟨hA, hctx⟩
    have ⟨hb, hb', hB⟩ := ih_body hctx'
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, ⟨hA, hB⟩⟩
  | forallEDF _ _ ih_A ih_body =>
    have ⟨hA, hA', _⟩ := ih_A hctx
    have hctx' : CtxScoped (_ :: _) := ⟨hA, hctx⟩
    have ⟨hb, hb', _⟩ := ih_body hctx'
    simp [ClosedN]
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩⟩
  | defeqDF _ _ ih1 ih2 =>
    have ⟨_, hB, _⟩ := ih1 hctx
    have ⟨he1, he2, _⟩ := ih2 hctx
    exact ⟨he1, he2, hB⟩
  | beta _ _ ih_body ih_arg =>
    have ⟨ha, _, hA⟩ := ih_arg hctx
    have hctx' : CtxScoped (_ :: _) := ⟨hA, hctx⟩
    have ⟨he, _, hB⟩ := ih_body hctx'
    exact ⟨⟨⟨hA, he⟩, ha⟩, he.inst ha, hB.inst ha⟩
  | eta _ ih =>
    have ⟨he, _, hfA⟩ := ih hctx
    have hfA' := hfA
    simp only [ClosedN] at hfA
    refine ⟨⟨hfA.1, ?_, ?_⟩, he, hfA'⟩
    · exact he.liftN
    · exact Nat.zero_lt_succ _
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    have ⟨hp, _, _⟩ := ih1 hctx
    have ⟨hh, _, _⟩ := ih2 hctx
    have ⟨hh', _, _⟩ := ih3 hctx
    exact ⟨hh, hh', hp⟩
  | extra hdf _ _ =>
    have ⟨hcl_l, hcl_r, hcl_t⟩ := henv.defeqClosed _ hdf
    exact ⟨(hcl_l.instL _).mono (Nat.zero_le _),
           (hcl_r.instL _).mono (Nat.zero_le _),
           (hcl_t.instL _).mono (Nat.zero_le _)⟩
  | letDF _ _ _ ih_ty ih_val ih_body =>
    have ⟨hty, hty', _⟩ := ih_ty hctx
    have ⟨hv, hv', _⟩ := ih_val hctx
    have hctx' : CtxScoped (_ :: _) := ⟨hty, hctx⟩
    have ⟨hb, hb', hB⟩ := ih_body hctx'
    exact ⟨⟨hty, hv, hb⟩, ⟨hty', hv', hb'⟩, hB.inst hv⟩
  | letZeta _ _ _ ih_ty ih_val ih_body =>
    have ⟨hty, _, _⟩ := ih_ty hctx
    have ⟨hv, _, _⟩ := ih_val hctx
    have hctx' : CtxScoped (_ :: _) := ⟨hty, hctx⟩
    have ⟨hb, _, hB⟩ := ih_body hctx'
    exact ⟨⟨hty, hv, hb⟩, hb.inst hv, hB.inst hv⟩
  | litDF =>
    simp [ClosedN]
    exact hlt.mono (Nat.zero_le _)
  | projDF _ ih =>
    have ⟨hs, _, hsT⟩ := ih hctx
    exact ⟨hs, hs, hpt_closed _ _ _ _ _ hs hsT⟩

/-! ## Definitions -/

/-- A value is well-typed: it's WF and quotes to a well-typed expression. -/
def ValTyped (env : SEnv) (uvars : Nat) (litType : TExpr)
    (projType : Nat → Nat → TExpr → TExpr → TExpr)
    (Γ : List TExpr) (v : SVal SLevel) (A : TExpr) (d : Nat) : Prop :=
  ValWF v d ∧ ∃ f e, quote_s f v d = some e ∧
    HasType env uvars litType projType Γ e A

/-- NbE property: IF eval and quote both succeed in fvarEnv,
    the quoted result is definitionally equal to the original at the same type. -/
def NbEProp (env : SEnv) (uvars : Nat) (litType : TExpr)
    (projType : Nat → Nat → TExpr → TExpr → TExpr)
    (Γ : List TExpr) (e A : TExpr) (d : Nat) : Prop :=
  ∀ f v fq e',
    eval_s f e (fvarEnv d) = some v →
    quote_s fq v d = some e' →
    IsDefEq env uvars litType projType Γ e e' A

/-! ## Easy cases of NbE preservation -/

-- Equation lemmas (for readability in proofs)
private theorem eval_s_bvar : eval_s (n+1) (.bvar idx : SExpr L) env = env[idx]? := rfl
private theorem eval_s_sort : eval_s (n+1) (.sort u : SExpr L) env = some (.sort u) := rfl
private theorem eval_s_const' : eval_s (n+1) (.const c ls : SExpr L) env =
    some (.neutral (.const c ls) []) := rfl
private theorem eval_s_lit : eval_s (n+1) (.lit l : SExpr L) env = some (.lit l) := rfl
private theorem eval_s_proj : eval_s (n+1) (.proj t i s : SExpr L) env = (none : Option (SVal L)) := rfl

private theorem eval_s_lam_eq : eval_s (n+1) (.lam dom body : SExpr L) env =
    ((eval_s n dom env).bind (fun vd => some (.lam vd body env))) := rfl

private theorem eval_s_forallE_eq : eval_s (n+1) (.forallE dom body : SExpr L) env =
    ((eval_s n dom env).bind (fun vd => some (.pi vd body env))) := rfl

private theorem eval_s_let_eq : eval_s (n+1) (.letE ty val body : SExpr L) env =
    ((eval_s n val env).bind (fun vv => eval_s n body (vv :: env))) := rfl

private theorem eval_s_app_eq : eval_s (n+1) (.app fn arg : SExpr L) env =
    ((eval_s n fn env).bind fun vf => (eval_s n arg env).bind fun va => apply_s n vf va) := rfl

private theorem apply_s_succ_neutral : apply_s (n+1) (.neutral hd spine : SVal L) arg =
    some (.neutral hd (spine ++ [arg])) := rfl
private theorem apply_s_succ_lam : apply_s (n+1) (.lam dom body fenv : SVal L) arg =
    eval_s n body (arg :: fenv) := rfl

private theorem quote_s_lam_eq {v_dom : SVal L} {body : SExpr L} {env : List (SVal L)} :
    quote_s (m+1) (SVal.lam v_dom body env) d =
    (do let domE ← quote_s m v_dom d
        let bodyV ← eval_s m body (SVal.neutral (.fvar d) [] :: env)
        let bodyE ← quote_s m bodyV (d + 1)
        some (.lam domE bodyE)) := by
  simp [quote_s]

private theorem quote_s_pi_eq {v_dom : SVal L} {body : SExpr L} {env : List (SVal L)} :
    quote_s (m+1) (SVal.pi v_dom body env) d =
    (do let domE ← quote_s m v_dom d
        let bodyV ← eval_s m body (SVal.neutral (.fvar d) [] :: env)
        let bodyE ← quote_s m bodyV (d + 1)
        some (.forallE domE bodyE)) := by
  simp [quote_s]

private theorem bind_eq_some {o : Option α} {f : α → Option β} {b : β}
    (h : o.bind f = some b) : ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => simp [Option.bind] at h
  | some a => exact ⟨a, rfl, h⟩

/-- Inverse of quoteSpine_snoc: if quoting spine ++ [v] succeeds,
    then quoting spine and quoting v both succeed separately. -/
private theorem quoteSpine_snoc_inv {f : Nat} {acc : SExpr L}
    {spine : List (SVal L)} {v : SVal L} {d : Nat} {e' : SExpr L}
    (h : quoteSpine_s f acc (spine ++ [v]) d = some e') :
    ∃ e1 ea, quoteSpine_s f acc spine d = some e1 ∧
             quote_s f v d = some ea ∧ e' = .app e1 ea := by
  induction spine generalizing acc with
  | nil =>
    simp only [List.nil_append] at h
    rw [quoteSpine_s.eq_2] at h
    obtain ⟨ea, hqa, hrest⟩ := bind_eq_some h
    rw [quoteSpine_s.eq_1] at hrest; cases hrest
    exact ⟨acc, ea, by rw [quoteSpine_s.eq_1], hqa, rfl⟩
  | cons a rest ih =>
    simp only [List.cons_append] at h
    rw [quoteSpine_s.eq_2] at h
    obtain ⟨aE, haE, hrest⟩ := bind_eq_some h
    obtain ⟨e1, ea, he1, hea, he'⟩ := ih hrest
    exact ⟨e1, ea, by rw [quoteSpine_s.eq_2, haE]; exact he1, hea, he'⟩

/-! ## NbE substitution — FALSE as stated

  The original `nbe_subst` claimed literal syntactic equality:
    quote(eval body (va :: fenv), d) = (quote(eval body (fvar(d) :: fenv), d+1)).inst(quote(va, d))
  This is FALSE because eval performs beta reduction but inst does not.

  **Counterexample**:
    body = .app (.bvar 0) (.sort 0)
    va = .lam (.sort 0) (.bvar 0) []  (identity function)
    fenv = [], d = 0

    Left side: eval body (va :: []) = apply va (.sort 0) = eval (.bvar 0) [.sort 0] = .sort 0
               quote (.sort 0) 0 = .sort 0
               e_result = .sort 0

    Right side: eval body (fvar(0) :: []) = apply fvar(0) (.sort 0) = neutral(fvar 0, [.sort 0])
                quote (neutral ..) 1 = .app (.bvar 0) (.sort 0)
                bodyE = .app (.bvar 0) (.sort 0)
                quote va 0 = .lam (.sort 0) (.bvar 0)
                ea = .lam (.sort 0) (.bvar 0)
                bodyE.inst ea = .app (.lam (.sort 0) (.bvar 0)) (.sort 0)

    Conclusion: .sort 0 ≠ .app (.lam (.sort 0) (.bvar 0)) (.sort 0)  — FALSE

  The correct relationship is QuoteEq (observational equivalence), not syntactic equality.
  Specifically, eval_inst_quoteEq at k=0 gives:
    QuoteEq (eval body (va :: fvarEnv d)) (eval (body.inst ea) (fvarEnv d)) d

  However, using this for the beta/let/eta cases of nbe_preservation requires
  relating NbE of (body.inst ea) to IsDefEq, which in turn needs NbE soundness
  for the substituted expression — creating a circularity that the current proof
  architecture (induction on IsDefEq) cannot handle.

  The correct approach requires a Kripke-style logical relation (semantic typing)
  that handles closures extensionally. See the plan for details. -/

-- nbe_subst is FALSE (see counterexample above). All 7 remaining sorries in this
-- file depend on it. The correct fix requires restructuring the proof to use a
-- logical relation instead of direct induction on IsDefEq for beta/let/eta.

/-- eval_s is deterministic modulo fuel: if both succeed, they give the same value. -/
theorem eval_s_det {e : SExpr L} {env : List (SVal L)} {v1 v2 : SVal L}
    (h1 : eval_s f1 e env = some v1) (h2 : eval_s f2 e env = some v2) :
    v1 = v2 := by
  have h1' := eval_fuel_mono h1 (Nat.le_max_left f1 f2)
  have h2' := eval_fuel_mono h2 (Nat.le_max_right f1 f2)
  rw [h1'] at h2'; exact Option.some.inj h2'

/-! ## Main theorem: conditional NbE preservation

    By induction on IsDefEq, if eval and quote succeed for either side,
    the result is definitionally equal to the original at the same type. -/

theorem IsDefEq.nbe_preservation
    {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt_closed : ∀ t i s sType k, ClosedN s k → ClosedN sType k →
      ClosedN (projType t i s sType) k)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    (hpt_inst : ∀ t i s sType a k,
      (projType t i s sType).inst a k =
      projType t i (s.inst a k) (sType.inst a k))
    (hextra_nf : ∀ df (ls : List SLevel) d, env.defeqs df →
      (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
      (∀ f v fq (e' : TExpr), eval_s f (df.lhs.instL ls) (fvarEnv d) = some v →
        quote_s fq v d = some e' → e' = df.lhs.instL ls) ∧
      (∀ f v fq (e' : TExpr), eval_s f (df.rhs.instL ls) (fvarEnv d) = some v →
        quote_s fq v d = some e' → e' = df.rhs.instL ls))
    {Γ : List TExpr} {e₁ e₂ A : TExpr}
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A)
    (hctx : CtxScoped Γ)
    {d : Nat} (hd : d = Γ.length) :
    NbEProp env uvars litType projType Γ e₁ A d ∧
    NbEProp env uvars litType projType Γ e₂ A d := by
  subst hd
  induction h with
  | @bvar Γ₀ i _ lookup =>
    -- eval (.bvar i) (fvarEnv d) = fvar(d-1-i), quote = .bvar i
    constructor <;> (intro f v fq e' hev hq; cases f with
    | zero => simp [eval_s] at hev
    | succ n =>
      rw [eval_s_bvar] at hev
      rw [fvarEnv_get (lookup.lt_length)] at hev
      cases hev
      cases fq with
      | zero => simp [quote_s] at hq
      | succ m =>
        simp [quote_s, quoteSpine_s, quoteHead, levelToIndex] at hq
        cases hq
        have hi := lookup.lt_length
        have : Γ₀.length - 1 - (Γ₀.length - 1 - i) = i := by omega
        rw [this]
        exact .bvar lookup)
  | symm _ ih =>
    have ⟨l, r⟩ := ih hctx
    exact ⟨r, l⟩
  | trans _ _ ih1 ih2 =>
    exact ⟨(ih1 hctx).1, (ih2 hctx).2⟩
  | sortDF hwf1 hwf2 heq =>
    constructor
    · intro f v fq e' hev hq; cases f with
      | zero => simp [eval_s] at hev
      | succ n =>
        rw [eval_s_sort] at hev; cases hev
        cases fq with
        | zero => simp [quote_s] at hq
        | succ m =>
          simp [quote_s] at hq; cases hq
          exact .trans (.sortDF hwf1 hwf2 heq) (.symm (.sortDF hwf1 hwf2 heq))
    · intro f v fq e' hev hq; cases f with
      | zero => simp [eval_s] at hev
      | succ n =>
        rw [eval_s_sort] at hev; cases hev
        cases fq with
        | zero => simp [quote_s] at hq
        | succ m =>
          simp [quote_s] at hq; cases hq
          exact .trans (.symm (.sortDF hwf1 hwf2 heq)) (.sortDF hwf1 hwf2 heq)
  | constDF hc hwf hwf' hlen heq =>
    constructor
    · intro f v fq e' hev hq; cases f with
      | zero => simp [eval_s] at hev
      | succ n =>
        rw [eval_s_const'] at hev; cases hev
        cases fq with
        | zero => simp [quote_s] at hq
        | succ m =>
          simp [quote_s, quoteSpine_s, quoteHead] at hq; cases hq
          exact .trans (.constDF hc hwf hwf' hlen heq) (.symm (.constDF hc hwf hwf' hlen heq))
    · intro f v fq e' hev hq; cases f with
      | zero => simp [eval_s] at hev
      | succ n =>
        rw [eval_s_const'] at hev; cases hev
        cases fq with
        | zero => simp [quote_s] at hq
        | succ m =>
          simp [quote_s, quoteSpine_s, quoteHead] at hq; cases hq
          exact .trans (.symm (.constDF hc hwf hwf' hlen heq)) (.constDF hc hwf hwf' hlen heq)
  | litDF =>
    constructor <;> (intro f v fq e' hev hq; cases f with
    | zero => simp [eval_s] at hev
    | succ n =>
      rw [eval_s_lit] at hev; cases hev
      cases fq with
      | zero => simp [quote_s] at hq
      | succ m =>
        simp [quote_s] at hq; cases hq
        exact .litDF)
  | projDF _ _ =>
    -- eval returns none for proj, so NbEProp is vacuously true
    constructor <;> (intro f v fq e' hev hq; cases f with
    | zero => simp [eval_s] at hev
    | succ n => rw [eval_s_proj] at hev; exact absurd hev nofun)
  | defeqDF h_AB h_e ih_AB ih_e =>
    have ⟨ih_e1, ih_e2⟩ := ih_e hctx
    constructor <;> intro f v fq e' hev hq
    · exact .defeqDF h_AB (ih_e1 f v fq e' hev hq)
    · exact .defeqDF h_AB (ih_e2 f v fq e' hev hq)
  | proofIrrel h_p h_h h_h' ih_p ih_h ih_h' =>
    exact ⟨(ih_h hctx).1, (ih_h' hctx).1⟩
  | extra hdf hwf hlen =>
    constructor
    · intro f v fq e' hev hq
      rw [(hextra_nf _ _ _ hdf hwf hlen).1 f v fq e' hev hq]
      exact .trans (.extra hdf hwf hlen) (.symm (.extra hdf hwf hlen))
    · intro f v fq e' hev hq
      rw [(hextra_nf _ _ _ hdf hwf hlen).2 f v fq e' hev hq]
      exact .trans (.symm (.extra hdf hwf hlen)) (.extra hdf hwf hlen)
  | appDF h_f h_a ih_f ih_a =>
    have ⟨nbF, nbF'⟩ := ih_f hctx
    have ⟨nbA, nbA'⟩ := ih_a hctx
    constructor
    · -- Left: NbEProp for (.app f a) at type (B.inst a)
      intro f_fuel v fq e' hev hq
      cases f_fuel with
      | zero => simp [eval_s] at hev
      | succ n =>
        rw [eval_s_app_eq] at hev
        obtain ⟨vf, hevF, hevRest⟩ := bind_eq_some hev
        obtain ⟨va, hevA, happ⟩ := bind_eq_some hevRest
        cases n with
        | zero => simp [eval_s] at hevF
        | succ n' =>
          cases vf with
          | neutral hd spine =>
            rw [apply_s_succ_neutral] at happ; cases happ
            cases fq with
            | zero => simp [quote_s] at hq
            | succ fq' =>
              rw [quote_s.eq_6] at hq
              obtain ⟨e1, ea, hqF, hqA, he'⟩ := quoteSpine_snoc_inv hq
              subst he'
              exact .appDF
                (nbF _ _ _ _ hevF (by rw [quote_s.eq_6]; exact hqF))
                (nbA _ _ _ _ hevA hqA)
          | lam dom body fenv =>
            -- apply_s (.lam ..) va = eval body (va :: fenv)
            -- Needs nbe_subst + quotable_of_wf to quote .lam value and
            -- get bodyE/ea, then IsDefEq.substitution + beta + type conversion.
            sorry
          | sort _ => exact absurd happ nofun
          | lit _ => exact absurd happ nofun
          | pi _ _ _ => exact absurd happ nofun
    · -- Right: NbEProp for (.app f' a') at type (B.inst a)
      intro f_fuel v fq e' hev hq
      cases f_fuel with
      | zero => simp [eval_s] at hev
      | succ n =>
        rw [eval_s_app_eq] at hev
        obtain ⟨vf, hevF, hevRest⟩ := bind_eq_some hev
        obtain ⟨va, hevA, happ⟩ := bind_eq_some hevRest
        cases n with
        | zero => simp [eval_s] at hevF
        | succ n' =>
          cases vf with
          | neutral hd spine =>
            rw [apply_s_succ_neutral] at happ; cases happ
            cases fq with
            | zero => simp [quote_s] at hq
            | succ fq' =>
              rw [quote_s.eq_6] at hq
              obtain ⟨e1, ea, hqF, hqA, he'⟩ := quoteSpine_snoc_inv hq
              subst he'
              exact .trans (.symm (.appDF h_f h_a))
                (.appDF (.trans h_f (nbF' _ _ _ _ hevF (by rw [quote_s.eq_6]; exact hqF)))
                        (.trans h_a (nbA' _ _ _ _ hevA hqA)))
          | lam dom body fenv =>
            -- Same as left lambda case
            sorry
          | sort _ => exact absurd happ nofun
          | lit _ => exact absurd happ nofun
          | pi _ _ _ => exact absurd happ nofun
  | lamDF h_A h_body ih_A ih_body =>
    have hA_cl := (h_A.closedN henv hlt hpt_closed hctx).1
    have hctx' : CtxScoped (_ :: _) := ⟨hA_cl, hctx⟩
    have ⟨nbA, nbA'⟩ := ih_A hctx
    have ⟨nbBody, nbBody'⟩ := ih_body hctx'
    constructor
    · intro f v fq e' hev hq
      cases f with | zero => simp [eval_s] at hev | succ n =>
      rw [eval_s_lam_eq] at hev
      obtain ⟨vA, hevA, hev'⟩ := bind_eq_some hev
      cases hev'
      cases fq with | zero => simp [quote_s] at hq | succ m =>
      rw [quote_s_lam_eq] at hq
      obtain ⟨domE, hqD, hq'⟩ := bind_eq_some hq
      obtain ⟨vBody, hevB, hq''⟩ := bind_eq_some hq'
      obtain ⟨bodyE, hqB, hq'''⟩ := bind_eq_some hq''
      cases hq'''
      rw [fvarEnv_succ] at hevB
      exact .lamDF (nbA n vA m domE hevA hqD) (nbBody m vBody m bodyE hevB hqB)
    · intro f v fq e' hev hq
      cases f with | zero => simp [eval_s] at hev | succ n =>
      rw [eval_s_lam_eq] at hev
      obtain ⟨vA', hevA', hev'⟩ := bind_eq_some hev
      cases hev'
      cases fq with | zero => simp [quote_s] at hq | succ m =>
      rw [quote_s_lam_eq] at hq
      obtain ⟨domE', hqD', hq'⟩ := bind_eq_some hq
      obtain ⟨vBody', hevB', hq''⟩ := bind_eq_some hq'
      obtain ⟨bodyE', hqB', hq'''⟩ := bind_eq_some hq''
      cases hq'''
      rw [fvarEnv_succ] at hevB'
      exact .trans (.symm (.lamDF h_A h_body))
        (.lamDF (.trans h_A (nbA' n vA' m domE' hevA' hqD'))
                (.trans h_body (nbBody' m vBody' m bodyE' hevB' hqB')))
  | forallEDF h_A h_body ih_A ih_body =>
    have hA_cl := (h_A.closedN henv hlt hpt_closed hctx).1
    have hctx' : CtxScoped (_ :: _) := ⟨hA_cl, hctx⟩
    have ⟨nbA, nbA'⟩ := ih_A hctx
    have ⟨nbBody, nbBody'⟩ := ih_body hctx'
    constructor
    · intro f v fq e' hev hq
      cases f with | zero => simp [eval_s] at hev | succ n =>
      rw [eval_s_forallE_eq] at hev
      obtain ⟨vA, hevA, hev'⟩ := bind_eq_some hev
      cases hev'
      cases fq with | zero => simp [quote_s] at hq | succ m =>
      rw [quote_s_pi_eq] at hq
      obtain ⟨domE, hqD, hq'⟩ := bind_eq_some hq
      obtain ⟨vBody, hevB, hq''⟩ := bind_eq_some hq'
      obtain ⟨bodyE, hqB, hq'''⟩ := bind_eq_some hq''
      cases hq'''
      rw [fvarEnv_succ] at hevB
      exact .forallEDF (nbA n vA m domE hevA hqD) (nbBody m vBody m bodyE hevB hqB)
    · intro f v fq e' hev hq
      cases f with | zero => simp [eval_s] at hev | succ n =>
      rw [eval_s_forallE_eq] at hev
      obtain ⟨vA', hevA', hev'⟩ := bind_eq_some hev
      cases hev'
      cases fq with | zero => simp [quote_s] at hq | succ m =>
      rw [quote_s_pi_eq] at hq
      obtain ⟨domE', hqD', hq'⟩ := bind_eq_some hq
      obtain ⟨vBody', hevB', hq''⟩ := bind_eq_some hq'
      obtain ⟨bodyE', hqB', hq'''⟩ := bind_eq_some hq''
      cases hq'''
      rw [fvarEnv_succ] at hevB'
      exact .trans (.symm (.forallEDF h_A h_body))
        (.forallEDF (.trans h_A (nbA' n vA' m domE' hevA' hqD'))
                    (.trans h_body (nbBody' m vBody' m bodyE' hevB' hqB')))
  | beta h_body h_arg ih_body ih_arg =>
    -- Goal: NbEProp (.app (.lam A e) e') (B.inst e') d
    --     ∧ NbEProp (e.inst e') (B.inst e') d
    -- h_body : IsDefEq (A::Γ) e e B,  h_arg : IsDefEq Γ e' e' A
    -- Key ingredients available:
    -- 1. ih_body → NbEProp e B (d+1) (body normalizes in fvarEnv(d+1))
    -- 2. ih_arg → NbEProp e' A d (arg normalizes in fvarEnv d)
    -- 3. nbe_subst: eval e (va :: fvarEnv d) quotes to bodyE.inst ea
    -- 4. IsDefEq.substitution: e ≡ bodyE : B → (e.inst e') ≡ (bodyE.inst e') : B.inst e'
    -- 5. beta rule: (.app (.lam A e) e') ≡ (e.inst e') : B.inst e'
    -- Blocked on: connecting nbe_subst output to substitution congruence
    -- (requires type conversion between B.inst e' and B.inst ea).
    sorry
  | eta h_e ih_e =>
    constructor
    · -- eval (.lam A (.app e.lift (.bvar 0))) opens with fvar(d), evals e.lift in
      -- fvar(d) :: fvarEnv d, then applies to fvar(d). Needs eval_lift_quoteEq:
      -- eval(e.lift, v :: env) QuoteEq eval(e, env). Blocked on SimVal.
      sorry
    · -- Right: NbEProp for e — directly from IH
      exact (ih_e hctx).1
  | letDF h_ty h_val h_body ih_ty ih_val ih_body =>
    -- eval (.letE ty val body) = eval body (eval val :: fvarEnv d).
    -- Same structure as beta: ih_body gives NbEProp for body in fvarEnv(d+1),
    -- nbe_subst + IsDefEq.substitution bridge to the goal.
    sorry
  | letZeta h_ty h_val h_body ih_ty ih_val ih_body =>
    -- Left: same as letDF. Right: NbEProp for body.inst val at B.inst val.
    -- Uses eval_inst_quoteEq + nbe_subst + IsDefEq.substitution.
    sorry

/-! ## Corollaries -/

/-- NbE type preservation: if a well-typed term evaluates and quotes,
    the result is definitionally equal to the original. -/
theorem nbe_type_preservation
    {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt_closed : ∀ t i s sType k, ClosedN s k → ClosedN sType k →
      ClosedN (projType t i s sType) k)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    (hpt_inst : ∀ t i s sType a k,
      (projType t i s sType).inst a k =
      projType t i (s.inst a k) (sType.inst a k))
    (hextra_nf : ∀ df (ls : List SLevel) d, env.defeqs df →
      (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
      (∀ f v fq (e' : TExpr), eval_s f (df.lhs.instL ls) (fvarEnv d) = some v →
        quote_s fq v d = some e' → e' = df.lhs.instL ls) ∧
      (∀ f v fq (e' : TExpr), eval_s f (df.rhs.instL ls) (fvarEnv d) = some v →
        quote_s fq v d = some e' → e' = df.rhs.instL ls))
    {Γ : List TExpr} {e A : TExpr}
    (h : HasType env uvars litType projType Γ e A)
    (hctx : CtxScoped Γ)
    {d : Nat} (hd : d = Γ.length)
    {f : Nat} {e' : TExpr}
    (hnbe : nbe_s f e (fvarEnv d) d = some e') :
    IsDefEq env uvars litType projType Γ e e' A := by
  simp only [nbe_s, bind, Option.bind] at hnbe
  cases hev : eval_s f e (fvarEnv d) with
  | none => simp [hev] at hnbe
  | some v =>
    simp [hev] at hnbe
    exact (h.nbe_preservation henv hlt hpt_closed hpt hpt_inst hextra_nf hctx hd).1
      f v f e' hev hnbe

end Ix.Theory
