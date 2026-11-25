import IxCC.Src.Proof.Unfold
import IxCCCorrect.Progress

/-!
# Progress by shapes, first instance (`IxCCCorrect.Shape`)

The first program class for which the `GoesWrong` disjunct of the compiler's
theorems is discharged, and the check of the invariant `plans/PROGRESS.md`
recommends for the rest: a **syntactic typing of SrcEval's values by shapes**, proved
sound by induction on the clock and then on the term.

The class (milestone M0, "branch-free `Nat` arithmetic with closures"): every constant
the root reaches is a λ-term over `Nat` literals, variables, relevant applications in
either mode, relevant `let`s, the `Nat`-valued primitives of the table, and other such
constants through their definition, their equation hint or a `csimp` entry, recursion
included. Functions are first class: closures, partial applications of primitives and
by-name thunks all occur. There is no data, no `case`, no irrelevant position.

* `Shape`: `nat`, or a function shape.
* `HasShape sig Γ t σ`: the term judgment, over a shape for each constant (`sig`).
* `ValOk`, `SlotOk`, `EnvOk`: the value judgment. A closure is typed **by its code**:
  its body has a shape in a context its captured environment satisfies. A thunk
  likewise. A partial application of a primitive is typed by the arguments it lacks.
* `SigOk p sig`: every constant with a shape resolves in `p` as its shape says.
* `allOk`: at every clock, each of SrcEval's functions on shaped inputs times out or
  returns a shaped value. In particular it is neither stuck nor a trap.
* `synth`, `sigCheck`: the decision. `synth_sound`, `sigOk_of_check`: it decides the
  judgments, from an untrusted certificate that lists a shape per constant.
* `neverWrong_of_shape`, `neverWrong_of_check`: `NeverWrong` of the front half's
  source at a `Nat` root, from the judgments and from the decision, and
  `recheck_sound_of_shape`: `Recheck.sound` for such a program with no disjunct.

**Why the invariant is syntactic.** SrcEval's clock is a depth bound: a value computed
at depth `k` (the body of a β or δ step taken at depth `k + 1`) is returned to depth
`k + 1` and may be applied there, which runs its body at depth `k` again. So no index
can be attached to "this closure is safe to apply": a relation indexed by the clock
is not closed under β (`plans/PROGRESS.md`, 2.3 gives the calculation), and an
unindexed semantic relation cannot be established for a closure by induction on the
clock, since it quantifies over every clock. Typing a closure by its code avoids both:
the induction hypothesis at a smaller clock applies to every shaped term, not only to
subterms, so it applies to the body of whatever closure arrives.

No model of the environment and no fact about the kernel is used. The module imports
the compiler only; it sits in this library because the statement it discharges does.
-/

set_option autoImplicit false

namespace IxCC.Correct.Shape

open IxCC.Src
open IxCC.Sem (Result Lang later later_zero later_succ)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-! ## Shapes and the term judgment -/

/-- The shape of a value: a `Nat`, or a function. -/
inductive Shape where
  | nat
  | fn (dom cod : Shape)
  deriving DecidableEq, Repr

/-- `Nat → … → Nat → Nat`, with `n` arguments. -/
def Shape.nats : Nat → Shape
  | 0 => .nat
  | n + 1 => .fn .nat (Shape.nats n)

/-- **The term judgment.** Every position is relevant (`Rel.rel`) and every λ is one
that is never a proof (`propWhen = never`, the A1 guard), so no clause depends on the
levels SrcEval carries. -/
inductive HasShape (sig : CId → Option Shape) : List Shape → Term → Shape → Prop
  | var {Γ : List Shape} {i : Nat} {σ : Shape} :
      Γ[i]? = some σ → HasShape sig Γ (.var i) σ
  | natLit {Γ : List Shape} {n : Nat} : HasShape sig Γ (.natLit n) .nat
  | const {Γ : List Shape} {c : CId} {us : List Ixon.Univ} {σ : Shape} :
      sig c = some σ → HasShape sig Γ (.const c us) σ
  | lam {Γ : List Shape} {b : Binder} {d body : Term} {σ τ : Shape} :
      b.propWhen = .never → HasShape sig (σ :: Γ) body τ →
      HasShape sig Γ (.lam b d body) (.fn σ τ)
  | app {Γ : List Shape} {f a : Term} {m : Mode} {σ τ : Shape} :
      HasShape sig Γ f (.fn σ τ) → HasShape sig Γ a σ → HasShape sig Γ (.app f a m .rel) τ
  | letE {Γ : List Shape} {nonDep : Bool} {lm : Ixon.V3.LetMode} {ty v body : Term}
      {σ τ : Shape} :
      HasShape sig Γ v σ → HasShape sig (σ :: Γ) body τ →
      HasShape sig Γ (.letE nonDep lm .rel ty v body) τ

/-! ## The value judgment -/

mutual

/-- **A value has a shape.** -/
inductive ValOk (sig : CId → Option Shape) : Value → Shape → Prop
  | lit {n : Nat} : ValOk sig (.lit n) .nat
  /-- a closure, by its code: the body has a shape in a context the captured
  environment satisfies -/
  | clo {b : Binder} {d body : Term} {ρ : List Slot} {ls : Levels} {Γ : List Shape}
      {σ τ : Shape} :
      b.propWhen = .never → EnvOk sig ρ Γ → HasShape sig (σ :: Γ) body τ →
      ValOk sig (.clo b d body ρ ls) (.fn σ τ)
  /-- a partial application of a `Nat`-valued primitive, by the arguments it lacks -/
  | pap (op : PrimOp) (ls : Levels) (args : List Slot) (τ : Shape) :
      op.isPredicate = false → (∀ s, s ∈ args → SlotOk sig s .nat) →
      args.length < op.arity → τ = Shape.nats (op.arity - args.length) →
      ValOk sig (.pap (.prim op) ls args) τ

/-- **A slot has a shape**: a value's, or a thunk's by its code. -/
inductive SlotOk (sig : CId → Option Shape) : Slot → Shape → Prop
  | val {v : Value} {σ : Shape} : ValOk sig v σ → SlotOk sig (.val v) σ
  | name {t : Term} {ρ : List Slot} {ls : Levels} {Γ : List Shape} {σ : Shape} :
      EnvOk sig ρ Γ → HasShape sig Γ t σ → SlotOk sig (.name t ρ ls) σ

/-- **An environment satisfies a context**, slot by slot. -/
inductive EnvOk (sig : CId → Option Shape) : List Slot → List Shape → Prop
  | nil : EnvOk sig [] []
  | cons {s : Slot} {ρ : List Slot} {σ : Shape} {Γ : List Shape} :
      SlotOk sig s σ → EnvOk sig ρ Γ → EnvOk sig (s :: ρ) (σ :: Γ)

end

/-- An outcome is a timeout or a value of the shape: not stuck, not a trap, not a
resource failure (SrcEval has none). -/
def ResOk (sig : CId → Option Shape) (σ : Shape) (r : Result Value) : Prop :=
  r = .timeout ∨ ∃ v, r = .ok v ∧ ValOk sig v σ

/-- **The program resolves every shaped constant as its shape says**: a `Nat`-valued
primitive of the table at its arity; an equation hint or a definition whose body has
the shape; a `csimp` entry whose target has it. -/
structure SigOk (p : Program) (sig : CId → Option Shape) : Prop where
  const : ∀ c σ, sig c = some σ →
    (∃ op, p.table.resolveOf c = some (.prim op) ∧ op.isPredicate = false ∧
      σ = Shape.nats op.arity) ∨
    (∃ thm body, p.table.resolveOf c = some (.eqn thm body) ∧ HasShape sig [] body σ) ∨
    (∃ g us thm, p.table.resolveOf c = some (.csimp g us thm) ∧ sig g = some σ) ∨
    (∃ lvls ty v, p.table.resolveOf c = none ∧
      p.decl? c = some (.defn .defn .safe lvls ty v) ∧ HasShape sig [] v σ)

/-! ## Small facts -/

theorem arity_cases (op : PrimOp) : op.arity = 1 ∨ op.arity = 2 := by
  cases op <;> decide

theorem headArity_prim (p : Program) (op : PrimOp) : p.headArity (.prim op) = op.arity := rfl

/-- A `Nat`-valued primitive's value on two numbers is a number. -/
theorem eval2_nat {op : PrimOp} (hp : op.isPredicate = false) (a b : Nat) :
    ∃ n, op.eval2 a b = .nat n := by
  cases op <;> first | exact ⟨_, rfl⟩ | cases hp

/-- A primitive applied to as many literals as its arity computes. -/
theorem evalLits_of_length {op : PrimOp} {ns : List Nat} (hl : ns.length = op.arity) :
    ∃ a b, op.evalLits ns = some (op.eval2 a b) := by
  rcases arity_cases op with h | h
  · rw [h] at hl
    match ns, hl with
    | [], hl => exact absurd hl (by decide)
    | [a], _ => exact ⟨a, 0, by simp [PrimOp.evalLits, h]⟩
    | _ :: _ :: rest, hl =>
      simp only [List.length_cons] at hl
      omega
  · rw [h] at hl
    match ns, hl with
    | [], hl => exact absurd hl (by decide)
    | [_], hl => exact absurd hl (by simp)
    | [a, b], _ => exact ⟨a, b, by simp [PrimOp.evalLits, h]⟩
    | _ :: _ :: _ :: rest, hl =>
      simp only [List.length_cons] at hl
      omega

theorem litArgs_map_lit : ∀ ns : List Nat, litArgs (ns.map Value.lit) = some ns
  | [] => rfl
  | n :: ns => by
    show (litArgs (ns.map Value.lit)).map (n :: ·) = some (n :: ns)
    rw [litArgs_map_lit ns]
    rfl

/-- F6 on literals, at a `Nat`-valued primitive's arity, returns a literal. -/
theorem primValue_lits (p : Program) {op : PrimOp} {ns : List Nat}
    (hp : op.isPredicate = false) (hl : ns.length = op.arity) :
    ∃ n, primValue p op (ns.map Value.lit) = .ok (.lit n) := by
  obtain ⟨a, b, he⟩ := evalLits_of_length hl
  obtain ⟨n, hn⟩ := eval2_nat hp a b
  refine ⟨n, ?_⟩
  simp only [primValue, litArgs_map_lit, he, hn]

/-- E7 at a relevant strict argument. -/
theorem eval_app_strict (p : Program) (k : Nat) (ls : Levels) (ρ : Env) (f a : Term) :
    eval p k ls ρ (.app f a .strict .rel) =
      (eval p k ls ρ f).bind fun fv => (eval p k ls ρ a).bind fun x => apply p k fv (.val x) := by
  rw [eval_app]
  rfl

/-- E7 at a relevant by-name argument. -/
theorem eval_app_byName (p : Program) (k : Nat) (ls : Levels) (ρ : Env) (f a : Term) :
    eval p k ls ρ (.app f a .byName .rel) =
      (eval p k ls ρ f).bind fun fv => apply p k fv (.name a ρ ls) := by
  rw [eval_app]
  rfl

/-- E5 at a relevant `let`. -/
theorem eval_letE_rel (p : Program) (k : Nat) (ls : Levels) (ρ : Env) (nonDep : Bool)
    (lm : Ixon.V3.LetMode) (ty v body : Term) :
    eval p k ls ρ (.letE nonDep lm .rel ty v body) =
      (eval p k ls ρ v).bind fun x => eval p k ls (.val x :: ρ) body := by
  rw [eval_letE]
  rfl

/-- A1's guard at a λ that is never a proof. -/
theorem apply_clo_never (p : Program) (k : Nat) (b : Binder) (d body : Term) (ρ : Env)
    (ls : Levels) (s : Slot) (hb : b.propWhen = .never) :
    apply p k (.clo b d body ρ ls) s = later k fun k => eval p k ls (s :: ρ) body := by
  rw [apply_clo, hb]
  rfl

/-! ## Canonical forms, by inversion of the value judgment -/

variable {sig : CId → Option Shape}

/-- **Canonical forms at `nat`**: a value of shape `nat` is a literal. -/
theorem ValOk.nat_inv {v : Value} (h : ValOk sig v .nat) : ∃ n, v = .lit n := by
  cases h with
  | lit => exact ⟨_, rfl⟩
  | pap op ls args τ hp ha hlt hτ =>
    obtain ⟨j, hj⟩ : ∃ j, op.arity - args.length = j + 1 :=
      ⟨op.arity - args.length - 1, by omega⟩
    rw [hj] at hτ
    simp [Shape.nats] at hτ

/-- An environment that satisfies a context has a slot of each variable's shape. -/
theorem EnvOk.get : ∀ (ρ : List Slot) (Γ : List Shape), EnvOk sig ρ Γ → ∀ (i : Nat) (σ : Shape),
    Γ[i]? = some σ → ∃ s, ρ[i]? = some s ∧ SlotOk sig s σ
  | [], _, h, i, σ, hi => by
    cases h
    simp at hi
  | s :: ρ, _, h, i, σ, hi => by
    cases h with
    | cons hs hρ =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨s, List.getElem?_cons_zero, hs⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi ⊢
        exact EnvOk.get ρ _ hρ i σ hi

/-- Forcing slots of shape `nat` times out or returns literals. -/
theorem forceAll_nat {p : Program} {k : Nat}
    (hslot : ∀ (s : Slot) (σ : Shape), SlotOk sig s σ → ResOk sig σ (force p k s)) :
    ∀ ss : List Slot, (∀ s, s ∈ ss → SlotOk sig s .nat) →
      forceAll p k ss = .timeout ∨
        ∃ ns : List Nat, forceAll p k ss = .ok (ns.map Value.lit) ∧ ns.length = ss.length
  | [], _ => .inr ⟨[], forceAll_nil p k, rfl⟩
  | s :: ss, h => by
    rw [forceAll_cons]
    rcases hslot s .nat (h s (List.mem_cons.2 (.inl rfl))) with hs | ⟨v, hs, hv⟩
    · rw [hs]
      exact .inl rfl
    · obtain ⟨n, rfl⟩ := hv.nat_inv
      rw [hs]
      rcases forceAll_nat hslot ss (fun s' hs' => h s' (List.mem_cons.2 (.inr hs'))) with
        ht | ⟨ns, hns, hnl⟩
      · rw [ht]
        exact .inl rfl
      · rw [hns]
        exact .inr ⟨n :: ns, rfl, by simp [hnl]⟩

/-! ## Soundness -/

/-- **Shape soundness at clock `k`**, for the four of SrcEval's functions the fragment
reaches through shaped inputs. -/
structure AllOk (p : Program) (sig : CId → Option Shape) (k : Nat) : Prop where
  term : ∀ (ls : Levels) (ρ : Env) (Γ : List Shape) (t : Term) (σ : Shape),
    HasShape sig Γ t σ → EnvOk sig ρ Γ → ResOk sig σ (eval p k ls ρ t)
  const : ∀ (ls : Levels) (c : CId) (σ : Shape), sig c = some σ →
    ResOk sig σ (evalConst p k ls c)
  app : ∀ (f : Value) (s : Slot) (σ τ : Shape), ValOk sig f (.fn σ τ) → SlotOk sig s σ →
    ResOk sig τ (apply p k f s)
  slot : ∀ (s : Slot) (σ : Shape), SlotOk sig s σ → ResOk sig σ (force p k s)

/-- **Shape soundness**: on a program that resolves its shaped constants as their
shapes say, at every clock, evaluation of a shaped term in a shaped environment, δ of a
shaped constant, application of a function-shaped value to a slot of its domain, and a
force of a shaped slot each time out or return a value of the shape. By strong
induction on the clock (every charge goes one down, and the hypothesis there covers
every shaped term), then on the term judgment. -/
theorem allOk {p : Program} (hsig : SigOk p sig) : ∀ k, AllOk p sig k := by
  intro k
  refine Nat.strongRecOn k fun k ih => ?_
  -- E1's force and a forced thunk
  have hslot : ∀ (s : Slot) (σ : Shape), SlotOk sig s σ → ResOk sig σ (force p k s) := by
    intro s σ hs
    cases hs with
    | val hv =>
      rw [force_val]
      exact .inr ⟨_, rfl, hv⟩
    | name hρ ht =>
      rw [force_name]
      cases k with
      | zero => exact .inl rfl
      | succ k => exact (ih k (Nat.lt_succ_self k)).term _ _ _ _ _ ht hρ
  -- E8 (δ)
  have hconst : ∀ (ls : Levels) (c : CId) (σ : Shape), sig c = some σ →
      ResOk sig σ (evalConst p k ls c) := by
    intro ls c σ hc
    rw [evalConst_eq]
    rcases hsig.const c σ hc with ⟨op, hres, hpred, rfl⟩ | ⟨thm, body, hres, hbody⟩ |
      ⟨g, us, thm, hres, hg⟩ | ⟨lvls, ty, v, hres, hdecl, hv⟩
    · rw [hres]
      show ResOk sig _ (headValue p k ls (.prim op))
      rw [headValue_eq, headArity_prim]
      have h0 : (op.arity == 0) = false := by
        rcases arity_cases op with h | h <;> rw [h] <;> rfl
      rw [h0]
      refine .inr ⟨_, rfl, .pap op ls [] _ hpred (fun s hs => by cases hs) ?_ rfl⟩
      rcases arity_cases op with h | h <;> rw [h] <;> decide
    · rw [hres]
      show ResOk sig σ (later k fun k => eval p k ls [] body)
      cases k with
      | zero => exact .inl rfl
      | succ k => exact (ih k (Nat.lt_succ_self k)).term _ _ _ _ _ hbody .nil
    · rw [hres]
      show ResOk sig σ (later k fun k => eval p k ls [] (.const g us))
      cases k with
      | zero => exact .inl rfl
      | succ k =>
        show ResOk sig σ (eval p k ls [] (.const g us))
        rw [eval_const]
        exact (ih k (Nat.lt_succ_self k)).const _ _ _ hg
    · rw [hres, hdecl]
      show ResOk sig σ (later k fun k => eval p k ls [] v)
      cases k with
      | zero => exact .inl rfl
      | succ k => exact (ih k (Nat.lt_succ_self k)).term _ _ _ _ _ hv .nil
  -- A1, A2 and F6
  have happ : ∀ (f : Value) (s : Slot) (σ τ : Shape), ValOk sig f (.fn σ τ) → SlotOk sig s σ →
      ResOk sig τ (apply p k f s) := by
    intro f s σ τ hf hs
    cases hf with
    | clo hb hρ hbody =>
      rw [apply_clo_never p k _ _ _ _ _ _ hb]
      cases k with
      | zero => exact .inl rfl
      | succ k => exact (ih k (Nat.lt_succ_self k)).term _ _ _ _ _ hbody (.cons hs hρ)
    | pap op ls' args τ' hp ha hlt hτ =>
      obtain ⟨j, hj⟩ : ∃ j, op.arity - args.length = j + 1 :=
        ⟨op.arity - args.length - 1, by omega⟩
      rw [hj] at hτ
      simp only [Shape.nats, Shape.fn.injEq] at hτ
      obtain ⟨rfl, rfl⟩ := hτ
      have hlen : (args ++ [s]).length = args.length + 1 := by simp
      have hall : ∀ s', s' ∈ args ++ [s] → SlotOk sig s' .nat := by
        intro s' hs'
        rcases List.mem_append.1 hs' with h | h
        · exact ha s' h
        · rw [List.mem_singleton.1 h]
          exact hs
      rw [apply_pap, headArity_prim]
      by_cases hsat : j = 0
      · have h1 : ((args ++ [s]).length == op.arity) = true := by
          rw [beq_iff_eq, hlen]
          omega
        simp only [h1, ↓reduceIte]
        rw [fire_prim]
        rcases forceAll_nat hslot (args ++ [s]) hall with hto | ⟨ns, hns, hnl⟩
        · rw [hto]
          exact .inl rfl
        · obtain ⟨n, hn⟩ := primValue_lits p hp (ns := ns) (by rw [hnl, hlen]; omega)
          rw [hns]
          show ResOk sig (Shape.nats j) (primValue p op (ns.map Value.lit))
          rw [hn]
          subst hsat
          exact .inr ⟨_, rfl, .lit⟩
      · have h1 : ¬ ((args ++ [s]).length == op.arity) = true := by
          rw [beq_iff_eq, hlen]
          omega
        have h2 : (args ++ [s]).length < op.arity := by
          rw [hlen]
          omega
        simp only [h1, h2, ↓reduceIte]
        refine .inr ⟨_, rfl, .pap op ls' (args ++ [s]) _ hp hall h2 ?_⟩
        rw [hlen]
        exact congrArg Shape.nats (by omega)
  -- E1 to E7, on the term judgment
  have hterm : ∀ (ls : Levels) (ρ : Env) (Γ : List Shape) (t : Term) (σ : Shape),
      HasShape sig Γ t σ → EnvOk sig ρ Γ → ResOk sig σ (eval p k ls ρ t) := by
    intro ls ρ Γ t σ ht
    induction ht generalizing ρ with
    | var hi =>
      intro hρ
      obtain ⟨s, hs, hok⟩ := EnvOk.get ρ _ hρ _ _ hi
      rw [eval_var_of p k ls ρ hs]
      exact hslot s _ hok
    | natLit =>
      intro _
      rw [eval_natLit]
      exact .inr ⟨_, rfl, .lit⟩
    | const hc =>
      intro _
      rw [eval_const]
      exact hconst _ _ _ hc
    | lam hb hbody _ =>
      intro hρ
      rw [eval_lam]
      exact .inr ⟨_, rfl, .clo hb hρ hbody⟩
    | @app Γ f a m σ τ hf ha ihf iha =>
      intro hρ
      cases m with
      | strict =>
        rw [eval_app_strict]
        rcases ihf ρ hρ with hfv | ⟨fv, hfv, hfok⟩
        · rw [hfv]
          exact .inl rfl
        · rw [hfv]
          rcases iha ρ hρ with hav | ⟨av, hav, haok⟩
          · show ResOk sig τ ((eval p k ls ρ a).bind fun x => apply p k fv (.val x))
            rw [hav]
            exact .inl rfl
          · show ResOk sig τ ((eval p k ls ρ a).bind fun x => apply p k fv (.val x))
            rw [hav]
            exact happ fv (.val av) _ _ hfok (.val haok)
      | byName =>
        rw [eval_app_byName]
        rcases ihf ρ hρ with hfv | ⟨fv, hfv, hfok⟩
        · rw [hfv]
          exact .inl rfl
        · rw [hfv]
          exact happ fv (.name a ρ ls) _ _ hfok (.name hρ ha)
    | letE hv hbody ihv ihb =>
      intro hρ
      rw [eval_letE_rel]
      rcases ihv ρ hρ with h1 | ⟨x, h1, hx⟩
      · rw [h1]
        exact .inl rfl
      · rw [h1]
        exact ihb _ (.cons (.val hx) hρ)
  exact ⟨hterm, hconst, happ, hslot⟩

/-- Applying a value of shape `Nat → … → Nat` to literals times out or returns a
value of shape `nat`. -/
theorem applyAll_nats {p : Program} {k : Nat} (h : AllOk p sig k) :
    ∀ (ns : List Nat) (f : Value), ValOk sig f (Shape.nats ns.length) →
      ResOk sig .nat (applyAll p k f ((ns.map Value.lit).map Slot.val))
  | [], f, hf => by
    show ResOk sig .nat (applyAll p k f [])
    rw [applyAll_nil]
    exact .inr ⟨f, rfl, hf⟩
  | n :: ns, f, hf => by
    show ResOk sig .nat
      (applyAll p k f (Slot.val (Value.lit n) :: (ns.map Value.lit).map Slot.val))
    rw [applyAll_cons]
    rcases h.app f (.val (.lit n)) .nat (Shape.nats ns.length) hf (.val .lit) with
      ha | ⟨v, ha, hv⟩
    · rw [ha]
      exact .inl rfl
    · rw [ha]
      exact applyAll_nats h ns v hv

/-- **A shaped root on `Nat` arguments times out or returns a literal**: SrcEval's
`run` is never stuck and never traps on it, and its result is a `Nat`. -/
theorem run_ok {p : Program} (hsig : SigOk p sig) {root : CId} (ns : List Nat)
    (hroot : sig root = some (Shape.nats ns.length)) (k : Nat) :
    run p k root (ns.map Value.lit) = .timeout ∨
      ∃ m, run p k root (ns.map Value.lit) = .ok (.lit m) := by
  have hall := allOk hsig k
  rw [run_eq]
  rcases hall.const [] root _ hroot with hc | ⟨f, hc, hf⟩
  · rw [hc]
    exact .inl rfl
  · rw [hc]
    rcases applyAll_nats hall ns f hf with ha | ⟨v, ha, hv⟩
    · exact .inl ha
    · obtain ⟨m, rfl⟩ := hv.nat_inv
      exact .inr ⟨m, ha⟩

/-! ## The discharge -/

/-- The view of a `Nat` literal at a root read back as `Nat`, or not read back, is not
a rejection. -/
theorem view_lit_ne_none {f : Recheck.Front} {r : Nat}
    (hty : f.tys r = none ∨ f.tys r = some ({}, .nat)) (I : IxCC.Lam.Erase.Input) (m : Nat) :
    f.view r (Lang.obs (S := CheckedProgram) ((I, Value.lit m) : Lang.Val CheckedProgram)) ≠
      none := by
  have ho : Lang.obs (S := CheckedProgram) ((I, Value.lit m) : Lang.Val CheckedProgram) =
      some (.nat m) := by
    show (IxCC.Lam.Erase.eraseVal I (Value.lit m)).bind IxCC.Lam.Erase.Proof.obsV = some (.nat m)
    simp [IxCC.Lam.Erase.eraseVal, IxCC.Lam.Erase.Proof.obsV]
  rw [ho]
  rcases hty with h | h
  · simp [Recheck.Front.view, Rt.viewOf, h]
  · rw [Recheck.view_nat h]
    simp

/-- **M0: `NeverWrong` for a shaped `Nat` root.** If the checked source resolves its
shaped constants as their shapes say, root `r` has shape `Nat → … → Nat` with as many
arguments as the input, and the root is read back as `Nat` (or not read back), then
the viewed source goes wrong at no clock: `Front.GoesWrong` is false of the input. -/
theorem neverWrong_of_shape {f : Recheck.Front} (hsig : SigOk f.src sig) {r : Nat}
    {addr : Ixon.Address} {c : CId} (hroot : f.src.roots[r]? = some (addr, c)) (ns : List Nat)
    (hc : sig c = some (Shape.nats ns.length))
    (hty : f.tys r = none ∨ f.tys r = some ({}, .nat)) :
    NeverWrong f.source (r, ns) := by
  rw [neverWrong_iff]
  intro k
  have e : Lang.run f.source.prog (r, ns) k =
      IxCC.Lam.Erase.Proof.srcRun ⟨f.src, f.checked⟩ (r, ns) k := rfl
  unfold IxCC.Lam.Erase.Proof.srcRun at e
  simp only [hroot] at e
  rcases run_ok hsig ns hc k with hr | ⟨m, hr⟩
  · rw [hr] at e
    constructor
    · rw [e]
      intro hw
      exact hw
    · intro v hv
      rw [e] at hv
      cases hv
  · rw [hr] at e
    constructor
    · rw [e]
      intro hw
      exact hw
    · intro v hv
      rw [e] at hv
      cases hv
      exact view_lit_ne_none hty _ m

/-- **M0 at the object**: `Recheck.sound` for a shaped `Nat` root, with no "source goes
wrong" case. Every value the object returns is the view of a value SrcEval returns,
and the object goes wrong at no clock. -/
theorem recheck_sound_of_shape {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a) (hsig : SigOk a.src sig) {r : Nat}
    {addr : Ixon.Address} {root : CId} (hroot : a.src.roots[r]? = some (addr, root))
    (ns : List Nat) (hc : sig root = some (Shape.nats ns.length))
    (hty : a.front.tys r = none ∨ a.front.tys r = some ({}, .nat))
    (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size) (hi : a.front.Covered c (r, ns)) :
    (∀ k w, Lang.run (a.linked D) (r, ns) k = .ok w →
      ∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (r, ns) k' = .ok v ∧
        a.front.view r (Lang.obs v) = some w) ∧
    (∀ k, ¬ (Lang.run (a.linked D) (r, ns) k).GoesWrong) :=
  recheck_sound_of_neverWrong h D hD (r, ns) hi
    (neverWrong_of_shape (f := a.front) hsig hroot ns hc hty)

/-! ## The decision

`HasShape` and `SigOk` are decided by a function a checker can run: shape synthesis
with the expected shape passed down to the λs (`synth`), over a certificate that lists
a shape for each constant (`sigCheck`). The certificate is untrusted: a wrong shape
makes the check fail. -/

/-- **Shape synthesis.** The shape of a term in a context, or `none`. `e` is the shape
expected, which a λ needs (its binder carries no shape) and nothing else reads. -/
def synth (sig : CId → Option Shape) : List Shape → Term → Option Shape → Option Shape
  | Γ, .var i, _ => Γ[i]?
  | _, .natLit _, _ => some .nat
  | _, .const c _, _ => sig c
  | Γ, .app f a _ r, _ =>
    if r = .rel then
      match synth sig Γ f none with
      | some (.fn σ τ) => if synth sig Γ a (some σ) = some σ then some τ else none
      | _ => none
    else none
  | Γ, .lam b _ body, e =>
    match e with
    | some (.fn σ τ) =>
      if b.propWhen = .never then
        if synth sig (σ :: Γ) body (some τ) = some τ then some (.fn σ τ) else none
      else none
    | _ => none
  | Γ, .letE _ _ r _ v body, e =>
    if r = .rel then
      match synth sig Γ v none with
      | some σ => synth sig (σ :: Γ) body e
      | none => none
    else none
  | _, _, _ => none

/-- A synthesized shape is a derivation. -/
theorem synth_sound : ∀ (t : Term) (Γ : List Shape) (e : Option Shape) (σ : Shape),
    synth sig Γ t e = some σ → HasShape sig Γ t σ := by
  intro t
  induction t with
  | var i =>
    intro Γ e σ h
    simp only [synth] at h
    exact .var h
  | sort u =>
    intro Γ e σ h
    simp [synth] at h
  | const c us =>
    intro Γ e σ h
    simp only [synth] at h
    exact .const h
  | app f a m r ihf iha =>
    intro Γ e σ h
    simp only [synth] at h
    split at h
    · rename_i hr
      subst hr
      split at h
      · rename_i σ' τ' hf
        split at h
        · rename_i ha
          simp only [Option.some.injEq] at h
          subst h
          exact .app (ihf _ _ _ hf) (iha _ _ _ ha)
        · cases h
      · cases h
    · cases h
  | lam b d body _ ihb =>
    intro Γ e σ h
    cases e with
    | none => simp [synth] at h
    | some s =>
      cases s with
      | nat => simp [synth] at h
      | fn σ' τ' =>
        simp only [synth] at h
        split at h
        · rename_i hb
          split at h
          · rename_i hbody
            simp only [Option.some.injEq] at h
            subst h
            exact .lam hb (ihb _ _ _ hbody)
          · cases h
        · cases h
  | pi b d c _ _ =>
    intro Γ e σ h
    simp [synth] at h
  | letE nonDep lm r ty v body _ ihv ihb =>
    intro Γ e σ h
    simp only [synth] at h
    split at h
    · rename_i hr
      subst hr
      split at h
      · rename_i σ' hv
        exact .letE (ihv _ _ _ hv) (ihb _ _ _ h)
      · cases h
    · cases h
  | proj s i e' _ =>
    intro Γ e σ h
    simp [synth] at h
  | natLit n =>
    intro Γ e σ h
    simp only [synth, Option.some.injEq] at h
    subst h
    exact .natLit
  | strLit s =>
    intro Γ e σ h
    simp [synth] at h

/-- The shape a certificate lists for a constant: its first entry's. -/
def sigOf : List (CId × Shape) → CId → Option Shape
  | [], _ => none
  | (c', σ) :: l, c => if c = c' then some σ else sigOf l c

theorem mem_of_sigOf : ∀ (l : List (CId × Shape)) (c : CId) (σ : Shape),
    sigOf l c = some σ → (c, σ) ∈ l
  | [], c, σ, h => by simp [sigOf] at h
  | (c', σ') :: l, c, σ, h => by
    simp only [sigOf] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst hc
      subst h
      exact List.mem_cons.2 (.inl rfl)
    · exact List.mem_cons.2 (.inr (mem_of_sigOf l c σ h))

/-- One constant resolves in the program as its shape says (`SigOk`'s clause, decided). -/
def entryOk (p : Program) (sig : CId → Option Shape) (c : CId) (σ : Shape) : Bool :=
  match p.table.resolveOf c with
  | some (.prim op) => !op.isPredicate && decide (σ = Shape.nats op.arity)
  | some (.eqn _ body) => decide (synth sig [] body (some σ) = some σ)
  | some (.csimp g _ _) => decide (sig g = some σ)
  | some (.case _) => false
  | some (.word _ _ _) => false
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) => decide (synth sig [] v (some σ) = some σ)
    | _ => false

theorem entryOk_sound {p : Program} {c : CId} {σ : Shape} (h : entryOk p sig c σ = true) :
    (∃ op, p.table.resolveOf c = some (.prim op) ∧ op.isPredicate = false ∧
      σ = Shape.nats op.arity) ∨
    (∃ thm body, p.table.resolveOf c = some (.eqn thm body) ∧ HasShape sig [] body σ) ∨
    (∃ g us thm, p.table.resolveOf c = some (.csimp g us thm) ∧ sig g = some σ) ∨
    (∃ lvls ty v, p.table.resolveOf c = none ∧
      p.decl? c = some (.defn .defn .safe lvls ty v) ∧ HasShape sig [] v σ) := by
  unfold entryOk at h
  split at h
  · rename_i op hres
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    exact .inl ⟨op, hres, h.1, h.2⟩
  · rename_i thm body hres
    exact .inr (.inl ⟨thm, body, hres, synth_sound _ _ _ _ (of_decide_eq_true h)⟩)
  · rename_i g us thm hres
    exact .inr (.inr (.inl ⟨g, us, thm, hres, of_decide_eq_true h⟩))
  · cases h
  · cases h
  · rename_i hres
    split at h
    · rename_i lvls ty v hdecl
      exact .inr (.inr (.inr ⟨lvls, ty, v, hres, hdecl,
        synth_sound _ _ _ _ (of_decide_eq_true h)⟩))
    · cases h

/-- **The check**: every entry of the certificate resolves as its shape says, under the
shapes the certificate lists. -/
def sigCheck (p : Program) (l : List (CId × Shape)) : Bool :=
  l.all fun e => entryOk p (sigOf l) e.1 e.2

theorem sigOk_of_check {p : Program} {l : List (CId × Shape)} (h : sigCheck p l = true) :
    SigOk p (sigOf l) :=
  ⟨fun c σ hc => entryOk_sound (List.all_eq_true.1 h (c, σ) (mem_of_sigOf l c σ hc))⟩

/-- **M0 as a decision.** For a front half the checker accepted, a certificate `l`
that passes `sigCheck` on the checked source and lists the shape `Nat → … → Nat` for
root `r`'s constant, at a root read back as `Nat` (or not read back): the viewed
source goes wrong at no clock on the root's inputs. Every hypothesis is a decision on
data the checker holds. -/
theorem neverWrong_of_check {f : Recheck.Front} {l : List (CId × Shape)}
    (h : sigCheck f.src l = true) {r : Nat} {addr : Ixon.Address} {c : CId}
    (hroot : f.src.roots[r]? = some (addr, c)) (ns : List Nat)
    (hc : sigOf l c = some (Shape.nats ns.length))
    (hty : f.tys r = none ∨ f.tys r = some ({}, .nat)) :
    NeverWrong f.source (r, ns) :=
  neverWrong_of_shape (sigOk_of_check h) hroot ns hc hty

end IxCC.Correct.Shape
