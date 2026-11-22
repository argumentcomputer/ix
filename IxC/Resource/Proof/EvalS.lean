import IxC.Resource.Eval
import IxC.Resource.Proof.Heap

/-!
# Linear-Budget-Threaded Reference Evaluator (`EvalS`)

Defines `evalS` / `spineS` / `callWithS` / `enterS` / `staticS` / `applyAllS` / `applyOneS` /
`applyAltS` over `MS := StateT (St × Nat) (Except Stop)`: identical to `Eval.lean`'s mutual
evaluator, except each recursive entry decrements a linear `budget : Nat` (returning
`.error .outOfFuel` when `budget = 0`).

This decouples the step-indexed logical relation `FunOkAt` (indexed on the linear budget `B`)
from `Eval.lean`'s tree-depth `fuel`, so `F4` proceeds by a single strong induction on `B` with
zero fuel-index loss across `letE`, `spine` argument loops, and `applyAll`.

Main theorem (`enter_to_enterS`): if `(enter P ext fuel params res rc body args).run st`
returns `.error (.violation k)` (or `.ok` / `.error .stuck`), then there exists `B : Nat`
such that `(enterS P ext fuel params res rc body args).run (st, B)` returns the exact same
result.
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## 1. The Budget-Threaded Monad `MS` -/

abbrev MS := StateT (St × Nat) (Except Stop)

def liftM {α : Type} (m : M α) : MS α := fun (st, b) =>
  match m.run st with
  | .ok (a, st') => .ok (a, (st', b))
  | .error e => .error e

def spend : MS Unit := fun (st, b) =>
  match b with
  | 0 => .error .outOfFuel
  | b' + 1 => .ok ((), (st, b'))

theorem MS_pure_run {α : Type} (a : α) (st : St) (b : Nat) :
    ((pure a : MS α).run (st, b)) = .ok (a, (st, b)) := rfl

theorem MS_bind_run {α β : Type} (m : MS α) (f : α → MS β) (st : St) (b : Nat) :
    ((m >>= f).run (st, b)) =
      (match m.run (st, b) with
       | .ok (a, sb') => (f a).run sb'
       | .error e => .error e) := by
  change (m.run (st, b)).bind (fun p => (f p.1).run p.2) = _
  cases m.run (st, b) <;> rfl

theorem MS_liftM_run {α : Type} (m : M α) (st : St) (b : Nat) :
    (liftM m).run (st, b) =
      (match m.run st with
       | .ok (a, st') => .ok (a, (st', b))
       | .error e => .error e) := rfl

theorem MS_spend_zero (st : St) :
    spend.run (st, 0) = .error .outOfFuel := rfl

theorem MS_spend_succ (st : St) (b : Nat) :
    spend.run (st, b + 1) = .ok ((), (st, b)) := rfl

/-! ## 2. Generic `List` `forIn` Bridge Helpers -/

/-- Execute a `for`-loop body `f` sequentially over a list in `M`, accumulating state `acc`. -/
def listLoopM {α β : Type} (f : α → β → M β) : List α → β → M β
  | [], acc => pure acc
  | x :: xs, acc => do
    let acc' ← f x acc
    listLoopM f xs acc'

theorem forIn_list_eq_listLoopM {α β : Type} (f : α → β → M β) (xs : List α) (acc : β) (st : St) :
    (forIn (m := M) xs acc (fun x a => (f x a) >>= fun a' => pure (.yield a'))).run st =
      (listLoopM f xs acc).run st := by
  induction xs generalizing acc st with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    rw [M_bind_run, M_bind_run]
    unfold listLoopM
    rw [M_bind_run]
    cases hfx : (f x acc).run st with
    | error e => rfl
    | ok p =>
      dsimp only
      rw [M_pure_run]
      exact ih p.1 p.2

theorem forIn_list_map_eq_listLoopM {α β γ : Type} (step : α → M γ) (comb : β → γ → β)
    (xs : List α) (acc : β) (st : St) :
    (forIn (m := M) xs acc (fun x a => step x >>= fun v => pure (.yield (comb a v)))).run st =
      (listLoopM (fun x a => step x >>= fun v => pure (comb a v)) xs acc).run st := by
  induction xs generalizing acc st with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    rw [M_bind_run, M_bind_run]
    unfold listLoopM
    rw [M_bind_run, M_bind_run]
    cases hs : (step x).run st with
    | error e => rfl
    | ok p =>
      dsimp only
      rw [M_pure_run, M_pure_run]
      exact ih (comb acc p.1) p.2

/-! ## 3. Budget-Threaded Evaluator `evalS` -/

/-- Bind parameters in `enter`, matching `Eval.enter`'s `for` loop. -/
def bindParamsM (P : Prog) (fuel s : Nat) : List (Param × Val) → List Bnd → M (List Bnd)
  | [], env => pure env
  | (p, v) :: rest, env => do
    let b ← bindAt P fuel s p.mode p.cls v
    bindParamsM P fuel s rest (b :: env)

theorem bindParamsM_eq_listLoopM (P : Prog) (fuel s : Nat) (xs : List (Param × Val))
    (env : List Bnd) (st : St) :
    (listLoopM (fun (pv : Param × Val) (acc : List Bnd) =>
        bindAt P fuel s pv.1.mode pv.1.cls pv.2 >>= fun b => pure (b :: acc)) xs env).run st =
      (bindParamsM P fuel s xs env).run st := by
  induction xs generalizing env st with
  | nil => rfl
  | cons pv rest ih =>
    unfold listLoopM bindParamsM
    rw [M_bind_run, M_bind_run, M_bind_run]
    cases h : (bindAt P fuel s pv.1.mode pv.1.cls pv.2).run st with
    | error e => rfl
    | ok p =>
      dsimp only
      rw [M_pure_run]
      exact ih (p.1 :: env) p.2

mutual

def evalListS (P : Prog) (ext : ExternOracle) : Nat → List Bnd → List Term → List Val → MS (List Val)
  | _, _, [], acc => pure acc
  | n, env, a :: rest, acc => do
    let v ← evalS P ext n env a
    evalListS P ext n env rest (acc ++ [v])

def evalCallArgsS (P : Prog) (ext : ExternOracle) :
    Nat → List Bnd → Option RunDef → List (Term × Nat) → List Val → MS (List Val)
  | _, _, _, [], acc => pure acc
  | n, env, d, (a, i) :: rest, acc => do
    let skip := match d with
      | some d => erasedAt d i
      | none => false
    let v ← if skip then pure (.imm .irr) else evalS P ext n env a
    evalCallArgsS P ext n env d rest (acc ++ [v])

def evalS (P : Prog) (ext : ExternOracle) : Nat → List Bnd → Term → MS Val
  | 0, _, _ => do spend; throw .outOfFuel
  | n + 1, env, t => do
    spend
    match t with
    | .irr => pure (.imm .irr)
    | .var i c => liftM do
      let some b := env[i]? | stuckM
      if b.mode == .erased then violate .erasedRead
      live b.val
      conform c b.val
    | .natLit k => liftM (natValue k)
    | .strLit s => liftM (strValue s)
    | .const r c => spineS P ext n env (.const r c) [] c
    | .app f a c => do
      let (h, as) := collect (.app f a c) []
      spineS P ext n env h as c
    | .lam p res rc fvs body => liftM (formClosure P n env p res rc fvs body)
    | .letE m d v b => do
      match m with
      | .value .erased => evalS P ext n (⟨.imm .irr, .erased⟩ :: env) b
      | _ => do
        let x ← evalS P ext n env v
        let (s, _) ← liftM openRegion
        let bnd ← liftM (bindAt P n s m.binderMode d x)
        let r ← evalS P ext n (bnd :: env) b
        if confinedTo s r then liftM (violate .borrowEscape)
        liftM (closeRegion s)
        pure r
    | .proj s i e c => do
      let v ← evalS P ext n env e
      liftM do
        live v
        let cs := P.ctorsOf s
        let some ctor := cs[0]? | stuckM
        let some (_, _, _, fields) := P.ctorOf? ctor | stuckM
        let some f := fields[i]? | stuckM
        if f.mode == .erased then violate .erasedRead
        if f.cls == .irr then return .imm .irr
        let asWrapper : M Val :=
          if P.wrapperField? s == some i then conform c v else stuckM
        match v with
        | .ref loc _ tv => do
          match (← obj loc).cell with
          | .ctor r' fs =>
            unless r' == ctor do stuckM
            let some fv := fs[i]? | stuckM
            conform c (← readOut (f.fmode == .inherited) tv fv)
          | .num _ => asWrapper
          | _ => stuckM
        | .imm _ => asWrapper
    | .case k major alts extra c => do
      let mv ← match major with
        | .var j mc => liftM do
          let some b := env[j]? | stuckM
          if b.mode == .erased then violate .erasedRead
          live b.val
          let v ← conform mc b.val
          if b.mode.isUnique then transfer P n b.mode.isBorrowed v else pure v
        | t => evalS P ext n env t
      let (j, fields) ← liftM (select P k mv)
      let some alt := k.alts[j]? | liftM stuckM
      let some altT := alts[j]? | liftM stuckM
      let args := alt.args.toList.map fun fa => match fa with
        | .field i => fields[i]?.getD (.imm .irr, false)
        | .irr => (.imm .irr, false)
        | .unit => (.imm .irr, false)
      let r ← applyAltS P ext n env altT args
      let ex ← evalListS P ext n env extra.toList []
      applyAllS P ext n r ex c

def spineS (P : Prog) (ext : ExternOracle) : Nat → List Bnd → Term → List Term → Cls → MS Val
  | 0, _, _, _, _ => do spend; throw .outOfFuel
  | n + 1, env, head, args, c => do
    spend
    match head with
    | .const r _ => do
      let d := P.find? r
      let vs ← evalCallArgsS P ext n env d args.zipIdx []
      callWithS P ext n r vs c
    | _ => do
      let f ← evalS P ext n env head
      let vs ← evalListS P ext n env args []
      applyAllS P ext n f vs c

def callWithS (P : Prog) (ext : ExternOracle) : Nat → Ref → List Val → Cls → MS Val
  | 0, _, _, _ => do spend; throw .outOfFuel
  | n + 1, r, vs, c => do
    spend
    match P.find? r with
    | some (.body params res rc _ body) =>
      if vs.length < params.size then liftM (makePap P n r params vs)
      else do
        let f ← if params.size == 0 then staticS P ext n r body rc
          else enterS P ext n params res rc body (vs.take params.size)
        applyAllS P ext n f (vs.drop params.size) c
    | some (.ctor _ _ nP fields) =>
      if vs.length < nP + fields.size then liftM (makePap P n r #[] vs)
      else if vs.length > nP + fields.size then liftM stuckM
      else liftM (construct r fields (vs.drop nP) c)
    | some (.prim p) =>
      if vs.length < p.arity then liftM (makePap P n r #[] vs)
      else if vs.length > p.arity then liftM stuckM
      else liftM do conform c (← prim p vs)
    | some (.extern params res rc _) =>
      if vs.length < params.size then liftM (makePap P n r params vs)
      else do
        let f ← liftM (callExtern P ext n r params res rc (vs.take params.size))
        applyAllS P ext n f (vs.drop params.size) c
    | some (.ind _) => pure (.imm .irr)
    | _ => liftM stuckM

def enterS (P : Prog) (ext : ExternOracle) :
    Nat → Array Param → ResultMode → Cls → Term → List Val → MS Val
  | 0, _, _, _, _, _ => do spend; throw .outOfFuel
  | n + 1, params, res, rc, body, vs => do
    spend
    let (s, cur) ← liftM openRegion
    let env ← liftM (bindParamsM P n s (params.toList.zip vs) [])
    let r ← evalS P ext n env body
    let r ← liftM (ret P n s cur res rc r)
    liftM (closeRegion s)
    pure r

def staticS (P : Prog) (ext : ExternOracle) : Nat → Ref → Term → Cls → MS Val
  | 0, _, _, _ => do spend; throw .outOfFuel
  | n + 1, r, body, rc => do
    spend
    let st ← liftM get
    match st.statics.find? (·.1 == r) with
    | some (_, v) => liftM do live v; pure v
    | none => do
      let v0 ← evalS P ext n [] body
      let v ← liftM (conform rc v0)
      liftM (modify fun s => { s with statics := s.statics.push (r, v) })
      pure v

def applyAllS (P : Prog) (ext : ExternOracle) : Nat → Val → List Val → Cls → MS Val
  | 0, _, _, _ => do spend; throw .outOfFuel
  | _ + 1, f, [], c => do spend; liftM (conform c f)
  | n + 1, f, a :: rest, c => do
    spend
    let g ← applyOneS P ext n f a (if rest.isEmpty then c else .val)
    applyAllS P ext n g rest c

def applyOneS (P : Prog) (ext : ExternOracle) : Nat → Val → Val → Cls → MS Val
  | 0, _, _, _ => do spend; throw .outOfFuel
  | n + 1, f, a, c => do
    spend
    match f with
    | .imm .irr => pure (.imm .irr)
    | .imm _ => liftM stuckM
    | .ref loc cap _ => do
      let o ← liftM (obj loc)
      unless o.cap == cap do liftM (violate .revokedUse)
      match o.cell with
      | .clo env p res rc _ body => do
        let (s, cur) ← liftM openRegion
        let b ← liftM (bindAt P n s p.mode p.cls a)
        let r ← evalS P ext n (b :: env) body
        let r ← liftM (ret P n s cur res rc r)
        liftM (closeRegion s)
        liftM (conform c r)
      | .pap r args => callWithS P ext n r (args.toList ++ [a]) c
      | .once t spent => do
        if spent then liftM (violate .onceReentry)
        liftM (setObj loc { o with cell := .once t true })
        applyOneS P ext n t a c
      | _ => liftM stuckM

def applyAltS (P : Prog) (ext : ExternOracle) : Nat → List Bnd → Term → List (Val × Bool) → MS Val
  | 0, _, _, _ => do spend; throw .outOfFuel
  | n + 1, env, t, [] => do spend; evalS P ext n env t
  | n + 1, env, t, (a, er) :: rest => do
    spend
    match t with
    | .lam p res rc _ body => do
      let (s, cur) ← liftM openRegion
      let b ← liftM (if er then pure ⟨.imm .irr, .erased⟩ else bindAt P n s p.mode p.cls a)
      let r ← applyAltS P ext n (b :: env) body rest
      let r ← liftM (ret P n s cur res rc r)
      liftM (closeRegion s)
      pure r
    | _ => do
      if ((a, er) :: rest).any (·.2) then liftM (violate .erasedRead)
      let f ← evalS P ext n env t
      applyAllS P ext n f (((a, er) :: rest).map (·.1)) .val

end

/-! ## 4. Adequacy: `Eval` Matches `EvalS` at Sufficiently Large Budget -/

/-- `ms` matches `m` at every budget `b ≥ B` (shifting leftover budget linearly). -/
def MatchesFrom {α : Type} (m : M α) (ms : MS α) (st : St) (B : Nat) : Prop :=
  match m.run st with
  | .ok (a, st') =>
    ∃ b₀, b₀ ≤ B ∧ ∀ d, ms.run (st, B + d) = .ok (a, (st', b₀ + d))
  | .error (.violation k) => ∀ d, ms.run (st, B + d) = .error (.violation k)
  | .error .stuck => ∀ d, ms.run (st, B + d) = .error .stuck
  | .error .outOfFuel => True

theorem MatchesFrom.mono {α : Type} {m : M α} {ms : MS α} {st : St} {B₁ B₂ : Nat}
    (hle : B₁ ≤ B₂) (h : MatchesFrom m ms st B₁) : MatchesFrom m ms st B₂ := by
  unfold MatchesFrom at h ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  cases hm : m.run st with
  | ok p =>
    rw [hm] at h
    obtain ⟨b₀, hb₀, hall⟩ := h
    refine ⟨b₀ + k, by omega, fun d => ?_⟩
    have := hall (k + d)
    have heq1 : B₁ + (k + d) = B₁ + k + d := by omega
    have heq2 : b₀ + (k + d) = b₀ + k + d := by omega
    rwa [heq1, heq2] at this
  | error e =>
    rw [hm] at h
    cases e with
    | violation kv =>
      intro d
      have := h (k + d)
      have heq : B₁ + (k + d) = B₁ + k + d := by omega
      rwa [heq] at this
    | stuck =>
      intro d
      have := h (k + d)
      have heq : B₁ + (k + d) = B₁ + k + d := by omega
      rwa [heq] at this
    | outOfFuel => trivial

theorem MatchesFrom_liftM {α : Type} (m : M α) (st : St) :
    MatchesFrom m (liftM m) st 0 := by
  unfold MatchesFrom
  cases hm : m.run st with
  | ok p =>
    refine ⟨0, Nat.le_refl _, fun d => ?_⟩
    rw [MS_liftM_run, hm]
  | error e =>
    cases e with
    | violation kv => intro d; rw [MS_liftM_run, hm]
    | stuck => intro d; rw [MS_liftM_run, hm]
    | outOfFuel => trivial

theorem MatchesFrom_pure {α : Type} (a : α) (st : St) :
    MatchesFrom (pure a) (pure a) st 0 := by
  unfold MatchesFrom
  rw [M_pure_run]
  exact ⟨0, Nat.le_refl _, fun d => by rw [MS_pure_run]⟩

theorem MatchesFrom_spend {α : Type} {m : M α} {ms : MS α} {st : St} {B : Nat}
    (h : MatchesFrom m ms st B) :
    MatchesFrom m (do spend; ms) st (B + 1) := by
  unfold MatchesFrom at h ⊢
  cases hm : m.run st with
  | ok p =>
    rw [hm] at h
    obtain ⟨b₀, hb₀, hall⟩ := h
    refine ⟨b₀, by omega, fun d => ?_⟩
    have hstep : B + 1 + d = (B + d) + 1 := by omega
    rw [hstep, MS_bind_run, MS_spend_succ]
    exact hall d
  | error e =>
    rw [hm] at h
    cases e with
    | violation kv =>
      intro d
      have hstep : B + 1 + d = (B + d) + 1 := by omega
      rw [hstep, MS_bind_run, MS_spend_succ]
      exact h d
    | stuck =>
      intro d
      have hstep : B + 1 + d = (B + d) + 1 := by omega
      rw [hstep, MS_bind_run, MS_spend_succ]
      exact h d
    | outOfFuel => trivial

theorem MatchesFrom_bind {α β : Type} {m : M α} {ms : MS α} {f : α → M β} {fs : α → MS β}
    {st : St} {B₁ : Nat} (hm : MatchesFrom m ms st B₁)
    (hf : ∀ a st', m.run st = .ok (a, st') → ∃ B₂, MatchesFrom (f a) (fs a) st' B₂) :
    ∃ B, MatchesFrom (m >>= f) (ms >>= fs) st B := by
  unfold MatchesFrom at hm
  cases hm1 : m.run st with
  | error e =>
    rw [hm1] at hm
    refine ⟨B₁, ?_⟩
    unfold MatchesFrom
    rw [M_bind_run, hm1]
    dsimp only
    cases e with
    | violation kv =>
      intro d; rw [MS_bind_run, hm d]
    | stuck =>
      intro d; rw [MS_bind_run, hm d]
    | outOfFuel => trivial
  | ok p =>
    rw [hm1] at hm
    obtain ⟨b₀, hb₀, hall₁⟩ := hm
    obtain ⟨B₂, hmf⟩ := hf p.1 p.2 hm1
    refine ⟨B₁ + B₂, ?_⟩
    unfold MatchesFrom at hmf ⊢
    rw [M_bind_run, hm1]
    dsimp only
    cases hf1 : (f p.1).run p.2 with
    | ok q =>
      rw [hf1] at hmf
      obtain ⟨b₁, hb₁, hall₂⟩ := hmf
      refine ⟨b₁ + b₀, by omega, fun d => ?_⟩
      rw [MS_bind_run]
      have h1 := hall₁ (B₂ + d)
      have heq1 : B₁ + (B₂ + d) = B₁ + B₂ + d := by omega
      rw [heq1] at h1
      rw [h1]
      dsimp only
      have h2 := hall₂ (b₀ + d)
      have heq2 : B₂ + (b₀ + d) = b₀ + (B₂ + d) := by omega
      have heq3 : b₁ + (b₀ + d) = b₁ + b₀ + d := by omega
      rw [heq2, heq3] at h2
      exact h2
    | error e =>
      rw [hf1] at hmf
      cases e with
      | violation kv =>
        intro d
        rw [MS_bind_run]
        have h1 := hall₁ (B₂ + d)
        have heq1 : B₁ + (B₂ + d) = B₁ + B₂ + d := by omega
        rw [heq1] at h1
        rw [h1]
        dsimp only
        have h2 := hmf (b₀ + d)
        have heq2 : B₂ + (b₀ + d) = b₀ + (B₂ + d) := by omega
        rwa [heq2] at h2
      | stuck =>
        intro d
        rw [MS_bind_run]
        have h1 := hall₁ (B₂ + d)
        have heq1 : B₁ + (B₂ + d) = B₁ + B₂ + d := by omega
        rw [heq1] at h1
        rw [h1]
        dsimp only
        have h2 := hmf (b₀ + d)
        have heq2 : B₂ + (b₀ + d) = b₀ + (B₂ + d) := by omega
        rwa [heq2] at h2
      | outOfFuel => trivial

theorem MatchesFrom_exists_spend {α : Type} {m : M α} {ms : MS α} {st : St}
    (h : ∃ B, MatchesFrom m ms st B) : ∃ B, MatchesFrom m (do spend; ms) st B :=
  let ⟨B, hB⟩ := h; ⟨B + 1, MatchesFrom_spend hB⟩

theorem MatchesFrom_exists_liftM {α : Type} (m : M α) (st : St) :
    ∃ B, MatchesFrom m (liftM m) st B :=
  ⟨0, MatchesFrom_liftM m st⟩

theorem MatchesFrom_exists_pure {α : Type} (a : α) (st : St) :
    ∃ B, MatchesFrom (pure a) (pure a) st B :=
  ⟨0, MatchesFrom_pure a st⟩

theorem MatchesFrom_exists_bind {α β : Type} {m : M α} {ms : MS α} {f : α → M β} {fs : α → MS β}
    {st : St} (hm : ∃ B₁, MatchesFrom m ms st B₁)
    (hf : ∀ a st', m.run st = .ok (a, st') → ∃ B₂, MatchesFrom (f a) (fs a) st' B₂) :
    ∃ B, MatchesFrom (m >>= f) (ms >>= fs) st B :=
  let ⟨_, h⟩ := hm; MatchesFrom_bind h hf

theorem MatchesFrom_eq_M {α : Type} {m₁ m₂ : M α} {ms : MS α} {st : St} {B : Nat}
    (heq : m₁.run st = m₂.run st) (h : MatchesFrom m₁ ms st B) : MatchesFrom m₂ ms st B := by
  unfold MatchesFrom at h ⊢
  rwa [← heq]

theorem MatchesFrom_outOfFuel {α : Type} {ms : MS α} {st : St} :
    ∃ B, MatchesFrom (throw .outOfFuel : M α) ms st B :=
  ⟨0, by unfold MatchesFrom; change True; trivial⟩

theorem MatchesFrom_evalList (P : Prog) (ext : ExternOracle) (n : Nat) (env : List Bnd)
    (ih : ∀ env t st, ∃ B, MatchesFrom (eval P ext n env t) (evalS P ext n env t) st B) :
    ∀ (xs : List Term) (acc : List Val) (st : St),
      ∃ B, MatchesFrom
        (listLoopM (fun a vs => eval P ext n env a >>= fun v => pure (vs ++ [v])) xs acc)
        (evalListS P ext n env xs acc) st B
  | [], acc, st => by
    unfold listLoopM evalListS
    exact MatchesFrom_exists_pure acc st
  | a :: rest, acc, st => by
    unfold listLoopM evalListS
    have hstep : ∃ B, MatchesFrom
        (eval P ext n env a >>= fun v =>
          listLoopM (fun a vs => eval P ext n env a >>= fun v => pure (vs ++ [v])) rest (acc ++ [v]))
        (evalS P ext n env a >>= fun v => evalListS P ext n env rest (acc ++ [v])) st B :=
      MatchesFrom_exists_bind (ih env a st) (fun v st' _ => MatchesFrom_evalList P ext n env ih rest (acc ++ [v]) st')
    obtain ⟨B, hB⟩ := hstep
    refine ⟨B, MatchesFrom_eq_M ?_ hB⟩
    rw [M_bind_run, M_bind_run, M_bind_run]
    cases (eval P ext n env a).run st with
    | error e => rfl
    | ok p => dsimp only; rw [M_pure_run]

theorem MatchesFrom_evalCallArgs (P : Prog) (ext : ExternOracle) (n : Nat) (env : List Bnd)
    (d : Option RunDef)
    (ih : ∀ env t st, ∃ B, MatchesFrom (eval P ext n env t) (evalS P ext n env t) st B) :
    ∀ (xs : List (Term × Nat)) (acc : List Val) (st : St),
      ∃ B, MatchesFrom
        (forIn (m := M) xs acc (fun x __s =>
          if (match d with | some d => erasedAt d x.2 | none => false) = true then
            pure (Val.imm .irr) >>= fun v => pure (.yield (__s ++ [v]))
          else eval P ext n env x.1 >>= fun v => pure (.yield (__s ++ [v]))))
        (evalCallArgsS P ext n env d xs acc) st B
  | [], acc, st => by
    simp only [List.forIn_nil]
    unfold evalCallArgsS
    exact MatchesFrom_exists_pure acc st
  | (a, i) :: rest, acc, st => by
    unfold evalCallArgsS
    cases hskip : (match d with | some d => erasedAt d i | none => false) with
    | true =>
      simp only [↓reduceIte]
      have hstep := MatchesFrom_exists_bind (MatchesFrom_exists_pure (Val.imm .irr) st)
        (fun v st' _ => MatchesFrom_evalCallArgs P ext n env d ih rest (acc ++ [v]) st')
      obtain ⟨B, hB⟩ := hstep
      refine ⟨B, MatchesFrom_eq_M ?_ hB⟩
      simp only [List.forIn_cons, hskip, ↓reduceIte]
      rw [M_bind_run, M_bind_run, M_bind_run, M_pure_run]
      dsimp only
      rw [M_pure_run]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hstep := MatchesFrom_exists_bind (ih env a st)
        (fun v st' _ => MatchesFrom_evalCallArgs P ext n env d ih rest (acc ++ [v]) st')
      obtain ⟨B, hB⟩ := hstep
      refine ⟨B, MatchesFrom_eq_M ?_ hB⟩
      simp only [List.forIn_cons, hskip, Bool.false_eq_true, ↓reduceIte]
      rw [M_bind_run, M_bind_run, M_bind_run]
      cases (eval P ext n env a).run st with
      | error e => rfl
      | ok p => dsimp only; rw [M_pure_run]

/-- Simultaneous adequacy of all 8 evaluators by induction on `fuel`. -/
theorem eval_matches_evalS (P : Prog) (ext : ExternOracle) :
    ∀ (fuel : Nat),
      (∀ env t st, ∃ B, MatchesFrom (eval P ext fuel env t) (evalS P ext fuel env t) st B) ∧
      (∀ env h as c st, ∃ B, MatchesFrom (spine P ext fuel env h as c) (spineS P ext fuel env h as c) st B) ∧
      (∀ r vs c st, ∃ B, MatchesFrom (callWith P ext fuel r vs c) (callWithS P ext fuel r vs c) st B) ∧
      (∀ ps res rc body vs st, ∃ B, MatchesFrom (enter P ext fuel ps res rc body vs) (enterS P ext fuel ps res rc body vs) st B) ∧
      (∀ r body rc st, ∃ B, MatchesFrom (static P ext fuel r body rc) (staticS P ext fuel r body rc) st B) ∧
      (∀ f vs c st, ∃ B, MatchesFrom (applyAll P ext fuel f vs c) (applyAllS P ext fuel f vs c) st B) ∧
      (∀ f a c st, ∃ B, MatchesFrom (applyOne P ext fuel f a c) (applyOneS P ext fuel f a c) st B) ∧
      (∀ env t as st, ∃ B, MatchesFrom (applyAlt P ext fuel env t as) (applyAltS P ext fuel env t as) st B)
  | 0 => ⟨fun _ _ _ => MatchesFrom_outOfFuel, fun _ _ _ _ _ => MatchesFrom_outOfFuel,
      fun _ _ _ _ => MatchesFrom_outOfFuel, fun _ _ _ _ _ _ => MatchesFrom_outOfFuel,
      fun _ _ _ _ => MatchesFrom_outOfFuel, fun _ _ _ _ => MatchesFrom_outOfFuel,
      fun _ _ _ _ => MatchesFrom_outOfFuel, fun _ _ _ _ => MatchesFrom_outOfFuel⟩
  | n + 1 => by
    obtain ⟨ihEval, ihSpine, ihCall, ihEnter, ihStatic, ihAll, ihOne, ihAlt⟩ := eval_matches_evalS P ext n
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- eval
      intro env t st
      unfold eval evalS
      apply MatchesFrom_exists_spend
      cases t with
      | irr => exact MatchesFrom_exists_pure (Val.imm .irr) st
      | var i c => exact MatchesFrom_exists_liftM _ st
      | natLit k => exact MatchesFrom_exists_liftM _ st
      | strLit s => exact MatchesFrom_exists_liftM _ st
      | const r c => exact ihSpine env (.const r c) [] c st
      | app f a c => exact ihSpine env (collect (.app f a c) []).1 (collect (.app f a c) []).2 c st
      | lam p res rc fvs body => exact MatchesFrom_exists_liftM _ st
      | letE m d v b =>
        cases m with
        | value bm =>
          cases bm with
          | erased => exact ihEval (⟨.imm .irr, .erased⟩ :: env) b st
          | many | borrowed | unique | uniqueBorrowed | once | onceBorrowed =>
            refine MatchesFrom_exists_bind (ihEval env v st) fun x st₁ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM openRegion st₁) fun p st₂ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (bindAt P n p.1 _ d x) st₂) fun bnd st₃ _ => ?_
            refine MatchesFrom_exists_bind (ihEval (bnd :: env) b st₃) fun r st₄ _ => ?_
            cases hcf : confinedTo p.1 r with
            | true =>
              simp only [↓reduceIte]
              refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (violate .borrowEscape) st₄) fun _ st₅ _ => ?_
              refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (closeRegion p.1) st₅) fun _ st₆ _ => ?_
              exact MatchesFrom_exists_pure r st₆
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (closeRegion p.1) st₄) fun _ st₅ _ => ?_
              exact MatchesFrom_exists_pure r st₅
        | borrow =>
          refine MatchesFrom_exists_bind (ihEval env v st) fun x st₁ _ => ?_
          refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM openRegion st₁) fun p st₂ _ => ?_
          refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (bindAt P n p.1 _ d x) st₂) fun bnd st₃ _ => ?_
          refine MatchesFrom_exists_bind (ihEval (bnd :: env) b st₃) fun r st₄ _ => ?_
          cases hcf : confinedTo p.1 r with
          | true =>
            simp only [↓reduceIte]
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (violate .borrowEscape) st₄) fun _ st₅ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (closeRegion p.1) st₅) fun _ st₆ _ => ?_
            exact MatchesFrom_exists_pure r st₆
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (closeRegion p.1) st₄) fun _ st₅ _ => ?_
            exact MatchesFrom_exists_pure r st₅
      | proj s i e c =>
        refine MatchesFrom_exists_bind (ihEval env e st) fun v st₁ _ => ?_
        exact MatchesFrom_exists_liftM _ st₁
      | case k major alts extra c =>
        have hcont : ∀ (mv : Val) (st₁ : St), ∃ B, MatchesFrom
            (do
              let __x ← select P k mv
              let some alt := k.alts[__x.1]? | stuckM
              let some altT := alts[__x.1]? | stuckM
              let r ← applyAlt P ext n env altT (alt.args.toList.map fun fa => match fa with
                | .field i => __x.2[i]?.getD (.imm .irr, false)
                | .irr => (.imm .irr, false)
                | .unit => (.imm .irr, false))
              let __s ← forIn extra.toList ([] : List Val) fun e __s => do
                let __do_lift ← eval P ext n env e
                pure (ForInStep.yield (__s ++ [__do_lift]))
              applyAll P ext n r __s c)
            (do
              let __x ← liftM (select P k mv)
              let some alt := k.alts[__x.1]? | liftM stuckM
              let some altT := alts[__x.1]? | liftM stuckM
              let r ← applyAltS P ext n env altT (alt.args.toList.map fun fa => match fa with
                | .field i => __x.2[i]?.getD (.imm .irr, false)
                | .irr => (.imm .irr, false)
                | .unit => (.imm .irr, false))
              let ex ← evalListS P ext n env extra.toList []
              applyAllS P ext n r ex c) st₁ B := by
          intro mv st₁
          refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (select P k mv) st₁) fun ⟨j, fields⟩ st₂ _ => ?_
          dsimp only
          cases halt : k.alts[j]? with
          | none => exact MatchesFrom_exists_liftM stuckM st₂
          | some alt =>
            cases haltT : alts[j]? with
            | none => exact MatchesFrom_exists_liftM stuckM st₂
            | some altT =>
              dsimp only
              let args := alt.args.toList.map fun fa => match fa with
                | .field i => fields[i]?.getD (.imm .irr, false)
                | .irr => (.imm .irr, false)
                | .unit => (.imm .irr, false)
              refine MatchesFrom_exists_bind (ihAlt env altT args st₂) fun r st₃ _ => ?_
              have hEx : ∃ B, MatchesFrom
                  (forIn (m := M) extra.toList ([] : List Val) (fun e ex =>
                    eval P ext n env e >>= fun v => pure (.yield (ex ++ [v]))))
                  (evalListS P ext n env extra.toList []) st₃ B := by
                obtain ⟨B, hB⟩ := MatchesFrom_evalList P ext n env ihEval extra.toList [] st₃
                refine ⟨B, MatchesFrom_eq_M ?_ hB⟩
                exact (forIn_list_map_eq_listLoopM (fun e => eval P ext n env e) (fun ex v => ex ++ [v]) extra.toList [] st₃).symm
              refine MatchesFrom_exists_bind hEx fun ex st₄ _ => ?_
              exact ihAll r ex c st₄
        cases major with
        | var j mc =>
          dsimp only
          obtain ⟨B, hB⟩ := MatchesFrom_exists_bind (MatchesFrom_exists_liftM
            (match env[j]? with
             | some b =>
               if (b.mode == BinderMode.erased) = true then do
                 violate Violation.erasedRead
                 live b.val
                 let v ← conform mc b.val
                 if b.mode.isUnique = true then transfer P n b.mode.isBorrowed v else pure v
               else do
                 live b.val
                 let v ← conform mc b.val
                 if b.mode.isUnique = true then transfer P n b.mode.isBorrowed v else pure v
             | _ => stuckM) st) (fun mv st₁ _ => hcont mv st₁)
          refine ⟨B, MatchesFrom_eq_M ?_ hB⟩
          cases hlu : env[j]? with
          | none =>
            simp only [M_bind_run]
            rfl
          | some b =>
            cases he : (b.mode == BinderMode.erased) with
            | true =>
              simp only [he, ↓reduceIte, M_bind_run]
              rfl
            | false =>
              simp only [he, Bool.false_eq_true, ↓reduceIte, M_bind_run]
              cases h1 : (live b.val).run st with
              | error e => rfl
              | ok p =>
                cases h2 : (conform mc b.val).run p.2 with
                | error e =>
                  simp only [h2]
                | ok q =>
                  cases b.mode.isUnique with
                  | true =>
                    simp only [↓reduceIte, M_bind_run, h2]
                    cases (transfer P n b.mode.isBorrowed q.1).run q.2 <;> rfl
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte, M_bind_run, M_pure_run, h2]
                    rfl
        | irr | const _ _ | natLit _ | strLit _ | app _ _ _ | lam _ _ _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ =>
          dsimp only
          refine MatchesFrom_exists_bind (ihEval env _ st) fun mv st₁ _ => hcont mv st₁
    · -- spine
      intro env head args c st
      unfold spine spineS
      apply MatchesFrom_exists_spend
      cases head with
      | const r rc =>
        dsimp only
        refine MatchesFrom_exists_bind (MatchesFrom_evalCallArgs P ext n env (P.find? r) ihEval args.zipIdx [] st) fun vs st₁ _ => ?_
        exact ihCall r vs c st₁
      | irr | var _ _ | natLit _ | strLit _ | app _ _ _ | lam _ _ _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ =>
        dsimp only
        refine MatchesFrom_exists_bind (ihEval env _ st) fun f st₁ _ => ?_
        have hArgs : ∃ B, MatchesFrom
            (forIn (m := M) args ([] : List Val) (fun a vs =>
              eval P ext n env a >>= fun v => pure (.yield (vs ++ [v]))))
            (evalListS P ext n env args []) st₁ B := by
          obtain ⟨B, hB⟩ := MatchesFrom_evalList P ext n env ihEval args [] st₁
          refine ⟨B, MatchesFrom_eq_M ?_ hB⟩
          exact (forIn_list_map_eq_listLoopM (fun a => eval P ext n env a) (fun vs v => vs ++ [v]) args [] st₁).symm
        refine MatchesFrom_exists_bind hArgs fun vs st₂ _ => ?_
        exact ihAll f vs c st₂
    · -- callWith
      intro r vs c st
      unfold callWith callWithS
      apply MatchesFrom_exists_spend
      cases P.find? r with
      | none => exact MatchesFrom_exists_liftM stuckM st
      | some d =>
        cases d with
        | body params res rc rs body =>
          by_cases hlt : vs.length < params.size
          · simp only [hlt, ↓reduceIte]
            exact MatchesFrom_exists_liftM _ st
          · simp only [hlt, ↓reduceIte]
            by_cases hz : params.size == 0
            · simp only [hz, ↓reduceIte]
              refine MatchesFrom_exists_bind (ihStatic r body rc st) fun f st₁ _ => ?_
              exact ihAll f (vs.drop params.size) c st₁
            · simp only [hz, Bool.false_eq_true, ↓reduceIte]
              refine MatchesFrom_exists_bind (ihEnter params res rc body (vs.take params.size) st) fun f st₁ _ => ?_
              exact ihAll f (vs.drop params.size) c st₁
        | ctor ind ci nP fields =>
          by_cases h1 : vs.length < nP + fields.size
          · simp only [h1, ↓reduceIte]; exact MatchesFrom_exists_liftM _ st
          · by_cases h2 : vs.length > nP + fields.size
            · simp only [h1, h2, ↓reduceIte]; exact MatchesFrom_exists_liftM _ st
            · simp only [h1, h2, ↓reduceIte]; exact MatchesFrom_exists_liftM _ st
        | prim p =>
          by_cases h1 : vs.length < p.arity
          · simp only [h1, ↓reduceIte]; exact MatchesFrom_exists_liftM _ st
          · by_cases h2 : vs.length > p.arity
            · simp only [h1, h2, ↓reduceIte]; exact MatchesFrom_exists_liftM _ st
            · simp only [h1, h2, ↓reduceIte]; exact MatchesFrom_exists_liftM _ st
        | extern params res rc rs =>
          by_cases hlt : vs.length < params.size
          · simp only [hlt, ↓reduceIte]; exact MatchesFrom_exists_liftM _ st
          · simp only [hlt, ↓reduceIte]
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM _ st) fun f st₁ _ => ?_
            exact ihAll f (vs.drop params.size) c st₁
        | ind cs => exact MatchesFrom_exists_pure (Val.imm .irr) st
        | caseDef _ | stuck _ _ _ _ => exact MatchesFrom_exists_liftM stuckM st
    · -- enter
      intro ps res rc body vs st
      unfold enter enterS
      apply MatchesFrom_exists_spend
      refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM openRegion st) fun sc st₁ _ => ?_
      have hBind : ∃ B, MatchesFrom
          (forIn (m := M) (ps.toList.zip vs) ([] : List Bnd) (fun (p, v) env =>
            bindAt P n sc.1 p.mode p.cls v >>= fun b => pure (.yield (b :: env))))
          (liftM (bindParamsM P n sc.1 (ps.toList.zip vs) [])) st₁ B := by
        obtain ⟨B, hB⟩ := MatchesFrom_exists_liftM (bindParamsM P n sc.1 (ps.toList.zip vs) []) st₁
        refine ⟨B, MatchesFrom_eq_M ?_ hB⟩
        rw [← bindParamsM_eq_listLoopM, ← forIn_list_map_eq_listLoopM]
      refine MatchesFrom_exists_bind hBind fun env st₂ _ => ?_
      refine MatchesFrom_exists_bind (ihEval env body st₂) fun r st₃ _ => ?_
      refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (ret P n sc.1 sc.2 res rc r) st₃) fun r' st₄ _ => ?_
      refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (closeRegion sc.1) st₄) fun _ st₅ _ => ?_
      exact MatchesFrom_exists_pure r' st₅
    · -- static
      intro r body rc st
      unfold static staticS
      apply MatchesFrom_exists_spend
      refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM get st) fun st0 st₁ hget => ?_
      rw [M_get_run] at hget
      cases hget
      cases st.statics.find? (·.1 == r) with
      | some p => exact MatchesFrom_exists_liftM _ st
      | none =>
        refine MatchesFrom_exists_bind (ihEval [] body st) fun v0 st₂ _ => ?_
        refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (conform rc v0) st₂) fun v st₃ _ => ?_
        refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM _ st₃) fun _ st₄ _ => ?_
        exact MatchesFrom_exists_pure v st₄
    · -- applyAll
      intro f vs c st
      cases vs with
      | nil =>
        unfold applyAll applyAllS
        apply MatchesFrom_exists_spend
        exact MatchesFrom_exists_liftM (conform c f) st
      | cons a rest =>
        unfold applyAll applyAllS
        apply MatchesFrom_exists_spend
        refine MatchesFrom_exists_bind (ihOne f a (if rest.isEmpty then c else .val) st) fun g st₁ _ => ?_
        exact ihAll g rest c st₁
    · -- applyOne
      intro f a c st
      unfold applyOne applyOneS
      apply MatchesFrom_exists_spend
      cases f with
      | imm i =>
        cases i with
        | irr => exact MatchesFrom_exists_pure (Val.imm .irr) st
        | con _ | bits _ => exact MatchesFrom_exists_liftM stuckM st
      | ref loc cap t =>
        refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (obj loc) st) fun o st₁ _ => ?_
        cases hcap : (o.cap == cap) with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (violate .revokedUse) st₁) fun _ st₂ hviol => ?_
          cases hviol
        | true =>
          simp only [↓reduceIte]
          cases o.cell with
          | clo env p res rc fvs body =>
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM openRegion st₁) fun sc st₂ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (bindAt P n sc.1 p.mode p.cls a) st₂) fun b st₃ _ => ?_
            refine MatchesFrom_exists_bind (ihEval (b :: env) body st₃) fun r st₄ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (ret P n sc.1 sc.2 res rc r) st₄) fun r' st₅ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (closeRegion sc.1) st₅) fun _ st₆ _ => ?_
            exact MatchesFrom_exists_liftM (conform c r') st₆
          | pap r args => exact ihCall r (args.toList ++ [a]) c st₁
          | once t spent =>
            cases spent with
            | true =>
              simp only [↓reduceIte]
              refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (violate .onceReentry) st₁) fun _ st₂ hviol => ?_
              cases hviol
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (setObj loc { o with cell := .once t true }) st₁) fun _ st₂ _ => ?_
              exact ihOne t a c st₂
          | ctor _ _ | num _ | str _ => exact MatchesFrom_exists_liftM stuckM st₁
    · -- applyAlt
      intro env t args st
      cases args with
      | nil =>
        unfold applyAlt applyAltS
        apply MatchesFrom_exists_spend
        exact ihEval env t st
      | cons hd rest =>
        unfold applyAlt applyAltS
        apply MatchesFrom_exists_spend
        cases t with
        | lam p res rc fvs body =>
          refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM openRegion st) fun sc st₁ _ => ?_
          cases her : hd.2 with
          | true =>
            simp only [↓reduceIte]
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (pure (⟨.imm .irr, .erased⟩ : Bnd)) st₁) fun b st₂ _ => ?_
            refine MatchesFrom_exists_bind (ihAlt (b :: env) body rest st₂) fun r st₃ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (ret P n sc.1 sc.2 res rc r) st₃) fun r' st₄ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (closeRegion sc.1) st₄) fun _ st₅ _ => ?_
            exact MatchesFrom_exists_pure r' st₅
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (bindAt P n sc.1 p.mode p.cls hd.1) st₁) fun b st₂ _ => ?_
            refine MatchesFrom_exists_bind (ihAlt (b :: env) body rest st₂) fun r st₃ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (ret P n sc.1 sc.2 res rc r) st₃) fun r' st₄ _ => ?_
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (closeRegion sc.1) st₄) fun _ st₅ _ => ?_
            exact MatchesFrom_exists_pure r' st₅
        | irr | var _ _ | natLit _ | strLit _ | const _ _ | app _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ =>
          cases hany : ((hd :: rest).any (·.2)) with
          | true =>
            simp only [↓reduceIte]
            refine MatchesFrom_exists_bind (MatchesFrom_exists_liftM (violate .erasedRead) st) fun _ st₁ hviol => ?_
            cases hviol
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine MatchesFrom_exists_bind (ihEval env _ st) fun f st₁ _ => ?_
            exact ihAll f ((hd :: rest).map (·.1)) .val st₁

/-- Adequacy corollary for `runR`: if `enter` hits a violation, `enterS` hits the same violation
at some finite budget `B`. -/
theorem enter_violation_to_enterS {P : Prog} {ext : ExternOracle} {fuel : Nat}
    {ps : Array Param} {res : ResultMode} {rc : Cls} {body : Term} {vs : List Val}
    {st : St} {k : Violation}
    (hv : (enter P ext fuel ps res rc body vs).run st = .error (.violation k)) :
    ∃ B, (enterS P ext fuel ps res rc body vs).run (st, B) = .error (.violation k) := by
  obtain ⟨B, hB⟩ := (eval_matches_evalS P ext fuel).2.2.2.1 ps res rc body vs st
  unfold MatchesFrom at hB
  rw [hv] at hB
  exact ⟨B, by simpa using hB 0⟩

end IxC.Resource.Proof
