import IxC.Resource.Check
import IxC.Resource.Proof.Heap

/-!
# Step-Free Mode Semantics (`ModeOk`)

Defines the step- and depth-free relational abstraction of `IxC.Resource.Check`
(`AState`, `Runs`, `ATerm`, `ACall`, `ALam`, `ACase`, `AAlt`, `BodyOk`,
`LamsClosed`, `CaseFieldsDistinct`, `CtorsIndexed`, `ModeOk`).

* `F5` (`IxC.Resource.Proof.F5`) proves `check lim env s = .accept n fp → ∃ P, Reads lim.oracle env s P ∧ ModeOk P`.
* `F4` (`IxC.Resource.Proof.F4`) proves `ModeOk P → Safe P`.

Because none of `Check.lean`'s non-recursive helpers (`readVar`, `valid`, `flowTo`,
`callResult`, `papVal`, `applyValue`, `bindInner`, `retCheck`, `anCtor`, `anProj`,
`notOnceSrc`, `newBnd`, `openReg`, `closeReg`, `setSt`) reads or decrements
`CSt.steps`, `Runs m σ a σ'` simply runs `m` at `steps := 0`, giving zero
transcription drift between `Check.lean` and `ModeOk.lean`.
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## 1. Step-Free Abstract State & `Runs` -/

/-- Checker state without the step budget `steps`. -/
structure AState where
  st : Array BSt := #[]
  once : Array Bool := #[]
  spent : Array Bool := #[]
  regions : List Nat := [1]
  nextRegion : Nat := 2
  deriving Inhabited

def AState.ofCSt (s : CSt) : AState :=
  { st := s.st, once := s.once, spent := s.spent,
    regions := s.regions, nextRegion := s.nextRegion }

def AState.toCSt (σ : AState) (steps : Nat := 0) : CSt :=
  { st := σ.st, once := σ.once, spent := σ.spent,
    regions := σ.regions, nextRegion := σ.nextRegion, steps := steps }

@[simp] theorem AState.ofCSt_toCSt (σ : AState) (steps : Nat) :
    AState.ofCSt (σ.toCSt steps) = σ := rfl

@[simp] theorem AState.toCSt_ofCSt (s : CSt) :
    (AState.ofCSt s).toCSt s.steps = s := rfl

/-- Step-independent execution of a non-recursive `CM` helper. -/
def Runs {α : Type} (m : CM α) (σ : AState) (a : α) (σ' : AState) : Prop :=
  m.run (σ.toCSt 0) = .ok (a, σ'.toCSt 0)

/-! ### Step-independence helper laws for `CM` (used by `F5`) -/

/-- `m` neither inspects nor mutates `CSt.steps`. -/
def StepIndep {α : Type} (m : CM α) : Prop :=
  ∀ (σ : AState) (k₁ k₂ : Nat),
    (∀ a s₁, m.run (σ.toCSt k₁) = .ok (a, s₁) →
      s₁.steps = k₁ ∧ m.run (σ.toCSt k₂) = .ok (a, (AState.ofCSt s₁).toCSt k₂)) ∧
    (∀ e, m.run (σ.toCSt k₁) = .error e → m.run (σ.toCSt k₂) = .error e)

theorem StepIndep.toRuns {α : Type} {m : CM α} (hi : StepIndep m)
    {s s' : CSt} {a : α} (h : m.run s = .ok (a, s')) :
    Runs m (AState.ofCSt s) a (AState.ofCSt s') := by
  have h1 := (hi (AState.ofCSt s) s.steps 0).1 a s' (by simpa using h)
  exact h1.2

theorem CM_pure_run {α : Type} (a : α) (s : CSt) :
    ((pure a : CM α).run s) = .ok (a, s) := rfl

theorem CM_bind_run {α β : Type} (m : CM α) (f : α → CM β) (s : CSt) :
    ((m >>= f).run s) =
      (match m.run s with
       | Except.ok (a, s') => (f a).run s'
       | Except.error e => Except.error e) := by
  change (m.run s).bind (fun p => (f p.1).run p.2) = _
  cases m.run s <;> rfl

theorem StepIndep.pure {α : Type} (a : α) : StepIndep (pure a : CM α) := by
  intro σ k₁ k₂
  constructor
  · intro b s₁ h; cases h; exact ⟨rfl, rfl⟩
  · intro e h; cases h

theorem StepIndep.throw {α : Type} (e : Halt) : StepIndep (throw e : CM α) := by
  intro σ k₁ k₂
  constructor
  · intro _ _ h; cases h
  · intro _ h; exact h

theorem StepIndep.bind {α β : Type} {m : CM α} {f : α → CM β}
    (hm : StepIndep m) (hf : ∀ a, StepIndep (f a)) : StepIndep (m >>= f) := by
  intro σ k₁ k₂
  constructor
  · intro b s₁ h
    rw [CM_bind_run] at h ⊢
    cases hm1 : m.run (σ.toCSt k₁) with
    | error e => rw [hm1] at h; cases h
    | ok p =>
      rw [hm1] at h
      have ⟨hpSteps, hm2⟩ := (hm σ k₁ k₂).1 p.1 p.2 hm1
      rw [hm2]
      have hfp : (f p.1).run ((AState.ofCSt p.2).toCSt k₁) = .ok (b, s₁) := by
        have hEq : (AState.ofCSt p.2).toCSt k₁ = p.2 := by
          rw [← hpSteps]; exact AState.toCSt_ofCSt p.2
        rw [hEq]; exact h
      exact (hf p.1 (AState.ofCSt p.2) k₁ k₂).1 b s₁ hfp
  · intro e h
    rw [CM_bind_run] at h ⊢
    cases hm1 : m.run (σ.toCSt k₁) with
    | error e' =>
      rw [hm1] at h
      cases h
      rw [(hm σ k₁ k₂).2 e hm1]
    | ok p =>
      rw [hm1] at h
      have ⟨hpSteps, hm2⟩ := (hm σ k₁ k₂).1 p.1 p.2 hm1
      rw [hm2]
      have hfp : (f p.1).run ((AState.ofCSt p.2).toCSt k₁) = .error e := by
        have hEq : (AState.ofCSt p.2).toCSt k₁ = p.2 := by
          rw [← hpSteps]; exact AState.toCSt_ofCSt p.2
        rw [hEq]; exact h
      exact (hf p.1 (AState.ofCSt p.2) k₁ k₂).2 e hfp

/-! ## 2. Structural Well-Formedness of Run Programs -/

/-- Variable `x` occurs free in `t` at binder depth `d` (structural, fuel-free). -/
inductive FreeVarIn : Nat → Term → Nat → Prop
  | var {d i : Nat} {c : Cls} : d ≤ i → FreeVarIn d (.var i c) (i - d)
  | appL {d x : Nat} {f a : Term} {c : Cls} : FreeVarIn d f x → FreeVarIn d (.app f a c) x
  | appR {d x : Nat} {f a : Term} {c : Cls} : FreeVarIn d a x → FreeVarIn d (.app f a c) x
  | lam {d x : Nat} {p : Param} {res : ResultMode} {rc : Cls} {fvs : Array Nat} {b : Term} :
      FreeVarIn (d + 1) b x → FreeVarIn d (.lam p res rc fvs b) x
  | letV {d x : Nat} {m : LetMode} {dc : Cls} {v b : Term} :
      FreeVarIn d v x → FreeVarIn d (.letE m dc v b) x
  | letB {d x : Nat} {m : LetMode} {dc : Cls} {v b : Term} :
      FreeVarIn (d + 1) b x → FreeVarIn d (.letE m dc v b) x
  | proj {d x : Nat} {s : Ref} {i : Nat} {e : Term} {c : Cls} :
      FreeVarIn d e x → FreeVarIn d (.proj s i e c) x
  | caseMj {d x : Nat} {k : CaseInfo} {mj : Term} {alts ex : Array Term} {c : Cls} :
      FreeVarIn d mj x → FreeVarIn d (.case k mj alts ex c) x
  | caseAlt {d x : Nat} {k : CaseInfo} {mj a : Term} {alts ex : Array Term} {c : Cls} :
      a ∈ alts.toList → FreeVarIn d a x → FreeVarIn d (.case k mj alts ex c) x
  | caseEx {d x : Nat} {k : CaseInfo} {mj a : Term} {alts ex : Array Term} {c : Cls} :
      a ∈ ex.toList → FreeVarIn d a x → FreeVarIn d (.case k mj alts ex c) x

/-- Every `.lam` inside `t` names all relevant free variables of its body in `fvs` (structural, fuel-free). -/
inductive LamsClosed : Term → Prop
  | irr : LamsClosed .irr
  | var {i c} : LamsClosed (.var i c)
  | const {r c} : LamsClosed (.const r c)
  | natLit {n} : LamsClosed (.natLit n)
  | strLit {s} : LamsClosed (.strLit s)
  | app {f a c} : LamsClosed f → LamsClosed a → LamsClosed (.app f a c)
  | lam {p res rc fvs b} :
      LamsClosed b → (∀ x, x ∈ fvs.toList ↔ FreeVarIn 1 b x) →
      LamsClosed (.lam p res rc fvs b)
  | letE {m d v b} : LamsClosed v → LamsClosed b → LamsClosed (.letE m d v b)
  | proj {s i e c} : LamsClosed e → LamsClosed (.proj s i e c)
  | case {k mj alts ex c} :
      LamsClosed mj →
      (∀ a ∈ alts.toList, LamsClosed a) →
      (∀ a ∈ ex.toList, LamsClosed a) →
      LamsClosed (.case k mj alts ex c)

/-- Every `.case` inside `t` forwards distinct constructor fields in each alternative (structural). -/
inductive CaseFieldsDistinct : Term → Prop
  | irr : CaseFieldsDistinct .irr
  | var {i c} : CaseFieldsDistinct (.var i c)
  | const {r c} : CaseFieldsDistinct (.const r c)
  | natLit {n} : CaseFieldsDistinct (.natLit n)
  | strLit {s} : CaseFieldsDistinct (.strLit s)
  | app {f a c} : CaseFieldsDistinct f → CaseFieldsDistinct a → CaseFieldsDistinct (.app f a c)
  | lam {p res rc fvs b} : CaseFieldsDistinct b → CaseFieldsDistinct (.lam p res rc fvs b)
  | letE {m d v b} : CaseFieldsDistinct v → CaseFieldsDistinct b → CaseFieldsDistinct (.letE m d v b)
  | proj {s i e c} : CaseFieldsDistinct e → CaseFieldsDistinct (.proj s i e c)
  | case {k mj alts ex c} :
      (∀ ca ∈ k.alts.toList, ∀ (i₁ i₂ q : Nat),
        ca.args[i₁]? = some (FieldArg.field q) → ca.args[i₂]? = some (FieldArg.field q) → i₁ = i₂) →
      CaseFieldsDistinct mj →
      (∀ a ∈ alts.toList, CaseFieldsDistinct a) →
      (∀ a ∈ ex.toList, CaseFieldsDistinct a) →
      CaseFieldsDistinct (.case k mj alts ex c)

/-- Every constructor in `P` appears at its constructor index in its inductive's constructor array. -/
def CtorsIndexed (P : Prog) : Prop :=
  ∀ r ind cidx nP fs, P.ctorOf? r = some (ind, cidx, nP, fs) → (P.ctorsOf ind)[cidx]? = some r

/-! ## 3. Abstract Join & Parameter/Loop Predicates -/

/-- Lattice order on binding states: `live ≤ shared ≤ dead`. -/
def BSt.le : BSt → BSt → Prop
  | .live, _ => True
  | .shared, .shared => True
  | .shared, .dead => True
  | .dead, .dead => True
  | _, _ => False

theorem BSt.le_refl : ∀ b, BSt.le b b
  | .live | .shared | .dead => trivial

theorem BSt.le_trans {a b c : BSt} (h1 : BSt.le a b) (h2 : BSt.le b c) : BSt.le a c := by
  cases a <;> cases b <;> cases c <;> simp [BSt.le] at h1 h2 ⊢

/-- `σ_join` soundly over-approximates `post` on all bindings of `pre`. -/
def StateJoinGe (pre post σ_join : AState) : Prop :=
  σ_join.st.size = pre.st.size ∧
  σ_join.once = pre.once ∧
  σ_join.spent.size = pre.spent.size ∧
  σ_join.regions = pre.regions ∧
  post.nextRegion ≤ σ_join.nextRegion ∧
  (∀ i, i < pre.st.size →
    match post.st[i]?, σ_join.st[i]? with
    | some bp, some bj => BSt.le bp bj
    | _, _ => False) ∧
  (∀ i, i < pre.spent.size → post.spent[i]? = some true → σ_join.spent[i]? = some true)

/-- `r_join` soundly over-approximates alt result `r_j` (filtered to bindings `< preSize`). -/
def ValJoinGe (preSize : Nat) (r_j r_join : AVal) : Prop :=
  r_j.skel.admits r_join.skel = true ∧
  (r_join.own = .uniq → r_j.own = .uniq) ∧
  (∀ d ∈ r_j.deps, d < preSize → d ∈ r_join.deps) ∧
  (∀ reg ∈ r_j.regs, reg ∈ r_join.regs) ∧
  (r_j.onceOnly = true → r_join.onceOnly = true)

/-- Abstract evaluation of a primitive's arguments (matching `anCall`'s `.prim` loop). -/
inductive APrimArgs :
    List (Option AVal) → AState → List Nat → List Nat → List Nat → List Nat → AState → Prop
  | nil {σ deps regs} : APrimArgs [] σ deps regs deps regs σ
  | consNone {rest σ deps₀ regs₀ deps regs σ'} :
      APrimArgs rest σ deps₀ regs₀ deps regs σ' →
      APrimArgs (none :: rest) σ deps₀ regs₀ deps regs σ'
  | consNonVal {a rest σ σ₁ deps₀ regs₀ deps regs σ'} :
      a.cls ≠ .val →
      Runs (valid a "a primitive's argument") σ () σ₁ →
      APrimArgs rest σ₁ deps₀ regs₀ deps regs σ' →
      APrimArgs (some a :: rest) σ deps₀ regs₀ deps regs σ'
  | consVal {a rest σ σ₁ deps₀ regs₀ deps regs σ'} :
      a.cls = .val →
      Runs (flowTo .share .unknown a "a primitive's argument") σ () σ₁ →
      APrimArgs rest σ₁ (natUnion deps₀ a.deps) (natUnion regs₀ a.regs) deps regs σ' →
      APrimArgs (some a :: rest) σ deps₀ regs₀ deps regs σ'

/-- Abstract capture loop of `anLam`: transfers unique captures and shares others
(matching `anLam`'s `for i in fvs.toList` loop with accumulators `deps₀`, `regs₀`, `owned₀`). -/
inductive ACaps (env : List ABnd) :
    List Nat → AState → List Nat → List Nat → List Nat → List Nat → List Nat → List Nat → AState → Prop
  | nil {σ deps regs owned} : ACaps env [] σ deps regs owned deps regs owned σ
  | consUniq {i rest b v σ σ₁ σ₂ deps₀ regs₀ owned₀ deps regs owned σ'} :
      env[i]? = some b →
      Runs (readVar env i) σ v σ₁ →
      captureTransfers b.mode = true →
      Runs (flowTo (.uniq b.mode.isBorrowed) v.skel v "a capture") σ₁ () σ₂ →
      ACaps env rest σ₂ deps₀ (natUnion regs₀ v.regs) (b.id :: owned₀) deps regs owned σ' →
      ACaps env (i :: rest) σ deps₀ regs₀ owned₀ deps regs owned σ'
  | consShare {i rest b v σ σ₁ σ₂ deps₀ regs₀ owned₀ deps regs owned σ'} :
      env[i]? = some b →
      Runs (readVar env i) σ v σ₁ →
      captureTransfers b.mode = false →
      Runs (flowTo .share v.skel v "a capture") σ₁ () σ₂ →
      ACaps env rest σ₂ (natUnion deps₀ v.deps) (natUnion regs₀ v.regs) owned₀ deps regs owned σ' →
      ACaps env (i :: rest) σ deps₀ regs₀ owned₀ deps regs owned σ'

/-- Restore a list of unique capture binding ids to `BSt.live` inside a closure body. -/
def restoreOwned (owned : List Nat) (σ : AState) : AState :=
  { σ with st := owned.foldl (fun arr x => arr.set! x BSt.live) σ.st }

/-- Open a fresh region in `AState` (matching `Check.openReg`). -/
def AState.openReg (σ : AState) : Nat × AState :=
  (σ.nextRegion, { σ with nextRegion := σ.nextRegion + 1, regions := σ.nextRegion :: σ.regions })

/-- Close region `s` in `AState` (matching `Check.closeReg`). -/
def AState.closeReg (s : Nat) (σ : AState) : AState :=
  { σ with regions := σ.regions.filter (· != s) }

/-- Push a new abstract binding into `AState` (matching `Check.newBnd`). -/
def AState.pushBnd (v : AVal) (isOnce : Bool) (σ : AState) : Nat × AState :=
  (σ.st.size, {
    σ with
    st := σ.st.push (if v.own == Own.uniq then BSt.live else BSt.shared)
    once := σ.once.push isOnce
    spent := σ.spent.push false
  })

/-- Compute the result `AVal` leaving a case alternative `.lam` after closing region `s`
(renaming `s` to `inner` when `res.isBorrowed`, mirroring `ret`'s `renameTaint`, and clearing
`deps`/`src` when `res.isUnique && rc == .val` per Bug #11). -/
def altRetVal (res : ResultMode) (rc : Cls) (s inner : Nat) (r : AVal) : AVal :=
  let regs :=
    if rc == .irr || rc == .imm || rc == .leaf then []
    else if res.isBorrowed && r.regs.contains s then
      natUnion (r.regs.filter (· != s)) [inner]
    else r.regs.filter (· != s)
  let deps := if res.isUnique && rc == .val then [] else r.deps
  let src := if res.isUnique && rc == .val then none else r.src
  { r with cls := rc, deps, regs, src }

/-- Compute the field argument list for alternative `j` of a `Term.case` (matching `anCase`). -/
def caseAltArgs (P : Prog) (k : CaseInfo) (mv : AVal) (consuming : Bool) (j : Nat)
    (ca : CaseAlt) : List (AVal × Bool × Bool) :=
  let ctors := P.ctorsOf k.ind
  let fields : Array Field := match ctors[j]? with
    | some ctor => match P.ctorOf? ctor with
      | some (_, _, _, fs) => fs
      | none => #[]
    | none => #[]
  ca.args.toList.map fun fa => match fa with
    | .field i => caseField P k fields mv consuming i
    | .irr => (({ cls := .irr } : AVal), false, false)
    | .unit => (({ cls := .imm } : AVal), false, false)

/-- Initialize abstract environment and state for a run body's parameters (matching `anDef`). -/
def initBody (params : Array Param) : List ABnd × AState :=
  let s0 : AState := { regions := [2, 1], nextRegion := 3 }
  params.foldl (init := ([], s0)) fun (env, σ) p =>
    let v := paramVal p 2
    let (id, σ') := σ.pushBnd v (p.mode.usage == .once)
    ({ id, mode := p.mode, val := v } :: env, σ')

/-- Iterated `applyValue` over a list of evaluated extra arguments (last at class `c`, earlier at `.val`). -/
inductive AApps : AVal → List AVal → Cls → AState → AVal → AState → Prop
  | nil {f c σ} : AApps f [] c σ { f with cls := c } σ
  | consLast {f a c σ g σ'} :
      Runs (applyValue f a c "an application") σ g σ' →
      AApps f [a] c σ { g with cls := c } σ'
  | consMore {f a a2 rest c σ g σ₁ r σ'} :
      Runs (applyValue f a .val "an application") σ g σ₁ →
      AApps g (a2 :: rest) c σ₁ r σ' →
      AApps f (a :: a2 :: rest) c σ r σ'

/-! ## 4. Main Step-Free Abstract Evaluation Relations -/

mutual

/-- Step-free abstract evaluation of a term (matching `anTerm`). -/
inductive ATerm (P : Prog) : List ABnd → Term → AState → AVal → AState → Prop
  | irr {env σ} :
      ATerm P env .irr σ { cls := .irr } σ
  | var {env i c σ v σ'} :
      Runs (readVar env i) σ v σ' →
      ATerm P env (.var i c) σ { v with cls := c } σ'
  | natLit {env n σ} :
      ATerm P env (.natLit n) σ { cls := natClass } σ
  | strLit {env s σ} :
      ATerm P env (.strLit s) σ { cls := .val, skel := .data } σ
  | constCall {env r c σ res σ'} :
      ACall P env r [] c σ res σ' →
      ATerm P env (.const r c) σ res σ'
  | appConst {env f a c r rc args σ res σ'} :
      termSpine (.app f a c) = (.const r rc, args) →
      ACall P env r args.toList c σ res σ' →
      ATerm P env (.app f a c) σ res σ'
  | appVal {env f a c h args σ fv σ₁ avs σ₂ res σ₃} :
      termSpine (.app f a c) = (h, args) →
      (∀ r rc, h ≠ .const r rc) →
      ATerm P env h σ fv σ₁ →
      AEvals P env args.toList σ₁ avs σ₂ →
      AApps fv avs c σ₂ res σ₃ →
      ATerm P env (.app f a c) σ res σ₃
  | lam {env p res rc fvs body σ deps regs owned σ₁ σ_body r_body σ_ret σ_end consumed} :
      ACaps env fvs.toList σ [] [] [] deps regs owned σ₁ →
      ATerm P
        ({ id := (restoreOwned owned σ₁).openReg.2.st.size,
           mode := p.mode,
           val := paramVal p (restoreOwned owned σ₁).openReg.1 } :: env)
        body
        ((restoreOwned owned σ₁).openReg.2.pushBnd
          (paramVal p (restoreOwned owned σ₁).openReg.1) (p.mode.usage == .once)).2
        r_body σ_body →
      Runs (retCheck r_body.skel res (restoreOwned owned σ₁).openReg.1
        { r_body with cls := rc } "a closure's result") σ_body () σ_ret →
      (∀ x ∈ owned, σ_ret.st[x]?.getD .dead = .dead → consumed = true) →
      σ_end = { σ₁ with nextRegion := σ_ret.nextRegion } →
      ATerm P env (.lam p res rc fvs body) σ
        { cls := .val, deps, regs, onceOnly := consumed, skel := .arrow p.mode p.skel res r_body.skel }
        σ_end
  | letErased {env d v b σ res σ'} :
      ATerm P ({ id := σ.st.size, mode := .erased, val := { cls := .irr } } :: env)
        b (σ.pushBnd { cls := .irr } false).2 res σ' →
      ATerm P env (.letE (.value .erased) d v b) σ res σ'
  | letVal {env m d v b σ x σ₁ bv σ₂ r σ₃ σ₄} :
      m ≠ .value .erased →
      ATerm P env v σ x σ₁ →
      Runs (bindInner m.binderMode d x σ₁.openReg.1 "a let") σ₁.openReg.2 bv σ₂ →
      ATerm P ({ id := σ₂.st.size, mode := m.binderMode, val := bv } :: env)
        b (σ₂.pushBnd bv (m.binderMode.usage == .once)).2 r σ₃ →
      Runs (valid r "a let's value") σ₃ () σ₄ →
      ¬ (σ₁.openReg.1 ∈ r.regs) →
      ATerm P env (.letE m d v b) σ r (σ₄.closeReg σ₁.openReg.1)
  | proj {env s i e c σ v σ₁ σ₂ res σ₃} :
      ATerm P env e σ v σ₁ →
      Runs (valid v "a projection") σ₁ () σ₂ →
      Runs (anProj P s i v c) σ₂ res σ₃ →
      ATerm P env (.proj s i e c) σ res σ₃
  | caseTerm {env k mj alts ex c σ mv consuming pre r_join σ_join avs σ_ex res σ_end} :
      alts.size = k.alts.size →
      AMajor P env mj σ mv consuming pre →
      AAlts P env k mv consuming pre 0 k.alts.toList alts.toList r_join σ_join →
      (k.alts.size = 0 →
        σ_join.st = pre.st ∧ σ_join.once = pre.once ∧
        σ_join.spent = pre.spent ∧ σ_join.regions = pre.regions ∧
        pre.nextRegion ≤ σ_join.nextRegion) →
      r_join.cls = c →
      r_join.src = none →
      r_join.onceOnly = false →
      (∀ d ∈ r_join.deps, d < pre.st.size) →
      (∀ reg ∈ r_join.regs, reg < σ_join.nextRegion) →
      AEvals P env ex.toList σ_join avs σ_ex →
      AApps r_join avs c σ_ex res σ_end →
      ATerm P env (.case k mj alts ex c) σ res σ_end

/-- Abstract evaluation of every alternative of a `Term.case`, joined into `(r_join, σ_join)`
(including Bug #10 `r_j.onceOnly = false` and Bug #11 `valid`/`isUniq` own-demotion before
filtering local deps `≥ pre.st.size`). -/
inductive AAlts (P : Prog) :
    List ABnd → CaseInfo → AVal → Bool → AState → Nat →
    List CaseAlt → List Term → AVal → AState → Prop
  | nil {env k mv consuming pre j r_join σ_join} :
      AAlts P env k mv consuming pre j [] [] r_join σ_join
  | cons {env k mv consuming pre j ca cas altT altTs r_join σ_join
          nextReg_j r_j post_j σ_chk_j σ_val_j uniq_j σ_u_j} :
      pre.nextRegion ≤ nextReg_j →
      AAlt P env altT (caseAltArgs P k mv consuming j ca) { pre with nextRegion := nextReg_j } r_j post_j →
      Runs (notOnceSrc r_j "a case alternative's result") post_j () σ_chk_j →
      r_j.onceOnly = false →
      Runs (valid r_j "a case alternative's result") σ_chk_j () σ_val_j →
      Runs (isUniq r_j) σ_val_j uniq_j σ_u_j →
      StateJoinGe pre σ_u_j σ_join →
      ValJoinGe pre.st.size
        { r_j with own := if r_j.own == Own.uniq && uniq_j then Own.uniq else Own.shared }
        r_join →
      AAlts P env k mv consuming pre (j + 1) cas altTs r_join σ_join →
      AAlts P env k mv consuming pre j (ca :: cas) (altT :: altTs) r_join σ_join

/-- Abstract evaluation of a list of plain arguments left-to-right. -/
inductive AEvals (P : Prog) : List ABnd → List Term → AState → List AVal → AState → Prop
  | nil {env σ} : AEvals P env [] σ [] σ
  | cons {env t rest σ v σ₁ vs σ₂} :
      ATerm P env t σ v σ₁ →
      AEvals P env rest σ₁ vs σ₂ →
      AEvals P env (t :: rest) σ (v :: vs) σ₂

/-- Abstract evaluation of a constant call's argument list (skipping erased positions). -/
inductive ACallArgs (P : Prog) :
    Option RunDef → List ABnd → Nat → List Term → AState → List (Option AVal) → AState → Prop
  | nil {d? env idx σ} : ACallArgs P d? env idx [] σ [] σ
  | consSkip {d? env idx t rest σ avs σ'} :
      (match d? with | some d => erasedAt d idx | none => false) = true →
      ACallArgs P d? env (idx + 1) rest σ avs σ' →
      ACallArgs P d? env idx (t :: rest) σ (none :: avs) σ'
  | consEval {d? env idx t rest σ v σ₁ avs σ₂} :
      (match d? with | some d => erasedAt d idx | none => false) = false →
      ATerm P env t σ v σ₁ →
      ACallArgs P d? env (idx + 1) rest σ₁ avs σ₂ →
      ACallArgs P d? env idx (t :: rest) σ (some v :: avs) σ₂

/-- Abstract evaluation of a constant call (matching `anCall`). -/
inductive ACall (P : Prog) :
    List ABnd → Ref → List Term → Cls → AState → AVal → AState → Prop
  | ind {env r cs args c σ avs σ₁} :
      P.find? r = some (.ind cs) →
      ACallArgs P (some (.ind cs)) env 0 args σ avs σ₁ →
      ACall P env r args c σ { cls := .irr } σ₁
  | ctor {env r ind ci nP fields args c σ avs σ₁ res σ₂} :
      P.find? r = some (.ctor ind ci nP fields) →
      ACallArgs P (some (.ctor ind ci nP fields)) env 0 args σ avs σ₁ →
      Runs (anCtor nP fields avs.toArray c) σ₁ res σ₂ →
      ACall P env r args c σ res σ₂
  | prim {env r p args c σ avs σ₁ deps regs σ₂} :
      P.find? r = some (.prim p) →
      ACallArgs P (some (.prim p)) env 0 args σ avs σ₁ →
      APrimArgs avs σ₁ [] [] deps regs σ₂ →
      ACall P env r args c σ
        (if avs.length < p.arity then { cls := .val, deps, regs, skel := .unknown } else { cls := c })
        σ₂
  | ifacePap {env r d ifc args c σ avs σ₁ res σ₂} :
      P.find? r = some d →
      ifaceOf? d = some ifc →
      ACallArgs P (some d) env 0 args σ avs σ₁ →
      avs.length < ifc.params.size →
      Runs (papVal ifc avs.toArray "a partial application") σ₁ res σ₂ →
      ACall P env r args c σ res σ₂
  | ifaceFullZero {env r d ifc args c σ avs σ₁ res σ₂} :
      P.find? r = some d →
      ifaceOf? d = some ifc →
      ACallArgs P (some d) env 0 args σ avs σ₁ →
      ifc.params.size = 0 →
      AApps { cls := ifc.resCls, skel := ifc.resSkel } (avs.filterMap id) c σ₁ res σ₂ →
      ACall P env r args c σ res σ₂
  | ifaceFullPos {env r d ifc args c σ avs σ₁ r0 σ₂ res σ₃} :
      P.find? r = some d →
      ifaceOf? d = some ifc →
      ACallArgs P (some d) env 0 args σ avs σ₁ →
      0 < ifc.params.size →
      ifc.params.size ≤ avs.length →
      Runs (callResult ifc (avs.toArray.extract 0 ifc.params.size) "a call") σ₁ r0 σ₂ →
      AApps r0 ((avs.drop ifc.params.size).filterMap id) c σ₂ res σ₃ →
      ACall P env r args c σ res σ₃

/-- Abstract evaluation of the major premise of a `Term.case` (matching `anCase`). -/
inductive AMajor (P : Prog) :
    List ABnd → Term → AState → AVal → Bool → AState → Prop
  | varConsuming {env j mc b σ v σ₁ σ₂} :
      env[j]? = some b →
      Runs (readVar env j) σ v σ₁ →
      b.mode.isUnique = true →
      mc = .val →
      Runs (flowTo (.uniq b.mode.isBorrowed) v.skel v "a consuming match") σ₁ () σ₂ →
      AMajor P env (.var j mc) σ { v with own := .uniq, deps := [], cls := mc, src := none } true σ₂
  | varPlain {env j mc b σ v σ₁} :
      env[j]? = some b →
      Runs (readVar env j) σ v σ₁ →
      (b.mode.isUnique = false ∨ mc ≠ .val) →
      AMajor P env (.var j mc) σ { v with cls := mc } false σ₁
  | nonVar {env t σ v σ₁} :
      (∀ j mc, t ≠ .var j mc) →
      ATerm P env t σ v σ₁ →
      AMajor P env t σ v false σ₁

/-- Abstract evaluation of a case alternative applied to its field arguments (matching `anAlt`). -/
inductive AAlt (P : Prog) :
    List ABnd → Term → List (AVal × Bool × Bool) → AState → AVal → AState → Prop
  | nil {env t σ r σ'} :
      ATerm P env t σ r σ' →
      AAlt P env t [] σ r σ'
  | lamErased {env p res rc fvs body a0 fromCell rest σ r σ₁ σ₂} :
      AAlt P ({ id := σ.openReg.2.st.size, mode := .erased, val := { cls := .irr } } :: env)
        body rest (σ.openReg.2.pushBnd { cls := .irr } false).2 r σ₁ →
      Runs (retCheck r.skel res σ.openReg.1 { r with cls := rc } "a case alternative") σ₁ () σ₂ →
      AAlt P env (.lam p res rc fvs body) ((a0, true, fromCell) :: rest) σ
        (altRetVal res rc σ.openReg.1 ((σ₂.closeReg σ.openReg.1).regions.headD 1) r)
        (σ₂.closeReg σ.openReg.1)
  | lamKept {env p res rc fvs body a0 fromCell rest σ bv σ₁ r σ₂ σ₃} :
      p.skel.admits (if fromCell && p.cls != .val then { a0 with deps := [], regs := [] } else a0).skel = true →
      Runs (bindInner p.mode p.cls
        (if fromCell && p.cls != .val then { a0 with deps := [], regs := [] } else a0)
        σ.openReg.1 "a case field's binder") σ.openReg.2 bv σ₁ →
      AAlt P ({ id := σ₁.st.size, mode := p.mode, val := bv } :: env)
        body rest (σ₁.pushBnd bv (p.mode.usage == .once)).2 r σ₂ →
      Runs (retCheck r.skel res σ.openReg.1 { r with cls := rc } "a case alternative") σ₂ () σ₃ →
      AAlt P env (.lam p res rc fvs body) ((a0, false, fromCell) :: rest) σ
        (altRetVal res rc σ.openReg.1 ((σ₃.closeReg σ.openReg.1).regions.headD 1) r)
        (σ₃.closeReg σ.openReg.1)
  | nonLam {env t a0 er fromCell rest σ f σ₁ res σ₂} :
      (∀ p res rc fvs body, t ≠ .lam p res rc fvs body) →
      ((a0, er, fromCell) :: rest).any (·.2.1) = false →
      ATerm P env t σ f σ₁ →
      AApps f (((a0, er, fromCell) :: rest).map (·.1)) .val σ₁ res σ₂ →
      AAlt P env t ((a0, er, fromCell) :: rest) σ res σ₂

end

/-! ## 5. `BodyOk`, `DefaultBodyOk`, `ModeOk`, and `Safe` -/

/-- A `RunDef` has an all-default calling interface (all params `.many` with default skeletons,
result `.shared` with default skeleton, or constructor fields all `.many`/`.inherited`). -/
def DefaultIface : RunDef → Prop
  | .body ps res _ rs _ =>
      (∀ p ∈ ps.toList, p.mode = .many ∧ p.skel.isDefault = true) ∧
      res = .shared ∧ rs.isDefault = true
  | .extern ps res _ rs =>
      (∀ p ∈ ps.toList, p.mode = .many ∧ p.skel.isDefault = true) ∧
      res = .shared ∧ rs.isDefault = true
  | .stuck ps res _ rs =>
      (∀ p ∈ ps.toList, p.mode = .many ∧ p.skel.isDefault = true) ∧
      res = .shared ∧ rs.isDefault = true
  | .ctor _ _ _ fs =>
      ∀ f ∈ fs.toList, f.mode = .many ∧ f.fmode = .inherited
  | .ind _ | .caseDef _ | .prim _ => True

/-- A run term carrying only default modes whose referenced constants, projected structures,
and matched inductives all have default interfaces in `P`. -/
inductive DefaultTerm (P : Prog) : Term → Prop
  | irr : DefaultTerm P .irr
  | var {i c} : DefaultTerm P (.var i c)
  | natLit {n} : DefaultTerm P (.natLit n)
  | strLit {s} : DefaultTerm P (.strLit s)
  | const {r c} :
      (∀ d, P.find? r = some d → DefaultIface d) →
      DefaultTerm P (.const r c)
  | app {f a c} :
      DefaultTerm P f → DefaultTerm P a → DefaultTerm P (.app f a c)
  | lam {p res rc fvs b} :
      p.mode = .many → res = .shared → DefaultTerm P b →
      DefaultTerm P (.lam p res rc fvs b)
  | letE {d v b} :
      DefaultTerm P v → DefaultTerm P b → DefaultTerm P (.letE (.value .many) d v b)
  | proj {s i e c} :
      (∀ ctor ∈ (P.ctorsOf s).toList, ∀ ind ci nP fs,
        P.ctorOf? ctor = some (ind, ci, nP, fs) →
        ∀ f ∈ fs.toList, f.mode = .many ∧ f.fmode = .inherited) →
      DefaultTerm P e → DefaultTerm P (.proj s i e c)
  | case {k mj alts ex c} :
      (∀ ctor ∈ (P.ctorsOf k.ind).toList, ∀ ind ci nP fs,
        P.ctorOf? ctor = some (ind, ci, nP, fs) →
        ∀ f ∈ fs.toList, f.mode = .many ∧ f.fmode = .inherited) →
      DefaultTerm P mj →
      (∀ a ∈ alts.toList, DefaultTerm P a) →
      (∀ e ∈ ex.toList, DefaultTerm P e) →
      DefaultTerm P (.case k mj alts ex c)

/-- An unchecked default-mode body (skipped on `check`'s slow path when its record and
every constant/structure/inductive it touches carry only default modes). -/
def DefaultBodyOk (P : Prog) (params : Array Param) (res : ResultMode) (rs : Skel)
    (body : Term) : Prop :=
  (∀ p ∈ params.toList, p.mode = .many ∧ p.skel.isDefault = true) ∧
  res = .shared ∧
  rs.isDefault = true ∧
  DefaultTerm P body

/-- A run body has a step-free mode derivation matching `anDef`. -/
def BodyOk (P : Prog) (params : Array Param) (res : ResultMode) (rc : Cls) (rs : Skel)
    (body : Term) : Prop :=
  (0 < params.size ∨ res = .shared) ∧
  ∃ r σ₁ σ₂,
    ATerm P (initBody params).1 body (initBody params).2 r σ₁ ∧
    Runs (retCheck rs res 2 { r with cls := rc } "the result") σ₁ () σ₂

/-- Complete step-free soundness certificate for a run program `P`. -/
def ModeOk (P : Prog) : Prop :=
  CtorsIndexed P ∧
  ∀ r params res rc rs body, P.find? r = some (.body params res rc rs body) →
    LamsClosed body ∧
    CaseFieldsDistinct body ∧
    (BodyOk P params res rc rs body ∨ DefaultBodyOk P params res rs body)

/-- Program-level mode safety (matching `ModeSafe`'s second conjunct over all bodies of `P`). -/
def Safe (P : Prog) : Prop :=
  ∀ r params res rc rs t, P.find? r = some (.body params res rc rs t) →
  ∀ ext, ExternOk P ext →
  ∀ h args, InputsOk P h params args →
  ∀ fuel k, runR P ext fuel r h args ≠ .violation k

/-! ## 6. Structural Helpers on `AAlts` and `AState` -/

/-- Well-formedness of an abstract state `σ`: synchronized array sizes and bounded, duplicate-free regions. -/
def AStateOk (σ : AState) : Prop :=
  σ.st.size = σ.once.size ∧
  σ.st.size = σ.spent.size ∧
  2 ≤ σ.nextRegion ∧
  1 ∈ σ.regions ∧
  σ.regions.Nodup ∧
  (∀ r ∈ σ.regions, 1 ≤ r ∧ r < σ.nextRegion)

/-- Monotonicity of `AState` transitions: arrays only grow, `once` is unchanged on old ids,
`st` moves only upward in `BSt.le`, `spent` moves only `false → true`, and `nextRegion` grows. -/
def AStateLe (σ₁ σ₂ : AState) : Prop :=
  σ₁.st.size ≤ σ₂.st.size ∧
  σ₁.nextRegion ≤ σ₂.nextRegion ∧
  (∀ i, i < σ₁.st.size →
    match σ₁.st[i]?, σ₂.st[i]? with
    | some b₁, some b₂ => BSt.le b₁ b₂
    | _, _ => False) ∧
  (∀ i, i < σ₁.once.size → σ₂.once[i]? = σ₁.once[i]?) ∧
  (∀ i, i < σ₁.spent.size → σ₁.spent[i]? = some true → σ₂.spent[i]? = some true)

theorem AStateLe.refl (σ : AState) : AStateLe σ σ := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, fun _ _ => rfl, fun _ _ h => h⟩
  intro i hi
  rw [Array.getElem?_eq_getElem hi]
  exact BSt.le_refl _

theorem AStateLe.trans {σ₁ σ₂ σ₃ : AState} (h12 : AStateLe σ₁ σ₂) (h23 : AStateLe σ₂ σ₃) :
    AStateLe σ₁ σ₃ := by
  obtain ⟨hsz12, hnr12, hst12, honce12, hsp12⟩ := h12
  obtain ⟨hsz23, hnr23, hst23, honce23, hsp23⟩ := h23
  refine ⟨Nat.le_trans hsz12 hsz23, Nat.le_trans hnr12 hnr23, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := hst12 i hi
    have hi2 : i < σ₂.st.size := Nat.lt_of_lt_of_le hi hsz12
    have h2 := hst23 i hi2
    rw [Array.getElem?_eq_getElem hi] at h1 ⊢
    rw [Array.getElem?_eq_getElem hi2] at h1 h2
    cases h3 : σ₃.st[i]? with
    | none => rw [h3] at h2; cases h2
    | some b3 => rw [h3] at h2; exact BSt.le_trans h1 h2
  · intro i hi
    have hEq := honce12 i hi
    have hi2 : i < σ₂.once.size := by
      have : σ₂.once[i]? = some σ₁.once[i] := by rw [hEq, Array.getElem?_eq_getElem hi]
      exact (Array.getElem?_eq_some_iff.mp this).1
    rw [honce23 i hi2, hEq]
  · intro i hi hsp
    have hsp2 := hsp12 i hi hsp
    have hi2 : i < σ₂.spent.size := (Array.getElem?_eq_some_iff.mp hsp2).1
    exact hsp23 i hi2 hsp2

/-- Extract the `idx`-th alternative derivation from `AAlts`. -/
theorem AAlts_get {P : Prog} {env : List ABnd} {k : CaseInfo} {mv : AVal} {consuming : Bool}
    {pre : AState} {r_join : AVal} {σ_join : AState} :
    ∀ {j : Nat} {cas : List CaseAlt} {altTs : List Term},
      AAlts P env k mv consuming pre j cas altTs r_join σ_join →
      ∀ {idx : Nat} {ca : CaseAlt} {altT : Term},
        cas[idx]? = some ca → altTs[idx]? = some altT →
        ∃ nextReg r_j post_j σ_chk_j σ_val_j uniq_j σ_u_j,
          pre.nextRegion ≤ nextReg ∧
          AAlt P env altT (caseAltArgs P k mv consuming (j + idx) ca)
            { pre with nextRegion := nextReg } r_j post_j ∧
          Runs (notOnceSrc r_j "a case alternative's result") post_j () σ_chk_j ∧
          r_j.onceOnly = false ∧
          Runs (valid r_j "a case alternative's result") σ_chk_j () σ_val_j ∧
          Runs (isUniq r_j) σ_val_j uniq_j σ_u_j ∧
          StateJoinGe pre σ_u_j σ_join ∧
          ValJoinGe pre.st.size
            { r_j with own := if r_j.own == Own.uniq && uniq_j then Own.uniq else Own.shared }
            r_join
  | _, _, _, .nil, _, _, _, hca, _ => by cases hca
  | j, _ :: cas, _ :: altTs, .cons hnr halt hno ho hval huniq hsj hvj hrest, 0, ca, altT, hca, haltT => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hca haltT
    subst hca; subst haltT
    exact ⟨_, _, _, _, _, _, _, hnr, halt, hno, ho, hval, huniq, hsj, hvj⟩
  | j, _ :: cas, _ :: altTs, .cons _ _ _ _ _ _ _ _ hrest, idx + 1, ca, altT, hca, haltT => by
    simp only [List.getElem?_cons_succ] at hca haltT
    have h := AAlts_get hrest hca haltT
    have heq : j + 1 + idx = j + (idx + 1) := by omega
    rw [heq] at h
    exact h

theorem AStateOk.openReg {σ : AState} (hok : AStateOk σ) :
    AStateOk σ.openReg.2 ∧ σ.openReg.1 = σ.nextRegion ∧ ¬ (σ.openReg.1 ∈ σ.regions) := by
  obtain ⟨h1, h2, hnr, h1in, hnd, hlt⟩ := hok
  have hnot : ¬ (σ.nextRegion ∈ σ.regions) := fun hm =>
    Nat.lt_irrefl _ (hlt _ hm).2
  refine ⟨⟨h1, h2, by dsimp [AState.openReg]; omega, List.mem_cons_of_mem _ h1in,
    List.nodup_cons.mpr ⟨hnot, hnd⟩, ?_⟩, rfl, hnot⟩
  intro r hr
  dsimp [AState.openReg] at hr ⊢
  rcases List.mem_cons.mp hr with rfl | hr'
  · exact ⟨by omega, by omega⟩
  · have := hlt r hr'; exact ⟨this.1, by omega⟩

theorem AStateOk.pushBnd {σ : AState} (hok : AStateOk σ) (v : AVal) (isOnce : Bool) :
    AStateOk (σ.pushBnd v isOnce).2 ∧ AStateLe σ (σ.pushBnd v isOnce).2 := by
  obtain ⟨h1, h2, hnr, h1in, hnd, hlt⟩ := hok
  refine ⟨⟨by simp [AState.pushBnd, h1], by simp [AState.pushBnd, h2], hnr, h1in, hnd, hlt⟩, ?_⟩
  refine ⟨by simp [AState.pushBnd], Nat.le_refl _, ?_, ?_, ?_⟩
  · intro i hi
    simp only [AState.pushBnd]
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_push_lt hi]
    exact BSt.le_refl _
  · intro i hi
    simp only [AState.pushBnd]
    rw [Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]
  · intro i hi hsp
    simp only [AState.pushBnd]
    rw [Array.getElem?_push_lt hi]
    rwa [Array.getElem?_eq_getElem hi] at hsp

theorem AStateOk.closeReg {σ : AState} {s : Nat} (hok : AStateOk σ) (hs : s ≠ 1) :
    AStateOk (σ.closeReg s) := by
  obtain ⟨h1, h2, hnr, h1in, hnd, hlt⟩ := hok
  refine ⟨h1, h2, hnr, ?_, hnd.filter _, ?_⟩
  · exact List.mem_filter.mpr ⟨h1in, by simp [hs.symm]⟩
  · intro r hr
    exact hlt r (List.mem_filter.mp hr).1

theorem AStateOk_initBody (params : Array Param) : AStateOk (initBody params).2 := by
  unfold initBody
  rw [← Array.foldl_toList]
  suffices ∀ (ps : List Param) (acc : List ABnd × AState),
      AStateOk acc.2 →
      AStateOk (ps.foldl (fun (env, σ) p =>
        let v := paramVal p 2
        let (id, σ') := σ.pushBnd v (p.mode.usage == .once)
        ({ id, mode := p.mode, val := v } :: env, σ')) acc).2 by
    apply this
    refine ⟨rfl, rfl, by decide, by simp, by simp, ?_⟩
    intro r hr
    dsimp only at hr ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega
  intro ps
  induction ps with
  | nil => intro acc h; exact h
  | cons p ps ih =>
    intro acc h
    exact ih _ (h.pushBnd _ _).1

end IxC.Resource.Proof
