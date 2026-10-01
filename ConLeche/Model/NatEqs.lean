module

public import ConLeche.Model.Install
public import ConLeche.Semantics.NatFrag
public import ConLeche.Semantics.DeclRun

public section

/-!
# The structural-`Nat` recurrences, established at `interp` from run
certificates (task #161, literal tier)

The literal tier's wall (`Steps/Nat.lean`) is exactly one law wide:
the stored operations' recurrences at `interp`.  This file builds the
recorded resumption route — **establishment from run certificates**:
`DeclDefnR` records one `isDefEqCore` run per substituted equation
(`NatEqsRun`, the H1 exposure), and `DefEqClaim` at the
pre-insertion environment converts each run into an `interp` equality
at the two-variable `Nat` context.  The v1 route (`NatEqsR`'s `DefEq`
+ `DefEq.sound`) is *not* transferable — its soundness lives at the
collapse currency only (the wall record's finding 2).

What the conversion costs beyond v1: `DefEqClaim` demands the
compared readings **graded** (`WellDenotedV` under `Sat`), which the
collapse-lane `DefEqClaimsR` never did.  The grading of an equation
side — an application spine over stored `Nat`-operation heads,
`Nat.zero`/`Nat.succ`, and two `Nat` free variables — is assembled
here from the environment invariant alone:

* argument memberships from `Sat` and `NatHeads`;
* head memberships from `mem_type` at the **pinned** operation types
  (`natOpTyPinned`), whose `denoteMeta` readings compute to two-step
  `.pi` spines over the `Nat` leaf;
* fibre facts at *unknown* regime bits from `type_wellDenotedV`'s
  `AnnotValid` — `app_mem_piR`'s `hB0` premise is exactly the
  validity `pi` clause, so **no bit positivity is ever needed**
  (the doctrine holds: bits are never taken from a metatheorem, and
  here they are not taken at all).

The layers: the two-variable context kit; the graded-argument walk
(`NatArg`); the head packages (`NatBinHead`/`NatUnHead`) and their
pinned-type establishment; the per-equation conversion; the crossing
to the install's extension (`denoteMeta_substConst0`); and the field
suppliers (`natOps_install` bespoke at the operation's own install,
`natOps_cons_fresh` at every other fresh cons).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## Level plumbing -/

/-- The ground-composition identity: substituting nothing reads the
assignment itself. -/
theorem substFn_nil (ψ : Name → Nat) : Level.substFn ψ [] [] = ψ :=
  funext fun _ => rfl

/-! ## The two-variable `Nat` context -/

/-- The `Nat` leaf at an assignment (every structural-`Nat` head is
stored level-monomorphically, so the spelling is the plain
assignment). -/
def natLeafAV {env : Env} (m : EnvModel V env) (ψ : Name → Nat) :
    AnnotTerm :=
  m.acval ConLeche.natName ψ

/-- The stored `Nat`'s interpretation. -/
noncomputable def natLeafV {env : Env} (m : EnvModel V env)
    (ψ : Name → Nat) (ρ : Nat → V) : V :=
  interp V ρ (natLeafAV m ψ)

/-- A leaf's interpretation does not read the environment
(`acval_interp2_closed` at the core carrier). -/
theorem acval_interp_closedC (m : EnvModel V env) (n : Name)
    (ψ : Name → Nat) (ρ ρ' : Nat → V) :
    interp V ρ (m.acval n ψ) = interp V ρ' (m.acval n ψ) :=
  interp_closed V
    (by rw [m.acval_erase]; exact m.cval_closed n ψ) ρ ρ'

/-- The `Nat` leaf's interpretation does not read the environment. -/
theorem natLeafAV_interp_closed (m : EnvModel V env) (ψ : Name → Nat)
    (ρ ρ' : Nat → V) :
    interp V ρ (natLeafAV m ψ) = interp V ρ' (natLeafAV m ψ) :=
  acval_interp_closedC m _ ψ ρ ρ'

/-- The two-variable context: both slots are the `Nat` leaf. -/
def natCtx2 {env : Env} (m : EnvModel V env) (ψ : Name → Nat) :
    List AnnotTerm :=
  [natLeafAV m ψ, natLeafAV m ψ]

/-- Two `Nat` members satisfy the two-variable context (`sat_two`'s P
mirror; the slot readings collapse by leaf closedness). -/
theorem sat_natCtx2 (m : EnvModel V env) {ψ : Name → Nat}
    {ρ : Nat → V} {x y : V}
    (hx : x ∈ˢ natLeafV m ψ ρ) (hy : y ∈ˢ natLeafV m ψ ρ) :
    Sat V (natCtx2 m ψ) (cons y (cons x ρ)) := by
  intro i Aa hi
  match i with
  | 0 =>
    obtain rfl : natLeafAV m ψ = Aa := by simpa [natCtx2] using hi
    show y ∈ˢ interp V _ (natLeafAV m ψ)
    rw [natLeafAV_interp_closed m ψ _ ρ]
    exact hy
  | 1 =>
    obtain rfl : natLeafAV m ψ = Aa := by simpa [natCtx2] using hi
    show x ∈ˢ interp V _ (natLeafAV m ψ)
    rw [natLeafAV_interp_closed m ψ _ ρ]
    exact hx
  | n + 2 => simp [natCtx2] at hi

/-- Conversely, a satisfying valuation of the two-variable context has
`Nat` members in both slots. -/
theorem sat_natCtx2_inv (m : EnvModel V env) {ψ : Name → Nat}
    {ρ : Nat → V} (hρ : Sat V (natCtx2 m ψ) ρ) :
    ρ 0 ∈ˢ natLeafV m ψ ρ ∧ ρ 1 ∈ˢ natLeafV m ψ ρ := by
  have h0 := hρ 0 (natLeafAV m ψ) (by simp [natCtx2])
  have h1 := hρ 1 (natLeafAV m ψ) (by simp [natCtx2])
  rw [natLeafAV_interp_closed m ψ _ ρ] at h0
  rw [natLeafAV_interp_closed m ψ _ ρ] at h1
  exact ⟨h0, h1⟩

/-! ## The graded-argument walk

A `Nat`-valued fragment term at the two-variable context: it reads,
its reading is graded, and its interpretation is a stored-`Nat`
member.  The intro lemmas below are the fragment's typing rules; the
head packages that drive the application rules follow. -/

/-- A graded `Nat`-valued argument. -/
def NatArg (m : EnvModel V env) (ψ : Name → Nat) (e : Expr) :
    Prop :=
  ∃ ea, denoteMeta m.acval env ψ 2 e = some ea ∧
    ∀ ρ : Nat → V, Sat V (natCtx2 m ψ) ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ natLeafV m ψ ρ

/-- The first equation variable (`fvar 0`). -/
theorem natArg_var0 (m : EnvModel V env) (ψ : Name → Nat) :
    NatArg m ψ (.fvar 0 (.const ConLeche.natName [])) := by
  refine ⟨.bvar 1, denoteMeta_fvar _ 2 0 _, fun ρ hρ => ?_⟩
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  rw [interp_bvar]
  exact (sat_natCtx2_inv m hρ).2

/-- The second equation variable (`fvar 1`). -/
theorem natArg_var1 (m : EnvModel V env) (ψ : Name → Nat) :
    NatArg m ψ (.fvar 1 (.const ConLeche.natName [])) := by
  refine ⟨.bvar 0, denoteMeta_fvar _ 2 1 _, fun ρ hρ => ?_⟩
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  rw [interp_bvar]
  exact (sat_natCtx2_inv m hρ).1

/-- `Nat.zero`. -/
theorem natArg_zero (m : EnvModel V env) {ψ : Name → Nat}
    (hnh : NatHeads m ψ) (hval : AcvalValid m)
    (hs : natLitSupported env = true) :
    NatArg m ψ (.const ConLeche.natZeroName []) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hlpZ' : (ConLeche.ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
      = [] := hlpZ
  have hzl : denoteMeta m.acval env ψ 2 (.const ConLeche.natZeroName [])
      = some (m.acval ConLeche.natZeroName (Level.substFn ψ
          (ConLeche.ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
          [])) :=
    denoteMeta_const hfZ (by simp [hlpZ'])
  rw [hlpZ'] at hzl
  refine ⟨m.acval ConLeche.natZeroName (Level.substFn ψ [] []), hzl,
    fun ρ hρ => ?_⟩
  refine ⟨⟨m.acval_wellDenoted _ _ ρ, hval _ _ ρ⟩, ?_⟩
  have h := (hnh hs ρ).1
  rwa [show natLeafV m ψ ρ
      = interp V ρ (m.acval ConLeche.natName (Level.substFn ψ [] []))
    from by rw [substFn_nil]; rfl]

/-- `Nat.succ` applied to a graded argument. -/
theorem natArg_succ (m : EnvModel V env) {ψ : Name → Nat}
    (hnh : NatHeads m ψ) (hval : AcvalValid m)
    (hs : natLitSupported env = true) {t : Expr}
    (ht : NatArg m ψ t) :
    NatArg m ψ (.app (.const ConLeche.natSuccName []) t) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  obtain ⟨ta, hta, htg⟩ := ht
  have hlpS' : (ConLeche.ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
      = [] := hlpS
  have hsl : denoteMeta m.acval env ψ 2 (.const ConLeche.natSuccName [])
      = some (m.acval ConLeche.natSuccName (Level.substFn ψ
          (ConLeche.ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
          [])) :=
    denoteMeta_const hfS (by simp [hlpS'])
  rw [hlpS'] at hsl
  refine ⟨.app (m.acval ConLeche.natSuccName (Level.substFn ψ [] [])) ta,
    by rw [denoteMeta_app, hsl, hta]; rfl, fun ρ hρ => ?_⟩
  obtain ⟨⟨htok, htv⟩, htm⟩ := htg ρ hρ
  have hsucc := (hnh hs ρ).2
  have hnatEq : interp V ρ (m.acval ConLeche.natName (Level.substFn ψ [] []))
      = natLeafV m ψ ρ := by rw [substFn_nil]; rfl
  rw [hnatEq] at hsucc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨m.acval_wellDenoted _ _ ρ, htok,
      1, natLeafV m ψ ρ, fun _ => natLeafV m ψ ρ, hsucc, htm,
      fun h => absurd h Nat.one_ne_zero⟩
  · rw [AnnotValid_app]
    exact ⟨hval _ _ ρ, htv⟩
  · rw [interp_app]
    exact app_mem_piR_pos Nat.one_ne_zero hsucc htm

/-! ## The head packages

What a fragment application rule needs of its head: the head reads to
a graded `AnnotTerm` whose interpretation sits in a (one- or two-step)
`piR` over the stored `Nat`, with the validity fibre facts at each
step — at *whatever* regime bits the stored annotation carries.
`app_mem_piR` consumes exactly this, so no bit positivity appears. -/

/-- A binary head over the pinned `Nat`, with codomain set `codS`. -/
def NatBinHead (m : EnvModel V env) (ψ : Name → Nat) (f : Expr)
    (codS : (Nat → V) → V) : Prop :=
  ∃ fa, denoteMeta m.acval env ψ 2 f = some fa ∧
    ∀ ρ : Nat → V, Sat V (natCtx2 m ψ) ρ →
      WellDenotedV V ρ fa ∧
      ∃ b₁ b₂ : Nat,
        interp V ρ fa ∈ˢ piR b₁ (natLeafV m ψ ρ)
          (fun _ => piR b₂ (natLeafV m ψ ρ) (fun _ => codS ρ)) ∧
        (b₁ = 0 → ∀ x, x ∈ˢ natLeafV m ψ ρ →
          piR b₂ (natLeafV m ψ ρ) (fun _ => codS ρ) ∈ˢ (univZero : V)) ∧
        (b₂ = 0 → ∀ x, x ∈ˢ natLeafV m ψ ρ → codS ρ ∈ˢ (univZero : V))

/-- A unary head over the pinned `Nat`, with codomain set `codS`. -/
def NatUnHead (m : EnvModel V env) (ψ : Name → Nat) (f : Expr)
    (codS : (Nat → V) → V) : Prop :=
  ∃ fa, denoteMeta m.acval env ψ 2 f = some fa ∧
    ∀ ρ : Nat → V, Sat V (natCtx2 m ψ) ρ →
      WellDenotedV V ρ fa ∧
      ∃ b₁ : Nat,
        interp V ρ fa ∈ˢ piR b₁ (natLeafV m ψ ρ) (fun _ => codS ρ) ∧
        (b₁ = 0 → ∀ x, x ∈ˢ natLeafV m ψ ρ → codS ρ ∈ˢ (univZero : V))

/-- **The binary application rule**: a binary head applied to two
graded arguments reads, is graded, and lands in the codomain set. -/
theorem natBinHead_app (m : EnvModel V env) {ψ : Name → Nat}
    {f x y : Expr} {codS : (Nat → V) → V}
    (hh : NatBinHead m ψ f codS) (hx : NatArg m ψ x)
    (hy : NatArg m ψ y) :
    ∃ ea, denoteMeta m.acval env ψ 2 (.app (.app f x) y) = some ea ∧
      ∀ ρ : Nat → V, Sat V (natCtx2 m ψ) ρ →
        WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ codS ρ := by
  obtain ⟨fa, hfa, hfg⟩ := hh
  obtain ⟨xa, hxa, hxg⟩ := hx
  obtain ⟨ya, hya, hyg⟩ := hy
  refine ⟨.app (.app fa xa) ya,
    by rw [denoteMeta_app, denoteMeta_app, hfa, hxa, hya]; rfl,
    fun ρ hρ => ?_⟩
  obtain ⟨⟨hfok, hfv⟩, b₁, b₂, hfm, hB1, hB2⟩ := hfg ρ hρ
  obtain ⟨⟨hxok, hxv⟩, hxm⟩ := hxg ρ hρ
  obtain ⟨⟨hyok, hyv⟩, hym⟩ := hyg ρ hρ
  -- the inner application's membership, at whatever bit
  have hinner : SetTheory.app (interp V ρ fa) (interp V ρ xa)
      ∈ˢ piR b₂ (natLeafV m ψ ρ) (fun _ => codS ρ) :=
    app_mem_piR hfm hxm hB1
  have houter : SetTheory.app
      (SetTheory.app (interp V ρ fa) (interp V ρ xa))
      (interp V ρ ya) ∈ˢ codS ρ :=
    app_mem_piR hinner hym hB2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, hyok, b₂, natLeafV m ψ ρ, fun _ => codS ρ, ?_, hym, ?_⟩
    · rw [WellDenoted_app]
      exact ⟨hfok, hxok, b₁, natLeafV m ψ ρ,
        fun _ => piR b₂ (natLeafV m ψ ρ) (fun _ => codS ρ), hfm, hxm,
        fun hz => hB1 hz⟩
    · rw [interp_app]
      exact hinner
    · intro hz z hz'
      exact hB2 hz z hz'
  · rw [AnnotValid_app, AnnotValid_app]
    exact ⟨⟨hfv, hxv⟩, hyv⟩
  · rw [interp_app, interp_app]
    exact houter

/-- **The unary application rule.** -/
theorem natUnHead_app (m : EnvModel V env) {ψ : Name → Nat}
    {f x : Expr} {codS : (Nat → V) → V}
    (hh : NatUnHead m ψ f codS) (hx : NatArg m ψ x) :
    ∃ ea, denoteMeta m.acval env ψ 2 (.app f x) = some ea ∧
      ∀ ρ : Nat → V, Sat V (natCtx2 m ψ) ρ →
        WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ codS ρ := by
  obtain ⟨fa, hfa, hfg⟩ := hh
  obtain ⟨xa, hxa, hxg⟩ := hx
  refine ⟨.app fa xa, by rw [denoteMeta_app, hfa, hxa]; rfl,
    fun ρ hρ => ?_⟩
  obtain ⟨⟨hfok, hfv⟩, b₁, hfm, hB1⟩ := hfg ρ hρ
  obtain ⟨⟨hxok, hxv⟩, hxm⟩ := hxg ρ hρ
  have happ : SetTheory.app (interp V ρ fa) (interp V ρ xa)
      ∈ˢ codS ρ := app_mem_piR hfm hxm hB1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨hfok, hxok, b₁, natLeafV m ψ ρ, fun _ => codS ρ, hfm, hxm,
      fun hz => hB1 hz⟩
  · rw [AnnotValid_app]
    exact ⟨hfv, hxv⟩
  · rw [interp_app]
    exact happ

/-! ## The pinned operation types, shape and reading

`natOpTyPinned` pins an operation's stored type syntactically; its
`denoteMeta` reading therefore computes to a two-step (binary) or
one-step (unary) `.pi` spine over the `Nat` leaf, at whatever regime
bits the stored annotation carries. -/

/-- The pinned binary type's syntactic shape (the `natOpTyPinned`
else-branch, unpacked). -/
theorem natOpTyPinned_shape_bin {env' : Env} {c : Name} {ty : Expr}
    (hnu : ¬(c = ConLeche.natPredName))
    (h : ConLeche.natOpTyPinned env' c ty = true) :
    ∃ mb₁ mb₂ cod,
      ty = .forallE (.const ConLeche.natName [])
        (.forallE (.const ConLeche.natName []) cod mb₂) mb₁ ∧
      ((c = ConLeche.natBeqName ∨ c = ConLeche.natBleName) →
        cod = .const ConLeche.boolName [] ∧
        ∃ ci, env'.find? ConLeche.boolName = some ci ∧
          ci.toConstantVal.levelParams = []) ∧
      (¬(c = ConLeche.natBeqName ∨ c = ConLeche.natBleName) →
        cod = .const ConLeche.natName []) := by
  unfold ConLeche.natOpTyPinned at h
  split at h
  · next hc => exact absurd hc hnu
  · split at h
    · next a dom b dom2 body mb2 mb =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hcod⟩ := h
      unfold ConLeche.natOpCod at hcod
      refine ⟨mb, mb2, body, rfl, ?_, ?_⟩
      all_goals split at hcod
      · intro _
        simp only [Bool.and_eq_true, beq_iff_eq] at hcod
        obtain ⟨rfl, hstore⟩ := hcod
        refine ⟨rfl, ?_⟩
        revert hstore
        cases hf : env'.find? ConLeche.boolName with
        | none => intro hh; exact nomatch hh
        | some ci =>
          intro hh
          simp only [Bool.and_eq_true] at hh
          exact ⟨ci, rfl, by simpa [List.isEmpty_iff] using hh.1⟩
      · next hcb =>
        intro hc
        exfalso
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcb
        exact hcb hc
      · next hcb =>
        intro hn
        exfalso
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcb
        exact hn hcb
      · intro _
        exact beq_iff_eq.mp hcod
    · exact nomatch h

/-- The pinned unary type's syntactic shape. -/
theorem natOpTyPinned_shape_un {env' : Env} {c : Name} {ty : Expr}
    (hu : c = ConLeche.natPredName)
    (h : ConLeche.natOpTyPinned env' c ty = true) :
    ∃ mb₁, ty = .forallE (.const ConLeche.natName [])
      (.const ConLeche.natName []) mb₁ := by
  unfold ConLeche.natOpTyPinned at h
  split at h
  · split at h
    · next a dom body mb =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hcod⟩ := h
      unfold ConLeche.natOpCod at hcod
      split at hcod
      · next hcb =>
        exfalso
        subst hu; exact absurd hcb (by decide)
      · exact ⟨mb, by rw [beq_iff_eq.mp hcod]⟩
    · exact nomatch h
  · next hc => exact absurd hu hc

/-! ## Reading the pinned types -/

/-- A stored level-monomorphic constant reads to its leaf at the plain
assignment. -/
theorem denoteMeta_levelless_const {acval : Name → (Name → Nat) → AnnotTerm}
    {ψ : Name → Nat} {d : Nat} {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) :
    denoteMeta acval env ψ d (.const n []) = some (acval n ψ) := by
  have h : denoteMeta acval env ψ d (.const n [])
      = some (acval n (Level.substFn ψ ci.toConstantVal.levelParams []))
    := denoteMeta_const hf (by simp [hlp])
  rw [hlp, substFn_nil] at h
  exact h

/-- The pinned binary operation type's reading: a two-step `.pi` over
the `Nat` leaf and the codomain leaf, at the stored regime bits. -/
theorem denoteMeta_pinnedBinTy (m : EnvModel V env) (ψ : Name → Nat)
    {mb₁ mb₂ : ConLeche.BinderMeta} {codN : Name}
    {ciN codCi : ConstantInfo}
    (hfN : env.find? ConLeche.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hcodF : env.find? codN = some codCi)
    (hcodLp : codCi.toConstantVal.levelParams = []) :
    denoteMeta m.acval env ψ 0
        (.forallE (.const ConLeche.natName [])
          (.forallE (.const ConLeche.natName []) (.const codN []) mb₂)
          mb₁)
      = some (.pi 0 (pwBit ψ mb₁.pw) (m.acval ConLeche.natName ψ)
          (.pi 0 (pwBit ψ mb₂.pw) (m.acval ConLeche.natName ψ)
            (m.acval codN ψ))) := by
  rw [denoteMeta_forallE, denoteMeta_levelless_const hfN hlpN]
  rw [show (Expr.forallE (.const ConLeche.natName [])
        (.const codN []) mb₂).instantiate1
        (.fvar 0 (.const ConLeche.natName []))
      = Expr.forallE (.const ConLeche.natName []) (.const codN []) mb₂
    from ConLeche.Expr.instantiate1_eq_self
      (by simp [ConLeche.Expr.looseBVarsBounded])]
  rw [denoteMeta_forallE, denoteMeta_levelless_const hfN hlpN]
  rw [show (Expr.const codN ([] : List ConLeche.Level)).instantiate1
        (.fvar 1 (.const ConLeche.natName []))
      = Expr.const codN [] from ConLeche.Expr.instantiate1_eq_self
      (by simp [ConLeche.Expr.looseBVarsBounded])]
  rw [denoteMeta_levelless_const hcodF hcodLp]
  rfl

/-- The pinned unary operation type's reading. -/
theorem denoteMeta_pinnedUnTy (m : EnvModel V env) (ψ : Name → Nat)
    {mb₁ : ConLeche.BinderMeta}
    {ciN : ConstantInfo}
    (hfN : env.find? ConLeche.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    denoteMeta m.acval env ψ 0
        (.forallE (.const ConLeche.natName [])
          (.const ConLeche.natName []) mb₁)
      = some (.pi 0 (pwBit ψ mb₁.pw) (m.acval ConLeche.natName ψ)
          (m.acval ConLeche.natName ψ)) := by
  rw [denoteMeta_forallE, denoteMeta_levelless_const hfN hlpN]
  rw [show (Expr.const ConLeche.natName ([] : List ConLeche.Level)).instantiate1
        (.fvar 0 (.const ConLeche.natName []))
      = Expr.const ConLeche.natName [] from ConLeche.Expr.instantiate1_eq_self
      (by simp [ConLeche.Expr.looseBVarsBounded])]
  rw [denoteMeta_levelless_const hfN hlpN]
  rfl

/-! ## Head packages from parts -/

/-- **The binary head package, from its parts**: a graded reading, a
membership in the (two-step, leaf-component) pinned product's reading,
and the product reading's own grading. -/
theorem natBinHead_of_parts (m : EnvModel V env) {ψ : Name → Nat}
    {f : Expr} {fa : AnnotTerm} {b₁ b₂ : Nat} {codN : Name}
    (hfa : denoteMeta m.acval env ψ 2 f = some fa)
    (hok : ∀ ρ : Nat → V, WellDenotedV V ρ fa)
    (hmem : ∀ ρ : Nat → V, interp V ρ fa ∈ˢ interp V ρ
      (.pi 0 b₁ (m.acval ConLeche.natName ψ)
        (.pi 0 b₂ (m.acval ConLeche.natName ψ) (m.acval codN ψ))))
    (htok : ∀ ρ : Nat → V, WellDenotedV V ρ
      ((.pi 0 b₁ (m.acval ConLeche.natName ψ)
        (.pi 0 b₂ (m.acval ConLeche.natName ψ) (m.acval codN ψ)))
        : AnnotTerm)) :
    NatBinHead m ψ f (fun ρ => interp V ρ (m.acval codN ψ)) := by
  refine ⟨fa, hfa, fun ρ _ => ⟨hok ρ, b₁, b₂, ?_, ?_, ?_⟩⟩
  · -- the membership, with the fibres closed off
    have h := hmem ρ
    rw [interp_pi] at h
    have hfib : (fun x => interp V (cons x ρ)
          ((.pi 0 b₂ (m.acval ConLeche.natName ψ) (m.acval codN ψ))
            : AnnotTerm))
        = fun _ => piR b₂ (natLeafV m ψ ρ)
            (fun _ => interp V ρ (m.acval codN ψ)) := by
      funext x
      rw [interp_pi]
      congr 1
      · exact acval_interp_closedC m _ ψ _ ρ
      · funext y
        exact acval_interp_closedC m _ ψ _ ρ
    rw [hfib] at h
    exact h
  · -- the outer fibre fact, from validity
    intro hz x hx
    have hv := (htok ρ).2
    rw [AnnotValid_pi] at hv
    have h := hv.2.2 hz x hx
    rw [show interp V (cons x ρ)
          ((.pi 0 b₂ (m.acval ConLeche.natName ψ) (m.acval codN ψ))
            : AnnotTerm)
        = piR b₂ (natLeafV m ψ ρ)
            (fun _ => interp V ρ (m.acval codN ψ)) from by
      rw [interp_pi]
      congr 1
      · exact acval_interp_closedC m _ ψ _ ρ
      · funext y
        exact acval_interp_closedC m _ ψ _ ρ] at h
    exact h
  · -- the inner fibre fact, from validity one binder in
    intro hz x hx
    have hv := (htok ρ).2
    rw [AnnotValid_pi] at hv
    have hinner := hv.2.1 x hx
    rw [AnnotValid_pi] at hinner
    have h := hinner.2.2 hz x
      (by rw [acval_interp_closedC m _ ψ (cons x ρ) ρ]; exact hx)
    rwa [acval_interp_closedC m _ ψ _ ρ] at h

/-- **The unary head package, from its parts.** -/
theorem natUnHead_of_parts (m : EnvModel V env) {ψ : Name → Nat}
    {f : Expr} {fa : AnnotTerm} {b₁ : Nat} {codN : Name}
    (hfa : denoteMeta m.acval env ψ 2 f = some fa)
    (hok : ∀ ρ : Nat → V, WellDenotedV V ρ fa)
    (hmem : ∀ ρ : Nat → V, interp V ρ fa ∈ˢ interp V ρ
      (.pi 0 b₁ (m.acval ConLeche.natName ψ) (m.acval codN ψ)))
    (htok : ∀ ρ : Nat → V, WellDenotedV V ρ
      ((.pi 0 b₁ (m.acval ConLeche.natName ψ) (m.acval codN ψ))
        : AnnotTerm)) :
    NatUnHead m ψ f (fun ρ => interp V ρ (m.acval codN ψ)) := by
  refine ⟨fa, hfa, fun ρ _ => ⟨hok ρ, b₁, ?_, ?_⟩⟩
  · have h := hmem ρ
    rw [interp_pi] at h
    have hfib : (fun x => interp V (cons x ρ) (m.acval codN ψ))
        = fun _ => interp V ρ (m.acval codN ψ) := by
      funext x
      exact acval_interp_closedC m _ ψ _ ρ
    rw [hfib] at h
    exact h
  · intro hz x hx
    have hv := (htok ρ).2
    rw [AnnotValid_pi] at hv
    have h := hv.2.2 hz x hx
    rwa [acval_interp_closedC m _ ψ _ ρ] at h

/-! ## Head packages from the environment invariant

A stored operation with a pinned type gets its head package from
`mem_type` (the leaf inhabits its type's reading) and `type_wellDenotedV` (the
reading is graded — which is where the fibre facts at the unknown
regime bits come from). -/

/-- **A stored pinned binary head.** -/
theorem natBinHead_of_stored (mp : EnvModelM V μ env) {ψ : Name → Nat}
    {o : Name} {cvo : ConstantVal} {vo : Expr}
    {ho : ReducibilityHint}
    (hf : env.find? o = some (.defnInfo cvo vo ho))
    (hlp : cvo.levelParams = [])
    {mb₁ mb₂ : ConLeche.BinderMeta} {codN : Name}
    (hty : cvo.type = .forallE (.const ConLeche.natName [])
      (.forallE (.const ConLeche.natName []) (.const codN []) mb₂)
      mb₁)
    {ciN codCi : ConstantInfo}
    (hfN : env.find? ConLeche.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hcodF : env.find? codN = some codCi)
    (hcodLp : codCi.toConstantVal.levelParams = []) :
    NatBinHead mp.base2 ψ (.const o [])
      (fun ρ => interp V ρ (mp.base2.acval codN ψ)) := by
  have hmemE := ConLeche.Semantics.Env.find?_mem hf
  have hnm : cvo.name = o := ConLeche.Semantics.Env.find?_name hf
  have hta : denoteMeta mp.base2.acval env ψ 0
      (ConstantInfo.defnInfo cvo vo ho).toConstantVal.type
      = some (.pi 0 (pwBit ψ mb₁.pw) (mp.base2.acval ConLeche.natName ψ)
          (.pi 0 (pwBit ψ mb₂.pw) (mp.base2.acval ConLeche.natName ψ)
            (mp.base2.acval codN ψ))) := by
    show denoteMeta mp.base2.acval env ψ 0 cvo.type = _
    rw [hty]
    exact denoteMeta_pinnedBinTy mp.base2 ψ hfN hlpN hcodF hcodLp
  refine natBinHead_of_parts mp.base2
    (denoteMeta_levelless_const hf (show (ConstantInfo.defnInfo cvo vo
      ho).toConstantVal.levelParams = [] from hlp))
    (fun ρ => ⟨mp.base2.acval_wellDenoted _ _ ρ, mp.acval_validV _ _ ρ⟩)
    (fun ρ => ?_) (fun ρ => mp.type_wellDenotedV _ hmemE ψ _ hta ρ)
  have h := mp.mem_type _ hmemE ψ _ hta ρ
  rwa [show (ConstantInfo.defnInfo cvo vo ho).name = o from hnm] at h

/-- **A stored pinned unary head.** -/
theorem natUnHead_of_stored (mp : EnvModelM V μ env) {ψ : Name → Nat}
    {o : Name} {cvo : ConstantVal} {vo : Expr}
    {ho : ReducibilityHint}
    (hf : env.find? o = some (.defnInfo cvo vo ho))
    (hlp : cvo.levelParams = [])
    {mb₁ : ConLeche.BinderMeta}
    (hty : cvo.type = .forallE (.const ConLeche.natName [])
      (.const ConLeche.natName []) mb₁)
    {ciN : ConstantInfo}
    (hfN : env.find? ConLeche.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    NatUnHead mp.base2 ψ (.const o [])
      (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName ψ)) := by
  have hmemE := ConLeche.Semantics.Env.find?_mem hf
  have hnm : cvo.name = o := ConLeche.Semantics.Env.find?_name hf
  have hta : denoteMeta mp.base2.acval env ψ 0
      (ConstantInfo.defnInfo cvo vo ho).toConstantVal.type
      = some (.pi 0 (pwBit ψ mb₁.pw) (mp.base2.acval ConLeche.natName ψ)
          (mp.base2.acval ConLeche.natName ψ)) := by
    show denoteMeta mp.base2.acval env ψ 0 cvo.type = _
    rw [hty]
    exact denoteMeta_pinnedUnTy mp.base2 ψ hfN hlpN
  refine natUnHead_of_parts mp.base2
    (denoteMeta_levelless_const hf (show (ConstantInfo.defnInfo cvo vo
      ho).toConstantVal.levelParams = [] from hlp))
    (fun ρ => ⟨mp.base2.acval_wellDenoted _ _ ρ, mp.acval_validV _ _ ρ⟩)
    (fun ρ => ?_) (fun ρ => mp.type_wellDenotedV _ hmemE ψ _ hta ρ)
  have h := mp.mem_type _ hmemE ψ _ hta ρ
  rwa [show (ConstantInfo.defnInfo cvo vo ho).name = o from hnm] at h

/-! ## The two-variable context discipline, and the conversion -/

/-- The `Nat`-leaved sides satisfy `CtxOk` at the two-variable
context. -/
theorem ctxOk_natCtx2 (m : EnvModel V env) {ψ : Name → Nat}
    (hval : AcvalValid m) {ciN : ConstantInfo}
    (hfN : env.find? ConLeche.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    {e : Expr}
    (hleaf : ∀ l ∈ e.fvarLeaves, l.1 < 2 ∧
      l.2 = .const ConLeche.natName []) :
    CtxOk m ψ 2 (natCtx2 m ψ) e := by
  refine ⟨rfl, fun l hl => ?_⟩
  obtain ⟨hlt, hty⟩ := hleaf l hl
  refine ⟨hlt, by rw [hty]; trivial, natLeafAV m ψ, natLeafAV m ψ,
    by rw [hty]; exact denoteMeta_levelless_const hfN hlpN, ?_, ?_, ?_⟩
  · show (natCtx2 m ψ)[2 - 1 - l.1]? = some (natLeafAV m ψ)
    obtain h01 | h01 : l.1 = 0 ∨ l.1 = 1 := by omega
    · rw [h01]; rfl
    · rw [h01]; rfl
  · intro ρ _
    exact natLeafAV_interp_closed m ψ ρ _
  · intro ρ _
    exact ⟨m.acval_wellDenoted _ _ ρ, hval _ _ ρ⟩

/-- **One substituted equation, converted**: the recorded run plus both
sides' packages give the two-variable `interp` equality — the exact
law shape `NatOps` stores.  `DefEqClaim` does the work; the frames
come from the v1 fragment machinery, the gradings from the packages,
the context from `ctxOk_natCtx2`. -/
theorem natEqLaw_of_run (mp : EnvModelM V μ env) {ψ : Name → Nat}
    {F : Nat} (hde : DefEqClaim μ mp.base2 ψ F)
    {ciN : ConstantInfo}
    (hfN : env.find? ConLeche.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    {lhs rhs : Expr} {la ra : AnnotTerm}
    (hrun : ConLeche.isDefEqCore μ env F 2 lhs rhs = .ok true)
    (hwl : Expr.WScoped 2 lhs) (hbl : lhs.looseBVarsBounded 0 = true)
    (hLl : Expr.LeavesBounded lhs)
    (hll : ∀ l ∈ lhs.fvarLeaves, l.1 < 2 ∧
      l.2 = .const ConLeche.natName [])
    (hwr : Expr.WScoped 2 rhs) (hbr : rhs.looseBVarsBounded 0 = true)
    (hLr : Expr.LeavesBounded rhs)
    (hlr : ∀ l ∈ rhs.fvarLeaves, l.1 < 2 ∧
      l.2 = .const ConLeche.natName [])
    (hla : denoteMeta mp.base2.acval env ψ 2 lhs = some la)
    (hga : ∀ ρ : Nat → V, Sat V (natCtx2 mp.base2 ψ) ρ →
      WellDenotedV V ρ la)
    (hra : denoteMeta mp.base2.acval env ψ 2 rhs = some ra)
    (hgr : ∀ ρ : Nat → V, Sat V (natCtx2 mp.base2 ψ) ρ →
      WellDenotedV V ρ ra) :
    ∀ (ρ : Nat → V) (x y : V),
      x ∈ˢ interp V ρ (mp.base2.acval ConLeche.natName ψ) →
      y ∈ˢ interp V ρ (mp.base2.acval ConLeche.natName ψ) →
      interp V (cons y (cons x ρ)) la
        = interp V (cons y (cons x ρ)) ra := by
  intro ρ x y hx hy
  have hρ : Sat V (natCtx2 mp.base2 ψ) (cons y (cons x ρ)) :=
    sat_natCtx2 mp.base2 hx hy
  exact hde hrun hwl hbl hLl hwr hbr hLr
    (ctxOk_natCtx2 mp.base2 mp.acvalValid hfN hlpN hll)
    (ctxOk_natCtx2 mp.base2 mp.acvalValid hfN hlpN hlr)
    hla hra hga hgr (cons y (cons x ρ)) hρ

/-! ## The crossing: substituted readings at the prefix are raw
readings at the extension (`denote_substConst0`'s P mirror) -/

/-- **The substitution crossing for the install's own constant**: on
the shallow fragment, reading in the extended environment under the
extended valuation is reading the substituted expression in the old
one. -/
theorem denoteMeta_substConst0 {acval : Name → (Name → Nat) → AnnotTerm}
    {ψ : Name → Nat} {c₀ : ConstantInfo} {c : Name} {v : Expr}
    {A : (Name → Nat) → AnnotTerm}
    (hname : c₀.name = c) (hfresh : env.find? c = none)
    (hlp : c₀.toConstantVal.levelParams = [])
    (hacl : ∀ (n : Name) (ψ' : Name → Nat) (k : Nat),
      (acval n ψ').liftN 1 k = acval n ψ')
    (hAcl : ∀ k : Nat, (A ψ).liftN 1 k = A ψ)
    (hv : denoteMeta acval env ψ 0 v = some (A ψ))
    (hvf : v.hasFvar = false) :
    ∀ (d : Nat) (e : Expr), shallowE e = true →
      denoteMeta (acvalWith acval c A) ⟨c₀ :: env.consts⟩ ψ d e
        = denoteMeta acval env ψ d (Expr.substConst0 c v e) := by
  intro d e
  induction e with
  | sort u =>
    intro _
    show denoteMeta (acvalWith acval c A) ⟨c₀ :: env.consts⟩ ψ d (.sort u)
      = denoteMeta acval env ψ d (.sort u)
    rw [denoteMeta_sort, denoteMeta_sort]
  | fvar idx ty =>
    intro _
    show denoteMeta (acvalWith acval c A) ⟨c₀ :: env.consts⟩ ψ d
        (.fvar idx ty) = denoteMeta acval env ψ d (.fvar idx ty)
    rw [denoteMeta_fvar, denoteMeta_fvar]
  | const n us =>
    intro _
    by_cases hn : n = c
    · subst hn
      by_cases hus : us = []
      · subst hus
        rw [show Expr.substConst0 n v (.const n []) = v from by
          rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
        have hfc : (⟨c₀ :: env.consts⟩ : Env).find? n = some c₀ := by
          rw [ConLeche.Env.find?_cons, if_pos hname]
        have h1 : denoteMeta (acvalWith acval n A) ⟨c₀ :: env.consts⟩ ψ d
            (.const n []) = some (acvalWith acval n A n ψ) :=
          denoteMeta_levelless_const hfc hlp
        rw [h1, show acvalWith acval n A n = A from acvalWith_self]
        exact (denoteMeta_depth_of_closed hacl hvf hAcl hv d).symm
      · rw [show Expr.substConst0 n v (.const n us) = .const n us from
          by rw [Expr.substConst0, if_neg (fun h => hus h.2)]]
        rw [denoteMeta, denoteMeta]
        rw [show (⟨c₀ :: env.consts⟩ : Env).find? n = some c₀ from by
          rw [ConLeche.Env.find?_cons, if_pos hname], hfresh]
        dsimp only
        rw [if_neg (by rw [hlp]; simpa using hus)]
    · rw [show Expr.substConst0 c v (.const n us) = .const n us from by
        rw [Expr.substConst0, if_neg (fun h => hn h.1)]]
      rw [denoteMeta, denoteMeta]
      rw [show (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n from by
        rw [ConLeche.Env.find?_cons,
          if_neg (fun hh => hn (hh.symm.trans hname))]]
      cases hf : env.find? n with
      | none => rfl
      | some ci =>
        dsimp only
        rw [show acvalWith acval c A n = acval n from acvalWith_ne hn]
  | app f a ihf iha =>
    intro hfr
    simp only [shallowE, Bool.and_eq_true] at hfr
    rw [show Expr.substConst0 c v (.app f a)
      = .app (Expr.substConst0 c v f) (Expr.substConst0 c v a) from
      rfl]
    rw [denoteMeta_app, denoteMeta_app, ihf hfr.1, iha hfr.2]
  | bvar _ => intro hfr; simp [shallowE] at hfr
  | lam _ _ _ => intro hfr; simp [shallowE] at hfr
  | forallE _ _ _ => intro hfr; simp [shallowE] at hfr
  | letE _ _ _ => intro hfr; simp [shallowE] at hfr
  | proj _ _ _ => intro hfr; simp [shallowE] at hfr
  | lit _ => intro hfr; simp [shallowE] at hfr

/-! ## `Nat`-codomain applications are graded arguments -/

/-- A binary head with `Nat` codomain applied to two graded arguments
is a graded argument. -/
theorem natArg_of_bin (m : EnvModel V env) {ψ : Name → Nat}
    {f x y : Expr}
    (hh : NatBinHead m ψ f
      (fun ρ => interp V ρ (m.acval ConLeche.natName ψ)))
    (hx : NatArg m ψ x) (hy : NatArg m ψ y) :
    NatArg m ψ (.app (.app f x) y) :=
  natBinHead_app m hh hx hy

/-- A unary head with `Nat` codomain applied to a graded argument is a
graded argument. -/
theorem natArg_of_un (m : EnvModel V env) {ψ : Name → Nat}
    {f x : Expr}
    (hh : NatUnHead m ψ f
      (fun ρ => interp V ρ (m.acval ConLeche.natName ψ)))
    (hx : NatArg m ψ x) :
    NatArg m ψ (.app f x) :=
  natUnHead_app m hh hx

/-- A graded argument's package, forgetting the membership — the shape
`natEqLaw_of_run`'s grading premises take. -/
theorem NatArg.package (m : EnvModel V env) {ψ : Name → Nat}
    {e : Expr} (h : NatArg m ψ e) :
    ∃ ea, denoteMeta m.acval env ψ 2 e = some ea ∧
      ∀ ρ : Nat → V, Sat V (natCtx2 m ψ) ρ → WellDenotedV V ρ ea := by
  obtain ⟨ea, hea, hg⟩ := h
  exact ⟨ea, hea, fun ρ hρ => (hg ρ hρ).1⟩

/-- A `Bool`-codomain application's package (comparison sides): the
membership in the codomain is dropped, the grading kept. -/
theorem natBinHead_app_package (m : EnvModel V env) {ψ : Name → Nat}
    {f x y : Expr} {codS : (Nat → V) → V}
    (hh : NatBinHead m ψ f codS) (hx : NatArg m ψ x)
    (hy : NatArg m ψ y) :
    ∃ ea, denoteMeta m.acval env ψ 2 (.app (.app f x) y) = some ea ∧
      ∀ ρ : Nat → V, Sat V (natCtx2 m ψ) ρ → WellDenotedV V ρ ea := by
  obtain ⟨ea, hea, hg⟩ := natBinHead_app m hh hx hy
  exact ⟨ea, hea, fun ρ hρ => (hg ρ hρ).1⟩

/-- A stored level-monomorphic constant's package (the comparison
right-hand sides' `Bool` constructors). -/
theorem natConst_package (m : EnvModel V env) {ψ : Name → Nat}
    (hval : AcvalValid m) {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) :
    ∃ ea, denoteMeta m.acval env ψ 2 (.const n []) = some ea ∧
      ∀ ρ : Nat → V, Sat V (natCtx2 m ψ) ρ → WellDenotedV V ρ ea :=
  ⟨m.acval n ψ, denoteMeta_levelless_const hf hlp,
    fun ρ _ => ⟨m.acval_wellDenoted _ _ ρ, hval _ _ ρ⟩⟩

/-! ## Descending the extension's storedness facts -/

/-- `natOpStoredOk` at a fresh cons, for a name other than the head,
descends to the prefix (the pinned-type conjunct stays at the
extension — its shape is env-free, and its `Bool`-codomain storedness
conjunct is descended separately by the caller). -/
theorem natOpStoredOk_descend {c₀ : ConstantInfo} {n : Name}
    (hne : n ≠ c₀.name)
    (hok : ConLeche.natOpStoredOk ⟨c₀ :: env.consts⟩ n = true) :
    ∃ cvn vn hn, env.find? n = some (.defnInfo cvn vn hn) ∧
      cvn.levelParams = [] ∧
      ConLeche.natOpTyPinned ⟨c₀ :: env.consts⟩ n cvn.type = true := by
  unfold ConLeche.natOpStoredOk at hok
  cases hf2 : (⟨c₀ :: env.consts⟩ : Env).find? n with
  | none => rw [hf2] at hok; exact nomatch hok
  | some ci =>
    rw [hf2] at hok
    cases ci with
    | defnInfo cvn vn hn =>
      simp only [Bool.and_eq_true] at hok
      have hfE : env.find? n = some (.defnInfo cvn vn hn) := by
        rw [ConLeche.Env.find?_cons] at hf2
        split at hf2
        · next heq => exact absurd heq.symm hne
        · exact hf2
      exact ⟨cvn, vn, hn, hfE,
        by simpa [List.isEmpty_iff] using hok.1, hok.2⟩
    | _ => exact nomatch hok

/-! ## The field's suppliers -/

/-- The pinned codomain's name: `Bool` for the comparisons, `Nat`
otherwise. -/
def natOpCodN (c : Name) : Name :=
  if c = ConLeche.natBeqName ∨ c = ConLeche.natBleName then ConLeche.boolName
  else ConLeche.natName

/-- Fragment terms mention only stored constants (the raw sides; the
head `c` must itself be stored). -/
theorem constsBound_of_natFragOk {c : Name}
    (hc : (env.find? c).isSome = true)
    (hnat : (env.find? ConLeche.natName).isSome = true) :
    ∀ {e : Expr}, ConLeche.Verify.natFragOk env c e = true →
      ConstsBound env e := by
  intro e
  induction e with
  | sort u => intro _; unfold ConstsBound; trivial
  | fvar idx ty =>
    intro h
    simp only [ConLeche.Verify.natFragOk, Bool.and_eq_true,
      beq_iff_eq] at h
    unfold ConstsBound
    rw [h.2]
    unfold ConstsBound
    exact hnat
  | const n us =>
    intro h
    unfold ConstsBound
    simp only [ConLeche.Verify.natFragOk, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, -⟩ | h
    · exact hc
    · revert h
      cases env.find? n with
      | none => intro h; exact nomatch h
      | some ci => intro _; rfl
  | app f a ihf iha =>
    intro h
    simp only [ConLeche.Verify.natFragOk, Bool.and_eq_true] at h
    unfold ConstsBound
    exact ⟨ihf h.1, iha h.2⟩
  | bvar _ => intro h; simp [ConLeche.Verify.natFragOk] at h
  | lam _ _ _ => intro h; simp [ConLeche.Verify.natFragOk] at h
  | forallE _ _ _ => intro h; simp [ConLeche.Verify.natFragOk] at h
  | letE _ _ _ => intro h; simp [ConLeche.Verify.natFragOk] at h
  | proj _ _ _ => intro h; simp [ConLeche.Verify.natFragOk] at h
  | lit _ => intro h; simp [ConLeche.Verify.natFragOk] at h

/-- The raw sides of a stored operation's recurrences are in the
fragment, from the guard alone. -/
theorem natOpEquations_frag_of_guard {c : Name}
    (hg : natOpGuard env c = true) :
    ∀ eq ∈ ConLeche.natOpEquations 0 c,
      ConLeche.Verify.natFragOk env c eq.1 = true ∧
        ConLeche.Verify.natFragOk env c eq.2 = true := by
  obtain ⟨hN, hz, hs, hdeps, hbool⟩ :=
    ConLeche.Verify.natOpGuard_stored hg
  refine ConLeche.Verify.natOpEquations_frag hz hs
    (fun n hn _ => hdeps n hn) (fun hc => (hbool (by
      rcases hc with rfl | rfl <;> simp)).1)
    (fun hc => (hbool (by rcases hc with rfl | rfl <;> simp)).2)

/-- A `Nat`-operation fragment has no `.proj` node at all. -/
theorem consCrossAt_of_natFragOk {c : Name} {c₀ : ConstantInfo} :
    ∀ {e : Expr}, ConLeche.Verify.natFragOk env c e = true →
      ConsCrossAt c₀ e := by
  intro e
  induction e with
  | sort _ => intro _ _ _ _; simp
  | fvar i ty =>
    intro h entry heq j
    simp only [ConLeche.Verify.natFragOk, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.2]
  | const _ _ => intro _ _ _ _; simp
  | app f a ihf iha =>
    intro h entry heq j
    simp only [ConLeche.Verify.natFragOk, Bool.and_eq_true] at h
    simp only [Expr.NoProjAt]
    exact ⟨ihf h.1 entry heq j, iha h.2 entry heq j⟩
  | bvar _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
    intro h; simp [ConLeche.Verify.natFragOk] at h

/-- **The per-operation crossing at a fresh cons**: an operation
stored in the prefix keeps its `NatOps` entry at the extension. -/
theorem natOps_entry_cons (mp : EnvModelM V μ env) {φ : Name → Nat}
    (hprev : NatOps mp.base2 φ)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hntc : ConsCrossEnv env c₀)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    {c : Name} (hcN : c ∈ ConLeche.natOpNames) (hne : c ≠ c₀.name)
    {cv' : ConstantVal} {v' : Expr} {hint' : ReducibilityHint}
    (hf₂ : (⟨c₀ :: env.consts⟩ : Env).find? c
      = some (.defnInfo cv' v' hint')) :
    natOpGuard (⟨c₀ :: env.consts⟩ : Env) c = true ∧
    ∀ eq ∈ ConLeche.natOpEquations 0 c, ∃ L R,
      denoteMeta m₂.acval ⟨c₀ :: env.consts⟩ φ 2 eq.1 = some L ∧
      denoteMeta m₂.acval ⟨c₀ :: env.consts⟩ φ 2 eq.2 = some R ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp V ρ (m₂.acval ConLeche.natName φ) →
        y ∈ˢ interp V ρ (m₂.acval ConLeche.natName φ) →
        interp V (cons y (cons x ρ)) L
          = interp V (cons y (cons x ρ)) R := by
  have _ := hntc
  have hfE : env.find? c = some (.defnInfo cv' v' hint') := by
    rw [ConLeche.Env.find?_cons] at hf₂
    split at hf₂
    · next heq => exact absurd heq.symm hne
    · exact hf₂
  obtain ⟨hg, hlaws⟩ := hprev c hcN cv' v' hint' hfE
  -- the stored heads are not the fresh cons
  obtain ⟨hN, -, -, -, -⟩ := ConLeche.Verify.natOpGuard_stored hg
  obtain ⟨ciN, hfN, -⟩ := ConLeche.Verify.storedNoLevels_exists hN
  have hnatne : ConLeche.natName ≠ c₀.name := fun hh => by
    rw [hh, hfresh] at hfN
    exact nomatch hfN
  have hcb : ∀ eq ∈ ConLeche.natOpEquations 0 c,
      ConstsBound env eq.1 ∧ ConstsBound env eq.2 := by
    intro eq hq
    obtain ⟨h1, h2⟩ := natOpEquations_frag_of_guard hg eq hq
    exact ⟨constsBound_of_natFragOk (by simp [hfE]) (by simp [hfN]) h1,
      constsBound_of_natFragOk (by simp [hfE]) (by simp [hfN]) h2⟩
  refine ⟨ConLeche.Verify.natOpGuard_cons hfresh hg, fun eq hq => ?_⟩
  obtain ⟨L, R, hL, hR, hlaw⟩ := hlaws eq hq
  have hfrag := natOpEquations_frag_of_guard hg eq hq
  refine ⟨L, R, ?_, ?_, ?_⟩
  · rw [hac]
    exact denoteMeta_cons_mono hfresh (consCrossAt_of_natFragOk hfrag.1) φ 2
      (hcb eq hq).1 hL
  · rw [hac]
    exact denoteMeta_cons_mono hfresh (consCrossAt_of_natFragOk hfrag.2) φ 2
      (hcb eq hq).2 hR
  · intro ρ x y hx hy
    rw [hac, show acvalWith mp.base2.acval c₀.name A ConLeche.natName
        = mp.base2.acval ConLeche.natName from acvalWith_ne hnatne]
      at hx hy
    exact hlaw ρ x y hx hy

/-- **`NatOps` at a fresh non-operation cons** — every value-kind
step except the operation's own install discharges its obligation
here.  The disjunctive premise: either the cons is not a definition at
all, or its name is not an operation name. -/
theorem natOps_cons_fresh (mp : EnvModelM V μ env) {φ : Name → Nat}
    (hprev : NatOps mp.base2 φ)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hntc : ConsCrossEnv env c₀)
    (hnothead : (∀ cv v hint, c₀ ≠ .defnInfo cv v hint) ∨
      c₀.name ∉ ConLeche.natOpNames)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    NatOps m₂ φ := by
  intro c hcN cv' v' hint' hf₂
  by_cases hne : c = c₀.name
  · subst hne
    rw [ConLeche.Env.find?_cons_self] at hf₂
    rcases hnothead with hnd | hnn
    · exact absurd (Option.some.inj hf₂) (hnd cv' v' hint')
    · exact absurd hcN hnn
  · exact natOps_entry_cons mp hprev hfresh hntc m₂ hac hcN hne hf₂

/-- **The installing operation's own head packages**, from the
harvest's facts: the annotated value's reading, grading and membership
at the declared type's reading, plus the type's pin.  Splits by the
operation's arity and codomain, concluding both forms
`natOps_install` takes. -/
theorem natSelfHead_install (mp : EnvModelM V μ env) {φ : Name → Nat}
    {c : Name} (hcmem : c ∈ ConLeche.natOpNames)
    {lps : List Name} {type' value' : Expr} {hint : ReducibilityHint}
    (hfresh : env.find? c = none)
    (hpin : ConLeche.natOpTyPinned
      (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩ : Env)
      c type' = true)
    (hs : natLitSupported env = true)
    {Ta : (Name → Nat) → AnnotTerm}
    (hTa : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 type' = some (Ta ψ))
    (hTok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (Ta ψ))
    {A : (Name → Nat) → AnnotTerm}
    (hA2 : ∀ ψ, denoteMeta mp.base2.acval env ψ 2 value' = some (A ψ))
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A ψ))
    (hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (Ta ψ)) :
    (c ≠ ConLeche.natPredName →
      NatBinHead mp.base2 φ value'
        (fun ρ => interp V ρ (mp.base2.acval (natOpCodN c) φ))) ∧
    (c = ConLeche.natPredName →
      NatUnHead mp.base2 φ value'
        (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName φ))) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN0,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hlpN : (ConstantInfo.indInfo cvN caps).toConstantVal.levelParams
      = [] := hlpN0
  constructor
  · -- the binary head
    intro hcp
    have hnu : ¬(c = ConLeche.natPredName) := by
      rintro rfl
      exact hcp rfl
    obtain ⟨mb₁, mb₂, cod, hty, hcmp, hncmp⟩ :=
      natOpTyPinned_shape_bin hnu hpin
    by_cases hccmp : c = ConLeche.natBeqName ∨ c = ConLeche.natBleName
    · -- `Bool` codomain
      obtain ⟨rfl, ci₂, hfB₂, hlpB₂⟩ := hcmp hccmp
      have hBne : ConLeche.boolName ≠ c :=
        ConLeche.Verify.ne_of_mem_natOpNames (by decide) hcmem
      have hfB : env.find? ConLeche.boolName = some ci₂ := by
        rw [ConLeche.Env.find?_cons] at hfB₂
        split at hfB₂
        · next heq =>
          exact absurd (heq.symm.trans (show (ConstantInfo.defnInfo
            ⟨c, lps, type'⟩ value' hint).name = c from rfl)) hBne
        · exact hfB₂
      have hTshape := denoteMeta_pinnedBinTy (codN := ConLeche.boolName)
        (mb₁ := mb₁) (mb₂ := mb₂)
        mp.base2 φ hfN hlpN hfB hlpB₂
      rw [← hty] at hTshape
      obtain heq : Ta φ = _ :=
        Option.some.inj ((hTa φ).symm.trans hTshape)
      have hres := natBinHead_of_parts mp.base2 (hA2 φ)
        (fun ρ => hAok φ ρ)
        (fun ρ => heq ▸ hmemA φ ρ) (fun ρ => heq ▸ hTok φ ρ)
      rwa [show natOpCodN c = ConLeche.boolName from by
        unfold natOpCodN; rw [if_pos hccmp]]
    · -- `Nat` codomain
      obtain rfl := hncmp hccmp
      have hTshape := denoteMeta_pinnedBinTy (codN := ConLeche.natName)
        (mb₁ := mb₁) (mb₂ := mb₂)
        mp.base2 φ hfN hlpN hfN hlpN
      rw [← hty] at hTshape
      obtain heq : Ta φ = _ :=
        Option.some.inj ((hTa φ).symm.trans hTshape)
      have hres := natBinHead_of_parts mp.base2 (hA2 φ)
        (fun ρ => hAok φ ρ)
        (fun ρ => heq ▸ hmemA φ ρ) (fun ρ => heq ▸ hTok φ ρ)
      rwa [show natOpCodN c = ConLeche.natName from by
        unfold natOpCodN; rw [if_neg hccmp]]
  · -- the unary head (`pred`)
    intro hcp
    obtain ⟨mb₁, hty⟩ :=
      natOpTyPinned_shape_un hcp hpin
    have hTshape := denoteMeta_pinnedUnTy mp.base2 φ hfN hlpN
      (mb₁ := mb₁)
    rw [← hty] at hTshape
    obtain heq : Ta φ = _ :=
      Option.some.inj ((hTa φ).symm.trans hTshape)
    exact natUnHead_of_parts mp.base2 (hA2 φ) (fun ρ => hAok φ ρ)
      (fun ρ => heq ▸ hmemA φ ρ) (fun ρ => heq ▸ hTok φ ρ)

/-- **`NatOps` at the operation's own install** — the run-certificate
conversion, end to end: the recorded `isDefEqCore` runs on the
substituted recurrences (`NatEqsRun`) become `interp` equalities
through `DefEqClaim` at the pre-insertion environment, and the
substitution crossing (`denoteMeta_substConst0`) restates them as the raw
equations' readings at the extension. -/
theorem natOps_install (mp : EnvModelM V μ env) {φ : Name → Nat}
    {F : Nat} (hde : DefEqClaim μ mp.base2 φ F)
    (hprev : NatOps mp.base2 φ)
    {c : Name} {lps : List Name} {type' value' : Expr}
    {hint : ReducibilityHint}
    (hcmem : c ∈ ConLeche.natOpNames)
    (hfresh : env.find? c = none)
    (hlpcv : lps = [])
    (hs : natLitSupported env = true)
    (hg2 : natOpGuard
      (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩ : Env) c
      = true)
    (hdepsOk : (ConLeche.natOpDeps c).all
      (ConLeche.natOpStoredOk
        (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩ : Env))
      = true)
    (hruns : NatEqsRun μ F env
      ((ConLeche.natOpEquations 0 c).map fun eq =>
        (Expr.substConst0 c value' eq.1,
         Expr.substConst0 c value' eq.2)))
    {A : (Name → Nat) → AnnotTerm}
    (hA : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ))
    (hAcl : ∀ ψ k, (A ψ).liftN 1 k = A ψ)
    (hvf' : value'.hasFvar = false)
    (hbv' : value'.looseBVarsBounded 0 = true)
    (hSelfBin : c ≠ ConLeche.natPredName →
      NatBinHead mp.base2 φ value'
        (fun ρ => interp V ρ (mp.base2.acval (natOpCodN c) φ)))
    (hSelfUn : c = ConLeche.natPredName →
      NatUnHead mp.base2 φ value'
        (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName φ)))
    (m₂ : EnvModel V
      ⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩)
    (hac : m₂.acval
      = acvalWith mp.base2.acval c A) :
    NatOps m₂ φ := by
  intro cq hcqN cv' v' hint' hf₂
  have hname0 : (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value'
      hint).name = c := rfl
  by_cases hne : cq = c
  case neg =>
    exact natOps_entry_cons mp hprev
      (c₀ := .defnInfo ⟨c, lps, type'⟩ value' hint)
      (hntc := fun _ h => ConstantInfo.noConfusion h)
      (show env.find? (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value'
        hint).name = none from hfresh) m₂
      (show m₂.acval = acvalWith mp.base2.acval
        (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value' hint).name A
        from hac) hcqN
      (show cq ≠ (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value'
        hint).name from hne) hf₂
  subst hne
  refine ⟨hg2, fun eq hq => ?_⟩
  obtain ⟨e1, e2⟩ := eq
  -- the shared preamble: storedness at the prefix, fragments, frames
  have hnh : NatHeads mp.base2 φ := mp.nat_heads φ
  have hvalV : AcvalValid mp.base2 := mp.acvalValid
  obtain ⟨hN₂, hz₂, hs₂, hdeps₂, hbool₂⟩ :=
    ConLeche.Verify.natOpGuard_stored hg2
  have tr : ∀ {n : Name}, n ≠ cq →
      ConLeche.Verify.storedNoLevels
        (⟨.defnInfo ⟨cq, lps, type'⟩ value' hint :: env.consts⟩ : Env) n →
      ConLeche.Verify.storedNoLevels env n := fun hne h =>
    ConLeche.Verify.storedNoLevels_of_cons
      (ci := .defnInfo ⟨cq, lps, type'⟩ value' hint) rfl hne h
  have hnz : ConLeche.natZeroName ≠ cq :=
    ConLeche.Verify.ne_of_mem_natOpNames (by decide) hcqN
  have hns : ConLeche.natSuccName ≠ cq :=
    ConLeche.Verify.ne_of_mem_natOpNames (by decide) hcqN
  have hnN : ConLeche.natName ≠ cq :=
    ConLeche.Verify.ne_of_mem_natOpNames (by decide) hcqN
  have hnT : ConLeche.boolTrueName ≠ cq :=
    ConLeche.Verify.ne_of_mem_natOpNames (by decide) hcqN
  have hnF : ConLeche.boolFalseName ≠ cq :=
    ConLeche.Verify.ne_of_mem_natOpNames (by decide) hcqN
  obtain ⟨hfr1, hfr2⟩ := ConLeche.Verify.natOpEquations_frag
    (env := env) (c := cq) (tr hnz hz₂) (tr hns hs₂)
    (fun n hn hne => tr hne (hdeps₂ n hn))
    (fun hc => tr hnT (hbool₂ (by rcases hc with rfl | rfl <;> simp)).1)
    (fun hc => tr hnF (hbool₂ (by rcases hc with rfl | rfl <;> simp)).2)
    (e1, e2) hq
  have hden : ∀ ψ : Name → Nat,
      ∃ V0, denote mp.base2.cvalE env ψ 0 value' = some V0 :=
    fun ψ => ⟨(A ψ).erase,
      denoteMeta_erase mp.base2.acval_erase 0 value' (hA ψ)⟩
  obtain ⟨hw1, hb1, hL1, hleaf1⟩ :=
    ConLeche.Verify.natFrag_subst_syntax hvf' hbv' hfr1
  obtain ⟨hw2, hb2, hL2, hleaf2⟩ :=
    ConLeche.Verify.natFrag_subst_syntax hvf' hbv' hfr2
  have hrun := hruns _ (List.mem_map.mpr ⟨(e1, e2), hq, rfl⟩)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN0,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hlpN : (ConstantInfo.indInfo cvN caps).toConstantVal.levelParams
      = [] := hlpN0
  -- the crossing and the membership conversion, shared
  have hcross : ∀ (e : Expr), shallowE e = true →
      ∀ {ea : AnnotTerm},
      denoteMeta mp.base2.acval env φ 2 (Expr.substConst0 cq value' e)
        = some ea →
      denoteMeta m₂.acval
          ⟨.defnInfo ⟨cq, lps, type'⟩ value' hint :: env.consts⟩ φ 2 e
        = some ea := by
    intro e hsh ea h
    rw [hac, denoteMeta_substConst0 (c₀ := .defnInfo ⟨cq, lps, type'⟩
        value' hint)
        (show (ConstantInfo.defnInfo ⟨cq, lps, type'⟩ value'
          hint).name = cq from rfl)
        hfresh hlpcv mp.base2.acval_closed (hAcl φ)
        (hA φ) hvf' 2 e hsh]
    exact h
  have hnatne : ConLeche.natName ≠
      (ConstantInfo.defnInfo ⟨cq, lps, type'⟩ value' hint).name := hnN
  have hmemc : ∀ (ρ : Nat → V) (x : V),
      x ∈ˢ interp V ρ (m₂.acval ConLeche.natName φ) →
      x ∈ˢ interp V ρ (mp.base2.acval ConLeche.natName φ) := by
    intro ρ x hx
    rw [hac] at hx
    rwa [show acvalWith mp.base2.acval cq A ConLeche.natName
        = mp.base2.acval ConLeche.natName from acvalWith_ne hnN] at hx
  -- stored dependency heads (the pinned types via `hdepsOk`)
  have hdepBin : ∀ o ∈ ConLeche.natOpDeps cq, o ≠ cq →
      ¬(o = ConLeche.natBeqName ∨ o = ConLeche.natBleName) →
      ¬(o = ConLeche.natPredName) →
      NatBinHead mp.base2 φ (.const o [])
        (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName φ)) := by
    intro o ho hone honcmp honun
    obtain ⟨cvo, vo, hino, hfo, hlpo, hpino⟩ :=
      natOpStoredOk_descend (c₀ := .defnInfo ⟨cq, lps, type'⟩ value'
        hint) hone (List.all_eq_true.mp hdepsOk o (by simpa using ho))
    obtain ⟨mb₁, mb₂, cod, hty, -, hcodN⟩ :=
      natOpTyPinned_shape_bin honun hpino
    exact natBinHead_of_stored (ψ := φ) mp hfo hlpo
      (by rw [hty, hcodN honcmp]) hfN hlpN hfN hlpN
  have hdepUn : ∀ o ∈ ConLeche.natOpDeps cq, o ≠ cq →
      o = ConLeche.natPredName →
      NatUnHead mp.base2 φ (.const o [])
        (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName φ)) := by
    intro o ho hone houn
    obtain ⟨cvo, vo, hino, hfo, hlpo, hpino⟩ :=
      natOpStoredOk_descend (c₀ := .defnInfo ⟨cq, lps, type'⟩ value'
        hint) hone (List.all_eq_true.mp hdepsOk o (by simpa using ho))
    obtain ⟨mb₁, hty⟩ := natOpTyPinned_shape_un houn hpino
    exact natUnHead_of_stored (ψ := φ) mp hfo hlpo hty hfN hlpN
  -- one equation, packaged: the shared closing move
  have close : ∀ {la ra : AnnotTerm},
      denoteMeta mp.base2.acval env φ 2
        (Expr.substConst0 cq value' e1) = some la →
      (∀ ρ : Nat → V, Sat V (natCtx2 mp.base2 φ) ρ →
        WellDenotedV V ρ la) →
      denoteMeta mp.base2.acval env φ 2
        (Expr.substConst0 cq value' e2) = some ra →
      (∀ ρ : Nat → V, Sat V (natCtx2 mp.base2 φ) ρ →
        WellDenotedV V ρ ra) →
      ∃ L R, denoteMeta m₂.acval
          ⟨.defnInfo ⟨cq, lps, type'⟩ value' hint :: env.consts⟩ φ 2
          e1 = some L ∧
        denoteMeta m₂.acval
          ⟨.defnInfo ⟨cq, lps, type'⟩ value' hint :: env.consts⟩ φ 2
          e2 = some R ∧
        ∀ (ρ : Nat → V) (x y : V),
          x ∈ˢ interp V ρ (m₂.acval ConLeche.natName φ) →
          y ∈ˢ interp V ρ (m₂.acval ConLeche.natName φ) →
          interp V (cons y (cons x ρ)) L
            = interp V (cons y (cons x ρ)) R := by
    intro la ra hla hga hra hgr
    refine ⟨la, ra,
      hcross e1 (ConLeche.Verify.shallowE_of_natFragOk hfr1) hla,
      hcross e2 (ConLeche.Verify.shallowE_of_natFragOk hfr2) hra,
      fun ρ x y hx hy => ?_⟩
    exact natEqLaw_of_run mp hde hfN hlpN hrun hw1 hb1 hL1 hleaf1
      hw2 hb2 hL2 hleaf2 hla hga hra hgr ρ x y (hmemc ρ x hx)
      (hmemc ρ y hy)
  -- the per-operation equation analysis
  clear hf₂ hcqN
  rcases (show cq = ConLeche.natPredName ∨ cq = ConLeche.natAddName ∨
      cq = ConLeche.natSubName ∨ cq = ConLeche.natMulName ∨
      cq = ConLeche.natPowName ∨ cq = ConLeche.natBeqName ∨
      cq = ConLeche.natBleName from by
    simpa [ConLeche.natOpNames] using hcmem) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `Nat.pred`
    have hun : NatUnHead mp.base2 φ value'
        (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName φ)) :=
      hSelfUn rfl
    have hvx := natArg_var0 mp.base2 φ
    have hz := natArg_zero mp.base2 hnh hvalV hs
    simp +decide [ConLeche.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- pred 0 = 0
      obtain ⟨la, hla, hga⟩ := NatArg.package mp.base2
        (natArg_of_un mp.base2 hun hz)
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2 hz
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- pred (succ x) = x
      obtain ⟨la, hla, hga⟩ := NatArg.package mp.base2
        (natArg_of_un mp.base2 hun
          (natArg_succ mp.base2 hnh hvalV hs hvx))
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2 hvx
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.add`
    have hbin : NatBinHead mp.base2 φ value'
        (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName φ)) := by
      have h := hSelfBin (by decide)
      simpa only [show natOpCodN ConLeche.natAddName = ConLeche.natName
        from by unfold natOpCodN; rw [if_neg (by decide)]] using h
    have hvx := natArg_var0 mp.base2 φ
    have hvy := natArg_var1 mp.base2 φ
    have hz := natArg_zero mp.base2 hnh hvalV hs
    simp +decide [ConLeche.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- add x 0 = x
      obtain ⟨la, hla, hga⟩ :=
        natBinHead_app_package mp.base2 hbin hvx hz
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2 hvx
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- add x (succ y) = succ (add x y)
      obtain ⟨la, hla, hga⟩ := natBinHead_app_package mp.base2 hbin
        hvx (natArg_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2
        (natArg_succ mp.base2 hnh hvalV hs
          (natArg_of_bin mp.base2 hbin hvx hvy))
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.sub`
    have hbin : NatBinHead mp.base2 φ value'
        (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName φ)) := by
      have h := hSelfBin (by decide)
      simpa only [show natOpCodN ConLeche.natSubName = ConLeche.natName
        from by unfold natOpCodN; rw [if_neg (by decide)]] using h
    have hpred := hdepUn ConLeche.natPredName (by decide) (by decide) rfl
    have hvx := natArg_var0 mp.base2 φ
    have hvy := natArg_var1 mp.base2 φ
    have hz := natArg_zero mp.base2 hnh hvalV hs
    simp +decide [ConLeche.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- sub x 0 = x
      obtain ⟨la, hla, hga⟩ :=
        natBinHead_app_package mp.base2 hbin hvx hz
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2 hvx
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- sub x (succ y) = pred (sub x y)
      obtain ⟨la, hla, hga⟩ := natBinHead_app_package mp.base2 hbin
        hvx (natArg_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2
        (natArg_of_un mp.base2 hpred
          (natArg_of_bin mp.base2 hbin hvx hvy))
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.mul`
    have hbin : NatBinHead mp.base2 φ value'
        (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName φ)) := by
      have h := hSelfBin (by decide)
      simpa only [show natOpCodN ConLeche.natMulName = ConLeche.natName
        from by unfold natOpCodN; rw [if_neg (by decide)]] using h
    have hadd := hdepBin ConLeche.natAddName (by decide) (by decide)
      (by decide) (by decide)
    have hvx := natArg_var0 mp.base2 φ
    have hvy := natArg_var1 mp.base2 φ
    have hz := natArg_zero mp.base2 hnh hvalV hs
    simp +decide [ConLeche.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- mul x 0 = 0
      obtain ⟨la, hla, hga⟩ :=
        natBinHead_app_package mp.base2 hbin hvx hz
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2 hz
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- mul x (succ y) = add (mul x y) x
      obtain ⟨la, hla, hga⟩ := natBinHead_app_package mp.base2 hbin
        hvx (natArg_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2
        (natArg_of_bin mp.base2 hadd
          (natArg_of_bin mp.base2 hbin hvx hvy) hvx)
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.pow`
    have hbin : NatBinHead mp.base2 φ value'
        (fun ρ => interp V ρ (mp.base2.acval ConLeche.natName φ)) := by
      have h := hSelfBin (by decide)
      simpa only [show natOpCodN ConLeche.natPowName = ConLeche.natName
        from by unfold natOpCodN; rw [if_neg (by decide)]] using h
    have hmul := hdepBin ConLeche.natMulName (by decide) (by decide)
      (by decide) (by decide)
    have hvx := natArg_var0 mp.base2 φ
    have hvy := natArg_var1 mp.base2 φ
    have hz := natArg_zero mp.base2 hnh hvalV hs
    simp +decide [ConLeche.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- pow x 0 = 1
      obtain ⟨la, hla, hga⟩ :=
        natBinHead_app_package mp.base2 hbin hvx hz
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2
        (natArg_succ mp.base2 hnh hvalV hs hz)
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- pow x (succ y) = mul (pow x y) x
      obtain ⟨la, hla, hga⟩ := natBinHead_app_package mp.base2 hbin
        hvx (natArg_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ := NatArg.package mp.base2
        (natArg_of_bin mp.base2 hmul
          (natArg_of_bin mp.base2 hbin hvx hvy) hvx)
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.beq`
    have hbin := hSelfBin (by decide)
    obtain ⟨ciT, hfT, hlpT⟩ := ConLeche.Verify.storedNoLevels_exists
      (tr hnT (hbool₂ (by decide)).1)
    obtain ⟨ciF, hfF, hlpF⟩ := ConLeche.Verify.storedNoLevels_exists
      (tr hnF (hbool₂ (by decide)).2)
    have hvx := natArg_var0 mp.base2 φ
    have hvy := natArg_var1 mp.base2 φ
    have hz := natArg_zero mp.base2 hnh hvalV hs
    simp +decide [ConLeche.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- beq 0 0 = true
      obtain ⟨la, hla, hga⟩ :=
        natBinHead_app_package mp.base2 hbin hz hz
      obtain ⟨ra, hra, hgr⟩ :=
        natConst_package mp.base2 hvalV hfT hlpT
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- beq 0 (succ y) = false
      obtain ⟨la, hla, hga⟩ := natBinHead_app_package mp.base2 hbin
        hz (natArg_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ :=
        natConst_package mp.base2 hvalV hfF hlpF
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- beq (succ x) 0 = false
      obtain ⟨la, hla, hga⟩ := natBinHead_app_package mp.base2 hbin
        (natArg_succ mp.base2 hnh hvalV hs hvx) hz
      obtain ⟨ra, hra, hgr⟩ :=
        natConst_package mp.base2 hvalV hfF hlpF
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- beq (succ x) (succ y) = beq x y
      obtain ⟨la, hla, hga⟩ := natBinHead_app_package mp.base2 hbin
        (natArg_succ mp.base2 hnh hvalV hs hvx)
        (natArg_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ :=
        natBinHead_app_package mp.base2 hbin hvx hvy
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.ble`
    have hbin := hSelfBin (by decide)
    obtain ⟨ciT, hfT, hlpT⟩ := ConLeche.Verify.storedNoLevels_exists
      (tr hnT (hbool₂ (by decide)).1)
    obtain ⟨ciF, hfF, hlpF⟩ := ConLeche.Verify.storedNoLevels_exists
      (tr hnF (hbool₂ (by decide)).2)
    have hvx := natArg_var0 mp.base2 φ
    have hvy := natArg_var1 mp.base2 φ
    have hz := natArg_zero mp.base2 hnh hvalV hs
    simp +decide [ConLeche.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- ble 0 y = true
      obtain ⟨la, hla, hga⟩ :=
        natBinHead_app_package mp.base2 hbin hz hvy
      obtain ⟨ra, hra, hgr⟩ :=
        natConst_package mp.base2 hvalV hfT hlpT
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- ble (succ x) 0 = false
      obtain ⟨la, hla, hga⟩ := natBinHead_app_package mp.base2 hbin
        (natArg_succ mp.base2 hnh hvalV hs hvx) hz
      obtain ⟨ra, hra, hgr⟩ :=
        natConst_package mp.base2 hvalV hfF hlpF
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- ble (succ x) (succ y) = ble x y
      obtain ⟨la, hla, hga⟩ := natBinHead_app_package mp.base2 hbin
        (natArg_succ mp.base2 hnh hvalV hs hvx)
        (natArg_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ :=
        natBinHead_app_package mp.base2 hbin hvx hvy
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra

end ConLeche.Model
