module

public import IxCK.Kernel.Model.GuardSignature
public import IxCK.Kernel.ExprOps

@[expose] public section

/-!
# A partial, context-independent classifier for field zero-signatures

The classifier operates on de Bruijn syntax and instantiated declarations. It is a data
computation, not a typing judgement: the circuit must separately infer each field sort and
compare zero-signatures. In Pi formation the domain universe is deliberately discarded, since
only the codomain universe determines zero-ness.

Every lookup on a successful computation is positive. Consequently extending the declaration
lookup preserves the exact result. This also separates the computation from validation limits:
the same raw declarations and field context give the same result at any limit.
-/

namespace Ix.Kernel.GuardClassifier

/-- Instantiated declared types and unfoldable definition values. Neither operation types terms. -/
structure Lookup (md : Mode) where
  typeOf : Key md → List Level → Option (Expr md)
  valueOf : Key md → List Level → Option (Expr md)

/-- An extension keeps all successful answers. Negative lookups need not be preserved. -/
structure Lookup.Extends (a b : Lookup md) : Prop where
  typeOf : ∀ k us e, a.typeOf k us = some e → b.typeOf k us = some e
  valueOf : ∀ k us e, a.valueOf k us = some e → b.valueOf k us = some e

private theorem bind_preserved {α β : Type} {a b : Option α} {f g : α → Option β}
    (ha : ∀ x, a = some x → b = some x)
    (hf : ∀ x y, f x = some y → g x = some y)
    {r : β} (h : a.bind f = some r) : b.bind g = some r := by
  obtain ⟨x, hx, hr⟩ := Option.bind_eq_some_iff.mp h
  exact Option.bind_eq_some_iff.mpr ⟨x, ha x hx, hf x r hr⟩

/-- A concrete lookup from stored kernel syntax. Only definitions unfold. -/
def Lookup.ofEnv (env : Env md) : Lookup md where
  typeOf k us := do
    let ci ← env.find? k
    if us.length = ci.toConstantVal.levelParams.length then
      some (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us)
    else none
  valueOf k us := do
    let ci ← env.find? k
    match ci with
    | .defnInfo cv value _ =>
      if us.length = cv.levelParams.length then
        some (value.instantiateLevelParams cv.levelParams us)
      else none
    | _ => none

/-- Keeping stored declarations produces the lookup extension required by the classifier. -/
theorem Lookup.ofEnv_extends {env env' : Env md}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci) :
    (Lookup.ofEnv env).Extends (Lookup.ofEnv env') := by
  constructor
  · intro k us e h
    exact bind_preserved (fun ci hci => hext k ci hci) (fun _ _ h => h) h
  · intro k us e h
    exact bind_preserved (fun ci hci => hext k ci hci) (fun _ _ h => h) h

/-- Expose a rigid head by definition unfolding, beta and let substitution. Stuck heads fail.
Beta here is only a data operation; independent typing supplies its semantic certificate. -/
def head (look : Lookup md) : Nat → Expr md → Option (Expr md)
  | 0, _ => none
  | _ + 1, e@(.sort _) => some e
  | _ + 1, e@(.forallE ..) => some e
  | _ + 1, e@(.lam ..) => some e
  | fuel + 1, .const k us => (look.valueOf k us).bind (head look fuel)
  | fuel + 1, .app f a => (head look fuel f).bind fun
      | .lam _ body _ => head look fuel (body.instantiate1Lift a)
      | _ => none
  | fuel + 1, .letE _ value body _ => head look fuel (body.instantiate1Lift value)
  | _ + 1, _ => none

/-- Successful normalization depends only on the positive declarations it read. -/
theorem head_mono {a b : Lookup md} (hext : a.Extends b) :
    ∀ fuel e r, head a fuel e = some r → head b fuel e = some r := by
  intro fuel
  induction fuel with
  | zero => intro e r h; exact h
  | succ fuel ih =>
    intro e r h
    cases e <;> simp only [head] at h ⊢
    case const k us =>
      exact bind_preserved (hext.valueOf k us) (fun e r h => ih e r h) h
    case app f arg =>
      refine bind_preserved (fun e h => ih f e h) ?_ h
      intro e r h
      cases e <;> first | exact ih _ _ h | exact h
    case letE ty value body mb => exact ih _ _ h
    all_goals exact h

/-- Structural type-shape calculation. Pi formation retains only the body universe; argument
checking is deliberately absent, since this result is compared to an independently inferred sort. -/
def infer (look : Lookup md) : Nat → List (Expr md) → Expr md → Option (Expr md)
  | 0, _, _ => none
  | _ + 1, _, .sort u => some (.sort (.succ u))
  | _ + 1, ctx, .bvar i => (ctx[i]?).map (Expr.liftLooseBVars (i + 1) 0)
  | _ + 1, _, .fvar _ ty => some ty
  | _ + 1, _, .const k us => look.typeOf k us
  | fuel + 1, ctx, .app f arg => do
    let tf ← infer look fuel ctx f
    let .forallE _ body _ ← head look fuel tf | none
    pure (body.instantiate1Lift arg)
  | fuel + 1, ctx, .forallE ty body _ => do
    let tb ← infer look fuel (ty :: ctx) body
    let .sort u ← head look fuel tb | none
    pure (.sort u)
  | fuel + 1, ctx, .lam ty body mb => do
    let tb ← infer look fuel (ty :: ctx) body
    pure (.forallE ty tb mb)
  | fuel + 1, ctx, .letE _ value body _ => infer look fuel ctx (body.instantiate1Lift value)
  | _ + 1, _, _ => none

/-- Successful classification is stable under positive lookup extension. -/
theorem infer_mono {a b : Lookup md} (hext : a.Extends b) :
    ∀ fuel ctx e r, infer a fuel ctx e = some r → infer b fuel ctx e = some r := by
  intro fuel
  induction fuel with
  | zero => intro ctx e r h; exact h
  | succ fuel ih =>
    intro ctx e r h
    cases e <;> simp only [infer] at h ⊢
    case const k us => exact hext.typeOf k us r h
    case app f arg =>
      refine bind_preserved (fun e h => ih ctx f e h) ?_ h
      intro e r h
      exact bind_preserved (fun e' h => head_mono hext fuel e e' h) (fun _ _ h => h) h
    case forallE ty body mb =>
      refine bind_preserved (fun e h => ih (ty :: ctx) body e h) ?_ h
      intro e r h
      exact bind_preserved (fun e' h => head_mono hext fuel e e' h) (fun _ _ h => h) h
    case lam ty body mb =>
      exact bind_preserved (fun e h => ih (ty :: ctx) body e h) (fun _ _ h => h) h
    case letE ty value body mb => exact ih ctx _ r h
    all_goals exact h

/-- The field classifier succeeds exactly when its structural type exposes a sort. -/
def sortSignature (look : Lookup md) (fuel : Nat) (ctx : List (Expr md)) (e : Expr md) :
    Option Level := do
  let t ← infer look fuel ctx e
  let .sort u ← head look fuel t | none
  pure (Level.guardSignatureLevel u)

/-- This is the cross-environment functionality contract for a successful field classifier. -/
theorem sortSignature_mono {a b : Lookup md} (hext : a.Extends b)
    {fuel : Nat} {ctx : List (Expr md)} {e : Expr md} {s : Level}
    (h : sortSignature a fuel ctx e = some s) : sortSignature b fuel ctx e = some s := by
  refine bind_preserved (fun t h => infer_mono hext fuel ctx e t h) ?_ h
  intro t r h
  exact bind_preserved (fun t' h => head_mono hext fuel t t' h) (fun _ _ h => h) h

/-- Two successful classifications agree when their positive declaration answers embed in one
common lookup. The two source computations may use unrelated validation limits. -/
theorem sortSignature_agree {a b common : Lookup md}
    (ha : a.Extends common) (hb : b.Extends common)
    {fuel : Nat} {ctx : List (Expr md)} {e : Expr md} {s t : Level}
    (hs : sortSignature a fuel ctx e = some s)
    (ht : sortSignature b fuel ctx e = some t) : s = t :=
  Option.some.inj ((sortSignature_mono ha hs).symm.trans (sortSignature_mono hb ht))

/-- Explicit installation and use comparisons to one stable classifier result imply the
projection guard's required zero transfer, after arbitrary universe substitution. No typing
uniqueness or equality of the two source role contexts is assumed. -/
theorem checked_zero_transfer {a b common : Lookup md}
    (ha : a.Extends common) (hb : b.Extends common)
    {fuel : Nat} {ctx : List (Expr md)} {e : Expr md} {s t stored used : Level}
    (hs : sortSignature a fuel ctx e = some s)
    (ht : sortSignature b fuel ctx e = some t)
    (hstore : ∀ φ, Level.eval φ (Level.guardSignatureLevel stored) = Level.eval φ s)
    (huse : ∀ φ, Level.eval φ (Level.guardSignatureLevel used) = Level.eval φ t)
    (ks : List LevelParam) (us : List Level) (φ : LevelParam → Nat)
    (hz : Level.eval φ (Level.subst ks us used) = 0) :
    Level.eval φ (Level.subst ks us stored) = 0 := by
  have hst : s = t := sortSignature_agree ha hb hs ht
  subst hst
  exact (Level.guardSignatureLevel_subst_zero_iff
    (fun ψ => (huse ψ).trans (hstore ψ).symm) ks us φ).mp hz

/-- Extra depth cannot change a successful head result. -/
theorem head_succ (look : Lookup md) :
    ∀ fuel e r, head look fuel e = some r → head look (fuel + 1) e = some r := by
  intro fuel
  induction fuel with
  | zero => intro e r h; cases h
  | succ fuel ih =>
    intro e r h
    cases e <;> simp only [head] at h ⊢
    case const k us =>
      exact bind_preserved (fun _ h => h) (fun e r h => ih e r h) h
    case app f arg =>
      refine bind_preserved (fun e h => ih f e h) ?_ h
      intro e r h
      cases e <;> first | exact ih _ _ h | exact h
    case letE ty value body mb => exact ih _ _ h
    all_goals exact h

/-- Extra depth cannot change a successful structural type result. -/
theorem infer_succ (look : Lookup md) :
    ∀ fuel ctx e r, infer look fuel ctx e = some r → infer look (fuel + 1) ctx e = some r := by
  intro fuel
  induction fuel with
  | zero => intro ctx e r h; cases h
  | succ fuel ih =>
    intro ctx e r h
    cases e <;> simp only [infer] at h ⊢
    case app f arg =>
      refine bind_preserved (fun e h => ih ctx f e h) ?_ h
      intro e r h
      exact bind_preserved (fun e' h => head_succ look fuel e e' h) (fun _ _ h => h) h
    case forallE ty body mb =>
      refine bind_preserved (fun e h => ih (ty :: ctx) body e h) ?_ h
      intro e r h
      exact bind_preserved (fun e' h => head_succ look fuel e e' h) (fun _ _ h => h) h
    case lam ty body mb =>
      exact bind_preserved (fun e h => ih (ty :: ctx) body e h) (fun _ _ h => h) h
    case letE ty value body mb => exact ih ctx _ r h
    all_goals exact h

/-- Canonical reading may erase a let node. A successful classifier remains successful at
its erased reading with the original depth budget. -/
theorem infer_eraseLet (look : Lookup md) {fuel : Nat} {ctx : List (Expr md)}
    {ty value body r : Expr md} {lm : LetMeta}
    (h : infer look fuel ctx (.letE ty value body lm) = some r) :
    infer look fuel ctx (body.instantiate1Lift value) = some r := by
  cases fuel with
  | zero => cases h
  | succ fuel => exact infer_succ look fuel ctx _ r h

/-- The same canonical-let transport for head exposure. -/
theorem head_eraseLet (look : Lookup md) {fuel : Nat}
    {ty value body r : Expr md} {lm : LetMeta}
    (h : head look fuel (.letE ty value body lm) = some r) :
    head look fuel (body.instantiate1Lift value) = some r := by
  cases fuel with
  | zero => cases h
  | succ fuel => exact head_succ look fuel _ r h

/-- The minimal directed guard contract uses zero-set comparisons, so the typed level may
be a semantically equivalent reading of the runtime level returned by ordinary inference. -/
theorem checked_zero_transfer_of_zero_iff {a b common : Lookup md}
    (ha : a.Extends common) (hb : b.Extends common)
    {fuel : Nat} {ctx : List (Expr md)} {e : Expr md} {s t stored used : Level}
    (hs : sortSignature a fuel ctx e = some s)
    (ht : sortSignature b fuel ctx e = some t)
    (hstore : ∀ φ, Level.eval φ stored = 0 ↔ Level.eval φ s = 0)
    (huse : ∀ φ, Level.eval φ used = 0 ↔ Level.eval φ t = 0)
    (ks : List LevelParam) (us : List Level) (φ : LevelParam → Nat)
    (hz : Level.eval φ (Level.subst ks us used) = 0) :
    Level.eval φ (Level.subst ks us stored) = 0 := by
  have hst : s = t := sortSignature_agree ha hb hs ht
  subst hst
  rw [Level.eval_subst] at hz ⊢
  exact (hstore _).mpr ((huse _).mp hz)

/-- A sort is a concrete member of the classifier's domain, in every lookup and context. -/
theorem sortSignature_sort (look : Lookup md) (ctx : List (Expr md)) (u : Level) :
    sortSignature look 1 ctx (.sort u) = some (.succ .zero) := rfl

/-- A raw open argument must be lifted beneath the result's binder. This regression distinguishes
capture-avoiding heap substitution from substitution of already-opened kernel terms. -/
theorem head_open_beta (look : Lookup md) :
    head look 3
      (.app (.lam (.sort (.succ .zero))
        (.forallE (.sort (.succ .zero)) (.bvar 1) .leanNever) .leanNever) (.bvar 0)) =
      some (.forallE (.sort (.succ .zero)) (.bvar 1) .leanNever) := rfl


end Ix.Kernel.GuardClassifier
