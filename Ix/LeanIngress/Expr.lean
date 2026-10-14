import Ix.Environment
import IxC.Kernel.Expr

/-! # Lean's terms as the checker's terms

The term half of the Source-mode ingress (`Ix.LeanIngress`): an
`Ix.Expr` (Lean's term as `Ix.CanonM` canonicalizes it) becomes an
`Ix.Kernel.Expr` with nothing hashed and nothing rewritten.

* **Names** are Lean's own: `Ix.Name` ↦ `Ix.Kernel.Name` component by
  component, the hash fields dropped (`ingressName`). Constants keep their
  Lean names, so the checker's pinned names (`Eq`, `Nat`, `Quot`, the literal
  support, the `Nat` operations, the standard axioms) are met under the names
  it pins.
* **Levels** are Lean's levels, constructor by constructor; they are not
  canonicalized. A level parameter becomes its position `σ n` under the
  constant's numbering `σ` of its own level parameters
  (`Ix.LeanIngress.Numbering`). A level metavariable is refused.
* **Terms**: `mdata` is erased, binder names and binder infos and `letE`'s
  `nonDep` flag are dropped, every binder carries `pw := .never` (the checker's
  annotation pass computes the datum, as for the Ixon reader's terms),
  literals stay literals and a projection names its structure. A free variable
  or a metavariable is refused.

`ingressExpr` is the specification, a structural recursion over the term
tree. A canonicalized term is a DAG (`CanonM` interns structurally equal
subterms, and a proof's tree can be exponentially larger than its DAG). The
ingress converts the terms of a declaration group's constants that number
their level parameters alike together, through `ingressExprs`, and compiled
code runs `ingressExprsShared` for them, the same function computed on the
DAG with one memo for all the terms, substituted by
`@[csimp]` on its proof (`ingressExprs_eq_shared`). The memo is verified, not
trusted, in the arrangement of the checker's `Expr.beqMemo`:

* an entry (`Entry`) is a node, its conversion, and the proof that the
  conversion is `ingressExpr` of the node, so there is no invariant about the
  map;
* a probe finds a candidate under the node's address (`withPtrAddr`) and
  confirms it by identity (`withPtrEq`). At run time the pointer test decides:
  the memo holds the stored node, so a stored node at the probed address is
  the probed node. In the pure model, where every address is `0`, the fallback
  `ingressIs` decides that the stored value is the conversion of the probed
  node, which is the fact the proof reads. No hash is consulted, neither
  the embedded BLAKE3 hash nor any other;
* the memo travels behind `Squash` and every result carries its proof, so a
  result is a subsingleton (the side condition of `withPtrAddr`).

The trust is the compiler's substitution on these kernel-checked equations
and the runtime's `withPtrAddr`/`withPtrEq`, as for the checker's own
`beqMemo`. -/

namespace Ix.LeanIngress

open Ix.Kernel (LevelParam)

abbrev KName := Ix.Kernel.Name
abbrev KLevel := Ix.Kernel.Level
abbrev KExpr := Ix.Kernel.Expr

/-- A term the checker has no syntax for. -/
inductive ExprError where
  | fvar (name : KName)
  | mvar (name : KName)
  | levelMVar (name : KName)
  deriving Repr, Inhabited, BEq

def ingressName : Ix.Name → KName
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ingressName p) s
  | .num p n _ => .num (ingressName p) n

instance : ToString ExprError where
  toString
    | .fvar n => s!"free variable {n}"
    | .mvar n => s!"metavariable {n}"
    | .levelMVar n => s!"level metavariable {n}"

def ingressLevel (σ : Ix.Name → LevelParam) : Ix.Level → Except ExprError KLevel
  | .zero _ => pure .zero
  | .succ u _ => return .succ (← ingressLevel σ u)
  | .max u v _ => return .max (← ingressLevel σ u) (← ingressLevel σ v)
  | .imax u v _ => return .imax (← ingressLevel σ u) (← ingressLevel σ v)
  | .param n _ => pure (.param (σ n))
  | .mvar n _ => throw (.levelMVar (ingressName n))

/-- **The term conversion** (the specification), under the constant's
numbering `σ` of its level parameters. -/
def ingressExpr (σ : Ix.Name → LevelParam) : Ix.Expr → Except ExprError KExpr
  | .bvar i _ => pure (Ix.Kernel.Expr.mkBvar i)
  | .fvar n _ => throw (.fvar (ingressName n))
  | .mvar n _ => throw (.mvar (ingressName n))
  | .sort u _ => return .sort (← ingressLevel σ u)
  | .const n us _ => return .const (ingressName n) (← us.toList.mapM (ingressLevel σ))
  | .app f a _ => return .app (← ingressExpr σ f) (← ingressExpr σ a)
  | .lam _ t b _ _ => return .lam (← ingressExpr σ t) (← ingressExpr σ b) { pw := .never }
  | .forallE _ t b _ _ => return .forallE (← ingressExpr σ t) (← ingressExpr σ b) { pw := .never }
  | .letE _ t v b _ _ =>
    return .letE (← ingressExpr σ t) (← ingressExpr σ v) (← ingressExpr σ b)
  | .lit (.natVal n) _ => pure (.lit (.natVal n))
  | .lit (.strVal s) _ => pure (.lit (.strVal s))
  | .mdata _ e _ => ingressExpr σ e
  | .proj n i e _ => return .proj (ingressName n) i (← ingressExpr σ e)

/-- Metadata is erased. -/
theorem ingressExpr_mdata (σ : Ix.Name → LevelParam) (d : Array (Ix.Name × Ix.DataValue))
    (e : Ix.Expr) (h : Address) : ingressExpr σ (.mdata d e h) = ingressExpr σ e := rfl

/-- The conversion of several terms. -/
def ingressExprs (σ : Ix.Name → LevelParam) (es : List Ix.Expr) : Except ExprError (List KExpr) :=
  es.mapM (ingressExpr σ)

/-! ## The conversion on the DAG

The walk converts terms under one numbering `σ`, so a memo holds the
conversions under that numbering only. -/

section Shared

variable (σ : Ix.Name → LevelParam)

/-- Is `value` the conversion of `e`? The fallback of a memo probe (pure
model only). -/
def ingressIs (e : Ix.Expr) (value : KExpr) : Bool :=
  match ingressExpr σ e with
  | .ok v => decide (v = value)
  | .error _ => false

variable {σ} in
theorem ingressIs_iff {e : Ix.Expr} {value : KExpr} :
    ingressIs σ e value = true ↔ ingressExpr σ e = .ok value := by
  unfold ingressIs
  split <;> simp_all

/-- A memo entry: a visited node, its conversion, and the proof. -/
structure Entry where
  node : Ix.Expr
  value : KExpr
  ok : ingressExpr σ node = .ok value

/-- The memo: entries under the address of their node. -/
abbrev Memo := Std.HashMap Nat (Entry σ)

/-- One node's result: its conversion, proved to be the tree conversion, and
the memo after it. -/
structure Res (e : Ix.Expr) where
  val : Except ExprError KExpr
  eq : val = ingressExpr σ e
  memo : Memo σ

/-- The result behind `Squash`: a subsingleton, so it may depend on
addresses. -/
abbrev Out (e : Ix.Expr) := Squash (Res σ e)

/-- The entry under `key`, if it is `e`'s: confirmed by identity
(`withPtrEq`), whose pure meaning is `ingressIs`. -/
@[inline] def probe (memo : Memo σ) (key : Nat) (e : Ix.Expr) :
    Option { v : KExpr // ingressExpr σ e = .ok v } :=
  match memo.get? key with
  | none => none
  | some p =>
    if h : withPtrEq p.node e (fun _ => ingressIs σ e p.value)
        (fun same => ingressIs_iff.mpr (same ▸ p.ok)) = true then
      some ⟨p.value, ingressIs_iff.mp h⟩
    else none

theorem ingressExpr_app (f a : Ix.Expr) (h : Address) : ingressExpr σ (.app f a h) =
    (ingressExpr σ f >>= fun x => ingressExpr σ a >>= fun y => pure (.app x y)) := rfl

theorem ingressExpr_lam (n : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo) (h : Address) :
    ingressExpr σ (.lam n t b bi h) =
    (ingressExpr σ t >>= fun x => ingressExpr σ b >>= fun y => pure (.lam x y { pw := .never })) := rfl

theorem ingressExpr_forallE (n : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo) (h : Address) :
    ingressExpr σ (.forallE n t b bi h) =
    (ingressExpr σ t >>= fun x => ingressExpr σ b >>= fun y => pure (.forallE x y { pw := .never })) :=
  rfl

theorem ingressExpr_letE (n : Ix.Name) (t v b : Ix.Expr) (nd : Bool) (h : Address) :
    ingressExpr σ (.letE n t v b nd h) =
    (ingressExpr σ t >>= fun x => ingressExpr σ v >>= fun y =>
      ingressExpr σ b >>= fun z => pure (.letE x y z)) := rfl

theorem ingressExpr_proj (n : Ix.Name) (i : Nat) (b : Ix.Expr) (h : Address) :
    ingressExpr σ (.proj n i b h) =
    (ingressExpr σ b >>= fun y => pure (.proj (ingressName n) i y)) := rfl

/-- The DAG walk. A node is probed under its address; on a miss it is
converted from its children's results (each child through the walk, so a
shared child is converted once) and, on success, recorded. A failure is not
recorded: it ends the conversion. -/
def go (memo : Memo σ) (e : @& Ix.Expr) : Out σ e :=
  withPtrAddr e (fun pa =>
    match probe σ memo pa.toNat e with
    | some hit => Squash.mk ⟨.ok hit.1, hit.2.symm, memo⟩
    | none =>
      let node : Out σ e := match e with
        | .bvar i _ => Squash.mk ⟨.ok (Ix.Kernel.Expr.mkBvar i), rfl, memo⟩
        | .fvar n _ => Squash.mk ⟨throw (.fvar (ingressName n)), rfl, memo⟩
        | .mvar n _ => Squash.mk ⟨throw (.mvar (ingressName n)), rfl, memo⟩
        | .sort u _ => Squash.mk ⟨(do return .sort (← ingressLevel σ u)), rfl, memo⟩
        | .const n us _ =>
          Squash.mk ⟨(do return .const (ingressName n) (← us.toList.mapM (ingressLevel σ))), rfl,
            memo⟩
        | .lit (.natVal n) _ => Squash.mk ⟨.ok (.lit (.natVal n)), rfl, memo⟩
        | .lit (.strVal s) _ => Squash.mk ⟨.ok (.lit (.strVal s)), rfl, memo⟩
        | .mdata d b h =>
          Squash.lift (go memo b) fun r =>
            Squash.mk ⟨r.val, r.eq.trans (ingressExpr_mdata σ d b h).symm, r.memo⟩
        | .app f a h =>
          Squash.lift (go memo f) fun r₁ =>
            match h₁ : r₁.val with
            | .error err =>
              Squash.mk ⟨.error err, by rw [ingressExpr_app, ← r₁.eq, h₁]; rfl, r₁.memo⟩
            | .ok x => Squash.lift (go r₁.memo a) fun r₂ =>
              match h₂ : r₂.val with
              | .error err =>
                Squash.mk ⟨.error err, by rw [ingressExpr_app, ← r₁.eq, h₁, ← r₂.eq, h₂]; rfl,
                  r₂.memo⟩
              | .ok y =>
                Squash.mk ⟨.ok (.app x y), by rw [ingressExpr_app, ← r₁.eq, h₁, ← r₂.eq, h₂]; rfl,
                  r₂.memo⟩
        | .lam n t b bi h =>
          Squash.lift (go memo t) fun r₁ =>
            match h₁ : r₁.val with
            | .error err =>
              Squash.mk ⟨.error err, by rw [ingressExpr_lam, ← r₁.eq, h₁]; rfl, r₁.memo⟩
            | .ok x => Squash.lift (go r₁.memo b) fun r₂ =>
              match h₂ : r₂.val with
              | .error err =>
                Squash.mk ⟨.error err, by rw [ingressExpr_lam, ← r₁.eq, h₁, ← r₂.eq, h₂]; rfl,
                  r₂.memo⟩
              | .ok y =>
                Squash.mk ⟨.ok (.lam x y { pw := .never }),
                  by rw [ingressExpr_lam, ← r₁.eq, h₁, ← r₂.eq, h₂]; rfl, r₂.memo⟩
        | .forallE n t b bi h =>
          Squash.lift (go memo t) fun r₁ =>
            match h₁ : r₁.val with
            | .error err =>
              Squash.mk ⟨.error err, by rw [ingressExpr_forallE, ← r₁.eq, h₁]; rfl, r₁.memo⟩
            | .ok x => Squash.lift (go r₁.memo b) fun r₂ =>
              match h₂ : r₂.val with
              | .error err =>
                Squash.mk ⟨.error err,
                  by rw [ingressExpr_forallE, ← r₁.eq, h₁, ← r₂.eq, h₂]; rfl, r₂.memo⟩
              | .ok y =>
                Squash.mk ⟨.ok (.forallE x y { pw := .never }),
                  by rw [ingressExpr_forallE, ← r₁.eq, h₁, ← r₂.eq, h₂]; rfl, r₂.memo⟩
        | .letE n t v b nd h =>
          Squash.lift (go memo t) fun r₁ =>
            match h₁ : r₁.val with
            | .error err =>
              Squash.mk ⟨.error err, by rw [ingressExpr_letE, ← r₁.eq, h₁]; rfl, r₁.memo⟩
            | .ok x => Squash.lift (go r₁.memo v) fun r₂ =>
              match h₂ : r₂.val with
              | .error err =>
                Squash.mk ⟨.error err, by rw [ingressExpr_letE, ← r₁.eq, h₁, ← r₂.eq, h₂]; rfl,
                  r₂.memo⟩
              | .ok y => Squash.lift (go r₂.memo b) fun r₃ =>
                match h₃ : r₃.val with
                | .error err =>
                  Squash.mk ⟨.error err,
                    by rw [ingressExpr_letE, ← r₁.eq, h₁, ← r₂.eq, h₂, ← r₃.eq, h₃]; rfl, r₃.memo⟩
                | .ok z =>
                  Squash.mk ⟨.ok (.letE x y z),
                    by rw [ingressExpr_letE, ← r₁.eq, h₁, ← r₂.eq, h₂, ← r₃.eq, h₃]; rfl, r₃.memo⟩
        | .proj n i b h =>
          Squash.lift (go memo b) fun r =>
            match hr : r.val with
            | .error err =>
              Squash.mk ⟨.error err, by rw [ingressExpr_proj, ← r.eq, hr]; rfl, r.memo⟩
            | .ok y =>
              Squash.mk ⟨.ok (.proj (ingressName n) i y), by rw [ingressExpr_proj, ← r.eq, hr]; rfl,
                r.memo⟩
      Squash.lift node fun r =>
        match hv : r.val with
        | .ok v => Squash.mk ⟨r.val, r.eq, r.memo.insert pa.toNat ⟨e, v, r.eq.symm.trans hv⟩⟩
        | .error _ => Squash.mk r)
    (fun _ _ => Subsingleton.elim _ _)

/-- Several terms' results: their conversions, proved to be the tree
conversions, and the memo after them. -/
structure ResList (es : List Ix.Expr) where
  val : Except ExprError (List KExpr)
  eq : val = ingressExprs σ es
  memo : Memo σ

/-- The DAG walk over several terms, with one memo: a subterm shared between
them is converted once. -/
def goList (memo : Memo σ) : (es : List Ix.Expr) → Squash (ResList σ es)
  | [] => Squash.mk ⟨.ok [], rfl, memo⟩
  | e :: es =>
    Squash.lift (go σ memo e) fun r =>
      match h : r.val with
      | .error err =>
        Squash.mk ⟨.error err, by
          rw [ingressExprs, List.mapM_cons, ← r.eq, h]; rfl, r.memo⟩
      | .ok x => Squash.lift (goList r.memo es) fun rs =>
        match hs : rs.val with
        | .error err =>
          Squash.mk ⟨.error err, by
            rw [ingressExprs, List.mapM_cons, ← r.eq, h, ← ingressExprs, ← rs.eq, hs]; rfl,
            rs.memo⟩
        | .ok xs =>
          Squash.mk ⟨.ok (x :: xs), by
            rw [ingressExprs, List.mapM_cons, ← r.eq, h, ← ingressExprs, ← rs.eq, hs]; rfl,
            rs.memo⟩

/-- A conversion with its proof: a subsingleton. -/
structure ListVal (es : List Ix.Expr) where
  val : Except ExprError (List KExpr)
  eq : val = ingressExprs σ es

instance (es : List Ix.Expr) : Subsingleton (ListVal σ es) :=
  ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => by subst ha; subst hb; rfl⟩

/-- The DAG walk from an empty memo, its memo dropped. -/
def ingressExprsVal (es : List Ix.Expr) : ListVal σ es :=
  Squash.lift (goList σ {} es) fun r => ⟨r.val, r.eq⟩

/-- **The conversion on the DAG.** -/
def ingressExprsShared (es : List Ix.Expr) : Except ExprError (List KExpr) :=
  (ingressExprsVal σ es).val

theorem ingressExprsShared_eq (es : List Ix.Expr) :
    ingressExprsShared σ es = ingressExprs σ es :=
  (ingressExprsVal σ es).eq

end Shared

/-- Compiled code runs the DAG walk wherever it calls `ingressExprs`. -/
@[csimp] theorem ingressExprs_eq_shared : @ingressExprs = @ingressExprsShared := by
  funext σ es
  exact (ingressExprsShared_eq σ es).symm

end Ix.LeanIngress
