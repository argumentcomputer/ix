import Ix.Environment
import IxC.Kernel.Expr
import Ix.SemanticContract

/-! # Lean's terms as the checker's terms

The term half of the Source-mode ingress (`Ix.LeanIngress`): an
`Ix.Expr` (Lean's term as `Ix.CanonM` canonicalizes it) becomes an
`Ix.Kernel.Expr` with nothing hashed and nothing rewritten.

* **Keys** are Lean's names: `Ix.Name` ↦ `Ix.Kernel.Name` component by
  component, the hash fields dropped (`ingressName`), and a constant's key is
  the role Source mode's fixed binding gives that name, or else the input
  key of the name (`ingressKey`). So the checker's role constants (`Eq`,
  `Nat`, `Quot`, the literal support, the `Nat` operations, the standard
  axioms) are met at their role keys.
* **Levels** are Lean's levels, constructor by constructor; they are not
  canonicalized. A level parameter becomes its position `σ n` under the
  constant's numbering `σ` of its own level parameters
  (`Ix.LeanIngress.Numbering`). A level metavariable is refused.
* **Terms**: `mdata` is erased (except a contract frame, below), binder names
  and binder infos are dropped, a `letE` carries Lean's let contract
  (`LetContract.lean nonDep`), every binder
  carries `pw := .never` (the checker's annotation pass computes the datum,
  as for the Ixon reader's terms), literals stay literals and a projection
  names its structure. A free variable or a metavariable is refused.
* **Binder contracts.** Lean has none, so a binder carries the Lean
  fragment's (`BinderMeta`'s defaults) unless a contract frame wraps it: an
  `mdata` node with `ix.contract` fields (`Ix.SemanticContract`). Frames are
  how the compiler's input carries resolved source contracts:
  `Ix.Compile.CompileInput.prepare` resolves the source markers
  (`ix.source.binder` metadata) and registrations on the Lean constants and
  puts a frame directly around each annotated binder, `Ix.CanonM` keeps
  the frames, and the compiler lowers each one into the Ixon binder it wraps
  (`Ix.SemanticContract.Contract.lower`). The ingress reads a frame as the
  compiler does, with the compiler's own `hasMetadata` and `read`
  (`ingressMData`): a `lam` frame's contract becomes the binder's
  `contract`; an `all` frame's input and result contracts become `contract`
  and `result`; a `letE` frame's binder contract and kind go on the let's
  contract, over Lean's `nonDep` flag, as the compiler lowers it; and a
  malformed frame, or one that is not directly around a binder of its kind,
  is refused, as the compiler refuses it. So a Source term carries the
  contracts that `Ix.Cert.compile` writes into the Ixon term the reader
  reads back, by construction. Unresolved source markers are plain metadata
  to both the ingress and `Ix.Cert.compile`, which then both give the
  defaults; the IO pipeline refuses them.

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
abbrev KExpr := Ix.Kernel.Expr .source

/-- A term the checker has no syntax for, or a contract frame the compiler
does not lower. -/
inductive ExprError where
  | fvar (name : KName)
  | mvar (name : KName)
  | levelMVar (name : KName)
  | contract (reason : String)
  deriving Repr, Inhabited, BEq

/-- Lean's name as the checker's name, component by component, the hash
fields dropped. -/
def ingressName : Ix.Name → Ix.Kernel.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ingressName p) s
  | .num p n _ => .num (ingressName p) n

/-- **A constant's key**: the role Source mode's fixed binding gives Lean's
name (`Ix.Kernel.Key.ofName`: the role whose Lean name it is), otherwise the
input key, the name itself. -/
def ingressKey (n : Ix.Name) : Ix.Kernel.Key .source := Ix.Kernel.Key.ofName (ingressName n)

instance : ToString ExprError where
  toString
    | .fvar n => s!"free variable {n}"
    | .mvar n => s!"metavariable {n}"
    | .levelMVar n => s!"level metavariable {n}"
    | .contract r => s!"contract frame: {r}"

def ingressLevel (σ : Ix.Name → LevelParam) : Ix.Level → Except ExprError KLevel
  | .zero _ => pure .zero
  | .succ u _ => return .succ (← ingressLevel σ u)
  | .max u v _ => return .max (← ingressLevel σ u) (← ingressLevel σ v)
  | .imax u v _ => return .imax (← ingressLevel σ u) (← ingressLevel σ v)
  | .param n _ => pure (.param (σ n))
  | .mvar n _ => throw (.levelMVar (ingressName n))

/-- The conversion `x` of the term `e` under a contract frame `c`: the
binder `e` with `c` on it, where the compiler's `Contract.lower` puts it
(`Ix.SemanticContract`): a `lam`'s or an `all`'s on its binder, a `letE`'s on
its let contract (its binder contract and kind over the `nonDep` flag). -/
def withContract (c : Ix.SemanticContract.Contract) (e : Ix.Expr) (x : KExpr) :
    Except ExprError KExpr :=
  match c.kind, e, x with
  | .lam, .lam .., .lam t b m => pure (.lam t b { m with contract := c.binder })
  | .all, .forallE .., .forallE t b m =>
    pure (.forallE t b { m with contract := c.binder, result := c.result })
  | .letE, .letE .., .letE t v b l =>
    pure (.letE t v b { contract := { l.contract with binder := c.binder, kind := c.letKind } })
  | _, _, _ => throw (.contract "semantic contract is not attached to its original binder")

/-- An `mdata` node with data `d` over the term `e`, whose conversion is `x`:
a contract frame (`Ix.SemanticContract.hasMetadata`) puts its contract on
`e`'s binder (`withContract`), as the compiler reads it; any other metadata
is erased. -/
def ingressMData (d : Array (Ix.Name × Ix.DataValue)) (e : Ix.Expr)
    (x : Except ExprError KExpr) : Except ExprError KExpr :=
  if Ix.SemanticContract.hasMetadata d then do
    let c ← (Ix.SemanticContract.read d).mapError .contract
    withContract c e (← x)
  else x

/-- **The term conversion** (the specification), under the constant's
numbering `σ` of its level parameters. -/
def ingressExpr (σ : Ix.Name → LevelParam) : Ix.Expr → Except ExprError KExpr
  | .bvar i _ => pure (Ix.Kernel.Expr.mkBvar i)
  | .fvar n _ => throw (.fvar (ingressName n))
  | .mvar n _ => throw (.mvar (ingressName n))
  | .sort u _ => return .sort (← ingressLevel σ u)
  | .const n us _ => return .const (ingressKey n) (← us.toList.mapM (ingressLevel σ))
  | .app f a _ => return .app (← ingressExpr σ f) (← ingressExpr σ a)
  | .lam _ t b _ _ => return .lam (← ingressExpr σ t) (← ingressExpr σ b) { pw := .never }
  | .forallE _ t b _ _ => return .forallE (← ingressExpr σ t) (← ingressExpr σ b) { pw := .never }
  | .letE _ t v b nd _ =>
    return .letE (← ingressExpr σ t) (← ingressExpr σ v) (← ingressExpr σ b)
      { contract := .lean nd }
  | .lit (.natVal n) _ => pure (.lit (.natVal n))
  | .lit (.strVal s) _ => pure (.lit (.strVal s))
  | .mdata d e _ => ingressMData d e (ingressExpr σ e)
  | .proj n i e _ => return .proj (ingressKey n) i (← ingressExpr σ e)

/-- Metadata is read by `ingressMData`. -/
theorem ingressExpr_mdata (σ : Ix.Name → LevelParam) (d : Array (Ix.Name × Ix.DataValue))
    (e : Ix.Expr) (h : Address) :
    ingressExpr σ (.mdata d e h) = ingressMData d e (ingressExpr σ e) := rfl

/-- Metadata that is not a contract frame is erased. -/
theorem ingressExpr_mdata_plain (σ : Ix.Name → LevelParam) {d : Array (Ix.Name × Ix.DataValue)}
    (e : Ix.Expr) (h : Address) (hd : Ix.SemanticContract.hasMetadata d = false) :
    ingressExpr σ (.mdata d e h) = ingressExpr σ e := by
  simp [ingressExpr_mdata, ingressMData, hd]

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
      ingressExpr σ b >>= fun z => pure (.letE x y z { contract := .lean nd })) := rfl

theorem ingressExpr_proj (n : Ix.Name) (i : Nat) (b : Ix.Expr) (h : Address) :
    ingressExpr σ (.proj n i b h) =
    (ingressExpr σ b >>= fun y => pure (.proj (ingressKey n) i y)) := rfl

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
          Squash.mk ⟨(do return .const (ingressKey n) (← us.toList.mapM (ingressLevel σ))), rfl,
            memo⟩
        | .lit (.natVal n) _ => Squash.mk ⟨.ok (.lit (.natVal n)), rfl, memo⟩
        | .lit (.strVal s) _ => Squash.mk ⟨.ok (.lit (.strVal s)), rfl, memo⟩
        | .mdata d b h =>
          Squash.lift (go memo b) fun r =>
            Squash.mk ⟨ingressMData d b r.val, by rw [ingressExpr_mdata, r.eq], r.memo⟩
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
                  Squash.mk ⟨.ok (.letE x y z { contract := .lean nd }),
                    by rw [ingressExpr_letE, ← r₁.eq, h₁, ← r₂.eq, h₂, ← r₃.eq, h₃]; rfl, r₃.memo⟩
        | .proj n i b h =>
          Squash.lift (go memo b) fun r =>
            match hr : r.val with
            | .error err =>
              Squash.mk ⟨.error err, by rw [ingressExpr_proj, ← r.eq, hr]; rfl, r.memo⟩
            | .ok y =>
              Squash.mk ⟨.ok (.proj (ingressKey n) i y), by rw [ingressExpr_proj, ← r.eq, hr]; rfl,
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

/-! Source mode's binding, checked: every role's Lean name keys that role, and
the name map holds the roles' names and nothing else. -/

#guard Ix.Kernel.Role.all.all fun r => (Ix.Kernel.Key.ofName r.leanName == .role r : Bool)
#guard Ix.Kernel.Role.byLeanName.size == Ix.Kernel.Role.all.length
