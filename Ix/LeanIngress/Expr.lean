module

public import Ix.Environment
public import IxC.Kernel.Expr
public import Ix.SemanticContract
public import Ix.IxonUniv
/- `withPtrEq` is `public` but not `@[expose]`; the memo probe (`probe`) reads
that `withPtrEq a b k h` is definitionally `k ()`, as `IxC.Kernel.Expr` does.
`import all` makes that body visible in this module only. -/
import all Init.Util

/-! # Lean's terms as the checker's terms

The term half of the Source-mode ingress (`Ix.LeanIngress`): an
`Ix.Expr` (Lean's term as `Ix.CanonM` canonicalizes it) becomes an
`Ix.Kernel.Expr` with nothing hashed and nothing rewritten.

It is a `module`, its API public and the specification's bodies exposed,
so that other modules share the conversion
instead of repeating it; the rest of the Source-mode ingress
(`Ix.LeanIngress`: grouping, order, lowering) imports it.

* **Keys** are Lean's names: `Ix.Name` ↦ `Ix.Kernel.Name` component by
  component, the hash fields dropped (`ingressName`), and a constant's key is
  the role Source mode's fixed binding gives that name, or else the input
  key of the name (`ingressKey`). So the checker's role constants (`Eq`,
  `Nat`, `Quot`, the literal support, the `Nat` operations, the standard
  axioms) are met at their role keys.
* **Levels** are Lean's levels, constructor by constructor; the term
  conversion does not canonicalize them. A level parameter becomes its
  position `σ n` under the constant's numbering `σ` of its own level
  parameters (`Ix.LeanIngress.Numbering`). A level metavariable is refused.
  The ingress then puts every level of a converted term in the compiler's
  canonical form (`canonLevel`, `mapLevels`, below; `Ix.LeanIngress.exprsOf`).
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

public section

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
@[expose] def ingressName : Ix.Name → Ix.Kernel.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ingressName p) s
  | .num p n _ => .num (ingressName p) n

/-- **A constant's key**: the role Source mode's fixed binding gives Lean's
name (`Ix.Kernel.Key.ofName`: the role whose Lean name it is), otherwise the
input key, the name itself. -/
@[expose] def ingressKey (n : Ix.Name) : Ix.Kernel.Key .source := Ix.Kernel.Key.ofName (ingressName n)

instance : ToString ExprError where
  toString
    | .fvar n => s!"free variable {n}"
    | .mvar n => s!"metavariable {n}"
    | .levelMVar n => s!"level metavariable {n}"
    | .contract r => s!"contract frame: {r}"

/-- How a constant's Lean level parameters `names` become the checker's
positions: name `i` is position `i`, except at a large eliminator (`large`:
a recursor with one level parameter more than its block's `n`), whose first
name, the elimination level, is the fresh position `n` and whose name
`i + 1` is the block's position `i`, as the Ixon reader numbers a recursor
(`Reader.recLps`). A name that is not among `names` is the position
`names.size`, which no parameter of the constant has. -/
structure Numbering where
  names : Array Ix.Name
  large : Bool := false

/-- Numberings compare their names structurally (`Ix.Name.beqRaw`):
`Ix.LeanIngress.exprsOf` converts a run of terms under one numbering with one
memo, so two numberings whose names only share stored hashes must not be one. -/
instance : BEq Numbering where
  beq σ τ := σ.large == τ.large && σ.names.isEqv τ.names Ix.Name.beqRaw

/-- The position of a level-parameter name, found by structural name equality
(`Ix.Name.beqRaw`; `Ix.Name`'s `==` compares stored hashes only). -/
@[expose] def Numbering.pos (σ : Numbering) (n : Ix.Name) : Ix.Kernel.LevelParam :=
  match σ.names.findIdx? (Ix.Name.beqRaw · n) with
  | none => σ.names.size
  | some 0 => if σ.large then σ.names.size - 1 else 0
  | some (i + 1) => if σ.large then i else i + 1

/-- The constant's own level parameters, numbered. -/
@[expose] def Numbering.params (σ : Numbering) : List Ix.Kernel.LevelParam :=
  σ.names.toList.map σ.pos

@[expose] def ingressLevel (σ : Ix.Name → LevelParam) : Ix.Level → Except ExprError KLevel
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
@[expose] def withContract (c : Ix.SemanticContract.Contract) (e : Ix.Expr) (x : KExpr) :
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
@[expose] def ingressMData (d : Array (Ix.Name × Ix.DataValue)) (e : Ix.Expr)
    (x : Except ExprError KExpr) : Except ExprError KExpr :=
  if Ix.SemanticContract.hasMetadata d then do
    let c ← (Ix.SemanticContract.read d).mapError .contract
    withContract c e (← x)
  else x

/-- **The term conversion** (the specification), under the constant's
numbering `σ` of its level parameters. -/
@[expose] def ingressExpr (σ : Ix.Name → LevelParam) : Ix.Expr → Except ExprError KExpr
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
@[expose] def ingressExprs (σ : Ix.Name → LevelParam) (es : List Ix.Expr) : Except ExprError (List KExpr) :=
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

/-! ## Canonical universes

The compiler stores every universe in canonical form: `Ixon.canonUniv` over
the constant's level parameters numbered by their index in its list
(`compileAndInternUnivCanon`), and the Ixon reader reads variable `i` back
as the constant's `i`-th parameter (`Reader.convUniv`; at a large eliminator
`Reader.recParam`, the elimination level first). `canonLevelIn lps` gives a
level that form for a constant whose level parameters, in its own order, are
`lps`: it numbers the positions by their index in `lps` (`idxIn`),
canonicalizes, and reads the variables back (`ofIdxIn`). The order matters:
`canonUniv` sorts by variable, and at a large eliminator the list's order
(the elimination level first) is not the positions' order (it last).

The ingress applies it to every lowered declaration, each constant over its
own list (`Ix.LeanIngress.canonDecl`), after the lowering: the in-process
modeller sees Lean's levels as Lean's kernel does, so its auxiliaries follow
Lean's. Quotient Source applies it to every group before the lowering instead
(`Ix.LeanIngress.Converted.quotient`), as the Ixon reader reads canonical
levels. The value of every level is unchanged (`canonLevelIn_eval`,
`Ix/LeanIngress/CanonLevel.lean`). -/

/-- The index of position `p` in the level-parameter list `lps`; a position
not in `lps` goes past it, so that `ofIdxIn` inverts it (`ofIdxIn_idxIn`). -/
@[expose] def idxIn (lps : List LevelParam) (p : LevelParam) : Nat :=
  match lps.idxOf? p with
  | some i => i
  | none => lps.length + p

/-- The position at index `i` of `lps` (past it, `idxIn`'s inverse). -/
@[expose] def ofIdxIn (lps : List LevelParam) (i : Nat) : LevelParam :=
  if h : i < lps.length then lps[i] else i - lps.length

theorem ofIdxIn_idxIn (lps : List LevelParam) (p : LevelParam) : ofIdxIn lps (idxIn lps p) = p := by
  unfold idxIn ofIdxIn
  cases hi : lps.idxOf? p with
  | some i =>
    dsimp only
    obtain ⟨hlt, hget, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [hlt, ↓reduceDIte, hget]
  | none =>
    dsimp only
    have hn : ¬ (lps.length + p < lps.length) := by omega
    simp only [hn, ↓reduceDIte]
    exact Nat.add_sub_cancel_left _ _

/-- A level as an Ixon universe, its positions numbered by `ι`. -/
@[expose] def univOfLevel (ι : LevelParam → Nat) : KLevel → Ixon.Univ
  | .zero => .zero
  | .succ u => .succ (univOfLevel ι u)
  | .max u v => .max (univOfLevel ι u) (univOfLevel ι v)
  | .imax u v => .imax (univOfLevel ι u) (univOfLevel ι v)
  | .param p => .var (ι p).toUInt64

/-- An Ixon universe as a level, variable `i` read as the position `π i`
(the reader's `convUniv`). -/
@[expose] def levelOfUniv (π : Nat → LevelParam) : Ixon.Univ → KLevel
  | .zero => .zero
  | .succ u => .succ (levelOfUniv π u)
  | .max u v => .max (levelOfUniv π u) (levelOfUniv π v)
  | .imax u v => .imax (levelOfUniv π u) (levelOfUniv π v)
  | .var i => .param (π i.toNat)

/-- **A level in the compiler's canonical form**, for a constant whose level
parameters, in its own order, are `lps`. -/
@[expose] def canonLevelIn (lps : List LevelParam) (l : KLevel) : KLevel :=
  levelOfUniv (ofIdxIn lps) (Ixon.canonUniv (univOfLevel (idxIn lps) l))

/-- `canonLevelIn` under a numbering: over its parameters' positions in the
constant's order (`Numbering.params`). -/
@[expose] def canonLevel (σ : Numbering) (l : KLevel) : KLevel :=
  canonLevelIn σ.params l

/-- Every level of a term mapped by `f` (a free variable's type included);
binders, keys and literals unchanged. -/
@[expose] def mapLevels (f : KLevel → KLevel) : KExpr → KExpr
  | .bvar i => .bvar i
  | .fvar i t => .fvar i (mapLevels f t)
  | .sort u => .sort (f u)
  | .const n us => .const n (us.map f)
  | .app a b => .app (mapLevels f a) (mapLevels f b)
  | .lam t b m => .lam (mapLevels f t) (mapLevels f b) m
  | .forallE t b m => .forallE (mapLevels f t) (mapLevels f b) m
  | .letE t v b l => .letE (mapLevels f t) (mapLevels f v) (mapLevels f b) l
  | .lit l => .lit l
  | .proj n i e => .proj n i (mapLevels f e)

/-! The executed `mapLevels` over several terms: one walk memoized by term
(a converted term is a DAG), proved to be the structural map. -/

section MapLevels

variable (f : KLevel → KLevel)

/-- The memo holds structural results only. -/
def LevelMemoInv (memo : Std.HashMap KExpr KExpr) : Prop :=
  ∀ k v, memo[k]? = some v → v = mapLevels f k

variable {f} in
theorem LevelMemoInv.insert {memo : Std.HashMap KExpr KExpr} (hm : LevelMemoInv f memo)
    {e r : KExpr} (heq : r = mapLevels f e) : LevelMemoInv f (memo.insert e r) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k v hk

/-- The memoized walk. -/
def mapLevelsGo (memo : Std.HashMap KExpr KExpr) : KExpr → KExpr × Std.HashMap KExpr KExpr
  | e@(.bvar _) => (e, memo)
  | e@(.lit _) => (e, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : KExpr × Std.HashMap KExpr KExpr :=
        match e with
        | .fvar i t =>
          let (t', memo) := mapLevelsGo memo t
          (.fvar i t', memo)
        | .sort u => (.sort (f u), memo)
        | .const n us => (.const n (us.map f), memo)
        | .app a b =>
          let (a', memo) := mapLevelsGo memo a
          let (b', memo) := mapLevelsGo memo b
          (.app a' b', memo)
        | .lam t b m =>
          let (t', memo) := mapLevelsGo memo t
          let (b', memo) := mapLevelsGo memo b
          (.lam t' b' m, memo)
        | .forallE t b m =>
          let (t', memo) := mapLevelsGo memo t
          let (b', memo) := mapLevelsGo memo b
          (.forallE t' b' m, memo)
        | .letE t v b l =>
          let (t', memo) := mapLevelsGo memo t
          let (v', memo) := mapLevelsGo memo v
          let (b', memo) := mapLevelsGo memo b
          (.letE t' v' b' l, memo)
        | .proj n i s =>
          let (s', memo) := mapLevelsGo memo s
          (.proj n i s', memo)
        | e => (e, memo)
      (r, memo.insert e r)

variable {f} in
/-- **The memoized walk is `mapLevels`.** -/
theorem mapLevelsGo_spec :
    ∀ (e : KExpr) {memo : Std.HashMap KExpr KExpr}, LevelMemoInv f memo →
      (mapLevelsGo f memo e).1 = mapLevels f e ∧ LevelMemoInv f (mapLevelsGo f memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | sort u =>
    intro memo hm
    rw [mapLevelsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | const n us =>
    intro memo hm
    rw [mapLevelsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | fvar i t ih =>
    intro memo hm
    rw [mapLevelsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      refine ⟨by simp [mapLevels, h1], ?_⟩
      exact h2.insert (by simp [mapLevels, h1])
  | app a b iha ihb =>
    intro memo hm
    rw [mapLevelsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [mapLevels, h1, h3], ?_⟩
      exact h4.insert (by simp [mapLevels, h1, h3])
  | lam t b m iht ihb =>
    intro memo hm
    rw [mapLevelsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [mapLevels, h1, h3], ?_⟩
      exact h4.insert (by simp [mapLevels, h1, h3])
  | forallE t b m iht ihb =>
    intro memo hm
    rw [mapLevelsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [mapLevels, h1, h3], ?_⟩
      exact h4.insert (by simp [mapLevels, h1, h3])
  | letE t v b l iht ihv ihb =>
    intro memo hm
    rw [mapLevelsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihv h2
      obtain ⟨h5, h6⟩ := ihb h4
      refine ⟨by simp [mapLevels, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [mapLevels, h1, h3, h5])
  | proj n i s ih =>
    intro memo hm
    rw [mapLevelsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      refine ⟨by simp [mapLevels, h1], ?_⟩
      exact h2.insert (by simp [mapLevels, h1])

/-- The walk over several terms, one memo throughout. -/
def mapLevelsGoList (memo : Std.HashMap KExpr KExpr) : List KExpr → List KExpr
  | [] => []
  | e :: es =>
    let (r, memo) := mapLevelsGo f memo e
    r :: mapLevelsGoList memo es

variable {f} in
theorem mapLevelsGoList_spec :
    ∀ (es : List KExpr) {memo : Std.HashMap KExpr KExpr}, LevelMemoInv f memo →
      mapLevelsGoList f memo es = es.map (mapLevels f)
  | [], _, _ => rfl
  | e :: es, memo, hm => by
    obtain ⟨h1, h2⟩ := mapLevelsGo_spec e hm
    simp only [mapLevelsGoList, List.map_cons, ← h1, mapLevelsGoList_spec es h2]

end MapLevels

/-- Every level of several terms mapped by `f` (the specification). -/
@[expose] def mapLevelsList (f : KLevel → KLevel) (es : List KExpr) : List KExpr :=
  es.map (mapLevels f)

/-- The executed `mapLevelsList`: one memoized walk. -/
def mapLevelsListFast (f : KLevel → KLevel) (es : List KExpr) : List KExpr :=
  mapLevelsGoList f {} es

/-- Compiled code runs the memoized walk wherever it calls `mapLevelsList`. -/
@[csimp] theorem mapLevelsList_eq_fast : @mapLevelsList = @mapLevelsListFast := by
  funext f es
  exact (mapLevelsGoList_spec es (fun k v h => by simp at h)).symm

end Ix.LeanIngress
