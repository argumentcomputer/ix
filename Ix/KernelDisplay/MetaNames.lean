module

public import Ix.Ixon
public import Ix.LeanIngress.Names
public import IxC.Kernel.Ixon.Reader
public import Ix.KernelDisplay.Render
public import IxC.Kernel.FEnv

@[expose] public section

/-! # `.meta`'s binder names, from the `.ixe`'s metadata (IxC step 6b, display only)

The meta reader is the Ixon reader at `.meta` (`Ix.Kernel.Reader.readRecord`,
the same code as `.anon`'s), followed by two display steps outside the kernel:
the display table's key names (`Benchmarks.Kernel.CheckIxeMeta.withDisplay`,
step 6) and this module's binder names. `nameRead` annotates every binder and
`let` of a reading's declarations with the name (and binder info) the `.ixe`'s
metadata arena gives it, so that names travel inside the terms through δ, β and
instantiation, as in Lean, and a failure can print a reduced term with them.

* **Which arena.** A declared constant's key names it in the metadata table
  (`metaTable`): the first of its Lean names (an alias fiber's in sorted order,
  as `displayTable` orders them), whose `Named.constMeta` holds the arena and
  the roots: a definition's type and value, an inductive's, a constructor's, an
  axiom's or a quotient's type, a recursor's type and rules (`ruleRoots`, in
  rule order).
* **The walk** (`nameGo`) follows a term and its arena node together, after
  the node's `mdata` chain: a `binder` node names a `lam`/`forallE`, a
  `letBinder` node a `letE`; `app` and `prj` nodes are followed, as
  `Ix.Tc.ingressExprMeta` reads them.
* **Missing or inconsistent metadata adds nothing and is never an error.** A
  key without metadata (the modeller's generated records, the prelude's) is
  left as it is; a node of the wrong kind or an index out of range leaves its
  subterm anonymous (the walk goes on below it without metadata, to count
  the binders for the coverage figure).
* **The result is the reading**: every step returns its term with the proof
  that it is the same term (the annotations are subsingletons,
  `Ix.Kernel.BinderMeta.display`), so `.meta` checks exactly the terms
  `.anon` checks. The reader rewrites a projection function's value
  (`projRewrite`), so that value's arena fits only down to the rewrite.
* **Sharing.** A term is a DAG (the record's sharing table); the walk is
  memoized by (arena position, term), a hit confirmed by `==` (a pointer test
  at run time), so a shared subterm at the same arena position is annotated
  once. -/

namespace Ix.KernelDisplay

open Ix.Kernel (Key BinderMeta LetMeta)
open Ix.Kernel.Reader

/-- A declared key's metadata: that of the first (in sorted order) of the Lean
names the environment maps to the key's record address. -/
abbrev MetaTable := Std.HashMap (Key .meta) Ixon.ConstantMeta

/-- **The metadata table** of an environment, keyed as `displayTable` keys
its display (the keys a reading with `cx` gives the names' addresses). -/
def metaTable (env : Ixon.Env) (cx : Ctx .meta) : MetaTable := Id.run do
  let mut best : Std.HashMap (Key .meta) (String × Ixon.ConstantMeta) := {}
  for (name, named) in env.named.toList do
    let some k := cx.keys.byAddress[named.addr]? <|> keyOfAddress cx.store cx.roles named.addr
      | continue
    let s := toString name
    match best[k]? with
    | some (s', _) => if s < s' then best := best.insert k (s, named.constMeta)
    | none => best := best.insert k (s, named.constMeta)
  return best.map fun _ (_, m) => m

/-- Binder and let counts: visited, and named from the metadata. -/
structure Coverage where
  binders : Nat := 0
  named : Nat := 0
  deriving Inhabited

instance : Add Coverage := ⟨fun a b => ⟨a.binders + b.binders, a.named + b.named⟩⟩

/-- The walk's state: the memo, keyed by (arena position, term hash), the
names resolved so far, and the coverage counts. -/
structure NameState where
  memo : Std.HashMap (UInt64 × UInt64) (Σ' (k v : Ix.Kernel.Expr .meta), v = k) := {}
  names : Std.HashMap Address Ix.Kernel.Name := {}
  coverage : Coverage := {}

abbrev NameM := StateM NameState

/-- What the walk reads: the environment's names and the constant's arena. -/
structure ArenaCx where
  names : Std.HashMap Address Ix.Name
  arena : Ixon.ExprMetaArena

/-- A name-hash address as the checker's name (anonymous if unknown). -/
def resolveName (cx : ArenaCx) (a : Address) : NameM Ix.Kernel.Name := do
  if let some n := (← get).names[a]? then return n
  let n := match cx.names[a]? with
    | some n => Ix.LeanIngress.ingressName n
    | none => .anonymous
  modify fun s => { s with names := s.names.insert a n }
  return n

/-- The node at `i` after its `mdata` chain; `none` outside the arena or after
as many steps as it has nodes. -/
def nodeAt (cx : ArenaCx) (i : UInt64) : Option Ixon.ExprMetaData := Id.run do
  let mut i := i
  for _ in [0:cx.arena.nodes.size] do
    match cx.arena.nodes[i.toNat]? with
    | some (.mdata _ child) => i := child
    | some n => return some n
    | none => return none
  return none

/-- Where the walk is: at an arena node, or where the metadata does not fit
(`none`: binders are counted, nothing is named). -/
inductive Pos where
  | node (i : UInt64)
  | none

/-- Count one binder or let; `named` if the metadata names it. -/
def count (named : Bool) : NameM Unit :=
  modify fun s => { s with coverage := s.coverage + ⟨1, if named then 1 else 0⟩ }

/-- A binder annotation from the arena. -/
def binderDisplay (cx : ArenaCx) (n : Address) (bi : Lean.BinderInfo) :
    NameM Ix.Kernel.BinderDisplay := do
  let name ← resolveName cx n
  count (name != .anonymous)
  return ⟨name, Ix.LeanIngress.ingressBinderInfo bi⟩

/-- The memo's key of a position and a term. -/
def memoKey (p : Pos) (k : Ix.Kernel.Expr .meta) : Option (UInt64 × UInt64) :=
  match p, k with
  | _, .bvar _ | _, .sort _ | _, .const .. | _, .lit _ => .none
  | .node i, _ => some (i, hash k)
  | .none, _ => some (UInt64.ofNat (2 ^ 64 - 1), hash k)

/-- **The names the arena gives the term `k` at the position `p`** (module
docstring), with the proof that the result is `k`. -/
def nameGo (cx : ArenaCx) (p : Pos) (k : Ix.Kernel.Expr .meta) : NameM { v : Ix.Kernel.Expr .meta // v = k } := do
  let key := memoKey p k
  if let some key := key then
    if let some ⟨k', v, h⟩ := (← get).memo[key]? then
      if hk : k' == k then return ⟨v, h.trans (eq_of_beq hk)⟩
  let node : Option Ixon.ExprMetaData := match p with
    | .node i => nodeAt cx i
    | _ => .none
  let r : { v : Ix.Kernel.Expr .meta // v = k } ← match hk : k, p, node with
    | .lam t b m, _, some (.binder n bi ti bj) => do
      let d ← binderDisplay cx n bi
      let t' ← nameGo cx (.node ti) t
      let b' ← nameGo cx (.node bj) b
      pure ⟨.lam t'.1 b'.1 { m with display := Squash.mk d },
        by rw [hk, t'.2, b'.2, Ix.LeanIngress.binderMeta_named]⟩
    | .forallE t b m, _, some (.binder n bi ti bj) => do
      let d ← binderDisplay cx n bi
      let t' ← nameGo cx (.node ti) t
      let b' ← nameGo cx (.node bj) b
      pure ⟨.forallE t'.1 b'.1 { m with display := Squash.mk d },
        by rw [hk, t'.2, b'.2, Ix.LeanIngress.binderMeta_named]⟩
    | .letE t v b l, _, some (.letBinder n ti vi bj) => do
      let name ← resolveName cx n
      count (name != .anonymous)
      let t' ← nameGo cx (.node ti) t
      let v' ← nameGo cx (.node vi) v
      let b' ← nameGo cx (.node bj) b
      pure ⟨.letE t'.1 v'.1 b'.1 { l with display := Squash.mk name },
        by rw [hk, t'.2, v'.2, b'.2, Ix.LeanIngress.letMeta_named]⟩
    | .app f a, _, some (.app fi ai) => do
      let f' ← nameGo cx (.node fi) f
      let a' ← nameGo cx (.node ai) a
      pure ⟨.app f'.1 a'.1, by rw [hk, f'.2, a'.2]⟩
    | .proj s j e, _, some (.prj _ c) => do
      let e' ← nameGo cx (.node c) e
      pure ⟨.proj s j e'.1, by rw [hk, e'.2]⟩
    -- no metadata here: count the binders below, name nothing, keep the term
    | .lam t b _, _, _ | .forallE t b _, _, _ => do
      count false
      let _ ← nameGo cx .none t
      let _ ← nameGo cx .none b
      pure ⟨_, rfl⟩
    | .letE t v b _, _, _ => do
      count false
      let _ ← nameGo cx .none t
      let _ ← nameGo cx .none v
      let _ ← nameGo cx .none b
      pure ⟨_, rfl⟩
    | .app f a, _, _ => do
      let _ ← nameGo cx .none f
      let _ ← nameGo cx .none a
      pure ⟨_, rfl⟩
    | .proj _ _ e, _, _ | .fvar _ e, _, _ => do
      let _ ← nameGo cx .none e
      pure ⟨_, rfl⟩
    | _, _, _ => pure ⟨_, rfl⟩
  if let some key := key then
    modify fun s => { s with memo := s.memo.insert key ⟨k, r.1, r.2⟩ }
  return r

/-- A term under the root `root` of a constant's arena, with a fresh memo
(the memo's positions are this arena's). -/
def nameTerm (cx : ArenaCx) (root : UInt64) (k : Ix.Kernel.Expr .meta) : NameM (Ix.Kernel.Expr .meta) := do
  modify fun s => { s with memo := {} }
  return (← nameGo cx (.node root) k).1

/-- A constant's arena and roots: its type's, its value's (a definition's),
its rules' (a recursor's). -/
def roots : Ixon.ConstantMetaInfo →
    Option (Ixon.ExprMetaArena × UInt64 × Option UInt64 × Array UInt64)
  | .defn _ _ _ _ a t v => some (a, t, some v, #[])
  | .axio _ _ a t | .quot _ _ a t | .indc _ _ _ _ _ a t | .ctor _ _ _ a t => some (a, t, none, #[])
  | .recr _ _ _ _ _ a t rs => some (a, t, none, rs)
  | _ => none

/-- What naming one record reads: the environment's names and the metadata
table. -/
structure NameCx where
  names : Std.HashMap Address Ix.Name
  table : MetaTable

/-- A constant's arena and roots, by its key. -/
def NameCx.rootsOf (c : NameCx) (k : Key .meta) :
    Option (ArenaCx × UInt64 × Option UInt64 × Array UInt64) := do
  let m ← c.table[k]?
  let (a, t, v, rs) ← roots m.info
  if a.nodes.isEmpty then none
  else some (⟨c.names, a⟩, t, v, rs)

/-- A constant's type, named. -/
def nameVal (c : NameCx) (cv : Ix.Kernel.ConstantVal .meta) :
    NameM (Ix.Kernel.ConstantVal .meta) := do
  let some (cx, t, _, _) := c.rootsOf cv.name | return cv
  return { cv with type := ← nameTerm cx t cv.type }

/-- A definition's type and value, named. -/
def nameValue (c : NameCx) (cv : Ix.Kernel.ConstantVal .meta) (v : Ix.Kernel.Expr .meta) :
    NameM (Ix.Kernel.ConstantVal .meta × Ix.Kernel.Expr .meta) := do
  let some (cx, t, some vr, _) := c.rootsOf cv.name | return (← nameVal c cv, v)
  let ty ← nameTerm cx t cv.type
  return ({ cv with type := ty }, ← nameTerm cx vr v)

/-- A block member, named: its type, and a recursor's rules. -/
def nameInfo (c : NameCx) : Ix.Kernel.ConstantInfo .meta → NameM (Ix.Kernel.ConstantInfo .meta)
  | .axiomInfo cv => .axiomInfo <$> nameVal c cv
  | .defnInfo cv v h => do let (cv, v) ← nameValue c cv v; pure (.defnInfo cv v h)
  | .thmInfo cv v => do let (cv, v) ← nameValue c cv v; pure (.thmInfo cv v)
  | .indInfo cv caps => (.indInfo · caps) <$> nameVal c cv
  | .ctorInfo cv nP nF => (.ctorInfo · nP nF) <$> nameVal c cv
  | .recInfo cv major pre rules => do
    let some (cx, t, _, rs) := c.rootsOf cv.name | return .recInfo cv major pre rules
    let ty ← nameTerm cx t cv.type
    let mut out := #[]
    for (r, i) in rules.zipIdx do
      out := out.push <| ← match rs[i]? with
        | some root => do pure { r with rhs := ← nameTerm cx root r.rhs }
        | none => pure r
    pure (.recInfo { cv with type := ty } major pre out.toList)
  | ci => pure ci

/-- A declaration, named. -/
def nameDecl (c : NameCx) : Ix.Kernel.Declaration .meta → NameM (Ix.Kernel.Declaration .meta)
  | .axiomDecl cv => .axiomDecl <$> nameVal c cv
  | .defnDecl cv v h => do let (cv, v) ← nameValue c cv v; pure (.defnDecl cv v h)
  | .thmDecl cv v => do let (cv, v) ← nameValue c cv v; pure (.thmDecl cv v)
  | .opaqueDecl cv v => do let (cv, v) ← nameValue c cv v; pure (.opaqueDecl cv v)
  | .quotDecl k cv => .quotDecl k <$> nameVal c cv
  | .indDecl block nP => do pure (.indDecl (← block.mapM (nameInfo c)) nP)
  | d => pure d

/-- **The meta reader's binder names**: a `.meta` reading with every binder and
`let` its constants' metadata names, and the coverage counts. -/
def nameRead (c : NameCx) (rd : Read .meta) (names : Std.HashMap Address Ix.Kernel.Name := {}) :
    Read .meta × Coverage × Std.HashMap Address Ix.Kernel.Name :=
  let (decls, s) := (rd.decls.mapM (nameDecl c)).run { names }
  ({ rd with decls }, s.coverage, s.names)


/-! ## Printing `.meta` terms -/

/-- A key's name in a term: its first Lean name (no address, unlike a
message's `name@hex8`), a derived key's base and its shape's suffix, a role's
or any other key as `Key.toName` spells it. -/
def termSpell (t : DisplayTable .meta) (k : Key .meta) : String :=
  match t[k]? with
  | some (d, _) => (d.names.head?.map (nameStr ∘ leanName)).getD (toString k)
  | none =>
    match k with
    | .aux b d => termSpell t b ++ "." ++ toString (d.spell .anonymous)
    | _ => toString k

/-- The types a reading's declarations give their keys: what the printer reads
binder infos and proposition tests from (a role's pinned declaration in the
environment carries no names; the record read with its metadata does). -/
def declTypes (ds : Array (Ix.Kernel.Declaration md)) : List (Key md × Ix.Kernel.Expr md) :=
  ds.toList.flatMap fun
    | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv =>
      [(cv.name, cv.type)]
    | .indDecl block _ => block.map fun ci => (ci.toConstantVal.name, ci.toConstantVal.type)
    | .basisDecl _ => []

/-- **The `.meta` printer's context**: constants named by the display table,
level parameters by the subject's names, binder infos and proposition tests
read from the types the named readings gave (`types`), else from the
environment `fe` the failure was found in. -/
def metaCx (t : DisplayTable .meta) (fe : Ix.Kernel.FEnv .meta)
    (levelNames : List Ix.Kernel.Name)
    (types : Std.HashMap (Key .meta) (Ix.Kernel.Expr .meta) := {}) : Cx .meta where
  spell := termSpell t
  levelName := fun i => match levelNames[i]? with
    | some n => nameStr (leanName n)
    | none => s!"u_{i + 1}"
  constType := fun k => types[k]? <|> (fe.find? k).map (·.toConstantVal.type)

end Ix.KernelDisplay
