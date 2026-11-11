import IxCCTests.IxonV3.Builder
import IxCCTests.Support.Envelope

/-! # Role-bound test environments

The certified kernel admits only role-bound environments, its reader declines
an inductive block stored without its recursor, and it declines every axiom
but the standard ones. The test environments the in-memory builder
(`IxCCTests.IxonV3.Builder`: `store`, `block`, `bytes`) makes are none of
these: unbound, their inductives without recursors, some built on an axiom.
This module makes role-bound ones the kernel front end accepts:

* a **base**: a committed role-bound closure (`fixtures/corpus/phase1-scalar/tuple`,
  the corpus's tuple program), decoded with its role binding, its prelude records and the rest
  of `ix compile`'s output; synthetic records are added to it with `store` and
  `block`, and the base's own constants (`Nat`, `Bool`, `Eq`, …) are there to
  be used or ignored;
* **recursors** for the inductive blocks a test adds (`simpleRecursor`): one
  inductive, no parameters or indices, in `Type`, whose constructor fields are
  either the inductive itself or a closed type stored at an address. The
  recursor is Lean's (a large eliminator `T.rec.{u}`: the motive, one minor
  premise per constructor taking the fields and then one induction hypothesis
  per recursive field, the major premise), written as `ix compile` writes it:
  a `recr` singleton whose rules call the recursor through `recur 0`;
* the **role-bound envelope** (`bytes`, `0xE5`, by the suites' one writer, `Support.Envelope`): the base's role binding after
  the assumptions, the constant root recomputed, and the base's reducibility
  hints kept.

A record that is already in the base (an enumeration of two constructors has
`Bool`'s content address) is not stored twice, and its block gets no second
recursor (the reader keeps one recursor per motive). -/

namespace IxCCTests.Support.Bound

open IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.IxonV3.Builder (record store block arrow lambda)

abbrev E := IxCC.Ixon.V3.Expr
abbrev Addr := IxCC.Ixon.Address

/-- The committed role-bound closure every test environment extends. -/
def baseStem : System.FilePath := "fixtures/corpus/phase1-scalar/tuple"

/-- The base, decoded; refused unless it is role-bound. -/
def loadBase : IO Env := do
  let raw ← IO.FS.readBinFile (baseStem.toString ++ ".ixe")
  let env ← IO.ofExcept (decodeAnonymousEnv raw)
  unless env.isBound do throw (IO.userError s!"{baseStem}: the base is not role-bound")
  return env

/-- The role-bound envelope (`0xE5`) of `env`, written by the suites' one
envelope writer (`Support.Envelope.envelope`) with the base's role binding:
the constant root recomputed, the reducibility hints and metadata kept.
Refused (`none`) for an environment without a binding. -/
def bytes (env : Env) : Option ByteArray :=
  env.binding.map fun b => IxCCTests.Support.Envelope.envelope env (some (b.address, b.bytes))

/-- `bytes` for an environment built on the base, which is role-bound (an
environment without a binding gives no bytes, which ingress refuses as
undecodable). -/
def write (env : Env) : ByteArray := (bytes env).getD .empty

/-- A constructor field: the inductive itself, or a closed type stored at an
address. -/
inductive Field where
  | self
  | ext (type : Addr)
  deriving BEq, Inhabited

/-- `inductive T | c₀ (fields₀) | … : Type`: one inductive, no parameters or
indices, its constructors' fields as given (`recur 0` for `self`, a reference
for a closed type). -/
def simpleBlock (ctors : Array (Array Field)) : Constant := Id.run do
  let exts := ctors.foldl (fun acc fs => fs.foldl (fun acc f => match f with
    | .ext t => if acc.contains t then acc else acc.push t
    | .self => acc) acc) (#[] : Array Addr)
  let fieldType := fun (f : Field) => match f with
    | .self => (.recur 0 #[] : E)
    | .ext t => .ref (exts.findIdx? (· == t) |>.getD 0).toUInt64 #[]
  let ctorInfo := ctors.zipIdx.map fun (fs, j) =>
    (⟨false, 0, j.toUInt64, 0, fs.size.toUInt64,
      fs.foldr (fun f acc => arrow (fieldType f) acc) (.recur 0 #[])⟩ : Constructor)
  return ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0, ctorInfo⟩], #[], exts, #[.succ .zero]⟩

/-- The recursor of `simpleBlock ctors` stored at `blk` (refs: `0` the
inductive, `1 + j` constructor `j`, then the closed field types; universes:
`0` the motive's level `u`):

`T.rec.{u} : (motive : T → Sort u) → (∀ fields₀, IH₀ → motive (c₀ fields₀)) → …
→ (t : T) → motive t`, rule `j`: `λ motive minors fields, mⱼ fields (T.rec
motive minors xᵣ)…` for each recursive field `xᵣ`. -/
def simpleRecursor (blk : Addr) (ctors : Array (Array Field)) : Constant := Id.run do
  let n := ctors.size
  let exts := ctors.foldl (fun acc fs => fs.foldl (fun acc f => match f with
    | .ext t => if acc.contains t then acc else acc.push t
    | .self => acc) acc) (#[] : Array Addr)
  let refs := #[indcProjAddr blk 0] ++ (Array.range n).map (ctorProjAddr blk 0 ·.toUInt64) ++ exts
  let tyRef : E := .ref 0 #[]
  let fieldType := fun (f : Field) => match f with
    | .self => tyRef
    | .ext t => .ref (1 + n + (exts.findIdx? (· == t) |>.getD 0)).toUInt64 #[]
  let v := fun (i : Nat) => (.var i.toUInt64 : E)
  let motiveTy : E := arrow tyRef (.sort 0)
  -- minor premise `j`, under the motive and minors `0 … j-1` (`motive` is `var j`)
  let minor := fun (j : Nat) => Id.run do
    let fs := ctors[j]!
    let m := fs.size
    let recs := (List.range m).filter fun i => fs[i]! == .self
    let h := recs.length
    let ctorApp := (List.range m).foldl (fun acc i => V3.Expr.app acc (v (m + h - 1 - i)))
      (.ref (1 + j).toUInt64 #[] : E)
    let mut body : E := .app (v (j + m + h)) ctorApp
    -- the induction hypotheses, innermost last: hypothesis `q` (for field `recs[q]`)
    -- sits at depth `m + q` within the minor
    for q in (List.range h).reverse do
      let r := recs[q]!
      body := arrow (.app (v (j + m + q)) (v (m + q - 1 - r))) body
    for i in (List.range m).reverse do
      body := arrow (fieldType fs[i]!) body
    return body
  let major : E := arrow tyRef (.app (v (n + 1)) (v 0))
  let typ := arrow motiveTy ((List.range n).foldr (fun j acc => arrow (minor j) acc) major)
  let rule := fun (j : Nat) => Id.run do
    let fs := ctors[j]!
    let m := fs.size
    -- under the motive, the `n` minors and the `m` fields: `1 + n + m` binders
    let motive := v (n + m)
    let minorAt := fun (k : Nat) => v (n + m - 1 - k)
    let field := fun (i : Nat) => v (m - 1 - i)
    let recAt := fun (i : Nat) => Id.run do
      let mut e : E := .app (.recur 0 #[0]) motive
      for k in List.range n do e := .app e (minorAt k)
      return V3.Expr.app e (field i)
    let mut body : E := (List.range m).foldl (fun acc i => V3.Expr.app acc (field i)) (minorAt j)
    for i in List.range m do
      if fs[i]! == .self then body := .app body (recAt i)
    for i in (List.range m).reverse do
      body := lambda (fieldType fs[i]!) body
    for k in (List.range n).reverse do
      body := lambda (minor k) body
    return (⟨m.toUInt64, lambda motiveTy body⟩ : RecursorRule)
  let r : Recursor := ⟨false, false, 1, 0, 0, 1, n.toUInt64, typ, (Array.range n).map rule⟩
  return ⟨.recr r, #[], refs, #[.var 0]⟩

/-- A simple inductive block and its recursor, as a test adds them. -/
structure Ind where
  block : Addr
  ind : Addr
  ctors : Array Addr
  recursor : Addr
  /-- whether the block was already in the environment (its recursor too) -/
  existing : Bool

/-- Add `simpleBlock ctors` with its projection records and, unless the block
is already there, its recursor. -/
def addSimple (env : Env) (ctors : Array (Array Field)) : Env × Ind := Id.run do
  let c := simpleBlock ctors
  let existing := env.consts.contains (record c).2
  let (env, blk) := block env c
  let recC := simpleRecursor blk ctors
  let (env, recursor) := if existing then (env, (record recC).2) else store env recC
  return (env, { block := blk, ind := indcProjAddr blk 0,
                 ctors := (Array.range ctors.size).map (ctorProjAddr blk 0 ·.toUInt64),
                 recursor, existing })

/-- `inductive E | c₀ | … | cₙ₋₁ : Type` with its recursor. -/
def addEnum (env : Env) (n : Nat) : Env × Ind :=
  addSimple env ((Array.range n).map fun _ => #[])

/-- `inductive T | leaf | node (l r : T) : Type` with its recursor. -/
def addTree (env : Env) : Env × Ind :=
  addSimple env #[#[], #[.self, .self]]

/-- `inductive L | nil | cons (x : A) (xs : L) : Type`, monomorphic in the type at
`elem`, with its recursor. -/
def addList (env : Env) (elem : Addr) : Env × Ind :=
  addSimple env #[#[], #[.ext elem, .self]]

end IxCCTests.Support.Bound
