import Aiur.Plonk.Source
import Aiur.Library.Field.BN254
import Std.Data.HashMap

/-!
# Untrusted lowering of Aiur tables to sparse PLONK gates

The lowering produces, for each table, gate templates over references:

* `cell k`: main cell `k / 2` of the current (`k` even) or next (`k` odd) row;
* `loc k`: a row-local internal wire;
* `pool k`: a global wire (`0` is the commitment challenge `γ`, `1` is `β`,
  then powers of `γ` and shared fingerprint bases);
* `sumIn`, `sumOut`: the LogUp running sum entering and leaving the row.

A table without fixed, selector or `last` reads is *uniform*: one template
serves every row. Other tables get one template per row, with the row's fixed
values and selectors folded into the coefficients.

Each node is evaluated to an affine form over atoms (cells, products of two
non-constant forms, and multi-term linear nodes used more than once). Gates
are emitted for asserted forms, lookup messages and the atoms they reach:

* a product `(αx + k)(βy + l)` is one gate;
* an asserted form with `n ≤ 3` atoms is one gate, otherwise `n - 2`;
* an asserted form whose single-use product atom has single-atom operands is
  that product's gate, with at most one further linear wire;
* a message is its fingerprint chain `d = base + Σ αᵢ·vᵢ·γ^eᵢ`, the gate
  `q·d = ±m` and the running-sum gate `s' = s + q`;
* a message of constants in a table with fixed columns is
  `d = U + k·γ^e + k₀`, `U` a shared pool base;
* a message whose multiplicity is the constant zero is dropped.

Nothing here is trusted: the checker validates every gate's meaning.
-/

namespace Aiur.Plonk.Lower

open Aiur.Library.Field.BN254 (modulus)

abbrev Fr := Aiur.Library.Field.BN254.F

inductive Tag where
  | constraint | count | fingerprint | logup | pool
  deriving Repr, BEq, Inhabited

/-- References, packed as `4k`, `4k+1`, `4k+2`; `3` is `sumIn`, `7` is `sumOut`. -/
abbrev Ref := Nat

def cell (k : Nat) : Ref := 4 * k
def loc (k : Nat) : Ref := 4 * k + 1
def pool (k : Nat) : Ref := 4 * k + 2
def sumIn : Ref := 3
def sumOut : Ref := 7

def gammaRef : Ref := pool 0
def betaRef : Ref := pool 1

structure LGate where
  a : Ref
  b : Ref
  c : Ref
  L : Fr
  R : Fr
  O : Fr
  M : Fr
  C : Fr
  tag : Tag
  /-- The table constraint this gate asserts, if any. -/
  root : Option Nat := none
  /-- The lookup whose multiplicity, `q` or running-sum relation this gate asserts. -/
  msg : Option Nat := none
  deriving Inhabited

/-- An affine form `Σ cs[i]·atom ids[i] + k`, atoms strictly increasing. -/
structure Form where
  ids : Array Nat := #[]
  cs : Array Fr := #[]
  k : Fr := 0
  deriving Inhabited

def Form.isConst (f : Form) : Bool := f.ids.isEmpty

def Form.combine (a b : Form) (negate : Bool) : Form := Id.run do
  let mut ids := #[]
  let mut cs := #[]
  let mut i := 0
  let mut j := 0
  while i < a.ids.size || j < b.ids.size do
    if j == b.ids.size || (i < a.ids.size && a.ids[i]! < b.ids[j]!) then
      ids := ids.push a.ids[i]!; cs := cs.push a.cs[i]!; i := i + 1
    else if i == a.ids.size || b.ids[j]! < a.ids[i]! then
      ids := ids.push b.ids[j]!; cs := cs.push (if negate then -b.cs[j]! else b.cs[j]!); j := j + 1
    else
      let c := if negate then a.cs[i]! - b.cs[j]! else a.cs[i]! + b.cs[j]!
      if c != 0 then ids := ids.push a.ids[i]!; cs := cs.push c
      i := i + 1; j := j + 1
  return { ids, cs, k := if negate then a.k - b.k else a.k + b.k }

def Form.scale (a : Form) (s : Fr) : Form :=
  if s == 0 then {} else { ids := a.ids, cs := a.cs.map (· * s), k := a.k * s }

/-- Global state: pool wires and their memo tables. -/
structure Pool where
  gates : Array LGate := #[]
  next : Nat := 2
  powers : Std.HashMap Nat Ref := {}
  chain : Std.HashMap (Ref × Nat × Nat) Ref := {}
  deriving Inhabited

/-- Row state. -/
structure St where
  gates : Array LGate := #[]
  nloc : Nat := 0
  atoms : Std.HashMap Nat (Ref × Fr) := {}
  linear : Std.HashMap (List (Nat × Nat)) Ref := {}
  products : Std.HashMap (Ref × Nat) Ref := {}
  chain : Std.HashMap (Ref × Ref × Nat × Nat) Ref := {}
  booleans : Std.HashMap Nat Unit := {}
  sum : Ref := sumIn
  pool : Pool := {}
  deriving Inhabited

abbrev M := StateM St

def freshLoc : M Ref := modifyGet fun s => (loc s.nloc, { s with nloc := s.nloc + 1 })

def gate (tag : Tag) (a b c : Ref) (qL qR qO qM qC : Fr) : M Unit :=
  modify fun s => { s with gates := s.gates.push ⟨a, b, c, qL, qR, qO, qM, qC, tag, none, none⟩ }

def poolFresh : M Ref := modifyGet fun s =>
  (pool s.pool.next, { s with pool := { s.pool with next := s.pool.next + 1 } })

def poolGate (a b c : Ref) (qL qR qO qM qC : Fr) : M Unit :=
  modify fun s => { s with pool := { s.pool with gates := s.pool.gates.push ⟨a, b, c, qL, qR, qO, qM, qC, .pool, none, none⟩ } }

/-- The pool wire `γ^e` for `e ≥ 1`. -/
partial def power (e : Nat) : M Ref := do
  if e == 1 then return gammaRef
  match (← get).pool.powers[e]? with
  | some r => return r
  | none =>
      let prev ← power (e - 1)
      let r ← poolFresh
      poolGate prev gammaRef r 0 0 (-1) 1 0
      modify fun s => { s with pool := { s.pool with powers := s.pool.powers.insert e r } }
      return r

/-- The pool wire `acc + k·γ^e` (`e ≥ 1`), shared by `(acc, e, k)`. -/
def poolAdd (acc : Ref) (e : Nat) (k : Fr) : M Ref := do
  match (← get).pool.chain[(acc, e, k.val)]? with
  | some r => return r
  | none =>
      let p ← power e
      let r ← poolFresh
      poolGate acc p r 1 k (-1) 0 0
      modify fun s => { s with pool := { s.pool with chain := s.pool.chain.insert (acc, e, k.val) r } }
      return r

/-- The fingerprint base `β + n·γ^n + Σ k_e·γ^e` over nonzero exponents. -/
def base (n : Nat) (consts : List (Nat × Fr)) : M Ref := do
  let mut acc ← poolAdd betaRef n (n : Fr)
  for (e, k) in consts do
    acc ← poolAdd acc e k
  return acc

structure Ctx where
  table : Table Fr
  row : Nat
  forms : Array Form
  defs : Std.HashMap Nat Form
  uses : Std.HashMap Nat Nat
  base : Nat

def Ctx.isProduct (x : Ctx) (atom : Nat) : Bool := atom ≥ x.base && !x.defs.contains (atom - x.base)

def nodeOperands : Node Fr → List Nat
  | .add a b | .sub a b | .mul a b => [a, b]
  | .neg a => [a]
  | _ => []

def Table.uniform (t : Table Fr) : Bool :=
  t.nodes.all fun
    | .fixed .. | .first | .last | .transition => false
    | _ => true

/-- Shared multi-term linear nodes become atoms, as in the Go lowering. -/
def sharedNodes (t : Table Fr) : Array Bool := Id.run do
  let mut refs := Array.replicate t.nodes.size 0
  for n in t.nodes do
    for o in nodeOperands n do refs := refs.modify o (· + 1)
  for i in t.constraints do refs := refs.modify i (· + 1)
  for l in t.lookups do
    refs := refs.modify l.count (· + 1)
    for i in l.args do refs := refs.modify i (· + 1)
  return (t.nodes.zip refs).map fun
    | (.add .., r) | (.sub .., r) | (.neg .., r) => r ≥ 2
    | _ => false

def evaluate (t : Table Fr) (shared : Array Bool) (row : Nat) : Ctx := Id.run do
  let base := 2 * t.width
  let next := (row + 1) % t.rows
  let mut forms : Array Form := #[]
  let mut defs : Std.HashMap Nat Form := {}
  for h : i in [0:t.nodes.size] do
    let get (j : Nat) : Form := forms.getD j {}
    let mut atomic := false
    let mut f : Form := match t.nodes[i] with
      | .const v => { k := v }
      | .main c n => { ids := #[2 * c + (if n then 1 else 0)], cs := #[1] }
      | .fixed c n => { k := t.fixed.getD ((if n then next else row) * t.fixedWidth + c) 0 }
      | .first => { k := if row == 0 then 1 else 0 }
      | .last => { k := if row + 1 == t.rows then 1 else 0 }
      | .transition => { k := if row + 1 == t.rows then 0 else 1 }
      | .add a b => (get a).combine (get b) false
      | .sub a b => (get a).combine (get b) true
      | .neg a => (get a).scale (-1)
      | .mul a b =>
          if (get a).isConst then (get b).scale (get a).k
          else if (get b).isConst then (get a).scale (get b).k
          else {}
    if let .mul a b := t.nodes[i] then
      if !(get a).isConst && !(get b).isConst then atomic := true
    if shared.getD i false && f.ids.size ≥ 2 then
      atomic := true
      defs := defs.insert i f
    if atomic then f := { ids := #[base + i], cs := #[1] }
    forms := forms.push f
  -- uses of atoms, for product fusion
  let mut uses : Std.HashMap Nat Nat := {}
  let demand (u : Std.HashMap Nat Nat) (f : Form) : Std.HashMap Nat Nat :=
    f.ids.foldl (fun u a => u.insert a (u.getD a 0 + 1)) u
  for j in t.constraints do uses := demand uses (forms.getD j {})
  for l in t.lookups do
    uses := demand uses (forms.getD l.count {})
    for a in l.args do uses := demand uses (forms.getD a {})
  for h : i in [0:t.nodes.size] do
    if (forms.getD i {}).ids == #[base + i] then
      match defs[i]? with
      | some d => uses := demand uses d
      | none =>
          for o in nodeOperands t.nodes[i] do uses := demand uses (forms.getD o {})
  return { table := t, row, forms, defs, uses, base }

mutual

/-- The wire of an atom and its coefficient: `coeff·wire` is the atom. -/
partial def atomWire (x : Ctx) (atom : Nat) : M (Ref × Fr) := do
  if atom < x.base then return (cell atom, 1)
  if let some w := (← get).atoms[atom]? then return w
  let node := atom - x.base
  let w ← match x.defs[node]? with
    | some d => do
        let (r, s) ← linearWire x d true
        pure (r, s)
    | none => do
        let (a, b) := match x.table.nodes[node]! with
          | .mul a b => (a, b)
          | _ => (0, 0)
        let (ra, α, k) ← operand x (x.forms.getD a {})
        let (rb, β, l) ← operand x (x.forms.getD b {})
        let p ← freshLoc
        gate .constraint ra rb p (α * l) (β * k) (-1) (α * β) (k * l)
        pure (p, 1)
  modify fun s => { s with atoms := s.atoms.insert atom w }
  return w

/-- `(wire, α, k)` with the form equal to `α·wire + k`. -/
partial def operand (x : Ctx) (f : Form) : M (Ref × Fr × Fr) := do
  if f.ids.size == 1 then
    let (r, s) ← atomWire x f.ids[0]!
    return (r, f.cs[0]! * s, f.k)
  let (r, s) ← linearWire x { f with k := 0 } false
  return (r, s, f.k)

/-- A wire for the form (its constant included when `withK`), memoised up to
scale; returns `(wire, scale)` with `scale·wire` the form. -/
partial def linearWire (x : Ctx) (f : Form) (withK : Bool) : M (Ref × Fr) := do
  if f.ids.size == 1 && (!withK || f.k == 0) then
    let (r, s) ← atomWire x f.ids[0]!
    return (r, f.cs[0]! * s)
  let c0 := f.cs[0]!
  let inv := c0⁻¹
  let key := (f.ids.toList.zip (f.cs.toList.map fun c => (c * inv).val)) ++
    (if withK then [(2 ^ 62, (f.k * inv).val)] else [])
  if let some r := (← get).linear[key]? then return (r, c0)
  let mut terms : Array (Ref × Fr) := #[]
  for i in [0:f.ids.size] do
    let (r, s) ← atomWire x f.ids[i]!
    terms := terms.push (r, f.cs[i]! * inv * s)
  let kk := if withK then f.k * inv else 0
  let mut acc ← freshLoc
  if terms.size == 1 then
    gate .constraint terms[0]!.1 terms[0]!.1 acc terms[0]!.2 0 (-1) 0 kk
  else
    gate .constraint terms[0]!.1 terms[1]!.1 acc terms[0]!.2 terms[1]!.2 (-1) 0 kk
    for i in [2:terms.size] do
      let nxt ← freshLoc
      gate .constraint acc terms[i]!.1 nxt 1 terms[i]!.2 (-1) 0 0
      acc := nxt
  modify fun s => { s with linear := s.linear.insert key acc }
  return (acc, c0)

end

def markRoot (j : Nat) : M Unit :=
  modify fun s => { s with gates := s.gates.modify (s.gates.size - 1) fun g => { g with root := some j } }

def assertZero (x : Ctx) (f : Form) : M Unit := do
  if f.isConst then
    if f.k != 0 then gate .constraint sumIn sumIn sumIn 0 0 0 0 f.k
    return
  -- a single-use product atom with single-atom operands is this relation's gate
  for i in [0:f.ids.size] do
    let atom := f.ids[i]!
    if x.isProduct atom && x.uses.getD atom 0 == 1 then
      let (a, b) := match x.table.nodes[atom - x.base]! with
        | .mul a b => (a, b)
        | _ => (0, 0)
      let fa := x.forms.getD a {}
      let fb := x.forms.getD b {}
      let (ra, α, k) ← operand x fa
      let (rb, β, l) ← operand x fb
      let c := f.cs[i]!
      let mut L := α * l * c
      let mut R := β * k * c
      let Mq := α * β * c
      let C := k * l * c + f.k
      let ia := if fa.ids.size == 1 then fa.ids[0]! else 0
      let ib := if fb.ids.size == 1 then fb.ids[0]! else 0
      let mut extra : Form := {}
      for j in [0:f.ids.size] do
        if j == i then continue
        let o := f.ids[j]!
        if fa.ids.size == 1 && o == ia then L := L + f.cs[j]!
        else if fb.ids.size == 1 && o == ib then R := R + f.cs[j]!
        else extra := { extra with ids := extra.ids.push o, cs := extra.cs.push f.cs[j]! }
      if extra.ids.isEmpty then
        gate .constraint ra rb ra L R 0 Mq C
      else
        let (re, s) ← linearWire x extra false
        gate .constraint ra rb re L R s Mq C
      return
  let n := f.ids.size
  if n ≤ 3 then
    let mut ws : Array (Ref × Fr) := #[]
    for i in [0:n] do
      let (r, s) ← atomWire x f.ids[i]!
      ws := ws.push (r, f.cs[i]! * s)
    let w (i : Nat) : Ref × Fr := ws.getD i (ws[0]!.1, 0)
    gate .constraint (w 0).1 (w 1).1 (w 2).1 (w 0).2 (w 1).2 (w 2).2 0 f.k
  else
    let head : Form := { ids := f.ids.extract 0 (n - 2), cs := f.cs.extract 0 (n - 2) }
    let (rh, sh) ← linearWire x head false
    let (r1, s1) ← atomWire x f.ids[n - 2]!
    let (r2, s2) ← atomWire x f.ids[n - 1]!
    gate .constraint rh r1 r2 sh (f.cs[n - 2]! * s1) (f.cs[n - 1]! * s2) 0 f.k

/-- `γ^e·wire`, shared within the row. -/
def scaledByPower (w : Ref) (e : Nat) : M Ref := do
  if let some r := (← get).products[(w, e)]? then return r
  let p ← power e
  let r ← freshLoc
  gate .fingerprint w p r 0 0 (-1) 1 0
  modify fun s => { s with products := s.products.insert (w, e) r }
  return r

def message (x : Ctx) (l : Lookup) : M Unit := do
  let cf := x.forms.getD l.count {}
  if cf.isConst && cf.k == 0 then return
  let sign : Fr := if l.negative then -1 else 1
  -- multiplicity `α·mw + mk`; a request's multiplicity is boolean
  let (mw, α, mk) ← if cf.isConst then pure (sumIn, (0 : Fr), cf.k) else operand x cf
  if !cf.isConst && !l.negative && !(← get).booleans.contains l.count then
    gate .count mw mw mw (2 * α * mk - α) 0 0 (α * α) (mk * mk - mk)
    modify fun s => { s with booleans := s.booleans.insert l.count () }
  let n := l.args.length
  let mut consts : Array (Nat × Fr) := #[]
  let mut c0 : Fr := 0
  let mut vars : Array (Ref × Fr × Nat) := #[]
  for (a, i) in l.args.zipIdx do
    let e := expOf n i
    let f := x.forms.getD a {}
    if f.k != 0 then
      if e == 0 then c0 := f.k else consts := consts.push (e, f.k)
    if !f.isConst then
      let (r, s, _) ← operand x { f with k := 0 }
      vars := vars.push (r, s, e)
  let sorted := consts.qsort (fun p q => p.1 < q.1)
  let mut d : Ref := 0
  if vars.isEmpty && x.table.fixedWidth > 0 && sorted.size ≥ 1 then
    let (ex, kx) := sorted[0]!
    let u ← base n (sorted.extract 1 sorted.size).toList
    let p ← power ex
    d ← freshLoc
    gate .fingerprint u p d 1 kx (-1) 0 c0
  else
    let b ← base n sorted.toList
    let mut acc := b
    let mut pendingC := c0
    if vars.isEmpty then
      if c0 != 0 then
        let r ← freshLoc
        gate .fingerprint acc acc r 1 0 (-1) 0 c0
        acc := r
    let ordered := vars.qsort (fun p q => p.1 < q.1 || (p.1 == q.1 && p.2.2 < q.2.2))
    for (w, s, e) in ordered do
      let t ← if e == 0 then pure w else scaledByPower w e
      let key := (acc, t, e, s.val + pendingC.val * modulus)
      match (← get).chain[key]? with
      | some r => acc := r
      | none =>
          let r ← freshLoc
          gate .fingerprint acc t r 1 s (-1) 0 pendingC
          modify fun st => { st with chain := st.chain.insert key r }
          acc := r
      pendingC := 0
    d := acc
  -- q·d = sign·m, then s' = s + q
  let q ← freshLoc
  gate .logup q d mw 0 0 (-sign * α) 1 (-sign * mk)
  let s ← freshLoc
  gate .logup (← get).sum q s 1 1 (-1) 0 0
  modify fun st => { st with sum := s }

/-- One row template: the table's constraints and messages at `row`. -/
def lowerRow (t : Table Fr) (shared : Array Bool) (row : Nat) : M Unit := do
  let x := evaluate t shared row
  for (j, i) in t.constraints.zipIdx do
    let before := (← get).gates.size
    assertZero x (x.forms.getD j {})
    if (← get).gates.size > before then markRoot i
  for (l, k) in t.lookups.zipIdx do
    let before := (← get).gates.size
    message x l
    modify fun s => Id.run do
      let mut gs := s.gates
      for i in [before:gs.size] do
        let g := gs[i]!
        if g.tag == .count || g.tag == .logup then gs := gs.set! i { g with msg := some k }
      return { s with gates := gs }

/-- Main columns some message depends on: the committed cells of a row. -/
def messageColumns (t : Table Fr) : List Nat := Id.run do
  let mut deps : Array (List Nat) := #[]
  for n in t.nodes do
    let d := match n with
      | .main c _ => [c]
      | .add a b | .sub a b | .mul a b => deps.getD a [] ++ deps.getD b []
      | .neg a => deps.getD a []
      | _ => []
    deps := deps.push d.eraseDups
  let mut cols : List Nat := []
  for l in t.lookups do
    cols := cols ++ deps.getD l.count []
    for a in l.args do cols := cols ++ deps.getD a []
  return cols.eraseDups

structure Census where
  constraint : Nat := 0
  count : Nat := 0
  fingerprint : Nat := 0
  logup : Nat := 0
  pool : Nat := 0
  commit : Nat := 0
  deriving Repr, Inhabited

def Census.total (c : Census) : Nat :=
  c.constraint + c.count + c.fingerprint + c.logup + c.pool + c.commit

def Census.add (c : Census) (gs : Array LGate) (times : Nat) : Census :=
  gs.foldl (fun c g => match g.tag with
    | .constraint => { c with constraint := c.constraint + times }
    | .count => { c with count := c.count + times }
    | .fingerprint => { c with fingerprint := c.fingerprint + times }
    | .logup => { c with logup := c.logup + times }
    | .pool => { c with pool := c.pool + times }) c

/-- Lower a table; returns its census and the updated pool. Row templates are
dropped after counting. -/
def lowerTable (t : Table Fr) (p : Pool) : Census × Pool := Id.run do
  let shared := sharedNodes t
  let commit := t.rows * (messageColumns t).length
  if Table.uniform t then
    let ((), s) := (lowerRow t shared 0).run { pool := p }
    return (Census.add { commit := commit } s.gates t.rows, s.pool)
  let mut c : Census := { commit := commit }
  let mut p := p
  for r in [0:t.rows] do
    let ((), s) := (lowerRow t shared r).run { pool := p }
    c := c.add s.gates 1
    p := s.pool
  return (c, p)

end Aiur.Plonk.Lower
