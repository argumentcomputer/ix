import Ix.Ixon

/-!
# Expanded recursor records and single-edit variants of them

A stored record shares subterms through its sharing table and keeps each binder's datum in
a separate section, aligned with the binders in pre-order. To alter one place of a
recursor's type or of a rule, the record is first expanded: every share replaced by its
entry, every binder carrying its own datum (`AE`). An expanded record is written back with
an empty sharing table and one block of data per root, so an edit that moves, drops or
copies a binder keeps every other binder's datum where it was. The expanded form of an
unaltered record must be accepted like the record itself; the suite runs it as the control
of every altered one.

The edits (`mutantsOf`) each change one thing: a bound-variable index, two indices
exchanged, an argument dropped, copied or exchanged with its neighbour, the minor premise
a rule applies, a universe level, a referenced constant, a binder's datum, a count of the
record, the order of two rules or of two minor premises.
-/

namespace Tests.Ix.IxVM.RecGen

/-- An expression with its sharing expanded, each binder with its datum. -/
inductive AE where
  | sort (u : UInt64)
  | var (i : UInt64)
  | ref (i : UInt64) (us : Array UInt64)
  | recur (i : UInt64) (us : Array UInt64)
  | prj (t i : UInt64) (e : AE)
  | str (i : UInt64)
  | nat (i : UInt64)
  | app (f a : AE)
  | lam (d : Ixon.BinderNode) (t b : AE)
  | all (d : Ixon.BinderNode) (t b : AE)
  | letE (nd : Bool) (m : Ixon.LetMode) (t v b : AE)
  deriving BEq, Inhabited

namespace AE

partial def toExpr : AE → Ixon.Expr
  | .sort u => .sort u
  | .var i => .var i
  | .ref i us => .ref i us
  | .recur i us => .recur i us
  | .prj t i e => .prj t i e.toExpr
  | .str i => .str i
  | .nat i => .nat i
  | .app f a => .app f.toExpr a.toExpr
  | .lam _ t b => .lam t.toExpr b.toExpr
  | .all _ t b => .all t.toExpr b.toExpr
  | .letE nd m t v b => .letE nd m t.toExpr v.toExpr b.toExpr

/-- The binder data in the section's order: a binder, its type, its body. -/
partial def nodes : AE → Array Ixon.BinderNode → Array Ixon.BinderNode
  | .lam d t b, acc => b.nodes (t.nodes (acc.push d))
  | .all d t b, acc => b.nodes (t.nodes (acc.push d))
  | .app f a, acc => a.nodes (f.nodes acc)
  | .letE _ _ t v b, acc => b.nodes (v.nodes (t.nodes acc))
  | .prj _ _ e, acc => e.nodes acc
  | _, acc => acc

/-- Add `n` to every variable at or above `k`. -/
partial def lift (n : Nat) : Nat → AE → AE
  | k, .var i => if i.toNat ≥ k then .var (i + n.toUInt64) else .var i
  | k, .app f a => .app (lift n k f) (lift n k a)
  | k, .lam d t b => .lam d (lift n k t) (lift n (k + 1) b)
  | k, .all d t b => .all d (lift n k t) (lift n (k + 1) b)
  | k, .letE nd m t v b => .letE nd m (lift n k t) (lift n k v) (lift n (k + 1) b)
  | k, .prj t i e => .prj t i (lift n k e)
  | _, e => e

/-- Remove the binder `k`: variables above it move down; `none` when it is used. -/
partial def lower : Nat → AE → Option AE
  | k, .var i =>
    if i.toNat == k then none else if i.toNat > k then some (.var (i - 1)) else some (.var i)
  | k, .app f a => do pure (.app (← lower k f) (← lower k a))
  | k, .lam d t b => do pure (.lam d (← lower k t) (← lower (k + 1) b))
  | k, .all d t b => do pure (.all d (← lower k t) (← lower (k + 1) b))
  | k, .letE nd m t v b => do pure (.letE nd m (← lower k t) (← lower k v) (← lower (k + 1) b))
  | k, .prj t i e => do pure (.prj t i (← lower k e))
  | _, e => some e

partial def spine : AE → AE × Array AE
  | .app f a =>
    let (h, as) := spine f
    (h, as.push a)
  | e => (e, #[])

def mkApp (h : AE) (as : Array AE) : AE := as.foldl .app h

abbrev Binder := Ixon.BinderNode × AE

partial def peelLams : Nat → AE → Option (Array Binder × AE)
  | 0, e => some (#[], e)
  | n + 1, .lam d t b => (peelLams n b).map fun (bs, body) => (#[(d, t)] ++ bs, body)
  | _, _ => none

partial def peelAlls : Nat → AE → Option (Array Binder × AE)
  | 0, e => some (#[], e)
  | n + 1, .all d t b => (peelAlls n b).map fun (bs, body) => (#[(d, t)] ++ bs, body)
  | _, _ => none

partial def peelAllLams : AE → Array Binder × AE
  | .lam d t b =>
    let (bs, body) := peelAllLams b
    (#[(d, t)] ++ bs, body)
  | e => (#[], e)

partial def peelAllAlls : AE → Array Binder × AE
  | .all d t b =>
    let (bs, body) := peelAllAlls b
    (#[(d, t)] ++ bs, body)
  | e => (#[], e)

def mkLams (bs : Array Binder) (body : AE) : AE := bs.foldr (fun (d, t) b => .lam d t b) body

def mkAlls (bs : Array Binder) (body : AE) : AE := bs.foldr (fun (d, t) b => .all d t b) body

/-- The nodes `site` selects, in pre-order. A selected node is not entered. -/
partial def sites (site : AE → Bool) : AE → Array AE → Array AE
  | e, acc =>
    if site e then acc.push e else
    match e with
    | .app f a => sites site a (sites site f acc)
    | .lam _ t b => sites site b (sites site t acc)
    | .all _ t b => sites site b (sites site t acc)
    | .letE _ _ t v b => sites site b (sites site v (sites site t acc))
    | .prj _ _ x => sites site x acc
    | _ => acc

/-- Rewrite the `target`-th selected node (in the order of `sites`) by `f`. -/
partial def mapNthAux (site : AE → Bool) (f : AE → AE) (target : Nat) : AE → Nat → AE × Nat
  | e, k =>
    if site e then (if k == target then f e else e, k + 1) else
    match e with
    | .app g a =>
      let (g', k1) := mapNthAux site f target g k
      let (a', k2) := mapNthAux site f target a k1
      (.app g' a', k2)
    | .lam d t b =>
      let (t', k1) := mapNthAux site f target t k
      let (b', k2) := mapNthAux site f target b k1
      (.lam d t' b', k2)
    | .all d t b =>
      let (t', k1) := mapNthAux site f target t k
      let (b', k2) := mapNthAux site f target b k1
      (.all d t' b', k2)
    | .letE nd m t v b =>
      let (t', k1) := mapNthAux site f target t k
      let (v', k2) := mapNthAux site f target v k1
      let (b', k3) := mapNthAux site f target b k2
      (.letE nd m t' v' b', k3)
    | .prj t i x =>
      let (x', k1) := mapNthAux site f target x k
      (.prj t i x', k1)
    | e => (e, k)

def mapNth (site : AE → Bool) (f : AE → AE) (target : Nat) (e : AE) : AE :=
  (mapNthAux site f target e 0).1

def isVar : AE → Bool
  | .var _ => true
  | _ => false

def isLevelSite : AE → Bool
  | .sort _ => true
  | .ref _ us => !us.isEmpty
  | .recur _ us => !us.isEmpty
  | _ => false

def isRef : AE → Bool
  | .ref .. => true
  | _ => false

/-- The binders of a term, each a place for a datum. -/
partial def binderCount : AE → Nat
  | .lam _ t b => 1 + binderCount t + binderCount b
  | .all _ t b => 1 + binderCount t + binderCount b
  | .app f a => binderCount f + binderCount a
  | .letE _ _ t v b => binderCount t + binderCount v + binderCount b
  | .prj _ _ x => binderCount x
  | _ => 0

/-- A datum with another zero set. -/
def flipDatum : Ixon.BinderNode → Ixon.BinderNode
  | .never m => .zero m
  | .zero m => .never m
  | .ifAllZero _ m => .never m
  | d => d

/-- Change the datum of the `target`-th binder (pre-order). -/
partial def flipNthDatumAux (target : Nat) : AE → Nat → AE × Nat
  | .lam d t b, k =>
    let d' := if k == target then flipDatum d else d
    let (t', k1) := flipNthDatumAux target t (k + 1)
    let (b', k2) := flipNthDatumAux target b k1
    (.lam d' t' b', k2)
  | .all d t b, k =>
    let d' := if k == target then flipDatum d else d
    let (t', k1) := flipNthDatumAux target t (k + 1)
    let (b', k2) := flipNthDatumAux target b k1
    (.all d' t' b', k2)
  | .app f a, k =>
    let (f', k1) := flipNthDatumAux target f k
    let (a', k2) := flipNthDatumAux target a k1
    (.app f' a', k2)
  | .letE nd m t v b, k =>
    let (t', k1) := flipNthDatumAux target t k
    let (v', k2) := flipNthDatumAux target v k1
    let (b', k3) := flipNthDatumAux target b k2
    (.letE nd m t' v' b', k3)
  | .prj t i x, k =>
    let (x', k1) := flipNthDatumAux target x k
    (.prj t i x', k1)
  | e, k => (e, k)

def flipNthDatum (target : Nat) (e : AE) : AE := (flipNthDatumAux target e 0).1

/-- Substitute `v` for the variable `k`; variables above it move down. -/
partial def inst (v : AE) : Nat → AE → AE
  | k, .var i =>
    if i.toNat == k then v.lift k 0 else if i.toNat > k then .var (i - 1) else .var i
  | k, .app f a => .app (inst v k f) (inst v k a)
  | k, .lam d t b => .lam d (inst v k t) (inst v (k + 1) b)
  | k, .all d t b => .all d (inst v k t) (inst v (k + 1) b)
  | k, .letE nd m t x b => .letE nd m (inst v k t) (inst v k x) (inst v (k + 1) b)
  | k, .prj t i e => .prj t i (inst v k e)
  | _, e => e

/-- Every `let` replaced by its body at its value: what the comparison of a stored term with
a generated one reads, whatever a `let`'s type annotation is. -/
partial def zeta : AE → AE
  | .letE _ _ _ v b => zeta (inst (zeta v) 0 b)
  | .app f a => .app (zeta f) (zeta a)
  | .lam d t b => .lam d (zeta t) (zeta b)
  | .all d t b => .all d (zeta t) (zeta b)
  | .prj t i e => .prj t i (zeta e)
  | e => e

end AE

/-! ## Expanding a record -/

partial def hasBinderUnder (full : Array Bool) : Ixon.Expr → Bool
  | .lam .. => true
  | .all .. => true
  | .app f a => hasBinderUnder full f || hasBinderUnder full a
  | .letE _ _ t v b => hasBinderUnder full t || hasBinderUnder full v || hasBinderUnder full b
  | .prj _ _ v => hasBinderUnder full v
  | .share n => full[n.toNat]?.getD false
  | _ => false

/-- Per sharing entry, whether it has a binder (through its own shares). -/
def binderful (sharing : Array Ixon.Expr) : Array Bool :=
  sharing.foldl (fun out e => out.push (hasBinderUnder out e)) #[]

structure ExpandCx where
  sharing : Array Ixon.Expr
  full : Array Bool
  blocks : Std.HashMap (Bool × Nat × Nat) (Array Ixon.BinderNode)
  /-- the largest expanded tree accepted, in nodes -/
  cap : Nat

abbrev ExpandM := StateT (Std.HashMap (Nat × Nat) (AE × Nat)) (Except String)

/-- `e` expanded with the nodes of its block from `pos` on: the tree, its size, and the
position after its own nodes. -/
def expand (cx : ExpandCx) : Nat → Ixon.Expr → Array Ixon.BinderNode → Nat →
    ExpandM (AE × Nat × Nat)
  | 0, _, _, _ => throw "the expansion ran out of depth"
  | fuel + 1, e, nodes, pos => do
    match e with
    | .sort u => return (.sort u, 1, pos)
    | .var i => return (.var i, 1, pos)
    | .ref i us => return (.ref i us, 1, pos)
    | .recur i us => return (.recur i us, 1, pos)
    | .str i => return (.str i, 1, pos)
    | .nat i => return (.nat i, 1, pos)
    | .prj t i v =>
      let (v', s, p) ← expand cx fuel v nodes pos
      return (.prj t i v', s + 1, p)
    | .app f a =>
      let (f', s1, p1) ← expand cx fuel f nodes pos
      let (a', s2, p2) ← expand cx fuel a nodes p1
      if s1 + s2 + 1 > cx.cap then throw "the expanded term exceeds the size cap"
      return (.app f' a', s1 + s2 + 1, p2)
    | .lam t b =>
      let some d := nodes[pos]? | throw "binder data: a block is shorter than its expression"
      if let .share _ := d then throw "binder data: a share node at a binder"
      let (t', s1, p1) ← expand cx fuel t nodes (pos + 1)
      let (b', s2, p2) ← expand cx fuel b nodes p1
      if s1 + s2 + 1 > cx.cap then throw "the expanded term exceeds the size cap"
      return (.lam d t' b', s1 + s2 + 1, p2)
    | .all t b =>
      let some d := nodes[pos]? | throw "binder data: a block is shorter than its expression"
      if let .share _ := d then throw "binder data: a share node at a binder"
      let (t', s1, p1) ← expand cx fuel t nodes (pos + 1)
      let (b', s2, p2) ← expand cx fuel b nodes p1
      if s1 + s2 + 1 > cx.cap then throw "the expanded term exceeds the size cap"
      return (.all d t' b', s1 + s2 + 1, p2)
    | .letE nd m t v b =>
      let (t', s1, p1) ← expand cx fuel t nodes pos
      let (v', s2, p2) ← expand cx fuel v nodes p1
      let (b', s3, p3) ← expand cx fuel b nodes p2
      if s1 + s2 + s3 + 1 > cx.cap then throw "the expanded term exceeds the size cap"
      return (.letE nd m t' v' b', s1 + s2 + s3 + 1, p3)
    | .share n =>
      let i := n.toNat
      let some entry := cx.sharing[i]? | throw "a share names no entry"
      if cx.full[i]?.getD false then
        let some (.share v) := nodes[pos]? | throw "binder data: no share node at a share"
        let key := (i, v.toNat)
        match (← get)[key]? with
        | some (ae, s) => return (ae, s, pos + 1)
        | none =>
          let some sub := cx.blocks[(true, i, v.toNat)]? | throw "binder data: a variant is missing"
          let (ae, s, p) ← expand cx fuel entry sub 0
          unless p == sub.size do throw "binder data: a variant has unused nodes"
          modify (·.insert key (ae, s))
          return (ae, s, pos + 1)
      else
        let key := (i, 0)
        match (← get)[key]? with
        | some (ae, s) => return (ae, s, pos)
        | none =>
          let (ae, s, _) ← expand cx fuel entry #[] 0
          modify (·.insert key (ae, s))
          return (ae, s, pos)

def expandRoot (cx : ExpandCx) (root : Nat) (e : Ixon.Expr) : ExpandM AE := do
  let nodes := cx.blocks.getD (false, root, 0) #[]
  let (ae, _, p) ← expand cx (1 <<< 20) e nodes 0
  unless p == nodes.size do throw "binder data: a root block has unused nodes"
  return ae

/-- A standalone recursor record, expanded. `r` keeps the counts and flags. -/
structure XRec where
  r : Ixon.Recursor
  refs : Array Address
  univs : Array Ixon.Univ
  typ : AE
  rules : Array (UInt64 × AE)
  deriving Inhabited

def XRec.ofConstant (c : Ixon.Constant) (r : Ixon.Recursor) (cap : Nat) : Except String XRec := do
  let cx : ExpandCx := {
    sharing := c.sharing, full := binderful c.sharing, cap,
    blocks := c.binders.foldl
      (fun m b => m.insert (b.shared, b.index.toNat, b.variant.toNat) b.nodes) {} }
  let act : ExpandM XRec := do
    let typ ← expandRoot cx 0 r.typ
    let mut rules : Array (UInt64 × AE) := #[]
    for (rl, i) in r.rules.zipIdx do
      rules := rules.push (rl.fields, ← expandRoot cx (i + 1) rl.rhs)
    return { r, refs := c.refs, univs := c.univs, typ, rules }
  (·.1) <$> act.run {}

/-- The record of an expanded recursor: no sharing, one block of data per root with a
binder (the type is root 0, rule `i` root `i + 1`). -/
def XRec.toConstant (x : XRec) : Ixon.Constant :=
  let roots := #[x.typ] ++ x.rules.map (·.2)
  let binders : Array Ixon.BinderBlock := roots.zipIdx.filterMap fun (ae, k) =>
    let ns := ae.nodes #[]
    if ns.isEmpty then none
    else some { shared := false, index := k.toUInt64, variant := 0, nodes := ns }
  { info := .recr { x.r with
      typ := x.typ.toExpr,
      rules := x.rules.map fun (f, ae) => { fields := f, rhs := ae.toExpr } },
    sharing := #[], refs := x.refs, univs := x.univs, binders }

/-! ## Single edits -/

def nextRand (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- `x` with a level that differs from level `old` in every model (its successor), and
that level's index. -/
def XRec.freshLevel (x : XRec) (old : UInt64) : XRec × UInt64 :=
  let u := x.univs[old.toNat]?.getD .zero
  ({ x with univs := x.univs.push (.succ u) }, x.univs.size.toUInt64)

def swapAt {α : Type} [Inhabited α] (xs : Array α) (i j : Nat) : Array α :=
  if i < xs.size && j < xs.size then (xs.set! i xs[j]!).set! j xs[i]! else xs

def dropAt {α : Type} (xs : Array α) (i : Nat) : Array α :=
  xs.extract 0 i ++ xs.extract (i + 1) xs.size

def dupAt {α : Type} [Inhabited α] (xs : Array α) (i : Nat) : Array α :=
  if i < xs.size then xs.extract 0 (i + 1) ++ #[xs[i]!] ++ xs.extract (i + 1) xs.size else xs

/-- Edits of one term that need no knowledge of its shape. Each result is the edited term,
with the record when the edit adds a level. -/
def genericEdits (x : XRec) (e : AE) (seed : UInt64) : Array (String × XRec × AE) := Id.run do
  let mut out : Array (String × XRec × AE) := #[]
  let mut rng := nextRand (seed ^^^ 0x9E3779B97F4A7C15)
  let vars := AE.sites AE.isVar e #[]
  -- one index lowered by one, one raised by one
  if !vars.isEmpty then
    let positive := (Array.range vars.size).filter fun k => match vars[k]! with
      | .var i => i > 0
      | _ => false
    if !positive.isEmpty then
      rng := nextRand rng
      let k := positive[rng.toNat % positive.size]!
      out := out.push ("var-1", x, AE.mapNth AE.isVar (fun
        | .var i => .var (i - 1)
        | t => t) k e)
    rng := nextRand rng
    let k := rng.toNat % vars.size
    out := out.push ("var+1", x, AE.mapNth AE.isVar (fun
      | .var i => .var (i + 1)
      | t => t) k e)
    -- two occurrences with different indices exchanged
    let mut found : Option (Nat × Nat) := none
    for _ in [0:24] do
      if found.isSome then break
      rng := nextRand rng
      let a := rng.toNat % vars.size
      rng := nextRand rng
      let b := rng.toNat % vars.size
      if !(vars[a]! == vars[b]!) then found := some (a, b)
    if let some (a, b) := found then
      let va := vars[a]!
      let vb := vars[b]!
      let e1 := AE.mapNth AE.isVar (fun _ => vb) a e
      out := out.push ("vars-exchanged", x, AE.mapNth AE.isVar (fun _ => va) b e1)
  -- one level replaced by its successor
  let levels := AE.sites AE.isLevelSite e #[]
  if !levels.isEmpty then
    rng := nextRand rng
    let k := rng.toNat % levels.size
    rng := nextRand rng
    let pick := rng.toNat
    let old : UInt64 := match levels[k]! with
      | .sort u => u
      | .ref _ us => us[pick % us.size]!
      | .recur _ us => us[pick % us.size]!
      | _ => 0
    let (x', fresh) := x.freshLevel old
    out := out.push ("level", x', AE.mapNth AE.isLevelSite (fun
      | .sort _ => .sort fresh
      | .ref i us => .ref i (us.set! (pick % us.size) fresh)
      | .recur i us => .recur i (us.set! (pick % us.size) fresh)
      | t => t) k e)
  -- one reference replaced by another constant of the table
  let refs := AE.sites AE.isRef e #[]
  if !refs.isEmpty && x.refs.size ≥ 2 then
    rng := nextRand rng
    let k := rng.toNat % refs.size
    rng := nextRand rng
    let step := 1 + rng.toNat % (x.refs.size - 1)
    if let .ref i _ := refs[k]! then
      let i' := (i.toNat + step) % x.refs.size
      unless x.refs[i']! == x.refs[i.toNat]?.getD default do
        out := out.push ("constant", x, AE.mapNth AE.isRef (fun
          | .ref _ us => .ref i'.toUInt64 us
          | t => t) k e)
  -- one binder's datum changed
  let nb := AE.binderCount e
  if nb > 0 then
    rng := nextRand rng
    out := out.push ("datum", x, AE.flipNthDatum (rng.toNat % nb) e)
  return out

/-- The edits of rule `j`, read as `λ p⃗ motive minor⃗ f⃗, minor_j f⃗ ih⃗`. -/
def ruleEdits (x : XRec) (j : Nat) (seed : UInt64) : Array (String × XRec) := Id.run do
  let np := x.r.params.toNat
  let n := x.r.minors.toNat
  let ni := x.r.indices.toNat
  let some (nfU, rhs) := x.rules[j]? | return #[]
  let nf := nfU.toNat
  let mut out : Array (String × XRec) := #[]
  let mut rng := nextRand (seed ^^^ (j.toUInt64 * 0x100000001B3 + 7))
  let setRule (x' : XRec) (rhs' : AE) : XRec := { x' with rules := x'.rules.set! j (nfU, rhs') }
  -- anywhere in the rule
  for (name, x', rhs') in genericEdits x rhs rng do
    out := out.push (s!"rule:any:{name}", setRule x' rhs')
  let some (bs, body) := rhs.peelLams (np + 1 + n + nf) | return out
  let withBody (x' : XRec) (body' : AE) : XRec := setRule x' (AE.mkLams bs body')
  -- anywhere in the rule's body
  rng := nextRand rng
  for (name, x', body') in genericEdits x body rng do
    out := out.push (s!"rule:body:{name}", withBody x' body')
  let (h, args) := body.spine
  unless args.size ≥ nf do return out
  let nih := args.size - nf
  -- the minor premise applied
  if n ≥ 2 then
    out := out.push ("rule:minor-of-next-constructor",
      withBody x (AE.mkApp (.var (nf + n - 1 - ((j + 1) % n)).toUInt64) args))
  out := out.push ("rule:motive-for-minor", withBody x (AE.mkApp (.var (nf + n).toUInt64) args))
  -- the field arguments
  if nf ≥ 2 then
    rng := nextRand rng
    let i := rng.toNat % (nf - 1)
    out := out.push ("rule:fields-exchanged", withBody x (AE.mkApp h (swapAt args i (i + 1))))
  if nf ≥ 1 then
    rng := nextRand rng
    let i := rng.toNat % nf
    out := out.push ("rule:field-dropped", withBody x (AE.mkApp h (dropAt args i)))
    out := out.push ("rule:field-copied", withBody x (AE.mkApp h (dupAt args i)))
  -- the inductive hypotheses
  if nih ≥ 1 then
    rng := nextRand rng
    let t := rng.toNat % nih
    out := out.push ("rule:ih-dropped", withBody x (AE.mkApp h (dropAt args (nf + t))))
    out := out.push ("rule:ih-copied", withBody x (AE.mkApp h (args.push args[nf + t]!)))
    out := out.push ("rule:ih-replaced-by-field", withBody x
      (AE.mkApp h (args.set! (nf + t) (.var 0))))
    if nih ≥ 2 then
      let t := rng.toNat % (nih - 1)
      unless args[nf + t]! == args[nf + t + 1]! do
        out := out.push ("rule:ihs-exchanged",
          withBody x (AE.mkApp h (swapAt args (nf + t) (nf + t + 1))))
    -- inside one inductive hypothesis: `λ a⃗, rec p⃗ motive minor⃗ e⃗ (f a⃗)`
    let (tele, core) := args[nf + t]!.peelAllLams
    let m := tele.size
    let (rh, rargs) := core.spine
    let withIh (x' : XRec) (ih' : AE) : XRec := withBody x' (AE.mkApp h (args.set! (nf + t) ih'))
    let withCall (rargs' : Array AE) : XRec := withIh x (AE.mkLams tele (AE.mkApp rh rargs'))
    if rargs.size == np + 1 + n + ni + 1 then
      if n ≥ 1 then
        out := out.push ("ih:motive-and-minor-exchanged", withCall (swapAt rargs np (np + 1)))
      out := out.push ("ih:motive-dropped", withCall (dropAt rargs np))
      if n ≥ 2 then
        out := out.push ("ih:minors-exchanged", withCall (swapAt rargs (np + 1) (np + 2)))
      if n ≥ 1 then
        out := out.push ("ih:minor-dropped", withCall (dropAt rargs (np + 1)))
      if np ≥ 2 then
        out := out.push ("ih:params-exchanged", withCall (swapAt rargs 0 1))
      if np ≥ 1 then
        out := out.push ("ih:param-dropped", withCall (dropAt rargs 0))
      if ni ≥ 2 then
        unless rargs[np + 1 + n]! == rargs[np + 1 + n + 1]! do
          out := out.push ("ih:indices-exchanged",
            withCall (swapAt rargs (np + 1 + n) (np + 1 + n + 1)))
      if ni ≥ 1 then
        out := out.push ("ih:index-dropped", withCall (dropAt rargs (np + 1 + n)))
        rng := nextRand rng
        let q := np + 1 + n + rng.toNat % ni
        for (name, x', a') in genericEdits x rargs[q]! rng do
          if name == "var-1" || name == "var+1" then
            out := out.push (s!"ih:index:{name}",
              withIh x' (AE.mkLams tele (AE.mkApp rh (rargs.set! q a'))))
      out := out.push ("ih:field-dropped", withCall rargs.pop)
      let (fh, fargs) := rargs.back!.spine
      if let .var fv := fh then
        if nf ≥ 2 && fv.toNat ≥ m then
          let fv' := m + (fv.toNat - m + 1) % nf
          out := out.push ("ih:other-field",
            withCall (rargs.set! (rargs.size - 1) (AE.mkApp (.var fv'.toUInt64) fargs)))
        if m ≥ 1 then
          out := out.push ("ih:field-argument-dropped",
            withCall (rargs.set! (rargs.size - 1) (AE.mkApp fh fargs.pop)))
        if m ≥ 2 then
          out := out.push ("ih:field-arguments-exchanged",
            withCall (rargs.set! (rargs.size - 1) (AE.mkApp fh (swapAt fargs 0 1))))
      if let .recur ri us := rh then
        if !us.isEmpty then
          let (x', fresh) := x.freshLevel us[0]!
          out := out.push ("ih:level",
            withIh x' (AE.mkLams tele (AE.mkApp (.recur ri (us.set! 0 fresh)) rargs)))
      if m ≥ 1 then
        let (d0, t0) := tele[0]!
        out := out.push ("ih:telescope-datum",
          withIh x (AE.mkLams (tele.set! 0 (AE.flipDatum d0, t0)) core))
        if let some core' := (AE.mkLams (tele.extract 1 tele.size) core).lower 0 then
          out := out.push ("ih:telescope-binder-dropped", withIh x core')
        rng := nextRand rng
        for (name, x', t') in genericEdits x t0 rng do
          if name == "var-1" || name == "var+1" || name == "constant" then
            out := out.push (s!"ih:telescope-domain:{name}",
              withIh x' (AE.mkLams (tele.set! 0 (d0, t')) core))
  -- the rule's binders
  let fieldAt (i : Nat) : Nat := np + 1 + n + i
  if nf ≥ 2 then
    rng := nextRand rng
    let i := rng.toNat % (nf - 1)
    let (d1, t1) := bs[fieldAt i]!
    let (d2, t2) := bs[fieldAt (i + 1)]!
    unless d1 == d2 && t1 == t2 do
      out := out.push ("rule:field-binders-exchanged",
        setRule x (AE.mkLams (swapAt bs (fieldAt i) (fieldAt (i + 1))) body))
  if nf ≥ 1 then
    rng := nextRand rng
    let i := rng.toNat % nf
    let (d, t) := bs[fieldAt i]!
    out := out.push ("rule:field-binder-datum",
      setRule x (AE.mkLams (bs.set! (fieldAt i) (AE.flipDatum d, t)) body))
    for (name, x', t') in genericEdits x t rng do
      out := out.push (s!"rule:field-domain:{name}",
        setRule x' (AE.mkLams (bs.set! (fieldAt i) (d, t')) body))
  if let some (d, t) := bs[np]? then
    out := out.push ("rule:motive-binder-datum",
      setRule x (AE.mkLams (bs.set! np (AE.flipDatum d, t)) body))
    rng := nextRand rng
    for (name, x', t') in genericEdits x t rng do
      out := out.push (s!"rule:motive-domain:{name}",
        setRule x' (AE.mkLams (bs.set! np (d, t')) body))
  if n ≥ 1 then
    rng := nextRand rng
    let q := np + 1 + rng.toNat % n
    let (d, t) := bs[q]!
    for (name, x', t') in genericEdits x t rng do
      out := out.push (s!"rule:minor-domain:{name}",
        setRule x' (AE.mkLams (bs.set! q (d, t')) body))
  if np ≥ 1 then
    rng := nextRand rng
    let q := rng.toNat % np
    let (d, t) := bs[q]!
    for (name, x', t') in genericEdits x t rng do
      out := out.push (s!"rule:param-domain:{name}",
        setRule x' (AE.mkLams (bs.set! q (d, t')) body))
  return out

/-- The edits of the type, read as `∀ p⃗ motive minor⃗ ı⃗ major, motive ı⃗ major`. -/
def typeEdits (x : XRec) (seed : UInt64) : Array (String × XRec) := Id.run do
  let np := x.r.params.toNat
  let n := x.r.minors.toNat
  let ni := x.r.indices.toNat
  let mut out : Array (String × XRec) := #[]
  let mut rng := nextRand (seed ^^^ 0xD1B54A32D192ED03)
  for (name, x', t') in genericEdits x x.typ rng do
    out := out.push (s!"type:any:{name}", { x' with typ := t' })
  let some (bs, concl) := x.typ.peelAlls (np + 1 + n + ni + 1) | return out
  let rebuilt (bs' : Array AE.Binder) (concl' : AE) : XRec := { x with typ := AE.mkAlls bs' concl' }
  -- two minor premises exchanged, each moved to the other's place
  if n ≥ 2 then
    rng := nextRand rng
    let q := np + 1 + rng.toNat % (n - 1)
    let (d1, a) := bs[q]!
    let (d2, b) := bs[q + 1]!
    if let some b' := b.lower 0 then
      out := out.push ("type:minors-exchanged",
        rebuilt ((bs.set! q (d2, b')).set! (q + 1) (d1, a.lift 1 0)) concl)
  -- one inductive hypothesis of a minor premise removed
  for q in [0:n] do
    let some (nfU, _) := x.rules[q]? | continue
    let (d, mty) := bs[np + 1 + q]!
    if let some (fbs, rest) := mty.peelAlls nfU.toNat then
      if let .all _ _ after := rest then
        if let some after' := after.lower 0 then
          out := out.push ("type:ih-binder-dropped",
            rebuilt (bs.set! (np + 1 + q) (d, AE.mkAlls fbs after')) concl)
          break
  -- the motive's sort
  let (dm, mot) := bs[np]!
  let (mbs, msort) := mot.peelAllAlls
  if let .sort u := msort then
    let (x', fresh) := x.freshLevel u
    out := out.push ("type:motive-sort",
      { x' with typ := AE.mkAlls (bs.set! np (dm, AE.mkAlls mbs (.sort fresh))) concl })
  -- the conclusion and the major premise
  rng := nextRand rng
  for (name, x', c') in genericEdits x concl rng do
    out := out.push (s!"type:conclusion:{name}", { x' with typ := AE.mkAlls bs c' })
  let (ch, cargs) := concl.spine
  if cargs.size ≥ 2 then
    out := out.push ("type:conclusion-arguments-exchanged",
      rebuilt bs (AE.mkApp ch (swapAt cargs (cargs.size - 2) (cargs.size - 1))))
  if cargs.size ≥ 1 then
    out := out.push ("type:conclusion-argument-dropped", rebuilt bs (AE.mkApp ch cargs.pop))
    out := out.push ("type:conclusion-first-argument-dropped",
      rebuilt bs (AE.mkApp ch (dropAt cargs 0)))
  let (dM, major) := bs[bs.size - 1]!
  rng := nextRand rng
  for (name, x', t') in genericEdits x major rng do
    out := out.push (s!"type:major:{name}",
      { x' with typ := AE.mkAlls (bs.set! (bs.size - 1) (dM, t')) concl })
  -- one minor premise
  if n ≥ 1 then
    rng := nextRand rng
    let q := np + 1 + rng.toNat % n
    let (d, t) := bs[q]!
    for (name, x', t') in genericEdits x t rng do
      out := out.push (s!"type:minor:{name}", { x' with typ := AE.mkAlls (bs.set! q (d, t')) concl })
    -- the constructor of this minor's conclusion replaced by the next minor's
    if n ≥ 2 then
      let q2 := np + 1 + ((q - (np + 1)) + 1) % n
      let ctorOf (mty : AE) : Option AE :=
        let (_, c) := mty.peelAllAlls
        let (_, cargs) := c.spine
        cargs.back?.map fun last => last.spine.1
      if let (some (.ref c1 _), some (.ref c2 us2)) := (ctorOf t, ctorOf bs[q2]!.2) then
        if c1 != c2 then
          let (tbs, c) := t.peelAllAlls
          let (mh, margs) := c.spine
          let (_, cas) := margs.back!.spine
          out := out.push ("type:minor-constructor",
            rebuilt (bs.set! q (d, AE.mkAlls tbs
              (AE.mkApp mh (margs.set! (margs.size - 1) (AE.mkApp (.ref c2 us2) cas))))) concl)
  return out

/-- The edits of the record's counts, flags and rule list. -/
def countEdits (x : XRec) (seed : UInt64) : Array (String × XRec) := Id.run do
  let r := x.r
  let n := x.rules.size
  let mut out : Array (String × XRec) := #[]
  let rng := nextRand (seed ^^^ 0xA24BAED4963EE407)
  out := out.push ("count:params+1", { x with r := { r with params := r.params + 1 } })
  if r.params > 0 then
    out := out.push ("count:params-1", { x with r := { r with params := r.params - 1 } })
  out := out.push ("count:indices+1", { x with r := { r with indices := r.indices + 1 } })
  if r.indices > 0 then
    out := out.push ("count:indices-1", { x with r := { r with indices := r.indices - 1 } })
  out := out.push ("count:motives+1", { x with r := { r with motives := r.motives + 1 } })
  out := out.push ("count:motive-as-minor",
    { x with r := { r with motives := r.motives - 1, minors := r.minors + 1 } })
  if r.minors > 0 then
    out := out.push ("count:minor-as-motive",
      { x with r := { r with motives := r.motives + 1, minors := r.minors - 1 } })
    out := out.push ("count:minors-1", { x with r := { r with minors := r.minors - 1 } })
  out := out.push ("count:minors+1", { x with r := { r with minors := r.minors + 1 } })
  if r.params > 0 then
    out := out.push ("count:param-as-index",
      { x with r := { r with params := r.params - 1, indices := r.indices + 1 } })
  if r.indices > 0 then
    out := out.push ("count:index-as-param",
      { x with r := { r with params := r.params + 1, indices := r.indices - 1 } })
  out := out.push ("count:levels+1", { x with r := { r with lvls := r.lvls + 1 } })
  if r.lvls > 0 then
    out := out.push ("count:levels-1", { x with r := { r with lvls := r.lvls - 1 } })
  out := out.push ("flag:k", { x with r := { r with k := !r.k } })
  out := out.push ("flag:unsafe", { x with r := { r with isUnsafe := !r.isUnsafe } })
  if n ≥ 1 then
    let j := rng.toNat % n
    let (f, rhs) := x.rules[j]!
    out := out.push ("rule:field-count+1", { x with rules := x.rules.set! j (f + 1, rhs) })
    if f > 0 then
      out := out.push ("rule:field-count-1", { x with rules := x.rules.set! j (f - 1, rhs) })
    out := out.push ("rules:last-dropped", { x with rules := x.rules.pop })
    out := out.push ("rules:last-copied", { x with rules := x.rules.push x.rules.back! })
  if n ≥ 2 then
    let j := rng.toNat % (n - 1)
    out := out.push ("rules:exchanged", { x with rules := swapAt x.rules j (j + 1) })
    let (f1, r1) := x.rules[j]!
    let (f2, r2) := x.rules[j + 1]!
    if f1 != f2 then
      out := out.push ("rules:bodies-exchanged",
        { x with rules := (x.rules.set! j (f1, r2)).set! (j + 1) (f2, r1) })
  return out

/-- Every edit of `x`: the counts, the type, and up to `maxRules` rules. -/
def mutantsOf (x : XRec) (seed : UInt64) (maxRules : Nat := 3) : Array (String × XRec) := Id.run do
  let mut out := countEdits x seed ++ typeEdits x seed
  let n := x.rules.size
  if n > 0 then
    -- the rules with the most fields first, so those with inductive hypotheses are edited
    let order := (Array.range n).qsort fun a b => x.rules[a]!.1 > x.rules[b]!.1
    for j in order.extract 0 maxRules do
      out := out ++ ruleEdits x j seed
  return out

/-- Whether two expanded records have the same counts and flags and, with every `let`
expanded, the same type and rules: they then denote the same recursor. -/
def XRec.zetaEq (x y : XRec) : Bool :=
  x.r.k == y.r.k && x.r.isUnsafe == y.r.isUnsafe && x.r.lvls == y.r.lvls &&
  x.r.params == y.r.params && x.r.indices == y.r.indices && x.r.motives == y.r.motives &&
  x.r.minors == y.r.minors && x.refs == y.refs &&
  x.univs == y.univs.extract 0 x.univs.size &&
  x.typ.zeta == y.typ.zeta && x.rules.size == y.rules.size &&
  (x.rules.zip y.rules).all fun ((f1, r1), (f2, r2)) => f1 == f2 && r1.zeta == r2.zeta

end Tests.Ix.IxVM.RecGen
