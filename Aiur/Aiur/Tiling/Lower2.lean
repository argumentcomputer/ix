import Aiur.Tiling.Lower
import Aiur.Tiling.PeriodicMerge
import Aiur.Tiling.PeriodicTemplate
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# v2 template lowering (unverified)

The algorithm of the prototype's v2 lowering (`crates/proof-compression/src/
aiur_backend/template/v2.rs`, `lower`), producing a `Template2`:

* nodes become linear forms over atoms (columns of a body, and products of two
  interned normalized linear forms, so `(a·g + b)(c·h + d)` is one product of
  `g`, `h`);
* identical unchunked lookups other than the receive merge by adding
  multiplicities, and lookups of zero multiplicity are dropped
  (`Circuit.mergeBy`);
* a product used once linearly and never as a cell is fused into its relation;
* a relation is a span of lanes with at most one product, in its first lane;
  longer relations chain full-row spans through carry slots;
* spans and lane messages (payloads of at most three values) are placed
  first-fit into gate rows; larger payloads take a row, or keyed chunk rows.

A multiplicity `mk + mc·x` with `mk ≠ 0`, or a constant one, gets a virtual
slot (`Template2.virtual`) defined as `mk + mc·x` (or `mk`); a chunked
receive's key is an invocation slot. Both are appended after the
prototype's slots, so slot numbers agree with the prototype's.

Nothing here is trusted: `tile2` returns a sharded system only after
`Sharded.check` accepts it.
-/

namespace Aiur.Tiling.Periodic

open Std

deriving instance Hashable for Atom

variable {F : Type}

structure Form2 (F : Type) where
  terms : List (Atom × F)
  k : F
  deriving BEq, Hashable

instance [Zero F] : Inhabited (Form2 F) := ⟨⟨[], 0⟩⟩

namespace Form2

variable [Field F] [DecidableEq F]

def const (k : F) : Form2 F := ⟨[], k⟩

def atom (a : Atom) (c : F) : Form2 F := ⟨[(a, c)], 0⟩

/-- `xs + s·ys` over sorted atoms, dropping zero coefficients of the sum. -/
def mergeLin (s : F) : List (Atom × F) → List (Atom × F) → List (Atom × F)
  | xs, [] => xs
  | [], (b, d) :: ys => if d * s = 0 then mergeLin s [] ys else (b, d * s) :: mergeLin s [] ys
  | (a, c) :: xs, (b, d) :: ys =>
      if a == b then
        if c + d * s = 0 then mergeLin s xs ys else (a, c + d * s) :: mergeLin s xs ys
      else if Atom.lt a b then (a, c) :: mergeLin s xs ((b, d) :: ys)
      else if d * s = 0 then mergeLin s ((a, c) :: xs) ys
      else (b, d * s) :: mergeLin s ((a, c) :: xs) ys
termination_by xs ys => xs.length + ys.length

def combine (x y : Form2 F) (s : F) : Form2 F := ⟨mergeLin s x.terms y.terms, x.k + y.k * s⟩

def scale (x : Form2 F) (c : F) : Form2 F :=
  if c = 0 then const 0 else ⟨x.terms.map fun (a, v) => (a, v * c), x.k * c⟩

def isZero (x : Form2 F) : Bool := x.terms.isEmpty && decide (x.k = 0)

end Form2

structure GateBuild (F : Type) where
  lanes : Array (LaneUse F) := #[]
  spans : Array Span := #[]

instance : Inhabited (GateBuild F) := ⟨{}⟩

/-- A message row before slot numbering is final: its lookup, `(tag, sub)`,
its key (`none`: unkeyed; `some none`: the invocation slot) and payload. -/
structure PendingRow (F : Type) where
  lookup : Nat
  tag : F
  sub : F
  key : Option (Option Nat)
  payload : List Nat

/-- A lookup's multiplicity `mk + mc·mult`. -/
structure PendingMult (F : Type) where
  offset : F
  coef : F
  mult : Option Nat

instance [Zero F] : Inhabited (PendingMult F) := ⟨⟨0, 0, none⟩⟩

structure Lowerer2 (F : Type) [BEq F] [Hashable F] where
  width : Nat
  lanes : Nat
  lins : Array (List (Atom × F)) := #[]
  linIds : HashMap (List (Atom × F)) Nat := {}
  prods : Array (Nat × Nat) := #[]
  prodIds : HashMap (Nat × Nat) Nat := {}
  usesLin : HashMap Atom Nat := {}
  usesCell : HashMap Atom Nat := {}
  done : HashSet Nat := {}
  needLin : HashSet Nat := {}
  needExact : HashSet (Form2 F) := {}
  inline : HashSet Nat := {}
  slots : Array (SlotDef F) := #[]
  cellMemo : HashMap Atom Nat := {}
  linMemo : HashMap Nat Nat := {}
  exactMemo : HashMap (Form2 F) Nat := {}
  gates : Array (GateBuild F) := #[]
  openRows : Array Nat := #[]
  msgRows : Array (Row2 F) := #[]
  rows : Array (PendingRow F) := #[]
  mults : Array (PendingMult F) := #[]

abbrev M2 (F : Type) [BEq F] [Hashable F] := StateT (Lowerer2 F) (Except String)

/-- A lookup after forms are computed: its index in the body, its index in
the unrolled circuit, and its forms. -/
structure Demand (F : Type) where
  lookup : Nat
  origs : List Nat
  args : List (Form2 F)
  mult : Form2 F

namespace Lowerer2

variable [Field F] [DecidableEq F] [Hashable F]

def newSlot (d : SlotDef F) : M2 F Nat :=
  modifyGet fun st => (st.slots.size, { st with slots := st.slots.push d })

def intern (lin : List (Atom × F)) : M2 F Nat := do
  let st ← get
  if let some id := st.linIds[lin]? then return id
  set { st with lins := st.lins.push lin, linIds := st.linIds.insert lin st.lins.size }
  return st.lins.size

/-- `(α, β, g)` with `form = α·g + β` and `g`'s first coefficient 1. -/
def norm (f : Form2 F) : M2 F (F × F × Nat) := do
  match f.terms with
  | (_, al) :: _ =>
      let ia := al⁻¹
      let g ← intern (f.terms.map fun (a, c) => (a, c * ia))
      return (al, f.k, g)
  | [] => throw "normalizing a constant"

def linForm (id : Nat) : M2 F (Form2 F) := do return ⟨(← get).lins[id]!, 0⟩

def mul (a b : Form2 F) : M2 F (Form2 F) := do
  if a.terms.isEmpty then return b.scale a.k
  if b.terms.isEmpty then return a.scale b.k
  let (al, be, ga) ← norm a
  let (gm, de, gb) ← norm b
  let key := (min ga gb, max ga gb)
  let st ← get
  let p ← match st.prodIds[key]? with
    | some p => pure p
    | none => do
        set { st with prods := st.prods.push key, prodIds := st.prodIds.insert key st.prods.size }
        pure st.prods.size
  let f := (Form2.atom (.product p) (al * gm)).combine (← linForm ga) (al * de)
  let f := f.combine (← linForm gb) (be * gm)
  return { f with k := f.k + be * de }

def forms (g : Graph F) (b : Body F) (bi : Nat) (prev : Option (Array (Form2 F))) :
    M2 F (Array (Form2 F)) := do
  let mut out : Array (Form2 F) := #[]
  for node in g.nodes do
    let f ← match node with
      | .const k => pure (Form2.const k)
      | .var c =>
          match b.subst.lookup c with
          | some k => pure (Form2.const k)
          | none =>
              match b.aliases.lookup c with
              | some (l, a) =>
                  match prev, g.lookups[l]? with
                  | some pv, some (_, args) =>
                      match args[a]? with
                      | some n => pure pv[n]!
                      | none => throw "alias argument out of range"
                  | _, _ => throw "alias without a previous body"
              | none => pure (Form2.atom (.column (bi * g.width + c)) 1)
      | .add x y => pure (out[x]!.combine out[y]! 1)
      | .sub x y => pure (out[x]!.combine out[y]! (-1))
      | .neg x => pure (out[x]!.scale (-1))
      | .mul x y => mul out[x]! out[y]!
    out := out.push f
  return out

mutual

partial def useAtom (a : Atom) (cell : Bool) : M2 F Unit := do
  modify fun st =>
    if cell then { st with usesCell := st.usesCell.insert a (st.usesCell.getD a 0 + 1) }
    else { st with usesLin := st.usesLin.insert a (st.usesLin.getD a 0 + 1) }
  if let .product p := a then
    let st ← get
    if !st.done.contains p then
      set { st with done := st.done.insert p }
      let (x, y) := st.prods[p]!
      operandDemand x
      operandDemand y

partial def operandDemand (lid : Nat) : M2 F Unit := do
  let st ← get
  match st.lins[lid]! with
  | [(a, _)] => useAtom a true
  | g =>
      if !st.needLin.contains lid then
        set { st with needLin := st.needLin.insert lid }
        for (a, _) in g do useAtom a false

end

def exactDemand (f : Form2 F) : M2 F Unit := do
  match f.terms with
  | [] => pure ()
  | [(a, c)] =>
      if c = 1 ∧ f.k = 0 then useAtom a true
      else demandAll
  | _ => demandAll
where
  demandAll : M2 F Unit := do
    let st ← get
    if !st.needExact.contains f then
      set { st with needExact := st.needExact.insert f }
      for (a, _) in f.terms do useAtom a false

/-- First-fit placement of a span (`role` given) or a lane message into gate rows. -/
def place (lanes : List (LaneUse F)) (role : Option Role) : M2 F Unit := do
  let st ← get
  let n := lanes.length
  let found := st.openRows.find? fun r => st.lanes - st.gates[r]!.lanes.size ≥ n
  let r ← match found with
    | some r => pure r
    | none => do
        set { st with gates := st.gates.push {}, openRows := st.openRows.push st.gates.size }
        pure st.gates.size
  modify fun st =>
    let row := st.gates[r]!
    let start := row.lanes.size
    let row : GateBuild F := {
      lanes := row.lanes ++ lanes.toArray
      spans := match role with
        | some ro => row.spans.push ⟨start, n, ro⟩
        | none => row.spans }
    let st := { st with gates := st.gates.set! r row }
    if row.lanes.size == st.lanes then { st with openRows := st.openRows.filter (· != r) } else st

def span (items : List (Item F)) (k : F) (n : Nat) (role : Role) : M2 F Unit := do
  let mut lanes : Array (Lane F) := Array.replicate n Lane.zero
  let mut product := false
  for item in items do
    if let .product c a b ca cb := item then
      lanes := lanes.set! 0 { (Lane.zero : Lane F) with qm := c, q0 := ca, q1 := cb, c0 := some a, c1 := some b }
      product := true
  let mut free : Array (Nat × Nat) := #[]
  for l in [0:n] do
    for c in [(if l == 0 && product then 2 else 0):4] do
      free := free.push (l, c)
  let mut pos := 0
  for item in items do
    if let .linear c s := item then
      let (l, cell) := free[pos]!
      pos := pos + 1
      lanes := lanes.modify l fun lane =>
        match cell with
        | 0 => { lane with c0 := some s, q0 := c }
        | 1 => { lane with c1 := some s, q1 := c }
        | 2 => { lane with c2 := some s, q2 := c }
        | _ => { lane with c3 := some s, q3 := c }
  lanes := lanes.modify 0 fun lane => { lane with qc := k }
  place (lanes.toList.map LaneUse.gate) (some role)

/-- Emit `Σ items + k = 0` as one span, or as full-row spans chained by carry
slots; every span holds at most one product, in its first lane. -/
def relation (items : List (Item F)) (k : F) (role : Role) : M2 F Unit := do
  let items := normalizeItems items
  if items.isEmpty then
    if k = 0 then return else throw "unsatisfiable relation"
  let L := (← get).lanes
  let cap := 4 * L
  let mut rest := items
  let mut k := k
  let mut carry : Option Nat := none
  for _ in [0:items.length + 2] do
    let reserved := if carry.isSome then 1 else 0
    let prods := (rest.filter (·.cells == 2)).length
    let cells := (rest.map Item.cells).sum + reserved
    if prods ≤ 1 && cells ≤ cap then
      let piece := rest ++ (match carry with | some c => [.linear 1 c] | none => [])
      span piece k (max 1 ((cells + 3) / 4)) role
      return
    let mut room := cap - 1 - reserved
    let mut piece : Array (Item F) := #[]
    let mut keep : Array (Item F) := #[]
    let mut took := false
    for item in rest do
      if item.cells ≤ room && (item.cells == 1 || !took) then
        room := room - item.cells
        if item.cells == 2 then took := true
        piece := piece.push item
      else keep := keep.push item
    rest := keep.toList
    if piece.isEmpty then throw "relation item does not fit a row"
    if let some c := carry then piece := piece.push (.linear 1 c)
    let next ← newSlot (.sum (piece.toList.flatMap Item.terms) k)
    piece := piece.push (.linear (-1) next)
    span piece.toList k L (.defines next)
    k := 0
    carry := some next
  throw "carry chain did not terminate"

mutual

partial def cell (a : Atom) : M2 F Nat := do
  if let some s := (← get).cellMemo[a]? then return s
  let s ← match a with
    | .column c => newSlot (.column c)
    | .product p => do
        if (← get).inline.contains p then throw "fused product used as a cell"
        let (x, y) := (← get).prods[p]!
        let a ← opcell x
        let b ← opcell y
        define [.product 1 a b 0 0] 0
  modify fun st => { st with cellMemo := st.cellMemo.insert a s }
  return s

partial def opcell (lid : Nat) : M2 F Nat := do
  let g := (← get).lins[lid]!
  if let [(a, _)] := g then return ← cell a
  if let some s := (← get).linMemo[lid]? then return s
  let s ← define (← items g) 0
  modify fun st => { st with linMemo := st.linMemo.insert lid s }
  return s

partial def exactCell (f : Form2 F) : M2 F Nat := do
  if let [(a, c)] := f.terms then
    if c = 1 ∧ f.k = 0 then return ← cell a
  if let some s := (← get).exactMemo[f]? then return s
  let s ← define (← items f.terms) f.k
  modify fun st => { st with exactMemo := st.exactMemo.insert f s }
  return s

partial def items (terms : List (Atom × F)) : M2 F (List (Item F)) := do
  let mut out : Array (Item F) := #[]
  for (a, c) in terms do
    match a with
    | .product p =>
        if (← get).inline.contains p then
          let (x, y) := (← get).prods[p]!
          let u ← opcell x
          let v ← opcell y
          out := out.push (.product c u v 0 0)
        else out := out.push (.linear c (← cell a))
    | .column _ => out := out.push (.linear c (← cell a))
  return out.toList

/-- A slot defined as `Σ items + k`, with its defining relation emitted. -/
partial def define (items : List (Item F)) (k : F) : M2 F Nat := do
  let out ← newSlot (.sum (items.flatMap Item.terms) k)
  relation (items ++ [.linear (-1) out]) k (.defines out)
  return out

end

def constant (f : Form2 F) : Option F := if f.terms.isEmpty then some f.k else none

def message (d : Demand F) : M2 F Unit := do
  let w := (← get).width
  let (tag, sub) ← match d.args with
    | t :: s :: _ =>
        match constant t, constant s with
        | some tag, some sub => pure (tag, sub)
        | _, _ => throw "non-constant lookup tag or id"
    | _ => throw "lookup without [tag, id] prefix"
  let receive := d.lookup == 0
  if receive && tag ≠ 1 then throw "receive is not a call"
  if tag ≠ 1 && tag ≠ 2 then throw "unknown lookup tag"
  let rom := tag = 2
  let (k0, c0, mult) ← match d.mult.terms with
    | [] => pure (d.mult.k, (0 : F), none)
    | [(a, c)] => pure (d.mult.k, c, some (← cell a))
    | _ => pure (0, 1, some (← exactCell d.mult))
  let payload ← (d.args.drop 2).mapM exactCell
  let p := payload.length
  if rom && p == 0 then throw "ROM lookup without address"
  let lk := (← get).mults.size
  let pushRow (tag sub : F) (key : Option (Option Nat)) (vals : List Nat) : M2 F Nat :=
    modifyGet fun st => (st.rows.size, { st with rows := st.rows.push ⟨lk, tag, sub, key, vals⟩ })
  if p ≤ 3 then
    let m ← pushRow tag sub none payload
    place [.message m] none
  else if p ≤ w - 1 then
    let m ← pushRow tag sub none payload
    modify fun st => { st with msgRows := st.msgRows.push (.message m false) }
  else
    let (key, values) ← if rom then pure (some (payload.head? ), payload.drop 1)
      else if receive then pure (some none, payload)
      else pure (some (some (← newSlot (.key lk))), payload)
    if !receive then
      match mult with
      | none => if k0 ≠ 0 ∧ k0 ≠ 1 then throw "chunked send with a non-boolean constant multiplicity"
      | some x => relation [.product (c0 * c0) x x (2 * k0 * c0 - c0) 0] (k0 * k0 - k0) (.boolean x)
    let per := w - 2
    let chunks := max 1 ((values.length + per - 1) / per)
    for c in [0:chunks] do
      let m ← pushRow tag (chunkSub rom sub c) key ((values.drop (c * per)).take per)
      modify fun st => { st with msgRows := st.msgRows.push (.message m receive) }
  modify fun st => { st with mults := st.mults.push ⟨k0, c0, mult⟩ }

end Lowerer2

open Lowerer2 in
/-- Lower one function (one body) or one unrolled function (several bodies of
one graph) to a v2 template. Also returns the merge groups: per logical
lookup, its lookups in the unrolled circuit. -/
def lower2 [Field F] [DecidableEq F] [Hashable F] (g : Graph F) (bodies : List (Body F)) (width : Nat) :
    Except String (Template2 F × List (List Nat)) := do
  if width < 8 || width % 4 != 0 then throw "v2 template width must be a multiple of 4, at least 8"
  let run : M2 F (List (List Nat)) := do
    let mut zeros : Array (Form2 F) := #[]
    let mut demands : Array (Demand F) := #[]
    let mut prev : Option (Array (Form2 F)) := none
    let mut orig := 0
    for (b, bi) in bodies.zipIdx do
      let fs ← forms g b bi prev
      for z in g.zeros do zeros := zeros.push fs[z]!
      for ((m, args), j) in g.lookups.zipIdx do
        if b.drop.contains j then continue
        demands := demands.push ⟨j, [orig], args.map (fs[·]!), fs[m]!⟩
        orig := orig + 1
      prev := some fs
    let mut merged : Array (Demand F) := #[]
    let mut seen : HashMap (List (Form2 F)) Nat := {}
    for d in demands do
      if d.mult.isZero then continue
      if d.lookup != 0 && d.args.length ≤ width + 1 then
        if let some at_ := seen[d.args]? then
          merged := merged.modify at_ fun e =>
            { e with mult := e.mult.combine d.mult 1, origs := e.origs ++ d.origs }
          continue
        seen := seen.insert d.args merged.size
      merged := merged.push d
    for z in zeros do
      for (a, _) in z.terms do useAtom a false
    for d in merged do
      match d.mult.terms with
      | [(a, _)] => useAtom a true
      | [] => pure ()
      | _ => exactDemand d.mult
      for a in d.args.drop 2 do exactDemand a
    let st ← get
    let inl := (List.range st.prods.size).filter fun p =>
      st.usesLin.getD (.product p) 0 == 1 && !st.usesCell.contains (.product p)
    set { st with inline := HashSet.ofList inl }
    for (z, j) in zeros.toList.zipIdx do
      if z.terms.isEmpty then
        if z.k ≠ 0 then throw "unsatisfiable constant constraint"
        continue
      relation (← items z.terms) z.k (.root j)
    for d in merged do message d
    return merged.toList.map (·.origs)
  let (groups, st) ← run.run ({ width, lanes := width / 4 } : Lowerer2 F)
  -- Invocation and virtual slots follow the prototype's slots.
  let n := st.slots.size
  let inv := if st.rows.any (·.key == some none) then some n else none
  let mut extra : Array (SlotDef F) := if inv.isSome then #[.invocation] else #[]
  let mut virt : Array (Option Nat) := #[]
  for pm in st.mults do
    if pm.offset ≠ 0 ∨ pm.mult.isNone then
      virt := virt.push (some (n + extra.size))
      extra := extra.push (.sum ((pm.mult.map fun x => [Term.linear pm.coef x]).getD []) pm.offset)
    else virt := virt.push none
  let messages : List (Message F) := st.rows.toList.map fun r =>
    let pm := st.mults[r.lookup]!
    let (sel, mult) := match virt[r.lookup]! with
      | some v => ((1 : F), v)
      | none => (pm.coef, pm.mult.getD 0)
    let cells := match r.key with
      | none => messageCells width mult r.payload
      | some key => keyedCells width mult ((key.orElse fun _ => inv).getD 0) r.payload
    (sel, r.tag, r.sub, cells)
  let gateRows : List (Row2 F) := st.gates.toList.map fun gb =>
    .gate (gb.lanes.toList ++ List.replicate (width / 4 - gb.lanes.size) .empty) gb.spans.toList
  let T : Template2 F := {
    width := width
    slots := st.slots.toList ++ extra.toList
    messages := messages
    rows := gateRows ++ st.msgRows.toList
    virtual := virt.toList.filterMap id }
  return ({ T with booleans := T.virtual.filter T.boolOk }, groups)

end Aiur.Tiling.Periodic
