import Aiur.Tiling.Shape

/-!
# Template lowering (unverified)

Lowers one wide circuit, given as a hash-consed graph, to a template. The
algorithm is the prototype's (`crates/proof-compression/src/aiur_backend/
template/lower.rs`) without keyed chunks: nodes become linear forms over
atoms (columns and products), every needed value becomes a slot, products
used once are fused into the relation that uses them, and long relations
are split into rows linked by carry slots.

Nothing here is trusted: `tile` accepts a template only after
`Template.check` validates it against `Graph.circuit`.
-/

namespace Aiur.Tiling

variable {F : Type} [CommRing F] [DecidableEq F]

inductive Atom where
  | column (c : Nat)
  | product (i : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

def Atom.lt : Atom → Atom → Bool
  | .column a, .column b => a < b
  | .column _, .product _ => true
  | .product _, .column _ => false
  | .product a, .product b => a < b

/-- `Σ c·atom + constant`, atoms strictly increasing, coefficients nonzero. -/
structure Form (F : Type) where
  terms : List (Atom × F)
  constant : F
  deriving BEq

instance [Zero F] : Inhabited (Form F) := ⟨⟨[], 0⟩⟩

namespace Form

def const (k : F) : Form F := ⟨[], k⟩
def atom (a : Atom) : Form F := ⟨[(a, 1)], 0⟩

def mergeTerms (scale : F) : List (Atom × F) → List (Atom × F) → List (Atom × F)
  | [], ys => ys.map fun (a, c) => (a, c * scale)
  | xs, [] => xs
  | (a, c) :: xs, (b, d) :: ys =>
      if a == b then
        let e := c + d * scale
        if e = 0 then mergeTerms scale xs ys else (a, e) :: mergeTerms scale xs ys
      else if Atom.lt a b then (a, c) :: mergeTerms scale xs ((b, d) :: ys)
      else (b, d * scale) :: mergeTerms scale ((a, c) :: xs) ys
termination_by xs ys => xs.length + ys.length

def combine (x y : Form F) (scale : F) : Form F :=
  ⟨mergeTerms scale x.terms y.terms, x.constant + y.constant * scale⟩

def scale (x : Form F) (k : F) : Form F :=
  if k = 0 then const 0 else ⟨x.terms.map fun (a, c) => (a, c * k), x.constant * k⟩

def asConstant (x : Form F) : Option F := if x.terms.isEmpty then some x.constant else none

end Form

inductive Item (F : Type) where
  | product (c : F) (a b : Nat) (ca cb : F)
  | linear (c : F) (s : Nat)

instance [Zero F] : Inhabited (Item F) := ⟨.linear 0 0⟩

def Item.cells : Item F → Nat
  | .product .. => 2
  | .linear .. => 1

def Item.terms : Item F → List (Term F)
  | .product c a b ca cb =>
      [Term.product c a b] ++ (if ca = 0 then [] else [.linear ca a]) ++
        (if cb = 0 then [] else [.linear cb b])
  | .linear c s => [.linear c s]

structure Builder (F : Type) where
  width : Nat
  forms : Array (Form F) := #[]
  operands : Array (Option (Form F × Form F)) := #[]
  columnUses : Array Nat := #[]
  productUses : Array Nat := #[]
  slots : Array (SlotDef F) := #[]
  columnSlots : Array (Option Nat) := #[]
  productSlots : Array (Option Nat) := #[]
  formSlots : List (Form F × Nat) := []
  rows : Array (Row F) := #[]
  pending : Array (Lane F × Role) := #[]
  invocation : Option Nat := none
  messageCount : Nat := 0

abbrev LowerM (F : Type) := StateT (Builder F) (Except String)

def zeroLane : Lane F := Lane.zero

def lanesOf (items : List (Item F)) (n : Nat) (k qid : F) : List (Lane F) := Id.run do
  let mut lanes : Array (Lane F) := Array.replicate n zeroLane
  let mut next := 0
  for item in items do
    if let .product c a b ca cb := item then
      lanes := lanes.modify next fun l => { l with qm := c, c0 := some a, c1 := some b, q0 := ca, q1 := cb }
      next := next + 1
  let mut free : Array (Nat × Nat) := #[]
  for l in [0:n] do
    let start := if l < next then 2 else 0
    for c in [start:4] do
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
  lanes := lanes.modify 0 fun lane => { lane with qc := k, qid := qid }
  return lanes.toList

/-- Merge repeated linear slots and absorb linear terms on a product's
operands into that product's lane. -/
def normalizeItems (items : List (Item F)) : List (Item F) := Id.run do
  let mut linear : List (Nat × F) := []
  let mut products : Array (Item F) := #[]
  for item in items do
    match item with
    | .linear c s =>
        linear := match linear.find? (·.1 == s) with
          | some _ => linear.map fun (t, d) => if t == s then (t, d + c) else (t, d)
          | none => linear ++ [(s, c)]
    | p => products := products.push p
  let mut out : Array (Item F) := #[]
  for p in products do
    match p with
    | .product c a b ca cb =>
        let mut ca := ca
        let mut cb := cb
        if let some (_, d) := linear.find? (·.1 == a) then
          ca := ca + d
          linear := linear.filter (·.1 != a)
        if let some (_, d) := linear.find? (·.1 == b) then
          cb := cb + d
          linear := linear.filter (·.1 != b)
        out := out.push (.product c a b ca cb)
    | p => out := out.push p
  let sorted := linear.mergeSort fun x y => x.1 ≤ y.1
  for (s, c) in sorted do
    if c ≠ 0 then out := out.push (.linear c s)
  return out.toList

namespace Builder

def newSlot (def_ : SlotDef F) : LowerM F Nat := do
  let st ← get
  set { st with slots := st.slots.push def_ }
  return st.slots.size

def flush : LowerM F Unit := do
  let st ← get
  if st.pending.isEmpty then return
  let lanesPerRow := st.width / 4
  let mut lanes := st.pending.toList.map (·.1)
  let mut roles := st.pending.toList.map (·.2)
  lanes := lanes ++ List.replicate (lanesPerRow - lanes.length) zeroLane
  roles := roles ++ List.replicate (lanesPerRow - roles.length) .pad
  set { st with pending := #[], rows := st.rows.push (.gate lanes false roles) }

def pushLane (lane : Lane F) (role : Role) : LowerM F Unit := do
  modify fun st => { st with pending := st.pending.push (lane, role) }
  let st ← get
  if st.pending.size == st.width / 4 then flush

def joined (items : List (Item F)) (k qid : F) (role : Role) : LowerM F Unit := do
  let st ← get
  set { st with rows := st.rows.push (.gate (lanesOf items (st.width / 4) k qid) true [role]) }

def emitPiece (items : List (Item F)) (k qid : F) (role : Role) : LowerM F Unit := do
  let cells := (items.map Item.cells).sum
  let prods := (items.filter (·.cells == 2)).length
  if prods ≤ 1 && cells ≤ 4 then
    match lanesOf items 1 k qid with
    | [lane] => pushLane lane role
    | _ => throw "one lane"
  else joined items k qid role

/-- Emit `Σ items + k = 0` over one lane, one joined row, or a chain of rows
linked by carry slots. -/
def relationWith (items : List (Item F)) (k qid : F) (role : Role) : LowerM F Unit := do
  let items := normalizeItems items
  if items.isEmpty then
    if k ≠ 0 || qid ≠ 0 then throw "unsatisfiable relation"
    return
  let st ← get
  let width := st.width
  let lanesPerRow := width / 4
  let cells := (items.map Item.cells).sum
  let prods := (items.filter (·.cells == 2)).length
  if prods ≤ 1 && cells ≤ 4 then
    emitPiece items k qid role
    return
  let (capCells, capProds) := if lanesPerRow ≥ 2 then (width, lanesPerRow) else (4, 1)
  if prods ≤ capProds && cells ≤ capCells then
    joined items k qid role
    return
  if qid ≠ 0 then throw "invocation-id relation spans several rows"
  let mut rest := items.filter (·.cells == 2) ++ items.filter (·.cells != 2)
  let mut carry : Option Nat := none
  let mut k := k
  let mut fuel := rest.length + 1
  while !rest.isEmpty do
    if fuel == 0 then throw "carry chain did not terminate"
    fuel := fuel - 1
    let reserved := if carry.isSome then 1 else 0
    let fitsAll := (rest.map Item.cells).sum + reserved ≤ capCells &&
      (rest.filter (·.cells == 2)).length ≤ capProds
    let mut piece : Array (Item F) := #[]
    if fitsAll then
      piece := rest.toArray
      rest := []
    else
      let mut used := reserved + 1
      let mut p := 0
      let mut keep : Array (Item F) := #[]
      for item in rest do
        if used + item.cells ≤ capCells && (item.cells == 1 || p < capProds) then
          used := used + item.cells
          if item.cells == 2 then p := p + 1
          piece := piece.push item
        else keep := keep.push item
      rest := keep.toList
      if piece.isEmpty then throw "relation item does not fit a row"
    if let some c := carry then piece := piece.push (.linear 1 c)
    if rest.isEmpty then
      emitPiece piece.toList k 0 role
    else
      let terms := piece.toList.flatMap Item.terms
      let next ← newSlot (.sum terms k)
      piece := piece.push (.linear (-1) next)
      emitPiece piece.toList k 0 (.defines next)
      k := 0
      carry := some next

def relation (items : List (Item F)) (k : F) (role : Role) : LowerM F Unit :=
  relationWith items k 0 role

/-- The instance's invocation-id slot, pinned by `x − id = 0`. -/
def invocationSlot : LowerM F Nat := do
  if let some s := (← get).invocation then return s
  let s ← newSlot .invocation
  relationWith [.linear 1 s] 0 (-1) (.pin s)
  modify fun st => { st with invocation := some s }
  return s

mutual

partial def atomSlot (atom : Atom) : LowerM F Nat := do
  let st ← get
  match atom with
  | .column c =>
      if let some (some s) := st.columnSlots[c]? then return s
      let s ← newSlot (.column c)
      modify fun st => { st with columnSlots := st.columnSlots.set! c (some s) }
      return s
  | .product i =>
      if let some (some s) := st.productSlots[i]? then return s
      let some (some (x, y)) := st.operands[i]? | throw "missing product operands"
      let (item, k) ← productItems 1 x y
      let s ← newSlot (.sum item.terms k)
      relation [item, .linear (-1) s] k (.defines s)
      modify fun st => { st with productSlots := st.productSlots.set! i (some s) }
      return s

/-- `(slot, α, k)` with `form = α·slot + k`. -/
partial def affine (form : Form F) : LowerM F (Nat × F × F) := do
  match form.terms with
  | [(atom, c)] => return (← atomSlot atom, c, form.constant)
  | _ => return (← value ⟨form.terms, 0⟩, 1, form.constant)

partial def productItems (c : F) (x y : Form F) : LowerM F (Item F × F) := do
  let (u, alpha, k1) ← affine x
  let (v, beta, k2) ← affine y
  return (.product (c * alpha * beta) u v (c * alpha * k2) (c * beta * k1), c * k1 * k2)

/-- Items whose sum plus the returned constant equals `form`. -/
partial def expand (form : Form F) : LowerM F (List (Item F) × F) := do
  let mut items : Array (Item F) := #[]
  let mut k := form.constant
  for (atom, c) in form.terms do
    let st ← get
    match atom with
    | .product i =>
        if st.productUses[i]?.getD 0 == 1 && (st.productSlots[i]?.join).isNone then
          let some (some (x, y)) := st.operands[i]? | throw "missing product operands"
          let (item, k0) ← productItems c x y
          items := items.push item
          k := k + k0
        else
          items := items.push (.linear c (← atomSlot atom))
    | .column _ => items := items.push (.linear c (← atomSlot atom))
  return (items.toList, k)

partial def value (form : Form F) : LowerM F Nat := do
  if let some (_, s) := (← get).formSlots.find? (·.1 == form) then return s
  let s ← match form.terms, form.constant with
    | [(atom, c)], k =>
        if c == 1 && k == 0 then atomSlot atom else defineSum form
    | _, _ => defineSum form
  modify fun st => { st with formSlots := (form, s) :: st.formSlots }
  return s

partial def defineSum (form : Form F) : LowerM F Nat := do
  let (items, k) ← expand form
  let s ← newSlot (.sum (items.flatMap Item.terms) k)
  relation (items ++ [.linear (-1) s]) k (.defines s)
  return s

end

def buildForms (g : Graph F) : LowerM F Unit := do
  for i in [0:g.nodes.size] do
    let st ← get
    let f : Form F ← match g.nodes[i]! with
      | .const k => pure (Form.const k)
      | .var c => pure (Form.atom (.column c))
      | .add x y => pure (st.forms[x]!.combine st.forms[y]! 1)
      | .sub x y => pure (st.forms[x]!.combine st.forms[y]! (-1))
      | .neg x => pure (st.forms[x]!.scale (-1))
      | .mul x y =>
          let fx := st.forms[x]!
          let fy := st.forms[y]!
          match fx.asConstant, fy.asConstant with
          | some k, _ => pure (fy.scale k)
          | none, some k => pure (fx.scale k)
          | none, none =>
              modify fun st => { st with operands := st.operands.set! i (some (fx, fy)) }
              pure (Form.atom (.product i))
    modify fun st => { st with forms := st.forms.push f }

def countUses (g : Graph F) : LowerM F Unit := do
  let st ← get
  let mut demanded : Array (Form F) := #[]
  for z in g.zeros do demanded := demanded.push st.forms[z]!
  for (m, args) in g.lookups do
    demanded := demanded.push st.forms[m]!
    for a in args do demanded := demanded.push st.forms[a]!
  for operand in st.operands do
    if let some (x, y) := operand then
      demanded := demanded.push x |>.push y
  let mut columnUses := st.columnUses
  let mut productUses := st.productUses
  for f in demanded do
    for (atom, _) in f.terms do
      match atom with
      | .column c => columnUses := columnUses.modify c (· + 1)
      | .product i => productUses := productUses.modify i (· + 1)
  set { st with columnUses, productUses }

def messages (g : Graph F) : LowerM F Unit := do
  for (m, args) in g.lookups do
    let st ← get
    let mform := st.forms[m]!
    let forms := args.map fun a => st.forms[a]!
    let (tag, sub) ← match forms with
      | t :: s :: _ =>
          match t.asConstant, s.asConstant with
          | some tag, some sub => pure (tag, sub)
          | _, _ => throw "non-constant lookup tag or id"
      | _ => throw "lookup without [tag, id] prefix"
    let (sel, mult) ← match mform.terms, mform.constant with
      | [(atom, c)], k => if k == 0 then pure (c, ← atomSlot atom) else pure (1, ← value mform)
      | _, _ => pure (1, ← value mform)
    let index := (← get).messageCount
    if tag != 1 && tag != 2 then throw "unknown lookup tag"
    if tag == 2 && forms.length == 2 then throw "ROM lookup without address"
    let payload ← (forms.drop 2).mapM value
    let width := (← get).width
    let rom := tag == 2
    let receive := index == 0
    let ceilDiv (a b : Nat) : Nat := (a + b - 1) / b
    let (key, values, chunks) ← if rom then
        pure (payload.head?, payload.drop 1, max 1 (ceilDiv (payload.length - 1) (width - 2)))
      else if payload.length ≤ width - 1 then
        pure (none, payload, 1)
      else if receive then
        pure (some (← invocationSlot), payload, ceilDiv payload.length (width - 2))
      else
        pure (some (← newSlot (.key index)), payload, ceilDiv payload.length (width - 2))
    if chunks > 1 && !receive then
      relation [.product (sel * sel) mult mult 0 0, .linear (-sel) mult] 0 (.boolean mult)
    let per := if key.isSome then width - 2 else width - 1
    for c in [0:chunks] do
      let chunk := (values.drop (c * per)).take per
      let head := match key with
        | some k => [some mult, some k]
        | none => [some mult]
      let used := head ++ chunk.map some
      let cells := used ++ List.replicate (width - used.length) none
      let stride : F := (2 ^ 32 : Nat)
      let sub' := if chunks == 1 && (key.isNone || rom) then sub
        else if rom then sub + (c : F) * stride
        else sub + ((c + 1 : Nat) : F) * stride
      modify fun st => { st with rows := st.rows.push (.message sel tag sub' cells) }
    modify fun st => { st with messageCount := st.messageCount + 1 }

end Builder

/-- Lower one graph to a template of `width`-cell rows. -/
def lower (g : Graph F) (width : Nat) : Except String (Template F) := do
  if width < 4 || width % 4 != 0 then throw "template width must be a positive multiple of 4"
  let init : Builder F := {
    width
    operands := Array.replicate g.nodes.size none
    columnUses := Array.replicate g.width 0
    productUses := Array.replicate g.nodes.size 0
    columnSlots := Array.replicate g.width none
    productSlots := Array.replicate g.nodes.size none }
  let ((), st) ← (do
      Builder.buildForms g
      Builder.countUses g
      let st ← get
      for (z, j) in g.zeros.zipIdx do
        let form := st.forms[z]!
        match form.asConstant with
        | some k => if k ≠ 0 then throw "unsatisfiable constant constraint"
        | none =>
            let (items, k) ← Builder.expand form
            Builder.relation items k (.root j)
      Builder.messages g
      Builder.flush : LowerM F Unit).run init
  return { width, slots := st.slots.toList, rows := st.rows.toList }

/-- A hash-consed graph of a circuit, sharing structurally equal subterms. It
is only a lowering hint: templates are checked against the circuit itself.

Children are interned before their parent, so two subterms are structurally
equal exactly when their nodes (operator and child indices) are; the table is
keyed by node, constants by value. -/
partial def Graph.ofCircuit (C : Circuit F) : Graph F := Id.run do
  let rec visit (e : Scalar.Circuit.ArithExpr F) (st : Array (Node F) × Std.HashMap (Nat × Nat × Nat) Nat × List (F × Nat)) :
      Nat × (Array (Node F) × Std.HashMap (Nat × Nat × Nat) Nat × List (F × Nat)) :=
    let intern (key : Nat × Nat × Nat) (node : Node F) (st : Array (Node F) × Std.HashMap (Nat × Nat × Nat) Nat × List (F × Nat)) :=
      let (nodes, index, consts) := st
      match index[key]? with
      | some i => (i, st)
      | none => (nodes.size, (nodes.push node, index.insert key nodes.size, consts))
    match e with
    | .const v =>
        let (nodes, index, consts) := st
        match consts.find? (·.1 == v) with
        | some (_, i) => (i, st)
        | none => (nodes.size, (nodes.push (.const v), index, (v, nodes.size) :: consts))
    | .var c => intern (1, c, 0) (.var c) st
    | .add x y =>
        let (a, st) := visit x st
        let (b, st) := visit y st
        intern (2, a, b) (.add a b) st
    | .sub x y =>
        let (a, st) := visit x st
        let (b, st) := visit y st
        intern (3, a, b) (.sub a b) st
    | .mul x y =>
        let (a, st) := visit x st
        let (b, st) := visit y st
        intern (4, a, b) (.mul a b) st
  let mut st : Array (Node F) × Std.HashMap (Nat × Nat × Nat) Nat × List (F × Nat) := (#[], {}, [])
  let mut zeros : Array Nat := #[]
  for z in C.constraints do
    let (i, s) := visit z st
    st := s; zeros := zeros.push i
  let mut lookups : Array (Nat × List Nat) := #[]
  for l in C.lookups do
    let (m, s) := visit l.multiplicity st
    st := s
    let mut args : Array Nat := #[]
    for a in l.args do
      let (i, s) := visit a st
      st := s; args := args.push i
    lookups := lookups.push (m, args.toList)
  return { width := C.width, nodes := st.1, zeros := zeros.toList, lookups := lookups.toList }

/-- Lower and validate. Only checked templates are returned. -/
def tileOne (g : Graph F) (width : Nat) : Except String (Template F) := do
  let T ← lower g width
  unless T.check g.circuit do throw "template failed validation"
  return T

end Aiur.Tiling
