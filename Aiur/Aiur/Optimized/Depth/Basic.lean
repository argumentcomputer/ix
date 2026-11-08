import Aiur.Optimized.PhysicalSemantics

/-!
# Depth pass (Track A, design H1)

A lookup argument with free provide multiplicities accepts cyclic memo tables:
a row for `fn loop(x) { loop(x) }` claiming `loop(0) = 42` with multiplicity 2
pays for its own self-call and for the public claim. This pass rules such
tables out without a per-function termination proof.

* A static partition of the chips into strongly connected components (SCCs) of
  the call graph comes with a rank: every call goes to a chip of lower or equal
  rank, and equal rank only between chips that carry a depth word.
* A *recursive* chip appends one column `d` to its provided call message, as a
  final `Field` argument.
* A call slot into the caller's own SCC appends the callee's depth word to its
  demanded message. An *exact* slot demands `d - 1` (no column, no lookup). A
  *gap* slot demands `d - 1 - gap`, with the gap split into limbs, each limb a
  fresh column range-checked by a fixed map.
* A call slot from another SCC into a recursive chip (*external*) carries the
  callee's depth word as a free column (option E1).

Every intra-SCC edge then lowers the depth word by `1 + gap ∈ [1, 2^k]`, where
`k` is the sum of the limb widths. A cycle of `L` rows would need such steps to
sum to zero in the field, so `L · 2^k` reaches the characteristic; a row bound
`N` with `N · 2^k` below the characteristic excludes every cycle
(`Depth.Soundness`).

The pass changes neither constraints nor memory lookups. Original sends keep
their order, followed by the limb range checks. Whether a slot is exact or gap
carries no proof obligation: both give `d_callee < d_caller`. A wrong `exact`
only makes honest proving fail.
-/

namespace Aiur.Optimized.Depth

open Circuit

variable {F : Type}

/-- How a call slot carries a callee depth word. -/
inductive SlotKind where
  /-- The callee has no depth word (not recursive, or a fixed map). -/
  | plain
  /-- Same SCC; the callee's depth word is `d - 1`. -/
  | exact
  /-- Same SCC; the callee's depth word is `d - 1 - gap`, with range-checked limbs. -/
  | gap
  /-- Another SCC; the callee's depth word is a free column. -/
  | external
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Columns allocated by a slot of this kind. -/
def SlotKind.width (limbs : List Nat) : SlotKind → Nat
  | .gap => limbs.length
  | .external => 1
  | _ => 0

structure ChipPlan where
  recursive : Bool := false
  /-- One kind per send, in send order. -/
  slots : List SlotKind := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Untrusted pass input. `Certified` checks everything soundness relies on. -/
structure Config where
  /-- Bit widths of the gap limbs, low limb first. `[16, 8]` gives `k = 24`. -/
  limbs : List Nat := [16, 8]
  plans : List (String × ChipPlan) := []
  /-- SCC ranks: callees lower. -/
  ranks : List (String × Nat) := []
  deriving Repr, BEq, Inhabited

def Config.plan (cfg : Config) (name : String) : ChipPlan := (List.lookup name cfg.plans).getD {}

def Config.recursive (cfg : Config) (name : String) : Bool := (cfg.plan name).recursive

def Config.rank (cfg : Config) (name : String) : Nat := (List.lookup name cfg.ranks).getD 0

/-- The gap bound is `2 ^ cfg.bits`. -/
def Config.bits (cfg : Config) : Nat := cfg.limbs.sum

/-! ## Range maps -/

def rangeName (width : Nat) : String := s!"Depth::range{width}"
def rangeInputs (width : Nat) : String := s!"Depth::range{width}_inputs"
def rangeUnits (width : Nat) : String := s!"Depth::range{width}_units"

def unitWire : WireValue α := ⟨.tuple [], []⟩

def rangeDecl (width : Nat) : MapDecl :=
  ⟨rangeName width, [("x", .field)], .tuple [], rangeInputs width, rangeUnits width⟩

/-- `range{width}(x) = ()` exactly for `x ∈ [0, 2^width)`. -/
def rangeInputTable [NatCast F] (width : Nat) : Table F :=
  ⟨rangeInputs width, .tuple [.field], (List.range (2 ^ width)).map fun (n : Nat) => .tuple [.field (n : F)]⟩

def rangeUnitTable (width : Nat) : Table F :=
  ⟨rangeUnits width, .tuple [], (List.range (2 ^ width)).map fun _ => .tuple []⟩

def rangeTables [NatCast F] (width : Nat) : List (Table F) := [rangeInputTable width, rangeUnitTable width]

def rangeNames (width : Nat) : List String := [rangeName width, rangeInputs width, rangeUnits width]

/-- Every name the pass adds: maps and their tables. -/
def Config.names (cfg : Config) : List String :=
  cfg.limbs.dedup.flatMap rangeNames

def rangeMessage (width : Nat) (value : F) : Message F :=
  ⟨rangeName width, [⟨.field, [value]⟩], unitWire⟩

/-! ## Chip compilation -/

def rangeSend (width column : Nat) (enable : ArithExpr F) : Send F :=
  ⟨rangeName width, [⟨.field, [.var column]⟩], unitWire, enable⟩

/-- Horner form: limb `i` lives in `column + i`. -/
def gapExpr [Field F] : List Nat → Nat → ArithExpr F
  | [], _ => .const 0
  | width :: widths, column =>
      .add (.var column) (.mul (.const ((2 ^ width : Nat) : F)) (gapExpr widths (column + 1)))

def limbChecks : List Nat → Nat → ArithExpr F → List (Send F)
  | [], _, _ => []
  | width :: widths, column, enable => rangeSend width column enable :: limbChecks widths (column + 1) enable

/-- The callee depth word a slot demands, given the caller's depth expression. -/
def extra [Field F] (limbs : List Nat) (depth : ArithExpr F) :
    SlotKind → Nat → Option (ArithExpr F)
  | .plain, _ => none
  | .exact, _ => some (.sub depth (.const 1))
  | .gap, column => some (.sub (.sub depth (.const 1)) (gapExpr limbs column))
  | .external, column => some (.var column)

def Send.extend (send : Send F) : Option (ArithExpr F) → Send F
  | none => send
  | some word => { send with args := send.args ++ [⟨.field, [word]⟩] }

/-- Original sends, in order, each with its depth word. `column` is the next free column. -/
def mainSends [Field F] (limbs : List Nat) (depth : ArithExpr F) :
    Nat → List (Send F × SlotKind) → List (Send F)
  | _, [] => []
  | column, (send, kind) :: rest =>
      Send.extend send (extra limbs depth kind column) ::
        mainSends limbs depth (column + kind.width limbs) rest

/-- Limb range checks of the gap slots, gated by their slot's enable. -/
def rangeSends (limbs : List Nat) : Nat → List (Send F × SlotKind) → List (Send F)
  | _, [] => []
  | column, (send, kind) :: rest =>
      (if kind = .gap then limbChecks limbs column send.enable else []) ++
        rangeSends limbs (column + kind.width limbs) rest

def nextColumn (limbs : List Nat) : Nat → List (Send F × SlotKind) → Nat
  | column, [] => column
  | column, (_, kind) :: rest => nextColumn limbs (column + kind.width limbs) rest

def ChipPlan.base (plan : ChipPlan) (chip : Chip F) : Nat :=
  if plan.recursive then chip.numVars + 1 else chip.numVars

def compileChip [Field F] (limbs : List Nat) (plan : ChipPlan)
    (chip : Chip F) : Chip F :=
  let pairs := chip.sends.zip plan.slots
  let depth : ArithExpr F := .var chip.numVars
  { chip with
    inputs := if plan.recursive then chip.inputs ++ [⟨.field, [chip.numVars]⟩] else chip.inputs
    numVars := nextColumn limbs (plan.base chip) pairs
    sends := mainSends limbs depth (plan.base chip) pairs ++ rangeSends limbs (plan.base chip) pairs }

/-- The depth system. Range maps and their tables are appended under fresh names. -/
def system [Field F] (cfg : Config) (source : System F) : System F :=
  { source with
    chips := source.chips.map fun chip => compileChip cfg.limbs (cfg.plan chip.name) chip
    maps := source.maps ++ cfg.limbs.dedup.map rangeDecl
    tables := source.tables ++ cfg.limbs.dedup.flatMap rangeTables }

/-! ## Messages -/

/-- The final word of the final argument: a recursive chip's depth word. -/
def depthWord [Zero F] (message : Message F) : F :=
  ((message.args.getLast?.map WireValue.words).bind List.head?).getD 0

/-- Drop the depth word of calls into recursive chips. -/
def erase (cfg : Config) (message : Message F) : Message F :=
  if cfg.recursive message.channel then { message with args := message.args.dropLast } else message

/-! ## Certificate -/

/-- What a call slot needs: equal rank only on depth-carrying intra-SCC slots,
and a depth word exactly on calls into recursive chips. -/
def slotOK (cfg : Config) (source : System F) (caller : String) (send : Send F)
    (kind : SlotKind) : Bool :=
  match source.findChip? send.channel with
  | none => decide (kind = .plain ∧ cfg.recursive send.channel = false)
  | some _ =>
      match kind with
      | .plain => decide (cfg.recursive send.channel = false ∧ cfg.rank send.channel < cfg.rank caller)
      | .external => decide (cfg.recursive send.channel = true ∧ cfg.rank send.channel < cfg.rank caller)
      | .exact | .gap => decide (cfg.recursive caller = true ∧ cfg.recursive send.channel = true ∧
          cfg.rank send.channel = cfg.rank caller)

/-- The added names are new, and no fixed map is treated as recursive. -/
def fresh (cfg : Config) (source : System F) : Bool :=
  decide cfg.names.Nodup &&
    source.chips.all (fun chip => decide (chip.name ∉ cfg.names) &&
      chip.sends.all fun send => decide (send.channel ∉ cfg.names)) &&
    source.maps.all (fun map => decide (map.name ∉ cfg.names) && decide (map.input ∉ cfg.names) &&
      decide (map.output ∉ cfg.names) && decide (cfg.recursive map.name = false)) &&
    source.tables.all (fun table => decide (table.name ∉ cfg.names))

def chipOK (cfg : Config) (source : System F) (chip : Chip F) : Bool :=
  chip.wellFormed && decide ((cfg.plan chip.name).slots.length = chip.sends.length) &&
    (chip.sends.zip (cfg.plan chip.name).slots).all fun pair => slotOK cfg source chip.name pair.1 pair.2

/-- The decidable SCC certificate, checked at export like `Grouping.Checked`. -/
def certify (cfg : Config) (source : System F) : Bool :=
  fresh cfg source && source.chips.all (chipOK cfg source)

def Certified (cfg : Config) (source : System F) : Prop := certify cfg source = true

instance (cfg : Config) (source : System F) : Decidable (Certified cfg source) := by
  unfold Certified; infer_instance

end Aiur.Optimized.Depth
