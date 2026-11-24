import Aiur.Optimized.Depth.Classify

/-!
# Recursion that needs no depth word

The depth pass gives every recursive circuit a depth word. Two kinds of recursion do not need
one, because a cycle among their rows is already impossible:

* *Structural* recursion: every call inside the SCC passes, in designated parameters, proper
  parts of the caller's designated parameters (components, or values behind a load). A cycle
  would need a cyclic data structure. Pointers only come from `store`, so a row whose arguments
  have finite store provenance (`ROM.Provenance`) cannot reach one.
* *Countdown* recursion: every call inside the SCC passes a designated field parameter moved by
  a small constant in one direction. The parameter is its own depth word; a cycle needs as many
  rows as the depth pass's gap argument excludes.

A call may keep the measure when it goes to a function of lower `order`, so helper functions
that forward their arguments are covered.

Such an SCC is *exempt*: its circuits are compiled as circuits without a depth word, and calls
into it are plain. `plan` finds exempt SCCs (untrusted); `check` and `certify` re-check them.

The soundness theorem of the depth pass (`Depth.acyclic`) does not cover exempt SCCs: with them
a memo graph may hold cyclic rows over cyclic data, unreachable from rows with good arguments.
The theorem for exempt SCCs is `Physical.Prepared.structural_memo_sound`
(`Depth.StructuralEndToEnd`).
-/

namespace Aiur.Optimized.Depth.Structural

variable {F : Type}

/-! ## Static relations between values and parameters -/

/-- How a value relates to a parameter of the function it occurs in. -/
inductive Relation where
  /-- The parameter itself. -/
  | same
  /-- A proper part of it: a component, or a value behind a load. -/
  | part
  /-- The parameter minus a small positive constant. -/
  | down
  /-- The parameter plus a small positive constant. -/
  | up
  deriving Repr, DecidableEq, Inhabited

/-- The known relations of a value: `(i, relation)` relates it to parameter `i`. -/
abbrev Parts := List (Nat × Relation)

/-- A component of the value, or what a load of it gives. -/
def Parts.proper (parts : Parts) : Parts :=
  parts.filterMap fun fact =>
    if fact.2 = .same ∨ fact.2 = .part then some (fact.1, Relation.part) else none

/-- The largest countdown step. A cycle of `L` steps moves a parameter by between `L` and
`L · maxStep`, which the row bound keeps below the characteristic. -/
def maxStep : Nat := 256

/-- Whether `constant` is a step: one of `1, …, maxStep`. -/
def isStep [NatCast F] [BEq F] (constant : F) : Bool :=
  (List.range maxStep).any fun n => constant == ((n + 1 : Nat) : F)

/-- The value moved by `constant`. -/
def Parts.step [NatCast F] [BEq F] (relation : Relation) (constant : F) (parts : Parts) : Parts :=
  if isStep constant then
    parts.filterMap fun fact => if fact.2 = .same then some (fact.1, relation) else none
  else []

/-- The value of `left op right` when `right` is a literal step. -/
def moved [NatCast F] [BEq F] (op : BinOp) (right : Expr F) (parts : Parts) : Parts :=
  match op, right with
  | .sub, .literal constant => parts.step .down constant
  | .add, .literal constant => parts.step .up constant
  | _, _ => []

/-- What every arm of a match gives. -/
def meet : List Parts → Parts
  | [] => []
  | first :: rest => rest.foldl (fun common parts => common.filter parts.contains) first

/-- The relations of the variables a pattern binds. -/
def bind : Pattern F → Parts → List (String × Parts)
  | .bind name, parts => [(name, parts)]
  | .tuple items, parts | .construct _ _ items, parts =>
      (items.map fun item => bind item parts.proper).flatten
  | _, _ => []
termination_by pattern => sizeOf pattern

/-- A call, with the relations of its arguments to the caller's parameters. -/
structure Call where
  callee : String
  args : List Parts
  deriving Repr, Inhabited

/-- The relations of an expression's value, and the calls it makes. -/
def scan [NatCast F] [BEq F] (env : List (String × Parts)) : Expr F → Parts × List Call
  | .literal _ => ([], [])
  | .var name => ((env.lookup name).getD [], [])
  | .tuple items | .construct _ _ items => ([], ((items.map (scan env)).map (·.2)).flatten)
  | .project value _ | .load value =>
      let inner := scan env value
      (inner.1.proper, inner.2)
  | .letValue pattern value body =>
      let bound := scan env value
      let rest := scan (bind pattern bound.1 ++ env) body
      (rest.1, bound.2 ++ rest.2)
  | .store value | .hint _ value _ | .neg value => ([], (scan env value).2)
  | .binary op left right =>
      let first := scan env left
      let second := scan env right
      (moved op right first.1, first.2 ++ second.2)
  | .assertEq _ left right | .ptrEq left right => ([], (scan env left).2 ++ (scan env right).2)
  | .call function args =>
      let scanned := args.map (scan env)
      ([], (scanned.map (·.2)).flatten ++ [⟨function, scanned.map (·.1)⟩])
  | .matchValue scrutinee arms =>
      let matched := scan env scrutinee
      let branches := arms.map fun arm => scan (bind arm.1 matched.1 ++ env) arm.2
      (meet (branches.map (·.1)), matched.2 ++ (branches.map (·.2)).flatten)
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      first
      | omega
      | cases arm; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- The calls of a function, relative to its own parameters. -/
def calls [NatCast F] [BEq F] (function : Function F) : List Call :=
  (scan (function.params.zipIdx.map fun (param, i) => (param.1, [(i, Relation.same)]))
    function.body).2

/-! ## Measures -/

/-- One component of a function's measure. -/
inductive Measure where
  /-- The largest of these parameters, as data structures. -/
  | parts (params : List Nat)
  /-- A field parameter that counts down. -/
  | down (param : Nat)
  /-- A field parameter that counts up. -/
  | up (param : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- How a call moves a measure. -/
inductive Move where
  | unknown
  | keeps
  | lowers
  deriving Repr, DecidableEq, Inhabited

/-- How a call moves one component, from the caller's `source` to the callee's `target`. -/
def Measure.move (args : List Parts) : Measure → Measure → Move
  | .parts source, .parts target =>
      let within := fun (relations : List Relation) =>
        !target.isEmpty && target.all fun j => source.any fun i =>
          relations.any fun relation => (args.getD j []).contains (i, relation)
      if within [.part] then .lowers else if within [.same, .part] then .keeps else .unknown
  | .down i, .down j =>
      let parts := args.getD j []
      if parts.contains (i, .down) then .lowers
      else if parts.contains (i, .same) then .keeps else .unknown
  | .up i, .up j =>
      let parts := args.getD j []
      if parts.contains (i, .up) then .lowers
      else if parts.contains (i, .same) then .keeps else .unknown
  | _, _ => .unknown

/-- A function's measure, and its order among the functions a call may keep the measure to. -/
structure FunctionPlan where
  measure : Measure
  order : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Untrusted: a measure for functions of exempt SCCs, by name. -/
abbrev Plan := List (String × FunctionPlan)

/-- A call descends: it lowers the measure, or keeps it and goes to a lower order. -/
def descends (plan : Plan) (caller : FunctionPlan) (call : Call) : Bool :=
  match plan.lookup call.callee with
  | none => false
  | some callee =>
      match Measure.move call.args caller.measure callee.measure with
      | .lowers => true
      | .keeps => decide (callee.order < caller.order)
      | .unknown => false

/-! ## Certificate -/

/-- Whether two functions' circuits are in one exempt SCC. -/
def together (cfg : Config) (representative : String → String) (caller callee : String) : Bool :=
  cfg.structural.contains (representative caller) &&
    cfg.structural.contains (representative callee) &&
    cfg.rank (representative caller) == cfg.rank (representative callee)

/-- Every call of `function` into its own exempt SCC descends. -/
def checkFunction [NatCast F] [BEq F] (cfg : Config) (representative : String → String)
    (plan : Plan) (function : Function F) : Bool :=
  match plan.lookup function.name with
  | none => false
  | some own =>
      (calls function).all fun call =>
        !together cfg representative function.name call.callee || descends plan own call

/-- The source half of the certificate: every function compiled to an exempt circuit descends,
every exempt circuit is some function's, and none carries a depth word. The bound on the
number of functions keeps a countdown cycle, which may visit a row once per function that
shares its circuit, within the depth pass's row-times-gap bound (`maxStep · 2^16 = 2^24`). -/
def check [NatCast F] [BEq F] (cfg : Config) (program : Program F)
    (representative : String → String) (plan : Plan) : Bool :=
  decide (program.functions.length ≤ 2 ^ 16) &&
  (program.functions.all fun function =>
    !cfg.structural.contains (representative function.name) ||
      checkFunction cfg representative plan function) &&
  cfg.structural.all fun chip =>
    !cfg.recursive chip && program.functions.any fun function => representative function.name == chip

/-- `slotOK`, or a plain call inside an exempt SCC. -/
def slotOK (cfg : Config) (source : Circuit.System F) (caller : String) (send : Circuit.Send F)
    (kind : SlotKind) : Bool :=
  Depth.slotOK cfg source caller send kind ||
    (kind == .plain && (source.findChip? send.channel).isSome && !cfg.recursive send.channel &&
      cfg.rank send.channel == cfg.rank caller &&
      cfg.structural.contains caller && cfg.structural.contains send.channel)

def chipOK (cfg : Config) (source : Circuit.System F) (chip : Circuit.Chip F) : Bool :=
  chip.wellFormed && decide ((cfg.plan chip.name).slots.length = chip.sends.length) &&
    (chip.sends.zip (cfg.plan chip.name).slots).all fun pair => slotOK cfg source chip.name pair.1 pair.2

/-- The circuit half of the certificate: `Depth.certify` with plain calls inside exempt SCCs,
whose circuits carry no depth word. -/
def certify (cfg : Config) (source : Circuit.System F) : Bool :=
  fresh cfg source && source.chips.all (chipOK cfg source) &&
    cfg.structural.all fun chip => !cfg.recursive chip

/-! ## Untrusted planning -/

/-- The measures of one kind (`0` parts, `1` down, `2` up) over `params` parameters; a parts
measure takes at most `width` of them. -/
def measures (params width : Nat) : Nat → List Measure
  | 0 =>
      let indices := List.range params
      let singles := indices.map ([·])
      let pairs := if width < 2 then [] else
        indices.flatMap fun i => (indices.filter (i < ·)).map fun j => [i, j]
      let triples := if width < 3 then [] else
        pairs.flatMap fun pair => (indices.filter (pair.getLastD 0 < ·)).map fun k => pair ++ [k]
      (singles ++ pairs ++ triples).map .parts
  | 1 => (List.range params).map .down
  | _ => (List.range params).map .up

/-- An order under which every call that keeps the measure goes down, if those calls have no
cycle: the length of the longest chain of such calls. -/
def orders (names : List String) (keeps : List (String × String)) : Option (List (String × Nat)) :=
  Id.run do
    let mut order := names.map fun name => (name, 0)
    for _ in names do
      order := order.map fun (name, _) =>
        (name, (keeps.filterMap fun (caller, callee) =>
          if caller == name then (order.lookup callee).map (· + 1) else none).foldl max 0)
    if keeps.all fun (caller, callee) =>
        decide ((order.lookup callee).getD 0 < (order.lookup caller).getD 0) then
      return some order
    return none

/-- A plan for one SCC with measures of the given `kind`, if there is one. `calls` are the
calls inside the SCC. -/
def planShape (members : List (String × Nat)) (calls : List (String × Call)) (kind : Nat)
    (width : Nat) : Option Plan := Id.run do
  let mut choices : List (List (String × Measure)) := [[]]
  for (name, params) in members do
    choices := (choices.flatMap fun chosen => (measures params width kind).filterMap fun candidate =>
      let chosen := (name, candidate) :: chosen
      -- Prune on the calls between the members chosen so far.
      if calls.all fun (caller, call) =>
          match chosen.lookup caller, chosen.lookup call.callee with
          | some source, some target => Measure.move call.args source target != .unknown
          | _, _ => true
        then some chosen else none).take 20000
  let names := members.map (·.1)
  for chosen in choices do
    let keeps := calls.filterMap fun (caller, call) =>
      match chosen.lookup caller, chosen.lookup call.callee with
      | some source, some target =>
          if Measure.move call.args source target == .keeps then some (caller, call.callee) else none
      | _, _ => none
    if let some order := orders names keeps then
      return some (chosen.map fun (name, measure) => (name, ⟨measure, (order.lookup name).getD 0⟩))
  return none

/-- The measure kinds tried, simplest first, each with the parameters a parts measure takes. -/
def shapes : List (Nat × Nat) := [(0, 1), (0, 3), (1, 1), (2, 1)]

/-- Find the exempt SCCs of `cfg` and rewrite it: their circuits lose the depth word, and calls
into them become plain. SCCs of more than `limit` functions are not tried. -/
def plan [NatCast F] [BEq F] (cfg : Config) (source : Circuit.System F) (program : Program F)
    (representative : String → String) (limit : Nat := 8) : Config × Plan := Id.run do
  let rankOf := fun (name : String) =>
    let chip := representative name
    if cfg.recursive chip then some (cfg.rank chip) else none
  let recursive := program.functions.filter fun function => (rankOf function.name).isSome
  let ranks := (recursive.filterMap fun function => rankOf function.name).eraseDups
  let mut exempt : List Nat := []
  let mut plans : Plan := []
  for rank in ranks do
    let members := recursive.filter fun function => rankOf function.name == some rank
    if members.length > limit then continue
    let names := members.map (·.name)
    let inside := members.flatMap fun function =>
      (calls function).filterMap fun call =>
        if names.contains call.callee then some (function.name, call) else none
    let sizes := members.map fun function => (function.name, function.params.length)
    if let some found := shapes.findSome? fun (shape, width) => planShape sizes inside shape width then
      exempt := rank :: exempt
      plans := plans ++ found
  let isExempt := fun (name : String) => cfg.recursive name && exempt.contains (cfg.rank name)
  let chips := source.chips.map fun chip =>
    let old := cfg.plan chip.name
    (chip.name, { recursive := old.recursive && !isExempt chip.name
                  slots := (chip.sends.zip old.slots).map fun (send, kind) =>
                    if isExempt send.channel then .plain else kind : ChipPlan })
  return ({ cfg with plans := chips
                     structural := (source.chips.filter (isExempt ·.name)).map (·.name) }, plans)

end Aiur.Optimized.Depth.Structural
