module
public import Tests.Ix.Resource
public section
namespace Tests.ResourceConversion
open Ixon Ix.Resource

def ref (i : UInt64) : Ixon.Expr := .ref i #[]
def box (x : Ixon.Expr) : Ixon.Expr := .app (.app (ref 4) (ref 0)) x

/-- Explicit test-only nominal metadata, mirrored by Rust. Literal slot zero
is deliberately 37, and slot one is zero: blob IDs are not natural values. -/
def program : Program := {
  declarations := #[
    { type := .sort 0, kind := .typeConstructor },
    { type := ref 0, kind := .constructor },
    { type := .all .many .shared (ref 0) (ref 0), kind := .constructor },
    { type := .all .many .shared (.sort 0) (.sort 0), kind := .typeConstructor },
    { type := .all .many .shared (.sort 0)
        (.all .many .shared (.var 0) (.app (ref 3) (.var 1))), kind := .constructor },
    { type := ref 0, kind := .constructor },
    { type := .all .many .shared (ref 0) (.sort 0), kind := .typeConstructor },
    { type := .all .many .shared (ref 0) (.app (ref 6) (.var 0)), kind := .assumption }
  ]
  sharing := #[.share 0]
  projections := #[{ typeRef := 3, constructor := 4, params := 1, fields := 1 }]
  natType := some (ref 0)
  naturalValues := #[37, 0, 1, 37, 2^100]
  naturalConstructors := some (1, 2) }

structure Case where
  name : String
  expected : String
  left : Ixon.Expr
  right : Ixon.Expr
  depth : Nat := 32

def cases : Array Case := #[
  ⟨"payload ID is not numeric value", "different", .nat 0, ref 1, 32⟩,
  ⟨"zero literal and constructor", "equal", .nat 1, ref 1, 32⟩,
  ⟨"successor literal and constructor", "equal", .nat 2, .app (ref 2) (ref 1), 32⟩,
  ⟨"distinct payloads with equal value", "equal", .nat 0, .nat 3, 32⟩,
  ⟨"missing literal payload", "different", .nat 9, ref 1, 32⟩,
  ⟨"unrelated nullary constructor", "different", .nat 1, ref 5, 32⟩,
  ⟨"natural constructor universe arguments", "different", .nat 1, .ref 1 #[0], 32⟩,
  ⟨"large literal remains binary", "different", .nat 4, .nat 0, 32⟩,
  ⟨"canonical structure projection", "equal", .prj 3 0 (box (.nat 1)), ref 1, 32⟩,
  ⟨"wrong projection owner", "different", .prj 0 0 (box (.nat 1)), ref 1, 32⟩,
  ⟨"wrong projection constructor", "different",
    .prj 3 0 (.app (.app (ref 5) (ref 0)) (.nat 1)), ref 1, 32⟩,
  ⟨"out of range projection", "different", .prj 3 1 (box (.nat 1)), ref 1, 32⟩,
  ⟨"undersaturated constructor projection", "different", .prj 3 0 (.app (ref 4) (.nat 1)), ref 1, 32⟩,
  ⟨"oversaturated constructor projection", "different", .prj 3 0 (.app (box (.nat 1)) (.nat 1)), ref 1, 32⟩,
  ⟨"nested projection", "equal", .prj 3 0 (box (.prj 3 0 (box (.nat 0)))), .nat 3, 32⟩,
  ⟨"projection retains lambda contract", "different",
    .prj 3 0 (box (.lam { uses := .linear } (ref 0) (.var 0))),
    .lam .many (ref 0) (.var 0), 32⟩,
  ⟨"cyclic sharing is bounded", "budget", .share 0, .nat 1, 12⟩,
  ⟨"zero depth fails closed", "budget", .nat 1, ref 1, 0⟩
]

def line (c : Case) : String :=
  s!"{c.name}\t{c.expected}\t{c.depth}\t{hexOfBytes (runPut (putExpr c.left))}\t{hexOfBytes (runPut (putExpr c.right))}"

def fixtureText : String :=
  cases.foldl (fun text c => text ++ line c ++ "\n")
    "# name\texpected\tdepth\tleft (ixon-v4 hex)\tright (ixon-v4 hex)\n"

def successor (e : Ixon.Expr) : Ixon.Expr := .app (ref 2) e

/-- Owner IDs deliberately differ from telescope positions. Each initializer
was written before its own binder, and can refer to earlier bindings. -/
def localContext : Context := {
  program
  vars := #[40, 7, 91]
  letValues := #[(7, successor (.var 0)), (91, successor (.var 0))] }

def localCases : Array Case := #[
  ⟨"two local aliases", "equal", .var 0, successor (successor (.var 2)), 32⟩,
  ⟨"outer local alias", "equal", .var 1, successor (.var 2), 32⟩,
  ⟨"different local values", "different", .var 0, successor (.var 2), 32⟩,
  ⟨"aliases under dependent binder", "equal",
    .all .many .shared (ref 0) (.app (ref 6) (.var 1)),
    .all .many .shared (ref 0) (.app (ref 6) (successor (successor (.var 3)))), 32⟩,
  ⟨"inner binder stays bound", "different",
    .all .many .shared (ref 0) (.var 0), .all .many .shared (ref 0) (.var 3), 32⟩,
  ⟨"local conversion retains lambda contract", "different",
    .lam { uses := .linear } (ref 0) (.var 1),
    .lam .many (ref 0) (successor (successor (.var 3))), 32⟩,
  ⟨"escaping local index", "unbound", .var 3, ref 1, 32⟩,
  ⟨"local expansion bounded", "budget", .var 0, successor (successor (.var 2)), 2⟩
]

def localFixtureText : String :=
  localCases.foldl (fun text c => text ++ line c ++ "\n")
    "# name\texpected\tdepth\tleft (ixon-v4 hex)\tright (ixon-v4 hex)\n"

def localOutcome (c : Case) : String :=
  match (requireTypeIn localContext c.depth c.left c.right).run {} with
  | .ok _ _ => "equal"
  | .error .typeMismatch _ => "different"
  | .error (.unbound _) _ => "unbound"
  | .error .budget _ => "budget"
  | .error _ _ => "unexpected-error"

def localFunction : Ixon.Expr :=
  .lam .many (ref 0) (.letE { nonDep := false, binder := .many } (ref 0) (successor (.var 0))
    (.app (ref 7) (.var 0)))

def localFunctionType (index : Ixon.Expr) : Ixon.Expr :=
  .all .many .shared (ref 0) (.app (ref 6) index)

def outcome (c : Case) (p : Program := program) : String :=
  match (compatible p c.depth c.left c.right).run {} with
  | .ok true _ => "equal"
  | .ok false _ => "different"
  | .error .budget _ => "budget"
  | .error _ _ => "unexpected-error"

/-- Raw conversion metadata tests: addressed-family authentication is checked
separately; these rules exercise bounded substitution and dispatch exactly. -/
def iotaProgram : Program := { program with
  declarations := program.declarations ++ #[
    { type := ref 0, kind := .assumption }, { type := ref 0, kind := .assumption }]
  conversionRecursors := #[
    { index := 8, leading := 1, major := 1, rules := #[
      { constructor := 4, params := 1, fields := 1,
        rhs := .lam .many (.all .many .shared (ref 0) (ref 0))
          (.lam .many (ref 0) (.app (.var 1) (.var 0))) }] },
    { index := 9, leading := 1, major := 1, rules := #[
      { constructor := 4, params := 1, fields := 1,
        rhs := .lam .many (.all .many .shared (ref 0) (ref 0))
          (.lam .many (ref 0) (.app (.app (ref 9) (.var 1)) (box (.var 0)))) }] }] }

def identity : Ixon.Expr := .lam .many (ref 0) (.var 0)
def reduceBox (minor value : Ixon.Expr) (recursor : UInt64 := 8) : Ixon.Expr :=
  .app (.app (ref recursor) minor) value

def iotaCases : Array Case := #[
  ⟨"iota selects exact field after parameter", "equal", reduceBox identity (box (.nat 0)), .nat 3, 64⟩,
  ⟨"iota keeps trailing application", "equal",
    .app (reduceBox (.lam .many (ref 0) (.lam .many (ref 0) (.var 1))) (box (.nat 0))) (.nat 1), .nat 3, 64⟩,
  ⟨"iota preserves lambda contract", "different",
    reduceBox (.lam .many (ref 0) (.lam { uses := .linear } (ref 0) (.var 0))) (box (.nat 0)),
    identity, 64⟩,
  ⟨"iota exact constructor identity", "different",
    reduceBox identity (.app (.app (ref 5) (ref 0)) (.nat 0)), .nat 3, 64⟩,
  ⟨"partial recursor is neutral", "different", .app (ref 8) identity, .nat 3, 64⟩,
  ⟨"undersaturated iota constructor", "unsupported", reduceBox identity (.app (ref 4) (ref 0)), .nat 3, 64⟩,
  ⟨"oversaturated iota constructor", "unsupported", reduceBox identity (.app (box (.nat 0)) (.nat 1)), .nat 3, 64⟩,
  ⟨"numeric major stays neutral", "different", reduceBox identity (.nat 1), .nat 1, 64⟩,
  ⟨"nested iota", "equal", reduceBox identity (box (reduceBox identity (box (.nat 0)))), .nat 3, 64⟩,
  ⟨"cyclic iota bounded", "budget", reduceBox identity (box (.nat 0)) 9, .nat 3, 24⟩,
  ⟨"iota zero depth", "budget", reduceBox identity (box (.nat 0)), .nat 3, 0⟩
]

def iotaFixtureText : String :=
  iotaCases.foldl (fun text c => text ++ line c ++ "\n")
    "# name\texpected\tdepth\tleft (ixon-v4 hex)\tright (ixon-v4 hex)\n"

def iotaOutcome (c : Case) : String :=
  match (compatible iotaProgram c.depth c.left c.right).run {} with
  | .ok true _ => "equal"
  | .ok false _ => "different"
  | .error (.unsupported _) _ => "unsupported"
  | .error .budget _ => "budget"
  | .error _ _ => "unexpected-error"

def checkMemo : IO Unit := do
  let linear := .lam { uses := .linear } (ref 0) (.var 0)
  let action : CheckM (Ixon.Expr × Ixon.Expr) := do
    let first ← whnf program 32 linear
    let second ← whnf program 32 identity
    return (first, second)
  match action.run { resourceWhnfMemoEnabled := true } with
  | .ok (first, second) state =>
    unless first != second && state.resourceWhnfMemo.size == 2 do
      throw (IO.userError "WHNF memo erased a lambda contract")
  | .error e _ => throw (IO.userError s!"WHNF memo: {repr e}")
  match (whnf program 8 (.share 0)).run { resourceWhnfMemoEnabled := true } with
  | .error .budget state =>
    unless state.resourceWhnfMemo.isEmpty do
      throw (IO.userError "cyclic WHNF was memoized as successful")
  | _ => throw (IO.userError "cyclic WHNF did not fail closed")
  let first : Program := { declarations := #[{ type := ref 0, body := some (.nat 1) }] }
  let second : Program := { declarations := #[{ type := ref 0, body := some (.nat 0) }] }
  let mixed : CheckM Ixon.Expr := do
    discard <| whnf first 32 (ref 0)
    whnf second 32 (ref 0)
  match mixed.run {} with
  | .ok value state =>
    unless value == .nat 0 && state.resourceWhnfMemo.isEmpty do
      throw (IO.userError "default WHNF state reused a result across programs")
  | .error e _ => throw (IO.userError s!"default WHNF: {repr e}")

def run : IO Unit := do
  checkMemo
  unless (← IO.FS.readFile "Tests/Fixtures/ixon-v4/resource-conversion.tsv") == fixtureText do
    throw (IO.userError "resource conversion fixture differs from its producer")
  for c in cases do
    unless outcome c == c.expected do
      throw (IO.userError s!"resource conversion {c.name}: {outcome c}, expected {c.expected}")
  let zero : Case := ⟨"disabled numeric rule", "different", .nat 1, ref 1, 32⟩
  unless outcome zero { program with naturalConstructors := none } == "different" do
    throw (IO.userError "natural conversion accepted without authenticated constructor identities")
  unless (← IO.FS.readFile "Tests/Fixtures/ixon-v4/resource-local-conversion.tsv") == localFixtureText do
    throw (IO.userError "local conversion fixture differs from its producer")
  for c in localCases do
    unless localOutcome c == c.expected do
      throw (IO.userError s!"local conversion {c.name}: {localOutcome c}, expected {c.expected}")
  for (name, index, accepted) in #[("dependent let", successor (.var 0), true),
      ("wrong dependent index", .var 0, false)] do
    let result := (analyze 128 { program } localFunction
      (some (localFunctionType index, .shared)) 0 .linear).run {}
    let actual := match result with | .ok .. => true | .error .. => false
    unless actual == accepted do
      throw (IO.userError s!"local conversion {name}: {repr result}")
  unless (← IO.FS.readFile "Tests/Fixtures/ixon-v4/resource-iota-conversion.tsv") == iotaFixtureText do
    throw (IO.userError "iota conversion fixture differs from its producer")
  for c in iotaCases do
    unless iotaOutcome c == c.expected do
      throw (IO.userError s!"iota conversion {c.name}: {iotaOutcome c}, expected {c.expected}")
  IO.println s!"Resource conversion: {cases.size + localCases.size + iotaCases.size + 3} shared and metadata checks passed"
end Tests.ResourceConversion
end
