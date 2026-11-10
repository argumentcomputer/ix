import Ix.Meta
import Ix.Compile.Equations
import LSpec

/-!
  The unfolding-equation export of `ix compile --equations`
  (`Ix.Compile.Equations`), on a source with a structurally recursive
  definition, a well-founded one, a mutual block, a non-recursive one and a
  root that reaches them and a library definition.

  The source is elaborated twice, from files written at run time: as it is,
  where `close` realizes the unfolding theorems, and with a proof that names
  `f.eq_def` for each local definition, where Lean's elaborator realizes them
  through the reserved-name action. Each theorem the export realized must have
  exactly the statement Lean gives it there. Every association must also state
  `f xs = …` for its own definition, and the closure must hold every
  associated theorem.
-/

open Lean LSpec

namespace Tests.Ix.Compile.Equations

/-- The definitions. `log2` is well-founded (Lean derives its `eq_def` when it
elaborates it); the others are structural (Lean derives theirs on demand). -/
def source : String := "namespace EqnFixture

def len : List Nat → Nat
  | [] => 0
  | _ :: t => len t + 1

def log2 (n : Nat) : Nat :=
  if h : n < 2 then 0 else log2 (n / 2) + 1
termination_by n
decreasing_by omega

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

def double (n : Nat) : Nat := n + n

def entry (l : List Nat) (n : Nat) : Nat :=
  len l + log2 n + (if isEven n then double n else 0) + l.length

end EqnFixture
"

/-- The local recursive definitions, each with its unfolding theorem. -/
def recursive : List (Name × Name) :=
  [(`EqnFixture.len, `EqnFixture.len.eq_def), (`EqnFixture.log2, `EqnFixture.log2.eq_def),
   (`EqnFixture.isEven, `EqnFixture.isEven.eq_def), (`EqnFixture.isOdd, `EqnFixture.isOdd.eq_def)]

/-- The structurally recursive ones, whose theorems the export must realize. -/
def structural : List Name := [`EqnFixture.len, `EqnFixture.isEven, `EqnFixture.isOdd]

/-- The source with Lean's own reference to each local unfolding theorem, in a
proof, so that the theorem the elaborator realizes stays in the environment
(`#check` would discard it). -/
def referenced : String :=
  source ++ String.join (recursive.zipIdx.map fun ((_, e), i) =>
    s!"theorem eqnReference{i} : True := by\n  have := @{e}\n  trivial\n")

/-- Whether `type`, under its binders, is `@Eq _ (definition …) _`. -/
def unfoldsItself (definition : Name) (type : Expr) : Bool :=
  match type.getForallBody.eq? with
  | some (_, lhs, _) => lhs.getAppFn.constName? == some definition
  | none => false

def elaborate (dir : System.FilePath) (file : String) (text : String) : IO Environment := do
  let path := dir / file
  IO.FS.writeFile path text
  getFileEnv path

def suite : IO (List LSpec.TestSeq) := do
  IO.FS.withTempDir fun dir => do
    let env ← elaborate dir "Equations.lean" source
    let before := structural.map fun d => env.contains (d ++ `eq_def)
    let (env, closed, found, failed) ← Ix.Compile.Equations.close env [`EqnFixture.entry]
    let leanEnv ← elaborate dir "EquationsReferenced.lean" referenced
    let closedNames : NameSet := closed.foldl (fun s (n, _) => s.insert n) {}
    let pairs := found.toList.map fun a => (a.definition, a.equation)
    let sameAsLean := recursive.all fun (_, e) =>
      match env.find? e, leanEnv.find? e with
      | some ours, some theirs => ours.type == theirs.type && ours.levelParams == theirs.levelParams
      | _, _ => false
    let selfUnfolding := found.all fun a =>
      match env.find? a.equation with
      | some (.thmInfo t) => unfoldsItself a.definition t.type
      | _ => false
    let json := Ix.Compile.Equations.toJson found failed
    let listed : List (String × String) := match json.getObjValAs? (Array Json) "equations" with
      | .ok rows => rows.toList.filterMap fun row =>
          match row.getObjValAs? String "definition", row.getObjValAs? String "equation" with
          | .ok d, .ok e => some (d, e)
          | _, _ => none
      | .error _ => []
    let sorted := listed.map (·.1)
    return [
      test "no structural unfolding theorem exists before the export" (before.all (!·)),
      test "every local recursive definition is associated with its own eq_def"
        (recursive.all pairs.contains),
      test "the non-recursive definitions are not associated"
        (!pairs.any fun (d, _) => d == `EqnFixture.double || d == `EqnFixture.entry),
      test "a library definition the root reaches is associated (List.length)"
        (pairs.contains (`List.length, `List.length.eq_def)),
      test "no equation generation failed" failed.isEmpty,
      test "each definition is associated once"
        ((pairs.map (·.1)).eraseDups.length == pairs.length),
      test "the closure holds every associated theorem"
        (found.all fun a => closedNames.contains a.equation),
      test "each realized theorem has the statement Lean's elaborator gives it" sameAsLean,
      test "each associated theorem states `f xs = …` for its definition" selfUnfolding,
      test "the JSON names its format"
        ((json.getObjValAs? String "format").toOption == some "ix/compile-equations/1"),
      test "the JSON lists every association, sorted by definition"
        (listed.length == found.size && sorted == sorted.mergeSort (· ≤ ·) &&
          recursive.all fun (d, e) => listed.contains (d.toString, e.toString)),
      test "the JSON lists no failure"
        (json.getObjValAs? (Array Json) "failures" |>.toOption |>.map (·.isEmpty) |>.getD false)]

end Tests.Ix.Compile.Equations
