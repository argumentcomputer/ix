import IxCC.Own.Plain.Certificate

set_option autoImplicit false
namespace IxCCTests.Recheck.Rc.CodecControls
open IxCC Lean System

def mutateFirst (rewrite : Json → Option Json) : Nat → Json → Option Json
  | 0, _ => none
  | fuel + 1, j =>
    match rewrite j with
    | some result => some result
    | none => match j with
      | .arr xs =>
        let (ys, changed) := xs.foldl (init := (#[], false)) fun (out, changed) child =>
          if changed then (out.push child, true)
          else match mutateFirst rewrite fuel child with
            | some replacement => (out.push replacement, true)
            | none => (out.push child, false)
        if changed then some (.arr ys) else none
      | _ => none

def rewrite (kind : String) (j : Json) : Option Json := do
  let xs ← j.getArr?.toOption
  match kind, xs.toList with
  | "remove-action", [.str "act", _, next] => some next
  | "inc-count", [.str "inc", x, n] =>
    some (.arr #[.str "inc", x, toJson ((n.getNat?.toOption.getD 0) + 1)])
  | "dec-variable", [.str "dec", x] =>
    some (.arr #[.str "dec", toJson ((x.getNat?.toOption.getD 0) + 4096)])
  | "extra-map-node", [.str "leaf"] =>
    some (.arr #[.str "node", .null, j, j])
  | "extra-action-field", [.str "inc", x, n] =>
    some (.arr #[.str "inc", x, n, .str "ignored?"])
  | "wrong-control-shape", [.str "return"] => some (.arr #[.str "trap"])
  | "capture-remove", [.str "join", .arr captured, b, k] =>
    some (.arr #[.str "join", .arr captured.pop, b, k])
  | "capture-duplicate", [.str "join", .arr captured, b, k] =>
    some (.arr #[.str "join", .arr (captured.push (captured[0]?.getD .null)), b, k])
  | "capture-order", [.str "join", .arr captured, b, k] =>
    some (.arr #[.str "join", .arr captured.reverse, b, k])
  | "branch-remove", [.str "case", .arr branches, d] =>
    some (.arr #[.str "case", .arr branches.pop, d])
  | "branch-extra", [.str "case", .arr branches, d] =>
    some (.arr #[.str "case", .arr (branches.push (branches[0]?.getD .null)), d])
  | "default-remove", [.str "case", branches, _] =>
    some (.arr #[.str "case", branches, .null])
  | "occupied-entry-null", [.str "node", value, z, o] =>
    if value == .null then none else some (.arr #[.str "node", .null, z, o])
  | "empty-entry-code", [.str "node", .null, z, o] =>
    some (.arr #[.str "node", .arr #[.str "return"], z, o])
  | "negative-natural", [.str "inc", x, _] =>
    some (.arr #[.str "inc", x, toJson (-1 : Int)])
  | "wrong-scalar-type", [.str "inc", _, n] =>
    some (.arr #[.str "inc", .str "0", n])
  | _, _ => none

def refused (F : Fir.Program) (label : String) (j : Json) : IO Unit := do
  match Own.Plain.Certificate.admit F j with
  | .error _ => IO.println s!"PASS refusal {label}"
  | .ok _ => throw (IO.userError s!"damaged ownership certificate accepted: {label}")

def negatives (F : Fir.Program) (j : Json) : IO Unit := do
  let xs ← IO.ofExcept j.getArr?
  unless xs.size == 2 do throw (IO.userError "unexpected producer envelope")
  refused F "version" (.arr #[.str "ixcc/own-plain/999", xs[1]!])
  refused F "extra-envelope-field" (.arr (xs.push (.str "extra")))
  refused F "missing-complete-map" (.arr #[xs[0]!, .arr #[.str "leaf"]])
  for kind in ["remove-action", "inc-count", "dec-variable", "extra-map-node",
      "extra-action-field", "wrong-control-shape", "negative-natural", "wrong-scalar-type"] do
    let some corrupted := mutateFirst (rewrite kind) 4096 j |
      throw (IO.userError s!"control {kind} did not actually mutate the certificate")
    refused F kind corrupted

/-- Decoder controls use a small explicit source with joins, branch/default
and an empty optional map slot. This is not the real-source correctness gate. -/
def syntheticControls : IO Unit := do
  let body : Fir.Code := .jp 0 [2] false (.ret (.var 2))
    (.case 0 [.mk default (.ret (.var 1))] (some (.ret (.var 0))))
  let fd : Fir.Fun := { key := default, params := [(0, .tobj), (1, .tobj)], body }
  let F : Fir.Program := {
    funs := .node (some fd) (.node none .leaf .leaf) .leaf
    size := 1, exports := [0], ctors := [], known := {} }
  let candidate := Own.Plain.Program.canonical F
  let j := Own.Plain.Certificate.encode candidate.bodies
  let _ ← IO.ofExcept (Own.Plain.Certificate.admit F j)
  for kind in ["capture-remove", "capture-duplicate", "branch-remove",
      "branch-extra", "default-remove", "occupied-entry-null", "empty-entry-code"] do
    let some corrupted := mutateFirst (rewrite kind) 4096 j |
      throw (IO.userError s!"synthetic control {kind} did not mutate")
    unless corrupted != j do throw (IO.userError s!"synthetic control {kind} was a no-op")
    refused F kind corrupted
  -- The ownership checker treats a join's captured list as a set of variables, so the reversed
  -- list is another placement it types, and admission accepts it (heap stage 2; before, admission
  -- refused every map but the canonical one). `OwnedIO.capturedOrder` takes such a certificate
  -- through the whole verifier and runs its object.
  let some reordered := mutateFirst (rewrite "capture-order") 4096 j |
    throw (IO.userError "synthetic control capture-order did not mutate")
  unless reordered != j do throw (IO.userError "synthetic control capture-order was a no-op")
  match Own.Plain.Certificate.admit F reordered with
  | .ok _ => IO.println "PASS acceptance capture-order (another placement the checker types)"
  | .error e => throw (IO.userError s!"reordered captured list refused: {e}")
  let encoded := Own.Plain.Certificate.code (Own.Plain.lowerCode [0, 1] [] body)
  match Own.Plain.Certificate.code? 0 encoded body with
  | .error _ => IO.println "PASS refusal action-depth"
  | .ok _ => throw (IO.userError "zero code depth accepted")
  match Own.Plain.Certificate.bodyMap? 1 (Own.Plain.Certificate.bodyMap candidate.bodies) F.funs with
  | .error _ => IO.println "PASS refusal map-depth"
  | .ok _ => throw (IO.userError "insufficient map depth accepted")
  match Own.Plain.Certificate.ofText F "{" with
  | .error _ => IO.println "PASS refusal malformed-json"
  | .ok _ => throw (IO.userError "malformed JSON accepted")

end IxCCTests.Recheck.Rc.CodecControls
