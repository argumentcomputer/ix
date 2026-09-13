import Compilatrix.Ixby.SymbolicWire
import Compilatrix.Ixby.Report
import Compilatrix.Coverage.Sources

namespace Compilatrix.Ixby.SymbolicExamples

open Ixon (Address)
open IxIR0 (Expr)

def address (n : UInt8) : Address := Address.replicate n
def app2 (fn a b : Expr) : Expr := .app (.app fn a) b
def pair (a b : Expr) : Expr := app2 (.ref (address 3)) a b
def pairData (a b : Data) : Data := .ctor (address 3) 2 [a, b]

def declarations : List (Address × IxIR0.Decl) := [
  (address 1, .ctor 0 0), (address 2, .ctor 1 1),
  (address 3, .ctor 2 2), (address 4, .ctor 2 2),
  (address 5, .recursor 0 false #[⟨0, .erased⟩, ⟨1, .var 0⟩, ⟨2, .var 1⟩]),
  (address 6, .recursor 1 false #[⟨0, .var 0⟩, ⟨1, .var 1⟩, ⟨2, pair (.var 2) (.var 1)⟩]),
  (address 7, .recursor 1 false #[⟨0, .var 0⟩,
    ⟨1, app2 (.var 2) (.var 1) (.var 0)⟩]),
  (address 8, .recursor 1 true #[⟨0, .var 0⟩,
    ⟨1, app2 (.var 2) (.var 1) (.var 0)⟩]),
  (address 20, .defn .shared (.lam .many (.var 0))),
  (address 21, .defn .shared (.lam .many (.lam .many (pair (.var 1) (.var 0)))))]

def constructorNat : Nat → Expr
  | 0 => .ref (address 1)
  | n + 1 => .app (.ref (address 2)) (constructorNat n)

def argument (input : Array Data) (i : Nat) : Data := input[i]?.getD .erased

structure Case where
  name : String
  parameters : Nat
  main : Expr
  expected : Array Data → Data
  wire : Bool := true

def cases : List Case := [
  ⟨"identity", 1, .var 0, fun xs => argument xs 0, true⟩,
  ⟨"beta", 1, .app (.lam .many (.var 0)) (.var 0), fun xs => argument xs 0, true⟩,
  ⟨"global-call", 1, .app (.ref (address 20)) (.var 0), fun xs => argument xs 0, true⟩,
  ⟨"capture-first", 2, app2 (.lam .many (.lam .many (.var 1))) (.var 1) (.var 0),
    fun xs => argument xs 0, true⟩,
  ⟨"capture-second", 2, app2 (.lam .many (.lam .many (.var 0))) (.var 1) (.var 0),
    fun xs => argument xs 1, true⟩,
  ⟨"let-capture", 2, .letE .many (.var 1) (.app (.lam .many (.var 1)) (.var 1)),
    fun xs => argument xs 0, true⟩,
  ⟨"higher-order", 1, app2 (.lam .many (.lam .many (.app (.var 1) (.var 0))))
    (.lam .many (.var 0)) (.var 0), fun xs => argument xs 0, true⟩,
  ⟨"pair", 2, pair (.var 1) (.var 0), fun xs => pairData (argument xs 0) (argument xs 1), true⟩,
  ⟨"pair-swapped", 2, pair (.var 0) (.var 1), fun xs => pairData (argument xs 1) (argument xs 0), true⟩,
  ⟨"duplicate", 1, pair (.var 0) (.var 0), fun xs => pairData (argument xs 0) (argument xs 0), true⟩,
  ⟨"nested-data", 2, .app (.ref (address 2)) (pair (.var 1) (.var 0)),
    fun xs => .ctor (address 2) 1 [pairData (argument xs 0) (argument xs 1)], true⟩,
  ⟨"partial-constructor", 2, .letE .many (.app (.ref (address 3)) (.var 1)) (.app (.var 0) (.var 1)),
    fun xs => pairData (argument xs 0) (argument xs 1), true⟩,
  ⟨"project-known", 2, .proj 0 (pair (.var 1) (.var 0)), fun xs => argument xs 0, true⟩,
  ⟨"same-tag-identity", 2, app2 (.ref (address 4)) (.var 1) (.var 0),
    fun xs => .ctor (address 4) 2 [argument xs 0, argument xs 1], true⟩,
  ⟨"case-known", 2, .app (.ref (address 5)) (pair (.var 1) (.var 0)), fun xs => argument xs 0, true⟩,
  ⟨"case-other-address", 2, .app (.ref (address 5)) (app2 (.ref (address 4)) (.var 1) (.var 0)),
    fun xs => argument xs 0, true⟩,
  ⟨"recursor-prefix", 3, app2 (.ref (address 6)) (.var 2) (pair (.var 1) (.var 0)),
    fun xs => pairData (argument xs 0) (argument xs 1), true⟩,
  ⟨"constructor-recursion", 1, app2 (.ref (address 7)) (.var 0) (constructorNat 9),
    fun xs => argument xs 0, true⟩,
  ⟨"literal-recursion", 1, app2 (.ref (address 8)) (.var 0) (.lit (.nat 17)),
    fun xs => argument xs 0, false⟩,
  ⟨"erased-apply", 1, .app .erased (.var 0), fun _ => .erased, true⟩,
  ⟨"erased-project", 1, .letE .many (.var 0) (.proj 99 .erased), fun _ => .erased, true⟩,
  ⟨"curried-global", 2, app2 (.ref (address 21)) (.var 1) (.var 0),
    fun xs => pairData (argument xs 0) (argument xs 1), true⟩,
  ⟨"four-argument-order", 4, pair (.var 3) (.var 0),
    fun xs => pairData (argument xs 0) (argument xs 3), true⟩,
  ⟨"two-live-captures", 2, .app (.lam .many (.var 2)) (.var 0), fun xs => argument xs 0, true⟩]

def generalPool : Array Data := #[.nat 0, .nat 1, .nat (2 ^ 160 + 7), .str "", .str "λ🙂\n",
  .erased, .ctor (address 1) 0 [], .ctor (address 2) 1 [.erased],
  pairData (.nat 19) (.str "payload"), .ctor (address 4) 2 [.erased, pairData (.nat 3) (.nat 4)]]

def wirePool : Array Data := #[.erased, .ctor (address 1) 0 [],
  .ctor (address 2) 1 [.ctor (address 1) 0 []], pairData .erased (.ctor (address 1) 0 []),
  .ctor (address 4) 2 [.ctor (address 2) 1 [.erased], .erased]]

def inputs (pool : Array Data) (parameters seed : Nat) : Array Data :=
  ((List.range parameters).map fun i => pool[(seed * 3 + i * 7) % pool.size]!).toArray

def Case.source (test : Case) : Source := { declarations, main := test.main, parameters := test.parameters }

def generated (count : Nat := 12) : List Case := (List.range count).map fun depth => {
  name := s!"generated-calls-{depth + 1}"
  parameters := 2
  main := (List.range (depth + 1)).foldl (fun expr _ => .app (.ref (address 20)) expr) (pair (.var 1) (.var 0))
  expected := fun xs => pairData (argument xs 0) (argument xs 1) }

private def definition (body type : Ixon.Expr) (refs : Array Address) : Ixon.Constant := {
  info := .defn { kind := .defn, safety := .safe, lvls := 0, typ := type, value := body }
  sharing := #[], refs, univs := #[.zero] }

/-- Typed open Ixon definitions pass the ordinary address, usage, erasure,
and member-coverage gates before the symbolic Ixby checker is called. -/
def ixonSources : Except String (List (String × Nat × List (Address × Ixon.Constant) × Address)) := do
  let base ← Coverage.directCall
  let constants := base.constants.take 3
  let natType := constants[1]!.1
  let identity := constants[2]!.1
  let block := constants[0]!.1
  let zero ← Coverage.addressed {
    info := .cPrj { idx := 0, cidx := 0, block }, sharing := #[], refs := #[], univs := #[] }
  let succ ← Coverage.addressed {
    info := .cPrj { idx := 0, cidx := 1, block }, sharing := #[], refs := #[], univs := #[] }
  let constants := constants ++ [zero, succ]
  let nat : Ixon.Expr := .ref 0 #[]
  let unary : Ixon.Expr := .all .many .shared nat nat
  let binary : Ixon.Expr := .all .many .shared nat unary
  let first ← Coverage.addressed (definition (.lam .many nat (.lam .many nat (.var 1))) binary #[natType])
  let second ← Coverage.addressed (definition (.lam .many nat (.lam .many nat (.var 0))) binary #[natType])
  let helper ← Coverage.addressed (definition
    (.lam .many nat (.app (.ref 1 #[]) (.app (.ref 1 #[]) (.var 0)))) unary #[natType, identity])
  let localCapture ← Coverage.addressed (definition
    (.lam .many nat (.letE true nat (.var 0) (.app (.lam .many nat (.var 1)) (.var 0)))) unary #[natType])
  return [("ixon-identity", 1, constants, identity),
    ("ixon-first", 2, constants ++ [first], first.1),
    ("ixon-second", 2, constants ++ [second], second.1),
    ("ixon-helper", 1, constants ++ [helper], helper.1),
    ("ixon-local-capture", 1, constants ++ [localCapture], localCapture.1)]

private def reject (name : String) (result : Except String α) : Except String String :=
  match result with
  | .error _ => .ok name
  | .ok _ => .error s!"unexpected symbolic acceptance: {name}"

def rejections : Except String (List String) := do
  let mut rejected := []
  for (name, parameters, main) in [
      ("opaque-projection", 1, Expr.proj 0 (.var 0)),
      ("opaque-application", 2, .app (.var 1) (.var 0)),
      ("opaque-constructor-case", 1, .app (.ref (address 5)) (.var 0)),
      ("opaque-nat-recursion", 2, app2 (.ref (address 8)) (.var 1) (.var 0)),
      ("function-result", 1, .lam .many (.var 0)),
      ("strict-let", 1, .letE .many (.proj 0 (.var 0)) .erased),
      ("strict-erased-argument", 1, .app .erased (.proj 0 (.var 0)))] do
    let compiled ← compile { declarations, parameters, main }
    rejected := rejected ++ [← reject name compiled.certifySymbolic]
  let simple : Source := { declarations, parameters := 1, main := .var 0 }
  let compiled ← compile simple
  rejected := rejected ++ [← reject "source-fuel" (compiled.certifySymbolic 0)]
  rejected := rejected ++ [← reject "target-fuel" (compiled.certifySymbolic 10000 0)]
  rejected := rejected ++ [← reject "result-depth" (compiled.certifySymbolic 10000 100000 0)]
  let divergent ← compile { simple with
    declarations := declarations ++ [(address 25, .defn .shared (.ref (address 25)))]
    main := .ref (address 25) }
  rejected := rejected ++ [← reject "divergence" (divergent.certifySymbolic 100 1000)]
  let limited ← compile { simple with main := .app (.lam .many (.var 0)) (.var 0) }
    { limits := { continuations := 0 } }
  rejected := rejected ++ [← reject "continuation-capacity" limited.certifySymbolic]
  for (name, depth, input) in [
      ("argument-arity", 100, #[]), ("argument-depth-zero", 0, #[Data.erased]),
      ("argument-depth", 1, #[.ctor (address 2) 1 [.erased]]),
      ("argument-address", 100, #[.ctor (address 99) 0 []]),
      ("argument-tag", 100, #[.ctor (address 3) 1 [.erased, .erased]]),
      ("argument-fields", 100, #[.ctor (address 3) 2 [.erased]])] do
    rejected := rejected ++ [← reject name (Arguments.check simple {} depth input)]
  rejected := rejected ++ [← reject "argument-boxing-node-budget"
    (Arguments.check simple { limits := { inputNodes := 1 } } 100 #[.nat 0])]
  rejected := rejected ++ [← reject "argument-nat-bits"
    (Arguments.check simple { limits := { natBits := 1 } } 100 #[.nat 4])]
  rejected := rejected ++ [← reject "argument-string-bytes"
    (Arguments.check simple { limits := { stringBytes := 1 } } 100 #[.str "λ"]) ]
  rejected := rejected ++ [← reject "profile-nat" (Arguments.check simple Config.crypto 100 #[.nat 0])]
  rejected := rejected ++ [← reject "profile-string" (Arguments.check simple Config.crypto 100 #[.str ""])]
  -- Each candidate below still passes the original whole-image validator.
  let first : Source := { declarations, parameters := 2, main := .var 1 }
  let second ← compile { first with main := .var 0 }
  rejected := rejected ++ [← reject "mutated-argument-order" (certifySymbolicImage first {} second.program)]
  let capture : Source := { first with main := .app (.lam .many (.var 2)) (.var 0) }
  let captureCode ← compile capture
  let swapped := { captureCode.program with functions := captureCode.program.functions.map fun fn =>
    { fn with blocks := fn.blocks.map fun block =>
      match block.instruction with
      | .letOp (.closure callee operands) next =>
          { block with instruction := .letOp (.closure callee operands.reverse) next }
      | _ => block } }
  let _ ← (Ix.Ixby.validateProgram {} swapped).mapError reprStr
  rejected := rejected ++ [← reject "mutated-capture-order" (certifySymbolicImage capture {} swapped)]
  let constructed : Source := { first with main := pair (.var 1) (.var 0) }
  let pairCode ← compile constructed
  let constructors := pairCode.program.constructors
  let swapped := { pairCode.program with
    constructors := (constructors.set! 6 constructors[7]!).set! 7 constructors[6]! }
  let _ ← (Ix.Ixby.validateProgram {} swapped).mapError reprStr
  rejected := rejected ++ [← reject "mutated-constructor-address" (certifySymbolicImage constructed {} swapped)]
  let badArity := { pairCode.program with constructors := constructors.modify 6 (fun ctor => { ctor with fields := 3 }) }
  rejected := rejected ++ [← reject "mutated-constructor-arity" (certifySymbolicImage constructed {} badArity)]
  let wireCode ← compile simple Config.crypto
  let exported ← wireCode.export
  let first ← Arguments.check simple Config.crypto 100 #[.erased]
  let second ← Arguments.check simple Config.crypto 100 #[.ctor (address 1) 0 []]
  let original ← first.export exported
  let _ ← first.read exported original.bytes
  rejected := rejected ++ [← reject "misbound-canonical-input" (second.read exported original.bytes)]
  rejected := rejected ++ [← reject "trailing-canonical-input" (first.read exported (original.bytes.push 0))]
  rejected := rejected ++ [← reject "truncated-canonical-input"
    (first.read exported (original.bytes.extract 0 (original.bytes.size - 1)))]
  return rejected

end Compilatrix.Ixby.SymbolicExamples
