import Compilatrix.Ixby.Wire
import Compilatrix.IxIR1.WellModedGen

namespace Compilatrix.Ixby.Examples

open Ixon (Address)
open IxIR0 (Expr)

def address (n : UInt8) : Address := Address.replicate n

def declarations : List (Address × IxIR0.Decl) := [
  (address 1, .ctor 0 0), (address 2, .ctor 1 1), (address 3, .ctor 2 2),
  (address 4, .recursor 0 true #[⟨0, .lit (.nat 7)⟩, ⟨1, .app (.var 1) (.var 0)⟩]),
  -- A distinct constructor with the same tag/field count must enter the same rule.
  (address 5, .ctor 1 1)]

private def app2 (f a b : Expr) : Expr := .app (.app f a) b
private def nat (n : Nat) : Expr := .lit (.nat n)

structure Case where
  name : String
  main : Expr
  expected : Data
  input : Array Data := #[]

def cases : List Case := [
  ⟨"nat", nat (2 ^ 130 + 7), .nat (2 ^ 130 + 7), #[]⟩,
  ⟨"string", .lit (.str "λ🙂\nIxby"), .str "λ🙂\nIxby", #[]⟩,
  ⟨"identity", .app (.lam .many (.var 0)) (nat 12), .nat 12, #[]⟩,
  ⟨"capture", app2 (.lam .many (.lam .many (.var 1))) (nat 12) (nat 13), .nat 12, #[]⟩,
  ⟨"let-capture", .letE .linear (nat 17)
    (.app (.lam .affine (.var 1)) (nat 99)), .nat 17, #[]⟩,
  ⟨"constructor", app2 (.ref (address 3)) (nat 12) (nat 13),
    .ctor (address 3) 2 [.nat 12, .nat 13], #[]⟩,
  ⟨"partial-constructor", .letE .many (.app (.ref (address 3)) (nat 12))
    (.proj 1 (.app (.var 0) (nat 13))), .nat 13, #[]⟩,
  ⟨"zero-constructor", .ref (address 1), .ctor (address 1) 0 [], #[]⟩,
  ⟨"rec-nat-zero", .app (.ref (address 4)) (nat 0), .nat 7, #[]⟩,
  ⟨"rec-nat-succ", .app (.ref (address 4)) (nat 25), .nat 7, #[]⟩,
  ⟨"rec-constructor", .app (.ref (address 4)) (.app (.ref (address 2)) (.ref (address 1))), .nat 7, #[]⟩,
  ⟨"rec-other-address", .app (.ref (address 4)) (.app (.ref (address 5)) (nat 4)), .nat 7, #[]⟩,
  ⟨"erased-apply", .app .erased (nat 1), .erased, #[]⟩,
  ⟨"erased-project", .proj 123 .erased, .erased, #[]⟩,
  ⟨"dynamic-nat", .app (.ref (address 4)) (.var 0), .nat 7, #[.nat 6]⟩,
  ⟨"dynamic-ctor", .app (.ref (address 4)) (.var 0), .nat 7,
    #[.ctor (address 2) 1 [.ctor (address 1) 0 []]]⟩,
  ⟨"runtime-order", .proj 0 (app2 (.ref (address 3)) (.var 1) (.var 0)),
    .str "first", #[.str "first", .nat 99]⟩]

def runCase (test : Case) : Except String Data := do
  let source : Source := { declarations, main := test.main, parameters := test.input.size }
  let compiled ← compile source
  let certificate ← compiled.certify test.input 10000 100000 1000
  unless certificate.result == test.expected do throw s!"{test.name}: independent expectation differs"
  return certificate.result

/-- All pure templates in the existing seeded corpus, including ownership
patterns excluded by IxIR₁. Returned functions are applied to a real Nat. -/
def generated : Except String Nat := do
  let decls := IxIR0.Examples.declList.filter fun (_, decl) =>
    match decl with | .extern _ => false | _ => true
  let mut state := IxIR1.WellModedGen.defaultSeed
  let mut checked := 0
  for index in [:IxIR1.WellModedGen.defaultCases] do
    let (test, next) := IxIR1.WellModedGen.generateAt IxIR1.WellModedGen.defaultSeed index state
    state := next
    if test.kind != .externAdd then
      let main := match test.kind with
        | .partialAdd | .partialNonMany | .uniqueCapture =>
            .app test.template.expr (IxIR0.Examples.natE 2)
        | _ => test.template.expr
      let compiled ← (compile { declarations := decls, main }).mapError
        (fun error => s!"generated {index} {reprStr test.kind}: {error}")
      let _ ← (compiled.certify #[] 10000 100000 1000).mapError
        (fun error => s!"generated {index} {reprStr test.kind}: {error}")
      checked := checked + 1
  return checked

private def reject (name : String) (result : Except String α) : Except String String :=
  match result with | .error _ => .ok name | .ok _ => .error s!"unexpected acceptance: {name}"

def rejections : Except String (List String) := do
  let simple : Source := { declarations := [], main := .erased }
  let mut rejected := []
  for (name, source, config) in [
      ("unknown-reference", { simple with main := .ref (address 99) }, {}),
      ("unbound-variable", { simple with main := .var 0 }, {}),
      ("duplicate-declaration", { simple with declarations :=
        [(address 1, .ctor 0 0), (address 1, .ctor 0 0)] }, {}),
      ("extern", { simple with declarations := [(address 1, .extern 0)] }, {}),
      ("work-limit", simple, { work := 0 }),
      ("depth-limit", simple, { depth := 0 }),
      ("function-limit", simple, { limits := { functions := 1 } }),
      ("constructor-limit", simple, { limits := { constructors := 3 } }),
      ("local-limit", simple, { limits := { locals := 0 } }),
      ("nat-profile-limit", { simple with main := nat 1 }, Config.profile { limits := { natBits := 0 } }),
      ("string-profile-limit", { simple with main := .lit (.str "x") },
        Config.profile { limits := { stringBytes := 0 } })] do
    rejected := rejected ++ [← reject name (compile source config)]
  for (name, main) in [
      ("apply-data", .app (nat 1) (nat 2)),
      ("project-literal", .proj 0 (nat 1)),
      ("project-function", .proj 0 (.lam .many .erased)),
      ("project-bounds", .proj 0 (.ref (address 1))),
      ("bad-major", .app (.ref (address 4)) .erased),
      ("field-count", .app (.ref (address 4)) (app2 (.ref (address 3)) .erased .erased)),
      ("strict-let", .letE .many (.app (nat 1) (nat 2)) .erased),
      ("strict-argument", .app .erased (.app (nat 1) (nat 2)))] do
    let compiled ← compile { declarations, main }
    rejected := rejected ++ [← reject name compiled.execute]
  let compiled ← compile simple
  rejected := rejected ++ [← reject "target-fuel" (compiled.execute #[] 0)]
  rejected := rejected ++ [← reject "input-arity" (compiled.execute #[.erased])]
  let identity ← compile { declarations := [], main := .var 0, parameters := 1 }
  rejected := rejected ++ [← reject "input-identity" (identity.execute #[.ctor (address 99) 0 []])]
  let funResult ← compile { simple with main := .lam .many (.var 0) }
  rejected := rejected ++ [← reject "function-output-data-abi" funResult.certify]
  let divergent ← compile { declarations := [(address 8, .defn .shared (.ref (address 8)))], main := .ref (address 8) }
  rejected := rejected ++ [← reject "runtime-divergence" (divergent.execute #[] 50)]
  rejected := rejected ++ [← reject "profile-limit-binding"
    (compiled.export { limits := { functions := 17 } })]
  return rejected

end Compilatrix.Ixby.Examples
