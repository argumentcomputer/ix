module
public import Ix.Aiur.Stages.Codegen

public section
namespace AiurTests.RustSyntax
open Aiur.Codegen

private def assertEq (actual expected : RustExpr) : RustStmt :=
  .exprStmt (.macroCall "assert_eq" #[actual, expected])

private def debugLabel : String := "debug {} quote: \" slash: \\ newline:\nλ"

/-- Compile and execute the rendered tree rather than asserting source-text
    snapshots. Covers precedence, escaping, block values, guarded patterns,
    closures, const parameters, and early return through a closure. -/
private def program : Array RustItem := Id.run do
  let text := "quote: \" slash: \\ newline:\n\r\t\x00 braces: {} unicode: λ"
  let bytes : Array RustExpr := text.toUTF8.data.map (fun b => .nat b.toNat)
  let guardedMatch (value : Nat) : RustExpr := .matchExpr (.call (.var "Some") #[.nat value]) #[
    { pat := .constructor #["Some"] #[.binding "x"]
      guard := some (.binop .lt (.var "x") (.nat 10))
      body := { tail := some (.var "x") } },
    { pat := .wildcard, body := { tail := some (.nat 99) } }]
  let closure : RustExpr := .closure #[.binding "x"] (.binop .add (.var "x") (.nat 1))
  let labelValue : RustExpr := .labeledBlock "value" {
    stmts := #[.forStmt (.binding "x") (.arrayLit #[.nat 4, .nat 5]) #[
      .ifStmt (.binop .eq (.var "x") (.nat 5))
        #[.breakWith "value" (.var "x")] none]]
    tail := some (.nat 0) }
  let resultTy : RustType := .app "Result" #[.named "u64", .named "u64"]
  let earlyReturn : RustItem := .function {
    name := "early_return"
    params := #[("fail", .named "bool")]
    returnTy := resultTy
    body := { stmts := #[
      .letStmt false "result" (some resultTy) (.call (.closure #[] (.block {
        stmts := #[
          .ifStmt (.var "fail") #[.returnStmt (.call (.var "Err") #[.nat 13])] none,
          .returnStmt (.call (.var "Ok") #[.nat 9])]
      })) #[]),
      .letStmt false "answer" none (.tryExpr (.var "result")),
      .returnStmt (.call (.var "Ok") #[.var "answer"])
    ] } }
  let choose : RustItem := .function {
    name := "choose"
    constParams := #[("MODE", .named "bool")]
    params := #[]
    returnTy := .named "u64"
    body := { tail := some (.ifExpr (.var "MODE")
      { tail := some (.nat 3) } { tail := some (.nat 8) }) } }
  let main : RustItem := .function {
    name := "main", params := #[], returnTy := .tuple #[]
    body := { stmts := (#[
      assertEq (.methodCall (.string text) "as_bytes" #[]) (.ref (.arrayLit bytes)),
      assertEq (.binop .mul (.binop .add (.nat 2) (.nat 3)) (.nat 4)) (.nat 20),
      assertEq (.call closure #[.nat 4]) (.nat 5),
      assertEq (guardedMatch 7) (.nat 7),
      assertEq (guardedMatch 17) (.nat 99),
      assertEq labelValue (.nat 5),
      assertEq (.call (.constGeneric (.var "choose") #[.bool true]) #[]) (.nat 3),
      assertEq (.call (.constGeneric (.var "choose") #[.bool false]) #[]) (.nat 8),
      assertEq (.call (.var "early_return") #[.bool false]) (.call (.var "Ok") #[.nat 9]),
      assertEq (.call (.var "early_return") #[.bool true]) (.call (.var "Err") #[.nat 13]),
      .letStmt false "pair" none (.tuple #[.nat 6]),
      assertEq (.field (.var "pair") "0") (.nat 6),
      .letStmt false "values" (some (.array (.named "u64") (.value 2)))
        (.arrayLit #[.nat 11, .nat 12]),
      .letStmt false "ptr" none
        (.cast (.ref (.var "values")) (.ptr false (.array (.named "u64") (.value 2)))),
      assertEq (.index (.unsafeBlock { tail := some (.deref (.var "ptr")) }) (.nat 1)) (.nat 12),
      assertEq (.index (.ref (.var "values")) (.nat 0)) (.nat 11),
      assertEq (.methodCall (.ref (.var "values")) "len" #[]) (.nat 2),
      .letStmt false "callbacks" none (.tuple #[closure]),
      assertEq (.call (.field (.var "callbacks") "0") #[.nat 4]) (.nat 5),
      assertEq (.field (.ifExpr (.bool true) { tail := some (.tuple #[.nat 2]) }
        { tail := some (.tuple #[.nat 3]) }) "0") (.nat 2),
      .letStmt false "__v_0" (some (.named "u64")) (.nat 41),
      .letStmt false "__v_1" (some (.named "u64")) (.nat 7)
    ] ++ emitOp 0 (.debug debugLabel none) ++
      emitOp 0 (.debug debugLabel (some #[])) ++
      emitOp 0 (.debug debugLabel (some #[0, 1]))) } }
  return #[earlyReturn, choose, main]

def run : IO UInt32 := IO.FS.withTempDir fun dir => do
  let source := dir / "syntax.rs"
  let binary := dir / "syntax-test"
  IO.FS.writeFile source (String.join (program.toList.map RustItem.toStr))
  let compile ← IO.Process.output {
    cmd := "rustc"
    args := #["--edition=2024", "--crate-name", "aiur_syntax_test", source.toString,
      "-o", binary.toString]
  }
  if compile.exitCode != 0 then
    IO.eprintln s!"Rust syntax test failed to compile:\n{compile.stderr}"
    return 1
  let result ← IO.Process.output { cmd := binary.toString }
  if result.exitCode != 0 then
    IO.eprintln s!"Rust syntax test failed at runtime:\n{result.stderr}"
    return 1
  let expectedOutput := debugLabel ++ "\n" ++ debugLabel ++ ": \n" ++ debugLabel ++ ": 41, 7\n"
  if result.stdout != expectedOutput then
    IO.eprintln s!"Generated debug operation printed unexpected output: {repr result.stdout}"
    return 1
  IO.println "aiur-rust-syntax: generated Rust compiled and all runtime assertions passed"
  return 0

end AiurTests.RustSyntax
end
