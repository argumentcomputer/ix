import Compilatrix.Recheck.Run

/-! Focused structural readback discovery controls, independent of exported
fixtures. The synthetic family has no List name or pinned address. -/

namespace CompilatrixTests.Recheck.Readback

open Compilatrix

private def app (f a : Src.Term) : Src.Term := .app f a .strict .type
private def pi (d b : Src.Term) : Src.Term := .pi {} .shared d b
private def typeSort : Src.Term := .sort (.succ .zero)
private def seqTy (a : Src.Term) : Src.Term := app (.const 1 []) a
private def rootDecl (ty : Src.Term) : Src.Decl := .defn .defn .safe 0 ty (.natLit 0)

def source : Src.Program :=
  let decls : List Src.Decl := [
    .induct true 0 0 0 typeSort [],
    .induct true 0 1 0 (pi typeSort typeSort) [2, 3],
    .ctor true 0 1 0 1 0 (pi typeSort (seqTy (.var 0))),
    .ctor true 0 1 1 1 2
      (pi typeSort (pi (.var 0) (pi (seqTy (.var 1)) (seqTy (.var 2))))),
    rootDecl (seqTy (.const 0 []))]
  { Src.Program.ofConsts (decls.map fun d => { ref := default, addr := default, decl := d }) with
    known := { nat := some 0 } }

def cfg : Cfg.Program :=
  { funs := .leaf, size := 0, exports := [], known := {}, ctors := [
    { key := .src 2, tag := 0, arity := 0 },
    { key := .src 3, tag := 1, arity := 2 }] }

private def checkCase (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"readback discovery: {name}")

private def rejects (p : Src.Program) (C : Cfg.Program := cfg) : Bool :=
  match Compilatrix.Recheck.Readback.discover p C 4 with
  | .error _ => true
  | .ok _ => false

def run : IO Nat := do
  let expected : Rt.Sig := { inds := [[[], [.nat, .ind 0]]] }
  checkCase "generic parametric recursive family"
    ((Compilatrix.Recheck.Readback.discover source cfg 4).toOption == some (expected, .ind 0))
  checkCase "rootTy fallback" (Compilatrix.Recheck.rootTy source cfg 4 == some (expected, .ind 0))
  let natRoot := source.setDecl 4 (rootDecl (.const 0 []))
  checkCase "original Nat branch" (Compilatrix.Recheck.rootTy natRoot cfg 4 == some ({}, .nat))
  let boolRoot := { source with known := { source.known with bool := some 1 } }
  let boolRoot := boolRoot.setDecl 4 (rootDecl (.const 1 []))
  checkCase "original Bool branch"
    (Compilatrix.Recheck.rootTy boolRoot cfg 4 == some (Compilatrix.Recheck.boolSig cfg, .ind 0))
  checkCase "missing constructors" (rejects source { cfg with ctors := [] })
  checkCase "duplicate constructors" (rejects source { cfg with ctors := cfg.ctors ++ cfg.ctors })
  checkCase "wrong tag" (rejects source { cfg with ctors := cfg.ctors.map fun r => { r with tag := r.tag + 1 } })
  checkCase "wrong field layout" (rejects source { cfg with ctors := cfg.ctors.map fun r => { r with arity := r.arity + 1 } })
  checkCase "unbound result variable" (rejects (source.setDecl 4 (rootDecl (.var 0))))
  checkCase "higher-order result" (rejects (source.setDecl 4 (rootDecl (.sort .zero))))
  checkCase "absent type argument" (rejects (source.setDecl 4 (rootDecl (.const 1 []))))
  checkCase "out-of-scope typeSort" (rejects (source.setDecl 4 (rootDecl (app (.const 1 [.var 0]) (.const 0 [])))))
  checkCase "indexed family" (rejects (source.setDecl 1 (.induct true 0 1 1 (pi typeSort typeSort) [2, 3])))
  checkCase "duplicate source constructor" (rejects (source.setDecl 1 (.induct true 0 1 0 (pi typeSort typeSort) [2, 2])))
  checkCase "wrong parent" (rejects (source.setDecl 2 (.ctor true 0 0 0 1 0 (pi typeSort (seqTy (.var 0))))))
  checkCase "dependent field"
    (rejects (source.setDecl 3 (.ctor true 0 1 1 1 2
      (pi typeSort (pi (.var 0) (pi (.var 0) (seqTy (.var 2))))))))
  checkCase "higher-order field"
    (rejects (source.setDecl 3 (.ctor true 0 1 1 1 2
      (pi typeSort (pi (pi (.var 0) (.var 1)) (pi (seqTy (.var 1)) (seqTy (.var 2))))))))
  checkCase "dangling root index" (!Compilatrix.Recheck.Readback.closed expected (.ind 1))
  checkCase "dangling field index"
    (!Compilatrix.Recheck.Readback.closed { inds := [[ [.ind 1] ]] } (.ind 0))
  let candidate ← IO.ofExcept (Compilatrix.Recheck.Readback.discoverRaw source cfg 4)
  let validate := Compilatrix.Recheck.Readback.valid source cfg 4
  checkCase "independent candidate validation" (validate candidate)
  checkCase "wrong candidate root" (!validate { candidate with root := .nat })
  checkCase "wrong candidate result type" (!validate { candidate with ty := .nat })
  checkCase "wrong candidate field types"
    (!validate { candidate with sig := { inds := [[[], [.ind 0, .nat]]] } })
  checkCase "missing candidate instance" (!validate { candidate with shapes := [] })
  checkCase "duplicate candidate instance"
    (!validate { candidate with shapes := candidate.shapes ++ candidate.shapes })
  let exhaustedRows : List Compilatrix.Recheck.Readback.Row :=
    List.replicate 128 { shape := .nat }
  checkCase "global instance budget"
    (match (Compilatrix.Recheck.Readback.lower source cfg.ctors 128 (.ind 1 [] [.nat])).run exhaustedRows with
     | .error "signature instance budget" => true
     | _ => false)
  checkCase "recursive discovery depth budget"
    (match (Compilatrix.Recheck.Readback.lower source cfg.ctors 0 (.ind 1 [] [.nat])).run [] with
     | .error "signature discovery budget" => true
     | _ => false)
  IO.println "readback discovery: 27 assertions passed"
  return 27

end CompilatrixTests.Recheck.Readback
