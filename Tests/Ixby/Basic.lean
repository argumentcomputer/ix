module
import Ix.Ixby
meta import Ix.Ixby

namespace Tests.Ixby.Basic

open Ix.Ixby

private def nv (n : Nat) : Value := .scalar (.nat n)
private def bv (b : Bool) : Value := .scalar (.bool b)
private def sv (s : String) : Value := .scalar (.str s)
private def lit (n : Nat) : Operand := .literal (.nat n)
private def fn (arity : Nat) (blocks : Array Block) : Function := { arity, blocks }
private def single (arity : Nat) (blocks : Array Block) : Program :=
  { functions := #[fn arity blocks] }

private def accepts (program : Program) (input : Array Value) (output : Value)
    (fuel := 1000) (limits : Limits := {}) : Bool :=
  match execute limits program input fuel with
  | .ok actual => actual == output
  | .error _ => false

private def rejects (program : Program) (input : Array Value) (error : Error)
    (fuel := 1000) (limits : Limits := {}) : Bool :=
  match execute limits program input fuel with
  | .error actual => actual == error
  | .ok _ => false

private def literalProgram (value : Scalar) : Program :=
  single 0 #[⟨0, .ret (.literal value)⟩]

private def identityProgram : Program := single 1 #[⟨1, .ret (.local 0)⟩]

private def primitiveProgram (primitive : Primitive) : Program :=
  single primitive.arity #[
    ⟨primitive.arity, .letOp (.primitive primitive
      ((List.range primitive.arity).map Operand.local)) 1⟩,
    ⟨primitive.arity + 1, .ret (.local primitive.arity)⟩]

private def pairId : CtorId := { block := 1, tag := 0 }
private def otherId : CtorId := { block := 2, tag := 0 }
private def memberId : CtorId := { block := 1, member := 1, tag := 0 }
private def pairDecl : CtorDecl := { id := pairId, fields := 2 }

private def pair (a b : Nat) : Value := .ctor pairId #[nv a, nv b]

/-- Calls another function, branches on a runtime argument, and constructs a
two-field result. This is a kernel-checked example, not Compilatrix output. -/
def pairProgram : Program := {
  constructors := #[pairDecl]
  functions := #[
    fn 1 #[⟨1, .letOp (.call 1 [.local 0]) 1⟩, ⟨2, .ret (.local 1)⟩],
    fn 1 #[
      ⟨1, .branch (.local 0) 1 2⟩,
      ⟨1, .letOp (.construct 0 [lit 7, lit 11]) 3⟩,
      ⟨1, .letOp (.construct 0 [lit 11, lit 7]) 3⟩,
      ⟨2, .ret (.local 1)⟩]]
}

private def callerLocals : Program := {
  functions := #[
    fn 1 #[
      ⟨1, .letOp (.copy (lit 999)) 1⟩,
      ⟨2, .letOp (.call 1 [.local 0]) 2⟩,
      ⟨3, .letOp (.primitive .natAdd [.local 1, .local 2]) 3⟩,
      ⟨4, .ret (.local 3)⟩],
    fn 1 #[⟨1, .ret (.local 0)⟩]]
}

private def factorial : Program := single 1 #[
  ⟨1, .caseNat (.local 0) 1 2⟩,
  ⟨1, .ret (lit 1)⟩,
  ⟨2, .letOp (.callSelf [.local 1]) 3⟩,
  ⟨3, .letOp (.primitive .natMul [.local 0, .local 2]) 4⟩,
  ⟨4, .ret (.local 3)⟩]

private def tailFactorial : Program := single 2 #[
  ⟨2, .caseNat (.local 0) 1 2⟩,
  ⟨2, .ret (.local 1)⟩,
  ⟨3, .letOp (.primitive .natMul [.local 0, .local 1]) 3⟩,
  ⟨4, .tailCallSelf [.local 2, .local 3]⟩]

private def parity : Program := {
  functions := #[
    fn 1 #[
      ⟨1, .caseNat (.local 0) 1 2⟩,
      ⟨1, .ret (.literal (.bool true))⟩,
      ⟨2, .tailCall 1 [.local 1]⟩],
    fn 1 #[
      ⟨1, .caseNat (.local 0) 1 2⟩,
      ⟨1, .ret (.literal (.bool false))⟩,
      ⟨2, .tailCall 0 [.local 1]⟩]]
}

private def addFunction : Function := fn 2 #[
  ⟨2, .letOp (.primitive .natAdd [.local 0, .local 1]) 1⟩,
  ⟨3, .ret (.local 2)⟩]

private def capturedAddition : Program := {
  functions := #[
    fn 0 #[
      ⟨0, .letOp (.closure 1 [lit 20]) 1⟩,
      ⟨1, .letOp (.apply (.local 0) [lit 22]) 2⟩,
      ⟨2, .ret (.local 1)⟩],
    addFunction]
}

private def partialApplication : Program := {
  functions := #[
    fn 0 #[
      ⟨0, .letOp (.closure 1 []) 1⟩,
      ⟨1, .letOp (.apply (.local 0) [lit 20]) 2⟩,
      ⟨2, .ret (.local 1)⟩],
    addFunction]
}

private def runtimeApplication : Program := {
  functions := #[
    fn 2 #[⟨2, .tailApply (.local 0) [.local 1]⟩],
    fn 1 #[⟨1, .ret (.local 0)⟩]]
}

private def overApplication : Program := {
  functions := #[
    fn 0 #[
      ⟨0, .letOp (.copy (lit 1000)) 1⟩,
      ⟨1, .letOp (.closure 1 []) 2⟩,
      ⟨2, .letOp (.apply (.local 1) [lit 20, lit 22]) 3⟩,
      ⟨3, .letOp (.primitive .natAdd [.local 0, .local 2]) 4⟩,
      ⟨4, .ret (.local 3)⟩],
    fn 1 #[
      ⟨1, .letOp (.closure 2 [.local 0]) 1⟩,
      ⟨2, .ret (.local 1)⟩],
    addFunction]
}

private def caseProgram : Program := {
  constructors := #[pairDecl, { id := otherId, fields := 2 },
    { id := memberId, fields := 2 }]
  functions := #[fn 1 #[
    ⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]⟩,
    ⟨3, .ret (.local 1)⟩,
    ⟨3, .ret (.local 2)⟩,
    ⟨3, .ret (lit 123)⟩]]
}

private def projectProgram (index : Nat) : Program := {
  constructors := #[pairDecl]
  functions := #[fn 1 #[
    ⟨1, .letOp (.project (.local 0) index) 1⟩,
    ⟨2, .ret (.local 1)⟩]]
}

private def infiniteTailCall : Program := single 0 #[⟨0, .tailCallSelf []⟩]

private def nilId : CtorId := { block := 3, tag := 0 }
private def consId : CtorId := { block := 3, tag := 1 }
private def listDecls : Array CtorDecl := #[
  { id := nilId, fields := 0 }, { id := consId, fields := 2 }]
private def nilValue : Value := .ctor nilId #[]
private def consValue (head : Nat) (tail : Value) : Value := .ctor consId #[nv head, tail]

private def sumList : Program := {
  constructors := listDecls
  functions := #[fn 2 #[
    ⟨2, .caseCtor (.local 0) [⟨0, 1⟩, ⟨1, 2⟩]⟩,
    ⟨2, .ret (.local 1)⟩,
    ⟨4, .letOp (.primitive .natAdd [.local 1, .local 2]) 3⟩,
    ⟨5, .tailCallSelf [.local 3, .local 4]⟩]]
}

private def checks : List (String × Bool) := [
  ("literal result", accepts (literalProgram (.nat 42)) #[] (nv 42) 2),
  ("successful execution tolerates extra fuel",
    accepts (literalProgram (.nat 42)) #[] (nv 42) 200),
  ("terminal return consumes fuel",
    rejects (literalProgram (.nat 42)) #[] .outOfFuel 1),
  ("zero fuel never accepts",
    rejects (literalProgram (.nat 42)) #[] .outOfFuel 0),
  ("input locals are initialized", accepts identityProgram #[nv 71] (nv 71)),
  ("nonzero program entry",
    accepts { entry := 1, functions := #[
      fn 0 #[⟨0, .ret (lit 7)⟩], fn 0 #[⟨0, .ret (lit 42)⟩]] } #[] (nv 42)),
  ("nonzero block entry",
    accepts { functions := #[{ arity := 0, entry := 1, blocks := #[
      ⟨0, .ret (lit 7)⟩, ⟨0, .ret (lit 42)⟩] }] } #[] (nv 42)),
  ("direct call and constructed output, true",
    accepts pairProgram #[bv true] (pair 7 11) 7),
  ("direct call and constructed output, false",
    accepts pairProgram #[bv false] (pair 11 7) 7),
  ("calls and returns cannot bypass the fuel budget",
    rejects pairProgram #[bv true] .outOfFuel 6),
  ("return restores caller function and locals", accepts callerLocals #[nv 7] (nv 1006)),
  ("zero-arity direct call",
    accepts { functions := #[
      fn 0 #[⟨0, .letOp (.call 1 []) 1⟩, ⟨1, .ret (.local 0)⟩],
      fn 0 #[⟨0, .ret (lit 17)⟩]] } #[] (nv 17)),
  ("non-tail recursion, base", accepts factorial #[nv 0] (nv 1)),
  ("non-tail recursion, inductive", accepts factorial #[nv 6] (nv 720)),
  ("Nat does not silently wrap at 32 bits",
    accepts factorial #[nv 13] (nv 6227020800)),
  ("tail recursion needs no continuation frame",
    accepts tailFactorial #[nv 8, nv 1] (nv 40320) 1000 { continuations := 0 }),
  ("non-tail calls obey continuation capacity",
    rejects factorial #[nv 1] (.limit .continuations) 1000 { continuations := 0 }),
  ("mutual calls use the correct current function, even",
    accepts parity #[nv 12] (bv true) 1000 { continuations := 0 }),
  ("mutual calls use the correct current function, odd",
    accepts parity #[nv 13] (bv false) 1000 { continuations := 0 }),
  ("infinite tail calls do not manufacture a result",
    rejects infiniteTailCall #[] .outOfFuel 100),
  ("zero-field constructor creation",
    accepts { constructors := listDecls, functions := #[fn 0 #[
      ⟨0, .letOp (.construct 0 []) 1⟩, ⟨1, .ret (.local 0)⟩]] } #[] nilValue),
  ("empty-list constructor case", accepts sumList #[nilValue, nv 0] (nv 0)),
  ("recursive immutable list traversal uses tags and field order",
    accepts sumList #[consValue 1 (consValue 2 (consValue 3 nilValue)), nv 0]
      (nv 6) 1000 { continuations := 0 }),
  ("closure capture order", accepts capturedAddition #[] (nv 42)),
  ("under-application returns an immutable PAP",
    accepts partialApplication #[] (.pap 1 #[nv 20])),
  ("validated higher-order input",
    accepts runtimeApplication #[.pap 1 #[], nv 42] (nv 42)),
  ("tail application avoids a caller-resume frame",
    accepts runtimeApplication #[.pap 1 #[], nv 42] (nv 42) 1000 { continuations := 0 }),
  ("over-application runs before caller resumption",
    accepts overApplication #[] (nv 1042)),
  ("over-application frames count toward capacity",
    rejects overApplication #[] (.limit .continuations) 1000 { continuations := 1 }),
  ("empty application is identity",
    accepts (single 0 #[⟨0, .tailApply (lit 42) []⟩]) #[] (nv 42)),
  ("erased values absorb application",
    accepts (single 0 #[⟨0, .tailApply .erased [lit 42]⟩]) #[] .erased),
  ("non-function application fails",
    rejects (single 0 #[⟨0, .tailApply (lit 42) [lit 1]⟩]) #[] .notFunction),
  ("constructor branch appends fields in order",
    accepts caseProgram #[pair 7 11] (nv 7)),
  ("constructor dispatch checks the declaration digest",
    accepts caseProgram #[.ctor otherId #[nv 7, nv 11]] (nv 11)),
  ("constructor dispatch checks the inductive member",
    accepts caseProgram #[.ctor memberId #[nv 7, nv 11]] (nv 123)),
  ("projection reads immutable fields", accepts (projectProgram 1) #[pair 7 11] (nv 11)),
  ("projection bounds are checked",
    rejects (projectProgram 2) #[pair 7 11] (.invalidProjection 2)),
  ("erased values absorb projection",
    accepts (projectProgram 0) #[.erased] .erased),
  ("projection from a scalar fails",
    rejects (projectProgram 0) #[nv 1] .notConstructor),
  ("non-constructor case fails", rejects caseProgram #[nv 7] .notConstructor),
  ("constructor case need not be exhaustive but missing cases fail",
    rejects { caseProgram with functions := #[fn 1 #[
      ⟨1, .caseCtor (.local 0) [⟨0, 1⟩]⟩, ⟨3, .ret (.local 1)⟩]] }
      #[.ctor otherId #[nv 7, nv 11]] (.missingCase otherId)),
  ("Nat case rejects Bool representation", rejects factorial #[bv false] .notNat),
  ("Bool branch rejects numeric truthiness", rejects pairProgram #[nv 1] .notBool),
  ("large exact Nat addition",
    accepts (primitiveProgram .natAdd) #[nv (2^32 - 1), nv 1] (nv (2^32))),
  ("Nat subtraction truncates at zero",
    accepts (primitiveProgram .natSub) #[nv 2, nv 9] (nv 0)),
  ("Nat division", accepts (primitiveProgram .natDiv) #[nv 19, nv 4] (nv 4)),
  ("Nat division by zero is explicit",
    accepts (primitiveProgram .natDiv) #[nv 19, nv 0] (nv 0)),
  ("Nat modulus", accepts (primitiveProgram .natMod) #[nv 19, nv 4] (nv 3)),
  ("Nat modulus by zero is explicit",
    accepts (primitiveProgram .natMod) #[nv 19, nv 0] (nv 19)),
  ("Nat equality returns Bool", accepts (primitiveProgram .natEq) #[nv 7, nv 7] (bv true)),
  ("Nat inequality returns Bool", accepts (primitiveProgram .natEq) #[nv 7, nv 8] (bv false)),
  ("Nat comparison", accepts (primitiveProgram .natLt) #[nv 7, nv 8] (bv true)),
  ("primitive types are checked",
    rejects (primitiveProgram .natAdd) #[bv true, nv 1] (.primitiveType .natAdd)),
  ("string append", accepts (primitiveProgram .strAppend) #[sv "Ix", sv "By"] (sv "IxBy")),
  ("string length counts Unicode scalars",
    accepts (primitiveProgram .strLength) #[sv "λ🙂"] (nv 2)),
  ("string equality", accepts (primitiveProgram .strEq) #[sv "λ", sv "λ"] (bv true)),
  ("empty image is rejected",
    rejects { functions := #[] } #[] (.invalidFunction 0)),
  ("invalid entry function",
    rejects { identityProgram with entry := 9 } #[nv 0] (.invalidFunction 9)),
  ("empty function is rejected",
    rejects (single 0 #[]) #[] (.invalidBlock 0 0)),
  ("invalid entry block",
    rejects { functions := #[{ arity := 0, entry := 9, blocks := #[⟨0, .ret (lit 1)⟩] }] }
      #[] (.invalidBlock 0 9)),
  ("entry arity mismatch", rejects identityProgram #[] (.arityMismatch 1 0)),
  ("entry frame contract mismatch",
    rejects (single 1 #[⟨0, .ret (lit 1)⟩]) #[nv 7] (.invalidBlock 0 0)),
  ("forward local reference is rejected",
    rejects (single 0 #[⟨0, .ret (.local 0)⟩]) #[] (.invalidInstruction 0 0)),
  ("unreachable malformed block is rejected",
    rejects (single 0 #[⟨0, .ret (lit 1)⟩, ⟨0, .ret (.local 0)⟩])
      #[] (.invalidInstruction 0 1)),
  ("unused malformed function is rejected",
    rejects { functions := #[
      fn 0 #[⟨0, .ret (lit 1)⟩], fn 0 #[⟨0, .ret (.local 0)⟩]] }
      #[] (.invalidInstruction 1 0)),
  ("let successor must have one additional local",
    rejects (single 0 #[⟨0, .letOp (.copy (lit 1)) 1⟩, ⟨0, .ret (lit 2)⟩])
      #[] (.invalidInstruction 0 0)),
  ("invalid let successor",
    rejects (single 0 #[⟨0, .letOp (.copy (lit 1)) 9⟩]) #[] (.invalidInstruction 0 0)),
  ("both Bool branch targets are validated",
    rejects (single 1 #[⟨1, .branch (.local 0) 0 9⟩]) #[bv true] (.invalidInstruction 0 0)),
  ("Nat successor binding is validated even on zero",
    rejects (single 1 #[⟨1, .caseNat (.local 0) 1 1⟩, ⟨1, .ret (lit 0)⟩])
      #[nv 0] (.invalidInstruction 0 0)),
  ("unknown direct callee",
    rejects (single 0 #[⟨0, .tailCall 9 []⟩]) #[] (.invalidInstruction 0 0)),
  ("direct calls require exact arity",
    rejects (single 1 #[⟨1, .tailCallSelf []⟩]) #[nv 0] (.invalidInstruction 0 0)),
  ("closure capture count must be below arity",
    rejects (single 1 #[
      ⟨1, .letOp (.closure 0 [.local 0]) 1⟩, ⟨2, .ret (.local 1)⟩])
      #[nv 0] (.invalidInstruction 0 0)),
  ("zero-arity functions cannot be unsaturated PAPs",
    rejects (single 0 #[⟨0, .letOp (.closure 0 []) 1⟩, ⟨1, .ret (.local 0)⟩])
      #[] (.invalidInstruction 0 0)),
  ("primitive arity is checked before execution",
    rejects (single 0 #[
      ⟨0, .letOp (.primitive .natAdd [lit 1]) 1⟩, ⟨1, .ret (.local 0)⟩])
      #[] (.invalidInstruction 0 0)),
  ("unknown constructor is rejected",
    rejects (single 0 #[⟨0, .letOp (.construct 0 []) 1⟩, ⟨1, .ret (.local 0)⟩])
      #[] (.invalidInstruction 0 0)),
  ("constructor field count is validated",
    rejects { constructors := #[pairDecl], functions := #[fn 0 #[
      ⟨0, .letOp (.construct 0 [lit 1]) 1⟩, ⟨1, .ret (.local 0)⟩]] }
      #[] (.invalidInstruction 0 0)),
  ("duplicate constructor identities are rejected",
    rejects { pairProgram with constructors := #[pairDecl, pairDecl] }
      #[bv true] (.duplicateConstructor pairId)),
  ("duplicate constructor alternatives are rejected",
    rejects { caseProgram with functions := #[fn 1 #[
      ⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨0, 1⟩]⟩, ⟨3, .ret (.local 1)⟩]] }
      #[pair 7 11] (.invalidInstruction 0 0)),
  ("input constructor identity must be declared",
    rejects identityProgram #[pair 7 11] .invalidValue),
  ("input constructor arity is checked",
    rejects caseProgram #[.ctor pairId #[nv 7]] .invalidValue),
  ("input PAP function is checked",
    rejects runtimeApplication #[.pap 99 #[], nv 1] (.invalidFunction 99)),
  ("saturated input PAP is rejected",
    rejects runtimeApplication #[.pap 1 #[nv 1], nv 2] (.invalidClosure 1)),
  ("nested input values are validated",
    rejects { identityProgram with constructors := #[pairDecl] }
      #[.ctor pairId #[nv 1, .pap 99 #[]]] (.invalidFunction 99)),
  ("function capacity",
    rejects identityProgram #[nv 1] (.limit .functions) 1000 { functions := 0 }),
  ("constructor capacity",
    rejects pairProgram #[bv true] (.limit .constructors) 1000 { constructors := 0 }),
  ("block capacity",
    rejects pairProgram #[bv true] (.limit .blocks) 1000 { blocks := 1 }),
  ("entry local capacity",
    rejects identityProgram #[nv 1] (.limit .locals) 1000 { locals := 0 }),
  ("bound local capacity",
    rejects (primitiveProgram .natAdd) #[nv 1, nv 2] (.invalidInstruction 0 1)
      1000 { locals := 2 }),
  ("operand capacity",
    rejects identityProgram #[nv 1] (.limit .operands) 1000 { operands := 0 }),
  ("zero input-node budget accepts an empty forest",
    accepts (literalProgram (.bool true)) #[] (bv true) 2 { inputNodes := 0 }),
  ("input node budget covers siblings",
    rejects (single 2 #[⟨2, .ret (.local 0)⟩]) #[nv 1, nv 2] (.limit .inputNodes)
      1000 { inputNodes := 1 }),
  ("input node budget covers nested fields",
    rejects { identityProgram with constructors := #[pairDecl] } #[pair 1 2]
      (.limit .inputNodes) 1000 { inputNodes := 2 }),
  ("exact input-node boundary succeeds",
    accepts { identityProgram with constructors := #[pairDecl] } #[pair 1 2]
      (pair 1 2) 1000 { inputNodes := 3 }),
  ("input Nat bit capacity",
    rejects identityProgram #[nv 256] (.limit .natBits) 1000 { natBits := 8 }),
  ("primitive result Nat bit capacity",
    rejects (primitiveProgram .natAdd) #[nv 255, nv 1] (.limit .natBits)
      1000 { natBits := 8 }),
  ("oversized literal rejected during image admission",
    rejects (literalProgram (.nat 256)) #[] (.invalidInstruction 0 0)
      1000 { natBits := 8 }),
  ("zero fits a zero-bit Nat capacity",
    accepts identityProgram #[nv 0] (nv 0) 1000 { natBits := 0 }),
  ("input string capacity counts UTF-8 bytes",
    rejects identityProgram #[sv "λ🙂"] (.limit .stringBytes)
      1000 { stringBytes := 5 }),
  ("primitive result string capacity",
    rejects (primitiveProgram .strAppend) #[sv "A", sv "B"] (.limit .stringBytes)
      1000 { stringBytes := 1 }),
  ("intermediate step detects a malformed frame",
    match step {} identityProgram { control := .eval {
      function := 0, block := 0, locals := #[] } } with
    | .error (.frameSize 1 0) => true
    | _ => false)
]

-- A small source observation with a real call/constructor target. The theorem
-- quantifies over both runtime inputs; it does not claim an IxIR₀/Compilatrix
-- bridge. Canonical input/output bytes and hash binding remain unimplemented.
def sourcePair (choose : Bool) : Nat × Nat := if choose then (7, 11) else (11, 7)

def pairValue (choose : Bool) : Value := if choose then pair 7 11 else pair 11 7

def pairABI : ABI Bool (Nat × Nat) where
  encodeInput choose := #[bv choose]
  decodeOutput
    | .ctor id fields =>
      if id == pairId then
        match fields.toList with
        | [.scalar (.nat a), .scalar (.nat b)] => some (a, b)
        | _ => none
      else none
    | _ => none

theorem pair_evaluates (choose : Bool) :
    Evaluates {} pairProgram #[bv choose] (pairValue choose) := by
  cases choose <;> exact ⟨7, rfl⟩

theorem pair_compiler_certified :
    CompilerCertified (fun (_source : Unit) input result => result = sourcePair input)
      (fun (_source : Unit) program => program = pairProgram) {} pairABI := by
  intro source program compiled input value executed
  subst program
  have equal := evaluates_deterministic executed (pair_evaluates input)
  refine ⟨sourcePair input, ?_, rfl⟩
  rw [equal]
  cases input <;> rfl

theorem pair_composition_example : (7, 11) = sourcePair true :=
  certified_execution pair_compiler_certified
    (source := ()) (input := true) rfl (pair_evaluates true) rfl

theorem forward_alone_is_insufficient :
    (∀ (_input : Bool) (_result : Nat × Nat), False →
      Evaluates {} pairProgram #[bv false] (pairValue false)) ∧
    ¬ExecutionRefinement (fun (_ : Unit) (_ : Bool) (_ : Nat × Nat) => False)
      () {} pairProgram pairABI := by
  constructor
  · intro _ _ impossible; exact False.elim impossible
  · intro reflects
    obtain ⟨_, _, impossible⟩ := reflects false (pairValue false) (pair_evaluates false)
    exact impossible

#guard checks.all (·.2)

public def suite : IO UInt32 := do
  IO.println "ixby (functional reference bytecode)"
  let mut failed := 0
  for (name, passed) in checks do
    if passed then IO.println s!"  ✓ {name}"
    else
      failed := failed + 1
      IO.eprintln s!"  ✗ {name}"
  IO.println s!"{checks.length - failed}/{checks.length} checks passed"
  return if failed == 0 then 0 else 1

end Tests.Ixby.Basic
