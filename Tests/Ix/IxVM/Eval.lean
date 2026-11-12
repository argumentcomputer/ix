module
public import Ix.IxVM.ClaimHarness
public import Tests.Ix.IxVM.Harness
public import LSpec
public import Ix.Meta
public import Ix.CompileCertified
public import Ix.Commit
public import Ix.IxEval

/-!
  IxVM evaluation claim tests (`Tests.Ix.IxVM.Eval`).
-/

public section
namespace Tests.Ix.IxVM.Eval

open LSpec IxVM.ClaimHarness

private def idType : Ixon.Expr :=
  .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
private def idValue : Ixon.Expr :=
  .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))

private def definition (ty value : Ixon.Expr) (refs : Array Address := #[])
    (lvls : UInt64 := 0) (univs : Array Ixon.Univ := #[.zero]) : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, lvls, ty, value⟩, #[], refs, univs, #[]⟩

private def withValue (c : Ixon.Constant) (value : Ixon.Expr) : Ixon.Constant :=
  match c.info with
  | .defn d => { c with info := .defn { d with value } }
  | _ => c

private def storeConstant (env : Ixon.Env) (c : Ixon.Constant) : Ixon.Env × Address :=
  let addr := Address.blake3 (Ixon.ser c)
  let env := env.storeConst addr c
  ({ env with anonHints := env.anonHints.insert addr (.regular 0) }, addr)

private def storeDef (env : Ixon.Env) (ty value : Ixon.Expr)
    (refs : Array Address := #[]) (lvls : UInt64 := 0)
    (univs : Array Ixon.Univ := #[.zero]) : Ixon.Env × Address :=
  storeConstant env (definition ty value refs lvls univs)

private def idOutput := definition idType idValue

/-- The claims' context: the default role table's. -/
private def evalCtx : Ix.ClaimContext :=
  Ix.ClaimContext.ofDefaultTable.toOption.getD default

private def witness (env : Ixon.Env) (input : Address) (out : Ixon.Constant)
    (tree : Option Ix.AssumptionTree := none) : IO ClaimWitness := do
  let (env, output) := storeConstant env out
  let trees := match tree with
    | none => {}
    | some t => ({} : Std.HashMap Address Ix.AssumptionTree).insert t.root t
  -- the hand-built records get their binder-data sections first, as the compiler writes them
  IO.ofExcept (Tests.Ix.IxVM.buildSectionedWitness env (.eval evalCtx input output (tree.map (·.root))) trees)

/-- Exact whole-claim FFT costs for successful evaluations. -/
private def evalFftCosts : List (String × Nat) := [
  ("identity", 182_991_056),
  ("beta", 183_950_958),
  ("zeta", 183_820_705),
  ("reduction under lambda", 183_885_094),
  ("delta", 185_017_427),
  ("theorem body", 183_992_108),
  ("opaque body", 183_992_108),
  ("mutual definition projection", 184_663_761),
  ("assumed dependency still unfolds", 185_712_994),
  ("input type need not be normalized", 184_060_074),
  ("universe-polymorphic normalization", 183_999_755),
  ("open sharing under binder", 185_072_767),
  ("normalization in lambda domain", 183_896_483),
  ("normalization in Pi domain and dependent codomain", 183_870_275),
  ("capture-avoiding beta under nested binders", 184_188_684),
  ("preserves theorem reference", 184_092_792),
  ("preserves opaque reference", 184_184_441),

  ("Tests.Ix.IxVM.Eval.Fixtures.arithmetic", 344_077_283),
  ("Tests.Ix.IxVM.Eval.Fixtures.listResult", 352_364_553),
  ("Tests.Ix.IxVM.Eval.Fixtures.recurResult", 397_415_167),
  ("Tests.Ix.IxVM.Eval.Fixtures.projResult", 214_259_848),
  ("Tests.Ix.IxVM.Eval.Fixtures.stringResult", 5_762_283_167),
  ("command claim after bundle transport", 337_975_459),

  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.indexedZip", 1_542_801_029),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.dependentBuild", 652_737_798),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.mutualEven", 418_332_116),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.mutualOdd", 416_429_156),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.nestedTree", 833_333_389),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.higherOrder", 529_301_277),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.largeArithmetic", 2_447_835_360),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.limbPredecessor", 227_491_969),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.dependentCast", 627_851_104),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.neutralApplication", 185_818_049),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.neutralProjection", 194_848_800),
  ("Lean differential: Tests.Ix.IxVM.Eval.Fixtures.dependentProjection", 308_385_414),
  ("well-founded recursion through accessibility proofs", 1_808_816_240),
  ("compact symbolic Nat offset beyond 32 bits", 271_588_026),
  ("symbolic Nat addition exposes zero after argument reduction", 327_132_321),

  ("generated arithmetic 0, seed 1230526029", 4_038_417_017),
  ("generated arithmetic 1, seed 5227010138933557030", 4_044_180_264),
  ("generated arithmetic 2, seed 9740023657447289539", 4_049_843_008),
  ("generated arithmetic 3, seed 312873973889897908", 4_041_227_736),
  ("generated arithmetic 4, seed 14324766925872067785", 4_042_513_785),
  ("generated arithmetic 5, seed 5865597085624116754", 4_050_488_114),
  ("generated arithmetic 6, seed 8838574616595545567", 4_039_535_746),
  ("generated arithmetic 7, seed 5951150478550409152", 4_046_084_789),
  ("generated arithmetic 8, seed 13867390926732686213", 4_037_150_893),
  ("generated arithmetic 9, seed 3876320172222402110", 4_047_879_940),
  ("generated arithmetic 10, seed 9199945194732150587", 4_046_798_450),
  ("generated arithmetic 11, seed 13341985934152315148", 4_034_922_996),
  ("generated arithmetic 12, seed 16617329689835589249", 4_010_702_864),
  ("generated arithmetic 13, seed 88728717077797802", 3_997_599_633),
  ("generated arithmetic 14, seed 1948624928862008023", 4_041_122_021),
  ("generated arithmetic 15, seed 6240852391080220056", 4_045_806_809),
  ("generated arithmetic 16, seed 15042951194288734653", 3_999_675_322),
  ("generated arithmetic 17, seed 6069444241543887446", 2_437_794_249),
  ("generated arithmetic 18, seed 9883539672627336371", 4_044_148_606),
  ("generated arithmetic 19, seed 4057147670932478308", 3_669_497_845),
  ("generated arithmetic 20, seed 5561980989402630457", 4_003_165_744),
  ("generated arithmetic 21, seed 215210223919765058", 4_045_725_211),
  ("generated arithmetic 22, seed 7293824100597899471", 2_435_028_837),
  ("generated arithmetic 23, seed 2714453358506657904", 3_667_968_808),
]

/-- Every accepted evaluation must have an exact FFT pin. Rejections are
checked by verdict and error; a missing acceptance pin fails the suite. -/
private def execute (name : String) (w : ClaimWitness) (error : Option String := none) :
    Except String Tests.Ix.IxVM.Case := do
  let expectedFftCost : Option Nat ← if error.isNone then
      match evalFftCosts.lookup name with
      | some cost => pure (some cost)
      | none => throw s!"missing evaluation FFT pin: {name}"
    else pure none
  return {
    label := s!"eval {if error.isNone then "accepts" else "rejects"} {name}"
    accept := error.isNone
    rejectsWith := error.bind fun e => if e.isEmpty then none else some e
    expectedFftCost
    witness := w }

-- Bypass host parsing so malformed and unauthenticated constants reach Aiur.
private def rawWitness (env : Ixon.Env) (input : Address) (bytes : ByteArray)
    (outputKey : Option Address := none) : ClaimWitness :=
  let output := outputKey.getD (Address.blake3 bytes)
  let claimBytes := Ix.Claim.ser (.eval evalCtx input output none)
  let digest := packedDigestKey (Address.blake3 claimBytes)
  -- The claim's context names the default table, which the circuit reads
  -- before anything else.
  let env := match withDefaultRoleBinding env with
    | .ok bound => bound
    | .error _ => env
  let io := addEntries env (fun _ => true) (seedBinding env default)
  let io := io.extend 0 digest (claimBytes.data.map .ofUInt8)
  let io := io.extend 2 (output.hash.data.map Aiur.G.ofUInt8) (bytes.data.map .ofUInt8)
  { funcName := `verify_claim, input := digest, inputIOBuffer := io }

def tests (r : Tests.Ix.IxVM.Runner) : IO Unit := do
  let beta := Ixon.Expr.app (.leanLam idType (.var 0)) idValue
  let underBinder := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (.var 0) (.app (.leanLam (.var 1) (.var 0)) (.var 0)))
  for (label, value) in [
      ("identity", idValue), ("beta", beta),
      ("zeta", Ixon.Expr.leanLet false idType idValue (.var 0)),
      ("reduction under lambda", underBinder)] do
    let (env, input) := storeDef {} idType value
    r.build <| execute label (← witness env input idOutput)
  let (env, dep) := storeDef {} idType beta
  let (env, input) := storeDef env idType (.ref 0 #[]) #[dep]
  r.build <| execute "delta" (← witness env input idOutput)
  let (axiomEnv, axiomInput) := storeConstant {} { idOutput with info := .axio ⟨false, 0, idType⟩ }
  r.build <| execute "input without a body"
    (← witness axiomEnv axiomInput idOutput) (some "")
  for (label, kind) in [("theorem body", Ix.DefKind.thm), ("opaque body", .opaq)] do
    let c : Ixon.Constant := ⟨.defn ⟨kind, .safe, 0, idType, beta⟩, #[], #[], #[.zero], #[]⟩
    let (fixture, a) := storeConstant {} c
    let fixture := { fixture with anonHints := fixture.anonHints.insert a .opaque }
    r.build <| execute label (← witness fixture a idOutput)
    r.build <| execute s!"output must be an ordinary definition (input with a {label})"
      (← witness env input c) (some "output must be a definition")
  for safety in [Ix.DefinitionSafety.unsaf, .part] do
    let c : Ixon.Constant := ⟨.defn ⟨.defn, safety, 0, idType, idValue⟩, #[], #[], #[.zero], #[]⟩
    -- decided data on the subject (a prover's choice), so that the case reaches the safety check
    let (fixture, a) := storeConstant {} (← IO.ofExcept (Tests.Ix.IxVM.withSafeTwinSection {} c))
    r.build <| execute s!"{repr safety} subject" (← witness fixture a idOutput)
      (some "unsafe or partial")
    r.build <| execute s!"{repr safety} output" (← witness env input c)
      (some "unsafe or partial output")
  let block : Ixon.Constant :=
    ⟨.muts #[.defn ⟨.defn, .safe, 0, idType, beta⟩], #[], #[], #[.zero], #[]⟩
  let (fixture, ba) := storeConstant {} block
  let projection : Ixon.Constant := ⟨.dPrj ⟨0, ba⟩, #[], #[], #[], #[]⟩
  let (fixture, pa) := storeConstant fixture projection
  r.build <| execute "mutual definition projection" (← witness fixture pa idOutput)
  let tree := Ix.AssumptionTree.canonical #[dep] |>.get!
  r.build <| execute "assumed dependency still unfolds" (← witness env input idOutput tree)
  let selfTree := Ix.AssumptionTree.canonical #[input] |>.get!
  r.build <| execute "subject in assumptions" (← witness env input idOutput selfTree)
    (some "input is an assumption")
  r.build <| execute "wrong output" (← witness env input (withValue idOutput (.sort 0)))
    (some "result does not match")
  r.build <| execute "unreduced output" (← witness env input (withValue idOutput beta))
    (some "result does not match")
  r.build <| execute "universe count mismatch"
    (← witness env input (definition idType idValue #[] 1)) (some "universe parameter count")
  r.build <| execute "correct value with a false declared type"
    (← witness env input (definition (.sort 0) idValue)) (some "output type does not match")
  -- Convertible types are deliberately insufficient: preserve the input's type
  -- structurally, rather than silently changing the output wrapper's contract.
  let aliasTy := Ixon.Expr.leanLet false (.sort 0) idType (.var 0)
  r.build <| execute "convertible but different output type"
    (← witness env input (definition aliasTy idValue)) (some "output type does not match")
  let (aliasEnv, aliasInput) := storeDef {} aliasTy beta
  r.build <| execute "input type need not be normalized"
    (← witness aliasEnv aliasInput (definition aliasTy idValue))
  let (badEnv, badInput) := storeDef {} (.sort 0) idValue
  let w ← witness badEnv badInput (definition (.sort 0) idValue)
  r.build <| execute "ill-typed input with matching output"
    w (some "")
  let badSelf := Ix.AssumptionTree.canonical #[badInput] |>.get!
  r.build <| execute "assumptions cannot waive input typechecking"
    (← witness badEnv badInput idOutput badSelf) (some "")
  let (badEnv, badDep) := storeDef {} idType (.sort 0)
  let (badEnv, badInput) := storeDef badEnv idType (.ref 0 #[]) #[badDep]
  r.build <| execute "ill-typed transitive dependency"
    (← witness badEnv badInput (withValue idOutput (.sort 0))) (some "")
  -- The output declaration is checked as a `check` claim's target is. An
  -- assumed dependency is not checked, so the normal form of a well-typed
  -- input can be ill-typed: here `Prop`, from the assumed
  -- `redexDep : idType := (fun (x : Type) => x) Prop`. The output,
  -- `idType := Prop`, repeats the input's type and that normal form, so only
  -- its own check refuses it. (The dependency is a redex so that it is not
  -- the output itself, which would be an assumption.)
  let (redexEnv, redexDep) := storeDef {} idType (.app (.leanLam (.sort 1) (.var 0)) (.sort 0))
    #[] 0 #[.zero, .succ .zero]
  let (redexEnv, redexInput) := storeDef redexEnv idType (.ref 0 #[]) #[redexDep]
  let redexTree := Ix.AssumptionTree.canonical #[redexDep] |>.get!
  r.build <| execute "ill-typed output under an assumed dependency"
    (← witness redexEnv redexInput (withValue idOutput (.sort 0)) redexTree)
    (some "inferred type is not def-eq to the expected type")
  -- An assumed output would not be checked.
  let outputTree := Ix.AssumptionTree.canonical #[(storeConstant env idOutput).2] |>.get!
  r.build <| execute "output in assumptions" (← witness env input idOutput outputTree)
    (some "output is an assumption")
  let (polyEnv, polyInput) := storeDef {} idType underBinder #[] 1 #[.var 0]
  r.build <| execute "universe-polymorphic normalization"
    (← witness polyEnv polyInput (definition idType idValue #[] 1 #[.var 0]))
  let shared := { (withValue idOutput (.leanLam (.sort 0) (.leanLam (.var 0) (.share 0)))) with
    sharing := #[.var 0] }
  r.build <| execute "open sharing under binder" (← witness env input shared)
  let propLet := Ixon.Expr.leanLet false (.sort 1) (.sort 0) (.var 0)
  let (binderEnv, binderInput) := storeDef {} idType
    (.leanLam propLet (.leanLam (.var 0) (.var 0))) #[] 0 #[.zero, .succ .zero]
  r.build <| execute "normalization in lambda domain"
    (← witness binderEnv binderInput idOutput)
  let propBeta := fun p => Ixon.Expr.app (.leanLam (.sort 0) (.var 0)) p
  let pi := Ixon.Expr.leanAll propLet
    (.leanAll (propBeta (.var 0)) (propBeta (.var 1)))
  let (piEnv, piInput) := storeDef {} (.sort 0) pi #[] 0 #[.zero, .succ .zero]
  r.build <| execute "normalization in Pi domain and dependent codomain"
    (← witness piEnv piInput (definition (.sort 0) idType))
  let captureTy := Ixon.Expr.leanAll (.sort 0)
    (.leanAll (.var 0) (.leanAll (.var 1) (.var 2)))
  let captureBody := Ixon.Expr.leanLam (.sort 0) (.leanLam (.var 0)
    (.app (.leanLam (.var 1) (.leanLam (.var 2) (.var 1))) (.var 0)))
  let captureNF := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (.var 0) (.leanLam (.var 1) (.var 1)))
  let (captureEnv, captureInput) := storeDef {} captureTy captureBody
  r.build <| execute "capture-avoiding beta under nested binders"
    (← witness captureEnv captureInput (definition captureTy captureNF))
  let captured := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (.var 0) (.leanLam (.var 1) (.var 0)))
  r.build <| execute "captured variable with the same type"
    (← witness captureEnv captureInput (definition captureTy captured)) (some "result does not match")
  for (label, kind) in [("theorem reference", Ix.DefKind.thm), ("opaque reference", .opaq)] do
    let c : Ixon.Constant := ⟨.defn ⟨kind, .safe, 0, idType, idValue⟩, #[], #[], #[.zero], #[]⟩
    let (fixture, a) := storeConstant {} c
    let (fixture, b) := storeConstant fixture (withValue c beta)
    let fixture := { fixture with anonHints := fixture.anonHints.insert a .opaque |>.insert b .opaque }
    let (fixture, subject) := storeDef fixture idType (.ref 0 #[]) #[a]
    let expected := definition idType (.ref 0 #[]) #[a]
    r.build <| execute s!"preserves {label}" (← witness fixture subject expected)
    r.build <| execute s!"does not unfold {label}"
      (← witness fixture subject idOutput) (some "result does not match")
    r.build <| execute s!"does not replace {label} by an equivalent proof"
      (← witness fixture subject { expected with refs := #[b] }) (some "result does not match")
  for (name, c) in [
      ("free variable", withValue idOutput (.var 0)),
      ("bad ref", withValue idOutput (.ref 0 #[])),
      ("bad universe index", withValue idOutput (.sort 1)),
      ("bad universe parameter", { idOutput with univs := #[.var 0] }),
      ("relative Rec", withValue idOutput (.recur 0 #[])),
      ("free variable through sharing", { (withValue idOutput (.share 0)) with sharing := #[.var 0] }),
      ("output axiom", { idOutput with info := .axio ⟨false, 0, idType⟩ }),
      ("output projection", projection), ("output block", block)] do
    r.build <| execute name (rawWitness env input (Ixon.ser c)) (some "")
  -- the record with its section, as the compiler writes it, then one byte more: the case is
  -- about the trailing byte, not the binder data
  let outputBytes := Ixon.ser (← IO.ofExcept (_root_.IxVM.RecordSections.withSection env idOutput))
  r.build <| execute "trailing output bytes"
    (rawWitness env input (outputBytes.push 0)) (some "Ingress::load_verified_constant")
  for n in [:outputBytes.size] do
    r.build <| execute s!"truncated output at {n}"
      (rawWitness env input (outputBytes.extract 0 n)) (some "")
  let w ← witness env input idOutput
  let cb := Ix.Claim.ser (.eval evalCtx input (Address.blake3 outputBytes) none)
  for (label, bytes) in [
      ("wrong format", cb.set! 1 3), ("wrong validator", cb.set! 2 0),
      ("trailing claim bytes", cb.push 0)] do
    let digest := packedDigestKey (Address.blake3 bytes)
    let io := w.inputIOBuffer.extend 0 digest (bytes.data.map .ofUInt8)
    r.build <| execute label { w with input := digest, inputIOBuffer := io } (some "")
  r.build <| execute "unauthenticated output bytes"
    (rawWitness env input (Ixon.ser (withValue idOutput (.sort 0)))
      (some (Address.blake3 outputBytes))) (some "")

-- Ordinary compiled Lean programs exercise primitive, recursor, constructor,
-- projection, and literal paths with all dependencies checked.
namespace Fixtures
def arithmetic : Nat := 6 * 7
def fortyTwo : Nat := 42
def listResult : List Nat := [6 * 7, 10 + 2]
def listExpected : List Nat := [42, 12]
def recurResult : Nat := List.foldl Nat.add 0 [1, 2, 3]
def six : Nat := 6
def projResult : Nat := (7, 9).2
def nine : Nat := 9
def stringResult : String := (fun s => s) "hello"
def stringExpected : String := "hello"

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def Vec.map (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (xs.map f)

def Vec.zipWith (f : α → β → γ) : Vec α n → Vec β n → Vec γ n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (f x y) (xs.zipWith f ys)

def Vec.sum : Vec Nat n → Nat
  | .nil => 0
  | .cons x xs => x + xs.sum

def Vec.build : (n : Nat) → Vec Nat n
  | 0 => .nil
  | n + 1 => .cons (n + 1) (build n)

def indexedZip : Nat :=
  Vec.sum (Vec.zipWith Nat.mul
    (Vec.map (fun n => n + 1) (.cons 1 (.cons 2 (.cons 3 .nil))))
    (.cons 4 (.cons 5 (.cons 6 .nil))))
def dependentBuild : Nat := (Vec.build 6).sum

mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n
  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end
def mutualEven : Nat := if even 12 then 17 else 23
def mutualOdd : Nat := if even 11 then 17 else 23

inductive Rose where
  | node : Nat → List Rose → Rose

def Rose.totalWF : Rose → Nat
  | .node n children => n + (children.map Rose.totalWF).foldl Nat.add 0

noncomputable def Rose.total (t : Rose) : Nat :=
  Rose.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun n _ children => n + children) 0 (fun _ _ head tail => head + tail) t

def tree : Rose := .node 1 [.node 2 [.node 3 [], .node 4 []], .node 5 []]
noncomputable def nestedTree : Nat := tree.total
def wellFoundedTree : Nat := tree.totalWF

-- Explicit accessibility proof: unlike elaborator-generated general WF
-- recursion, this does not insert Lean.opaqueId around the proof.
noncomputable def transparentWF : Nat → Nat :=
  WellFounded.fix Nat.lt_wfRel.wf fun n recurse =>
    match n with
    | 0 => 0
    | k + 1 => (k + 1) + recurse k (Nat.lt_succ_self k)
noncomputable def wellFoundedSum : Nat := transparentWF 6

def higherOrder : Nat :=
  ([1, 2, 3, 4, 5].map (fun x => (fun f => f (x * x)) (fun n => n + 1))).foldl Nat.add 0

def largeArithmetic : Nat := ((4294967296 + 17) * 4294967299) / 7
def limbPredecessor : Nat := match (4294967296 : Nat) with | 0 => 7 | n + 1 => n

theorem threeEq : (1 + 2 : Nat) = 3 := rfl
def dependentCast : Nat :=
  (Eq.ndrec (motive := Vec Nat) (Vec.build (1 + 2)) threeEq).sum

def neutralApplication : (α : Type) → (α → α) → α → α :=
  fun α f x => f ((fun y : α => y) x)
def neutralProjection : Nat × Nat → Nat := fun p => (fun q : Nat × Nat => q.1) p
def dependentProjection : (p : Sigma (fun n => Vec Nat n)) → Vec Nat p.1 :=
  fun p => (fun q : Sigma (fun n => Vec Nat n) => q.2) p

def openOffset : Nat → Nat := fun n => Nat.add n (Nat.add 4294967296 17)
def openZero : Nat → Nat := fun n => Nat.add n (Nat.sub 7 7)
end Fixtures

private def natOutput (env : Ixon.Env) (n : Nat) : IO (Ixon.Env × Ixon.Constant) := do
  let nat ← lookupAddr env ``Nat
  let (env, addr) := env.storeBlob (ByteArray.mk (Nat.toBytesLE n))
  return (env, definition (.ref 0 #[]) (.nat 1) #[nat, addr] 0 #[])

private def listOutput (env : Ixon.Env) : IO (Ixon.Env × Ixon.Constant) := do
  let nat ← lookupAddr env ``Nat
  let consAddr ← lookupAddr env ``List.cons
  let nilAddr ← lookupAddr env ``List.nil
  let listAddr ← lookupAddr env ``List
  let (env, a) := env.storeBlob (ByteArray.mk (Nat.toBytesLE 42))
  let (env, b) := env.storeBlob (ByteArray.mk (Nat.toBytesLE 12))
  let ty := Ixon.Expr.ref 0 #[]
  let cons := Ixon.Expr.app (.ref 1 #[0]) ty
  let nil := Ixon.Expr.app (.ref 2 #[0]) ty
  let root := Ixon.Expr.app (.app cons (.nat 3)) (.app (.app cons (.nat 4)) nil)
  return (env, definition (.app (.ref 5 #[0]) ty) root
    #[nat, consAddr, nilAddr, a, b, listAddr])

def compiledTests (leanEnv : Lean.Environment) (r : Tests.Ix.IxVM.Runner) : IO Unit := do
  let pairs := #[
    (``Fixtures.arithmetic, ``Fixtures.fortyTwo),
    (``Fixtures.listResult, ``Fixtures.listExpected),
    (``Fixtures.recurResult, ``Fixtures.six),
    (``Fixtures.projResult, ``Fixtures.nine),
    (``Fixtures.stringResult, ``Fixtures.stringExpected)]
  let env ← loadSharedIxonEnv (pairs.flatMap (fun (a, b) => #[a, b]) ++ synthesizedPrimNames) leanEnv
  for (a, b) in pairs do
    let input ← lookupAddr env a
    let output ← lookupAddr env b
    let some c := env.getConst? output | throw <| IO.userError "missing fixture"
    let raw := c
    -- Lean numeral syntax elaborates to OfNat applications. Specify the
    -- expected normal forms independently, with actual literal nodes.
    let (fixture, obj) ←
      if b == ``Fixtures.fortyTwo then natOutput env 42
      else if b == ``Fixtures.six then natOutput env 6
      else if b == ``Fixtures.nine then natOutput env 9
      else if b == ``Fixtures.listExpected then listOutput env
      else pure (env, raw)
    r.build <| execute (toString a) (← witness fixture input obj)
    if a == ``Fixtures.arithmetic then
      r.build <| execute "unreduced OfNat output"
        (← witness env input raw) (some "result does not match")
      let (fixture, wrongObj) ← natOutput env 9
      r.build <| execute "wrong result with the same type"
        (← witness fixture input wrongObj) (some "result does not match")

private def compileClosure (leanEnv : Lean.Environment) (names : Array Lean.Name) :
    IO Ix.CompileM.CompilePhases := do
  let mut seen : Lean.NameSet := {}
  let mut entries := #[]
  for n in names ++ synthesizedPrimNames do
    for entry in Lean.collectDependencies n leanEnv.constants do
      unless seen.contains entry.1 do
        seen := seen.insert entry.1
        entries := entries.push entry
  Ix.CompileM.compilePhasesOf leanEnv entries.toList

private def compiledOutput (base : Ix.CompileM.CompileEnv) (env : Ixon.Env)
    (lvls : List Lean.Name) (ty value : Lean.Expr) : IO (Ixon.Env × Ixon.Constant) := do
  let (addr, cache) ← IO.ofExcept (Ix.Commit.compileDef base lvls ty value)
  let some bytes := cache.constants[addr]? | throw <| IO.userError "missing compiled output"
  let obj ← IO.ofExcept (Ixon.de bytes)
  return ({ env with blobs := cache.blobs }, obj)

/-- Independent Lean reduction supplies the expected terms, never IxVM's own
normalizer. Closed numeric examples additionally pin a hand-computed result.
Neutral terms deliberately avoid arithmetic, where Lean and IxVM choose
different representations for stuck primitives. -/
def difficultTests (leanEnv : Lean.Environment) (r : Tests.Ix.IxVM.Runner) : IO TestSeq := do
  let numeric : Array (Lean.Name × Nat) := #[
    (``Fixtures.indexedZip, 47), (``Fixtures.dependentBuild, 21),
    (``Fixtures.mutualEven, 17), (``Fixtures.mutualOdd, 23),
    (``Fixtures.nestedTree, 15), (``Fixtures.higherOrder, 60),
    (``Fixtures.largeArithmetic, ((4294967296 + 17) * 4294967299) / 7),
    (``Fixtures.limbPredecessor, 4294967295), (``Fixtures.dependentCast, 6)]
  let neutral := #[``Fixtures.neutralApplication, ``Fixtures.neutralProjection,
    ``Fixtures.dependentProjection]
  let phases ← compileClosure leanEnv
    (numeric.map Prod.fst ++ neutral ++
      #[``Fixtures.wellFoundedTree, ``Fixtures.wellFoundedSum,
        ``Fixtures.openOffset, ``Fixtures.openZero])
  let base := Ix.Commit.mkCompileEnv phases
  let env := phases.compileEnv
  let mut seq : TestSeq := .done
  for name in numeric.map Prod.fst ++ neutral do
    let some (.defnInfo info) := leanEnv.find? name
      | throw <| IO.userError s!"expected definition: {name}"
    let expected ← runMeta (Lean.Meta.withTransparency .all (Lean.Meta.reduceAll info.value)) leanEnv
    if let some (_, n) := numeric.find? (fun p => p.1 == name) then
      seq := seq ++ test s!"Lean oracle agrees with pinned result: {name}"
        (expected == .lit (.natVal n))
    let input ← lookupAddr env name
    let (fixture, obj) ← compiledOutput base env info.levelParams info.type expected
    r.build <| execute s!"Lean differential: {name}" (← witness fixture input obj)
    if let some (_, n) := numeric.find? (fun p => p.1 == name) then
      let (fixture, wrong) ← natOutput env (n + 1)
      r.build <| execute s!"incorrect result: {name}"
        (← witness fixture input wrong) (some "result does not match")
  -- The elaborator deliberately wraps this accessibility proof in opaqueId.
  -- A kernel-reduction claim must respect that boundary, even though native
  -- compilation can execute the function by erasing proofs.
  let input ← lookupAddr env ``Fixtures.wellFoundedTree
  let (fixture, output) ← natOutput env 15
  let opaqueId ← lookupAddr env ``Lean.opaqueId
  seq := seq ++ test "generated WF fixture contains the opaqueId dependency"
    ((closureFrom env input).contains opaqueId)
  r.build <| execute "opaque accessibility proof blocks kernel evaluation"
    (← witness fixture input output) (some "result does not match")
  -- This explicit proof does expose constructors to Acc.rec. Meta keeps its
  -- theorem heads opaque, so pin the independent triangular-number answer.
  let input ← lookupAddr env ``Fixtures.wellFoundedSum
  let (fixture, output) ← natOutput env 21
  r.build <| execute "well-founded recursion through accessibility proofs"
    (← witness fixture input output)
  let (fixture, wrong) ← natOutput env 22
  r.build <| execute "incorrect well-founded recursion result"
    (← witness fixture input wrong) (some "result does not match")
  -- Open Nat offset must remain compact; unfolding Nat.add's implementation
  -- here would expand billions of successors or leave a different normal form.
  let nat ← lookupAddr env ``Nat
  let add ← lookupAddr env ``Nat.add
  let (fixture, literal) := env.storeBlob (ByteArray.mk (Nat.toBytesLE 4294967313))
  let natArrow := Ixon.Expr.leanAll (.ref 0 #[]) (.ref 0 #[])
  let output := definition natArrow
    (.leanLam (.ref 0 #[]) (.app (.app (.ref 1 #[]) (.var 0)) (.nat 2)))
    #[nat, add, literal] 0 #[]
  let input ← lookupAddr env ``Fixtures.openOffset
  r.build <| execute "compact symbolic Nat offset beyond 32 bits"
    (← witness fixture input output)
  let input ← lookupAddr env ``Fixtures.openZero
  r.build <| execute "symbolic Nat addition exposes zero after argument reduction"
    (← witness env input (definition natArrow (.leanLam (.ref 0 #[]) (.var 0)) #[nat] 0 #[]))
  return seq

private structure GenState where
  seed : UInt64 := 0x4958564d
  coverage : Array Nat := Array.replicate 7 0

private def draw (bound : Nat) : StateM GenState Nat := do
  modify fun s => { s with seed := s.seed * 6364136223846793005 + 1442695040888963407 }
  return ((← get).seed >>> 32).toNat % bound

/-- Typed arithmetic terms with lexical binders. The second component is an
independent numeric interpretation; it does not inspect either reducer's output.
Fuel bounds term size, and successor denominators keep division nonzero. -/
private def genNat (fuel : Nat) (locals : List Nat) :
    StateM GenState (Lean.Expr × Nat) := do
  let nat := Lean.mkConst ``Nat
  match fuel with
  | 0 =>
    if !locals.isEmpty && (← draw 2) == 0 then
      let i ← draw locals.length
      return (.bvar i, locals[i]!)
    let n ← draw 17
    return (Lean.mkNatLit n, n)
  | fuel + 1 =>
    let mode ← draw 7
    modify fun s => { s with coverage := s.coverage.modify mode (· + 1) }
    let (a, av) ← genNat fuel locals
    if mode == 3 || mode == 4 then
      let (body, value) ← genNat fuel (av :: locals)
      if mode == 3 then
        return (.letE `x nat a body false, value)
      return (.app (.lam `x nat body .default) a, value)
    let (b, bv) ← genNat fuel locals
    let binary := fun name b => Lean.mkApp2 (Lean.mkConst name) a b
    match mode with
    | 0 => return (binary ``Nat.add b, av + bv)
    | 1 => return (binary ``Nat.mul b, av * bv)
    | 2 => return (binary ``Nat.sub b, av - bv)
    | 5 => return (binary ``Nat.div (Lean.mkApp (Lean.mkConst ``Nat.succ) b), av / (bv + 1))
    | _ => return (binary ``Nat.mod (Lean.mkApp (Lean.mkConst ``Nat.succ) b), av % (bv + 1))

def differentialTests (leanEnv : Lean.Environment) (r : Tests.Ix.IxVM.Runner) : IO TestSeq := do
  let phases ← compileClosure leanEnv
    #[``Nat.add, ``Nat.mul, ``Nat.sub, ``Nat.div, ``Nat.mod, ``Nat.succ]
  let base := Ix.Commit.mkCompileEnv phases
  let ty := Lean.mkConst ``Nat
  let mut state : GenState := {}
  let mut seq : TestSeq := .done
  for i in [:24] do
    let seed := state.seed
    let ((value, answer), next) := (genNat 4 []).run state
    state := next
    let label := s!"generated arithmetic {i}, seed {seed}"
    let nf ← runMeta (Lean.Meta.withTransparency .all (Lean.Meta.reduceAll value)) leanEnv
    seq := seq ++ test s!"Lean agrees with independent numeric oracle: {label}"
      (nf == .lit (.natVal answer))
    let (input, cache) ← IO.ofExcept (Ix.Commit.compileDef base [] ty value)
    let some bytes := cache.constants[input]? | throw <| IO.userError "missing generated input"
    let c : Ixon.Constant ← IO.ofExcept (Ixon.de bytes)
    let env := phases.compileEnv.storeConst input c
    let env := { env with blobs := cache.blobs, anonHints := env.anonHints.insert input (.regular 0) }
    let (fixture, output) ← compiledOutput cache env [] ty nf
    r.build <| execute label (← witness fixture input output)
    let (fixture, wrong) ← natOutput fixture (answer + 1)
    r.build <| execute s!"mutated output: {label}"
      (← witness fixture input wrong) (some "result does not match")
  seq := seq ++ test "generated corpus covers add/mul/sub/let/beta/div/mod"
    (state.coverage.all (· > 0))
  return seq

private def packBundle (env : Ixon.Env) (root : Address) : IO Ixon.Env := do
  let name := Ix.Name.mkStr Ix.Name.mkAnon "_obj"
  let (names, blobs) := Ixon.RawEnv.addNameComponentsWithBlobs env.names env.blobs name
  let env := { env with names, blobs }.registerName name { addr := root, constMeta := .empty }
  let dir ← IO.FS.createTempDir
  try
    let source := dir / "source.ixe"
    let target := dir / "bundle.ixe"
    IO.FS.writeBinFile source (← IO.ofExcept (Ixon.serEnv env))
    Ixon.rsPackEnv source.toString "_obj" #[] target.toString true false
    IO.ofExcept (Ixon.runGetExact Ixon.Env.getEnv (← IO.FS.readBinFile target))
  finally
    IO.FS.removeDirAll dir

/-- Check the command's printed claim against an independent construction,
transport both endpoints through ordinary bundles, then execute the claim. -/
def commandTests (leanEnv : Lean.Environment) (r : Tests.Ix.IxVM.Runner) : IO TestSeq := do
  let phases ← compileClosure leanEnv #[``Fixtures.arithmetic]
  let base := Ix.Commit.mkCompileEnv phases
  let (claim, cache) ← IO.ofExcept (Ix.Commit.evalClaimWithEnv evalCtx base []
    (Lean.mkConst ``Fixtures.arithmetic) (.lit (.natVal 42)) (Lean.mkConst ``Nat))
  let .eval _ input output _ := claim | throw <| IO.userError "expected Eval claim"
  let some bytes := cache.constants[input]? | throw <| IO.userError "missing command input"
  let c : Ixon.Constant ← IO.ofExcept (Ixon.de bytes)
  let env := phases.compileEnv.storeConst input c
  let some bytes := cache.constants[output]? | throw <| IO.userError "missing command output"
  let c : Ixon.Constant ← IO.ofExcept (Ixon.de bytes)
  let env := env.storeConst output c
  let env := { env with
    blobs := cache.blobs
    anonHints := env.anonHints.insert input (.regular 0) |>.insert output (.regular 0) }
  let command : Lean.Elab.Command.CommandElabM Unit := do
    Lean.Elab.Command.elabCommand
      (← `(command| #ixeval Tests.Ix.IxVM.Eval.Fixtures.arithmetic))
  let ctx : Lean.Elab.Command.Context := {
    fileName := "commandTests", fileMap := Lean.FileMap.ofString ""
    snap? := none, cancelTk? := none }
  let (_, state) ← match ← EIO.toIO' ((command ctx).run (Lean.Elab.Command.mkState leanEnv)) with
    | .ok result => pure result
    | .error e => throw <| IO.userError (← e.toMessageData.toString)
  let messages ← state.messages.toList.mapM fun msg => do
    pure (msg.severity, ← msg.data.toString)
  let expected := s!"42\n{claim}\ndigest {Address.blake3 (Ix.Claim.ser claim)}"
  let seq := test "command prints the expected result, Eval claim, and digest"
    (messages == [(.information, expected)])
  let inputBundle ← packBundle env input
  let outputBundle ← packBundle env output
  let seq := seq ++ test "bundles retain the claim's individual constant addresses"
    (inputBundle.main == some input && outputBundle.main == some output)
    ++ test "output bundle prunes the input and display metadata"
      (!outputBundle.consts.contains input && outputBundle.named.isEmpty)
  let transported := { inputBundle with
    consts := outputBundle.consts.fold (fun m k v => m.insert k v) inputBundle.consts
    blobs := outputBundle.blobs.fold (fun m k v => m.insert k v) inputBundle.blobs
    anonHints := outputBundle.anonHints.fold (fun m k v => m.insert k v) inputBundle.anonHints }
  let w ← IO.ofExcept (buildClaimWitness transported claim)
  r.build (execute "command claim after bundle transport" w)
  return seq

/-- Every evaluation claim through the IxVM program, and the Lean oracles
that pin their expected results independently. -/
def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let oracles ← IO.mkRef TestSeq.done
  let code ← Tests.Ix.IxVM.withRunner "ixvm-eval" fun r => do
    tests r
    compiledTests leanEnv r
    let difficult ← difficultTests leanEnv r
    let generated ← differentialTests leanEnv r
    let command ← commandTests leanEnv r
    oracles.set (difficult ++ generated ++ command)
    let labels ← r.labels.get
    for (name, _) in evalFftCosts do
      unless labels.contains s!"eval accepts {name}" do
        r.fail s!"unused evaluation FFT pin: {name}"
  let lean ← lspecIO (.ofList [("ixvm-eval oracles", [← oracles.get])]) []
  return if code == 0 && lean == 0 then 0 else 1

end Tests.Ix.IxVM.Eval
