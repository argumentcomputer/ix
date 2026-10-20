module
public import Ix.IxVM.Toplevel
public import Ix.IxVM.ClaimHarness
public import Tests.Aiur.Common
public import Ix.Meta
public import Ix.Commit
public import Ix.IxEval

public section
namespace Tests.Ix.IxVM.Eval

open LSpec IxVM.ClaimHarness

-- Closed, axiom-free fixtures keep semantic and adversarial tests small.
private def idType : Ixon.Expr :=
  .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
private def idValue : Ixon.Expr :=
  .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))

private def storeDef (env : Ixon.Env) (ty value : Ixon.Expr)
    (refs : Array Address := #[]) (lvls : UInt64 := 0)
    (univs : Array Ixon.Univ := #[.zero]) : Ixon.Env × Address :=
  let c : Ixon.Constant := ⟨.defn ⟨.defn, .safe, lvls, ty, value⟩, #[], refs, univs⟩
  let addr := Address.blake3 (Ixon.ser c)
  let env := env.storeConst addr c
  ({ env with anonHints := env.anonHints.insert addr (.regular 0) }, addr)

private def idObj : Ixon.ExprObj := ⟨0, idValue, #[], #[], #[.zero]⟩

private def witness (env : Ixon.Env) (input : Address) (out : Ixon.ExprObj)
    (tree : Option Ix.AssumptionTree := none) : IO ClaimWitness := do
  let (env, output) ← IO.ofExcept (env.storeExprObj out)
  let trees := match tree with
    | none => {}
    | some t => ({} : Std.HashMap Address Ix.AssumptionTree).insert t.root t
  IO.ofExcept (buildClaimWitness env (.eval input output (tree.map (·.root))) trees)

private def execute (vm : Aiur.CompiledToplevel) (name : String)
    (w : ClaimWitness) (error : Option String := none) : TestSeq :=
  let idx := vm.getFuncIdx `verify_claim |>.get!
  let result := vm.bytecode.execute idx w.input w.inputIOBuffer
  let native := vm.bytecode.executeIxVM idx w.input w.inputIOBuffer
  let parityOk : Bool := match result, native with
    | .error a, .error b => toString a == toString b
    | .ok (a, ai, aq), .ok (b, bi, bq) =>
      a == b && ai == bi && aq.size == bq.size &&
        (aq.zip bq).all fun (a, b) => a.uniqueRows == b.uniqueRows && a.totalHits == b.totalHits
    | _, _ => false
  let parity := test s!"Eval bytecode/generated parity: {name}" parityOk
  parity ++ match result, error with
  | .ok (out, io, _), none =>
    test s!"Eval accepts {name}" (out.isEmpty && io == w.inputIOBuffer)
  | .error e, some expected =>
    test s!"Eval rejects {name}: {e}" (((toString e).splitOn expected).length > 1)
  | .error e, none => test s!"Eval accepts {name}: {e}" false
  | .ok _, some _ => test s!"Eval rejects {name}" false

-- Bypass host validation deliberately: these tests must exercise the circuit.
private def rawWitness (env : Ixon.Env) (input : Address) (bytes : ByteArray)
    (objectKey : Option Address := none) : ClaimWitness :=
  let output := objectKey.getD (Address.blake3 bytes)
  let claimBytes := Ix.Claim.ser (.eval input output none)
  let digest := packedDigestKey (Address.blake3 claimBytes)
  let io := addEntries env (fun _ => true) default
  let io := io.extend 0 digest (claimBytes.data.map .ofUInt8)
  let io := io.extend 6 (output.hash.data.map Aiur.G.ofUInt8) (bytes.data.map .ofUInt8)
  { funcName := `verify_claim, input := digest, inputIOBuffer := io }

def codecTests : TestSeq := Id.run do
  let obj : Ixon.ExprObj := ⟨0, .leanLam (.sort 0) (.var 0), #[], #[], #[.zero]⟩
  let golden := ByteArray.mk #[0xe0, 5, 0, 0x81, 7, 0, 0x10, 0, 0, 1, 0]
  let mut seq := test "ExprObj Lean/Rust golden bytes" (obj.ser == golden)
    ++ test "ExprObj exact roundtrip" ((Ixon.ExprObj.de golden).toOption == some obj)
  for n in [:golden.size] do
    seq := seq ++ test s!"ExprObj rejects truncation at {n}"
      (Ixon.ExprObj.de (golden.extract 0 n) |>.toOption.isNone)
  return seq

def serdeTest : AiurTestCase :=
  let io := (default : Aiur.IOBuffer).extend 6 #[0] (idObj.ser.data.map .ofUInt8)
  { functionName := `expr_obj_serde_test, label := "ExprObj Aiur codec roundtrip"
    input := #[], inputIOBuffer := io, expectedIOBuffer := io
    interpret := false, withProof := false }

def tests (vm : Aiur.CompiledToplevel) : IO TestSeq := do
  let mut seq := codecTests
  let beta := Ixon.Expr.app (.leanLam idType (.var 0)) idValue
  let underBinder := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (.var 0) (.app (.leanLam (.var 1) (.var 0)) (.var 0)))
  for (label, value) in [
      ("identity", idValue), ("beta", beta),
      ("zeta", Ixon.Expr.leanLet false idType idValue (.var 0)),
      ("reduction under lambda", underBinder)] do
    let (env, input) := storeDef {} idType value
    seq := seq ++ execute vm label (← witness env input idObj)
  let (env, dep) := storeDef {} idType beta
  let (env, input) := storeDef env idType (.ref 0 #[]) #[dep]
  seq := seq ++ execute vm "delta" (← witness env input idObj)
  for (label, kind) in [("theorem body", Ix.DefKind.thm), ("opaque body", .opaq)] do
    let c : Ixon.Constant := ⟨.defn ⟨kind, .safe, 0, idType, beta⟩, #[], #[], #[.zero]⟩
    let a := Address.blake3 (Ixon.ser c)
    let fixture := ({} : Ixon.Env).storeConst a c
    let fixture := { fixture with anonHints := fixture.anonHints.insert a .opaque }
    seq := seq ++ execute vm label (← witness fixture a idObj)
  for safety in [Ix.DefinitionSafety.unsaf, .part] do
    let c : Ixon.Constant := ⟨.defn ⟨.defn, safety, 0, idType, idValue⟩, #[], #[], #[.zero]⟩
    let a := Address.blake3 (Ixon.ser c)
    let fixture := ({} : Ixon.Env).storeConst a c
    let fixture := { fixture with anonHints := fixture.anonHints.insert a (.regular 0) }
    seq := seq ++ execute vm "unsafe/partial subject" (← witness fixture a idObj)
      (some "unsafe or partial")
  let block : Ixon.Constant :=
    ⟨.muts #[.defn ⟨.defn, .safe, 0, idType, beta⟩], #[], #[], #[.zero]⟩
  let ba := Address.blake3 (Ixon.ser block)
  let projection : Ixon.Constant := ⟨.dPrj ⟨0, ba⟩, #[], #[], #[]⟩
  let pa := Address.blake3 (Ixon.ser projection)
  let fixture := (({} : Ixon.Env).storeConst ba block).storeConst pa projection
  let fixture := { fixture with anonHints := fixture.anonHints.insert pa (.regular 0) }
  seq := seq ++ execute vm "mutual definition projection" (← witness fixture pa idObj)
  let tree := Ix.AssumptionTree.canonical #[dep] |>.get!
  seq := seq ++ execute vm "assumed dependency still unfolds" (← witness env input idObj tree)
  let selfTree := Ix.AssumptionTree.canonical #[input] |>.get!
  seq := seq ++ execute vm "subject in assumptions" (← witness env input idObj selfTree)
    (some "input is an assumption")
  seq := seq ++ execute vm "wrong output" (← witness env input { idObj with root := .sort 0 })
    (some "result does not match")
  seq := seq ++ execute vm "unreduced output" (← witness env input { idObj with root := beta })
    (some "result does not match")
  seq := seq ++ execute vm "universe count mismatch"
    (← witness env input { idObj with lvls := 1 }) (some "universe parameter count")
  -- Input has the same well-typed result but a false declared type.
  let (badEnv, badInput) := storeDef {} (.sort 0) idValue
  let w ← witness badEnv badInput idObj
  let r := vm.bytecode.execute (vm.getFuncIdx `verify_claim |>.get!) w.input w.inputIOBuffer
  seq := seq ++ test "Eval rejects ill-typed input before accepting its result" r.toOption.isNone
  let badSelf := Ix.AssumptionTree.canonical #[badInput] |>.get!
  let w ← witness badEnv badInput idObj badSelf
  seq := seq ++ test "assumptions cannot waive input typechecking"
    (vm.bytecode.execute (vm.getFuncIdx `verify_claim |>.get!) w.input w.inputIOBuffer).toOption.isNone
  -- An ill-typed dependency that would otherwise reduce to the right value.
  let (badEnv, dep) := storeDef {} idType (.sort 0)
  let (badEnv, badInput) := storeDef badEnv idType (.ref 0 #[]) #[dep]
  let w ← witness badEnv badInput { idObj with root := .sort 0 }
  seq := seq ++ test "Eval checks transitive dependencies"
    (vm.bytecode.execute (vm.getFuncIdx `verify_claim |>.get!) w.input w.inputIOBuffer).toOption.isNone
  -- Universe-polymorphic identity and open shared subterms.
  let (polyEnv, polyInput) := storeDef {} idType underBinder #[] 1 #[.var 0]
  seq := seq ++ execute vm "universe-polymorphic normalization"
    (← witness polyEnv polyInput { idObj with lvls := 1, univs := #[.var 0] })
  let shared : Ixon.ExprObj := { idObj with
    root := .leanLam (.sort 0) (.leanLam (.var 0) (.share 0)), sharing := #[.var 0] }
  seq := seq ++ execute vm "open sharing under binder" (← witness env input shared)
  -- Normalize both binder domains and Pi bodies, including reducible types.
  let propLet := Ixon.Expr.leanLet false (.sort 1) (.sort 0) (.var 0)
  let (binderEnv, binderInput) := storeDef {} idType
    (.leanLam propLet (.leanLam (.var 0) (.var 0))) #[] 0 #[.zero, .succ .zero]
  seq := seq ++ execute vm "normalization in lambda domain"
    (← witness binderEnv binderInput idObj)
  let propBeta := fun p => Ixon.Expr.app (.leanLam (.sort 0) (.var 0)) p
  let pi := Ixon.Expr.leanAll propLet
    (.leanAll (propBeta (.var 0)) (propBeta (.var 1)))
  let (piEnv, piInput) := storeDef {} (.sort 0) pi #[] 0 #[.zero, .succ .zero]
  seq := seq ++ execute vm "normalization in Pi domain and dependent codomain"
    (← witness piEnv piInput { idObj with root := idType })
  -- Substitution must lift x through the surviving z binder, not capture z.
  let captureTy := Ixon.Expr.leanAll (.sort 0)
    (.leanAll (.var 0) (.leanAll (.var 1) (.var 2)))
  let captureBody := Ixon.Expr.leanLam (.sort 0) (.leanLam (.var 0)
    (.app (.leanLam (.var 1) (.leanLam (.var 2) (.var 1))) (.var 0)))
  let captureNF := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (.var 0) (.leanLam (.var 1) (.var 1)))
  let (captureEnv, captureInput) := storeDef {} captureTy captureBody
  seq := seq ++ execute vm "capture-avoiding beta under nested binders"
    (← witness captureEnv captureInput { idObj with root := captureNF })
  let captured := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (.var 0) (.leanLam (.var 1) (.var 0)))
  seq := seq ++ execute vm "captured variable with the same type"
    (← witness captureEnv captureInput { idObj with root := captured })
    (some "result does not match")
  -- A theorem/opaque SUBJECT exposes its body, but references inside an
  -- expression follow WHNF's opacity policy. Proof irrelevance must not
  -- allow replacing one theorem reference by another of the same type.
  for (label, kind) in [("theorem reference", Ix.DefKind.thm), ("opaque reference", .opaq)] do
    let c : Ixon.Constant := ⟨.defn ⟨kind, .safe, 0, idType, idValue⟩, #[], #[], #[.zero]⟩
    let a := Address.blake3 (Ixon.ser c)
    let other := { c with info := .defn ⟨kind, .safe, 0, idType, beta⟩ }
    let b := Address.blake3 (Ixon.ser other)
    let fixture := (({} : Ixon.Env).storeConst a c).storeConst b other
    let fixture := { fixture with anonHints := fixture.anonHints.insert a .opaque |>.insert b .opaque }
    let (fixture, subject) := storeDef fixture idType (.ref 0 #[]) #[a]
    let expected : Ixon.ExprObj := ⟨0, .ref 0 #[], #[], #[a], #[]⟩
    seq := seq ++ execute vm s!"preserves {label}" (← witness fixture subject expected)
    seq := seq ++ execute vm s!"does not unfold {label}"
      (← witness fixture subject idObj) (some "result does not match")
    seq := seq ++ execute vm s!"does not replace {label} by an equivalent proof"
      (← witness fixture subject { expected with refs := #[b] }) (some "result does not match")
  for (name, obj, err) in [
      ("free variable", { idObj with root := .var 0 }, "free term variable"),
      ("bad ref", { idObj with root := .ref 0 #[] }, "table index"),
      ("bad universe index", { idObj with root := .sort 1 }, "table index"),
      ("bad universe parameter", { idObj with univs := #[.var 0] }, "universe"),
      ("relative Rec", { idObj with root := .recur 0 #[] }, "block-local Rec"),
      ("cyclic sharing", { idObj with sharing := #[.share 0] }, "table index"),
      ("forward sharing", { idObj with sharing := #[.share 1, .var 0] }, "table index")] do
    seq := seq ++ execute vm name (rawWitness env input obj.ser) (some err)
  seq := seq ++ execute vm "trailing object bytes"
    (rawWitness env input (idObj.ser.push 0)) (some "trailing bytes")
  seq := seq ++ execute vm "legacy object format"
    (rawWitness env input (idObj.ser.set! 1 4)) (some "unsupported object format")
  for n in [:idObj.ser.size] do
    let w := rawWitness env input (idObj.ser.extract 0 n)
    seq := seq ++ test s!"Eval rejects truncated ExprObj at {n}"
      (vm.bytecode.execute (vm.getFuncIdx `verify_claim |>.get!) w.input w.inputIOBuffer).toOption.isNone
  -- Claim-level authentication and version checks are shared with Check,
  -- but exercise the new dispatch arm with adversarial bytes too.
  let w ← witness env input idObj
  let (_, output) ← IO.ofExcept (env.storeExprObj idObj)
  let cb := Ix.Claim.ser (.eval input output none)
  for (label, bytes) in [
      ("v4 claim", cb.set! 1 4), ("wrong validator", cb.set! 2 0),
      ("trailing claim bytes", cb.push 0)] do
    let digest := packedDigestKey (Address.blake3 bytes)
    let io := w.inputIOBuffer.extend 0 digest (bytes.data.map .ofUInt8)
    seq := seq ++ test s!"Eval rejects {label}"
      (vm.bytecode.execute (vm.getFuncIdx `verify_claim |>.get!) digest io).toOption.isNone
  let c := env.getConst? input |>.get!
  seq := seq ++ execute vm "constant used as output"
    (rawWitness env input (Ixon.ser c)) (some "wrong tag")
  let altered := { idObj with root := .sort 0 }
  let mismatched := rawWitness env input altered.ser (some (Address.blake3 idObj.ser))
  let r := vm.bytecode.execute (vm.getFuncIdx `verify_claim |>.get!) mismatched.input mismatched.inputIOBuffer
  seq := seq ++ test "Eval authenticates output bytes" r.toOption.isNone
  return seq

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

private def natObj (env : Ixon.Env) (n : Nat) : Ixon.Env × Ixon.ExprObj :=
  let (env, addr) := env.storeBlob (ByteArray.mk (Nat.toBytesLE n))
  (env, ⟨0, .nat 0, #[], #[addr], #[]⟩)

private def listObj (env : Ixon.Env) : IO (Ixon.Env × Ixon.ExprObj) := do
  let nat ← lookupAddr env ``Nat
  let consAddr ← lookupAddr env ``List.cons
  let nilAddr ← lookupAddr env ``List.nil
  let (env, a) := env.storeBlob (ByteArray.mk (Nat.toBytesLE 42))
  let (env, b) := env.storeBlob (ByteArray.mk (Nat.toBytesLE 12))
  let ty := Ixon.Expr.ref 0 #[]
  let cons := Ixon.Expr.app (.ref 1 #[0]) ty
  let nil := Ixon.Expr.app (.ref 2 #[0]) ty
  let root := Ixon.Expr.app (.app cons (.nat 3)) (.app (.app cons (.nat 4)) nil)
  return (env, ⟨0, root, #[], #[nat, consAddr, nilAddr, a, b], #[.zero]⟩)

def compiledTests (leanEnv : Lean.Environment) (vm : Aiur.CompiledToplevel) : IO TestSeq := do
  let pairs := #[
    (``Fixtures.arithmetic, ``Fixtures.fortyTwo),
    (``Fixtures.listResult, ``Fixtures.listExpected),
    (``Fixtures.recurResult, ``Fixtures.six),
    (``Fixtures.projResult, ``Fixtures.nine),
    (``Fixtures.stringResult, ``Fixtures.stringExpected)]
  let env ← loadSharedIxonEnv (pairs.flatMap (fun (a, b) => #[a, b]) ++ synthesizedPrimNames) leanEnv
  let mut seq : TestSeq := .done
  for (a, b) in pairs do
    let input ← lookupAddr env a
    let output ← lookupAddr env b
    let some c := env.getConst? output | throw <| IO.userError "missing fixture"
    let .defn d := c.info | throw <| IO.userError "expected fixture definition"
    let raw : Ixon.ExprObj := ⟨d.lvls, d.value, c.sharing, c.refs, c.univs⟩
    -- Lean numeral syntax elaborates to OfNat applications. Specify the
    -- expected normal forms independently, with actual literal nodes.
    let (fixture, obj) ←
      if b == ``Fixtures.fortyTwo then pure (natObj env 42)
      else if b == ``Fixtures.six then pure (natObj env 6)
      else if b == ``Fixtures.nine then pure (natObj env 9)
      else if b == ``Fixtures.listExpected then listObj env
      else pure (env, raw)
    seq := seq ++ execute vm (toString a) (← witness fixture input obj)
    if a == ``Fixtures.arithmetic then
      seq := seq ++ execute vm "unreduced OfNat output"
        (← witness env input raw) (some "result does not match")
      let (fixture, wrongObj) := natObj env 9
      seq := seq ++ execute vm "wrong result with the same type"
        (← witness fixture input wrongObj) (some "result does not match")
  return seq

private def compileClosure (leanEnv : Lean.Environment) (names : Array Lean.Name) :
    IO Ix.CompileM.CompilePhases := do
  let mut seen : Lean.NameSet := {}
  let mut entries := #[]
  for n in names ++ synthesizedPrimNames do
    for entry in Lean.collectDependencies n leanEnv.constants do
      unless seen.contains entry.1 do
        seen := seen.insert entry.1
        entries := entries.push entry
  Ix.CompileM.rsCompilePhasesOf entries.toList

private def compiledObj (base : Ix.CompileM.CompileEnv) (env : Ixon.Env)
    (lvls : List Lean.Name) (ty value : Lean.Expr) : IO (Ixon.Env × Ixon.ExprObj) := do
  let (addr, cache) ← IO.ofExcept (Ix.Commit.compileExprObj base lvls ty value)
  let some bytes := cache.blobs[addr]? | throw <| IO.userError "missing compiled ExprObj"
  let obj ← IO.ofExcept (Ixon.ExprObj.de bytes)
  return ({ env with blobs := cache.blobs }, obj)

/-- Independent Lean reduction supplies the expected terms, never IxVM's own
normalizer. Closed numeric examples additionally pin a hand-computed result.
Neutral terms deliberately avoid arithmetic, where Lean and IxVM choose
different representations for stuck primitives. -/
def difficultTests (leanEnv : Lean.Environment) (vm : Aiur.CompiledToplevel) : IO TestSeq := do
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
    IO.eprintln s!"[ixvm] eval fixture: {name}"
    let some (.defnInfo info) := leanEnv.find? name
      | throw <| IO.userError s!"expected definition: {name}"
    let expected ← runMeta (Lean.Meta.withTransparency .all (Lean.Meta.reduceAll info.value)) leanEnv
    if let some (_, n) := numeric.find? (fun p => p.1 == name) then
      seq := seq ++ test s!"Lean oracle agrees with pinned result: {name}"
        (expected == .lit (.natVal n))
    let input ← lookupAddr env name
    let (fixture, obj) ← compiledObj base env info.levelParams info.type expected
    seq := seq ++ execute vm s!"Lean differential: {name}" (← witness fixture input obj)
    if let some (_, n) := numeric.find? (fun p => p.1 == name) then
      let (fixture, wrong) := natObj env (n + 1)
      seq := seq ++ execute vm s!"incorrect result: {name}"
        (← witness fixture input wrong) (some "result does not match")
  -- The elaborator deliberately wraps this accessibility proof in opaqueId.
  -- A kernel-reduction claim must respect that boundary, even though native
  -- compilation can execute the function by erasing proofs.
  IO.eprintln "[ixvm] eval fixture: opaque well-founded accessibility proof"
  let input ← lookupAddr env ``Fixtures.wellFoundedTree
  let (fixture, output) := natObj env 15
  let opaqueId ← lookupAddr env ``Lean.opaqueId
  seq := seq ++ test "generated WF fixture contains the opaqueId dependency"
    ((closureFrom env input).contains opaqueId)
  seq := seq ++ execute vm "opaque accessibility proof blocks kernel evaluation"
    (← witness fixture input output) (some "result does not match")
  -- This explicit proof does expose constructors to Acc.rec. Meta keeps its
  -- theorem heads opaque, so pin the independent triangular-number answer.
  IO.eprintln "[ixvm] eval fixture: transparent well-founded recursion"
  let input ← lookupAddr env ``Fixtures.wellFoundedSum
  let (fixture, output) := natObj env 21
  seq := seq ++ execute vm "well-founded recursion through accessibility proofs"
    (← witness fixture input output)
  let (fixture, wrong) := natObj env 22
  seq := seq ++ execute vm "incorrect well-founded recursion result"
    (← witness fixture input wrong) (some "result does not match")
  -- Open Nat offset must remain compact; unfolding Nat.add's implementation
  -- here would expand billions of successors or leave a different normal form.
  let nat ← lookupAddr env ``Nat
  let add ← lookupAddr env ``Nat.add
  let (fixture, literal) := env.storeBlob (ByteArray.mk (Nat.toBytesLE 4294967313))
  let output : Ixon.ExprObj := ⟨0,
    .leanLam (.ref 0 #[]) (.app (.app (.ref 1 #[]) (.var 0)) (.nat 2)),
    #[], #[nat, add, literal], #[]⟩
  let input ← lookupAddr env ``Fixtures.openOffset
  IO.eprintln "[ixvm] eval fixture: compact symbolic offset"
  seq := seq ++ execute vm "compact symbolic Nat offset beyond 32 bits"
    (← witness fixture input output)
  let input ← lookupAddr env ``Fixtures.openZero
  seq := seq ++ execute vm "symbolic Nat addition exposes zero after argument reduction"
    (← witness env input ⟨0, .leanLam (.ref 0 #[]) (.var 0), #[], #[nat], #[]⟩)
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

def differentialTests (leanEnv : Lean.Environment) (vm : Aiur.CompiledToplevel) : IO TestSeq := do
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
    IO.eprintln s!"[ixvm] eval differential: {label}"
    let nf ← runMeta (Lean.Meta.withTransparency .all (Lean.Meta.reduceAll value)) leanEnv
    seq := seq ++ test s!"Lean agrees with independent numeric oracle: {label}"
      (nf == .lit (.natVal answer))
    let (input, cache) ← IO.ofExcept (Ix.Commit.compileDef base [] ty value)
    let some bytes := cache.constants[input]? | throw <| IO.userError "missing generated input"
    let c : Ixon.Constant ← IO.ofExcept (Ixon.de bytes)
    let env := phases.compileEnv.storeConst input c
    let env := { env with blobs := cache.blobs, anonHints := env.anonHints.insert input (.regular 0) }
    let (fixture, output) ← compiledObj cache env [] ty nf
    seq := seq ++ execute vm label (← witness fixture input output)
    let (fixture, wrong) := natObj fixture (answer + 1)
    seq := seq ++ execute vm s!"mutated output: {label}"
      (← witness fixture input wrong) (some "result does not match")
  seq := seq ++ test "generated corpus covers add/mul/sub/let/beta/div/mod"
    (state.coverage.all (· > 0))
  return seq

/-- Check the command's actual printed claim against a separately constructed
claim, then execute that same claim through both IxVM backends. -/
def commandTests (leanEnv : Lean.Environment) (vm : Aiur.CompiledToplevel) : IO TestSeq := do
  let phases ← compileClosure leanEnv #[``Fixtures.arithmetic]
  let base := Ix.Commit.mkCompileEnv phases
  let (claim, cache) ← IO.ofExcept (Ix.Commit.evalClaimWithEnv base []
    (Lean.mkConst ``Fixtures.arithmetic) (.lit (.natVal 42)) (Lean.mkConst ``Nat))
  let .eval input _ _ := claim | throw <| IO.userError "expected Eval claim"
  let some bytes := cache.constants[input]? | throw <| IO.userError "missing command input"
  let c : Ixon.Constant ← IO.ofExcept (Ixon.de bytes)
  let env := phases.compileEnv.storeConst input c
  let env := { env with
    blobs := cache.blobs
    anonHints := env.anonHints.insert input (.regular 0) }
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
  let w ← IO.ofExcept (buildClaimWitness env claim)
  return seq ++ execute vm "claim printed by the evaluation command" w

end Tests.Ix.IxVM.Eval
