import IxCCTests.KernelFront.Report
import IxCCTests.KernelFront.Bound
import IxCCTests.KernelFront.Hints
import IxCCTests.KernelFront.LamRuns
import IxCCTests.KernelFront.Cli
import IxCCTests.Src.Support
import IxCCTests.Support.Envelope
import IxCCTests.IxonV3.Builder

/-! # `tests-kernel-front`: the front end over the certified kernel on the committed closures

Since the switch, ingress (`Recheck.ingress`) is the kernel's acceptance and
the producer's annotator and Stage A are the kernel's. On two committed
closures (`phase1-scalar`'s `tuple` and `bench-k1`'s `fib`; every committed
closure is role-bound, as `ix compile` writes it): the kernel accepts it,
ingress reads it, and Stage A accepts the producer's certificate of every root
(`Report.report`). Then the
refusals:

* an unbound envelope (the same records without the binding,
  `Support.Envelope.unboundTwin`);
* a role binding whose bytes do not hash to its address, a closure missing a
  record its root references, a role table naming a record the closure lacks;
* a certificate whose annotation differs from the kernel annotator's in one
  tag (Stage A);
* a program that is not the kernel's reading: a constant's value changed, a
  constructor's field count changed, a constant keyed by another address.

Then the tuple closure with one more record, a constant whose ∀ chain shares
one type at each of 200 steps (`sharedLevelConstants`), is accepted with every
record: the kernel keeps the chain's universe level small.

Then, on every committed role-bound closure: the envelope decodes it and the
kernel accepts it, but for `src-diag`'s `sorry.ixe`, which the kernel declines
for its `sorry`; on `phase1-boundary`'s `fields255` and `tags126`, whose roots
reach a record over IxCC's consumer budget, ingress refuses at `decode`, naming
the record; and on the others under 512 KiB ingress reads every root and every
root that compiles has its certificate accepted by Stage A; on `sorry.ixe`
ingress declines.

Then the role-bound test builder (`IxCCTests.Support.Bound`), with the hostile
family's enumeration case ported to it (`Bound`).

Then the artifact's reducibility hints (`Hints`): the closure the kernel checks
in exponential time without them accepted within a bound, the hint function
the statements name read a second way, and hostile and missing hints through
the front end, each ending in the honest object and certificate or a clean
decline.

Then the annotator's λ-runs (`LamRuns`): on every committed closure with a
sidecar that the kernel accepts and ingress reads, and on adversarial programs,
the kernel annotator (one kernel question per run of λs) gives exactly the
annotation of its per-λ reference (`Reference`, the definition it replaced).

The same report on other role-bound closures, written into scratch by the
tree's `ix`, is `tests-kernel-front report …` (`Main`). -/

namespace IxCCTests.KernelFront

open IxCC IxCC.Src
open IxCCTests.Src (Assert expect)

/-- The committed closures the suite tampers with, and their root. -/
def fixtures : List (String × String × String) :=
  [("tuple", "fixtures/corpus/phase1-scalar/tuple", "entry"),
   ("fib", "fixtures/ixon-v4/bench-k1/fib", "entry")]

/-- Every committed role-bound closure under `fixtures/`: not the resource
handoff vectors (unbound, ix's fixture package). -/
def committedClosures : IO (Array System.FilePath) := do
  let all ← System.FilePath.walkDir "fixtures"
  let skip := ["/handoff/"]
  let ixe := all.filter fun p => p.extension == some "ixe" && !skip.any fun s => (p.toString.splitOn s).length > 1
  return ixe.qsort (·.toString < ·.toString)

/-- The closures whose every root reaches a record over IxCC's consumer budget:
the envelope decodes them and the kernel accepts them; ingress refuses every
root at `ingress: decode`, naming the record (their expected decline). -/
def reachRefused : List String :=
  ["phase1-boundary/fields255.ixe", "phase1-boundary/tags126.ixe"]

/-- The closures the kernel declines (`sorryAx`, on purpose). -/
def kernelDeclined : List String := ["src-diag/sorry.ixe"]

/-- Closures below this size are also run root by root through ingress, the
producer and Stage A (`report`); the larger ones have many roots, which the
corpus checks compile. -/
def reportBytes : Nat := 512 * 1024

/-- A closure's sidecar: `NAME.equations.json` beside it, or the RC input's. -/
def sidecarOf (path : System.FilePath) : IO (Option System.FilePath) := do
  let stem := path.withExtension "equations.json"
  if ← stem.pathExists then return some stem
  let rc := path.withFileName "consumer.equations.json"
  if ← rc.pathExists then return some rc
  return none

def read (stem : String) : IO (ByteArray × Lean.Json) := do
  let bytes ← IO.FS.readBinFile s!"{stem}.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
  return (bytes, json)

def isRefusal (r : Except KernelFront.Refusal α) (stage : KernelFront.Stage) : Bool :=
  match r with
  | .error e => e.stage == stage
  | .ok _ => false

/-- Two constants whose ∀ chains share one type at every step, at length `k`:
`dag` is `def L : Type := T k` with `T 1 = Prop → Prop`, `T (j+1) = T j → T j`
and each `T j` a sharing entry; `let` is
`def L : (let a0 : Type := Prop; let a(j+1) : Type := aj → aj; …; Type) := Prop`.
Until the kernel built the ∀ rule's level with `mk_imax`'s folds, its level was
shared as a DAG whose tree doubled per step, and each took time doubling in
`k`. -/
def sharedLevelConstants (k : Nat) : List (String × _root_.Ixon.Constant) :=
  let arrow := IxCC.Ixon.V3.Expr.leanAll (.var 0) (.var 1)
  let letType := Id.run do
    let mut body : IxCC.Ixon.V3.Expr := .sort 1
    for _ in [0:k] do
      body := IxCC.Ixon.V3.Expr.leanLet false (.sort 1) arrow body
    return IxCC.Ixon.V3.Expr.leanLet false (.sort 1) (.sort 0) body
  let table : Array IxCC.Ixon.V3.Expr := (Array.range k).map fun j =>
    if j == 0 then IxCC.Ixon.V3.Expr.leanAll (.sort 0) (.sort 0)
    else IxCC.Ixon.V3.Expr.leanAll (.share (j - 1).toUInt64) (.share (j - 1).toUInt64)
  let univs : Array IxCC.Ixon.Univ := #[.zero, .succ .zero]
  let mk (c : IxCC.Ixon.V3.Constant) : _root_.Ixon.Constant :=
    IxCC.Ixon.V4.constantToIx (IxCCTests.IxonV3.Builder.completeBinders c)
  [("dag", mk ⟨.defn ⟨.defn, .safe, {}, 0, .sort 1, .share (k - 1).toUInt64⟩, table, #[], univs, #[]⟩),
   ("let", mk ⟨.defn ⟨.defn, .safe, {}, 0, letType, .sort 0⟩, #[], #[], univs, #[]⟩)]

/-- Flip the class of one argument tag (the first relevant one). -/
def flipOne : List (TermKey × List Relevance.Tag) → List (TermKey × List Relevance.Tag)
  | [] => []
  | (k, ts) :: rest =>
    match ts.findIdx? (fun | .arg .rel => true | _ => false) with
    | some i => (k, ts.set i (.arg .type)) :: rest
    | none => (k, ts) :: flipOne rest

/-- Ixon v5 & `specVersion = 4` regression checks built directly on `IxCK`'s committed
v5 prelude records: exercises post-K3 `Reading.corrRec` mode-tamper refusals (λ/Π/let,
multi-variant binderful shares, mutual definition blocks), N2 fail-closed stored
zero-ness datum cross-checks (λ bodies, Π types, shared leading Πs, irrelevant lets,
large eliminator `Nat.rec` rules, advisory `.undecided`), R8 `checkEqn` over plain v5
`f.eq_def` theorems, N4 `specVersion = 4` role/policy checks, and the N5 `ModeCheckHook`. -/
def v5Suite (a : Assert) : IO Unit := do
  let kaddrToV3 (ka : _root_.Address) : Ixon.Address :=
    (Ixon.Address.ofBytes? ka.hash).getD default
  let storeV5 (env : Ixon.V3.Env) (c : Ixon.V3.Constant) : Ixon.V3.Env × Ixon.Address :=
    let bytes := Ixon.V3.constantBytes c
    let addr := Ixon.Address.blake3Pure bytes
    ({ env with consts := env.consts.insert addr bytes }, addr)
  let preRecs ← IO.ofExcept Ix.Kernel.Reader.preludeRecords
  let fullTable ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let preRoles : List Ix.Kernel.Role := Ix.Kernel.preludeShape.flatten
  let bound := fullTable.bound.filter fun (r, _) => preRoles.contains r
  let tbl : Ix.Kernel.RoleTable := { version := Ix.Kernel.specVersion, bound, evidence := #[] }
  let _ ← IO.ofExcept tbl.check
  let tblBytes := tbl.toBytes
  let tblAddr := Ixon.Address.blake3Pure tblBytes
  let mut consts : Std.HashMap Ixon.Address ByteArray := {}
  for (ka, kc) in preRecs do
    consts := consts.insert (kaddrToV3 ka) (_root_.Ixon.serConstant kc)
  let env0 : Ixon.V3.Env :=
    { consts, blobs := {}, binding := some { address := tblAddr, bytes := tblBytes } }
  let mut rmap : Std.HashMap Ix.Kernel.Role Ixon.Address := {}
  for (r, ka) in bound do
    rmap := rmap.insert r (kaddrToV3 ka)
  let natA := rmap[Ix.Kernel.Role.nat]!
  let natZeroA := rmap[Ix.Kernel.Role.natZero]!
  let natRecA := rmap[Ix.Kernel.Role.natRec]!
  let eqA := rmap[Ix.Kernel.Role.eq]!
  let eqReflA := rmap[Ix.Kernel.Role.eqRefl]!
  let natE : Ixon.V3.Expr := .ref 0 #[]
  let oneU : Array IxCC.Ixon.Univ := #[.succ .zero]
  let (env, idNatA) := storeV5 env0
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, .lam natE (.var 0)⟩, #[], #[natA], #[],
      #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.never {}]⟩]⟩
  let (env, idErasedA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE (.all natE natE), .lam natE (.lam natE (.var 0))⟩,
      #[], #[natA], #[],
      #[⟨false, 0, 0, #[.never .erased, .never {}]⟩,
        ⟨false, 1, 0, #[.never .erased, .never {}]⟩]⟩
  let eqApp : Ixon.V3.Expr :=
    .app (.app (.app (.ref 2 #[0]) natE) (.app (.app (.ref 1 #[]) (.var 1)) (.var 0))) (.var 0)
  let reflProof : Ixon.V3.Expr :=
    .lam natE (.lam natE (.app (.app (.ref 3 #[0]) natE) (.var 0)))
  let (env, idErasedEqA) := storeV5 env
    ⟨.defn ⟨.thm, .safe, {}, 0, .all natE (.all natE eqApp), reflProof⟩,
      #[], #[natA, idErasedA, eqA, eqReflA], oneU,
      #[⟨false, 0, 0, #[.zero {}, .zero {}]⟩,
        ⟨false, 1, 0, #[.zero {}, .zero {}]⟩]⟩
  let (env, letBorrowA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, .lam natE (.letE false .borrow natE (.var 0) (.var 0))⟩,
      #[], #[natA], #[],
      #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.never {}]⟩]⟩
  let (env, letNonDepA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, .lam natE (.letE true (.value .many) natE (.var 0) (.var 0))⟩,
      #[], #[natA], #[],
      #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.never {}]⟩]⟩
  let proofTy : Ixon.V3.Expr := .all natE (.app (.app (.app (.ref 1 #[0]) natE) (.var 0)) (.var 0))
  let proofVal : Ixon.V3.Expr := .lam natE (.app (.app (.ref 2 #[0]) natE) (.var 0))
  let (env, proofFnA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, proofTy, proofVal⟩,
      #[], #[natA, eqA, eqReflA], oneU,
      #[⟨false, 0, 0, #[.zero {}]⟩, ⟨false, 1, 0, #[.zero {}]⟩]⟩
  let (env, polyIdA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 1, .all (.sort 0) (.all (.var 0) (.var 1)),
        .lam (.sort 0) (.lam (.var 0) (.var 0))⟩,
      #[], #[], #[.var 0],
      #[⟨false, 0, 0, #[.ifAllZero #[0] {}, .ifAllZero #[0] {}]⟩,
        ⟨false, 1, 0, #[.ifAllZero #[0] {}, .ifAllZero #[0] {}]⟩]⟩
  let (env, sharedFnA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, .lam natE (.app (.share 0) (.app (.share 0) (.var 0)))⟩,
      #[.lam natE (.var 0)], #[natA], #[],
      #[⟨false, 0, 0, #[.never {}]⟩,
        ⟨false, 1, 0, #[.never {}, .share 0, .share 1]⟩,
        ⟨true, 0, 0, #[.never {}]⟩,
        ⟨true, 0, 1, #[.never .unique]⟩]⟩
  let (env, sharedPiGoodA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE (.share 0), .lam natE (.lam natE (.var 0))⟩,
      #[.all natE natE], #[natA], #[],
      #[⟨false, 0, 0, #[.never {}, .share 0]⟩,
        ⟨false, 1, 0, #[.never {}, .never {}]⟩,
        ⟨true, 0, 0, #[.never {}]⟩]⟩
  let (env, sharedPiBadA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE (.share 0), .lam natE (.lam natE (.var 0))⟩,
      #[.all natE natE], #[natA], #[],
      #[⟨false, 0, 0, #[.never {}, .share 0]⟩,
        ⟨false, 1, 0, #[.never {}, .never {}]⟩,
        ⟨true, 0, 0, #[.zero {}]⟩]⟩
  let useNatRecVal : Ixon.V3.Expr := .lam natE
    (.app (.app (.app (.app (.ref 1 #[0]) (.lam natE natE)) (.ref 2 #[])) (.lam natE (.lam natE (.var 0)))) (.var 0))
  let (env, useNatRecA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, useNatRecVal⟩,
      #[], #[natA, natRecA, natZeroA], oneU,
      #[⟨false, 0, 0, #[.never {}]⟩,
        ⟨false, 1, 0, #[.never {}, .never {}, .never {}, .never {}]⟩]⟩
  let eqZeroTy : Ixon.V3.Expr := .app (.app (.app (.ref 2 #[0]) natE) (.ref 1 #[])) (.ref 1 #[])
  let eqZeroVal : Ixon.V3.Expr := .app (.app (.ref 3 #[0]) natE) (.ref 1 #[])
  let irrLetVal : Ixon.V3.Expr := .letE false (.value .many) eqZeroTy eqZeroVal (.lam natE (.var 0))
  let (env, irrLetGoodA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, irrLetVal⟩,
      #[], #[natA, natZeroA, eqA, eqReflA], oneU,
      #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.never {}]⟩]⟩
  let (env, irrLetBadA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, irrLetVal⟩,
      #[], #[natA, natZeroA, eqA, eqReflA], oneU,
      #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.zero {}]⟩]⟩
  let mutDefBlock : Ixon.V3.Constant :=
    ⟨.muts #[
      .defn ⟨.defn, .safe, {}, 0, .all natE natE, .lam natE (.var 0)⟩,
      .defn ⟨.defn, .safe, {}, 0, .all natE natE, .lam natE (.app (.recur 0 #[]) (.var 0))⟩
    ], #[], #[natA], #[],
      #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.never {}]⟩,
        ⟨false, 2, 0, #[.never .unique]⟩, ⟨false, 3, 0, #[.never .unique]⟩]⟩
  let (env, mutBlkA) := storeV5 env mutDefBlock
  let (env, mutD0A) := storeV5 env ⟨.dPrj ⟨0, mutBlkA⟩, #[], #[], #[], #[]⟩
  let (env, mutD1A) := storeV5 env ⟨.dPrj ⟨1, mutBlkA⟩, #[], #[], #[], #[]⟩
  let (env, undecidedA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, .lam natE (.var 0)⟩, #[], #[natA], #[],
      #[⟨false, 0, 0, #[.undecided {}]⟩, ⟨false, 1, 0, #[.undecided {}]⟩]⟩
  let (env, badDatumTermA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, .lam natE (.var 0)⟩, #[], #[natA], #[],
      #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.zero {}]⟩]⟩
  let (env, badDatumTypeA) := storeV5 env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE natE, .lam natE (.var 0)⟩, #[], #[natA], #[],
      #[⟨false, 0, 0, #[.zero {}]⟩, ⟨false, 1, 0, #[.never {}]⟩]⟩
  -- Kernel acceptance on specVersion = 4 v5 prelude + records
  let acc ← match KernelFront.accept env with
    | .ok acc => pure acc
    | .error r => throw (IO.userError s!"v5Suite: KernelFront.accept failed: {r.report}")
  expect a (acc.records.length == env.consts.size) "v5Suite: accept record count mismatch"
  -- N4 checks
  expect a (tbl.version == 4) "v5Suite: expected specVersion = 4"
  expect a ((KernelFront.Order.checkUserAxiomRoles tbl).toOption.isNone)
    "v5Suite: minimal prelude table should fail checkUserAxiomRoles"
  expect a ((KernelFront.Order.checkUserAxiomRoles fullTable).toOption.isSome)
    "v5Suite: defaultTable should pass checkUserAxiomRoles"
  expect a (KernelFront.policyOf (Ix.Kernel.unknownConstError (.role .trustCompiler)) == some .compilerTrust)
    "v5Suite: policyOf unknownConstError trustCompiler"
  expect a (KernelFront.policyOf (Ix.Kernel.unresolvedConstsError (md := .anon) "test"
      (.const (.role .ofReduceBool) [])) == some .compilerTrust)
    "v5Suite: policyOf unresolvedConstsError ofReduceBool"
  -- Ingress, Reading.build, Annotate & Reference parity on honest roots
  let honestRoots := #[idNatA, idErasedA, idErasedEqA, letBorrowA, letNonDepA,
    proofFnA, polyIdA, sharedFnA, sharedPiGoodA, useNatRecA, irrLetGoodA, mutD0A, mutD1A, undecidedA]
  let seeds : Src.Ingress.Seeds := {
    statement := honestRoots ++ Src.Ingress.pinnedAddresses (KernelFront.pinsOfTable acc.table)
    proofs := #[idErasedEqA]
  }
  let recs ← IO.ofExcept (Src.Ingress.reach env seeds)
  let p0 ← IO.ofExcept (Src.Ingress.readConsts env recs honestRoots)
  let p0 := { p0 with known := { pins := KernelFront.pinsOfTable acc.table } }
  let p0 := { p0 with known := Src.Pinned.known p0 }
  let rd ← IO.ofExcept (KernelFront.Reading.build acc p0)
  let fe := Ix.Kernel.mkFEnv acc.env
  let kernel : KernelFront.Kernel := { acc, rd, fe }
  let ann ← IO.ofExcept (kernel.annotateChecked p0)
  let annRef ← IO.ofExcept (Reference.annotate fe rd p0)
  expect a (ann.eqb annRef) "v5Suite: Annotate and Reference disagree on honest v5 roots"
  let natRecId := (p0.lookup natRecA).getD 0
  expect a (ann.nodes.any fun (k, _) => k == .rule natRecId 0) "v5Suite: Nat.rec rule 0 missing"
  expect a (ann.nodes.any fun (k, _) => k == .rule natRecId 1) "v5Suite: Nat.rec rule 1 missing"
  -- R7 post-K3 mode-tamper refusals (λ, Π input/result, let mode/nonDep, shared variant, mutual block)
  let idNatId := (p0.lookup idNatA).getD 0
  let some (.defn dk ds dl idTy idVal) := p0.decl? idNatId | throw (IO.userError "v5Suite: idNat missing")
  for badMode in ([.erased, .unique, .borrowed, { input := .many, result := .unique }] : List Ixon.V3.AllMode) do
    let badVal := match idVal with
      | .lam b d body => Term.lam { b with mode := badMode } d body
      | t => t
    expect a (match KernelFront.annotate fe rd (p0.setDecl idNatId (.defn dk ds dl idTy badVal)) with
      | .error m => (m.splitOn "a λ binder's contract differs").length > 1
      | .ok _ => false) s!"v5Suite: tampered λ mode {repr badMode} not refused"
  let badPiIn := match idTy with | .pi b d c => Term.pi { b with mode := .unique } d c | t => t
  expect a (match rd.typeCheck (p0.setDecl idNatId (.defn dk ds dl badPiIn idVal)) idNatId with
    | .error m => (m.splitOn "a Π binder's contracts differ").length > 1
    | .ok _ => false) "v5Suite: tampered Π input mode not refused"
  let badPiRes := match idTy with
    | .pi b d c => Term.pi { b with mode := { b.mode with result := .unique } } d c
    | t => t
  expect a (match rd.typeCheck (p0.setDecl idNatId (.defn dk ds dl badPiRes idVal)) idNatId with
    | .error m => (m.splitOn "a Π binder's contracts differ").length > 1
    | .ok _ => false) "v5Suite: tampered Π result mode not refused"
  let letBorrowId := (p0.lookup letBorrowA).getD 0
  let some (.defn dk ds dl lbTy lbVal) := p0.decl? letBorrowId | throw (IO.userError "v5Suite: letBorrow missing")
  let badLetMode := match lbVal with
    | .lam b d (.letE nd _ r ty v body) => Term.lam b d (.letE nd (.value .many) r ty v body)
    | t => t
  expect a (match KernelFront.annotate fe rd (p0.setDecl letBorrowId (.defn dk ds dl lbTy badLetMode)) with
    | .error m => (m.splitOn "a let's contract differs").length > 1
    | .ok _ => false) "v5Suite: tampered let mode not refused"
  let letNonDepId := (p0.lookup letNonDepA).getD 0
  let some (.defn dk ds dl lnTy lnVal) := p0.decl? letNonDepId | throw (IO.userError "v5Suite: letNonDep missing")
  let badLetNd := match lnVal with
    | .lam b d (.letE _ lm r ty v body) => Term.lam b d (.letE false lm r ty v body)
    | t => t
  expect a (match KernelFront.annotate fe rd (p0.setDecl letNonDepId (.defn dk ds dl lnTy badLetNd)) with
    | .error m => (m.splitOn "a let's contract differs").length > 1
    | .ok _ => false) "v5Suite: tampered let nonDep not refused"
  let sharedFnId := (p0.lookup sharedFnA).getD 0
  let some (.defn dk ds dl sfTy sfVal) := p0.decl? sharedFnId | throw (IO.userError "v5Suite: sharedFn missing")
  let badShVal := match sfVal with
    | .lam b d (.app f (.app (.lam sb sd sbody) x m1 r1) m2 r2) =>
      Term.lam b d (.app f (.app (.lam { sb with mode := .many } sd sbody) x m1 r1) m2 r2)
    | t => t
  expect a (match KernelFront.annotate fe rd (p0.setDecl sharedFnId (.defn dk ds dl sfTy badShVal)) with
    | .error m => (m.splitOn "a λ binder's contract differs").length > 1
    | .ok _ => false) "v5Suite: tampered shared variant mode not refused"
  let mutD1Id := (p0.lookup mutD1A).getD 0
  let some (.defn dk ds dl m1Ty m1Val) := p0.decl? mutD1Id | throw (IO.userError "v5Suite: mutD1 missing")
  let badM1Val := match m1Val with | .lam b d body => Term.lam { b with mode := .many } d body | t => t
  expect a (match KernelFront.annotate fe rd (p0.setDecl mutD1Id (.defn dk ds dl m1Ty badM1Val)) with
    | .error m => (m.splitOn "a λ binder's contract differs").length > 1
    | .ok _ => false) "v5Suite: tampered mutual member mode not refused"
  -- N2 fail-closed stored zero-ness datum cross-check
  for (label, badA) in [("badDatumTerm", badDatumTermA), ("badDatumType", badDatumTypeA),
      ("sharedPiBad", sharedPiBadA), ("irrLetBad", irrLetBadA)] do
    let bSeeds : Src.Ingress.Seeds := {
      statement := #[badA] ++ Src.Ingress.pinnedAddresses (KernelFront.pinsOfTable acc.table)
    }
    let bRecs ← IO.ofExcept (Src.Ingress.reach env bSeeds)
    let pB ← IO.ofExcept (Src.Ingress.readConsts env bRecs #[badA])
    let pB := { pB with known := { pins := KernelFront.pinsOfTable acc.table } }
    let pB := { pB with known := Src.Pinned.known pB }
    let rdB ← IO.ofExcept (KernelFront.Reading.build acc pB)
    expect a (match KernelFront.annotate fe rdB pB, Reference.annotate fe rdB pB with
      | .error m1, .error m2 =>
        (m1.splitOn "stored binder datum").length > 1 &&
        (m1.splitOn "disagrees with computed").length > 1 && m1 == m2
      | _, _ => false) s!"v5Suite: {label} did not fail closed identically in Annotate & Reference"
  -- R8 eqn route with plain v5 Lean f.eq_def theorem
  let idErasedId := (p0.lookup idErasedA).getD 0
  let idErasedEqId := (p0.lookup idErasedEqA).getD 0
  let resEqn ← IO.ofExcept (Src.Table.checkEqn p0 idErasedId idErasedEqId)
  expect a (match resEqn with
    | .eqn thm (.lam b0 _ (.lam b1 _ _)) => thm == idErasedEqId && b0.isErased && b1.isDefault
    | _ => false) "v5Suite: R8 checkEqn did not transport subject header modes"
  let tblWithEqn : Src.Table := { resolve := NatMap.leaf.insert idErasedId resEqn }
  let _ ← IO.ofExcept (Src.Table.validate {} { p0 with table := tblWithEqn })
  let _ ← IO.ofExcept (Src.Table.ofCert {} p0 (Src.Table.TableCert.ofTable tblWithEqn))
  let _ ← IO.ofExcept (kernel.annotateChecked { p0 with table := tblWithEqn })
  let some (.defn dk ds dl eTy eVal) := p0.decl? idErasedId | throw (IO.userError "v5Suite: idErased missing")
  let badEVal := match eVal with | .lam b d body => Term.lam { b with mode := .many } d body | t => t
  expect a (match Src.Table.checkEqn (p0.setDecl idErasedId (.defn dk ds dl eTy badEVal)) idErasedId idErasedEqId with
    | .error m => (m.splitOn "eqn-drops-contracts").length > 1
    | .ok _ => false) "v5Suite: R8 mismatched subject header modes not refused"
  -- N5 ModeCheckHook
  expect a (KernelFront.defaultModeCheck acc).isOk "v5Suite: defaultModeCheck failed"
  let denyHook : KernelFront.ModeCheckHook := fun _ => throw { stage := .modeCheck, message := "mode check refused" }
  expect a (match denyHook acc with
    | .error r => r.stage == .modeCheck && r.stage.word == "mode-check"
    | .ok _ => false) "v5Suite: custom ModeCheckHook did not refuse at modeCheck stage"
  IO.println "v5Suite: R7/R8/N2/N4/N5 checks on specVersion=4 v5 prelude passed"

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    for (label, bound, root) in fixtures do
      let (bb, bj) ← read bound
      let ub ← IxCCTests.Support.Envelope.unboundTwin s!"{bound}.ixe"
      let benv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bb)
      let uenv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv ub)
      -- acceptance
      let acc ← match KernelFront.accept benv with
        | .ok acc => pure acc
        | .error e => throw (IO.userError s!"{label}: the kernel refused the role-bound closure: {e}")
      expect a (acc.records.length == benv.consts.size && acc.decls.size > 0)
        s!"{label}: the kernel's entry did not receive every record"
      expect a (isRefusal (KernelFront.accept uenv) .envelope)
        s!"{label}: the unbound twin was not refused as unbound"
      -- ingress, every root produced, Stage A on each certificate
      let rep ← report label bb bj
      expect a (rep.findings.isEmpty && rep.roots.size ≥ 1)
        s!"{label}: ingress refused it or Stage A refused a certificate: {rep.findings}"
      -- refusals of the bytes
      let some b := benv.binding | throw (IO.userError s!"{label}: not role-bound")
      let tampered := { benv with binding := some { b with bytes := b.bytes.push 0 } }
      expect a (isRefusal (KernelFront.accept tampered) .binding)
        s!"{label}: a binding section that does not hash to its address was accepted"
      let some (rootAddr, _) := (← IO.ofExcept (Src.Hints.ofK1Json bj)).roots[0]?
        | throw (IO.userError s!"{label}: the sidecar names no root")
      let some rootBytes := benv.consts[rootAddr]? | throw (IO.userError s!"{label}: no root record")
      let rootConst ← IO.ofExcept (Ixon.V3.decodeConstant rootBytes)
      let some dep := rootConst.value.refs.find? (benv.consts.contains ·)
        | throw (IO.userError s!"{label}: the root references no record")
      let missing := { benv with consts := benv.consts.erase dep }
      expect a ((KernelFront.accept missing).toOption.isNone)
        s!"{label}: a closure missing a record its root references was accepted"
      let some (_, bnat) := (acc.table.bound.find? (·.1 == .nat))
        | throw (IO.userError s!"{label}: the table binds no Nat")
      let natAddr : Ixon.Address := match Ixon.Address.ofBytes? bnat.hash with
        | some x => x
        | none => default
      let unboundNat := { benv with consts := benv.consts.erase natAddr }
      expect a ((KernelFront.accept unboundNat).toOption.isNone)
        s!"{label}: a role table naming a record the closure lacks was accepted"
      -- Stage A
      let cfg : Recheck.Config := { names := [root] }
      let k ← match Recheck.ingress bb bj [root] with
        | .ok k => pure k
        | .error e => throw (IO.userError s!"{label}: kernel ingress: {e.render}")
      let cert ← match Recheck.produce cfg k with
        | .ok c => pure c
        | .error e => throw (IO.userError s!"{label}: kernel produce: {e.render}")
      expect a (Recheck.checkCanonicalRelevance cfg k cert.table cert.relevance)
        s!"{label}: Stage A refused the kernel annotator's own annotation"
      let flipped := { cert.relevance with nodes := flipOne cert.relevance.nodes }
      expect a (flipped != cert.relevance &&
          !Recheck.checkCanonicalRelevance cfg k cert.table flipped)
        s!"{label}: Stage A accepted an annotation with one tag changed"
      -- a program that is not the kernel's reading
      let p := k.program
      let some (_, rootId) := p.roots.head? | throw (IO.userError s!"{label}: no root")
      let wrongValue := p.setTerm (.value rootId) (.natLit 7)
      expect a ((KernelFront.annotate k.kernel.fe k.kernel.rd wrongValue).toOption.isNone)
        s!"{label}: a value that is not the kernel's reading was annotated"
      let ctorIds := (List.range p.size).filter fun c =>
        match p.decl? c with | some (.ctor ..) => true | _ => false
      let some c0 := ctorIds.head? | throw (IO.userError s!"{label}: no constructor")
      let wrongCtor := match p.decl? c0 with
        | some (.ctor s l i x pa f ty) => p.setDecl c0 (.ctor s l i x pa (f + 1) ty)
        | _ => p
      expect a ((KernelFront.Reading.build acc wrongCtor).toOption.isNone)
        s!"{label}: a constructor with another field count was read as the kernel's"
      let wrongAddr : Src.Program := { p with consts := p.consts.modify rootId fun e =>
        { e with addr := Ixon.Address.replicate 7 } }
      expect a ((KernelFront.Reading.build acc wrongAddr).toOption.isNone)
        s!"{label}: a constant keyed by another address was read as the kernel's"
      IO.println s!"{label}: accepted, {acc.records.length} records, {acc.decls.size} declarations; \
        ingress {rep.ingressMs} ms (kernel {rep.acceptMs} ms); Stage A accepts every certificate"
    -- a role-bound closure carrying a constant whose ∀ chain shares one type: the
    -- kernel's entry checks every record, and the chain's levels stay small
    let (tb, _) ← read "fixtures/corpus/phase1-scalar/tuple"
    let tenv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv tb)
    for (name, c) in sharedLevelConstants 200 do
      let bytes := _root_.Ixon.serConstant c
      let env := { tenv with consts := tenv.consts.insert (Ixon.Address.blake3Pure bytes) bytes }
      let t0 ← IO.monoMsNow
      let r ← IO.lazyPure fun _ => KernelFront.accept env
      let t1 ← IO.monoMsNow
      match r with
      | .ok acc =>
        expect a (acc.records.length == tenv.consts.size + 1)
          s!"tuple with the {name} chain: the kernel's entry did not receive every record"
        IO.println s!"tuple with the {name} chain at length 200 ({bytes.size} bytes): accepted, \
          {acc.records.length} records, {t1 - t0} ms"
      | .error e =>
        throw (IO.userError s!"tuple with the {name} chain at length 200: refused: {e}")
    -- every committed closure: the kernel accepts it, but for the three that
    -- are refused for their own reasons; and the report on the small ones
    let mut accepted := 0
    let mut compared := 0
    for path in ← committedClosures do
      let label := path.toString
      let bytes ← IO.FS.readBinFile path
      match Ixon.V3.decodeAnonymousEnv bytes with
      | .error e =>
        -- every committed closure decodes: IxCC's budget applies to what a root reaches
        expect a false s!"{label}: the envelope does not decode: {e}"
      | .ok env =>
        match KernelFront.accept env with
        | .ok _ =>
          expect a (!kernelDeclined.any (label.endsWith ·)) s!"{label}: accepted, but expected declined"
          accepted := accepted + 1
        | .error r =>
          -- the diagnostics fixture holds `sorry` on purpose
          expect a (kernelDeclined.any (label.endsWith ·) && (match r.outcome with | some .declined => true | _ => false) &&
              (r.message.splitOn "sorryAx").length > 1)
            s!"{label}: the kernel refused it: {r.render}"
          -- what `ixcc` prints: the kernel's line verbatim, then the plain-words line
          if kernelDeclined.any (label.endsWith ·) then
            expect a (r.policy == some .sorryAx) s!"{label}: not classified as the sorryAx policy decline"
            if let some sidecar ← sidecarOf path then
              let bj ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
              let expected := r.render ++ "\n" ++ KernelFront.PolicyDecline.sorryAx.explain
              expect a (match Recheck.ingress bytes bj [] with
                  | .error e => e.stage == .ingress && e.code == "kernel" && e.message == expected
                  | .ok _ => false)
                s!"{label}: ingress did not report the kernel's line and the explanation"
        if reachRefused.any (label.endsWith ·) then
          -- every root reaches a record over IxCC's budget: refused at decode, the record named
          if let some sidecar ← sidecarOf path then
            let bj ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
            expect a (match Recheck.ingress bytes bj [] with
                | .error e => e.stage == .ingress && e.code == "decode" &&
                    (e.message.splitOn "constant exceeds the consumer budget (record").length > 1
                | .ok _ => false)
              s!"{label}: ingress did not refuse the reached over-budget record at decode"
        else if bytes.size < reportBytes then
          if let some sidecar ← sidecarOf path then
            let bj ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
            let rep ← report label bytes bj
            if kernelDeclined.any (label.endsWith ·) then
              -- the diagnostics fixture: ingress declines it (the kernel, `sorry`)
              expect a (rep.bound && rep.findings.size == 1 &&
                  rep.findings.all fun f => f.startsWith "ingress: " &&
                    (f.splitOn "declined").length > 1 && (f.splitOn "sorryAx").length > 1)
                s!"{label}: expected only ingress to decline (sorryAx): {rep.findings}"
            else
              expect a (rep.bound && rep.findings.isEmpty)
                s!"{label}: ingress refused it or Stage A refused a certificate: {rep.findings}"
            compared := compared + 1
    IO.println s!"every committed closure: {accepted} accepted by the kernel, the reached-budget and the \
      kernel's refusals as expected; {compared} under {reportBytes} bytes run through ingress, \
      the producer and Stage A, root by root"
    -- the role-bound test builder, and the hostile enumeration case ported to it
    for line in ← Bound.run a do IO.println line
    IxCCTests.KernelFront.Hints.run a
    -- the annotator's λ-runs against the per-λ reference, on every committed closure the
    -- kernel accepts and ingress reads, and on the adversarial programs (`LamRuns`)
    let mut pairs := #[]
    for path in ← committedClosures do
      let label := path.toString
      unless kernelDeclined.any (label.endsWith ·) || reachRefused.any (label.endsWith ·) do
        -- the k1 family's sidecar is `equations.json` beside its closure
        let plain := path.withFileName "equations.json"
        match ← sidecarOf path with
        | some sidecar => pairs := pairs.push (path, sidecar)
        | none => if ← plain.pathExists then pairs := pairs.push (path, plain)
    for line in ← LamRuns.run a pairs do IO.println line
    -- Ixon v5 & specVersion = 4 checks (R7, R8, N2, N4, N5) on IxCK's committed v5 prelude
    v5Suite a
    -- `ixcc` at the command line (`Cli.suite`): limits, re-execution, signals, a deep record
    let dir ← IO.FS.createTempDir
    try
      let (k, s) ← Cli.suite dir
      a.modify (· + k)
      IO.println s!"ixcc at the command line: {k} assertions, {s} skipped"
    finally IO.FS.removeDirAll dir
    IO.println s!"tests-kernel-front: {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: kernel front end: {error}"
    return false

end IxCCTests.KernelFront
