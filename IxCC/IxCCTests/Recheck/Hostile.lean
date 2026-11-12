import IxCC.CompileClaim
import IxCC.Ring0
import IxCC.Recheck.Linked
import IxCC.Cli
import IxCC.X86.Layout.Basic
import IxCC.Anf.Semantics
import IxCCTests.Support.Bound
import IxCCTests.Src.Support

/-! # Hostile inputs to the verifiers and the middle end's replay

Regression tests for hostile certificates and inputs found in review. Programs
are added to a committed role-bound closure with the role-bound test builder
(`IxCCTests.Support.Bound`: each inductive with its recursor, no user axiom),
written as Ixon v4 bytes and read through `Recheck.ingress`, the route a real
`.ixe` takes: the certified kernel accepts every one of them, so each refusal
below is the verifier's own, at the stage and code the test names.

* **A relevance retagging**. A certificate retagging a relevant parameter of
  `idc (c : E) : E := c` and its call site in `main := idc c₁` as irrelevant
  compiles, without the canonical check, to an object returning the wrong
  constructor; `Recheck.run`, `CompileClaim.verifyProgram`,
  `checkClaimProgram`, `verifyBytes` and both `Ring0Sip` verifiers refuse it.
  (The regression was first found on a closure with no pinned identity, on
  which `checkCanonical` was once skipped; a role-bound closure binds `Nat`,
  `Bool` and `Eq`, so that precondition cannot be built: the refusal itself is
  what is kept.) The enumeration has three constructors; a two-constructor
  one is the base's own `Bool`, kept as a control.
* **Stage A on `ixcc check-cert`** (the canonical-annotation check), and the
  certified kernel's acceptance of the whole closure on every byte-level entry
  point: an ill-typed record the program never reaches declines the artifact.
* **The root signature checks, the specialisation bound and the
  frontier dedupe of the layout's reachability walk**.
* **The `--rc auto` immortal fallback** on the hostile annotated
  program, and `check-cert` refusing `--rc`.
* **A certificate's `lazy` rows** (on the committed fixture
  `phase2-closures/sparse`, not the builder): a row for an ordinary
  definition, a sparse casesOn's row at another arity, or its row beside a
  `resolve` entry that replaces its value, refused at the table.
* **Middle-end budgets**. A single hostile `inline` step, at the
  size that crashed `ixcc check-cert` with a stack overflow, through every
  verifier; an inline round over many callers; a walk that copies past its
  budget; a specialisation over an exponentially shared value tree. Each must
  be refused with an ordinary error, not by running out of stack, memory or
  time. And the producer's inline-round retry: a round the re-run refuses for
  one caller is retried without it, and a program whose retried round takes it
  past a budget checked later compiles through the run without the retry.
  And the shrink walk's pending join entry (case-of-case as a move): equal
  to its source at every clock, correct forced on through its inlining
  fallback, not taken for a large alternative selected twice; and its
  test-only switch confined to the producer (that the checker re-derives the
  choice is `tests-corpus`'s). -/

namespace IxCCTests.Recheck.Hostile

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Src (Assert expect annotationNoCanonical)
open IxCCTests.IxonV3.Builder (store block arrow lambda)
open IxCCTests.Support.Bound (loadBase addEnum addSimple Field)

abbrev Addr := IxCC.Ixon.Address
abbrev X := IxCC.Ixon.V3.Expr

def defn (ty val : X) : ConstantInfo := .defn ⟨.defn, .safe, 0, ty, val⟩

/-! ## Programs as bytes -/

/-- An environment's role-bound envelope (every environment here extends the
role-bound base, `Support.Bound.write`). -/
def bytes (env : Env) : ByteArray := IxCCTests.Support.Bound.write env

/-- The enumeration at `refs[0]`. -/
def enumC : X := .ref 0 #[]

structure Base where
  env : Env
  enumI : Addr
  ctors : Array Addr
  /-- `idc (c : E) : E := c`. -/
  idc : Addr
  /-- whether the enumeration is the base's own block (two constructors: `Bool`) -/
  existing : Bool

/-- `inductive E | c₀ | … | cₙ₋₁ : Type` (with its recursor) and
`idc (c : E) : E := c`, added to the role-bound base `env0`. -/
def base (env0 : Env) (n : Nat) : Base := Id.run do
  let (e, en) := addEnum env0 n
  let (e, idc) := store e ⟨defn (arrow enumC enumC) (lambda enumC (.var 0)), #[], #[en.ind], #[]⟩
  return { env := e, enumI := en.ind, ctors := en.ctors, idc, existing := en.existing }

/-- An `ixcc/k1-equations/1` sidecar naming `roots`, with no equations. -/
def sidecar (roots : List (String × Addr)) : Lean.Json :=
  Lean.Json.mkObj [
    ("format", Lean.Json.str "ixcc/k1-equations/1"),
    ("roots", Lean.Json.arr (roots.map fun (n, a) =>
      Lean.Json.mkObj [("name", Lean.Json.str n), ("address", Lean.Json.str (toString a))]).toArray),
    ("equations", Lean.Json.arr #[])]

/-- The enumeration program: `main : E := idc c₁`, and a root `rᵢ := cᵢ` per
constructor, so that every constructor is emitted. With `illTyped`, the
environment also holds an unreachable constant whose value does not have its
type. -/
def enumEnv (env0 : Env) (n : Nat) (illTyped : Bool := false) : Env × Addr × List (String × Addr) := Id.run do
  let b := base env0 n
  let (e, main) := store b.env
    ⟨defn enumC (.app (.ref 1 #[]) (.ref 2 #[])), #[], #[b.enumI, b.idc, b.ctors[1]!], #[]⟩
  let mut e := e
  let mut roots := [("main", main)]
  for (c, i) in b.ctors.toList.zipIdx do
    let (e', r) := store e ⟨defn enumC (.ref 1 #[]), #[], #[b.enumI, c], #[]⟩
    e := e'
    roots := roots ++ [(s!"r{i}", r)]
  if illTyped then
    e := (store e ⟨defn (arrow enumC enumC) (.ref 1 #[]), #[], #[b.enumI, b.ctors[0]!], #[]⟩).1
  return (e, main, roots)

/-- The inline amplifier: `k (a b : E) : E := a`; `f x` is a balanced `k`-tree of
depth `dF` over `x` (`2^(dF+1) - 1` calls of `k`); `g x` a balanced `k`-tree
of depth `dG` whose `2^dG` leaves are `f x`; `main := g c₁`. Every stored
expression is a few nodes deep: the trees are `share` DAGs. -/
def ampEnv (env0 : Env) (dF dG : Nat) : Env × Addr × Addr × Addr := Id.run do
  let b := base env0 3
  let (e, k) := store b.env
    ⟨defn (arrow enumC (arrow enumC enumC)) (lambda enumC (lambda enumC (.var 1))), #[], #[b.enumI], #[]⟩
  let mut shF : Array X := #[.app (.app (.ref 1 #[]) (.var 0)) (.var 0)]
  for i in [1:dF+1] do
    let prev : X := .share (i - 1).toUInt64
    shF := shF.push (.app (.app (.ref 1 #[]) prev) prev)
  let (e, f) := store e
    ⟨defn (arrow enumC enumC) (lambda enumC (.share dF.toUInt64)), shF, #[b.enumI, k], #[]⟩
  let mut shG : Array X := #[.app (.ref 2 #[]) (.var 0)]
  for i in [1:dG+1] do
    let prev : X := .share (i - 1).toUInt64
    shG := shG.push (.app (.app (.ref 1 #[]) prev) prev)
  let (e, g) := store e
    ⟨defn (arrow enumC enumC) (lambda enumC (.share dG.toUInt64)), shG, #[b.enumI, k, f], #[]⟩
  let (e, main) := store e
    ⟨defn enumC (.app (.ref 1 #[]) (.ref 2 #[])), #[], #[b.enumI, g, b.ctors[1]!], #[]⟩
  return (e, f, g, main)

/-! ## Certificates and objects without the canonical check -/

/-- A certificate for annotation `ann` whose other parts the honest oracles
make for it, through the front end without `checkCanonical` (which refuses a
hostile annotation). -/
def mkCert (cfg : Recheck.Config) (P : Src.Program) (tc : Src.Table.TableCert)
    (ann : Src.Relevance.Ann) : Except Recheck.Err Recheck.Cert := do
  let table ← (Src.Table.ofCert cfg.table P tc).mapError fun m =>
    ({ stage := .table, code := "table", message := m } : Recheck.Err)
  let (src, checked) ← match annotationNoCanonical { P with table } ann with
    | .ok r => pure r
    | .error _ => throw ({ stage := .relevance, code := "relevance",
                           message := "tiers S and C refuse the annotation" } : Recheck.Err)
  let (lam, _) ← (Lam.erase src checked).mapError Recheck.Err.ofErase
  let trace ← (Anf.Pipeline.produce cfg.budgets lam).mapError fun m =>
    ({ stage := .anf, code := "anf.produce", message := m } : Recheck.Err)
  let anf := ((trace.stages.getLast?).map (·.2)).getD default
  let fir ← (Fir.lower anf).mapError Recheck.Err.ofFir
  let C := Cfg.lower (Own.immortal fir)
  Recheck.checkParams cfg C (C.exports.zipIdx.map fun (f, i) => (i, f))
  let lowered ← (Rt.lower { names := cfg.names } C).mapError Recheck.Err.ofRt
  let (xv, _) ← (Xv.Select.run lowered.program).mapError Recheck.Err.ofSelect
  let r ← (Xv.Alloc.run cfg.env xv).mapError fun m =>
    ({ stage := .alloc, code := "alloc.fallback", message := m } : Recheck.Err)
  let layouts := Xv.Stacking.produce r.program
  let stacked ← (Xv.Stacking.run r.program layouts lowered.reps cfg.env).mapError
    (Recheck.Err.ofBackend ∘ .stacking)
  let order := X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape
  pure { table := tc, relevance := ann, mid := trace.cert, alloc := r.outs, frames := layouts, order }

/-- The object `Recheck.run` would make from `c` if the front end did not run
`checkCanonical`: `Recheck.run` with `Src.Recheck.annotation` replaced by
`annotationNoCanonical`. A claim naming it is what an attacker would submit. -/
def objectNoCanonical (cfg : Recheck.Config) (P : Src.Program) (c : Recheck.Cert) :
    Except Recheck.Err ByteArray := do
  let table ← (Src.Table.ofCert cfg.table P c.table).mapError fun m =>
    ({ stage := .table, code := "table.entry", message := m } : Recheck.Err)
  let (src, checked) ← match annotationNoCanonical { P with table } c.relevance with
    | .ok r => pure r
    | .error _ => throw ({ stage := .relevance, code := "relevance",
                           message := "tiers S and C refuse the annotation" } : Recheck.Err)
  let (lam, _) ← (Lam.erase src checked).mapError Recheck.Err.ofErase
  let (_, _, _, C) ← Recheck.middle c src lam
  Recheck.checkParams cfg C (List.zipIdx C.exports |>.map fun (f, i) => (i, f))
  (Rt.checkSwitches C).mapError Recheck.Err.ofSwitch
  let lowered ← (Rt.lower { names := cfg.names } C).mapError Recheck.Err.ofRt
  let root := (src.roots.head?.map (·.1)).getD default
  let (_, xl, stacked, program, exports) ← Recheck.backTyped cfg lowered root c
  Recheck.checkSymbols stacked.exports
  let backend ← (Backend.finish xl.main stacked program exports
    (cfg.provenance.getD (Recheck.defaultProvenance root))).mapError Recheck.Err.ofBackend
  pure backend.object

/-- The driver for the Ring-0 checks. -/
def driver : X86.Driver where
  base   := 0x00100000
  region := 0x10000000
  size   := 0x00010000
  budget := 0x00002000
  sp     := 0x20000008
  ret    := 0x70000001
  init   := fun _ => 0
  flags  := {}
  other  := fun _ => 0

def ofErr {α : Type} (label : String) (r : Except Recheck.Err α) : IO α :=
  match r with
  | .ok x => pure x
  | .error e => throw (IO.userError s!"{label}: {e.render}")

/-- The enumeration program (for two constructors, the base's `Bool`) with
its honest certificate, and the hostile one: `idc`'s parameter and `main`'s
argument retagged `.type`. -/
structure Case where
  bytes : ByteArray
  json : Lean.Json
  inp : Recheck.Input
  cfg : Recheck.Config
  main : Addr
  honest : Recheck.Cert
  hostile : Recheck.Cert
  /-- whether the enumeration is the base's own `Bool` -/
  existing : Bool

def mkCase (n : Nat) : IO Case := do
  let env0 ← loadBase
  let (env, main, roots) := enumEnv env0 n
  let bs := bytes env
  let json := sidecar roots
  let inp ← ofErr s!"enum-{n}: ingress" (Recheck.ingress bs json [])
  let P := inp.program
  let cfg := Recheck.Config.forInput {} inp
  let honest ← ofErr s!"enum-{n}: produce" (Recheck.produce cfg inp)
  let b := base env0 n
  let some idcId := P.lookup b.idc | throw (IO.userError s!"enum-{n}: idc not ingested")
  let some mainId := P.lookup main | throw (IO.userError s!"enum-{n}: main not ingested")
  let hostileAnn : Src.Relevance.Ann :=
    { honest.relevance with
      consts := honest.relevance.consts.modify idcId fun cr =>
        { cr with params := cr.params.map fun _ => .type }
      nodes := honest.relevance.nodes.map fun (k, tags) =>
        if k == Src.TermKey.value mainId then
          (k, tags.map fun t => match t with
            | .arg _ => .arg .type
            | t => t)
        else (k, tags) }
  let hostile ← ofErr s!"enum-{n}: hostile certificate" (mkCert cfg P honest.table hostileAnn)
  return { bytes := bs, json, inp, cfg, main, honest, hostile, existing := b.existing }

/-! ## The program-level and byte-level verifiers on a relevance retagging -/

def pinFree (a : Assert) (n : Nat) : IO String := do
  let c ← mkCase n
  let P := c.inp.program
  let cfg := c.cfg
  let pinned := P.known.nat.isSome && P.known.bool.isSome && P.known.eq.isSome
  -- the role-bound base binds `Nat`, `Bool` and `Eq`; two constructors are its `Bool`
  expect a pinned s!"enum-{n}: the base's pinned identities are not all bound"
  expect a (c.existing == (n == 2)) s!"enum-{n}: the base's Bool block {c.existing}"
  -- The honest certificate is accepted everywhere, and its object returns `c₁`.
  let art ← ofErr s!"enum-{n}: Recheck.run (honest)" (Recheck.run cfg P c.honest)
  let claim : CompileClaim :=
    { env := c.inp.env.root, roleTable := c.inp.env.bindingAddress, target := c.main
      policy := .immortal, abiArity := 0
      elfHash := Address.blake3Pure art.object }
  let text := c.honest.toText
  let sip : Ring0.Ring0Sip := { cfg, claim, certText := text, driver }
  expect a (CompileClaim.verifyProgram cfg P claim text) s!"enum-{n}: verifyProgram refused the honest claim"
  expect a (CompileClaim.checkClaimProgram cfg P claim text).isOk
    s!"enum-{n}: checkClaimProgram refused the honest claim"
  expect a (CompileClaim.verifyBytes cfg c.bytes c.json claim text) s!"enum-{n}: verifyBytes refused the honest claim"
  expect a (sip.verifyProgram P) s!"enum-{n}: Ring0Sip.verifyProgram refused the honest SIP"
  expect a (sip.verifyBytes c.bytes c.json) s!"enum-{n}: Ring0Sip.verifyBytes refused the honest SIP"
  expect a ((art.linked driver).run (0, []) 1000000 matches .ok (some (.ctor 1 [])))
    s!"enum-{n}: the honest object does not return constructor 1"
  -- The hostile certificate: tiers S and C accept its annotation, and without
  -- the canonical check it would compile to a different object.
  let hostileObj ← ofErr s!"enum-{n}: the hostile object" (objectNoCanonical cfg P c.hostile)
  expect a (hostileObj != art.object) s!"enum-{n}: the hostile annotation does not change the object"
  match Recheck.run cfg P c.hostile with
  | .ok _ => expect a false s!"enum-{n}: Recheck.run accepted the hostile certificate"
  | .error e =>
    expect a (e.stage == .relevance && e.code == "relevance-S1")
      s!"enum-{n}: Recheck.run refused the hostile certificate, but not by checkCanonical: {e.render}"
  let hclaim := { claim with elfHash := Address.blake3Pure hostileObj }
  let htext := c.hostile.toText
  let hsip := { sip with claim := hclaim, certText := htext }
  expect a (!CompileClaim.verifyProgram cfg P hclaim htext) s!"enum-{n}: verifyProgram accepted the hostile claim"
  expect a (!(CompileClaim.checkClaimProgram cfg P hclaim htext).isOk)
    s!"enum-{n}: checkClaimProgram accepted the hostile claim"
  expect a (!CompileClaim.verifyBytes cfg c.bytes c.json hclaim htext)
    s!"enum-{n}: verifyBytes accepted the hostile claim"
  expect a (!hsip.verifyProgram P) s!"enum-{n}: Ring0Sip.verifyProgram accepted the hostile SIP"
  expect a (!hsip.verifyBytes c.bytes c.json) s!"enum-{n}: Ring0Sip.verifyBytes accepted the hostile SIP"
  return s!"enum-{n} ({if c.existing then "the base's Bool" else "a new enumeration"}): honest claim \
    accepted by every verifier, object returns constructor 1; hostile claim (object {hostileObj.size} \
    bytes) refused by Recheck.run (relevance-S1), verifyProgram, checkClaimProgram, verifyBytes and \
    both Ring0Sip verifiers"

/-! ## Stage A on the command line, and the kernel's acceptance of the whole closure -/

/-- `ixcc check-cert` on files in `dir`, in process, returning the error. -/
def checkCert (dir : System.FilePath) (cert : Recheck.Cert) (extra : List String) :
    IO (Except Recheck.Err Unit) := do
  IO.FS.writeFile (dir / "cert.json") cert.toText
  let o ← IO.ofExcept (IxCC.Cli.parse (["check-cert", (dir / "c.ixe").toString, "--equations",
    (dir / "c.json").toString, "--cert", (dir / "cert.json").toString] ++ extra))
  (IxCC.Cli.execute o).run

def cliStageA (a : Assert) : IO String := IO.FS.withTempDir fun dir => do
  let c ← mkCase 3
  IO.FS.writeBinFile (dir / "c.ixe") c.bytes
  IO.FS.writeFile (dir / "c.json") c.json.pretty
  match ← checkCert dir c.honest [] with
  | .ok () => expect a true ""
  | .error e => expect a false s!"check-cert refused the honest certificate: {e.render}"
  -- The hostile certificate (also refused later, by `checkCanonical`, with
  -- `relevance-S1`), and the honest one with its annotated terms listed in
  -- reverse: the same annotation to every checker but Stage A's equality.
  let reversed := { c.honest with relevance := { c.honest.relevance with
    nodes := c.honest.relevance.nodes.reverse } }
  expect a (reversed.relevance != c.honest.relevance) "the reversed annotation equals the honest one"
  for (label, cert) in [("hostile", c.hostile), ("reordered", reversed)] do
    match ← checkCert dir cert [] with
    | .ok () => expect a false s!"check-cert accepted the {label} certificate"
    | .error e =>
      expect a (e.stage == .relevance && e.code == "relevance-canonical")
        s!"check-cert refused the {label} certificate, but not by Stage A: {e.render}"
  return "check-cert: the honest certificate accepted; R1's hostile one and the honest one reordered refused \
    by Stage A (relevance-canonical)"

/-- `ixcc` on a command line, in process, returning the error. -/
def runCli (args : List String) : IO (Except Recheck.Err Unit) := do
  let o ← IO.ofExcept (IxCC.Cli.parse args)
  (IxCC.Cli.execute o).run

/-- An environment holding an ill-typed constant the program never reaches:
the certified kernel's acceptance is of the whole closure, so ingress declines
it (`ingress: kernel`, declined: a type mismatch; the kernel does not take a
failed conversion search as evidence that the input is wrong), and with it every
byte-level entry point, whatever the claim; the same program without that record
is accepted (`mkCase`). The flag that skipped typing is gone. -/
def kernelWhole (a : Assert) : IO String := IO.FS.withTempDir fun dir => do
  let c ← mkCase 3
  let env0 ← loadBase
  let (ill, _, _) := enumEnv env0 3 (illTyped := true)
  let bs := bytes ill
  let r := Recheck.ingress bs c.json []
  let declined := fun (e : Recheck.Err) => e.stage == .ingress && e.code == "kernel" &&
    (e.message.splitOn "(declined)").length > 1 && (e.message.splitOn "type mismatch").length > 1
  expect a (match r with | .error e => declined e | .ok _ => false)
    s!"ill-typed: ingress did not decline the unreachable ill-typed record: \
      {match r with | .error e => e.render | .ok _ => "accepted"}"
  let illRoot := (← IO.ofExcept (decodeAnonymousEnv bs)).root
  let art ← ofErr "ill-typed: Recheck.run (honest)" (Recheck.run c.cfg c.inp.program c.honest)
  let claim : CompileClaim :=
    { env := illRoot, roleTable := c.inp.env.bindingAddress, target := c.main
      policy := .immortal, abiArity := 0, elfHash := Address.blake3Pure art.object }
  let text := c.honest.toText
  expect a (CompileClaim.makeClaim c.cfg bs c.json matches .error _) "ill-typed: makeClaim accepted"
  expect a (!CompileClaim.verifyBytes c.cfg bs c.json claim text) "ill-typed: verifyBytes accepted"
  expect a (!(CompileClaim.checkClaim c.cfg bs c.json claim text).isOk) "ill-typed: checkClaim accepted"
  let sip : Ring0.Ring0Sip := { cfg := c.cfg, claim, certText := text, driver }
  expect a (!sip.verifyBytes bs c.json) "ill-typed: Ring0Sip.verifyBytes accepted"
  IO.FS.writeBinFile (dir / "c.ixe") bs
  IO.FS.writeFile (dir / "c.json") c.json.pretty
  match ← checkCert dir c.honest [] with
  | .ok () => expect a false "ill-typed: check-cert accepted"
  | .error e => expect a (declined e) s!"ill-typed: check-cert refused, but not by the kernel: {e.render}"
  match ← runCli ["compile", (dir / "c.ixe").toString, "--equations", (dir / "c.json").toString,
      "-o", (dir / "c.o").toString] with
  | .ok () => expect a false "ill-typed: compile accepted"
  | .error e => expect a (declined e) s!"ill-typed: compile refused, but not by the kernel: {e.render}"
  expect a (!(IxCC.Cli.parse ["compile", "c.ixe", "--equations", "c.json", "-o", "c.o",
      "--no-typecheck"]).toBool) "--no-typecheck is still accepted"
  return "an unreachable ill-typed record: ingress declines the artifact (kernel, declined, type \
    mismatch), so makeClaim, verifyBytes, checkClaim, Ring0Sip.verifyBytes, check-cert and compile \
    refuse it; --no-typecheck is a usage error"

/-! ## The root signature checks and the specialisation bound -/

def rootChecks (a : Assert) : IO String := do
  let l ← IxCCTests.Src.loadBench "gcd"
  let P := l.program
  let some (addr, const) := P.roots.head? | throw (IO.userError "gcd: no root")
  let root : Recheck.Root :=
    { name := "entry", const, addr, fn := 0, symbol := "cx_entry", params := 2, ty := some ({}, .nat) }
  expect a (CompileClaim.rootParamsAllNat P root) "gcd entry: two Nat parameters refused"
  expect a (CompileClaim.checkImmortalRoot P root) "gcd entry: immortal root refused"
  -- The parameter count must be the type's telescope length
  expect a (!CompileClaim.rootParamsAllNat P { root with params := 1 })
    "N4: a root passed fewer parameters than its type takes"
  expect a (!CompileClaim.rootParamsAllNat P { root with params := 3 })
    "N4: a root passed more parameters than its type takes"
  -- An immortal result is a scalar or an enumeration of field-free constructors
  expect a (CompileClaim.isImmortalViewType { inds := [[[], []]] } (.ind 0)) "a two-constructor enumeration"
  expect a (!CompileClaim.isImmortalViewType { inds := [[[], [.nat]]] } (.ind 0))
    "N4: a constructor with a field accepted as an immortal view"
  expect a (!CompileClaim.isImmortalViewType { inds := [[]] } (.ind 0)) "N4: an empty inductive accepted"
  expect a (!CompileClaim.isImmortalViewType {} (.ind 0)) "N4: an unknown inductive accepted"
  -- At most 64 decisions per specialisation step, masks of at most 64 parameters
  let d : Anf.Specialize.Decision := { caller := 0, callee := 1, mask := [true] }
  let spec := fun (ds : List Anf.Specialize.Decision) => Recheck.checkMidCert { steps := [.specialize { decisions := ds }] }
  expect a (spec (List.replicate 64 d)).isOk "N6: 64 decisions refused"
  expect a (!(spec (List.replicate 65 d)).isOk) "N6: 65 decisions accepted"
  expect a (spec [{ d with mask := List.replicate 64 true }]).isOk "N6: a 64-parameter mask refused"
  expect a (!(spec [{ d with mask := List.replicate 65 true }]).isOk) "N6: a 65-parameter mask accepted"
  return "N4: rootParamsAllNat refuses a parameter count other than the telescope's; isImmortalViewType \
    refuses fields and empty inductives. N6: checkMidCert refuses 65 decisions and 65-parameter masks"

/-! ## The frontier dedupe in the layout's reachability walk -/

/-- A chain of `n` balanced joins: blocks `2i` and `2i + 1` both branch to
`2i + 2` and `2i + 3`. Each step's frontier lists every target of every fresh
block, so it holds four entries; without the dedupe (`reachStep` expanding a
block the frontier lists twice only once) it doubles at every join. -/
def reachDedupe (a : Assert) : IO String := do
  let n := 40
  let blk (i : Nat) : X86.Block :=
    { instructions := #[]
      terminator := if 2 * (i / 2) + 2 < 2 * n then
          .branch default [] default (UInt32.ofNat (2 * (i / 2) + 2)) (UInt32.ofNat (2 * (i / 2) + 3))
        else .ret }
  let m : X86.Layout.NatMap X86.Block := (List.range (2 * n)).foldl (fun m i => m.insert i (blk i)) {}
  let mut seen : X86.Layout.NatSet := {}
  let mut frontier : List Nat := [0, 1]
  let mut widest := 0
  for _ in [0:n] do
    let (s, next) := X86.Layout.reachStep m seen frontier
    seen := s
    frontier := next
    widest := max widest next.length
    expect a (next.length ≤ 4) s!"S10: a frontier of {next.length} blocks after a balanced join"
  expect a ((X86.Layout.reach m (2 * n + 1) {} [0, 1]).size == 2 * n) "S10: reach misses blocks"
  return s!"S10: {n} balanced joins, widest frontier {widest} entries, every block reached"

/-! ## `--rc auto` and `makeClaim` fall back to the immortal policy -/

/-- A one-constructor, two-field structure over the type at `field`, with its
recursor (`Support.Bound.addSimple`). -/
def addPair (env : Env) (field : Addr) : Env × IxCCTests.Support.Bound.Ind :=
  addSimple env #[#[.ext field, .ext field]]

/-- The hostile `auto` program with a claim-eligible first root, `main : E := idc c₁`;
`Box := mk E E`, `Two := mk Box Box`, `dupf (b : Box) : Two := Two.mk b b`
(duplicates a heap parameter) and `lin (1 c : E) : E := c` (a linear binder
contract, which puts the program outside `Own.Plain.programDomain`). -/
def autoEnv (env0 : Env) : Env × List (String × Addr) := Id.run do
  let b := base env0 3
  let (e, box) := addPair b.env b.enumI
  let boxI := box.ind
  let (e, two) := addPair e boxI
  let twoI := two.ind
  let twoMk := two.ctors[0]!
  let (e, main) := store e
    ⟨defn enumC (.app (.ref 1 #[]) (.ref 2 #[])), #[], #[b.enumI, b.idc, b.ctors[1]!], #[]⟩
  let (e, dupf) := store e
    ⟨defn (arrow (.ref 0 #[]) (.ref 1 #[]))
        (lambda (.ref 0 #[]) (.app (.app (.ref 2 #[]) (.var 0)) (.var 0))),
      #[], #[boxI, twoI, twoMk], #[]⟩
  let (e, lin) := store e
    ⟨defn (.all BinderContract.linear .shared enumC enumC) (.lam BinderContract.linear enumC (.var 0)),
      #[], #[b.enumI], #[]⟩
  -- a root per constructor, so that every constructor is emitted and `main`'s
  -- result has a readback signature
  let mut e := e
  let mut roots := [("main", main), ("dupf", dupf), ("lin", lin)]
  for (c, i) in b.ctors.toList.zipIdx do
    let (e', r) := store e ⟨defn enumC (.ref 1 #[]), #[], #[b.enumI, c], #[]⟩
    e := e'
    roots := roots ++ [(s!"r{i}", r)]
  return (e, roots)

/-- `execute` on a command line, in process. -/
def cli (args : List String) : IO (Except Recheck.Err Unit) := do
  let o ← IO.ofExcept (IxCC.Cli.parse args)
  (IxCC.Cli.execute o).run

def autoFallback (a : Assert) : IO String := IO.FS.withTempDir fun dir => do
  let (env, roots) := autoEnv (← loadBase)
  let bs := bytes env
  let json := sidecar roots
  let inp ← ofErr "auto: ingress" (Recheck.ingress bs json [])
  let cfg := Recheck.Config.forInput {} inp
  -- plain RC is selected, and refused
  let front ← ofErr "auto: produceFir" (Recheck.RcReplay.produceFir cfg inp)
  expect a (Own.Plain.selectRcPolicyForSrc front.src front.fir == .plainRc) "auto: plain RC not selected"
  expect a (!Own.Plain.programDomain front.fir) "auto: the program is in the plain-RC domain"
  expect a (Recheck.RcReplay.produce cfg inp matches .error _) "auto: plain RC accepted the program"
  -- `produceAuto` falls back to the immortal policy, and says why
  match Recheck.RcReplay.produceAuto cfg inp with
  | .ok (.immortal cert art _ reason) =>
    expect a (reason.code == "own.plain") s!"auto: the plain-RC refusal is {reason.render}"
    let again ← ofErr "auto: Recheck.run" (Recheck.run cfg inp.program cert)
    expect a (again.object == art.object) "auto: the fallback's object is not Recheck.run's"
  | .ok _ => expect a false "auto: produceAuto did not fall back to the immortal policy"
  | .error e => expect a false s!"auto: produceAuto refused the program: {e.render}"
  -- the claim binds the policy compiled under, and verifies
  let (claim, text, elf) ← IO.ofExcept (CompileClaim.makeClaim cfg bs json)
  expect a (claim.policy == .immortal) "auto: makeClaim's claim does not bind the immortal policy"
  expect a (claim.elfHash == Address.blake3Pure elf) "auto: the claim's hash is not the object's"
  expect a (CompileClaim.verifyBytes cfg bs json claim text) "auto: verifyBytes refused makeClaim's claim"
  expect a (!CompileClaim.verifyBytes cfg bs json { claim with policy := .plainRc } text)
    "auto: verifyBytes accepted the claim under the plain-RC policy"
  -- the command line: `--rc auto` compiles under the immortal policy, `--rc on` refuses
  IO.FS.writeBinFile (dir / "c.ixe") bs
  IO.FS.writeFile (dir / "c.json") json.pretty
  let common := [(dir / "c.ixe").toString, "--equations", (dir / "c.json").toString]
  match ← cli (["compile"] ++ common ++ ["--rc", "auto", "-o", (dir / "auto.o").toString,
      "--emit-cert", (dir / "auto.cert").toString]) with
  | .ok () => expect a true ""
  | .error e => expect a false s!"auto: compile --rc auto refused: {e.render}"
  let certText := (← IO.FS.readFile (dir / "auto.cert")).trimAscii.toString
  expect a (!certText.startsWith "[\"ixcc/rc-cert/2\"") "auto: compile --rc auto emitted a plain-RC certificate"
  match ← cli (["check-cert"] ++ common ++ ["--cert", (dir / "auto.cert").toString]) with
  | .ok () => expect a true ""
  | .error e => expect a false s!"auto: check-cert refused --rc auto's certificate: {e.render}"
  match ← cli (["compile"] ++ common ++ ["--rc", "on", "-o", (dir / "on.o").toString]) with
  | .ok () => expect a false "auto: compile --rc on accepted the program"
  | .error e => expect a (e.code == "own.plain") s!"auto: compile --rc on refused it with {e.render}"
  -- `check-cert` takes its policy from the certificate: `--rc` is a usage error
  expect a (!(IxCC.Cli.parse (["check-cert"] ++ common ++ ["--cert", "c.cert", "--rc", "auto"])).toBool)
    "check-cert accepted --rc"
  return "R1's auto program: plain RC selected and refused (own.plain); produceAuto, makeClaim and \
    compile --rc auto fall back to the immortal policy (claim verified); --rc on still refuses; \
    check-cert --rc is a usage error"

/-! ## Middle-end budgets -/

/-- The `amp` input with the honest table and relevance (so Stage A passes)
and the single middle-end step `inline [(g, [f])]`. -/
def ampCase (dF dG : Nat) : IO (ByteArray × Lean.Json × Recheck.Input × Recheck.Config × Addr × Recheck.Cert) := do
  let (env, f, g, main) := ampEnv (← loadBase) dF dG
  let bs := bytes env
  let json := sidecar [("main", main)]
  let inp ← ofErr "amp: ingress" (Recheck.ingress bs json [])
  let P := inp.program
  let cfg := Recheck.Config.forInput {} inp
  let (table0, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let tc := Src.Table.TableCert.ofTable table0
  let table ← IO.ofExcept (Src.Table.ofCert cfg.table P tc)
  let ann ← IO.ofExcept (inp.kernel.annotateChecked { P with table })
  let base : Recheck.Cert := { table := tc, relevance := ann }
  let (src, checked) ← ofErr "amp: front" (Recheck.front cfg P base)
  let (lam, _) ← match Lam.erase src checked with
    | .ok r => pure r
    | .error _ => throw (IO.userError "amp: erasure declined")
  let some fId := P.lookup f | throw (IO.userError "amp: f not ingested")
  let some gId := P.lookup g | throw (IO.userError "amp: g not ingested")
  let gidOf := fun (c : Src.CId) =>
    (lam.globalList.find? fun (_, gl) => match gl.key with
      | .const c' _ => c' == c
      | _ => false).map (·.1)
  let some gf := gidOf fId | throw (IO.userError "amp: no global for f")
  let some gg := gidOf gId | throw (IO.userError "amp: no global for g")
  return (bs, json, inp, cfg, main, { base with mid := { steps := [.inline [(gg, [gf])]] } })

/-- An amplifier `ampCase dF dG` with its single `inline` step, refused with an
ordinary `anf.replay` error naming `budget` by `Recheck.run` and every verifier. -/
def amplifier (a : Assert) (dF dG : Nat) (budget : String) : IO String := IO.FS.withTempDir fun dir => do
  let (bs, json, inp, cfg, main, hostile) ← ampCase dF dG
  let P := inp.program
  expect a (Recheck.checkCanonicalRelevance cfg inp hostile.table hostile.relevance)
    "amp: Stage A refuses the certificate, so the byte-level verifiers would not reach the replay"
  expect a (Recheck.checkMidCert hostile.mid).isOk "amp: checkMidCert refuses the step"
  let t0 ← IO.monoMsNow
  match Recheck.run cfg P hostile with
  | .ok _ => expect a false "amp: Recheck.run accepted the certificate"
  | .error e =>
    expect a (e.stage == .anf && e.code == "anf.replay" && (e.message.splitOn budget).length > 1)
      s!"amp: Recheck.run refused, but not by {budget}: {e.render}"
  let ms := (← IO.monoMsNow) - t0
  let claim : CompileClaim :=
    { env := inp.env.root, roleTable := inp.env.bindingAddress, target := main
      policy := .immortal, abiArity := 0
      elfHash := Address.blake3Pure (ByteArray.mk #[0]) }
  let text := hostile.toText
  let sip : Ring0.Ring0Sip := { cfg, claim, certText := text, driver }
  expect a (!CompileClaim.verifyBytes cfg bs json claim text) "amp: verifyBytes accepted"
  expect a (!(CompileClaim.checkClaim cfg bs json claim text).isOk) "amp: checkClaim accepted"
  expect a (!CompileClaim.verifyProgram cfg P claim text) "amp: verifyProgram accepted"
  expect a (!(CompileClaim.checkClaimProgram cfg P claim text).isOk) "amp: checkClaimProgram accepted"
  expect a (!sip.verifyBytes bs json) "amp: Ring0Sip.verifyBytes accepted"
  expect a (!sip.verifyProgram P) "amp: Ring0Sip.verifyProgram accepted"
  IO.FS.writeBinFile (dir / "c.ixe") bs
  IO.FS.writeFile (dir / "c.json") json.pretty
  match ← checkCert dir hostile [] with
  | .ok () => expect a false "amp: check-cert accepted"
  | .error e => expect a (e.stage == .anf && e.code == "anf.replay") s!"amp: check-cert: {e.render}"
  return s!"amp-{dF}-{dG} (.ixe {bs.size} bytes, certificate {text.utf8ByteSize} bytes): Recheck.run refused \
    ({budget}) in {ms} ms; verifyBytes, checkClaim, verifyProgram, checkClaimProgram, both Ring0Sip \
    verifiers and check-cert refuse it"

/-- The crashing input, `amp-12-11` (its `f` makes 8,191 calls, so its Lam global is
over `maxLamNodes`), and `amp-10-11`, whose `f` converts to a chain of 2,047
bindings, over `maxDepth` (its `inline` step would ask for 2,048 copies of it,
which the walk's depth budget would stop after two). -/
def inlineAmplifier (a : Assert) : IO String := do
  let lam ← amplifier a 12 11 "Lam global exceeds"
  let copy ← amplifier a 10 11 "depth budget"
  return s!"R1's {lam}; {copy}"

/-- `n` dead `atom` bindings before `ret`: `2 n + 1` nodes. -/
def chain (n : Nat) : Anf.Exp :=
  (List.range n).foldl (fun e _ => .bind Anf.freshLet (.atom .box) e) (.ret .box)

/-- One binding of a constructor of `n - 3` atoms, then `ret`: `n` nodes, three
levels deep. -/
def fat (n : Nat) : Anf.Exp :=
  .bind Anf.freshLet (.con (.src 0) (List.replicate (n - 3) .box)) (.ret .box)

/-- Global 0 is `fat (2 binds + 1)` (as many nodes as `chain binds`, but
shallow, within the depth budgets) over one parameter; globals `1 … callers`
each call it `calls` times. -/
def callersProgram (callers calls binds : Nat) : Anf.Program :=
  let callee : Anf.GDef := { key := .dispatch 0, ps := [{}], body := fat (2 * binds + 1) }
  let body := (List.range calls).foldl (fun e _ => .bind Anf.freshLet (.call 0 [.var 0]) e) (.ret .box)
  let caller : Anf.GDef := { key := .dispatch 1, ps := [{}], body }
  { globals := Src.NatMap.ofList ((0, callee) :: (List.range callers).map fun i => (i + 1, caller))
    size := callers + 1, roots := [1], ctors := [], known := {} }

/-- `x₀ := c []; xᵢ₊₁ := c [xᵢ, xᵢ]` up to `depth`, then `call 0 [x_depth]`:
the value tree of the call's argument has `2^(depth+1) - 1` nodes. -/
def tower (depth : Nat) : Anf.Exp :=
  let rec go : Nat → Anf.Exp
    | 0 => .bind Anf.freshLet (.call 0 [.var 0]) (.ret (.var 0))
    | k + 1 => .bind Anf.freshLet (.con (.src 0) [.var 0, .var 0]) (go k)
  .bind Anf.freshLet (.con (.src 0) []) (go depth)

def budgets (a : Assert) : IO String := do
  -- the bounded count is the node count, cut off past its cap
  for e in [chain 0, chain 7, tower 3, tower 12, (callersProgram 1 5 3).global? 1 |>.map (·.body) |>.getD .trap] do
    for cap in [0, 1, 5, 64, 4096, 1000000] do
      expect a (e.nodesUpTo cap == min e.nodes (cap + 1))
        s!"Exp.nodesUpTo {cap} disagrees with Exp.nodes ({e.nodes})"
  -- a walk that copies past its budget: two calls of a callee of about maxCopy nodes
  let cb := Anf.Walk.maxCopy / 2 - 8
  match Anf.Inline.round (callersProgram 1 2 cb) [(1, [0])] with
  | .ok _ => expect a false s!"a walk copying {2 * (2 * cb + 1)} nodes was accepted"
  | .error m => expect a ((m.splitOn "copy budget").length > 1) s!"the over-budget walk: {m}"
  -- one call is within the walk's budget
  expect a (Anf.Inline.round (callersProgram 1 1 cb) [(1, [0])]).isOk s!"a walk copying {2 * cb + 1} nodes refused"
  -- a round whose walks are each within budget but whose output is not:
  -- callers each inlining that callee once, over the program budget together
  let k := Anf.maxProgramNodes / (2 * cb) + 2
  match Anf.Inline.round (callersProgram k 1 cb) ((List.range k).map fun i => (i + 1, [0])) with
  | .ok _ => expect a false s!"an inline round making {k * (2 * cb + 1)} nodes was accepted"
  | .error m => expect a ((m.splitOn "the program exceeds").length > 1) s!"the over-budget round: {m}"
  -- the size check after P1 and after each step counts the whole program
  let gb := Anf.maxGlobalNodes / 2
  expect a (Anf.Pipeline.checkGlobalNodes (callersProgram 1 1 (gb - 8))).isOk s!"a {2 * gb - 15}-node global refused"
  expect a (!(Anf.Pipeline.checkGlobalNodes (callersProgram 1 1 (gb + 8))).isOk) s!"a {2 * gb + 17}-node global accepted"
  let kp := Anf.maxProgramNodes / (2 * gb) + 2
  let many : Anf.Program := { callersProgram 0 0 (gb - 8) with
    globals := Src.NatMap.ofList ((List.range kp).map fun i =>
      (i, ({ key := .dispatch i, ps := [{}], body := fat (2 * (gb - 8) + 1) } : Anf.GDef))), size := kp }
  expect a (!(Anf.Pipeline.checkGlobalNodes many).isOk) s!"a {kp * (2 * gb - 15)}-node program accepted"
  -- the back end's work: five 8,000-node globals (nodes squared), and two hundred
  -- 125-way cases (the switch check searches the constructor table per pair)
  let fatProg : Anf.Program := { callersProgram 0 0 0 with
    globals := Src.NatMap.ofList ((List.range 5).map fun i =>
      (i, ({ key := .dispatch i, ps := [{}], body := fat 8000 } : Anf.GDef))), size := 5 }
  let wideBody : Anf.Exp := .case (.var 0) ((List.range 125).map fun i => .mk (.src i) 0 (.ret (.var 0))) none
  let wideProg : Anf.Program := { callersProgram 0 0 0 with
    globals := Src.NatMap.ofList ((List.range 200).map fun i =>
      (i, ({ key := .dispatch i, ps := [{}], body := wideBody } : Anf.GDef))), size := 200
    ctors := (List.range 125).map fun i => { key := .src i, tag := i, arity := 0 } }
  for (label, Q) in [("five 8,000-node globals", fatProg), ("two hundred 125-way cases", wideProg)] do
    expect a (Anf.backWork Q > Anf.maxBackWork && Anf.Pipeline.programNodesUpTo Q.globalList 0 ≤ Anf.maxProgramNodes)
      s!"{label}: back-end work {Anf.backWork Q}, within the budget {Anf.maxBackWork}"
    match Anf.Pipeline.checkGlobalNodes Q with
    | .ok _ => expect a false s!"{label} accepted"
    | .error m => expect a ((m.splitOn "back end's work budget").length > 1) s!"{label}: {m}"
  -- a specialisation whose value tree is exponentially larger than its caller
  let towerProgram : Anf.Program :=
    { globals := Src.NatMap.ofList [(0, { key := .dispatch 0, ps := [{}], body := .ret (.var 0) }),
        (1, { key := .dispatch 1, ps := [{}], body := tower 48 })]
      size := 2, roots := [1], ctors := [], known := {} }
  match Anf.Specialize.run { decisions := [{ caller := 1, callee := 0, mask := [true] }] } towerProgram with
  | .ok _ => expect a false "a specialisation over a 2^49-node value tree was accepted"
  | .error m => expect a ((m.splitOn "work budget").length > 1) s!"the exponential specialisation: {m}"
  -- the same decision over a small tree is fine
  let smallCaller : Anf.GDef := { key := .dispatch 1, ps := [{}], body := tower 4 }
  let small := { towerProgram with globals := towerProgram.globals.insert 1 smallCaller }
  expect a (Anf.Specialize.run { decisions := [{ caller := 1, callee := 0, mask := [true] }] } small).isOk
    "a specialisation over a 31-node value tree refused"
  return s!"Exp.nodesUpTo agrees with Exp.nodes below its cap; refused: a walk copying {2 * (2 * cb + 1)} \
    nodes, an inline round making {k * (2 * cb + 1)} nodes, a {2 * gb + 17}-node global, a \
    {kp * (2 * gb - 15)}-node program, a specialisation over a 2^49-node value tree"

/-- `tower depth` with a binding of a `w`-atom constructor below its chain, so
that every census in the chain reads those atoms again. -/
def towerOver (depth w : Nat) : Anf.Exp :=
  let rec go : Nat → Anf.Exp
    | 0 => .bind Anf.freshLet (.con (.src 0) (List.replicate w (.var 0)))
        (.bind Anf.freshLet (.call 0 [.var 0]) (.ret (.var 0)))
    | k + 1 => .bind Anf.freshLet (.con (.src 0) [.var 0, .var 0]) (go k)
  .bind Anf.freshLet (.con (.src 0) []) (go depth)

/-- Global 0 returns its parameter; globals `1 … k` are `tower depth`. -/
def towers (k depth : Nat) : Anf.Program :=
  { globals := Src.NatMap.ofList ((0, ({ key := .dispatch 0, ps := [{}], body := .ret (.var 0) } : Anf.GDef)) ::
      (List.range k).map fun i =>
        (i + 1, ({ key := .dispatch (i + 1), ps := [{}], body := tower depth } : Anf.GDef)))
    size := k + 1, roots := [1], ctors := [], known := {} }

/-- One global over one parameter: a local function of one parameter whose
body is `fat m` (`m` nodes), applied `uses` times (each result bound, the
last returned). -/
def betaProgram (m uses : Nat) : Anf.Program :=
  let apps := (List.range uses).foldr (fun i e => .bind Anf.freshLet (.app (.var i) [.box]) e)
    (.ret (.var 0))
  let gd : Anf.GDef := { key := .dispatch 0, ps := [{}], body := .bind Anf.freshLet (.fn [{}] (fat m)) apps }
  { globals := Src.NatMap.ofList [(0, gd)], size := 1, roots := [0], ctors := [], known := {} }

/-- The same local function applied once, inside a join point of four nodes
that a two-way `case` on the parameter jumps to twice: shrink emits the join
point (its body expands the function first) and inlines it at both jumps (a
small join point), so the function's body is walked three times. -/
def betaJoinProgram (m : Nat) : Anf.Program :=
  let jb : Anf.Exp := .bind Anf.freshLet (.app (.var 1) [.var 0]) (.ret (.var 0))
  let sw : Anf.Exp := .case (.var 1)
    [.mk (.src 0) 0 (.jump 0 [.lit (.nat 1)]), .mk (.src 1) 0 (.jump 0 [.lit (.nat 2)])] none
  let gd : Anf.GDef :=
    { key := .dispatch 0, ps := [{}], body := .bind Anf.freshLet (.fn [{}] (fat m)) (.join 1 false jb sw) }
  { globals := Src.NatMap.ofList [(0, gd)], size := 1, roots := [0], ctors := [], known := {} }

def retryFallbackMechanism (a : Assert) : IO String := do
  -- the producer's inline-round retry falls back to the run without it when
  -- the run with it fails, and is not tried at all when it is off
  let late : Bool → Except String Nat := fun r => if r then .error "a later budget" else .ok 0
  expect a (Anf.Pipeline.withRetryFallback true late matches .ok 0)
    "retryFallback: a run the retry makes fail is not rerun without it"
  let onlyRetry : Bool → Except String Nat := fun r => if r then .ok 1 else .error "without"
  expect a (Anf.Pipeline.withRetryFallback false onlyRetry matches .error _)
    "retryFallback: with the retry off, the run with it was taken"
  let both : Bool → Except String Nat := fun r => if r then .ok 1 else .ok 0
  expect a (Anf.Pipeline.withRetryFallback true both matches .ok 1)
    "retryFallback: a run with the retry that succeeds is not the one taken"
  let never : Bool → Except String Nat := fun _ => .error "refused"
  expect a (Anf.Pipeline.withRetryFallback true never matches .error _)
    "retryFallback: a run that fails both ways succeeds"
  return "retry fallback: the run without the retry is taken exactly when the run with it fails"

/-- The program of `retryLater`: `E` (three constructors); the structures
`T₁ := mk E E`, `Tᵢ₊₁ := mk Tᵢ Tᵢ` up to `T₉`, and `W := mk T₉ T₉`;
`k (a b : E) : E := a`; `pi (w : W) : E`, the first field ten times;
`h (q : E → T₉) : W := W.mk (q c₀) (q c₁)`; for `i < 17`,
`bᵢ (x : E) : W := h (fun y => tᵢ)`, where `tᵢ` is the balanced `T₉` tree of
511 constructor applications whose leaves are the `i`-th pair of `y`, `x`, `c₀`,
`c₁`, `c₂` (so that the `bᵢ` are distinct constants); and
`main : E := k (pi (b₀ c₀)) (k (pi (b₁ c₀)) (… (pi (b₁₆ c₀))))`. The trees are
`share` DAGs. -/
def retryLaterEnv (env0 : Env) : Env × Addr := Id.run do
  let b := base env0 3
  let mut e := b.env
  -- `tys`: E, T₁ … T₉, W; `mks`: their constructors from T₁'s
  let mut tys : Array Addr := #[b.enumI]
  let mut mks : Array Addr := #[]
  for _ in [0:10] do
    let (e', t) := addPair e tys.back!
    e := e'
    tys := tys.push t.ind
    mks := mks.push t.ctors[0]!
  let (e', k) := store e
    ⟨defn (arrow enumC (arrow enumC enumC)) (lambda enumC (lambda enumC (.var 1))), #[], #[b.enumI], #[]⟩
  e := e'
  -- `pi`'s references: W, T₉, …, T₁, E
  let mut pv : X := .var 0
  for i in [0:10] do pv := .prj i.toUInt64 0 pv
  let (e', pi) := store e
    ⟨defn (arrow (.ref 0 #[]) (.ref 10 #[])) (lambda (.ref 0 #[]) pv), #[], tys.reverse, #[]⟩
  e := e'
  -- `h`'s references: E, T₉, W, W.mk, c₀, c₁
  let q : X := arrow enumC (.ref 1 #[])
  let hv := lambda q (.app (.app (.ref 3 #[]) (.app (.var 0) (.ref 4 #[]))) (.app (.var 0) (.ref 5 #[])))
  let (e', h) := store e
    ⟨defn (arrow q (.ref 2 #[])) hv, #[], #[b.enumI, tys[9]!, tys[10]!, mks[9]!, b.ctors[0]!, b.ctors[1]!], #[]⟩
  e := e'
  -- each `bᵢ`'s references: E, W, h, T₁.mk … T₉.mk, c₀, c₁, c₂; under `fun x => … fun y =>`,
  -- `y` is variable 0 and `x` variable 1
  let leaves : Array X := #[.var 0, .var 1, .ref 12 #[], .ref 13 #[], .ref 14 #[]]
  let bRefs : Array Addr := #[b.enumI, tys[10]!, h] ++ mks.extract 0 9 ++ b.ctors
  let mut bs : Array Addr := #[]
  for i in [0:17] do
    let mut sh : Array X := #[.app (.app (.ref 3 #[]) leaves[i / 5]!) leaves[i % 5]!]
    for l in [1:9] do
      let prev : X := .share (l - 1).toUInt64
      sh := sh.push (.app (.app (.ref (3 + l).toUInt64 #[]) prev) prev)
    let (e', bi) := store e
      ⟨defn (arrow enumC (.ref 1 #[])) (lambda enumC (.app (.ref 2 #[]) (lambda enumC (.share 8)))),
        sh, bRefs, #[]⟩
    e := e'
    bs := bs.push bi
  -- `main`'s references: E, k, pi, c₀, b₀ … b₁₆
  let call : Nat → X := fun i => .app (.ref 2 #[]) (.app (.ref (4 + i).toUInt64 #[]) (.ref 3 #[]))
  let mut mv : X := call 16
  for j in [0:16] do
    mv := .app (.app (.ref 1 #[]) (call (15 - j))) mv
  let (e', main) := store e ⟨defn enumC mv, #[], #[b.enumI, k, pi, b.ctors[0]!] ++ bs, #[]⟩
  return (e', main)

/-- The inline-round retry's fallback on a program from bytes (`retryLaterEnv`).
The first inline round lists `main` (callees `k`, `pi` and every `bᵢ`, each about
2,050 nodes, which `main`'s walk copies past the walk's copy budget) and each
`bᵢ` (callee `h`). The re-run refuses the round, so without the retry the rounds
end and nothing is inlined. With the retry the round is taken without `main`;
the shrink step after it β-reduces each `bᵢ`'s local function at the two
applications `h` brought in, which doubles each `bᵢ` (a second expansion of 2,045
nodes, within the walk's budgets) and takes the whole program past the back
end's work budget (`Anf.maxBackWork`), which is checked only after the shrink
step: `produceOnce` with the retry refuses the program there. `produce` (and so
`compileInput`, and `compileInputRetry` around it) falls back to the run without
the retry, which compiles. -/
def retryLater (a : Assert) : IO String := do
  let (env, main) := retryLaterEnv (← loadBase)
  let bs := bytes env
  let json := sidecar [("main", main)]
  let inp ← ofErr "retryLater: ingress" (Recheck.ingress bs json [])
  let cfg := Recheck.Config.forInput {} inp
  let ps ← ofErr "retryLater: front" (Recheck.produceSource cfg inp)
  let (lam, _) ← match Lam.erase ps.src ps.checked with
    | .ok r => pure r
    | .error _ => throw (IO.userError "retryLater: erasure declined")
  -- the middle end with the retry refuses the program after the retried round's shrink step
  match Anf.Pipeline.produceOnce { cfg.budgets with retryInline := true } lam with
  | .ok _ => expect a false "retryLater: the middle end with the retry accepted the program"
  | .error m => expect a ((m.splitOn "back end's work budget").length > 1) s!"retryLater: with the retry: {m}"
  let t0 ← match Anf.Pipeline.produceOnce { cfg.budgets with retryInline := false } lam with
    | .ok t => pure (some t)
    | .error m => expect a false s!"retryLater: the middle end without the retry refused it: {m}"; pure none
  -- the mechanism, step by step on the program the first round is proposed on
  let p := cfg.budgets.shrink.params
  if let some t0 := t0 then
    expect a (t0.cert.steps.all fun | .inline _ => false | _ => true)
      "retryLater: without the retry an inline round was taken"
    let P0 ← IO.ofExcept (Anf.Pipeline.run { t0.cert with steps := t0.cert.steps.take 2 } lam)
    let r := Anf.Inline.produce cfg.budgets.inline P0
    expect a (!(Anf.Pipeline.Step.run p (.inline r) P0).isOk) "retryLater: the re-run accepts the first round"
    let r' := r.filter fun e => (Anf.Pipeline.Step.run p (.inline [e]) P0).isOk
    expect a (r'.length + 1 == r.length) s!"retryLater: the re-run refuses {r.length - r'.length} callers alone, expected one"
    match Anf.Pipeline.Step.run p (.inline r') P0 with
    | .error m => expect a false s!"retryLater: the re-run refuses the retried round: {m}"
    | .ok P3 =>
      let (_, P2, _) ← IO.ofExcept (Anf.Shrink.produce cfg.budgets.shrink P3)
      expect a (Anf.backWork P3 ≤ Anf.maxBackWork && Anf.backWork P2 > Anf.maxBackWork)
        s!"retryLater: back-end work {Anf.backWork P3} after the retried round, {Anf.backWork P2} after its \
          shrink step; expected within {Anf.maxBackWork}, then past it"
  -- the producer and the compiler fall back to the run without the retry
  match Anf.Pipeline.produce cfg.budgets lam, t0 with
  | .ok t, some t0 =>
    let last := fun (t : Anf.Pipeline.Trace) => ((t.stages.getLast?).map (·.2)).getD default
    expect a (t.cert.steps.length == t0.cert.steps.length && (last t).beq (last t0))
      "retryLater: produce did not fall back to the run without the retry"
  | .error m, _ => expect a false s!"retryLater: produce refused the program: {m}"
  | _, none => pure ()
  let (c, art) ← ofErr "retryLater: compileInputRetry" (Recheck.compileInputRetry {} inp)
  let (c0, art0) ← ofErr "retryLater: compileInput without the retry" (Recheck.compileInput ({} : Recheck.Config).noRetry inp)
  expect a (c.mid.steps.length == c0.mid.steps.length && art.object == art0.object)
    "retryLater: compileInputRetry's object is not the one compiled without the retry"
  return s!"inline-round retry, fallback: the retried round's shrink step takes the program past the back \
    end's work budget; produce, compileInput and compileInputRetry compile it without the retry \
    ({art.object.size}-byte object)"

/-- The inline-round retry (`Anf.Pipeline.produce`, `Budgets.retryInline`), on
`ampEnv 3 8` compiled from bytes: `f x` makes 15 calls of `k` (61 nodes, so the
default oracle inlines it) and `g x` makes 255 calls of `k` over 256 leaves `f
x`. The first inline round the oracle proposes lists `f` (callee `k`) and `g`
(callees `k` and `f`); `g`'s walk copies `f` at its leaves past the walk's
budgets, so the re-run refuses the round, and refuses `g`'s entry alone, while
it accepts `f`'s alone. Without the retry that round ends the rounds of every
phase and nothing is inlined; with it the round is taken without `g` and `f`
shrinks to its parameter (behind ticks), so the program ends smaller. Both runs
compile (each certificate replayed by `Recheck.run`). -/
def retryRound (a : Assert) : IO String := do
  let (env, f, g, main) := ampEnv (← loadBase) 3 8
  let bs := bytes env
  let json := sidecar [("main", main)]
  let inp ← ofErr "retry: ingress" (Recheck.ingress bs json [])
  let P := inp.program
  let (c1, a1) ← ofErr "retry: compile with the retry" (Recheck.compileInput {} inp)
  let (c0, a0) ← ofErr "retry: compile without the retry"
    (Recheck.compileInput ({} : Recheck.Config).noRetry inp)
  let some fId := P.lookup f | throw (IO.userError "retry: f not ingested")
  let some gId := P.lookup g | throw (IO.userError "retry: g not ingested")
  let rounds := fun (c : Recheck.Cert) => c.mid.steps.filterMap fun
    | .inline r => some r
    | _ => none
  expect a (rounds c0).isEmpty
    s!"retry: without the retry {(rounds c0).length} inline rounds were taken, expected none"
  -- the program the first round was proposed on: the steps before it, replayed
  let before := c1.mid.steps.takeWhile fun
    | .inline _ => false
    | _ => true
  let P0 ← IO.ofExcept (Anf.Pipeline.run { c1.mid with steps := before } a1.lam)
  -- `f`'s and `g`'s globals there (pruning renumbers the globals)
  let gidOf := fun (c : Src.CId) =>
    (P0.globalList.find? fun (_, gd) => match gd.key with
      | .const c' _ => c' == c
      | _ => false).map (·.1)
  let some gf := gidOf fId | throw (IO.userError "retry: no global for f")
  let some gg := gidOf gId | throw (IO.userError "retry: no global for g")
  let r := Anf.Inline.produce {} P0
  let p := c1.mid.shrink
  let callers := r.map (·.1)
  expect a (callers.length == 2 && callers.contains gf && callers.contains gg)
    s!"retry: the proposed round lists the callers {callers}, expected f ({gf}) and g ({gg})"
  expect a (!(Anf.Pipeline.Step.run p (.inline r) P0).isOk) "retry: the re-run accepts the proposed round"
  let rf := r.filter (·.1 == gf)
  match Anf.Pipeline.Step.run p (.inline (r.filter (·.1 == gg))) P0 with
  | .ok _ => expect a false "retry: the re-run accepts g's entry alone"
  | .error m => expect a ((m.splitOn "budget exhausted").length > 1) s!"retry: g alone: {m}"
  expect a (Anf.Pipeline.Step.run p (.inline rf) P0).isOk "retry: the re-run refuses f's entry alone"
  -- the round taken is the proposed one without g
  match rounds c1 with
  | r1 :: _ =>
    expect a (r1.map (·.1) == [gf] && r1 == rf)
      s!"retry: the first round taken lists the callers {r1.map (·.1)}, expected f's entry alone"
  | [] => expect a false "retry: with the retry no inline round was taken"
  let nodes := fun (Q : Anf.Program) => Q.globalList.foldl (fun n (_, gd) => n + gd.body.nodes) 0
  expect a (nodes a1.anf < nodes a0.anf)
    s!"retry: {nodes a1.anf} nodes with the retry, {nodes a0.anf} without; expected fewer with it"
  return s!"inline-round retry: the round over f and g is refused (g alone past the walk's budgets) \
    and retried as f's entry; {(rounds c1).length} rounds and {nodes a1.anf} nodes with the retry, \
    none and {nodes a0.anf} without; both compile"

/-- The walk's copy accounting for β-reductions (2026-11-11): a local function
the walk inlines at its applications is moved by its first expansion, which is
not charged (its body is part of the global, which the binding skips), and
every later expansion is charged its nodes, whether the function has several
saturated applications or one application that a join point inlined at two
jumps walks again. Every walk takes at most its global's nodes plus its copies
(`Fires.steps`). The first assertion fails on the accounting it replaced, which
charged every expansion: a once-used function of more than `maxCopy` nodes was
refused. -/
def betaMoves (a : Assert) : IO String := do
  let p := ({} : Anf.Shrink.Params)
  let round (P : Anf.Program) : Except String Anf.Walk.Fires := do
    let some gd := P.global? 0 | throw "no global 0"
    let (_, f) ← Anf.Shrink.round P p gd
    pure f
  let nodes (P : Anf.Program) : Nat := ((P.global? 0).map (·.body.nodes)).getD 0
  let big := Anf.Walk.maxCopy + Anf.Walk.maxCopy / 2
  let half := Anf.Walk.maxCopy / 2 + 904
  let third := Anf.Walk.maxCopy / 3 + 300
  -- moved: one application of a function larger than the copy budget
  let once := betaProgram big 1
  expect a (nodes once ≤ Anf.maxGlobalNodes) s!"betaMoves: the {nodes once}-node global is over the node budget"
  match round once with
  | .ok f =>
    expect a (f.beta == 1 && f.copied == 0) s!"betaMoves: once: beta {f.beta}, copied {f.copied}, expected 1 and 0"
    expect a (f.steps ≤ nodes once + f.copied) s!"betaMoves: once: {f.steps} steps"
  | .error m => expect a false s!"betaMoves: a once-applied {big}-node local function refused: {m}"
  -- copied: two applications charge the second; three pass the budget
  let twice := betaProgram half 2
  match round twice with
  | .ok f =>
    expect a (f.beta == 2 && f.copied == half) s!"betaMoves: twice: beta {f.beta}, copied {f.copied}, expected 2 and {half}"
    expect a (f.steps ≤ nodes twice + f.copied) s!"betaMoves: twice: {f.steps} steps"
  | .error m => expect a false s!"betaMoves: a twice-applied {half}-node local function refused: {m}"
  match round (betaProgram half 3) with
  | .ok f => expect a false s!"betaMoves: a thrice-applied {half}-node local function accepted (copied {f.copied})"
  | .error m => expect a ((m.splitOn "copy budget").length > 1) s!"betaMoves: thrice: {m}"
  -- copied again through a join point inlined at two jumps
  let jp := betaJoinProgram third
  match round jp with
  | .ok f =>
    expect a (f.beta == 3 && f.joinSmall == 2 && f.copied ≥ 2 * third)
      s!"betaMoves: join: beta {f.beta}, joinSmall {f.joinSmall}, copied {f.copied}, expected 3, 2, at least {2 * third}"
    expect a (f.steps ≤ nodes jp + f.copied) s!"betaMoves: join: {f.steps} steps"
  | .error m => expect a false s!"betaMoves: the join program ({third}-node function) refused: {m}"
  match round (betaJoinProgram half) with
  | .ok f => expect a false s!"betaMoves: the join program ({half}-node function) accepted (copied {f.copied})"
  | .error m => expect a ((m.splitOn "copy budget").length > 1) s!"betaMoves: join, {half} nodes: {m}"
  return s!"β-reductions: a once-applied {big}-node local function is moved (copied 0); a second \
    application of a {half}-node one is charged and a third refused; a join point inlined at two jumps \
    charges both re-expansions ({third} nodes: accepted; {half}: refused); every walk within its step bound"

/-- Two field-less constructors for the pending join entry's tests. -/
def keyA : IxCC.Key.CtorKey := .src 0
def keyB : IxCC.Key.CtorKey := .src 1

/-- One global over `ps` parameters whose body is `join j y = jb in scope`,
with the constructors `A` and `B`. -/
def joinProgram (ps : Nat) (jb scope : Anf.Exp) : Anf.Program :=
  let gd : Anf.GDef := { key := .dispatch 0, ps := List.replicate ps {}, body := .join 1 false jb scope }
  { globals := Src.NatMap.ofList [(0, gd)], size := 1, roots := [0]
    ctors := [{ key := keyA, tag := 0, arity := 0 }, { key := keyB, tag := 1, arity := 0 }], known := {} }

/-- `y := c []; jump j [y]`. -/
def jumpCon (c : IxCC.Key.CtorKey) : Anf.Exp := .bind Anf.freshLet (.con c []) (.jump 0 [.var 0])

/-- A result as `SimUpTo` compares it: a stuck source is matched by
anything, a resource failure matches anything, otherwise equal outcomes and
equal values (a literal's number, a constructor's key). -/
def refinesAt (s t : IxCC.Sem.Result Anf.Val) : Bool :=
  match s, t with
  | .stuck, _ | _, .resource _ | .timeout, .timeout | .trap, .trap => true
  | .ok (.lit (.nat a)), .ok (.lit (.nat b)) => a == b
  | .ok (.con c _), .ok (.con c' _) => c == c'
  | _, _ => false

/-- The walk's output `tgt` against its source `src` (both bodies of global 0
of `P`, so with the same parameters) on each environment, at each clock up to
`clocks`: a source timeout must be a target timeout (or a resource failure)
at the same clock, and any other source outcome must be refined by the
target's at some clock up to `clocks + 4`. The clocks at which a pair fails. -/
def simAtClocks (P : Anf.Program) (src tgt : Anf.Exp) (envs : List (List Anf.Val)) (clocks : Nat) :
    List (List Anf.Val × Nat) :=
  envs.flatMap fun ρ => (List.range (clocks + 1)).filterMap fun k =>
    let s := Anf.eval P k ρ [] src
    let good := match s with
      | .timeout => match Anf.eval P k ρ [] tgt with
        | .timeout | .resource _ => true
        | _ => false
      | _ => (List.range (clocks + 5)).any fun k' => refinesAt s (Anf.eval P k' ρ [] tgt)
    if good then none else some (ρ, k)

/-- The pending join entry (case-of-case as a move): under shrink a
non-recursive join point of one parameter whose body is a `case` on it, every
jump to which passes a known constructor its `case` selects, is walked as
pending (`Walk.pendOk`): each jump takes its alternative, the first selection of
each a move, and the join point is emitted dead with body `trap`.

* **Simulated.** `join j y = tick (case y {A ⇒ ret 1; B ⇒ ret 2})` in
  `case x {A ⇒ y := B; jump j [y]; B ⇒ y := A; jump j [y]}`: one round takes it
  as pending (two selections, nothing copied, the join point's body `trap`), and
  the output, evaluated on `x = A`, `B` and a literal at every clock 0 … 8, is
  what the source gives (a source timeout at the same clock, any other outcome
  at some clock).
* **Forced on, through the inlining fallback.** With a jump passing the second
  parameter `z`, whose constructor the walk does not know, the pre-check
  refuses it; forced on (`Walk.Cfg.pendForce := some true`, a test-only
  switch), the jump the walk cannot resolve inlines the join point's body
  (`Fires.pendInline`), and the output is still what the source gives on every
  `x`, `z` and clock.
* **A large alternative selected twice is not pending.** With an alternative
  over the case-of-case bound selected by both jumps, the pre-check refuses it
  and the walk is the one without the pending entry (the same output and counts
  as forced off); selected by one jump, it is pending and moved (nothing
  copied). -/
def pendingJoin (a : Assert) : IO String := do
  let p := ({} : Anf.Shrink.Params)
  let r (n : Nat) : Anf.Exp := .ret (.lit (.nat n))
  let isPending : Anf.Exp → Bool := fun
    | .join 1 false .trap _ => true
    | _ => false
  -- simulated
  let jb : Anf.Exp := .tick (.case (.var 0) [.mk keyA 0 (r 1), .mk keyB 0 (r 2)] none)
  let scope : Anf.Exp := .case (.var 0) [.mk keyA 0 (jumpCon keyB), .mk keyB 0 (jumpCon keyA)] none
  let P := joinProgram 1 jb scope
  let some gd := P.global? 0 | throw (IO.userError "pendingJoin: no global")
  match Anf.Shrink.round P p gd with
  | .error m => expect a false s!"pendingJoin: the round refused: {m}"
  | .ok (gd', f) =>
    expect a (isPending gd'.body && f.caseOfCase == 2 && f.copied == 0 && f.pendInline == 0)
      s!"pendingJoin: not walked as pending (caseOfCase {f.caseOfCase}, copied {f.copied}, pendInline {f.pendInline})"
    expect a (f.steps ≤ gd.body.nodes + f.copied) s!"pendingJoin: {f.steps} steps"
    let bad := simAtClocks P gd.body gd'.body [[.con keyA []], [.con keyB []], [.lit (.nat 7)]] 8
    expect a bad.isEmpty s!"pendingJoin: the output differs from the source at {bad.length} environments and clocks"
  -- forced on: one jump the walk cannot resolve
  let scopeZ : Anf.Exp := .case (.var 1) [.mk keyA 0 (jumpCon keyB), .mk keyB 0 (.jump 0 [.var 0])] none
  let PZ := joinProgram 2 jb scopeZ
  let some gz := PZ.global? 0 | throw (IO.userError "pendingJoin: no global")
  let C := Anf.Shrink.cfg PZ p
  expect a (!Anf.Walk.pendOk C 2 .leaf jb scopeZ) "pendingJoin: the pre-check admits a jump of unknown constructor"
  match (Anf.Walk.global { C with pendForce := some true } gz).run {} with
  | .error m => expect a false s!"pendingJoin: forced on, refused: {m}"
  | .ok (gz', f) =>
    expect a (isPending gz'.body && f.pendInline == 1 && f.caseOfCase == 1)
      s!"pendingJoin: forced on: pendInline {f.pendInline}, caseOfCase {f.caseOfCase}, expected 1 and 1"
    expect a (f.steps ≤ gz.body.nodes + f.copied) s!"pendingJoin: forced on: {f.steps} steps"
    let vs : List Anf.Val := [.con keyA [], .con keyB [], .lit (.nat 7)]
    let bad := simAtClocks PZ gz.body gz'.body (vs.flatMap fun x => vs.map fun z => [z, x]) 8
    expect a bad.isEmpty s!"pendingJoin: forced on, the output differs from the source at {bad.length} environments and clocks"
  match Anf.Shrink.round PZ p gz with
  | .ok (gz', f) => expect a (!isPending gz'.body && f.pendInline == 0) "pendingJoin: decided, the unresolvable join is pending"
  | .error m => expect a false s!"pendingJoin: decided, refused: {m}"
  -- a large alternative selected twice, then once
  let big := p.caseOfCase + 88
  let jbig : Anf.Exp := .case (.var 0) [.mk keyA 0 (fat big), .mk keyB 0 (r 2)] none
  -- the arms differ (a dead binding in one), so that the pre-check's refusal is not the
  -- same-arms rule's
  let twice : Anf.Exp := .case (.var 0)
    [.mk keyA 0 (jumpCon keyA), .mk keyB 0 (.bind Anf.freshLet (.con keyB []) (jumpCon keyA))] none
  let PT := joinProgram 1 jbig twice
  let some gt := PT.global? 0 | throw (IO.userError "pendingJoin: no global")
  let CT := Anf.Shrink.cfg PT p
  expect a (!Anf.Walk.pendOk CT 1 .leaf jbig twice) "pendingJoin: the pre-check admits a large alternative selected twice"
  match Anf.Shrink.round PT p gt, (Anf.Walk.global { CT with pendForce := some false } gt).run {} with
  | .ok (gd1, f1), .ok (gd0, f0) =>
    expect a (!isPending gd1.body && gd1.body.beq gd0.body && f1.copied == f0.copied && f1.total == f0.total)
      "pendingJoin: a large alternative selected twice: the walk differs from today's"
  | _, _ => expect a false "pendingJoin: a large alternative selected twice: a round refused"
  -- the arms pass the other constructor (passing their own would be a case identity, which
  -- the pre-check refuses and the walk turns into one jump)
  let once : Anf.Exp := .case (.var 0) [.mk keyA 0 (jumpCon keyB), .mk keyB 0 (jumpCon keyA)] none
  let PO := joinProgram 1 jbig once
  let some go := PO.global? 0 | throw (IO.userError "pendingJoin: no global")
  match Anf.Shrink.round PO p go with
  | .ok (go', f) =>
    expect a (isPending go'.body && f.copied == 0)
      s!"pendingJoin: a large alternative selected once: not moved (copied {f.copied})"
  | .error m => expect a false s!"pendingJoin: a large alternative selected once: refused: {m}"
  return s!"pending join entry: walked as pending (two selections moved, body trap) and equal to its source \
    at clocks 0 … 8; forced on, a jump of unknown constructor inlines the body (pendInline 1), equal to its \
    source; a {big}-node alternative selected twice is walked as without the pending entry, selected once moved"

/-- The code lines (outside comments, trimmed) of a Lean source that mention
`word`. -/
def codeLinesWith (text word : String) : List String := Id.run do
  let mut inBlock := false
  let mut out : Array String := #[]
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    if inBlock then
      if (t.splitOn "-/").length > 1 then inBlock := false
    else if t.startsWith "/-" then
      if (t.splitOn "-/").length == 1 then inBlock := true
    else if ((((t.splitOn "--").headD "").splitOn word).length > 1) then
      out := out.push t
  return out.toList

/-- The production library's files (`IxCC/`, read from the package root) whose
code mentions `word`, with those lines, in path order. -/
def productionMentions (word : String) : IO (List (String × List String)) := do
  let files ← System.FilePath.walkDir "IxCC"
  let files := (files.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)
  let mut out : Array (String × List String) := #[]
  for f in files do
    let ls := codeLinesWith (← IO.FS.readFile f) word
    if !ls.isEmpty then out := out.push (f.toString, ls)
  return out.toList

/- The re-run's shrink walks never force the pending choice: `Shrink.cfg`,
which `round`, `rounds` and `run` use, leaves it at `none`. -/
example (P : Anf.Program) (p : Anf.Shrink.Params) : (Anf.Shrink.cfg P p).pendForce = none := rfl

/- The command line's configuration (`Cli.execute`: `Config.forInput {}` of the
input, and its `noRetry`) leaves the producer's switch at its default: the
first at `none`, the second as the first. -/
example (inp : Recheck.Input) : (Recheck.Config.forInput {} inp).budgets.shrink.pendForce = none := by
  unfold Recheck.Config.forInput
  split <;> rfl

example (cfg : Recheck.Config) : cfg.noRetry.budgets.shrink = cfg.budgets.shrink := rfl

/-- The pending choice's test-only switch (`Shrink.Budgets.pendForce`) reaches
only the producer. The production library's code mentions the switch on five
lines only: `Walk.Cfg`'s field and the walk's one read of it, and
`Shrink.Budgets`' field, the producer's round (`Shrink.produceRound`) and
`Shrink.produce`. The producer's rounds (`produceRound`, `fixpointWithin`) are
used in `Anf/Shrink.lean` only, `Shrink.produce` in `Anf/Pipeline.lean` only
(the middle end's producer), and that producer (`Pipeline.produce`,
`produceOnce`) only there and in the producers (`Recheck/Produce.lean`,
`Recheck/Rc/Produce.lean`): none in the checker
(`Recheck.run`, `RcReplay.run`, `verifyProgram` and what they call), whose
shrink walks are `Shrink.cfg`'s (the first `example` above), and none in the
command line, whose configuration is the default (the other two). That the
checker re-derives the choice, refusing a deviating producer's certificate
where its own walk reaches another program, is `tests-corpus`'s (the
`natural` fixture of `phase1-machines`). -/
def pendChoice (a : Assert) : IO String := do
  let lines ← productionMentions "pendForce"
  let want : List (String × List String) :=
    [("IxCC/Anf/Shrink.lean",
       ["pendForce : Option Bool := none", "(Walk.global { cfg P p with pendForce := force } gd).run {}",
        "let (gd', n, work, f) := fixpointWithin B.pendForce P B.params gd B.rounds 0 work {}"]),
     ("IxCC/Anf/Walk.lean",
       ["pendForce : Option Bool := none", "pure (C.pendForce.getD (pendOk C d seed b body))"])]
  expect a (lines == want) s!"pendChoice: the switch is mentioned in the production library's code at {lines}"
  let only : List (String × List String) :=
    [("produceRound", ["IxCC/Anf/Shrink.lean"]), ("fixpointWithin", ["IxCC/Anf/Shrink.lean"]),
     ("Shrink.produce", ["IxCC/Anf/Pipeline.lean"]), ("produceOnce", ["IxCC/Anf/Pipeline.lean"]),
     ("Pipeline.produce", ["IxCC/Recheck/Produce.lean", "IxCC/Recheck/Rc/Produce.lean"])]
  for (word, files) in only do
    let at_ := (← productionMentions word).map (·.1)
    expect a (at_.all files.contains) s!"pendChoice: {word} is used in {at_}, expected only in {files}"
  return s!"pending choice: its test-only switch is mentioned on {(lines.map (·.2.length)).sum} code lines of \
    {lines.length} production files, and the producer's entry points only by producers"

/-- The shrink census (FA residual): under shrink the walk counts the bound
variable's uses over the rest of the body at each binding, so one round on a
global of `n` bindings each used later reads about `n²` nodes: up to the
global's depth times its nodes, some 3·10⁷ within the node and depth
budgets, and 64 rounds of it, which one step may ask for, some 2·10⁹. The walk charges that reading to `Fires.work` and refuses
past `Walk.maxWalkWork`; a step refuses once its walks' work passes
`Anf.maxStepWork`. Asserted on the outcome and the counter, not on time. -/
def shrinkWork (a : Assert) : IO String := do
  let p := ({} : Anf.Shrink.Params)
  -- a small tower is shrunk, and the counter shows the census's n² reads
  let n := 1000
  let small := towers 1 n
  let some g1 := small.global? 1 | throw (IO.userError "towers: no global 1")
  let w ← match Anf.Shrink.round small p g1 with
    | .ok (_, f) => pure f.work
    | .error m => expect a false s!"a shrink round on a {g1.body.nodes}-node tower refused: {m}"; pure 0
  expect a (w ≥ n * n && w ≤ Anf.Walk.maxWalkWork)
    s!"a shrink round on a {n}-binding tower: work {w}, expected at least {n * n}"
  -- one round on a global within the node and depth budgets that asks for about
  -- m · 10,000 reads: m bindings over a 10,000-atom constructor
  let m := 1500
  let big : Anf.Program := { towers 1 1 with
    globals := (towers 1 1).globals.insert 1 { key := .dispatch 1, ps := [{}], body := towerOver m 10000 } }
  let some gb := big.global? 1 | throw (IO.userError "towers: no global 1")
  expect a (gb.body.nodes ≤ Anf.maxGlobalNodes && (Anf.Pipeline.checkGlobalNodes big).isOk)
    s!"the big tower ({gb.body.nodes} nodes) is over the node or depth budget"
  match Anf.Shrink.round big p gb with
  | .ok (_, f) => expect a false s!"a shrink round reading about {m * 10000} nodes was accepted (work {f.work})"
  | .error msg => expect a ((msg.splitOn "work budget").length > 1) s!"the {m * 10000}-read round: {msg}"
  -- the same through the certified step: 64 rounds of the global
  match Anf.Shrink.run p [0, 64] big with
  | .ok _ => expect a false s!"64 shrink rounds of a {gb.body.nodes}-node tower were accepted"
  | .error msg => expect a ((msg.splitOn "work budget").length > 1) s!"64 rounds of the big tower: {msg}"
  -- k globals, each round within the walk's budget, over the step's budget together
  let d := 1500
  let some gw := (towers 1 d).global? 1 | throw (IO.userError "towers: no global 1")
  let ww ← match Anf.Shrink.round (towers 1 d) p gw with
    | .ok (_, f) => pure f.work
    | .error msg => expect a false s!"one round of a {d}-binding tower refused: {msg}"; pure 1
  let k := Anf.maxStepWork / ww + 2
  expect a (k * ww > Anf.maxStepWork && k * gw.body.nodes < Anf.maxProgramNodes)
    s!"{k} {d}-binding towers: {k * ww} work, within the step budget"
  match Anf.Shrink.run p ((List.range (k + 1)).map fun i => if i == 0 then 0 else 1) (towers k d) with
  | .ok _ => expect a false s!"a shrink step of {k * ww} work was accepted"
  | .error msg => expect a ((msg.splitOn "work budget").length > 1) s!"the over-budget shrink step: {msg}"
  return s!"shrink census charged: a round on a {n}-binding tower does {w} work; refused: one round and \
    64 rounds on a {gb.body.nodes}-node tower (about {m * 10000} reads; walk budget {Anf.Walk.maxWalkWork}), \
    one round each of {k} {d}-binding towers ({ww} work each, {k * ww} together; step budget \
    {Anf.maxStepWork})"

/-! ## A certificate's `lazy` rows

A `lazy` row passes a definition's arguments by name, which changes what the
program evaluates, so the checked path accepts one only for a pinned row or a
sparse casesOn at its binder count (`Src.Table.checkLazy`, in `Table.ofCert`). -/

/-- `Recheck.run` refuses `c` at the table, with a message that starts with `msg`. -/
def refusedAtTable (a : Assert) (label : String) (cfg : Recheck.Config) (P : Src.Program)
    (c : Recheck.Cert) (msg : String) : IO Unit :=
  match Recheck.run cfg P c with
  | .ok _ => expect a false s!"{label}: accepted"
  | .error e => expect a (e.stage matches .table && e.code == "table.entry" && e.message.startsWith msg)
      s!"{label}: {e.render}"

/-- On the committed fixture `phase2-closures/sparse` (root `Sparse.minS`, whose
match reaches a sparse casesOn): its certificate is accepted; with a `lazy` row
added for an ordinary definition (the root, of two λs), or its sparse casesOn's
row at another arity, it is refused at the table (`table: table.entry`). -/
def sparseLazy (a : Assert) : IO String := do
  let dir : System.FilePath := "fixtures/corpus/phase2-closures"
  let bs ← IO.FS.readBinFile (dir / "sparse.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "sparse.equations.json")))
  let inp ← ofErr "sparse: ingress" (Recheck.ingress bs json ["Sparse.minS"])
  let P := inp.program
  let cfg := Recheck.Config.forInput {} inp
  let cert ← ofErr "sparse: produce" (Recheck.produce cfg inp)
  let _ ← ofErr "sparse: the produced certificate" (Recheck.run cfg P cert)
  let some (_, root) := P.roots.head? | throw (IO.userError "sparse: no root")
  let sparse := cert.table.lazy.filter fun (c, _) => (Src.Table.checkSparseCases P c).isOk
  let some (s, arity) := sparse.head? | throw (IO.userError "sparse: no sparse casesOn row in the certificate")
  let withLazy := fun (rows : List (Src.CId × Nat)) => { cert with table := { cert.table with lazy := rows } }
  refusedAtTable a "a lazy row for the root" cfg P (withLazy ((root, 2) :: cert.table.lazy))
    s!"table entry of constant {root}: lazy: not a pinned row, and not a sparse casesOn"
  refusedAtTable a "the sparse casesOn's row at a smaller arity" cfg P
    (withLazy (cert.table.lazy.map fun (c, n) => if c == s then (c, n - 1) else (c, n)))
    s!"table entry of constant {s}: lazy: not a pinned row, and a sparse casesOn of {arity} binders, not {arity - 1}"
  -- The sparse casesOn's row beside a `resolve` entry that replaces its value: a
  -- `csimp s g thm`, valid on its own, on the program with a copy `g` and `thm : @s = @g`.
  let some (P', g, thm) := IxCCTests.Src.withCsimpTwin P s | throw (IO.userError "sparse: no csimp twin")
  let paired := { cert with table := { cert.table with resolve := (s, .csimp g thm) :: cert.table.resolve } }
  refusedAtTable a "the sparse casesOn's row beside a csimp entry" cfg P' paired
    s!"table entry of constant {s}: lazy: a sparse casesOn's row beside a resolve entry"
  expect a ((Src.Table.ofCert cfg.table P' { paired.table with
      lazy := paired.table.lazy.filter (·.1 != s) }) matches .ok _)
    "the csimp entry without the sparse row: the table accepted"
  return s!"sparse casesOn: {sparse.length} row(s) in Sparse.minS's certificate; a row for an ordinary \
    definition, a row at another arity and a row beside a csimp entry refused at table: table.entry"

end IxCCTests.Recheck.Hostile
