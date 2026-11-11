import IxCC.CompileClaim
import IxCC.Ring0
import IxCC.Recheck.Linked
import IxCC.Cli
import IxCC.X86.Layout.Basic
import IxCCTests.IxonV3.TypingFixtures
import IxCCTests.Src.Support

/-! # Hostile inputs to the verifiers and the middle end's replay

Regression tests for hostile certificates and inputs found in review. Programs
are written as Ixon v4 bytes with the test byte writer and read through
`Recheck.ingress` with erased typing on, the route a real `.ixe` takes.

* **Pin-free programs**. A closure with no constant whose
  content is `Nat`, `Bool` or `Eq` has no pinned identities. `checkCanonical`
  was skipped on such programs, so a certificate retagging a relevant
  parameter and its call site as irrelevant compiled to an object returning
  the wrong constructor, and `Recheck.run`, `CompileClaim.verifyProgram`,
  `checkClaimProgram` and `Ring0Sip.verifyProgram` accepted a claim naming
  it. The hostile enumeration has three constructors; a two-constructor one has
  `Bool`'s content address and is pinned, and is kept as a control.
* **Stage A on `ixcc check-cert`** (the canonical-annotation check) and the **erased-typing
  default** of the claim APIs and the command line.
* **The root signature checks, the specialisation bound and the
  frontier dedupe of the layout's reachability walk**.
* **The `--rc auto` immortal fallback** on the hostile annotated
  program, and `check-cert` refusing `--rc`.
* **Middle-end budgets**. A single hostile `inline` step, at the
  size that crashed `ixcc check-cert` with a stack overflow, through every
  verifier; an inline round over many callers; a walk that copies past its
  budget; a specialisation over an exponentially shared value tree. Each must
  be refused with an ordinary error, not by running out of stack, memory or
  time. -/

namespace IxCCTests.Recheck.Hostile

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Src (Assert expect annotationNoCanonical)
open IxCCTests.IxonV3.TypingFixtures (store block bytes arrow lambda)

abbrev Addr := IxCC.Ixon.Address
abbrev X := IxCC.Ixon.V3.Expr

def defn (ty val : X) : ConstantInfo := .defn ⟨.defn, .safe, 0, ty, val⟩

/-! ## Programs as bytes -/

/-- `inductive E | c₀ | … | cₙ₋₁ : Type`. -/
def enumInd (n : Nat) : V3.Inductive :=
  ⟨false, 0, 0, 0, .sort 0, (Array.range n).map fun i => ⟨false, 0, i.toUInt64, 0, 0, .recur 0 #[]⟩⟩

/-- The enumeration at `refs[0]`. -/
def enumC : X := .ref 0 #[]

structure Base where
  env : Env
  enumI : Addr
  ctors : Array Addr
  /-- `idc (c : E) : E := c`. -/
  idc : Addr

def base (n : Nat) : Base := Id.run do
  let (e, blk) := block {} ⟨.muts #[.indc (enumInd n)], #[], #[], #[.succ .zero]⟩
  let enumI := Tc.indcProjAddr blk 0
  let ctors := (Array.range n).map fun j => Tc.ctorProjAddr blk 0 j.toUInt64
  let (e, idc) := store e ⟨defn (arrow enumC enumC) (lambda enumC (.var 0)), #[], #[enumI], #[]⟩
  return { env := e, enumI, ctors, idc }

/-- An `ixcc/k1-equations/1` sidecar naming `roots`, with no equations. -/
def sidecar (roots : List (String × Addr)) : Lean.Json :=
  Lean.Json.mkObj [
    ("format", Lean.Json.str "ixcc/k1-equations/1"),
    ("roots", Lean.Json.arr (roots.map fun (n, a) =>
      Lean.Json.mkObj [("name", Lean.Json.str n), ("address", Lean.Json.str (toString a))]).toArray),
    ("equations", Lean.Json.arr #[])]

/-- The pin-free program: `main : E := idc c₁`, and a root `rᵢ := cᵢ` per
constructor, so that every constructor is emitted. With `illTyped`, the
environment also holds an unreachable constant whose value does not have its
type. -/
def pinFreeEnv (n : Nat) (illTyped : Bool := false) : Env × Addr × List (String × Addr) := Id.run do
  let b := base n
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
def ampEnv (dF dG : Nat) : Env × Addr × Addr × Addr := Id.run do
  let b := base 3
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

/-- A pin-free (or, for two constructors, `Bool`-pinned) program with its
honest certificate, and the hostile one: `idc`'s parameter and `main`'s
argument retagged `.type`. -/
structure Case where
  bytes : ByteArray
  json : Lean.Json
  inp : Recheck.Input
  cfg : Recheck.Config
  main : Addr
  honest : Recheck.Cert
  hostile : Recheck.Cert

def mkCase (n : Nat) (illTyped : Bool := false) : IO Case := do
  let (env, main, roots) := pinFreeEnv n illTyped
  let bs := bytes env
  let json := sidecar roots
  let inp ← ofErr s!"enum-{n}: ingress" (Recheck.ingress bs json [] (typecheck := !illTyped))
  let P := inp.program
  let cfg := Recheck.Config.forInput {} inp
  let honest ← ofErr s!"enum-{n}: produce" (Recheck.produce cfg inp)
  let some idcId := P.lookup (base n).idc | throw (IO.userError s!"enum-{n}: idc not ingested")
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
  return { bytes := bs, json, inp, cfg, main, honest, hostile }

/-! ## The program-level verifiers on pin-free programs -/

def pinFree (a : Assert) (n : Nat) : IO String := do
  let c ← mkCase n
  let P := c.inp.program
  let cfg := c.cfg
  let pinned := P.known.nat.isSome || P.known.bool.isSome || P.known.eq.isSome
  -- two constructors are `Bool`'s content address; three are nothing pinned
  expect a (pinned == (n == 2)) s!"enum-{n}: pinned identities {pinned}"
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
  return s!"enum-{n} ({if pinned then "Bool-pinned" else "nothing pinned"}): honest claim accepted by every \
    verifier, object returns constructor 1; hostile claim (object {hostileObj.size} bytes) refused by \
    Recheck.run (relevance-S1), verifyProgram, checkClaimProgram, verifyBytes and both Ring0Sip verifiers"

/-! ## Stage A on the command line, and the erased-typing default -/

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

/-- An environment holding an ill-typed constant the program does not reach:
erased typing (the default) refuses it; without typing it compiles. -/
def typecheckDefault (a : Assert) : IO String := IO.FS.withTempDir fun dir => do
  let c ← mkCase 3 (illTyped := true)
  let cfg := c.cfg
  expect a (Recheck.ingress c.bytes c.json [] (typecheck := true) matches .error _)
    "typing accepted the ill-typed constant"
  let (claim, text, _) ← IO.ofExcept (CompileClaim.makeClaim cfg c.bytes c.json (typecheck := false))
  expect a (CompileClaim.makeClaim cfg c.bytes c.json matches .error _) "makeClaim does not type by default"
  expect a (CompileClaim.verifyBytes cfg c.bytes c.json claim text (typecheck := false))
    "verifyBytes without typing refused the claim"
  expect a (!CompileClaim.verifyBytes cfg c.bytes c.json claim text) "verifyBytes does not type by default"
  expect a (!(CompileClaim.checkClaim cfg c.bytes c.json claim text).isOk) "checkClaim does not type by default"
  let sip : Ring0.Ring0Sip := { cfg, claim, certText := text, driver }
  expect a (sip.verifyBytes c.bytes c.json (typecheck := false)) "Ring0Sip.verifyBytes without typing refused"
  expect a (!sip.verifyBytes c.bytes c.json) "Ring0Sip.verifyBytes does not type by default"
  IO.FS.writeBinFile (dir / "c.ixe") c.bytes
  IO.FS.writeFile (dir / "c.json") c.json.pretty
  match ← checkCert dir c.honest ["--no-typecheck"] with
  | .ok () => expect a true ""
  | .error e => expect a false s!"check-cert --no-typecheck refused: {e.render}"
  match ← checkCert dir c.honest [] with
  | .ok () => expect a false "check-cert does not type by default"
  | .error e => expect a (e.stage == .ingress) s!"check-cert refused, but not at ingress: {e.render}"
  return "an unreachable ill-typed constant: makeClaim, verifyBytes, checkClaim, Ring0Sip.verifyBytes and \
    check-cert refuse it by default and accept it without typing"

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

/-- A one-constructor, two-field structure over the type at `refs[0]`. -/
def pairBlock (field : Addr) : Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0,
      #[⟨false, 0, 0, 0, 2, arrow (.ref 0 #[]) (arrow (.ref 0 #[]) (.recur 0 #[]))⟩]⟩],
    #[], #[field], #[.succ .zero]⟩

/-- The hostile `auto` program with a claim-eligible first root, `main : E := idc c₁`;
`Box := mk E E`, `Two := mk Box Box`, `dupf (b : Box) : Two := Two.mk b b`
(duplicates a heap parameter) and `lin (1 c : E) : E := c` (a linear binder
contract, which puts the program outside `Own.Plain.programDomain`). -/
def autoEnv : Env × List (String × Addr) := Id.run do
  let b := base 3
  let (e, boxBlk) := block b.env (pairBlock b.enumI)
  let boxI := Tc.indcProjAddr boxBlk 0
  let (e, twoBlk) := block e (pairBlock boxI)
  let twoI := Tc.indcProjAddr twoBlk 0
  let twoMk := Tc.ctorProjAddr twoBlk 0 0
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
  let (env, roots) := autoEnv
  let bs := bytes env
  let json := sidecar roots
  let inp ← ofErr "auto: ingress" (Recheck.ingress bs json [] true)
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
  let (env, f, g, main) := ampEnv dF dG
  let bs := bytes env
  let json := sidecar [("main", main)]
  let inp ← ofErr "amp: ingress" (Recheck.ingress bs json [] true)
  let P := inp.program
  let cfg := Recheck.Config.forInput {} inp
  let (table0, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let tc := Src.Table.TableCert.ofTable table0
  let table ← IO.ofExcept (Src.Table.ofCert cfg.table P tc)
  let ann ← IO.ofExcept (Src.Relevance.annotate inp.env { P with table })
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

end IxCCTests.Recheck.Hostile
