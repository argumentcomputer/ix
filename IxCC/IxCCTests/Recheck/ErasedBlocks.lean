import IxCCTests.Recheck.Erased

/-! # Constructor fields written erased under recursors, and the minors of mutual and nested blocks

A constructor field written erased (`0`) is dropped: the constructor stores `irr` there (SrcEval)
or nothing (erasure), and a minor premise receives □ for it. When SrcEval runs a recursor itself
(F2), the rule of the major's constructor receives the fields as slots and applies the minor it
dispatches; for a recursive field it also passes the field as the major of an induction
hypothesis. Two checks hold the rule and the minors to the constructor's interface:

* **C3, with each minor paired with the constructor whose fields it receives** (`Check.elimShape?`,
  `Check.ruleDispatch`): at a recursor, the rule of each constructor meets the minor it dispatches.
  A recursor of a mutual block takes the minors of every constructor of the block and has rules
  for its own inductive's constructors only, so pairing minor `j` with rule `j` checked the wrong
  minors at a block's second recursor and none of its own: an η-short minor over a field written
  erased then compiled to an object returning a wrong constructor (`mainB` below, before this
  check). A nested block is stored as a mutual block with auxiliary types, with the same pairing.
* **The forwarding clause** (`Check.Canonical.forwardsErased?`, in `checkCanonical`): a reached
  recursor's rule uses a field its constructor writes erased only as that field's argument to the
  minor it dispatches, decided on the stored rule term (IxCC does not check that a rule has the
  kernel's generated shape). It refuses a recursive field written erased by name: under a single
  inductive (also refused by C3's η-short clause at the rule's induction-hypothesis call, whose
  minors are the rule's own variables), and where the hypothesis is another member's recursor
  (`mainM2`), which C3 does not see; before this clause only erasure's decline of such rules
  (a capability gap) stopped that one.

The single-inductive programs are built on the role-bound test builder and go through the
certified kernel (which accepts a field written erased on a constructor, and does not compare a
stored rule's binder data); the mutual and nested ones are the committed closure
`fixtures/ixon-v4/erased-blocks` (`ix compile`), with the field written erased below the kernel,
as a kernel that sees no mode accepts it (today's kernel refuses a field written erased in a
mutual block, at the constructor). Outcomes before the checks: `plans/resource-cert/L1.md` (the
lead's tree, engineer RL). -/

namespace IxCCTests.Recheck.ErasedBlocks

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Src (Assert expect)
open IxCCTests.Recheck.Hostile (defn sidecar ofErr)
open IxCCTests.IxonV3.Builder (store block arrow lambda)
open IxCCTests.Support.Bound (loadBase addEnum)
open IxCCTests.Recheck.Erased (E objMain srcMain lookup ingest accepted refused withNode eraseParam
  mapArg withCtor ctorRoots installed)

abbrev X := IxCC.Ixon.V3.Expr

/-! ## The harness -/

/-- Set the binder of the `i`-th leading λ. -/
def setLam (f : Src.Binder → Src.Binder) : Nat → Src.Term → Src.Term
  | 0, .lam b d t => .lam (f b) d t
  | n + 1, .lam b d t => .lam b d (setLam f n t)
  | _, t => t

/-- Replace the body under `n` leading λs. -/
def setBody (body : Src.Term) : Nat → Src.Term → Src.Term
  | 0, _ => body
  | n + 1, .lam b d t => .lam b d (setBody body n t)
  | _, t => t

/-- The body under `n` leading λs. -/
def bodyUnder : Nat → Src.Term → Src.Term
  | n + 1, .lam _ _ t => bodyUnder n t
  | _, t => t

def erasedPrf (b : Src.Binder) : Src.Binder := { b with contract := .erased, rel := Src.Rel.prf }

/-- The constant heading the argument reached by `path` (argument indices through spines). -/
def headAt : List Nat → Src.Term → Option Src.CId
  | [], t =>
    match t.spine.1 with
    | .const c _ => some c
    | _ => none
  | i :: rest, t =>
    match t.spine.2[i]? with
    | some (a, _, _) => headAt rest a
    | none => none

/-- Every spine headed by `k` gets its argument `pos` tagged a proof (the argument for a field
written erased), at any depth. -/
partial def retagCtor (k : Src.CId) (pos : Nat) : Src.Term → Src.Term
  | t@(.app ..) =>
    let (h, args) := t.spine
    let args := args.map fun (a, m, r) => (retagCtor k pos a, m, r)
    let args := match h with
      | .const c _ =>
        if c == k then args.zipIdx.map fun ((a, m, r), i) => if i == pos then (a, m, Src.Rel.prf) else (a, m, r)
        else args
      | _ => args
    Src.Term.mkApps h args
  | .lam b d t => .lam b d (retagCtor k pos t)
  | .letE c r ty v b => .letE c r ty (retagCtor k pos v) (retagCtor k pos b)
  | .proj s i e => .proj s i (retagCtor k pos e)
  | t => t

/-- `refused`, returning every message of the front end's refusal. -/
def refusedAll (a : Assert) (label : String) (cfg : Recheck.Config) (P : Src.Program)
    (tc : Src.Table.TableCert) (ann : Src.Relevance.Ann) (needles : List String) :
    IO (String × List String) := do
  let line ← refused a label cfg P tc ann needles
  let table ← match Src.Table.ofCert cfg.table P tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"{label}: the table refused it: {m}")
  let Pt := { P with table }
  match Src.Recheck.annotation Pt ann with
  | .error (.relevance errs) => return (line, errs.toList.map (·.render Pt))
  | _ => return (line, [])

/-- The forwarding clause on recursor `r` of `P`: its message, or `none`. -/
def forwards (P : Src.Program) (r : Src.CId) : Option String :=
  Src.Relevance.Check.Canonical.forwardsErased? P r

/-- The (argument position, minor, rule) triples C3 pairs at a saturated call of `r`. -/
def pairsOf (P : Src.Program) (r : Src.CId) : List (Nat × Nat × Nat) :=
  ((Src.Relevance.Check.elimShape? P r).map (·.minors)).getD []

/-! ## A single inductive: `T | leaf | mk (t : T)` (PLAN-2 §4.4) -/

/-- `next : E → E := λ e. E.rec (λ _. E) c₁ c₂ c₀ e` (refs: `E`, `E.rec`, `c₀`, `c₁`, `c₂`). -/
def nextC (en : IxCCTests.Support.Bound.Ind) : Constant :=
  let body : X := .app (.app (.app (.app (.app (.ref 1 #[0]) (.lam .many E E)) (.ref 3 #[])) (.ref 4 #[]))
    (.ref 2 #[])) (.var 0)
  ⟨defn (arrow E E) (lambda E body), #[], #[en.ind, en.recursor, en.ctors[0]!, en.ctors[1]!, en.ctors[2]!],
    #[.succ .zero]⟩

/-- `inductive T | leaf | mk (fc t : T) : Type`. -/
def tBlock (fc : BinderContract) : Constant :=
  let self : X := .recur 0 #[]
  let leaf : Constructor := ⟨false, 0, 0, 0, 0, self⟩
  let mk : Constructor := ⟨false, 0, 1, 0, 1, .all fc .shared self self⟩
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0, #[leaf, mk]⟩], #[], #[], #[.succ .zero]⟩

/-- `T.rec.{u} : (motive : T → Sort u) → motive leaf → ((t : T) → motive t → motive (mk t)) →
(t : T) → motive t`; rule 0 `λ motive m₀ m₁. m₀`, rule 1 `λ motive m₀ m₁ (rfc t : T). m₁ t (T.rec
motive m₀ m₁ t)` (refs: `T`, `leaf`, `mk`). -/
def tRec (blk : IxCC.Ixon.Address) (rfc : BinderContract) : Constant :=
  let refs := #[indcProjAddr blk 0, ctorProjAddr blk 0 0, ctorProjAddr blk 0 1]
  let tT : X := .ref 0 #[]
  let v := fun (i : Nat) => (IxCC.Ixon.V3.Expr.var i.toUInt64)
  let motiveTy : X := arrow tT (.sort 0)
  let minor0 : X := .app (v 0) (.ref 1 #[])
  let minor1 : X := arrow tT (arrow (.app (v 2) (v 0)) (.app (v 3) (.app (.ref 2 #[]) (v 1))))
  let major : X := arrow tT (.app (v 3) (v 0))
  let typ : X := arrow motiveTy (arrow minor0 (arrow minor1 major))
  let rule0 : RecursorRule := ⟨0, lambda motiveTy (lambda minor0 (lambda minor1 (v 1)))⟩
  let ih : X := .app (.app (.app (.app (.recur 0 #[0]) (v 3)) (v 2)) (v 1)) (v 0)
  let rule1 : RecursorRule :=
    ⟨1, lambda motiveTy (lambda minor0 (lambda minor1 (.lam rfc tT (.app (.app (v 1) (v 0)) ih))))⟩
  ⟨.recr ⟨false, false, 1, 0, 0, 1, 2, typ, #[rule0, rule1]⟩, #[], refs, #[.var 0]⟩

/-- `main := T.rec.{1} (λ _. E) c₀ (λ (t : T) (ih : E). next ih) (mk (mk leaf))`: `c₂` (a dropped
field read as `leaf` would give `c₁`). Refs: `E`, `T.rec`, `T`, `next`, `c₀`, `mk`, `leaf`. -/
def tMain (en : IxCCTests.Support.Bound.Ind) (tInd tr mk leaf nx : IxCC.Ixon.Address) : Constant :=
  let minor1 : X := .lam .many (.ref 2 #[]) (.lam .many E (.app (.ref 3 #[]) (.var 0)))
  let major : X := .app (.ref 5 #[]) (.app (.ref 5 #[]) (.ref 6 #[]))
  let body : X := .app (.app (.app (.app (.ref 1 #[0]) (.lam .many (.ref 2 #[]) E)) (.ref 4 #[])) minor1) major
  ⟨defn E body, #[], #[en.ind, tr, tInd, nx, en.ctors[0]!, mk, leaf], #[.succ .zero]⟩

structure TProg where
  env : Env
  roots : List (String × IxCC.Ixon.Address)
  tRec : IxCC.Ixon.Address
  mkC : IxCC.Ixon.Address
  main : IxCC.Ixon.Address

def tProg (fc rfc : BinderContract) : IO TProg := do
  let (e, en) := addEnum (← loadBase) 3
  let (e, nx) := store e (nextC en)
  let (e, blk) := block e (tBlock fc)
  let (e, tr) := store e (tRec blk rfc)
  let mk := ctorProjAddr blk 0 1
  let (e, main) := store e (tMain en (indcProjAddr blk 0) tr mk (ctorProjAddr blk 0 0) nx)
  let (e, rs) := ctorRoots e en.ind en.ctors
  return { env := e, roots := [("main", main)] ++ rs, tRec := tr, mkC := mk, main }

/-- Through the certified kernel: it accepts, and the producer refuses with every needle. -/
def kernelThenRefused (a : Assert) (label : String) (pr : TProg) (needles : Src.Program → Src.CId → List String) :
    IO (Src.Program × Src.CId × String) := do
  let inp ← ofErr s!"{label}: ingress" (Recheck.ingress (IxCCTests.Support.Bound.write pr.env) (sidecar pr.roots) [])
  let P := inp.program
  let rId ← lookup P pr.tRec "T.rec"
  let ns := needles P rId
  match Recheck.produce (Recheck.Config.forInput {} inp) inp with
  | .ok _ =>
    expect a false s!"{label}: produce accepted it"
    return (P, rId, s!"{label}: accepted")
  | .error err =>
    expect a (err.stage == .relevance && ns.all (err.message.contains ·))
      s!"{label}: produce refused it otherwise: {err.render}"
    return (P, rId, s!"{label}: {err.render}")

def single (a : Assert) : IO (Array String) := do
  let c₂ : Sem.Obs := .ctor 2 []
  -- the control: no mark
  let pr ← tProg .many .many
  let h ← ingest "T, no mark" pr.env pr.roots
  let P := h.inp.program
  let rId ← lookup P pr.tRec "T.rec"
  let mkId ← lookup P pr.mkC "T.mk"
  let mainId ← lookup P pr.main "main"
  expect a (objMain h.art == some c₂ && srcMain h.art mainId == some c₂) "T control: not c₂"
  expect a (pairsOf P rId == [(1, 0, 0), (2, 1, 1)]) s!"T.rec's pairing: {pairsOf P rId}"
  let mut out := #["T.rec (λ_.E) c₀ (λ t ih. next ih) (mk (mk leaf)): accepted, c₂ (object and SrcEval); C3 pairs rule j with minor j"]
  -- K1: `mk`'s field written erased; the kernel accepts (it compares no field's contract here)
  let (P1, r1, line) ← kernelThenRefused a "T, mk's field written erased (kernel-accepted)" (← tProg .erased .many)
    fun P r => [s!"in rule 1 of {P.short r}", "minor 1 does not bind field 0, which is written erased"]
  out := out.push line
  match forwards P1 r1 with
  | some m => do
    expect a (m.contains "rule 1 of the recursor uses field 0" && m.contains "other than as that field's argument")
      s!"T, mk's field written erased: the forwarding clause says {m}"
    out := out.push s!"T, mk's field written erased: the forwarding clause: {m}"
  | none => expect a false "T, mk's field written erased: the forwarding clause accepts T.rec"
  -- K7, K6: rule 1's field λ written erased (the kernel does not compare a rule's binder data)
  out := out.push (← kernelThenRefused a "T, rule 1's field λ written erased (kernel-accepted)" (← tProg .many .erased)
    fun P r => [s!"in rule 1 of {P.short r}", "[relevance C1]"]).2.2
  out := out.push (← kernelThenRefused a "T, mk's field and rule 1's λ written erased (kernel-accepted)"
    (← tProg .erased .erased) fun P r => [s!"in rule 1 of {P.short r}", "[relevance C1]",
      "minor 1 does not bind field 0, which is written erased"]).2.2
  -- below the kernel: `mk`'s field written erased and `main`'s minor binding it erased
  let Pi ← installed h
  let some (.ctor x1 x2 x3 x4 np nf mkTy) := Pi.decl? mkId | throw (IO.userError "mk")
  let Pe := Pi.setDecl mkId (.ctor x1 x2 x3 x4 np nf (eraseParam 0 mkTy))
  let annE := withCtor h.cert.relevance Pe mkId
  let some (.defn dk ds dl mty mval) := Pe.decl? mainId | throw (IO.userError "main")
  let mval := retagCtor mkId 0 (mapArg rId 2 (fun (x, m, r) => (setLam erasedPrf 0 x, m, r)) mval)
  let Pe := Pe.setDecl mainId (.defn dk ds dl mty mval)
  let annE := withNode annE (.value mainId) mval.tagOrder
  out := out.push (← refused a "T, mk's field written erased, main's minor binding it erased" h.cfg Pe
    h.cert.table annE [s!"in rule 1 of {P.short rId}", "minor 1 does not bind field 0, which is written erased"])
  -- rules of a shape the kernel would not generate (IxCC does not check the shape)
  let some (.recr s k l rnp nmot nmin ni ind rules rty) := Pe.decl? rId | throw (IO.userError "T.rec")
  let some rule1 := rules[1]? | throw (IO.userError "rule 1")
  let (_, gargs) := (bodyUnder 4 rule1.rhs).spine
  let some (_, m₀, r₀) := gargs[0]? | throw (IO.userError "rule 1's minor application")
  let some (_, m₁', r₁') := gargs[1]? | throw (IO.userError "rule 1's hypothesis")
  for (body, what, needle) in [
      (Src.Term.mkApps (.var 1) [(.var 0, m₀, r₀), (.var 0, m₁', r₁')], "λ motive m₀ m₁ t. m₁ t t",
        "rule 1 of the recursor uses field 0"),
      (Src.Term.var 0, "λ motive m₀ m₁ t. t", "rule 1 of the recursor dispatches no minor premise")] do
    let rhs := setBody body 4 rule1.rhs
    let Pr := Pe.setDecl rId (.recr s k l rnp nmot nmin ni ind (rules.set 1 { rule1 with rhs }) rty)
    let annR := withNode annE (.rule rId 1) rhs.tagOrder
    out := out.push (← refused a s!"T, mk's field written erased, rule 1 replaced by {what}" h.cfg Pr
      h.cert.table annR [s!"({P.short rId})", needle])
  return out

/-! ## Mutual and nested blocks: `fixtures/ixon-v4/erased-blocks` -/

def blocksDir : System.FilePath := "fixtures/ixon-v4/erased-blocks"

/-- Root `name` of the fixture with the constructor roots, through ingress; the table and the
kernel annotator's annotation the producer would use; the program with that annotation
installed. -/
structure Loaded where
  inp : Recheck.Input
  cfg : Recheck.Config
  tc : Src.Table.TableCert
  ann : Src.Relevance.Ann
  Pi : Src.Program
  main : Src.CId

def load (name : String) : IO Loaded := do
  let raw ← IO.FS.readBinFile (blocksDir / "blocks.ixe")
  let sc ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (blocksDir / "blocks.equations.json")))
  let chosen := [s!"ErasedBlocks.{name}", "ErasedBlocks.r0", "ErasedBlocks.r1", "ErasedBlocks.r2"]
  let inp ← ofErr s!"{name}: ingress" (Recheck.ingress raw sc chosen)
  let cfg := Recheck.Config.forInput {} inp
  let P := inp.program
  let some (_, main) := P.roots.head? | throw (IO.userError s!"{name}: no root")
  let (table, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let ann ← match inp.kernel.annotateChecked { P with table } with
    | .ok ann => pure ann
    | .error m => throw (IO.userError s!"{name}: the annotator: {m}")
  let Pi ← match Src.Relevance.install { P with table } ann with
    | .ok p => pure p
    | .error m => throw (IO.userError s!"{name}: install: {m}")
  return { inp, cfg, tc := Src.Table.TableCert.ofTable table, ann, Pi, main }

/-- SrcEval on the honest program. -/
def srcHonest (l : Loaded) : Option Sem.Obs :=
  match Src.Relevance.check l.Pi l.ann, Src.run l.Pi 100000 l.main [] with
  | .ok ch, .ok v => Src.readback l.Pi ch.keeps v
  | _, _ => none

/-- The program with field `field` of the constructor at `path` in `main`'s value written erased
below the kernel, the program's arguments for it tagged irrelevant, and the λs `marks`
(argument position of `main`'s spine, λ index) written erased: the program, its annotation, the
constructor and `main`'s head. -/
def plant (l : Loaded) (path : List Nat) (field : Nat) (marks : List (Nat × Nat)) :
    IO (Src.Program × Src.Relevance.Ann × Src.CId × Src.CId) := do
  let some (.defn dk ds dl mty mval) := l.Pi.decl? l.main | throw (IO.userError "main")
  let some rId := headAt [] mval | throw (IO.userError "main's head")
  let some kId := headAt path mval | throw (IO.userError "the constructor")
  let some (.ctor x1 x2 x3 x4 np nf kTy) := l.Pi.decl? kId | throw (IO.userError "not a constructor")
  let Q := l.Pi.setDecl kId (.ctor x1 x2 x3 x4 np nf (eraseParam (np + field) kTy))
  let mval := retagCtor kId (np + field) mval
  let mval := marks.foldl (fun v (pos, i) => mapArg rId pos (fun (x, m, r) => (setLam erasedPrf i x, m, r)) v) mval
  let Q := Q.setDecl l.main (.defn dk ds dl mty mval)
  return (Q, withNode (withCtor l.ann Q kId) (.value l.main) mval.tagOrder, kId, rId)

/-- The recursor of a block (more than one motive) one of whose rules is constructor `k`'s. -/
def recOf (P : Src.Program) (k : Src.CId) : Option Src.CId :=
  (List.range P.size).find? fun c =>
    match P.decl? c with
    | some (.recr _ _ _ _ nmot _ _ _ rules _) => decide (1 < nmot) && rules.any (·.ctor == k)
    | _ => false

def blocks (a : Assert) : IO (Array String) := do
  let mut out := #[]
  -- the minors of a block's second recursor: `B.rec` takes the minors of a0 a1 b0 b1
  let l ← load "mainB"
  let cert ← ofErr "mainB: produce" (Recheck.produce l.cfg l.inp)
  let art ← ofErr "mainB: Recheck.run" (Recheck.run l.cfg l.inp.program cert)
  expect a (objMain art == some (.ctor 1 []) && srcMain art l.main == some (.ctor 1 []))
    s!"mainB control: object {repr (objMain art)}, SrcEval {repr (srcMain art l.main)}"
  let (Q, ann, b1, bRec) ← plant l [6] 0 []
  expect a (pairsOf Q bRec == [(4, 2, 0), (5, 3, 1)]) s!"B.rec's pairing: {pairsOf Q bRec}"
  out := out.push "mainB := B.rec … useE (b1 c₁): accepted, c₁ (object and SrcEval); C3 pairs B.rec's rules 0, 1 with minors 2, 3"
  out := out.push (← refused a "B.rec's minor for b1, η-short over b1's field written erased" l.cfg Q l.tc ann
    [s!"in the value of {Q.short l.main}", s!"({Q.short b1})", "minor 3 does not bind field 0, which is written erased"])
  -- a field of one member whose type is another member: the hypothesis is `B2.rec`'s
  let l ← load "mainM2"
  expect a (srcHonest l == some (.ctor 2 [])) s!"mainM2 control: SrcEval {repr (srcHonest l)}"
  let (Q, ann, a1, aRec) ← plant l [5] 0 [(2, 0)]
  out := out.push "mainM2 := A2.rec … (λ b ih. ih) c₁ c₂ (a1 b1): SrcEval c₂ (erasure declines the honest program)"
  out := out.push (← refused a "a1's field written erased, the hypothesis B2.rec … b" l.cfg Q l.tc ann
    [s!"({Q.short aRec})", s!"rule 0 of the recursor uses field 0 of {Q.short a1}",
     "other than as that field's argument to the minor premise it dispatches"])
  -- nested blocks: the auxiliary recursor over `O Tree` (`L Rose`) takes the four minors
  for (name, path) in [("mainN", [6, 0]), ("mainN1", [6]), ("mainR", [6, 0])] do
    let l ← load name
    let (Q, ann, k, _) ← plant l path 0 [(5, 0)]
    let some aux := recOf Q k | throw (IO.userError s!"{name}: no auxiliary recursor")
    expect a (pairsOf Q aux == [(4, 2, 0), (5, 3, 1)]) s!"{name}: the auxiliary recursor's pairing: {pairsOf Q aux}"
    expect a ((forwards Q aux).any (·.contains s!"uses field 0 of {Q.short k}"))
      s!"{name}: the forwarding clause on the auxiliary recursor: {forwards Q aux}"
    let (line, ms) ← refusedAll a s!"{name}: the container's field written erased, its minor binding it erased"
      l.cfg Q l.tc ann [s!"({Q.short k})", "minor 3 does not bind field 0, which is written erased"]
    expect a (ms.all fun m => !m.contains s!"in the value of {Q.short l.main}")
      s!"{name}: a refusal at the user's call: {ms}"
    out := out.push line
  return out

def run (a : Assert) : IO (Array String) := do
  return (← single a) ++ (← blocks a)

end IxCCTests.Recheck.ErasedBlocks
