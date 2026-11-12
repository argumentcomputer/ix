import IxCCTests.Recheck.Hostile

/-! # Erased parameters: what a caller drops, the callee's run behaviour never reads

A caller drops the argument of every parameter its callee's type writes erased (`0`): the
annotator tags it irrelevant (`KernelFront.erasedAt`) and C2 holds it to the callee's parameter
classes. The compiler is right only if the callee's run behaviour never reads that argument. Each
part below writes a program where it does, on one route by which a constant's run behaviour
reaches the compiler, and asserts that the front end refuses it by name (`Src.Recheck.annotation`,
and `Recheck.run` on a certificate made without the canonical check), with an honest twin
accepted whose object and SrcEval return the value the program means.

Before these checks, each mismatch below compiled to an object returning a wrong constructor (or
was stuck in SrcEval and refused later by an unrelated stage); `plans/ingest-678/C2PRE.md` has the
outcomes. Only the `case` part goes through the certified kernel as it is (the kernel accepts it
today); every other part is built on an ingested honest program below the kernel, as a kernel
without the contract comparison would accept it: the kernel refuses each today because its
conversion compares binder contracts, or because a stored recursor's type must be the generated
one. -/

namespace IxCCTests.Recheck.Erased

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Src (Assert expect)
open IxCCTests.Recheck.Hostile (defn sidecar driver mkCert ofErr)
open IxCCTests.IxonV3.Builder (store block arrow lambda)
open IxCCTests.Support.Bound (loadBase addEnum addSimple simpleBlock Field)

abbrev X := IxCC.Ixon.V3.Expr

/-- The enumeration (or inductive) at `refs[0]`. -/
def E : X := .ref 0 #[]

/-! ## The harness -/

structure Honest where
  inp : Recheck.Input
  cfg : Recheck.Config
  cert : Recheck.Cert
  art : Recheck.Artifact

def objMain (art : Recheck.Artifact) : Option Sem.Obs :=
  match (art.linked driver).run (0, []) 1000000 with
  | .ok o => o
  | _ => none

def srcMain (art : Recheck.Artifact) (main : Src.CId) : Option Sem.Obs :=
  match Src.run art.src 100000 main [] with
  | .ok v => Src.readback art.src art.checked.keeps v
  | _ => none

def lookup (P : Src.Program) (a : IxCC.Ixon.Address) (what : String) : IO Src.CId :=
  match P.lookup a with
  | some c => pure c
  | none => throw (IO.userError s!"{what} is not in the program read")

/-- Ingress (the certified kernel's acceptance), `produce` and `Recheck.run`. -/
def ingest (label : String) (env : Env) (roots : List (String × IxCC.Ixon.Address))
    (chosen : List String := []) : IO Honest := do
  let inp ← ofErr s!"{label}: ingress" (Recheck.ingress (IxCCTests.Support.Bound.write env) (sidecar roots) chosen)
  let cfg := Recheck.Config.forInput {} inp
  let cert ← ofErr s!"{label}: produce" (Recheck.produce cfg inp)
  let art ← ofErr s!"{label}: Recheck.run" (Recheck.run cfg inp.program cert)
  return { inp, cfg, cert, art }

/-- The program with this table certificate and annotation compiles, and its object and SrcEval
return `expected` at `main`. -/
def accepted (a : Assert) (label : String) (cfg : Recheck.Config) (P : Src.Program)
    (tc : Src.Table.TableCert) (ann : Src.Relevance.Ann) (main : Src.CId) (expected : Sem.Obs) : IO Unit := do
  let cert ← ofErr s!"{label}: certificate" (mkCert cfg P tc ann)
  let art ← ofErr s!"{label}: Recheck.run" (Recheck.run cfg P cert)
  expect a (objMain art == some expected) s!"{label}: the object returns {repr (objMain art)}"
  expect a (srcMain art main == some expected) s!"{label}: SrcEval returns {repr (srcMain art main)}"

/-- The front end refuses it with a message containing every needle; so does `Recheck.run` on a
certificate made without the canonical check, where tiers S and C let one be made. -/
def refused (a : Assert) (label : String) (cfg : Recheck.Config) (P : Src.Program)
    (tc : Src.Table.TableCert) (ann : Src.Relevance.Ann) (needles : List String) : IO String := do
  let table ← match Src.Table.ofCert cfg.table P tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"{label}: the table refused it: {m}")
  let Pt := { P with table }
  let mut shown := ""
  match Src.Recheck.annotation Pt ann with
  | .ok _ => expect a false s!"{label}: accepted by Src.Recheck.annotation"
  | .error (.relevance errs) =>
    let ms := errs.toList.map (·.render Pt)
    shown := (ms.find? fun m => needles.all (m.contains ·)).getD ""
    expect a (!shown.isEmpty) s!"{label}: refused without naming {needles}: {ms}"
  | .error _ => expect a false s!"{label}: refused at install or table"
  match mkCert cfg P tc ann with
  | .ok cert =>
    match Recheck.run cfg P cert with
    | .ok _ => expect a false s!"{label}: Recheck.run accepted it"
    | .error e =>
      expect a (e.stage == .relevance && needles.all (e.message.contains ·))
        s!"{label}: Recheck.run refused it otherwise: {e.render}"
  | .error _ => pure ()
  return s!"{label}: {shown}"

def withNode (ann : Src.Relevance.Ann) (key : Src.TermKey) (tags : List Src.Relevance.Tag) : Src.Relevance.Ann :=
  if ann.nodes.any (·.1 == key) then
    { ann with nodes := ann.nodes.map fun (k, ts) => if k == key then (k, tags) else (k, ts) }
  else { ann with nodes := ann.nodes ++ [(key, tags)] }

/-- Write parameter `i` of a Π telescope erased. -/
def eraseParam : Nat → Src.Term → Src.Term
  | 0, .pi b r d body => .pi { b with contract := .erased } r d body
  | n + 1, .pi b r d body => .pi b r d (eraseParam n body)
  | _, t => t

/-- Map argument `pos` of the top spine of `t`, when it is headed by `head`. -/
def mapArg (head : Src.CId) (pos : Nat) (g : Src.Term.Arg → Src.Term.Arg) (t : Src.Term) : Src.Term :=
  let (h, args) := t.spine
  match h with
  | .const c _ =>
    if c == head then Src.Term.mkApps h (args.zipIdx.map fun (x, i) => if i == pos then g x else x) else t
  | _ => t

/-- The canonical record of `c` from its type (`checkCanonical`'s classifier); a parameter written
erased is a proof unless its type already makes it irrelevant (`KernelFront.honourErased`). -/
def canonRel (p : Src.Program) (c : Src.CId) : Src.Relevance.ConstRel :=
  match p.decl? c with
  | some d =>
    let (ps, res) := Src.Relevance.Check.Canonical.classifyTelescope p [] (d.type.piCount + 1) d.type
    { result := res.getD .rel
      params := ps.map fun (b, r?) =>
        if b.contract.uses == .erased then
          match r? with
          | some r => if r.alwaysIrr then r else Src.Rel.prf
          | none => Src.Rel.prf
        else r?.getD .rel }
  | none => { result := .rel, params := [] }

def withConst (ann : Src.Relevance.Ann) (p : Src.Program) (c : Src.CId) : Src.Relevance.Ann :=
  { ann with consts := ann.consts.insert c (canonRel p c) }

def withCtor (ann : Src.Relevance.Ann) (p : Src.Program) (k : Src.CId) : Src.Relevance.Ann :=
  match p.decl? k with
  | some (.ctor _ _ _ _ np _ _) =>
    let cr := canonRel p k
    { ann with consts := ann.consts.insert k cr
               ctors := ann.ctors.insert k { fields := (cr.params.drop np).map Src.Relevance.FieldClass.ofRel } }
  | _ => ann

/-- `rᵢ := cᵢ` for every constructor, so that every constructor is emitted. -/
def ctorRoots (e : Env) (ind : IxCC.Ixon.Address) (ctors : Array IxCC.Ixon.Address) :
    Env × List (String × IxCC.Ixon.Address) := Id.run do
  let mut e := e
  let mut roots := []
  for (c, i) in ctors.toList.zipIdx do
    let (e', r) := store e ⟨defn E (.ref 1 #[]), #[], #[ind, c], #[]⟩
    e := e'
    roots := roots ++ [(s!"r{i}", r)]
  return (e, roots)

def installed (h : Honest) : IO Src.Program :=
  match Src.Relevance.install h.inp.program h.cert.relevance with
  | .ok p => pure p
  | .error m => throw (IO.userError s!"install: {m}")

/-! ## A definition's own body, and a `csimp` redirect -/

/-- `E` (`c₀ c₁ c₂`), `idc (c : E) : E := c`, `k (a b : E) : E := a`,
`f : (x : E) → E → E := λ (x : E). idc` with contract `fc` on `x`, `main := f c₁ c₂`
(`c₂`), `useK := k c₀ c₀`. -/
def fProg (label : String) (fc : BinderContract) : IO (Honest × Src.CId × Src.CId × Src.CId) := do
  let (e, en) := addEnum (← loadBase) 3
  let (e, idc) := store e ⟨defn (arrow E E) (lambda E (.var 0)), #[], #[en.ind], #[]⟩
  let (e, k) := store e ⟨defn (arrow E (arrow E E)) (lambda E (lambda E (.var 1))), #[], #[en.ind], #[]⟩
  let (e, f) := store e ⟨defn (.all fc .shared E (arrow E E)) (.lam fc E (.ref 1 #[])), #[], #[en.ind, idc], #[]⟩
  let (e, main) := store e ⟨defn E (.app (.app (.ref 1 #[]) (.ref 2 #[])) (.ref 3 #[])), #[],
    #[en.ind, f, en.ctors[1]!, en.ctors[2]!], #[]⟩
  let (e, useK) := store e ⟨defn E (.app (.app (.ref 1 #[]) (.ref 2 #[])) (.ref 2 #[])), #[],
    #[en.ind, k, en.ctors[0]!], #[]⟩
  let (e, rs) := ctorRoots e en.ind en.ctors
  let h ← ingest label e ([("main", main), ("useK", useK)] ++ rs)
  let P := h.inp.program
  return (h, ← lookup P f "f", ← lookup P k "k", ← lookup P main "main")

def valueAndCsimp (a : Assert) : IO (Array String) := do
  let c₂ : Sem.Obs := .ctor 2 []
  let (h, f, k, main) ← fProg "own body" .erased
  let P := h.inp.program
  expect a (objMain h.art == some c₂ && srcMain h.art main == some c₂) "own body: the honest twin is not c₂"
  -- the value η-short under the erased parameter: `f := k`
  let some (.defn _ _ _ fTy _) := P.decl? f | throw (IO.userError "f")
  let short ← refused a "own body, η-short under a parameter written erased" h.cfg
    (P.setDecl f (.defn .defn .safe 0 fTy (.const k []))) h.cert.table (withNode h.cert.relevance (.value f) [])
    [s!"in the value of {P.short f}", "parameter 0 is written erased"]
  -- csimp f g thm, with `g : E → E → E := λ a b. a` (the `0` not written on `g`)
  let some (P', g, thm) := IxCCTests.Src.withCsimpTwin P f | throw (IO.userError "no csimp twin")
  let (eS, rest) := match fTy with
    | .pi _ _ d body => (d, body)
    | t => (t, t)
  let gVal : Src.Term := .lam {} eS (.lam {} eS (.var 1))
  let P' := P'.setDecl g (.defn .defn .safe 0 (.pi {} {} eS rest) gVal)
  let ann := withNode (withConst h.cert.relevance P' g) (.value g) [.lam .rel .never, .lam .rel .never]
  let tc := { h.cert.table with resolve := (f, .csimp g thm) :: h.cert.table.resolve }
  let redirect ← refused a "csimp redirect of a definition with a parameter written erased" h.cfg P' tc ann
    [s!"({P.short f})", s!"the csimp redirect to {P'.short g}", "parameter 0 is written erased"]
  -- a lazy row or a word entry proposed for `f` is refused by the table
  let lazyTc := { h.cert.table with lazy := (f, 2) :: h.cert.table.lazy }
  expect a ((Src.Table.ofCert h.cfg.table P lazyTc) matches .error _) "a lazy row for f: accepted by the table"
  let wordTc := { h.cert.table with resolve := (f, .word .w64 .add f) :: h.cert.table.resolve }
  expect a ((Src.Table.ofCert h.cfg.table P wordTc) matches .error _) "a word entry for f: accepted by the table"
  -- an `eqn` entry for `f` with `thm : ∀ (0 x : E) (y : E), f x y = y`: the table builds an
  -- equation body from the subject's header only against a checked pair of a resource context
  let some eqId := P.known.eq | throw (IO.userError "no Eq")
  let lhs := Src.Term.mkApps (.const f []) [(.var 1, .strict, .rel), (.var 0, .strict, .rel)]
  let stmt := Src.Term.pi { contract := .erased } {} eS (.pi {} {} eS
    (Src.Term.mkApps (.const eqId [.succ .zero]) [(eS, .strict, .rel), (lhs, .strict, .rel), (.var 0, .strict, .rel)]))
  let ta := IxCCTests.Src.Builder.fakeAddr (P.size + 3000000)
  let Pq := P.push { ref := .member ta 0, addr := ta, decl := .defn .thm .safe 0 stmt (.natLit 0) }
  let eqnTc := { h.cert.table with resolve := (f, .eqn P.size) :: h.cert.table.resolve }
  match Src.Table.ofCert h.cfg.table Pq eqnTc with
  | .ok _ => expect a false "an eqn entry for f: accepted by the table"
  | .error m => expect a (m.contains "eqn-drops-contracts") s!"an eqn entry for f: refused otherwise: {m}"
  -- the other direction: `f` erases nothing, `g : (0 x : E) → E → E := λ (0 x) y. y`
  let (h, f, _, main) ← fProg "csimp, the target erasing" .many
  let P := h.inp.program
  let some (.defn _ _ _ fTy _) := P.decl? f | throw (IO.userError "f")
  let (eS, rest) := match fTy with
    | .pi _ _ d body => (d, body)
    | t => (t, t)
  let some (P', g, thm) := IxCCTests.Src.withCsimpTwin P f | throw (IO.userError "no csimp twin")
  let gVal : Src.Term := .lam { contract := .erased } eS (.lam {} eS (.var 0))
  let P' := P'.setDecl g (.defn .defn .safe 0 (.pi { contract := .erased } {} eS rest) gVal)
  let ann := withNode (withConst h.cert.relevance P' g) (.value g)
    [.lam ((canonRel P' g).params.headD .rel) .never, .lam .rel .never]
  let tc := { h.cert.table with resolve := (f, .csimp g thm) :: h.cert.table.resolve }
  accepted a "csimp to a target whose type writes its first parameter erased" h.cfg P' tc ann main c₂
  return #[short, redirect, "csimp to a target writing its parameter erased: accepted, c₂ (object and SrcEval)",
    "a lazy row, a word entry and an eqn entry (no resource context) proposed for f: refused by the table"]

/-! ## A `case` entry, through the certified kernel -/

/-- `E.casesOn.{u} : (motive : E → Sort u) → (t : E) → motive c₀ → (m₁ : motive c₁) → motive c₂ →
motive t := λ motive t m₀ m₁ m₂. E.rec.{u} motive m₀ m₁ m₂ t`, contract `mc` on `m₁` (type and λ). -/
def casesOnC (en : IxCCTests.Support.Bound.Ind) (mc : BinderContract) : Constant :=
  let mot : X := arrow E (.sort 0)
  let d0 : X := .app (.var 1) (.ref 1 #[])
  let d1 : X := .app (.var 2) (.ref 2 #[])
  let d2 : X := .app (.var 3) (.ref 3 #[])
  let ty : X := .all .many .shared mot (.all .many .shared E (.all .many .shared d0
    (.all mc .shared d1 (.all .many .shared d2 (.app (.var 4) (.var 3))))))
  let body : X := .app (.app (.app (.app (.app (.ref 4 #[0]) (.var 4)) (.var 2)) (.var 1)) (.var 0)) (.var 3)
  let val : X := .lam .many mot (.lam .many E (.lam .many d0 (.lam mc d1 (.lam .many d2 body))))
  ⟨.defn ⟨.defn, .safe, 1, ty, val⟩, #[], #[en.ind, en.ctors[0]!, en.ctors[1]!, en.ctors[2]!, en.recursor], #[.var 0]⟩

/-- `main := E.casesOn.{1} (λ _ : E. E) c₁ c₀ c₂ c₁` (`c₂`). -/
def casesEnv (mc : BinderContract) : IO (Env × IxCC.Ixon.Address × List (String × IxCC.Ixon.Address)) := do
  let (e, en) := addEnum (← loadBase) 3
  let (e, co) := store e (casesOnC en mc)
  let (e, main) := store e ⟨defn E (.app (.app (.app (.app (.app (.ref 1 #[0]) (.lam .many E E)) (.ref 3 #[]))
    (.ref 2 #[])) (.ref 4 #[])) (.ref 3 #[])), #[], #[en.ind, co, en.ctors[0]!, en.ctors[1]!, en.ctors[2]!],
    #[.succ .zero]⟩
  let (e, rs) := ctorRoots e en.ind en.ctors
  return (e, co, [("main", main)] ++ rs)

def caseEntry (a : Assert) : IO (Array String) := do
  let c₂ : Sem.Obs := .ctor 2 []
  let (e, _, roots) ← casesEnv .many
  let h ← ingest "casesOn, nothing erased" e roots
  let some (_, main) := h.inp.program.roots.head? | throw (IO.userError "no root")
  expect a (objMain h.art == some c₂ && srcMain h.art main == some c₂) "casesOn control: not c₂"
  -- the minor m₁ written erased: the kernel accepts the artifact, the producer refuses it
  let (e, co, roots) ← casesEnv .erased
  let inp ← ofErr "casesOn with m₁ erased: ingress" (Recheck.ingress (IxCCTests.Support.Bound.write e) (sidecar roots) [])
  let P := inp.program
  let coId ← lookup P co "casesOn"
  let cfg := Recheck.Config.forInput {} inp
  let needles := [s!"({P.short coId})", "parameter 3 is written erased", "its case entry"]
  match Recheck.produce cfg inp with
  | .ok _ => expect a false "casesOn with m₁ erased: produce accepted it"
  | .error err =>
    expect a (err.code == "relevance-S1" && needles.all (err.message.contains ·))
      s!"casesOn with m₁ erased: produce refused it otherwise: {err.render}"
  -- the kernel annotator's own annotation (Stage A holds), on a certificate made without the check
  let (table, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let ann ← match inp.kernel.annotateChecked { P with table } with
    | .ok ann => pure ann
    | .error m => throw (IO.userError s!"casesOn: the annotator: {m}")
  let tc := Src.Table.TableCert.ofTable table
  expect a (Recheck.checkCanonicalRelevance cfg inp tc ann) "casesOn with m₁ erased: Stage A refuses the annotator's annotation"
  expect a (tc.resolve.lookup coId == some .case) "casesOn with m₁ erased: no case entry"
  let line ← refused a "a case entry whose type writes a minor erased (kernel-accepted)" cfg P tc ann needles
  return #["casesOn control: accepted, c₂ (object and SrcEval)", line]

/-! ## A recursor -/

/-- Lean's recursor of an `n`-constructor enumeration block `blk` (no contract written). -/
def enumRec (blk : IxCC.Ixon.Address) (n : Nat) : Constant := Id.run do
  let refs := #[indcProjAddr blk 0] ++ (Array.range n).map (ctorProjAddr blk 0 ·.toUInt64)
  let tyRef : X := .ref 0 #[]
  let motiveTy : X := arrow tyRef (.sort 0)
  let minor := fun (k : Nat) => (.app (.var k.toUInt64) (.ref (1 + k).toUInt64 #[]) : X)
  let major : X := arrow tyRef (.app (.var (n + 1).toUInt64) (.var 0))
  let typ : X := arrow motiveTy ((List.range n).foldr (fun k acc => arrow (minor k) acc) major)
  let rule := fun (k : Nat) => Id.run do
    let mut body : X := .var (n - 1 - k).toUInt64
    for k' in (List.range n).reverse do
      body := lambda (minor k') body
    return (⟨0, lambda motiveTy body⟩ : RecursorRule)
  let r : Recursor := ⟨false, false, 1, 0, 0, 1, n.toUInt64, typ, (Array.range n).map rule⟩
  return ⟨.recr r, #[], refs, #[.var 0]⟩

def recursor (a : Assert) : IO (Array String) := do
  let n := 4
  let (e, blk) := block (← loadBase) (simpleBlock ((Array.range n).map fun _ => #[]))
  let (e, recr) := store e (enumRec blk n)
  let ind := indcProjAddr blk 0
  let ctors := (Array.range n).map (ctorProjAddr blk 0 ·.toUInt64)
  -- main := F.rec.{1} (λ _ : F. F) d₀ d₁ d₂ d₃ d₁ (`d₁`)
  let (e, main) := store e ⟨defn E (.app (.app (.app (.app (.app (.app (.ref 1 #[0]) (.lam .many E E))
    (.ref 2 #[])) (.ref 3 #[])) (.ref 4 #[])) (.ref 5 #[])) (.ref 3 #[])), #[],
    #[ind, recr, ctors[0]!, ctors[1]!, ctors[2]!, ctors[3]!], #[.succ .zero]⟩
  let (e, rs) := ctorRoots e ind ctors
  let h ← ingest "recursor" e ([("main", main)] ++ rs)
  let P := h.inp.program
  let rId ← lookup P recr "the recursor"
  let mainId ← lookup P main "main"
  expect a (objMain h.art == some (.ctor 1 []) && srcMain h.art mainId == some (.ctor 1 []))
    "recursor control: not d₁"
  -- the recursor's type writes minor 1 (parameter 2) erased; its rules are unchanged
  let Pi ← installed h
  let some (.recr s k l np nmot nmin ni ind' rules ty) := Pi.decl? rId | throw (IO.userError "recursor")
  let Pi := Pi.setDecl rId (.recr s k l np nmot nmin ni ind' rules (eraseParam 2 ty))
  let some (.defn dk ds dl mty mval) := Pi.decl? mainId | throw (IO.userError "main")
  let mval := mapArg rId 2 (fun (x, m, _) => (x, m, Src.Rel.prf)) mval
  let Pi := Pi.setDecl mainId (.defn dk ds dl mty mval)
  let ann := withNode (withConst h.cert.relevance Pi rId) (.value mainId) mval.tagOrder
  let line ← refused a "a recursor whose type writes a minor erased" h.cfg Pi h.cert.table ann
    [s!"({P.short rId})", "parameter 2 is written erased", "the recursor"]
  return #["recursor control: accepted, d₁ (object and SrcEval)", line]

/-! ## Minor premises against constructor fields -/

/-- `Key.casesOn.{u} : (motive : Key → Sort u) → (t : Key) → ((a b c : E) → motive (mk a b c)) →
motive t := λ motive t m. Key.rec.{u} motive (λ a b c. m a b c) t` (refs: `Key`, `mk`, `E`,
`Key.rec`); the table's scan gives it a `case` entry. -/
def keyCasesOn (key : IxCCTests.Support.Bound.Ind) (eInd : IxCC.Ixon.Address) : Constant :=
  let keyT : X := .ref 0 #[]
  let eT : X := .ref 2 #[]
  let mot : X := arrow keyT (.sort 0)
  let mDom : X := .all .many .shared eT (.all .many .shared eT (.all .many .shared eT
    (.app (.var 4) (.app (.app (.app (.ref 1 #[]) (.var 2)) (.var 1)) (.var 0)))))
  let ty : X := .all .many .shared mot (.all .many .shared keyT (.all .many .shared mDom (.app (.var 2) (.var 1))))
  let wrapper : X := lambda eT (lambda eT (lambda eT (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0))))
  let val : X := lambda mot (lambda keyT (lambda mDom
    (.app (.app (.app (.ref 3 #[0]) (.var 2)) wrapper) (.var 1))))
  ⟨.defn ⟨.defn, .safe, 1, ty, val⟩, #[], #[key.ind, key.ctors[0]!, eInd, key.recursor], #[.var 0]⟩

/-- `Key | mk (a b c : E)` with its recursor, `useG3 (a b c : E) : E := b`, and
`main := Key.rec.{1} (λ _ : Key. E) useG3 (mk c₀ c₁ c₂)` (`c₁`), or with `viaCase`,
`main := Key.casesOn.{1} (λ _ : Key. E) (mk c₀ c₁ c₂) useG3`. Returns the program, the
eliminator `main` applies, `mk`, `main`, and the minor's and the major's argument positions. -/
def keyProg (label : String) (viaCase : Bool) :
    IO (Honest × Src.CId × Src.CId × Src.CId × Nat × Nat) := do
  let (e, en) := addEnum (← loadBase) 3
  let (e, key) := addSimple e #[#[.ext en.ind, .ext en.ind, .ext en.ind]]
  let (e, useG) := store e ⟨defn (arrow E (arrow E (arrow E E))) (lambda E (lambda E (lambda E (.var 1)))), #[],
    #[en.ind], #[]⟩
  let (e, elim) := if viaCase then store e (keyCasesOn key en.ind) else (e, key.recursor)
  let motive : X := .lam .many (.ref 2 #[]) (.ref 0 #[])
  let major : X := .app (.app (.app (.ref 4 #[]) (.ref 5 #[])) (.ref 6 #[])) (.ref 7 #[])
  let body : X := if viaCase then .app (.app (.app (.ref 1 #[0]) motive) major) (.ref 3 #[])
    else .app (.app (.app (.ref 1 #[0]) motive) (.ref 3 #[])) major
  let (e, main) := store e ⟨defn E body, #[],
    #[en.ind, elim, key.ind, useG, key.ctors[0]!, en.ctors[0]!, en.ctors[1]!, en.ctors[2]!], #[.succ .zero]⟩
  let (e, rs) := ctorRoots e en.ind en.ctors
  let h ← ingest label e ([("main", main)] ++ rs)
  let P := h.inp.program
  let elimId ← lookup P elim (if viaCase then "Key.casesOn" else "Key.rec")
  if viaCase then
    expect' (h.cert.table.resolve.lookup elimId == some .case) s!"{label}: Key.casesOn has no case entry"
  return (h, elimId, ← lookup P key.ctors[0]! "Key.mk", ← lookup P main "main",
    if viaCase then 2 else 1, if viaCase then 1 else 2)
where
  expect' (cond : Bool) (msg : String) : IO Unit := unless cond do throw (IO.userError msg)

def minors (a : Assert) (viaCase : Bool) : IO (Array String) := do
  let route := if viaCase then "case entry" else "recursor"
  let (h, rId, mkId, main, minorPos, majorPos) ← keyProg s!"minors, {route}" viaCase
  expect a (objMain h.art == some (.ctor 1 []) && srcMain h.art main == some (.ctor 1 []))
    s!"minors control ({route}): not c₁"
  let Pi ← installed h
  let some (.defn dk ds dl mty mval) := Pi.decl? main | throw (IO.userError "main")
  let some (.ctor _ _ _ _ _ _ mkTy) := Pi.decl? mkId | throw (IO.userError "mk")
  let eS : Src.Term := match mkTy with
    | .pi _ _ d _ => d
    | t => t
  let ePrf : Src.Binder := { contract := .erased, rel := Src.Rel.prf }
  /- `λ a (0 b) c. body`, as a minor -/
  let lam3 := fun (body : Src.Term) => Src.Term.lam {} eS (.lam ePrf eS (.lam {} eS body))
  let withMinor := fun (P : Src.Program) (minor : Src.Term) =>
    let v := mapArg rId minorPos (fun (_, m, r) => (minor, m, r)) mval
    (P.setDecl main (.defn dk ds dl mty v), v)
  -- no field written erased: a minor whose middle λ is written erased returns its third or first field
  let mut out := #[]
  for (body, expected, what) in [(Src.Term.var 0, Sem.Obs.ctor 2 [], "c"), (.var 2, .ctor 0 [], "a")] do
    let (P, v) := withMinor Pi (lam3 body)
    accepted a s!"{route}: minor λ a (0 b) c. {what} on mk c₀ c₁ c₂" h.cfg P h.cert.table
      (withNode h.cert.relevance (.value main) v.tagOrder) main expected
    out := out.push s!"{route}: minor λ a (0 b) c. {what}, no field erased: accepted, {repr expected} (object and SrcEval)"
  -- field 1 written erased on `mk`, and the program's `mk c₀ c₁ c₂` passing □ for it
  let some (.ctor x1 x2 x3 x4 np nf _) := Pi.decl? mkId | throw (IO.userError "mk")
  let Pe := Pi.setDecl mkId (.ctor x1 x2 x3 x4 np nf (eraseParam 1 mkTy))
  let dropB := mapArg rId majorPos fun (x, m, r) => (mapArg mkId 1 (fun (y, m', _) => (y, m', Src.Rel.prf)) x, m, r)
  let annE := withCtor h.cert.relevance Pe mkId
  -- the η-short minor `useG3`, as the program has it
  let v := dropB mval
  let P := Pe.setDecl main (.defn dk ds dl mty v)
  out := out.push (← refused a s!"{route}: an η-short minor over a field written erased" h.cfg P h.cert.table
    (withNode annE (.value main) v.tagOrder)
    [s!"in the value of {P.short main}", s!"({P.short mkId})", "minor 0 does not bind field 1, which is written erased"])
  -- its honest twin: the minor binds the erased field with an erased λ
  let (P, v) := withMinor Pe (lam3 (.var 0))
  let v := dropB v
  let P := P.setDecl main (.defn dk ds dl mty v)
  accepted a s!"{route}: minor λ a (0 b) c. c over field 1 written erased" h.cfg P h.cert.table
    (withNode annE (.value main) v.tagOrder) main (.ctor 2 [])
  return out.push s!"{route}: minor λ a (0 b) c. c, field 1 erased: accepted, c₂ (object and SrcEval)"

/-! ## Quotients, the pinned `Nat.succ` and a primitive -/

def quotAddrs (env : Env) : List (QuotKind × IxCC.Ixon.Address) :=
  env.consts.toList.filterMap fun (a, bytes) =>
    match V3.decodeConstant bytes with
    | .ok dc =>
      match dc.value.info with
      | .quot q => some (q.kind, a)
      | _ => none
    | .error _ => none

/-- `main := Quot.lift.{1,1} E (Eq E) E idc h (Quot.mk.{1} E (Eq E) c₁)` (`c₁`), built on an
ingested program that reads `Quot.lift`, `Quot.mk` and `Eq` (unchosen sidecar roots), with
`Quot.lift`'s function or `Quot.mk`'s element written erased. -/
def quot (a : Assert) : IO (Array String) := do
  let env0 ← loadBase
  let qs := quotAddrs env0
  let some qty := qs.lookup .type | throw (IO.userError "no Quot in the base")
  let some qmkA := qs.lookup .ctor | throw (IO.userError "no Quot.mk in the base")
  let some qliftA := qs.lookup .lift | throw (IO.userError "no Quot.lift in the base")
  let (e, en) := addEnum env0 3
  let (e, idc) := store e ⟨defn (arrow E E) (lambda E (.var 0)), #[], #[en.ind], #[]⟩
  let (e0, m0) := store e ⟨defn E (.ref 1 #[]), #[], #[en.ind, en.ctors[1]!], #[]⟩
  let inp0 ← ofErr "quot: first ingress" (Recheck.ingress (IxCCTests.Support.Bound.write e0) (sidecar [("main", m0)]) [])
  let some eq0 := inp0.program.known.eq | throw (IO.userError "no Eq")
  let eqA := inp0.program.addr eq0
  let eqE : X := .app (.ref 2 #[0]) E
  let hDom : X := .all .many .shared E (.all .many .shared E (.all .many .shared
    (.app (.app (.app (.ref 2 #[0]) E) (.var 1)) (.var 0))
    (.app (.app (.app (.ref 2 #[0]) E) (.app (.var 3) (.var 2))) (.app (.var 3) (.var 1)))))
  let qlTy : X := .all .many .shared (arrow E E) (.all .many .shared hDom
    (.all .many .shared (.app (.app (.ref 3 #[0]) E) eqE) E))
  let (e, ql) := store e ⟨.defn ⟨.defn, .safe, 0, qlTy, .app (.app (.app (.ref 1 #[0, 0]) E) eqE) E⟩, #[],
    #[en.ind, qliftA, eqA, qty], #[.succ .zero]⟩
  let (e, qm) := store e ⟨.defn ⟨.defn, .safe, 0, .app (.app (.ref 3 #[0]) E) eqE,
    .app (.app (.app (.ref 1 #[0]) E) eqE) (.ref 4 #[])⟩, #[], #[en.ind, qmkA, eqA, qty, en.ctors[1]!], #[.succ .zero]⟩
  let (e, main) := store e ⟨defn E (.ref 1 #[]), #[], #[en.ind, en.ctors[1]!], #[]⟩
  let (e, rs) := ctorRoots e en.ind en.ctors
  let h ← ingest "quot" e ([("main", main)] ++ rs ++ [("ql", ql), ("qm", qm), ("idc", idc)])
    (["main"] ++ rs.map (·.1))
  let P := h.inp.program
  let mainId ← lookup P main "main"
  let liftId ← lookup P qliftA "Quot.lift"
  let mkId ← lookup P qmkA "Quot.mk"
  let idcId ← lookup P idc "idc"
  let eId ← lookup P en.ind "E"
  let c1 ← lookup P en.ctors[1]! "c₁"
  let some eqId := P.known.eq | throw (IO.userError "no Eq")
  let Pi ← installed h
  let one : IxCC.Ixon.Univ := .succ .zero
  let eT : Src.Term := .const eId []
  let eqT : Src.Term := .app (.const eqId [one]) eT .strict .type
  let build := fun (eraseLift eraseMk : Bool) => Id.run do
    let mut P := Pi
    if eraseLift then
      if let some (.quot qk l ty) := P.decl? liftId then P := P.setDecl liftId (.quot qk l (eraseParam 3 ty))
    if eraseMk then
      if let some (.quot qk l ty) := P.decl? mkId then P := P.setDecl mkId (.quot qk l (eraseParam 2 ty))
    let mkV := Src.Term.mkApps (.const mkId [one])
      [(eT, .strict, .type), (eqT, .strict, .type), (.const c1 [], .strict, if eraseMk then Src.Rel.prf else .rel)]
    let v := Src.Term.mkApps (.const liftId [one, one])
      [(eT, .strict, .type), (eqT, .strict, .type), (eT, .strict, .type),
       (.const idcId [], .strict, if eraseLift then Src.Rel.prf else .rel), (.sort .zero, .strict, Src.Rel.prf),
       (mkV, .strict, .rel)]
    let Q := P.setDecl mainId (.defn .defn .safe 0 eT v)
    let ann := withConst (withConst (withConst h.cert.relevance Q liftId) Q mkId) Q idcId
    let ann := withNode (withNode ann (.value mainId) v.tagOrder) (.value idcId) [.lam .rel .never]
    (Q, ann)
  let (P0, ann0) := build false false
  accepted a "Quot.lift idc h (Quot.mk r c₁)" h.cfg P0 h.cert.table ann0 mainId (.ctor 1 [])
  let (P1, ann1) := build true false
  let lift ← refused a "Quot.lift with its function written erased" h.cfg P1 h.cert.table ann1
    [s!"({P.short liftId})", "parameter 3 is written erased, but Quot.lift reads it"]
  let (P2, ann2) := build false true
  let mk ← refused a "Quot.mk with its element written erased" h.cfg P2 h.cert.table ann2
    [s!"({P.short mkId})", "parameter 2 is written erased, but Quot.mk reads it"]
  return #["Quot.lift idc h (Quot.mk r c₁): accepted, c₁ (object and SrcEval)", lift, mk]

/-- `main : Nat := Nat.succ 4` and `main : Nat := Nat.add 2 3` (`5`) on an ingested program
(the pinned constants are read with it), with the field or the first parameter written erased. -/
def pinned (a : Assert) : IO (Array String) := do
  let (e, en) := addEnum (← loadBase) 3
  let (e, main) := store e ⟨defn E (.ref 1 #[]), #[], #[en.ind, en.ctors[1]!], #[]⟩
  let (e, rs) := ctorRoots e en.ind en.ctors
  let h ← ingest "pinned" e ([("main", main)] ++ rs)
  let P := h.inp.program
  let mainId ← lookup P main "main"
  let some natId := P.known.nat | throw (IO.userError "no Nat")
  let some succId := P.known.natSucc | throw (IO.userError "no Nat.succ")
  let some addN := P.known.pins.prims.lookup .add | throw (IO.userError "no Nat.add pin")
  let some addId := (List.range P.size).find? fun c => IxCC.Src.Pinned.addrNat (P.addr c) == addN
    | throw (IO.userError "Nat.add is not in the program read")
  let Pi ← installed h
  let natT : Src.Term := .const natId []
  let five : Sem.Obs := .nat 5
  let succ := fun (erase : Bool) => Id.run do
    let mut P := Pi
    if erase then
      if let some (.ctor x1 x2 x3 x4 np nf ty) := P.decl? succId then
        P := P.setDecl succId (.ctor x1 x2 x3 x4 np nf (eraseParam 0 ty))
    let v := Src.Term.app (.const succId []) (.natLit 4) .strict (if erase then Src.Rel.prf else .rel)
    let Q := P.setDecl mainId (.defn .defn .safe 0 natT v)
    (Q, withNode (withCtor h.cert.relevance Q succId) (.value mainId) v.tagOrder)
  let (P0, ann0) := succ false
  accepted a "Nat.succ 4" h.cfg P0 h.cert.table ann0 mainId five
  let (P1, ann1) := succ true
  let s ← refused a "Nat.succ with its field written erased" h.cfg P1 h.cert.table ann1
    [s!"({P.short succId})", "parameter 0 is written erased, but the constructor reads it"]
  let tc := if h.cert.table.resolve.any (·.1 == addId) then h.cert.table
    else { h.cert.table with resolve := (addId, .prim .add) :: h.cert.table.resolve }
  let add := fun (erase : Bool) => Id.run do
    let mut P := Pi
    if erase then
      if let some (.defn dk ds dl ty v) := P.decl? addId then
        P := P.setDecl addId (.defn dk ds dl (eraseParam 0 ty) v)
    let v := Src.Term.mkApps (.const addId [])
      [(.natLit 2, .strict, if erase then Src.Rel.prf else .rel), (.natLit 3, .strict, .rel)]
    let Q := P.setDecl mainId (.defn .defn .safe 0 natT v)
    (Q, withNode (withConst h.cert.relevance Q addId) (.value mainId) v.tagOrder)
  let (P2, ann2) := add false
  accepted a "Nat.add 2 3" h.cfg P2 tc ann2 mainId five
  let (P3, ann3) := add true
  let ad ← refused a "Nat.add with parameter 0 written erased" h.cfg P3 tc ann3
    [s!"({P.short addId})", "parameter 0 is written erased, but the primitive Nat.add reads it"]
  return #["Nat.succ 4 and Nat.add 2 3: accepted, 5 (object and SrcEval)", s, ad]

def run (a : Assert) : IO (Array String) := do
  return (← valueAndCsimp a) ++ (← caseEntry a) ++ (← recursor a) ++ (← minors a false) ++
    (← minors a true) ++ (← quot a) ++
    (← pinned a)

end IxCCTests.Recheck.Erased
