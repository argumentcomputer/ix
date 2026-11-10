import IxCCTests.Recheck.Hostile

/-! # Deep and wide inputs, for the verifiers' native stack

The verifier's traversals recurse natively, so the depth of what they walk
must stay within what a thread's stack holds. This module generates the
shapes that stress that, as Ixon v4 bytes:

* `deep n`: `main : L := cons c₀ (cons c₀ (… nil))`, `n` constructor
  applications deep (stored as a chain of `share`s, each at most 200 deep, so
  the decoder accepts it). The source, Lam and Anf terms are all about `n`
  deep.
* `wide d`: the inline amplifier with `g = f`: `f x` is a balanced `k`-tree of depth
  `d` over `x`, a share DAG of `d + 1` stored nodes whose Lam expansion has
  `2^(d+1) - 1` calls, each of which ANF conversion turns into one binding of
  a chain.
* `deepType n`: `main : F (F (… (F E))) := c₀` with `n` applications of the
  identity type function `F`.
* `deepApp n` and `deepLet n`: `n` applications of an identity function, and
  `n` nested `let`s.
* `tree d`: a balanced constructor tree of depth `d` (a share DAG), whose ANF
  is a chain of `2^(d+1) - 1` bindings each used later.
* `many n`: `n + 1` distinct globals, each calling the next.

`stage` runs the recheck path on one of them up to a named stage
(`ingress`, `annotate`, `front`, `erase`, `convert`, `run`, or `verify`, which
runs every verifier entry point), so that a script can find, under a small
Lean stack (`LEAN_STACK_SIZE_KB`, which sets the stack of the thread running a
Lean `main`; `ulimit -s` does not), the depth at which each stage overflows;
`probeAmp` and `probeWalk` do the same for the inline amplifier and for one walk.
`stack8` is the regression test: every verifier entry point on the crashing
inputs and on these shapes at and past each budget, in a child process whose
stack is 8 MiB (`stackPart`). `writeShrink` and `writeAmpShrink` write inputs
whose certificates ask for many shrink rounds, for timing `check-cert`. -/

namespace IxCCTests.Recheck.Deep

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Recheck.Hostile
open IxCCTests.Src (Assert expect)
open IxCCTests.IxonV3.TypingFixtures (store block bytes arrow lambda)

/-- `inductive L | nil | cons (e : E) (l : L)` over the type at `refs[0]`. -/
def listBlock (elem : Addr) : Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0,
      #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
        ⟨false, 0, 1, 0, 2, arrow (.ref 0 #[]) (arrow (.recur 0 #[]) (.recur 0 #[]))⟩]⟩],
    #[], #[elem], #[.succ .zero]⟩

/-- `step` applied `n` times to `inner`, stored as a chain of shares of at most
200 steps each: the expression and its share table. -/
def chain (step : X → X) (inner : X) (n : Nat) : Array X × X := Id.run do
  let mut sh : Array X := #[]
  let mut cur := inner
  let mut remaining := n
  for _ in [0:(n + 199) / 200] do
    let k := min 200 remaining
    sh := sh.push (Nat.repeat step k cur)
    cur := .share (sh.size - 1).toUInt64
    remaining := remaining - k
  return (sh, cur)

/-- `deep n`. -/
def deepEnv (n : Nat) : Env × Addr := Id.run do
  let b := base 3
  let (e, blk) := block b.env (listBlock b.enumI)
  let listI := Tc.indcProjAddr blk 0
  let nil := Tc.ctorProjAddr blk 0 0
  let cons := Tc.ctorProjAddr blk 0 1
  -- refs: 0 L, 1 cons, 2 nil, 3 c₀
  let (sh, v) := chain (fun t => .app (.app (.ref 1 #[]) (.ref 3 #[])) t) (.ref 2 #[]) n
  let (e, main) := store e ⟨defn (.ref 0 #[]) v, sh, #[listI, cons, nil, b.ctors[0]!], #[]⟩
  return (e, main)

/-- `deepType n`. -/
def deepTypeEnv (n : Nat) : Env × Addr := Id.run do
  let b := base 3
  let (e, f) := store b.env ⟨defn (arrow (.sort 0) (.sort 0)) (lambda (.sort 0) (.var 0)), #[], #[],
    #[.succ .zero]⟩
  -- refs: 0 E, 1 F, 2 c₀
  let (sh, ty) := chain (fun t => .app (.ref 1 #[]) t) (.ref 0 #[]) n
  let (e, main) := store e ⟨defn ty (.ref 2 #[]), sh, #[b.enumI, f, b.ctors[0]!], #[]⟩
  return (e, main)

/-- `deepApp n`: `main : E := idc (idc (… c₁))`, `n` applications of the identity
function deep. -/
def deepAppEnv (n : Nat) : Env × Addr := Id.run do
  let b := base 3
  -- refs: 0 E, 1 idc, 2 c₁
  let (sh, v) := chain (fun t => .app (.ref 1 #[]) t) (.ref 2 #[]) n
  let (e, main) := store b.env ⟨defn (.ref 0 #[]) v, sh, #[b.enumI, b.idc, b.ctors[1]!], #[]⟩
  return (e, main)

/-- `deepLet n`: `main : E := let x₀ : E := c₀; let x₁ : E := x₀; …; xₙ`, `n + 1`
nested `let`s. -/
def deepLetEnv (n : Nat) : Env × Addr := Id.run do
  let b := base 3
  let c : LetContract := { nonDep := false }
  -- refs: 0 E, 1 c₀
  let (sh, v) := chain (fun t => .letE c (.ref 0 #[]) (.var 0) t) (.var 0) n
  let (e, main) := store b.env
    ⟨defn (.ref 0 #[]) (.letE c (.ref 0 #[]) (.ref 1 #[]) v), sh, #[b.enumI, b.ctors[0]!], #[]⟩
  return (e, main)

/-- `many n`: `main : E := fₙ c₀` with `f₀ x := x` and `fᵢ₊₁ x := fᵢ x`, `n + 1`
distinct globals, so that every level holds that many functions. -/
def manyEnv (n : Nat) : Env × Addr := Id.run do
  let b := base 3
  -- f₀: refs 0 E
  let (e0, f0) := store b.env ⟨defn (arrow (.ref 0 #[]) (.ref 0 #[])) (lambda (.ref 0 #[]) (.var 0)), #[],
    #[b.enumI], #[]⟩
  let mut e := e0
  let mut f := f0
  for _ in [0:n] do
    -- fᵢ₊₁: refs 0 E, 1 fᵢ
    let (e', f') := store e ⟨defn (arrow (.ref 0 #[]) (.ref 0 #[]))
      (lambda (.ref 0 #[]) (.app (.ref 1 #[]) (.var 0))), #[], #[b.enumI, f], #[]⟩
    e := e'
    f := f'
  -- refs: 0 E, 1 fₙ, 2 c₀
  let (eM, main) := store e ⟨defn (.ref 0 #[]) (.app (.ref 1 #[]) (.ref 2 #[])), #[], #[b.enumI, f, b.ctors[0]!], #[]⟩
  return (eM, main)

/-- `shared n`: `main : E := idc t (w t)`, where `t` is `n` applications of
`idc` over `c₁` and `w` wraps `n` more around it, all stored as shares of at
most 200: the term's tree is about `2 n` deep, but `t` is first used shallowly.
Ingress used to reuse its conversion under `w` without counting its depth
again; it now checks a reused share's height against the depth left there. -/
def sharedEnv (n : Nat) : Env × Addr := Id.run do
  let b := base 3
  -- refs: 0 E, 1 idc, 2 c₁
  let step := fun (t : X) => (.app (.ref 1 #[]) t : X)
  let mut sh : Array X := #[]
  let mut cur : X := .ref 2 #[]
  for _ in [0:(n + 199) / 200] do
    sh := sh.push (Nat.repeat step 200 cur)
    cur := .share (sh.size - 1).toUInt64
  let top := cur
  for _ in [0:(n + 199) / 200] do
    sh := sh.push (Nat.repeat step 200 cur)
    cur := .share (sh.size - 1).toUInt64
  let (e, main) := store b.env ⟨defn (.ref 0 #[]) (.app (.app (.ref 1 #[]) top) cur), sh,
    #[b.enumI, b.idc, b.ctors[1]!], #[]⟩
  return (e, main)

/-- `inductive T | leaf | node (l r : T)`. -/
def treeBlock : Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0,
      #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
        ⟨false, 0, 1, 0, 2, arrow (.recur 0 #[]) (arrow (.recur 0 #[]) (.recur 0 #[]))⟩]⟩],
    #[], #[], #[.succ .zero]⟩

/-- `main : T`, a balanced tree of `node`s of depth `d` stored as a share DAG
(`d + 1` stored nodes): its Lam term has `2^(d+1) - 1` constructor nodes and
ANF conversion makes it a chain of that many constructor bindings, each used
later, so every shrink round's census reads the rest of the chain at each of
them. -/
def treeEnv (d : Nat) : Env × Addr := Id.run do
  let (e, blk) := block {} treeBlock
  let tI := Tc.indcProjAddr blk 0
  let leaf := Tc.ctorProjAddr blk 0 0
  let node := Tc.ctorProjAddr blk 0 1
  -- refs: 0 T, 1 node, 2 leaf
  let mut sh : Array X := #[.app (.app (.ref 1 #[]) (.ref 2 #[])) (.ref 2 #[])]
  for i in [1:d+1] do
    let prev : X := .share (i - 1).toUInt64
    sh := sh.push (.app (.app (.ref 1 #[]) prev) prev)
  let (e, main) := store e ⟨defn (.ref 0 #[]) (.share d.toUInt64), sh, #[tI, node, leaf], #[]⟩
  return (e, main)

/-- A shape's bytes and sidecar. -/
def shape (name : String) (n : Nat) : Except String (ByteArray × Lean.Json) :=
  match name with
  | "deep" => let (e, main) := deepEnv n; .ok (bytes e, sidecar [("main", main)])
  | "deepType" => let (e, main) := deepTypeEnv n; .ok (bytes e, sidecar [("main", main)])
  | "wide" => let (e, _, _, main) := ampEnv n 0; .ok (bytes e, sidecar [("main", main)])
  | "tree" => let (e, main) := treeEnv n; .ok (bytes e, sidecar [("main", main)])
  | "deepApp" => let (e, main) := deepAppEnv n; .ok (bytes e, sidecar [("main", main)])
  | "deepLet" => let (e, main) := deepLetEnv n; .ok (bytes e, sidecar [("main", main)])
  | "many" => let (e, main) := manyEnv n; .ok (bytes e, sidecar [("main", main)])
  | _ => .error s!"unknown shape {name}"

/-- The certificate Stage A expects: the table `Table.build` proposes and the
canonical annotation, with no middle-end step. -/
def baseCert (inp : Recheck.Input) (cfg : Recheck.Config) : Except String Recheck.Cert := do
  let P := inp.program
  let (table0, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let tc := Src.Table.TableCert.ofTable table0
  let table ← Src.Table.ofCert cfg.table P tc
  let ann ← Src.Relevance.annotate inp.env { P with table }
  return { table := tc, relevance := ann }

/-- A shape's environment and root. -/
def shapeEnv (name : String) (n : Nat) : Except String (Env × Addr) :=
  match name with
  | "deep" => .ok (deepEnv n)
  | "deepType" => .ok (deepTypeEnv n)
  | "wide" => let (e, _, _, main) := ampEnv n 0; .ok (e, main)
  | "tree" => .ok (treeEnv n)
  | "deepApp" => .ok (deepAppEnv n)
  | "deepLet" => .ok (deepLetEnv n)
  | "many" => .ok (manyEnv n)
  | _ => .error s!"unknown shape {name}"

/-- A certificate for a deep instance that the annotator cannot produce (it
types through `Tc`, whose stack stops at 1,024 frames): the annotation of a
shallow instance (`n₀` deep) carried over by address, with the root's value
tags repeated to its depth. The constants other than the root are the same in
both, and each level of the chain carries the same tags. This is what a
claimant can hand a program-level verifier, which runs no annotator. -/
def transplantedCert (name : String) (n n₀ : Nat) (inp : Recheck.Input) (cfg : Recheck.Config) :
    Except String Recheck.Cert := do
  let (e₀, main₀) ← shapeEnv name n₀
  let inp₀ ← (Recheck.ingress (bytes e₀) (sidecar [("main", main₀)]) [] true).mapError (·.render)
  let cfg₀ := Recheck.Config.forInput {} inp₀
  let base₀ ← baseCert inp₀ cfg₀
  -- the tags one more level adds, from an instance one level deeper
  let (e₁, main₁) ← shapeEnv name (n₀ + 1)
  let inp₁ ← (Recheck.ingress (bytes e₁) (sidecar [("main", main₁)]) [] true).mapError (·.render)
  let base₁ ← baseCert inp₁ (Recheck.Config.forInput {} inp₁)
  let rootTags := fun (inp : Recheck.Input) (main : Addr) (b : Recheck.Cert) =>
    match inp.program.lookup main with
    | some m => (b.relevance.nodes.lookup (Src.TermKey.value m)).getD []
    | none => []
  let len₀ := (rootTags inp₀ main₀ base₀).length
  let perLevel := (rootTags inp₁ main₁ base₁).length - len₀
  let P := inp.program
  let P₀ := inp₀.program
  let some (mainAddr, mainId) := P.roots.head? | throw "no root"
  let some mainId₀ := P₀.lookup main₀ | throw "no shallow root"
  let remap := fun (c : Src.CId) => if c == mainId₀ then some mainId else P.lookup (P₀.addr c)
  let _ := mainAddr
  let consts := Src.NatMap.ofList (base₀.relevance.consts.toList.filterMap fun (c, r) =>
    (remap c).map (·, r))
  let ctors := Src.NatMap.ofList (base₀.relevance.ctors.toList.filterMap fun (c, r) =>
    (remap c).map (·, r))
  let key := fun (k : Src.TermKey) => match k with
    | .value c => (remap c).map Src.TermKey.value
    | .eqn c => (remap c).map Src.TermKey.eqn
    | .rule r j => (remap r).map (Src.TermKey.rule · j)
  let nodes := base₀.relevance.nodes.filterMap fun (k, tags) => (key k).map fun k' =>
    if k == Src.TermKey.value mainId₀ then
      -- each level of the chain carries the same tags
      (k', List.replicate (len₀ + (n - n₀) * perLevel) (tags.headD default))
    else (k', tags)
  let (table0, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  return { table := Src.Table.TableCert.ofTable table0, relevance := { consts, ctors, nodes } }

/-- `c` with the backend parts (allocation, frames, block order) the producer
makes for the program that `c`'s front end and middle end give, so that the
verifier's replay of a hostile middle end reaches the end of the backend. -/
def withBackend (cfg : Recheck.Config) (P : Src.Program) (c : Recheck.Cert) : Except String Recheck.Cert := do
  let f ← (Recheck.runLir cfg P c).mapError (·.render)
  let (xv, _) ← (Xv.Select.run f.lowered.program).mapError fun e => (Recheck.Err.ofSelect e).render
  let r ← Xv.Alloc.run cfg.env xv
  let layouts := Xv.Stacking.produce r.program
  let stacked ← (Xv.Stacking.run r.program layouts f.lowered.reps cfg.env).mapError fun e =>
    (Recheck.Err.ofBackend (.stacking e)).render
  let order := X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape
  return { c with alloc := r.outs, frames := layouts, order }

/-- Run the recheck path on `bytes` up to `stage`; the outcome as a line. -/
def stage (name : String) (bs : ByteArray) (json : Lean.Json) (typecheck : Bool)
    (mkCert : Recheck.Input → Recheck.Config → Except String Recheck.Cert := baseCert) : IO String := do
  let inp ← match Recheck.ingress bs json [] typecheck with
    | .ok i => pure i
    | .error e => return s!"ingress refused: {e.render}"
  if name == "ingress" then return "ingress ok"
  let cfg := Recheck.Config.forInput {} inp
  let P := inp.program
  let base ← match mkCert inp cfg with
    | .ok c => pure c
    | .error m => return s!"table or annotate refused: {m}"
  if name == "annotate" then return "annotate ok"
  let base ← if name == "run" || name == "verify" then
      match withBackend cfg P base with
      | .ok c => pure c
      | .error m => return s!"backend producer refused: {m}"
    else pure base
  if name == "verify" then
    let claim : CompileClaim :=
      { env := inp.env.root, target := (P.roots.head?.map (·.1)).getD default, policy := .immortal
        abiArity := 0, elfHash := Address.blake3Pure (ByteArray.mk #[0]) }
    let text := base.toText
    let sip : Ring0.Ring0Sip := { cfg, claim, certText := text, driver }
    let rs := [("verifyBytes", CompileClaim.verifyBytes cfg bs json claim text typecheck),
      ("checkClaim", (CompileClaim.checkClaim cfg bs json claim text typecheck).isOk),
      ("Ring0Sip.verifyBytes", sip.verifyBytes bs json typecheck),
      ("verifyProgram", CompileClaim.verifyProgram cfg P claim text),
      ("checkClaimProgram", (CompileClaim.checkClaimProgram cfg P claim text).isOk),
      ("Ring0Sip.verifyProgram", sip.verifyProgram P)]
    return s!"verify: {rs.map fun (n, b) => s!"{n} {b}"}"
  let (src, checked) ← match Recheck.front cfg P base with
    | .ok r => pure r
    | .error e => return s!"front refused: {e.render}"
  if name == "front" then return "front ok"
  let (lam, _) ← match Lam.erase src checked with
    | .ok r => pure r
    | .error _ => return "erase refused"
  if name == "erase" then return s!"erase ok, {lam.size} globals"
  match Anf.convert lam with
  | .error m => return s!"convert refused: {m}"
  | .ok _ => if name == "convert" then return "convert ok" else pure ()
  match Recheck.run cfg P base with
  | .ok _ => return "run ok"
  | .error e => return s!"run refused: {e.render}"

/-- `tests-recheck --write-shrink DIR D [ROUNDS STEPS]`: `treeEnv D` as
`tree-D.ixe` and its sidecar, with a certificate whose table and relevance are
Stage A's and whose middle end is `STEPS` shrink steps (1 by default) of
`ROUNDS` rounds (64 by default) of every global, written as
`tree-D.shrink.cert` (`tree-D-ROUNDS-STEPS.shrink.cert` if given). -/
def writeShrink (dir : System.FilePath) (d : Nat) (rounds : Nat := 64) (steps : Nat := 1)
    (stem : String := s!"tree-{d}") : IO Unit := do
  let (e, main) := treeEnv d
  let bs := bytes e
  let json := sidecar [("main", main)]
  let inp ← IO.ofExcept ((Recheck.ingress bs json [] true).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let base ← IO.ofExcept (baseCert inp cfg)
  let cert : Recheck.Cert :=
    { base with mid := { steps := List.replicate steps (.shrink (List.replicate 16 rounds)) } }
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / s!"{stem}.ixe") bs
  IO.FS.writeFile (dir / s!"{stem}.equations.json") json.pretty
  IO.FS.writeFile (dir / s!"{stem}.shrink.cert") cert.toText
  IO.FS.writeFile (dir / s!"{stem}.base.cert") base.toText
  IO.println s!"{stem}: {bs.size} bytes, certificate {cert.toText.utf8ByteSize} bytes"

/-- `tests-recheck --write-amp DIR DF DG`: the inline amplifier `amp-DF-DG` as `.ixe`, its
sidecar, and its `inline` certificate (`.hostile.cert`) and Stage A's
(`.base.cert`), for timing `check-cert` natively. -/
def writeAmp (dir : System.FilePath) (dF dG : Nat) : IO Unit := do
  let (bs, json, _, _, _, hostile) ← ampCase dF dG
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / s!"amp-{dF}-{dG}.ixe") bs
  IO.FS.writeFile (dir / s!"amp-{dF}-{dG}.equations.json") json.pretty
  IO.FS.writeFile (dir / s!"amp-{dF}-{dG}.hostile.cert") hostile.toText
  IO.FS.writeFile (dir / s!"amp-{dF}-{dG}.base.cert") { hostile with mid := {} }.toText

/-- `tests-recheck --write-amp-shrink DIR DF DG`: the inline amplifier `amp-DF-DG`
as `amp-DF-DG.ixe` and its sidecar, with a certificate whose middle end is its
`inline` step followed by 64 shrink rounds of every global, so that the shrink
census runs over the inlined global. -/
def writeAmpShrink (dir : System.FilePath) (dF dG : Nat) : IO Unit := do
  let (bs, json, _, _, _, hostile) ← ampCase dF dG
  let cert : Recheck.Cert :=
    { hostile with mid := { steps := hostile.mid.steps ++ [.shrink (List.replicate 16 64)] } }
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / s!"amp-{dF}-{dG}.ixe") bs
  IO.FS.writeFile (dir / s!"amp-{dF}-{dG}.equations.json") json.pretty
  IO.FS.writeFile (dir / s!"amp-{dF}-{dG}.shrink.cert") cert.toText
  IO.println s!"amp-{dF}-{dG}: {bs.size} bytes, certificate {cert.toText.utf8ByteSize} bytes"

/-- `tests-recheck --probe-amp DF DG [STAGE]`: the inline amplifier with its single
`inline` step (`Hostile.ampCase`), for a global the step grows to near the
budgets, up to `STAGE`: `anf` (the middle end's replay), `lir`
(`Recheck.runLir`), `produce` (the producer's backend parts) or `run` (the
default: `Recheck.run` on the certificate with those parts). -/
def probeAmp (dF dG : Nat) (stg : String := "run") : IO UInt32 := do
  let (_, _, inp, cfg, _, hostile) ← ampCase dF dG
  let P := inp.program
  let nodes := fun (A : Anf.Program) => A.globalList.map fun (p : Anf.GlobalId × Anf.GDef) => p.2.body.nodes
  IO.println s!"amp-{dF}-{dG} to {stg}: {← match stg with
    | "anf" => pure <| match Recheck.front cfg P hostile with
      | .error e => s!"front refused: {e.render}"
      | .ok (src, checked) => match Lam.erase src checked with
        | .error _ => "erase refused"
        | .ok (lam, _) => match Anf.Pipeline.run hostile.mid lam with
          | .ok A => s!"anf ok, global nodes {nodes A}"
          | .error m => s!"anf refused: {m}"
    | "lir" => pure <| match Recheck.runLir cfg P hostile with
      | .ok f => s!"lir ok, Anf global nodes {nodes f.anf}"
      | .error e => s!"lir refused: {e.render}"
    | "produce" => pure <| match withBackend cfg P hostile with
      | .ok _ => "produce ok"
      | .error m => s!"backend producer refused: {m}"
    | _ => pure <| match withBackend cfg P hostile with
      | .error m => s!"backend producer refused: {m}"
      | .ok c => match Recheck.run cfg P c with
        | .ok a => s!"run ok, Anf global nodes {nodes a.anf}"
        | .error e => s!"run refused: {e.render}"}"
  return 0

/-- `tests-recheck --probe-walk N`: one `inline` walk that copies an
`N`-binding callee into a caller, so the walk recurses about `N` bindings deep
(the copy is `2 N + 1` nodes, checked against the copy budget as it goes). -/
def probeWalk (n : Nat) : IO UInt32 := do
  let out := match Anf.Inline.round (callersProgram 1 1 n) [(1, [0])] with
    | .ok (P, _) => s!"inline ok, global nodes {P.globalList.map fun (p : Anf.GlobalId × Anf.GDef) => p.2.body.nodes}"
    | .error m => s!"inline refused: {m}"
  IO.println s!"walk {n}: {out}"
  return 0

/-! ## Every verifier on an 8 MiB stack -/

/-- Every verifier entry point on one input, with a claim for its environment
and root (and a hash no object has, so nothing is accepted): `verifyBytes`,
`checkClaim` and `Ring0Sip.verifyBytes` on the bytes, and, if ingress accepts
them, `verifyProgram`, `checkClaimProgram`, `Ring0Sip.verifyProgram`,
`Recheck.run` and an in-process `check-cert`. The outcomes as a line. -/
def entryPoints (dir : System.FilePath) (label : String) (bs : ByteArray) (json : Lean.Json) (main : Addr)
    (typecheck : Bool) (mkCert : Recheck.Input → Recheck.Config → Except String Recheck.Cert) :
    IO String := do
  let env ← IO.ofExcept (V3.decodeAnonymousEnv bs)
  let claim : CompileClaim := { env := env.root, target := main, policy := .immortal, abiArity := 0
                                elfHash := Address.blake3Pure (ByteArray.mk #[0]) }
  let (inp?, cert) ← match Recheck.ingress bs json [] typecheck with
    | .error e => pure (Sum.inl e.render, ({} : Recheck.Cert))
    | .ok inp => match mkCert inp (Recheck.Config.forInput {} inp) with
      | .ok c => pure (Sum.inr inp, c)
      | .error m => throw (IO.userError s!"{label}: no certificate: {m}")
  let text := cert.toText
  let word := fun (b : Bool) => if b then "accepted" else "refused"
  let cfg := match inp? with | .inr inp => Recheck.Config.forInput {} inp | .inl _ => {}
  let sip : Ring0.Ring0Sip := { cfg, claim, certText := text, driver }
  let bytesLevel := [s!"verifyBytes {word (CompileClaim.verifyBytes cfg bs json claim text typecheck)}",
    s!"checkClaim {word (CompileClaim.checkClaim cfg bs json claim text typecheck).isOk}",
    s!"Ring0Sip.verifyBytes {word (sip.verifyBytes bs json typecheck)}"]
  let rest ← match inp? with
    | .inl e => pure [s!"ingress refused ({e})"]
    | .inr inp =>
      let P := inp.program
      let run := match Recheck.run cfg P cert with
        | .ok _ => "accepted"
        | .error e => s!"refused ({e.stage.name}: {e.code}: {e.message.take 60})"
      IO.FS.writeBinFile (dir / "c.ixe") bs
      IO.FS.writeFile (dir / "c.json") json.pretty
      let cc ← match ← checkCert dir cert (if typecheck then [] else ["--no-typecheck"]) with
        | .ok () => pure "accepted"
        | .error e => pure s!"refused ({e.stage.name}: {e.code})"
      pure [s!"verifyProgram {word (CompileClaim.verifyProgram cfg P claim text)}",
        s!"checkClaimProgram {word (CompileClaim.checkClaimProgram cfg P claim text).isOk}",
        s!"Ring0Sip.verifyProgram {word (sip.verifyProgram P)}", s!"Recheck.run {run}", s!"check-cert {cc}"]
  return s!"{label} ({bs.size} bytes): {", ".intercalate (bytesLevel ++ rest)}"

/-- The longest chain of shape `name` that ingress accepts (typing off): the
largest `n` whose terms are within `Src.Ingress.depthBudget`. -/
def deepest (name : String) : IO Nat := do
  let ok := fun (n : Nat) => match shapeEnv name n with
    | .ok (e, main) => (Recheck.ingress (bytes e) (sidecar [("main", main)]) [] false).isOk
    | .error _ => false
  let mut lo := 1
  let mut hi := Src.Ingress.depthBudget + 1
  if !ok lo || ok hi then throw (IO.userError s!"{name}: the depth budget does not bound the chain")
  for _ in [0:32] do
    if hi - lo ≤ 1 then break
    let mid := (lo + hi) / 2
    if ok mid then lo := mid else hi := mid
  return lo

/-- `tests-recheck --stack-8mib`, run by `stackPart` with `LEAN_STACK_SIZE_KB=8192`:
every verifier entry point on the crashing inputs and on generated deep and
wide inputs at and past each budget, typing on and off. A line per input, then
a summary line; a native stack overflow aborts the process instead. -/
def stack8Lines : IO (Array String) := IO.FS.withTempDir fun dir => do
  let mut lines : Array String := #[]
  -- The amplifier inputs (`amp-12-11` and `amp-13-13` crashed an 8 MiB checker), the
  -- largest inline the copy budget allows through to the end of the backend,
  -- and one just past it
  for (dF, dG, full) in [(12, 11, false), (13, 13, false), (2, 7, true), (3, 7, true)] do
    let (bs, json, _, _, main, hostile) ← ampCase dF dG
    let mk := fun (inp : Recheck.Input) (cfg : Recheck.Config) =>
      .ok (if full then (withBackend cfg inp.program hostile).toOption.getD hostile else hostile)
    lines := lines.push (← entryPoints dir s!"amp-{dF}-{dG} inline" bs json main true mk)
    if !full then
      lines := lines.push (← entryPoints dir s!"amp-{dF}-{dG} base" bs json main true
        fun _ _ => .ok { hostile with mid := {} })
  -- wide: the Lam global at the P1 budget and past it
  for d in [11, 13] do
    let (e, _, _, main) := ampEnv d 0
    lines := lines.push (← entryPoints dir s!"wide {d}" (bytes e) (sidecar [("main", main)]) main true
      fun inp cfg => do
        let b ← baseCert inp cfg
        return (withBackend cfg inp.program b).toOption.getD b)
  -- deep: at the ingress depth budget and past it, typing off (typing refuses
  -- them sooner), with a certificate carried over from a shallow instance
  for name in ["deep", "deepApp", "deepLet", "deepType"] do
    let n ← deepest name
    for (m, pos) in [(n, "at"), (n + 1, "past")] do
      let (e, main) ← IO.ofExcept (shapeEnv name m)
      lines := lines.push (← entryPoints dir s!"{name} {m} ({pos} the depth budget)" (bytes e)
        (sidecar [("main", main)]) main false fun inp cfg => do
          let c ← transplantedCert name m 200 inp cfg
          return (withBackend cfg inp.program c).toOption.getD c)
  -- a share converted once and reused deeper: ingress checks its height
  -- against the depth left at each use
  let (e, main) := sharedEnv 1200
  lines := lines.push (← entryPoints dir "shared 1200 + 1200 (past the depth budget, shares reused)" (bytes e)
    (sidecar [("main", main)]) main false fun _ _ => .ok {})
  return lines

/-- The parent of `stack8`: the same executable with `LEAN_STACK_SIZE_KB=8192`
(the stack of the thread that runs a Lean `main`; `ulimit -s` does not
change it), which must exit normally with a line per input. -/
def stackPart (a : Assert) : IO (Array String) := do
  let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["--stack-8mib"]
                                env := #[("LEAN_STACK_SIZE_KB", some "8192")] }
  let lines := (out.stdout.splitOn "\n").filter (!·.isEmpty)
  expect a (out.exitCode == 0)
    s!"tests-recheck --stack-8mib exited with {out.exitCode} on an 8 MiB stack: {out.stderr}"
  let summary := lines.getLast?.getD ""
  expect a (summary.startsWith "stack-8mib:") s!"tests-recheck --stack-8mib: no summary line: {summary}"
  let has := fun (pre sub : String) =>
    lines.any fun l => l.startsWith pre && (l.splitOn sub).length > 1
  -- The amplifier inputs are refused by the budgets, not by a crash
  expect a (has "amp-12-11 inline" "Lam global exceeds") "amp-12-11 is not refused by the Lam node budget"
  expect a (has "amp-13-13 base" "Lam global exceeds") "amp-13-13 is not refused by the Lam node budget"
  expect a (has "wide 13" "Lam global exceeds") "wide 13 is not refused by the Lam node budget"
  -- every input past the depth budget is refused at ingress
  for name in ["deep", "deepApp", "deepLet", "deepType"] do
    expect a (lines.any fun l => l.startsWith s!"{name} " && (l.splitOn "(past the depth budget)").length > 1
        && (l.splitOn "expression depth budget exhausted").length > 1)
      s!"{name} past the depth budget is not refused at ingress"
    expect a (lines.any fun l => l.startsWith s!"{name} " && (l.splitOn "(at the depth budget)").length > 1
        && (l.splitOn "Recheck.run").length > 1)
      s!"{name} at the depth budget does not reach the program-level verifiers"
  -- nothing is accepted (the claims name a hash no object has)
  let claimed := ["verifyBytes accepted", "checkClaim accepted", "verifyProgram accepted",
    "checkClaimProgram accepted"]
  expect a (lines.all fun l => claimed.all fun w => (l.splitOn w).length == 1)
    "a verifier accepted a claim with a made-up hash"
  let inL := fun (l a : String) => (l.splitOn a).length > 1
  -- ingress counts a reused share's height against the depth left
  expect a (has "shared" "expression depth budget exhausted")
    "shares reused deeper than the depth budget are not refused at ingress"
  -- nesting depth: every chain at its budget passes the check, one level past is refused
  let lam := lines.filter (·.startsWith "lam ")
  let anf := lines.filter (·.startsWith "anf ")
  let inl := lines.filter (·.startsWith "inline case ")
  expect a (lam.length == 20 && anf.length == 14 && inl.length == 2)
    s!"nesting lines: {lam.length} Lam, {anf.length} Anf, {inl.length} inline"
  for l in lam do
    expect a (if inL l "(at " then !inL l "Lam global exceeds"
      else (inL l "Pipeline.run refused" && inL l "Lam global exceeds the depth budget")) s!"Lam chain: {l}"
  for l in anf do
    expect a (if inL l "(at " then (inL l "check accepted" && !inL l "exceeds the depth budget")
      else inL l "check refused (middle end: a global exceeds the depth budget)")
      s!"Anf chain: {l}"
  for l in inl do
    expect a (if inL l "(at " then (inL l "check accepted" && inL l "inline walk accepted")
      else (inL l "inline walk refused" && inL l "walk: depth budget exhausted")) s!"inline copy: {l}"
  return lines.toArray

/-! ## Lam chains of one nesting constructor -/

/-- `n` levels of `kind` above `.box`: `lam`, `app` (argument), `appf`
(function), `let` (body), `letv` (bound value), `con` (field), `case`
(alternative), `cases` (scrutinee), `proj` or `tick`. -/
def lamChain (kind : String) (n : Nat) : Lam.Term :=
  let c : V3.LetContract := { nonDep := false }
  (List.range n).foldl (fun t _ => match kind with
    | "lam" => .lam .strict {} t
    | "app" => .app (.glob 0) t .strict
    | "appf" => .app t .box .strict
    | "let" => .letE c .box t
    | "letv" => .letE c t .box
    | "con" => .con (.src 0) [t]
    | "case" => .case .box [.mk (.src 1) 0 t] none
    | "cases" => .case t [.mk (.src 1) 0 .box] none
    | "proj" => .proj (.src 0) 0 t
    | _ => .tick t) .box

/-- One global, `lamChain kind n`. -/
def lamProgram (kind : String) (n : Nat) : Lam.Program :=
  { globals := Src.NatMap.ofList [(0, ({ key := default, body := lamChain kind n } : Lam.Global))], size := 1,
    roots := [0], ctors := [{ key := .src 0, tag := 0, arity := 1 }, { key := .src 1, tag := 1, arity := 0 }],
    known := default }

/-- `tests-recheck --probe-lam KIND N STAGE`: `lamProgram KIND N` through
`Lam.modesOk` (which erasure runs on its output), the middle end's Lam check (`check`) or P1
without it (`convert`). -/
def probeLam (kind : String) (n : Nat) (stg : String) : IO UInt32 := do
  let L := lamProgram kind n
  let out := match stg with
    | "modesOk" => s!"modesOk {Lam.modesOk L}"
    | "check" => match Anf.Pipeline.checkLamNodes L with
      | .ok _ => "check ok"
      | .error m => s!"check refused: {m}"
    | _ => match Anf.convert L with
      | .ok P => s!"convert ok, {(P.globalList.map fun (p : Anf.GlobalId × Anf.GDef) => p.2.body.nodes)} nodes"
      | .error m => s!"convert refused: {m}"
  IO.println s!"lam {kind} {n} {stg}: {out}"
  return 0

/-! ## Anf chains of one nesting constructor -/

/-- `n` levels of `kind` above `bottom`: `tick`, a single-alternative `case`,
a two-alternative `case` (`case2`), erasure's `tick (case …)` (`tcase`), a
join point in the bound expression's place (`join`) or in the body
(`joinb`), or else a binding. -/
def anfChain (kind : String) (n : Nat) (bottom : Anf.Exp) : Anf.Exp :=
  (List.range n).foldl (fun e _ => match kind with
    | "tick" => .tick e
    | "case" => .case (.var 0) [.mk (.src 0) 0 e] none
    | "case2" => .case (.var 0) [.mk (.src 0) 0 e, .mk (.src 1) 0 (.ret (.var 0))] none
    | "tcase" => .tick (.case (.var 0) [.mk (.src 0) 0 e] none)
    | "join" => .join 0 false (.ret .box) e
    | "joinb" => .join 0 false e (.jump 0 [])
    | _ => .bind Anf.freshLet (.atom .box) e) bottom

/-- Two nullary constructors, for the chains' `case`s. -/
def anfCtors : List Lam.CtorInfo :=
  [{ key := .src 0, tag := 0, arity := 0 }, { key := .src 1, tag := 1, arity := 0 }]

/-- `k` globals of one parameter, each `anfChain kind n` over `ret` of it, or
(`wide`) one `case` of `n` alternatives, each returning, or (`comb`) one of eight
alternatives, each `anfChain "case" n`, or (`live`) `n` copies of the parameter
all live into one constructor. -/
def chainProgram (kind : String) (n k : Nat) : Anf.Program :=
  let body : Anf.Exp := if kind == "wide" then
      .case (.var 0) ((List.range n).map fun i => .mk (.src i) 0 (.ret (.var 0))) none
    else if kind == "comb" then
      .case (.var 0) ((List.range 8).map fun i => .mk (.src i) 0 (anfChain "case" n (.ret (.var 0)))) none
    else if kind == "live" then
      (List.range n).foldl (fun e _ => .bind Anf.freshLet (.atom (.var 0)) e)
        (.bind Anf.freshLet (.con (.src 0) ((List.range n).map fun i => .var i)) (.ret (.var 0)))
    else anfChain kind n (.ret (.var 0))
  let g := fun i => ({ key := .dispatch i, ps := [{}], body } : Anf.GDef)
  { globals := Src.NatMap.ofList ((List.range k).map fun i => (i, g i)), size := k, roots := [k - 1],
    ctors := if kind == "wide" then (List.range n).map fun i => { key := .src i, tag := i, arity := 0 }
      else if kind == "comb" then (List.range 8).map fun i => { key := .src i, tag := i, arity := 0 }
      else if kind == "live" then [{ key := .src 0, tag := 0, arity := n }]
      else anfCtors, known := {} }

/-- `tests-recheck --probe-walkk KIND N C OP`: one walk over a global of `N`
levels of `KIND` (`anfChain`): a shrink round (`shrink`), or an inline walk
(`inline`) that copies a callee of `C` such levels at the global's bottom, so
the walk recurses about `N + C` levels deep. The budgets are not checked
first, so this measures the walk's own native depth. -/
def probeWalkKind (kind : String) (n c : Nat) (op : String) : IO UInt32 := do
  let callee : Anf.GDef := { key := .dispatch 0, ps := [{}], body := anfChain kind c (.ret (.var 0)) }
  let bottom : Anf.Exp :=
    if op == "inline" then .bind Anf.freshLet (.call 0 [.var 0]) (.ret (.var 0)) else .ret (.var 0)
  let g : Anf.GDef := { key := .dispatch 1, ps := [{}], body := anfChain kind n bottom }
  let P : Anf.Program := { globals := Src.NatMap.ofList [(0, callee), (1, g)], size := 2, roots := [1],
                           ctors := anfCtors, known := {} }
  let out := match op with
    | "shrink" => match Anf.Shrink.round P {} g with
      | .ok (g', f) => s!"shrink ok: {g'.body.nodes} nodes, walk depth {f.depth}"
      | .error m => s!"shrink refused: {m}"
    | _ => match Anf.Inline.round P [(1, [0])] with
      | .ok (P', f) => s!"inline ok: {(P'.globalList.map fun (p : Anf.GlobalId × Anf.GDef) => p.2.body.nodes)} nodes, walk depth {f.depth}"
      | .error m => s!"inline refused: {m}"
  IO.println s!"walk {kind} {n} + {c} {op}: {out}"
  return 0

/-- Run `x`, recording its wall time under `label`. -/
def timed {α : Type} (label : String) (acc : IO.Ref (Array String)) (x : Unit → Except String α) : IO α := do
  let t0 ← IO.monoMsNow
  match x () with
  | .ok a =>
    let t1 ← IO.monoMsNow
    acc.modify (·.push s!"{label} {t1 - t0} ms")
    pure a
  | .error m => throw (IO.userError s!"{label}: {m}")

/-- `tests-recheck --probe-back KIND N K`: `chainProgram KIND N K` through the
verifier's levels after the middle end, with the producer's allocation, frames
and order, each level timed. -/
def probeBack (kind : String) (n k : Nat) : IO UInt32 := do
  let P := chainProgram kind n k
  let acc ← IO.mkRef #[]
  let cfg : Recheck.Config := {}
  let refused := fun (s : String) => s!"{s} refused"
  let fir ← timed "Fir.lower" acc fun _ => (Fir.lower P).mapError fun _ => refused "Fir.lower"
  let own ← timed "Own.immortal" acc fun _ => .ok (Own.immortal fir)
  let C ← timed "Cfg.lower" acc fun _ => .ok (Cfg.lower own)
  let _ ← timed "Rt.checkSwitches" acc fun _ => (Rt.checkSwitches C).mapError fun _ => refused "switches"
  let l ← timed "Rt.lower" acc fun _ => (Rt.lower { names := cfg.names } C).mapError fun _ => refused "Rt.lower"
  let (xvp, _) ← timed "producer Select.run" acc fun _ =>
    (Xv.Select.run l.program).mapError fun _ => refused "Select.run"
  let r ← timed "producer Alloc.run" acc fun _ => Xv.Alloc.run cfg.env xvp
  let layouts ← timed "producer Stacking.produce" acc fun _ => .ok (Xv.Stacking.produce r.program)
  let st0 ← timed "producer Stacking.run" acc fun _ =>
    (Xv.Stacking.run r.program layouts l.reps cfg.env).mapError fun _ => refused "Stacking.run"
  let order ← timed "producer Order.produce" acc fun _ =>
    .ok (X86.Layout.Order.produce (X86.Layout.tunnel st0.program) st0.shape)
  let xv ← timed "Select.select" acc fun _ => (Xv.Select.select l.program).mapError fun _ => refused "select"
  let _ ← timed "Validate.program" acc fun _ =>
    (Xv.Validate.program cfg.env xv r.outs).mapError fun _ => refused "validate"
  let xl ← timed "Alloc.applyProgram" acc fun _ => Xv.Alloc.applyProgram xv r.outs
  let st ← timed "Stacking.run" acc fun _ =>
    (Xv.Stacking.run xl layouts l.reps cfg.env).mapError fun _ => refused "Stacking.run"
  let tun ← timed "Layout.tunnel" acc fun _ => .ok (X86.Layout.tunnel st.program)
  let (prog, _) ← timed "Layout.run" acc fun _ =>
    (X86.Layout.run tun st.shape order).mapError fun _ => refused "Layout.run"
  let checked ← timed "Program.checkK" acc fun _ => prog.checkK.mapError fun _ => refused "checkK"
  let _ ← timed "Stream.encodeK" acc fun _ => (X86.Stream.encodeK checked).mapError fun _ => refused "encodeK"
  let _ ← timed "Backend.finish" acc fun _ =>
    (Backend.finish xl.main st prog [] (Recheck.defaultProvenance default)).mapError fun _ => refused "finish"
  IO.println s!"back {kind} {n} x{k} (back work {Anf.backWork P}, {(P.globalList.map fun (p : Anf.GlobalId × Anf.GDef) => p.2.body.nodes).foldl (· + ·) 0} nodes): {", ".intercalate (← acc.get).toList}"
  return 0

/-- `tests-recheck --probe STAGE SHAPE N [--no-typecheck] [--transplant]`. -/
def probe (args : List String) : IO UInt32 := do
  match args with
  | stg :: shp :: n :: rest =>
    let (bs, json) ← IO.ofExcept (shape shp n.toNat!)
    let mkCert := if rest.contains "--transplant" then transplantedCert shp n.toNat! 200
      else if rest.contains "--empty" then fun _ _ => .ok {} else baseCert
    IO.println s!"{shp} {n} ({bs.size} bytes) to {stg}: {← stage stg bs json (!rest.contains "--no-typecheck") mkCert}"
    return 0
  | _ => IO.eprintln "usage: tests-recheck --probe STAGE SHAPE N [--no-typecheck]"; return 2

/-! ## Nesting depth on an 8 MiB stack -/

/-- The verifier's levels after the middle end on `P` (`Fir.lower` to
`Backend.finish`), with the producer's allocation, frames and order: the
object's size. -/
def anfBack (P : Anf.Program) : Except String Nat := do
  let cfg : Recheck.Config := {}
  let fir ← (Fir.lower P).mapError fun _ => "Fir.lower refused"
  let C := Cfg.lower (Own.immortal fir)
  let l ← (Rt.lower { names := cfg.names } C).mapError fun _ => "Rt.lower refused"
  let (xvp, _) ← (Xv.Select.run l.program).mapError fun _ => "Select.run refused"
  let r ← Xv.Alloc.run cfg.env xvp
  let layouts := Xv.Stacking.produce r.program
  let st0 ← (Xv.Stacking.run r.program layouts l.reps cfg.env).mapError fun _ => "Stacking.run refused"
  let order := X86.Layout.Order.produce (X86.Layout.tunnel st0.program) st0.shape
  let xv ← (Xv.Select.select l.program).mapError fun _ => "select refused"
  (Xv.Validate.program cfg.env xv r.outs).mapError fun _ => "validate refused"
  let xl ← Xv.Alloc.applyProgram xv r.outs
  let (stacked, program, exports) ← (Backend.lay xl
    { l.config (Recheck.defaultProvenance default) with layouts := some layouts, order := some order, env := cfg.env }).mapError
      fun _ => "lay refused"
  let a ← (Backend.finish xl.main stacked program exports (Recheck.defaultProvenance default)).mapError
    fun _ => "finish refused"
  return a.object.size

/-- Nesting-depth inputs, one chain per nesting constructor, at each depth
budget and one level past it, through the levels that recurse on them: Lam
chains through the middle end's replay (`Anf.Pipeline.run`); Anf chains
through the size and depth check (one level past the budget is refused), a
shrink step (which may make a chain shallower, so it may accept one past it)
and, at the budget, the verifier's back end; and an inline walk whose copy is at the copy-depth
budget and one level past it, below a global at the depth budget (the nesting
shape that motivated the walk's depth budget). A line each. -/
def nestingLines : IO (Array String) := do
  let mut lines : Array String := #[]
  let word := fun (r : Except String Unit) => match r with
    | .ok () => "accepted"
    | .error m => s!"refused ({m})"
  for k in ["lam", "app", "appf", "let", "letv", "con", "case", "cases", "proj", "tick"] do
    for (n, pos) in [(Anf.maxLamDepth - 1, "at"), (Anf.maxLamDepth, "past")] do
      let r := (Anf.Pipeline.run {} (lamProgram k n)).map fun _ => ()
      lines := lines.push s!"lam {k} depth {n + 1} ({pos} the depth budget): Pipeline.run {word r}"
  for k in ["tick", "case", "case2", "tcase", "join", "joinb", "bind"] do
    let per := if k == "tcase" then 2 else 1
    let nAt := (Anf.maxDepth - 1) / per
    for (n, pos) in [(nAt, "at"), (nAt + 1, "past")] do
      let P := chainProgram k n 1
      let depth := ((P.global? 0).map fun gd => gd.body.depthUpTo 1000000 1000000).getD 0
      let chk := (Anf.Pipeline.checkGlobalNodes P).map fun _ => ()
      let shr := (Anf.Pipeline.Step.run {} (.shrink [1]) P).map fun _ => ()
      let back := if pos == "at" then s!", back end {word ((anfBack P).map fun _ => ())}" else ""
      lines := lines.push
        s!"anf {k} depth {depth} ({pos} the depth budget): check {word chk}, shrink step {word shr}{back}"
  -- A global of single-alternative cases at the depth budget, inlining a
  -- callee of them that brings the walk just under its depth budget, and just past it
  let spare := Anf.Walk.maxWalkDepth - Anf.maxDepth
  for (c, pos) in [(spare - 8, "at"), (spare + 8, "past")] do
    let callee : Anf.GDef := { key := .dispatch 0, ps := [{}], body := anfChain "case" c (.ret (.var 0)) }
    let gBody := anfChain "case" (Anf.maxDepth - 2) (.bind Anf.freshLet (.call 0 [.var 0]) (.ret (.var 0)))
    let g : Anf.GDef := { key := .dispatch 1, ps := [{}], body := gBody }
    let gs := Src.NatMap.ofList [(0, callee), (1, g)]
    let P : Anf.Program := { globals := gs, size := 2, roots := [1], ctors := anfCtors, known := {} }
    let chk := (Anf.Pipeline.checkGlobalNodes P).map fun _ => ()
    let r := (Anf.Inline.round P [(1, [0])]).map fun _ => ()
    lines := lines.push s!"inline case {Anf.maxDepth - 2} + copy {c} ({pos} the walk-depth budget): \
      check {word chk}, inline walk {word r}"
  return lines

/-- `tests-recheck --stack-8mib`, run by `stackPart` with `LEAN_STACK_SIZE_KB=8192`:
`stack8Lines` and `nestingLines`, a line per input, then a summary line; a
native stack overflow aborts the process instead. -/
def stack8 : IO UInt32 := do
  let lines := (← stack8Lines) ++ (← nestingLines)
  for line in lines do IO.println line
  IO.println s!"stack-8mib: {lines.size} inputs"
  return 0

end IxCCTests.Recheck.Deep
