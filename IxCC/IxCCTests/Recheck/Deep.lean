import IxCCTests.Recheck.Hostile

/-! # Deep and wide inputs, for the verifiers' native stack

The verifier's traversals recurse natively, so the depth of what they walk
must stay within what a thread's stack holds. This module generates the
shapes that stress that, as Ixon v4 bytes:

* `deep n`: `main : L := cons c₀ (cons c₀ (… nil))`, `n` constructor
  applications deep (stored as a chain of `share`s, each at most 200 deep, so
  the decoder accepts it). The source, Lam and Anf terms are all about `n`
  deep.
* `wide d`: R1's amplifier with `g = f`: `f x` is a balanced `k`-tree of depth
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
`probeAmp` and `probeWalk` do the same for R1's amplifier and for one walk.
`stack8` is the regression test: every verifier entry point on R1's crashing
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

/-- `tests-recheck --write-amp-shrink DIR DF DG`: R1's amplifier `amp-DF-DG`
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

/-- `tests-recheck --probe-amp DF DG [STAGE]`: R1's amplifier with its single
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
every verifier entry point on R1's crashing inputs and on generated deep and
wide inputs at and past each budget, typing on and off. A line per input, then
a summary line; a native stack overflow aborts the process instead. -/
def stack8 : IO UInt32 := IO.FS.withTempDir fun dir => do
  let mut lines : Array String := #[]
  -- R1's inputs (`amp-12-11` and `amp-13-13` crashed an 8 MiB checker), the
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
  for line in lines do IO.println line
  IO.println s!"stack-8mib: {lines.size} inputs through every verifier entry point"
  return 0

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
  -- R1's inputs are refused by the budgets, not by a crash
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
  return lines.toArray

/-- `tests-recheck --probe STAGE SHAPE N [--no-typecheck] [--transplant]`. -/
def probe (args : List String) : IO UInt32 := do
  match args with
  | stg :: shp :: n :: rest =>
    let (bs, json) ← IO.ofExcept (shape shp n.toNat!)
    let mkCert := if rest.contains "--transplant" then transplantedCert shp n.toNat! 200 else baseCert
    IO.println s!"{shp} {n} ({bs.size} bytes) to {stg}: {← stage stg bs json (!rest.contains "--no-typecheck") mkCert}"
    return 0
  | _ => IO.eprintln "usage: tests-recheck --probe STAGE SHAPE N [--no-typecheck]"; return 2

end IxCCTests.Recheck.Deep
