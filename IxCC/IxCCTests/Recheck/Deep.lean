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
open IxCCTests.IxonV3.Builder (store arrow lambda)
open IxCCTests.Support.Bound (loadBase addList addTree)

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
def deepEnv (env0 : Env) (n : Nat) : Env × Addr := Id.run do
  let b := base env0 3
  let (e, l) := addList b.env b.enumI
  let listI := l.ind
  let nil := l.ctors[0]!
  let cons := l.ctors[1]!
  -- refs: 0 L, 1 cons, 2 nil, 3 c₀
  let (sh, v) := chain (fun t => .app (.app (.ref 1 #[]) (.ref 3 #[])) t) (.ref 2 #[]) n
  let (e, main) := store e ⟨defn (.ref 0 #[]) v, sh, #[listI, cons, nil, b.ctors[0]!], #[]⟩
  return (e, main)

/-- `deepType n`. -/
def deepTypeEnv (env0 : Env) (n : Nat) : Env × Addr := Id.run do
  let b := base env0 3
  let (e, f) := store b.env ⟨defn (arrow (.sort 0) (.sort 0)) (lambda (.sort 0) (.var 0)), #[], #[],
    #[.succ .zero]⟩
  -- refs: 0 E, 1 F, 2 c₀
  let (sh, ty) := chain (fun t => .app (.ref 1 #[]) t) (.ref 0 #[]) n
  let (e, main) := store e ⟨defn ty (.ref 2 #[]), sh, #[b.enumI, f, b.ctors[0]!], #[]⟩
  return (e, main)

/-- `deepApp n`: `main : E := idc (idc (… c₁))`, `n` applications of the identity
function deep. -/
def deepAppEnv (env0 : Env) (n : Nat) : Env × Addr := Id.run do
  let b := base env0 3
  -- refs: 0 E, 1 idc, 2 c₁
  let (sh, v) := chain (fun t => .app (.ref 1 #[]) t) (.ref 2 #[]) n
  let (e, main) := store b.env ⟨defn (.ref 0 #[]) v, sh, #[b.enumI, b.idc, b.ctors[1]!], #[]⟩
  return (e, main)

/-- `deepLet n`: `main : E := let x₀ : E := c₀; let x₁ : E := x₀; …; xₙ`, `n + 1`
nested `let`s. -/
def deepLetEnv (env0 : Env) (n : Nat) : Env × Addr := Id.run do
  let b := base env0 3
  let c : LetContract := { nonDep := false }
  -- refs: 0 E, 1 c₀
  let (sh, v) := chain (fun t => .letE c (.ref 0 #[]) (.var 0) t) (.var 0) n
  let (e, main) := store b.env
    ⟨defn (.ref 0 #[]) (.letE c (.ref 0 #[]) (.ref 1 #[]) v), sh, #[b.enumI, b.ctors[0]!], #[]⟩
  return (e, main)

/-- `many n`: `main : E := fₙ c₀` with `f₀ x := x` and `fᵢ₊₁ x := fᵢ x`, `n + 1`
distinct globals, so that every level holds that many functions. -/
def manyEnv (env0 : Env) (n : Nat) : Env × Addr := Id.run do
  let b := base env0 3
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

/-- `shared n`: `main : E := k t (w t)` (`k (a b : E) : E := a`), where `t`
is `n` applications of `idc` over `c₁` and `w` wraps `n` more around it, all
stored as shares of at most 200: the term's tree is about `2 n` deep, but `t`
is first used shallowly (the certified kernel accepts it; the program is well
typed).
Ingress used to reuse its conversion under `w` without counting its depth
again; it now checks a reused share's height against the depth left there. -/
def sharedEnv (env0 : Env) (n : Nat) : Env × Addr := Id.run do
  let b := base env0 3
  let (e, k) := store b.env
    ⟨defn (arrow enumC (arrow enumC enumC)) (lambda enumC (lambda enumC (.var 1))), #[], #[b.enumI], #[]⟩
  -- refs: 0 E, 1 idc, 2 c₁, 3 k
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
  let (e, main) := store e ⟨defn (.ref 0 #[]) (.app (.app (.ref 3 #[]) top) cur), sh,
    #[b.enumI, b.idc, b.ctors[1]!, k], #[]⟩
  return (e, main)

/-- `main : T`, a balanced tree of `node`s of depth `d` stored as a share DAG
(`d + 1` stored nodes): its Lam term has `2^(d+1) - 1` constructor nodes and
ANF conversion makes it a chain of that many constructor bindings, each used
later, so every shrink round's census reads the rest of the chain at each of
them. -/
def treeEnv (env0 : Env) (d : Nat) : Env × Addr := Id.run do
  let (e, t) := addTree env0
  let tI := t.ind
  let leaf := t.ctors[0]!
  let node := t.ctors[1]!
  -- refs: 0 T, 1 node, 2 leaf
  let mut sh : Array X := #[.app (.app (.ref 1 #[]) (.ref 2 #[])) (.ref 2 #[])]
  for i in [1:d+1] do
    let prev : X := .share (i - 1).toUInt64
    sh := sh.push (.app (.app (.ref 1 #[]) prev) prev)
  let (e, main) := store e ⟨defn (.ref 0 #[]) (.share d.toUInt64), sh, #[tI, node, leaf], #[]⟩
  return (e, main)

/-- A shape's bytes and sidecar. -/
def shape (env0 : Env) (name : String) (n : Nat) : Except String (ByteArray × Lean.Json) :=
  match name with
  | "deep" => let (e, main) := deepEnv env0 n; .ok (bytes e, sidecar [("main", main)])
  | "deepType" => let (e, main) := deepTypeEnv env0 n; .ok (bytes e, sidecar [("main", main)])
  | "wide" => let (e, _, _, main) := ampEnv env0 n 0; .ok (bytes e, sidecar [("main", main)])
  | "tree" => let (e, main) := treeEnv env0 n; .ok (bytes e, sidecar [("main", main)])
  | "deepApp" => let (e, main) := deepAppEnv env0 n; .ok (bytes e, sidecar [("main", main)])
  | "deepLet" => let (e, main) := deepLetEnv env0 n; .ok (bytes e, sidecar [("main", main)])
  | "many" => let (e, main) := manyEnv env0 n; .ok (bytes e, sidecar [("main", main)])
  | _ => .error s!"unknown shape {name}"

/-- The certificate Stage A expects: the table `Table.build` proposes and the
canonical annotation, with no middle-end step. -/
def baseCert (inp : Recheck.Input) (cfg : Recheck.Config) : Except String Recheck.Cert := do
  let P := inp.program
  let (table0, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let tc := Src.Table.TableCert.ofTable table0
  let table ← Src.Table.ofCert cfg.table P tc
  let ann ← inp.kernel.annotateChecked { P with table }
  return { table := tc, relevance := ann }

/-- A shape's environment and root. -/
def shapeEnv (env0 : Env) (name : String) (n : Nat) : Except String (Env × Addr) :=
  match name with
  | "deep" => .ok (deepEnv env0 n)
  | "deepType" => .ok (deepTypeEnv env0 n)
  | "wide" => let (e, _, _, main) := ampEnv env0 n 0; .ok (e, main)
  | "tree" => .ok (treeEnv env0 n)
  | "deepApp" => .ok (deepAppEnv env0 n)
  | "deepLet" => .ok (deepLetEnv env0 n)
  | "many" => .ok (manyEnv env0 n)
  | _ => .error s!"unknown shape {name}"

/-- A certificate for a deep instance made without the annotator, as a
claimant could make it: the annotation of a shallow instance (`n₀` deep)
carried over by address, with the root's value tags repeated to its depth.
The constants other than the root are the same in both, and each level of
the chain carries the same tags. This is what a claimant can hand a
program-level verifier, which runs no annotator. -/
def transplantedCert (env0 : Env) (name : String) (n n₀ : Nat) (inp : Recheck.Input) (cfg : Recheck.Config) :
    Except String Recheck.Cert := do
  let (e₀, main₀) ← shapeEnv env0 name n₀
  let inp₀ ← (Recheck.ingress (bytes e₀) (sidecar [("main", main₀)]) []).mapError (·.render)
  let cfg₀ := Recheck.Config.forInput {} inp₀
  let base₀ ← baseCert inp₀ cfg₀
  -- the tags one more level adds, from an instance one level deeper
  let (e₁, main₁) ← shapeEnv env0 name (n₀ + 1)
  let inp₁ ← (Recheck.ingress (bytes e₁) (sidecar [("main", main₁)]) []).mapError (·.render)
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
def stage (name : String) (bs : ByteArray) (json : Lean.Json)
    (mkCert : Recheck.Input → Recheck.Config → Except String Recheck.Cert := baseCert) : IO String := do
  let inp ← match Recheck.ingress bs json [] with
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
      { env := inp.env.root, roleTable := inp.env.bindingAddress
        target := (P.roots.head?.map (·.1)).getD default, policy := .immortal
        abiArity := 0, elfHash := Address.blake3Pure (ByteArray.mk #[0]) }
    let text := base.toText
    let sip : Ring0.Ring0Sip := { cfg, claim, certText := text, driver }
    let rs := [("verifyBytes", CompileClaim.verifyBytes cfg bs json claim text),
      ("checkClaim", (CompileClaim.checkClaim cfg bs json claim text).isOk),
      ("Ring0Sip.verifyBytes", sip.verifyBytes bs json),
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
  let (e, main) := treeEnv (← loadBase) d
  let bs := bytes e
  let json := sidecar [("main", main)]
  let inp ← IO.ofExcept ((Recheck.ingress bs json []).mapError (·.render))
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

/-! ## Wide inputs, from bytes -/

/-- A wide input as bytes, sidecar and certificate text: `tree N` (a constructor
tree of depth `N` as a share DAG: its annotation holds one tag list of about
`2^(N+2)` entries), `many N` (`N + 1` globals: as many table and annotation
entries), `roots N` (a sidecar naming one root `N` times), `equations N` (a
sidecar with `N` empty equation entries), or `tags N` (`tree 4` with a
certificate whose annotation has one more term of `N` tags). The honest
certificate is Stage A's. -/
def wideInput (kind : String) (n : Nat) : IO (ByteArray × Lean.Json × String) := do
  let honest := fun (e : Env) (main : Addr) (json : Lean.Json) => do
    let bs := bytes e
    let inp ← IO.ofExcept ((Recheck.ingress bs json []).mapError (·.render))
    let cert ← IO.ofExcept (baseCert inp (Recheck.Config.forInput {} inp))
    let _ := main
    pure (bs, json, cert)
  match kind with
  | "tree" | "many" =>
    let env0 ← loadBase
    let (e, main) := if kind == "tree" then treeEnv env0 n else manyEnv env0 n
    let json := sidecar [("main", main)]
    let (bs, json, cert) ← honest e main json
    return (bs, json, cert.toText)
  | "roots" =>
    let (e, main) := deepAppEnv (← loadBase) 4
    let json := sidecar ((List.range n).map fun _ => ("main", main))
    return (bytes e, json, "{}")
  | "equations" =>
    let (e, main) := deepAppEnv (← loadBase) 4
    let json := Lean.Json.mkObj [("format", .str "ixcc/k1-equations/1"),
      ("roots", .arr #[Lean.Json.mkObj [("name", .str "main"), ("address", .str (toString main))]]),
      ("equations", .arr (Array.replicate n (Lean.Json.mkObj [])))]
    return (bytes e, json, "{}")
  | _ =>
    let (e, main) := treeEnv (← loadBase) 4
    let (bs, json, cert) ← honest e main (sidecar [("main", main)])
    let key := (cert.relevance.nodes.head?.map (·.1)).getD (.value 0)
    let wide : Recheck.Cert := { cert with relevance := { cert.relevance with
      nodes := cert.relevance.nodes ++ [(key, List.replicate n (.arg .rel))] } }
    return (bs, json, wide.toText)

/-- `tests-recheck --write-wide DIR KIND N`: `wideInput KIND N` as
`KIND-N.ixe`, `KIND-N.equations.json` and `KIND-N.cert`. -/
def writeWide (dir : System.FilePath) (kind : String) (n : Nat) : IO Unit := do
  let (bs, json, text) ← wideInput kind n
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / s!"{kind}-{n}.ixe") bs
  IO.FS.writeFile (dir / s!"{kind}-{n}.equations.json") json.compress
  IO.FS.writeFile (dir / s!"{kind}-{n}.cert") text
  IO.println s!"{kind}-{n}: {bs.size} bytes, sidecar {json.compress.utf8ByteSize} bytes, certificate {text.utf8ByteSize} bytes"

/-- With `IXCC_STACK_TRACE` set, name the input about to run on standard error
(flushed), so a run that overflows its stack shows which input did. -/
def traceInput (label : String) : IO Unit := do
  if (← IO.getEnv "IXCC_STACK_TRACE").isSome then
    IO.eprintln s!"input: {label}"
    (← IO.getStderr).flush

/-- The byte-level verifiers on one input (`verifyBytes`, `checkClaim`,
`Ring0Sip.verifyBytes`, with a claim for the input's first root), and an in-process `check-cert`: the outcomes as a line. -/
def bytesEntries (dir : System.FilePath) (label : String) (bs : ByteArray) (json : Lean.Json)
    (text : String) : IO String := do
  traceInput label
  let env ← IO.ofExcept (V3.decodeAnonymousEnv bs)
  let main := match Src.Hints.ofK1Json json with
    | .ok h => (h.roots[0]?.map (·.1)).getD default
    | .error _ => default
  let claim : CompileClaim := { env := env.root, roleTable := env.bindingAddress, target := main
                                policy := .immortal, abiArity := 0
                                elfHash := Address.blake3Pure (ByteArray.mk #[0]) }
  let word := fun (b : Bool) => if b then "accepted" else "refused"
  let cfg : Recheck.Config := {}
  let sip : Ring0.Ring0Sip := { cfg, claim, certText := text, driver }
  let outs := #[s!"verifyBytes {word (CompileClaim.verifyBytes cfg bs json claim text)}",
    s!"checkClaim {word (CompileClaim.checkClaim cfg bs json claim text).isOk}",
    s!"Ring0Sip.verifyBytes {word (sip.verifyBytes bs json)}"]
  IO.FS.writeBinFile (dir / "c.ixe") bs
  IO.FS.writeFile (dir / "c.json") json.compress
  IO.FS.writeFile (dir / "cert.json") text
  let o ← IO.ofExcept (IxCC.Cli.parse ["check-cert", (dir / "c.ixe").toString, "--equations",
    (dir / "c.json").toString, "--cert", (dir / "cert.json").toString])
  let cc ← match ← (IxCC.Cli.execute o).run with
    | .ok () => pure "accepted"
    | .error e => pure s!"refused ({e.stage.name}: {e.code})"
  return s!"{label}: {", ".intercalate outs.toList}, check-cert {cc}"

/-- `tests-recheck --wide KIND N`: `bytesEntries` on `wideInput KIND N`. -/
def probeWide (kind : String) (n : Nat) : IO UInt32 := IO.FS.withTempDir fun dir => do
  let (bs, json, text) ← wideInput kind n
  IO.println (← bytesEntries dir s!"{kind} {n} (certificate {text.utf8ByteSize} bytes)" bs json text)
  return 0

/-- `tests-recheck --size-diag SHAPE N`: the honest allocation certificate of a
shape against `Xv.Validate.sizeOk`, component by component, per function. -/
def sizeDiag (name : String) (n : Nat) : IO UInt32 := do
  let (e, main) ← IO.ofExcept (shapeEnv (← loadBase) name n)
  let inp ← IO.ofExcept ((Recheck.ingress (bytes e) (sidecar [("main", main)]) []).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let cert ← IO.ofExcept ((Recheck.produce cfg inp).mapError (·.render))
  let f ← IO.ofExcept ((Recheck.runLir cfg inp.program cert).mapError (·.render))
  let xv ← IO.ofExcept ((Xv.Select.select f.lowered.program).mapError fun _ => "select")
  for (fn, o) in xv.funcs.toList.zip cert.alloc do
    let blocks := fn.blocks.toList
    let m := Xv.Validate.regMentions fn
    let per := (blocks.zip o.blocks).map fun (b, bo) =>
      (bo.locs.length == b.body.size, bo.termLocs.length == (Xv.Term.operands b.term).length,
       (b.body.toList.zip bo.locs).all (fun (i, ls) => ls.length == (Xv.Inst.operands i).length),
       Xv.Validate.maxRun bo.edits 0 0 0, Xv.Validate.factsSorted bo.cert .leaf)
    IO.println s!"fn: blocks {blocks.length}/{o.blocks.length} slots {o.numSlots} mentions {m} sizeOk {Xv.Validate.sizeOk fn o}"
    IO.println s!"  per block (locs, termLocs, operand counts, edits at one position, facts sorted): {per}"
  return 0

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
    (mkCert : Recheck.Input → Recheck.Config → Except String Recheck.Cert) :
    IO String := do
  traceInput label
  let env ← IO.ofExcept (V3.decodeAnonymousEnv bs)
  let claim : CompileClaim := { env := env.root, roleTable := env.bindingAddress, target := main
                                policy := .immortal, abiArity := 0
                                elfHash := Address.blake3Pure (ByteArray.mk #[0]) }
  let (inp?, cert) ← match Recheck.ingress bs json [] with
    | .error e => pure (Sum.inl e.render, ({} : Recheck.Cert))
    | .ok inp => match mkCert inp (Recheck.Config.forInput {} inp) with
      | .ok c => pure (Sum.inr inp, c)
      | .error m => throw (IO.userError s!"{label}: no certificate: {m}")
  let text := cert.toText
  let word := fun (b : Bool) => if b then "accepted" else "refused"
  let cfg := match inp? with | .inr inp => Recheck.Config.forInput {} inp | .inl _ => {}
  let sip : Ring0.Ring0Sip := { cfg, claim, certText := text, driver }
  let bytesLevel := [s!"verifyBytes {word (CompileClaim.verifyBytes cfg bs json claim text)}",
    s!"checkClaim {word (CompileClaim.checkClaim cfg bs json claim text).isOk}",
    s!"Ring0Sip.verifyBytes {word (sip.verifyBytes bs json)}"]
  let rest ← match inp? with
    | .inl e => pure [s!"ingress refused ({e})"]
    | .inr inp =>
      let P := inp.program
      let run := match Recheck.run cfg P cert with
        | .ok _ => "accepted"
        | .error e => s!"refused ({e.stage.name}: {e.code}: {e.message.take 60})"
      IO.FS.writeBinFile (dir / "c.ixe") bs
      IO.FS.writeFile (dir / "c.json") json.pretty
      let cc ← match ← checkCert dir cert [] with
        | .ok () => pure "accepted"
        | .error e => pure s!"refused ({e.stage.name}: {e.code})"
      pure [s!"verifyProgram {word (CompileClaim.verifyProgram cfg P claim text)}",
        s!"checkClaimProgram {word (CompileClaim.checkClaimProgram cfg P claim text).isOk}",
        s!"Ring0Sip.verifyProgram {word (sip.verifyProgram P)}", s!"Recheck.run {run}", s!"check-cert {cc}"]
  return s!"{label} ({bs.size} bytes): {", ".intercalate (bytesLevel ++ rest)}"

/-- The longest chain of shape `name` that ingress accepts: the largest `n`
whose terms are within `Src.Ingress.depthBudget` (the kernel accepts every
chain; IxCC's conversion refuses the ones past the budget). -/
def deepest (env0 : Env) (name : String) : IO Nat := do
  let ok := fun (n : Nat) => match shapeEnv env0 name n with
    | .ok (e, main) => (Recheck.ingress (bytes e) (sidecar [("main", main)]) []).isOk
    | .error _ => false
  let mut lo := 1
  let mut hi := Src.Ingress.depthBudget + 1
  if !ok lo || ok hi then throw (IO.userError s!"{name}: the depth budget does not bound the chain")
  for _ in [0:32] do
    if hi - lo ≤ 1 then break
    let mid := (lo + hi) / 2
    if ok mid then lo := mid else hi := mid
  return lo

/-- Wide inputs from bytes through every byte-level entry point (`bytesEntries`):
the constructor tree whose honest annotation holds a 262,142-entry tag list
(`tree 16`; the derived list equality took a frame per entry), a certificate
with a 300,000-entry tag list, sidecars with 300,000 roots and 300,000
equation entries, and 4,001 globals. A line each. -/
def widthLines : IO (Array String) := IO.FS.withTempDir fun dir => do
  let mut lines : Array String := #[]
  for (kind, n) in [("tree", 16), ("tags", 300000), ("roots", 300000), ("equations", 300000), ("many", 4000)] do
    let (bs, json, text) ← wideInput kind n
    lines := lines.push (← bytesEntries dir s!"width {kind} {n}" bs json text)
  return lines

/-- Part of the 8 MiB child (`stack8`): every verifier entry point on the
programs that once overflowed an 8 MiB stack and on generated deep and wide
inputs at and past each budget, every one through the certified kernel's
acceptance. A line per input. -/
def stack8Lines : IO (Array String) := IO.FS.withTempDir fun dir => do
  let env0 ← loadBase
  let mut lines : Array String := #[]
  -- The amplifier inputs (`amp-12-11` and `amp-13-13` crashed an 8 MiB checker), the
  -- largest inline the copy budget allows through to the end of the backend,
  -- and one just past it
  for (dF, dG, full) in [(12, 11, false), (13, 13, false), (2, 7, true), (3, 7, true)] do
    let (bs, json, _, _, main, hostile) ← ampCase dF dG
    let mk := fun (inp : Recheck.Input) (cfg : Recheck.Config) =>
      .ok (if full then (withBackend cfg inp.program hostile).toOption.getD hostile else hostile)
    lines := lines.push (← entryPoints dir s!"amp-{dF}-{dG} inline" bs json main mk)
    if !full then
      lines := lines.push (← entryPoints dir s!"amp-{dF}-{dG} base" bs json main
        fun _ _ => .ok { hostile with mid := {} })
  -- wide: the Lam global at the P1 budget and past it
  for d in [11, 13] do
    let (e, _, _, main) := ampEnv env0 d 0
    lines := lines.push (← entryPoints dir s!"wide {d}" (bytes e) (sidecar [("main", main)]) main
      fun inp cfg => do
        let b ← baseCert inp cfg
        return (withBackend cfg inp.program b).toOption.getD b)
  -- deep: at the ingress depth budget and past it, with a certificate carried
  -- over from a shallow instance
  for name in ["deep", "deepApp", "deepLet", "deepType"] do
    let n ← deepest env0 name
    for (m, pos) in [(n, "at"), (n + 1, "past")] do
      let (e, main) ← IO.ofExcept (shapeEnv env0 name m)
      lines := lines.push (← entryPoints dir s!"{name} {m} ({pos} the depth budget)" (bytes e)
        (sidecar [("main", main)]) main fun inp cfg => do
          let c ← transplantedCert env0 name m 200 inp cfg
          return (withBackend cfg inp.program c).toOption.getD c)
  -- a share converted once and reused deeper: ingress checks its height
  -- against the depth left at each use
  let (e, main) := sharedEnv env0 1200
  lines := lines.push (← entryPoints dir "shared 1200 + 1200 (past the depth budget, shares reused)" (bytes e)
    (sidecar [("main", main)]) main fun _ _ => .ok {})
  return lines

/-- The parent of `stack8` and `stack2`: the same executable with
`LEAN_STACK_SIZE_KB=8192` and with 2048 (the stack of the thread that runs a
Lean `main`; `ulimit -s` does not change it), each of which must exit
normally with a line per input; the 2 MiB run's lines must be the 8 MiB
run's. -/
def stackPart (a : Assert) : IO (Array String) := do
  let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["--stack-8mib"]
                                env := #[("LEAN_STACK_SIZE_KB", some "8192")] }
  let lines := (out.stdout.splitOn "\n").filter (!·.isEmpty)
  -- the certificate-driven inputs on a quarter of that stack
  let small ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["--stack-2mib"]
                                  env := #[("LEAN_STACK_SIZE_KB", some "2048")] }
  expect a (small.exitCode == 0)
    s!"tests-recheck --stack-2mib exited with {small.exitCode} on a 2 MiB stack: {small.stderr}"
  let smallLines := (small.stdout.splitOn "\n").filter (!·.isEmpty)
  expect a (smallLines.getLast?.any (·.startsWith "stack-2mib:")) "tests-recheck --stack-2mib: no summary line"
  expect a (smallLines.dropLast.all lines.contains) "the 2 MiB run's lines are not the 8 MiB run's"
  expect a (smallLines.length > 20) s!"tests-recheck --stack-2mib: {smallLines.length} lines"
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
  let wide := lines.filter (·.startsWith "width ")
  let alloc := lines.filter (·.startsWith "alloc ")
  expect a (alloc.length == 8) s!"allocation inputs: {alloc.length} lines"
  for l in alloc do
    expect a (if inL l "(past " then inL l "check-cert refused (alloc: alloc.shape)"
      else if inL l "(within " then inL l "check-cert refused (alloc: alloc.edge)"
      else !inL l "alloc.shape" && !inL l "cert.parse") s!"allocation cap: {l}"
  expect a (alloc.any fun l => inL l "alloc slots" && inL l "(at " && inL l "check-cert accepted")
    "the last function at its frame-slot cap is not accepted"
  -- the front and middle certificates' caps: at the cap accepted, past it refused by the cap
  let caps := lines.filter (·.startsWith "cap ")
  expect a (caps.length == 7) s!"certificate cap inputs: {caps.length} lines"
  for l in caps do
    let ok := if inL l "(at " then inL l "check-cert accepted" && inL l "Recheck.run accepted"
      else if inL l "cap table" then inL l "names a constant outside the program, or one twice"
      else if inL l "cap relevance" then inL l "names a constant outside the program, or a runtime term twice"
      else if inL l "cap inline" then
        inL l "check-cert refused (anf: anf.replay)" && inL l "a round lists more callers than the program has globals"
      else inL l "check-cert refused (anf: anf.replay)" && inL l "lists more globals than the program has"
    expect a ok s!"certificate cap: {l}"
  expect a (wide.length == 5) s!"wide inputs: {wide.length} lines"
  expect a (wide.any fun l => inL l "width tree 16" && inL l "check-cert refused (anf")
    "the 262,142-tag annotation is not refused normally by check-cert"
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

/-- `tests-recheck --probe STAGE SHAPE N [--transplant | --empty]`. -/
def probe (args : List String) : IO UInt32 := do
  let env0 ← loadBase
  match args with
  | stg :: shp :: n :: rest =>
    let (bs, json) ← IO.ofExcept (shape env0 shp n.toNat!)
    let mkCert := if rest.contains "--transplant" then transplantedCert env0 shp n.toNat! 200
      else if rest.contains "--empty" then fun _ _ => .ok {} else baseCert
    IO.println s!"{shp} {n} ({bs.size} bytes) to {stg}: {← stage stg bs json mkCert}"
    return 0
  | _ => IO.eprintln "usage: tests-recheck --probe STAGE SHAPE N [--transplant | --empty]"; return 2

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
      traceInput s!"lam {k} {n}"
      let r := (Anf.Pipeline.run {} (lamProgram k n)).map fun _ => ()
      lines := lines.push s!"lam {k} depth {n + 1} ({pos} the depth budget): Pipeline.run {word r}"
  for k in ["tick", "case", "case2", "tcase", "join", "joinb", "bind"] do
    let per := if k == "tcase" then 2 else 1
    let nAt := (Anf.maxDepth - 1) / per
    for (n, pos) in [(nAt, "at"), (nAt + 1, "past")] do
      traceInput s!"anf {k} {n}"
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
    traceInput s!"inline case {c}"
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

/-- `tree 9` with its producer's whole certificate (accepted by every
verifier but for the claim's hash), as bytes, sidecar and certificate. -/
def honestTree9 : IO (ByteArray × Lean.Json × Recheck.Cert) := do
  let (e, main) := treeEnv (← loadBase) 9
  let bs := bytes e
  let json := sidecar [("main", main)]
  let inp ← IO.ofExcept ((Recheck.ingress bs json []).mapError (·.render))
  let cert ← IO.ofExcept ((Recheck.produce (Recheck.Config.forInput {} inp) inp).mapError (·.render))
  return (bs, json, cert)

/-- `honestTree9` with an allocation changed: `selfmoves N` puts `N` moves of a
location to itself before the first instruction of the last block of the
first function that has one, `factregs N` adds registers `0 … N − 1` to the
first fact of the last block of the first function that has one, `slots N`
sets the last function's frame slots to `N`. -/
def allocInput (kind : String) (n : Nat) : IO (ByteArray × Lean.Json × String) := do
  let (bs, json, cert) ← honestTree9
  if kind == "slots" then
    let some o := cert.alloc.getLast? | throw (IO.userError "tree 9: no allocation")
    let cert' : Recheck.Cert := { cert with alloc := cert.alloc.dropLast ++ [{ o with numSlots := n }] }
    return (bs, json, cert'.toText)
  let some o := cert.alloc.head? | throw (IO.userError "tree 9: no allocation")
  let lastWith := fun (p : Xv.Alloc.BlockOut → Bool) =>
    ((o.blocks.zipIdx.filter fun (bo, _) => p bo).getLast?.map (·.2)).getD 0
  let o' : Xv.Alloc.Output := match kind with
    | "selfmoves" =>
      let k := lastWith fun bo => !bo.locs.isEmpty
      { o with blocks := o.blocks.zipIdx.map fun (bo, i) =>
          if i == k then
            let l := ((bo.locs.head?.bind List.head?)).getD (.slot 0)
            { bo with edits := List.replicate n (0, .move l l) ++ bo.edits }
          else bo }
    | "factregs" =>
      let k := lastWith fun bo => !bo.cert.isEmpty
      { o with blocks := o.blocks.zipIdx.map fun (bo, i) =>
          if i == k then
            match bo.cert with
            | (l, vs) :: rest => { bo with cert := (l, (List.range n ++ vs.map (· + n))) :: rest }
            | [] => bo
          else bo }
    | _ => { o with numSlots := n }
  let cert' : Recheck.Cert := { cert with alloc := o' :: cert.alloc.tail }
  return (bs, json, cert'.toText)

/-- The first and last functions of `honestTree9` as Xv: what
`Xv.Validate.sizeOk` derives its caps from. -/
def tree9Funcs : IO (Xv.Func Lir.VReg × Xv.Func Lir.VReg) := do
  let (bs, json, cert) ← honestTree9
  let inp ← IO.ofExcept ((Recheck.ingress bs json []).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let f ← IO.ofExcept ((Recheck.runLir cfg inp.program cert).mapError (·.render))
  let xv ← IO.ofExcept ((Xv.Select.select f.lowered.program).mapError fun _ => "select")
  let some fn := xv.funcs.toList.head? | throw (IO.userError "tree 9: no function")
  let some last := xv.funcs.toList.getLast? | throw (IO.userError "tree 9: no function")
  return (fn, last)

/-- The allocation certificate's caps from bytes (`allocInput`), through every
byte-level entry point: each component at its cap in `tree 9`'s first
function (the frame slots in its last, whose cap is below the decoder's) and
one past it, and the two inputs that once overflowed or outlasted the
validator: 100,000 moves of a location to itself at one position and a fact
of 100,000 registers. A line each. -/
def allocLines : IO (Array String) := IO.FS.withTempDir fun dir => do
  let (fn, last) ← tree9Funcs
  let r := Xv.Validate.regMentions fn
  let (_, _, cert) ← honestTree9
  let some o := cert.alloc.head? | throw (IO.userError "tree 9: no allocation")
  let lastIdx := fun (p : Xv.Alloc.BlockOut → Bool) =>
    ((o.blocks.zipIdx.filter fun (bo, _) => p bo).getLast?.map (·.2)).getD 0
  -- `allocInput`'s blocks: self-moves at position 0 of one, registers in the first fact of another
  let kMoves := lastIdx fun bo => !bo.locs.isEmpty
  let kFacts := lastIdx fun bo => !bo.cert.isEmpty
  let at0 := (((o.blocks[kMoves]?).map (·.edits)).getD [] |>.filter (·.1 == 0)).length
  let movesAt := (fn.blocks[kMoves]?.map (Xv.Validate.editsAllowed · 0)).getD 0 - at0
  let factAt := Xv.Validate.factFactor * (r + 1) - ((o.blocks[kFacts]?).map (Xv.Validate.factEntries ·.cert)).getD 0
  let rLast := Xv.Validate.regMentions last
  let cases : List (String × Nat × String) := [
    ("selfmoves", movesAt, "at"), ("selfmoves", movesAt + 1, "past"),
    ("selfmoves", 100000, if 100000 > movesAt then "past" else "within"),
    ("factregs", factAt, "at"), ("factregs", factAt + 1, "past"),
    ("factregs", 100000, if 100000 > factAt then "past" else "within"),
    ("slots", rLast + Xv.Validate.slotSlack, "at"), ("slots", rLast + Xv.Validate.slotSlack + 1, "past")]
  let mut lines : Array String := #[]
  for (kind, n, pos) in cases do
    let (bs, json, text) ← allocInput kind n
    lines := lines.push (← bytesEntries dir s!"alloc {kind} {n} ({pos} the cap)" bs json text)
  return lines

/-- The front and middle certificates' caps from bytes, on `tree 9` and its
honest certificate: a table column naming a constant twice, one naming a
constant past the program, an annotation naming a runtime term twice, and an
inline round and a shrink step listing as many globals as the program has
(at the cap: steps that change nothing, accepted) and one more (past it). A
line each: `bytesEntries`, then `Recheck.run`'s outcome. -/
def capLines : IO (Array String) := IO.FS.withTempDir fun dir => do
  let (bs, json, cert) ← honestTree9
  let inp ← IO.ofExcept ((Recheck.ingress bs json []).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let f ← IO.ofExcept ((Recheck.runLir cfg inp.program cert).mapError (·.render))
  let size := inp.program.size
  let g := f.anf.size
  let mid := fun (s : Anf.Pipeline.Step) =>
    { cert with mid := { cert.mid with steps := cert.mid.steps ++ [s] } }
  let cases : List (String × Recheck.Cert) := [
    ("table inline column naming constant 0 twice (past the cap)",
      { cert with table := { cert.table with inline := [0, 0] } }),
    (s!"table recKind column naming constant {size} of {size} (past the cap)",
      { cert with table := { cert.table with recKind := [size] } }),
    ("relevance naming its first runtime term twice (past the cap)",
      { cert with relevance := { cert.relevance with
          nodes := cert.relevance.nodes.take 1 ++ cert.relevance.nodes } }),
    (s!"inline round of {g} callers for {g} globals (at the cap)", mid (.inline ((List.range g).map (·, [])))),
    (s!"inline round of {g + 1} callers for {g} globals (past the cap)",
      mid (.inline ((List.range (g + 1)).map (·, [])))),
    (s!"shrink step of {g} round counts for {g} globals (at the cap)", mid (.shrink (List.replicate g 0))),
    (s!"shrink step of {g + 1} round counts for {g} globals (past the cap)",
      mid (.shrink (List.replicate (g + 1) 0)))]
  let mut lines : Array String := #[]
  for (label, c) in cases do
    let run := match Recheck.run cfg inp.program c with
      | .ok _ => "accepted"
      | .error e => s!"refused ({e.stage.name}: {e.code}: {e.message.take 96})"
    lines := lines.push s!"{← bytesEntries dir s!"cap {label}" bs json c.toText}, Recheck.run {run}"
  return lines

/-- `tests-recheck --write-alloc DIR KIND N`: `allocInput KIND N` as files, for
timing native `ixcc check-cert` on it. -/
def writeAlloc (dir : System.FilePath) (kind : String) (n : Nat) : IO Unit := do
  let (bs, json, text) ← allocInput kind n
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / s!"alloc-{kind}-{n}.ixe") bs
  IO.FS.writeFile (dir / s!"alloc-{kind}-{n}.equations.json") json.compress
  IO.FS.writeFile (dir / s!"alloc-{kind}-{n}.cert") text
  IO.println s!"alloc-{kind}-{n}: {bs.size} bytes, certificate {text.utf8ByteSize} bytes"

/-- `tests-recheck --stack-8mib`, run by `stackPart` with `LEAN_STACK_SIZE_KB=8192`:
`stack8Lines`, `nestingLines`, `widthLines`, `allocLines` and `capLines`, a line per input, then a
summary line; a native stack overflow aborts the process instead. -/
def stack8 : IO UInt32 := do
  let lines := (← stack8Lines) ++ (← nestingLines) ++ (← widthLines) ++ (← allocLines) ++ (← capLines)
  for line in lines do IO.println line
  IO.println s!"stack-8mib: {lines.size} inputs"
  return 0

/-- `tests-recheck --stack-2mib`, run by `stackPart` with `LEAN_STACK_SIZE_KB=2048`:
the inputs whose size the certificate or the sidecar sets (`widthLines`,
`allocLines`, `capLines`), on a quarter of `stack8`'s stack. The program-shaped
inputs of `stack8Lines` and `nestingLines` need the 8 MiB stack the
middle-end budgets were sized for. -/
def stack2 : IO UInt32 := do
  let lines := (← widthLines) ++ (← allocLines) ++ (← capLines)
  for line in lines do IO.println line
  IO.println s!"stack-2mib: {lines.size} inputs"
  return 0

end IxCCTests.Recheck.Deep
