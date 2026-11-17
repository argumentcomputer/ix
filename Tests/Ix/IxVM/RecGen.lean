import Ix.Ixon
import Ix.Claim
import Ix.ClaimContext
import Ix.AssumptionTree
import Ix.IxVM.ClaimHarness
import IxC.Kernel.Ixon.Reader
import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.RecGenTerms
import Tests.Ix.IxVM.RecGenDefs

/-!
# The native recursor generator against stored recursor records

A stored recursor of a native (one type, not nested) inductive family is accepted by
regenerating its type and rules inside the program (`KernelCheck::nat_rec_check`) and
comparing them with the record. The rules are not typed, so the generator and the
comparison carry the soundness of every iota step at such a family. This suite runs that
check on real records and on altered ones, through the IxVM program in circuit-verdict
mode (`Tests.Ix.IxVM.Harness`).

One record is checked per claim: a `check` claim on the recursor record whose assumptions
are every record its reference table names, under an assumed binding. The claim walk then
runs `KernelCheck::check_const` on the recursor record alone; the records it loads (the
family's block, the constants of its type) are hash-checked as always but not themselves
checked. The witness holds the records within a few reference steps of the target and is
widened when the program asks for a record it lacks.

`ixvm-recgen` (manual) reads its work from the environment:

* `IX_RECGEN_MODE`: `honest` (every standalone recursor record of an `.ixe` file, as
  stored), `mutate` (single-edit variants of a stratified sample, each of which must be
  rejected), `synthetic` (the fixture families of `Tests.Ix.IxVM.RecGenDefs`: stored and
  kernel-generated recursors, their edits, a dead `let` in a rule, a deep reflexive field),
  `kernelgen` (the certified kernel's generated recursor for corpus families with a small
  dependency closure, as a record of its own), `classify` (the accepted edits a `mutate` run
  saved, re-read and compared with their controls);
* `IX_RECGEN_IXE`: the compiled corpus;
* `IX_RECGEN_OUT`: a directory for the per-record tables and the summaries;
* `IX_RECGEN_LIMIT`, `IX_RECGEN_PER_TAG`, `IX_RECGEN_SEED`, `IX_RECGEN_WORKERS`: sample size,
  records taken per stratum, sample offset, parallel host processes;
* `IX_RECGEN_TAG`, `IX_RECGEN_NAME`: keep one stratum, or the records whose name contains one
  of the given strings; `IX_RECGEN_LABEL` prefixes the output files.

An accepted edit is not by itself a wrong recursor: the comparison expands a `let` on either
side and never reads its type annotation, so an edit inside a `let` that expansion erases
leaves the same term. Each accepted edit is therefore compared with its control once every
`let` is expanded (`XRec.zetaEq`); a run fails only on one that still differs.
-/

namespace Tests.Ix.IxVM.RecGen

open IxVM.ClaimHarness

abbrev E := Ixon.Expr

def envNat (name : String) (dflt : Nat) : IO Nat := do
  return ((← IO.getEnv name).bind String.toNat?).getD dflt

def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-! ## Walks over a record's sharing table -/

/-- Some node of `e` satisfies `p` (sharing entries memoized). -/
partial def anyNode (sh : Array E) (p : E → Bool) (e : E) :
    StateM (Std.HashMap Nat Bool) Bool := do
  match e with
  | .share i =>
    match (← get)[i.toNat]? with
    | some b => return b
    | none =>
      modify (·.insert i.toNat false)
      let b ← match sh[i.toNat]? with
        | some e' => anyNode sh p e'
        | none => pure false
      modify (·.insert i.toNat b)
      return b
  | _ =>
    if p e then return true
    match e with
    | .app f a => if (← anyNode sh p f) then return true else anyNode sh p a
    | .lam t b => if (← anyNode sh p t) then return true else anyNode sh p b
    | .all t b => if (← anyNode sh p t) then return true else anyNode sh p b
    | .letE _ _ t v b =>
      if (← anyNode sh p t) then return true
      if (← anyNode sh p v) then return true
      anyNode sh p b
    | .prj _ _ x => anyNode sh p x
    | _ => return false

def anyIn (sh : Array E) (p : E → Bool) (e : E) : Bool :=
  Id.run ((anyNode sh p e).run' {})

def isLet : E → Bool
  | .letE .. => true
  | _ => false

def isRecur : E → Bool
  | .recur .. => true
  | _ => false

/-! ## The family a recursor eliminates, and its shape -/

structure Parent where
  projAddr : Address
  blockAddr : Address
  block : Ixon.Constant
  idx : Nat
  ind : Ixon.Inductive

/-- The inductive at the head of the recursor's major premise, read with the record's
own counts. -/
def parentOf (env : Ixon.Env) (c : Ixon.Constant) (r : Ixon.Recursor) : Except String Parent := do
  let n := (r.params + r.motives + r.minors + r.indices).toNat
  let some (_, rest) := Ix.Kernel.Reader.stripAll c n r.typ
    | throw "recursor type is shorter than its counts"
  let .all dom _ := Ix.Kernel.Reader.unshare c rest | throw "no major premise"
  let .ref j _ := Ix.Kernel.Reader.appHead c Ix.Kernel.Reader.spineFuel dom
    | throw "the major premise's head is not a reference"
  let some pa := c.refs[j.toNat]? | throw "the major premise's head is out of range"
  let some pc := env.getConst? pa | throw "the family's record is missing"
  let .iPrj p := pc.info | throw "the major premise's head is not an inductive projection"
  let some bc := env.getConst? p.block | throw "the family's block is missing"
  let .muts ms := bc.info | throw "the family's block is not a block"
  let some (.indc ind) := ms[p.idx.toNat]? | throw "the family's member is not an inductive"
  pure { projAddr := pa, blockAddr := p.block, block := bc, idx := p.idx.toNat, ind }

/-- A value `λ x₁ … xₖ, x₁` (`k ≥ 1`), binder data aside: what `KernelCheck::consume_wrapper`
consumes at a binder domain. -/
def lamFirst (c : Ixon.Constant) : Nat → Nat → E → Bool
  | 0, _, _ => false
  | fuel + 1, n, e =>
    match Ix.Kernel.Reader.unshare c e with
    | .lam _ b => lamFirst c fuel (n + 1) b
    | .var i => n > 0 && i.toNat + 1 == n
    | _ => false

def isWrapper (env : Ixon.Env) (a : Address) : Bool :=
  match env.getConst? a with
  | some c =>
    match c.info with
    | .defn d =>
      (match d.kind with
        | .defn => lamFirst c 64 0 d.value
        | _ => false)
    | _ => false
  | none => false

structure Shape where
  nParams : Nat := 0
  nIdx : Nat := 0
  nCtors : Nat := 0
  maxFields : Nat := 0
  /-- direct recursive fields, over all constructors -/
  recFields : Nat := 0
  /-- the most recursive or reflexive fields in one constructor -/
  maxRecInCtor : Nat := 0
  /-- reflexive fields, and the deepest telescope of one -/
  reflFields : Nat := 0
  reflDepth : Nat := 0
  /-- a recursive or reflexive field before an ordinary one -/
  recBeforeOrdinary : Bool := false
  large : Bool := false
  k : Bool := false
  letInFamily : Bool := false
  letInRecursor : Bool := false
  wrapper : Bool := false
  aliasFormer : Bool := false
  deriving Inhabited

def shapeOf (env : Ixon.Env) (c : Ixon.Constant) (r : Ixon.Recursor) (p : Parent) : Shape := Id.run do
  let bc := p.block
  let sh := bc.sharing
  let ind := p.ind
  let wrapIdx : Array Bool := bc.refs.map (isWrapper env)
  let isWrapRef : E → Bool := fun e => match e with
    | .ref j _ => wrapIdx[j.toNat]?.getD false
    | _ => false
  let mut s : Shape := {
    nParams := ind.params.toNat, nIdx := ind.indices.toNat, nCtors := ind.ctors.size,
    large := r.lvls.toNat == ind.lvls.toNat + 1, k := r.k }
  if anyIn sh isLet ind.typ then s := { s with letInFamily := true }
  if anyIn sh isWrapRef ind.typ then s := { s with wrapper := true }
  match Ix.Kernel.Reader.stripAll bc (ind.params + ind.indices).toNat ind.typ with
  | some (_, body) =>
    match Ix.Kernel.Reader.unshare bc body with
    | .sort _ => pure ()
    | _ => s := { s with aliasFormer := true }
  | none => s := { s with aliasFormer := true }
  for ct in ind.ctors do
    if anyIn sh isLet ct.typ then s := { s with letInFamily := true }
    if anyIn sh isWrapRef ct.typ then s := { s with wrapper := true }
    s := { s with maxFields := max s.maxFields ct.fields.toNat }
    match Ix.Kernel.Reader.stripAll bc ct.params.toNat ct.typ with
    | none => pure ()
    | some (_, body) =>
      let (fds, _) := Ix.Kernel.Reader.stripAllFull bc ct.fields.toNat body
      let mut inCtor := 0
      let mut seenRec := false
      for d in fds do
        if anyIn sh isRecur d then
          let depth := (Ix.Kernel.Reader.stripAllFull bc 4096 d).1.length
          inCtor := inCtor + 1
          seenRec := true
          if depth == 0 then s := { s with recFields := s.recFields + 1 }
          else s := { s with reflFields := s.reflFields + 1, reflDepth := max s.reflDepth depth }
        else if seenRec then s := { s with recBeforeOrdinary := true }
      s := { s with maxRecInCtor := max s.maxRecInCtor inCtor }
  if anyIn c.sharing isLet r.typ || r.rules.any (fun rl => anyIn c.sharing isLet rl.rhs) then
    s := { s with letInRecursor := true }
  return s

/-- The strata a shape belongs to. -/
def Shape.tags (s : Shape) : Array String := Id.run do
  let mut t : Array String := #[]
  t := t.push (if s.nIdx == 0 then "idx:0" else if s.nIdx == 1 then "idx:1" else "idx:2+")
  t := t.push (if s.nCtors == 0 then "ctors:0" else if s.nCtors == 1 then "ctors:1" else "ctors:many")
  t := t.push (if s.large then "elim:large" else "elim:small")
  if s.k then t := t.push "k-like"
  if s.nCtors == 1 && s.nIdx == 0 && s.recFields == 0 && s.reflFields == 0 then
    t := t.push "structure-like"
  if s.recFields > 0 then t := t.push "rec-field"
  if s.maxRecInCtor ≥ 2 then t := t.push "rec-fields:2+-in-one-ctor"
  if s.recBeforeOrdinary then t := t.push "rec-before-ordinary"
  if s.reflFields > 0 then
    t := t.push (if s.reflDepth == 1 then "reflexive:depth-1" else if s.reflDepth == 2 then
      "reflexive:depth-2" else "reflexive:depth-3+")
  if s.recFields == 0 && s.reflFields == 0 then t := t.push "no-rec-field"
  if s.letInFamily then t := t.push "let-in-family"
  if s.letInRecursor then t := t.push "let-in-recursor"
  if s.wrapper then t := t.push "wrapper-in-family"
  if s.aliasFormer then t := t.push "alias-former"
  if s.nParams == 0 then t := t.push "params:0"
  return t

/-! ## Witnesses -/

def addrKey (a : Address) : Array Aiur.G := a.hash.data.map .ofUInt8

def hintG : Lean.ReducibilityHints → Aiur.G
  | .opaque => .ofNat 0
  | .abbrev => .ofNat 0xFFFFFFFF
  | .regular n => .ofNat (min (1 + n.toNat) 0xFFFFFFFE)

/-- The records `a` names: its reference table, a projection's block, a block's member
projections. -/
def depsOf (env : Ixon.Env) (a : Address) : Array Address :=
  match env.getConst? a with
  | none => #[]
  | some c => Id.run do
    let mut out := c.refs
    match c.info with
    | .iPrj p => out := out.push p.block
    | .cPrj p => out := out.push p.block
    | .rPrj p => out := out.push p.block
    | .dPrj p => out := out.push p.block
    | .muts ms =>
      for (m, i) in ms.zipIdx do
        let i := i.toUInt64
        match m with
        | .defn _ => out := out.push (projWrapperAddr (.dPrj ⟨i, a⟩))
        | .recr _ => out := out.push (projWrapperAddr (.rPrj ⟨i, a⟩))
        | .indc ind =>
          out := out.push (projWrapperAddr (.iPrj ⟨i, a⟩))
          for (_, j) in ind.ctors.zipIdx do
            out := out.push (projWrapperAddr (.cPrj ⟨i, j.toUInt64, a⟩))
    | _ => pure ()
    return out

/-- The addresses within `depth` naming steps of `roots`, roots first; `none` past `cap`. -/
def closureTo (env : Ixon.Env) (roots : Array Address) (depth cap : Nat) :
    Option (Array Address) := Id.run do
  let mut seen : Std.HashSet Address := {}
  let mut order : Array Address := #[]
  let mut cur : Array Address := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      order := order.push r
      cur := cur.push r
  let mut d := 0
  while d < depth && !cur.isEmpty do
    let mut next : Array Address := #[]
    for a in cur do
      for x in depsOf env a do
        unless seen.contains x do
          seen := seen.insert x
          order := order.push x
          next := next.push x
    if order.size > cap then return none
    cur := next
    d := d + 1
  return some order

structure Built where
  witness : ClaimWitness
  records : Nat
  bytes : Nat

/-- The witness of the claim "`target` checks, given every record of `frontier`": the
claim, the binding, the assumption tree, the records `extra` (not in `env`) and those of
`scope` that `env` holds, with their hints and blobs. -/
def buildWitness (env : Ixon.Env) (ctx : Ix.ClaimContext)
    (extra : Array (Address × Ixon.Constant)) (target : Address) (frontier scope : Array Address) :
    Built := Id.run do
  let asmTree? := Ix.AssumptionTree.canonical frontier
  let claim := Ix.Claim.check ctx target (asmTree?.map (·.root))
  let claimBytes := Ix.Claim.ser claim
  let digestKey := packedDigestKey (Address.blake3 claimBytes)
  let mut io : Aiur.IOBuffer := seedBinding env default
  io := io.extend 0 digestKey (claimBytes.data.map .ofUInt8)
  if let some t := asmTree? then
    io := io.extend 1 (addrKey t.root) ((Ix.AssumptionTree.ser t).data.map .ofUInt8)
  let mut records := 0
  let mut bytes := 0
  let mut have_ : Std.HashSet Address := {}
  for (a, c) in extra do
    if have_.contains a then continue
    have_ := have_.insert a
    let b := Ixon.ser c
    io := io.extend 2 (addrKey a) (b.data.map .ofUInt8)
    records := records + 1
    bytes := bytes + b.size
  for a in scope do
    if have_.contains a then continue
    have_ := have_.insert a
    if let some lc := env.consts.get? a then
      let b := lc.rawBytes
      io := io.extend 2 (addrKey a) (b.data.map .ofUInt8)
      records := records + 1
      bytes := bytes + b.size
      if let some h := env.anonHints.get? a then
        io := io.extend 3 (addrKey a) #[hintG h]
      -- a block's model payload, as the prover's harness serves it (empty when it has none):
      -- a record that an edit routes to the modeled check is then refused by the program
      match lc.peekTag with
      | .ok .muts =>
        io := io.extend 7 (addrKey a)
          (((env.models.get? a).getD ByteArray.empty).data.map .ofUInt8)
      | _ => pure ()
    if let some blob := env.blobs.get? a then
      io := io.extend 4 (addrKey a) (blob.data.map fun x => .ofNat x.toNat)
      bytes := bytes + blob.size
      -- an edit can name a blob as a constant: its bytes are then also served as a record,
      -- so that the program reads them and refuses them itself
      unless env.consts.contains a do
        io := io.extend 2 (addrKey a) (blob.data.map .ofUInt8)
  return { witness := { funcName := `verify_claim, input := digestKey, inputIOBuffer := io },
           records, bytes }

/-- Every record the reference table of `c` names, except `self`. -/
def frontierOf (c : Ixon.Constant) (self : Address) : Array Address := Id.run do
  let mut seen : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  for r in c.refs do
    if r != self && !seen.contains r then
      seen := seen.insert r
      out := out.push r
  return out

/-! ## Running cases and reading verdicts -/

inductive Verdict where
  /-- accepted; `reached` is false when the case named a function the run did not call -/
  | accepted (reached : Bool)
  | rejected (msg : String)
  /-- the witness lacked data the program asked for -/
  | missing (msg : String)
  | noLine
  deriving Inhabited, Repr

def Verdict.isAccepted : Verdict → Bool
  | .accepted _ => true
  | _ => false

def Verdict.text : Verdict → String
  | .accepted true => "accepted"
  | .accepted false => "accepted-without-reaching"
  | .rejected m => s!"rejected: {m}"
  | .missing m => s!"missing: {m}"
  | .noLine => "no-verdict"

/-- The assertion text of a rejection: the message after the function and instruction. -/
def rejectionReason (msg : String) : String :=
  match msg.splitOn ": " with
  | _ :: rest@(_ :: _) => ": ".intercalate rest
  | _ => msg

/-- The verdict lines of a host run, by label. A line is `LABEL: accepted (T)`,
`LABEL: rejected: ERROR (T)` or the same after `FAILED ` with `; expected …`. -/
def parseVerdicts (stdout : String) (labels : Array String) : Std.HashMap String Verdict := Id.run do
  let known : Std.HashSet String := labels.foldl (·.insert ·) {}
  let mut out : Std.HashMap String Verdict := {}
  for line in stdout.splitOn "\n" do
    let failed := line.startsWith "FAILED "
    let rest := if failed then "FAILED ".intercalate ((line.splitOn "FAILED ").drop 1) else line
    match rest.splitOn ": " with
    | lbl :: tail@(_ :: _) =>
      if known.contains lbl then
        let body := ": ".intercalate tail
        if body.startsWith "accepted" then
          out := out.insert lbl (.accepted (!hasSub body "expected an acceptance calling"))
        else if body.startsWith "rejected" then
          let msg := ": ".intercalate ((body.splitOn ": ").drop 1)
          let msg := (msg.splitOn "; expected ").headD msg
          if hasSub msg "missing hint" || hasSub msg "invalid IO key" then
            out := out.insert lbl (.missing msg)
          else out := out.insert lbl (.rejected msg)
    | _ => pure ()
  return out

structure Host where
  artifact : String
  host : String
  dir : System.FilePath

def Host.make : IO Host := do
  let artifact ← programArtifact
  let host ← programHost
  let some out ← IO.getEnv "IX_RECGEN_OUT" | throw (IO.userError "IX_RECGEN_OUT is not set")
  let dir := System.FilePath.mk out
  IO.FS.createDirAll (dir / "cases")
  return { artifact, host, dir }

/-- Run `cases` in one host process in circuit-verdict mode; the case file is removed. -/
def Host.run (h : Host) (tag : String) (cases : Array Case) : IO (Std.HashMap String Verdict) := do
  if cases.isEmpty then return {}
  let path := h.dir / "cases" / s!"{tag}.ixt"
  let handle ← IO.FS.Handle.mk path .write
  handle.write Ix.AiurInvocation.casesHeader
  for c in cases do handle.write c.encode
  handle.write Ix.AiurInvocation.casesTrailer
  handle.flush
  let out ← IO.Process.output {
    cmd := h.host, args := #["test", h.artifact, path.toString],
    env := #[(circuitVerdictVar, some "1")] }
  IO.FS.removeFile path
  match circuitAcknowledgement out.stdout with
  | some n =>
    if n == 0 then
      throw (IO.userError s!"{tag}: the host enabled no deferred assertion")
  | none =>
    throw (IO.userError s!"{tag}: the host did not run in circuit-verdict mode: {out.stderr}")
  return parseVerdicts out.stdout (cases.map (·.label))

/-- `f 0 … f (n - 1)` on `workers` dedicated threads, results in index order. -/
def parFor {α : Type} [Inhabited α] (workers n : Nat) (f : Nat → IO α) : IO (Array α) := do
  let next ← IO.mkRef 0
  let worker : IO (Array (Nat × α)) := do
    let mut acc : Array (Nat × α) := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if i ≥ n then break
      acc := acc.push (i, ← f i)
    return acc
  let tasks ← (List.range (max 1 workers)).mapM fun _ => IO.asTask (prio := .dedicated) worker
  let mut out : Array (Option α) := Array.replicate n none
  for t in tasks do
    let done ← IO.ofExcept (← IO.wait t)
    for (i, a) in done do
      out := out.set! i (some a)
  return out.map (·.getD default)

/-! ## The corpus -/

instance : Inhabited Parent := ⟨⟨default, default, default, 0, default⟩⟩

structure Target where
  addr : Address
  name : String
  c : Ixon.Constant
  r : Ixon.Recursor
  parent : Except String Parent
  shape : Shape
  deriving Inhabited

structure Corpus where
  env : Ixon.Env
  ctx : Ix.ClaimContext
  targets : Array Target
  /-- The constants the program may load without a reference to them: the binding's bound
  constants and the primitive addresses (a literal's type and constructor forms). -/
  support : Array Address

/-- The standalone recursor records of `env`, by address. -/
def Corpus.ofEnv (env : Ixon.Env) : IO Corpus := do
  let t0 ← IO.monoMsNow
  let some binding := env.roleBinding
    | throw (IO.userError "the corpus carries no role binding")
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofBinding binding.address (bindingAssumed := true))
  let mut nameOf : Std.HashMap Address String := {}
  for (n, nm) in env.named.toArray do
    unless nameOf.contains nm.addr do nameOf := nameOf.insert nm.addr (toString n)
  let mut recs : Array (Address × Ixon.Constant × Ixon.Recursor) := #[]
  for (a, lc) in env.consts.toArray do
    match lc.peekTag with
    | .ok .recr =>
      if let some c := lc.get? then
        if let .recr r := c.info then recs := recs.push (a, c, r)
    | _ => pure ()
  let sorted := recs.qsort fun x y => x.1.hash.data < y.1.hash.data
  let targets := sorted.map fun (a, c, r) =>
    let parent := parentOf env c r
    let shape := match parent with
      | .ok p => shapeOf env c r p
      | .error _ => {}
    ({ addr := a, name := nameOf.getD a (toString a), c, r, parent, shape } : Target)
  let support := bindingRoots env true ++ Ix.primAddrSet.toArray.filter env.consts.contains
  IO.println s!"[ixvm-recgen] {targets.size} standalone recursor records, {support.size} support \
    constants ({(← IO.monoMsNow) - t0} ms)"
  return { env, ctx, targets, support }

def Corpus.load (path : String) : IO Corpus := do
  let t0 ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  IO.println s!"[ixvm-recgen] {path}: {env.consts.size} records, {env.named.size} names \
    ({(← IO.monoMsNow) - t0} ms)"
  Corpus.ofEnv env

/-- An evenly spaced sample of at most `limit` (0 = all). -/
def sample {α : Type} [Inhabited α] (xs : Array α) (limit seed : Nat) : Array α :=
  if limit == 0 || xs.size ≤ limit then xs
  else (Array.range limit).map fun i => xs[(seed + i * xs.size / limit) % xs.size]!

/-- The number of witness scopes tried in turn. -/
def scopeLevels : Nat := 4

def closureCap : Nat := 400000

/-- Witness scope `level` of a target: the records within 1, 2 or 4 naming steps of the target
and its frontier; from the third level on also the support constants (two steps), and at
the last the whole closure of all of them. -/
def scopeFor (cp : Corpus) (addr : Address) (frontier : Array Address) (level : Nat) :
    Option (Array Address) :=
  let roots := #[addr] ++ frontier
  match level with
  | 0 => closureTo cp.env roots 1 closureCap
  | 1 => closureTo cp.env roots 2 closureCap
  | 2 =>
    (closureTo cp.env roots 4 closureCap).bind fun a =>
      (closureTo cp.env cp.support 2 closureCap).map (a ++ ·)
  | _ => closureTo cp.env (roots ++ cp.support) 1000000 closureCap

structure Outcome where
  verdict : Verdict := .noLine
  depth : Nat := 0
  records : Nat := 0
  bytes : Nat := 0
  ms : Nat := 0
  deriving Inhabited

/-- Check `record` at `addr` (a record of the corpus, or one of `extra`) alone, widening
the witness while the program asks for more. `start` is the first scope level tried. -/
def checkOne (h : Host) (cp : Corpus) (tag label : String) (addr : Address) (record : Ixon.Constant)
    (extra : Array (Address × Ixon.Constant)) (accept : Bool)
    (exercises : Option String := none) (start : Nat := 0) : IO Outcome := do
  let t0 ← IO.monoMsNow
  let frontier := frontierOf record addr
  let mut last : Outcome := {}
  for level in [start:scopeLevels] do
    let some scope := scopeFor cp addr frontier level
      | return { last with verdict := .missing "closure exceeds the record cap" }
    let b := buildWitness cp.env cp.ctx extra addr frontier scope
    let verdicts ← h.run tag #[{ label, accept, exercises, witness := b.witness }]
    let v := verdicts.getD label .noLine
    last := { verdict := v, depth := level, records := b.records, bytes := b.bytes,
              ms := (← IO.monoMsNow) - t0 }
    match v with
    | .missing _ => continue
    | _ => return last
  return last

def tsvLine (xs : List String) : String := "\t".intercalate xs

/-- Counts per stratum: (run, accepted). -/
def tally (rows : Array (Array String × Bool)) : Array (String × Nat × Nat) := Id.run do
  let mut m : Std.HashMap String (Nat × Nat) := {}
  for (tags, ok) in rows do
    for t in tags do
      let (n, a) := m.getD t (0, 0)
      m := m.insert t (n + 1, if ok then a + 1 else a)
  return m.toArray.qsort fun x y => x.1 < y.1

/-! ## Honest records -/

/-- Every chosen record as stored. `IX_RECGEN_TAG` keeps one stratum; `IX_RECGEN_EXERCISE`
names the function an acceptance is asked to have called (default the native recursor
check; with another function, an acceptance that did not call it is counted, not failed);
`IX_RECGEN_LABEL` prefixes the output files. -/
def runHonest (cp : Corpus) (h : Host) : IO UInt32 := do
  let limit ← envNat "IX_RECGEN_LIMIT" 0
  let seed ← envNat "IX_RECGEN_SEED" 0
  let workers ← envNat "IX_RECGEN_WORKERS" 32
  let tag? ← IO.getEnv "IX_RECGEN_TAG"
  let fn := (← IO.getEnv "IX_RECGEN_EXERCISE").getD "KernelCheck::nat_rec_check"
  let strict := fn == "KernelCheck::nat_rec_check"
  let label := (← IO.getEnv "IX_RECGEN_LABEL").getD "honest"
  let pool := match tag? with
    | some tag => cp.targets.filter (·.shape.tags.contains tag)
    | none => cp.targets
  let chosen := sample pool limit seed
  IO.println s!"[ixvm-recgen] {label}: {chosen.size} of {cp.targets.size} standalone recursor \
    records (pool {pool.size}), exercising {fn}, {workers} workers"
  let t0 ← IO.monoMsNow
  let outcomes ← parFor workers chosen.size fun i => do
    let t := chosen[i]!
    checkOne h cp s!"{label}{i}" s!"rg{i}x" t.addr t.c #[] true (some fn)
  let mut lines : Array String := #[tsvLine ["index", "name", "address", "verdict", "depth",
    "records", "bytes", "ms", "strata", "detail"]]
  let mut rows : Array (Array String × Bool) := #[]
  let mut accepted := 0
  let mut unreached : Array String := #[]
  let mut rejected : Array String := #[]
  let mut unresolved : Array String := #[]
  let mut noParent := 0
  let mut bytes := 0
  for (t, i) in chosen.zipIdx do
    let o := outcomes[i]!
    let tags := t.shape.tags
    bytes := bytes + o.bytes
    let ok := match o.verdict with
      | .accepted reached => reached || !strict
      | _ => false
    match o.verdict with
    | .accepted true => accepted := accepted + 1
    | .accepted false => unreached := unreached.push s!"{t.name}\t{t.addr}"
    | .rejected m => rejected := rejected.push s!"{t.name}\t{t.addr}\t{m}"
    | .missing m => unresolved := unresolved.push s!"{t.name}\t{t.addr}\t{m}"
    | .noLine => unresolved := unresolved.push s!"{t.name}\t{t.addr}\tno verdict line"
    let detail := match t.parent with
      | .ok _ => ""
      | .error e => e
    if detail != "" then noParent := noParent + 1
    rows := rows.push (tags, ok)
    lines := lines.push (tsvLine [toString i, t.name, toString t.addr, o.verdict.text,
      toString o.depth, toString o.records, toString o.bytes, toString o.ms,
      ",".intercalate tags.toList, detail])
  IO.FS.writeFile (h.dir / s!"{label}.tsv") ("\n".intercalate lines.toList ++ "\n")
  let mut summary : Array String := #[
    s!"standalone recursor records in the corpus: {cp.targets.size}",
    s!"pool: {pool.size} (stratum {tag?.getD "all"})",
    s!"run: {chosen.size}",
    s!"accepted, having called {fn}: {accepted}",
    s!"accepted without calling it: {unreached.size}",
    s!"rejected: {rejected.size}",
    s!"no verdict (witness incomplete or no line): {unresolved.size}",
    s!"family not read from the record: {noParent}",
    s!"witness bytes in the settling runs: {bytes}",
    s!"elapsed ms: {(← IO.monoMsNow) - t0}",
    "", "stratum\trun\taccepted"]
  for (tag, n, a) in tally rows do summary := summary.push s!"{tag}\t{n}\t{a}"
  let byDepth := (Array.range scopeLevels).map fun d =>
    (outcomes.filter (·.depth == d)).size
  summary := summary.push ""
  summary := summary.push s!"records settled at witness scope level 0..{scopeLevels - 1}: {byDepth}"
  summary := summary.push ""
  summary := summary.push "REJECTED:"
  for r in rejected do summary := summary.push r
  summary := summary.push "UNRESOLVED:"
  for r in unresolved do summary := summary.push r
  summary := summary.push "ACCEPTED WITHOUT THE CALL:"
  for r in unreached do summary := summary.push r
  IO.FS.writeFile (h.dir / s!"{label}-summary.txt") ("\n".intercalate summary.toList ++ "\n")
  for l in summary.toList.take 70 do IO.println l
  let bad := !rejected.isEmpty || !unresolved.isEmpty || (strict && !unreached.isEmpty)
  return if bad then 1 else 0

/-! ## Altered records -/

def fmtDatum : Ixon.BinderNode → String
  | .never _ => "n"
  | .zero _ => "z"
  | .ifAllZero ps _ => s!"p{ps}"
  | .share v => s!"s{v}"
  | .undecided _ => "?"

partial def AE.fmt : AE → String
  | .sort u => s!"(sort {u})"
  | .var i => s!"#{i}"
  | .ref i us => s!"(ref {i} {us})"
  | .recur i us => s!"(rec {i} {us})"
  | .prj t i e => s!"(prj {t} {i} {e.fmt})"
  | .str i => s!"(str {i})"
  | .nat i => s!"(nat {i})"
  | .app f a =>
    let (h, as) := (AE.app f a).spine
    "(" ++ " ".intercalate ((h :: as.toList).map AE.fmt) ++ ")"
  | .lam d t b => s!"(λ[{fmtDatum d}] {t.fmt}. {b.fmt})"
  | .all d t b => s!"(∀[{fmtDatum d}] {t.fmt}. {b.fmt})"
  | .letE _ _ t v b => s!"(let {t.fmt} := {v.fmt}; {b.fmt})"

def XRec.fmt (x : XRec) : String :=
  let r := x.r
  let head := s!"recursor k={r.k} unsafe={r.isUnsafe} lvls={r.lvls} params={r.params} \
    indices={r.indices} motives={r.motives} minors={r.minors}\nunivs={repr x.univs}\n\
    refs={x.refs}\ntype: {x.typ.fmt}"
  x.rules.zipIdx.foldl (fun s ((f, rhs), i) => s ++ s!"\nrule {i} fields={f}: {rhs.fmt}") head

def hexOf (b : ByteArray) : String :=
  let digit (n : UInt8) : Char := if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)
  String.ofList (b.data.toList.flatMap fun (x : UInt8) => [digit (x >>> 4), digit (x &&& 15)])

/-- A sample that takes up to `perTag` records of every stratum, then evenly spaced
records up to `total`. -/
def stratified (targets : Array Target) (perTag total seed : Nat) : Array Target := Id.run do
  let mut chosen : Std.HashSet Nat := {}
  let mut order : Array Nat := #[]
  let mut byTag : Std.HashMap String (Array Nat) := {}
  for (t, i) in targets.zipIdx do
    for tag in t.shape.tags do
      byTag := byTag.insert tag ((byTag.getD tag #[]).push i)
  for (_, idxs) in byTag.toArray.qsort (fun a b => a.1 < b.1) do
    for i in sample idxs perTag seed do
      unless chosen.contains i do
        chosen := chosen.insert i
        order := order.push i
  for i in sample (Array.range targets.size) total seed do
    if order.size ≥ total then break
    unless chosen.contains i do
      chosen := chosen.insert i
      order := order.push i
  return order.map (targets[·]!)

structure MutResult where
  op : String
  addr : Address
  verdict : Verdict
  record : Ixon.Constant
  deriving Inhabited

structure MutOutcome where
  control : Outcome := {}
  /-- why no altered record ran -/
  skipped : Option String := none
  expanded : Option XRec := none
  results : Array MutResult := #[]
  deriving Inhabited

/-- The control (the expanded record, which must be accepted) and every edit of it, each a
record of its own that must be rejected. The edits run at the control's witness scope; one
whose run lacks a record is rerun on wider scopes. -/
def mutateOne (h : Host) (cp : Corpus) (i : Nat) (name : String) (c : Ixon.Constant)
    (r : Ixon.Recursor) (cap maxRules batch : Nat) (seed : UInt64) : IO MutOutcome := do
  match XRec.ofConstant c r cap with
  | .error e => return { skipped := some s!"not expanded: {e}" }
  | .ok x =>
    let c0 := x.toConstant
    let a0 := Address.blake3 (Ixon.ser c0)
    let control ← checkOne h cp s!"m{i}c" s!"rg{i}x" a0 c0 #[(a0, c0)] true
      (some "KernelCheck::nat_rec_check")
    match control.verdict with
    | .accepted true => pure ()
    | _ => return { control, expanded := some x,
                    skipped := some s!"the expanded record of {name} is not accepted" }
    let mut seen : Std.HashSet Address := ({} : Std.HashSet Address).insert a0
    let mut ms : Array (String × Address × Ixon.Constant) := #[]
    for (op, xm) in mutantsOf x (seed + i.toUInt64) maxRules do
      let cm := xm.toConstant
      let am := Address.blake3 (Ixon.ser cm)
      if seen.contains am then continue
      seen := seen.insert am
      ms := ms.push (op, am, cm)
    let some scope := scopeFor cp a0 (frontierOf c0 a0) control.depth
      | return { control, expanded := some x, skipped := some "no witness scope" }
    let mut results : Array MutResult := #[]
    let mut k0 := 0
    while k0 < ms.size do
      let chunk := ms.extract k0 (k0 + batch)
      let cases : Array Case := chunk.mapIdx fun k (_, am, cm) =>
        let b := buildWitness cp.env cp.ctx #[(am, cm)] am (frontierOf cm am) scope
        { label := s!"rg{i}x{k0 + k}x", accept := false, witness := b.witness }
      let verdicts ← h.run s!"m{i}b{k0}" cases
      for ((op, am, cm), k) in chunk.zipIdx do
        let lbl := s!"rg{i}x{k0 + k}x"
        let mut v := verdicts.getD lbl .noLine
        let again := match v with
          | .missing _ => true
          | .noLine => true
          | _ => false
        if again then
          let o ← checkOne h cp s!"m{i}r{k0 + k}" lbl am cm #[(am, cm)] false none
            (control.depth + 1)
          -- a rerun that finds no wider scope keeps the first verdict
          v := match o.verdict with
            | .noLine => v
            | w => w
        -- only an accepted edit keeps its record, for the report
        results := results.push {
          op, addr := am, verdict := v, record := if v.isAccepted then cm else default }
      k0 := k0 + batch
    return { control, expanded := some x, results }

/-- An accepted edit, for the report: the control and the altered record as text, and
whether the two are equal once every `let` is expanded (`XRec.zetaEq`), in which case the
edit only changed something inside a `let` that expansion erases (its type annotation, or a
value the body does not use). -/
def describeAccepted (control : Option XRec) (m : MutResult) (cap : Nat) :
    String × String × Bool :=
  let altered : Except String XRec := match m.record.info with
    | .recr r' => XRec.ofConstant m.record r' (cap * 4)
    | _ => .error "not a recursor record"
  let orig := match control with
    | some x => x.fmt
    | none => ""
  match control, altered with
  | some x, .ok y => (orig, y.fmt, x.zetaEq y)
  | _, .ok y => (orig, y.fmt, false)
  | _, .error e => (orig, s!"(not expanded: {e})", false)

/-- An edit's class: its name without the per-site suffix. -/
def opClass (op : String) : String := op

def runMutate (cp : Corpus) (h : Host) : IO UInt32 := do
  let total ← envNat "IX_RECGEN_LIMIT" 600
  let perTag ← envNat "IX_RECGEN_PER_TAG" 40
  let seed ← envNat "IX_RECGEN_SEED" 1
  let workers ← envNat "IX_RECGEN_WORKERS" 32
  let cap ← envNat "IX_RECGEN_CAP" 60000
  let maxRules ← envNat "IX_RECGEN_RULES" 3
  let batch ← envNat "IX_RECGEN_BATCH" 12
  let label := (← IO.getEnv "IX_RECGEN_LABEL").getD "mutate"
  let pool := match (← IO.getEnv "IX_RECGEN_TAG") with
    | some tag => cp.targets.filter (·.shape.tags.contains tag)
    | none => cp.targets
  -- `IX_RECGEN_NAME`: keep the records whose name contains one of the comma-separated strings
  let pool := match (← IO.getEnv "IX_RECGEN_NAME") with
    | some ns => pool.filter fun t => (ns.splitOn ",").any fun n => hasSub t.name n
    | none => pool
  let chosen := stratified pool perTag total seed
  IO.println s!"[ixvm-recgen] {label}: {chosen.size} of {cp.targets.size} standalone recursor \
    records, up to {perTag} per stratum, {workers} workers"
  let t0 ← IO.monoMsNow
  let outcomes ← parFor workers chosen.size fun i => do
    let t := chosen[i]!
    try mutateOne h cp i t.name t.c t.r cap maxRules batch (UInt64.ofNat seed * 1000003)
    catch e => pure ({ skipped := some s!"error: {e}" } : MutOutcome)
  IO.FS.createDirAll (h.dir / s!"{label}-accepted")
  let mut lines : Array String := #[tsvLine ["index", "name", "edit", "address", "verdict"]]
  let mut perOp : Std.HashMap String (Nat × Nat × Nat × Nat) := {}
  let mut reasons : Std.HashMap String (Std.HashMap String Nat) := {}
  let mut acceptedList : Array String := #[]
  let mut acceptedWrong := 0
  let mut unresolvedList : Array String := #[]
  let mut skipped : Array String := #[]
  let mut rows : Array (Array String × Bool) := #[]
  let mut controls := 0
  let mut nMut := 0
  let mut nRej := 0
  for (t, i) in chosen.zipIdx do
    let o := outcomes[i]!
    if let some why := o.skipped then
      skipped := skipped.push s!"{t.name}\t{t.addr}\t{why}\t{o.control.verdict.text}"
      continue
    controls := controls + 1
    rows := rows.push (t.shape.tags, true)
    for (m, k) in o.results.zipIdx do
      nMut := nMut + 1
      let cls := opClass m.op
      let (n, rej, acc, unres) := perOp.getD cls (0, 0, 0, 0)
      lines := lines.push (tsvLine [toString i, t.name, m.op, toString m.addr, m.verdict.text])
      match m.verdict with
      | .rejected msg =>
        nRej := nRej + 1
        perOp := perOp.insert cls (n + 1, rej + 1, acc, unres)
        let why := (rejectionReason msg).splitOn " (" |>.headD ""
        let hist := reasons.getD cls {}
        reasons := reasons.insert cls (hist.insert why (hist.getD why 0 + 1))
      | .accepted _ =>
        perOp := perOp.insert cls (n + 1, rej, acc + 1, unres)
        let (orig, alt, same) := describeAccepted o.expanded m cap
        acceptedList := acceptedList.push
          s!"{i}\t{k}\t{t.name}\t{m.op}\t{m.addr}\tequal once lets are expanded: {same}"
        unless same do acceptedWrong := acceptedWrong + 1
        IO.FS.writeFile (h.dir / s!"{label}-accepted" / s!"{i}-{k}.txt")
          s!"name: {t.name}\nstored record: {t.addr}\nedit: {m.op}\naltered record: {m.addr}\n\
            equal to the control once every let is expanded: {same}\n\
            altered bytes: {hexOf (Ixon.ser m.record)}\n\n== control ==\n{orig}\n\n\
            == altered ==\n{alt}\n"
      | v =>
        perOp := perOp.insert cls (n + 1, rej, acc, unres + 1)
        unresolvedList := unresolvedList.push s!"{i}\t{k}\t{t.name}\t{m.op}\t{v.text}"
  IO.FS.writeFile (h.dir / s!"{label}.tsv") ("\n".intercalate lines.toList ++ "\n")
  let mut summary : Array String := #[
    s!"standalone recursor records in the corpus: {cp.targets.size}",
    s!"sampled: {chosen.size}",
    s!"controls accepted (expanded record, through nat_rec_check): {controls}",
    s!"sampled but not edited: {skipped.size}",
    s!"altered records run: {nMut}",
    s!"rejected: {nRej}",
    s!"ACCEPTED: {acceptedList.size}",
    s!"accepted and not equal to the control once every let is expanded: {acceptedWrong}",
    s!"no verdict: {unresolvedList.size}",
    s!"elapsed ms: {(← IO.monoMsNow) - t0}",
    "", "edit\trun\trejected\taccepted\tno-verdict"]
  for (op, n, rej, acc, unres) in perOp.toArray.qsort (fun a b => a.1 < b.1) do
    summary := summary.push s!"{op}\t{n}\t{rej}\t{acc}\t{unres}"
  summary := summary.push ""
  summary := summary.push "stratum\tcontrols\taccepted"
  for (tag, n, a) in tally rows do summary := summary.push s!"{tag}\t{n}\t{a}"
  summary := summary.push ""
  summary := summary.push "ACCEPTED ALTERED RECORDS (index, edit number, name, edit, address):"
  for a in acceptedList do summary := summary.push a
  summary := summary.push "NO VERDICT:"
  for a in unresolvedList do summary := summary.push a
  summary := summary.push "NOT EDITED:"
  for s in skipped do summary := summary.push s
  IO.FS.writeFile (h.dir / s!"{label}-summary.txt") ("\n".intercalate summary.toList ++ "\n")
  let mut why : Array String := #["edit\trejection\tcount"]
  for (op, hist) in reasons.toArray.qsort (fun a b => a.1 < b.1) do
    for (r, n) in hist.toArray.qsort (fun a b => a.2 > b.2) do
      why := why.push s!"{op}\t{r}\t{n}"
  IO.FS.writeFile (h.dir / s!"{label}-reasons.tsv") ("\n".intercalate why.toList ++ "\n")
  for l in summary.toList.take 140 do IO.println l
  return if acceptedWrong == 0 && unresolvedList.isEmpty then 0 else 1

/-! ## The certified kernel's generated recursor as a record -/

/-- A kernel binder datum as a section node. The kernel names a level parameter by its
identifier; a record names it by its position among the declaration's parameters `lps`. -/
def datumOf (lps : List Nat) (pw : Ix.Kernel.PropWhen) : Ixon.BinderNode :=
  match pw.toList? with
  | none => .never {}
  | some ps =>
    Ix.Compile.BinderData.nodeOf
      (.binder (some (ps.toArray.map fun p => (lps.findIdx? (· == p)).getD p)))

/-- The binder data of a kernel term, in the section's order. -/
partial def kernelNodes (lps : List Nat) :
    Ix.Kernel.Expr .anon → Array Ixon.BinderNode → Array Ixon.BinderNode
  | .lam t b m, acc => kernelNodes lps b (kernelNodes lps t (acc.push (datumOf lps m.pw)))
  | .forallE t b m, acc => kernelNodes lps b (kernelNodes lps t (acc.push (datumOf lps m.pw)))
  | .app f a, acc => kernelNodes lps a (kernelNodes lps f acc)
  | .letE t v b _, acc => kernelNodes lps b (kernelNodes lps v (kernelNodes lps t acc))
  | .proj _ _ e, acc => kernelNodes lps e acc
  | _, acc => acc

/-- The recursor the certified kernel holds under the key of the record at `addr`: the type
and rules its native install generated (`structRecTyR`, `structRecRhsR`), encoded as a
record with `r`'s counts and flags, the kernel's own binder data, no sharing. -/
def ixcRecord (k : IxVM.PwHints.KernelEnv) (roles : Std.HashMap Ix.Kernel.Role Address)
    (addr : Address) (r : Ixon.Recursor) : Except String Ixon.Constant := do
  let some key := (k.setup.cx.memberKey (.member addr 0)).toOption
    | throw "the record has no key"
  let some (.recInfo cv _ _ rules) := k.fe.find? key
    | throw "the kernel holds no recursor under the record's key"
  let nm : IxVM.Model.Names := { roles }
  let lps := cv.levelParams
  let self : Ix.Kernel.Key .anon → Option Nat := fun x => if x == key then some 0 else none
  let rhss := rules.toArray.map (·.rhs)
  let act : IxVM.Model.EncM (Ixon.Expr × Array Ixon.Expr) := do
    let t ← IxVM.Model.encExpr nm lps self cv.type
    let rr ← rhss.mapM (IxVM.Model.encExpr nm lps self)
    pure (t, rr)
  let ((typ, encoded), s) ← act.run {}
  unless encoded.size == r.rules.size do
    throw s!"the kernel's recursor has {encoded.size} rules, the record {r.rules.size}"
  let roots := #[cv.type] ++ rhss
  let binders : Array Ixon.BinderBlock := roots.zipIdx.filterMap fun (e, i) =>
    let ns := kernelNodes lps e #[]
    if ns.isEmpty then none
    else some { shared := false, index := i.toUInt64, variant := 0, nodes := ns }
  return {
    info := .recr { r with typ, rules := (r.rules.zip encoded).map fun (rl, rhs) => { rl with rhs } },
    sharing := #[], refs := s.refs, univs := s.univs, binders }

/-- The first place two expanded terms differ, their tables resolved (a reference by its
address, a level by its canonical form), as the two subterms there; `none` when equal. -/
partial def firstDiff (x y : XRec) : AE → AE → Option (String × String)
  | a, b =>
    let lvl (u v : UInt64) : Bool :=
      (x.univs[u.toNat]?.map Ixon.canonUniv) == (y.univs[v.toNat]?.map Ixon.canonUniv)
    let lvls (us vs : Array UInt64) : Bool :=
      us.size == vs.size && (us.zip vs).all fun (u, v) => lvl u v
    let here : Option (String × String) := some (a.fmt, b.fmt)
    match a, b with
    | .sort u, .sort v => if lvl u v then none else here
    | .var i, .var j => if i == j then none else here
    | .ref i us, .ref j vs =>
      if x.refs[i.toNat]? == y.refs[j.toNat]? && lvls us vs then none else here
    | .recur i us, .recur j vs => if i == j && lvls us vs then none else here
    | .str i, .str j => if x.refs[i.toNat]? == y.refs[j.toNat]? then none else here
    | .nat i, .nat j => if x.refs[i.toNat]? == y.refs[j.toNat]? then none else here
    | .prj t i e, .prj t' i' e' =>
      if x.refs[t.toNat]? == y.refs[t'.toNat]? && i == i' then firstDiff x y e e' else here
    | .app f c, .app f' c' => (firstDiff x y f f').orElse fun _ => firstDiff x y c c'
    | .lam d t c, .lam d' t' c' =>
      if d == d' then (firstDiff x y t t').orElse fun _ => firstDiff x y c c' else here
    | .all d t c, .all d' t' c' =>
      if d == d' then (firstDiff x y t t').orElse fun _ => firstDiff x y c c' else here
    | .letE _ _ t v c, .letE _ _ t' v' c' =>
      ((firstDiff x y t t').orElse fun _ => firstDiff x y v v').orElse fun _ => firstDiff x y c c'
    | _, _ => here

def clip (s : String) (n : Nat := 240) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ "…"

/-- Where the stored recursor and another record of it differ, per root. -/
def compareRecords (x y : XRec) : Array String := Id.run do
  let mut out : Array String := #[]
  if let some (a, b) := firstDiff x y x.typ y.typ then
    out := out.push s!"type: {clip a} | {clip b}"
  for ((_, r1), j) in x.rules.zipIdx do
    match y.rules[j]? with
    | some (_, r2) =>
      if let some (a, b) := firstDiff x y r1 r2 then
        out := out.push s!"rule {j}: {clip a} | {clip b}"
    | none => out := out.push s!"rule {j}: missing"
  return out

/-- After an accepted run of the record `c`: whether the comparison consumed a wrapper
(`KernelCheck::consume_wrapper` was called). When it was not, the generated type and rules
are the record's up to `let` expansion alone. -/
def wrapperNote (h : Host) (cp : Corpus) (tag label : String) (a : Address) (c : Ixon.Constant)
    (o : Outcome) : IO String := do
  match o.verdict with
  | .accepted _ =>
    let w ← checkOne h cp tag label a c #[(a, c)] true (some "KernelCheck::consume_wrapper") o.depth
    match w.verdict with
    | .accepted true => pure " [a wrapper was consumed]"
    | .accepted false => pure " [no wrapper consumed]"
    | v => pure s!" [wrapper probe: {v.text}]"
  | _ => pure ""

/-! ## Fixture families -/

def storeRecord (env : Ixon.Env) (c : Ixon.Constant) : Ixon.Env × Address :=
  let a := Address.blake3 (Ixon.ser c)
  (env.storeConst a c, a)

/-- `c` with every reference to `old` naming `new`. -/
def repoint (c : Ixon.Constant) (old new : Address) : Ixon.Constant :=
  { c with refs := c.refs.map fun a => if a == old then new else a }

/-- The family `T : Type` with one constructor `mk : (A → … → A → T) → T` (`n` arrows,
`A` the constant at `a`) and its recursor, written out with their binder data: the block,
its two projection records and the recursor record. -/
def deepRecords (a : Address) (n : Nat) :
    (Address × Ixon.Constant) × (Address × Ixon.Constant) × (Address × Ixon.Constant) ×
      (Address × Ixon.Constant) :=
  let never : Ixon.BinderNode := .never {}
  let pw : Ixon.BinderNode := .ifAllZero #[0] {}
  let arrows (dom body : Ixon.Expr) : Ixon.Expr :=
    (List.range n).foldl (fun acc _ => Ixon.Expr.all dom acc) body
  -- the block: refs [A], levels [1]
  let ctorTy : Ixon.Expr := .all (arrows (.ref 0 #[]) (.recur 0 #[])) (.recur 0 #[])
  let ctor : Ixon.Constructor :=
    { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 1, typ := ctorTy }
  let ind : Ixon.Inductive :=
    { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0, ctors := #[ctor] }
  let block : Ixon.Constant := {
    info := .muts #[.indc ind], sharing := #[], refs := #[a], univs := #[.succ .zero],
    binders := #[{ shared := false, index := 1, variant := 0, nodes := Array.replicate (n + 1) never }] }
  let blockA := Address.blake3 (Ixon.ser block)
  let tC : Ixon.Constant := ⟨.iPrj ⟨0, blockA⟩, #[], #[], #[], #[]⟩
  let tA := Address.blake3 (Ixon.ser tC)
  let mkC : Ixon.Constant := ⟨.cPrj ⟨0, 0, blockA⟩, #[], #[], #[], #[]⟩
  let mkA := Address.blake3 (Ixon.ser mkC)
  -- the recursor: refs [T, mk, A], levels [u]
  let t : Ixon.Expr := .ref 0 #[]
  let dom : Ixon.Expr := .ref 2 #[]
  let d := arrows dom t
  let applied (f : Ixon.Expr) : Ixon.Expr :=
    (List.range n).foldl (fun acc j => Ixon.Expr.app acc (.var (n - 1 - j).toUInt64)) f
  let ihDom := arrows dom (.app (.var (n + 1).toUInt64) (applied (.var n.toUInt64)))
  let motiveTy : Ixon.Expr := .all t (.sort 0)
  let minorTy : Ixon.Expr := .all d (.all ihDom (.app (.var 2) (.app (.ref 1 #[]) (.var 1))))
  let typ : Ixon.Expr := .all motiveTy (.all minorTy (.all t (.app (.var 2) (.var 0))))
  let call : Ixon.Expr :=
    .app (.app (.app (.recur 0 #[0]) (.var (n + 2).toUInt64)) (.var (n + 1).toUInt64))
      (applied (.var n.toUInt64))
  let ih : Ixon.Expr := (List.range n).foldl (fun acc _ => Ixon.Expr.lam dom acc) call
  let rhs : Ixon.Expr := .lam motiveTy (.lam minorTy (.lam d (.app (.app (.var 1) (.var 0)) ih)))
  let minorNodes := #[pw] ++ Array.replicate n never ++ #[pw] ++ Array.replicate n pw
  let typNodes := #[pw, never, pw] ++ minorNodes ++ #[pw]
  let ruleNodes := #[pw, never, pw] ++ minorNodes ++ #[pw] ++ Array.replicate n never ++
    Array.replicate n pw
  let recr : Ixon.Recursor := {
    k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0, motives := 1, minors := 1,
    typ, rules := #[{ fields := 1, rhs }] }
  let recC : Ixon.Constant := {
    info := .recr recr, sharing := #[], refs := #[tA, mkA, a], univs := #[.var 0],
    binders := #[{ shared := false, index := 0, variant := 0, nodes := typNodes },
                 { shared := false, index := 1, variant := 0, nodes := ruleNodes }] }
  ((blockA, block), (tA, tC), (mkA, mkC), (Address.blake3 (Ixon.ser recC), recC))

/-- A case line of the fixture report. -/
structure Row where
  label : String
  expected : String
  got : String
  deriving Inhabited

def Row.ok (r : Row) : Bool := r.got.startsWith r.expected

def rowOf (label expected : String) (o : Outcome) : Row :=
  { label, expected, got := o.verdict.text }

/-- What the certified kernel does with `records` on top of `env`: per record, installed or
why not. -/
def kernelVerdicts (env : Ixon.Env) (records : Array (Address × Ixon.Constant)) :
    Except String (IxVM.PwHints.KernelEnv × Array (Address × String)) := do
  let some b := env.roleBinding | throw "no role binding"
  let mut support : Array (Address × Ixon.Constant) := #[]
  let mine : Std.HashSet Address := records.foldl (fun s (a, _) => s.insert a) {}
  for (a, lc) in env.consts do
    unless mine.contains a do
      if let some c := lc.get? then support := support.push (a, c)
  let view : IxVM.PwHints.View := {
    records, support, blobs := env.blobs, hints := env.anonHints, table := some b.bytes }
  let k ← IxVM.PwHints.KernelEnv.ofView view (lenient := false)
  let out := records.map fun (a, _) =>
    match k.failures.find? (·.1 == a) with
    | some (_, why) => (a, s!"refused: {why}")
    | none => (a, "installed")
  return (k, out)

/-- The fixtures of a dead `let` in a stored recursor, on the recursor `t` (a family with a
recursive constructor last) and a theorem `thm` whose proof reduces through it. -/
def letFixtures (h : Host) (cp : Corpus) (t : Target) (thm : Option (Address × Ixon.Constant)) :
    IO (Array Row) := do
  let x ← IO.ofExcept (XRec.ofConstant t.c t.r 200000)
  let np := x.r.params.toNat
  let n := x.r.minors.toNat
  let j := x.rules.size - 1
  let (nfU, rhs) := x.rules[j]!
  let some (bs, body) := rhs.peelLams (np + 1 + n + nfU.toNat)
    | throw (IO.userError "the fixture rule has an unexpected shape")
  let (hd, args) := body.spine
  let some r0 := (AE.sites AE.isRef x.typ #[])[0]? | throw (IO.userError "no constant in the type")
  let (x1, fresh) := x.freshLevel 0
  let mode : Ixon.LetMode := .value .many
  -- junk: a sort applied to a constant, and that constant applied to itself
  let junkT : AE := .app (.sort 0) r0
  let junkV : AE := .app r0 r0
  let withRule (x' : XRec) (rhs' : AE) : XRec := { x' with rules := x'.rules.set! j (nfU, rhs') }
  let variants : Array (String × String × XRec) := #[
    ("rule: dead let at the top, ill-typed type and value", "accepted",
      withRule x (.letE true mode junkT junkV (rhs.lift 1 0))),
    ("rule: dead let under the binders, ill-typed, naming bound variables", "accepted",
      withRule x (AE.mkLams bs (.letE true mode (.app (.var 1) (.var 0)) (.app (.var 0) (.var 0))
        (body.lift 1 0)))),
    ("rule: used let whose value is the minor premise, ill-typed annotation", "accepted",
      withRule x (AE.mkLams bs (.letE true mode junkT hd
        (AE.mkApp (.var 0) (args.map (·.lift 1 0)))))),
    ("rule: used let whose value is the motive", "rejected",
      withRule x (AE.mkLams bs (.letE true mode junkT (.var (nfU.toNat + n).toUInt64)
        (AE.mkApp (.var 0) (args.map (·.lift 1 0)))))),
    ("type: dead let at the top, ill-typed", "rejected",
      { x with typ := .letE true mode junkT junkV (x.typ.lift 1 0) }),
    ("type: dead let at the top, well-typed", "rejected",
      { x1 with typ := .letE true mode (.sort fresh) (.sort 0) (x.typ.lift 1 0) }),
    ("rule: dead let around the last argument (an inductive hypothesis), ill-typed", "accepted",
      withRule x (AE.mkLams bs (AE.mkApp hd (args.set! (args.size - 1)
        (.letE true mode junkT junkV (args.back!.lift 1 0))))))]
  let mut rows : Array Row := #[]
  let mut built : Array (Address × Ixon.Constant) := #[]
  for ((label, expected, xv), i) in variants.zipIdx do
    let c := xv.toConstant
    let a := Address.blake3 (Ixon.ser c)
    built := built.push (a, c)
    let o ← checkOne h cp s!"let{i}" s!"rg{i}x" a c #[(a, c)] (expected == "accepted")
    rows := rows.push (rowOf label expected o)
  -- a dead let in a binder domain of the type: ill-typed, then well-typed
  if let some (tbs, concl) := x.typ.peelAlls (np + 1) then
    let (dm, mot) := tbs[np]!
    let inDomain (x' : XRec) (ty v : AE) : XRec :=
      { x' with typ := AE.mkAlls (tbs.set! np (dm, .letE true mode ty v (mot.lift 1 0))) concl }
    let inResult : XRec := match mot with
      | .all d0 t0 b0 =>
        { x1 with typ := AE.mkAlls (tbs.set! np (dm,
            .all d0 t0 (.letE true mode (.sort fresh) (.sort 0) (b0.lift 1 0)))) concl }
      | _ => x1
    for ((label, expected, xv), i) in #[
        ("type: dead let at the top of the motive's domain, ill-typed", "rejected",
          inDomain x junkT junkV),
        ("type: dead let at the top of the motive's domain, well-typed", "rejected",
          inDomain x1 (.sort fresh) (.sort 0)),
        ("type: dead let in the motive's result, well-typed", "accepted", inResult)].zipIdx do
      let c := xv.toConstant
      let a := Address.blake3 (Ixon.ser c)
      let o ← checkOne h cp s!"letd{i}" s!"rg{i}x" a c #[(a, c)] (expected == "accepted")
      rows := rows.push (rowOf label expected o)
  -- reduction through the stored rule: the theorem at the stored recursor, at the two
  -- dead-let records, and at a record whose last rule returns the first minor premise
  if let some (_, tc) := thm then
    unless tc.refs.contains t.addr do
      throw (IO.userError "the theorem does not name the recursor")
    let wrong := (withRule x (AE.mkLams bs (.var (nfU.toNat + n - 1).toUInt64))).toConstant
    let wrongA := Address.blake3 (Ixon.ser wrong)
    let cases : Array (String × String × Option (Address × Ixon.Constant)) := #[
      ("theorem reducing through the stored recursor", "accepted", none),
      ("theorem reducing through the record with a dead let at the top of its rule", "accepted",
        built[0]?),
      ("theorem reducing through the record with a dead let under its rule's binders", "accepted",
        built[1]?),
      ("theorem reducing through the record with a dead let around an inductive hypothesis", "",
        built[6]?),
      ("theorem reducing through a record whose rule returns another minor premise", "rejected",
        some (wrongA, wrong))]
    for ((label, expected, alt), i) in cases.zipIdx do
      let (c, extra) := match alt with
        | some (ra, rc) => (repoint tc t.addr ra, #[(ra, rc)])
        | none => (tc, #[])
      let a := Address.blake3 (Ixon.ser c)
      let o ← checkOne h cp s!"thm{i}" s!"rg{i}x" a c (extra.push (a, c)) (expected == "accepted")
      rows := rows.push (rowOf label expected o)
  return rows

/-- The fixture of a reflexive field of Π-depth `n`: the circuit on the block, the
constructor and the recursor, and the certified kernel on the same records. -/
def deepFixture (h : Host) (cp : Corpus) (nat : Address) (n : Nat) : IO (Array Row) := do
  let ((blockA, block), (tA, tC), (mkA, mkC), (recA, recC)) := deepRecords nat n
  let extra := #[(blockA, block), (tA, tC), (mkA, mkC), (recA, recC)]
  let mut rows : Array Row := #[]
  let o ← checkOne h cp s!"deep{n}r" "rg0x" recA recC extra true (some "KernelCheck::nat_rec_check")
  rows := rows.push (rowOf s!"depth {n}: the recursor record, circuit" "accepted" o)
  let o ← checkOne h cp s!"deep{n}t" "rg1x" tA tC extra true
  rows := rows.push (rowOf s!"depth {n}: the family (type projection, walked), circuit" "accepted" o)
  let o ← checkOne h cp s!"deep{n}c" "rg2x" mkA mkC extra true
  rows := rows.push (rowOf s!"depth {n}: the constructor (projection, walked), circuit" "accepted" o)
  match kernelVerdicts cp.env extra with
  | .error e => rows := rows.push { label := s!"depth {n}: certified kernel", expected := "", got := e }
  | .ok (k, vs) =>
    for (a, v) in vs do
      if a == blockA then
        rows := rows.push { label := s!"depth {n}: certified kernel, block", expected := "", got := v }
    let held := match (k.setup.cx.memberKey (.member recA 0)).toOption with
      | some key =>
        (match k.fe.find? key with
          | some (.recInfo ..) => "installed"
          | _ => "not installed")
      | none => "no key"
    rows := rows.push { label := s!"depth {n}: certified kernel, recursor", expected := "", got := held }
  return rows

/-- The fixture families (`Tests.Ix.IxVM.RecGenDefs`), compiled by the certified compiler:
each stored recursor, the certified kernel's generated recursor for it, their difference,
every edit of the stored one; then the dead-`let` and the deep-reflexive fixtures. -/
def runSynthetic (leanEnv : Lean.Environment) (h : Host) : IO UInt32 := do
  let fams := Tests.Ix.IxVM.RecGenDefs.families
  let recNames := fams.map Lean.mkRecName
  let names := recNames ++ Tests.Ix.IxVM.RecGenDefs.reductions
  let missing := names.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-recgen] not in the environment: {missing}"
    return 1
  let workers ← envNat "IX_RECGEN_WORKERS" 32
  let cap ← envNat "IX_RECGEN_CAP" 200000
  let env ← loadSharedIxonEnv names.toArray leanEnv
  let cp ← Corpus.ofEnv env
  let addrOf (n : Lean.Name) : Option Address := env.getAddr? (Ix.Name.fromLeanName n)
  let targetAt (a : Address) : Option Target := cp.targets.find? (·.addr == a)
  let mine := recNames.toArray.filterMap fun n => (addrOf n).bind targetAt
  IO.println s!"[ixvm-recgen] synthetic: {mine.size} of {recNames.length} fixture recursors are \
    standalone records; the environment holds {cp.targets.size} standalone recursors"
  let mut summary : Array String := #[]
  let mut bad := 0
  -- every standalone recursor of the compiled environment, as stored
  let honest ← parFor workers cp.targets.size fun i => do
    let t := cp.targets[i]!
    checkOne h cp s!"s{i}" s!"rg{i}x" t.addr t.c #[] true (some "KernelCheck::nat_rec_check")
  let honestBad := (cp.targets.zip honest).filter fun (_, o) => match o.verdict with
    | .accepted true => false
    | _ => true
  summary := summary.push s!"stored recursor records of the compiled environment: \
    {cp.targets.size} run, {cp.targets.size - honestBad.size} accepted"
  for (t, o) in honestBad do
    bad := bad + 1
    summary := summary.push s!"  NOT ACCEPTED {t.name}: {o.verdict.text}"
  -- the certified kernel's generated recursors
  let allRecords : Array (Address × Ixon.Constant) := env.consts.fold (init := #[]) fun out a lc =>
    match lc.get? with
    | some c => out.push (a, c)
    | none => out
  let kernel := kernelVerdicts env allRecords
  let roles : Std.HashMap Ix.Kernel.Role Address := match env.roleBinding with
    | some b => match Ix.Kernel.RoleTable.ofBytes b.bytes with
      | some table => table.bound.foldl (fun m (r, a) => m.insert r a) {}
      | none => {}
    | none => {}
  summary := summary.push ""
  summary := summary.push "fixture\tstrata\tstored\tkernel-generated\tdifference"
  match kernel with
  | .error e =>
    bad := bad + 1
    summary := summary.push s!"the certified kernel's environment was not built: {e}"
  | .ok (k, _) =>
    let gen ← parFor workers mine.size fun i => do
      let t := mine[i]!
      match ixcRecord k roles t.addr t.r with
      | .error e => pure (s!"none ({e})", "")
      | .ok c =>
        let a := Address.blake3 (Ixon.ser c)
        let o ← checkOne h cp s!"k{i}" s!"rg{i}x" a c #[(a, c)] true
          (some "KernelCheck::nat_rec_check")
        let diff := match XRec.ofConstant t.c t.r cap, XRec.ofConstant c
            (match c.info with | .recr r => r | _ => t.r) cap with
          | .ok x, .ok y =>
            let ds := compareRecords x y
            if ds.isEmpty then "identical" else " ;; ".intercalate ds.toList
          | _, _ => "not compared"
        let note ← wrapperNote h cp s!"kw{i}" s!"rg{i}x" a c o
        pure (o.verdict.text, diff ++ note)
    for (t, i) in mine.zipIdx do
      let stored := match (cp.targets.zip honest).find? (·.1.addr == t.addr) with
        | some (_, o) => o.verdict.text
        | none => "?"
      let (g, diff) := gen[i]!
      unless g == "accepted" do bad := bad + 1
      summary := summary.push
        s!"{t.name}\t{",".intercalate t.shape.tags.toList}\t{stored}\t{g}\t{diff}"
  -- every edit of every fixture recursor
  let muts ← parFor workers mine.size fun i => do
    let t := mine[i]!
    try mutateOne h cp i t.name t.c t.r cap 16 12 77
    catch e => pure ({ skipped := some s!"error: {e}" } : MutOutcome)
  let mut nMut := 0
  let mut nRej := 0
  let mut lines : Array String := #[tsvLine ["name", "edit", "address", "verdict"]]
  summary := summary.push ""
  summary := summary.push "fixture\tedits\trejected\taccepted\tno-verdict"
  IO.FS.createDirAll (h.dir / "synthetic-accepted")
  for (t, i) in mine.zipIdx do
    let o := muts[i]!
    if let some why := o.skipped then
      bad := bad + 1
      summary := summary.push s!"{t.name}\tNOT EDITED: {why} ({o.control.verdict.text})"
      continue
    let mut rej := 0
    let mut acc := 0
    let mut unres := 0
    let mut accWrong := 0
    for (m, kk) in o.results.zipIdx do
      lines := lines.push (tsvLine [t.name, m.op, toString m.addr, m.verdict.text])
      match m.verdict with
      | .rejected _ => rej := rej + 1
      | .accepted _ =>
        acc := acc + 1
        let (orig, alt, same) := describeAccepted o.expanded m cap
        unless same do accWrong := accWrong + 1
        IO.FS.writeFile (h.dir / "synthetic-accepted" / s!"{i}-{kk}.txt")
          s!"name: {t.name}\nedit: {m.op}\naltered record: {m.addr}\n\
            equal to the control once every let is expanded: {same}\n\
            altered bytes: {hexOf (Ixon.ser m.record)}\n\n== control ==\n{orig}\n\n\
            == altered ==\n{alt}\n"
        summary := summary.push s!"  ACCEPTED EDIT {t.name}: {m.op} ({i}-{kk}); equal to the \
          control once every let is expanded: {same}"
      | v =>
        unres := unres + 1
        summary := summary.push s!"  NO VERDICT {t.name}: {m.op}: {v.text}"
    nMut := nMut + o.results.size
    nRej := nRej + rej
    bad := bad + accWrong + unres
    summary := summary.push s!"{t.name}\t{o.results.size}\t{rej}\t{acc}\t{unres}"
  summary := summary.push s!"edits of fixture recursors: {nMut} run, {nRej} rejected"
  IO.FS.writeFile (h.dir / "synthetic-edits.tsv") ("\n".intercalate lines.toList ++ "\n")
  -- the dead-`let` fixtures and the deep reflexive field
  summary := summary.push ""
  summary := summary.push "fixture case\texpected\tgot"
  let d0 := (addrOf ``Tests.Ix.IxVM.RecGenDefs.D0I0.rec).bind targetAt
  let thm := (addrOf ``Tests.Ix.IxVM.RecGenDefs.d0i0_iota).bind fun a =>
    (env.getConst? a).map fun c => (a, c)
  let mut rows : Array Row := #[]
  match d0 with
  | some t =>
    try rows := rows ++ (← letFixtures h cp t thm)
    catch e => rows := rows.push { label := "dead-let fixtures", expected := "built", got := s!"{e}" }
  | none => rows := rows.push { label := "dead-let fixtures", expected := "built", got := "no D0I0.rec" }
  let nat? := match env.roleBinding with
    | some b => (Ix.Kernel.RoleTable.ofBytes b.bytes).bind (·.addressOf? .nat)
    | none => none
  match nat? with
  | some nat =>
    for n in [1, 3, 1000, 1023, 1024, 1100] do
      try rows := rows ++ (← deepFixture h cp nat n)
      catch e =>
        rows := rows.push { label := s!"depth {n}", expected := "built", got := s!"{e}" }
  | none => rows := rows.push { label := "deep reflexive field", expected := "built", got := "no Nat" }
  for r in rows do
    unless r.ok do bad := bad + 1
    summary := summary.push s!"{r.label}\t{r.expected}\t{r.got}"
  IO.FS.writeFile (h.dir / "synthetic-summary.txt") ("\n".intercalate summary.toList ++ "\n")
  for l in summary do IO.println l
  return if bad == 0 then 0 else 1

/-- The certified kernel's generated recursor on real families: for a stratified sample of
the corpus's recursors whose dependency closure has at most `IX_RECGEN_CLOSURE` records, the
kernel installs the closure, its generated recursor is encoded as a record and claimed
alone, and it is compared with the stored record. -/
def runKernelGen (cp : Corpus) (h : Host) : IO UInt32 := do
  let total ← envNat "IX_RECGEN_LIMIT" 120
  let perTag ← envNat "IX_RECGEN_PER_TAG" 8
  let seed ← envNat "IX_RECGEN_SEED" 1
  let workers ← envNat "IX_RECGEN_WORKERS" 12
  let maxClosure ← envNat "IX_RECGEN_CLOSURE" 1500
  let cap ← envNat "IX_RECGEN_CAP" 200000
  let some binding := cp.env.roleBinding | throw (IO.userError "no role binding")
  let roles : Std.HashMap Ix.Kernel.Role Address :=
    match Ix.Kernel.RoleTable.ofBytes binding.bytes with
    | some table => table.bound.foldl (fun m (r, a) => m.insert r a) {}
    | none => {}
  let t0 ← IO.monoMsNow
  let sizes ← parFor 48 cp.targets.size fun i => do
    let t := cp.targets[i]!
    pure ((closureTo cp.env #[t.addr] 1000000 maxClosure).map (·.size))
  let small := (cp.targets.zip sizes).filterMap fun (t, s) => s.map fun _ => t
  let named := match (← IO.getEnv "IX_RECGEN_NAME") with
    | some ns => small.filter fun t => (ns.splitOn ",").any fun n => hasSub t.name n
    | none => small
  let dump : List String := match (← IO.getEnv "IX_RECGEN_DUMP") with
    | some ns => ns.splitOn ","
    | none => []
  let chosen := stratified named perTag total seed
  IO.println s!"[ixvm-recgen] kernel-generated: {small.size} of {cp.targets.size} recursors have a \
    closure of at most {maxClosure} records; {chosen.size} sampled ({(← IO.monoMsNow) - t0} ms)"
  let recOf : Std.HashMap Address (Array Address) := cp.targets.foldl (init := {}) fun m t =>
    match t.parent with
    | .ok p => m.insert p.blockAddr ((m.getD p.blockAddr #[]).push t.addr)
    | .error _ => m
  let results ← parFor workers chosen.size fun i => do
    let t := chosen[i]!
    let t1 ← IO.monoMsNow
    -- the closure, with the recursor of every native family in it: the kernel installs an
    -- inductive block only with its recursor record in the input
    let mut roots : Array Address := #[t.addr]
    let mut scope : Array Address := #[]
    for _ in [0:8] do
      let some s := closureTo cp.env roots 1000000 (maxClosure * 4)
        | break
      scope := s
      let held : Std.HashSet Address := s.foldl (·.insert ·) {}
      let more := s.foldl (init := (#[] : Array Address)) fun acc a =>
        (recOf.getD a #[]).foldl (fun acc r => if held.contains r then acc else acc.push r) acc
      if more.isEmpty then break
      roots := roots ++ more
    if scope.isEmpty then return ("no closure", "", 0, 0)
    let records := scope.filterMap fun a => (cp.env.getConst? a).map fun c => (a, c)
    let view : IxVM.PwHints.View := {
      records, blobs := cp.env.blobs, hints := cp.env.anonHints, table := some binding.bytes }
    match IxVM.PwHints.KernelEnv.ofView view with
    | .error e => pure (s!"kernel environment not built: {e}", "", records.size, 0)
    | .ok k =>
      match ixcRecord k roles t.addr t.r with
      | .error e =>
        let blockOf : Option Address := match t.parent with
          | .ok p => some p.blockAddr
          | .error _ => none
        let why := match k.failures.find? (fun (a, _) => a == t.addr || some a == blockOf) with
          | some (_, w) => s!"; the kernel refused the family: {w}"
          | none => ""
        pure (s!"none ({e}{why})", "", records.size, (← IO.monoMsNow) - t1)
      | .ok c =>
        let a := Address.blake3 (Ixon.ser c)
        let o ← checkOne h cp s!"g{i}" s!"rg{i}x" a c #[(a, c)] true
          (some "KernelCheck::nat_rec_check")
        let diff := match XRec.ofConstant t.c t.r cap, XRec.ofConstant c
            (match c.info with | .recr r => r | _ => t.r) cap with
          | .ok x, .ok y =>
            let ds := compareRecords x y
            if ds.isEmpty then "identical" else " ;; ".intercalate ds.toList
          | _, _ => "not compared"
        if dump.any (fun n => hasSub t.name n) then
          let text := match XRec.ofConstant t.c t.r cap, XRec.ofConstant c
              (match c.info with | .recr r => r | _ => t.r) cap with
            | .ok x, .ok y => s!"== stored ==\n{x.fmt}\n\n== kernel-generated ==\n{y.fmt}\n"
            | _, _ => "not expanded"
          IO.FS.writeFile (h.dir / s!"kernelgen-dump-{i}.txt") s!"name: {t.name}\n{text}"
        let note ← wrapperNote h cp s!"gw{i}" s!"rg{i}x" a c o
        pure (o.verdict.text, diff ++ note, records.size, (← IO.monoMsNow) - t1)
  let mut lines : Array String := #[tsvLine ["name", "address", "closure", "ms", "strata",
    "kernel-generated record", "difference from the stored record"]]
  let mut accepted := 0
  let mut identical := 0
  let mut none_ := 0
  let mut rows : Array (Array String × Bool) := #[]
  let mut notAccepted : Array String := #[]
  for (t, i) in chosen.zipIdx do
    let (v, diff, n, ms) := results[i]!
    lines := lines.push (tsvLine [t.name, toString t.addr, toString n, toString ms,
      ",".intercalate t.shape.tags.toList, v, diff])
    if v == "accepted" then
      accepted := accepted + 1
      if diff.startsWith "identical" then identical := identical + 1
      rows := rows.push (t.shape.tags, true)
    else if v.startsWith "none" || v.startsWith "kernel" || v.startsWith "no closure" then
      none_ := none_ + 1
    else
      rows := rows.push (t.shape.tags, false)
      notAccepted := notAccepted.push s!"{t.name}\t{t.addr}\t{v}\t{diff}"
  IO.FS.writeFile (h.dir / "kernelgen.tsv") ("\n".intercalate lines.toList ++ "\n")
  let mut summary : Array String := #[
    s!"recursors with a closure of at most {maxClosure} records: {small.size} of {cp.targets.size}",
    s!"sampled: {chosen.size}",
    s!"kernel-generated record obtained and run: {chosen.size - none_}",
    s!"accepted through nat_rec_check: {accepted}",
    s!"of those, structurally identical to the stored record: {identical}",
    s!"no kernel-generated record (the kernel did not install the family): {none_}",
    s!"NOT ACCEPTED: {notAccepted.size}",
    s!"elapsed ms: {(← IO.monoMsNow) - t0}",
    "", "stratum\trun\taccepted"]
  for (tag, n, a) in tally rows do summary := summary.push s!"{tag}\t{n}\t{a}"
  summary := summary.push ""
  summary := summary.push "NOT ACCEPTED:"
  for l in notAccepted do summary := summary.push l
  IO.FS.writeFile (h.dir / "kernelgen-summary.txt") ("\n".intercalate summary.toList ++ "\n")
  for l in summary do IO.println l
  return if notAccepted.isEmpty then 0 else 1

def unhex (s : String) : ByteArray := Id.run do
  let val (c : Char) : UInt8 :=
    if c.isDigit then (c.toNat - 48).toUInt8 else (c.toNat - 87).toUInt8
  let cs := s.toList.toArray
  let mut out : ByteArray := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (val cs[2 * i]! * 16 + val cs[2 * i + 1]!)
  return out

/-- Decide the accepted edits saved by an earlier run (`IX_RECGEN_DIR`, the files of a
`<label>-accepted` directory): each altered record is read back from its bytes, expanded,
and compared with the expansion of the stored record it was made from, as terms and once
every `let` is expanded. -/
def runClassify (cp : Corpus) (h : Host) : IO UInt32 := do
  let some dir ← IO.getEnv "IX_RECGEN_DIR" | throw (IO.userError "IX_RECGEN_DIR is not set")
  let cap ← envNat "IX_RECGEN_CAP" 400000
  let byAddr : Std.HashMap String Target :=
    cp.targets.foldl (fun m t => m.insert (toString t.addr) t) {}
  let mut lines : Array String := #[tsvLine ["file", "name", "edit", "altered record",
    "equal once lets are expanded", "first difference before expansion (control | altered)"]]
  let mut same := 0
  let mut different := 0
  let mut broken := 0
  let entries := (← (System.FilePath.mk dir).readDir).qsort fun a b => a.fileName < b.fileName
  for entry in entries do
    let text ← IO.FS.readFile entry.path
    let field (key : String) : String :=
      ((text.splitOn "\n").find? (·.startsWith key)).map (fun l =>
        key.intercalate ((l.splitOn key).drop 1)) |>.getD ""
    let name := field "name: "
    let edit := field "edit: "
    let stored := field "stored record: "
    let bytes := unhex (field "altered bytes: ")
    let altered := Address.blake3 bytes
    let verdict : Except String (Bool × String) := do
      let some t := byAddr[stored]? | throw "the stored record is not in the corpus"
      let c ← Ixon.deConstantExact bytes
      let .recr r := c.info | throw "the altered record is not a recursor"
      let x ← XRec.ofConstant t.c t.r cap
      let y ← XRec.ofConstant c r cap
      let ds := compareRecords x y
      pure (x.zetaEq y, " ;; ".intercalate ds.toList)
    match verdict with
    | .ok (eq, diff) =>
      if eq then same := same + 1 else different := different + 1
      lines := lines.push (tsvLine [entry.fileName, name, edit, toString altered, toString eq, diff])
    | .error e =>
      broken := broken + 1
      lines := lines.push (tsvLine [entry.fileName, name, edit, toString altered, "?", e])
  IO.FS.writeFile (h.dir / "classify.tsv") ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"[ixvm-recgen] classify {dir}: {entries.size} accepted edits; {same} equal to their \
    control once every let is expanded, {different} not, {broken} not read"
  for l in lines do IO.println l
  return if different == 0 && broken == 0 then 0 else 1

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let mode := (← IO.getEnv "IX_RECGEN_MODE").getD "honest"
  let h ← Host.make
  let corpus : IO Corpus := do
    let some path ← IO.getEnv "IX_RECGEN_IXE"
      | throw (IO.userError "set IX_RECGEN_IXE to an .ixe file")
    Corpus.load path
  match mode with
  | "honest" => runHonest (← corpus) h
  | "mutate" => runMutate (← corpus) h
  | "synthetic" => runSynthetic leanEnv h
  | "kernelgen" => runKernelGen (← corpus) h
  | "classify" => runClassify (← corpus) h
  | other =>
    IO.eprintln s!"[ixvm-recgen] unknown mode {other}"
    return 1

end Tests.Ix.IxVM.RecGen
