module

public import Ix.LeanIngress
public import Ix.KernelCheck.Step
public import Ix.Compile.BinderData
public import Ix.Compile.Parallel
public import Ix.Compile.FrontEnd
public import Ix.CompileM

public section

/-!
# The compiler's binder-data annotator: IxC's pass over the Lean source

`ix compile` writes every block record's binder-data section while it builds
the record, before the record is hashed (`Ix.CompileM.withBinderSection`). This
module is the annotator it runs there. The data are IxC's: its annotation pass
(`annotateBodyI`, its telescope loops `annotatePisI`/`annotateLamsI`) writes at
every binder the zero-ness of the codomain sort, by `annotPwPiI`/`annotPwLamI`
on the annotated opened body; nothing here infers anything itself.

**The environment.** Before the compile, IxC ingests the compile's own input
in Source mode (`Ix.LeanIngress`: every constant keyed by its Lean name, or its
role's key) and installs it with phase A of its fold
(`annotDeclStepWithUserAxioms`, at the committed bundle's evidence), once, in
dependency order (`install`). Unsafe and partial groups go through the typing
tier; a declaration that fails is retried after them. The installed
environment and IxC's core over it are marked persistent: every worker reads
them, none writes them.

**The walk.** For a block record, each root is walked beside its member's
Source term (the Lean source converted as the ingress converts it): the
record's tree gives the numbering (its `lam`, `all` and `share` nodes in
pre-order, a share's entry a block of its own, one variant per distinct node
list), the Source term gives the leaves. The walk is IxC's pass over the pair:
a run of binders of one kind is opened in bulk, its leaf annotated, the datum
computed once at the leaf (every binder of the run has it, since the
zero-ness of `imax u v` is that of `v`) and the run closed with one
`abstractRangeC`; a `let` is ζ-reduced, its type and value annotated first; a
share is walked once per context of the variables it can name. Each record's
caches start empty and are dropped with it.

**Unsafe and partial records** carry the undecided section
(`Ix.CompileM.undecidedSection`). So does a record whose sources the annotator
cannot find or align, and every binder whose datum IxC's function cannot
compute, or under which something is undecided, is the undecided node.

The annotator is a pure function of its input (the installed environment, the
record and its sources). It is not trusted: the compiler keeps its section only
in canonical form (`Ix.CompileM.sectionAdmissible`), and a checker validates
every datum it reads.
-/

namespace Ix.Compile.KernelAnnotate

open Ix.Kernel (FEnv PropWhen BinderMeta)
open Ix.Kernel.Reader (CName CExpr CDecl ReadError State)
open Ix.LeanIngress
open IxVM.PwHints (Node Block)

abbrev KExpr := Ix.Kernel.Expr .source
abbrev CM := Ix.Kernel.Cached.CheckCM .source

/-! ## The installed environment -/

/-- IxC's environment of a compile's input, and what installing it found. -/
structure Installed where
  fe : FEnv .source
  core : Ix.Kernel.Cached.CoreFnsI .source
  /-- the compile's input, for the members' sources -/
  env : Ix.Environment
  installed : Nat := 0
  /-- the groups or declarations the ingress or the install refused, and why -/
  failures : Array (String × String) := #[]
  /-- the phases' times (ms) -/
  times : Array (String × Nat) := #[]

/-- The index of `env` (the newest constant of a key wins), by a loop. -/
def reindex (env : Ix.Kernel.Env .source) : FEnv .source := Id.run do
  let n := env.consts.length
  let mut idx : Std.HashMap (Ix.Kernel.Key .source) (Nat × Ix.Kernel.ConstantInfo .source) :=
    Std.HashMap.emptyWithCapacity n
  let mut i := n
  for ci in env.consts do
    i := i - 1
    unless idx.contains ci.name do idx := idx.insert ci.name (i, ci)
  return ⟨env, idx, n⟩

/-- One declaration through phase A of IxC's fold; on a failure, the environment
as it was. -/
def step (ev : Ix.Kernel.Evidences .source) (fe : FEnv .source) (pos : Nat)
    (d : Ix.Kernel.Declaration .source) :
    FEnv .source × Nat × Option (Ix.Kernel.CheckError .source) :=
  let before := fe.env
  match Ix.Kernel.Cached.annotDeclStepWithUserAxioms .verified ev (pos, fe, #[]) d {} with
  | .ok ((pos', fe', _), _) => (fe', pos', none)
  | .error (e, _) => (reindex before, pos + 1, some e)

def readErrorString : ReadError → String
  | .malformed m => s!"malformed: {m}"
  | .declined m => s!"declined: {m}"

/-- The name a declaration is reported under. -/
def declName (d : Ix.Kernel.Declaration .source) : String :=
  match d.names.head? with
  | some k => toString k
  | none => "?"

private instance : Nonempty (FEnv .source) := ⟨Ix.Kernel.mkFEnv Ix.Kernel.Env.empty⟩

private instance : Nonempty (Ix.Kernel.Cached.CoreFnsI .source) :=
  ⟨Ix.Kernel.Cached.coreKnotI .verified (Ix.Kernel.mkFEnv Ix.Kernel.Env.empty) 0⟩

/-- **Install the compile's input** in Source mode, phase A only, and mark the
environment and IxC's core over it persistent. -/
def install (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (workers : Nat := 32) :
    IO (Except String Installed) := do
  let t0 ← IO.monoMsNow
  let pre ← match (Ix.Kernel.Reader.builtinPrelude : Except String (Ix.Kernel.Reader.Prelude .source)) with
    | .ok p => pure p
    | .error e => return .error s!"binder data: the prelude does not read: {e}"
  let groups ← IO.lazyPure fun _ => groupsOf env blocks
  let converted ← IO.lazyPure fun _ => Ix.Compile.Parallel.map (max workers 1) convert groups
  let g ← IO.lazyPure fun _ => graphOf blocks groups converted
  let tierConv : Array (Option (Except ReadError (Ix.Kernel.Tier.TierDecl .source))) ←
    IO.lazyPure fun _ => groups.map fun grp => if isTierGroup grp then some (convertTier grp) else none
  let gT : Graph := { g with converted := g.converted.zipIdx.map fun (c, i) =>
    if (tierConv[i]!).isSome then .ok (.definitions #[]) else c }
  let sched ← IO.lazyPure fun _ => scheduleOf gT
  let t1 ← IO.monoMsNow
  let groupName (gi : Nat) : String := match (groups[gi]!.names)[0]? with
    | some n => n.pretty
    | none => "?"
  let mut st : State .source := pre.state
  let mut lowered : Array (CDecl .source) := #[]
  let mut tiers : Array (Nat × Ix.Kernel.Tier.TierDecl .source) := #[]
  let mut failures : Array (String × String) := #[]
  for (gi, c) in sched do
    if let some t := tierConv[gi]! then
      match t with
      | .ok d => tiers := tiers.push (gi, d)
      | .error e => failures := failures.push (groupName gi, readErrorString e)
      continue
    match c >>= fun c => lower st c with
    | .ok r =>
      st := st.commit r
      lowered := lowered ++ r.decls.map canonDecl
    | .error e => failures := failures.push (groupName gi, readErrorString e)
  let prepared := Ix.Kernel.Frontend.preparePrelude pre.ix lowered
  let ev := Ix.RoleEvidence.bundleEvidence ()
  let t2 ← IO.monoMsNow
  let mut fe : FEnv .source := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  let mut pos := 0
  let mut ok := 0
  let mut retry : Array (CDecl .source) := #[]
  for d in prepared do
    let (fe', pos', err) := step ev fe pos d
    fe := fe'
    pos := pos'
    match err with
    | none => ok := ok + 1
    | some _ => retry := retry.push d
  -- the typing tier, then the declarations that failed before it (those that
  -- reference a tier constant)
  let logical := fe
  for (gi, d) in Benchmarks.Kernel.CheckIxeStep.stageDeferred (·.2) tiers do
    let (fe', err) := Benchmarks.Kernel.CheckIxeStep.stepTier logical fe d
    fe := fe'
    match err with
    | none => ok := ok + 1
    | some e =>
      let why := (Benchmarks.Kernel.CheckIxeStep.tierOutcome d.safety e).2
      failures := failures.push (groupName gi, why)
  for d in retry do
    let (fe', pos', err) := step ev fe pos d
    fe := fe'
    pos := pos'
    match err with
    | none => ok := ok + 1
    | some e =>
      let why := (Benchmarks.Kernel.CheckIxeStep.checkOutcome e).2
      failures := failures.push (declName d, why)
  let t3 ← IO.monoMsNow
  let shared ← (unsafe Runtime.markPersistent fe : BaseIO (FEnv .source))
  let core ← (unsafe Runtime.markPersistent
    (Ix.Kernel.Cached.coreKnotI .verified shared Ix.Kernel.checkFuel) :
      BaseIO (Ix.Kernel.Cached.CoreFnsI .source))
  return .ok { fe := shared, core, env, installed := ok, failures,
               times := #[("convert", t1 - t0), ("lower", t2 - t1), ("install", t3 - t2)] }

/-- **Install a compile's input**: its condensation (`Ix.CondenseM`, as the
compile's front end builds it), then `install`. -/
def installInput (env : Ix.Environment) (workers : Nat := 32) : IO (Except String Installed) := do
  let blocks ← IO.lazyPure fun _ => Ix.CondenseM.run (Ix.Compile.FrontEnd.graph env)
  install env blocks workers

/-! ## The walk -/

/-- A context entry: a binder's free variable or a `let`'s annotated value, with
an identity for the sharing memo. -/
structure CtxEntry where
  id : Nat
  val : KExpr

/-- What a record's walk reads. -/
structure Cx where
  fe : FEnv .source
  core : Ix.Kernel.Cached.CoreFnsI .source
  sharing : Array Ixon.Expr
  bounds : Array Nat

/-- A record's walk state: the sharing entries' variants (by node list) and
blocks, and the memo of share sites under the same context. -/
structure WState where
  nextId : Nat := 0
  variants : Std.HashMap Nat (Std.HashMap (Array Node) Nat) := {}
  blocks : Array Block := #[]
  memo : Std.HashMap (Nat × List Nat) (KExpr × Nat × Bool) := {}

abbrev WM := StateT WState CM
/-- An entry's walk: its nodes' data, by ordinal. -/
abbrev EM := StateT (Array Node) WM

/-- Bounds the walk's depth (the recursion is structural on it). -/
def walkFuel : Nat := 1 <<< 24

/-- The record and its source differ: the record gets the undecided section. -/
def mismatch (what : String) : EM α :=
  throw (.internal s!"binder data: the record and its source differ at {what}")

private def freshId : EM Nat :=
  modifyGetThe WState fun st => (st.nextId, { st with nextId := st.nextId + 1 })

private def reserve : EM Nat :=
  modifyGet fun nodes => (nodes.size, nodes.push (.binder none))

private def setNode (ord : Nat) (n : Node) : EM Unit :=
  modify fun nodes => nodes.set! ord n

/-- The variant of entry `n` for the node list `nodes`. -/
private def variantOf (n : Nat) (nodes : Array Node) : WM Nat := do
  let st ← get
  let table := st.variants.getD n {}
  match table[nodes]? with
  | some v => pure v
  | none =>
    let v := table.size
    set { st with variants := st.variants.insert n (table.insert nodes v)
                  blocks := st.blocks.push ⟨1, n, v, nodes⟩ }
    pure v

/-- IxC's datum of a run whose annotated opened leaf is `leaf` at `depth`
(`annotPwPiI` for a ∀ run, `annotPwLamI` for a λ run); `none` where IxC's
function fails. -/
def datum (cx : Cx) (pi : Bool) (depth : Nat) (leaf : KExpr) : EM (Option PropWhen) := do
  let act : CM PropWhen :=
    if pi then Ix.Kernel.Cached.annotPwPiI cx.core cx.fe depth leaf
    else Ix.Kernel.Cached.annotPwLamI cx.core cx.fe depth leaf
  let res : Option PropWhen ← (tryCatch (some <$> act) (fun _ => pure none) : CM (Option PropWhen))
  pure res

/-- A run of binders of one kind in both trees: each binder's domain in the
record and in the source, and its metadata (the record's contracts); then both
bodies. -/
def binderRun (pi : Bool) : Ixon.Expr → KExpr → Array (Ixon.Expr × KExpr × BinderMeta) →
    Ixon.Expr × KExpr × Array (Ixon.Expr × KExpr × BinderMeta)
  | e@(.lam c t b), x@(.lam ty body _), acc =>
    if pi then (e, x, acc) else binderRun pi b body (acc.push (t, ty, BinderMeta.ofContracts c .shared))
  | e@(.all c r t b), x@(.forallE ty body _), acc =>
    if pi then binderRun pi b body (acc.push (t, ty, BinderMeta.ofContracts c r)) else (e, x, acc)
  | e, x, acc => (e, x, acc)

/-- The walk of one entry's tree `e` beside its source `x`, under `ctx`
(innermost first) at binder depth `depth`: the annotated opened term, and
whether anything in it is undecided. Every numbered node of `e` gets its datum
at its ordinal. -/
def walk : Nat → Cx → List CtxEntry → Nat → Ixon.Expr → KExpr → EM (KExpr × Bool)
  | 0, _, _, _, _, _ => mismatch "the walk's depth bound"
  | fuel + 1, cx, ctx, depth, e, x =>
    match e, x with
    | .var i, _ =>
      match ctx[i.toNat]? with
      | some c => pure (c.val, false)
      | none => mismatch "a loose variable"
    | .app f a, .app xf xa => do
      let (f', bf) ← walk fuel cx ctx depth f xf
      let (a', ba) ← walk fuel cx ctx depth a xa
      pure (.app f' a', bf || ba)
    | .lam .., .lam .. | .all .., .forallE .. => do
      let pi := e matches .all ..
      let (leafE, leafX, bs) := binderRun pi e x #[]
      let mut inner := ctx
      let mut ords : Array Nat := #[]
      let mut stk : List (Ix.Kernel.Cached.AnnotBinderEntry .source) := []
      let mut bad := false
      for h : j in [:bs.size] do
        let (t, ty, mb) := bs[j]
        ords := ords.push (← reserve)
        let (t', bt) ← walk fuel cx inner (depth + j) t ty
        bad := bad || bt
        let id ← freshId
        inner := ⟨id, .fvar (depth + j) t'⟩ :: inner
        stk := (t', mb) :: stk
      let k := bs.size
      let (leaf', bl) ← walk fuel cx inner (depth + k) leafE leafX
      let pw? ← datum cx pi (depth + k) leaf'
      let undecided := bad || bl || pw?.isNone
      let node : Node := if undecided then .undecided else Node.ofPw (pw?.getD .never)
      for ord in ords do setNode ord node
      let mk : KExpr → KExpr → BinderMeta → KExpr :=
        if pi then fun ty b mb => .forallE ty b mb else fun ty b mb => .lam ty b mb
      let out ← (Ix.Kernel.Cached.annotateBindersOutI mk depth (some (pw?.getD .never)) stk (k - 1)
        (leaf'.abstractRangeC depth k) : CM KExpr)
      pure (out, undecided)
    | .letE _ t v b, .letE ty val body _ => do
      -- IxC annotates the type and the value, then the body with the value
      -- transparent (its ζ-reduct)
      let (_, bt) ← walk fuel cx ctx depth t ty
      let (v', bv) ← walk fuel cx ctx depth v val
      let id ← freshId
      let (b', bb) ← walk fuel cx (⟨id, v'⟩ :: ctx) depth b body
      pure (b', bt || bv || bb)
    | .prj _ _ v, .proj k i xv => do
      let (v', bv) ← walk fuel cx ctx depth v xv
      pure (.proj k i v', bv)
    | .share n, _ => do
      let ord ← reserve
      let n := n.toNat
      let key := (n, (ctx.take (cx.bounds[n]?.getD 0)).map (·.id))
      let (e', variant, bad) ← match (← getThe WState).memo[key]? with
        | some hit => pure hit
        | none => do
          let some entry := cx.sharing[n]? | mismatch "a share"
          let ((e', bad), nodes) ← ((walk fuel cx ctx depth entry x).run #[] :
            WM ((KExpr × Bool) × Array Node))
          let variant ← variantOf n nodes
          modifyThe WState fun st => { st with memo := st.memo.insert key (e', variant, bad) }
          pure (e', variant, bad)
      setNode ord (.share variant)
      pure (e', bad)
    | .sort _, .sort _ | .ref .., .const .. | .recur .., .const .. | .str _, .lit _
    | .nat _, .lit _ => pure (x, false)
    | _, _ => mismatch "a node"

/-! ## A record's sources -/

/-- Whether a member of `c` is unsafe or partial. -/
def unsafeOrPartial (c : Ixon.Constant) : Bool :=
  let defn (d : Ixon.Definition) : Bool := match d.safety with
    | .safe => false
    | _ => true
  match c.info with
  | .defn d => defn d
  | .recr r => r.isUnsafe
  | .axio a => a.isUnsafe
  | .muts ms => ms.any fun
    | .defn d => defn d
    | .indc i => i.isUnsafe || i.ctors.any (·.isUnsafe)
    | .recr r => r.isUnsafe
  | _ => false

/-- The block's members, as the record lists them. -/
def members (c : Ixon.Constant) : Array (Ixon.MutConst ⊕ Ixon.ConstantInfo) :=
  match c.info with
  | .muts ms => ms.map .inl
  | info => #[.inr info]

/-- A source constant's root terms with their numberings, in section order, when
its kind is the record member's. -/
def sourceItems (find : Ix.Name → Option Ix.ConstantInfo) (ci : Ix.ConstantInfo) :
    Ixon.MutConst ⊕ Ixon.ConstantInfo → Option (Array (Numbering × Ix.Expr))
  | .inl (.defn _) | .inr (.defn _) =>
    let σ : Numbering := ⟨ci.getCnst.levelParams, false⟩
    match ci with
    | .defnInfo d => some #[(σ, d.cnst.type), (σ, d.value)]
    | .thmInfo t => some #[(σ, t.cnst.type), (σ, t.value)]
    | .opaqueInfo o => some #[(σ, o.cnst.type), (σ, o.value)]
    | _ => none
  | .inr (.axio _) => match ci with
    | .axiomInfo a => some #[(⟨a.cnst.levelParams, false⟩, a.cnst.type)]
    | _ => none
  | .inr (.quot _) => match ci with
    | .quotInfo q => some #[(⟨q.cnst.levelParams, false⟩, q.cnst.type)]
    | _ => none
  | .inl (.recr r) | .inr (.recr r) => match ci with
    | .recInfo v => do
      guard (v.rules.size == r.rules.size)
      let indLevels := match v.all[0]?.bind find with
        | some (.inductInfo i) => i.cnst.levelParams.size
        | _ => v.cnst.levelParams.size
      let σ : Numbering := ⟨v.cnst.levelParams, v.cnst.levelParams.size == indLevels + 1⟩
      some (#[(σ, v.cnst.type)] ++ v.rules.map ((σ, ·.rhs)))
    | _ => none
  | .inl (.indc i) => match ci with
    | .inductInfo v => do
      let σ : Numbering := ⟨v.cnst.levelParams, false⟩
      let ctors ← v.ctors.mapM fun n => match find n with
        | some (.ctorInfo k) => some (⟨k.cnst.levelParams, false⟩, k.cnst.type)
        | _ => none
      guard (ctors.size == i.ctors.size)
      some (#[(σ, v.cnst.type)] ++ ctors)
    | _ => none
  | _ => none

/-- The Source roots of a record, from its members' sources (`extra` first,
then the compile's input). -/
def sourceRoots (env : Ix.Environment) (extra : Array (Ix.Name × Ix.ConstantInfo))
    (names : Array Ix.Name) (c : Ixon.Constant) : Option (Array KExpr) := do
  let ms := members c
  guard (ms.size == names.size)
  let find (n : Ix.Name) : Option Ix.ConstantInfo :=
    ((extra.find? (·.1 == n)).map (·.2)).orElse fun _ => env.consts.get? n
  let mut items : Array (Numbering × Ix.Expr) := #[]
  for (m, n) in ms.zip names do
    let ci ← find n
    items := items ++ (← sourceItems find ci m)
  let roots := (exprsOf items).toOption
  let roots ← roots
  guard (roots.size == (IxVM.PwHints.roots c).size)
  return roots

/-! ## The annotator -/

/-- **The section of a block record**, from its members' sources: IxC's pass
over each root beside its source, against the installed environment. -/
def annotate (k : Installed) (extra : Array (Ix.Name × Ix.ConstantInfo)) (names : Array Ix.Name)
    (c : Ixon.Constant) : Array Ixon.BinderBlock :=
  let rs := IxVM.PwHints.roots c
  if rs.isEmpty then #[] else
  if unsafeOrPartial c then Ix.CompileM.undecidedSection c else
  match sourceRoots k.env extra names c with
  | none => Ix.CompileM.undecidedSection c
  | some xs =>
    let cx : Cx := { fe := k.fe, core := k.core, sharing := c.sharing,
                     bounds := IxVM.PwHints.bounds c.sharing }
    let act : WM (Array Block) := do
      let mut out := #[]
      for h : i in [:rs.size] do
        let some x := xs[i]? | throw (.internal "binder data: a root without a source")
        let (_, nodes) ← (walk walkFuel cx [] 0 rs[i] x).run #[]
        out := out.push ⟨0, i, 0, nodes⟩
      return out
    match (act.run {}).run {} with
    | .ok ((roots, st), _) =>
      match Ix.Compile.BinderData.sectionOf c (roots ++ st.blocks) with
      | .ok s => s
      | .error _ => Ix.CompileM.undecidedSection c
    | .error _ => Ix.CompileM.undecidedSection c

/-- **The annotator of a compile** over its installed input. -/
def annotator (k : Installed) : Ix.BinderAnnotator :=
  { run := annotate k }

/-- The safe records of `env` whose section has an undecided binder, by address. -/
def undecidedSafe (env : Ixon.Env) (workers : Nat := 32) : Array Address :=
  let records : Array (Address × Ixon.LazyConstant) := env.consts.toArray
  (Ix.Compile.Parallel.map (max workers 1) (fun (a, lc) =>
    match lc.get? with
    | some c =>
      if !unsafeOrPartial c && c.binders.any (·.nodes.any (· == .undecided)) then some a else none
    | none => none) records).filterMap id

end Ix.Compile.KernelAnnotate

end
