module

public import Lean.Meta
public import Ix.CompileM
public import Ix.SemanticContract

public section

/-!
# The compiler's binder-data annotator

`ix compile` writes every block record's binder-data section while it builds
the record, before the record is hashed (`Ix.CompileM.withBinderSection`). This
module is the annotator it runs there: it reads each binder's datum off Lean's
own elaboration of the block's source declarations, with `Meta.inferType`.

**The datum.** The zero-ness of the binder's codomain sort, as a function of
the constant's universe parameters: `never`, or "zero exactly when every
parameter of S is zero". For a `∀` it is the zero-ness of the sort of the body;
for a `λ`, of the sort of the body's type. Zero-ness of a level is `never` or
"all of S zero" for a unique S, and a binder's codomain sort is unique up to
level equivalence, so every correct annotator writes the same datum.

**Telescopes.** The zero-ness of `imax u v` is that of `v`, so every binder of a
run of `λ`s (or of `∀`s) has the datum of the innermost one. The annotator
infers once per run, not once per binder.

**Sharing.** It walks the record as stored, with its sharing table, beside the
Lean source expression (whose `mdata` the record does not keep). A share node
visits its entry once per context: the entry's data depend only on the free
variables its loose variables name, so `(entry, those variables)` memoises the
entry's node list, and a shared proof term is not expanded. An entry's
variants are its distinct node lists, numbered in order of first occurrence,
as the canonical form requires (`Ixon.Constant.bindersComplete`).

**Unsafe and partial constants** carry the undecided node (`0x04`) at every
binder: their types need not check. So does every binder of a record whose
source the annotator cannot find or align, and every binder of a run whose
datum Lean's inference cannot compute; each is reported (`annotator`), and
`--strict-binder-data` fails the compile on a safe one.

The annotator is not trusted. The compiler keeps its section only in canonical
form (`Ix.CompileM.sectionAdmissible`), and a checker validates every datum it
reads.
-/

namespace BinderAnnotate

open Lean Meta

/-! ## A record's structure -/

/-- The root expressions of a record in section order. -/
def roots (c : Ixon.Constant) : Array Ixon.Expr := c.info.binderRoots

/-- One more than the largest loose variable of `e`, under the bounds of the
entries before it. -/
def looseBound (shared : Array Nat) : Ixon.Expr → Nat
  | .var i => i.toNat + 1
  | .app f a => max (looseBound shared f) (looseBound shared a)
  | .lam _ t b => max (looseBound shared t) (looseBound shared b - 1)
  | .all _ _ t b => max (looseBound shared t) (looseBound shared b - 1)
  | .letE _ t v b =>
    max (max (looseBound shared t) (looseBound shared v)) (looseBound shared b - 1)
  | .prj _ _ v => looseBound shared v
  | .share n => shared[n.toNat]?.getD 0
  | _ => 0

/-- Each sharing entry's loose bound. -/
def bounds (sharing : Array Ixon.Expr) : Array Nat :=
  sharing.foldl (fun out e => out.push (looseBound out e)) #[]

/-! ## The datum -/

/-- The zero-ness of a level over the parameters `lps`: `none` never, `some S`
zero exactly when every parameter of `S` (by position) is; `Option.none` on a
parameter outside `lps` or a metavariable. -/
def zeroness (lps : List Name) : Level → Option (Option (Array Nat))
  | .zero => some (some #[])
  | .succ _ => some none
  | .max a b => do
    match ← zeroness lps a, ← zeroness lps b with
    | some s, some t => pure (some (s ++ t))
    | _, _ => pure none
  | .imax _ b => zeroness lps b
  | .param n => (lps.idxOf? n).map fun i => some #[i]
  | .mvar _ => none

/-- A datum in the section's spelling. -/
def nodeOf : Option (Array Nat) → Ixon.BinderNode
  | none => .never
  | some ps =>
    let sorted := ps.qsort (· < ·)
    let distinct := sorted.foldl (fun out p => if out.back? == some p then out else out.push p) #[]
    if distinct.isEmpty then .zero else .ifAllZero (distinct.map (·.toUInt64))

/-- The datum of a run of binders whose innermost body is `body` (under the
run's locals): the zero-ness of the sort of `body` for `∀`, of `body`'s type for
`λ`. The undecided node when Lean's inference fails or the sort is not one. -/
def datum (lps : List Name) (lam : Bool) (body : Expr) : MetaM Ixon.BinderNode := do
  try
    let ty ← if lam then inferType body else pure body
    match ← whnf (← inferType ty) with
    | .sort u =>
      match zeroness lps (← instantiateLevelMVars u) with
      | some z => pure (nodeOf z)
      | none => pure .undecided
    | _ => pure .undecided
  catch _ => pure .undecided

/-! ## The walk -/

structure Cx where
  sharing : Array Ixon.Expr
  bounds : Array Nat
  full : Array Bool
  lps : List Name

structure St where
  /-- each entry's variants, in order of first occurrence -/
  variants : Array (Array (Array Ixon.BinderNode))
  /-- an entry's variant in the context of the free variables it names -/
  memo : Std.HashMap (Nat × List FVarId) Nat := {}
  undecided : Nat := 0

abbrev M := StateT St MetaM

def mismatch (what : String) : M α :=
  throwError "binder data: the record and its source differ at {what}"

/-- Intern entry `n`'s node list as a variant. -/
def intern (n : Nat) (nodes : Array Ixon.BinderNode) : M Nat := do
  let s ← get
  let vs := s.variants[n]?.getD #[]
  match vs.findIdx? (· == nodes) with
  | some v => return v
  | none =>
    set { s with variants := s.variants.set! n (vs.push nodes) }
    return vs.size

/-- `x` with `k` applications peeled (each through `mdata`): the head and the
arguments, first to last. -/
def peelApps : Nat → Expr → Array Expr → Option (Expr × Array Expr)
  | 0, x, acc => some (x, acc.reverse)
  | k + 1, x, acc => match x.consumeMData with
    | .app f a => peelApps k f (acc.push a)
    | _ => none

/-- An Ixon application spine: the head and the arguments, first to last. -/
def ixonSpine : Ixon.Expr → Array Ixon.Expr → Ixon.Expr × Array Ixon.Expr
  | .app f a, acc => ixonSpine f (acc.push a)
  | h, acc => (h, acc.reverse)

/-- A run of binders of one kind in both trees: each binder's Ixon domain,
name, Lean domain and info, then both bodies. -/
def binderRun (lam : Bool) : Ixon.Expr → Expr → Array (Ixon.Expr × Name × Expr × BinderInfo) →
    Ixon.Expr × Expr × Array (Ixon.Expr × Name × Expr × BinderInfo)
  | e@(.lam _ t b), x, acc =>
    if !lam then (e, x, acc) else
    match x.consumeMData with
    | .lam n d body bi => binderRun lam b body (acc.push (t, n, d, bi))
    | x' => (e, x', acc)
  | e@(.all _ _ t b), x, acc =>
    if lam then (e, x, acc) else
    match x.consumeMData with
    | .forallE n d body bi => binderRun lam b body (acc.push (t, n, d, bi))
    | x' => (e, x', acc)
  | e, x, acc => (e, x, acc)

/-- Open the run's binders as locals (each domain over the ones before it). -/
partial def openRun (bs : List (Ixon.Expr × Name × Expr × BinderInfo)) (fvars doms : Array Expr)
    (k : Array Expr → Array Expr → M α) : M α :=
  match bs with
  | [] => k fvars doms
  | (_, n, d, bi) :: rest =>
    let d' := d.instantiateRev fvars
    withLocalDecl n bi d' fun fv => openRun rest (fvars.push fv) (doms.push d') k

mutual

/-- The numbered nodes of `e`, against its Lean source `x` (closed over the
context's locals `ctx`, outermost first), appended to `out`. -/
partial def walk (cx : Cx) (ctx : Array Expr) (e : Ixon.Expr) (x : Expr)
    (out : Array Ixon.BinderNode) : M (Array Ixon.BinderNode) := do
  let x := x.consumeMData
  match e with
  | .lam .. => walkRun cx ctx true e x out
  | .all .. => walkRun cx ctx false e x out
  | .app .. =>
    let (h, args) := ixonSpine e #[]
    let some (h', args') := peelApps args.size x #[] | mismatch "an application"
    let mut out ← walk cx ctx h h' out
    for (a, a') in args.zip args' do
      out ← walk cx ctx a a' out
    return out
  | .letE _ t v b =>
    let .letE n t' v' b' _ := x | mismatch "a let"
    let out ← walk cx ctx t t' out
    let out ← walk cx ctx v v' out
    withLetDecl n t' v' fun fv => walk cx (ctx.push fv) b (b'.instantiate1 fv) out
  | .prj _ _ s =>
    let .proj _ _ s' := x | mismatch "a projection"
    walk cx ctx s s' out
  | .share n => walkShare cx ctx n.toNat x out
  | _ =>
    match x with
    | .lam .. | .forallE .. | .app .. | .letE .. | .proj .. => mismatch "a leaf"
    | _ => return out

/-- A run of binders: one inference for the run, then each domain, then the body. -/
partial def walkRun (cx : Cx) (ctx : Array Expr) (lam : Bool) (e : Ixon.Expr) (x : Expr)
    (out : Array Ixon.BinderNode) : M (Array Ixon.BinderNode) := do
  let (body, bodyX, bs) := binderRun lam e x #[]
  if bs.isEmpty then mismatch "a binder"
  openRun bs.toList #[] #[] fun fvars doms => do
    let inner := bodyX.instantiateRev fvars
    let node ← datum cx.lps lam inner
    if node == .undecided then
      modify fun s => { s with undecided := s.undecided + bs.size }
    let mut out := out
    for h : i in [:bs.size] do
      out := out.push node
      out ← walk cx (ctx ++ fvars.extract 0 i) bs[i].1 (doms[i]?.getD default) out
    walk cx (ctx ++ fvars) body inner out

/-- A share node: the entry's variant in this context, visited at its first
occurrence there. -/
partial def walkShare (cx : Cx) (ctx : Array Expr) (n : Nat) (x : Expr)
    (out : Array Ixon.BinderNode) : M (Array Ixon.BinderNode) := do
  unless cx.full[n]?.getD false do return out
  let k := cx.bounds[n]?.getD 0
  if k > ctx.size then mismatch "a share's context"
  let key := (n, (ctx.extract (ctx.size - k) ctx.size).toList.map (·.fvarId!))
  if let some v := (← get).memo[key]? then
    return out.push (.share v.toUInt64)
  let some entry := cx.sharing[n]? | mismatch "a share"
  let nodes ← walk cx ctx entry x #[]
  let v ← intern n nodes
  modify fun s => { s with memo := s.memo.insert key v }
  return out.push (.share v.toUInt64)

end

/-- The section, from each root's Lean source and level parameters. -/
def sectionM (c : Ixon.Constant) (sources : Array (Expr × List Name)) : M (Array Ixon.BinderBlock) := do
  let rs := roots c
  let mut rootNodes : Array (Array Ixon.BinderNode) := #[]
  for (e, (x, lps)) in rs.zip sources do
    let cx : Cx := { sharing := c.sharing, bounds := bounds c.sharing,
                     full := Ixon.binderfulEntries c.sharing, lps }
    rootNodes := rootNodes.push (← walk cx #[] e x #[])
  let variants := (← get).variants
  let mut out : Array Ixon.BinderBlock := #[]
  for h : r in [:rootNodes.size] do
    unless rootNodes[r].isEmpty do
      out := out.push { shared := false, index := r.toUInt64, variant := 0, nodes := rootNodes[r] }
  for h : n in [:variants.size] do
    for h' : v in [:variants[n].size] do
      out := out.push { shared := true, index := n.toUInt64, variant := v.toUInt64,
                        nodes := variants[n][v] }
  return out

/-! ## Sources -/

/-- A Lean constant's root expressions, in section order, when its kind is the
record member's. -/
def sourceRoots (env : Environment) (ci : ConstantInfo) : Ixon.MutConst ⊕ Ixon.ConstantInfo →
    Option (Array Expr)
  | .inl (.defn _) | .inr (.defn _) => match ci with
    | .defnInfo d => some #[d.type, d.value]
    | .thmInfo t => some #[t.type, t.value]
    | .opaqueInfo o => some #[o.type, o.value]
    | _ => none
  | .inr (.axio _) => match ci with | .axiomInfo a => some #[a.type] | _ => none
  | .inr (.quot _) => match ci with | .quotInfo q => some #[q.type] | _ => none
  | .inl (.recr r) | .inr (.recr r) => match ci with
    | .recInfo v => if v.rules.length == r.rules.size then
        some (#[v.type] ++ v.rules.toArray.map (·.rhs)) else none
    | _ => none
  | .inl (.indc i) => match ci with
    | .inductInfo v => do
      let ctors ← v.ctors.toArray.mapM fun n => (env.find? n).map (·.type)
      if ctors.size == i.ctors.size then some (#[v.type] ++ ctors) else none
    | _ => none
  | _ => none

/-- The block's members, as the record lists them. -/
def members (c : Ixon.Constant) : Array (Ixon.MutConst ⊕ Ixon.ConstantInfo) :=
  match c.info with
  | .muts ms => ms.map .inl
  | info => #[.inr info]

/-- The Lean environment holding the members' sources, each root's expression
and level parameters, and whether every member is safe and total. -/
def sources (envs : Array Environment) (extra : Array (Name × ConstantInfo)) (names : Array Ix.Name)
    (c : Ixon.Constant) : Option (Environment × Array (Expr × List Name) × Bool) := do
  let ms := members c
  guard (ms.size == names.size)
  let leanNames := names.map Ix.SemanticContract.toLeanName
  let fromExtra (n : Name) : Option ConstantInfo := (extra.find? (·.1 == n)).map (·.2)
  let env ← envs.find? fun env => leanNames.all fun n => (fromExtra n).isSome || env.contains n
  let mut out : Array (Expr × List Name) := #[]
  let mut decided := true
  for (m, n) in ms.zip leanNames do
    let ci ← (fromExtra n).orElse fun _ => env.find? n
    let rs ← sourceRoots env ci m
    out := out ++ rs.map (·, ci.levelParams)
    if ci.isUnsafe || ci.isPartial then decided := false
  guard (out.size == (roots c).size)
  return (env, out, decided)

/-! ## The annotator of a compile -/

/-- **The section of a block record**, from its members' sources in `envs`.
`report` collects the safe records given an undecided binder (their member
names), for the compile's report and `--strict-binder-data`. -/
def annotate (envs : Array Environment) (report : IO.Ref (Array String))
    (extra : Array (Name × ConstantInfo)) (names : Array Ix.Name)
    (c : Ixon.Constant) : IO (Array Ixon.BinderBlock) := do
  if (roots c).isEmpty then return #[]
  let undecided : IO Unit :=
    report.modify (·.push (", ".intercalate (names.map (·.pretty)).toList))
  let some (env, srcs, decided) := sources envs extra names c | do
    undecided
    return Ix.CompileM.undecidedSection c
  unless decided do return Ix.CompileM.undecidedSection c
  let ctx : Core.Context := { fileName := "<binder data>", fileMap := default,
                              maxHeartbeats := 0, maxRecDepth := 100000 }
  let init : St := { variants := Array.replicate c.sharing.size #[] }
  let act : MetaM (Array Ixon.BinderBlock × St) :=
    withTransparency .all ((sectionM c srcs).run init)
  try
    let ((blocks, st), _) ← (act.run' {} {}).toIO ctx { env }
    if st.undecided > 0 then undecided
    return blocks
  catch _ =>
    undecided
    return Ix.CompileM.undecidedSection c

private unsafe def annotateUnsafe (envs : Array Environment) (report : IO.Ref (Array String))
    (extra : Array (Name × ConstantInfo)) (names : Array Ix.Name) (c : Ixon.Constant) :
    Array Ixon.BinderBlock :=
  match unsafeIO (annotate envs report extra names c) with
  | .ok binders => binders
  | .error _ => #[]

/-- `annotate` as the pure function the compile's input carries
(`Ix.Environment.binderAnnotator?`). It reads only its arguments: Lean's
elaboration of the sources is deterministic. -/
@[implemented_by annotateUnsafe]
opaque annotatePure (envs : Array Environment) (report : IO.Ref (Array String))
    (extra : Array (Name × ConstantInfo)) (names : Array Ix.Name) (c : Ixon.Constant) :
    Array Ixon.BinderBlock

/-- **The annotator of a compile over `envs`** (its source environments, each
marked persistent: the compile's workers share them), with the report of the
safe records it leaves undecided. -/
def annotator (envs : Array Environment) : IO (Ix.BinderAnnotator × IO.Ref (Array String)) := do
  let envs ← envs.mapM fun (env : Environment) =>
    (unsafe Runtime.markPersistent env : BaseIO Environment)
  let report ← IO.mkRef #[]
  return ({ run := annotatePure envs report }, report)

end BinderAnnotate

end
