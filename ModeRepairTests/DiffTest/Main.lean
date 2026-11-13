import IxC.Resource
import IxC.Kernel.Ixon.Prelude
import DiffTest.Hyp
import DiffTest.Gen

/-! # The differential tester's driver (MT): self-test, runs, tallies, shrinking -/

namespace MT.DiffTest

open IxC.Resource Ixon

/-! ## Self-test: the hand-built interface against the reader's rules -/

/- Ixon v5 (since `jcb/ixcc-mode-repair` was rebased onto f2b985847): a binder's mode is in the
record's binder-data section, one node per `lam`/`all` in pre-order, not inline in the
expression. `ixTy` and `defRecord` return each root's nodes beside its expression. -/

/-- Ixon records for the universe: the prelude's `Nat` and `Bool`, and a block
plus projection per other inductive (only its constructor count is read). -/
structure STStore where
  store : Ix.Kernel.Reader.Store
  blob : Address → Option ByteArray
  table : Ix.Kernel.RoleTable
  refs : Array Address

def dummyInd (nCtors : Nat) : Ixon.Constant :=
  let ctors : Array Ixon.Constructor := ((List.range nCtors).map fun j =>
    ({ isUnsafe := false, lvls := 0, cidx := j.toUInt64, params := 0, fields := 0, typ := Ixon.Expr.sort 0 } :
      Ixon.Constructor)).toArray
  let ind : Ixon.Inductive :=
    { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := Ixon.Expr.sort 0, ctors }
  { info := Ixon.ConstantInfo.muts #[Ixon.MutConst.indc ind],
    sharing := #[], refs := #[], univs := #[.zero] }

def stAddr (k : Nat) : Address := ⟨⟨#[k.toUInt8, 0x73, 0x74]⟩⟩

def mkSTStore : Except String STStore := do
  let tbl ← Ix.Kernel.Reader.defaultTable
  let recs ← Ix.Kernel.Reader.preludeRecords
  let evid ← Ix.Kernel.Reader.evidenceRecords
  let blobs ← Ix.Kernel.Reader.evidenceBlobs
  let some natA := tbl.addressOf? .nat | throw "no nat role"
  let some boolA := tbl.addressOf? .bool | throw "no bool role"
  -- list, box, sbox, ekey, pairN, pairL, wrap: block at stAddr (2k), projection at stAddr (2k+1)
  let counts := [2, 1, 1, 1, 1, 1, 1]
  let mine : List (Address × Ixon.Constant) := (counts.zipIdx.map fun (n, k) =>
    [(stAddr (2 * k), dummyInd n),
     (stAddr (2 * k + 1), ({ info := .iPrj ⟨0, stAddr (2 * k)⟩, sharing := #[], refs := #[], univs := #[] } :
       Ixon.Constant))]).flatten
  let base : Ix.Kernel.Reader.Store := fun a =>
    ((mine.find? (·.1 == a)).map (·.2)) <|> ((recs.find? (·.1 == a)).map (·.2)) <|>
      ((evid.find? (·.1 == a)).map (·.2))
  pure { store := base, blob := fun a => blobs.lookup a, table := tbl,
         refs := #[natA, boolA] ++ ((List.range 7).map fun k => stAddr (2 * k + 1)).toArray }

def tyIdx : Ty → Option Nat
  | .nat => some 0 | .bool => some 1 | .list => some 2 | .box => some 3 | .sbox => some 4
  | .ekey => some 5 | .pairN => some 6 | .pairL => some 7 | .wrap => some 8
  | _ => none

/-- A type as an Ixon expression, with the modes of its binder nodes in pre-order. -/
partial def ixTy : Ty → Option (Ixon.Expr × Array AllMode)
  | .list => some (.app (.ref 2 #[]) (.ref 0 #[]), #[])
  | .arr m r a b => do
    let (ea, na) ← ixTy a
    let (eb, nb) ← ixTy b
    pure (.all ea eb, #[{ input := m, result := r }] ++ na ++ nb)
  | .eq .. => none
  | t => do pure (.ref (← tyIdx t).toUInt64 #[], #[])

/-- The definition record of `d`'s interface: its type's ∀s and its value's λs
carry the modes (a λ's result mode is its ∀'s, as `teleAgree` asks), in the
record's binder-data section; the body is a sort (it is skipped). -/
def defRecord (st : STStore) (d : UDef) : Option Ixon.Constant := do
  let (rty, rnodes) ← ixTy d.rty
  let doms ← d.params.mapM fun (t, _) => ixTy t
  let n := d.params.length
  let mode (m : BinderMode) (i : Nat) : AllMode := { input := m, result := if i + 1 == n then d.res else .shared }
  let (typ, tnodes) := (d.params.zip doms).zipIdx.foldr (fun (((_, m), (dom, dn)), i) (acc, an) =>
    (Ixon.Expr.all dom acc, #[mode m i] ++ dn ++ an)) (rty, rnodes)
  let (value, vnodes) := (d.params.zip doms).zipIdx.foldr (fun (((_, m), (dom, dn)), i) (acc, an) =>
    (Ixon.Expr.lam dom acc, #[mode m i] ++ dn ++ an)) ((.sort 0 : Ixon.Expr), (#[] : Array AllMode))
  let block (root : Nat) (ns : Array AllMode) : Array BinderBlock :=
    if ns.isEmpty then #[] else #[{ shared := false, index := root.toUInt64, variant := 0, nodes := ns.map .never }]
  pure { info := .defn { kind := Ix.DefKind.defn, safety := Ix.DefinitionSafety.safe, lvls := 0, typ, value },
         sharing := #[], refs := st.refs, univs := #[.zero], binders := block 0 tnodes ++ block 1 vnodes }

/-- `readBody`'s interface rules without the classes: the telescopes, their
agreement, each parameter's mode, skeleton and `noLeafType`, the result mode and
skeleton. -/
def readerIface (st : STStore) (d : UDef) : Except String (List (BinderMode × Skel × Bool) × ResultMode × Skel) := do
  let some rec := defRecord st d | throw "skipped"
  let a := stAddr 200
  let store : Ix.Kernel.Reader.Store := fun x => if x == a then some rec else st.store x
  let s : Subject := { table := st.table, store, blob := st.blob, seeds := [a] }
  let rd := Reading.make s
  let x ← rd.rcx noClasses (.member a 0)
  let .defn dd := rec.info | throw "not a definition"
  let ((alls, codSkel), _) ← (inBlock x.rm (rootKey 0) (do
      let (alls, cod) ← readForalls x readFuel dd.typ
      let cs ← readSkel x readFuel cod
      pure (alls, cs))).run {}
  let (lams, _) ← (inBlock x.rm (rootKey 1) (do
      let (lams, body) ← readLamNodes x readFuel dd.value
      skip x.rm readFuel body
      pure lams)).run {}
  teleAgree alls lams
  let k := lams.length
  let res := (lams.getLast?.map (·.1.result)).getD .shared
  let rs := arrowChain ((alls.drop k).map fun (m, s, _) => (m, s)) codSkel
  pure (lams.map (fun (m, sk, dom) => (m.input, sk, x.noLeafType dom)), res, rs)

/-- Whether the tree under test's reader has the landed `noLeafType` rule (`Nat`
no leaf): true at `6db9089a7`; false after repair A, whose `noLeafType` is always
false (and whose checker reads `Param.noLeaf` nowhere). Probed, not assumed. -/
def treeNoLeafRule (st : STStore) : Bool :=
  match readerIface st { ref := userR 0, params := [(.nat, .many)], res := .shared, rty := .nat, body := .lit 0 } with
  | .ok ((_, _, nl) :: _, _, _) => nl
  | _ => true

/-- `none`: agree; `some msg`: disagree; skipped definitions (an `Eq` type) are `ok`.
`nlRule`: the tree's `noLeafType` rule is the landed one (`treeNoLeafRule`); when
it is not, the expected `noLeaf` is false everywhere (the generator keeps the
landed rule in `Param.noLeaf`, which nothing reads after repair A). -/
def selfTest (st : STStore) (nlRule : Bool) (d : UDef) : Option String :=
  match readerIface st d with
  | .error "skipped" => none
  | .error e => some s!"reader fails: {e}"
  | .ok (ps, res, rs) =>
    let mine := d.params.map fun (t, m) => (m, t.skel, nlRule && t.noLeaf)
    let pOk := ps.length == mine.length && (ps.zip mine).all fun ((m, s, nl), (m', s', nl')) =>
      m == m' && s == s' && nl == nl'
    if pOk && res == d.res && rs == d.rty.skel then none
    else some s!"params {repr ps} vs {repr mine}; res {repr res} vs {repr d.res}; rs {repr rs} vs {repr d.rty.skel}"

/-! ## Runs -/

def isOOF : Outcome → Bool
  | .outOfFuel => true
  | _ => false

def violation? : Outcome → Option Violation
  | .violation k => some k
  | _ => none

def oName : Outcome → String
  | .value .. => "value"
  | .violation k => s!"{repr k}"
  | .stuck => "stuck"
  | .outOfFuel => "oof"

/-- Every fuel from 0 to the first that is not out of fuel (at most 128), then
to `2·f₀ + 16`, then 1000 and 100000 (256 too when no `f₀ ≤ 128`). -/
def runAll (go : Nat → Outcome) : Array (Nat × Outcome) := Id.run do
  let mut out : Array (Nat × Outcome) := #[]
  let mut f0 : Option Nat := none
  for f in [0:129] do
    let o := go f
    out := out.push (f, o)
    if !isOOF o then
      f0 := some f
      break
  match f0 with
  | some z => for f in [z + 1:2 * z + 17] do out := out.push (f, go f)
  | none => out := out.push (256, go 256)
  out := out.push (1000, go 1000)
  out := out.push (100000, go 100000)
  return out

/-- Fuel-dependent: a violation at some fuel while the top fuel gives a value, or an
outcome other than a value after a value. -/
def nonMonotone (os : Array (Nat × Outcome)) : Bool := Id.run do
  let topValue := match os.back? with | some (_, .value ..) => true | _ => false
  if topValue && os.any (fun (_, o) => (violation? o).isSome) then return true
  let mut seen := false
  for (_, o) in os do
    if seen && oName o != "value" then return true
    if oName o == "value" then seen := true
  return false

def verdictShort : Verdict → String
  | .accept .. => "accept"
  | .refuse _ w => s!"refuse: {(w.splitOn ":").headD w}"
  | .decline r => s!"decline: {r}"

/-! ## Printing -/

def refName (r : Ref) : String :=
  let named : List (Ref × String) := [
    (natI, "natI"), (boolI, "boolI"), (trueR, "trueR"), (falseR, "falseR"), (listI, "listI"), (nilR, "nilR"),
    (consR, "consR"), (boxI, "boxI"), (boxC, "boxC"), (sboxI, "sboxI"), (sboxC, "sboxC"), (ekeyI, "ekeyI"),
    (ekeyC, "ekeyC"), (pairNI, "pairNI"), (pairNC, "pairNC"), (pairLI, "pairLI"), (pairLC, "pairLC"),
    (wrapI, "wrapI"), (wrapC, "wrapC"), (eqI, "eqI"), (reflC, "reflC"), (addP, "addP"), (consumeR, "consumeR"),
    (lenR, "lenR"), (callTwiceR, "callTwiceR"), (idR, "idR"), (constR, "constR"), (mkKR, "mkKR"),
    (exFresh, "exFresh"), (exId, "exId"), (exBox, "exBox"), (exStale, "exStale")]
  match named.find? (·.1 == r) with
  | some (_, n) => n
  | none =>
    if let some j := (List.range 64).find? (fun j => userR j == r) then s!"(userR {j})"
    else if let some j := (List.range 64).find? (fun j => inFnR j == r) then s!"(inFnR {j})"
    else (repr r).pretty

def clsS (c : Cls) : String := s!".{(reprStr c).splitOn "." |>.getLast!}"
def bmS (m : BinderMode) : String := s!".{(reprStr m).splitOn "." |>.getLast!}"
def rmS (m : ResultMode) : String := s!".{(reprStr m).splitOn "." |>.getLast!}"

partial def skelS : Skel → String
  | .data => ".data"
  | .unknown => ".unknown"
  | .dataApp f a => s!"(.dataApp {skelS f} {skelS a})"
  | .arrow i d r c => s!"(.arrow {bmS i} {skelS d} {rmS r} {skelS c})"

def paramS (p : Param) : String :=
  s!"\{ mode := {bmS p.mode}, cls := {clsS p.cls}, skel := {skelS p.skel}, noLeaf := {p.noLeaf} }"

def letS : LetMode → String
  | .value m => s!"(.value {bmS m})"
  | .borrow => ".borrow"

/-- A run term as Lean source of their constructors. -/
partial def termS : Term → String
  | .irr => ".irr"
  | .var i c => s!"(.var {i} {clsS c})"
  | .const r c => s!"(.const {refName r} {clsS c})"
  | .app f a c => s!"(.app {termS f} {termS a} {clsS c})"
  | .lam p r rc fvs b => s!"(.lam {paramS p} {rmS r} {clsS rc} {repr fvs} {termS b})"
  | .letE m d v b => s!"(.letE {letS m} {clsS d} {termS v} {termS b})"
  | .case k mj alts ex c =>
    s!"(.case (caseOf {refName k.ind} {repr (k.alts.toList.map (·.args.size))}) {termS mj} #[{", ".intercalate (alts.toList.map termS)}] #[{", ".intercalate (ex.toList.map termS)}] {clsS c})"
  | .natLit n => s!"(.natLit {n})"
  | .strLit s => s!"(.strLit {repr s})"
  | .proj s i e c => s!"(.proj {refName s} {i} {termS e} {clsS c})"

/-- A typed term as readable pseudo-source (de Bruijn variables as `#i`). -/
partial def gS : G → String
  | .var i _ => s!"#{i}"
  | .lit n => s!"{n}"
  | .call f [] _ => refName f
  | .call f args _ => s!"({refName f} {" ".intercalate (args.map gS)})"
  | .appv f args _ => s!"({gS f} {" ".intercalate (args.map gS)})"
  | .lam m r a _ b => s!"(fun ({bmS m} : {a.name}) ↦{rmS r} {gS b})"
  | .letE lm s v b => s!"(let {letS lm} : {s.name} := {gS v}; {gS b})"
  | .proj _ i e _ => s!"{gS e}.{i}"
  | .case k mj alts ex _ => s!"(match[{k.name}] {gS mj} with {" | ".intercalate (alts.map gS)}){String.join (ex.map fun e => " " ++ gS e)}"
  | .cast e _ => s!"(cast _ {gS e})"
  | .irr => "_"

def udefS (d : UDef) : String :=
  let ps := " ".intercalate (d.params.map fun (t, m) => s!"({bmS m} : {t.name})")
  s!"def {refName d.ref} {ps} : {rmS d.res} {d.rty.name} :=\n    {gS d.body}"

def runDefS (d : UDef) : String :=
  match d.runDef with
  | .body ps res rc rs t =>
    s!"({refName d.ref}, .body #[{", ".intercalate (ps.toList.map paramS)}] {rmS res} {clsS rc} {skelS rs}\n    {termS t})"
  | _ => ""

def valS : Val → String
  | .imm (.con r) => s!"(.imm (.con {refName r}))"
  | .imm (.bits n) => s!"(.imm (.bits {n}))"
  | .imm .irr => "(.imm .irr)"
  | .ref l c t => s!"(.ref {l} {c} {t})"

def cellS : Cell → String
  | .ctor r fs => s!".ctor {refName r} #[{", ".intercalate (fs.toList.map valS)}]"
  | .num n => s!".num {n}"
  | .str s => s!".str {repr s}"
  | .pap r as => s!".pap {refName r} #[{", ".intercalate (as.toList.map valS)}]"
  | .clo .. => ".clo …"
  | .once .. => ".once …"

def heapS (h : Heap) : String :=
  s!"heap (nextCap {h.nextCap}): " ++ ", ".intercalate (h.objs.toList.zipIdx.map fun (o, l) => s!"{l}:⟨{cellS o.cell}, cap {o.cap}⟩")

/-! ## Shrinking -/

partial def G.size : G → Nat
  | .call _ args _ => 1 + (args.map G.size).foldl (· + ·) 0
  | .appv f args _ => 1 + f.size + (args.map G.size).foldl (· + ·) 0
  | .lam _ _ _ _ b => 1 + b.size
  | .letE _ _ v b => 1 + v.size + b.size
  | .proj _ _ e _ => 1 + e.size
  | .case _ mj alts ex _ => 1 + mj.size + (alts.map G.size).foldl (· + ·) 0 + (ex.map G.size).foldl (· + ·) 0
  | .cast e _ => 1 + e.size
  | _ => 1

partial def G.modes : G → Nat
  | .call _ args _ => (args.map G.modes).foldl (· + ·) 0
  | .appv f args _ => f.modes + (args.map G.modes).foldl (· + ·) 0
  | .lam _ _ _ _ b => b.modes
  | .letE lm _ v b => (if lm == .value .many then 0 else 1) + v.modes + b.modes
  | .proj _ _ e _ => e.modes
  | .case _ mj alts ex _ => mj.modes + (alts.map G.modes).foldl (· + ·) 0 + (ex.map G.modes).foldl (· + ·) 0
  | .cast e _ => e.modes
  | _ => 0

def listVariants {α : Type} (xs : List α) (f : α → List α) : List (List α) :=
  (List.range xs.length).flatMap fun i =>
    match xs[i]? with
    | some x => (f x).map fun x' => xs.set i x'
    | none => []

/-- Single-step rewrites of a term: a subterm replaced by its type's leaf, a `let`'s mode set to default. -/
partial def rewrites (g : G) : List G :=
  let here := if g.ty.cls != .irr && (leafOf g.ty).size < g.size then [leafOf g.ty] else []
  let kids := match g with
    | .call f args t => (listVariants args rewrites).map (.call f · t)
    | .appv f args t => (rewrites f).map (.appv · args t) ++ (listVariants args rewrites).map (.appv f · t)
    | .lam m r a b body => (rewrites body).map (.lam m r a b ·)
    | .letE lm s v b => (rewrites v).map (.letE lm s · b) ++ (rewrites b).map (.letE lm s v ·) ++
        (if lm != .value .many then [.letE (.value .many) s v b] else [])
    | .proj s i e t => (rewrites e).map (.proj s i · t)
    | .case k mj alts ex t => (rewrites mj).map (.case k · alts ex t) ++ (listVariants alts rewrites).map (.case k mj · ex t) ++
        (listVariants ex rewrites).map (.case k mj alts · t)
    | .cast e t => (rewrites e).map (.cast · t)
    | _ => []
  let tyEq (a b : Ty) : Bool := a == b
  let hoist := match g with
    | .call _ args t => args.filter (fun a => tyEq a.ty t)
    | .appv f args t => (f :: args).filter (fun a => tyEq a.ty t)
    | .case _ mj alts _ t => (mj :: alts.filter (fun a => match a with | .lam .. => false | _ => true)).filter (fun a => tyEq a.ty t)
    | .cast e t => if tyEq e.ty t then [e] else []
    | .proj _ _ e t => if tyEq e.ty t then [e] else []
    | _ => []
  hoist ++ here ++ kids

partial def G.refs : G → List Ref
  | .call f args _ => f :: args.flatMap G.refs
  | .appv f args _ => f.refs ++ args.flatMap G.refs
  | .lam _ _ _ _ b => b.refs
  | .letE _ _ v b => v.refs ++ b.refs
  | .proj _ _ e _ => e.refs
  | .case _ mj alts ex _ => mj.refs ++ alts.flatMap G.refs ++ ex.flatMap G.refs
  | .cast e _ => e.refs
  | _ => []

/-- Whether `r` occurs only saturated (`n` arguments) in `g`. -/
partial def G.onlySaturated (r : Ref) (n : Nat) : G → Bool
  | .call f args _ => (f != r || args.length == n) && args.all (G.onlySaturated r n)
  | .appv f args _ => f.onlySaturated r n && args.all (G.onlySaturated r n)
  | .lam _ _ _ _ b => b.onlySaturated r n
  | .letE _ _ v b => v.onlySaturated r n && b.onlySaturated r n
  | .proj _ _ e _ => e.onlySaturated r n
  | .case _ mj alts ex _ => mj.onlySaturated r n && alts.all (G.onlySaturated r n) && ex.all (G.onlySaturated r n)
  | .cast e _ => e.onlySaturated r n
  | _ => true

def GProg.measure (gp : GProg) : Nat :=
  ((gp.defs ++ gp.inFns).map fun d => 16 * (d.body.size + 2) + d.body.modes +
    (d.params.filter (·.2 != .many)).length).foldl (· + ·) 0

/-- Single-step variants of a program, the seed `seed` kept. -/
def variants (gp : GProg) (seed : Ref) (inputRefs : List Ref) : List GProg :=
  let all := gp.defs ++ gp.inFns
  let used (r : Ref) : Bool := r == seed || inputRefs.contains r || all.any fun d => d.ref != r && d.body.refs.contains r
  let drops := (gp.defs.filter fun d => !used d.ref).map fun d => { gp with defs := gp.defs.filter (·.ref != d.ref) }
  let dropsF := (gp.inFns.filter fun d => !used d.ref).map fun d => { gp with inFns := gp.inFns.filter (·.ref != d.ref) }
  let bodies := (List.range gp.defs.length).flatMap fun i =>
    match gp.defs[i]? with
    | some d => (rewrites d.body).map fun b => { gp with defs := gp.defs.set i { d with body := b } }
    | none => []
  let bodiesF := (List.range gp.inFns.length).flatMap fun i =>
    match gp.inFns[i]? with
    | some d => (rewrites d.body).map fun b => { gp with inFns := gp.inFns.set i { d with body := b } }
    | none => []
  let modes := (List.range gp.defs.length).flatMap fun i =>
    match gp.defs[i]? with
    | some d =>
      if !(inputRefs.contains d.ref) && all.all (fun e => e.body.onlySaturated d.ref d.params.length) then
        (List.range d.params.length).filterMap fun k =>
          match d.params[k]? with
          | some (t, m) => if m == .many then none
              else some { gp with defs := gp.defs.set i { d with params := d.params.set k (t, .many) } }
          | none => none
      else []
    | none => []
  drops ++ dropsF ++ modes ++ bodies ++ bodiesF

def inputRefsOf (h : Heap) : List Ref :=
  h.objs.toList.filterMap fun o => match o.cell with
    | .pap r _ => some r
    | _ => none

/-- Whether `gp` still exhibits the hit: accepted, inputs meeting `InputsOk`, and a violation of kind `k`. -/
def stillHits (gp : GProg) (seed : Ref) (h : Heap) (args : List Val) (k : Violation) : Bool :=
  let P := gp.prog
  match (gp.defs.find? (·.ref == seed)) with
  | none => false
  | some d =>
    (checkBodies {} P gp.bodies).isAccept &&
    inputsOkB P h (d.params.map fun (t, m) => t.param m).toArray args &&
    (runAll fun f => runR P (checkedOracle P) f seed h args).any fun (_, o) => violation? o == some k

def shrink (gp : GProg) (seed : Ref) (h : Heap) (args : List Val) (k : Violation) (budget : Nat) : GProg × Nat := Id.run do
  let mut cur := gp
  let mut evals := 0
  let mut progress := true
  while progress && evals < budget do
    progress := false
    for v in variants cur seed (inputRefsOf h) do
      if evals ≥ budget then break
      if v.measure ≥ cur.measure then continue
      evals := evals + 1
      if stillHits v seed h args k then
        cur := v
        progress := true
        break
  return (cur, evals)

/-! ## Recognisers (written after the first job; they classify shrunk hits, never steer the generator)

Knockouts first, where one exists: a variant of the program or oracle that removes
exactly the finding's mechanism, after which the checker refuses or the run no
longer violates. Then syntactic shapes. A hit matching none is reported first. -/

/-- Any node satisfying `p`, with the binder modes in scope (index 0 innermost). -/
partial def anyGE (p : List BinderMode → G → Bool) (env : List BinderMode) (g : G) : Bool :=
  p env g || match g with
    | .call _ args _ => args.any (anyGE p env)
    | .appv f args _ => anyGE p env f || args.any (anyGE p env)
    | .lam m _ _ _ b => anyGE p (m :: env) b
    | .letE lm _ v b => anyGE p env v || anyGE p (lm.binderMode :: env) b
    | .proj _ _ e _ => anyGE p env e
    | .case _ mj alts ex _ => anyGE p env mj || alts.any (anyGE p env) || ex.any (anyGE p env)
    | .cast e _ => anyGE p env e
    | _ => false

def anyDef (gp : GProg) (p : List BinderMode → G → Bool) : Bool :=
  (gp.defs ++ gp.inFns).any fun d => anyGE p (d.params.reverse.map (·.2)) d.body

def isCtorRef (r : Ref) : Bool := match r with
  | .ctor .. => true
  | _ => false

partial def freeVarsG (d : Nat) : G → List Nat
  | .var i _ => if i ≥ d then [i - d] else []
  | .call _ args _ => args.flatMap (freeVarsG d)
  | .appv f args _ => freeVarsG d f ++ args.flatMap (freeVarsG d)
  | .lam _ _ _ _ b => freeVarsG (d + 1) b
  | .letE _ _ v b => freeVarsG d v ++ freeVarsG (d + 1) b
  | .proj _ _ e _ => freeVarsG d e
  | .case _ mj alts ex _ => freeVarsG d mj ++ alts.flatMap (freeVarsG d) ++ ex.flatMap (freeVarsG d)
  | .cast e _ => freeVarsG d e
  | _ => []

partial def lamDepth : G → Nat
  | .lam _ _ _ _ b => lamDepth b + 1
  | _ => 0

def fieldCount (k : Ty) (j : Nat) : Nat :=
  match indOf? k with
  | some ik => (ik.shape[j]?.map (·.2.1.length)).getD 0
  | none => 0

/-- A term whose value is a once binding (through `let` bodies, casts, and the
alternatives of a case, each under its λ telescope; MU: the alternatives added,
after MT-dt-first2's seed 5 case 81756 and seed 8 case 75787). -/
partial def onceResult (env : List BinderMode) : G → Bool
  | .var i _ => (env[i]?.map (·.usage == .once)).getD false
  | .letE lm _ _ b => onceResult (lm.binderMode :: env) b
  | .cast e _ => onceResult env e
  | .case _ _ alts _ _ => alts.any (altOnce env)
  | _ => false
where altOnce (env : List BinderMode) : G → Bool
  | .lam m _ _ _ b => altOnce (m :: env) b
  | g => onceResult env g

/-- The outer variable a term's value is (through `let` bodies and the λ telescope of a
one-constructor case), shifted out by `d` binders. -/
partial def resultVar (d : Nat) : G → Option Nat
  | .var i _ => if i ≥ d then some (i - d) else none
  | .letE _ _ _ b => resultVar (d + 1) b
  | .case _ _ [alt] [] _ => resultVar (d + lamDepth alt) (stripLams alt)
  | _ => none
where stripLams : G → G
  | .lam _ _ _ _ b => stripLams b
  | g => g

def arityOf (gp : GProg) (r : Ref) : Option Nat :=
  match (gp.defs ++ gp.inFns).find? (·.ref == r) with
  | some d => some d.params.length
  | none =>
    if r == consumeR || r == lenR || r == callTwiceR || r == exFresh || r == exId || r == exBox || r == exStale then some 1
    else if r == idR || r == addP then some 2
    else if r == constR || r == mkKR then some 4
    else none

def violatesWith (P : Prog) (ext : ExternOracle) (seed : Ref) (h : Heap) (args : List Val) (k : Violation) : Bool :=
  (runAll fun f => runR P ext f seed h args).any fun (_, o) => violation? o == some k

/-! ### Knockouts added by MU -/

/-- The binder modes of a constant's parameters (`consume`'s is unique; other helpers plain). -/
def paramModes (gp : GProg) (r : Ref) : List BinderMode :=
  match (gp.defs ++ gp.inFns).find? (·.ref == r) with
  | some d => d.params.map (·.2)
  | none => if r == consumeR then [.unique] else []

def dropUniqueB : BinderMode → BinderMode
  | .unique => .many
  | .uniqueBorrowed => .borrowed
  | m => m

def dropUniqueR : ResultMode → ResultMode
  | .unique => .shared
  | .uniqueBorrowed => .borrowed
  | m => m

/-- Finding 17's knockout on types: a unique mode on a leaf (a binder of class leaf,
an arrow whose result is a leaf) made plain (borrowed stays). -/
partial def Ty.knock17 : Ty → Ty
  | .arr m r a b =>
    .arr (if a.cls == .leaf then dropUniqueB m else m) (if b.cls == .leaf then dropUniqueR r else r) a.knock17 b.knock17
  | t => t

partial def G.knock17 : G → G
  | .var i t => .var i t.knock17
  | .call f args t => .call f (args.map G.knock17) t.knock17
  | .appv f args t => .appv f.knock17 (args.map G.knock17) t.knock17
  | .lam m r a b body =>
    .lam (if a.cls == .leaf then dropUniqueB m else m) (if b.cls == .leaf then dropUniqueR r else r)
      a.knock17 b.knock17 body.knock17
  | .letE lm s v b =>
    let lm' := match lm with
      | .value m => if s.cls == .leaf then LetMode.value (dropUniqueB m) else lm
      | .borrow => .borrow
    .letE lm' s.knock17 v.knock17 b.knock17
  | .proj s i e t => .proj s i e.knock17 t.knock17
  | .case k mj alts ex t => .case k mj.knock17 (alts.map G.knock17) (ex.map G.knock17) t.knock17
  | .cast e t => .cast e.knock17 t.knock17
  | g => g

/-- Every unique mode on a leaf made plain, everywhere in the program (interfaces,
skeletons, binders), so that call sites and bodies stay in step. -/
def GProg.knock17 (gp : GProg) : GProg :=
  let f (d : UDef) : UDef :=
    { d with params := d.params.map (fun (t, m) => (t.knock17, if t.cls == .leaf then dropUniqueB m else m)),
             res := if d.rty.cls == .leaf then dropUniqueR d.res else d.res,
             rty := d.rty.knock17, body := d.body.knock17 }
  { gp with defs := gp.defs.map f, inFns := gp.inFns.map f }

/-- Candidate 19's knockout: a borrowed mode on a leaf made plain (unique and once kept). -/
def dropBorrowB : BinderMode → BinderMode
  | .borrowed => .many
  | .uniqueBorrowed => .unique
  | .onceBorrowed => .once
  | m => m

partial def Ty.knock19 : Ty → Ty
  | .arr m r a b => .arr (if a.cls == .leaf then dropBorrowB m else m) r a.knock19 b.knock19
  | t => t

partial def Ty.hasUniqueValResult : Ty → Bool
  | .arr _ r _ b => (r.isUnique && b.cls == .val) || b.hasUniqueValResult
  | _ => false

partial def G.knock19 : G → G
  | .var i t => .var i t.knock19
  | .call f args t => .call f (args.map G.knock19) t.knock19
  | .appv f args t => .appv f.knock19 (args.map G.knock19) t.knock19
  | .lam m r a b body => .lam (if a.cls == .leaf then dropBorrowB m else m) r a.knock19 b.knock19 body.knock19
  | .letE lm s v b =>
    let lm' := match lm with
      | .value m => if s.cls == .leaf then LetMode.value (dropBorrowB m) else lm
      | .borrow => if s.cls == .leaf then LetMode.value .many else .borrow
    .letE lm' s.knock19 v.knock19 b.knock19
  | .proj s i e t => .proj s i e.knock19 t.knock19
  | .case k mj alts ex t => .case k mj.knock19 (alts.map G.knock19) (ex.map G.knock19) t.knock19
  | .cast e t => .cast e.knock19 t.knock19
  | g => g

def GProg.knock19 (gp : GProg) : GProg :=
  let f (d : UDef) : UDef :=
    { d with params := d.params.map (fun (t, m) => (t.knock19, if t.cls == .leaf then dropBorrowB m else m)),
             rty := d.rty.knock19, body := d.body.knock19 }
  { gp with defs := gp.defs.map f, inFns := gp.inFns.map f }

/-- Every cast between different types (reachable only under an absurd hypothesis)
replaced by its type's closed leaf: the stuck-cause knockout. -/
partial def G.fixCasts : G → G
  | .call f args t => .call f (args.map G.fixCasts) t
  | .appv f args t => .appv f.fixCasts (args.map G.fixCasts) t
  | .lam m r a b body => .lam m r a b body.fixCasts
  | .letE lm s v b => .letE lm s v.fixCasts b.fixCasts
  | .proj s i e t => .proj s i e.fixCasts t
  | .case k mj alts ex t => .case k mj.fixCasts (alts.map G.fixCasts) (ex.map G.fixCasts) t
  | .cast e t => if e.ty == t then .cast e.fixCasts t else leafOf t
  | g => g

def GProg.fixCasts (gp : GProg) : GProg :=
  let f (d : UDef) : UDef := { d with body := d.body.fixCasts }
  { gp with defs := gp.defs.map f, inFns := gp.inFns.map f }

/-- Finding 16's knockout: a case with extra arguments judged at class `val` (its control). -/
partial def caseExValT : Term → Term
  | .lam p r rc fvs b => .lam p r rc fvs (caseExValT b)
  | .app f a c => .app (caseExValT f) (caseExValT a) c
  | .letE m d v b => .letE m d (caseExValT v) (caseExValT b)
  | .proj s i e c => .proj s i (caseExValT e) c
  | .case k mj alts ex c =>
    .case k (caseExValT mj) (alts.map caseExValT) (ex.map caseExValT) (if ex.isEmpty then c else .val)
  | t => t

def mapBodies (f : Term → Term) (P : Prog) : Prog :=
  { P with defs := P.defs.map fun (r, d) => (r, match d with
      | .body ps res rc rs t => .body ps res rc rs (f t)
      | d => d) }

/-- Finding 18's knockout: `SBox`'s field inherited instead of `@shared`. -/
def sboxInherited (P : Prog) : Prog :=
  { P with defs := P.defs.map fun (r, d) =>
      if r == sboxC then (r, .ctor sboxI 0 0 #[fieldOf .val]) else (r, d) }

/-- Whether the term reads `SBox`'s `@shared` field (a projection or a case on it). -/
def readsShared (g : G) : Bool := match g with
  | .proj s _ _ _ => s == sboxI
  | .case k _ _ _ _ => k == .sbox
  | _ => false

def callsUser (gp : GProg) (g : G) : Bool := match g with
  | .call f _ _ => (gp.defs ++ gp.inFns).any (·.ref == f)
  | .appv .. => true
  | _ => false

/-- The refusal witness's head, `""` when the checker accepts. -/
def refusalHead : Verdict → String
  | .refuse _ w => (w.splitOn ":").headD w
  | .decline r => s!"decline {r}"
  | .accept .. => ""

/-- The labels of a shrunk hit, in order of reliability. -/
def recognise (gp : GProg) (seed : Ref) (h : Heap) (args : List Val) (k : Violation) (ill : Bool) : List String :=
  let P := gp.prog
  let bodies := gp.bodies
  let os := runAll fun f => runR P (checkedOracle P) f seed h args
  let top := (os.back?.map (·.2)).getD .stuck
  let refusesWith (q : Param → Bool) := !(checkBodies {} (dropNoLeafWhere q P) bodies).isAccept
  let isArrow (p : Param) : Bool := match p.skel with | .arrow .. => true | _ => false
  let uses (r : Ref) := anyDef gp fun _ g => match g with | .call f _ _ => f == r | _ => false
  let labels : List (Bool × String) := [
    (ill, "F15 (ill-typed stream)"),
    (uses exStale && !violatesWith P (oracleFamilyWith true false) seed h args k, "F14 (stale capability from an extern)"),
    (uses exBox && !violatesWith P (oracleFamilyWith false true) seed h args k, "F5 (extern stores a confined value in a @shared field)"),
    ((violation? top).isNone && (match top with | .value .. => true | _ => false), "F7 (violation only at some fuels)"),
    (refusesWith (fun p => p.cls == .leaf), "F1 (noLeaf at a Nat parameter)"),
    (refusesWith isArrow, "F2 (noLeaf at a function parameter)"),
    (refusesWith (fun p => p.cls == .val && !isArrow p), "F3 family (noLeaf at a data parameter)"),
    -- MU: before the syntactic F12, so that a primitive's pap that only carries finding 17's confined leaf
    -- is labelled 17 (MU-dt-r3 seed 3 case 87641)
    -- MU: by knockout (every unique mode on a leaf made plain: the checker then refuses with borrowEscape),
    -- which covers let binders, results, λ and case-alternative binders (MT-dt-first2 seed 8 case 93805)
    (k == .borrowEscape && (let kp := gp.knock17; refusalHead (checkBodies {} kp.prog kp.bodies) == "borrowEscape"),
      "F17 (a unique mode on a leaf keeps its confinement)"),
    -- MU: the same knockout together with F1-3's (`noLeaf := false` everywhere), for the landed tree, where a
    -- unique leaf result's knockout alone is hidden by `noLeaf` (MU-dt-landed seed 3 case 28008)
    (k == .borrowEscape && (let kp := gp.knock17; refusalHead (checkBodies {} (dropNoLeaf kp.prog) kp.bodies) == "borrowEscape"),
      "F17+F1-3 (finding 17's mechanism, its knockout hidden by noLeaf: needs both knockouts)"),
    (anyDef gp (fun _ g => match g with | .call f args _ => f == addP && args.length < 2 | _ => false) && k == .borrowEscape,
      "F12 (a primitive's partial application)"),
    (k == .revokedUse && anyDef gp (fun _ g => match g with
      | .call f args _ => isCtorRef f && (args.filterMap (resultVar 0)).length != ((args.filterMap (resultVar 0)).eraseDups).length
      | _ => false), "F8 (a unique value stored twice in one cell)"),
    -- MU, after MR's `bad11b (@once f) := useBox ⟨f⟩` (open at 7e9d1c656): a once binding stored in
    -- a constructor's field (no constructor of this universe has a function field, so that route is
    -- out of the grammar) or captured by a closure that is passed on or let-bound (a case
    -- alternative's λ telescope binds fields and is not such a closure), then called through it
    (k == .onceReentry && anyDef gp (fun env g =>
      let capturesOnce (a : G) : Bool := match a with
        | .lam .. => (freeVarsG 0 a).any fun i => (env[i]?.map (·.usage == .once)).getD false
        | _ => false
      match g with
      | .call f args _ => (isCtorRef f && args.any (onceResult env)) || args.any capturesOnce
      | .appv _ args _ => args.any capturesOnce
      | .letE _ _ v _ => capturesOnce v
      | _ => false), "F11b (a once binding stored in a cell or captured by a closure, called through it)"),
    (k == .onceReentry && anyDef gp (fun env g =>
      match g with
      | .call _ args _ => args.any (onceResult env)
      | .appv _ args _ => args.any (onceResult env)
      | _ => false), "F11 (a once binding passed on)"),
    (k == .revokedUse && anyDef gp (fun env g =>
      let consumingLam (a : G) : Bool := match a with
        | .lam .. => (freeVarsG 0 a).any fun i => (env[i]?.map (·.isUnique)).getD false
        | _ => false
      -- MU: a partial application that has transferred a unique argument (MT-dt-first2 seed 3 case 89080)
      let uniquePap (a : G) : Bool := match a with
        | .call f as _ => match arityOf gp f with
          | some n => as.length < n && (as.zip (paramModes gp f)).any (·.2.isUnique)
          | none => false
        | _ => false
      match g with
      | .call _ args _ => args.any fun a => consumingLam a || uniquePap a
      | .appv _ args _ => args.any fun a => consumingLam a || uniquePap a
      | _ => false), "F10 (a once-only closure lent)"),
    -- MU: by its control (the case at class val refuses), revokedUse only (F16's violation)
    (k == .revokedUse && anyDef gp (fun _ g => match g with | .case _ _ _ ex t => !ex.isEmpty && t.cls != .val | _ => false) &&
      !(checkBodies {} (mapBodies caseExValT P) bodies).isAccept,
      "F16 (a case's extra arguments at the case's class)"),
    (k == .revokedUse && anyDef gp (fun _ g => match g with | .appv _ args _ => args.length ≥ 2 | _ => false),
      "F13 (a function value of two arguments, one application at a time)"),
    -- MU: SBox's field inherited makes the checker refuse, and the @shared field is read from a cell
    -- a callee built (a call's result, or a cell built in another definition)
    (k == .borrowEscape && !(checkBodies {} (sboxInherited P) bodies).isAccept &&
      (anyDef gp (fun _ g => match g with
        | .proj s _ e _ => s == sboxI && callsUser gp e
        | .case k mj _ _ _ => k == .sbox && callsUser gp mj
        | _ => false) ||
       ((gp.defs ++ gp.inFns).any fun d1 => (gp.defs ++ gp.inFns).any fun d2 => d1.ref != d2.ref &&
         anyGE (fun _ g => match g with | .call f _ _ => f == sboxC | _ => false) [] d1.body &&
         anyGE (fun _ g => readsShared g) [] d2.body)),
      "F18 (a @shared field built by a callee holds the caller's confined value)"),
    -- MU: candidate 19 (a borrowed leaf passed at a plain parameter keeps its confinement into a cell
    -- whose unique return transfers it): a unique result of class val somewhere, and with every borrowed
    -- mode on a leaf made plain the run no longer violates
    (k == .borrowEscape &&
      ((gp.defs ++ gp.inFns).any (fun d => d.res.isUnique && d.rty.cls == .val) ||
       anyDef gp (fun _ g => match g with | .lam _ r _ b _ => r.isUnique && b.cls == .val | _ => false) ||
       (gp.defs ++ gp.inFns).any (fun d => d.params.any fun (t, _) => t.hasUniqueValResult)) &&
      (let kp := gp.knock19; !violatesWith kp.prog (checkedOracle kp.prog) seed h args k),
      "C19 (a borrowed leaf passed at a plain parameter keeps its confinement; the callee's unique return of a cell holding it)"),
    (k == .borrowEscape && anyDef gp (fun _ g => match g with
      | .appv .. => true
      | .call f args _ => match arityOf gp f with
        | some n => args.length > n
        | none => false
      | .case k _ alts ex _ => !ex.isEmpty || alts.zipIdx.any (fun (a, j) => lamDepth a < fieldCount k j)
      | _ => false), "F9 family (an application drops the function's regions)")]
  labels.filterMap fun (b, l) => if b then some l else none

/-! ## The driver -/

structure Cfg where
  seed : Nat := 1
  /-- the first case (MU: `--from i --n 1` regenerates case `i` alone; case `i` draws from `mix(seed, i)` only) -/
  start : Nat := 0
  n : Nat := 100
  maxDefs : Nat := 3
  depth : Nat := 4
  inputs : Nat := 3
  illInputs : Nat := 2
  externs : Bool := true
  shrinkBudget : Nat := 400
  outDir : String := "out"
  maxHitsPrinted : Nat := 40
  classify : Bool := false
  /-- the tree's `noLeafType` rule is the landed one (probed at start-up, `treeNoLeafRule`) -/
  nlRule : Bool := true
  /-- how many stuck runs at the top fuel to print (MU: for tracing their causes) -/
  maxStuckPrinted : Nat := 3
  /-- print every case's program and verdicts (MU: with `--from i --n 1`, to look at one case) -/
  showCases : Bool := false

structure Tally where
  programs : Nat := 0
  accept : Nat := 0
  refuse : Nat := 0
  decline : Nat := 0
  counterexamples : Nat := 0
  acceptClean : Nat := 0
  refuseViolates : Nat := 0
  completeness : Nat := 0
  noLeafCost : Nat := 0
  variantAccepts : Nat := 0
  variantRefusesLandedAccepts : Nat := 0
  runs : Nat := 0
  stuckTop : Nat := 0
  stuckCast : Nat := 0
  stuckOther : Nat := 0
  oofTop : Nat := 0
  notCovered : Nat := 0
  genBug : Nat := 0
  noAdmissible : Nat := 0
  admittedByK : Nat := 0
  nonMono : Nat := 0
  illPrograms : Nat := 0
  illHits : Nat := 0
  illRuns : Nat := 0
  selfOk : Nat := 0
  selfBad : Nat := 0
  violKinds : List (String × Nat) := []
  witnesses : List (String × Nat) := []
  labels : List (String × Nat) := []
  deriving Inhabited

def bump (xs : List (String × Nat)) (k : String) : List (String × Nat) :=
  match xs.find? (·.1 == k) with
  | some _ => xs.map fun (a, n) => if a == k then (a, n + 1) else (a, n)
  | none => xs ++ [(k, 1)]

/-- One seed's run of `n` programs. -/
def runSeed (cfg : Cfg) (st : STStore) : IO Tally := do
  let mut t : Tally := {}
  let mut printed : List String := []
  let mut hitNo := 0
  let mut vlines : Array String := #[]
  IO.FS.createDirAll s!"{cfg.outDir}/{cfg.seed}"
  for i in [cfg.start:cfg.start + cfg.n] do
    let g0 := Rng.ofCase cfg.seed i
    let ((gp, nDefs), g1) := (do
      let nd := 1 + (← rand cfg.maxDefs)
      pure (← genProg cfg.externs nd cfg.depth, nd) : R (GProg × Nat)).run g0
    let _ := nDefs
    let P := gp.prog
    t := { t with programs := t.programs + 1 }
    -- self-test of every generated interface
    for d in gp.defs ++ gp.inFns do
      match selfTest st cfg.nlRule d with
      | none => t := { t with selfOk := t.selfOk + 1 }
      | some msg =>
        t := { t with selfBad := t.selfBad + 1 }
        if t.selfBad ≤ 5 then IO.println s!"[self-test MISMATCH] seed {cfg.seed} case {i} {refName d.ref}: {msg}"
    let vL := checkBodies {} P gp.bodies
    let vV := checkBodies {} (dropNoLeaf P) gp.bodies
    if cfg.showCases then
      IO.println s!"[show] seed {cfg.seed} case {i}: checker {verdictShort vL} ({match vL with | .refuse a w => s!"{w} @ {a}" | _ => ""}); noLeaf := false variant {verdictShort vV}\n  {"\n  ".intercalate ((gp.defs ++ gp.inFns).map udefS)}\n  run definitions:\n  {"\n  ".intercalate ((gp.defs ++ gp.inFns).map runDefS)}"
    match vL with
    | .accept .. => t := { t with accept := t.accept + 1 }
    | .refuse .. => t := { t with refuse := t.refuse + 1 }
    | .decline .. => t := { t with decline := t.decline + 1 }
    if vV.isAccept then t := { t with variantAccepts := t.variantAccepts + 1 }
    -- runs, well typed then ill typed
    let mut g := g1
    let mut violated : Option (UDef × Heap × List Val × Violation × List Nat) := none
    let mut illViol : Option (UDef × Heap × List Val × Violation × List Nat) := none
    for d in gp.defs do
      let params := (d.params.map fun (ty, m) => ty.param m).toArray
      -- `ArgOk` asks an erased parameter for `irr` and a leaf one for a number cell: no input exists
      let wasSkipped := params.any (fun p => p.mode == .erased && (p.cls == .leaf || match p.skel with | .arrow .. => true | _ => false))
      if !stmtV2 && wasSkipped then
        t := { t with noAdmissible := t.noAdmissible + 1 }
        continue
      -- MU: under repair K such a seed is admitted; its inputs come from a stream of their own, so
      -- that every other seed's inputs stay those of the trees before K
      let mut gK := Rng.ofCase (cfg.seed + 1000) (i * 16 + (gp.defs.findIdx? (·.ref == d.ref)).getD 0)
      if wasSkipped then t := { t with admittedByK := t.admittedByK + 1 }
      for k in [0:cfg.inputs + cfg.illInputs] do
        let ill := k ≥ cfg.inputs
        let ((h, args), g') := (genInputs gp ill d.params).run (if wasSkipped then gK else g)
        if wasSkipped then gK := g' else g := g'
        unless inputsOkB P h params args do
          t := { t with genBug := t.genBug + 1 }
          if t.genBug ≤ 3 then
            IO.println s!"[inputsOkB fails] case {i} {refName d.ref}: {inputsWhy P h params args}; {", ".intercalate (args.map valS)}; {heapS h}\n  {udefS d}"
          continue
        let os := runAll fun f => runR P (checkedOracle P) f d.ref h args
        if cfg.showCases then
          let changes := (os.toList.zip ((none :: os.toList.map some).take os.size)).filterMap fun ((f, o), prev) =>
            match prev with
            | some (_, po) => if oName po == oName o then none else some s!"{f}: {oName o}"
            | none => some s!"{f}: {oName o}"
          IO.println s!"[show]   {refName d.ref}{if ill then " (ill-typed)" else ""} on {", ".intercalate (args.map valS)}; {heapS h}\n    outcome by fuel (changes): {changes}"
        if ill then t := { t with illRuns := t.illRuns + 1 } else t := { t with runs := t.runs + 1 }
        let top := (os.back?.map (·.2)).getD .stuck
        if !ill then
          match top with
          | .stuck =>
            match runR P oracleFamily 100000 d.ref h args with
            | .stuck =>
              t := { t with stuckTop := t.stuckTop + 1 }
              -- MU: the cause, by knockout: every cast between different types (reachable only under
              -- an absurd hypothesis) replaced by its type's closed leaf; a run that is then not stuck
              -- was stuck at such a cast
              let fixed := gp.fixCasts
              let P' := fixed.prog
              match runR P' oracleFamily 100000 d.ref h args with
              | .stuck =>
                t := { t with stuckOther := t.stuckOther + 1 }
                if t.stuckOther ≤ cfg.maxStuckPrinted then
                  IO.println s!"[stuck at fuel 100000, not an absurd cast] case {i} {refName d.ref}: {", ".intercalate (args.map valS)}; {heapS h}\n  {"\n  ".intercalate ((gp.defs ++ gp.inFns).map udefS)}"
              | _ =>
                t := { t with stuckCast := t.stuckCast + 1 }
                if t.stuckCast ≤ 2 then
                  IO.println s!"[stuck at fuel 100000, an absurd cast] case {i} {refName d.ref}: {", ".intercalate (args.map valS)}; {heapS h}\n  {"\n  ".intercalate ((gp.defs ++ gp.inFns).map udefS)}"
            | _ =>
              t := { t with notCovered := t.notCovered + 1 }
              if t.notCovered ≤ 2 then
                IO.println s!"[not covered] case {i} {refName d.ref}: {", ".intercalate (args.map valS)}\n  {"\n  ".intercalate ((gp.defs ++ gp.inFns).map udefS)}"
          | .outOfFuel => t := { t with oofTop := t.oofTop + 1 }
          | _ => pure ()
          if nonMonotone os then t := { t with nonMono := t.nonMono + 1 }
        let vfs := (os.filter fun (_, o) => (violation? o).isSome).toList
        if let some (_, o) := vfs.head? then
          if let some kind := violation? o then
            let found := (d, h, args, kind, vfs.map (·.1))
            if ill then
              if illViol.isNone then illViol := some found
            else
              if violated.isNone then violated := some found
    -- classification
    match vL, violated with
    | .accept .., some _ => t := { t with counterexamples := t.counterexamples + 1 }
    | .accept .., none =>
      t := { t with acceptClean := t.acceptClean + 1 }
      if !vV.isAccept then t := { t with noLeafCost := t.noLeafCost + 1 }
    | .refuse _ w, none =>
      t := { t with completeness := t.completeness + 1, witnesses := bump t.witnesses ((w.splitOn ":").headD w) }
    | .refuse .., some _ => t := { t with refuseViolates := t.refuseViolates + 1 }
    | _, _ => pure ()
    if vL.isAccept && !vV.isAccept then t := { t with variantRefusesLandedAccepts := t.variantRefusesLandedAccepts + 1 }
    let mut labCode := "-"
    let mut kindS := "-"
    let hit : Option (UDef × Heap × List Val × Violation × List Nat × Bool) :=
      match vL.isAccept, violated, illViol with
      | true, some (d, h, a, k, fs), _ => some (d, h, a, k, fs, false)
      | true, none, some (d, h, a, k, fs) => some (d, h, a, k, fs, true)
      | _, _, _ => none
    if let some (d, h, args, kind, fs, ill) := hit then
      if ill then t := { t with illPrograms := t.illPrograms + 1, illHits := t.illHits + 1 }
      t := { t with violKinds := bump t.violKinds s!"{repr kind}{if ill then " (ill-typed)" else ""}" }
      let (small, evals) := shrink gp d.ref h args kind cfg.shrinkBudget
      let P' := small.prog
      let os' := runAll fun f => runR P' (checkedOracle P') f d.ref h args
      let vfs' := (os'.filter fun (_, o) => violation? o == some kind).toList.map (·.1)
      let src := "\n".intercalate ((small.defs ++ small.inFns).map udefS)
      let lean := "\n".intercalate ((small.defs ++ small.inFns).map runDefS)
      let labs := if cfg.classify then recognise small d.ref h args kind ill else []
      let label := labs.headD (if cfg.classify then "UNRECOGNISED" else "unclassified")
      labCode := (label.splitOn " ").headD label
      kindS := (s!"{repr kind}".splitOn ".").getLast!
      t := { t with labels := bump t.labels label }
      let key := if cfg.classify && label != "UNRECOGNISED" then label else s!"{repr kind}|{ill}|{src}"
      hitNo := hitNo + 1
      let text := s!"HIT [{label}] (all labels: {labs}) seed {cfg.seed} case {i} seed-def {refName d.ref} kind {repr kind}{if ill then " ILL-TYPED STREAM" else ""}\n  original fuels with a violation: {fs.take 12}\n  shrunk ({evals} evaluations), fuels with the violation: {vfs'.take 12}\n  inputs: {", ".intercalate (args.map valS)}; {heapS h}\n  source:\n  {src}\n  run definitions:\n  {lean}\n"
      if hitNo ≤ 400 then IO.FS.writeFile s!"{cfg.outDir}/{cfg.seed}/hit-{hitNo}.txt" text
      unless printed.contains key do
        printed := printed ++ [key]
        if printed.length ≤ cfg.maxHitsPrinted then IO.println text
    -- one line per case: case, verdict, clean or violates (typed stream), the `noLeaf := false`
    -- variant's verdict, the hit's first label and violation kind (`-` without a hit), and after
    -- ` | ` the refusal's witness and place
    let vc (v : Verdict) : String := match v with | .accept .. => "A" | .refuse .. => "R" | .decline .. => "D"
    let wit := match vL with
      | .refuse at_ w => s!"{w} @ {at_}"
      | .decline r => r
      | .accept .. => ""
    vlines := vlines.push s!"{i} {vc vL} {if violated.isSome then "V" else "C"} {vc vV} {labCode} {kindS} | {wit.replace "\n" " "}"
  IO.FS.writeFile s!"{cfg.outDir}/{cfg.seed}/verdicts.txt" ("\n".intercalate vlines.toList ++ "\n")
  return t

def tallyS (t : Tally) : String :=
  s!"programs {t.programs}: accept {t.accept}, refuse {t.refuse}, decline {t.decline}\n" ++
  s!"  counterexamples (accept, typed input, a violation) {t.counterexamples}; ill-typed-stream hits {t.illHits}\n" ++
  s!"  accept and clean {t.acceptClean}; refuse and violates {t.refuseViolates}; refuse and clean (completeness) {t.completeness}\n" ++
  s!"  noLeaf := false variant: accepts {t.variantAccepts}; refuses where landed accepts {t.variantRefusesLandedAccepts}; of those clean (cost of dropping) {t.noLeafCost}\n" ++
  s!"  runs {t.runs} (+ ill {t.illRuns}): stuck at top fuel {t.stuckTop} (at an absurd cast {t.stuckCast}, other {t.stuckOther}), out of fuel at top {t.oofTop}, not covered {t.notCovered}, inputs failing inputsOkB {t.genBug}, seeds with no admissible input (an erased leaf or arrow parameter) {t.noAdmissible}, admitted by repair K {t.admittedByK}, non-monotone {t.nonMono}\n" ++
  s!"  self-test: {t.selfOk} interfaces agree with the reader's rules, {t.selfBad} disagree\n" ++
  s!"  violation kinds of hits: {t.violKinds}\n" ++
  s!"  refusal witnesses (completeness programs): {t.witnesses}\n" ++
  s!"  hits by recogniser: {t.labels}"

def parseArgs (args : List String) (cfg : Cfg) : Cfg :=
  match args with
  | "--seed" :: v :: rest => parseArgs rest { cfg with seed := v.toNat! }
  | "--n" :: v :: rest => parseArgs rest { cfg with n := v.toNat! }
  | "--defs" :: v :: rest => parseArgs rest { cfg with maxDefs := v.toNat! }
  | "--depth" :: v :: rest => parseArgs rest { cfg with depth := v.toNat! }
  | "--inputs" :: v :: rest => parseArgs rest { cfg with inputs := v.toNat! }
  | "--ill" :: v :: rest => parseArgs rest { cfg with illInputs := v.toNat! }
  | "--no-externs" :: rest => parseArgs rest { cfg with externs := false }
  | "--shrink" :: v :: rest => parseArgs rest { cfg with shrinkBudget := v.toNat! }
  | "--out" :: v :: rest => parseArgs rest { cfg with outDir := v }
  | "--classify" :: rest => parseArgs rest { cfg with classify := true }
  | "--from" :: v :: rest => parseArgs rest { cfg with start := v.toNat! }
  | "--stuck" :: v :: rest => parseArgs rest { cfg with maxStuckPrinted := v.toNat! }
  | "--hits" :: v :: rest => parseArgs rest { cfg with maxHitsPrinted := v.toNat! }
  | "--show" :: rest => parseArgs rest { cfg with showCases := true }
  | _ :: rest => parseArgs rest cfg
  | [] => cfg

/-! ## Comparing two trees' verdict files (MU)

`difftest --compare A B`: `A/<seed>/verdicts.txt` and `B/<seed>/verdicts.txt` for
seeds 1 to 8, the same cases of the same generator (case `i` of seed `s` is the
same program and inputs on both trees). A is the landed tree, B a repaired one. -/

structure VLine where
  i : Nat
  v : String
  run : String
  var : String
  lab : String
  kind : String
  wit : String
  deriving Inhabited

def parseV (s : String) : Option VLine :=
  let (left, wit) := match s.splitOn " | " with
    | [] => ("", "")
    | [l] => (l, "")
    | l :: rest => (l, " | ".intercalate rest)
  match left.splitOn " " with
  | [i, v, run, var, lab, kind] => some { i := i.toNat!, v, run, var, lab, kind, wit }
  | _ => none


def sortedS (xs : List (String × Nat)) (top : Nat := 1000) : String :=
  let ys := (xs.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))).toList.take top
  "\n".intercalate (ys.map fun (k, n) => s!"    {n}\t{k}")

def witHead (w : String) : String := (w.splitOn ":").headD w

/-- The witness without the place (`… @ at`). -/
def witBody (w : String) : String := (w.splitOn " @ ").headD w

def compareDirs (a b : String) : IO UInt32 := do
  let mut pairs : Array (Nat × VLine × VLine) := #[]
  for s in [1:9] do
    let fa : System.FilePath := s!"{a}/{s}/verdicts.txt"
    let fb : System.FilePath := s!"{b}/{s}/verdicts.txt"
    unless (← fa.pathExists) && (← fb.pathExists) do
      IO.println s!"seed {s}: a verdict file is missing"
      continue
    let xs := (← IO.FS.lines fa).filterMap parseV
    let ys := (← IO.FS.lines fb).filterMap parseV
    if xs.size != ys.size then IO.println s!"seed {s}: {xs.size} vs {ys.size} lines"
    for (x, y) in xs.zip ys do
      if x.i != y.i then
        IO.println s!"seed {s}: case {x.i} vs {y.i}, misaligned"
        return 1
      pairs := pairs.push (s, x, y)
  let n := pairs.size
  let cnt (p : Nat × VLine × VLine → Bool) := (pairs.filter p).size
  IO.println s!"compare A = {a}, B = {b}: {n} programs"
  for isA in [true, false] do
    let sel (q : Nat × VLine × VLine) : VLine := if isA then q.2.1 else q.2.2
    IO.println s!"  {if isA then "A" else "B"}: accept {cnt fun q => (sel q).v == "A"}, refuse {cnt fun q => (sel q).v == "R"}, decline {cnt fun q => (sel q).v == "D"}; counterexamples {cnt fun q => (sel q).v == "A" && (sel q).run == "V"}; hits (with ill-typed) {cnt fun q => (sel q).lab != "-"}; accept and clean {cnt fun q => (sel q).v == "A" && (sel q).run == "C"}"
  -- hits by first label
  let mut labs : List (String × Nat × Nat) := []
  for (_, x, y) in pairs do
    for (l, isA) in [(x.lab, true), (y.lab, false)] do
      if l != "-" then
        labs := match labs.find? (·.1 == l) with
          | some _ => labs.map fun (k, p, q) => if k == l then (k, if isA then p + 1 else p, if isA then q else q + 1) else (k, p, q)
          | none => labs ++ [(l, if isA then 1 else 0, if isA then 0 else 1)]
  IO.println "hits by first label: label, A, B"
  for (l, p, q) in labs.toArray.qsort (fun u v => u.1 < v.1) do IO.println s!"    {l}\t{p}\t{q}"
  -- transitions of hit cases
  let mut tr : List (String × Nat) := []
  for (_, x, y) in pairs do
    if x.lab != "-" || y.lab != "-" then
      let yS := if y.lab != "-" then y.lab else if y.v == "R" then s!"refused ({witHead y.wit})" else if y.v == "A" && y.run == "C" then "accepted, clean" else s!"{y.v} {y.run}"
      tr := bump tr s!"{x.lab} -> {yS}"
  IO.println s!"hit cases, A's label -> B:\n{sortedS tr}"
  -- B's hits to look at: unrecognised, or of a class a repair so far should have removed
  let mut bLabs : List String := []
  for (_, _, y) in pairs do
    if y.lab != "-" && !bLabs.contains y.lab then bLabs := bLabs ++ [y.lab]
  for l in bLabs do
    let cs := pairs.filter fun (_, _, y) => y.lab == l
    let k := if l == "UNRECOGNISED" then 40 else 8
    IO.println s!"B hits labelled {l}: {cs.size}; first: {(cs.toList.take k).map fun (s, x, y) => s!"s{s}c{y.i}({y.kind}, A {x.lab})"}"
  -- completeness: A accepts and its runs never violate, B refuses
  let lost := pairs.filter fun (_, x, y) => x.v == "A" && x.run == "C" && y.v == "R"
  let mut byCause : List (String × Nat) := []
  let mut byWit : List (String × Nat) := []
  for (_, x, y) in lost do
    byCause := bump byCause (if x.var == "R" then "repair A (the noLeaf := false variant on A refuses too)" else "not A's (B refuses, the noLeaf := false variant on A accepts)")
    byWit := bump byWit s!"[{if x.var == "R" then "A" else "not A"}] {witBody y.wit}"
  IO.println s!"completeness: A accepts and never violates at any fuel tried, B refuses: {lost.size} (of A's {cnt fun q => q.2.1.v == "A" && q.2.1.run == "C"} clean acceptances); of these, B's own runs clean {(lost.filter fun q => q.2.2.run == "C").size}"
  IO.println s!"  by cause:\n{sortedS byCause}"
  IO.println s!"  by B's witness:\n{sortedS byWit 40}"
  let mut seenW : List String := []
  for (_, _, y) in lost do
    let w := witBody y.wit
    unless seenW.contains w do seenW := seenW ++ [w]
  IO.println "  examples per witness:"
  for w in seenW do
    let cs := lost.filter fun (_, _, y) => witBody y.wit == w
    IO.println s!"    {w}: {(cs.toList.take 4).map fun (s, _, y) => s!"s{s}c{y.i}"}"
  IO.println s!"  first cases: {(lost.toList.take 30).map fun (s, _, y) => s!"s{s}c{y.i}"}"
  let lostNotA := lost.filter fun (_, x, _) => x.var != "R"
  IO.println s!"  first not-A cases: {(lostNotA.toList.take 30).map fun (s, _, y) => s!"s{s}c{y.i}"}"
  -- counterexamples on A, by what B does
  let mut cx : List (String × Nat) := []
  for (_, x, y) in pairs do
    if x.v == "A" && x.run == "V" then
      cx := bump cx (if y.v == "R" then s!"B refuses ({witHead y.wit})" else if y.run == "C" then "B accepts, its runs clean (a change of runR)" else "B accepts, still violates")
  IO.println s!"A's counterexamples (typed) on B:\n{sortedS cx}"
  -- verdicts that moved the other way
  let gained := pairs.filter fun (_, x, y) => x.v != "A" && y.v == "A"
  IO.println s!"B accepts where A does not: {gained.size}; first: {(gained.toList.take 30).map fun (s, x, y) => s!"s{s}c{y.i}(A {x.v} {witHead x.wit})"}"
  let runMoved := pairs.filter fun (_, x, y) => x.run != y.run
  IO.println s!"runs that moved (clean <-> violates, typed stream): {runMoved.size}; A V -> B C {(runMoved.filter fun q => q.2.1.run == "V").size}; first: {(runMoved.toList.take 30).map fun (s, x, y) => s!"s{s}c{y.i}({x.run}->{y.run}, {x.v}/{y.v})"}"
  return 0

end MT.DiffTest

open MT.DiffTest in
def main (args : List String) : IO UInt32 := do
  if let "--compare" :: a :: b :: _ := args then
    return ← compareDirs a b
  let cfg := parseArgs args {}
  IO.println s!"difftest: seed {cfg.seed}, cases {cfg.start} to {cfg.start + cfg.n - 1}, defs ≤ {cfg.maxDefs}, depth {cfg.depth}, inputs {cfg.inputs} + ill {cfg.illInputs}, externs {cfg.externs}, shrink budget {cfg.shrinkBudget}"
  let st ← match mkSTStore with
    | .ok st => pure st
    | .error e => do IO.println s!"self-test store: {e}"; return 1
  let nl := treeNoLeafRule st
  IO.println s!"statement: {if stmtV2 then "with repairs I and K (an extern's fresh reference carries its cell's capability; ArgOk's class clauses at non-erased parameters only)" else "as before repairs I and K"}"
  IO.println s!"tree under test: noLeafType {if nl then "the landed rule (Nat has no leaf)" else "always false (repair A)"}; the self-test expects {if nl then "the generator's noLeaf" else "noLeaf false everywhere"}"
  let cfg := { cfg with nlRule := nl }
  let t0 ← IO.monoMsNow
  let t ← runSeed cfg st
  let t1 ← IO.monoMsNow
  IO.println s!"seed {cfg.seed} done in {t1 - t0} ms ({(t1 - t0) * 1000 / (max cfg.n 1)} ms per thousand programs)"
  IO.println (tallyS t)
  return 0
