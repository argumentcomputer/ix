import IxCC.Fir.Shape

/-!
# An untrusted producer of shape certificates (`IxCC.Fir.ShapeInfer`)

Design note: `plans/ONE-PIPELINE.md`, section 2.2. Nothing here is trusted or proved: the
certificate `infer` proposes is decided by `Fir.Shape.check`, and `run` falls back to the
certificate that states nothing (`trivial`) when the proposal is refused.

**The inference** is a forward data-flow analysis over the whole program, ascending from "no
value seen" for every variable, parameter, result and constructor field:

* an operand's shape is its variable's, `natLt (n + 1)` for a literal, `irr` for `□`;
* a primitive's result is `Fir.Shape.primShape` of its operands' shapes, the same function the
  checker uses (so bounds flow: `natLt a + natLt b` is `natLt (a + b)`, a word operation is a
  word of its width);
* a constructor application is `enum I`, `data d` or a closure (`fn any any`), by the table
  below, and joins its arguments' shapes into the fields of its entry; a projection out of a
  `data d` reads the field's shape; the predecessor a `Nat` peels to is `nat`;
* a call joins its arguments into the callee's parameters and reads the callee's result; a jump
  joins its arguments into the join point's parameters; `ret` and a tail call join into the
  function's result.

Rounds repeat until nothing changes. A bound that keeps growing (a counter in a loop) is widened
to `nat` after `Config.widenAfter` rounds. What is still unseen at a fixed point (the parameters
of a function nothing calls, a join point nothing jumps to, a field nothing builds, the result of
a function that never returns) is set to `any`, one class at a time, and the rounds resume.

**The data table.** `Fir` does not record which inductive a constructor belongs to, so the
producer is told (`Config.indOf`, from the source program). One entry per inductive with a
constructor in the program's table: an enumeration when every such constructor is field-less,
a data entry otherwise. The table is monovariant: `List Nat` and `List Bool` in one program
share an entry, whose element field joins to `any`. Without `indOf` no constructor is typed.

**Roots.** The parameters of an export are whatever the caller passes; `Config.rootParam` is the
shape the producer assumes of each (`any` assumes nothing; `nat` is what today's entry wrapper
passes). The certificate's facts hold under that assumption (`ShapeSound` asks the arguments to
have the parameter shapes), so whoever runs an export must supply it.

**Arrays: the marked place.** The checker has the array rules (`Fir.Shape.ArrOk`, `arrOk`), but
`Fir.lower` still refuses array primitives, so no program this producer sees has one; it gives an
array primitive's result `any` (`primShape`), no `arr` shape is ever inferred, and the native
flow condition (`Fir.Rep.flowsOk`) holds of every certificate produced here. When array
primitives reach `Fir.lower`'s output (lane `prims-core`, design D9), their transfer function
(`Fir.Shape.arrShape`) goes in `rhsShape`, and the demotion loop of section 2.5 (lower an element
shape to `any` along every flow that `Shape.flowOk` refuses, report it) goes after `infer`.
-/

set_option autoImplicit false

namespace IxCC.Fir.ShapeInfer

open IxCC.Shape
open IxCC.Fir (Var FunId JoinId Arg Rhs Code Alt Program CtorInfo)
open IxCC.Fir.Shape

/-- What the producer is told. -/
structure Config where
  /-- The inductive of a source constructor, where known. -/
  indOf : Src.CId → Option Src.CId := fun _ => none
  /-- The shape assumed of each parameter of an export. -/
  rootParam : Shape := .any
  /-- The most rounds the analysis runs. -/
  rounds : Nat := 96
  /-- From this round on, a bound that changes is widened to `nat`. -/
  widenAfter : Nat := 6

/-! ## Shapes: join and rendering -/

/-- An upper bound of two shapes under `Shape.le`. -/
def join (widen : Bool) : Shape → Shape → Shape
  | .arr e n, .arr e' n' => .arr (join widen e e') (if n == n' then n else none)
  | .natLt a, .natLt b =>
    if a == b then .natLt a else if widen then .nat else .natLt (max a b)
  | .natLt _, .nat => .nat
  | .nat, .natLt _ => .nat
  | σ, τ => if σ == τ then σ else .any

def joinOpt (widen : Bool) : Option Shape → Option Shape → Option Shape
  | none, r => r
  | l, none => l
  | some a, some b => some (join widen a b)

def joinList (widen : Bool) : List (Option Shape) → List (Option Shape) → List (Option Shape)
  | a :: as, b :: bs => joinOpt widen a b :: joinList widen as bs
  | as, [] => as
  | [], _ => []

/-- A shape on one line. -/
def render : Shape → String
  | .any => "any"
  | .irr => "irr"
  | .nat => "nat"
  | .natLt b => s!"nat<{b}"
  | .word w => s!"word{w.bits}"
  | .enum i => s!"enum#{i}"
  | .data d => s!"data{d}"
  | .fn a b => s!"({render a} -> {render b})"
  | .inter a b => s!"({render a} & {render b})"
  | .arr e n =>
    match n with
    | some n => s!"arr[{n}] {render e}"
    | none => s!"arr {render e}"

/-! ## The data table -/

/-- The constructors of one inductive that the program's table lists, with their arities. -/
structure Group where
  ind : Src.CId
  ctors : List (Key.CtorKey × Nat)
  deriving Inhabited

def addCtor (ind : Src.CId) (k : Key.CtorKey) (arity : Nat) : List Group → List Group
  | [] => [{ ind, ctors := [(k, arity)] }]
  | g :: rest =>
    if g.ind == ind then
      (if g.ctors.any (·.1 == k) then g else { g with ctors := g.ctors ++ [(k, arity)] }) :: rest
    else g :: addCtor ind k arity rest

/-- The enumerations and data entries of a program. -/
structure Tables where
  enums : List (Src.CId × List Key.CtorKey) := []
  datas : List Group := []
  deriving Inhabited

def tables (P : Program) (cfg : Config) : Tables :=
  let groups := P.ctors.foldl (init := ([] : List Group)) fun gs r =>
    match r.key with
    | .src c =>
      if P.known.natZero == some r.key || P.known.natSucc == some r.key then gs
      else
        match cfg.indOf c with
        | some ind => addCtor ind r.key r.arity gs
        | none => gs
    | .clo _ _ | .arr => gs
  { enums := (groups.filter fun g => g.ctors.all (·.2 == 0)).map fun g => (g.ind, g.ctors.map (·.1))
    datas := groups.filter fun g => !g.ctors.all (·.2 == 0) }

def keyIndex (k : Key.CtorKey) : List (Key.CtorKey × Nat) → Nat → Option Nat
  | [], _ => none
  | e :: rest, i => if e.1 == k then some i else keyIndex k rest (i + 1)

def findData (k : Key.CtorKey) : List Group → Nat → Option (Nat × Nat)
  | [], _ => none
  | g :: rest, d =>
    match keyIndex k g.ctors 0 with
    | some ci => some (d, ci)
    | none => findData k rest (d + 1)

/-- How a constructor is typed. -/
inductive Kind where
  | clo
  | enum (ind : Src.CId)
  | data (d ci : Nat)
  | other

def classify (t : Tables) (k : Key.CtorKey) : Kind :=
  match k with
  | .clo _ _ => .clo
  | .src _ =>
    match t.enums.find? fun e => e.2.contains k with
    | some e => .enum e.1
    | none =>
      match findData k t.datas 0 with
      | some (d, ci) => .data d ci
      | none => .other
  | .arr => .other

/-! ## The analysis state -/

/-- What has been seen so far: a missing variable, result or `none` slot is "no value yet". -/
structure St where
  vars : Src.NatMap (Src.NatMap Shape) := .leaf
  params : Src.NatMap (List (Option Shape)) := .leaf
  rets : Src.NatMap Shape := .leaf
  /-- `fields[d][ci][i]`: field `i` of constructor `ci` of data entry `d`. -/
  fields : List (List (List (Option Shape))) := []
  changed : Bool := false
  deriving Inhabited

def St.touch (st : St) (ch : Bool) : St := if ch then { st with changed := true } else st

/-- The walk of one function: its variables, and the program-wide state. -/
structure W where
  vm : Src.NatMap Shape
  st : St

/-- What is fixed during the walk of one function. -/
structure Cx where
  P : Program
  t : Tables
  widen : Bool
  f : FunId
  jps : Src.NatMap (List Var)

def updAt {α : Type} : List α → Nat → (α → α) → List α
  | [], _, _ => []
  | a :: as, 0, f => f a :: as
  | a :: as, i + 1, f => a :: updAt as i f

def setVar (widen : Bool) (vm : Src.NatMap Shape) (x : Var) (r : Option Shape) :
    Src.NatMap Shape × Bool :=
  match r with
  | none => (vm, false)
  | some σ =>
    match vm.get? x with
    | none => (vm.insert x σ, true)
    | some old =>
      let new := join widen old σ
      if new == old then (vm, false) else (vm.insert x new, true)

def argShape? (vm : Src.NatMap Shape) : Arg → Option Shape
  | .var x => vm.get? x
  | .lit (.nat n) => some (.natLt (n + 1))
  | .lit (.str _) => some .any
  | .erased => some .irr

def argShapes? (vm : Src.NatMap Shape) : List Arg → Option (List Shape)
  | [] => some []
  | a :: as =>
    match argShape? vm a, argShapes? vm as with
    | some σ, some σs => some (σ :: σs)
    | _, _ => none

def fieldsOf (st : St) (d ci : Nat) : List (Option Shape) := (st.fields.getD d []).getD ci []

/-- A call's arguments, joined into the callee's parameters. -/
def callArgs (cx : Cx) (w : W) (g : FunId) (as : List Arg) : W :=
  let cur := w.st.params.getD g []
  let new := joinList cx.widen cur (as.map (argShape? w.vm))
  if new == cur then w
  else { w with st := { w.st with params := w.st.params.insert g new, changed := true } }

/-- A constructor's arguments, joined into its entry's fields. -/
def joinFields (cx : Cx) (w : W) (d ci : Nat) (as : List Arg) : W :=
  let cur := fieldsOf w.st d ci
  let new := joinList cx.widen cur (as.map (argShape? w.vm))
  if new == cur then w
  else
    { w with st := { w.st with
        fields := updAt w.st.fields d fun e => updAt e ci fun _ => new
        changed := true } }

/-- A shape joined into the result of the function being walked. -/
def joinRet (cx : Cx) (w : W) (r : Option Shape) : W :=
  match r with
  | none => w
  | some σ =>
    match w.st.rets.get? cx.f with
    | none => { w with st := { w.st with rets := w.st.rets.insert cx.f σ, changed := true } }
    | some old =>
      let new := join cx.widen old σ
      if new == old then w
      else { w with st := { w.st with rets := w.st.rets.insert cx.f new, changed := true } }

/-- The shape of a right-hand side, and the state after its effects on the tables. -/
def rhsShape (cx : Cx) (w : W) : Rhs → Option Shape × W
  | .arg a => (argShape? w.vm a, w)
  | .ctor c as =>
    match classify cx.t c.key with
    | .clo => (some (.fn .any .any), w)
    | .enum ind => (some (if as.isEmpty then .enum ind else .any), w)
    | .data d ci =>
      if as.length == (fieldsOf w.st d ci).length then (some (.data d), joinFields cx w d ci as)
      else (some .any, w)
    | .other => (some .any, w)
  | .proj y c i =>
    match w.vm.get? y with
    | none => (none, w)
    | some (.data d) =>
      match (cx.t.datas[d]?).bind fun g => keyIndex c g.ctors 0 with
      | some ci =>
        match (fieldsOf w.st d ci)[i]? with
        | some s => (s, w)
        | none => (some .any, w)
      | none => (some .any, w)
    | some σ =>
      if σ.le .nat && cx.P.known.natSucc == some c && i == 0 then (some .nat, w)
      else (some .any, w)
  | .prim op as => ((argShapes? w.vm as).map (primShape op), w)
  | .call g as => (w.st.rets.get? g, callArgs cx w g as)

/-- A jump's arguments, joined into the join point's parameters. -/
def jmpArgs (widen : Bool) : List Var → List Arg → W → W
  | p :: ps, a :: as, w =>
    let (vm, ch) := setVar widen w.vm p (argShape? w.vm a)
    jmpArgs widen ps as { vm, st := w.st.touch ch }
  | _, _, w => w

mutual

def goCode (cx : Cx) : Code → W → W
  | .bind x r k, w =>
    let (s, w1) := rhsShape cx w r
    let (vm, ch) := setVar cx.widen w1.vm x s
    goCode cx k { vm, st := w1.st.touch ch }
  | .jp _ _ _ body k, w => goCode cx k (goCode cx body w)
  | .jmp j as, w => jmpArgs cx.widen (cx.jps.getD j []) as w
  | .case _ alts d, w => goOpt cx d (goAlts cx alts w)
  | .ret a, w => joinRet cx w (argShape? w.vm a)
  | .tcall g as, w =>
    let w1 := callArgs cx w g as
    joinRet cx w1 (w1.st.rets.get? g)
  | .trap, w => w

def goAlts (cx : Cx) : List Alt → W → W
  | [], w => w
  | .mk _ b :: rest, w => goAlts cx rest (goCode cx b w)

def goOpt (cx : Cx) : Option Code → W → W
  | none, w => w
  | some c, w => goCode cx c w

end

mutual

/-- The parameters of each join point of a body. -/
def joinsOf : Code → Src.NatMap (List Var) → Src.NatMap (List Var)
  | .bind _ _ k, m => joinsOf k m
  | .jp j ps _ b k, m => joinsOf k (joinsOf b (m.insert j ps))
  | .case _ alts d, m => joinsOfOpt d (joinsOfAlts alts m)
  | .jmp .., m | .ret _, m | .tcall .., m | .trap, m => m

def joinsOfAlts : List Alt → Src.NatMap (List Var) → Src.NatMap (List Var)
  | [], m => m
  | .mk _ b :: rest, m => joinsOfAlts rest (joinsOf b m)

def joinsOfOpt : Option Code → Src.NatMap (List Var) → Src.NatMap (List Var)
  | none, m => m
  | some c, m => joinsOf c m

end

/-- A function with the parameters of its join points. -/
structure FunInfo where
  f : FunId
  fd : Fir.Fun
  jps : Src.NatMap (List Var)

def funInfos (P : Program) : List FunInfo :=
  P.funs.toList.map fun e => { f := e.1, fd := e.2, jps := joinsOf e.2.body .leaf }

def paramVars (widen : Bool) : List Var → List (Option Shape) → Src.NatMap Shape × Bool →
    Src.NatMap Shape × Bool
  | x :: xs, s :: ss, (vm, ch) =>
    let (vm', ch') := setVar widen vm x s
    paramVars widen xs ss (vm', ch || ch')
  | _, _, acc => acc

/-- One function, once. -/
def funPass (P : Program) (t : Tables) (widen : Bool) (st : St) (fi : FunInfo) : St :=
  let cx : Cx := { P, t, widen, f := fi.f, jps := fi.jps }
  let (vm, ch) := paramVars widen (fi.fd.params.map (·.1)) (st.params.getD fi.f [])
    (st.vars.getD fi.f .leaf, false)
  let w := goCode cx fi.fd.body { vm, st := st.touch ch }
  { w.st with vars := w.st.vars.insert fi.f w.vm }

/-! ## What stays unseen at a fixed point -/

def fillList (l : List (Option Shape)) : List (Option Shape) := l.map fun s => some (s.getD .any)

/-- Parameters of functions nothing calls. -/
def fillParams (funs : List FunInfo) (st : St) : St :=
  funs.foldl (init := st) fun st fi =>
    let cur := st.params.getD fi.f []
    if cur.any (·.isNone) then
      { st with params := st.params.insert fi.f (fillList cur), changed := true }
    else st

/-- Parameters of join points nothing jumps to. -/
def fillJoins (funs : List FunInfo) (st : St) : St :=
  funs.foldl (init := st) fun st fi =>
    let vm := st.vars.getD fi.f .leaf
    let missing := (fi.jps.toList.flatMap (·.2)).filter fun p => (vm.get? p).isNone
    if missing.isEmpty then st
    else
      { st with
        vars := st.vars.insert fi.f (missing.foldl (fun m p => m.insert p .any) vm)
        changed := true }

/-- Fields of constructors nothing builds. -/
def fillFields (st : St) : St :=
  if st.fields.any fun e => e.any fun fl => fl.any (·.isNone) then
    { st with fields := st.fields.map fun e => e.map fillList, changed := true }
  else st

/-- Results of functions that never return. -/
def fillRets (funs : List FunInfo) (st : St) : St :=
  funs.foldl (init := st) fun st fi =>
    if (st.rets.get? fi.f).isNone then
      { st with rets := st.rets.insert fi.f .any, changed := true }
    else st

/-- The first class of unseen slots that is not empty, set to `any`. -/
def fill (funs : List FunInfo) (st : St) : St :=
  let st1 := fillParams funs st
  if st1.changed then st1
  else
    let st2 := fillJoins funs st1
    if st2.changed then st2
    else
      let st3 := fillFields st2
      if st3.changed then st3 else fillRets funs st3

/-- Rounds until nothing changes and nothing is unseen, or the fuel runs out. -/
def loop (P : Program) (t : Tables) (cfg : Config) (funs : List FunInfo) : Nat → Nat → St → St
  | 0, _, st => st
  | fuel + 1, i, st =>
    let st1 := funs.foldl (funPass P t (decide (cfg.widenAfter ≤ i))) { st with changed := false }
    if st1.changed then loop P t cfg funs fuel (i + 1) st1
    else
      let st2 := fill funs st1
      if st2.changed then loop P t cfg funs fuel (i + 1) st2 else st1

def initial (P : Program) (cfg : Config) (t : Tables) (funs : List FunInfo) : St :=
  let params := funs.foldl (init := (.leaf : Src.NatMap (List (Option Shape)))) fun m fi =>
    m.insert fi.f
      (List.replicate fi.fd.params.length
        (if P.exports.contains fi.f then some cfg.rootParam else none))
  { params, fields := t.datas.map fun g => g.ctors.map fun e => List.replicate e.2 none }

/-! ## The certificate -/

/-- The certificate a state stands for: what is unseen is `any`. -/
def certOf (t : Tables) (funs : List FunInfo) (st : St) : ShapeCert :=
  let funs' := funs.foldl (init := (.leaf : Src.NatMap FunShapes)) fun m fi =>
    let vm := st.vars.getD fi.f .leaf
    let ps := st.params.getD fi.f []
    -- a parameter's variable is listed at the parameter's shape, whatever was seen of it
    let vm := ((fi.fd.params.map (·.1)).zip ps).foldl (init := vm) fun m e =>
      m.insert e.1 (e.2.getD .any)
    let vars := vm.toList.foldl (init := (.leaf : Src.NatMap Shape)) fun m e =>
      if e.2 == .any then m else m.insert e.1 e.2
    let joins := fi.jps.toList.foldl (init := (.leaf : Src.NatMap (List Shape))) fun m e =>
      m.insert e.1 (e.2.map fun p => vars.getD p .any)
    m.insert fi.f
      { params := (fi.fd.params.map (·.1)).map fun x => vars.getD x .any
        ret := (st.rets.get? fi.f).getD .any
        vars, joins }
  { funs := funs'
    datas := (t.datas.zip st.fields).map fun e =>
      { ind := e.1.ind, params := []
        ctors := (e.1.ctors.zip e.2).map fun c => (c.1.1, c.2.map (·.getD .any))
        struct := e.1.ctors.length == 1 }
    enums := t.enums }

/-- **The proposed certificate** (untrusted). -/
def infer (P : Program) (cfg : Config := {}) : ShapeCert :=
  let t := tables P cfg
  let funs := funInfos P
  certOf t funs (loop P t cfg funs cfg.rounds 0 (initial P cfg t funs))

/-- **The certificate that states nothing**: every shape `any`. It always checks. -/
def trivial (P : Program) : ShapeCert :=
  let funs := funInfos P
  { funs := funs.foldl (init := (.leaf : Src.NatMap FunShapes)) fun m fi =>
      m.insert fi.f
        { params := List.replicate fi.fd.params.length .any
          joins := fi.jps.toList.foldl (init := (.leaf : Src.NatMap (List Shape))) fun m e =>
            m.insert e.1 (List.replicate e.2.length .any) } }

/-- The producer with its check: the proposal when the checker accepts it (`true`), the
certificate that states nothing otherwise (`false`). -/
def run (P : Program) (cfg : Config := {}) : ShapeCert × Bool :=
  let cert := infer P cfg
  if check P cert then (cert, true) else (trivial P, false)

/-! ## Reading a refusal -/

def renderArg : Arg → String
  | .var x => s!"v{x}"
  | .lit (.nat n) => s!"{n}"
  | .lit (.str _) => "<str>"
  | .erased => "□"

def renderRhs (fs : FunShapes) : Rhs → String
  | .arg a => s!"{renderArg a} : {render (argShape fs a)}"
  | .ctor c as => s!"ctor#{c.tag}/{as.length} {as.map fun a => render (argShape fs a)}"
  | .proj y _ i => s!"proj v{y}.{i} of {render (fs.var y)}"
  | .prim op as => s!"{op.name} {as.map fun a => render (argShape fs a)}"
  | .call g as => s!"call f{g} {as.map fun a => render (argShape fs a)}"

mutual

/-- The first node of a body the checker refuses, described for reading. -/
def whyCode (P : Program) (cert : ShapeCert) (fs : FunShapes) : Code → Option String
  | .bind x r k =>
    if rhsOk P cert fs r (fs.var x) then whyCode P cert fs k
    else some s!"bind v{x} : {render (fs.var x)} := {renderRhs fs r}"
  | .jp j ps _ body k =>
    if paramsOk fs ps (fs.join j) then
      match whyCode P cert fs body with
      | some s => some s
      | none => whyCode P cert fs k
    else some s!"join point j{j}: parameters {ps.map fun p => render (fs.var p)} declared \
      {(fs.join j).map render}"
  | .jmp j as =>
    if argsOk fs as (fs.join j) then none
    else some s!"jump j{j} {as.map fun a => render (argShape fs a)} to {(fs.join j).map render}"
  | .case _ alts d =>
    match whyAlts P cert fs alts with
    | some s => some s
    | none => whyOpt P cert fs d
  | .ret a =>
    if argOk fs a fs.ret then none
    else some s!"ret {renderArg a} : {render (argShape fs a)} at result {render fs.ret}"
  | .tcall g as =>
    if argsOk fs as (cert.fn g).params && (cert.fn g).ret.le fs.ret then none
    else some s!"tail call f{g} {as.map fun a => render (argShape fs a)} to \
      {(cert.fn g).params.map render} -> {render (cert.fn g).ret} at result {render fs.ret}"
  | .trap => none

def whyAlts (P : Program) (cert : ShapeCert) (fs : FunShapes) : List Alt → Option String
  | [] => none
  | .mk _ b :: rest =>
    match whyCode P cert fs b with
    | some s => some s
    | none => whyAlts P cert fs rest

def whyOpt (P : Program) (cert : ShapeCert) (fs : FunShapes) : Option Code → Option String
  | none => none
  | some c => whyCode P cert fs c

end

/-- Why the checker refuses function `f`, if it does. -/
def whyFun (P : Program) (cert : ShapeCert) (f : FunId) (fd : Fir.Fun) : Option String :=
  let fs := cert.fn f
  if !paramsOk fs (fd.params.map (·.1)) fs.params then
    some s!"f{f}: parameters {(fd.params.map (·.1)).map fun x => render (fs.var x)} declared \
      {fs.params.map render}"
  else (whyCode P cert fs fd.body).map fun s => s!"f{f}: {s}"

mutual

/-- The functions a body calls. -/
def callsOf : Code → List FunId → List FunId
  | .bind _ r k, acc =>
    callsOf k (match r with
      | .call g _ => g :: acc
      | _ => acc)
  | .jp _ _ _ b k, acc => callsOf k (callsOf b acc)
  | .case _ alts d, acc => callsOfOpt d (callsOfAlts alts acc)
  | .tcall g _, acc => g :: acc
  | .jmp .., acc | .ret _, acc | .trap, acc => acc

def callsOfAlts : List Alt → List FunId → List FunId
  | [], acc => acc
  | .mk _ b :: rest, acc => callsOfAlts rest (callsOf b acc)

def callsOfOpt : Option Code → List FunId → List FunId
  | none, acc => acc
  | some c, acc => callsOf c acc

end

/-- The functions reachable from `root` by calls (the fuel bounds the number of steps). -/
def reachable (P : Program) (root : FunId) : List FunId :=
  go (P.funs.toList.length + 1) [root] .leaf []
where
  go : Nat → List FunId → Src.NatSet → List FunId → List FunId
    | 0, _, _, acc => acc.reverse
    | _ + 1, [], _, acc => acc.reverse
    | fuel + 1, f :: todo, seen, acc =>
      if seen.contains f then go fuel todo seen acc
      else
        match P.fun? f with
        | some fd => go fuel (callsOf fd.body [] ++ todo) (seen.insert f) (f :: acc)
        | none => go fuel todo (seen.insert f) acc

/-- The first function reachable from `root` that the checker refuses, with the reason. -/
def whyRoot (P : Program) (cert : ShapeCert) (root : FunId) : Option String :=
  (reachable P root).findSome? fun f => (P.fun? f).bind fun fd => whyFun P cert f fd

/-- How many variables of the reachable functions have each kind of shape:
`(nat, natLt, enum, data, fn, any or unlisted, other)`. -/
structure Census where
  nat : Nat := 0
  natLt : Nat := 0
  enum : Nat := 0
  data : Nat := 0
  fn : Nat := 0
  other : Nat := 0
  deriving Inhabited

def Census.add (c : Census) : Shape → Census
  | .nat => { c with nat := c.nat + 1 }
  | .natLt _ => { c with natLt := c.natLt + 1 }
  | .enum _ => { c with enum := c.enum + 1 }
  | .data _ => { c with data := c.data + 1 }
  | .fn _ _ => { c with fn := c.fn + 1 }
  | .any => c
  | _ => { c with other := c.other + 1 }

/-- The census of the listed variables of the functions reachable from `root`. -/
def census (P : Program) (cert : ShapeCert) (root : FunId) : Census :=
  (reachable P root).foldl (init := {}) fun c f =>
    (cert.fn f).vars.toList.foldl (init := c) fun c e => c.add e.2

end IxCC.Fir.ShapeInfer
