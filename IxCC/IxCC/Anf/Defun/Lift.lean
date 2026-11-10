import IxCC.Anf.Census
import IxCC.Anf.Budget

/-! # P8, the walk: λ-lifting, closure values and unknown calls

The expression half of closed-world defunctionalisation (P8,
`docs/closures-design.md`, "The translation"). One structural walk per
global rewrites

* `fn ps b`, the `i`-th local function of global `g` in post-order (the λs
  nested in `b` first, counted over `g`'s whole body), into the closure cell
  `con (clo (lam (key g) [i]) 0) caps`, and records a lifted global whose
  parameters are the captures followed by `ps` and whose body is `b`'s image
  with its free variables renamed onto the captures (`capRen`);
* `glob h` of a function global into the field-less cell
  `con (clo (key h) 0) []`, recording `h` as an escaping global;
* `app f as` into `call (dispatch as.length) (f :: as)`, the dispatcher's id
  being `size + as.length - 1` (`dispId`), and `app f []` into `atom f`
  (applying to no arguments returns the function itself);

and leaves every other form unchanged. A CAF's `glob` stays a call of the
CAF.

**Captures.** The walk is inside out: `b` is rewritten first (its λs are
already cells, in the enclosing index space), then the captures are the free
indices of the result outside its `n` parameters, deduplicated and listed
outermost binder first (`captures`), which is the order of the lifted
global's parameters. Nested lifted bodies are closed over their own
parameters, so every node is rewritten, scanned for free variables and
renamed once, in its innermost λ.

**Errors.** The walk refuses (`Error.input`) what P8's correctness relies on
and a well-scoped program never has: a local function without parameters, a
free variable of a local function's body that is out of scope, and the value
of a global beyond the program's size. The declines the closures design
names (too many captures, tag space) and the budgets are the assembly's
(`Anf.Defun`).

Kernel-evaluable (D17): structural recursion over the term, lists and
`Src.NatMap`s. The recursion is as deep as the term, which the middle end's
depth budget bounds (`Anf.maxDepth`). -/

namespace IxCC.Anf.Defun

open IxCC.Ixon

/-- Why P8 refuses a program. -/
inductive Error where
  /-- Decline: a closure cell of the source with this global id would have
  more fields than a constructor cell holds (`maxCellFields`). -/
  | captures (id : GlobalId) (fields : Nat)
  /-- Decline: more closure keys than constructor tags (`maxClosureKeys`). -/
  | tags (keys : Nat)
  /-- The input breaks a precondition of P8 that a well-scoped program meets. -/
  | input (g : GlobalId) (what : String)
  /-- The input's constructor table already has a closure key. -/
  | table
  /-- Two globals whose closures the program builds have equal keys. -/
  | keys (g h : GlobalId)
  /-- A middle-end budget refuses the step before its work is done. -/
  | budget (what : String)
  deriving Repr, Inhabited

def Error.render : Error → String
  | .captures id n =>
    s!"defun.captures: the closures of global {id} need cells of {n} fields, more than a constructor cell holds"
  | .tags n => s!"defun.tags: {n} closure keys, more than the constructor tag space holds"
  | .input g what => s!"defun.input: global {g}: {what}"
  | .table => "defun.input: the constructor table already has a closure key"
  | .keys g h => s!"defun.input: globals {g} and {h}, whose closures the program builds, have equal keys"
  | .budget what => s!"defun.budget: {what}"

instance : ToString Error := ⟨Error.render⟩

/-! ## Renaming free variables -/

/-- Rename a variable free under `d` binders by `f` (on its index outside
them); bound variables are unchanged. -/
def Atom.renameVars (f : Nat → Nat) (d : Nat) : Atom → Atom
  | .var i => if i < d then .var i else .var (d + f (i - d))
  | a => a

def Atom.renameList (f : Nat → Nat) (d : Nat) : List Atom → List Atom
  | [] => []
  | a :: as => Atom.renameVars f d a :: Atom.renameList f d as

mutual

/-- Rename the free variables of an expression under `d` binders. -/
def Exp.renameVars (f : Nat → Nat) (d : Nat) : Exp → Exp
  | .bind c b e => .bind c (Bind.renameVars f d b) (Exp.renameVars f (d + 1) e)
  | .join n r b e => .join n r (Exp.renameVars f (d + n) b) (Exp.renameVars f d e)
  | .jump j as => .jump j (Atom.renameList f d as)
  | .case x alts dft => .case (Atom.renameVars f d x) (Exp.renameAlts f d alts) (Exp.renameOpt f d dft)
  | .ret a => .ret (Atom.renameVars f d a)
  | .tick e => .tick (Exp.renameVars f d e)
  | .trap => .trap

def Bind.renameVars (f : Nat → Nat) (d : Nat) : Bind → Bind
  | .atom a => .atom (Atom.renameVars f d a)
  | .con c as => .con c (Atom.renameList f d as)
  | .proj c i x => .proj c i (Atom.renameVars f d x)
  | .prim p as => .prim p (Atom.renameList f d as)
  | .glob g => .glob g
  | .call g as => .call g (Atom.renameList f d as)
  | .app h as => .app (Atom.renameVars f d h) (Atom.renameList f d as)
  | .fn ps b => .fn ps (Exp.renameVars f (d + ps.length) b)

def Exp.renameAlts (f : Nat → Nat) (d : Nat) : List Alt → List Alt
  | [] => []
  | .mk k n b :: as => .mk k n (Exp.renameVars f (d + n) b) :: Exp.renameAlts f d as

def Exp.renameOpt (f : Nat → Nat) (d : Nat) : Option Exp → Option Exp
  | none => none
  | some e => some (Exp.renameVars f d e)

end

/-! ## Captures -/

/-- The captures of a local function at value depth `Γ` whose rewritten body
`b'` has `n` parameters: the free indices of `b'` outside its parameters,
without repetition, outermost binder first (decreasing index). `free` lists
them with repetition; every one must be below `Γ` (the walk checks). -/
def captures (Γ : Nat) (free : List Nat) : List Nat :=
  let s := Src.NatSet.ofList free
  ((List.range Γ).filter s.contains).reverse

/-- Where each capture lands in the lifted global: capture `caps[p]` is
parameter `p`, at index `caps.length - 1 - p` below the `n` parameters. -/
def capMap (caps : List Nat) : Src.NatMap Nat :=
  Src.NatMap.ofList (caps.zipIdx.map fun (x, p) => (x, caps.length - 1 - p))

/-- The renaming of a lifted body: the `n` parameters stay, a capture moves to
its parameter (`capMap`). -/
def capRen (caps : List Nat) (n : Nat) : Nat → Nat :=
  let m := capMap caps
  fun x => if x < n then x else n + m.getD (x - n) 0

/-! ## The walk -/

/-- A lifted local function. -/
structure Lifted where
  key : Key.GKey
  /-- How many captures come first among its parameters. -/
  ncaps : Nat
  /-- The local function's own parameters. -/
  ps : List V3.BinderContract
  /-- Over the captures and then `ps`. -/
  body : Exp
  deriving Inhabited

/-- The lifted global: captures get the plain contract (`many`, `shared`). -/
def Lifted.toGDef (l : Lifted) : GDef :=
  { key := l.key, ps := List.replicate l.ncaps {} ++ l.ps, body := l.body }

/-- What the walk collects. -/
structure Acc where
  /-- Lifted local functions, newest first. -/
  lifted : List Lifted := []
  /-- The next local function's index in the current global. -/
  next : Nat := 0
  /-- Function globals whose value the program takes. -/
  escapes : Src.NatSet := .leaf
  /-- The largest arity of an `app` with arguments. -/
  maxApp : Nat := 0
  deriving Inhabited

/-- The global the walk is in. -/
structure Ctx where
  prog : Program
  g : GlobalId
  key : Key.GKey

/-- The dispatcher of arity `m ≥ 1` in a program of `size` globals. -/
def dispId (size m : Nat) : GlobalId := size + m - 1

mutual

/-- Rewrite an expression at value depth `Γ`. -/
def exp (C : Ctx) (Γ : Nat) (acc : Acc) : Exp → Except Error (Exp × Acc)
  | .bind c b e => do
    let (b', acc) ← bind C Γ acc b
    let (e', acc) ← exp C (Γ + 1) acc e
    pure (.bind c b' e', acc)
  | .join n r b e => do
    let (b', acc) ← exp C (Γ + n) acc b
    let (e', acc) ← exp C Γ acc e
    pure (.join n r b' e', acc)
  | .jump j as => pure (.jump j as, acc)
  | .case x as d => do
    let (as', acc) ← alts C Γ acc as
    let (d', acc) ← opt C Γ acc d
    pure (.case x as' d', acc)
  | .ret a => pure (.ret a, acc)
  | .tick e => do
    let (e', acc) ← exp C Γ acc e
    pure (.tick e', acc)
  | .trap => pure (.trap, acc)

/-- Rewrite a right-hand side at value depth `Γ`. -/
def bind (C : Ctx) (Γ : Nat) (acc : Acc) : Bind → Except Error (Bind × Acc)
  | .glob h =>
    if h < C.prog.size then
      match C.prog.global? h with
      | some hd =>
        match hd.ps with
        | [] => pure (.glob h, acc)
        | _ :: _ => pure (.con (.clo hd.key 0) [], { acc with escapes := acc.escapes.insert h })
      | none => pure (.glob h, acc)
    else throw (.input C.g s!"the value of global {h}, beyond the program's size")
  | .app f as =>
    match as with
    | [] => pure (.atom f, acc)
    | _ :: _ =>
      pure (.call (dispId C.prog.size as.length) (f :: as), { acc with maxApp := max acc.maxApp as.length })
  | .fn ps b =>
    match ps with
    | [] => throw (.input C.g "a local function without parameters")
    | _ :: _ => do
      let n := ps.length
      let (b', acc) ← exp C (Γ + n) acc b
      let free := b'.free n
      unless free.all (· < Γ) do throw (.input C.g "a free variable of a local function is out of scope")
      let caps := captures Γ free
      let key := Key.GKey.lam C.key [acc.next]
      let body := Exp.renameVars (capRen caps n) 0 b'
      pure (.con (.clo key 0) (caps.map .var),
        { acc with lifted := { key, ncaps := caps.length, ps, body } :: acc.lifted, next := acc.next + 1 })
  | .atom a => pure (.atom a, acc)
  | .con c as => pure (.con c as, acc)
  | .proj c i x => pure (.proj c i x, acc)
  | .prim p as => pure (.prim p as, acc)
  | .call g as => pure (.call g as, acc)

def alts (C : Ctx) (Γ : Nat) (acc : Acc) : List Alt → Except Error (List Alt × Acc)
  | [] => pure ([], acc)
  | .mk k n b :: as => do
    let (b', acc) ← exp C (Γ + n) acc b
    let (as', acc) ← alts C Γ acc as
    pure (.mk k n b' :: as', acc)

def opt (C : Ctx) (Γ : Nat) (acc : Acc) : Option Exp → Except Error (Option Exp × Acc)
  | none => pure (none, acc)
  | some e => do
    let (e', acc) ← exp C Γ acc e
    pure (some e', acc)

end

/-- Rewrite one global; its local functions are numbered from 0. -/
def global (P : Program) (g : GlobalId) (gd : GDef) (acc : Acc) : Except Error (GDef × Acc) := do
  let (body, acc) ← exp { prog := P, g, key := gd.key } gd.ps.length { acc with next := 0 } gd.body
  pure ({ gd with body }, acc)

/-! ## The walk's work, bounded before it runs -/

/-- `acc` plus the walk's work on the expressions in `todo` (each paired
with its value depth): one per node and, per local function, the depth it
sits at (the scan of its captures). Stops once the total passes `cap`; a
tail call over the worklist, so neither its work nor its native stack grows
with the term. Each step adds at least one, so `cap + 2` steps of fuel always
suffice. -/
def workGo (cap : Nat) : Nat → List (Exp × Nat) → Nat → Nat
  | 0, _, _ => cap + 1
  | _, [], acc => acc
  | fuel + 1, (e, Γ) :: todo, acc =>
    if acc > cap then acc
    else
      match e with
      | .bind _ b body =>
        match b with
        | .fn ps fb => workGo cap fuel ((fb, Γ + ps.length) :: (body, Γ + 1) :: todo) (acc + 2 + Γ)
        | .con _ as | .prim _ as | .call _ as | .app _ as =>
          workGo cap fuel ((body, Γ + 1) :: todo) (acc + as.length + 2)
        | .atom _ | .glob _ | .proj .. => workGo cap fuel ((body, Γ + 1) :: todo) (acc + 2)
      | .join n _ b body => workGo cap fuel ((b, Γ + n) :: (body, Γ) :: todo) (acc + 1)
      | .jump _ as => workGo cap fuel todo (acc + as.length + 1)
      | .case _ as d =>
        workGo cap fuel ((as.map fun a => (a.body, Γ + a.arity)) ++ (d.toList.map (·, Γ)) ++ todo) (acc + 1)
      | .ret _ | .trap => workGo cap fuel todo (acc + 1)
      | .tick body => workGo cap fuel ((body, Γ) :: todo) (acc + 1)

/-- The walk's work on a program's globals, up to `cap` (`cap + 1` once it
passes it). -/
def programWork (cap : Nat) : List (GlobalId × GDef) → Nat → Nat
  | [], used => used
  | (_, gd) :: rest, used =>
    let used := workGo cap (cap + 2) [(gd.body, gd.ps.length)] used
    if used > cap then used else programWork cap rest used

end IxCC.Anf.Defun
