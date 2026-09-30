import Compilatrix.Fir.Syntax
import Compilatrix.Anf.WellFormed
import Compilatrix.Anf.Census

/-! # Anf → Fir (`Fir.lower`)

The Phase 1 conversion of design note 03 §2.2 (`Fir.convert`, module
`Fir.Lower`). It is on the recheck path in style P (proved once, re-run;
03 §4.5), so it is written in kernel-evaluable style (D17): structural
recursion over Anf terms, a threaded name supply, lists and `Src.NatMap`.

* **Declines closures.** A program with a local closure (`fn`), an unknown
  call (`app`) or the value of a function global (`glob` of a global with
  parameters) is declined with `Error.closures`, naming the globals, until
  P8 (closed-world defunctionalisation, Phase 2) removes them (02 §8, 06
  S45). Nothing else is declined.
* **One to one otherwise.** Every Anf global becomes the function with the
  same id, key, contracts and result contract; a CAF (no parameters) becomes
  a zero-argument function called at each use (06 S36), so `glob g` of a CAF
  is `call g []`. `call` stays a known call; `bind x (call g as) (ret x)`
  (ticks allowed before the `ret`) is the tail call `tcall g as`. `con`,
  `proj`, `prim` and `case` map one to one, with `CtorInfo.ofKey`; `join n
  rec b e` becomes `jp j ps rec b e`; `jump` becomes `jmp`.
* **Names.** De Bruijn indices become variables from a per-function supply
  (parameters first); join points likewise. A `case` alternative binds no
  fields: the arm starts with a projection for each field its body uses.
  A literal or □ scrutinee, or projection source, is bound to a variable
  first.
* **Ticks are erased** (06 S31). `tickBound` gives the constant `N` of the
  timeout clause (03 §2.2): Anf timing out at `N · (k + 1)` means Fir times
  out at `k`.
* **Representation:** every parameter is `tobj` (06 S33). -/

namespace Compilatrix.Fir

open Compilatrix.Ixon

namespace Lower

/-- Why Anf → Fir declines or rejects a program. -/
inductive Error where
  /-- Closures remain (fn, app, function-valued glob, by global): declined
  until P8 (Phase 2). -/
  | closures (fns apps globs : List Anf.GlobalId)
  /-- A variable or join point out of scope, or an arity or key the
  constructor table does not have (the input is not `WellScoped`). -/
  | malformed (g : Anf.GlobalId) (what : String)
  /-- A global `0 … size - 1` is missing. -/
  | missing (g : Anf.GlobalId)
  deriving Repr, Inhabited

def Error.render : Error → String
  | .closures fns apps globs =>
    s!"fir.closures: declined until P8 (closed-world defunctionalisation, Phase 2): " ++
    s!"fn in globals {fns}, app in {apps}, function-valued glob in {globs}"
  | .malformed g what => s!"fir.malformed: global {g}: {what}"
  | .missing g => s!"fir.missing: global {g} is absent"

/-! ## The decline set -/

/-- The globals that still need closures. -/
structure Residual where
  fns : List Anf.GlobalId := []
  apps : List Anf.GlobalId := []
  globs : List Anf.GlobalId := []
  deriving Repr, Inhabited

/-- Counts of `fn`, `app` and function-valued `glob` in a term. -/
structure Counts where
  fns : Nat := 0
  apps : Nat := 0
  globs : Nat := 0

def Counts.add (a b : Counts) : Counts :=
  { fns := a.fns + b.fns, apps := a.apps + b.apps, globs := a.globs + b.globs }

mutual

def countExp (isFn : Anf.GlobalId → Bool) : Anf.Exp → Counts
  | .bind _ b e => (countBind isFn b).add (countExp isFn e)
  | .join _ _ b e => (countExp isFn b).add (countExp isFn e)
  | .case _ alts d => (countAlts isFn alts).add (countOpt isFn d)
  | .tick e => countExp isFn e
  | .jump .. | .ret _ | .trap => {}

def countBind (isFn : Anf.GlobalId → Bool) : Anf.Bind → Counts
  | .fn _ b => ({ fns := 1 } : Counts).add (countExp isFn b)
  | .app .. => { apps := 1 }
  | .glob g => if isFn g then { globs := 1 } else {}
  | _ => {}

def countAlts (isFn : Anf.GlobalId → Bool) : List Anf.Alt → Counts
  | [] => {}
  | .mk _ _ b :: as => (countExp isFn b).add (countAlts isFn as)

def countOpt (isFn : Anf.GlobalId → Bool) : Option Anf.Exp → Counts
  | none => {}
  | some e => countExp isFn e

end

/-- The globals with closures left, as `Anf.Pipeline.residual` reports
them. -/
def residual (A : Anf.Program) : Residual :=
  let isFn := fun g => (A.arity? g).any (· > 0)
  A.globalList.foldl (fun r (g, gd) =>
    let c := countExp isFn gd.body
    { fns := if c.fns > 0 then r.fns ++ [g] else r.fns
      apps := if c.apps > 0 then r.apps ++ [g] else r.apps
      globs := if c.globs > 0 then r.globs ++ [g] else r.globs }) {}

def Residual.isEmpty (r : Residual) : Bool := r.fns.isEmpty && r.apps.isEmpty && r.globs.isEmpty

/-! ## The name supply -/

structure St where
  vars : Nat
  joins : Nat := 0
  /-- `let borrow` sites, newest first. -/
  lets : List (Var × V3.LetContract) := []

def St.fresh (st : St) : Var × St := (st.vars, { st with vars := st.vars + 1 })

/-- The variable an Anf `bind` with contract `c` binds, recorded when it is a
`let borrow` site. -/
def St.bindFresh (st : St) (c : V3.LetContract) : Var × St :=
  let (x, st) := st.fresh
  (x, if c.kind == .borrowShared then { st with lets := (x, c) :: st.lets } else st)

/-- `n` fresh variables, in order. -/
def St.freshN (st : St) (n : Nat) : List Var × St :=
  (List.range' st.vars n, { st with vars := st.vars + n })

def atom (g : Anf.GlobalId) (ρ : List Var) : Anf.Atom → Except Error Arg
  | .var i =>
    match ρ[i]? with
    | some x => .ok (.var x)
    | none => .error (.malformed g s!"variable #{i} out of scope")
  | .lit l => .ok (.lit l)
  | .box => .ok .erased

def atoms (g : Anf.GlobalId) (ρ : List Var) : List Anf.Atom → Except Error (List Arg)
  | [] => .ok []
  | a :: as => do
    let x ← atom g ρ a
    let xs ← atoms g ρ as
    pure (x :: xs)

/-- The continuation returns the value just bound (ticks allowed first): a
call before it is a tail call. -/
def returnsTop : Anf.Exp → Bool
  | .ret (.var 0) => true
  | .tick e => returnsTop e
  | _ => false

/-- An atom as a variable: a variable is itself; a literal or □ is bound to
a fresh variable by the returned prefix. -/
def atomVar (g : Anf.GlobalId) (ρ : List Var) (st : St) (a : Anf.Atom) :
    Except Error (Var × (Code → Code) × St) := do
  match a with
  | .var i =>
    match ρ[i]? with
    | some x => pure (x, id, st)
    | none => throw (.malformed g s!"variable #{i} out of scope")
  | a =>
    let arg ← atom g ρ a
    let (t, st) := st.fresh
    pure (t, fun k => .bind t (.arg arg) k, st)

/-- The projections an arm needs: field `i` of `n` (de Bruijn index
`n - 1 - i` in the body) when the body uses it. -/
def projections (x : Var) (key : Key.CtorKey) (body : Anf.Exp) : List Var → Nat → Code → Code
  | [], _, k => k
  | f :: fs, i, k =>
    let n := fs.length + i + 1
    let rest := projections x key body fs (i + 1) k
    if body.occ (n - 1 - i) > 0 then .bind f (.proj x key i) rest else rest

mutual

def exp (A : Anf.Program) (g : Anf.GlobalId) (ρ : List Var) (J : List JoinId) (st : St) :
    Anf.Exp → Except Error (Code × St)
  | .bind c b e => do
    match b with
    | .call h as =>
      let args ← atoms g ρ as
      if returnsTop e then pure (.tcall h args, st)
      else
        let (x, st) := st.bindFresh c
        let (k, st) ← exp A g (x :: ρ) J st e
        pure (.bind x (.call h args) k, st)
    | .glob h =>
      match A.global? h with
      | some hd =>
        if hd.ps.isEmpty then
          if returnsTop e then pure (.tcall h [], st)
          else
            let (x, st) := st.bindFresh c
            let (k, st) ← exp A g (x :: ρ) J st e
            pure (.bind x (.call h []) k, st)
        else throw (.closures [] [] [g])
      | none => throw (.malformed g s!"glob of a missing global {h}")
    | .atom a =>
      let arg ← atom g ρ a
      let (x, st) := st.bindFresh c
      let (k, st) ← exp A g (x :: ρ) J st e
      pure (.bind x (.arg arg) k, st)
    | .con key as =>
      let args ← atoms g ρ as
      match CtorInfo.ofKey A.ctors key with
      | some info =>
        let (x, st) := st.bindFresh c
        let (k, st) ← exp A g (x :: ρ) J st e
        pure (.bind x (.ctor info args) k, st)
      | none => throw (.malformed g s!"constructor key {reprStr key} is not in the table")
    | .proj key i a =>
      let (y, pre, st) ← atomVar g ρ st a
      let (x, st) := st.bindFresh c
      let (k, st) ← exp A g (x :: ρ) J st e
      pure (pre (.bind x (.proj y key i) k), st)
    | .prim p as =>
      let args ← atoms g ρ as
      let (x, st) := st.bindFresh c
      let (k, st) ← exp A g (x :: ρ) J st e
      pure (.bind x (.prim p args) k, st)
    | .app .. => throw (.closures [] [g] [])
    | .fn .. => throw (.closures [g] [] [])
  | .join n r b e => do
    let j := st.joins
    let st := { st with joins := st.joins + 1 }
    let (ps, st) := st.freshN n
    let (body, st) ← exp A g (ps.reverse ++ ρ) (if r then j :: J else J) st b
    let (k, st) ← exp A g ρ (j :: J) st e
    pure (.jp j ps r body k, st)
  | .jump j as => do
    let args ← atoms g ρ as
    match J[j]? with
    | some j' => pure (.jmp j' args, st)
    | none => throw (.malformed g s!"join point #{j} out of scope")
  | .case x alts d => do
    let (y, pre, st) ← atomVar g ρ st x
    let (alts', st) ← exps A g ρ J y st alts
    let (d', st) ← opt A g ρ J st d
    pure (pre (.case y alts' d'), st)
  | .ret a => do
    let arg ← atom g ρ a
    pure (.ret arg, st)
  | .tick e => exp A g ρ J st e
  | .trap => pure (.trap, st)

def exps (A : Anf.Program) (g : Anf.GlobalId) (ρ : List Var) (J : List JoinId) (y : Var)
    (st : St) : List Anf.Alt → Except Error (List Alt × St)
  | [] => pure ([], st)
  | .mk key n body :: as => do
    let (fs, st) := st.freshN n
    let (b, st) ← exp A g (fs.reverse ++ ρ) J st body
    let (rest, st) ← exps A g ρ J y st as
    pure (.mk key (projections y key body fs 0 b) :: rest, st)

def opt (A : Anf.Program) (g : Anf.GlobalId) (ρ : List Var) (J : List JoinId) (st : St) :
    Option Anf.Exp → Except Error (Option Code × St)
  | none => pure (none, st)
  | some e => do
    let (c, st) ← exp A g ρ J st e
    pure (some c, st)

end

/-- One global as a function: parameters are variables `0 … n - 1`. -/
def function (A : Anf.Program) (g : Anf.GlobalId) (gd : Anf.GDef) : Except Error Fun := do
  let n := gd.ps.length
  let params := List.range n
  let (body, st) ← exp A g params.reverse [] { vars := n } gd.body
  pure { key := gd.key, params := params.map (·, .tobj), body, result := gd.result
         contracts := gd.ps, letContracts := st.lets.reverse, vars := st.vars, joins := st.joins }

def functions (A : Anf.Program) : List Anf.GlobalId → Except Error (List (FunId × Fun))
  | [] => pure []
  | g :: gs => do
    match A.global? g with
    | some gd =>
      let f ← function A g gd
      let fs ← functions A gs
      pure ((g, f) :: fs)
    | none => throw (.missing g)

end Lower

/-- Anf → Fir (03 §2.2): declines residual closures, else converts every
global. -/
def lower (A : Anf.Program) : Except Lower.Error Program := do
  let r := Lower.residual A
  unless r.isEmpty do throw (.closures r.fns r.apps r.globs)
  let fs ← Lower.functions A (List.range A.size)
  pure { funs := Src.NatMap.ofList fs, size := A.size, exports := A.roots, ctors := A.ctors
         known := A.known }

/-! ## The tick bound (06 S31) -/

namespace TickBound

/-- `(d, s)`: `d` bounds the Anf charges Fir does not make (ticks,
non-recursive jumps and the jump entering a recursive join point) on any
path from here to the next Fir charge (a call, a recursive jump) or the end;
`s` bounds the same from the start of every recursive join body inside.
`J` gives, per join point in scope, the cost of jumping to it: `0` for a
recursive jump (a Fir charge), else `1 +` its body's `d`. -/
def maxPair (a b : Nat × Nat) : Nat × Nat := (max a.1 b.1, max a.2 b.2)

mutual

def exp (J : List Nat) : Anf.Exp → Nat × Nat
  | .bind _ _ e => exp J e
  | .join _ r b e =>
    let (db, sb) := exp (if r then 0 :: J else J) b
    let (de, se) := exp ((db + 1) :: J) e
    (de, max (max sb se) (if r then db else 0))
  | .jump j _ => (J.getD j 0, 0)
  | .case _ alts d => maxPair (alts' J alts) (opt J d)
  | .ret _ | .trap => (0, 0)
  | .tick e => let (d, s) := exp J e; (d + 1, s)

def alts' (J : List Nat) : List Anf.Alt → Nat × Nat
  | [] => (0, 0)
  | .mk _ _ b :: as => maxPair (exp J b) (alts' J as)

def opt (J : List Nat) : Option Anf.Exp → Nat × Nat
  | none => (0, 0)
  | some e => exp J e

end

end TickBound

/-- `N_f` of a global: the most Anf-only charges between two Fir charges
on its charge-free paths (03 §2.2). -/
def tickDepth (gd : Anf.GDef) : Nat :=
  let (d, s) := TickBound.exp [] gd.body
  max d s

/-- `N p = 1 + max_f N_f`: Anf timing out at `N p · (k + 1)` implies Fir
timing out at `k` (the timeout clause of `Fir.convert_correct`). -/
def tickBound (A : Anf.Program) : Nat :=
  1 + A.globalList.foldl (fun n (_, gd) => max n (tickDepth gd)) 0

end Compilatrix.Fir
