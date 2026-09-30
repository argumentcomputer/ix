import Compilatrix.Anf.Opd
import Compilatrix.Lam.ModesOk

/-! # P1: ANF conversion (Lam → Anf)

`Anf.convert` (design note 02 §8, P1), a CPS-style conversion with
level-based operands, so no term is ever shifted:

* A Lam variable maps to a target operand (a target *level*, a literal or
  □) and a flag saying whether it holds a thunk. `ModesOk` (checked first)
  makes that static: exactly the `name` λ binders hold thunks.
* A continuation (`Kont`) is `ret`, a jump to a target join level, or a
  meta-continuation receiving the target depths and the value's operand.
  A `case` whose continuation is a meta-continuation becomes a join point
  over that continuation (non-tail `case`, 02 §6.1); a tail `case` or one
  inside another join point's alternatives passes its continuation down.
* A global's leading λ-telescope becomes its parameters; any other λ-telescope
  an `fn` of that arity.
* A saturated spine headed by a function global becomes `call g as` (extra
  arguments are applied to the result); a `name` argument becomes the thunk
  closure `fn [_] a`; a read of a thunk variable `x` becomes `app x [□]`.

**Clock** (Lam and Anf both use depth clocks). Lam charges at `glob`,
closure entry, `name` reads and `tick`; Anf at calls, applications, jumps,
CAF `glob`s and `tick`. The conversion keeps every Lam charge at the same or
a greater depth (tick dominance, 02 §7.1), and is exact on the common
shapes:
* a thunk read's charge is the thunk application's; a CAF `glob`'s is the
  Anf CAF `glob`'s; a closure entry's is the application's (Anf charges
  every non-empty application, so a Lam spine applied one argument at a
  time and the Anf application of a group of arguments charge at the same
  depth);
* a bare function `glob` (free in Anf) gets an explicit `tick`;
* a spine headed by a function global or thunk charges before evaluating
  its first argument in Lam. Anf evaluates the arguments first, so when an
  argument can fail or charge (it is not a *pure* term: a non-thunk
  variable, literal, □, λ or constructor of pure terms, or a `name`
  argument), the spine gets a leading `tick` (for a `call`, when any of its
  arguments is impure); consecutive pure arguments are applied as one group,
  and an impure argument starts a new application (Lam evaluates it after
  the previous application).

Recursion is on explicit fuel (kernel-evaluable, D17); the pass reads no
certificate. -/

namespace Compilatrix.Anf.Convert

open Compilatrix.Ixon

/-- What a Lam variable is in the target. -/
structure VarInfo where
  opd : Opd
  /-- A `name` variable: it holds a thunk closure. -/
  thunk : Bool := false
  deriving Inhabited

/-- The Lam scope (by de Bruijn index) and the target depths. -/
structure Cx where
  vars : List VarInfo
  d : Nat
  dj : Nat

abbrev M := Except String

/-- A continuation for the value of the term being converted. -/
inductive Kont where
  | ret
  /-- Jump to the join point at this target join level. -/
  | jump (lvl : Nat)
  /-- A meta-continuation over the target depths `d` and `dj` at the point
  the value is available. -/
  | bind (c : V3.LetContract) (k : Nat → Nat → Opd → M Exp)

instance : Inhabited Kont := ⟨.ret⟩

/-- Bind `b` and continue with its value. -/
def emit (cx : Cx) (b : Bind) : Kont → M Exp
  | .ret => pure (.bind freshLet b (.ret (.var 0)))
  | .jump l => pure (.bind freshLet b (.jump (cx.dj - 1 - l) [.var 0]))
  | .bind c k => return .bind c b (← k (cx.d + 1) cx.dj (.lvl cx.d))

/-- Continue with an operand. -/
def pass (cx : Cx) (o : Opd) : Kont → M Exp
  | .ret => pure (.ret (o.atom cx.d))
  | .jump l => pure (.jump (cx.dj - 1 - l) [o.atom cx.d])
  | .bind _ k => k cx.d cx.dj o

/-- A λ-telescope: binder modes and contracts (outermost first), and the
body. -/
def telescope : Lam.Term → List (Lam.Mode × V3.BinderContract) × Lam.Term
  | .lam m c b => let (ps, body) := telescope b; ((m, c) :: ps, body)
  | t => ([], t)

/-- The Lam scope extended by `n` binders at target levels `d … d + n - 1`
(outermost first), with the given thunk flags. -/
def pushParams (vars : List VarInfo) (d : Nat) (thunks : List Bool) : List VarInfo :=
  (thunks.zipIdx.map fun (t, i) => ({ opd := .lvl (d + i), thunk := t } : VarInfo)).reverse ++ vars

mutual

/-- Pure terms: their conversion binds only values (no charge, no failure). -/
def pureTerm (vars : List VarInfo) : Lam.Term → Bool
  | .var i => match vars[i]? with
    | some vi => !vi.thunk
    | none => false
  | .lit _ | .box | .lam .. => true
  | .con _ fs => pureList vars fs
  | _ => false

def pureList (vars : List VarInfo) : List Lam.Term → Bool
  | [] => true
  | t :: ts => pureTerm vars t && pureList vars ts

end

/-- A pure argument: a pure term, or any `name` argument (a thunk closure). -/
def pureArg (vars : List VarInfo) : Lam.Term × Lam.Mode → Bool
  | (_, .name) => true
  | (t, .strict) => pureTerm vars t

/-- Arities of the Lam globals (leading λ-telescope lengths). -/
abbrev Arities := Src.NatMap Nat

mutual

def conv (A : Arities) : Nat → Cx → Lam.Term → Kont → M Exp
  | 0, _, _, _ => throw "convert: fuel"
  | fuel + 1, cx, t, k =>
    match t with
    | .var i =>
      match cx.vars[i]? with
      | some vi =>
        if vi.thunk then emit cx (.app (vi.opd.atom cx.d) [.box]) k else pass cx vi.opd k
      | none => throw s!"convert: variable #{i} out of scope"
    | .glob g =>
      match A.get? g with
      | some 0 => emit cx (.glob g) k
      | some _ => return .tick (← emit cx (.glob g) k)
      | none => throw s!"convert: global {g} out of range"
    | .lam .. =>
      let (ps, body) := telescope t
      let n := ps.length
      do
        let vars := pushParams cx.vars cx.d (ps.map (·.1 == .name))
        let b ← conv A fuel { vars, d := cx.d + n, dj := 0 } body .ret
        emit cx (.fn (ps.map (·.2)) b) k
    | .app .. => spine A fuel cx t k
    | .letE c v b =>
      conv A fuel cx v (.bind c fun d dj o =>
        conv A fuel { vars := { opd := o } :: cx.vars, d, dj } b k)
    | .con c fs =>
      convList A fuel cx fs fun d dj os => emit { cx with d, dj } (.con c (os.map (·.atom d))) k
    | .case s alts dflt =>
      conv A fuel cx s (.bind freshLet fun d dj o => caseOn A fuel { cx with d, dj } o alts dflt k)
    | .proj c i s =>
      conv A fuel cx s (.bind freshLet fun d dj o => emit { cx with d, dj } (.proj c i (o.atom d)) k)
    | .lit l => pass cx (.lit l) k
    | .prim p args =>
      convList A fuel cx args fun d dj os => emit { cx with d, dj } (.prim p (os.map (·.atom d))) k
    | .tick b => return .tick (← conv A fuel cx b k)
    | .box => pass cx .box k
    | .trap => pure .trap

/-- A `case` on operand `o`; a meta-continuation with more than one branch
becomes a join point. -/
def caseOn (A : Arities) : Nat → Cx → Opd → List Lam.Alt → Option Lam.Term → Kont → M Exp
  | 0, _, _, _, _, _ => throw "convert: fuel"
  | fuel + 1, cx, o, alts, dflt, k =>
    let branches := alts.length + (if dflt.isSome then 1 else 0)
    match k with
    | .bind _ f =>
      if branches ≤ 1 then caseBody A fuel cx o alts dflt k
      else do
        let jb ← f (cx.d + 1) cx.dj (.lvl cx.d)
        let body ← caseBody A fuel { cx with dj := cx.dj + 1 } o alts dflt (.jump cx.dj)
        return .join 1 false jb body
    | k => caseBody A fuel cx o alts dflt k

def caseBody (A : Arities) : Nat → Cx → Opd → List Lam.Alt → Option Lam.Term → Kont → M Exp
  | 0, _, _, _, _, _ => throw "convert: fuel"
  | fuel + 1, cx, o, alts, dflt, k => do
    let alts' ← convAlts A fuel cx alts k
    let dflt' ← match dflt with
      | some t => some <$> conv A fuel cx t k
      | none => pure none
    return .case (o.atom cx.d) alts' dflt'

def convAlts (A : Arities) : Nat → Cx → List Lam.Alt → Kont → M (List Alt)
  | 0, _, _, _ => throw "convert: fuel"
  | _, _, [], _ => pure []
  | fuel + 1, cx, .mk key n body :: rest, k => do
    let vars := pushParams cx.vars cx.d (List.replicate n false)
    let b ← conv A fuel { cx with vars, d := cx.d + n } body k
    return .mk key n b :: (← convAlts A fuel cx rest k)

/-- Convert terms left to right, then continue with their operands. -/
def convList (A : Arities) : Nat → Cx → List Lam.Term → (Nat → Nat → List Opd → M Exp) → M Exp
  | 0, _, _, _ => throw "convert: fuel"
  | _, cx, [], f => f cx.d cx.dj []
  | fuel + 1, cx, t :: ts, f =>
    conv A fuel cx t (.bind freshLet fun d dj o =>
      convList A fuel { cx with d, dj } ts fun d' dj' os => f d' dj' (o :: os))

/-- Convert spine arguments left to right (a `name` argument becomes a thunk
closure), then continue with their operands. -/
def convArgs (A : Arities) : Nat → Cx → List (Lam.Term × Lam.Mode) →
    (Nat → Nat → List Opd → M Exp) → M Exp
  | 0, _, _, _ => throw "convert: fuel"
  | _, cx, [], f => f cx.d cx.dj []
  | fuel + 1, cx, (a, .strict) :: rest, f =>
    conv A fuel cx a (.bind freshLet fun d dj o =>
      convArgs A fuel { cx with d, dj } rest fun d' dj' os => f d' dj' (o :: os))
  | fuel + 1, cx, (a, .name) :: rest, f => do
    let body ← conv A fuel { vars := cx.vars, d := cx.d + 1, dj := 0 } a .ret
    emit cx (.fn [{}] body) (.bind freshLet fun d dj o =>
      convArgs A fuel { cx with d, dj } rest fun d' dj' os => f d' dj' (o :: os))

/-- Apply operand `fo` to spine arguments: each group is an impure argument
(or the first) followed by the pure arguments after it. -/
def groups (A : Arities) : Nat → Cx → Opd → List (Lam.Term × Lam.Mode) → Kont → M Exp
  | 0, _, _, _, _ => throw "convert: fuel"
  | _, cx, fo, [], k => pass cx fo k
  | fuel + 1, cx, fo, a :: rest, k =>
    let run := rest.takeWhile (pureArg cx.vars)
    let rest' := rest.drop run.length
    convArgs A fuel cx (a :: run) fun d dj os =>
      let cx' := { cx with d, dj }
      let b := Bind.app (fo.atom d) (os.map (·.atom d))
      match rest' with
      | [] => emit cx' b k
      | _ => emit cx' b (.bind freshLet fun d dj o => groups A fuel { cx with d, dj } o rest' k)

/-- An application spine. -/
def spine (A : Arities) : Nat → Cx → Lam.Term → Kont → M Exp
  | 0, _, _, _ => throw "convert: fuel"
  | fuel + 1, cx, t, k =>
    let (h, args) := Lam.Term.spine t
    let tickIf := fun (b : Bool) (e : Exp) => if b then Exp.tick e else e
    match h with
    | .glob g =>
      match A.get? g with
      | some 0 =>
        emit cx (.glob g) (.bind freshLet fun d dj o => groups A fuel { cx with d, dj } o args k)
      | some n =>
        if n ≤ args.length then
          let callArgs := args.take n
          let rest := args.drop n
          let impure := !(callArgs.all (pureArg cx.vars))
          tickIf impure <$> convArgs A fuel cx callArgs fun d dj os =>
            let cx' := { cx with d, dj }
            let b := Bind.call g (os.map (·.atom d))
            match rest with
            | [] => emit cx' b k
            | _ => emit cx' b (.bind freshLet fun d dj o => groups A fuel { cx with d, dj } o rest k)
        else
          let impure := match args with
            | a :: _ => !pureArg cx.vars a
            | [] => false
          tickIf impure <$> emit cx (.glob g)
            (.bind freshLet fun d dj o => groups A fuel { cx with d, dj } o args k)
      | none => throw s!"convert: global {g} out of range"
    | .var i =>
      match cx.vars[i]? with
      | some vi =>
        if vi.thunk then
          emit cx (.app (vi.opd.atom cx.d) [.box])
            (.bind freshLet fun d dj o => groups A fuel { cx with d, dj } o args k)
        else groups A fuel cx vi.opd args k
      | none => throw s!"convert: variable #{i} out of scope"
    | h => conv A fuel cx h (.bind freshLet fun d dj o => groups A fuel { cx with d, dj } o args k)

end

/-- Fuel for one global body: every call descends into a subterm, a list
tail or a spine argument. -/
def fuelFor (t : Lam.Term) : Nat := 4 * t.nodes + 64

/-- Convert one global: its leading λ-telescope becomes its parameters. -/
def global (A : Arities) (gl : Lam.Global) : M GDef := do
  let (ps, body) := telescope gl.body
  let vars := pushParams [] 0 (ps.map (·.1 == .name))
  let b ← conv A (fuelFor gl.body) { vars, d := ps.length, dj := 0 } body .ret
  return { key := gl.key, ps := ps.map (·.2), result := gl.result, body := b }

def arities (P : Lam.Program) : Arities :=
  Src.NatMap.ofList (P.globalList.map fun (g, gl) => (g, (telescope gl.body).1.length))

end Convert

open Convert in
/-- P1: convert a `ModesOk` Lam program; global ids, roots, the constructor
table and the pinned keys are unchanged. -/
def convert (P : Lam.Program) : Except String Program := do
  unless Lam.modesOk P do throw "convert: the Lam program is not ModesOk"
  let A := arities P
  let gs ← P.globalList.mapM fun (g, gl) => do
    let gd ← (Convert.global A gl).mapError (s!"global {g}: " ++ ·)
    return (g, gd)
  return { globals := Src.NatMap.ofList gs, size := P.size, roots := P.roots, ctors := P.ctors,
           known := P.known }

end Compilatrix.Anf
