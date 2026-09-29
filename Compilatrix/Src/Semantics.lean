import Compilatrix.Src.Value
import Compilatrix.Src.Prim
import Compilatrix.Sem.Result

/-! # SrcEval

The clocked big-step semantics of Src (design note 01 §3), the stage-S
meaning of a program. Rules (§3.2):

* E1 `var`: a `val` slot gives its value; a `name` slot is evaluated in its
  environment (clock charge, not memoised).
* E2 `sort`/`pi`: `irr`. E3 literals. E4 `lam`: a closure.
* E5 `letE`: a relevant let evaluates its value; others bind `irr`.
* E6 `proj`: the field of the structure's constructor; anything else stuck.
* E7 `app f a m`: `f`, then the argument slot by mode (`strict` evaluates,
  `byName` suspends, `irr` binds `irr`), then `apply` — the curried
  left-to-right order that Lam uses (02 §4.2).
* E8 `const` (δ): through the table (`prim`, `csimp`, `eqn`, `case`), then
  the declaration: special heads give a `pap` (fired at once when nullary);
  a safe definition or an allowlisted opaque evaluates its value (charged);
  theorems, axioms, other opaques, unsafe and partial constants are stuck.
* A1 β on a closure, guarded by `propWhen` (charged); A2 `pap` accumulation
  (free), firing at arity; A3 applying anything else is stuck.
* F1 constructors force their fields (`Nat.zero`/`succ` give literals);
  F2 ordinary ι forces the major, peeling `Nat` literals (charged); F3
  subsingleton ι takes fields from index slots or `irr` without forcing the
  major; F4 empty recursors trap; F5 `case` forces the major and the
  selected minor and applies it to the fields (charged); F6 primitives on
  literals; F7 `Quot.mk`; F8 `Quot.lift` (charged).
* E9 string expansion is not in the Phase 1 fragment: a string used as a
  projection subject or major is stuck (`Admit` declines strings).

Applying or projecting `irr` is stuck at every level (06 S38). SrcEval never
returns `resource`; `Nat` is exact (06 S19). -/

namespace Compilatrix.Src

open Compilatrix.Sem (Result)

/-- Peel exactly `n` leading λs. -/
def peelLams : Nat → Term → Option Term
  | 0, t => some t
  | n + 1, .lam _ _ t => peelLams n t
  | _ + 1, _ => none

namespace Program

/-- Arity of a special head (0 for a malformed one, which fires and sticks). -/
def headArity (p : Program) : Head → Nat
  | .ctor c =>
    match p.decl? c with
    | some (.ctor _ _ _ _ np nf _) => np + nf
    | _ => 0
  | .quotMk _ => 3
  | .quotLift _ => 6
  | .recr r => ((p.decl? r).bind Decl.recArity).getD 0
  | .cases c =>
    match p.table.resolveOf c with
    | some (.case r) =>
      match p.decl? r with
      | some (.recr _ _ _ np _ nmin ni _ _ _) => np + 1 + ni + 1 + nmin
      | _ => 0
    | _ => 0
  | .prim op => op.arity

/-- The rule and field slots for a forced major (F2): `Nat` literals peel
when the recursor's inductive is the pinned `Nat`; otherwise the value must
be a constructor of that inductive with exactly `np` parameters. -/
def selectRule (p : Program) (ind np : CId) (major : Value) : Option (Nat × List Slot) :=
  match major with
  | .lit n =>
    if some ind == p.known.nat then
      match n with
      | 0 => some (0, [])
      | n + 1 => some (1, [.val (.lit n)])
    else none
  | .con c _ ps fs =>
    match p.decl? c with
    | some (.ctor _ _ ind' cidx _ _ _) =>
      if ind' == ind && ps.length == np then some (cidx, fs.map .val) else none
    | _ => none
  | _ => none

def isQuotCtor (p : Program) (c : CId) : Bool :=
  match p.decl? c with
  | some (.quot .ctor ..) => true
  | _ => false

/-- A `Bool` result as the pinned constructor. -/
def boolValue (p : Program) (b : Bool) : Result Value :=
  match (if b then p.known.boolTrue else p.known.boolFalse) with
  | some c => .ok (.con c [] [] [])
  | none => .stuck

/-- E6: the field of the structure's only constructor. -/
def projectField (p : Program) (s : CId) (i : Nat) : Value → Result Value
  | .con c _ _ fs =>
    match p.decl? s with
    | some (.induct _ _ _ _ _ ctors) =>
      if ctors.size == 1 && ctors[0]? == some c then Result.ofOption fs[i]? else .stuck
    | _ => .stuck
  | _ => .stuck

end Program

/-- Literal arguments of a primitive. -/
def litArgs : List Value → Option (List Nat)
  | [] => some []
  | .lit n :: vs => (litArgs vs).map (n :: ·)
  | _ => none

mutual

def eval (p : Program) (k : Nat) (ls : Levels) (ρ : Env) (t : Term) : Result Value :=
  match t with
  | .var i =>
    match ρ[i]? with
    | some s => force p k s
    | none => .stuck
  | .sort _ | .pi .. => .ok (.irr (some t) ρ ls)
  | .natLit n => .ok (.lit n)
  | .strLit s => .ok (.str s)
  | .lam b d body => .ok (.clo b d body ρ ls)
  | .letE _ r _ v body =>
    if r == .rel then
      match eval p k ls ρ v with
      | .ok x => eval p k ls (.val x :: ρ) body
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    else eval p k ls (.val (.irr (some v) ρ ls) :: ρ) body
  | .proj s i e =>
    match eval p k ls ρ e with
    | .ok v => p.projectField s i v
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .app f a m =>
    match eval p k ls ρ f with
    | .ok fv =>
      match m with
      | .strict =>
        match eval p k ls ρ a with
        | .ok x => apply p k fv (.val x)
        | .timeout => .timeout
        | .resource r => .resource r
        | .trap => .trap
        | .stuck => .stuck
      | .byName => apply p k fv (.name a ρ ls)
      | .irr => apply p k fv (.val (.irr (some a) ρ ls))
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .const c us => evalConst p k (us.map (evalUniv ls)) c
termination_by (k, sizeOf t + 3, 0)

/-- E8 (δ) at the instantiated levels `ls`. -/
def evalConst (p : Program) (k : Nat) (ls : Levels) (c : CId) : Result Value :=
  match p.table.resolveOf c with
  | some (.prim op) => headValue p k ls (.prim op)
  | some (.csimp g vs _) =>
    match k with
    | 0 => .timeout
    | k + 1 => eval p k ls [] (.const g vs)
  | some (.eqn _ body) =>
    match k with
    | 0 => .timeout
    | k + 1 => eval p k ls [] body
  | some (.case _) => headValue p k ls (.cases c)
  | none =>
    match p.decl? c with
    | some (.ctor ..) => headValue p k ls (.ctor c)
    | some (.recr ..) => headValue p k ls (.recr c)
    | some (.quot .ctor ..) => headValue p k ls (.quotMk c)
    | some (.quot .lift ..) => headValue p k ls (.quotLift c)
    | some (.defn .defn .safe _ _ v) =>
      match k with
      | 0 => .timeout
      | k + 1 => eval p k ls [] v
    | some (.defn .opaq .safe _ _ v) =>
      if p.table.isOpaqueByValue c then
        match k with
        | 0 => .timeout
        | k + 1 => eval p k ls [] v
      else .stuck
    | _ => .stuck
termination_by (k, 2, 0)

/-- A special head as a value: fired at once when nullary. -/
def headValue (p : Program) (k : Nat) (ls : Levels) (h : Head) : Result Value :=
  if p.headArity h == 0 then fire p k h ls [] else .ok (.pap h ls [])
termination_by (k, 1, 1)

def apply (p : Program) (k : Nat) (f : Value) (s : Slot) : Result Value :=
  match f with
  | .clo b _ body ρ ls =>
    if b.propWhen.allowsBeta ls then
      match k with
      | 0 => .timeout
      | k + 1 => eval p k ls (s :: ρ) body
    else .stuck
  | .pap h ls args =>
    let args := args ++ [s]
    let arity := p.headArity h
    if args.length == arity then fire p k h ls args
    else if args.length < arity then .ok (.pap h ls args)
    else .stuck
  | _ => .stuck
termination_by (k, 2, 0)

def applyAll (p : Program) (k : Nat) (f : Value) (ss : List Slot) : Result Value :=
  match ss with
  | [] => .ok f
  | s :: rest =>
    match apply p k f s with
    | .ok v => applyAll p k v rest
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
termination_by (k, 2, ss.length + 1)

/-- Fire a saturated special head (F1–F8). -/
def fire (p : Program) (k : Nat) (h : Head) (ls : Levels) (args : List Slot) : Result Value :=
  match h with
  | .ctor c =>
    match p.decl? c with
    | some (.ctor _ _ _ _ np _ _) =>
      match forceAll p k (args.drop np) with
      | .ok fields =>
        if some c == p.known.natZero then .ok (.lit 0)
        else if some c == p.known.natSucc then
          match fields with
          | [.lit n] => .ok (.lit (n + 1))
          | _ => .stuck
        else .ok (.con c ls (args.take np) fields)
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | _ => .stuck
  | .quotMk c =>
    match args with
    | [α, r, a] =>
      match force p k a with
      | .ok v => .ok (.con c ls [α, r] [v])
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | _ => .stuck
  | .quotLift _ =>
    match k with
    | 0 => .timeout
    | k + 1 =>
      match args with
      | [_, _, _, f, _, q] =>
        match force p k q with
        | .ok (.con c' _ _ [a]) =>
          if p.isQuotCtor c' then
            match force p k f with
            | .ok fv => apply p k fv (.val a)
            | .timeout => .timeout
            | .resource r => .resource r
            | .trap => .trap
            | .stuck => .stuck
          else .stuck
        | .ok _ => .stuck
        | .timeout => .timeout
        | .resource r => .resource r
        | .trap => .trap
        | .stuck => .stuck
      | _ => .stuck
  | .recr r =>
    match k with
    | 0 => .timeout
    | k + 1 =>
      match p.decl? r, p.table.recKindOf r with
      | some (.recr _ _ _ np nmot nmin ni ind rules _), some kind =>
        let pre := args.take (np + nmot + nmin)
        let chosen : Result (Nat × List Slot) :=
          match kind with
          | .empty => .trap
          | .ordinary =>
            match force p k (args.getD (np + nmot + nmin + ni) default) with
            | .ok major => Result.ofOption (p.selectRule ind np major)
            | .timeout => .timeout
            | .resource r => .resource r
            | .trap => .trap
            | .stuck => .stuck
          | .subsingleton srcs =>
            let indices := (args.drop (np + nmot + nmin)).take ni
            .ok (0, srcs.toList.map fun
              | .index i => indices.getD i (Slot.irrNone ls)
              | .proof => Slot.irrNone ls)
        match chosen with
        | .ok (j, fields) =>
          match rules[j]? with
          | some rule =>
            let slots := pre ++ fields
            match peelLams slots.length rule.rhs with
            | some body => eval p k ls slots.reverse body
            | none => .stuck
          | none => .stuck
        | .timeout => .timeout
        | .resource r => .resource r
        | .trap => .trap
        | .stuck => .stuck
      | _, _ => .stuck
  | .cases c =>
    match k with
    | 0 => .timeout
    | k + 1 =>
      match p.table.resolveOf c with
      | some (.case r) =>
        match p.decl? r, p.table.recKindOf r with
        | some (.recr _ _ _ np _ _ ni ind _ _), some kind =>
          let chosen : Result (Nat × List Slot) :=
            match kind with
            | .empty => .trap
            | .ordinary =>
              match force p k (args.getD (np + 1 + ni) default) with
              | .ok major => Result.ofOption (p.selectRule ind np major)
              | .timeout => .timeout
              | .resource r => .resource r
              | .trap => .trap
              | .stuck => .stuck
            | .subsingleton srcs =>
              .ok (0, srcs.toList.map fun
                | .index i => args.getD (np + 1 + i) (Slot.irrNone ls)
                | .proof => Slot.irrNone ls)
          match chosen with
          | .ok (j, fields) =>
            match force p k (args.getD (np + 1 + ni + 1 + j) default) with
            | .ok minor => applyAll p k minor fields
            | .timeout => .timeout
            | .resource r => .resource r
            | .trap => .trap
            | .stuck => .stuck
          | .timeout => .timeout
          | .resource r => .resource r
          | .trap => .trap
          | .stuck => .stuck
        | _, _ => .stuck
      | _ => .stuck
  | .prim op =>
    match forceAll p k args with
    | .ok vs =>
      match litArgs vs with
      | some ns =>
        match op.evalLits ns with
        | some (.nat n) => .ok (.lit n)
        | some (.bool b) => p.boolValue b
        | none => .stuck
      | none => .stuck
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
termination_by (k, 1, 0)

def force (p : Program) (k : Nat) (s : Slot) : Result Value :=
  match s with
  | .val v => .ok v
  | .name t ρ ls =>
    match k with
    | 0 => .timeout
    | k + 1 => eval p k ls ρ t
termination_by (k, 0, 0)

def forceAll (p : Program) (k : Nat) (ss : List Slot) : Result (List Value) :=
  match ss with
  | [] => .ok []
  | s :: rest =>
    match force p k s with
    | .ok v =>
      match forceAll p k rest with
      | .ok vs => .ok (v :: vs)
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
termination_by (k, 0, ss.length + 1)

end

/-- Run a root on argument values: δ on the root, then β per argument. -/
def run (p : Program) (k : Nat) (root : CId) (xs : List Value) : Result Value :=
  match evalConst p k [] root with
  | .ok f => applyAll p k f (xs.map .val)
  | r => r

end Compilatrix.Src
