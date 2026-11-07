import IxCC.Lam.Syntax
import IxCC.Sem.Result

/-! # Lam semantics

The clocked big-step semantics of Lam (design note 02 §4.2), with the same
slot discipline and the same clock as SrcEval: the clock is a **depth
bound**, charged at a `name`-slot read, a `glob` (δ), closure entry (β) and
`tick`, so erasure can be clock-exact wherever it keeps SrcEval's charges.

* `var i`: a `val` slot gives its value; a `name` slot evaluates its term in
  its environment (charged; call by name, not memoised).
* `glob g` evaluates `g`'s closed body in `[]` (charged).
* `app f a strict` evaluates `f`, then `a`, then applies; `app f a name`
  evaluates `f` and applies to the thunk `name ρ a`. `apply` enters a
  closure (charged); applying anything else is stuck.
* `letE` is strict. `con` evaluates its fields left to right.
* `case` evaluates the scrutinee and reads it as a constructor (`asCtor`:
  `Nat` literals peel into the pinned `Nat` keys); it takes the first
  alternative whose key **and** arity match, else the default, else stuck.
* `proj c i` of `con c fs` is `fs[i]`; any other value (another key, □) is
  stuck.
* `prim` evaluates its arguments left to right, then needs literals.
* `tick t` charges one unit; `box` is □; `trap` traps.
* **□ is stuck** under `apply`, `proj`, `case` and `prim` (06 S38): no
  absorption, as in SrcEval.

Lam never returns `resource`: `Nat` is exact (06 S19). The semantics is
never evaluated on the recheck path (D17), so it recurses well-founded on
`(k, size)` like SrcEval. -/

namespace IxCC.Lam

open IxCC.Sem (Result)

mutual

inductive Val where
  | clos (ρ : List Slot) (b : Term)
  | con (c : Key.CtorKey) (fs : List Val)
  | lit (l : Lit)
  | box

inductive Slot where
  | val (v : Val)
  | name (ρ : List Slot) (t : Term)

end

instance : Inhabited Val := ⟨.box⟩
instance : Inhabited Slot := ⟨.val .box⟩

abbrev Env := List Slot

namespace Val

/-- A value as a constructor: `Nat` literals peel as `Nat.zero`/`Nat.succ`
with the pinned keys (IxIR₀'s `natLit`). -/
def asCtor (K : Known) : Val → Option (Key.CtorKey × List Val)
  | .con c fs => some (c, fs)
  | .lit (.nat 0) => K.natZero.map (·, [])
  | .lit (.nat (n + 1)) => K.natSucc.map (·, [.lit (.nat n)])
  | _ => none

def shape : Val → String
  | .clos .. => "clos"
  | .con _ fs => s!"con/{fs.length}"
  | .lit (.nat n) => s!"lit {n}"
  | .lit (.str _) => "str"
  | .box => "box"

end Val

/-- Literal arguments of a primitive. -/
def natArgs : List Val → Option (List Nat)
  | [] => some []
  | .lit (.nat n) :: vs => (natArgs vs).map (n :: ·)
  | _ => none

/-- A saturated primitive on evaluated arguments. -/
def primResult (K : Known) (p : Prim) (vs : List Val) : Result Val :=
  match natArgs vs with
  | some ns =>
    match p.sem ns with
    | some (.nat n) => .ok (.lit (.nat n))
    | some (.bool b) =>
      match (if b then K.boolTrue else K.boolFalse) with
      | some c => .ok (.con c [])
      | none => .stuck
    | none => .stuck
  | none => .stuck

mutual

def eval (P : Program) (k : Nat) (ρ : Env) (t : Term) : Result Val :=
  match t with
  | .var i =>
    match ρ[i]? with
    | some s => force P k s
    | none => .stuck
  | .glob g =>
    match P.global? g with
    | some gl =>
      match k with
      | 0 => .timeout
      | k + 1 => eval P k [] gl.body
    | none => .stuck
  | .lam _ _ b => .ok (.clos ρ b)
  | .app f a m =>
    match eval P k ρ f with
    | .ok fv =>
      match m with
      | .strict =>
        match eval P k ρ a with
        | .ok av => apply P k fv (.val av)
        | .timeout => .timeout
        | .resource r => .resource r
        | .trap => .trap
        | .stuck => .stuck
      | .name => apply P k fv (.name ρ a)
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .letE _ v b =>
    match eval P k ρ v with
    | .ok x => eval P k (.val x :: ρ) b
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .con c fs =>
    match evalList P k ρ fs with
    | .ok vs => .ok (.con c vs)
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .case s alts d =>
    match eval P k ρ s with
    | .ok v =>
      match v.asCtor P.known with
      | some (c, fs) => evalAlts P k ρ c fs alts d
      | none => .stuck
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .proj c i s =>
    match eval P k ρ s with
    | .ok (.con c' fs) => if c' = c then Result.ofOption fs[i]? else .stuck
    | .ok _ => .stuck
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .lit l => .ok (.lit l)
  | .prim p args =>
    match evalList P k ρ args with
    | .ok vs => primResult P.known p vs
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .tick b =>
    match k with
    | 0 => .timeout
    | k + 1 => eval P k ρ b
  | .box => .ok .box
  | .trap => .trap
termination_by (k, sizeOf t + 3)

/-- Enter a closure (charged); anything else is stuck. -/
def apply (P : Program) (k : Nat) (f : Val) (s : Slot) : Result Val :=
  match f with
  | .clos ρ b =>
    match k with
    | 0 => .timeout
    | k + 1 => eval P k (s :: ρ) b
  | _ => .stuck
termination_by (k, 2)

/-- Read a slot: a `name` slot is evaluated (charged). -/
def force (P : Program) (k : Nat) (s : Slot) : Result Val :=
  match s with
  | .val v => .ok v
  | .name ρ t =>
    match k with
    | 0 => .timeout
    | k + 1 => eval P k ρ t
termination_by (k, 1)

def evalList (P : Program) (k : Nat) (ρ : Env) (ts : List Term) : Result (List Val) :=
  match ts with
  | [] => .ok []
  | t :: rest =>
    match eval P k ρ t with
    | .ok v =>
      match evalList P k ρ rest with
      | .ok vs => .ok (v :: vs)
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
termination_by (k, sizeOf ts + 3)

/-- The first alternative whose key and arity match, with the fields bound
(field `i` of `n` at index `n - 1 - i`); else the default; else stuck. -/
def evalAlts (P : Program) (k : Nat) (ρ : Env) (c : Key.CtorKey) (fs : List Val)
    (alts : List Alt) (d : Option Term) : Result Val :=
  match alts with
  | [] =>
    match d with
    | some t => eval P k ρ t
    | none => .stuck
  | .mk key n body :: rest =>
    if key = c ∧ n = fs.length then eval P k (fs.reverse.map .val ++ ρ) body
    else evalAlts P k ρ c fs rest d
termination_by (k, sizeOf alts + sizeOf d + 3)

end

/-- Apply a value to argument slots, left to right. -/
def applyAll (P : Program) (k : Nat) (f : Val) : List Slot → Result Val
  | [] => .ok f
  | s :: rest =>
    match apply P k f s with
    | .ok v => applyAll P k v rest
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck

/-- Run a root on argument values: `glob` of the root, then one application
per argument (as `Src.run`: δ, then β per argument). -/
def run (P : Program) (k : Nat) (root : GlobalId) (xs : List Val) : Result Val :=
  match eval P k [] (.glob root) with
  | .ok f => applyAll P k f (xs.map .val)
  | r => r

end IxCC.Lam
