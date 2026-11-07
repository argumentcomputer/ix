import IxCC.Anf.Syntax
import IxCC.Sem.Result

/-! # Anf semantics

The clocked big-step semantics of Anf (design note 02 §6.2). As in Lam, the
clock is a **depth bound**: a charge evaluates the rest of its computation
at `k - 1`, and sequenced computations each run at `k`.

* Atoms read the environment (no charge; variables hold values, since thunks
  are closures `fn [_] …` after ANF conversion).
* `bind` evaluates its right-hand side, then the body with the value pushed.
* `join n rec b e` pushes a join closure (environment, join environment,
  arity, body) and evaluates `e`. `jump j as` **charges one unit** and runs
  join point `j`'s body in its own environments extended by the arguments;
  a recursive join point sees itself at index 0 (06 S30).
* `case` reads its scrutinee as a constructor (`asCtor`, with `Nat`
  literals peeling into the pinned keys) and takes the first alternative
  whose key and arity match, else the default, else stuck.
* `glob g` of a function global is its closure (free); of a CAF, its body
  evaluated in the empty environment (charged).
* `call g as` enters `g` (charged); arity mismatches are stuck.
* `applyN f vs` is Lean's `apply`, with **one charge per application of a
  non-empty argument list**: under-saturation extends the closure's
  arguments, exact saturation enters the body, over-saturation enters and
  then applies the result to the rest (another charge). Charging the
  under-saturated case is what lets a Lam application, which always
  charges, map to one `app` (a deliberate divergence from 02 §6.2, which
  charges only at saturation and so needs extra ticks).
* `proj`, `case`, `prim` and application of □ (or of any non-closure) are
  stuck (06 S38); `trap` traps; scope and arity errors are stuck.

Anf never returns `resource` (`Nat` is exact). The semantics is never
evaluated on the recheck path (D17), so it recurses well-founded on the
clock and the term size. -/

namespace IxCC.Anf

open IxCC.Sem (Result)

mutual

inductive Val where
  /-- A closure of arity `n` over environment `ρ` with `got.length < n`
  arguments supplied. -/
  | clos (ρ : List Val) (n : Nat) (b : Exp) (got : List Val)
  | con (c : Key.CtorKey) (fs : List Val)
  | lit (l : Lam.Lit)
  | box

end

instance : Inhabited Val := ⟨.box⟩

/-- A join closure. -/
inductive JClo where
  | mk (ρ : List Val) (J : List JClo) (n : Nat) (b : Exp) (rec : Bool)

instance : Inhabited JClo := ⟨.mk [] [] 0 .trap false⟩

namespace Val

/-- A value as a constructor: `Nat` literals peel as `Nat.zero`/`Nat.succ`
with the pinned keys. -/
def asCtor (K : Lam.Known) : Val → Option (Key.CtorKey × List Val)
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

def Atom.eval (ρ : List Val) : Atom → Option Val
  | .var i => ρ[i]?
  | .lit l => some (.lit l)
  | .box => some .box

def evalAtoms (ρ : List Val) : List Atom → Option (List Val)
  | [] => some []
  | a :: as =>
    match a.eval ρ, evalAtoms ρ as with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Literal arguments of a primitive. -/
def natArgs : List Val → Option (List Nat)
  | [] => some []
  | .lit (.nat n) :: vs => (natArgs vs).map (n :: ·)
  | _ => none

/-- A saturated primitive on evaluated arguments (as Lam's `primResult`). -/
def primResult (K : Lam.Known) (p : Lam.Prim) (vs : List Val) : Result Val :=
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

def eval (P : Program) (k : Nat) (ρ : List Val) (J : List JClo) (e : Exp) : Result Val :=
  match e with
  | .bind _ b body =>
    match evalBind P k ρ b with
    | .ok v => eval P k (v :: ρ) J body
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .join n r b body => eval P k ρ (.mk ρ J n b r :: J) body
  | .jump j as =>
    match J[j]?, evalAtoms ρ as with
    | some (.mk ρ' J' n b r), some vs =>
      if vs.length = n then
        match k with
        | 0 => .timeout
        | k + 1 => eval P k (vs.reverse ++ ρ') (if r then .mk ρ' J' n b r :: J' else J') b
      else .stuck
    | _, _ => .stuck
  | .case x alts d =>
    match x.eval ρ with
    | some v =>
      match v.asCtor P.known with
      | some (c, fs) => evalAlts P k ρ J c fs alts d
      | none => .stuck
    | none => .stuck
  | .ret a => Result.ofOption (a.eval ρ)
  | .tick body =>
    match k with
    | 0 => .timeout
    | k + 1 => eval P k ρ J body
  | .trap => .trap
termination_by (k, sizeOf e + 1, 0)

def evalBind (P : Program) (k : Nat) (ρ : List Val) (b : Bind) : Result Val :=
  match b with
  | .atom a => Result.ofOption (a.eval ρ)
  | .con c as =>
    match evalAtoms ρ as with
    | some vs => .ok (.con c vs)
    | none => .stuck
  | .proj c i x =>
    match x.eval ρ with
    | some (.con c' fs) => if c' = c then Result.ofOption fs[i]? else .stuck
    | _ => .stuck
  | .prim p as =>
    match evalAtoms ρ as with
    | some vs => primResult P.known p vs
    | none => .stuck
  | .glob g =>
    match P.global? g with
    | some gd =>
      match gd.ps with
      | [] =>
        match k with
        | 0 => .timeout
        | k + 1 => eval P k [] [] gd.body
      | _ :: _ => .ok (.clos [] gd.ps.length gd.body [])
    | none => .stuck
  | .call g as =>
    match P.global? g, evalAtoms ρ as with
    | some gd, some vs =>
      if vs.length = gd.ps.length then
        match k with
        | 0 => .timeout
        | k + 1 => eval P k vs.reverse [] gd.body
      else .stuck
    | _, _ => .stuck
  | .app f as =>
    match f.eval ρ, evalAtoms ρ as with
    | some fv, some vs => applyN P k fv vs
    | _, _ => .stuck
  | .fn ps body =>
    match ps with
    | [] => .stuck
    | _ :: _ => .ok (.clos ρ ps.length body [])
termination_by (k, sizeOf b + 1, 0)

/-- Apply a value to arguments: one charge per non-empty application. -/
def applyN (P : Program) (k : Nat) (f : Val) (vs : List Val) : Result Val :=
  match vs with
  | [] => .ok f
  | v :: rest =>
    match f with
    | .clos ρ n b got =>
      match k with
      | 0 => .timeout
      | k + 1 =>
        if _h : got.length < n then
          if got.length + (v :: rest).length < n then .ok (.clos ρ n b (got ++ v :: rest))
          else
            let all := got ++ v :: rest
            match eval P k ((all.take n).reverse ++ ρ) [] b with
            | .ok r => applyN P (k + 1) r (all.drop n)
            | .timeout => .timeout
            | .resource r => .resource r
            | .trap => .trap
            | .stuck => .stuck
        else .stuck
    | _ => .stuck
termination_by (k, 0, vs.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.right
       simp only [List.length_drop, List.length_append, List.length_cons]; omega)

/-- The first alternative whose key and arity match, with the fields bound
(field `i` of `n` at index `n - 1 - i`); else the default; else stuck. -/
def evalAlts (P : Program) (k : Nat) (ρ : List Val) (J : List JClo) (c : Key.CtorKey)
    (fs : List Val) (alts : List Alt) (d : Option Exp) : Result Val :=
  match alts with
  | [] =>
    match d with
    | some e => eval P k ρ J e
    | none => .stuck
  | .mk key n body :: rest =>
    if key = c ∧ n = fs.length then eval P k (fs.reverse ++ ρ) J body
    else evalAlts P k ρ J c fs rest d
termination_by (k, sizeOf alts + sizeOf d + 1, 0)

end

/-- Run a root on argument values: its value (a closure for a function
global), then one application of all arguments. -/
def run (P : Program) (k : Nat) (root : GlobalId) (xs : List Val) : Result Val :=
  match evalBind P k [] (.glob root) with
  | .ok f => applyN P k f xs
  | r => r

end IxCC.Anf
