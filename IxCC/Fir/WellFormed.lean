import IxCC.Fir.Syntax

/-! # Fir well-formedness

`Fir.WellFormed P` (design note 03 §2.1), decided by `Fir.check`, which
names the first violation:

* **single binding:** every variable is bound once per function (parameters,
  `bind`s, join parameters), every join point once, all below the
  function's `vars`/`joins` supply;
* **scope:** every variable is used where it is bound (a `bind` scopes over
  its continuation, a join point's parameters over its body, the variables
  of the enclosing scope are visible in join bodies and case arms); every
  jump targets a join point in scope (a recursive one is in scope in its own
  body) with its arity; jumps are in tail position by construction;
* **calls** name a function with the right number of arguments;
* **constructors:** a `ctor`'s info is `CtorInfo.ofKey` of its key and it
  has that many arguments; `proj` indices and `case` keys come from the
  table, and a `case`'s keys are distinct; primitives are saturated;
* **Phase 1 representation:** every parameter is `tobj` (06 S33);
* **program:** every function `0 … size - 1` is present, function keys are
  pairwise distinct (D19), exports are in range, and the pinned keys have
  the arities `Nat` peeling and Boolean primitives need.

Not on the recheck path (it is `Fir.lower`'s postcondition, 03 §2.2). -/

namespace IxCC.Fir

open IxCC.Src (NatSet NatMap)

namespace Check

/-- What checking a function body reads. -/
structure Ctx where
  P : Program
  /-- Bound on variables and join points. -/
  vars : Nat
  joins : Nat

def argOk (scope : NatSet) : Arg → Bool
  | .var x => scope.contains x
  | _ => true

def argsOk (scope : NatSet) (as : List Arg) : Bool := as.all (argOk scope)

def arityOf (P : Program) (f : FunId) : Option Nat := (P.fun? f).map (·.arity)

def rhsOk (P : Program) (scope : NatSet) : Rhs → Except String Unit
  | .arg a => if argOk scope a then .ok () else .error "argument out of scope"
  | .ctor c as =>
    if CtorInfo.ofKey P.ctors c.key != some c then .error "ctor info is not ofKey of its key"
    else if as.length != c.arity then .error "ctor arity"
    else if !argsOk scope as then .error "ctor argument out of scope"
    else .ok ()
  | .proj x c i =>
    if !scope.contains x then .error s!"projection of v{x} out of scope"
    else match CtorInfo.ofKey P.ctors c with
      | some info => if i < info.arity then .ok () else .error "projection index"
      | none => .error "projection key not in the table"
  | .prim p as =>
    if as.length != p.arity then .error s!"{p.name} is not saturated"
    else if !argsOk scope as then .error "primitive argument out of scope" else .ok ()
  | .call f as =>
    if arityOf P f != some as.length then .error s!"call of f{f} with {as.length} arguments"
    else if !argsOk scope as then .error "call argument out of scope" else .ok ()

/-- Bind fresh variables: each below the supply and not yet bound. -/
def bindVars (cx : Ctx) (scope seen : NatSet) : List Var → Except String (NatSet × NatSet)
  | [] => .ok (scope, seen)
  | x :: xs =>
    if x ≥ cx.vars then .error s!"v{x} is beyond the variable supply {cx.vars}"
    else if seen.contains x then .error s!"v{x} is bound twice"
    else bindVars cx (scope.insert x) (seen.insert x) xs

def keysOf : List Alt → List Key.CtorKey
  | [] => []
  | .mk k _ :: as => k :: keysOf as

mutual

/-- Check `c` in `scope` with join points `J` (id, arity); `seen` threads the
variables and join points bound so far in the function. -/
def code (cx : Ctx) (scope : NatSet) (J : List (JoinId × Nat)) (seen : NatSet × NatSet) :
    Code → Except String (NatSet × NatSet)
  | .bind x r k => do
    rhsOk cx.P scope r
    let (scope, vs) ← bindVars cx scope seen.1 [x]
    code cx scope J (vs, seen.2) k
  | .jp j ps r b k => do
    if j ≥ cx.joins then throw s!"j{j} is beyond the join supply {cx.joins}"
    if seen.2.contains j then throw s!"j{j} is bound twice"
    let (bscope, vs) ← bindVars cx scope seen.1 ps
    let seen ← code cx bscope (if r then (j, ps.length) :: J else J) (vs, seen.2.insert j) b
    code cx scope ((j, ps.length) :: J) seen k
  | .jmp j as =>
    match J.lookup j with
    | some n =>
      if n != as.length then .error s!"jump to j{j} with {as.length} arguments, arity {n}"
      else if !argsOk scope as then .error "jump argument out of scope"
      else .ok seen
    | none => .error s!"jump to j{j} out of scope"
  | .case x alts d => do
    if !scope.contains x then throw s!"case on v{x} out of scope"
    let ks := keysOf alts
    if !(ks.all fun k => (CtorInfo.ofKey cx.P.ctors k).isSome) then throw "case key not in the table"
    if !decide ks.Nodup then throw "case keys repeat"
    let seen ← alts' cx scope J seen alts
    opt cx scope J seen d
  | .ret a => if argOk scope a then .ok seen else .error "returned variable out of scope"
  | .tcall f as =>
    if arityOf cx.P f != some as.length then .error s!"tail call of f{f} with {as.length} arguments"
    else if !argsOk scope as then .error "tail-call argument out of scope" else .ok seen
  | .trap => .ok seen

def alts' (cx : Ctx) (scope : NatSet) (J : List (JoinId × Nat)) (seen : NatSet × NatSet) :
    List Alt → Except String (NatSet × NatSet)
  | [] => .ok seen
  | .mk _ b :: as => do
    let seen ← code cx scope J seen b
    alts' cx scope J seen as

def opt (cx : Ctx) (scope : NatSet) (J : List (JoinId × Nat)) (seen : NatSet × NatSet) :
    Option Code → Except String (NatSet × NatSet)
  | none => .ok seen
  | some c => code cx scope J seen c

end

def function (P : Program) (f : FunId) (fd : Fun) : Except String Unit := do
  let cx : Ctx := { P, vars := fd.vars, joins := fd.joins }
  if !(fd.params.all (·.2 == .tobj)) then throw s!"f{f}: a parameter is not tobj"
  let (scope, seen) ← (bindVars cx .leaf .leaf (fd.params.map (·.1))).mapError (s!"f{f}: " ++ ·)
  let _ ← (code cx scope [] (seen, .leaf) fd.body).mapError (s!"f{f}: " ++ ·)
  pure ()

/-- The pinned keys have the arities peeling and Boolean results need. -/
def knownOk (P : Program) : Bool :=
  let ok := fun (c : Option Key.CtorKey) (n : Nat) => match c with
    | some c => ((CtorInfo.ofKey P.ctors c).map (·.arity)).all (· == n)
    | none => true
  ok P.known.natZero 0 && ok P.known.natSucc 1 && ok P.known.boolFalse 0 && ok P.known.boolTrue 0

end Check

/-- Well-formedness with the first violation. -/
def check (P : Program) : Except String Unit := do
  for f in List.range P.size do
    match P.fun? f with
    | some fd => Check.function P f fd
    | none => throw s!"f{f} is missing"
  if !decide (P.funList.map (·.2.key)).Nodup then throw "function keys repeat"
  if !(P.exports.all (· < P.size)) then throw "an export is out of range"
  if !decide (P.ctors.map (·.key)).Nodup then throw "constructor table keys repeat"
  if !Check.knownOk P then throw "pinned keys have the wrong arity"

def wellFormed (P : Program) : Bool := (check P).isOk

/-- `Fir.WellFormed` (03 §2.1). -/
def WellFormed (P : Program) : Prop := wellFormed P = true

instance (P : Program) : Decidable (WellFormed P) := inferInstanceAs (Decidable (_ = true))

end IxCC.Fir
