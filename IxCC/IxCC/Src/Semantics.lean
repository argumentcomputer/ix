import IxCC.Src.Value
import IxCC.Src.Prim
import IxCC.Sem.Result

/-! # SrcEval

The clocked big-step semantics of Src, the stage-S
meaning of a program. Rules:

* E1 `var`: a `val` slot gives its value; a `name` slot is evaluated in its
  environment (clock charge, not memoised).
* E2 `sort`/`pi`: `irr`. E3 literals. E4 `lam`: a closure.
* E5 `letE`: a let irrelevant at the current levels binds `irr`; others
  evaluate their value.
* E6 `proj`: the field of the structure's constructor; anything else stuck.
* E7 `app f a m r`: `f`, then the argument slot: `irr` where `r` is
  irrelevant at the current levels, otherwise by mode (`strict` evaluates,
  `byName` suspends), then `apply` — the curried left-to-right order that
  Lam uses.
* E8 `const` (δ): through the table (`prim`, `csimp`, `eqn`, `case`), then
  the declaration: special heads give a `pap` (fired at once when nullary);
  a safe definition or an allowlisted opaque evaluates its value (charged);
  theorems, axioms, other opaques, unsafe and partial constants are stuck.
* A1 β on a closure, guarded by `propWhen` (charged); A2 `pap` accumulation
  (free), firing at arity; A3 applying anything else is stuck.
* F1 constructors force their fields (`Nat.zero`/`succ` give literals);
  F2 ordinary ι forces the major, peeling `Nat` literals (charged); F3
  subsingleton ι takes fields from index slots or `irr` without forcing the
  major (a `subsingleton when` recursor takes F3 where `when` holds at its
  levels and F2 elsewhere); F4 empty recursors trap; F5 `case` forces the major and the
  selected minor and applies it to the fields (charged); F6 primitives on
  literals; F7 `Quot.mk`; F8 `Quot.lift` (charged).
* F6w (stage W1): a fixed-width word operation (a `word` table entry) forces its
  arguments, reads each as the tower `UIntN.ofBitVec (BitVec.ofFin (Fin.mk n _))`
  of the pinned constructors with `n` below the width's size (`ofNat`'s as a
  `Nat` literal), and returns `WordOp.eval`'s result as a tower (`mkWord?`) or a
  literal; anything else, an out-of-range tower included, is stuck. Not
  charged, as F6 is not.
* E9 string expansion is not in the Phase 1 fragment: a string used as a
  projection subject or major is stuck (`Admit` declines strings).

Relevance is level-exact (D18): every `irr` decision (E5, E7, and the kind
of F2/F3/F5) is taken at the concrete levels SrcEval carries, so
sort-polymorphic code at `Sort 0` passes `irr` exactly where its position is
a proof. Applying or projecting `irr` is stuck at every level.
SrcEval never returns `resource`; `Nat` is exact. -/

namespace IxCC.Src

open IxCC.Sem (Result)

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
  | .word _ op => op.arity

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

/-- The constructor `UIntN.ofBitVec` of width `w`, where pinned and present. -/
def wordCtor? (p : Program) (w : Width) : Option CId := p.known.wordCtors.lookup w

/-- A value read as a word of width `w` (F6w): the tower `UIntN.ofBitVec (BitVec.ofFin (Fin.mk n
_))` of the pinned constructors around a literal `n` below the width's size. Its parameter slots
and proof are not read; the number is, and a tower whose number is at or above the size (which
only a false proof of `Fin.mk`'s bound builds) is not a word here, so F6w is stuck on it rather
than computing what the reference body would. -/
def asWord? (p : Program) (w : Width) : Value → Option Nat
  | .con c _ [] [.con c' _ [_] [.con c'' _ [_] [.lit n, _]]] =>
    if some c == p.wordCtor? w && some c' == p.known.bitVecOfFin && some c'' == p.known.finMk &&
        decide (n < w.size) then
      some n
    else none
  | _ => none

/-- The tower of a word (F6w's result): the parameters as literal slots, the proof field `irr`
with no term. -/
def mkWord? (p : Program) (w : Width) (n : Nat) : Option Value := do
  let c ← p.wordCtor? w
  let bv ← p.known.bitVecOfFin
  let fin ← p.known.finMk
  pure (.con c [] [] [.con bv [] [.val (.lit w.bits)]
    [.con fin [] [.val (.lit w.size)] [.lit n, .irr none [] []]]])

/-- A word operation's result as a value: a tower or a literal. A decision is stuck: no table
entry makes one a primitive in stage W1 (`WordOp.isPrimitive`). -/
def wordResult (p : Program) : WordResult → Result Value
  | .word w n => Result.ofOption (p.mkWord? w n)
  | .nat n => .ok (.lit n)
  | .dec _ => .stuck

/-- F6w on the forced arguments: `ofNat`'s a literal, every other argument a word of width
`w`, as many as the operation's arity. -/
def wordValue (p : Program) (w : Width) (op : WordOp) : List Value → Result Value
  | [a] =>
    if op.arity != 1 then .stuck
    else
      let x? : Option Nat := match op, a with
        | .ofNat, .lit n => some n
        | .ofNat, _ => none
        | _, v => p.asWord? w v
      match x? with
      | some x => p.wordResult (op.eval w x 0)
      | none => .stuck
  | [a, b] =>
    if op.arity != 2 then .stuck
    else
      match p.asWord? w a, p.asWord? w b with
      | some x, some y => p.wordResult (op.eval w x y)
      | _, _ => .stuck
  | _ => .stuck

/-- E6: the field of the structure's only constructor. -/
def projectField (p : Program) (s : CId) (i : Nat) : Value → Result Value
  | .con c _ _ fs =>
    match p.decl? s with
    | some (.induct _ _ _ _ _ ctors) =>
      if ctors.length == 1 && ctors.head? == some c then Result.ofOption fs[i]? else .stuck
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
    if r.irrAt ls then eval p k ls (.val (.irr (some v) ρ ls) :: ρ) body
    else
      match eval p k ls ρ v with
      | .ok x => eval p k ls (.val x :: ρ) body
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
  | .proj s i e =>
    match eval p k ls ρ e with
    | .ok v => p.projectField s i v
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .app f a m r =>
    match eval p k ls ρ f with
    | .ok fv =>
      if r.irrAt ls then apply p k fv (.val (.irr (some a) ρ ls))
      else
        match m with
        | .strict =>
          match eval p k ls ρ a with
          | .ok x => apply p k fv (.val x)
          | .timeout => .timeout
          | .resource r => .resource r
          | .trap => .trap
          | .stuck => .stuck
        | .byName => apply p k fv (.name a ρ ls)
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
  | some (.word w op _) => headValue p k ls (.word w op)
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
      match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
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
          | .subsingleton _ srcs =>
            let indices := (args.drop (np + nmot + nmin)).take ni
            .ok (0, srcs.map fun
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
        match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
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
            | .subsingleton _ srcs =>
              .ok (0, srcs.map fun
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
  | .word w op =>
    match forceAll p k args with
    | .ok vs => p.wordValue w op vs
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

/-- The evaluator contract's version (`docs/evaluator-interface.md`, EV-1's versions so far): 1,
the rules E1–E9, A1–A3 and F1–F8; 2, with F6w (stage W1, the fixed-width word operations). -/
def contractVersion : Nat := 2

/-- Run a root on argument values: δ on the root, then β per argument. -/
def run (p : Program) (k : Nat) (root : CId) (xs : List Value) : Result Value :=
  match evalConst p k [] root with
  | .ok f => applyAll p k f (xs.map .val)
  | r => r

end IxCC.Src
