import CompilatrixTests.Src.Support

/-! A test-only instrumented SrcEval that names the cause of a `stuck`
outcome (research note `relevance-checker.md` §2.1, §4.3). It mirrors
`Compilatrix.Src.Semantics` rule for rule; every census run also runs
SrcEval itself and requires the same outcome, so the two cannot drift
apart unnoticed. `Sem.Result` does not change.

Causes are grouped as the census reports them:
* **relevance**: an `irr` value demanded (applied, projected, a major, a
  primitive argument, a quotient, a `Nat.succ` field; R1), the β guard (R2),
  or δ on a theorem or a type (a proof or type evaluated because a position
  was relevant);
* **missing primitive**: δ on an opaque outside the opaque-by-value
  allowlist (an extern with no primitive entry);
* **declined form**: δ on an axiom, an unsafe or partial constant, or a
  string demanded (E9 is not in the Phase 1 fragment);
* **other**: shape errors (R3), scope (R5), malformed heads. -/

namespace CompilatrixTests.Src.StuckEval

open Compilatrix Compilatrix.Src

inductive Cause where
  | irrApplied
  | irrProjected
  | irrMajor
  | irrPrimArg
  | irrQuotient
  | irrField
  | betaGuard
  | proofDelta
  | typeDelta
  | opaqueDelta
  | axiomDelta
  | unsafeDelta
  | stringDemand
  | shape (what : String)
  | scope
  | malformed (what : String)
  deriving BEq, Repr, Inhabited

namespace Cause

/-- The census group of a cause. -/
def group : Cause → String
  | .irrApplied | .irrProjected | .irrMajor | .irrPrimArg | .irrQuotient | .irrField
  | .betaGuard | .proofDelta | .typeDelta => "relevance"
  | .opaqueDelta => "missing primitive"
  | .axiomDelta | .unsafeDelta | .stringDemand => "declined form"
  | .shape _ | .scope | .malformed _ => "other"

def name : Cause → String
  | .irrApplied => "irr applied (A3)"
  | .irrProjected => "irr projected (E6)"
  | .irrMajor => "irr major (F2/F5)"
  | .irrPrimArg => "irr primitive argument (F6)"
  | .irrQuotient => "irr quotient (F8)"
  | .irrField => "irr Nat.succ field (F1)"
  | .betaGuard => "β guard (A1)"
  | .proofDelta => "δ on a theorem (E8)"
  | .typeDelta => "δ on a type (E8)"
  | .opaqueDelta => "δ on an opaque (E8)"
  | .axiomDelta => "δ on an axiom (E8)"
  | .unsafeDelta => "δ on an unsafe or partial constant (E8)"
  | .stringDemand => "string demanded (E9)"
  | .shape w => s!"shape: {w}"
  | .scope => "variable out of scope (E1)"
  | .malformed w => s!"malformed: {w}"

end Cause

/-- A non-`ok` outcome. SrcEval never returns `resource`. -/
inductive Stop where
  | timeout
  | trap
  | stuck (c : Cause)
  deriving BEq, Repr, Inhabited

abbrev Out := Except Stop

def stuck (c : Cause) : Out α := .error (.stuck c)

/-- The cause of a failed demand on a value of the wrong form. -/
def demandCause (irr : Cause) (what : String) : Value → Cause
  | .irr .. => irr
  | .str _ => .stringDemand
  | v => .shape s!"{what} on {v.shape}"

namespace Program

def projectField (p : Program) (s : CId) (i : Nat) : Value → Out Value
  | .con c _ _ fs =>
    match p.decl? s with
    | some (.induct _ _ _ _ _ ctors) =>
      if ctors.length == 1 && ctors.head? == some c then
        match fs[i]? with
        | some v => .ok v
        | none => stuck (.shape "projection index out of range")
      else stuck (.shape "projection of another constructor")
    | _ => stuck (.malformed "projection of a non-inductive")
  | v => stuck (demandCause .irrProjected "projection" v)

def selectRule (p : Program) (ind np : CId) (major : Value) : Out (Nat × List Slot) :=
  match Src.Program.selectRule p ind np major with
  | some r => .ok r
  | none => stuck (demandCause .irrMajor "eliminator major" major)

end Program

mutual

partial def eval (p : Program) (k : Nat) (ls : Levels) (ρ : Env) : Term → Out Value
  | .var i =>
    match ρ[i]? with
    | some s => force p k s
    | none => stuck .scope
  | t@(.sort _) | t@(.pi ..) => .ok (.irr (some t) ρ ls)
  | .natLit n => .ok (.lit n)
  | .strLit s => .ok (.str s)
  | .lam b d body => .ok (.clo b d body ρ ls)
  | .letE _ r _ v body =>
    if r.irrAt ls then eval p k ls (.val (.irr (some v) ρ ls) :: ρ) body
    else do
      let x ← eval p k ls ρ v
      eval p k ls (.val x :: ρ) body
  | .proj s i e => do
    Program.projectField p s i (← eval p k ls ρ e)
  | .app f a m r => do
    let fv ← eval p k ls ρ f
    if r.irrAt ls then apply p k fv (.val (.irr (some a) ρ ls))
    else
      match m with
      | .strict => apply p k fv (.val (← eval p k ls ρ a))
      | .byName => apply p k fv (.name a ρ ls)
  | .const c us => evalConst p k (us.map (evalUniv ls)) c

partial def evalConst (p : Program) (k : Nat) (ls : Levels) (c : CId) : Out Value :=
  match p.table.resolveOf c with
  | some (.prim op) => headValue p k ls (.prim op)
  | some (.csimp g vs _) =>
    match k with
    | 0 => .error .timeout
    | k + 1 => eval p k ls [] (.const g vs)
  | some (.eqn _ body) =>
    match k with
    | 0 => .error .timeout
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
      | 0 => .error .timeout
      | k + 1 => eval p k ls [] v
    | some (.defn .opaq .safe _ _ v) =>
      if p.table.isOpaqueByValue c then
        match k with
        | 0 => .error .timeout
        | k + 1 => eval p k ls [] v
      else stuck .opaqueDelta
    | some (.defn .thm ..) => stuck .proofDelta
    | some (.defn _ _ ..) => stuck .unsafeDelta
    | some (.axio true ..) => stuck .axiomDelta
    | some (.axio false ..) => stuck .unsafeDelta
    | some (.induct ..) | some (.quot .type ..) | some (.quot .ind ..) => stuck .typeDelta
    | none => stuck (.malformed "a reference without a declaration")

partial def headValue (p : Program) (k : Nat) (ls : Levels) (h : Head) : Out Value :=
  if p.headArity h == 0 then fire p k h ls [] else .ok (.pap h ls [])

partial def apply (p : Program) (k : Nat) (f : Value) (s : Slot) : Out Value :=
  match f with
  | .clo b _ body ρ ls =>
    if b.propWhen.allowsBeta ls then
      match k with
      | 0 => .error .timeout
      | k + 1 => eval p k ls (s :: ρ) body
    else stuck .betaGuard
  | .pap h ls args =>
    let args := args ++ [s]
    let arity := p.headArity h
    if args.length == arity then fire p k h ls args
    else if args.length < arity then .ok (.pap h ls args)
    else stuck (.malformed "over-applied head")
  | v => stuck (demandCause .irrApplied "application" v)

partial def applyAll (p : Program) (k : Nat) (f : Value) : List Slot → Out Value
  | [] => .ok f
  | s :: rest => do applyAll p k (← apply p k f s) rest

partial def fire (p : Program) (k : Nat) (h : Head) (ls : Levels) (args : List Slot) : Out Value :=
  match h with
  | .ctor c =>
    match p.decl? c with
    | some (.ctor _ _ _ _ np _ _) => do
      let fields ← forceAll p k (args.drop np)
      if some c == p.known.natZero then .ok (.lit 0)
      else if some c == p.known.natSucc then
        match fields with
        | [.lit n] => .ok (.lit (n + 1))
        | [v] => stuck (demandCause .irrField "Nat.succ field" v)
        | _ => stuck (.malformed "Nat.succ arity")
      else .ok (.con c ls (args.take np) fields)
    | _ => stuck (.malformed "constructor head")
  | .quotMk c =>
    match args with
    | [α, r, a] => do .ok (.con c ls [α, r] [← force p k a])
    | _ => stuck (.malformed "Quot.mk arity")
  | .quotLift _ =>
    match k with
    | 0 => .error .timeout
    | k + 1 =>
      match args with
      | [_, _, _, f, _, q] => do
        match ← force p k q with
        | .con c' _ _ [a] =>
          if p.isQuotCtor c' then apply p k (← force p k f) (.val a)
          else stuck (.shape "Quot.lift of another constructor")
        | v => stuck (demandCause .irrQuotient "Quot.lift" v)
      | _ => stuck (.malformed "Quot.lift arity")
  | .recr r =>
    match k with
    | 0 => .error .timeout
    | k + 1 =>
      match p.decl? r, (p.table.recKindOf r).map (fun k => RecKind.atLevels ls k) with
      | some (.recr _ _ _ np nmot nmin ni ind rules _), some kind => do
        let pre := args.take (np + nmot + nmin)
        let (j, fields) ← match kind with
          | .empty => .error .trap
          | .ordinary => do
            Program.selectRule p ind np (← force p k (args.getD (np + nmot + nmin + ni) default))
          | .subsingleton _ srcs =>
            let indices := (args.drop (np + nmot + nmin)).take ni
            .ok (0, srcs.map fun
              | .index i => indices.getD i (Slot.irrNone ls)
              | .proof => Slot.irrNone ls)
        match rules[j]? with
        | some rule =>
          let slots := pre ++ fields
          match peelLams slots.length rule.rhs with
          | some body => eval p k ls slots.reverse body
          | none => stuck (.malformed "rule arity")
        | none => stuck (.malformed "missing rule")
      | _, _ => stuck (.malformed "recursor without a kind")
  | .cases c =>
    match k with
    | 0 => .error .timeout
    | k + 1 =>
      match p.table.resolveOf c with
      | some (.case r) =>
        match p.decl? r, (p.table.recKindOf r).map (fun k => RecKind.atLevels ls k) with
        | some (.recr _ _ _ np _ _ ni ind _ _), some kind => do
          let (j, fields) ← match kind with
            | .empty => .error .trap
            | .ordinary => do
              Program.selectRule p ind np (← force p k (args.getD (np + 1 + ni) default))
            | .subsingleton _ srcs =>
              .ok (0, srcs.map fun
                | .index i => args.getD (np + 1 + i) (Slot.irrNone ls)
                | .proof => Slot.irrNone ls)
          applyAll p k (← force p k (args.getD (np + 1 + ni + 1 + j) default)) fields
        | _, _ => stuck (.malformed "case key without a recursor kind")
      | _ => stuck (.malformed "case head without an entry")
  | .prim op => do
    let vs ← forceAll p k args
    match litArgs vs with
    | some ns =>
      match op.evalLits ns with
      | some (.nat n) => .ok (.lit n)
      | some (.bool b) =>
        match (if b then p.known.boolTrue else p.known.boolFalse) with
        | some c => .ok (.con c [] [] [])
        | none => stuck (.malformed "Bool is absent")
      | none => stuck (.malformed "primitive arity")
    | none =>
      match vs.find? (fun v => !(v matches .lit _)) with
      | some v => stuck (demandCause .irrPrimArg "primitive argument" v)
      | none => stuck (.malformed "primitive arguments")

partial def force (p : Program) (k : Nat) : Slot → Out Value
  | .val v => .ok v
  | .name t ρ ls =>
    match k with
    | 0 => .error .timeout
    | k + 1 => eval p k ls ρ t

partial def forceAll (p : Program) (k : Nat) : List Slot → Out (List Value)
  | [] => .ok []
  | s :: rest => do
    let v ← force p k s
    return v :: (← forceAll p k rest)

end

def run (p : Program) (k : Nat) (root : CId) (xs : List Value) : Out Value := do
  applyAll p k (← evalConst p k [] root) (xs.map .val)

/-- The SrcEval outcome this run corresponds to (for the differential). -/
def Out.outcome : Out Value → String
  | .ok v => s!"ok {v.shape}"
  | .error .timeout => "timeout"
  | .error .trap => "trap"
  | .error (.stuck _) => "stuck"

end CompilatrixTests.Src.StuckEval
