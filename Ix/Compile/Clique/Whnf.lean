/-
  Ix.Compile.Clique.Whnf: a small weak-head reducer, used by the structural
  transport to type a path into a `below` dictionary (design document §5.3).

  Lean finds the dictionary entry of a recursive call with `searchPProd`
  (`Elab/PreDefinition/Structural/BRecOn.lean`): it unfolds the `below` type
  (`whnf`) and walks its `PProd`/`And` nodes until it meets `C arg`, where `C`
  is a canary standing for the packed motive. The transport needs the same
  split of a path into the part that walks the inductive's `below` structure
  (independent of the clique) and the part inside the packed motive
  (re-associated). It replays Lean's walk: the packed motives are replaced by
  fresh free variables (the canaries), and the `below` type is reduced by
  δ (definitions), β, ζ, ι (a recursor on a constructor application, Nat
  literals as `zero`/`succ`) and projection of a constructor. Only `below`
  types are ever reduced, and only to weak head normal form.

  Total: every step consumes `fuel`; exhaustion is reported, never hidden.
-/
module
public import Ix.Compile.Clique.Basic
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN instantiateRev substLevels stripMdata)

def nNatZero : Name := leanName ``Nat.zero
def nNatSucc : Name := leanName ``Nat.succ

/-- `natLit k ↦ Nat.zero` / `Nat.succ (natLit (k - 1))`. -/
def natLitToCtor : Expr → Option Expr
  | .lit (.natVal 0) _ => some (Expr.mkConst nNatZero #[])
  | .lit (.natVal (k + 1)) _ => some (Expr.mkApp (Expr.mkConst nNatSucc #[]) (Expr.mkLit (.natVal k)))
  | _ => none

/-- Beta-reduce a head `λ` against the arguments. -/
def betaApp (f : Expr) (args : Array Expr) : Expr := Id.run do
  let mut f := f
  let mut i := 0
  let mut acc : Array Expr := #[]
  for a in args do
    match stripMdata f with
    | .lam _ _ b _ _ => acc := acc.push a; f := b; i := i + 1
    | _ => break
  -- `instantiateRev` takes the innermost binder's value first
  mkAppN (instantiateRev f acc.reverse) (args.extract i args.size)

mutual
/-- One weak-head step, or `none` when `e` is in weak head normal form. -/
def whnfStep (const? : Name → Option ConstantInfo) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, e =>
    let e := stripMdata e
    let (h, args) := getAppFnArgs e
    match stripMdata h with
    | .lam .. => if args.isEmpty then none else some (betaApp (stripMdata h) args)
    | .letE _ _ v b _ _ => some (mkAppN (instantiateRev b #[v]) args)
    | .const c us _ =>
      match const? c with
      | some (.defnInfo d) => some (mkAppN (substLevels d.cnst.levelParams us d.value) args)
      | some (.recInfo r) =>
        let majorIdx := r.numParams + r.numMotives + r.numMinors + r.numIndices
        if h : majorIdx < args.size then
          let major := whnf const? fuel args[majorIdx]
          let major := (natLitToCtor major).getD major
          match getAppFnArgs major with
          | (.const k _ _, kargs) =>
            match r.rules.find? (·.ctor == k), const? k with
            | some rule, some (.ctorInfo cv) =>
              let rhs := substLevels r.cnst.levelParams us rule.rhs
              let pre := args.extract 0 (r.numParams + r.numMotives + r.numMinors)
              let fields := kargs.extract cv.numParams kargs.size
              some (mkAppN (mkAppN rhs (pre ++ fields)) (args.extract (majorIdx + 1) args.size))
            | _, _ => none
          | _ => none
        else none
      | _ => none
    | .proj _ i s _ =>
      let s' := whnf const? fuel s
      match getAppFnArgs s' with
      | (.const k _ _, kargs) =>
        match const? k with
        | some (.ctorInfo cv) =>
          match kargs[cv.numParams + i]? with
          | some fld => some (mkAppN fld args)
          | none => none
        | _ => none
      | _ => none
    | _ => none

/-- Weak head normal form, within `fuel` steps. -/
def whnf (const? : Name → Option ConstantInfo) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    match whnfStep const? fuel e with
    | some e' => whnf const? fuel e'
    | none => e
end

def whnfFuel : Nat := 256

end Ix.Compile.Clique

end
