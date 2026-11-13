module

public import IxC.Resource.Read
public import IxC.Kernel.TypeChecker

/-!
# The checker's class oracle

The checker reads its run program with this oracle: the kernel's fueled
annotation, inference and weak-head normalisation (`Ix.Kernel.whnf`,
`inferTypeCore` at the `verified` mode), asked mode-free questions only. It
answers a class only on a positive answer: `irr` where the kernel types a term
as a type, a type former or a proof, `imm`/`leaf` where it reduces a type to an
immediate or leaf type (`ImmT`, `LeafT`). Anything else is `val`, the class with
the full discipline, so a missing answer makes the checker stricter, never more
lenient. A kernel failure for lack of fuel is a decline (`decline:`).
-/

@[expose] public section

namespace IxC.Resource

open Ix.Kernel (Env Key)

/-- The oracle's limits: the kernel's fuel per question, and how deep the class
of a wrapper's field may be followed. -/
structure OracleLimits where
  fuel : Nat := 1 <<< 16
  depth : Nat := 16
  deriving Inhabited

/-- A kernel answer: `some` on success, `none` on a refusal (no positive
answer), an error for lack of fuel. -/
def kernelAnswer {α : Type} (r : Ix.Kernel.CheckM .anon α) : Except String (Option α) :=
  match r with
  | .ok a => .ok (some a)
  | .error (.internal _) => .error "decline: the kernel ran out of fuel"
  | .error _ => .ok none

def oWhnf (env : Env .anon) (lim : OracleLimits) (d : Nat) (e : KExpr) : Except String (Option KExpr) :=
  kernelAnswer (Ix.Kernel.whnf .verified env lim.fuel d e)

def oInfer (env : Env .anon) (lim : OracleLimits) (d : Nat) (e : KExpr) :
    Except String (Option KExpr) := do
  match ← kernelAnswer (Ix.Kernel.annotateCore .verified env lim.fuel d e) with
  | none => pure none
  | some e' => kernelAnswer (Ix.Kernel.inferTypeCore .verified env lim.fuel d e')

/-- The kept fields of a constructor at the type's arguments, opened: each
field's depth and type, by the oracle's classes. -/
def keptFields (env : Env .anon) (lim : OracleLimits) (irr : Nat → KExpr → Except String Bool) :
    Nat → Nat → KExpr → List Bool → Except String (Option (List (Nat × KExpr)))
  | 0, _, _, _ => pure none
  | _ + 1, _, _, [] => pure (some [])
  | n + 1, d, t, e :: er => do
    match t with
    | .forallE A B _ => do
      let rest ← keptFields env lim irr n (d + 1) (B.instantiate1 (.fvar d A)) er
      match rest with
      | none => pure none
      | some out => if e || (← irr d A) then pure (some out) else pure (some ((d, A) :: out))
    | _ => pure none

/-- **The class of the terms of type `T`**, by positive answers only. At its
depth limit the oracle declines: as landed it answered `val`, which is not
conservative, since the checker reads a positive class of a part against a
`val` whole (`caseField`: a major of class `val` is a cell) and a k-ary type
former needs depth k + 1 to be found `irr` (finding 4). -/
def oTypeClass (env : Env .anon) (sh : Key .anon → Option (List CtorShape)) (lim : OracleLimits) :
    Nat → Nat → KExpr → Except String Cls
  | 0, _, _ => throw "decline: the class oracle's depth limit"
  | n + 1, d, T => do
    let some W ← oWhnf env lim d T | return .val
    -- a type, a type former
    match W with
    | .sort _ => return .irr
    | .forallE A B _ =>
      if (← oTypeClass env sh lim n (d + 1) (B.instantiate1 (.fvar d A))) == .irr then return .irr
    | _ => pure ()
    -- a proposition; a level comparison out of fuel (`Level.isEquiv` answers `none` past
    -- `Level.defaultFuel`) is a decline, not "not a proposition" (V5: as landed `none` was taken
    -- as false, and a type of a sort that may be `Prop` went on to be classed `val` or by shape)
    let tyOfW ← oInfer env lim d W
    if let some S := tyOfW then
      let sortOfW ← oWhnf env lim d S
      if let some (.sort u) := sortOfW then
        match Ix.Kernel.Level.isEquiv u .zero with
        | some true => return .irr
        | some false => pure ()
        | none => throw "decline: the level comparison ran out of fuel"
    -- an immediate or a leaf
    match W.getAppFn with
    | .const (.role .nat) _ => return natClass
    | .const I _ =>
      let args := W.getAppArgs
      let some cs := sh I | return .val
      let irrAt (d' : Nat) (A : KExpr) : Except String Bool := do
        pure ((← oTypeClass env sh lim n d' A) == .irr)
      let mut fields : List (List (Nat × KExpr)) := []
      for c in cs do
        let some T' := instParams c.type (args.take c.nParams) | return .val
        let some ks ← keptFields env lim irrAt (c.erased.length + 1) d T' c.erased | return .val
        fields := fields ++ [ks]
      if fields.all (·.isEmpty) then return .imm
      match fields with
      | [[(d', F)]] =>
        let fc ← oTypeClass env sh lim n d' F
        if fc == .leaf then
          -- `BitVec w` at a literal width of at most 64 is an immediate
          if let .const (.role .bitVec) _ := W.getAppFn then
            if let [w] := args then
              let width ← oWhnf env lim d w
              if let some (.lit (.natVal k)) := width then
                if k ≤ 64 then return .imm
          return .leaf
        if fc == .imm then return .imm
        return .val
      | _ => return .val
    | _ => return .val

/-- The class of a term: of its type. -/
def oNodeClass (env : Env .anon) (sh : Key .anon → Option (List CtorShape)) (lim : OracleLimits)
    (d : Nat) (e : KExpr) : Except String Cls := do
  let some T ← oInfer env lim d e | return .val
  oTypeClass env sh lim lim.depth d T

/-- **The checker's class oracle** over the environment `env`. -/
def oracleClassifier (env : Env .anon) (sh : Key .anon → Option (List CtorShape))
    (lim : OracleLimits) : Classifier :=
  { type := fun d T => oTypeClass env sh lim lim.depth d T, node := oNodeClass env sh lim }

end IxC.Resource

end
