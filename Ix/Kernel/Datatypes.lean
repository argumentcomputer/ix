/-
  Kernel Datatypes: Value, Neutral, SusValue, TypedExpr, Env, TypedConst.

  Closure-based semantic domain for NbE typechecking.
  Parameterized over MetaMode for compile-time metadata erasure.
-/
import Ix.Kernel.Types

namespace Ix.Kernel

/-! ## TypeInfo -/

inductive TypeInfo (m : MetaMode) where
  | unit | proof | none
  | sort : Level m → TypeInfo m
  deriving Inhabited

/-! ## AddInfo -/

structure AddInfo (Info Body : Type) where
  info : Info
  body : Body
  deriving Inhabited

/-! ## Forward declarations for mutual types -/

abbrev TypedExpr (m : MetaMode) := AddInfo (TypeInfo m) (Expr m)

/-! ## Value / Neutral / SusValue -/

mutual
  inductive Value (m : MetaMode) where
    | sort : Level m → Value m
    | app  : Neutral m → List (AddInfo (TypeInfo m) (Thunk (Value m))) → List (TypeInfo m) → Value m
    | lam  : AddInfo (TypeInfo m) (Thunk (Value m)) → TypedExpr m → ValEnv m
             → MetaField m Ix.Name → MetaField m Lean.BinderInfo → Value m
    | pi   : AddInfo (TypeInfo m) (Thunk (Value m)) → TypedExpr m → ValEnv m
             → MetaField m Ix.Name → MetaField m Lean.BinderInfo → Value m
    | lit  : Lean.Literal → Value m
    | exception : String → Value m

  inductive Neutral (m : MetaMode) where
    | fvar  : Nat → MetaField m Ix.Name → Neutral m
    | const : Address → Array (Level m) → MetaField m Ix.Name → Neutral m
    | proj  : Address → Nat → AddInfo (TypeInfo m) (Value m) → MetaField m Ix.Name → Neutral m

  inductive ValEnv (m : MetaMode) where
    | mk : List (AddInfo (TypeInfo m) (Thunk (Value m))) → List (Level m) → ValEnv m
end

instance : Inhabited (Value m) where default := .exception "uninit"
instance : Inhabited (Neutral m) where default := .fvar 0 default
instance : Inhabited (ValEnv m) where default := .mk [] []

abbrev SusValue (m : MetaMode) := AddInfo (TypeInfo m) (Thunk (Value m))

instance : Inhabited (SusValue m) where
  default := .mk default { fn := fun _ => default }

/-! ## TypedConst -/

inductive TypedConst (m : MetaMode) where
  | «axiom»     : (type : TypedExpr m) → TypedConst m
  | «theorem»   : (type value : TypedExpr m) → TypedConst m
  | «inductive» : (type : TypedExpr m) → (struct : Bool) → TypedConst m
  | «opaque»    : (type value : TypedExpr m) → TypedConst m
  | definition  : (type value : TypedExpr m) → (part : Bool) → TypedConst m
  | constructor : (type : TypedExpr m) → (idx fields : Nat) → TypedConst m
  | recursor    : (type : TypedExpr m) → (params motives minors indices : Nat) → (k : Bool)
                  → (indAddr : Address) → (rules : Array (Nat × TypedExpr m)) → TypedConst m
  | quotient    : (type : TypedExpr m) → (kind : QuotKind) → TypedConst m
  deriving Inhabited

def TypedConst.type : TypedConst m → TypedExpr m
  | «axiom»     type ..
  | «theorem»   type ..
  | «inductive» type ..
  | «opaque»    type ..
  | definition  type ..
  | constructor type ..
  | recursor    type ..
  | quotient    type .. => type

/-! ## Accessors -/

namespace AddInfo

def expr (t : TypedExpr m) : Expr m := t.body
def thunk (sus : SusValue m) : Thunk (Value m) := sus.body
def get (sus : SusValue m) : Value m := sus.body.get
def getTyped (sus : SusValue m) : AddInfo (TypeInfo m) (Value m) := ⟨sus.info, sus.body.get⟩
def value (val : AddInfo (TypeInfo m) (Value m)) : Value m := val.body
def sus (val : AddInfo (TypeInfo m) (Value m)) : SusValue m := ⟨val.info, val.body⟩

end AddInfo

/-! ## TypedExpr helpers -/

partial def TypedExpr.toImplicitLambda : TypedExpr m → TypedExpr m
  | .mk _ (.lam _ body _ _) => toImplicitLambda ⟨default, body⟩
  | x => x

/-! ## Value helpers -/

def Value.neu (n : Neutral m) : Value m := .app n [] []

def Value.ctorName : Value m → String
  | .sort      .. => "sort"
  | .app       .. => "app"
  | .lam       .. => "lam"
  | .pi        .. => "pi"
  | .lit       .. => "lit"
  | .exception .. => "exception"

def Neutral.summary : Neutral m → String
  | .fvar idx name => s!"fvar({name}, {idx})"
  | .const addr _ name => s!"const({name}, {addr})"
  | .proj _ idx _ name => s!"proj({name}, {idx})"

def Value.summary : Value m → String
  | .sort _ => "Sort"
  | .app neu args _ => s!"{neu.summary} applied to {args.length} args"
  | .lam .. => "lam"
  | .pi .. => "Pi"
  | .lit (.natVal n) => s!"natLit({n})"
  | .lit (.strVal s) => s!"strLit(\"{s}\")"
  | .exception e => s!"exception({e})"

def TypeInfo.pp : TypeInfo m → String
  | .unit => ".unit"
  | .proof => ".proof"
  | .none => ".none"
  | .sort _ => ".sort"

private def listGetOpt (l : List α) (i : Nat) : Option α :=
  match l, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n+1 => listGetOpt xs n

/-- Deep structural dump (one level into args) for debugging stuck terms. -/
def Value.dump : Value m → String
  | .sort _ => "Sort"
  | .app neu args infos =>
    let argStrs := args.zipIdx.map fun (a, i) =>
      let info := match listGetOpt infos i with | some ti => TypeInfo.pp ti | none => "?"
      s!"  [{i}] info={info} val={a.get.summary}"
    s!"{neu.summary} applied to {args.length} args:\n" ++ String.intercalate "\n" argStrs
  | .lam dom _ _ _ _ => s!"lam(dom={dom.get.summary}, info={dom.info.pp})"
  | .pi dom _ _ _ _ => s!"Pi(dom={dom.get.summary}, info={dom.info.pp})"
  | .lit (.natVal n) => s!"natLit({n})"
  | .lit (.strVal s) => s!"strLit(\"{s}\")"
  | .exception e => s!"exception({e})"

/-! ## ValEnv helpers -/

namespace ValEnv

def exprs : ValEnv m → List (SusValue m)
  | .mk es _ => es

def univs : ValEnv m → List (Level m)
  | .mk _ us => us

def extendWith (env : ValEnv m) (thunk : SusValue m) : ValEnv m :=
  .mk (thunk :: env.exprs) env.univs

def withExprs (env : ValEnv m) (exprs : List (SusValue m)) : ValEnv m :=
  .mk exprs env.univs

end ValEnv

/-! ## Smart constructors -/

def mkConst (addr : Address) (univs : Array (Level m)) (name : MetaField m Ix.Name := default) : Value m :=
  .neu (.const addr univs name)

def mkSusVar (info : TypeInfo m) (idx : Nat) (name : MetaField m Ix.Name := default) : SusValue m :=
  .mk info (.mk fun _ => .neu (.fvar idx name))

end Ix.Kernel
