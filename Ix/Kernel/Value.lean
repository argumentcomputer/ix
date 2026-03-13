/-
  Kernel2 Value: The semantic domain for a Krivine-style NbE kernel.

  Val represents values in the NbE kernel. Key design:
  - Closures capture (body : Expr, env : Array Val) for O(1) beta reduction
  - Free variables use de Bruijn LEVELS (not indices) — no shifting under binders
  - Spine arguments and proj structs are LAZY (Nat → forced on demand via ST.Ref)
  - Constructors are Val.ctor with cached metadata (cidx, numParams, etc.) for O(1) detection
  - Let-expressions are zeta-reduced eagerly (no VLet)
  - Delta unfolding is single-step (Krivine machine semantics)
-/
import Ix.Kernel.Types

namespace Ix.Kernel

-- Abbreviations to avoid Lean.Expr / Lean.ConstantInfo shadowing
abbrev KExpr (m : Ix.Kernel.MetaMode) := Ix.Kernel.Expr m
abbrev KLevel (m : Ix.Kernel.MetaMode) := Ix.Kernel.Level m
abbrev KMetaField (m : Ix.Kernel.MetaMode) (α : Type) := Ix.Kernel.MetaField m α
abbrev KMetaId (m : Ix.Kernel.MetaMode) := Ix.Kernel.MetaId m
abbrev KConstantInfo (m : Ix.Kernel.MetaMode) := Ix.Kernel.ConstantInfo m
abbrev KEnv (m : Ix.Kernel.MetaMode) := Ix.Kernel.Env m
abbrev KPrimitives (m : Ix.Kernel.MetaMode) := Ix.Kernel.Primitives m
abbrev KReducibilityHints := Ix.Kernel.ReducibilityHints
abbrev KDefinitionSafety := Ix.Kernel.DefinitionSafety

/-! ## Thunk identifier

Spine arguments and projection structs are lazy. A Nat indexes into an
external thunk table (Array of ST.Ref) managed by TypecheckM. Val itself
contains no ST.Ref, avoiding positivity issues. -/

/-! ## Core value types

Val and Head are mutually referential. Closure fields are inlined into lam/pi.
Spine and proj-struct positions hold Nats for call-by-need evaluation. -/

mutual

inductive Head (m : Ix.Kernel.MetaMode) : Type where
  | fvar  (level : Nat) (type : Val m)
  | const (id : KMetaId m) (levels : Array (KLevel m))

inductive Val (m : Ix.Kernel.MetaMode) : Type where
  | lam     (name : KMetaField m Ix.Name)
            (bi : KMetaField m Lean.BinderInfo)
            (dom : Val m) (body : KExpr m) (env : Array (Val m))
  | pi      (name : KMetaField m Ix.Name)
            (bi : KMetaField m Lean.BinderInfo)
            (dom : Val m) (body : KExpr m) (env : Array (Val m))
  | sort    (level : KLevel m)
  | neutral (head : Head m) (spine : Array Nat)
  | ctor    (id : KMetaId m) (levels : Array (KLevel m))
            (cidx : Nat) (numParams : Nat) (numFields : Nat)
            (inductId : KMetaId m) (spine : Array Nat)
  | lit     (l : Lean.Literal)
  | proj    (typeId : KMetaId m) (idx : Nat) (struct : Nat)
            (spine : Array Nat)

end

instance : Inhabited (Head m) where
  default := .const default #[]

instance : Inhabited (Val m) where
  default := .sort .zero

/-! ## Closure wrapper -/

/-- A closure captures an expression body and its evaluation environment.
    When applied to a value v: eval body (env.push v). -/
structure Closure (m : Ix.Kernel.MetaMode) where
  body : KExpr m
  env  : Array (Val m)

instance : Inhabited (Closure m) where
  default := ⟨default, #[]⟩

/-- Extract the closure from a lam value. -/
def Val.lamClosure : Val m → Closure m
  | .lam _ _ _ body env => ⟨body, env⟩
  | _ => default

/-- Extract the closure from a pi value. -/
def Val.piClosure : Val m → Closure m
  | .pi _ _ _ body env => ⟨body, env⟩
  | _ => default

/-! ## Smart constructors -/

namespace Val

def mkConst (id : KMetaId m) (levels : Array (KLevel m)) : Val m :=
  .neutral (.const id levels) #[]

def mkFVar (level : Nat) (type : Val m) : Val m :=
  .neutral (.fvar level type) #[]

def constId? : Val m → Option (KMetaId m)
  | .neutral (.const id _) _ => some id
  | .ctor id .. => some id
  | _ => none

def constAddr? : Val m → Option Address
  | .neutral (.const id _) _ => some id.addr
  | .ctor id .. => some id.addr
  | _ => none

def isSort : Val m → Bool
  | .sort _ => true
  | _ => false

def sortLevel! : Val m → KLevel m
  | .sort l => l
  | _ => panic! "Val.sortLevel!: not a sort"

def isPi : Val m → Bool
  | .pi .. => true
  | _ => false

def natVal? : Val m → Option Nat
  | .lit (.natVal n) => some n
  | _ => none

def strVal? : Val m → Option String
  | .lit (.strVal s) => some s
  | _ => none

/-! ### Spine / head accessors for lazy delta -/

def headLevels! : Val m → Array (KLevel m)
  | .neutral (.const _ ls) _ => ls
  | .ctor _ ls .. => ls
  | _ => #[]

def spine! : Val m → Array Nat
  | .neutral _ sp => sp
  | .ctor _ _ _ _ _ _ sp => sp
  | _ => #[]

end Val

/-! ## Helpers for lazy delta -/

def sameHeadVal (t s : Val m) : Bool :=
  match t, s with
  | .neutral (.const a _) _, .neutral (.const b _) _ => a.addr == b.addr
  | .ctor a .., .ctor b .. => a.addr == b.addr
  | _, _ => false

/-! ## Pretty printing -/

namespace Val

partial def pp : Val m → String
  | .lam _ _ dom _ env => s!"(λ _ : {pp dom} => <closure {env.size}>)"
  | .pi _ _ dom _ env => s!"(Π _ : {pp dom} → <closure {env.size}>)"
  | .sort _lvl => "Sort"
  | .neutral (.fvar level _) spine =>
    let base := s!"fvar.{level}"
    if spine.isEmpty then base else s!"({base} <{spine.size} thunks>)"
  | .neutral (.const id _) spine =>
    let n := toString id.name
    let base := if n == "()" then s!"#{String.ofList ((toString id.addr).toList.take 8)}"
                else n
    if spine.isEmpty then base else s!"({base} <{spine.size} thunks>)"
  | .ctor id _ cidx _ _ _ spine =>
    let n := toString id.name
    let base := if n == "()" then s!"ctor#{String.ofList ((toString id.addr).toList.take 8)}[{cidx}]"
                else s!"ctor:{n}[{cidx}]"
    if spine.isEmpty then base else s!"({base} <{spine.size} thunks>)"
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => s!"\"{s}\""
  | .proj _ idx _struct spine =>
    let base := s!"<thunk>.{idx}"
    if spine.isEmpty then base else s!"({base} <{spine.size} thunks>)"

instance : ToString (Val m) where
  toString := Val.pp

end Val

end Ix.Kernel
