/-
  Kernel Types: Closure-based typechecker types with compile-time metadata erasure.

  The MetaMode flag controls whether name/binder metadata is present:
  - `Expr .meta` carries full names and binder info (for debugging)
  - `Expr .anon` has Unit fields (proven no metadata leakage)
-/
import Ix.Address
import Ix.Environment
import Std.Data.HashMap

namespace Ix.Kernel

/-! ## MetaMode and MetaField -/

inductive MetaMode where | «meta» | anon

def MetaField (m : MetaMode) (α : Type) : Type :=
  match m with
  | .meta => α
  | .anon => Unit

instance {m : MetaMode} {α : Type} [Inhabited α] : Inhabited (MetaField m α) :=
  match m with
  | .meta => inferInstanceAs (Inhabited α)
  | .anon => ⟨()⟩

instance {m : MetaMode} {α : Type} [BEq α] : BEq (MetaField m α) :=
  match m with
  | .meta => inferInstanceAs (BEq α)
  | .anon => ⟨fun _ _ => true⟩

instance {m : MetaMode} {α : Type} [Repr α] : Repr (MetaField m α) :=
  match m with
  | .meta => inferInstanceAs (Repr α)
  | .anon => ⟨fun _ _ => "()".toFormat⟩

instance {m : MetaMode} {α : Type} [ToString α] : ToString (MetaField m α) :=
  match m with
  | .meta => inferInstanceAs (ToString α)
  | .anon => ⟨fun _ => "()"⟩

instance {m : MetaMode} {α : Type} [Ord α] : Ord (MetaField m α) :=
  match m with
  | .meta => inferInstanceAs (Ord α)
  | .anon => ⟨fun _ _ => .eq⟩

/-! ## MetaId

Constant identifier that pairs a name with an address in `.meta` mode,
and degenerates to plain `Address` in `.anon` mode. Used as the universal
key for kernel environment lookups. -/

def MetaId (m : MetaMode) : Type :=
  match m with
  | .meta => Ix.Name × Address
  | .anon => Address

instance : Inhabited (MetaId m) :=
  match m with
  | .meta => inferInstanceAs (Inhabited (Ix.Name × Address))
  | .anon => inferInstanceAs (Inhabited Address)

instance : BEq (MetaId m) :=
  match m with
  | .meta => inferInstanceAs (BEq (Ix.Name × Address))
  | .anon => inferInstanceAs (BEq Address)

instance : Hashable (MetaId m) :=
  match m with
  | .meta => inferInstanceAs (Hashable (Ix.Name × Address))
  | .anon => inferInstanceAs (Hashable Address)

instance : Repr (MetaId m) :=
  match m with
  | .meta => inferInstanceAs (Repr (Ix.Name × Address))
  | .anon => inferInstanceAs (Repr Address)

instance : ToString (MetaId m) :=
  match m with
  | .meta => ⟨fun (n, a) => s!"{n}@{a}"⟩
  | .anon => inferInstanceAs (ToString Address)

namespace MetaId

def addr (mid : MetaId m) : Address :=
  match m, mid with
  | .meta, (_, a) => a
  | .anon, a => a

def name (mid : MetaId m) : MetaField m Ix.Name :=
  match m, mid with
  | .meta, (n, _) => n
  | .anon, _ => ()

def mk (m : MetaMode) (addr : Address) (name : MetaField m Ix.Name) : MetaId m :=
  match m, name with
  | .meta, n => (n, addr)
  | .anon, () => addr

end MetaId

/-! ## Level -/

inductive Level (m : MetaMode) where
  | zero
  | succ   (l : Level m)
  | max    (l₁ l₂ : Level m)
  | imax   (l₁ l₂ : Level m)
  | param  (idx : Nat) (name : MetaField m Ix.Name)
  deriving Inhabited

/-- Level equality ignores param names (non-semantic metadata). -/
partial def Level.beq : Level m → Level m → Bool
  | .zero, .zero => true
  | .succ a, .succ b => Level.beq a b
  | .max a1 a2, .max b1 b2 => Level.beq a1 b1 && Level.beq a2 b2
  | .imax a1 a2, .imax b1 b2 => Level.beq a1 b1 && Level.beq a2 b2
  | .param i _, .param j _ => i == j
  | _, _ => false

instance : BEq (Level m) where beq := Level.beq

/-! ## Expr -/

inductive Expr (m : MetaMode) where
  | bvar    (idx : Nat) (name : MetaField m Ix.Name)
  | sort    (level : Level m)
  | const   (id : MetaId m) (levels : Array (Level m))
  | app     (fn arg : Expr m)
  | lam     (ty body : Expr m)
             (name : MetaField m Ix.Name) (bi : MetaField m Lean.BinderInfo)
  | forallE (ty body : Expr m)
             (name : MetaField m Ix.Name) (bi : MetaField m Lean.BinderInfo)
  | letE    (ty val body : Expr m)
             (name : MetaField m Ix.Name)
  | lit     (l : Lean.Literal)
  | proj    (typeId : MetaId m) (idx : Nat) (struct : Expr m)
  deriving Inhabited

/-- Pointer equality check for Exprs (O(1) fast path). -/
private unsafe def Expr.ptrEqUnsafe (a : @& Expr m) (b : @& Expr m) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

@[implemented_by Expr.ptrEqUnsafe]
opaque Expr.ptrEq : @& Expr m → @& Expr m → Bool

/-- Structural equality for Expr, ignoring metadata (names, binder info).
    Metadata is non-semantic in the kernel — only de Bruijn structure, addresses,
    universe levels, and literals matter. Iterates over binder body spines to
    avoid stack overflow on deeply nested let/lam/forallE chains. -/
partial def Expr.beq : Expr m → Expr m → Bool := go where
  go (a b : Expr m) : Bool := Id.run do
    if Expr.ptrEq a b then return true
    let mut ca := a; let mut cb := b
    repeat
      match ca, cb with
      | .lam ty1 body1 _ _, .lam ty2 body2 _ _ =>
        if !(go ty1 ty2) then return false
        ca := body1; cb := body2
      | .forallE ty1 body1 _ _, .forallE ty2 body2 _ _ =>
        if !(go ty1 ty2) then return false
        ca := body1; cb := body2
      | .letE ty1 val1 body1 _, .letE ty2 val2 body2 _ =>
        if !(go ty1 ty2 && go val1 val2) then return false
        ca := body1; cb := body2
      | _, _ => break
    match ca, cb with
    | .bvar i1 _, .bvar i2 _ => return i1 == i2
    | .sort l1, .sort l2 => return l1 == l2
    | .const id1 ls1, .const id2 ls2 => return id1.addr == id2.addr && ls1 == ls2
    | .app fn1 arg1, .app fn2 arg2 => return go fn1 fn2 && go arg1 arg2
    | .lit l1, .lit l2 => return l1 == l2
    | .proj id1 i1 s1, .proj id2 i2 s2 =>
      return id1.addr == id2.addr && i1 == i2 && go s1 s2
    | _, _ => return false

instance : BEq (Expr m) where beq := Expr.beq

/-! ## Pretty printing helpers -/

private def succCount : Level m → Nat → Nat × Level m
  | .succ l, n => succCount l (n + 1)
  | l, n => (n, l)

private partial def ppLevel : Level m → String
  | .zero => "0"
  | .succ l =>
    let (n, base) := succCount l 1
    match base with
    | .zero => toString n
    | _ => s!"{ppLevel base} + {n}"
  | .max l₁ l₂ => s!"max ({ppLevel l₁}) ({ppLevel l₂})"
  | .imax l₁ l₂ => s!"imax ({ppLevel l₁}) ({ppLevel l₂})"
  | .param idx name =>
    let s := s!"{name}"
    if s == "()" then s!"u_{idx}" else s

private def ppSort (l : Level m) : String :=
  match l with
  | .zero => "Prop"
  | .succ .zero => "Type"
  | .succ l' =>
    let s := ppLevel l'
    if s.any (· == ' ') then s!"Type ({s})" else s!"Type {s}"
  | _ =>
    let s := ppLevel l
    if s.any (· == ' ') then s!"Sort ({s})" else s!"Sort {s}"

private def ppBinderName (name : MetaField m Ix.Name) : String :=
  let s := s!"{name}"
  if s == "()" then "_"
  else if s.isEmpty then "???"
  else s

private def ppVarName (name : MetaField m Ix.Name) (idx : Nat) : String :=
  let s := s!"{name}"
  if s == "()" then s!"^{idx}"
  else if s.isEmpty then "???"
  else s

private def ppConstName (name : MetaField m Ix.Name) (addr : Address) : String :=
  let s := s!"{name}"
  if s == "()" then s!"#{String.ofList ((toString addr).toList.take 8)}"
  else if s.isEmpty then s!"{addr}"
  else s

/-! ## Expr smart constructors -/

namespace Expr

def mkBVar (idx : Nat) : Expr m := .bvar idx default
def mkSort (level : Level m) : Expr m := .sort level
def mkConst (id : MetaId m) (levels : Array (Level m)) : Expr m :=
  .const id levels
def mkApp (fn arg : Expr m) : Expr m := .app fn arg
def mkLam (ty body : Expr m) : Expr m := .lam ty body default default
def mkForallE (ty body : Expr m) : Expr m := .forallE ty body default default
/-- Build a nested chain of forall binders: `mkForallChain #[A, B, C] body = ∀ A, ∀ B, ∀ C, body` -/
def mkForallChain (doms : Array (Expr m)) (body : Expr m) : Expr m :=
  doms.foldr (fun dom acc => .forallE dom acc default default) body
def mkLetE (ty val body : Expr m) : Expr m := .letE ty val body default
def mkLit (l : Lean.Literal) : Expr m := .lit l
def mkProj (typeId : MetaId m) (idx : Nat) (struct : Expr m) : Expr m :=
  .proj typeId idx struct

/-! ### Predicates -/

def isSort : Expr m → Bool | sort .. => true | _ => false
def isForall : Expr m → Bool | forallE .. => true | _ => false
def isLambda : Expr m → Bool | lam .. => true | _ => false
def isApp : Expr m → Bool | app .. => true | _ => false
def isLit : Expr m → Bool | lit .. => true | _ => false
def isConst : Expr m → Bool | const .. => true | _ => false
def isBVar : Expr m → Bool | bvar .. => true | _ => false

def isConstOf (e : Expr m) (addr : Address) : Bool :=
  match e with | const id _ => id.addr == addr | _ => false

/-! ### Accessors -/

def bvarIdx! : Expr m → Nat | bvar i _ => i | _ => panic! "bvarIdx!"
def sortLevel! : Expr m → Level m | sort l => l | _ => panic! "sortLevel!"
def bindingDomain! : Expr m → Expr m
  | forallE ty _ _ _ => ty | lam ty _ _ _ => ty | _ => panic! "bindingDomain!"
def bindingBody! : Expr m → Expr m
  | forallE _ b _ _ => b | lam _ b _ _ => b | _ => panic! "bindingBody!"
def appFn! : Expr m → Expr m | app f _ => f | _ => panic! "appFn!"
def appArg! : Expr m → Expr m | app _ a => a | _ => panic! "appArg!"
def constId! : Expr m → MetaId m | const id _ => id | _ => panic! "constId!"
def constAddr! : Expr m → Address | const id _ => id.addr | _ => panic! "constAddr!"
def constLevels! : Expr m → Array (Level m) | const _ ls => ls | _ => panic! "constLevels!"
def litValue! : Expr m → Lean.Literal | lit l => l | _ => panic! "litValue!"
def projIdx! : Expr m → Nat | proj _ i _ => i | _ => panic! "projIdx!"
def projStruct! : Expr m → Expr m | proj _ _ s => s | _ => panic! "projStruct!"
def projTypeId! : Expr m → MetaId m | proj id _ _ => id | _ => panic! "projTypeId!"
def projTypeAddr! : Expr m → Address | proj id _ _ => id.addr | _ => panic! "projTypeAddr!"

/-! ### App Spine -/

def getAppFn : Expr m → Expr m
  | app f _ => getAppFn f
  | e => e

def getAppNumArgs : Expr m → Nat
  | app f _ => getAppNumArgs f + 1
  | _ => 0

partial def getAppRevArgs (e : Expr m) : Array (Expr m) :=
  go e #[]
where
  go : Expr m → Array (Expr m) → Array (Expr m)
    | app f a, acc => go f (acc.push a)
    | _, acc => acc

def getAppArgs (e : Expr m) : Array (Expr m) :=
  e.getAppRevArgs.reverse

def mkAppN (fn : Expr m) (args : Array (Expr m)) : Expr m :=
  args.foldl (fun acc a => mkApp acc a) fn

def mkAppRange (fn : Expr m) (start stop : Nat) (args : Array (Expr m)) : Expr m := Id.run do
  let mut r := fn
  for i in [start:stop] do
    r := mkApp r args[i]!
  return r

def prop : Expr m := mkSort .zero

partial def pp (atom : Bool := false) : Expr m → String
  | .bvar idx name => ppVarName name idx
  | .sort level => ppSort level
  | .const id _ => ppConstName id.name id.addr
  | .app fn arg =>
    let s := s!"{pp false fn} {pp true arg}"
    if atom then s!"({s})" else s
  | .lam ty body name _ =>
    let s := ppLam s!"({ppBinderName name} : {pp false ty})" body
    if atom then s!"({s})" else s
  | .forallE ty body name _ =>
    let s := ppPi s!"({ppBinderName name} : {pp false ty})" body
    if atom then s!"({s})" else s
  | .letE ty val body name =>
    let s := s!"let {ppBinderName name} : {pp false ty} := {pp false val}; {pp false body}"
    if atom then s!"({s})" else s
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => s!"\"{s}\""
  | .proj _ idx struct => s!"{pp true struct}.{idx}"
where
  ppLam (acc : String) : Expr m → String
    | .lam ty body name _ =>
      ppLam s!"{acc} ({ppBinderName name} : {pp false ty})" body
    | e => s!"λ {acc} => {pp false e}"
  ppPi (acc : String) : Expr m → String
    | .forallE ty body name _ =>
      ppPi s!"{acc} ({ppBinderName name} : {pp false ty})" body
    | e => s!"∀ {acc}, {pp false e}"

/-- Short constructor tag for tracing (no recursion into subterms). -/
def tag : Expr m → String
  | .bvar idx _ => s!"bvar({idx})"
  | .sort _ => "sort"
  | .const id _ => s!"const({id.name})"
  | .app .. => "app"
  | .lam .. => "lam"
  | .forallE .. => "forallE"
  | .letE .. => "letE"
  | .lit (.natVal n) => s!"natLit({n})"
  | .lit (.strVal s) => s!"strLit({s})"
  | .proj _ idx _ => s!"proj({idx})"

/-! ### Substitution helpers -/

/-- Lift free bvar indices by `n`. Under `depth` binders, bvars < depth are
    bound and stay; bvars >= depth are free and get shifted by n. -/
partial def liftBVars (e : Expr m) (n : Nat) (depth : Nat := 0) : Expr m :=
  if n == 0 then e
  else go e depth
where
  go (e : Expr m) (d : Nat) : Expr m :=
    match e with
    | .bvar idx name => if idx >= d then .bvar (idx + n) name else e
    | .app fn arg => .app (go fn d) (go arg d)
    | .lam .. => Id.run do
      let mut cur := e; let mut curD := d
      let mut acc : Array (Expr m × MetaField m Ix.Name × MetaField m Lean.BinderInfo) := #[]
      repeat
        match cur with
        | .lam ty body name bi => acc := acc.push (go ty curD, name, bi); curD := curD + 1; cur := body
        | _ => break
      let mut result := go cur curD
      for i in [:acc.size] do
        let j := acc.size - 1 - i; let (ty, name, bi) := acc[j]!
        result := .lam ty result name bi
      return result
    | .forallE .. => Id.run do
      let mut cur := e; let mut curD := d
      let mut acc : Array (Expr m × MetaField m Ix.Name × MetaField m Lean.BinderInfo) := #[]
      repeat
        match cur with
        | .forallE ty body name bi => acc := acc.push (go ty curD, name, bi); curD := curD + 1; cur := body
        | _ => break
      let mut result := go cur curD
      for i in [:acc.size] do
        let j := acc.size - 1 - i; let (ty, name, bi) := acc[j]!
        result := .forallE ty result name bi
      return result
    | .letE .. => Id.run do
      let mut cur := e; let mut curD := d
      let mut acc : Array (Expr m × Expr m × MetaField m Ix.Name) := #[]
      repeat
        match cur with
        | .letE ty val body name => acc := acc.push (go ty curD, go val curD, name); curD := curD + 1; cur := body
        | _ => break
      let mut result := go cur curD
      for i in [:acc.size] do
        let j := acc.size - 1 - i; let (ty, val, name) := acc[j]!
        result := .letE ty val result name
      return result
    | .proj typeId idx struct => .proj typeId idx (go struct d)
    | .sort .. | .const .. | .lit .. => e

/-- Bulk substitution: replace bvar i with subst[i] for i < subst.size.
    Free bvars (i >= subst.size) become bvar (i - subst.size).
    Under binders, substitution values are lifted appropriately. -/
partial def instantiate (e : Expr m) (subst : Array (Expr m)) : Expr m :=
  if subst.isEmpty then e
  else go e 0
where
  go (e : Expr m) (shift : Nat) : Expr m :=
    match e with
    | .bvar idx name =>
      if idx < shift then e  -- bound by inner binder
      else
        let realIdx := idx - shift
        if h : realIdx < subst.size then
          (subst[realIdx]).liftBVars shift
        else
          .bvar (idx - subst.size) name
    | .app fn arg => .app (go fn shift) (go arg shift)
    | .lam .. => Id.run do
      let mut cur := e; let mut curShift := shift
      let mut acc : Array (Expr m × MetaField m Ix.Name × MetaField m Lean.BinderInfo) := #[]
      repeat
        match cur with
        | .lam ty body name bi => acc := acc.push (go ty curShift, name, bi); curShift := curShift + 1; cur := body
        | _ => break
      let mut result := go cur curShift
      for i in [:acc.size] do
        let j := acc.size - 1 - i; let (ty, name, bi) := acc[j]!
        result := .lam ty result name bi
      return result
    | .forallE .. => Id.run do
      let mut cur := e; let mut curShift := shift
      let mut acc : Array (Expr m × MetaField m Ix.Name × MetaField m Lean.BinderInfo) := #[]
      repeat
        match cur with
        | .forallE ty body name bi => acc := acc.push (go ty curShift, name, bi); curShift := curShift + 1; cur := body
        | _ => break
      let mut result := go cur curShift
      for i in [:acc.size] do
        let j := acc.size - 1 - i; let (ty, name, bi) := acc[j]!
        result := .forallE ty result name bi
      return result
    | .letE .. => Id.run do
      let mut cur := e; let mut curShift := shift
      let mut acc : Array (Expr m × Expr m × MetaField m Ix.Name) := #[]
      repeat
        match cur with
        | .letE ty val body name => acc := acc.push (go ty curShift, go val curShift, name); curShift := curShift + 1; cur := body
        | _ => break
      let mut result := go cur curShift
      for i in [:acc.size] do
        let j := acc.size - 1 - i; let (ty, val, name) := acc[j]!
        result := .letE ty val result name
      return result
    | .proj typeId idx struct => .proj typeId idx (go struct shift)
    | .sort .. | .const .. | .lit .. => e

/-- Single substitution: replace bvar 0 with val. -/
def instantiate1 (body val : Expr m) : Expr m := body.instantiate #[val]

/-- Cheap beta reduction: if `e` is `(fun x₁ ... xₙ => body) a₁ ... aₘ`, and `body` is
    either a bvar or has no loose bvars, substitute without a full traversal.
    Matches lean4lean's `Expr.cheapBetaReduce`. -/
def cheapBetaReduce (e : Expr m) : Expr m := Id.run do
  let fn := e.getAppFn
  match fn with
  | .lam .. => pure ()
  | _ => return e
  let args := e.getAppArgs
  -- Walk lambda binders, counting how many args we can consume
  let mut cur := fn
  let mut i : Nat := 0
  repeat
    if i >= args.size then break
    match cur with
    | .lam _ body _ _ => cur := body; i := i + 1
    | _ => break
  -- cur is the lambda body after consuming i args; substitute
  if i == 0 then return e
  let body := cur.instantiate (args[:i].toArray.reverse)
  return body.mkAppRange i args.size args

/-- Substitute universe level params in an expression's Level nodes using a given
    level substitution function. -/
partial def instantiateLevelParamsBy (e : Expr m) (substFn : Level m → Level m) : Expr m :=
  go e
where
  go (e : Expr m) : Expr m :=
    match e with
    | .sort lvl => .sort (substFn lvl)
    | .const id ls => .const id (ls.map substFn)
    | .app fn arg => .app (go fn) (go arg)
    | .lam .. => Id.run do
      let mut cur := e
      let mut acc : Array (Expr m × MetaField m Ix.Name × MetaField m Lean.BinderInfo) := #[]
      repeat
        match cur with
        | .lam ty body name bi => acc := acc.push (go ty, name, bi); cur := body
        | _ => break
      let mut result := go cur
      for i in [:acc.size] do
        let j := acc.size - 1 - i; let (ty, name, bi) := acc[j]!
        result := .lam ty result name bi
      return result
    | .forallE .. => Id.run do
      let mut cur := e
      let mut acc : Array (Expr m × MetaField m Ix.Name × MetaField m Lean.BinderInfo) := #[]
      repeat
        match cur with
        | .forallE ty body name bi => acc := acc.push (go ty, name, bi); cur := body
        | _ => break
      let mut result := go cur
      for i in [:acc.size] do
        let j := acc.size - 1 - i; let (ty, name, bi) := acc[j]!
        result := .forallE ty result name bi
      return result
    | .letE .. => Id.run do
      let mut cur := e
      let mut acc : Array (Expr m × Expr m × MetaField m Ix.Name) := #[]
      repeat
        match cur with
        | .letE ty val body name => acc := acc.push (go ty, go val, name); cur := body
        | _ => break
      let mut result := go cur
      for i in [:acc.size] do
        let j := acc.size - 1 - i; let (ty, val, name) := acc[j]!
        result := .letE ty val result name
      return result
    | .proj typeId idx struct => .proj typeId idx (go struct)
    | .bvar .. | .lit .. => e

/-- Check if expression has any bvars with index >= depth. -/
partial def hasLooseBVarsAbove (e : Expr m) (depth : Nat) : Bool := Id.run do
  let mut cur := e; let mut curDepth := depth
  repeat
    match cur with
    | .lam ty body _ _ =>
      if hasLooseBVarsAbove ty curDepth then return true
      curDepth := curDepth + 1; cur := body
    | .forallE ty body _ _ =>
      if hasLooseBVarsAbove ty curDepth then return true
      curDepth := curDepth + 1; cur := body
    | .letE ty val body _ =>
      if hasLooseBVarsAbove ty curDepth then return true
      if hasLooseBVarsAbove val curDepth then return true
      curDepth := curDepth + 1; cur := body
    | _ => break
  match cur with
  | .bvar idx _ => return idx >= curDepth
  | .app fn arg => return hasLooseBVarsAbove fn curDepth || hasLooseBVarsAbove arg curDepth
  | .proj _ _ struct => return hasLooseBVarsAbove struct curDepth
  | _ => return false

/-- Does the expression have any loose (free) bvars? -/
def hasLooseBVars (e : Expr m) : Bool := e.hasLooseBVarsAbove 0

/-- Name of the Expr constructor (for diagnostics). -/
def ctorName : Expr m → String
  | bvar .. => "bvar" | sort .. => "sort" | const .. => "const"
  | app .. => "app" | lam .. => "lam" | forallE .. => "forallE"
  | letE .. => "letE" | lit .. => "lit" | proj .. => "proj"

/-- Accessor for binding name. -/
def bindingName! : Expr m → MetaField m Ix.Name
  | forallE _ _ n _ => n | lam _ _ n _ => n | _ => panic! "bindingName!"

/-- Accessor for binding binder info. -/
def bindingInfo! : Expr m → MetaField m Lean.BinderInfo
  | forallE _ _ _ bi => bi | lam _ _ _ bi => bi | _ => panic! "bindingInfo!"

/-- Accessor for letE name. -/
def letName! : Expr m → MetaField m Ix.Name
  | letE _ _ _ n => n | _ => panic! "letName!"

/-- Accessor for letE type. -/
def letType! : Expr m → Expr m
  | letE ty _ _ _ => ty | _ => panic! "letType!"

/-- Accessor for letE value. -/
def letValue! : Expr m → Expr m
  | letE _ v _ _ => v | _ => panic! "letValue!"

/-- Accessor for letE body. -/
def letBody! : Expr m → Expr m
  | letE _ _ b _ => b | _ => panic! "letBody!"

end Expr

/-! ## Structural ordering -/

/-- Numeric tag for Level constructors, used for ordering. -/
private def Level.tag : Level m → UInt8
  | .zero     => 0
  | .succ _   => 1
  | .max _ _  => 2
  | .imax _ _ => 3
  | .param _ _ => 4

/-- Pointer equality check for Levels (O(1) fast path). -/
private unsafe def Level.ptrEqUnsafe (a : @& Level m) (b : @& Level m) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

@[implemented_by Level.ptrEqUnsafe]
opaque Level.ptrEq : @& Level m → @& Level m → Bool

/-- Structural ordering on universe levels. Pointer-equal levels short-circuit to .eq. -/
partial def Level.compare (a b : Level m) : Ordering :=
  if Level.ptrEq a b then .eq
  else match a, b with
  | .zero, .zero => .eq
  | .succ l₁, .succ l₂ => Level.compare l₁ l₂
  | .max a₁ a₂, .max b₁ b₂ =>
    match Level.compare a₁ b₁ with | .eq => Level.compare a₂ b₂ | o => o
  | .imax a₁ a₂, .imax b₁ b₂ =>
    match Level.compare a₁ b₁ with | .eq => Level.compare a₂ b₂ | o => o
  | .param i₁ _, .param i₂ _ => Ord.compare i₁ i₂
  | _, _ => Ord.compare a.tag b.tag

private def Level.compareArray (a b : Array (Level m)) : Ordering := Id.run do
  match Ord.compare a.size b.size with
  | .eq =>
    for i in [:a.size] do
      match Level.compare a[i]! b[i]! with
      | .eq => continue
      | o => return o
    return .eq
  | o => return o

/-- Numeric tag for Expr constructors, used for ordering. -/
private def Expr.tag' : Expr m → UInt8
  | .bvar ..    => 0
  | .sort ..    => 1
  | .const ..   => 2
  | .app ..     => 3
  | .lam ..     => 4
  | .forallE .. => 5
  | .letE ..    => 6
  | .lit ..     => 7
  | .proj ..    => 8

/-- Fully iterative structural ordering on expressions using an explicit worklist.
    Pointer-equal exprs short-circuit to .eq. Never recurses — uses a stack of
    pending comparison pairs to avoid call-stack overflow on huge expressions. -/
partial def Expr.compare (a b : Expr m) : Ordering := Id.run do
  let mut stack : Array (Expr m × Expr m) := #[(a, b)]
  while h : stack.size > 0 do
    let (e1, e2) := stack[stack.size - 1]
    stack := stack.pop
    if Expr.ptrEq e1 e2 then continue
    -- Flatten binder chains
    let mut ca := e1; let mut cb := e2
    repeat
      match ca, cb with
      | .lam ty1 body1 _ _, .lam ty2 body2 _ _ =>
        stack := stack.push (ty1, ty2); ca := body1; cb := body2
      | .forallE ty1 body1 _ _, .forallE ty2 body2 _ _ =>
        stack := stack.push (ty1, ty2); ca := body1; cb := body2
      | .letE ty1 val1 body1 _, .letE ty2 val2 body2 _ =>
        stack := stack.push (ty1, ty2); stack := stack.push (val1, val2)
        ca := body1; cb := body2
      | _, _ => break
    -- Flatten app spines, then push heads back for further processing
    match ca, cb with
    | .app .., .app .. =>
      let mut f1 := ca; let mut f2 := cb
      repeat match f1, f2 with
        | .app fn1 arg1, .app fn2 arg2 =>
          stack := stack.push (arg1, arg2); f1 := fn1; f2 := fn2
        | _, _ => break
      -- Push heads back onto stack so binder/leaf handling runs on them
      stack := stack.push (f1, f2)
      continue
    | _, _ => pure ()
    -- Compare leaf nodes (non-binder, non-app)
    match ca, cb with
    | .bvar i1 _, .bvar i2 _ =>
      match Ord.compare i1 i2 with | .eq => pure () | o => return o
    | .sort l1, .sort l2 =>
      match Level.compare l1 l2 with | .eq => pure () | o => return o
    | .const id1 ls1, .const id2 ls2 =>
      match Ord.compare id1.addr id2.addr with | .eq => pure () | o => return o
      match Level.compareArray ls1 ls2 with | .eq => pure () | o => return o
    | .lit l1, .lit l2 =>
      let o := match l1, l2 with
        | .natVal n1, .natVal n2 => Ord.compare n1 n2
        | .natVal _, .strVal _ => .lt
        | .strVal _, .natVal _ => .gt
        | .strVal s1, .strVal s2 => Ord.compare s1 s2
      match o with | .eq => pure () | o => return o
    | .proj id1 i1 s1, .proj id2 i2 s2 =>
      match Ord.compare id1.addr id2.addr with | .eq => pure () | o => return o
      match Ord.compare i1 i2 with | .eq => pure () | o => return o
      stack := stack.push (s1, s2)
    | _, _ =>
      match Ord.compare ca.tag' cb.tag' with | .eq => pure () | o => return o
  return .eq

/-- Pointer-based comparison for expressions.
    Structurally-equal expressions at different addresses are considered distinct.
    This is fine for def-eq failure caches (we just get occasional misses).
    Lean 4 uses refcounting (no moving GC), so addresses are stable. -/
private unsafe def Expr.ptrCompareUnsafe (a : @& Expr m) (b : @& Expr m) : Ordering :=
  Ord.compare (ptrAddrUnsafe a) (ptrAddrUnsafe b)

@[implemented_by Expr.ptrCompareUnsafe]
opaque Expr.ptrCompare : @& Expr m → @& Expr m → Ordering

/-- Compare pairs of expressions by content (first component, then second).
    Uses structural `Expr.compare` so the failure cache works across pointer-distinct
    copies of the same expression. -/
def Expr.pairCompare (a b : Expr m × Expr m) : Ordering :=
  match Expr.compare a.1 b.1 with
  | .eq => Expr.compare a.2 b.2
  | ord => ord

/-! ## Enums -/

inductive DefinitionSafety where
  | safe | «unsafe» | «partial»
  deriving BEq, Repr, Inhabited

inductive ReducibilityHints where
  | opaque | abbrev | regular (height : UInt32)
  deriving BEq, Repr, Inhabited

namespace ReducibilityHints

def lt' : ReducibilityHints → ReducibilityHints → Bool
  | _,           .opaque     => false
  | .abbrev,     _           => false
  | .opaque,     _           => true
  | _,           .abbrev     => true
  | .regular d₁, .regular d₂ => d₁ < d₂

def isRegular : ReducibilityHints → Bool
  | .regular _ => true
  | _ => false

end ReducibilityHints

inductive QuotKind where
  | type | ctor | lift | ind
  deriving BEq, Repr, Inhabited

/-! ## ConstantInfo -/

structure ConstantVal (m : MetaMode) where
  numLevels : Nat
  type : Expr m
  name : MetaField m Ix.Name
  levelParams : MetaField m (Array Ix.Name)
  deriving Inhabited

def ConstantVal.mkUnivParams (cv : ConstantVal m) : Array (Level m) :=
  match m with
  | .meta =>
    let lps : Array Ix.Name := cv.levelParams
    Array.ofFn (n := cv.numLevels) fun i =>
      .param i.val (if h : i.val < lps.size then lps[i.val] else default)
  | .anon => Array.ofFn (n := cv.numLevels) fun i => .param i.val ()

structure AxiomVal (m : MetaMode) extends ConstantVal m where
  isUnsafe : Bool

structure DefinitionVal (m : MetaMode) extends ConstantVal m where
  value : Expr m
  hints : ReducibilityHints
  safety : DefinitionSafety
  all : Array (MetaId m) := #[]

structure TheoremVal (m : MetaMode) extends ConstantVal m where
  value : Expr m
  all : Array (MetaId m) := #[]

structure OpaqueVal (m : MetaMode) extends ConstantVal m where
  value : Expr m
  isUnsafe : Bool
  all : Array (MetaId m) := #[]

structure QuotVal (m : MetaMode) extends ConstantVal m where
  kind : QuotKind

structure InductiveVal (m : MetaMode) extends ConstantVal m where
  numParams : Nat
  numIndices : Nat
  all : Array (MetaId m) := #[]
  ctors : Array (MetaId m) := #[]
  numNested : Nat
  isRec : Bool
  isUnsafe : Bool
  isReflexive : Bool

structure ConstructorVal (m : MetaMode) extends ConstantVal m where
  induct : MetaId m := default
  cidx : Nat
  numParams : Nat
  numFields : Nat
  isUnsafe : Bool

structure RecursorRule (m : MetaMode) where
  ctor : MetaId m := default
  nfields : Nat
  rhs : Expr m

structure RecursorVal (m : MetaMode) extends ConstantVal m where
  all : Array (MetaId m) := #[]
  inductBlock : Array (MetaId m) := #[]
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : Array (RecursorRule m)
  k : Bool
  isUnsafe : Bool

inductive ConstantInfo (m : MetaMode) where
  | axiomInfo   (val : AxiomVal m)
  | defnInfo    (val : DefinitionVal m)
  | thmInfo     (val : TheoremVal m)
  | opaqueInfo  (val : OpaqueVal m)
  | quotInfo    (val : QuotVal m)
  | inductInfo  (val : InductiveVal m)
  | ctorInfo    (val : ConstructorVal m)
  | recInfo     (val : RecursorVal m)

namespace ConstantInfo

def cv : ConstantInfo m → ConstantVal m
  | axiomInfo v => v.toConstantVal
  | defnInfo v => v.toConstantVal
  | thmInfo v => v.toConstantVal
  | opaqueInfo v => v.toConstantVal
  | quotInfo v => v.toConstantVal
  | inductInfo v => v.toConstantVal
  | ctorInfo v => v.toConstantVal
  | recInfo v => v.toConstantVal

def numLevels (ci : ConstantInfo m) : Nat := ci.cv.numLevels
def type (ci : ConstantInfo m) : Expr m := ci.cv.type

def isUnsafe : ConstantInfo m → Bool
  | axiomInfo v => v.isUnsafe
  | defnInfo v => v.safety == .unsafe
  | thmInfo _ => false
  | opaqueInfo v => v.isUnsafe
  | quotInfo _ => false
  | inductInfo v => v.isUnsafe
  | ctorInfo v => v.isUnsafe
  | recInfo v => v.isUnsafe

def hasValue : ConstantInfo m → Bool
  | defnInfo .. | thmInfo .. | opaqueInfo .. => true
  | _ => false

def value? : ConstantInfo m → Option (Expr m)
  | defnInfo v => some v.value
  | thmInfo v => some v.value
  | opaqueInfo v => some v.value
  | _ => none

def hints : ConstantInfo m → ReducibilityHints
  | defnInfo v => v.hints
  | _ => .opaque

def safety : ConstantInfo m → DefinitionSafety
  | defnInfo v => v.safety
  | ci => if ci.isUnsafe then .unsafe else .safe

def all? : ConstantInfo m → Option (Array (MetaId m))
  | defnInfo v => some v.all
  | thmInfo v => some v.all
  | opaqueInfo v => some v.all
  | inductInfo v => some v.all
  | recInfo v => some v.all
  | _ => none

def kindName : ConstantInfo m → String
  | axiomInfo .. => "axiom"
  | defnInfo .. => "definition"
  | thmInfo .. => "theorem"
  | opaqueInfo .. => "opaque"
  | quotInfo .. => "quotient"
  | inductInfo .. => "inductive"
  | ctorInfo .. => "constructor"
  | recInfo .. => "recursor"

end ConstantInfo

/-! ## Kernel.Env -/

def Address.compare (a b : Address) : Ordering := Ord.compare a b

structure Env (m : MetaMode) where
  consts : Std.HashMap (MetaId m) (ConstantInfo m) := {}
  addrIndex : Std.HashMap Address (MetaId m) := {}

instance : Inhabited (Env m) where
  default := {}

instance : ForIn n (Env m) (MetaId m × ConstantInfo m) where
  forIn env init f :=
    ForIn.forIn env.consts init fun p acc => f (p.1, p.2) acc

namespace Env

def find? (env : Env m) (mid : MetaId m) : Option (ConstantInfo m) :=
  env.consts.get? mid

def findByAddr? (env : Env m) (addr : Address) : Option (ConstantInfo m) :=
  match m with
  | .anon => env.consts.get? addr
  | .meta =>
    match env.addrIndex.get? addr with
    | some mid => env.consts.get? mid
    | none => none

def get (env : Env m) (mid : MetaId m) : Except String (ConstantInfo m) :=
  match env.find? mid with
  | some ci => .ok ci
  | none => .error s!"unknown constant {mid}"

def insert (env : Env m) (mid : MetaId m) (ci : ConstantInfo m) : Env m :=
  { consts := env.consts.insert mid ci,
    addrIndex := env.addrIndex.insert mid.addr mid }

def size (env : Env m) : Nat :=
  env.consts.size

def contains (env : Env m) (mid : MetaId m) : Bool :=
  env.consts.contains mid

def containsAddr (env : Env m) (addr : Address) : Bool :=
  match m with
  | .anon => env.consts.contains addr
  | .meta => env.addrIndex.contains addr

def isStructureLike (env : Env m) (mid : MetaId m) : Bool :=
  match env.find? mid with
  | some (.inductInfo v) =>
    !v.isRec && v.numIndices == 0 && v.ctors.size == 1 &&
    match env.find? v.ctors[0]! with
    | some (.ctorInfo _) => true
    | _ => false
  | _ => false

end Env

/-! ## Primitives -/

private def addr! (s : String) : Address :=
  match Address.fromString s with
  | some a => a
  | none => panic! s!"invalid hex address: {s}"

/-- Word size mode for platform-dependent reduction.
    Controls what `System.Platform.numBits` reduces to. -/
inductive WordSize where
  | word32
  | word64
  deriving Repr, Inhabited, DecidableEq

def WordSize.numBits : WordSize → Nat
  | .word32 => 32
  | .word64 => 64

/-- Convert a dotted Lean name string like "Nat.add" to an Ix.Name. -/
private def strToIxName (s : String) : Ix.Name :=
  let parts := s.splitOn "."
  parts.foldl Ix.Name.mkStr Ix.Name.mkAnon

/-- Build a MetaId from a name string and address. In .anon mode, returns just the address. -/
def mkPrimId (m : MetaMode) (name : String) (addr : Address) : MetaId m :=
  MetaId.mk m addr (match m with | .meta => strToIxName name | .anon => ())

structure Primitives (m : MetaMode) where
  nat : MetaId m := default
  natZero : MetaId m := default
  natSucc : MetaId m := default
  natAdd : MetaId m := default
  natSub : MetaId m := default
  natMul : MetaId m := default
  natPow : MetaId m := default
  natGcd : MetaId m := default
  natMod : MetaId m := default
  natDiv : MetaId m := default
  natBeq : MetaId m := default
  natBle : MetaId m := default
  natLand : MetaId m := default
  natLor : MetaId m := default
  natXor : MetaId m := default
  natShiftLeft : MetaId m := default
  natShiftRight : MetaId m := default
  natPred : MetaId m := default
  natBitwise : MetaId m := default
  natModCoreGo : MetaId m := default
  natDivGo : MetaId m := default
  bool : MetaId m := default
  boolTrue : MetaId m := default
  boolFalse : MetaId m := default
  string : MetaId m := default
  stringMk : MetaId m := default
  char : MetaId m := default
  charMk : MetaId m := default
  stringOfList : MetaId m := default
  list : MetaId m := default
  listNil : MetaId m := default
  listCons : MetaId m := default
  eq : MetaId m := default
  eqRefl : MetaId m := default
  quotType : MetaId m := default
  quotCtor : MetaId m := default
  quotLift : MetaId m := default
  quotInd : MetaId m := default
  /-- Extra addresses for complex primitive validation (mod/div/gcd/bitwise).
      These are only needed for checking primitive definitions, not for WHNF/etc. -/
  natLE : MetaId m := default
  natDecLe : MetaId m := default
  natDecEq : MetaId m := default
  natBleRefl : MetaId m := default
  natNotBleRefl : MetaId m := default
  natBeqRefl : MetaId m := default
  natNotBeqRefl : MetaId m := default
  ite : MetaId m := default
  dite : MetaId m := default
  «not» : MetaId m := default
  accRec : MetaId m := default
  accIntro : MetaId m := default
  natLtSuccSelf : MetaId m := default
  natDivRecFuelLemma : MetaId m := default
  /-- Lean.reduceBool: opaque @[extern] constant for native_decide.
      Resolved by name during environment conversion; default = not found. -/
  reduceBool : MetaId m := default
  /-- Lean.reduceNat: opaque @[extern] constant for native nat evaluation.
      Resolved by name during environment conversion; default = not found. -/
  reduceNat : MetaId m := default
  /-- eagerReduce: identity function that triggers eager reduction mode.
      Resolved by name during environment conversion; default = not found. -/
  eagerReduce : MetaId m := default
  /-- System.Platform.numBits: platform-dependent word size.
      Resolved by name during environment conversion; default = not found. -/
  systemPlatformNumBits : MetaId m := default
  deriving Repr, Inhabited

def buildPrimitives (m : MetaMode) : Primitives m :=
  let p := mkPrimId m
  { -- Core types and constructors
    nat           := p "Nat"           (addr! "fc0e1e912f2d7f12049a5b315d76eec29562e34dc39ebca25287ae58807db137")
    natZero       := p "Nat.zero"      (addr! "fac82f0d2555d6a63e1b8a1fe8d86bd293197f39c396fdc23c1275c60f182b37")
    natSucc       := p "Nat.succ"      (addr! "7190ce56f6a2a847b944a355e3ec595a4036fb07e3c3db9d9064fc041be72b64")
    bool          := p "Bool"          (addr! "6405a455ba70c2b2179c7966c6f610bf3417bd0f3dd2ba7a522533c2cd9e1d0b")
    boolTrue      := p "Bool.true"     (addr! "420dead2168abd16a7050edfd8e17d45155237d3118782d0e68b6de87742cb8d")
    boolFalse     := p "Bool.false"    (addr! "c127f89f92e0481f7a3e0631c5615fe7f6cbbf439d5fd7eba400fb0603aedf2f")
    string        := p "String"        (addr! "591cf1c489d505d4082f2767500f123e29db5227eb1bae4721eeedd672f36190")
    stringMk      := p "String.mk"     (addr! "f055b87da4265d980cdede04ce5c7d986866e55816dc94d32a5d90e805101230")
    char          := p "Char"          (addr! "563b426b73cdf1538b767308d12d10d746e1f0b3b55047085bf690319a86f893")
    charMk        := p "Char.mk"       (addr! "7156fef44bc309789375d784e5c36e387f7119363dd9cd349226c52df43d2075")
    list          := p "List"          (addr! "abed9ff1aba4634abc0bd3af76ca544285a32dcfe43dc27b129aea8867457620")
    listNil       := p "List.nil"      (addr! "0ebe345dc46917c824b6c3f6c42b101f2ac8c0e2c99f033a0ee3c60acb9cd84d")
    listCons      := p "List.cons"     (addr! "f79842f10206598929e6ba60ce3ebaa00d11f201c99e80285f46cc0e90932832")
    -- Nat arithmetic primitives
    natAdd        := p "Nat.add"       (addr! "dcc96f3f914e363d1e906a8be4c8f49b994137bfdb077d07b6c8a4cf88a4f7bf")
    natSub        := p "Nat.sub"       (addr! "6903e9bbd169b6c5515b27b3fc0c289ba2ff8e7e0c7f984747d572de4e6a7853")
    natMul        := p "Nat.mul"       (addr! "8e641c3df8fe3878e5a219c888552802743b9251c3c37c32795f5b9b9e0818a5")
    natPow        := p "Nat.pow"       (addr! "d9be78292bb4e79c03daaaad82e756c5eb4dd5535d33b155ea69e5cbce6bc056")
    natGcd        := p "Nat.gcd"       (addr! "e8a3be39063744a43812e1f7b8785e3f5a4d5d1a408515903aa05d1724aeb465")
    natMod        := p "Nat.mod"       (addr! "14031083457b8411f655765167b1a57fcd542c621e0c391b15ff5ee716c22a67")
    natDiv        := p "Nat.div"       (addr! "863c18d3a5b100a5a5e423c20439d8ab4941818421a6bcf673445335cc559e55")
    natBeq        := p "Nat.beq"       (addr! "127a9d47a15fc2bf91a36f7c2182028857133b881554ece4df63344ec93eb2ce")
    natBle        := p "Nat.ble"       (addr! "6e4c17dc72819954d6d6afc412a3639a07aff6676b0813cdc419809cc4513df5")
    natLand       := p "Nat.land"      (addr! "e1425deee6279e2db2ff649964b1a66d4013cc08f9e968fb22cc0a64560e181a")
    natLor        := p "Nat.lor"       (addr! "3649a28f945b281bd8657e55f93ae0b8f8313488fb8669992a1ba1373cbff8f6")
    natXor        := p "Nat.xor"       (addr! "a711ef2cb4fa8221bebaa17ef8f4a965cf30678a89bc45ff18a13c902e683cc5")
    natShiftLeft  := p "Nat.shiftLeft" (addr! "16e4558f51891516843a5b30ddd9d9b405ec096d3e1c728d09ff152b345dd607")
    natShiftRight := p "Nat.shiftRight" (addr! "b9515e6c2c6b18635b1c65ebca18b5616483ebd53936f78e4ae123f6a27a089e")
    natPred       := p "Nat.pred"      (addr! "27ccc47de9587564d0c87f4b84d231c523f835af76bae5c7176f694ae78e7d65")
    natBitwise    := p "Nat.bitwise"   (addr! "f3c9111f01de3d46cb3e3f6ad2e35991c0283257e6c75ae56d2a7441e8c63e8b")
    natModCoreGo  := p "Nat.modCore.go" (addr! "7304267986fb0f6d398b45284aa6d64a953a72faa347128bf17c52d1eaf55c8e")
    natDivGo      := p "Nat.div.go"    (addr! "b3266f662eb973cafd1c5a61e0036d4f9a8f5db6dab7d9f1fe4421c4fb4e1251")
    -- String/Char definitions
    stringOfList  := p "String.ofList" (addr! "f055b87da4265d980cdede04ce5c7d986866e55816dc94d32a5d90e805101230")
    -- Eq
    eq            := p "Eq"            (addr! "c1b8d6903a3966bfedeccb63b6702fe226f893740d5c7ecf40045e7ac7635db3")
    eqRefl        := p "Eq.refl"       (addr! "154ff4baae9cd74c5ffd813f61d3afee0168827ce12fd49aad8141ebe011ae35")
    -- Quot primitives are resolved from .quot tags at conversion time
    -- Extra: mod/div/gcd validation helpers (for future complex primitive validation)
    natLE              := p "Nat.le"                (addr! "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")
    natDecLe           := p "Nat.decLe"             (addr! "fa523228c653841d5ad7f149c1587d0743f259209306458195510ed5bf1bfb14")
    natDecEq           := p "Nat.decEq"             (addr! "84817cd97c5054a512c3f0a6273c7cd81808eb2dec2916c1df737e864df6b23a")
    natBleRefl         := p "Nat.ble_refl"          (addr! "204286820d20add0c3f1bda45865297b01662876fc06c0d5c44347d5850321fe")
    natNotBleRefl      := p "Nat.not_ble_refl"      (addr! "2b2da52eecb98350a7a7c5654c0f6f07125808c5188d74f8a6196a9e1ca66c0c")
    natBeqRefl         := p "Nat.beq_refl"          (addr! "db18a07fc2d71d4f0303a17521576dc3020ab0780f435f6760cc9294804004f9")
    natNotBeqRefl      := p "Nat.not_beq_refl"      (addr! "d5ae71af8c02a6839275a2e212b7ee8e31a9ae07870ab721c4acf89644ef8128")
    ite                := p "ite"                    (addr! "4ddf0c98eee233ec746f52468f10ee754c2e05f05bdf455b1c77555a15107b8b")
    dite               := p "dite"                   (addr! "a942a2b85dd20f591163fad2e84e573476736d852ad95bcfba50a22736cd3c79")
    «not»              := p "Not"                    (addr! "236b6e6720110bc351a8ad6cbd22437c3e0ef014981a37d45ba36805c81364f3")
    accRec             := p "Acc.rec"                (addr! "23104251c3618f32eb77bec895e99f54edd97feed7ac27f3248da378d05e3289")
    accIntro           := p "Acc.intro"              (addr! "7ff829fa1057b6589e25bac87f500ad979f9b93f77d47ca9bde6b539a8842d87")
    natLtSuccSelf      := p "Nat.lt_succ_self"       (addr! "2d2e51025b6e0306fdc45b79492becea407881d5137573d23ff144fc38a29519")
    natDivRecFuelLemma := p "Nat.div_rec_fuel_lemma" (addr! "026b6f9a63f5fe7ac20b41b81e4180d95768ca78d7d1962aa8280be6b27362b7")
  }

end Ix.Kernel
