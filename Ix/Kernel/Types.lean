/-
  Kernel Types: Closure-based typechecker types with compile-time metadata erasure.

  The MetaMode flag controls whether name/binder metadata is present:
  - `Expr .meta` carries full names and binder info (for debugging)
  - `Expr .anon` has Unit fields (proven no metadata leakage)
-/
import Ix.Address
import Ix.Environment

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

/-! ## Level -/

inductive Level (m : MetaMode) where
  | zero
  | succ   (l : Level m)
  | max    (l₁ l₂ : Level m)
  | imax   (l₁ l₂ : Level m)
  | param  (idx : Nat) (name : MetaField m Ix.Name)
  deriving Inhabited, BEq

/-! ## Expr -/

inductive Expr (m : MetaMode) where
  | bvar    (idx : Nat) (name : MetaField m Ix.Name)
  | sort    (level : Level m)
  | const   (addr : Address) (levels : Array (Level m))
             (name : MetaField m Ix.Name)
  | app     (fn arg : Expr m)
  | lam     (ty body : Expr m)
             (name : MetaField m Ix.Name) (bi : MetaField m Lean.BinderInfo)
  | forallE (ty body : Expr m)
             (name : MetaField m Ix.Name) (bi : MetaField m Lean.BinderInfo)
  | letE    (ty val body : Expr m)
             (name : MetaField m Ix.Name)
  | lit     (l : Lean.Literal)
  | proj    (typeAddr : Address) (idx : Nat) (struct : Expr m)
             (typeName : MetaField m Ix.Name)
  deriving Inhabited

/-- Pointer equality check for Exprs (O(1) fast path). -/
private unsafe def Expr.ptrEqUnsafe (a : @& Expr m) (b : @& Expr m) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

@[implemented_by Expr.ptrEqUnsafe]
opaque Expr.ptrEq : @& Expr m → @& Expr m → Bool

/-- Structural equality for Expr, iterating over binder body spines to avoid
    stack overflow on deeply nested let/lam/forallE chains. -/
partial def Expr.beq : Expr m → Expr m → Bool := go where
  go (a b : Expr m) : Bool := Id.run do
    if Expr.ptrEq a b then return true
    let mut ca := a; let mut cb := b
    repeat
      match ca, cb with
      | .lam ty1 body1 n1 bi1, .lam ty2 body2 n2 bi2 =>
        if !(go ty1 ty2 && n1 == n2 && bi1 == bi2) then return false
        ca := body1; cb := body2
      | .forallE ty1 body1 n1 bi1, .forallE ty2 body2 n2 bi2 =>
        if !(go ty1 ty2 && n1 == n2 && bi1 == bi2) then return false
        ca := body1; cb := body2
      | .letE ty1 val1 body1 n1, .letE ty2 val2 body2 n2 =>
        if !(go ty1 ty2 && go val1 val2 && n1 == n2) then return false
        ca := body1; cb := body2
      | _, _ => break
    match ca, cb with
    | .bvar i1 n1, .bvar i2 n2 => return i1 == i2 && n1 == n2
    | .sort l1, .sort l2 => return l1 == l2
    | .const a1 ls1 n1, .const a2 ls2 n2 => return a1 == a2 && ls1 == ls2 && n1 == n2
    | .app fn1 arg1, .app fn2 arg2 => return go fn1 fn2 && go arg1 arg2
    | .lit l1, .lit l2 => return l1 == l2
    | .proj a1 i1 s1 n1, .proj a2 i2 s2 n2 =>
      return a1 == a2 && i1 == i2 && go s1 s2 && n1 == n2
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
def mkConst (addr : Address) (levels : Array (Level m)) : Expr m :=
  .const addr levels default
def mkApp (fn arg : Expr m) : Expr m := .app fn arg
def mkLam (ty body : Expr m) : Expr m := .lam ty body default default
def mkForallE (ty body : Expr m) : Expr m := .forallE ty body default default
def mkLetE (ty val body : Expr m) : Expr m := .letE ty val body default
def mkLit (l : Lean.Literal) : Expr m := .lit l
def mkProj (typeAddr : Address) (idx : Nat) (struct : Expr m) : Expr m :=
  .proj typeAddr idx struct default

/-! ### Predicates -/

def isSort : Expr m → Bool | sort .. => true | _ => false
def isForall : Expr m → Bool | forallE .. => true | _ => false
def isLambda : Expr m → Bool | lam .. => true | _ => false
def isApp : Expr m → Bool | app .. => true | _ => false
def isLit : Expr m → Bool | lit .. => true | _ => false
def isConst : Expr m → Bool | const .. => true | _ => false
def isBVar : Expr m → Bool | bvar .. => true | _ => false

def isConstOf (e : Expr m) (addr : Address) : Bool :=
  match e with | const a _ _ => a == addr | _ => false

/-! ### Accessors -/

def bvarIdx! : Expr m → Nat | bvar i _ => i | _ => panic! "bvarIdx!"
def sortLevel! : Expr m → Level m | sort l => l | _ => panic! "sortLevel!"
def bindingDomain! : Expr m → Expr m
  | forallE ty _ _ _ => ty | lam ty _ _ _ => ty | _ => panic! "bindingDomain!"
def bindingBody! : Expr m → Expr m
  | forallE _ b _ _ => b | lam _ b _ _ => b | _ => panic! "bindingBody!"
def appFn! : Expr m → Expr m | app f _ => f | _ => panic! "appFn!"
def appArg! : Expr m → Expr m | app _ a => a | _ => panic! "appArg!"
def constAddr! : Expr m → Address | const a _ _ => a | _ => panic! "constAddr!"
def constLevels! : Expr m → Array (Level m) | const _ ls _ => ls | _ => panic! "constLevels!"
def litValue! : Expr m → Lean.Literal | lit l => l | _ => panic! "litValue!"
def projIdx! : Expr m → Nat | proj _ i _ _ => i | _ => panic! "projIdx!"
def projStruct! : Expr m → Expr m | proj _ _ s _ => s | _ => panic! "projStruct!"
def projTypeAddr! : Expr m → Address | proj a _ _ _ => a | _ => panic! "projTypeAddr!"

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
  | .const addr _ name => ppConstName name addr
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
  | .proj _ idx struct _ => s!"{pp true struct}.{idx}"
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
  | .const _ _ name => s!"const({name})"
  | .app .. => "app"
  | .lam .. => "lam"
  | .forallE .. => "forallE"
  | .letE .. => "letE"
  | .lit (.natVal n) => s!"natLit({n})"
  | .lit (.strVal s) => s!"strLit({s})"
  | .proj _ idx _ _ => s!"proj({idx})"

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
    | .proj typeAddr idx struct typeName => .proj typeAddr idx (go struct d) typeName
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
    | .proj typeAddr idx struct typeName => .proj typeAddr idx (go struct shift) typeName
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
    | .const addr ls name => .const addr (ls.map substFn) name
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
    | .proj typeAddr idx struct typeName => .proj typeAddr idx (go struct) typeName
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
  | .proj _ _ struct _ => return hasLooseBVarsAbove struct curDepth
  | _ => return false

/-- Does the expression have any loose (free) bvars? -/
def hasLooseBVars (e : Expr m) : Bool := e.hasLooseBVarsAbove 0

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
    | .const a1 ls1 _, .const a2 ls2 _ =>
      match Ord.compare a1 a2 with | .eq => pure () | o => return o
      match Level.compareArray ls1 ls2 with | .eq => pure () | o => return o
    | .lit l1, .lit l2 =>
      let o := match l1, l2 with
        | .natVal n1, .natVal n2 => Ord.compare n1 n2
        | .natVal _, .strVal _ => .lt
        | .strVal _, .natVal _ => .gt
        | .strVal s1, .strVal s2 => Ord.compare s1 s2
      match o with | .eq => pure () | o => return o
    | .proj a1 i1 s1 _, .proj a2 i2 s2 _ =>
      match Ord.compare a1 a2 with | .eq => pure () | o => return o
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
  all : Array Address
  allNames : MetaField m (Array Ix.Name) := default

structure TheoremVal (m : MetaMode) extends ConstantVal m where
  value : Expr m
  all : Array Address
  allNames : MetaField m (Array Ix.Name) := default

structure OpaqueVal (m : MetaMode) extends ConstantVal m where
  value : Expr m
  isUnsafe : Bool
  all : Array Address
  allNames : MetaField m (Array Ix.Name) := default

structure QuotVal (m : MetaMode) extends ConstantVal m where
  kind : QuotKind

structure InductiveVal (m : MetaMode) extends ConstantVal m where
  numParams : Nat
  numIndices : Nat
  all : Array Address
  ctors : Array Address
  allNames : MetaField m (Array Ix.Name) := default
  ctorNames : MetaField m (Array Ix.Name) := default
  numNested : Nat
  isRec : Bool
  isUnsafe : Bool
  isReflexive : Bool

structure ConstructorVal (m : MetaMode) extends ConstantVal m where
  induct : Address
  inductName : MetaField m Ix.Name := default
  cidx : Nat
  numParams : Nat
  numFields : Nat
  isUnsafe : Bool

structure RecursorRule (m : MetaMode) where
  ctor : Address
  ctorName : MetaField m Ix.Name := default
  nfields : Nat
  rhs : Expr m

structure RecursorVal (m : MetaMode) extends ConstantVal m where
  all : Array Address
  allNames : MetaField m (Array Ix.Name) := default
  inductBlock : Array Address := #[]
  inductNames : MetaField m (Array (Array Ix.Name)) := default
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
  | _ => .safe

def all? : ConstantInfo m → Option (Array Address)
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

structure EnvId (m : MetaMode) where
  addr : Address
  name : MetaField m Ix.Name

instance : Inhabited (EnvId m) where
  default := ⟨default, default⟩

instance : BEq (EnvId m) where
  beq a b := a.addr == b.addr && a.name == b.name

def EnvId.compare (a b : EnvId m) : Ordering :=
  match Address.compare a.addr b.addr with
  | .eq => Ord.compare a.name b.name
  | ord => ord

structure Env (m : MetaMode) where
  entries : Std.TreeMap (EnvId m) (ConstantInfo m) EnvId.compare
  addrIndex : Std.TreeMap Address (EnvId m) Address.compare

instance : Inhabited (Env m) where
  default := { entries := .empty, addrIndex := .empty }

instance : ForIn n (Env m) (Address × ConstantInfo m) where
  forIn env init f :=
    ForIn.forIn env.entries init fun p acc => f (p.1.addr, p.2) acc

namespace Env

def find? (env : Env m) (addr : Address) : Option (ConstantInfo m) :=
  match env.addrIndex.get? addr with
  | some id => env.entries.get? id
  | none => none

def findByEnvId (env : Env m) (id : EnvId m) : Option (ConstantInfo m) :=
  env.entries.get? id

def get (env : Env m) (addr : Address) : Except String (ConstantInfo m) :=
  match env.find? addr with
  | some ci => .ok ci
  | none => .error s!"unknown constant {addr}"

def insert (env : Env m) (addr : Address) (ci : ConstantInfo m) : Env m :=
  let id : EnvId m := ⟨addr, ci.cv.name⟩
  let entries := env.entries.insert id ci
  let addrIndex := match env.addrIndex.get? addr with
    | some _ => env.addrIndex
    | none => env.addrIndex.insert addr id
  { entries, addrIndex }

def add (env : Env m) (addr : Address) (ci : ConstantInfo m) : Env m :=
  env.insert addr ci

def size (env : Env m) : Nat :=
  env.addrIndex.size

def contains (env : Env m) (addr : Address) : Bool :=
  env.addrIndex.get? addr |>.isSome

def isStructureLike (env : Env m) (addr : Address) : Bool :=
  match env.find? addr with
  | some (.inductInfo v) =>
    !v.isRec && v.numIndices == 0 && v.ctors.size == 1 &&
    match env.find? v.ctors[0]! with
    | some (.ctorInfo cv) => cv.numFields > 0
    | _ => false
  | _ => false

end Env

/-! ## Primitives -/

private def addr! (s : String) : Address :=
  match Address.fromString s with
  | some a => a
  | none => panic! s!"invalid hex address: {s}"

structure Primitives where
  nat : Address := default
  natZero : Address := default
  natSucc : Address := default
  natAdd : Address := default
  natSub : Address := default
  natMul : Address := default
  natPow : Address := default
  natGcd : Address := default
  natMod : Address := default
  natDiv : Address := default
  natBeq : Address := default
  natBle : Address := default
  natLand : Address := default
  natLor : Address := default
  natXor : Address := default
  natShiftLeft : Address := default
  natShiftRight : Address := default
  bool : Address := default
  boolTrue : Address := default
  boolFalse : Address := default
  string : Address := default
  stringMk : Address := default
  char : Address := default
  charMk : Address := default
  list : Address := default
  listNil : Address := default
  listCons : Address := default
  quotType : Address := default
  quotCtor : Address := default
  quotLift : Address := default
  quotInd : Address := default
  deriving Repr, Inhabited

def buildPrimitives : Primitives :=
  { nat           := addr! "fc0e1e912f2d7f12049a5b315d76eec29562e34dc39ebca25287ae58807db137"
    natZero       := addr! "fac82f0d2555d6a63e1b8a1fe8d86bd293197f39c396fdc23c1275c60f182b37"
    natSucc       := addr! "7190ce56f6a2a847b944a355e3ec595a4036fb07e3c3db9d9064fc041be72b64"
    natAdd        := addr! "dcc96f3f914e363d1e906a8be4c8f49b994137bfdb077d07b6c8a4cf88a4f7bf"
    natSub        := addr! "6903e9bbd169b6c5515b27b3fc0c289ba2ff8e7e0c7f984747d572de4e6a7853"
    natMul        := addr! "8e641c3df8fe3878e5a219c888552802743b9251c3c37c32795f5b9b9e0818a5"
    natPow        := addr! "d9be78292bb4e79c03daaaad82e756c5eb4dd5535d33b155ea69e5cbce6bc056"
    natGcd        := addr! "e8a3be39063744a43812e1f7b8785e3f5a4d5d1a408515903aa05d1724aeb465"
    natMod        := addr! "14031083457b8411f655765167b1a57fcd542c621e0c391b15ff5ee716c22a67"
    natDiv        := addr! "863c18d3a5b100a5a5e423c20439d8ab4941818421a6bcf673445335cc559e55"
    natBeq        := addr! "127a9d47a15fc2bf91a36f7c2182028857133b881554ece4df63344ec93eb2ce"
    natBle        := addr! "6e4c17dc72819954d6d6afc412a3639a07aff6676b0813cdc419809cc4513df5"
    natLand       := addr! "e1425deee6279e2db2ff649964b1a66d4013cc08f9e968fb22cc0a64560e181a"
    natLor        := addr! "3649a28f945b281bd8657e55f93ae0b8f8313488fb8669992a1ba1373cbff8f6"
    natXor        := addr! "a711ef2cb4fa8221bebaa17ef8f4a965cf30678a89bc45ff18a13c902e683cc5"
    natShiftLeft  := addr! "16e4558f51891516843a5b30ddd9d9b405ec096d3e1c728d09ff152b345dd607"
    natShiftRight := addr! "b9515e6c2c6b18635b1c65ebca18b5616483ebd53936f78e4ae123f6a27a089e"
    bool          := addr! "6405a455ba70c2b2179c7966c6f610bf3417bd0f3dd2ba7a522533c2cd9e1d0b"
    boolTrue      := addr! "420dead2168abd16a7050edfd8e17d45155237d3118782d0e68b6de87742cb8d"
    boolFalse     := addr! "c127f89f92e0481f7a3e0631c5615fe7f6cbbf439d5fd7eba400fb0603aedf2f"
    string        := addr! "591cf1c489d505d4082f2767500f123e29db5227eb1bae4721eeedd672f36190"
    stringMk      := addr! "f055b87da4265d980cdede04ce5c7d986866e55816dc94d32a5d90e805101230"
    char          := addr! "563b426b73cdf1538b767308d12d10d746e1f0b3b55047085bf690319a86f893"
    charMk        := addr! "7156fef44bc309789375d784e5c36e387f7119363dd9cd349226c52df43d2075"
    list          := addr! "abed9ff1aba4634abc0bd3af76ca544285a32dcfe43dc27b129aea8867457620"
    listNil       := addr! "0ebe345dc46917c824b6c3f6c42b101f2ac8c0e2c99f033a0ee3c60acb9cd84d"
    listCons      := addr! "f79842f10206598929e6ba60ce3ebaa00d11f201c99e80285f46cc0e90932832"
    -- Quot primitives need to be computed; use default until wired up
  }

end Ix.Kernel
