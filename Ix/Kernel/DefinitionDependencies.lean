module

public import Ix.Kernel.Monad

/-!
Safe definitions must have an acyclic graph of definition dependencies.
Type checking a reference only checks its declared type; it cannot justify a
cycle such as `theorem loop : P := loop`. This traversal follows constants in
both types and values, including references hidden under binders and lets.
Inductives, constructors, recursors, and axioms are terminal declarations;
their own admission rules justify their interpretations separately.
-/

public section
@[expose] section

namespace Ix.Kernel

/-- Shared Lean/Rust bound for the dependency walk. Exhaustion rejects the
declaration; it never turns an incomplete traversal into success. -/
def maxDefinitionDependencySteps : Nat := 1_000_000

/-- Constant references in a list of expression roots. The worklist avoids
host-stack recursion, and address memoization visits shared syntax once.
Projection heads are references as well as their major arguments. -/
def definitionRefs (roots : List (KExpr m)) : Array (KId m) :=
  go roots {} #[]
where
  go (stack : List (KExpr m)) (seen : Std.HashSet Address)
      (refs : Array (KId m)) : Array (KId m) :=
    match stack with
    | [] => refs
    | expr :: stack =>
      if seen.contains expr.addr then go stack seen refs
      else
        let seen := seen.insert expr.addr
        match expr with
        | .const id .. => go stack seen (refs.push id)
        | .app fn arg _ => go (fn :: arg :: stack) seen refs
        | .lam _ _ domain body _ | .all _ _ domain body _ =>
            go (domain :: body :: stack) seen refs
        | .letE _ domain value body _ _ => go (domain :: value :: body :: stack) seen refs
        | .prj id _ major _ => go (major :: stack) seen (refs.push id)
        | _ => go stack seen refs
  termination_by exprWorkSize stack
  decreasing_by
    all_goals simp [exprWorkSize, KExpr.treeSize, KExpr.treeSize_pos] <;> omega

/-- Only definitions add dependency edges. Recursive inductive and recursor
blocks are checked by their dedicated validators. -/
def KConst.definitionDependencies : KConst m → Array (KId m)
  | .defn (ty := type) (val := value) .. => definitionRefs [type, value]
  | _ => #[]

inductive DefinitionDependencyTask (m : Mode) where
  | enter (id : KId m)
  | finish (id : KId m) (declaration : KConst m)

/-- The completed declarations are in dependency order. This certificate is
local to one check and is discarded on error; it is not a semantic cache. -/
structure DefinitionDependencyState (m : Mode) where
  pending : List (DefinitionDependencyTask m)
  active : Std.HashSet Address := {}
  finished : Std.HashSet Address := {}
  ordered : Array (KId m × KConst m) := #[]

namespace RecM

/-- One depth-first dependency step, including the actual lazy lookup. A
completed node is published only after every direct dependency is complete. -/
def definitionDependencyStep (walk : DefinitionDependencyState m) :
    RecM m (BoundedStep (DefinitionDependencyState m) (Array (KId m × KConst m))) := do
  match walk.pending with
  | [] => return .done walk.ordered
  | .enter id :: pending =>
    if walk.finished.contains id.addr then return .next { walk with pending }
    if walk.active.contains id.addr then
      throw (.other s!"cyclic definition dependency at {id}")
    let declaration ← TcM.getConst id
    let dependencies := declaration.definitionDependencies.toList.map DefinitionDependencyTask.enter
    return .next { walk with
      pending := dependencies ++ .finish id declaration :: pending
      active := walk.active.insert id.addr }
  | .finish id declaration :: pending =>
    if walk.finished.contains id.addr ||
        !(declaration.definitionDependencies.all fun dependency =>
          walk.finished.contains dependency.addr) then
      throw (.other s!"incomplete definition dependencies at {id}")
    return .next { walk with
      pending, active := walk.active.erase id.addr, finished := walk.finished.insert id.addr
      ordered := walk.ordered.push (id, declaration) }

/-- Return the concrete dependency order produced by the bounded traversal. -/
def definitionDependencyOrder (roots : Array (KId m)) : RecM m (Array (KId m × KConst m)) :=
  runBounded definitionDependencyStep maxDefinitionDependencySteps
    { pending := roots.toList.map DefinitionDependencyTask.enter }

/-- Safe declarations cannot use circular definitions to justify a type or
value. Partial and unsafe declarations retain their separate safety policy. -/
def checkDefinitionDependencies (declaration : KConst m) : RecM m Unit := do
  match declaration with
  | .defn (safety := .safe) .. =>
    let _ ← definitionDependencyOrder declaration.definitionDependencies
    return ()
  | _ => return ()

end RecM
end Ix.Kernel

end
end
