module

public import Ix.Kernel.Monad

/-!
Dependency ordering inside an anonymous or named definition block. A safe
definition's type and value may use an earlier member, but may not obtain
their justification from a cycle of pending safe definitions. Inductive
and recursor blocks have separate validators for their recursive structure.

This check concerns the local declaration/block boundary. Ordering external
dependencies is a separate obligation of environment and claim admission.
-/

public section
@[expose] section

namespace Ix.Kernel

/-- The fields consulted when ordering safe definitions. -/
structure SafeDefinition (m : Mode) where
  id : KId m
  ty : KExpr m
  val : KExpr m

namespace SafeDefinition

def ofConst? (id : KId m) : KConst m → Option (SafeDefinition m)
  | .defn (safety := .safe) (ty := ty) (val := val) .. => some ⟨id, ty, val⟩
  | _ => none

/-- Projection heads count as dependencies, as do ordinary constant nodes. -/
def mentions (definition : SafeDefinition m) (id : KId m) : Bool :=
  exprMentionsAddr definition.ty id.addr || exprMentionsAddr definition.val id.addr

def ready (pending : List (SafeDefinition m)) (definition : SafeDefinition m) : Bool :=
  pending.all fun dependency => !definition.mentions dependency.id

/-- Simultaneously remove every member whose dependencies have already been
removed. The fuel bounds rejected cyclic inputs as well as accepted ones. -/
def order? : Nat → List (SafeDefinition m) → Option (List (SafeDefinition m))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, pending@(_ :: _) =>
      let ready := pending.filter (ready pending)
      if ready.isEmpty then none
      else
        let rest := pending.filter fun definition => !definition.ready pending
        (order? fuel rest).map (ready ++ ·)

def acyclic (pending : List (SafeDefinition m)) : Bool :=
  (order? pending.length pending).isSome

end SafeDefinition

namespace KEnv

/-- Read the complete pending safe subset. Missing or non-definition members
fail closed; the block classifier normally rejects these first. -/
def safeDefinitions? (env : KEnv m) : List (KId m) → Option (List (SafeDefinition m))
  | [] => some []
  | id :: rest => do
      let declaration ← env.consts[id]?
      let .defn .. := declaration | none
      let tail ← env.safeDefinitions? rest
      match SafeDefinition.ofConst? id declaration with
      | some definition => some (definition :: tail)
      | none => some tail

def definitionBlockAcyclic (env : KEnv m) (members : Array (KId m)) : Bool :=
  match env.safeDefinitions? members.toList with
  | some pending => SafeDefinition.acyclic pending
  | none => false

end KEnv

end Ix.Kernel

end
end
