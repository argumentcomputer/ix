module
public import Ix.Compile.Canon.OccurrenceKey
public section

namespace Ix.Compile.Canon

/-- Structural lookup of a generated name; cached name digests are absent
from the decision. The original name is retained for metadata/iteration. -/
def nameLookup {α : Type} : List (Ix.Name × α) → Lean.Name → Option α
  | [], _ => none
  | (name, value) :: rest, sought =>
      if keyName name = sought then some value else nameLookup rest sought

structure NameTable (α : Type) where
  entries : List (Ix.Name × α) := []
  cache : Std.HashMap UInt64 (Ix.Name × α) := {}
  valid : ∀ (bucket : UInt64) (pair : Ix.Name × α), cache[bucket]? = some pair →
    nameLookup entries (keyName pair.1) = some pair.2

instance {α : Type} : EmptyCollection (NameTable α) :=
  ⟨{ entries := [], cache := {}, valid := by simp }⟩
instance {α : Type} : Inhabited (NameTable α) := ⟨{}⟩

namespace NameTable
variable {α : Type}

def get? (table : NameTable α) (name : Ix.Name) : Option α :=
  nameLookup table.entries (keyName name)

/-- A hash selects a candidate, whose complete name structure confirms it.
A collision or a differently cached spelling falls back to the core. -/
def getFast? (table : NameTable α) (name : Ix.Name) : Option α :=
  match table.cache[hash name]? with
  | some (stored, value) =>
      if keyName stored = keyName name then some value else table.get? name
  | none => table.get? name

theorem getFast?_eq (table : NameTable α) (name : Ix.Name) :
    table.getFast? name = table.get? name := by
  unfold getFast? get?
  split
  · rename_i stored value hit
    split
    · rename_i same
      exact (same ▸ table.valid (hash name) (stored, value) hit).symm
    · rfl
  · rfl

@[csimp] theorem get?_eq_fast : @get? = @getFast? := by
  funext α table name
  exact (table.getFast?_eq name).symm

def contains (table : NameTable α) (name : Ix.Name) : Bool :=
  (table.get? name).isSome

def isEmpty (table : NameTable α) : Bool := table.entries.isEmpty

/-- Overwrite follows ordinary map semantics. Updating an existing
structural key clears stale candidates; first insertion retains the cache. -/
def insert (table : NameTable α) (name : Ix.Name) (value : α) : NameTable α :=
  if absent : table.get? name = none then
    { entries := (name, value) :: table.entries
      cache := table.cache.insert (hash name) (name, value)
      valid := by
        intro bucket pair hit
        by_cases same : hash name = bucket
        · subst bucket
          simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hit
          subst pair
          simp [nameLookup]
        · have oldHit : table.cache[bucket]? = some pair := by
            simpa [Std.HashMap.getElem?_insert, same] using hit
          have old := table.valid bucket pair oldHit
          have different : keyName name ≠ keyName pair.1 := by
            intro equal
            have contradiction := absent
            unfold get? at contradiction
            rw [equal, old] at contradiction
            contradiction
          simp [nameLookup, different, old] }
  else
    { entries := (name, value) :: table.entries.filter
        (fun entry => decide (keyName entry.1 ≠ keyName name))
      cache := {}
      valid := by simp }

def toList (table : NameTable α) : List (Ix.Name × α) := table.entries
def toArray (table : NameTable α) : Array (Ix.Name × α) := table.entries.toArray
def size (table : NameTable α) : Nat := table.entries.length

def fold {β : Type v} (f : β → Ix.Name → α → β) (init : β) (table : NameTable α) : β :=
  table.entries.foldl (fun acc (name, value) => f acc name value) init

instance {m : Type → Type v} [Monad m] : ForIn m (NameTable α) (Ix.Name × α) where
  forIn table init f := forIn table.entries init f

end NameTable

abbrev NameSet := NameTable Unit

/-- Rename generated constant and projection names through the structural
table. This is the total helper for the auxiliary-order consumer. -/
def NameTable.replaceConstNames (table : NameTable Ix.Name) (e : Ix.Expr) : Ix.Expr :=
  if table.isEmpty then e else go e
where
  go : Ix.Expr → Ix.Expr
    | .const n us _ => Ix.Expr.mkConst ((table.get? n).getD n) us
    | .app f a _ => Ix.Expr.mkApp (go f) (go a)
    | .lam n t b bi _ => Ix.Expr.mkLam n (go t) (go b) bi
    | .forallE n t b bi _ => Ix.Expr.mkForallE n (go t) (go b) bi
    | .letE n t v b nd _ => Ix.Expr.mkLetE n (go t) (go v) (go b) nd
    | .proj n i b _ => Ix.Expr.mkProj ((table.get? n).getD n) i (go b)
    | .mdata md b _ => Ix.Expr.mkMData md (go b)
    | e => e

/-- The generated-name membership walk. Other callers retain their
existing input-name set API. No expression-hash memo is involved. -/
def mentionsName (present : Ix.Name → Bool) : Ix.Expr → Bool
  | .const n _ _ => present n
  | .app f a _ => mentionsName present f || mentionsName present a
  | .lam _ t b _ _ | .forallE _ t b _ _ =>
      mentionsName present t || mentionsName present b
  | .letE _ t v b _ _ =>
      mentionsName present t || mentionsName present v || mentionsName present b
  | .proj n _ s _ => present n || mentionsName present s
  | .mdata _ s _ => mentionsName present s
  | _ => false

end Ix.Compile.Canon
