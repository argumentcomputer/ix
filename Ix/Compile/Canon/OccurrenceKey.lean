module
public import Ix.Environment
public import Ix.SemanticContract
public import Std.Data.HashMap.Lemmas
public section

namespace Ix.Compile.Canon

/-! Structural occurrence keys contain no cached name, level or expression
hash. Source-mode keys retain every source field; canonical-mode callers
first apply `addrKey`, including its universe normalization and erasures. -/

inductive KeyData where
  | nil
  | pair (head tail : KeyData)
  | tag (value : Nat)
  | nat (value : Nat)
  | int (value : _root_.Int)
  | string (value : String)
  | name (value : Lean.Name)
  deriving DecidableEq, Inhabited

def KeyData.node (tag : Nat) (children : List KeyData) : KeyData :=
  .pair (.tag tag) (children.foldr .pair .nil)

def keyName : Ix.Name → Lean.Name := Ix.SemanticContract.toLeanName

def keySubstring (s : Ix.Substring) : KeyData :=
  .node 0 [.string s.str, .nat s.startPos, .nat s.stopPos]

def keySourceInfo : Ix.SourceInfo → KeyData
  | .original a i b j => .node 0 [keySubstring a, .nat i, keySubstring b, .nat j]
  | .synthetic a b c => .node 1 [.nat a, .nat b, .nat (if c then 1 else 0)]
  | .none => .node 2 []

def keyPreresolved : Ix.SyntaxPreresolved → KeyData
  | .namespace n => .node 0 [.name (keyName n)]
  | .decl n aliases => .node 1 [.name (keyName n), .node 0 (aliases.toList.map .string)]

def keySyntax (s : Ix.Syntax) : KeyData :=
  match s with
  | .missing => .node 0 []
  | .node info kind args => .node 1
      [keySourceInfo info, .name (keyName kind),
       .node 0 (args.attach.toList.map fun a => keySyntax a.1)]
  | .atom info value => .node 2 [keySourceInfo info, .string value]
  | .ident info raw value pres => .node 3
      [keySourceInfo info, keySubstring raw, .name (keyName value),
       .node 0 (pres.toList.map keyPreresolved)]
termination_by sizeOf s
decreasing_by
  simp_wf
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem a.property) (by omega)

def keyDataValue : Ix.DataValue → KeyData
  | .ofString s => .node 0 [.string s]
  | .ofBool b => .node 1 [.nat (if b then 1 else 0)]
  | .ofName n => .node 2 [.name (keyName n)]
  | .ofNat n => .node 3 [.nat n]
  | .ofInt (.ofNat n) => .node 4 [.int (.ofNat n)]
  | .ofInt (.negSucc n) => .node 4 [.int (.negSucc n)]
  | .ofSyntax s => .node 5 [keySyntax s]

inductive KeyLevel where
  | zero
  | succ (u : KeyLevel)
  | max (u v : KeyLevel)
  | imax (u v : KeyLevel)
  | param (name : Lean.Name)
  | mvar (name : Lean.Name)
  deriving DecidableEq, Inhabited

def keyLevelShape : Ix.Level → KeyLevel
  | .zero _ => .zero
  | .succ u _ => .succ (keyLevelShape u)
  | .max u v _ => .max (keyLevelShape u) (keyLevelShape v)
  | .imax u v _ => .imax (keyLevelShape u) (keyLevelShape v)
  | .param n _ => .param (keyName n)
  | .mvar n _ => .mvar (keyName n)

/-- Reference identity in a nested occurrence. Addresses never share a
constructor with a source/generated spelling, including literal `#<hex>` names. -/
inductive OccurrenceRef where
  | named (name : Lean.Name)
  | external (address : Address)
  deriving DecidableEq, BEq, Inhabited

inductive OccurrenceKey where
  | bvar (index : Nat)
  | fvar (name : Lean.Name)
  | mvar (name : Lean.Name)
  | sort (level : KeyLevel)
  | const (ref : OccurrenceRef) (levels : List KeyLevel)
  | app (fn arg : OccurrenceKey)
  | lam (name : Lean.Name) (type body : OccurrenceKey) (info : UInt8)
  | forallE (name : Lean.Name) (type body : OccurrenceKey) (info : UInt8)
  | letE (name : Lean.Name) (type value body : OccurrenceKey) (nonDep : Bool)
  | natLit (value : Nat)
  | strLit (value : String)
  | mdata (data : List (Lean.Name × KeyData)) (body : OccurrenceKey)
  | proj (ref : OccurrenceRef) (index : Nat) (body : OccurrenceKey)
  deriving DecidableEq, Inhabited

instance : BEq OccurrenceKey := ⟨fun a b => decide (a = b)⟩

def occurrenceKey : Ix.Expr → OccurrenceKey
  | .bvar i _ => .bvar i
  | .fvar n _ => .fvar (keyName n)
  | .mvar n _ => .mvar (keyName n)
  | .sort u _ => .sort (keyLevelShape u)
  | .const n us _ => .const (.named (keyName n)) (us.toList.map keyLevelShape)
  | .app f a _ => .app (occurrenceKey f) (occurrenceKey a)
  | .lam n t b bi _ => .lam (keyName n) (occurrenceKey t) (occurrenceKey b) (Ix.Expr.binderInfoTag bi)
  | .forallE n t b bi _ => .forallE (keyName n) (occurrenceKey t) (occurrenceKey b) (Ix.Expr.binderInfoTag bi)
  | .letE n t v b nd _ => .letE (keyName n) (occurrenceKey t) (occurrenceKey v) (occurrenceKey b) nd
  | .lit (.natVal n) _ => .natLit n
  | .lit (.strVal s) _ => .strLit s
  | .mdata md e _ => .mdata (md.toList.map fun (n,v) => (keyName n, keyDataValue v)) (occurrenceKey e)
  | .proj n i e _ => .proj (.named (keyName n)) i (occurrenceKey e)

/-- A structural specification key with an arbitrary cache hint. The hint
is deliberately excluded from equality and all refinement assumptions. -/
structure OccurrenceInput where
  key : OccurrenceKey
  bucket : UInt64

def sourceOccurrence (e : Ix.Expr) : OccurrenceInput := ⟨occurrenceKey e, hash e⟩

instance : Coe Ix.Expr OccurrenceInput := ⟨sourceOccurrence⟩

def occurrenceLookup : List (OccurrenceKey × Ix.Name) → OccurrenceKey → Option Ix.Name
  | [], _ => none
  | (key, value) :: rest, sought =>
      if key = sought then some value else occurrenceLookup rest sought

/-- The specification is `entries`. Every cached candidate carries the
structural lookup invariant; arbitrary hash collisions are permitted. -/
structure OccurrenceTable where
  entries : List (OccurrenceKey × Ix.Name) := []
  cache : Std.HashMap UInt64 (OccurrenceKey × Ix.Name) := {}
  valid : ∀ (bucket : UInt64) (pair : OccurrenceKey × Ix.Name), cache[bucket]? = some pair →
    occurrenceLookup entries pair.1 = some pair.2

instance : EmptyCollection OccurrenceTable :=
  ⟨{ entries := [], cache := {}, valid := by simp }⟩
instance : Inhabited OccurrenceTable := ⟨{}⟩

def OccurrenceTable.get? (table : OccurrenceTable) (input : OccurrenceInput) : Option Ix.Name :=
  occurrenceLookup table.entries input.key

/-- The hash only selects a candidate. A structural match confirms the hit;
every miss, including a collision, falls back to the structural specification. -/
def OccurrenceTable.getFast? (table : OccurrenceTable) (input : OccurrenceInput) : Option Ix.Name :=
  match table.cache[input.bucket]? with
  | some (stored, value) =>
      if stored = input.key then some value else occurrenceLookup table.entries input.key
  | none => occurrenceLookup table.entries input.key

theorem OccurrenceTable.getFast?_eq (table : OccurrenceTable) (input : OccurrenceInput) :
    table.getFast? input = table.get? input := by
  unfold getFast? get?
  split
  · rename_i stored value hit
    split
    · rename_i same
      exact (same ▸ table.valid input.bucket (stored, value) hit).symm
    · rfl
  · rfl

@[csimp] theorem OccurrenceTable.get?_eq_fast :
    @OccurrenceTable.get? = @OccurrenceTable.getFast? := by
  funext table input
  exact (table.getFast?_eq input).symm

/-- A changed or colliding advisory hash cannot change a lookup result. -/
theorem OccurrenceTable.get?_bucket (table : OccurrenceTable) (key : OccurrenceKey)
    (a b : UInt64) : table.get? ⟨key, a⟩ = table.get? ⟨key, b⟩ := by
  simp only [get?]

theorem OccurrenceRef.named_ne_external (n : Lean.Name) (a : Address) :
    OccurrenceRef.named n ≠ .external a := by intro h; cases h

theorem OccurrenceKey.const_tag_disjoint (n : Lean.Name) (a : Address)
    (us vs : List KeyLevel) :
    OccurrenceKey.const (.named n) us ≠ .const (.external a) vs := by intro h; cases h

theorem OccurrenceKey.proj_tag_disjoint (n : Lean.Name) (a : Address)
    (i j : Nat) (x y : OccurrenceKey) :
    OccurrenceKey.proj (.named n) i x ≠ .proj (.external a) j y := by intro h; cases h

def OccurrenceTable.contains (table : OccurrenceTable) (input : OccurrenceInput) : Bool :=
  (table.get? input).isSome

/-- Insert only the first discovery of a structural key. -/
def OccurrenceTable.insert (table : OccurrenceTable) (input : OccurrenceInput) (value : Ix.Name) :
    OccurrenceTable :=
  if absent : table.get? input = none then
    { entries := (input.key, value) :: table.entries
      cache := table.cache.insert input.bucket (input.key, value)
      valid := by
        intro bucket pair hit
        by_cases same : input.bucket = bucket
        · subst bucket
          simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hit
          subst pair
          simp [occurrenceLookup]
        · have oldHit : table.cache[bucket]? = some pair := by
            simpa [Std.HashMap.getElem?_insert, same] using hit
          have old := table.valid bucket pair oldHit
          have different : input.key ≠ pair.1 := by
            intro equal
            have contradiction := absent
            unfold get? at contradiction
            rw [equal, old] at contradiction
            contradiction
          simp [occurrenceLookup, different, old] }
  else table

end Ix.Compile.Canon
