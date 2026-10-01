module

public import Std.Data.HashMap
/- `withPtrEq` is `public` but not `@[expose]`, and its whole point here
is that it is *definitionally* `k ()` — which is what
`Name.beqPtr_eq` proves.  `import all` makes that body visible **in
this module only**; that theorem is the public relay, so no importer
needs it, and the executed `Name.beq` stays the plain
`decide (· = ·)` that the kernel can still reduce. -/
import all Init.Util

/-!
# Hierarchical names

`ConLeche.Name`, the checker's own mirror of `Lean.Name` (cached hash in
a `@[computed_field]`, pointer-and-hash-guarded equality substituted by
`@[csimp]`).  Split out of `ConLeche/Kernel/Expr.lean` on 2026-09-06 so
that `ConLeche/Kernel/PropWhen.lean` — which needs names and nothing
else — can sit *below* the expression type it annotates.
-/

@[expose] public section

namespace ConLeche

/-- Hierarchical names, same shape as `Lean.Name` — including the
cached hash, which lives in a `@[computed_field]` exactly as
`Lean.Name`'s does (`@[computed_field, inline] hash : Name → UInt64`,
`Init/Prelude.lean`; the C runtime stores it in the object header and
reads it with `lean_name_hash_ptr`).  Logically the field is a
*function of the value*, so it is invisible to every statement:
`DecidableEq` is still the derived structural equality, and the field
only spares the `Hashable` instance a walk (task #176 P3). -/
inductive Name where
  | anonymous
  | str (pre : Name) (s : String)
  | num (pre : Name) (n : Nat)
with
  /-- The cached hash of a name (official: the `uint64` in the `Name`
  object's header). -/
  @[computed_field] hashData : Name → UInt64
    | .anonymous => 1723
    | .str p s => mixHash (mixHash 1 p.hashData) (hash s)
    | .num p n => mixHash (mixHash 2 p.hashData) (hash n)
deriving DecidableEq, Repr, Inhabited

/-- Hashing a name is an `O(1)` field read, not a structural walk with
a byte-wise `String` hash per limb. -/
instance : Hashable Name := ⟨Name.hashData⟩

/-- Name equality in the official kernel's shape (task #176 P1):
**pointer** (`lean_name_eq`'s `if (n1 == n2) return true`), then the
**cached hash** (`lean_name_hash_ptr`), then the structural walk —
`_tmp/lean4-master-kernel/lean4_object.cpp:2762`.  This is the
*implementation* of `Name.beq`; `Name.beqPtr_eq` proves the two guards
redundant. -/
@[inline] def Name.beqPtr (a b : Name) : Bool :=
  withPtrEq a b (fun _ => a.hashData == b.hashData && decide (a = b))
    (fun h => by subst h; simp)

/-- Both guards are redundant: `withPtrEq a b k h` is *defined* as
`k ()`, and `hashData` is a function of the value, so a hash mismatch
**is** an inequality. -/
theorem Name.beqPtr_eq (a b : Name) : Name.beqPtr a b = decide (a = b) := by
  show (a.hashData == b.hashData && decide (a = b)) = decide (a = b)
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- The executed name equality.  Definitionally `decide (a = b)` — so
the kernel, `by decide` and `#guard` still see plain structural
equality — with `beqPtr` substituted by the compiler on the strength
of the `@[csimp]` equation below. -/
def Name.beq (a b : Name) : Bool := decide (a = b)

/-- **The compiler substitution, on a kernel-checked equality.**
`@[csimp]` (not `@[implemented_by]`) is what replaces `Name.beq` by
`Name.beqPtr` in compiled code — *"do not use `implemented_by`.  If
you can prove them equal, use `csimp`"* (user ruling, 2026-09-05).
Nothing here is taken on faith: `withPtrEq a b k h` is *defined* as
`k ()` and its obligation is discharged at `beqPtr`, and `hashData` is
a function of the value, so the hash guard cannot reject an equal
pair.  `Expr.beq` is substituted the same way (`Expr.beq_eq_beqMemo`),
so no equality in the tree is an escape. -/
@[csimp] theorem Name.beq_eq_beqPtr : @Name.beq = @Name.beqPtr := by
  funext a b; exact (Name.beqPtr_eq a b).symm

instance : BEq Name := ⟨Name.beq⟩

/-- `Name.beq` is lawful — it *is* `decide (· = ·)`. -/
instance : LawfulBEq Name where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Name.beq]

namespace Name

/-- Conversion from `Lean.Name` (dropping macro scopes is the caller's duty). -/
def ofLeanName : Lean.Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (ofLeanName p) s
  | .num p n => .num (ofLeanName p) n

protected def toString : Name → String
  | .anonymous => "[anonymous]"
  | .str .anonymous s => s
  | .str p s => p.toString ++ "." ++ s
  | .num .anonymous n => toString n
  | .num p n => p.toString ++ "." ++ toString n

instance : ToString Name := ⟨Name.toString⟩

end Name

end ConLeche
