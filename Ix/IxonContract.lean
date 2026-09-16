module
public import Ix.IxonMode

/-!
# Relative locality and value contracts

Usage, ownership, and locality are independent. Local scopes and loan origins
are tracked by the checker; contracts contain no named lifetime parameters.
-/

@[expose] public section

namespace Ixon

inductive Locality where
  | unrestricted
  | local
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

instance : ReflBEq Locality where
  rfl := by intro l; cases l <;> rfl

instance : LawfulBEq Locality where
  eq_of_beq := by
    intro left right h
    cases left <;> cases right <;>
      first | rfl | exact Bool.noConfusion h

namespace Locality

def toBits : Locality → UInt8
  | .unrestricted => 0
  | .local => 1

def ofBits? : UInt8 → Option Locality
  | 0 => some .unrestricted
  | 1 => some .local
  | _ => none

@[simp] theorem ofBits?_toBits (l : Locality) : ofBits? l.toBits = some l := by
  cases l <;> rfl

end Locality

structure ValueContract where
  owned : Owned := .shared
  locality : Locality := .unrestricted
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

instance : ReflBEq ValueContract where
  rfl := by
    rintro ⟨owned, locality⟩
    cases owned <;> cases locality <;> rfl

instance : LawfulBEq ValueContract where
  eq_of_beq := by
    rintro ⟨owned, locality⟩ ⟨owned', locality'⟩ h
    cases owned <;> cases locality <;> cases owned' <;> cases locality' <;>
      first | rfl | exact Bool.noConfusion h

namespace ValueContract

def shared : ValueContract := {}
def unique : ValueContract := { owned := .unique }
def localShared : ValueContract := { locality := .local }
def localUnique : ValueContract := { owned := .unique, locality := .local }

/-- `! = 0`, unmarked = 1, `~! = 2`, `~ = 3`. -/
def toBits (v : ValueContract) : UInt8 :=
  v.owned.toBits ||| (v.locality.toBits <<< 1)

def ofBits? (bits : UInt8) : Option ValueContract := do
  if bits > 3 then none else
    return ⟨← Owned.ofBits? (bits &&& 1), ← Locality.ofBits? (bits >>> 1)⟩

@[simp] theorem ofBits?_toBits (v : ValueContract) :
    ofBits? v.toBits = some v := by
  rcases v with ⟨owned, locality⟩
  cases owned <;> cases locality <;> rfl

end ValueContract

structure BinderContract where
  uses : Uses := .many
  value : ValueContract := .shared
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

instance : ReflBEq BinderContract where
  rfl := by
    rintro ⟨uses, owned, locality⟩
    cases uses <;> cases owned <;> cases locality <;> rfl

instance : LawfulBEq BinderContract where
  eq_of_beq := by
    rintro ⟨uses, owned, locality⟩ ⟨uses', owned', locality'⟩ h
    cases uses <;> cases owned <;> cases locality <;>
      cases uses' <;> cases owned' <;> cases locality' <;>
      first | rfl | exact Bool.noConfusion h

namespace BinderContract

/-- Usage convenience constructors preserve shared, unrestricted access. -/
def erased : BinderContract := { uses := .erased }
def linear : BinderContract := { uses := .linear }
def affine : BinderContract := { uses := .affine }
def many : BinderContract := {}

def toBits (b : BinderContract) : UInt8 :=
  b.uses.toBits ||| (b.value.toBits <<< 2)

def ofBits? (bits : UInt8) : Option BinderContract := do
  if bits > 15 then none else
    return ⟨← Uses.ofBits? (bits &&& 3), ← ValueContract.ofBits? (bits >>> 2)⟩

@[simp] theorem ofBits?_toBits (b : BinderContract) :
    ofBits? b.toBits = some b := by
  rcases b with ⟨uses, owned, locality⟩
  cases uses <;> cases owned <;> cases locality <;> rfl

end BinderContract

def packAllContract (input : BinderContract) (result : ValueContract) : UInt8 :=
  input.toBits ||| (result.toBits <<< 4)

def unpackAllContract? (bits : UInt8) : Option (BinderContract × ValueContract) := do
  if bits > 63 then none else
    return (← BinderContract.ofBits? (bits &&& 15),
      ← ValueContract.ofBits? (bits >>> 4))

@[simp] theorem unpackAllContract?_packAllContract
    (input : BinderContract) (result : ValueContract) :
    unpackAllContract? (packAllContract input result) = some (input, result) := by
  rcases input with ⟨uses, owned, locality⟩
  rcases result with ⟨resultOwned, resultLocality⟩
  cases uses <;> cases owned <;> cases locality <;>
    cases resultOwned <;> cases resultLocality <;> rfl

inductive LetKind where
  | value
  | borrowShared
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

instance : ReflBEq LetKind where
  rfl := by intro k; cases k <;> rfl

instance : LawfulBEq LetKind where
  eq_of_beq := by
    intro k k' h
    cases k <;> cases k' <;> first | rfl | exact Bool.noConfusion h

structure LetContract where
  nonDep : Bool
  kind : LetKind := .value
  binder : BinderContract := .many
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace LetContract

def lean (nonDep : Bool) : LetContract := { nonDep }

def borrow (nonDep : Bool) (uses : Uses := .many) : LetContract :=
  { nonDep, kind := .borrowShared, binder := ⟨uses, .localShared⟩ }

/-- The existing let Tag4 size holds the dependency and borrow-kind flags. -/
def flags (c : LetContract) : UInt64 :=
  (if c.nonDep then 1 else 0) ||| (match c.kind with | .value => 0 | .borrowShared => 2)

def ofFlags? (flags : UInt64) (binder : BinderContract) : Option LetContract :=
  if flags > 3 then none else
    some {
      nonDep := flags &&& 1 == 1
      kind := if flags &&& 2 == 2 then .borrowShared else .value
      binder := binder
    }

@[simp] theorem ofFlags?_flags (c : LetContract) :
    ofFlags? c.flags c.binder = some c := by
  rcases c with ⟨nonDep, kind, binder⟩
  cases nonDep <;> cases kind <;> simp [ofFlags?, flags] <;> decide

end LetContract

namespace Uses

/-- Alternative paths join their possible demands. -/
def join : Uses → Uses → Uses
  | .erased, .erased => .erased
  | .linear, .linear => .linear
  | .many, _ | _, .many => .many
  | _, _ => .affine

def admits : Uses → Nat → Prop
  | .erased, n => n = 0
  | .linear, n => n = 1
  | .affine, n => n ≤ 1
  | .many, _ => True

theorem covers_sound (declared actual : Uses) (n : Nat)
    (h : declared.covers actual = true) (hn : actual.admits n) :
    declared.admits n := by
  cases declared <;> cases actual <;> simp_all [covers, admits]

theorem join_left (a b : Uses) (n : Nat) (h : a.admits n) :
    (a.join b).admits n := by
  cases a <;> cases b <;> simp_all [join, admits]

theorem join_right (a b : Uses) (n : Nat) (h : b.admits n) :
    (a.join b).admits n := by
  cases a <;> cases b <;> simp_all [join, admits]

theorem add_sound (a b : Uses) (m n : Nat)
    (ha : a.admits m) (hb : b.admits n) : (add a b).admits (m + n) := by
  cases a <;> cases b <;> simp_all [add, admits]

theorem mul_sound (a b : Uses) (m n : Nat)
    (ha : a.admits m) (hb : b.admits n) : (mul a b).admits (m * n) := by
  cases a <;> cases b <;> simp_all [mul, admits]
  simpa using Nat.mul_le_mul ha hb

end Uses
end Ixon
end
