import IxCC.Src.Value

/-! # Global and constructor keys

Structural identities of the rebuilt pipeline's globals and constructors
(D19; `plans/x86-v2/00-conventions.md` "Identity and keys", note 02 §4.1).
Keys are built from Src's dense constant identities (`Src.CId`, one per
source `CRef`) and universe profiles (D18), never from digests: they compare
by `DecidableEq`, no theorem mentions a hash, and an address is only a label
for diagnostics.

* `CtorKey` names a constructor: a source constructor, or (Phase 2, P8) a
  closure shape.
* `GKey` names a global: erasure makes `const`, `byName`, `recStar` and
  `wrapper` globals, each at a universe profile; P4, P5 and P8 add `spec`,
  `worker`, `lam` and `dispatch`.
* `ArgKey` is a specialisation argument (P4).

The three types are mutually recursive, and Lean's `DecidableEq` deriving
handler does not cover mutual nested inductives, so the decision procedure
is written here by mutual structural recursion (kernel-evaluable, D17). -/

namespace IxCC.Key

/-- Which universe parameters are zero (D18). -/
abbrev Profile := Src.Profile

mutual

/-- Constructor identity (D19). -/
inductive CtorKey where
  /-- A source constructor. -/
  | src (c : Src.CId)
  /-- P8's closure constructor: global `f` with `supplied` arguments. -/
  | clo (f : GKey) (supplied : Nat)

/-- Global identity (D19). -/
inductive GKey where
  /-- Constant `c` at a profile: its δ body. -/
  | const (c : Src.CId) (prof : Profile)
  /-- The by-name variant of a `lazy` constant. -/
  | byName (c : Src.CId) (prof : Profile)
  /-- The erased recursor `r⋆`. -/
  | recStar (r : Src.CId) (prof : Profile)
  /-- A full-arity curried global for an unsaturated special head. -/
  | wrapper (h : Src.Head) (prof : Profile)
  /-- P4: `g` specialised on `args`. -/
  | spec (g : GKey) (args : List ArgKey)
  /-- P5: `g`'s worker keeping the parameters marked `true`. -/
  | worker (g : GKey) (keep : List Bool)
  /-- P8: a λ lifted from `g`'s body at `path`. -/
  | lam (g : GKey) (path : List Nat)
  /-- P8: the dispatcher of an arity. -/
  | dispatch (arity : Nat)

/-- A specialisation argument (P4). -/
inductive ArgKey where
  | glob (g : GKey)
  | con (c : CtorKey) (args : List ArgKey)
  | lit (n : Nat)
  | hole (i : Nat)

end

deriving instance Repr for CtorKey, GKey, ArgKey

instance : Inhabited CtorKey := ⟨.src 0⟩
instance : Inhabited GKey := ⟨.dispatch 0⟩

mutual

def CtorKey.decEq : (a b : CtorKey) → Decidable (a = b)
  | .src c, .src d =>
    if h : c = d then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .clo f n, .clo g m =>
    match GKey.decEq f g with
    | isTrue hf =>
      if hn : n = m then isTrue (hf ▸ hn ▸ rfl) else isFalse (fun e => by cases e; exact hn rfl)
    | isFalse hf => isFalse (fun e => by cases e; exact hf rfl)
  | .src _, .clo .. | .clo .., .src _ => isFalse (fun e => by cases e)
  termination_by structural a => a

def GKey.decEq : (a b : GKey) → Decidable (a = b)
  | .const c p, .const d q | .byName c p, .byName d q | .recStar c p, .recStar d q =>
    if h : c = d ∧ p = q then isTrue (h.1 ▸ h.2 ▸ rfl)
    else isFalse (fun e => by cases e; exact h ⟨rfl, rfl⟩)
  | .wrapper c p, .wrapper d q =>
    if h : c = d ∧ p = q then isTrue (h.1 ▸ h.2 ▸ rfl)
    else isFalse (fun e => by cases e; exact h ⟨rfl, rfl⟩)
  | .spec f xs, .spec g ys =>
    match GKey.decEq f g, ArgKey.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | .worker f xs, .worker g ys =>
    match GKey.decEq f g with
    | isTrue h1 =>
      if h2 : xs = ys then isTrue (h1 ▸ h2 ▸ rfl) else isFalse (fun e => by cases e; exact h2 rfl)
    | isFalse h1 => isFalse (fun e => by cases e; exact h1 rfl)
  | .lam f xs, .lam g ys =>
    match GKey.decEq f g with
    | isTrue h1 =>
      if h2 : xs = ys then isTrue (h1 ▸ h2 ▸ rfl) else isFalse (fun e => by cases e; exact h2 rfl)
    | isFalse h1 => isFalse (fun e => by cases e; exact h1 rfl)
  | .dispatch n, .dispatch m =>
    if h : n = m then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .const .., .byName .. | .const .., .recStar .. | .const .., .wrapper .. | .const .., .spec ..
  | .const .., .worker .. | .const .., .lam .. | .const .., .dispatch ..
  | .byName .., .const .. | .byName .., .recStar .. | .byName .., .wrapper ..
  | .byName .., .spec .. | .byName .., .worker .. | .byName .., .lam .. | .byName .., .dispatch ..
  | .recStar .., .const .. | .recStar .., .byName .. | .recStar .., .wrapper ..
  | .recStar .., .spec .. | .recStar .., .worker .. | .recStar .., .lam ..
  | .recStar .., .dispatch ..
  | .wrapper .., .const .. | .wrapper .., .byName .. | .wrapper .., .recStar ..
  | .wrapper .., .spec .. | .wrapper .., .worker .. | .wrapper .., .lam ..
  | .wrapper .., .dispatch ..
  | .spec .., .const .. | .spec .., .byName .. | .spec .., .recStar .. | .spec .., .wrapper ..
  | .spec .., .worker .. | .spec .., .lam .. | .spec .., .dispatch ..
  | .worker .., .const .. | .worker .., .byName .. | .worker .., .recStar ..
  | .worker .., .wrapper .. | .worker .., .spec .. | .worker .., .lam ..
  | .worker .., .dispatch ..
  | .lam .., .const .. | .lam .., .byName .. | .lam .., .recStar .. | .lam .., .wrapper ..
  | .lam .., .spec .. | .lam .., .worker .. | .lam .., .dispatch ..
  | .dispatch .., .const .. | .dispatch .., .byName .. | .dispatch .., .recStar ..
  | .dispatch .., .wrapper .. | .dispatch .., .spec .. | .dispatch .., .worker ..
  | .dispatch .., .lam .. => isFalse (fun e => by cases e)
  termination_by structural a => a

def ArgKey.decEq : (a b : ArgKey) → Decidable (a = b)
  | .glob f, .glob g =>
    match GKey.decEq f g with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .con c xs, .con d ys =>
    match CtorKey.decEq c d, ArgKey.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | .lit n, .lit m | .hole n, .hole m =>
    if h : n = m then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .glob _, .con .. | .glob _, .lit _ | .glob _, .hole _
  | .con .., .glob _ | .con .., .lit _ | .con .., .hole _
  | .lit _, .glob _ | .lit _, .con .. | .lit _, .hole _
  | .hole _, .glob _ | .hole _, .con .. | .hole _, .lit _ => isFalse (fun e => by cases e)
  termination_by structural a => a

def ArgKey.decEqList : (a b : List ArgKey) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match ArgKey.decEq x y, ArgKey.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (fun e => by cases e)
  termination_by structural a => a

end

instance : DecidableEq CtorKey := CtorKey.decEq
instance : DecidableEq GKey := GKey.decEq
instance : DecidableEq ArgKey := ArgKey.decEq

namespace GKey

/-- The source constant a key is derived from, if any: the bucket of
erasure's key table (keys with no constant use bucket 0). -/
def bucket : GKey → Nat
  | .const c _ | .byName c _ | .recStar c _ => c
  | .wrapper h _ =>
    match h with
    | .ctor c | .quotMk c | .quotLift c | .recr c | .cases c => c
    | .prim _ => 0
  | .spec g _ | .worker g _ | .lam g _ => g.bucket
  | .dispatch _ => 0

/-- Short rendering for diagnostics and reports. -/
def render : GKey → String
  | .const c p => s!"const {c}{Src.Profile.render p}"
  | .byName c p => s!"byName {c}{Src.Profile.render p}"
  | .recStar r p => s!"rec⋆ {r}{Src.Profile.render p}"
  | .wrapper h p =>
    let h := match h with
      | .ctor c => s!"ctor {c}" | .quotMk c => s!"Quot.mk {c}" | .quotLift c => s!"Quot.lift {c}"
      | .recr c => s!"rec {c}" | .cases c => s!"cases {c}" | .prim op => s!"prim {op.name}"
    s!"wrapper ({h}){Src.Profile.render p}"
  | .spec g _ => s!"spec ({g.render})"
  | .worker g _ => s!"worker ({g.render})"
  | .lam g _ => s!"lam ({g.render})"
  | .dispatch n => s!"dispatch {n}"

end GKey

end IxCC.Key
