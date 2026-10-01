module

public import ConLeche.Kernel.PropWhen
public import ConLeche.Kernel.Exclusive
/- `withPtrEq` is `public` but not `@[expose]`, and its whole point here
is that it is *definitionally* `k ()` — which is what
`Level.beqPtr_eq` and `Expr.beqMemo_eq` prove.  `import all` makes that
body visible **in this module only**; those theorems are the public
relays, so no importer needs it, and the executed `Level.beq` and
`Expr.beq` stay the plain `decide (· = ·)` that the kernel can still
reduce. -/
import all Init.Util


/-!
# Kernel expressions

The checker's own term representation, mirroring Lean's kernel expressions.
We deliberately do not reuse `Lean.Expr`: our own inductive has no cached
metadata, which keeps the verification story clean.

Design decisions (see DESIGN.md):
* Free variables (`fvar`) follow nanoda's representation: a de Bruijn *level*
  together with the variable's type (and binder name, for error messages).
  The type is part of the variable's identity, so a local context is implicit
  in every open term.  Input terms coming from declarations are closed and
  use only `bvar` (de Bruijn *indices*).
* No metavariables, no `mdata`: those never reach a kernel.
-/

@[expose] public section

namespace ConLeche


/-- Universe levels, mirroring `Lean.Level` without metavariables —
including the cached hash, which `Lean.Level` also keeps in a
`@[computed_field]` (`data`, `Lean/Level.lean`) and the C++ kernel in
the level's packed data word (`level::hash()`).  As for `Name`, the
field is a function of the value and no statement sees it. -/
inductive Level where
  | zero
  | succ (u : Level)
  | max (u v : Level)
  | imax (u v : Level)
  | param (n : Name)
with
  /-- The cached hash of a level. -/
  @[computed_field] hashData : Level → UInt64
    | .zero => 1
    | .succ u => mixHash 3 u.hashData
    | .max u v => mixHash 5 (mixHash u.hashData v.hashData)
    | .imax u v => mixHash 7 (mixHash u.hashData v.hashData)
    | .param n => mixHash 11 (hash n)
deriving DecidableEq, Repr, Inhabited

/-- Hashing a level is an `O(1)` field read (the memo maps keyed by
`Level` — `lsimpC`, `lnzC`, `eqvC` — probe with this). -/
instance : Hashable Level := ⟨Level.hashData⟩

/-- Level equality in the official kernel's shape (task #176 P2):
the cached **hash** and the **pointer** before the structural walk —
`level.cpp:125` is `kind` → `hash` → `is_eqp` → structural.  The
implementation of `Level.beq`; `Level.beqPtr_eq` proves both guards
redundant. -/
@[inline] def Level.beqPtr (a b : Level) : Bool :=
  withPtrEq a b (fun _ => a.hashData == b.hashData && decide (a = b))
    (fun h => by subst h; simp)

/-- Both guards are redundant (see `Name.beqPtr_eq`). -/
theorem Level.beqPtr_eq (a b : Level) : Level.beqPtr a b = decide (a = b) := by
  show (a.hashData == b.hashData && decide (a = b)) = decide (a = b)
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- The executed level equality: definitionally `decide (a = b)`, with
`beqPtr` substituted by the compiler on the `@[csimp]` equation below
(see `Name.beq_eq_beqPtr` for why this is not an escape). -/
def Level.beq (a b : Level) : Bool := decide (a = b)

/-- The `Level` twin of `Name.beq_eq_beqPtr`: `@[csimp]`, not
`@[implemented_by]`, on a kernel-checked equality. -/
@[csimp] theorem Level.beq_eq_beqPtr : @Level.beq = @Level.beqPtr := by
  funext a b; exact (Level.beqPtr_eq a b).symm

instance : BEq Level := ⟨Level.beq⟩

/-- `Level.beq` is lawful — it *is* `decide (· = ·)`. -/
instance : LawfulBEq Level where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Level.beq]

/-- Metadata carried by a binder (`forallE`, `lam`): the codomain
prop-ness annotation `pw` (task #161 — the validated-annotation design;
one datum per binder, written by the untrusted annotate pass or the
input stream and *validated* by the checker; the reduction rules never
read it).  Unannotated input defaults to `.never` at the parser — a
definite, validatable claim.  The display `BinderInfo` that used to
sit beside it is gone (task #205): the official kernel's equality and
hash ignore it, so it was never data the checker held — the frontend
validates a stream's spelling and drops it (`parseBinderInfo`). -/
structure BinderMeta where
  pw : PropWhen
  deriving DecidableEq, Repr, Hashable

instance : Inhabited BinderMeta := ⟨⟨.never⟩⟩

/-- Literals. -/
inductive Literal where
  | natVal (n : Nat)
  | strVal (s : String)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Does the level mention a parameter (the official kernel's
`level.has_param`)?  There is no interned level table here, so this is
an `O(|u|)` walk — paid once per `.sort`/`.const` node construction,
never per memo touch. -/
def levelHasParam : Level → Bool
  | .zero => false
  | .param _ => true
  | .succ u => levelHasParam u
  | .max u v | .imax u v => levelHasParam u || levelHasParam v

/-- `levelHasParam` over a `const` node's level arguments. -/
def levelsHaveParam : List Level → Bool
  | [] => false
  | u :: us => levelHasParam u || levelsHaveParam us

/-- A level's hash: the cached `@[computed_field]`, so a `.sort`/`.const`
node's `hash` field is `O(1)` in the level's size *and* exact (before
task #176 P3 this was a depth-4-bounded walk, `Level.hashB`, because
the level had nowhere to put a hash — the same trade `Expr.hashB` made
before task #172 B3a). -/
@[inline] def levelHash (u : Level) : UInt64 := u.hashData

/-- `levelHash` folded over a level list. -/
def levelsHash : List Level → UInt64
  | [] => 13
  | u :: us => mixHash (levelHash u) (levelsHash us)

/-! ## The packed node word (task #167)

`Lean.Expr` stores its derived data in one `UInt64` (`Lean.Expr.Data`:
a 32-bit hash, a 20-bit `looseBVarRange`, flags).  `ConLeche.Expr` does
the same, with one `@[computed_field] data : Expr → UInt64` whose
layout is

| bits | field | width |
|---|---|---|
| 63…32 | `hash` | 32 |
| 31 | *reserved* (always 0) | 1 |
| 30…16 | `bvarB`, the loose-bvar bound | 15 |
| 15…1 | `fvarB`, the fvar range | 15 |
| 0 | `hasLP` | 1 |

The two ranges **saturate** at `satRange = 2^15 - 1`: a node whose
bound would not fit stores `satRange`, which reads as "*at least*
`satRange`".  Saturation is a *representation* decision and costs
nothing logically — `Expr.bvarB`/`Expr.fvarB` remain the exact
functions `Expr.bvarBound`/`Expr.fvarRange` (`bvarB_eq`, `fvarB_eq`),
because the accessors fall back to a memoized exact walk on the
saturated branch.  What saturation costs is *performance*, and only
on terms that saturate: the `O(1)` field read becomes an `O(DAG)`
walk.  Measured maxima on the real streams — `init-full` 213,
`grind-ring-5` 488, `app-lam` (the deepest artificial workload) 4000 —
leave the branch unreached with 8× headroom.

The packing is written with **arithmetic**, not bitwise, operators
(`* 65536` for a shift, `/ 65536 % 32768` for a field read): the code
LLVM emits is the same shift-and-mask, and every roundtrip lemma
below is then `omega` after `UInt64.toNat`. -/

/-- Saturation value of the two 15-bit range fields: a stored
`satRange` reads as "at least `satRange`". -/
def satRange : Nat := 32767

/-- Assemble the packed word from a 32-bit hash, two 15-bit ranges and
the level-param flag.  Sums, not `|||`: the fields are disjoint, so
addition *is* the bitwise join, and the arithmetic form is what makes
the roundtrip lemmas `omega`-provable. -/
@[inline] def packData (h b f : UInt64) (lp : Bool) : UInt64 :=
  h * 4294967296 + b * 65536 + f * 2 + (if lp then 1 else 0)

/-- Hash field of a packed word (bits 63…32). -/
@[inline] def hashOfData (w : UInt64) : UInt64 := w / 4294967296

/-- Loose-bvar-bound field of a packed word (bits 30…16). -/
@[inline] def bvarOfData (w : UInt64) : UInt64 := w / 65536 % 32768

/-- Fvar-range field of a packed word (bits 15…1). -/
@[inline] def fvarOfData (w : UInt64) : UInt64 := w / 2 % 32768

/-- Has-level-param field of a packed word (bit 0). -/
@[inline] def lpOfData (w : UInt64) : Bool := w % 2 == 1

/-- Truncate a mixed hash to the packed word's 32 bits. -/
@[inline] def hash32 (w : UInt64) : UInt64 := w % 4294967296

/-- A leaf's range field: `n + 1`, saturating. -/
@[inline] def satSucc (n : Nat) : UInt64 := UInt64.ofNat (min (n + 1) satRange)

/-- A binder's range field: the body's bound less one, saturating
(a saturated body keeps a saturated bound — the stored value means
"at least", and subtracting from it would under-approximate). -/
@[inline] def satPred (x : UInt64) : UInt64 :=
  if x == 32767 then 32767 else if x == 0 then 0 else x - 1

/-! ### The packing roundtrip -/

theorem bvarOfData_lt (w : UInt64) : (bvarOfData w).toNat < 32768 := by
  simp [bvarOfData, UInt64.toNat_mod]; omega

theorem fvarOfData_lt (w : UInt64) : (fvarOfData w).toNat < 32768 := by
  simp [fvarOfData, UInt64.toNat_mod]; omega

theorem satSucc_lt (n : Nat) : (satSucc n).toNat < 32768 := by
  simp [satSucc, satRange]; omega

/-- `UInt64.max` transports to `Nat.max` through `toNat`. -/
theorem toNat_max (a b : UInt64) : (max a b).toNat = max a.toNat b.toNat := by
  simp only [Max.max]
  split <;> rename_i h <;> simp_all [UInt64.le_iff_toNat_le] <;> omega

/-- Predecessor on a `UInt64` known to be nonzero. -/
theorem toNat_sub_one {x : UInt64} (h : x.toNat ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hs := UInt64.toNat_lt_size x
  simp only [UInt64.size] at hs
  simp only [UInt64.toNat_sub, UInt64.toNat_one]
  omega

theorem satPred_lt {x : UInt64} (hx : x.toNat < 32768) :
    (satPred x).toNat < 32768 := by
  unfold satPred
  split
  · decide
  · split
    · decide
    · rename_i h₁ h₂
      have hne : x.toNat ≠ 0 := by
        simpa [← UInt64.toNat_inj] using h₂
      rw [toNat_sub_one hne]
      omega

theorem max_lt_32768 {a b : UInt64} (ha : a.toNat < 32768)
    (hb : b.toNat < 32768) : (max a b).toNat < 32768 := by
  rw [toNat_max]; omega

theorem bvarOfData_pack (h b f : UInt64) (lp : Bool)
    (hb : b.toNat < 32768) (hf : f.toNat < 32768) :
    bvarOfData (packData h b f lp) = b := by
  apply UInt64.toNat_inj.mp
  cases lp <;>
  · simp [bvarOfData, packData, UInt64.toNat_add, UInt64.toNat_mul,
      UInt64.toNat_div, UInt64.toNat_mod]
    omega

theorem fvarOfData_pack (h b f : UInt64) (lp : Bool)
    (_hb : b.toNat < 32768) (hf : f.toNat < 32768) :
    fvarOfData (packData h b f lp) = f := by
  apply UInt64.toNat_inj.mp
  cases lp <;>
  · simp [fvarOfData, packData, UInt64.toNat_add, UInt64.toNat_mul,
      UInt64.toNat_div, UInt64.toNat_mod]
    omega

theorem lpOfData_pack (h b f : UInt64) (lp : Bool)
    (_hb : b.toNat < 32768) (_hf : f.toNat < 32768) :
    lpOfData (packData h b f lp) = lp := by
  cases lp <;>
  · simp [lpOfData, packData, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.toNat_mul, UInt64.toNat_mod]
    omega

theorem hashOfData_pack (h b f : UInt64) (lp : Bool)
    (_hh : h.toNat < 4294967296) (hb : b.toNat < 32768)
    (hf : f.toNat < 32768) :
    hashOfData (packData h b f lp) = hash32 h := by
  apply UInt64.toNat_inj.mp
  cases lp <;>
  · simp [hashOfData, hash32, packData, UInt64.toNat_add, UInt64.toNat_mul,
      UInt64.toNat_div, UInt64.toNat_mod]
    omega

/-- Kernel expressions.

`fvar idx type`: an opened variable, identified by its de Bruijn level
`idx` *and* its type.  Closed input terms contain no `fvar`s.

## No display data (task #205, user ruling)

The official kernel's `is_equal` and `hash` ignore binder names and
`BinderInfo`s (`expr_eq_fn.cpp:52, :100-103`).  Task #203 first made
every term the checker holds carry them at one normal form; the user's
ruling on that — *"if we don't keep the names we should drop the
fields!"* — is why `lam`/`forallE`/`letE` carry no binder name,
`fvar` no display name and `BinderMeta` no `BinderInfo`: there is
nothing α-irrelevant in a node, so structural `=`/`==` and the packed
`hash` ARE α-equivalence, with nothing to normalise and nothing a
fabricated term could get wrong.  The frontend still *validates* a
stream's `name` and `binderInfo` fields (a malformed record is
malformed) and drops them (`ConLeche/Frontend/ExportC.lean`); the pin
builder's `pi "a"`/`piI "α"` keep the `Init.Prelude` spelling as a
reader-facing argument (`ConLeche/Kernel/Basis/Builder.lean`).  Error
messages never printed a binder name; positions (de Bruijn level,
constant name) are what they carry.

## The computed field (task #172 B3a; packed at task #167)

Every node carries a block of derived data, **computed once at
construction time** by Lean's `@[computed_field]` feature — exactly
`Lean.Expr`'s own arrangement, down to the packing:

* `hash`  — the node's hash, so hashing a term for a memo lookup is a
  field read instead of a traversal;
* `bvarB` — the loose-bvar *bound*: the least `k` with
  `looseBVarsBounded k` (`Expr.bvarBound` is the same recurrence
  spelled as an ordinary function; `bvarB_eq` proves them equal).
  Instantiation at or above the bound is the identity;
* `fvarB` — the fvar *range*: max fvar index + 1 (`0` = fvar-free;
  `fvar` type annotations are not descended, matching the abstraction
  traversals — `Expr.fvarRange`).  Abstraction at or above the range
  is the identity;
* `hasLP` — has-level-param (`Expr.hasLevelParam`; the official
  kernel's `has_univ_param`).  Level instantiation on a node without
  it is the identity.

**One word holds all four** (`data`, the layout table above
`satRange`), which is where the node's memory goes: four separate
fields cost a `UInt64`, two boxed `Nat` pointers and a `Bool`; one
word costs eight bytes.  `bvarB` and `fvarB` *saturate* at
`satRange`; the accessors stay **exact** by falling back, on the
saturated branch alone, to a memoized walk (`bvarBoundMemo`,
`fvarRangeMemo` in `Kernel/ExprOps.lean`).  So no lemma anywhere
weakens and no invariant is threaded: saturation buys memory and
costs performance, and only on terms that saturate.

The *storage* is the compiler's: `Lean/Elab/ComputedFields.lean:33` —
*"This file implements the computed fields feature by simulating it
via `implemented_by`."*  That is a named trust escape; it is
enumerated, with the user ruling that adopted it, in the trust census
in `ConLeche/Cached/ExprNodes.lean`'s module docstring. -/
inductive Expr where
  | bvar (i : Nat)
  | fvar (idx : Nat) (type : Expr)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : Expr)
  | lam (type body : Expr) (m : BinderMeta)
  | forallE (type body : Expr) (m : BinderMeta)
  | letE (type value body : Expr)
  | lit (l : Literal)
  | proj (structName : Name) (idx : Nat) (e : Expr)
with
  /-- The packed derived-data word: `hash` (32) ǀ reserved (1) ǀ
  `bvarB` (15, saturating) ǀ `fvarB` (15, saturating) ǀ `hasLP` (1). -/
  @[computed_field] data : Expr → UInt64
    | .bvar i =>
      packData (hash32 (mixHash 3 (Hashable.hash i))) (satSucc i) 0 false
    | .fvar idx ty =>
      packData (hash32 (mixHash 5 (mixHash (Hashable.hash idx)
          (hashOfData ty.data))))
        0 (satSucc idx) (lpOfData ty.data)
    | .sort u =>
      packData (hash32 (mixHash 7 (levelHash u))) 0 0 (levelHasParam u)
    | .const n us =>
      packData (hash32 (mixHash 11 (mixHash (Hashable.hash n)
          (levelsHash us)))) 0 0 (levelsHaveParam us)
    | .app f a =>
      packData (hash32 (mixHash 17
          (mixHash (hashOfData f.data) (hashOfData a.data))))
        (max (bvarOfData f.data) (bvarOfData a.data))
        (max (fvarOfData f.data) (fvarOfData a.data))
        (lpOfData f.data || lpOfData a.data)
    | .lam ty b m =>
      packData (hash32 (mixHash 19
          (mixHash (hashOfData ty.data)
            (mixHash (hashOfData b.data) (Hashable.hash m.pw)))))
        (max (bvarOfData ty.data) (satPred (bvarOfData b.data)))
        (max (fvarOfData ty.data) (fvarOfData b.data))
        (lpOfData ty.data || lpOfData b.data || m.pw.hasParams)
    | .forallE ty b m =>
      packData (hash32 (mixHash 23
          (mixHash (hashOfData ty.data)
            (mixHash (hashOfData b.data) (Hashable.hash m.pw)))))
        (max (bvarOfData ty.data) (satPred (bvarOfData b.data)))
        (max (fvarOfData ty.data) (fvarOfData b.data))
        (lpOfData ty.data || lpOfData b.data || m.pw.hasParams)
    | .letE ty v b =>
      packData (hash32 (mixHash 29
          (mixHash (hashOfData ty.data)
            (mixHash (hashOfData v.data) (hashOfData b.data)))))
        (max (max (bvarOfData ty.data) (bvarOfData v.data))
          (satPred (bvarOfData b.data)))
        (max (max (fvarOfData ty.data) (fvarOfData v.data))
          (fvarOfData b.data))
        (lpOfData ty.data || lpOfData v.data || lpOfData b.data)
    | .lit l => packData (hash32 (mixHash 31 (Hashable.hash l))) 0 0 false
    | .proj s i e =>
      packData (hash32 (mixHash 37 (mixHash (Hashable.hash s)
          (mixHash (Hashable.hash i) (hashOfData e.data)))))
        (bvarOfData e.data) (fvarOfData e.data) (lpOfData e.data)
deriving DecidableEq, Repr, Inhabited

/-! ## The packed word's accessors

`hash` and `hasLP` are exact bit reads.  `bvarBRaw`/`fvarBRaw` are the
*saturating* reads: below `satRange` they are the exact bound
(`bvarBRaw_exact` in `Kernel/ExprOps.lean`, `fvarBRaw_exact` in
`Verify/Cached/Erase.lean`); at
`satRange` they mean "at least that", and `Expr.bvarB`/`Expr.fvarB`
(`Kernel/ExprOps.lean`) recover exactness there with a memoized
walk. -/

namespace Expr

/-- The node's 32-bit hash (`O(1)`).  The recurrence reads exactly
what `is_equal` in the official kernel reads (`expr_eq_fn.cpp`) plus
the validated `pw` datum; there is no display data in a node (task
#205), so hashing and `DecidableEq` are α-equivalence outright. -/
@[inline] def hash (e : Expr) : UInt64 := hashOfData e.data

/-- Has-level-param: is level instantiation ever non-trivial here?
One bit, so this read is *exact*. -/
@[inline] def hasLP (e : Expr) : Bool := lpOfData e.data

/-- The stored loose-bvar bound, saturating at `satRange`. -/
@[inline] def bvarBRaw (e : Expr) : Nat := (bvarOfData e.data).toNat

/-- The stored fvar range, saturating at `satRange`. -/
@[inline] def fvarBRaw (e : Expr) : Nat := (fvarOfData e.data).toNat

end Expr

/-- Hashing is the computed field: `O(1)`, no traversal.  (Before task
#172 B3a this was a *node-budgeted* walk, `Expr.hashB`, because the
pure representation had nowhere to put a hash.  `levelHash` kept a
depth budget for the same reason until task #176 P3 gave `Level` its
own computed field; no hash in the tree is budgeted any more.) -/
instance : Hashable Expr := ⟨Expr.hash⟩

namespace Expr

/-! ### The stored ranges, constructor by constructor

Each equation is the packed word's recurrence read back through the
roundtrip lemmas; together they are what the exactness induction in
`Verify/Cached/Erase.lean` runs on. -/

theorem bvarBRaw_lt (e : Expr) : e.bvarBRaw < 32768 := bvarOfData_lt _

theorem fvarBRaw_lt (e : Expr) : e.fvarBRaw < 32768 := fvarOfData_lt _

private theorem toNat_satSucc (n : Nat) :
    (satSucc n).toNat = min (n + 1) satRange := by
  simp [satSucc, satRange]
  omega

private theorem toNat_satPred {x : UInt64} (_hx : x.toNat < 32768) :
    (satPred x).toNat = if x.toNat = satRange then satRange else x.toNat - 1 := by
  by_cases hs : x.toNat = satRange
  · have : x = 32767 := by rw [← UInt64.toNat_inj]; simpa [satRange] using hs
    simp [satPred, this, satRange]
  · have hne : x ≠ 32767 := by
      rw [Ne, ← UInt64.toNat_inj]; simpa [satRange] using hs
    by_cases hz : x.toNat = 0
    · have : x = 0 := by rw [← UInt64.toNat_inj]; simpa using hz
      simp [satPred, this, satRange]
    · have hz' : x ≠ 0 := by rw [Ne, ← UInt64.toNat_inj]; simpa using hz
      simp only [satPred, beq_iff_eq, hne, hz', if_false, if_neg hs,
        toNat_sub_one hz]

@[simp] theorem bvarBRaw_bvar (i : Nat) :
    (Expr.bvar i).bvarBRaw = min (i + 1) satRange := by
  show (bvarOfData (packData _ (satSucc i) 0 false)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (satSucc_lt i) (by decide), toNat_satSucc]

@[simp] theorem bvarBRaw_fvar (idx : Nat) (ty : Expr) :
    (Expr.fvar idx ty).bvarBRaw = 0 := by
  show (bvarOfData (packData _ 0 (satSucc idx) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (by decide) (satSucc_lt idx)]; rfl

@[simp] theorem bvarBRaw_sort (u : Level) : (Expr.sort u).bvarBRaw = 0 := by
  show (bvarOfData (packData _ 0 0 _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem bvarBRaw_const (n : Name) (us : List Level) :
    (Expr.const n us).bvarBRaw = 0 := by
  show (bvarOfData (packData _ 0 0 _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem bvarBRaw_lit (l : Literal) : (Expr.lit l).bvarBRaw = 0 := by
  show (bvarOfData (packData _ 0 0 _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem bvarBRaw_app (f a : Expr) :
    (Expr.app f a).bvarBRaw = max f.bvarBRaw a.bvarBRaw := by
  show (bvarOfData (packData _ (max _ _) (max _ _) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem bvarBRaw_lam (ty b : Expr) (m : BinderMeta) :
    (Expr.lam ty b m).bvarBRaw =
      max ty.bvarBRaw
        (if b.bvarBRaw = satRange then satRange else b.bvarBRaw - 1) := by
  show (bvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max,
    toNat_satPred (bvarOfData_lt _)]
  rfl

@[simp] theorem bvarBRaw_forallE (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE ty b m).bvarBRaw =
      max ty.bvarBRaw
        (if b.bvarBRaw = satRange then satRange else b.bvarBRaw - 1) := by
  show (bvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max,
    toNat_satPred (bvarOfData_lt _)]
  rfl

@[simp] theorem bvarBRaw_letE (ty v b : Expr) :
    (Expr.letE ty v b).bvarBRaw =
      max (max ty.bvarBRaw v.bvarBRaw)
        (if b.bvarBRaw = satRange then satRange else b.bvarBRaw - 1) := by
  show (bvarOfData (packData _ (max (max _ _) (satPred _)) (max (max _ _) _)
    _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
      (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))
      (fvarOfData_lt _)), toNat_max, toNat_max,
    toNat_satPred (bvarOfData_lt _)]
  rfl

@[simp] theorem bvarBRaw_proj (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).bvarBRaw = e.bvarBRaw := by
  show (bvarOfData (packData _ _ _ _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (bvarOfData_lt _) (fvarOfData_lt _)]
  rfl

@[simp] theorem fvarBRaw_bvar (i : Nat) : (Expr.bvar i).fvarBRaw = 0 := by
  show (fvarOfData (packData _ (satSucc i) 0 false)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (satSucc_lt i) (by decide)]; rfl

@[simp] theorem fvarBRaw_fvar (idx : Nat) (ty : Expr) :
    (Expr.fvar idx ty).fvarBRaw = min (idx + 1) satRange := by
  show (fvarOfData (packData _ 0 (satSucc idx) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (by decide) (satSucc_lt idx), toNat_satSucc]

@[simp] theorem fvarBRaw_sort (u : Level) : (Expr.sort u).fvarBRaw = 0 := by
  show (fvarOfData (packData _ 0 0 _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem fvarBRaw_const (n : Name) (us : List Level) :
    (Expr.const n us).fvarBRaw = 0 := by
  show (fvarOfData (packData _ 0 0 _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem fvarBRaw_lit (l : Literal) : (Expr.lit l).fvarBRaw = 0 := by
  show (fvarOfData (packData _ 0 0 _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem fvarBRaw_app (f a : Expr) :
    (Expr.app f a).fvarBRaw = max f.fvarBRaw a.fvarBRaw := by
  show (fvarOfData (packData _ (max _ _) (max _ _) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem fvarBRaw_lam (ty b : Expr) (m : BinderMeta) :
    (Expr.lam ty b m).fvarBRaw = max ty.fvarBRaw b.fvarBRaw := by
  show (fvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem fvarBRaw_forallE (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE ty b m).fvarBRaw = max ty.fvarBRaw b.fvarBRaw := by
  show (fvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem fvarBRaw_letE (ty v b : Expr) :
    (Expr.letE ty v b).fvarBRaw =
      max (max ty.fvarBRaw v.fvarBRaw) b.fvarBRaw := by
  show (fvarOfData (packData _ (max (max _ _) (satPred _)) (max (max _ _) _)
    _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
      (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))
      (fvarOfData_lt _)), toNat_max, toNat_max]
  rfl

@[simp] theorem fvarBRaw_proj (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).fvarBRaw = e.fvarBRaw := by
  show (fvarOfData (packData _ _ _ _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (bvarOfData_lt _) (fvarOfData_lt _)]
  rfl

/-! ### The has-level-param bit, constructor by constructor -/

@[simp] theorem hasLP_bvar (i : Nat) : (Expr.bvar i).hasLP = false := by
  show lpOfData (packData _ (satSucc i) 0 false) = _
  rw [lpOfData_pack _ _ _ _ (satSucc_lt i) (by decide)]

@[simp] theorem hasLP_fvar (idx : Nat) (ty : Expr) :
    (Expr.fvar idx ty).hasLP = ty.hasLP := by
  show lpOfData (packData _ 0 (satSucc idx) _) = _
  rw [lpOfData_pack _ _ _ _ (by decide) (satSucc_lt idx)]; rfl

@[simp] theorem hasLP_sort (u : Level) :
    (Expr.sort u).hasLP = levelHasParam u := by
  show lpOfData (packData _ 0 0 _) = _
  rw [lpOfData_pack _ _ _ _ (by decide) (by decide)]

@[simp] theorem hasLP_const (n : Name) (us : List Level) :
    (Expr.const n us).hasLP = levelsHaveParam us := by
  show lpOfData (packData _ 0 0 _) = _
  rw [lpOfData_pack _ _ _ _ (by decide) (by decide)]

@[simp] theorem hasLP_lit (l : Literal) : (Expr.lit l).hasLP = false := by
  show lpOfData (packData _ 0 0 _) = _
  rw [lpOfData_pack _ _ _ _ (by decide) (by decide)]

@[simp] theorem hasLP_app (f a : Expr) :
    (Expr.app f a).hasLP = (f.hasLP || a.hasLP) := by
  show lpOfData (packData _ (max _ _) (max _ _) _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_lam (ty b : Expr) (m : BinderMeta) :
    (Expr.lam ty b m).hasLP = (ty.hasLP || b.hasLP || m.pw.hasParams) := by
  show lpOfData (packData _ (max _ (satPred _)) (max _ _) _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_forallE (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE ty b m).hasLP =
      (ty.hasLP || b.hasLP || m.pw.hasParams) := by
  show lpOfData (packData _ (max _ (satPred _)) (max _ _) _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_letE (ty v b : Expr) :
    (Expr.letE ty v b).hasLP = (ty.hasLP || v.hasLP || b.hasLP) := by
  show lpOfData (packData _ (max (max _ _) (satPred _)) (max (max _ _) _)
    _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
      (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))
      (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_proj (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).hasLP = e.hasLP := by
  show lpOfData (packData _ _ _ _) = _
  rw [lpOfData_pack _ _ _ _ (bvarOfData_lt _) (fvarOfData_lt _)]
  rfl


/-! ## Equality

The official kernel's `is_equal`: pointer identity, then the computed
hashes (a cheap reject — a hash mismatch *is* an inequality), then
structural descent.  Since instantiation and abstraction return
unchanged subterms **by reference**, the pointer test decides most
comparisons in `O(1)`, which is the arena's index comparison in a
different mechanism.

**The specification is plain decidable equality**, `beq a b =
decide (a = b)`, and the executed function is **proved** equal to it
(`beqMemo_eq`) and substituted by `@[csimp]` — the same arrangement
as `Name.beq`/`Level.beq`, with no `implemented_by` and nothing
`unsafe` anywhere on the path.  The two runtime facts a pointer test
rests on — an address names one immutable object, so pointer-equal
means equal — enter only through `Init.Util`'s `withPtrEq` and
`withPtrAddr`, whose *pure* definitions (`k ()`, `k 0`) are what the
theorem is about; the compiler's substitution of the real address is
its own contract, licensed by the side conditions those functions
demand and this file discharges.

The descent is **memoised** on the DAG so that it is `O(DAG)` rather
than `O(tree)`: hash-consing identifies structurally equal terms
however they arose, so the arena never compares two
distinct-but-equal DAGs, while a reduction that rebuilds a term the
arena would have collapsed does exactly that.  The memo is
*verified*, not trusted:

* an entry is the **pair of objects** a completed descent proved
  equal, together with the proof (`EqPair`), so the map's value type
  carries the invariant and no lemma about the map is needed;
* a probe finds a candidate by the address pair (`beqKey`) and then
  checks the candidate **by identity** (`withPtrEqDecEq` on each
  side), which is where the `a = b` behind a hit comes from.  At
  runtime the identity test is the pointer test: the stored objects
  are held by the memo, so their addresses stay theirs for the life
  of the comparison and an address match *is* an identity match.  The
  structural fallback that `withPtrEqDecEq` requires exists for the
  pure model and is never reached by compiled code;
* the memo is passed through a quotient (`Squash`) that identifies
  all its states, so the result of the descent is a *subsingleton*
  (a `Decidable (a = b)` beside an unobservable state) — which is
  exactly the side condition `withPtrAddr` asks of a continuation
  that reads an address.  The compiler erases the quotient; the
  runtime map is the raw hash map.

The pure model, in which every address is `0`, is a slow but correct
structural equality: every branch of the descent returns
`Decidable (a = b)` for its own `a`, `b`, so the equation holds by
construction and the proof of `beqMemo_eq` is three lines. -/

/-- `true` for the nodes whose comparison recurses.  The memo is
consulted and written **only** at these: a `bvar`, `sort`, `const` or
`lit` pair is decided without a descent, so an entry for it can never
save a walk and every one of them costs a probe, a bucket cons cell
and, at the end of the call, its `lean_dec_ref`.  Leaves are the
majority of the nodes of a real term. -/
@[inline] def beqRecursive : Expr → Bool
  | .fvar .. | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => true
  | _ => false

/-- A memo entry: the pair of objects a completed descent proved
equal, the addresses the descent saw them at, and the proof.  The
proof is erased; the addresses are the probe's cheap filter; the
objects are what the probe verifies against (`probeHit`) — and
holding them is what keeps their addresses theirs. -/
structure EqPair where
  fst : Expr
  snd : Expr
  pa : USize
  pb : USize
  eq : fst = snd

/-- The default a probe reads on a miss: no object has address `0`,
so its filter never passes at runtime. -/
def EqPair.dflt : EqPair := ⟨.bvar 0, .bvar 0, 0, 0, rfl⟩

/-- The memo: keyed on the packed address pair (`beqKey`). -/
abbrev BeqMap := Std.HashMap Nat EqPair

/-- The memo key of a pair of addresses, packed into ONE small `Nat`:
a `Nat × Nat` key would be a `Prod` cell allocated on every probe and
every write, while a `Nat` below `2^62` is a tagged scalar and costs
nothing.  The packing need not be injective — the probe verifies the
stored pair itself — so a collision between distinct pairs costs an
entry, never an answer. -/
@[inline] def beqKey (pa pb : USize) : Nat :=
  ((pa ^^^ (pb * 0x9E3779B97F4A7C15)) &&& 0x3FFFFFFFFFFFFFFF).toNat

/-- `withPtrAddr` into a subsingleton: its side condition — the
continuation's result does not depend on the address — is then
`Subsingleton.elim`. -/
@[inline] def withAddr {α : Type u} {β : Type v} [Subsingleton β] (a : α)
    (k : USize → β) : β :=
  withPtrAddr a k (fun _ _ => Subsingleton.elim _ _)

/-- Identity, decided: the pointer test at runtime, the derived
structural decision in the pure model. -/
@[inline] def ptrDec (a b : Expr) : Decidable (a = b) :=
  withPtrEqDecEq a b (fun _ => instDecidableEqExpr a b)

/-- Does the entry at `key` identify the pair `(a, b)`?  The stored
addresses are the filter; the stored objects, tested by identity, are
the verification, and the proof behind a `true` is the entry's own.
At runtime a passed filter is an identity match, so `ptrDec` decides
by pointer and never walks. -/
@[inline] def probeHit (m : BeqMap) (key : Nat) (pa pb : USize) (a b : Expr) :
    { h : Bool // h = true → a = b } :=
  let p := m.getD key EqPair.dflt
  if p.pa == pa && p.pb == pb then
    match ptrDec p.fst a, ptrDec p.snd b with
    | isTrue h1, isTrue h2 => ⟨true, fun _ => h1 ▸ h2 ▸ p.eq⟩
    | _, _ => ⟨false, fun h => Bool.noConfusion h⟩
  else ⟨false, fun h => Bool.noConfusion h⟩

/-! ### The memo discipline: memoise only what is shared (task #319)

The memo is the substitution walks' (`ConLeche/Cached/ExprOpsC.lean`,
"The substitution walks"), and the tree has ONE such discipline: at
every recursive child position `withExclusive`
(`ConLeche/Kernel/Exclusive.lean`) reads the count of the BORROWED
node, and only a pair whose two nodes are both SHARED is probed and
recorded — a pair with an exclusive side cannot be queried again
within this comparison, so it costs no key, no probe and no entry.
This is the official kernel's `expr_eq_fn::check_cache` guard
(`src/kernel/expr_eq_fn.cpp`: `if (is_shared(a) && is_shared(b))` in
front of the probe and the write), which the task #240 record could
not port because a Lean walk saw its arguments owned; task #317's
`withExclusive` reads a borrowed node's count, and `beqGoX`'s terms
are borrowed already.

The child step `enterBeq` plays `enter*P`'s part: the pointer test,
the computed-word test, the leaf test, then the two exclusivity
reads.  There is NO cutoff — the node budget that used to keep the
table away from small comparisons was the tree's second heuristic
cutoff after the walks' and went with it (task #319) — so the table
appears at the first shared/shared pair proved equal, the root pair
is never asked (it reaches `beqGoX` past `beqMemo`'s pointer and word
tests and cannot recur), and nothing bounds the table but the
comparison's own end.  The entries are `EqPair`s (the pair, its two
addresses, and its proof), the key is the packed address pair
(`beqKey`), and a hit is validated by identity on BOTH stored objects
(`probeHit`) — self-proving entries, so there is no table invariant
and no lemma about the table at all.  Every branch returns
`Decidable (a = b)` for its own `a`, `b`, and the memo is behind the
quotient; `beqMemo_eq` is three lines, as it always was. -/

/-- The raw result of one node's comparison: the decision and the
memo (absent until the first recorded pair). -/
structure BeqResX (a b : Expr) where
  dec : Decidable (a = b)
  map : Option BeqMap

/-- The result as the descent returns it: the raw result behind a
quotient identifying all of them, so that it is a subsingleton — the
decision is one (`Decidable` is a subsingleton) and the state is
unobservable.  Erased by the compiler. -/
abbrev BeqOutX (a b : Expr) := Squash (BeqResX a b)

@[inline] def BeqOutX.mk {a b : Expr} (d : Decidable (a = b)) (map : Option BeqMap) :
    BeqOutX a b :=
  Quot.mk _ ⟨d, map⟩

/-- The write-back: the entry under its key, in the table or in a
fresh one. -/
@[inline] def BeqMap.record (mp : Option BeqMap) (key : Nat) (p : EqPair) : Option BeqMap :=
  match mp with
  | none => some (({} : BeqMap).insert key p)
  | some m => some (m.insert key p)

/-- The child step of `beqGoX`: pointer identity, the computed word,
the leaf test, then the exclusivity of each side — an exclusive side
means the pair cannot recur and the descent runs with the memo
untouched; a shared/shared pair is probed, and recorded on a completed
`true`.  The terms are borrowed, so the counts read are the counts of
the references inside the terms (the requirement stated in
`ConLeche/Cached/ExprOpsC.lean`; the check is the IR audit). -/
@[inline] def enterBeq (map : Option BeqMap) (a b : @& Expr)
    (rec : Option BeqMap → BeqOutX a b) : BeqOutX a b :=
  withAddr a fun pa => withAddr b fun pb =>
  if pa == pb then .mk (ptrDec a b) map
  else if h : a.data != b.data then
    .mk (isFalse (fun e => by subst e; simp at h)) map
  else if !beqRecursive a then rec map
  else withExcl a fun ea =>
    if ea then rec map
    else withExcl b fun eb =>
    if eb then rec map
    else
      let hit : { h : Bool // h = true → a = b } :=
        match map with
        | some m => probeHit m (beqKey pa pb) pa pb a b
        | none => ⟨false, fun h => Bool.noConfusion h⟩
      if hh : hit.1 then .mk (isTrue (hit.2 hh)) map
      else Squash.lift (rec map) fun r =>
        match r.dec with
        | isTrue h => .mk (isTrue h) (BeqMap.record r.map (beqKey pa pb) ⟨a, b, pa, pb, h⟩)
        | d => .mk d r.map

/-- The memoised structural descent: the constructor cases with the
child step (`enterBeq`) in front of every recursive call — every
branch returning `Decidable (a = b)` for its own `a`, `b` (the module
docstring above says why that is the whole proof).  A completed
`false` aborts the comparison at every level, so no unequal pair is
ever re-queried and only proved-equal pairs are stored, as in the
official kernel's `expr_eq_fn`.  The root pair reaches it past
`beqMemo`'s pointer and word tests and is never asked.  The terms are
borrowed (`@&`): the write-back is the only consumer that stores
them, and owned terms cost a reference-count pair per node — and the
exclusivity read would then answer `false` at every node
(`ConLeche/Kernel/Exclusive.lean`, "The borrowed-parameter
requirement"). -/
def beqGoX (map : Option BeqMap) (a b : @& Expr) : BeqOutX a b :=
  match a, b with
  | .bvar i, .bvar j =>
    .mk (if h : i = j then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.bvar.inj e))) map
  | .fvar i t, .fvar j u =>
    if h : i = j then
      Squash.lift (enterBeq map t u fun m => beqGoX m t u) fun r =>
        .mk (match r.dec with
          | isTrue h' => isTrue (by subst h; subst h'; rfl)
          | isFalse h' => isFalse (fun e => h' (Expr.fvar.inj e).2))
          r.map
    else .mk (isFalse (fun e => h (Expr.fvar.inj e).1)) map
  | .sort u, .sort v =>
    .mk (if h : u == v then isTrue (by rw [beq_iff_eq.mp h])
         else isFalse (fun e => h (beq_iff_eq.mpr (Expr.sort.inj e)))) map
  | .const n us, .const m vs =>
    .mk (if h : n == m && us == vs then
           isTrue (by
             have h1 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1
             have h2 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
             rw [h1, h2])
         else isFalse (fun e => h (by
           obtain ⟨h1, h2⟩ := Expr.const.inj e
           subst h1; subst h2; simp))) map
  | .app f x, .app g y =>
    Squash.lift (enterBeq map f g fun m => beqGoX m f g) fun r₁ =>
      match r₁.dec with
      | isFalse h => .mk (isFalse (fun e => h (Expr.app.inj e).1)) r₁.map
      | isTrue h => Squash.lift (enterBeq r₁.map x y fun m => beqGoX m x y) fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h' => isTrue (by subst h; subst h'; rfl)
          | isFalse h' => isFalse (fun e => h' (Expr.app.inj e).2))
          r₂.map
  | .lam t b m, .lam t' b' m' =>
    if h : m = m' then
      Squash.lift (enterBeq map t t' fun mp => beqGoX mp t t') fun r₁ =>
        match r₁.dec with
        | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.lam.inj e).1)) r₁.map
        | isTrue h₁ => Squash.lift (enterBeq r₁.map b b' fun mp => beqGoX mp b b') fun r₂ =>
          .mk (match r₂.dec with
            | isTrue h₂ => isTrue (by subst h; subst h₁; subst h₂; rfl)
            | isFalse h₂ => isFalse (fun e => h₂ (Expr.lam.inj e).2.1))
            r₂.map
    else .mk (isFalse (fun e => h (Expr.lam.inj e).2.2)) map
  | .forallE t b m, .forallE t' b' m' =>
    if h : m = m' then
      Squash.lift (enterBeq map t t' fun mp => beqGoX mp t t') fun r₁ =>
        match r₁.dec with
        | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.forallE.inj e).1)) r₁.map
        | isTrue h₁ => Squash.lift (enterBeq r₁.map b b' fun mp => beqGoX mp b b') fun r₂ =>
          .mk (match r₂.dec with
            | isTrue h₂ => isTrue (by subst h; subst h₁; subst h₂; rfl)
            | isFalse h₂ => isFalse (fun e => h₂ (Expr.forallE.inj e).2.1))
            r₂.map
    else .mk (isFalse (fun e => h (Expr.forallE.inj e).2.2)) map
  | .letE t v b, .letE t' v' b' =>
    Squash.lift (enterBeq map t t' fun mp => beqGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.letE.inj e).1)) r₁.map
      | isTrue h₁ => Squash.lift (enterBeq r₁.map v v' fun mp => beqGoX mp v v') fun r₂ =>
        match r₂.dec with
        | isFalse h₂ => .mk (isFalse (fun e => h₂ (Expr.letE.inj e).2.1)) r₂.map
        | isTrue h₂ => Squash.lift (enterBeq r₂.map b b' fun mp => beqGoX mp b b') fun r₃ =>
          .mk (match r₃.dec with
            | isTrue h₃ => isTrue (by subst h₁; subst h₂; subst h₃; rfl)
            | isFalse h₃ => isFalse (fun e => h₃ (Expr.letE.inj e).2.2))
            r₃.map
  | .lit l, .lit l' =>
    .mk (if h : l = l' then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.lit.inj e))) map
  | .proj s i e, .proj s' i' e' =>
    if h : s == s' && i == i' then
      Squash.lift (enterBeq map e e' fun mp => beqGoX mp e e') fun r =>
        .mk (match r.dec with
          | isTrue h' =>
            isTrue (by
              have h1 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1
              have h2 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
              rw [h1, h2, h'])
          | isFalse h' => isFalse (fun e => h' (Expr.proj.inj e).2.2))
          r.map
    else .mk (isFalse (fun e => h (by
      obtain ⟨h1, h2, _⟩ := Expr.proj.inj e
      subst h1; subst h2; simp))) map
  | a', b' => .mk (instDecidableEqExpr a' b') map
termination_by structural a

/-- The descent's decision, from a fresh state (no table: the first
shared/shared pair proved equal creates it). -/
def beqDec (a b : Expr) : Decidable (a = b) :=
  Squash.lift (beqGoX none a b) fun r => r.dec

/-- The executed equality: pointer test, computed-word test, then the
memoised descent.  The implementation of `beq`; `beqMemo_eq` proves
it is `decide (a = b)`. -/
@[inline] def beqMemo (a b : Expr) : Bool :=
  withPtrEq a b (fun _ => if a.data == b.data then @decide (a = b) (beqDec a b) else false)
    (fun h => by subst h; simp)

/-- The executed equality is the specification: `withPtrEq a b k h`
is *defined* as `k ()`, the word guard cannot reject an equal pair,
and `beqDec` is *a* decision of `a = b`, hence *the* decision. -/
theorem beqMemo_eq (a b : Expr) : beqMemo a b = decide (a = b) := by
  show (if a.data == b.data then @decide (a = b) (beqDec a b) else false) = decide (a = b)
  rw [Subsingleton.elim (beqDec a b) (instDecidableEqExpr a b)]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- The executed structural equality.  Definitionally `decide (a = b)`,
hence definitionally the `BEq` any `DecidableEq` type has, with
`beqMemo` substituted by the compiler on the `@[csimp]` equation
below. -/
def beq (a b : Expr) : Bool := decide (a = b)

/-- The `Expr` twin of `Name.beq_eq_beqPtr`: `@[csimp]` on a
kernel-checked equality, not `@[implemented_by]`. -/
@[csimp] theorem beq_eq_beqMemo : @Expr.beq = @Expr.beqMemo := by
  funext a b; exact (beqMemo_eq a b).symm

instance : BEq Expr := ⟨Expr.beq⟩

/-- `beq` is lawful — it *is* `decide (· = ·)`. -/
instance : LawfulBEq Expr where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Expr.beq]

/-! ## The shared `bvar` pool (task #177)

A `bvar` node is the smallest thing this checker builds and the one it
builds most: every substitution shifts loose indices, every abstraction
introduces one, the parser reads one per occurrence.  Each of those was
a fresh allocation — and, since the substitution walks stopped
recording their atoms in the per-walk memo, a fresh allocation that
nothing shared afterwards.

`bvarPool` is one **static** table of the first `bvarPoolSize` of them.
It is a closed top-level `def`, so the runtime builds it once at module
initialization and marks it persistent (`lean_mark_persistent` in the
generated C): handing out `bvarPool[i]` costs a bounds check and a
borrowed read, and its reference counting is free.  `mkBvar` is
representation-transparent (`mkBvar_eq`, `@[simp]`), so pattern
matching stays on `.bvar` and no statement anywhere changes.

**Where it is used.**  Every *runtime* `bvar` construction goes through
it, and the routing is one line: `ConLeche.Expr.mkBVar` is the
cached tier's only `bvar` builder, so the substitution and abstraction
walks and the frontend's parser are all covered at once.  The
remaining `.bvar` literals in the tree are either the pure *spec*
functions of `ConLeche/Kernel/ExprOps.lean` (which must keep the bare
constructor — they are what the pool is proved transparent against) or
closed constants such as the cores' `.bvar 0`, which the compiler
already lifts to a per-module `_init_…_closed__n` and marks persistent
itself.

The bound covers the corpus with room to spare: the deepest de Bruijn
index the battery produces is the 4 000-binder λ tower of
`good/perf/app-lam`. -/

/-- Size of the static `bvar` pool. -/
def bvarPoolSize : Nat := 4096

@[inherit_doc bvarPoolSize]
def bvarPool : Array Expr := (Array.range bvarPoolSize).map Expr.bvar

/-- The `bvar` smart constructor: the pooled node below `bvarPoolSize`,
a fresh one above it.  Same value either way (`mkBvar_eq`). -/
@[inline] def mkBvar (i : Nat) : Expr :=
  if h : i < bvarPool.size then bvarPool[i] else .bvar i

@[simp] theorem mkBvar_eq (i : Nat) : mkBvar i = .bvar i := by
  unfold mkBvar
  split
  · simp [bvarPool]
  · rfl

end Expr

end ConLeche

