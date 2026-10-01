module

public import ConLeche.Cached.ExprNodes
public import ConLeche.Kernel.Core

@[expose] public section

/-!
# The cached syntactic operations on `Expr`

The **executed** counterparts of the arena operations in
`ConLeche/Kernel/IExpr.lean` — same clauses, same memo discipline, same
cutoffs; the mechanism differs only in where the derived data lives (a
field of the node instead of a parallel array indexed by the node's
arena position) and in how a rebuilt node is obtained (allocation
instead of a cons-table probe).

Two structural consequences of dropping the arena, both load-bearing
for the pilot's numbers:

* the scope and definedness walks' memos are keyed on `Expr` itself
  (`O(1)` hashing off the cached field, pointer-first equality), so
  shared sub-DAGs are still visited once — a `Std.HashMap Expr α`
  replaces the arena's `Std.HashMap EIdx α` one for one.  The
  SUBSTITUTION walks key theirs by address instead; see "The
  substitution walks" below;
* a cutoff (`bvarB ≤ d`, `fvarB ≤ d`, `!hasLP`) returns the node
  **itself**, so the result shares memory with the input and later
  pointer comparisons on it are `O(1)` — the analogue of the arena
  returning the same index.
-/

namespace ConLeche.Expr

/-! ## Spines -/

/-- Prepend the spine arguments of `e` to `acc` (outermost last). -/
def getAppArgsAccC : Expr → List Expr → List Expr
  | .app f a .., acc => getAppArgsAccC f (a :: acc)
  | _, acc => acc

/-- The arguments of an application spine, outermost last. -/
@[inline] def getAppArgsC (e : Expr) : List Expr := getAppArgsAccC e []

/-! ## The substitution walks (tasks #314, #316, #317)

ONE walk per operation — `instantiate1XP`, `instantiate1LiftXP`,
`instantiateListXP`, `instantiateRevXP`, `abstract1XP`,
`abstractRangeXP`, `instLevelParamsXP` — and ONE memo discipline.  The
design, as landed:

* **Memoise only what is shared.**  At every compound node past the
  cutoff the walk asks `withExclusive`
  (`ConLeche/Kernel/Exclusive.lean`) whether the node is an EXCLUSIVE
  object — single-threaded, reference count 1.  An exclusive node
  cannot be reached twice, so it is rebuilt with the memo untouched:
  no key, no probe, no insert.  A shared node (count `> 1`,
  multi-threaded, or persistent — the installed environment) is
  probed and, on a miss, recorded after the rebuild.  The table is
  created at the first shared compound node (`none` until then); the
  root is never probed (it cannot be reached again within its own
  walk).  The official kernel's `replace_fn` caches exactly the
  `!is_likely_unshared(e)` nodes.
* **Key the memo by address and cursor.**  The key is the node's
  address, read by `withPtrAddr` (`Expr.withAddr`) at the top of the
  shared step, packed with the cursor into one `Nat` (`pkey`) — a
  scalar, no allocation, no structural hash.  The table is a
  `Std.HashMap` on that key.
* **Validate a hit by pointer identity.**  A probe that returns an
  entry is believed only after `Expr.ptrDec` (`withPtrEq`, the
  pointer comparison at runtime and the derived structural decision
  in the model) says the stored node IS the current one, and the
  cursors compare equal.  The address is therefore never trusted: a
  wrong key can only cost a rebuild, never a value.
* **Every entry is self-proving.**  A `PEnt` stores its node, its
  rebuild, its cursor and the proof `val = s node depth`.  So there is
  **no table invariant** — the table may be anything, may grow and may
  overwrite — and a validated hit yields the proof the walk's result
  type demands by rewriting along the two equalities.  This is the
  `BeqMap`/`EqPair`/`probeHit` shape of `Expr.beqGoX`, applied to the
  walks.
* **No cutoff.**  The walk is exact: it memoises every shared compound
  node it meets, for as long as the walk lasts, and nothing bounds the
  table.  The node budget of task #313 — a heuristic that stopped
  memoising after 256 nodes and restarted — is gone (task #317).

**The borrowed-parameter convention is a REQUIREMENT, not an
optimisation.**  The node is borrowed (`@&`) all the way down, and so
is the replacement.  An owned parameter is a reference of its own, and
the count `withExclusive` reads would then be "in-tree references
+ 1" — every child of a held root would answer shared, and the memo
would degenerate to the always-memoised walk.  Borrowed, the count is
the number of references INSIDE the term (plus the caller's at the
root, which is never asked), which is the question the memo exists to
answer.  **How this is checked**: by reading the generated C of every
walk (`.lake/build/ir/ConLeche/Cached/ExprOpsC.c`) for a surviving
`lean_inc_ref` of the node before `lean_is_exclusive_obj` — the IR
audits of the task #314 and #316 records (DESIGN.md).  A change to
these walks that drops a `@&` or lets a `let`, a closure or a `Prod`
hold the node across the check is silently correct and measurably
slower; the audit is what catches it.

**Verification is intrinsic** (the `Expr.beqGoX` shape): a walk returns
a `Squash` of the rebuilt term with its proof of equality to the PLAIN
descent (`*P`, the reference — `Verify/Cached/OpsC.lean` proves each
`*P` equal to the specification) beside the memo, which is
unobservable.  The result is a `Subsingleton`, which is the obligation
`withExclusive` and `withPtrAddr` each ask of their continuation — so
the wrapper's theorem holds whatever the reference count and the
address are, by the primitives' contracts, never by a case analysis on
either.  Each walk's `enter*P` is the child step: the cutoff, the
compound test, then the exclusivity read; its `rec` argument is the
descent itself, inlined, so the recursive call is applied to the
subterm and termination is the walk's own.

Nothing here adds to the trust surface beyond the one allowlisted
escape: `withPtrAddr` and `withPtrEq` are `Init.Util`'s (and the tree
already relies on both, in `Expr.beqGoX` and `Name.beq`), and
`withExclusive` is `ConLeche/Kernel/Exclusive.lean`'s — the walks' one
`unsafe`-implemented primitive, whose module docstring is the
justification `tests/trust-surface.sh` points at. -/

/-- The nodes a memo entry can save a descent of. -/
@[inline] def isCompound : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => true
  | _ => false

/-- The term of a walk's result (the quotient lifts: the term is fixed
by its subtype). -/
@[inline] def resTerm {c : Expr} {M : Type} (s : Squash ({ r : Expr // r = c } × M)) : Expr :=
  Quotient.lift (fun p => p.1.1) (fun p q _ => by rw [p.1.2, q.1.2]) s

/-- What the term of a walk's result is: the value its subtype names.
Whatever the exclusivity reads and the addresses were along the
way. -/
theorem resTerm_eq {c : Expr} {M : Type} (s : Squash ({ r : Expr // r = c } × M)) :
    resTerm s = c := by
  induction s using Quotient.ind with
  | _ p => exact p.1.2

/-! ### The memo

The key is the node's ADDRESS packed with the cursor into one `Nat`
(`pkey`: addresses are 8-byte aligned, so `addr / 8`, then the cursor
modulo `2^16` in the low bits — pure register arithmetic, a tagged
scalar, no allocation and no structural hash), and the table is a
`Std.HashMap` on it under a MIXING hash (the address bits are dense;
`hash64` is what `Lean.Ptr` uses, and the identity hash of `Nat` would
cluster them after Std's fold — the intern table's lesson of task
#89).

A structural key `(e, c)` was what the walks used before task #316: a
`Prod` allocation per entry, the node's cached hash mixed with the
cursor, and a `beq` on every probe.  The C++ kernel's `replace_fn`
pays none of that — its cache is an `unordered_map` on the raw `expr`
pointer and the offset — and neither does this.

The price of the cheap key is that the key alone proves nothing, so
the entry does: `PEnt` stores its node, its rebuild, its cursor and
the proof, and `PEnt.hit` believes a probe only after the cursors
compare equal and `Expr.ptrDec` says the stored node IS the current
one.  A key collision (an address reused within one walk cannot happen
— every recorded node is held by its entry and the root by the caller
— but nothing here depends on that) fails validation and is a miss.
Hence **no table invariant at all**: the table may grow, rehash and
overwrite freely, and no lemma about it is needed.

`withPtrAddr`'s own obligation is discharged the same way the rest of
the section's are: the continuation of the address read is the whole
shared-node step and returns a `Squash`, so it is `Subsingleton.elim`
(`Expr.withAddr`).  The address may choose HOW the walk computes —
which slot, which entry is consulted — never WHAT. -/

/-- The packed key: the node's address over its 8-byte alignment,
then the cursor modulo `2^16` in the low bits.  Pure `UInt64` register
arithmetic; a tagged scalar as a `Nat` (addresses are below `2^47`).
In the model the address is `0` and the key is the cursor — the
tables never rely on the key: an entry validates itself. -/
@[inline] def pkey (addr : USize) (c : Nat) : Nat :=
  (addr.toUInt64 / 8 * 65536 + (UInt64.ofNat c &&& 65535)).toNat

/-- A memo entry: the node it was made for, its rebuild, the cursor,
and the proof — the entry is its own invariant. -/
structure PEnt (s : Expr → Nat → Expr) where
  node : Expr
  val : Expr
  depth : Nat
  eq : val = s node depth

/-- A validated hit: the cursor compares equal and the stored node IS
the current one (by pointer at runtime — `Expr.ptrDec` — structurally
in the model); then the entry's proof is the walk's. -/
@[inline] def PEnt.hit {s : Expr → Nat → Expr} {β : Sort u} (p : PEnt s) (e : Expr) (c : Nat)
    (k : { r : Expr // r = s e c } → β) (miss : Unit → β) : β :=
  if hd : p.depth = c then
    match Expr.ptrDec p.node e with
    | isTrue hn => k ⟨p.val, by rw [p.eq, hn, hd]⟩
    | isFalse _ => miss ()
  else miss ()

/-- The hash-map variant's key: the packed `Nat` under a MIXING hash —
the identity hash of `Nat` clusters dense address bits after Std's
fold (the intern table's lesson, task #89). -/
structure PKey where
  val : Nat

instance : BEq PKey := ⟨fun a b => a.val == b.val⟩
instance : Hashable PKey := ⟨fun k => hash64 (UInt64.ofNat k.val)⟩

/-- The hash-map table: the incumbent's `Std.HashMap`, keyed by the
packed address instead of the structural pair. -/
abbrev HTab (s : Expr → Nat → Expr) := Std.HashMap PKey (PEnt s)

/-- The pointer-keyed memo: absent until the first shared compound
node. -/
abbrev MemoXP (s : Expr → Nat → Expr) := Option (HTab s)

/-- A pointer-keyed walk's result: the term, fixed by its proof,
beside the memo. -/
abbrev ResXP (s : Expr → Nat → Expr) (e : Expr) (c : Nat) :=
  { r : Expr // r = s e c } × MemoXP s

/-- The record: the entry under its packed key, in the table or in a
fresh one. -/
@[inline] def MemoXP.insert {s : Expr → Nat → Expr} (memo : MemoXP s) (key : Nat)
    (p : PEnt s) : MemoXP s :=
  match memo with
  | none => some (({} : HTab s).insert ⟨key⟩ p)
  | some m => some (m.insert ⟨key⟩ p)

/-- The shared-node step over the pointer-keyed memo: the address
read, the probe, the validated hit — else the descent and the record
under the key read BEFORE the descent (the result is a `Squash`, so
the address is unobservable: `withAddr`). -/
@[inline] def MemoXP.shared {s : Expr → Nat → Expr} (memo : MemoXP s) (e : Expr) (c : Nat)
    (rec : Unit → Squash (ResXP s e c)) : Squash (ResXP s e c) :=
  withAddr e fun addr =>
  let key := pkey addr c
  match memo with
  | none => Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
      Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, r, c, hr⟩)
  | some m =>
    match m[(⟨key⟩ : PKey)]? with
    | some p => p.hit e c (fun r => Squash.mk (r, memo)) fun _ =>
        Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
          Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, r, c, hr⟩)
    | none => Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
        Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, r, c, hr⟩)

/-- The cursor-free instance (`instLevelParams`): the cursored memo at
cursor `0`. -/
abbrev MemoXP0 (s : Expr → Expr) := MemoXP (fun e _ => s e)

abbrev ResXP0 (s : Expr → Expr) (e : Expr) := { r : Expr // r = s e } × MemoXP0 s

@[inline] def MemoXP0.shared {s : Expr → Expr} (memo : MemoXP0 s) (e : Expr)
    (rec : Unit → Squash (ResXP0 s e)) : Squash (ResXP0 s e) :=
  MemoXP.shared (s := fun e _ => s e) memo e 0 rec

/-! ### `instantiate1LiftC` (task #214, P4)

The capture-avoiding substitution `Expr.instantiate1Lift` — the one
substitution on the direct install's executed path that once had no
memoised twin at all: `structProjBodies` runs it once per field over
the constructor telescope, turning a DAG-shared field type into an
unshared tree each time.  The twin is the section's walk, with the
`bvarB` cutoff (a node bounded at or below the cursor is returned
unchanged).  `instantiate1LiftC_spec`
(`ConLeche/Verify/Cached/OpsC.lean`) reads it as
`Expr.instantiate1Lift`. -/

/-- The plain descent of `instantiate1LiftC`: the reference
`instantiate1LiftXP` carries its own proof against. -/
def instantiate1LiftP (v : Expr) (e : Expr) (d : Nat) : Expr :=
  if e.bvarB ≤ d then e else
  match e with
  | .bvar i .. =>
    if i = d then Expr.liftLooseBVars d 0 v else if i > d then Expr.mkBvar (i - 1) else e
  | .fvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (instantiate1LiftP v f d) (instantiate1LiftP v a d)
  | .lam ty body m .. =>
    mkLam (instantiate1LiftP v ty d) (instantiate1LiftP v body (d + 1)) m
  | .forallE ty body m .. =>
    mkForallE (instantiate1LiftP v ty d) (instantiate1LiftP v body (d + 1)) m
  | .letE ty val body .. =>
    mkLetE (instantiate1LiftP v ty d) (instantiate1LiftP v val d)
      (instantiate1LiftP v body (d + 1))
  | .proj sn i sub .. => mkProj sn i (instantiate1LiftP v sub d)

theorem instantiate1LiftP_cut {v e : Expr} {d : Nat} (h : e.bvarB ≤ d) :
    instantiate1LiftP v e d = e := by
  rw [instantiate1LiftP.eq_def]; simp [h]

/-- The child step of `instantiate1LiftXP`: the cutoff, the compound
test, the exclusivity read. -/
@[inline] def enterLiftP (v : @& Expr) (e : @& Expr) (d : Nat)
    (memo : MemoXP (instantiate1LiftP v))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (instantiate1LiftP v) e d)) :
    Squash (ResXP (instantiate1LiftP v) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiate1LiftP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut

/-- The walk of `instantiate1LiftC`. -/
def instantiate1LiftXP (v : @& Expr) (memo : MemoXP (instantiate1LiftP v)) (e : @& Expr)
    (d : Nat) (hcut : ¬ e.bvarB ≤ d) : Squash (ResXP (instantiate1LiftP v) e d) :=
  match e with
  | .bvar i .. =>
    Squash.mk (⟨if i = d then Expr.liftLooseBVars d 0 v
        else if i > d then Expr.mkBvar (i - 1) else .bvar i,
      by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterLiftP v f d memo (fun h => instantiate1LiftXP v memo f d h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterLiftP v a d memo (fun h => instantiate1LiftXP v memo a d h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [instantiate1LiftP]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterLiftP v ty d memo (fun h => instantiate1LiftXP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLiftP v body (d + 1) memo (fun h => instantiate1LiftXP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by rw [instantiate1LiftP]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterLiftP v ty d memo (fun h => instantiate1LiftXP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLiftP v body (d + 1) memo (fun h => instantiate1LiftXP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by rw [instantiate1LiftP]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterLiftP v ty d memo (fun h => instantiate1LiftXP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLiftP v val d memo (fun h => instantiate1LiftXP v memo val d h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterLiftP v body (d + 1) memo (fun h => instantiate1LiftXP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [instantiate1LiftP]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterLiftP v sub d memo (fun h => instantiate1LiftXP v memo sub d h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [instantiate1LiftP]; simp [hcut, hs, mkProj]⟩, memo)

/-- The cached `Expr.instantiate1Lift`: the cutoff, then the walk. -/
def instantiate1LiftC (e : @& Expr) (v : Expr) (d : Nat := 0) : Expr :=
  if hcut : e.bvarB ≤ d then e else
  resTerm (instantiate1LiftXP v none e d hcut)

/-- The plain descent of `instantiate1C`: the reference the walk is
verified against (`instantiate1P_spec`, `Verify/Cached/OpsC.lean`, is
the equation to `Expr.instantiate1`). -/
def instantiate1P (v : Expr) (e : Expr) (d : Nat) : Expr :=
  if e.bvarB ≤ d then e else
  match e with
  | .bvar i .. => if i = d then v else if i > d then Expr.mkBvar (i - 1) else e
  | .fvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (instantiate1P v f d) (instantiate1P v a d)
  | .lam ty body m .. => mkLam (instantiate1P v ty d) (instantiate1P v body (d + 1)) m
  | .forallE ty body m .. =>
    mkForallE (instantiate1P v ty d) (instantiate1P v body (d + 1)) m
  | .letE ty val body .. =>
    mkLetE (instantiate1P v ty d) (instantiate1P v val d) (instantiate1P v body (d + 1))
  | .proj sn i sub .. => mkProj sn i (instantiate1P v sub d)

theorem instantiate1P_cut {v e : Expr} {d : Nat} (h : e.bvarB ≤ d) :
    instantiate1P v e d = e := by
  rw [instantiate1P.eq_def]; simp [h]

/-- The child step of `instantiate1XP`: the cutoff, the compound test,
the exclusivity read. -/
@[inline] def enter1P (v : @& Expr) (e : @& Expr) (d : Nat) (memo : MemoXP (instantiate1P v))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (instantiate1P v) e d)) :
    Squash (ResXP (instantiate1P v) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiate1P_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut

/-- The walk of `instantiate1C` (the node is past the cutoff: the
wrapper and `enter1P` test it). -/
def instantiate1XP (v : @& Expr) (memo : MemoXP (instantiate1P v)) (e : @& Expr) (d : Nat)
    (hcut : ¬ e.bvarB ≤ d) : Squash (ResXP (instantiate1P v) e d) :=
  match e with
  | .bvar i .. =>
    Squash.mk (⟨if i = d then v else if i > d then Expr.mkBvar (i - 1) else .bvar i,
      by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enter1P v f d memo (fun h => instantiate1XP v memo f d h) |>.lift fun (⟨f', hf⟩, memo) =>
    enter1P v a d memo (fun h => instantiate1XP v memo a d h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [instantiate1P]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enter1P v ty d memo (fun h => instantiate1XP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enter1P v body (d + 1) memo (fun h => instantiate1XP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by rw [instantiate1P]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enter1P v ty d memo (fun h => instantiate1XP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enter1P v body (d + 1) memo (fun h => instantiate1XP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by rw [instantiate1P]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enter1P v ty d memo (fun h => instantiate1XP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enter1P v val d memo (fun h => instantiate1XP v memo val d h) |>.lift fun (⟨v', hv⟩, memo) =>
    enter1P v body (d + 1) memo (fun h => instantiate1XP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [instantiate1P]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enter1P v sub d memo (fun h => instantiate1XP v memo sub d h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [instantiate1P]; simp [hcut, hs, mkProj]⟩, memo)

/-- The cached `Expr.instantiate1`: the cutoff, then the walk. -/
def instantiate1C (e : @& Expr) (v : Expr) (d : Nat := 0) : Expr :=
  if hcut : e.bvarB ≤ d then e else
  resTerm (instantiate1XP v none e d hcut)

/-- The plain descent of `instantiateListC`: the reference
`instantiateListXP` carries its own proof against. -/
def instantiateListP (vs : Array Expr) (e : Expr) (k : Nat) (d : Nat) : Expr :=
  if k = 0 then e
  else if e.bvarB ≤ d then e
  else
    match e with
    | .bvar i .. =>
      if i < d then e
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[i - d]
          if i - d = 0 || w.bvarB ≤ d then w
          else instantiateListP vs w (i - d) d
        else e
      else Expr.mkBvar (i - k)
    | .fvar .. | .sort .. | .const .. | .lit .. => e
    | .app f a .. => mkApp (instantiateListP vs f k d) (instantiateListP vs a k d)
    | .lam ty body m .. => mkLam (instantiateListP vs ty k d) (instantiateListP vs body k (d + 1)) m
    | .forallE ty body m .. =>
      mkForallE (instantiateListP vs ty k d) (instantiateListP vs body k (d + 1)) m
    | .letE ty val body .. =>
      mkLetE (instantiateListP vs ty k d) (instantiateListP vs val k d) (instantiateListP vs body k (d + 1))
    | .proj sn i sub .. => mkProj sn i (instantiateListP vs sub k d)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

theorem instantiateListP_cut {vs : Array Expr} {e : Expr} {k d : Nat} (h : e.bvarB ≤ d) :
    instantiateListP vs e k d = e := by
  rw [instantiateListP.eq_def]; simp [h]

/-- (Task #316, the pointer-keyed twin.) The child step of `instantiateListXP` (`k` is the parent's live prefix). -/
@[inline] def enterListP (vs : @& Array Expr) (e : @& Expr) (k d : Nat)
    (memo : MemoXP (fun e d => instantiateListP vs e k d))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (fun e d => instantiateListP vs e k d) e d)) :
    Squash (ResXP (fun e d => instantiateListP vs e k d) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiateListP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut

/-- The walk of the bulk instantiation.  The `bvar` arm's re-entry at
a replacement runs under a FRESH memo: it is the one place the live
prefix `k` shrinks, and `k` is not part of the key. -/
def instantiateListXP (vs : @& Array Expr) (k : Nat) (memo : MemoXP (fun e d => instantiateListP vs e k d))
    (e : @& Expr) (d : Nat) (hk : ¬ k = 0) (hcut : ¬ e.bvarB ≤ d) :
    Squash (ResXP (fun e d => instantiateListP vs e k d) e d) :=
  match e with
  | .bvar i .. =>
    if hi : i < d then Squash.mk (⟨.bvar i, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi]⟩, memo)
    else if _h : i - d < k then
      if h : i - d < vs.size then
        let w := vs[i - d]
        if h0 : i - d = 0 || w.bvarB ≤ d then
          Squash.mk (⟨w, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0]⟩, memo)
        else
          have h0' : ¬ i - d = 0 ∧ ¬ w.bvarB ≤ d := by
            simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or] using h0
          instantiateListXP vs (i - d) none w d h0'.1 h0'.2 |>.lift fun (⟨r, hr⟩, _) =>
          Squash.mk (⟨r, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0, hr]⟩, memo)
      else Squash.mk (⟨.bvar i, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h, h]⟩, memo)
    else Squash.mk (⟨Expr.mkBvar (i - k), by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut]⟩, memo)
  | .app f a .. =>
    enterListP vs f k d memo (fun h => instantiateListXP vs k memo f d hk h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterListP vs a k d memo (fun h => instantiateListXP vs k memo a d hk h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterListP vs ty k d memo (fun h => instantiateListXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterListP vs body k (d + 1) memo (fun h => instantiateListXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterListP vs ty k d memo (fun h => instantiateListXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterListP vs body k (d + 1) memo (fun h => instantiateListXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterListP vs ty k d memo (fun h => instantiateListXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterListP vs val k d memo (fun h => instantiateListXP vs k memo val d hk h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterListP vs body k (d + 1) memo (fun h => instantiateListXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterListP vs sub k d memo (fun h => instantiateListXP vs k memo sub d hk h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hs, mkProj]⟩, memo)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

/-- The cached `Expr.instantiateList` (bulk): the cutoff, then the walk. -/
def instantiateListC (e : @& Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  match vs with
  | [] => e
  | v :: vs' =>
    let a := (v :: vs').toArray
    if hcut : e.bvarB ≤ d then e
    else resTerm (instantiateListXP a a.size none e d (by simp [a]) hcut)

/-- The plain descent of `instantiateRev` (as `instantiateListP` on
the reversed array): the reference of `instantiateRevXP`. -/
def instantiateRevP (vs : Array Expr) (e : Expr) (k : Nat) (d : Nat) : Expr :=
  if k = 0 then e
  else if e.bvarB ≤ d then e
  else
    match e with
    | .bvar i .. =>
      if i < d then e
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[vs.size - 1 - (i - d)]'(by omega)
          if i - d = 0 || w.bvarB ≤ d then w
          else instantiateRevP vs w (i - d) d
        else e
      else Expr.mkBvar (i - k)
    | .fvar .. | .sort .. | .const .. | .lit .. => e
    | .app f a .. => mkApp (instantiateRevP vs f k d) (instantiateRevP vs a k d)
    | .lam ty body m .. => mkLam (instantiateRevP vs ty k d) (instantiateRevP vs body k (d + 1)) m
    | .forallE ty body m .. =>
      mkForallE (instantiateRevP vs ty k d) (instantiateRevP vs body k (d + 1)) m
    | .letE ty val body .. =>
      mkLetE (instantiateRevP vs ty k d) (instantiateRevP vs val k d) (instantiateRevP vs body k (d + 1))
    | .proj sn i sub .. => mkProj sn i (instantiateRevP vs sub k d)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

theorem instantiateRevP_cut {vs : Array Expr} {e : Expr} {k d : Nat} (h : e.bvarB ≤ d) :
    instantiateRevP vs e k d = e := by
  rw [instantiateRevP.eq_def]; simp [h]

/-- (Task #316, the pointer-keyed twin.) The child step of `instantiateRevXP` (`k` is the parent's live prefix). -/
@[inline] def enterRevP (vs : @& Array Expr) (e : @& Expr) (k d : Nat)
    (memo : MemoXP (fun e d => instantiateRevP vs e k d))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (fun e d => instantiateRevP vs e k d) e d)) :
    Squash (ResXP (fun e d => instantiateRevP vs e k d) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiateRevP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut

/-- The walk of the bulk instantiation on a reversed accumulator.  The
`bvar` arm's re-entry at a replacement runs under a FRESH memo: it is
the one place the live prefix `k` shrinks, and `k` is not part of the
key. -/
def instantiateRevXP (vs : @& Array Expr) (k : Nat) (memo : MemoXP (fun e d => instantiateRevP vs e k d))
    (e : @& Expr) (d : Nat) (hk : ¬ k = 0) (hcut : ¬ e.bvarB ≤ d) :
    Squash (ResXP (fun e d => instantiateRevP vs e k d) e d) :=
  match e with
  | .bvar i .. =>
    if hi : i < d then Squash.mk (⟨.bvar i, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi]⟩, memo)
    else if _h : i - d < k then
      if h : i - d < vs.size then
        let w := vs[vs.size - 1 - (i - d)]'(by omega)
        if h0 : i - d = 0 || w.bvarB ≤ d then
          Squash.mk (⟨w, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0]⟩, memo)
        else
          have h0' : ¬ i - d = 0 ∧ ¬ w.bvarB ≤ d := by
            simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or] using h0
          instantiateRevXP vs (i - d) none w d h0'.1 h0'.2 |>.lift fun (⟨r, hr⟩, _) =>
          Squash.mk (⟨r, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0, hr]⟩, memo)
      else Squash.mk (⟨.bvar i, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi, _h, h]⟩, memo)
    else Squash.mk (⟨Expr.mkBvar (i - k), by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi, _h]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut]⟩, memo)
  | .app f a .. =>
    enterRevP vs f k d memo (fun h => instantiateRevXP vs k memo f d hk h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterRevP vs a k d memo (fun h => instantiateRevXP vs k memo a d hk h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterRevP vs ty k d memo (fun h => instantiateRevXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRevP vs body k (d + 1) memo (fun h => instantiateRevXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterRevP vs ty k d memo (fun h => instantiateRevXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRevP vs body k (d + 1) memo (fun h => instantiateRevXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterRevP vs ty k d memo (fun h => instantiateRevXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRevP vs val k d memo (fun h => instantiateRevXP vs k memo val d hk h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterRevP vs body k (d + 1) memo (fun h => instantiateRevXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterRevP vs sub k d memo (fun h => instantiateRevXP vs k memo sub d hk h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hs, mkProj]⟩, memo)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

/-- Bulk instantiation on a reversed accumulator array: the cutoffs,
then the walk. -/
def instantiateRev (e : @& Expr) (vs : Array Expr) (d : Nat := 0) : Expr :=
  if hk : vs.size = 0 then e
  else if hcut : e.bvarB ≤ d then e
  else resTerm (instantiateRevXP vs vs.size none e d hk hcut)

/-! ## Abstraction -/

/-- The plain descent of `abstract1C`: the reference of
`abstract1XP`. -/
def abstract1P (d : Nat) (e : Expr) (k : Nat) : Expr :=
  if e.fvarB ≤ d then e else
  match e with
  | .fvar idx .. => if idx = d then Expr.mkBvar k else e
  | .bvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (abstract1P d f k) (abstract1P d a k)
  | .lam ty body m .. => mkLam (abstract1P d ty k) (abstract1P d body (k + 1)) m
  | .forallE ty body m .. => mkForallE (abstract1P d ty k) (abstract1P d body (k + 1)) m
  | .letE ty val body .. =>
    mkLetE (abstract1P d ty k) (abstract1P d val k) (abstract1P d body (k + 1))
  | .proj sn i sub .. => mkProj sn i (abstract1P d sub k)

theorem abstract1P_cut {d : Nat} {e : Expr} {k : Nat} (h : e.fvarB ≤ d) :
    abstract1P d e k = e := by
  rw [abstract1P.eq_def]; simp [h]

/-- (Task #316.) The child step of `abstract1XP`: the pointer-keyed twin of `enterAbs1`. -/
@[inline] def enterAbs1P (d : Nat) (e : @& Expr) (k : Nat) (memo : MemoXP (abstract1P d))
    (rec : (hcut : ¬ e.fvarB ≤ d) → Squash (ResXP (abstract1P d) e k)) :
    Squash (ResXP (abstract1P d) e k) :=
  if hcut : e.fvarB ≤ d then Squash.mk (⟨e, (abstract1P_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e k fun _ => rec hcut

/-- The walk of `abstract1C`. -/
def abstract1XP (d : Nat) (memo : MemoXP (abstract1P d)) (e : @& Expr) (k : Nat)
    (hcut : ¬ e.fvarB ≤ d) : Squash (ResXP (abstract1P d) e k) :=
  match e with
  | .fvar idx ty .. =>
    Squash.mk (⟨if idx = d then Expr.mkBvar k else .fvar idx ty,
      by rw [abstract1P]; simp [hcut]⟩, memo)
  | .bvar i .. => Squash.mk (⟨.bvar i, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterAbs1P d f k memo (fun h => abstract1XP d memo f k h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterAbs1P d a k memo (fun h => abstract1XP d memo a k h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [abstract1P]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterAbs1P d ty k memo (fun h => abstract1XP d memo ty k h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbs1P d body (k + 1) memo (fun h => abstract1XP d memo body (k + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by rw [abstract1P]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterAbs1P d ty k memo (fun h => abstract1XP d memo ty k h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbs1P d body (k + 1) memo (fun h => abstract1XP d memo body (k + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by rw [abstract1P]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterAbs1P d ty k memo (fun h => abstract1XP d memo ty k h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbs1P d val k memo (fun h => abstract1XP d memo val k h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterAbs1P d body (k + 1) memo (fun h => abstract1XP d memo body (k + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [abstract1P]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterAbs1P d sub k memo (fun h => abstract1XP d memo sub k h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [abstract1P]; simp [hcut, hs, mkProj]⟩, memo)

/-- The cached `Expr.abstract1`: the cutoff, then the walk. -/
def abstract1C (e : @& Expr) (d : Nat) (k : Nat := 0) : Expr :=
  if hcut : e.fvarB ≤ d then e else
  resTerm (abstract1XP d none e k hcut)

/-- The plain descent of `abstractRangeC`: the reference of
`abstractRangeXP`. -/
def abstractRangeP (d k : Nat) (e : Expr) (c : Nat) : Expr :=
  if e.fvarB ≤ d then e else
  match e with
  | .fvar idx .. =>
    if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx)) else e
  | .bvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (abstractRangeP d k f c) (abstractRangeP d k a c)
  | .lam ty body m .. =>
    mkLam (abstractRangeP d k ty c) (abstractRangeP d k body (c + 1)) m
  | .forallE ty body m .. =>
    mkForallE (abstractRangeP d k ty c) (abstractRangeP d k body (c + 1)) m
  | .letE ty val body .. =>
    mkLetE (abstractRangeP d k ty c) (abstractRangeP d k val c)
      (abstractRangeP d k body (c + 1))
  | .proj sn i sub .. => mkProj sn i (abstractRangeP d k sub c)

theorem abstractRangeP_cut {d k : Nat} {e : Expr} {c : Nat} (h : e.fvarB ≤ d) :
    abstractRangeP d k e c = e := by
  rw [abstractRangeP.eq_def]; simp [h]

/-- (Task #316.) The child step of `abstractRangeXP`: the pointer-keyed twin of `enterAbsR`. -/
@[inline] def enterAbsRP (d k : Nat) (e : @& Expr) (c : Nat) (memo : MemoXP (abstractRangeP d k))
    (rec : (hcut : ¬ e.fvarB ≤ d) → Squash (ResXP (abstractRangeP d k) e c)) :
    Squash (ResXP (abstractRangeP d k) e c) :=
  if hcut : e.fvarB ≤ d then Squash.mk (⟨e, (abstractRangeP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e c fun _ => rec hcut

/-- The walk of `abstractRangeC`. -/
def abstractRangeXP (d k : Nat) (memo : MemoXP (abstractRangeP d k)) (e : @& Expr) (c : Nat)
    (hcut : ¬ e.fvarB ≤ d) : Squash (ResXP (abstractRangeP d k) e c) :=
  match e with
  | .fvar idx ty .. =>
    Squash.mk (⟨if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx))
        else .fvar idx ty,
      by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .bvar i .. => Squash.mk (⟨.bvar i, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterAbsRP d k f c memo (fun h => abstractRangeXP d k memo f c h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterAbsRP d k a c memo (fun h => abstractRangeXP d k memo a c h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [abstractRangeP]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterAbsRP d k ty c memo (fun h => abstractRangeXP d k memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbsRP d k body (c + 1) memo (fun h => abstractRangeXP d k memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by rw [abstractRangeP]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterAbsRP d k ty c memo (fun h => abstractRangeXP d k memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbsRP d k body (c + 1) memo (fun h => abstractRangeXP d k memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by rw [abstractRangeP]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterAbsRP d k ty c memo (fun h => abstractRangeXP d k memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbsRP d k val c memo (fun h => abstractRangeXP d k memo val c h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterAbsRP d k body (c + 1) memo (fun h => abstractRangeXP d k memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [abstractRangeP]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterAbsRP d k sub c memo (fun h => abstractRangeXP d k memo sub c h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [abstractRangeP]; simp [hcut, hs, mkProj]⟩, memo)

/-- The cached `Expr.abstractRange` (`k = 0` is the identity and skips
the traversal, as in the arena): the cutoff, then the walk. -/
def abstractRangeC (e : @& Expr) (d k : Nat) (c : Nat := 0) : Expr :=
  match k with
  | 0 => e
  | _ + 1 =>
    if hcut : e.fvarB ≤ d then e else
    resTerm (abstractRangeXP d k none e c hcut)

/-! ## Level instantiation -/

/-- The plain descent of `instLevelParams`: the reference of
`instLevelParamsXP`. -/
def instLevelParamsP (ks : List Name) (us : List Level) (e : Expr) : Expr :=
  if !e.hasLP then e else
  match e with
  | .bvar .. | .lit .. => e
  | .sort u .. => mkSort (Level.subst ks us u)
  | .const n vs .. => mkConst n (vs.map (Level.subst ks us))
  | .fvar idx ty .. => mkFVar idx (instLevelParamsP ks us ty)
  | .app f a .. => mkApp (instLevelParamsP ks us f) (instLevelParamsP ks us a)
  | .lam ty body m .. =>
    mkLam (instLevelParamsP ks us ty) (instLevelParamsP ks us body) ⟨Level.substPW ks us m.pw⟩
  | .forallE ty body m .. =>
    mkForallE (instLevelParamsP ks us ty) (instLevelParamsP ks us body)
      ⟨Level.substPW ks us m.pw⟩
  | .letE ty val body .. =>
    mkLetE (instLevelParamsP ks us ty) (instLevelParamsP ks us val)
      (instLevelParamsP ks us body)
  | .proj s i sub .. => mkProj s i (instLevelParamsP ks us sub)

theorem instLevelParamsP_cut {ks : List Name} {us : List Level} {e : Expr}
    (h : (!e.hasLP) = true) : instLevelParamsP ks us e = e := by
  rw [instLevelParamsP.eq_def]; simp [h]

/-- The child step of `instLevelParamsXP`: the cutoff, then the
exclusivity read on EVERY node past it — there is no compound test
here, since a `const` with level parameters is a `Level.subst` per
occurrence and worth recording. -/
@[inline] def enterLPP (ks : @& List Name) (us : @& List Level) (e : @& Expr)
    (memo : MemoXP0 (instLevelParamsP ks us))
    (rec : (hcut : ¬ (!e.hasLP) = true) → Squash (ResXP0 (instLevelParamsP ks us) e)) :
    Squash (ResXP0 (instLevelParamsP ks us) e) :=
  if hcut : (!e.hasLP) = true then Squash.mk (⟨e, (instLevelParamsP_cut hcut).symm⟩, memo)
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e fun _ => rec hcut

/-- The walk of `instLevelParams`. -/
def instLevelParamsXP (ks : @& List Name) (us : @& List Level)
    (memo : MemoXP0 (instLevelParamsP ks us)) (e : @& Expr) (hcut : ¬ (!e.hasLP) = true) :
    Squash (ResXP0 (instLevelParamsP ks us) e) :=
  match e with
  | .bvar i .. => Squash.mk (⟨.bvar i, by rw [instLevelParamsP.eq_def, if_neg hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [instLevelParamsP.eq_def, if_neg hcut]⟩, memo)
  | .sort u .. =>
    Squash.mk (⟨mkSort (Level.subst ks us u), by rw [instLevelParamsP.eq_def, if_neg hcut]⟩, memo)
  | .const n vs .. =>
    Squash.mk (⟨mkConst n (vs.map (Level.subst ks us)),
      by rw [instLevelParamsP.eq_def, if_neg hcut]⟩, memo)
  | .fvar idx ty .. =>
    enterLPP ks us ty memo (fun h => instLevelParamsXP ks us memo ty h) |>.lift fun (⟨t, ht⟩, memo) =>
    Squash.mk (⟨mkFVar idx t, by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [ht, mkFVar]⟩, memo)
  | .app f a .. =>
    enterLPP ks us f memo (fun h => instLevelParamsXP ks us memo f h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterLPP ks us a memo (fun h => instLevelParamsXP ks us memo a h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterLPP ks us ty memo (fun h => instLevelParamsXP ks us memo ty h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLPP ks us body memo (fun h => instLevelParamsXP ks us memo body h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' ⟨Level.substPW ks us m.pw⟩,
      by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterLPP ks us ty memo (fun h => instLevelParamsXP ks us memo ty h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLPP ks us body memo (fun h => instLevelParamsXP ks us memo body h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' ⟨Level.substPW ks us m.pw⟩,
      by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterLPP ks us ty memo (fun h => instLevelParamsXP ks us memo ty h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLPP ks us val memo (fun h => instLevelParamsXP ks us memo val h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterLPP ks us body memo (fun h => instLevelParamsXP ks us memo body h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterLPP ks us sub memo (fun h => instLevelParamsXP ks us memo sub h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [hs, mkProj]⟩, memo)

/-- The cached `Expr.instantiateLevelParams`: the cutoff, then the
walk. -/
def instLevelParams (ks : List Name) (us : List Level) (e : @& Expr) : Expr :=
  if hcut : (!e.hasLP) = true then e else
  resTerm (instLevelParamsXP ks us none e hcut)

/-- The cached `ProjEntry.typeAt`: the same two instantiations through
the memoized, **sharing-preserving** `instLevelParams` and
`instantiateListC` (`ProjEntry.typeAtI_eq`, `ConLeche/Verify/Cached/
OpsC.lean`, is the equation).

The executable `.proj` inference clause used to call the spec's
`ProjEntry.typeAt` directly — legitimate as a *value* (`Expr = Expr`)
but not as a *computation*: `Expr.instantiateList` is the unmemoized
tree walk, and its `bvar` arm re-traverses the replacement (`vs[j - d]`
under `vs.take (j - d)`), so every occurrence of the subject and of
every parameter in the field type came back as a fresh **tree copy**
of a term that was a DAG.  On a projection chain over a Mathlib
carrier (`(Classical.choice …).ColimitCocone.0.Cocone.0.CommRingCat.0`)
the copies nest, and at `AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`
(subject tree 3.9 · 10⁸ nodes on a 3 106-node DAG) the copy alone is
the out-of-memory — DESIGN.md "The affine frontier". -/
def _root_.ConLeche.ProjEntry.typeAtI (entry : ProjEntry) (us : List Level)
    (targs : List Expr) (pe : Expr) : Expr :=
  instantiateListC (instLevelParams entry.levelParams us entry.body)
    (pe :: targs.reverse)

/-! ## The `Bool`-valued walks

The scope, definedness and resolution guards are the substitution
walks' design over a `Bool`, and the tree has ONE memo discipline for
every traversal memo in it (task #319; `Expr.beqGoX` is the third
instance).  Each guard used to create a `Std.HashMap` per call, keyed
STRUCTURALLY on the node (and, for the scope walk, the cursor), and
record EVERY node it decided — a probe that compared the stored node
with the query by `Expr.beq`, and an entry for every leaf.  Instead:

* **memoise only what is shared** — at every compound child past the
  cutoff, `withExclusive` (`ConLeche/Kernel/Exclusive.lean`) on the
  node (borrowed); an exclusive node is descended with the memo
  untouched (no key, no probe, no insert), a shared one is probed and
  recorded on a miss.  A node with one reference cannot be reached
  again, so recording it is pure loss;
* **key by address and cursor** — `withPtrAddr` (`Expr.withAddr`) at
  the top of the shared step, packed with the cursor into one `Nat`
  (`pkey`), under the mixing hash of `PKey`.  No structural hash and
  no `Expr.beq` on any probe;
* **validate a hit by pointer identity** — `Expr.ptrDec` on the
  stored node against the current one, plus a cursor compare.  The
  address is never trusted: a wrong key can only cost a descent,
  never a value;
* **every entry is self-proving** — a `BEnt` carries its node, its
  cursor, its decision and the proof `val = s node depth`, so there
  is **no table invariant** and no lemma about the table at all;
* **no cutoff beyond the walk's own** (`fvarB`, `hasLP`, and none at
  all for `constsResolveFC`): every shared compound node the walk
  meets is memoised, for as long as the call lasts.

A walk's result is a `Squash` of `{ r : Bool // r = <the plain
descent> }` beside the memo — a `Subsingleton`, which is the
obligation `withExclusive` and `withPtrAddr` each ask of their
continuation — and the wrapper reads the decision off it with
`resBool`.  The plain descents (`*P`) carry the cutoff and are proved
equal to their `ConLeche.Expr` specifications in
`ConLeche/Verify/Cached/{OpsC,GuardsC}.lean`.  **The borrowed
parameter is a requirement, not an optimisation**, for the reason the
substitution walks' section states.

The one walk of this file that is NOT of this shape is
`fvarLeavesGoC`, whose memo is a visited SET; its docstring says
why. -/

/-- The nodes a `Bool` memo entry can save a descent of: the compound
nodes, and `fvar` — every walk of this section descends into the
ANNOTATION, so the cached fvar range does not decide an `fvar` node. -/
@[inline] def isCompoundF : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. | .fvar .. => true
  | _ => false

/-- A `Bool` memo entry: the node it was decided for, the cursor, the
decision, and the proof — the entry is its own invariant (`PEnt` with
`Bool` in place of the rebuilt term). -/
structure BEnt (s : Expr → Nat → Bool) where
  node : Expr
  depth : Nat
  val : Bool
  eq : val = s node depth

/-- A validated hit: the cursor compares equal and the stored node IS
the current one (by pointer at runtime — `Expr.ptrDec` — structurally
in the model); then the entry's proof is the walk's. -/
@[inline] def BEnt.hit {s : Expr → Nat → Bool} {β : Sort u} (p : BEnt s) (e : Expr) (c : Nat)
    (k : { r : Bool // r = s e c } → β) (miss : Unit → β) : β :=
  if hd : p.depth = c then
    match Expr.ptrDec p.node e with
    | isTrue hn => k ⟨p.val, by rw [p.eq, hn, hd]⟩
    | isFalse _ => miss ()
  else miss ()

/-- The `Bool` table: the packed address-and-cursor key under the
mixing hash of `PKey`. -/
abbrev BTab (s : Expr → Nat → Bool) := Std.HashMap PKey (BEnt s)

/-- The pointer-keyed `Bool` memo: absent until the first shared
compound node. -/
abbrev MemoB (s : Expr → Nat → Bool) := Option (BTab s)

/-- A `Bool` walk's result: the decision, fixed by its proof, beside
the memo. -/
abbrev ResB (s : Expr → Nat → Bool) (e : Expr) (c : Nat) :=
  { r : Bool // r = s e c } × MemoB s

/-- The record: the entry under its packed key, in the table or in a
fresh one. -/
@[inline] def MemoB.insert {s : Expr → Nat → Bool} (memo : MemoB s) (key : Nat)
    (p : BEnt s) : MemoB s :=
  match memo with
  | none => some (({} : BTab s).insert ⟨key⟩ p)
  | some m => some (m.insert ⟨key⟩ p)

/-- The shared-node step over the pointer-keyed `Bool` memo: the
address read, the probe, the validated hit — else the descent and the
record under the key read BEFORE the descent (`MemoXP.shared`
verbatim, with `BEnt` for `PEnt`). -/
@[inline] def MemoB.shared {s : Expr → Nat → Bool} (memo : MemoB s) (e : Expr) (c : Nat)
    (rec : Unit → Squash (ResB s e c)) : Squash (ResB s e c) :=
  withAddr e fun addr =>
  let key := pkey addr c
  match memo with
  | none => Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
      Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, c, r, hr⟩)
  | some m =>
    match m[(⟨key⟩ : PKey)]? with
    | some p => p.hit e c (fun r => Squash.mk (r, memo)) fun _ =>
        Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
          Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, c, r, hr⟩)
    | none => Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
        Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, c, r, hr⟩)

/-- The cursor-free instance: the cursored `Bool` memo at cursor
`0`. -/
abbrev MemoB0 (s : Expr → Bool) := MemoB (fun e _ => s e)

abbrev ResB0 (s : Expr → Bool) (e : Expr) := { r : Bool // r = s e } × MemoB0 s

@[inline] def MemoB0.shared {s : Expr → Bool} (memo : MemoB0 s) (e : Expr)
    (rec : Unit → Squash (ResB0 s e)) : Squash (ResB0 s e) :=
  MemoB.shared (s := fun e _ => s e) memo e 0 rec

/-- The decision of a `Bool` walk's result (the quotient lifts: the
decision is fixed by its subtype). -/
@[inline] def resBool {c : Bool} {M : Type} (s : Squash ({ r : Bool // r = c } × M)) : Bool :=
  Quotient.lift (fun p => p.1.1) (fun p q _ => by rw [p.1.2, q.1.2]) s

/-- What the decision of a `Bool` walk's result is: the value its
subtype names.  Whatever the exclusivity reads and the addresses were
along the way. -/
theorem resBool_eq {c : Bool} {M : Type} (s : Squash ({ r : Bool // r = c } × M)) :
    resBool s = c := by
  induction s using Quotient.ind with
  | _ p => exact p.1.2

/-! ## Scope queries -/

/-- The plain descent of `wscopedBC`: the reference the walk is
verified against (`wscopedBP_spec`, `ConLeche/Verify/Cached/OpsC.lean`,
is the equation to `Expr.wscopedB`).  The cursor is the node's second
argument, as it is for the substitution walks — it CHANGES at `fvar`,
where the annotation is entered at the variable's own index, so the
memo key must carry it. -/
def wscopedBP (e : Expr) (d : Nat) : Bool :=
  if e.fvarB == 0 then true else
  match e with
  | .bvar .. | .sort .. | .const .. | .lit .. => true
  | .fvar idx ty .. => idx < d && wscopedBP ty idx
  | .app f a .. => wscopedBP f d && wscopedBP a d
  | .lam ty body _ .. | .forallE ty body _ .. => wscopedBP ty d && wscopedBP body d
  | .letE ty val body .. => wscopedBP ty d && wscopedBP val d && wscopedBP body d
  | .proj _ _ sub .. => wscopedBP sub d

theorem wscopedBP_cut {e : Expr} {d : Nat} (h : (e.fvarB == 0) = true) :
    wscopedBP e d = true := by
  rw [wscopedBP.eq_def]; simp [h]

/-- The child step of `wscopedBXP`: the cutoff, the compound test, the
exclusivity read. -/
@[inline] def enterWSP (e : @& Expr) (d : Nat) (memo : MemoB wscopedBP)
    (rec : (hcut : (e.fvarB == 0) = false) → Squash (ResB wscopedBP e d)) :
    Squash (ResB wscopedBP e d) :=
  match hcut : e.fvarB == 0 with
  | true => Squash.mk (⟨true, (wscopedBP_cut hcut).symm⟩, memo)
  | false =>
    if !isCompoundF e then rec hcut
    else withExcl e fun excl =>
      if excl then rec hcut else memo.shared e d fun _ => rec hcut

/-- The walk of `wscopedBC` (the node is past the cutoff: the wrapper
and `enterWSP` test it). -/
def wscopedBXP (memo : MemoB wscopedBP) (e : @& Expr) (d : Nat)
    (hcut : (e.fvarB == 0) = false) : Squash (ResB wscopedBP e d) :=
  match e with
  | .bvar .. => Squash.mk (⟨true, by rw [wscopedBP]; simp [hcut]⟩, memo)
  | .sort .. => Squash.mk (⟨true, by rw [wscopedBP]; simp [hcut]⟩, memo)
  | .const .. => Squash.mk (⟨true, by rw [wscopedBP]; simp [hcut]⟩, memo)
  | .lit .. => Squash.mk (⟨true, by rw [wscopedBP]; simp [hcut]⟩, memo)
  | .fvar idx ty .. =>
    if hidx : idx < d then
      enterWSP ty idx memo (fun h => wscopedBXP memo ty idx h)
        |>.lift fun (⟨rt, ht⟩, memo) =>
      Squash.mk (⟨rt, by rw [wscopedBP]; simp [hcut, hidx, ← ht]⟩, memo)
    else
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, hidx]⟩, memo)
  | .app f a .. =>
    enterWSP f d memo (fun h => wscopedBXP memo f d h) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      enterWSP a d memo (fun h => wscopedBXP memo a d h) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [wscopedBP]; simp [hcut, ← hf, ← ha]⟩, memo)
    | false, hf =>
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← hf]⟩, memo)
  | .lam ty body _ .. =>
    enterWSP ty d memo (fun h => wscopedBXP memo ty d h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterWSP body d memo (fun h => wscopedBXP memo body d h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [wscopedBP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← ht]⟩, memo)
  | .forallE ty body _ .. =>
    enterWSP ty d memo (fun h => wscopedBXP memo ty d h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterWSP body d memo (fun h => wscopedBXP memo body d h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [wscopedBP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← ht]⟩, memo)
  | .letE ty val body .. =>
    enterWSP ty d memo (fun h => wscopedBXP memo ty d h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterWSP val d memo (fun h => wscopedBXP memo val d h)
        |>.lift fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        enterWSP body d memo (fun h => wscopedBXP memo body d h)
          |>.lift fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [wscopedBP]; simp [hcut, ← ht, ← hv, ← hb]⟩, memo)
      | false, hv =>
        Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← ht, ← hv]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← ht]⟩, memo)
  | .proj _ _ sub .. =>
    enterWSP sub d memo (fun h => wscopedBXP memo sub d h) |>.lift fun (⟨rs, hs⟩, memo) =>
    Squash.mk (⟨rs, by rw [wscopedBP]; simp [hcut, ← hs]⟩, memo)

/-- The cached `Expr.wscopedB d` (one memoized DAG walk): the cutoff,
then the walk. -/
def wscopedBC (d : Nat) (e : Expr) : Bool :=
  match hcut : e.fvarB == 0 with
  | true => true
  | false => resBool (wscopedBXP none e d hcut)

/-- Core of `fvarLeavesC` (memoized set accumulation).

**The one walk of the tree whose memo is not the `withExclusive`
idiom, and why** (task #319, which put that idiom in front of every
other traversal memo — the substitution walks, `Expr.beqGoX`, and the
`Bool`-valued walks above).  This memo is a visited SET, and its
entries are `Unit`: what an entry means is *"this node's leaves are
already in `acc`"* — a statement about the ACCUMULATOR, which changes
at every step, and about the walk's own descent path, not about the
node.  It is the verification's `SeenInv`
(`ConLeche/Verify/Cached/GuardsC.lean`): every key of `seen` either
has all its leaves in `acc` already or is *gray* (being processed).
An entry carrying no value cannot prove itself, so this memo needs a
table invariant — which is exactly what the idiom removes.

The self-proving alternative is an entry carrying the node's own leaf
list, `{ r : List (Nat × Expr) // r = Expr.fvarLeaves e }`, appended
at the parent.  That closes as a proof — it is the `Bool` walks'
shape with a list in place of the decision — but it is the wrong
ALGORITHM: `Expr.fvarLeaves` concatenates at every compound node
(`ConLeche/Kernel/ExprOps.lean`), so a node's own list is the leaf
list of its TREE unfolding, and materialising one per entry is
precisely the blow-up the `seen` set exists to avoid (an `app e e`
ladder gives the root a list of `2^k` elements on `k` nodes; the
affine frontier's 3.9 · 10⁸-node unfolding of a 3 106-node DAG is the
real instance).  Weakening the subtype to a membership
characterization — all the one consumer, `leafMem`, needs — closes
just as easily and does not shrink the lists: siblings still
concatenate, and deduplicating at each node reintroduces a per-node
set, i.e. the table the entry was meant to replace.  So the
accumulator is the algorithm here, and the accumulator is what cannot
be carried in a type.  DESIGN.md, task #319, records this as the one
permitted exception and the open question behind it. -/
def fvarLeavesGoC (acc : List (Nat × Expr))
    (seen : Std.HashMap Expr Unit) (e : Expr) :
    List (Nat × Expr) × Std.HashMap Expr Unit :=
  if e.fvarB == 0 then (acc, seen) else
  match seen[e]? with
  | some _ => (acc, seen)
  | none =>
    let seen := seen.insert e ()
    match e with
    | .bvar .. | .sort .. | .const .. | .lit .. => (acc, seen)
    | .fvar idx ty .. => fvarLeavesGoC ((idx, ty) :: acc) seen ty
    | .app f a .. =>
      let (acc, seen) := fvarLeavesGoC acc seen f
      fvarLeavesGoC acc seen a
    | .lam ty body _ .. | .forallE ty body _ .. =>
      let (acc, seen) := fvarLeavesGoC acc seen ty
      fvarLeavesGoC acc seen body
    | .letE ty val body .. =>
      let (acc, seen) := fvarLeavesGoC acc seen ty
      let (acc, seen) := fvarLeavesGoC acc seen val
      fvarLeavesGoC acc seen body
    | .proj _ _ sub .. => fvarLeavesGoC acc seen sub

/-- The reachable `fvar` leaves (hereditarily through annotations). -/
def fvarLeavesC (e : Expr) : List (Nat × Expr) :=
  (fvarLeavesGoC [] {} e).1

/-- Is `(idx, ty)` in the base leaf list?  Compares the annotation
with `Expr.beq` (pointer-first). -/
def leafMem : List (Nat × Expr) → Nat → Expr → Bool
  | [], _, _ => false
  | (i, t) :: rest, idx, ty =>
    (i == idx && t == ty) || leafMem rest idx ty

/-- The plain descent of the leaf-subset walk: the reference the walk
is verified against (`leavesSubP_spec`,
`ConLeche/Verify/Cached/GuardsC.lean`, is the equation to the
`Expr`-level leaf-subset boolean).  `leafMem` is the membership
test (task #86). -/
def leavesSubP (bl : List (Nat × Expr)) (e : Expr) : Bool :=
  if e.fvarB == 0 then true else
  match e with
  | .bvar .. | .sort .. | .const .. | .lit .. => true
  | .fvar idx ty .. => leafMem bl idx ty && leavesSubP bl ty
  | .app f a .. => leavesSubP bl f && leavesSubP bl a
  | .lam ty body _ .. | .forallE ty body _ .. => leavesSubP bl ty && leavesSubP bl body
  | .letE ty val body .. =>
    leavesSubP bl ty && leavesSubP bl val && leavesSubP bl body
  | .proj _ _ sub .. => leavesSubP bl sub

theorem leavesSubP_cut {bl : List (Nat × Expr)} {e : Expr} (h : (e.fvarB == 0) = true) :
    leavesSubP bl e = true := by
  rw [leavesSubP.eq_def]; simp [h]

/-- The child step of `leavesSubXP`: the cutoff, the compound test,
the exclusivity read. -/
@[inline] def enterLSub (bl : @& List (Nat × Expr)) (e : @& Expr)
    (memo : MemoB0 (leavesSubP bl))
    (rec : (hcut : (e.fvarB == 0) = false) → Squash (ResB0 (leavesSubP bl) e)) :
    Squash (ResB0 (leavesSubP bl) e) :=
  match hcut : e.fvarB == 0 with
  | true => Squash.mk (⟨true, (leavesSubP_cut hcut).symm⟩, memo)
  | false =>
    if !isCompoundF e then rec hcut
    else withExcl e fun excl =>
      if excl then rec hcut else memo.shared e fun _ => rec hcut

/-- The leaf-subset walk (the node is past the cutoff: `leavesSubC`
and `enterLSub` test it). -/
def leavesSubXP (bl : @& List (Nat × Expr)) (memo : MemoB0 (leavesSubP bl))
    (e : @& Expr) (hcut : (e.fvarB == 0) = false) : Squash (ResB0 (leavesSubP bl) e) :=
  match e with
  | .bvar .. => Squash.mk (⟨true, by rw [leavesSubP]; simp [hcut]⟩, memo)
  | .sort .. => Squash.mk (⟨true, by rw [leavesSubP]; simp [hcut]⟩, memo)
  | .const .. => Squash.mk (⟨true, by rw [leavesSubP]; simp [hcut]⟩, memo)
  | .lit .. => Squash.mk (⟨true, by rw [leavesSubP]; simp [hcut]⟩, memo)
  | .fvar idx ty .. =>
    if hlm : leafMem bl idx ty = true then
      enterLSub bl ty memo (fun h => leavesSubXP bl memo ty h)
        |>.lift fun (⟨rt, ht⟩, memo) =>
      Squash.mk (⟨rt, by rw [leavesSubP]; simp [hcut, hlm, ← ht]⟩, memo)
    else
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, hlm]⟩, memo)
  | .app f a .. =>
    enterLSub bl f memo (fun h => leavesSubXP bl memo f h) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      enterLSub bl a memo (fun h => leavesSubXP bl memo a h) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [leavesSubP]; simp [hcut, ← hf, ← ha]⟩, memo)
    | false, hf =>
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← hf]⟩, memo)
  | .lam ty body _ .. =>
    enterLSub bl ty memo (fun h => leavesSubXP bl memo ty h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLSub bl body memo (fun h => leavesSubXP bl memo body h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [leavesSubP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← ht]⟩, memo)
  | .forallE ty body _ .. =>
    enterLSub bl ty memo (fun h => leavesSubXP bl memo ty h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLSub bl body memo (fun h => leavesSubXP bl memo body h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [leavesSubP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← ht]⟩, memo)
  | .letE ty val body .. =>
    enterLSub bl ty memo (fun h => leavesSubXP bl memo ty h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLSub bl val memo (fun h => leavesSubXP bl memo val h)
        |>.lift fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        enterLSub bl body memo (fun h => leavesSubXP bl memo body h)
          |>.lift fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [leavesSubP]; simp [hcut, ← ht, ← hv, ← hb]⟩, memo)
      | false, hv =>
        Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← ht, ← hv]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← ht]⟩, memo)
  | .proj _ _ sub .. =>
    enterLSub bl sub memo (fun h => leavesSubXP bl memo sub h) |>.lift fun (⟨rs, hs⟩, memo) =>
    Squash.mk (⟨rs, by rw [leavesSubP]; simp [hcut, ← hs]⟩, memo)

/-- The cached leaf-subset test: the cutoff, then the walk. -/
def leavesSubC (bl : List (Nat × Expr)) (e : Expr) : Bool :=
  match hcut : e.fvarB == 0 with
  | true => true
  | false => resBool (leavesSubXP bl none e hcut)

/-- The fabrication leaf guard: every `fvar` leaf of `fab` is one of
`base` (short-circuits on `fvar`-free fabrications, `O(1)` off the
cached range). -/
def leafGuard (fab base : Expr) : Bool :=
  !fab.hasFvar || leavesSubC (fvarLeavesC base) fab

/-! ## Telescope operations -/

/-- The `instantiate1C` chain of `Expr.instSpine`. -/
def instSpineChainC : List Expr → Nat → Expr → Expr
  | [], _, e => e
  | a :: as, t, e => instSpineChainC as (t - 1) (instantiate1C e a t)

/-- The cached `Expr.instSpine` (bulk when the spine spans the
telescope context, the chain otherwise). -/
def instSpineC (args : List Expr) (t : Nat) (e : Expr) : Expr :=
  if args.length = t + 1 then instantiateListC e args.reverse 0
  else instSpineChainC args t e

/-- Core of `piResidual` (bulk form, task #50).

Not structural: the `bvar` arm re-enters on the same argument list with
the accumulator flushed.  Measure `(as.length, acc.length)` — the
`forallE` arm consumes an argument, the `bvar` arm keeps the arguments
and empties a nonempty accumulator. -/
def piResidualAcc : List Expr → Expr → List Expr → Option Expr
  | acc, e, [] => some (instantiateListC e acc 0)
  | acc, e, a :: as =>
    match e with
    | .forallE _ b _ .. => piResidualAcc (a :: acc) b as
    | .bvar .. =>
      match acc with
      | [] => none
      | _ :: _ => piResidualAcc [] (instantiateListC e acc 0) (a :: as)
    | _ => none
termination_by acc _ as => (as.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp +arith +decide)
    | (apply Prod.Lex.left; simp +arith +decide)

@[inherit_doc piResidualAcc]
def piResidual (e : Expr) (args : List Expr) : Option Expr :=
  piResidualAcc [] e args

/-! ## Level-parameter definedness (the parsed-index driver's guard) -/

/-- The plain descent of `allLevelParamsDefinedC`: the reference the
walk is verified against (`allLevelParamsDefinedP_spec`,
`ConLeche/Verify/Cached/GuardsC.lean`, is the equation to
`Expr.allLevelParamsDefined`).  The cutoff: a node without a level
parameter is `true` without traversal. -/
def allLevelParamsDefinedP (params : List Name) (e : Expr) : Bool :=
  if e.hasLP then
    match e with
    | .bvar .. | .lit .. => true
    | .sort u .. => Level.allParamsDefined params u
    | .const _ us .. => us.all (Level.allParamsDefined params)
    | .fvar _ ty .. => allLevelParamsDefinedP params ty
    | .app f a .. =>
      allLevelParamsDefinedP params f && allLevelParamsDefinedP params a
    | .lam ty body m .. | .forallE ty body m .. =>
      allLevelParamsDefinedP params ty && allLevelParamsDefinedP params body
        && m.pw.paramsDefined params
    | .letE ty val body .. =>
      allLevelParamsDefinedP params ty && allLevelParamsDefinedP params val
        && allLevelParamsDefinedP params body
    | .proj _ _ sub .. => allLevelParamsDefinedP params sub
  else true

theorem allLevelParamsDefinedP_cut {params : List Name} {e : Expr}
    (h : ¬ e.hasLP = true) : allLevelParamsDefinedP params e = true := by
  rw [allLevelParamsDefinedP.eq_def]; simp [h]

/-- The child step of `allLevelParamsDefinedXP`: the cutoff, the
compound test, the exclusivity read. -/
@[inline] def enterLPD (params : @& List Name) (e : @& Expr)
    (memo : MemoB0 (allLevelParamsDefinedP params))
    (rec : (hcut : e.hasLP = true) →
      Squash (ResB0 (allLevelParamsDefinedP params) e)) :
    Squash (ResB0 (allLevelParamsDefinedP params) e) :=
  if hcut : e.hasLP = true then
    (if !isCompoundF e then rec hcut
     else withExcl e fun excl =>
       if excl then rec hcut else memo.shared e fun _ => rec hcut)
  else Squash.mk (⟨true, (allLevelParamsDefinedP_cut hcut).symm⟩, memo)

/-- The walk of `allLevelParamsDefinedC` (the node is past the
cutoff: the wrapper and `enterLPD` test it). -/
def allLevelParamsDefinedXP (params : @& List Name)
    (memo : MemoB0 (allLevelParamsDefinedP params)) (e : @& Expr)
    (hcut : e.hasLP = true) :
    Squash (ResB0 (allLevelParamsDefinedP params) e) :=
  match e with
  | .bvar .. => Squash.mk (⟨true, by rw [allLevelParamsDefinedP]; simp [hcut]⟩, memo)
  | .lit .. => Squash.mk (⟨true, by rw [allLevelParamsDefinedP]; simp [hcut]⟩, memo)
  | .sort u .. =>
    Squash.mk (⟨Level.allParamsDefined params u,
      by rw [allLevelParamsDefinedP]; simp [hcut]⟩, memo)
  | .const _ us .. =>
    Squash.mk (⟨us.all (Level.allParamsDefined params),
      by rw [allLevelParamsDefinedP]; simp [hcut]⟩, memo)
  | .fvar _ ty .. =>
    enterLPD params ty memo (fun h => allLevelParamsDefinedXP params memo ty h)
      |>.lift fun (⟨rt, ht⟩, memo) =>
    Squash.mk (⟨rt, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht]⟩, memo)
  | .app f a .. =>
    enterLPD params f memo (fun h => allLevelParamsDefinedXP params memo f h)
      |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      enterLPD params a memo (fun h => allLevelParamsDefinedXP params memo a h)
        |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [allLevelParamsDefinedP]; simp [hcut, ← hf, ← ha]⟩, memo)
    | false, hf =>
      Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← hf]⟩, memo)
  | .lam ty body m .. =>
    enterLPD params ty memo (fun h => allLevelParamsDefinedXP params memo ty h)
      |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLPD params body memo (fun h => allLevelParamsDefinedXP params memo body h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb && m.pw.paramsDefined params,
        by rw [allLevelParamsDefinedP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht]⟩, memo)
  | .forallE ty body m .. =>
    enterLPD params ty memo (fun h => allLevelParamsDefinedXP params memo ty h)
      |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLPD params body memo (fun h => allLevelParamsDefinedXP params memo body h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb && m.pw.paramsDefined params,
        by rw [allLevelParamsDefinedP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht]⟩, memo)
  | .letE ty val body .. =>
    enterLPD params ty memo (fun h => allLevelParamsDefinedXP params memo ty h)
      |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLPD params val memo (fun h => allLevelParamsDefinedXP params memo val h)
        |>.lift fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        enterLPD params body memo (fun h => allLevelParamsDefinedXP params memo body h)
          |>.lift fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht, ← hv, ← hb]⟩, memo)
      | false, hv =>
        Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht, ← hv]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht]⟩, memo)
  | .proj _ _ sub .. =>
    enterLPD params sub memo (fun h => allLevelParamsDefinedXP params memo sub h)
      |>.lift fun (⟨rs, hs⟩, memo) =>
    Squash.mk (⟨rs, by rw [allLevelParamsDefinedP]; simp [hcut, ← hs]⟩, memo)

/-- The cached `Expr.allLevelParamsDefined params` (one memoized DAG
walk): the cutoff, then the walk. -/
def allLevelParamsDefinedC (params : List Name) (e : Expr) : Bool :=
  if hcut : e.hasLP = true then resBool (allLevelParamsDefinedXP params none e hcut)
  else true

end ConLeche.Expr
