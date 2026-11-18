import IxVMRefinement.Assembly.FamilyFold

/-! # The family record of a block, member by member

A mutual or nested block `B` is installed with one family record `rb`: a block of recursors
whose recursor at position `k` eliminates the `k`-th member of the block's flattened family, the
block's own types first, then the nested auxiliaries. The circuit checks this of the record a
family check is handed (`KernelModeled::check_recs`: one motive per member of the record, the
recursor at position `k` eliminating motive `k`, the first motives' carriers the block's types
in order). `FamilyOfBlock E B cb ms rb crb rs` states it over a store, on the two records' own
expressions:

* the block is a block of inductives with its projection records, the family record a block of
  recursors with its projection records (`FamBlockRecord`, `FamRecRecord`);
* one recursor per type of the block at least (`covers`; the nested auxiliaries follow), so the
  family record of a non-empty block is non-empty;
* one complete family: each recursor has one motive per member of the record (`motives`);
* the carriers: in every recursor, the motive at a position below the block's type count is
  over the block's member at that position (`carriers`);
* the member correspondence: the recursor at a position below the type count has its major
  premise over the block's member at that position (`major`).

The readers `motiveCarrier` and `majorHead` follow sharing and read a head constant by its
reference, as a family record names the types of its block (a record of its own). They are total,
with fuel. -/

namespace IxVM.Refinement.Binding.FamilyOf

open IxVM.Consistency
open IxVM.Refinement.Typing (FamBlockRecord FamRecRecord)

/-- The fuel of the readers: more than any binder telescope or application spine they walk. -/
def fuel : Nat := 65536

/-- A sharing reference followed, at most `n` times, to a node that is none. -/
def unshare (c : Ixon.Constant) : Nat → Ixon.Expr → Ixon.Expr
  | 0, e => e
  | n + 1, .share i =>
    match c.sharing[i.toNat]? with
    | some e' => unshare c n e'
    | none => .share i
  | _ + 1, e => e

/-- The node of an expression, sharing followed. -/
def node (c : Ixon.Constant) (e : Ixon.Expr) : Ixon.Expr :=
  unshare c (c.sharing.size + 1) e

/-- The body after exactly `n` leading binders. -/
def peel (c : Ixon.Constant) : Nat → Ixon.Expr → Option Ixon.Expr
  | 0, e => some e
  | n + 1, e =>
    match node c e with
    | .all _ b => peel c n b
    | _ => none

/-- The domain of the leading binder. -/
def domOf (c : Ixon.Constant) (e : Ixon.Expr) : Option Ixon.Expr :=
  match node c e with
  | .all d _ => some d
  | _ => none

/-- The domain of the last of the leading binders (at most `n` of them). -/
def lastDom (c : Ixon.Constant) : Nat → Ixon.Expr → Option Ixon.Expr
  | 0, _ => none
  | n + 1, e =>
    match node c e with
    | .all d b =>
      match node c b with
      | .all _ _ => lastDom c n b
      | _ => some d
    | _ => none

/-- The head of an application spine (at most `n` applications). -/
def spineHead (c : Ixon.Constant) : Nat → Ixon.Expr → Ixon.Expr
  | 0, e => node c e
  | n + 1, e =>
    match node c e with
    | .app f _ => spineHead c n f
    | h => h

/-- The constant at the head of a term, named by reference. -/
def refHead (c : Ixon.Constant) (e : Ixon.Expr) : Option _root_.Address :=
  match spineHead c fuel e with
  | .ref i _ => c.refs[i.toNat]?
  | _ => none

/-- **The carrier of motive `i`** of the recursor `r` of the record `c`: the constant heading the
last binder domain of the motive's type (the type the motive is over). -/
def motiveCarrier (c : Ixon.Constant) (r : Ixon.Recursor) (i : Nat) : Option _root_.Address := do
  let e ← peel c (r.params.toNat + i) r.typ
  let m ← domOf c e
  let d ← lastDom c fuel m
  refHead c d

/-- **The head of the major premise's type** of the recursor `r` of the record `c`. -/
def majorHead (c : Ixon.Constant) (r : Ixon.Recursor) : Option _root_.Address := do
  let e ← peel c (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) r.typ
  let d ← domOf c e
  refHead c d

/-- **`rb` is the family record of the block `B`, member by member, in the store `E`** (module
docstring). -/
structure FamilyOfBlock (E : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) (rb : _root_.Address) (crb : Ixon.Constant)
    (rs : Array Ixon.MutConst) : Prop where
  block : FamBlockRecord E B cb ms
  record : FamRecRecord E rb crb rs
  /-- One recursor per type of the block at least: a non-empty block has a non-empty family. -/
  covers : ms.size ≤ rs.size
  /-- One complete family: each recursor has one motive per member of the record. -/
  motives : ∀ k r, rs[k]? = some (.recr r) → r.motives.toNat = rs.size
  /-- The carriers: in every recursor, motive `i` below the type count is over member `i`. -/
  carriers : ∀ k r, rs[k]? = some (.recr r) → ∀ i m, ms[i]? = some m →
    motiveCarrier crb r i = some (memberAddr B i m)
  /-- The member correspondence: the recursor at position `k` below the type count eliminates
  member `k`. -/
  major : ∀ k r m, rs[k]? = some (.recr r) → ms[k]? = some m →
    majorHead crb r = some (memberAddr B k m)

/-- **The family record of a non-empty block has a recursor at every type's position**, and each
is that type's (the correspondence a twin's parts are matched by). -/
theorem FamilyOfBlock.recursor_at {E : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (h : FamilyOfBlock E B cb ms rb crb rs) {k : Nat} {m : Ixon.MutConst}
    (hm : ms[k]? = some m) :
    ∃ r, rs[k]? = some (.recr r) ∧ majorHead crb r = some (memberAddr B k m) := by
  have hk : k < ms.size := by
    rcases Nat.lt_or_ge k ms.size with hlt | hge
    · exact hlt
    · rw [Array.getElem?_eq_none hge] at hm
      cases hm
  have hkr : k < rs.size := Nat.lt_of_lt_of_le hk h.covers
  have hget : rs[k]? = some rs[k] := Array.getElem?_eq_getElem hkr
  have hmem : rs.toList[k]? = some rs[k] := by simpa only [Array.getElem?_toList] using hget
  obtain ⟨r, hr⟩ := h.record.recrs rs[k] (List.mem_of_getElem? hmem)
  rw [hr] at hget
  exact ⟨r, hget, h.major k r m hget hm⟩

/-- **A non-empty block's family record has a constant address**: the projection address of its
first recursor. -/
theorem FamilyOfBlock.constAddr_of_nonempty {E : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (h : FamilyOfBlock E B cb ms rb crb rs) (hne : 0 < ms.size) :
    ∃ x, Typing.ConstAddrOf rb crb x := by
  have hr0 : 0 < rs.size := Nat.lt_of_lt_of_le hne h.covers
  exact ⟨memberAddr rb 0 rs[0], Or.inr ⟨rs, 0, rs[0], h.record.muts,
    Array.getElem?_eq_getElem hr0, Or.inl rfl⟩⟩

end IxVM.Refinement.Binding.FamilyOf
