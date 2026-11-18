import IxVMRefinement.Assembly.FamilyFold

/-! # The family record of a block, position by position over its flattened family

A mutual or nested block `B` is installed with one family record `rb`: a block of recursors
whose recursor at position `k` eliminates the `k`-th entry of the block's flattened family, the
block's own types first, then the nested auxiliaries (a container's type at the parameters the
block nests through it). The circuit checks this of the record a family check is handed
(`KernelModeled::check_family`: the flattened family read off the record, `build_flat_block`,
whose auxiliaries are the constructors' nested occurrences, `check_nested_aux`; `check_recs`: one
motive per member of the record, the recursor at position `k` eliminating motive `k`).
`FamilyOfBlock E B cb ms rb crb rs flat` states it over a store, on the two records' own
expressions, with `flat` the type each position eliminates:

* the block is a block of inductives with its projection records, the family record a block of
  recursors with its projection records (`FamBlockRecord`, `FamRecRecord`);
* one recursor per entry of the flattened family (`covers`), whose first entries are the
  block's types in order (`originals`); so the family record of a non-empty block is non-empty
  (`types_le`);
* one complete family: each recursor has one motive per entry (`motives`);
* the carriers: in every recursor, motive `j` is over entry `j` (`carriers`);
* the correspondence: the recursor at position `k` has its major premise over entry `k`
  (`major`), auxiliary positions included (`recursor_at`).

An entry is the type's address; two auxiliaries over one container (at different parameters)
are told apart by their position, which the circuit reads off the record and checks against the
constructors' nested occurrences.

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

/-- **`rb` is the family record of the block `B`, position by position over the flattened family
`flat`, in the store `E`** (module docstring). `flat` lists the type each position eliminates,
in the order of the record: the block's types first, then the nested auxiliaries' containers. -/
structure FamilyOfBlock (E : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) (rb : _root_.Address) (crb : Ixon.Constant)
    (rs : Array Ixon.MutConst) (flat : List _root_.Address) : Prop where
  block : FamBlockRecord E B cb ms
  record : FamRecRecord E rb crb rs
  /-- One recursor per entry of the flattened family. -/
  covers : flat.length = rs.size
  /-- The flattened family's first entries are the block's types, in order. -/
  originals : ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m →
    flat[i]? = some (memberAddr B i m)
  /-- One complete family: each recursor has one motive per entry. -/
  motives : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr r) →
    r.motives.toNat = flat.length
  /-- The carriers: in every recursor, motive `j` is over entry `j`. -/
  carriers : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr r) →
    ∀ (j : Nat) (a : _root_.Address), flat[j]? = some a → motiveCarrier crb r j = some a
  /-- The correspondence: the recursor at position `k` eliminates entry `k`. -/
  major : ∀ (k : Nat) (r : Ixon.Recursor) (a : _root_.Address),
    rs[k]? = some (Ixon.MutConst.recr r) → flat[k]? = some a → majorHead crb r = some a

/-- **Every position of the flattened family holds a recursor, and it eliminates that position's
entry**: the correspondence a twin's parts are matched by, auxiliary positions included. -/
theorem FamilyOfBlock.recursor_at {E : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst} {flat : List _root_.Address}
    (h : FamilyOfBlock E B cb ms rb crb rs flat) {k : Nat} {a : _root_.Address}
    (hk : flat[k]? = some a) :
    ∃ r : Ixon.Recursor, rs[k]? = some (Ixon.MutConst.recr r) ∧ majorHead crb r = some a := by
  have hkf : k < flat.length := by
    rcases Nat.lt_or_ge k flat.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hk
      cases hk
  have hkr : k < rs.size := by rw [← h.covers]; exact hkf
  have hget : rs[k]? = some rs[k] := Array.getElem?_eq_getElem hkr
  have hmem : rs.toList[k]? = some rs[k] := by simpa only [Array.getElem?_toList] using hget
  obtain ⟨r, hr⟩ := h.record.recrs rs[k] (List.mem_of_getElem? hmem)
  rw [hr] at hget
  exact ⟨r, hget, h.major k r a hget hk⟩

/-- **The block's types are among the positions**: one recursor per type at least, so the family
record of a non-empty block is non-empty. -/
theorem FamilyOfBlock.types_le {E : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst} {flat : List _root_.Address}
    (h : FamilyOfBlock E B cb ms rb crb rs flat) : ms.size ≤ rs.size := by
  rw [← h.covers]
  rcases Nat.eq_zero_or_pos ms.size with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · have hlt : ms.size - 1 < ms.size := Nat.sub_lt hpos Nat.one_pos
    have hm : ms[ms.size - 1]? = some ms[ms.size - 1] := Array.getElem?_eq_getElem hlt
    have hf := h.originals _ _ hm
    have hfl : ms.size - 1 < flat.length := by
      rcases Nat.lt_or_ge (ms.size - 1) flat.length with hl | hge
      · exact hl
      · rw [List.getElem?_eq_none hge] at hf
        cases hf
    omega

/-- **A non-empty block's family record has a constant address**: the projection address of its
first recursor. -/
theorem FamilyOfBlock.constAddr_of_nonempty {E : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst} {flat : List _root_.Address}
    (h : FamilyOfBlock E B cb ms rb crb rs flat) (hne : 0 < ms.size) :
    ∃ x, Typing.ConstAddrOf rb crb x := by
  have hr0 : 0 < rs.size := Nat.lt_of_lt_of_le hne h.types_le
  exact ⟨memberAddr rb 0 rs[0], Or.inr ⟨rs, 0, rs[0], h.record.muts,
    Array.getElem?_eq_getElem hr0, Or.inl rfl⟩⟩

/-! ## The readers' fuel

The readers walk a binder telescope and an application spine with the fixed fuel `fuel`; the
circuit's readers (`last_binder_dom`, `collect_spine`) follow the expression structurally. A
reader that answers at some fuel answers the same at every larger one, so raising the fuel, or
deriving it from the record, keeps every answer read so far, and the answers at two fuels agree.
What a fixed fuel cannot give is an answer the circuit reads past it. -/

/-- **`lastDom` answers the same at every larger fuel.** -/
theorem lastDom_mono (c : Ixon.Constant) (d : Ixon.Expr) :
    ∀ (n m : Nat) (e : Ixon.Expr), lastDom c n e = some d → n ≤ m → lastDom c m e = some d := by
  intro n
  induction n with
  | zero =>
    intro m e h _
    simp [lastDom] at h
  | succ n ih =>
    intro m e h hle
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [lastDom] at h ⊢
    cases hn : node c e with
    | all d' b =>
      simp only [hn] at h ⊢
      cases hb : node c b with
      | all x y =>
        simp only [hb] at h ⊢
        exact ih m b h (by omega)
      | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
      | letE _ _ _ _ _ | share _ =>
        simp only [hb] at h ⊢
        exact h
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
    | letE _ _ _ _ _ | share _ =>
      simp only [hn] at h <;> cases h

/-- **`spineHead` answers the same at every larger fuel once it reached a node that is no
application.** -/
theorem spineHead_mono (c : Ixon.Constant) :
    ∀ (n m : Nat) (e : Ixon.Expr), (∀ f a, spineHead c n e ≠ .app f a) → n ≤ m →
      spineHead c m e = spineHead c n e := by
  intro n
  induction n with
  | zero =>
    intro m e hna _
    cases m with
    | zero => rfl
    | succ m =>
      simp only [spineHead] at hna ⊢
      cases hn : node c e with
      | app f a => exact absurd hn (hna f a)
      | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | lam _ _ | all _ _
      | letE _ _ _ _ _ | share _ => rfl
  | succ n ih =>
    intro m e hna hle
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [spineHead] at hna ⊢
    cases hn : node c e with
    | app f a =>
      simp only [hn] at hna ⊢
      exact ih m f hna (by omega)
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | lam _ _ | all _ _
    | letE _ _ _ _ _ | share _ => rfl

/-- The constant at the head of a term, named by reference, at the fuel `n`. -/
def refHeadAt (c : Ixon.Constant) (n : Nat) (e : Ixon.Expr) : Option _root_.Address :=
  match spineHead c n e with
  | .ref i _ => c.refs[i.toNat]?
  | _ => none

theorem refHead_eq (c : Ixon.Constant) (e : Ixon.Expr) : refHead c e = refHeadAt c fuel e := rfl

/-- **`refHeadAt` answers the same at every larger fuel.** -/
theorem refHeadAt_mono {c : Ixon.Constant} {n m : Nat} {e : Ixon.Expr} {a : _root_.Address}
    (h : refHeadAt c n e = some a) (hle : n ≤ m) : refHeadAt c m e = some a := by
  have hna : ∀ f x, spineHead c n e ≠ .app f x := by
    intro f x hfx
    unfold refHeadAt at h
    rw [hfx] at h
    simp at h
  unfold refHeadAt at h ⊢
  rw [spineHead_mono c n m e hna hle]
  exact h

/-- The carrier of motive `i` at the fuel `n` (`motiveCarrier` at `fuel`). -/
def motiveCarrierAt (c : Ixon.Constant) (r : Ixon.Recursor) (i n : Nat) :
    Option _root_.Address := do
  let e ← peel c (r.params.toNat + i) r.typ
  let m ← domOf c e
  let d ← lastDom c n m
  refHeadAt c n d

/-- The head of the major premise's type at the fuel `n` (`majorHead` at `fuel`). -/
def majorHeadAt (c : Ixon.Constant) (r : Ixon.Recursor) (n : Nat) : Option _root_.Address := do
  let e ← peel c (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) r.typ
  let d ← domOf c e
  refHeadAt c n d

theorem motiveCarrier_eq (c : Ixon.Constant) (r : Ixon.Recursor) (i : Nat) :
    motiveCarrier c r i = motiveCarrierAt c r i fuel := rfl

theorem majorHead_eq (c : Ixon.Constant) (r : Ixon.Recursor) :
    majorHead c r = majorHeadAt c r fuel := rfl

/-- **`motiveCarrierAt` answers the same at every larger fuel.** -/
theorem motiveCarrierAt_mono {c : Ixon.Constant} {r : Ixon.Recursor} {i n m : Nat}
    {a : _root_.Address} (h : motiveCarrierAt c r i n = some a) (hle : n ≤ m) :
    motiveCarrierAt c r i m = some a := by
  unfold motiveCarrierAt at h ⊢
  cases hp : peel c (r.params.toNat + i) r.typ with
  | none => simp [hp] at h
  | some e =>
    cases hd : domOf c e with
    | none => simp [hp, hd] at h
    | some mm =>
      cases hl : lastDom c n mm with
      | none => simp [hp, hd, hl] at h
      | some d =>
        have hl' : lastDom c m mm = some d := lastDom_mono c d n m mm hl hle
        simp [hp, hd, hl] at h
        simp [hp, hd, hl']
        exact refHeadAt_mono h hle

/-- **`majorHeadAt` answers the same at every larger fuel.** -/
theorem majorHeadAt_mono {c : Ixon.Constant} {r : Ixon.Recursor} {n m : Nat}
    {a : _root_.Address} (h : majorHeadAt c r n = some a) (hle : n ≤ m) :
    majorHeadAt c r m = some a := by
  unfold majorHeadAt at h ⊢
  cases hp : peel c (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat)
    r.typ with
  | none => simp [hp] at h
  | some e =>
    cases hd : domOf c e with
    | none => simp [hp, hd] at h
    | some d =>
      simp [hp, hd] at h
      simp [hp, hd]
      exact refHeadAt_mono h hle

/-- **The carrier read at two fuels is one.** -/
theorem motiveCarrierAt_unique {c : Ixon.Constant} {r : Ixon.Recursor} {i n n' : Nat}
    {a a' : _root_.Address} (h : motiveCarrierAt c r i n = some a)
    (h' : motiveCarrierAt c r i n' = some a') : a = a' := by
  have e1 := motiveCarrierAt_mono h (Nat.le_max_left n n')
  have e2 := motiveCarrierAt_mono h' (Nat.le_max_right n n')
  exact Option.some.inj (e1.symm.trans e2)

/-- **The major premise's head read at two fuels is one.** -/
theorem majorHeadAt_unique {c : Ixon.Constant} {r : Ixon.Recursor} {n n' : Nat}
    {a a' : _root_.Address} (h : majorHeadAt c r n = some a)
    (h' : majorHeadAt c r n' = some a') : a = a' := by
  have e1 := majorHeadAt_mono h (Nat.le_max_left n n')
  have e2 := majorHeadAt_mono h' (Nat.le_max_right n n')
  exact Option.some.inj (e1.symm.trans e2)

end IxVM.Refinement.Binding.FamilyOf
