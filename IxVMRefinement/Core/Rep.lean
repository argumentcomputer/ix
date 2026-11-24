import IxVMRefinement.Core.Obs
import IxVMRefinement.Obs.Names
import Aiur.Library.IxVMRep
import IxVM.Field
import Ix.IxVM.Refinement.KernelLevels
import IxCK.Kernel.Verify.Level
import IxCK.Kernel.Verify.PropWhen

/-! # The term seam: IxVM heap terms and the kernel's `Expr`

`Tm κ d Γ h k E p`: the heap value `p` (a `KernelTypes::KExpr`) represents the kernel
term `E`, at local binder depth `k`, opening depth `d` and ghost context `Γ`, under the
keying `κ` of addresses. One inductive over the heap cells, one constructor per
`KernelTypes::KExprNode` constructor (two for `BVar`, two for `Lit`):

* `BVar i` with `i < k` is the local `.bvar i`; with `k ≤ i < k + d` it is the opened
  variable `.fvar j (Γ j)`, `j = d - 1 - (i - k)`: IxVM's index counts from the inside, the
  kernel's opened variable from the outside, and the variable carries its type (`Γ j`), as
  the rules require. Every index is below `2^63`, so IxVM's field arithmetic on indices
  (`expr_lbr`'s `i + 1`, the lifts' `i + shift` by a shift below `2^32`) does not wrap
  (conversion's `UInt64::to_field` already bounds a converted index by `2^56`).
* `Srt ℓ` and `Const a ls`: levels are related **up to semantic equality** (`LvEq`,
  `Level.EvalEqList`) with the level the heap represents (`RepKLevel`, the level slice's
  relation), because `DefEq` has no transitivity and IxVM's level operations simplify.
  A constant's key is `κ (ixAddr a)`: the keying of the role table the run read
  (role-bound addresses to `.role r`, the others to `.id a`; `Ctx.lean`).
* `Lam ty b ℓ` and `Forall ty b ℓ`: the binder datum is `bmeta ℓ`, the zero-ness of the
  stored level `ℓ` (`Level.zeronessOf`, semantic: `zeronessOf_congr`). `bmeta` is the one
  definition that states the binder's contracts are the defaults.
* `Let ty v b` is ζ-expanded: its image is the image of `b` with the image of `v`
  substituted (`instShift`, capture-avoiding: `v` may mention the enclosing local binders).
  The type must be represented too. So no image contains a `letE`.
* `Lit (Nat limbs)` is the literal of the limbs' little-endian value (`limbsVal`);
  `Lit (Str bytes)` is the string whose UTF-8 encoding the bytes are (`StrBytes`).
* `Proj s i e` is `.proj (κ (ixAddr s)) i e'`.

IxVM's context list `types` is not part of this relation: it is a segment of the ghost
context `Γ` (`Ctx.lean`, `TypesRep`). Every relation here is monotone in the heap
(`Tm.mono`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)

set_option linter.unusedVariables false

/-! ## Names -/

abbrev F := IxVM.F

/-- The prepared source's world. -/
abbrev W : World F := IxVM.source.world

/-- The kernel's expressions, keys and levels, in the Ixon mode. -/
abbrev KExpr := Ix.Kernel.Expr .anon
abbrev KKey := Ix.Kernel.Key .anon
abbrev KLevel := Ix.Kernel.Level

abbrev kexprEnum : String := "KernelTypes::KExprNode"
abbrev klitEnum : String := "KernelTypes::KLiteral"
abbrev klevelEnum : String := "KernelTypes::KLevelNode"
abbrev kciEnum : String := "KernelTypes::KConstantInfo"
abbrev krrEnum : String := "KernelTypes::KRecRule"
abbrev kexprTy : Generic.Ty := .ptr (.named "KernelTypes::KExprNode" [])
abbrev klevelTy : Generic.Ty := .ptr (.named "KernelTypes::KLevelNode" [])
/-- `Lists::Node<&KernelTypes::KExprNode>`: term lists (spines, contexts). -/
abbrev kexprListEnum : String := Obs.Names.«Lists::Node<&KernelTypes::KExprNode>»
/-- `Lists::Node<&KernelTypes::KLevelNode>`: level lists. -/
abbrev klevelListEnum : String := Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>»
/-- `Lists::Node<[Field; 8]>`: `KernelTypes::KLimbs`, little-endian 64-bit limbs. -/
abbrev limbListEnum : String := Obs.Names.«Lists::Node<[Field; 8]>»
/-- `Lists::Node<Field>`: byte streams. -/
abbrev byteListEnum : String := Obs.Names.«Lists::Node<Field>»
/-- `Lists::Node<KernelTypes::KRecRule>`: recursor rules. -/
abbrev krrListEnum : String := Obs.Names.«Lists::Node<KernelTypes::KRecRule>»
/-- `Lists::Node<&[Field; 32]>`: address lists. -/
abbrev addrListEnum : String := Obs.Names.«Lists::Node<&[Field; 32]>»
/-- The cell type of a `Bytes::AddressRef`. -/
abbrev addrTy : Aiur.Ty := .tuple (List.replicate 32 .field)

@[simp] theorem kexpr_ctor :
    constructorName [] (.named "KernelTypes::KExprNode" []) = kexprEnum := by decide +kernel

@[simp] theorem kexprList_ctor :
    constructorName [] (.named "Lists::Node" [kexprTy]) = kexprListEnum := by decide +kernel

@[simp] theorem kexprList_inst :
    instanceName [] "Lists::Node" (some [kexprTy]) = kexprListEnum := by decide +kernel

@[simp] theorem klevelList_ctor :
    constructorName [] (.named "Lists::Node" [klevelTy]) = klevelListEnum := by decide +kernel

theorem klevelListEnum_eq : klevelListEnum = IxVM.Refinement.KernelLevels.klevelListEnum := by
  decide +kernel

/-- The view's address of an IxVM address. -/
def ixAddr (a : Bytes.Address) : _root_.Address := ⟨⟨a.toArray⟩⟩

theorem loadValue_enum_cell {enumName : String} {heap : Heap F} {addr : Nat}
    {c : String} {xs : List (SourceValue F)}
    (cell : heap[addr]? = some (.construct enumName c xs)) :
    loadValue heap (.ptr (.enum enumName) addr) = .ok (.construct enumName c xs) := by
  simp [loadValue, cell, Value.type, bind, Except.bind, pure, Except.pure]

/-- A cell and a load of the same pointer agree. -/
theorem load_cell {heap : Heap F} {addr : Nat} {en c c' : String}
    {xs ys : List (SourceValue F)}
    (cell : heap[addr]? = some (.construct en c xs))
    (hl : loadValue heap (.ptr (.enum en) addr) = .ok (.construct en c' ys)) :
    c = c' ∧ xs = ys := by
  rw [loadValue_enum_cell cell] at hl
  injection hl with hv
  injection hv with _ hc hxs
  exact ⟨hc, hxs⟩

/-- A load of a pointer to a cell of another constructor. -/
theorem load_cell_ne {heap : Heap F} {addr : Nat} {en c c' : String}
    {xs ys : List (SourceValue F)}
    (cell : heap[addr]? = some (.construct en c xs))
    (hl : loadValue heap (.ptr (.enum en) addr) = .ok (.construct en c' ys)) (hne : c ≠ c') :
    False :=
  hne (load_cell cell hl).1

/-! ## Levels up to semantic equality -/

/-- **Semantic level equality**: equal values under every assignment. -/
def LvEq (u v : KLevel) : Prop := ∀ φ, Ix.Kernel.Level.eval φ u = Ix.Kernel.Level.eval φ v

/-- **Pointwise semantic equality of level lists** (`Level.EvalEqList`, the premise of
`DefEq.const`). -/
def LvEqList (us vs : List KLevel) : Prop := ∀ φ, Ix.Kernel.Level.EvalEqList φ us vs

theorem LvEq.refl (u : KLevel) : LvEq u u := fun _ => rfl
theorem LvEq.symm {u v : KLevel} (h : LvEq u v) : LvEq v u := fun φ => (h φ).symm
theorem LvEq.trans {u v w : KLevel} (h₁ : LvEq u v) (h₂ : LvEq v w) : LvEq u w :=
  fun φ => (h₁ φ).trans (h₂ φ)

theorem evalEqList_refl (φ : Ix.Kernel.LevelParam → Nat) :
    ∀ us : List KLevel, Ix.Kernel.Level.EvalEqList φ us us
  | [] => trivial
  | _ :: us => ⟨rfl, evalEqList_refl φ us⟩

theorem LvEqList.refl (us : List KLevel) : LvEqList us us := fun φ => evalEqList_refl φ us

/-- **A level, up to semantic equality**: `p` represents a level (`RepKLevel`) whose value is
`u`'s under every assignment. -/
def LvRep (h : Heap F) (u : KLevel) (p : SourceValue F) : Prop :=
  ∃ l, RepKLevel h l p ∧ LvEq u l

/-- **A level list, up to pointwise semantic equality.** -/
def LvListRep (h : Heap F) (us : List KLevel) (p : SourceValue F) : Prop :=
  ∃ ls, RepKLevelList h ls p ∧ LvEqList us ls

theorem LvRep.mono {h₁ h₂ : Heap F} {u : KLevel} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : LvRep h₁ u p) : LvRep h₂ u p :=
  let ⟨l, rl, he⟩ := r; ⟨l, rl.mono ext, he⟩

theorem LvListRep.mono {h₁ h₂ : Heap F} {us : List KLevel} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : LvListRep h₁ us p) : LvListRep h₂ us p :=
  let ⟨ls, rl, he⟩ := r; ⟨ls, rl.mono ext, he⟩

/-! ## Binder data, literals, ζ -/

/-- **The binder datum of a stored level**: the kernel binder's `pw` is the zero-ness of
the level IxVM's `Lam`/`Forall` node stores. **This is the one definition that fixes the
binder's contracts**: the kernel's defaults (`many`, `shared`), the only binder metadata
kernel terms carry once binder contracts leave the kernel. No term related here has
another contract. -/
def bmeta (ℓ : KLevel) : Ix.Kernel.BinderMeta := { pw := ℓ.zeronessOf }

/-- Zero-ness is semantic: semantically equal levels have the same datum. -/
theorem zeronessOf_congr {u v : KLevel} (h : LvEq u v) : u.zeronessOf = v.zeronessOf :=
  Ix.Kernel.PropWhen.eq_of_holds fun φ => by
    rw [Ix.Kernel.PropWhen.zeronessOf_sound, Ix.Kernel.PropWhen.zeronessOf_sound, h φ]

theorem bmeta_congr {u v : KLevel} (h : LvEq u v) : bmeta u = bmeta v := by
  unfold bmeta; rw [zeronessOf_congr h]

/-- The value of a little-endian limb list. -/
def limbsVal : List UInt64 → Nat
  | [] => 0
  | l :: ls => l.toNat + 18446744073709551616 * limbsVal ls

/-- **A string literal's bytes**: `bytes` are valid UTF-8 and decode to `s`, as the kernel
reader decodes a string literal's blob (`String.fromUTF8?`, `Reader.convExpr`). -/
def StrBytes (s : String) (bytes : List UInt8) : Prop := String.fromUTF8? ⟨bytes.toArray⟩ = some s

/-- **Capture-avoiding instantiation** (`Ix.Kernel.Expr.instantiate1Lift`): the loose bound
variable `j` of `e` replaced by `v`, lifted over the `j` binders passed, the loose bound
variables above `j` lowered by one. The kernel's `Expr.instantiate1` does not lift `v`; the two
agree when `v` has no loose bound variable. The image of a `Let` is `instShift v 0 b`, the
ζ-reduct the statement's `Annotates.letE` reads once it substitutes without capture. -/
abbrev instShift (v : KExpr) (j : Nat) (e : KExpr) : KExpr := Ix.Kernel.Expr.instantiate1Lift e v j

/-- The opened variable a free `BVar i` at local depth `k` and opening depth `d` stands for. -/
abbrev fvIdx (d k i : Nat) : Nat := d - 1 - (i - k)

/-! ## Resolved keys -/

/-- **The unresolved key**: a key no environment stores and no role table's keying returns (the
projection table of a projection table). A keying that knows which addresses resolve
(`ScopedCtx.κ`) sends every other address here. -/
def unresolvedKey : KKey := .aux (.aux (.role default) .projTable) .projTable

/-- **The key resolves**: it is not `unresolvedKey`. A `Const` or `Proj` node is represented
only when the key of its address resolves. Under a role table's own keying every key does
(`Ctx.lean`), so there the premise is no restriction. -/
class Resolved (k : KKey) : Prop where
  ne : k ≠ unresolvedKey

/-! ## Where a projection is permitted

A keying carries a second bit for each address, the *projection permission*, and carries it at
the address's marker. `projMarker` and `ProjPermitted` are the whole encoding: every other
statement speaks of `ProjPermitted` (and, where it must say an address is one a record can have,
of `IsProjMarker`). A keying that held the two bits as separate components would change these
definitions and the lemmas beside them, and nothing else. -/

/-- **The marker of an address**: its bytes followed by 33 zero bytes. A record's address has 32
bytes (`ixAddr_size`; the hash's output), a marker has more, so no record's address is a marker
(`not_isProjMarker_of_size`). A marker is only ever the argument of a keying: no store, heap or
environment is read at one. -/
def projMarker (a : _root_.Address) : _root_.Address :=
  ⟨⟨⟨a.hash.data.toList ++ List.replicate 33 0⟩⟩⟩

/-- **A projection is permitted at the address** under the keying: the second bit the keying
carries for the address, read as the resolution of the address's marker. A `Proj` node is
represented only where a projection is permitted at its structure's address (`Tm.proj`). A role
table's own keying permits it everywhere; a prefix's keying permits it at the stored addresses;
the keying of a stage permits it at the addresses the prefix under the stage stores, so not at a
constant the stage adds (`Ctx.lean`). -/
class ProjPermitted (κ : _root_.Address → KKey) (a : _root_.Address) : Prop where
  ne : κ (projMarker a) ≠ unresolvedKey

/-- A keying under which every key resolves permits every projection. -/
instance (κ : _root_.Address → KKey) [h : ∀ a, Resolved (κ a)] (a : _root_.Address) :
    ProjPermitted κ a :=
  ⟨(h (projMarker a)).ne⟩

/-- A keying that keeps every resolved key of another permits the projections the other
permits. -/
theorem ProjPermitted.of_keep {κ₁ κ₂ : _root_.Address → KKey}
    (keep : ∀ x, κ₁ x ≠ unresolvedKey → κ₂ x = κ₁ x) {a : _root_.Address}
    (h : ProjPermitted κ₁ a) : ProjPermitted κ₂ a :=
  ⟨by rw [keep _ h.ne]; exact h.ne⟩

/-- Two addresses with one marker are one address. -/
theorem projMarker_injective {a b : _root_.Address} (h : projMarker a = projMarker b) : a = b := by
  obtain ⟨⟨⟨la⟩⟩⟩ := a
  obtain ⟨⟨⟨lb⟩⟩⟩ := b
  have h1 : la ++ List.replicate 33 (0 : UInt8) = lb ++ List.replicate 33 0 :=
    congrArg (fun x : _root_.Address => x.hash.data.toList) h
  have h2 : la = lb := List.append_cancel_right h1
  subst h2
  rfl

/-- **The address is a marker.** -/
def IsProjMarker (a : _root_.Address) : Prop := ∃ y, a = projMarker y

/-- **No address of 32 bytes is a marker.** -/
theorem not_isProjMarker_of_size {a : _root_.Address} (h : a.hash.size = 32) :
    ¬ IsProjMarker a := by
  rintro ⟨y, rfl⟩
  obtain ⟨⟨⟨ly⟩⟩⟩ := y
  have hs : (projMarker ⟨⟨⟨ly⟩⟩⟩).hash.size = ly.length + 33 := by
    show (ly ++ List.replicate 33 (0 : UInt8)).length = ly.length + 33
    simp
  omega

/-! ## The relation -/

/-- **The term seam**: at local binder depth `k`, the heap value `p` represents the kernel term
`E`, at opening depth `d`, ghost context `Γ` and keying `κ` (module docstring). -/
inductive Tm (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr) (h : Heap F) :
    Nat → KExpr → SourceValue F → Prop where
  | bvarLocal {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : (ZMod.val i) < 9223372036854775808) (hi : (ZMod.val i) < k) :
      Tm κ d Γ h k (.bvar (ZMod.val i)) (.ptr (.enum kexprEnum) addr)
  | bvarFree {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : (ZMod.val i) < 9223372036854775808) (hk : k ≤ (ZMod.val i)) (hd : (ZMod.val i) - k < d) :
      Tm κ d Γ h k (.fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i)))) (.ptr (.enum kexprEnum) addr)
  | sort {k addr : Nat} {lp : SourceValue F} {l u : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Srt" [lp]))
      (rl : RepKLevel h l lp) (hu : LvEq u l) :
      Tm κ d Γ h k (.sort u) (.ptr (.enum kexprEnum) addr)
  | const {k addr : Nat} {ap lsp : SourceValue F} {a : Bytes.Address} {ls us : List KLevel}
      [res : Resolved (κ (ixAddr a))]
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (rls : RepKLevelList h ls lsp)
      (hus : LvEqList us ls) :
      Tm κ d Γ h k (.const (κ (ixAddr a)) us) (.ptr (.enum kexprEnum) addr)
  | app {k addr : Nat} {fp ap : SourceValue F} {Ef Ea : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (rf : Tm κ d Γ h k Ef fp) (ra : Tm κ d Γ h k Ea ap) :
      Tm κ d Γ h k (.app Ef Ea) (.ptr (.enum kexprEnum) addr)
  | lam {k addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
      (rt : Tm κ d Γ h k T tp) (rb : Tm κ d Γ h (k + 1) B bp) (rl : RepKLevel h ℓ lp) :
      Tm κ d Γ h k (.lam T B (bmeta ℓ)) (.ptr (.enum kexprEnum) addr)
  | forallE {k addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (rt : Tm κ d Γ h k T tp) (rb : Tm κ d Γ h (k + 1) B bp) (rl : RepKLevel h ℓ lp) :
      Tm κ d Γ h k (.forallE T B (bmeta ℓ)) (.ptr (.enum kexprEnum) addr)
  | letE {k addr : Nat} {tp vp bp : SourceValue F} {T V B : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
      (rt : Tm κ d Γ h k T tp) (rv : Tm κ d Γ h k V vp) (rb : Tm κ d Γ h (k + 1) B bp) :
      Tm κ d Γ h k (instShift V 0 B) (.ptr (.enum kexprEnum) addr)
  | litNat {k addr : Nat} {lp : SourceValue F} {limbs : List UInt64}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Nat" [lp]]))
      (rl : RepList limbListEnum RepU64 h limbs lp) (hc : limbs.getLast? ≠ some 0) :
      Tm κ d Γ h k (.lit (.natVal (limbsVal limbs))) (.ptr (.enum kexprEnum) addr)
  | litStr {k addr : Nat} {bp : SourceValue F} {bytes : List UInt8} {s : String}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Str" [bp]]))
      (rb : Bytes.RepByteStream byteListEnum h bytes bp) (hs : StrBytes s bytes) :
      Tm κ d Γ h k (.lit (.strVal s)) (.ptr (.enum kexprEnum) addr)
  | proj {k addr : Nat} {ap ep : SourceValue F} {a : Bytes.Address} {i : F} {E : KExpr}
      [res : Resolved (κ (ixAddr a))] [perm : ProjPermitted κ (ixAddr a)]
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (re : Tm κ d Γ h k E ep) :
      Tm κ d Γ h k (.proj (κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) addr)

/-- The view's address of an IxVM address has 32 bytes. -/
theorem ixAddr_size (a : Bytes.Address) : (ixAddr a).hash.size = 32 := by
  obtain ⟨arr, hsz⟩ := a
  exact hsz

/-- The view's address of an IxVM address is no marker. -/
theorem ixAddr_not_marker (a : Bytes.Address) : ¬ IsProjMarker (ixAddr a) :=
  not_isProjMarker_of_size (ixAddr_size a)

section
variable (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr)

/-- A top-level term (local depth `0`). -/
abbrev TmE (h : Heap F) (E : KExpr) (p : SourceValue F) : Prop := Tm κ d Γ h 0 E p

/-- A list of top-level terms (`Lists::List<KExpr>`: spines, argument lists), elementwise. -/
abbrev TmL (h : Heap F) (Es : List KExpr) (p : SourceValue F) : Prop :=
  RepList kexprListEnum (TmE κ d Γ) h Es p

end

/-- **A closed term**: represented at every opening depth and ghost context (a stored
constant's type, value or rule). -/
def TmC (κ : _root_.Address → KKey) (h : Heap F) (E : KExpr) (p : SourceValue F) : Prop :=
  ∀ d Γ, Tm κ d Γ h 0 E p

/-! ## Heap monotonicity -/

theorem Tm.mono {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h₁ h₂ : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : Tm κ d Γ h₁ k E p) : Tm κ d Γ h₂ k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal (ext.getElem?_eq cell) hs hi
  | bvarFree cell hs hk hd => exact .bvarFree (ext.getElem?_eq cell) hs hk hd
  | sort cell rl hu => exact .sort (ext.getElem?_eq cell) (rl.mono ext) hu
  | const cell ra rls hus =>
    exact .const (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
      (rls.mono ext) hus
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ rl iht ihb => exact .lam (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | forallE cell _ _ rl iht ihb => exact .forallE (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | letE cell _ _ _ iht ihv ihb => exact .letE (ext.getElem?_eq cell) iht ihv ihb
  | litNat cell rl hc =>
    exact .litNat (ext.getElem?_eq cell) (repList_heapMono₂ _ repU64_heapMono₂ ext rl) hc
  | litStr cell rb hs =>
    exact .litStr (ext.getElem?_eq cell) (Bytes.repByteStream_heapMono₂ _ ext rb) hs
  | proj cell ra _ ihe =>
    exact .proj (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) ihe

theorem tmE_heapMono₂ {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    HeapMono₂ (TmE κ d Γ) :=
  fun _ _ _ _ ext rep => Tm.mono ext rep

theorem TmL.mono {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h₁ h₂ : Heap F}
    {Es : List KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : TmL κ d Γ h₁ Es p) : TmL κ d Γ h₂ Es p :=
  repList_heapMono₂ kexprListEnum tmE_heapMono₂ ext rep

theorem TmC.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : TmC κ h₁ E p) : TmC κ h₂ E p :=
  fun d Γ => (rep d Γ).mono ext

/-- A term represented at opening depth `0` has no opened variable: it is represented at every
depth and context. -/
theorem Tm.of_depth_zero {κ : _root_.Address → KKey} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ h k E p) :
    ∀ d, Tm κ d Γ' h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact fun _ => .bvarLocal cell hs hi
  | bvarFree _ _ _ hd => exact absurd hd (by omega)
  | sort cell rl hu => exact fun _ => .sort cell rl hu
  | const cell ra rls hus => exact fun _ => .const cell ra rls hus
  | app cell _ _ ihf iha => exact fun d => .app cell (ihf d) (iha d)
  | lam cell _ _ rl iht ihb => exact fun d => .lam cell (iht d) (ihb d) rl
  | forallE cell _ _ rl iht ihb => exact fun d => .forallE cell (iht d) (ihb d) rl
  | letE cell _ _ _ iht ihv ihb => exact fun d => .letE cell (iht d) (ihv d) (ihb d)
  | litNat cell rl hc => exact fun _ => .litNat cell rl hc
  | litStr cell rb hs => exact fun _ => .litStr cell rb hs
  | proj cell ra _ ihe => exact fun d => .proj cell ra (ihe d)

theorem TmC.of_depth_zero {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ h 0 E p) : TmC κ h E p :=
  fun d _ => rep.of_depth_zero d

/-- **The image reads the ghost context below the opening depth only**: changing `Γ` at or above
`d` changes nothing. -/
theorem Tm.congr_ghost {κ : _root_.Address → KKey} {d : Nat} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (hΓ : ∀ j, j < d → Γ' j = Γ j)
    (rep : Tm κ d Γ h k E p) : Tm κ d Γ' h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | @bvarFree k addr i cell hs hk hd =>
    rw [← hΓ (fvIdx d k (ZMod.val i)) (by unfold fvIdx; omega)]
    exact .bvarFree cell hs hk hd
  | sort cell rl hu => exact .sort cell rl hu
  | const cell ra rls hus => exact .const cell ra rls hus
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

/-! ## Inversion at a loaded cell

Each lemma reads a represented pointer's node off a load of that pointer (the form the
generated path lemmas give). -/

section Inversion
variable {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
  {E : KExpr} {p : SourceValue F}

theorem Tm.isPtr (rep : Tm κ d Γ h k E p) : ∃ addr, p = .ptr (.enum kexprEnum) addr := by
  cases rep <;> exact ⟨_, rfl⟩

theorem Tm.bvar_of_load {x : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "BVar" [x])) :
    ∃ i : F, x = .field i ∧ (ZMod.val i) < 9223372036854775808 ∧
      (((ZMod.val i) < k ∧ E = .bvar (ZMod.val i)) ∨
        (k ≤ (ZMod.val i) ∧ (ZMod.val i) - k < d ∧ E = .fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))) := by
  cases rep with
  | bvarLocal cell hs hi =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; exact ⟨_, hx.symm, hs, .inl ⟨hi, rfl⟩⟩
  | bvarFree cell hs hk hd =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; exact ⟨_, hx.symm, hs, .inr ⟨hk, hd, rfl⟩⟩
  | sort cell _ _ | const cell _ _ _ | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _
  | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.sort_of_load {x : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Srt" [x])) :
    ∃ u, E = .sort u ∧ LvRep h u x := by
  cases rep with
  | sort cell rl hu =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; subst hx; exact ⟨_, rfl, _, rl, hu⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | const cell _ _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.const_of_load {x y : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Const" [x, y])) :
    ∃ a us, E = .const (κ (ixAddr a)) us ∧ Bytes.RepAddressRef addrTy h a x ∧ LvListRep h us y := by
  cases rep with
  | const cell ra rls hus =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨_, _, rfl, ra, _, rls, hus⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.app_of_load {x y : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "App" [x, y])) :
    ∃ Ef Ea, E = .app Ef Ea ∧ Tm κ d Γ h k Ef x ∧ Tm κ d Γ h k Ea y := by
  cases rep with
  | app cell rf ra =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨_, _, rfl, rf, ra⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.lam_of_load {x y z : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Lam" [x, y, z])) :
    ∃ T B ℓ, E = .lam T B (bmeta ℓ) ∧ Tm κ d Γ h k T x ∧ Tm κ d Γ h (k + 1) B y ∧
      RepKLevel h ℓ z := by
  cases rep with
  | lam cell rt rb rl =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy hrest'; injection hrest' with hz
    subst hx hy hz; exact ⟨_, _, _, rfl, rt, rb, rl⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.forallE_of_load {x y z : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Forall" [x, y, z])) :
    ∃ T B ℓ, E = .forallE T B (bmeta ℓ) ∧ Tm κ d Γ h k T x ∧ Tm κ d Γ h (k + 1) B y ∧
      RepKLevel h ℓ z := by
  cases rep with
  | forallE cell rt rb rl =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy hrest'; injection hrest' with hz
    subst hx hy hz; exact ⟨_, _, _, rfl, rt, rb, rl⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.letE_of_load {x y z : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Let" [x, y, z])) :
    ∃ T V B, E = instShift V 0 B ∧ Tm κ d Γ h k T x ∧ Tm κ d Γ h k V y ∧
      Tm κ d Γ h (k + 1) B z := by
  cases rep with
  | letE cell rt rv rb =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy hrest'; injection hrest' with hz
    subst hx hy hz; exact ⟨_, _, _, rfl, rt, rv, rb⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.lit_of_load {x : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Lit" [x])) :
    (∃ lp limbs, x = .construct klitEnum "Nat" [lp] ∧ RepList limbListEnum RepU64 h limbs lp ∧
        limbs.getLast? ≠ some 0 ∧ E = .lit (.natVal (limbsVal limbs))) ∨
      (∃ bp bytes s, x = .construct klitEnum "Str" [bp] ∧
        Bytes.RepByteStream byteListEnum h bytes bp ∧ StrBytes s bytes ∧ E = .lit (.strVal s)) := by
  cases rep with
  | litNat cell rl hc =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; exact .inl ⟨_, _, hx.symm, rl, hc, rfl⟩
  | litStr cell rb hs =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; exact .inr ⟨_, _, _, hx.symm, rb, hs, rfl⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.proj_of_load {x y z : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Proj" [x, y, z])) :
    ∃ (a : Bytes.Address) (i : F) (Es : KExpr), y = .field i ∧ E = .proj (κ (ixAddr a)) (ZMod.val i) Es ∧
      Bytes.RepAddressRef addrTy h a x ∧ Tm κ d Γ h k Es z := by
  cases rep with
  | proj cell ra re =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy hrest'; injection hrest' with hz
    subst hx hz; exact ⟨_, _, _, hy.symm, rfl, ra, re⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

/-- **A projection is permitted at the structure of a represented `Proj` node**: the premise
the node was represented with, read at the address its cell holds. -/
theorem Tm.proj_permitted {x y z : SourceValue F} {a : Bytes.Address} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Proj" [x, y, z]))
    (ha : Bytes.RepAddressRef addrTy h a x) : ProjPermitted κ (ixAddr a) := by
  cases rep with
  | @proj _ _ _ _ a' _ _ _ perm cell ra re =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx
    subst hx
    have e : a' = a := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra ha
    rw [← e]
    exact perm
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

end Inversion

/-! ### Lists -/

theorem RepList.nil_of_load {α : Type} {enumName : String}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F} {xs : List α} {p : SourceValue F}
    (rep : RepList enumName R h xs p) (hl : loadValue h p = .ok (.construct enumName "Nil" [])) :
    xs = [] := by
  cases rep with
  | nil _ => rfl
  | cons cell _ _ => exact (load_cell_ne cell hl (by decide)).elim

theorem RepList.cons_of_load {α : Type} {enumName : String}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F} {xs : List α} {p x y : SourceValue F}
    (rep : RepList enumName R h xs p)
    (hl : loadValue h p = .ok (.construct enumName "Cons" [x, y])) :
    ∃ z zs, xs = z :: zs ∧ R h z x ∧ RepList enumName R h zs y := by
  cases rep with
  | nil cell => exact (load_cell_ne cell hl (by decide)).elim
  | cons cell rh rt =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨_, _, rfl, rh, rt⟩

/-! ## Building represented terms -/

section Store
variable {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}

/-- A stored `App` node of two represented terms. -/
theorem Tm.store_app {h : Heap F} {k : Nat} {Ef Ea : KExpr} {fp ap : SourceValue F}
    (rf : Tm κ d Γ h k Ef fp) (ra : Tm κ d Γ h k Ea ap) :
    Tm κ d Γ (h ++ [.construct kexprEnum "App" [fp, ap]]) k (.app Ef Ea)
      (.ptr (.enum kexprEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "App" [fp, ap]]) := Heap.Extends.snoc h _
  exact .app (by simp) (rf.mono ext) (ra.mono ext)

theorem TmL.store_nil (h : Heap F) :
    TmL κ d Γ (h ++ [.construct kexprListEnum "Nil" []]) []
      (.ptr (.enum kexprListEnum) h.length) :=
  allocNil_rep kexprListEnum (TmE κ d Γ) h

theorem TmL.store_cons {h : Heap F} {E : KExpr} {Es : List KExpr} {ep lp : SourceValue F}
    (re : TmE κ d Γ h E ep) (rl : TmL κ d Γ h Es lp) :
    TmL κ d Γ (h ++ [.construct kexprListEnum "Cons" [ep, lp]]) (E :: Es)
      (.ptr (.enum kexprListEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [ep, lp]]) :=
    Heap.Extends.snoc h _
  exact .cons (by simp) (re.mono ext) (rl.mono ext)

end Store

/-! ## Resolved images -/

/-- **No constant or projection node of the term carries the unresolved key** (the types of
opened variables are not read). The image of a represented term is such a term
(`Tm.keysResolved`), so a load site reads the resolution of the constant in its hand from the
term it is loading for. -/
def KeysResolved : KExpr → Prop
  | .const k _ => k ≠ unresolvedKey
  | .app f a => KeysResolved f ∧ KeysResolved a
  | .lam t b _ => KeysResolved t ∧ KeysResolved b
  | .forallE t b _ => KeysResolved t ∧ KeysResolved b
  | .letE t v b _ => KeysResolved t ∧ KeysResolved v ∧ KeysResolved b
  | .proj s _ e => s ≠ unresolvedKey ∧ KeysResolved e
  | .bvar _ | .fvar _ _ | .sort _ | .lit _ => True

theorem keysResolved_lift (n : Nat) (e : KExpr) :
    ∀ c, KeysResolved e → KeysResolved (e.liftLooseBVars n c) := by
  induction e with
  | bvar i =>
    intro c _
    simp only [Ix.Kernel.Expr.liftLooseBVars]
    split <;> simp only [KeysResolved]
  | sort _ | const _ _ | lit _ | fvar _ _ _ =>
    intro c hr
    simpa only [Ix.Kernel.Expr.liftLooseBVars] using hr
  | app f a ihf iha =>
    intro c hr
    simp only [Ix.Kernel.Expr.liftLooseBVars, KeysResolved] at hr ⊢
    exact ⟨ihf c hr.1, iha c hr.2⟩
  | lam ty body bm iht ihb | forallE ty body bm iht ihb =>
    intro c hr
    simp only [Ix.Kernel.Expr.liftLooseBVars, KeysResolved] at hr ⊢
    exact ⟨iht c hr.1, ihb (c + 1) hr.2⟩
  | letE ty val body bm iht ihv ihb =>
    intro c hr
    simp only [Ix.Kernel.Expr.liftLooseBVars, KeysResolved] at hr ⊢
    exact ⟨iht c hr.1, ihv c hr.2.1, ihb (c + 1) hr.2.2⟩
  | proj name i inner ih =>
    intro c hr
    simp only [Ix.Kernel.Expr.liftLooseBVars, KeysResolved] at hr ⊢
    exact ⟨hr.1, ih c hr.2⟩

theorem keysResolved_instShift {V : KExpr} (hV : KeysResolved V) (B : KExpr) :
    ∀ j, KeysResolved B → KeysResolved (instShift V j B) := by
  induction B with
  | bvar i =>
    intro j _
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift]
    split
    · exact keysResolved_lift _ _ _ hV
    · split <;> simp only [KeysResolved]
  | sort _ | const _ _ | lit _ | fvar _ _ _ =>
    intro j hr
    simpa only [instShift, Ix.Kernel.Expr.instantiate1Lift] using hr
  | app f a ihf iha =>
    intro j hr
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift, KeysResolved] at hr ⊢
    exact ⟨ihf j hr.1, iha j hr.2⟩
  | lam ty body bm iht ihb | forallE ty body bm iht ihb =>
    intro j hr
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift, KeysResolved] at hr ⊢
    exact ⟨iht j hr.1, ihb (j + 1) hr.2⟩
  | letE ty val body bm iht ihv ihb =>
    intro j hr
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift, KeysResolved] at hr ⊢
    exact ⟨iht j hr.1, ihv j hr.2.1, ihb (j + 1) hr.2.2⟩
  | proj name i inner ih =>
    intro j hr
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift, KeysResolved] at hr ⊢
    exact ⟨hr.1, ih j hr.2⟩

/-- The head of an application spine with resolved keys has resolved keys. -/
theorem keysResolved_mkAppN_head : ∀ (zs : List KExpr) (f : KExpr),
    KeysResolved (Ix.Kernel.Expr.mkAppN f zs) → KeysResolved f
  | [], _, hr => hr
  | z :: zs, f, hr => by
    have h1 : KeysResolved (.app f z) := keysResolved_mkAppN_head zs (.app f z) hr
    simp only [KeysResolved] at h1
    exact h1.1

/-- **The image of a represented term has resolved keys.** -/
theorem Tm.keysResolved {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) : KeysResolved E := by
  induction rep with
  | bvarLocal => simp only [KeysResolved]
  | bvarFree => simp only [KeysResolved]
  | sort => simp only [KeysResolved]
  | const =>
    simp only [KeysResolved]
    exact Resolved.ne
  | app _ _ _ ihf iha =>
    simp only [KeysResolved]
    exact ⟨ihf, iha⟩
  | lam _ _ _ _ iht ihb =>
    simp only [KeysResolved]
    exact ⟨iht, ihb⟩
  | forallE _ _ _ _ iht ihb =>
    simp only [KeysResolved]
    exact ⟨iht, ihb⟩
  | letE _ _ _ _ _ ihv ihb => exact keysResolved_instShift ihv _ 0 ihb
  | litNat => simp only [KeysResolved]
  | litStr => simp only [KeysResolved]
  | proj _ _ _ ihe =>
    simp only [KeysResolved]
    exact ⟨Resolved.ne, ihe⟩

/-- A represented constant's key resolves. -/
theorem Tm.const_key_ne {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {key : KKey} {us : List KLevel} {p : SourceValue F}
    (rep : Tm κ d Γ h k (.const key us) p) : key ≠ unresolvedKey := by
  have hr := rep.keysResolved
  simpa only [KeysResolved] using hr

/-- A represented projection's structure key resolves. -/
theorem Tm.proj_key_ne {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {key : KKey} {i : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Tm κ d Γ h k (.proj key i E) p) : key ≠ unresolvedKey := by
  have hr := rep.keysResolved
  simp only [KeysResolved] at hr
  exact hr.1

/-- The head constant of a represented application spine resolves. -/
theorem Tm.head_key_ne {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {key : KKey} {us : List KLevel} {zs : List KExpr} {p : SourceValue F}
    (rep : Tm κ d Γ h k (Ix.Kernel.Expr.mkAppN (.const key us) zs) p) : key ≠ unresolvedKey := by
  have hr := keysResolved_mkAppN_head zs _ rep.keysResolved
  simpa only [KeysResolved] using hr

end IxVM.Refinement.Core
