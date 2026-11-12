import IxVMRefinement.Core.Obs
import IxVMRefinement.Obs.Names
import Aiur.Library.IxVMRep
import IxVM.Field
import Ix.IxVM.Refinement.KernelLevels
import IxC.Kernel.Verify.Level
import IxC.Kernel.Verify.PropWhen

/-! # The term seam: IxVM heap terms and the kernel's `Expr`

`Tm κ d Γ h k E p`: the heap value `p` (a `KernelTypes::KExpr`) represents the kernel
term `E`, at local binder depth `k`, opening depth `d` and ghost context `Γ`, under the
keying `κ` of addresses. One inductive over the heap cells, one constructor per
`KernelTypes::KExprNode` constructor (two for `BVar`, two for `Lit`):

* `BVar i` with `i < k` is the local `.bvar i`; with `k ≤ i < k + d` it is the opened
  variable `.fvar j (Γ j)`, `j = d - 1 - (i - k)`: IxVM's index counts from the inside, the
  kernel's opened variable from the outside, and the variable carries its type (`Γ j`), as
  the rules require.
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

/-- **A string literal's bytes**: `bytes` is the UTF-8 encoding of `s` (so the bytes are
valid UTF-8, and `s` is determined). -/
def StrBytes (s : String) (bytes : List UInt8) : Prop := s.toUTF8.data.toList = bytes

/-- **Capture-avoiding instantiation**: the loose bound variable `j` of `e` replaced by `v`,
lifted over the `j` binders passed (`liftLooseBVars j 0 v`), the loose bound variables above
`j` lowered by one. The kernel's `Expr.instantiate1` does not lift `v`; the two agree when `v`
has no loose bound variable. The image of a `Let` is `instShift v 0 b`. -/
def instShift (v : KExpr) : Nat → KExpr → KExpr
  | j, .bvar i => if i = j then Ix.Kernel.Expr.liftLooseBVars j 0 v
      else if j < i then .bvar (i - 1) else .bvar i
  | _, .fvar i ty => .fvar i ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | j, .app f a => .app (instShift v j f) (instShift v j a)
  | j, .lam ty b m => .lam (instShift v j ty) (instShift v (j + 1) b) m
  | j, .forallE ty b m => .forallE (instShift v j ty) (instShift v (j + 1) b) m
  | j, .letE ty val b m => .letE (instShift v j ty) (instShift v j val) (instShift v (j + 1) b) m
  | _, .lit l => .lit l
  | j, .proj s i e => .proj s i (instShift v j e)

/-- The opened variable a free `BVar i` at local depth `k` and opening depth `d` stands for. -/
abbrev fvIdx (d k i : Nat) : Nat := d - 1 - (i - k)

/-! ## The relation -/

/-- **The term seam**: at local binder depth `k`, the heap value `p` represents the kernel term
`E`, at opening depth `d`, ghost context `Γ` and keying `κ` (module docstring). -/
inductive Tm (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr) (h : Heap F) :
    Nat → KExpr → SourceValue F → Prop where
  | bvarLocal {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hi : i.val < k) :
      Tm κ d Γ h k (.bvar i.val) (.ptr (.enum kexprEnum) addr)
  | bvarFree {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hk : k ≤ i.val) (hd : i.val - k < d) :
      Tm κ d Γ h k (.fvar (fvIdx d k i.val) (Γ (fvIdx d k i.val))) (.ptr (.enum kexprEnum) addr)
  | sort {k addr : Nat} {lp : SourceValue F} {l u : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Srt" [lp]))
      (rl : RepKLevel h l lp) (hu : LvEq u l) :
      Tm κ d Γ h k (.sort u) (.ptr (.enum kexprEnum) addr)
  | const {k addr : Nat} {ap lsp : SourceValue F} {a : Bytes.Address} {ls us : List KLevel}
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
      (rl : RepList limbListEnum RepU64 h limbs lp) :
      Tm κ d Γ h k (.lit (.natVal (limbsVal limbs))) (.ptr (.enum kexprEnum) addr)
  | litStr {k addr : Nat} {bp : SourceValue F} {bytes : List UInt8} {s : String}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Str" [bp]]))
      (rb : Bytes.RepByteStream byteListEnum h bytes bp) (hs : StrBytes s bytes) :
      Tm κ d Γ h k (.lit (.strVal s)) (.ptr (.enum kexprEnum) addr)
  | proj {k addr : Nat} {ap ep : SourceValue F} {a : Bytes.Address} {i : F} {E : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (re : Tm κ d Γ h k E ep) :
      Tm κ d Γ h k (.proj (κ (ixAddr a)) i.val E) (.ptr (.enum kexprEnum) addr)

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
  | bvarLocal cell hi => exact .bvarLocal (ext.getElem?_eq cell) hi
  | bvarFree cell hk hd => exact .bvarFree (ext.getElem?_eq cell) hk hd
  | sort cell rl hu => exact .sort (ext.getElem?_eq cell) (rl.mono ext) hu
  | const cell ra rls hus =>
    exact .const (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
      (rls.mono ext) hus
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ rl iht ihb => exact .lam (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | forallE cell _ _ rl iht ihb => exact .forallE (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | letE cell _ _ _ iht ihv ihb => exact .letE (ext.getElem?_eq cell) iht ihv ihb
  | litNat cell rl => exact .litNat (ext.getElem?_eq cell) (repList_heapMono₂ _ repU64_heapMono₂ ext rl)
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
  | bvarLocal cell hi => exact fun _ => .bvarLocal cell hi
  | bvarFree _ _ hd => exact absurd hd (by omega)
  | sort cell rl hu => exact fun _ => .sort cell rl hu
  | const cell ra rls hus => exact fun _ => .const cell ra rls hus
  | app cell _ _ ihf iha => exact fun d => .app cell (ihf d) (iha d)
  | lam cell _ _ rl iht ihb => exact fun d => .lam cell (iht d) (ihb d) rl
  | forallE cell _ _ rl iht ihb => exact fun d => .forallE cell (iht d) (ihb d) rl
  | letE cell _ _ _ iht ihv ihb => exact fun d => .letE cell (iht d) (ihv d) (ihb d)
  | litNat cell rl => exact fun _ => .litNat cell rl
  | litStr cell rb hs => exact fun _ => .litStr cell rb hs
  | proj cell ra _ ihe => exact fun d => .proj cell ra (ihe d)

theorem TmC.of_depth_zero {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ h 0 E p) : TmC κ h E p :=
  fun d _ => rep.of_depth_zero d

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
    ∃ i : F, x = .field i ∧
      ((i.val < k ∧ E = .bvar i.val) ∨
        (k ≤ i.val ∧ i.val - k < d ∧ E = .fvar (fvIdx d k i.val) (Γ (fvIdx d k i.val)))) := by
  cases rep with
  | bvarLocal cell hi =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; exact ⟨_, hx.symm, .inl ⟨hi, rfl⟩⟩
  | bvarFree cell hk hd =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; exact ⟨_, hx.symm, .inr ⟨hk, hd, rfl⟩⟩
  | sort cell _ _ | const cell _ _ _ | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _
  | letE cell _ _ _ | litNat cell _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.sort_of_load {x : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Srt" [x])) :
    ∃ u, E = .sort u ∧ LvRep h u x := by
  cases rep with
  | sort cell rl hu =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; subst hx; exact ⟨_, rfl, _, rl, hu⟩
  | bvarLocal cell _ | bvarFree cell _ _ | const cell _ _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.const_of_load {x y : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Const" [x, y])) :
    ∃ a us, E = .const (κ (ixAddr a)) us ∧ Bytes.RepAddressRef addrTy h a x ∧ LvListRep h us y := by
  cases rep with
  | const cell ra rls hus =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨_, _, rfl, ra, _, rls, hus⟩
  | bvarLocal cell _ | bvarFree cell _ _ | sort cell _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.app_of_load {x y : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "App" [x, y])) :
    ∃ Ef Ea, E = .app Ef Ea ∧ Tm κ d Γ h k Ef x ∧ Tm κ d Γ h k Ea y := by
  cases rep with
  | app cell rf ra =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨_, _, rfl, rf, ra⟩
  | bvarLocal cell _ | bvarFree cell _ _ | sort cell _ _ | const cell _ _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ | litStr cell _ _ | proj cell _ _ =>
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
  | bvarLocal cell _ | bvarFree cell _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ | litStr cell _ _ | proj cell _ _ =>
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
  | bvarLocal cell _ | bvarFree cell _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ | litStr cell _ _ | proj cell _ _ =>
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
  | bvarLocal cell _ | bvarFree cell _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | litNat cell _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.lit_of_load {x : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Lit" [x])) :
    (∃ lp limbs, x = .construct klitEnum "Nat" [lp] ∧ RepList limbListEnum RepU64 h limbs lp ∧
        E = .lit (.natVal (limbsVal limbs))) ∨
      (∃ bp bytes s, x = .construct klitEnum "Str" [bp] ∧
        Bytes.RepByteStream byteListEnum h bytes bp ∧ StrBytes s bytes ∧ E = .lit (.strVal s)) := by
  cases rep with
  | litNat cell rl =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; exact .inl ⟨_, _, hx.symm, rl, rfl⟩
  | litStr cell rb hs =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx; exact .inr ⟨_, _, _, hx.symm, rb, hs, rfl⟩
  | bvarLocal cell _ | bvarFree cell _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem Tm.proj_of_load {x y z : SourceValue F} (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Proj" [x, y, z])) :
    ∃ a (i : F) Es, y = .field i ∧ E = .proj (κ (ixAddr a)) i.val Es ∧
      Bytes.RepAddressRef addrTy h a x ∧ Tm κ d Γ h k Es z := by
  cases rep with
  | proj cell ra re =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy hrest'; injection hrest' with hz
    subst hx hz; exact ⟨_, _, _, hy.symm, rfl, ra, re⟩
  | bvarLocal cell _ | bvarFree cell _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ | litStr cell _ _ =>
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

end IxVM.Refinement.Core
