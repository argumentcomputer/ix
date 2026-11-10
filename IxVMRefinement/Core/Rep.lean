import IxVMRefinement.Core.Obs
import IxVMRefinement.Obs.Names
import Aiur.Library.IxVMRep
import IxVM.Field
import IxC.Kernel.Rules.Derived
import IxC.Kernel.Verify.InstList
import IxC.Kernel.Verify.InstLevels

/-! # The representation relation: IxVM heap terms and the kernel's `Expr`

A representation relation between IxVM heap terms and the kernel's `Expr` at an
opening depth. Design note.

## Two layers

1. **Heap to IxVM's own AST**: `Aiur.Library.IxVMRep.RepIxVMKExpr` relates a heap
   pointer to `IxVMKExpr F`, a de Bruijn AST with one constructor per
   `KernelTypes::KExprNode`, with heap monotonicity and determinism (reused).
2. **IxVM's AST to the kernel's `Expr`**: `Tr κ d Γ k t E` (below), a relation
   that is a partial function.
   * `k` is the local binder depth inside the term, `d` the kernel's opening
     depth, `Γ` a ghost context: the free variable `j` carries the type `Γ j`,
     as the rules require (`IxC/Kernel/Rules/Rel.lean` header).
   * `BVar i` with `i < k` is `.bvar i`; with `i - k < d` it is the free
     variable `.fvar (d-1-(i-k)) (Γ (d-1-(i-k)))`: IxVM's index counts from the
     inside, the kernel's free variable from the outside.
   * `Const a ls` is `.const (κ a) …` for the reader's keying `κ` (role-bound
     addresses to `.role r`, the others to `.id a`). Soundness needs no
     injectivity of `κ`: IxVM compares addresses, and equal addresses get equal
     keys.
   * Binders carry `nb = { pw := .never }` (Lean-fragment contracts).
   `RepE κ d Γ h E p` is the composite at local depth `0`.

IxVM's context list `types` is not part of the relation for terms: it is a
*segment* of the ghost context (entry `j` translates to `Γ (d-1-j)`), read only
by inference. The opening depth `d` is the segment's top end, so trimming its
outer entries (`ctx_trim`) leaves every image unchanged and needs no renaming
lemma (no bottom shift of the context is needed under this convention); lowering (`k_infer_rebase`, `k_def_eq_rebase`) leaves the images
unchanged but runs the inner computation at depth `d - g`, so its derivations
must be moved back to depth `d` by a depth-weakening lemma the rules do not have.

## Annotations

The kernel's binder datum `pw` (the codomain sort's zero-ness) is read by the
model's interpretation of `λ`/`∀` and by the rules at β (`Red.betaGate`), binder
congruence (`DefEq.lam`/`forallE`/`eta`) and binder inference
(`Infer.forallE`/`lam`). IxVM computes none. The relation writes `never` at every
binder. Then β is `Red.betaGate`, binder congruence's datum and contract
equalities are `rfl`; but a term is *graded* (the soundness theorems' premise)
only if none of its binders has a codomain that can be a proposition. So the
model facts proved here are about the data fragment, and `λ`-inference (whose
rule validates the datum by a sort computation IxVM never makes) has no rule.
Relating proofs (`λ h : p, …`) requires IxVM to carry and validate the datum;
the relation then reads it from the node.

## Lets, levels, literals, projections

* Lets: the rules have no ζ (the kernel's annotation pass substitutes lets
  away). The full relation ζ-expands; here a `Let` has no image, so a represented
  term has no let.
* Levels: the slice is level-free (`Const a []` only). The full relation must be
  up to level equivalence, because `DefEq` has no transitivity and IxVM's level
  instantiation simplifies.
* `Nat` literals translate to their value (limb order little-endian, not used
  by any proof here); string literals and projections have no image. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.IxVMRep Aiur.Library.List

abbrev F := IxVM.F

/-- The kernel's expressions, in the Ixon mode. -/
abbrev KExpr := Ix.Kernel.Expr .anon

/-- The binder datum the relation writes: `never`, Lean-fragment contracts. -/
abbrev nb : Ix.Kernel.BinderMeta := { pw := .never }

theorem nb_isNever : nb.pw.isNever = true := Ix.Kernel.PropWhen.isNever_never

/-! ## Names of the heap enums -/

abbrev kexprEnum : String := "KernelTypes::KExprNode"
abbrev kexprTy : Generic.Ty := .ptr (.named "KernelTypes::KExprNode" [])
abbrev kexprListEnum : String := Obs.Names.«Lists::Node<&KernelTypes::KExprNode>»
abbrev klevelTy : Generic.Ty := .ptr (.named "KernelTypes::KLevelNode" [])
abbrev klevelListEnum : String := Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>»
abbrev limbListEnum : String := nodeEnumName (.named "UInt64::U64" [])
abbrev byteListEnum : String := "${\"name\":\"Lists::Node\",\"types\":[\"field\"]}"
abbrev addrTy : Aiur.Ty := .tuple (List.replicate 32 .field)
abbrev kciEnum : String := "KernelTypes::KConstantInfo"

@[simp] theorem kexpr_ctor :
    constructorName [] (.named "KernelTypes::KExprNode" []) = kexprEnum := by decide +kernel

@[simp] theorem kexprList_ctor :
    constructorName [] (.named "Lists::Node" [kexprTy]) = kexprListEnum := by decide +kernel

@[simp] theorem kexprList_inst :
    instanceName [] "Lists::Node" (some [kexprTy]) = kexprListEnum := by decide +kernel

@[simp] theorem klevelList_ctor :
    constructorName [] (.named "Lists::Node" [klevelTy]) = klevelListEnum := by decide +kernel

@[simp] theorem kci_ctor :
    constructorName [] (.named "KernelTypes::KConstantInfo" []) = kciEnum := by decide +kernel

theorem loadValue_enum_cell {enumName : String} {heap : Heap F} {addr : Nat}
    {c : String} {xs : List (SourceValue F)}
    (cell : heap[addr]? = some (.construct enumName c xs)) :
    loadValue heap (.ptr (.enum enumName) addr) = .ok (.construct enumName c xs) := by
  simp [loadValue, cell, Value.type, bind, Except.bind, pure, Except.pure]

/-! ## Layer 1: the heap -/

/-- IxVM's term AST at a heap pointer. -/
abbrev RepK (h : Heap F) (t : IxVMKExpr F) (p : SourceValue F) : Prop :=
  RepIxVMKExpr addrTy klevelListEnum limbListEnum byteListEnum h t p

theorem RepK.mono {h₁ h₂ : Heap F} {t : IxVMKExpr F} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepK h₁ t p) : RepK h₂ t p :=
  RepIxVMKExpr.mono ext rep

/-- The cell of a pointer whose loaded value is an `App` node. -/
theorem RepK.app_of_load {h : Heap F} {t : IxVMKExpr F} {p x y : SourceValue F}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "App" [x, y])) :
    ∃ f a, t = .app f a ∧ RepK h f x ∧ RepK h a y := by
  cases rep with
  | app cell rf ra =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs
    injection hargs with hx hrest; injection hrest with hy _
    subst hx hy
    exact ⟨_, _, rfl, rf, ra⟩
  | bvar cell | sort cell _ | const cell _ _ | lam cell _ _ | forallE cell _ _
  | letE cell _ _ _ | litNat cell _ | litStr cell _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

theorem RepK.lam_of_load {h : Heap F} {t : IxVMKExpr F} {p x y : SourceValue F}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "Lam" [x, y])) :
    ∃ ty b, t = .lam ty b ∧ RepK h ty x ∧ RepK h b y := by
  cases rep with
  | lam cell rt rb =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs
    injection hargs with hx hrest; injection hrest with hy _
    subst hx hy
    exact ⟨_, _, rfl, rt, rb⟩
  | bvar cell | sort cell _ | const cell _ _ | app cell _ _ | forallE cell _ _
  | letE cell _ _ _ | litNat cell _ | litStr cell _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

theorem RepK.const_of_load {h : Heap F} {t : IxVMKExpr F} {p x y : SourceValue F}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "Const" [x, y])) :
    ∃ a ls, t = .const a ls ∧ Bytes.RepAddressRef addrTy h a x ∧
      RepList klevelListEnum RepIxVMKUniv h ls y := by
  cases rep with
  | const cell ra rl =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs
    injection hargs with hx hrest; injection hrest with hy _
    subst hx hy
    exact ⟨_, _, rfl, ra, rl⟩
  | bvar cell | sort cell _ | app cell _ _ | lam cell _ _ | forallE cell _ _
  | letE cell _ _ _ | litNat cell _ | litStr cell _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

theorem RepK.let_of_load {h : Heap F} {t : IxVMKExpr F} {p : SourceValue F}
    {xs : List (SourceValue F)}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "Let" xs)) :
    ∃ ty v b, t = .letE ty v b := by
  cases rep with
  | letE cell _ _ _ => exact ⟨_, _, _, rfl⟩
  | bvar cell | sort cell _ | const cell _ _ | app cell _ _ | lam cell _ _
  | forallE cell _ _ | litNat cell _ | litStr cell _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

theorem RepK.proj_of_load {h : Heap F} {t : IxVMKExpr F} {p : SourceValue F}
    {xs : List (SourceValue F)}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "Proj" xs)) :
    ∃ a i e, t = .proj a i e := by
  cases rep with
  | proj cell _ _ => exact ⟨_, _, _, rfl⟩
  | bvar cell | sort cell _ | const cell _ _ | app cell _ _ | lam cell _ _
  | forallE cell _ _ | letE cell _ _ _ | litNat cell _ | litStr cell _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

/-- A stored `App` node of two represented terms. -/
theorem RepK.store_app {h : Heap F} {f a : IxVMKExpr F} {fp ap : SourceValue F}
    (rf : RepK h f fp) (ra : RepK h a ap) :
    RepK (h ++ [.construct kexprEnum "App" [fp, ap]]) (.app f a)
      (.ptr (.enum kexprEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "App" [fp, ap]]) := Heap.Extends.snoc h _
  exact .app (by simp) (rf.mono ext) (ra.mono ext)

/-! ### Lists -/

theorem RepList.nil_of_load {α : Type} {enumName : String}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F} {xs : List α} {p : SourceValue F}
    (rep : RepList enumName R h xs p) (hl : loadValue h p = .ok (.construct enumName "Nil" [])) :
    xs = [] := by
  cases rep with
  | nil _ => rfl
  | cons cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

theorem RepList.cons_of_load {α : Type} {enumName : String}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F} {xs : List α} {p x y : SourceValue F}
    (rep : RepList enumName R h xs p)
    (hl : loadValue h p = .ok (.construct enumName "Cons" [x, y])) :
    ∃ z zs, xs = z :: zs ∧ R h z x ∧ RepList enumName R h zs y := by
  cases rep with
  | nil cell =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)
  | cons cell rh rt =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs
    injection hargs with hx hrest; injection hrest with hy _
    subst hx hy
    exact ⟨_, _, rfl, rh, rt⟩

/-! ## Layer 2: the translation -/

/-- IxVM's levels to the kernel's. -/
def trLevel : IxVMKUniv F → Ix.Kernel.Level
  | .zero => .zero
  | .succ u => .succ (trLevel u)
  | .max u v => .max (trLevel u) (trLevel v)
  | .imax u v => .imax (trLevel u) (trLevel v)
  | .param i => .param (ZMod.val i)

/-- The value of a little-endian limb list. -/
def limbsVal : List UInt64 → Nat
  | [] => 0
  | l :: ls => l.toNat + 18446744073709551616 * limbsVal ls

/-- **The translation**, at local binder depth `k`, opening depth `d` and ghost
context `Γ`, under the keying `κ`. -/
inductive Tr (κ : Bytes.Address → Ix.Kernel.Key .anon) (d : Nat) (Γ : Nat → KExpr) :
    Nat → IxVMKExpr F → KExpr → Prop where
  | bvarLocal {k : Nat} {i : F} (hi : (ZMod.val i) < k) : Tr κ d Γ k (.bvar i) (.bvar (ZMod.val i))
  | bvarFree {k : Nat} {i : F} (hk : k ≤ (ZMod.val i)) (hd : (ZMod.val i) - k < d) :
      Tr κ d Γ k (.bvar i) (.fvar (d - 1 - ((ZMod.val i) - k)) (Γ (d - 1 - ((ZMod.val i) - k))))
  | sort {k : Nat} {l : IxVMKUniv F} : Tr κ d Γ k (.sort l) (.sort (trLevel l))
  | const {k : Nat} {a : Bytes.Address} : Tr κ d Γ k (.const a []) (.const (κ a) [])
  | app {k : Nat} {f a : IxVMKExpr F} {Ef Ea : KExpr} :
      Tr κ d Γ k f Ef → Tr κ d Γ k a Ea → Tr κ d Γ k (.app f a) (.app Ef Ea)
  | lam {k : Nat} {ty b : IxVMKExpr F} {T B : KExpr} :
      Tr κ d Γ k ty T → Tr κ d Γ (k + 1) b B → Tr κ d Γ k (.lam ty b) (.lam T B nb)
  | forallE {k : Nat} {ty b : IxVMKExpr F} {T B : KExpr} :
      Tr κ d Γ k ty T → Tr κ d Γ (k + 1) b B → Tr κ d Γ k (.forallE ty b) (.forallE T B nb)
  | litNat {k : Nat} {limbs : List UInt64} :
      Tr κ d Γ k (.litNat limbs) (.lit (.natVal (limbsVal limbs)))

theorem Tr.app_inv {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {f a : IxVMKExpr F} {E : KExpr} (h : Tr κ d Γ k (.app f a) E) :
    ∃ Ef Ea, E = .app Ef Ea ∧ Tr κ d Γ k f Ef ∧ Tr κ d Γ k a Ea := by
  cases h; exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem Tr.lam_inv {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {ty b : IxVMKExpr F} {E : KExpr} (h : Tr κ d Γ k (.lam ty b) E) :
    ∃ T B, E = .lam T B nb ∧ Tr κ d Γ k ty T ∧ Tr κ d Γ (k + 1) b B := by
  cases h; exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem Tr.const_inv {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {a : Bytes.Address} {ls : List (IxVMKUniv F)} {E : KExpr}
    (h : Tr κ d Γ k (.const a ls) E) : ls = [] ∧ E = .const (κ a) [] := by
  cases h; exact ⟨rfl, rfl⟩

theorem Tr.let_inv {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {ty v b : IxVMKExpr F} {E : KExpr} (h : Tr κ d Γ k (.letE ty v b) E) : False := by
  cases h

theorem Tr.proj_inv {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {a : Bytes.Address} {i : F} {e : IxVMKExpr F} {E : KExpr}
    (h : Tr κ d Γ k (.proj a i e) E) : False := by
  cases h

/-- A closed term translates the same at every depth and context. -/
theorem Tr.closed {κ : Bytes.Address → Ix.Kernel.Key .anon} {Γ Γ' : Nat → KExpr} {k : Nat}
    {t : IxVMKExpr F} {E : KExpr} (h : Tr κ 0 Γ k t E) : ∀ d, Tr κ d Γ' k t E := by
  induction h with
  | bvarLocal hi => exact fun _ => .bvarLocal hi
  | bvarFree _ hd => exact absurd hd (by omega)
  | sort => exact fun _ => .sort
  | const => exact fun _ => .const
  | app _ _ ihf iha => exact fun d => .app (ihf d) (iha d)
  | lam _ _ iht ihb => exact fun d => .lam (iht d) (ihb d)
  | forallE _ _ iht ihb => exact fun d => .forallE (iht d) (ihb d)
  | litNat => exact fun _ => .litNat

/-! ## The composite relation -/

section
variable (κ : Bytes.Address → Ix.Kernel.Key .anon) (d : Nat) (Γ : Nat → KExpr)

/-- **The representation relation** at local depth `k`: the heap term at `p`
translates to `E`. -/
def RepEk (k : Nat) (h : Heap F) (E : KExpr) (p : SourceValue F) : Prop :=
  ∃ t, RepK h t p ∧ Tr κ d Γ k t E

/-- **The representation relation** of a top-level term. -/
abbrev RepE : Heap F → KExpr → SourceValue F → Prop := RepEk κ d Γ 0

/-- A list of terms (`Lists::List<KExpr>`), elementwise. -/
abbrev RepSpine (h : Heap F) (As : List KExpr) (p : SourceValue F) : Prop :=
  RepList kexprListEnum (RepE κ d Γ) h As p

/-- A closed term: represented at every depth and context. -/
def RepEc (h : Heap F) (E : KExpr) (p : SourceValue F) : Prop :=
  ∀ d' (Γ' : Nat → KExpr), RepE κ d' Γ' h E p

end

theorem RepEk.mono {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {h₁ h₂ : Heap F} {E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepEk κ d Γ k h₁ E p) : RepEk κ d Γ k h₂ E p := by
  obtain ⟨t, rt, tt⟩ := rep
  exact ⟨t, rt.mono ext, tt⟩

theorem repE_heapMono₂ {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat}
    {Γ : Nat → KExpr} : HeapMono₂ (RepE κ d Γ) :=
  fun _ _ _ _ ext rep => RepEk.mono ext rep

theorem RepSpine.mono {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat}
    {Γ : Nat → KExpr} {h₁ h₂ : Heap F} {As : List KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepSpine κ d Γ h₁ As p) : RepSpine κ d Γ h₂ As p :=
  repList_heapMono₂ kexprListEnum repE_heapMono₂ ext rep

theorem RepEc.mono {κ : Bytes.Address → Ix.Kernel.Key .anon} {h₁ h₂ : Heap F}
    {E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepEc κ h₁ E p) : RepEc κ h₂ E p :=
  fun d Γ => RepEk.mono ext (rep d Γ)

theorem RepE.store_app {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat}
    {Γ : Nat → KExpr} {h : Heap F} {Ef Ea : KExpr} {fp ap : SourceValue F}
    (rf : RepE κ d Γ h Ef fp) (ra : RepE κ d Γ h Ea ap) :
    RepE κ d Γ (h ++ [.construct kexprEnum "App" [fp, ap]]) (.app Ef Ea)
      (.ptr (.enum kexprEnum) h.length) := by
  obtain ⟨tf, rtf, ttf⟩ := rf
  obtain ⟨ta, rta, tta⟩ := ra
  exact ⟨_, RepK.store_app rtf rta, .app ttf tta⟩

theorem RepSpine.store_nil {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat}
    {Γ : Nat → KExpr} (h : Heap F) :
    RepSpine κ d Γ (h ++ [.construct kexprListEnum "Nil" []]) []
      (.ptr (.enum kexprListEnum) h.length) :=
  allocNil_rep kexprListEnum (RepE κ d Γ) h

/-! ## Kernel-side spine algebra and the β chain -/

namespace K
open Ix.Kernel.Rules

abbrev mkAppN : KExpr → List KExpr → KExpr := Ix.Kernel.Expr.mkAppN

theorem mkAppN_append : ∀ (As Bs : List KExpr) (f : KExpr),
    mkAppN f (As ++ Bs) = mkAppN (mkAppN f As) Bs
  | [], _, _ => rfl
  | a :: As, Bs, f => by
    show mkAppN (.app f a) (As ++ Bs) = mkAppN (mkAppN (.app f a) As) Bs
    exact mkAppN_append As Bs (.app f a)

theorem mkAppN_snoc (f a : KExpr) (As : List KExpr) :
    mkAppN f (As ++ [a]) = .app (mkAppN f As) a := by
  rw [mkAppN_append]; rfl

theorem getAppFn_mkAppN : ∀ (As : List KExpr) (f : KExpr),
    (mkAppN f As).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: As, f => by
    show (mkAppN (.app f a) As).getAppFn = f.getAppFn
    rw [getAppFn_mkAppN As (.app f a)]
    rfl

theorem getAppArgs_mkAppN : ∀ (As : List KExpr) (f : KExpr),
    (mkAppN f As).getAppArgs = f.getAppArgs ++ As
  | [], f => by simp [mkAppN, Ix.Kernel.Expr.mkAppN]
  | a :: As, f => by
    show (mkAppN (.app f a) As).getAppArgs = f.getAppArgs ++ a :: As
    rw [getAppArgs_mkAppN As (.app f a)]
    simp [Ix.Kernel.Expr.getAppArgs]

theorem red_mkAppN {env : Ix.Kernel.Env .anon} {d : Nat} : ∀ (As : List KExpr) {f f' : KExpr},
    Red env d f f' → Red env d (mkAppN f As) (mkAppN f' As)
  | [], _, _, h => h
  | _ :: As, _, _, h => red_mkAppN As (.appFn h)

/-- A telescope of `λ`s with the datum `never`, outermost first. -/
def lams : List KExpr → KExpr → KExpr
  | [], D => D
  | T :: Ts, D => .lam T (lams Ts D) nb

theorem lams_instantiate1 : ∀ (Ts : List KExpr) (D v : KExpr) (k : Nat),
    ∃ Ts' : List KExpr, Ts'.length = Ts.length ∧
      (lams Ts D).instantiate1 v k = lams Ts' (D.instantiate1 v (k + Ts.length))
  | [], D, v, k => ⟨[], rfl, by simp [lams]⟩
  | T :: Ts, D, v, k => by
    obtain ⟨Ts', hlen, heq⟩ := lams_instantiate1 Ts D v (k + 1)
    refine ⟨T.instantiate1 v k :: Ts', by simp [hlen], ?_⟩
    have hk : k + 1 + Ts.length = k + (T :: Ts).length := by simp; omega
    show Ix.Kernel.Expr.instantiate1 (.lam T (lams Ts D) nb) v k = _
    rw [Ix.Kernel.Expr.instantiate1, heq, hk]
    rfl

/-- **The β chain**: a `never`-datum `λ`-telescope applied to as many arguments
as it has binders, then to `rest`, reduces to its body under the reversed
arguments, applied to `rest`: a chain of `Red.betaGate` under the spine
congruence, folded by `instantiateList_append_one`. -/
theorem red_beta_chain {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (As : List KExpr) (Ts : List KExpr) (D : KExpr) (rest : List KExpr),
      Ts.length = As.length →
      Red env d (mkAppN (lams Ts D) (As ++ rest))
        (mkAppN (D.instantiateList As.reverse 0) rest)
  | [], Ts, D, rest, hlen => by
    match Ts, hlen with
    | [], _ =>
      show Red env d (mkAppN D rest) (mkAppN (D.instantiateList [] 0) rest)
      rw [Ix.Kernel.Expr.instantiateList_nil]
      exact .refl
    | _ :: _, hlen => simp at hlen
  | A :: As, Ts, D, rest, hlen => by
    match Ts, hlen with
    | [], hlen => simp at hlen
    | T :: Ts, hlen =>
      have hlen' : Ts.length = As.length := by simpa using hlen
      obtain ⟨Ts', hlen'', heq⟩ := lams_instantiate1 Ts D A 0
      have hstep : Red env d (mkAppN (lams (T :: Ts) D) ((A :: As) ++ rest))
          (mkAppN (lams Ts' (D.instantiate1 A (0 + Ts.length))) (As ++ rest)) := by
        show Red env d (mkAppN (.app (.lam T (lams Ts D) nb) A) (As ++ rest)) _
        rw [← heq]
        exact red_mkAppN _ (.betaGate nb_isNever)
      have hrest := red_beta_chain (env := env) (d := d) As Ts' (D.instantiate1 A (0 + Ts.length)) rest
        (by rw [hlen'', hlen'])
      have hfold : (D.instantiate1 A (0 + Ts.length)).instantiateList As.reverse 0 =
          D.instantiateList (A :: As).reverse 0 := by
        rw [List.reverse_cons, Ix.Kernel.Expr.instantiateList_append_one, List.length_reverse,
          hlen']
      rw [hfold] at hrest
      exact .trans hstep hrest

/-- `δ` at a level-free constant head: the unfolding is the stored value applied
to the spine. -/
theorem unfold_const_head {env : Ix.Kernel.Env .anon} {n : Ix.Kernel.Key .anon}
    {cv : Ix.Kernel.ConstantVal .anon} {V : KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (As : List KExpr)
    (hfind : env.find? n = some (.defnInfo cv V hint)) (hlp : cv.levelParams = []) :
    Ix.Kernel.unfoldDefinition env (mkAppN (.const n []) As) = some (mkAppN V As) := by
  have hfn : (mkAppN (.const n []) As).getAppFn = .const n [] := by
    rw [getAppFn_mkAppN]; rfl
  have hargs : (mkAppN (.const n []) As).getAppArgs = As := by
    rw [getAppArgs_mkAppN]; rfl
  have hinst : V.instantiateLevelParams [] [] = V := Ix.Kernel.Expr.instantiateLevelParams_self [] V
  simp [Ix.Kernel.unfoldDefinition, hfn, hfind, hargs, hlp, hinst]

end K

end IxVM.Refinement.Core
