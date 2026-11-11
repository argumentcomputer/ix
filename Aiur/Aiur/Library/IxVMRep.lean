import Aiur.HeapMono
import Aiur.Library.U64.Correctness
import Aiur.Library.List.Correctness
import Aiur.Library.Bytes.Correctness
import Aiur.Library.RBTreeMap.Correctness
import Aiur.Library.Blake3.Correctness

/-!
# `IxVM` Heap Representation Predicates, Monotonicity, Determinism, and Deserialization Lemmas

This module defines Lean reference models of IxVM's data (universes, expressions,
role tables) and predicates relating them to `SourceValue F` heap values. They
are models written after the IxVM sources, groundwork for a future proof of
correspondence with the IxVM program; nothing here evaluates an IxVM `.aiur`
function or proves anything about one. It provides:
1. Determinism/injectivity (`det`) for primitive and container representation
   predicates (`RepU8`, `RepU32`, `RepU64`, `RepAddress`, `RepAddressRef`,
   `RepOption`, `RepLinkedList`, `RepList`, `RepBinaryTree`, `RepRBTreePtr`).
2. Mathematical ASTs and `SourceValue F` heap representation predicates for:
   - `IxVMUniv` (`Zero | Succ | Max | IMax | Var`) & `RepIxVMUniv`
   - `IxVMIExpr` (`Srt | Var | Ref | Rec | Prj | Str | Nat | App | Lam | All | Let | Share`) & `RepIxVMIExpr`
   - `IxVMKUniv` (`Zero | Succ | Max | IMax | Param`) & `RepIxVMKUniv`
   - `IxVMKExpr` (`BVar | Sort | Const | App | Lam | ForallE | LetE | LitNat | LitStr | Proj`) & `RepIxVMKExpr`
   - `IxVMRoleEvidence`, `IxVMRoleTable`, `IxVMRoleCtx` & `RepRoleEvidence`, `RepRoleTable`, `RepRoleCtx`
3. `HeapMono` (`Heap.Extends h₁ h₂ → Rep* h₁ x v → Rep* h₂ x v`) and determinism /
   injectivity (`Rep* h x₁ v → Rep* h x₂ v → x₁ = x₂`) for each `IxVM` predicate.
4. Ingress stream authentication (`ingress_verify_stream_sound`) and `TagN`
   header / multi-byte `UInt64` decoding lemmas (`tag_header_split_unique`,
   `tagn4_header_split_unique`, `tagn2_header_split_unique`, `u64OfLeBytes_*`,
   and `tagn_tail_two_byte_spec`).
-/

namespace Aiur.Library.IxVMRep

open Aiur
open Aiur.Library
open Aiur.Library.List
open Aiur.Library.Bytes
open Aiur.Library.RBTreeMap

variable {F : Type}

/-! ## 1. Determinism of Primitive and Container Representation Predicates -/

theorem nat_lt_256_inj [Field F] (large : U32.Compatible F) {a b : Nat}
    (ha : a < 256) (hb : b < 256) (heq : (a : F) = (b : F)) : a = b := by
  have ha' : a < 3 * U32.base := by unfold U32.base; omega
  have hb' : b < 3 * U32.base := by unfold U32.base; omega
  exact large ha' hb' heq

private theorem limb_eq_of_tuple_eq [Field F] (large : U32.Compatible F)
    {n w₁ w₂ : Nat}
    (hTuple : (_root_.List.range n).map (fun i => (Value.field (((w₁ / 256 ^ i) % 256 : Nat) : F) : SourceValue F)) =
              (_root_.List.range n).map (fun i => (Value.field (((w₂ / 256 ^ i) % 256 : Nat) : F) : SourceValue F)))
    (i : Nat) (hi : i < n) :
    (w₁ / 256 ^ i) % 256 = (w₂ / 256 ^ i) % 256 := by
  have hElem := congrArg (fun xs : _root_.List (SourceValue F) => xs[i]?) hTuple
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq, Value.field.injEq] at hElem
  exact nat_lt_256_inj large (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hElem

private theorem nat_eq_of_byte_limbs : ∀ (n a b : Nat),
    a < 256 ^ n → b < 256 ^ n →
    (∀ i < n, (a / 256 ^ i) % 256 = (b / 256 ^ i) % 256) → a = b
  | 0, a, b, ha, hb, _ => by omega
  | n + 1, a, b, ha, hb, h => by
      have h0 := h 0 (Nat.zero_lt_succ n)
      simp only [Nat.pow_zero, Nat.div_one] at h0
      have hPowEq : 256 ^ (n + 1) = 256 ^ n * 256 := Nat.pow_succ 256 n
      have hDiv : a / 256 = b / 256 :=
        nat_eq_of_byte_limbs n (a / 256) (b / 256)
          (Nat.div_lt_of_lt_mul (by omega))
          (Nat.div_lt_of_lt_mul (by omega))
          (fun i hi => by
            have hi' := h (i + 1) (Nat.succ_lt_succ hi)
            have hPow : 256 ^ (i + 1) = 256 * 256 ^ i := by
              rw [Nat.pow_succ, Nat.mul_comm]
            rw [hPow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at hi'
            exact hi')
      have ha' := Nat.div_add_mod a 256
      have hb' := Nat.div_add_mod b 256
      omega

theorem repU32_det [Field F] (large : U32.Compatible F) {h : Heap F}
    {w₁ w₂ : UInt32} {v : SourceValue F}
    (h₁ : RepU32 h w₁ v) (h₂ : RepU32 h w₂ v) : w₁ = w₂ := by
  have hTuple := Value.tuple.inj (h₁.symm.trans h₂)
  exact UInt32.ext (nat_eq_of_byte_limbs 4 w₁.toNat w₂.toNat w₁.toNat_lt w₂.toNat_lt
    (fun i hi => limb_eq_of_tuple_eq large hTuple i hi))

theorem repU64_det [Field F] (large : U32.Compatible F) {h : Heap F}
    {w₁ w₂ : UInt64} {v : SourceValue F}
    (h₁ : RepU64 h w₁ v) (h₂ : RepU64 h w₂ v) : w₁ = w₂ := by
  have hTuple := Value.tuple.inj (h₁.symm.trans h₂)
  exact UInt64.ext (nat_eq_of_byte_limbs 8 w₁.toNat w₂.toNat w₁.toNat_lt w₂.toNat_lt
    (fun i hi => limb_eq_of_tuple_eq large hTuple i hi))

private theorem list_map_u8_field_inj [Field F] (large : U32.Compatible F)
    {xs ys : _root_.List UInt8}
    (h : xs.map (fun b : UInt8 => (Value.field (b.toNat : F) : SourceValue F)) =
         ys.map (fun b : UInt8 => (Value.field (b.toNat : F) : SourceValue F))) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp at h ⊢
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          exact List.cons_eq_cons.mpr ⟨repU8_inj large (h := ([] : Heap F)) rfl h.1, ih h.2⟩

theorem repAddress_det [Field F] (large : U32.Compatible F) {h : Heap F}
    {a₁ a₂ : Address} {v : SourceValue F}
    (h₁ : RepAddress h a₁ v) (h₂ : RepAddress h a₂ v) : a₁ = a₂ := by
  have hTuple := Value.tuple.inj (h₁.symm.trans h₂)
  exact Vector.toList_inj.mp (list_map_u8_field_inj large hTuple)

theorem repAddressRef_det [Field F] (large : U32.Compatible F) {ty : Ty} {h : Heap F}
    {a₁ a₂ : Address} {ptr : SourceValue F}
    (h₁ : RepAddressRef ty h a₁ ptr) (h₂ : RepAddressRef ty h a₂ ptr) : a₁ = a₂ := by
  obtain ⟨addr₁, v₁, hptr₁, hcell₁, hrep₁⟩ := h₁
  obtain ⟨addr₂, v₂, hptr₂, hcell₂, hrep₂⟩ := h₂
  rw [hptr₁] at hptr₂
  injection hptr₂ with _ hAddr
  subst hAddr
  rw [hcell₁] at hcell₂
  injection hcell₂ with hVal
  subst hVal
  exact repAddress_det large hrep₁ hrep₂

theorem repOption_det {α : Type*} {enumName : String}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F}
    (hR : ∀ {x₁ x₂ v}, R h x₁ v → R h x₂ v → x₁ = x₂)
    {o₁ o₂ : Option α} {v : SourceValue F}
    (h₁ : RepOption enumName R h o₁ v) (h₂ : RepOption enumName R h o₂ v) :
    o₁ = o₂ := by
  revert h₂
  generalize hv : v = v'
  intro h₂
  cases h₁ with
  | none =>
      cases h₂ with
      | none => rfl
      | some _ =>
          injection hv with _ hCtor _
          exact absurd hCtor (by decide)
  | some hv₁ =>
      cases h₂ with
      | none =>
          injection hv with _ hCtor _
          exact absurd hCtor (by decide)
      | some hv₂ =>
          injection hv with _ _ hArgs
          injection hArgs with hVal _
          subst hVal
          exact congrArg some (hR hv₁ hv₂)

theorem repLinkedList_det {α : Type*} {enumName nilCtor consCtor : String}
    (hNe : nilCtor ≠ consCtor)
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F}
    (hR : ∀ {x₁ x₂ v}, R h x₁ v → R h x₂ v → x₁ = x₂)
    {xs₁ xs₂ : _root_.List α} {ptr : SourceValue F}
    (h₁ : RepLinkedList enumName nilCtor consCtor R h xs₁ ptr)
    (h₂ : RepLinkedList enumName nilCtor consCtor R h xs₂ ptr) :
    xs₁ = xs₂ := by
  induction h₁ generalizing xs₂ with
  | nil cell₁ =>
      cases h₂ with
      | nil _ => rfl
      | cons cell₂ _ _ =>
          rw [cell₁] at cell₂
          injection cell₂ with hVal
          injection hVal with _ hCtor _
          exact absurd hCtor hNe
  | cons cell₁ headRep₁ _ ih =>
      cases h₂ with
      | nil cell₂ =>
          rw [cell₁] at cell₂
          injection cell₂ with hVal
          injection hVal with _ hCtor _
          exact absurd hCtor.symm hNe
      | cons cell₂ headRep₂ tailRep₂ =>
          rw [cell₁] at cell₂
          injection cell₂ with hVal
          injection hVal with _ _ hArgs
          injection hArgs with hHead hTail
          injection hTail with hTailPtr _
          subst hHead hTailPtr
          exact List.cons_eq_cons.mpr ⟨hR headRep₁ headRep₂, ih tailRep₂⟩

theorem repList_det {α : Type*} {enumName : String}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F}
    (hR : ∀ {x₁ x₂ v}, R h x₁ v → R h x₂ v → x₁ = x₂)
    {xs₁ xs₂ : _root_.List α} {ptr : SourceValue F}
    (h₁ : RepList enumName R h xs₁ ptr)
    (h₂ : RepList enumName R h xs₂ ptr) :
    xs₁ = xs₂ :=
  repLinkedList_det (by decide) hR h₁ h₂

theorem repBinaryTree_det {α : Type*} {enumName leafCtor branchCtor : String}
    (hNe : leafCtor ≠ branchCtor)
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F}
    (hR : ∀ {x₁ x₂ v}, R h x₁ v → R h x₂ v → x₁ = x₂)
    {t₁ t₂ : BinaryTree α} {ptr : SourceValue F}
    (h₁ : RepBinaryTree enumName leafCtor branchCtor R h t₁ ptr)
    (h₂ : RepBinaryTree enumName leafCtor branchCtor R h t₂ ptr) :
    t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | leaf cell₁ =>
      cases h₂ with
      | leaf _ => rfl
      | branch cell₂ _ _ _ =>
          rw [cell₁] at cell₂
          injection cell₂ with hVal
          injection hVal with _ hCtor _
          exact absurd hCtor hNe
  | branch cell₁ labelRep₁ _ _ ihl ihr =>
      cases h₂ with
      | leaf cell₂ =>
          rw [cell₁] at cell₂
          injection cell₂ with hVal
          injection hVal with _ hCtor _
          exact absurd hCtor.symm hNe
      | branch cell₂ labelRep₂ leftRep₂ rightRep₂ =>
          rw [cell₁] at cell₂
          injection cell₂ with hVal
          injection hVal with _ _ hArgs
          injection hArgs with hLbl hRest₁
          injection hRest₁ with hLeft hRest₂
          injection hRest₂ with hRight _
          subst hLbl hLeft hRight
          rw [hR labelRep₁ labelRep₂, ihl leftRep₂, ihr rightRep₂]

theorem repRBTreePtr_det {K V : Type*} {enumName nilCtor nodeCtor : String}
    (hNe : nilCtor ≠ nodeCtor)
    {RLabel : Heap F → (Nat × K × V) → SourceValue F → Prop} {h : Heap F}
    (hR : ∀ {x₁ x₂ v}, RLabel h x₁ v → RLabel h x₂ v → x₁ = x₂)
    {t₁ t₂ : RBTree K V} {ptr : SourceValue F}
    (h₁ : RepRBTreePtr enumName nilCtor nodeCtor RLabel h t₁ ptr)
    (h₂ : RepRBTreePtr enumName nilCtor nodeCtor RLabel h t₂ ptr) :
    t₁ = t₂ := by
  have hBin := repBinaryTree_det hNe hR h₁ h₂
  have hOf := congrArg RBTree.ofBinaryTree hBin
  rwa [RBTree.ofBinaryTree_toBinaryTree, RBTree.ofBinaryTree_toBinaryTree] at hOf

/-! ## 2. `IxVMUniv` (`Ixon::Univ`) Representation, `HeapMono`, and Determinism -/

/-- Mathematical AST of `Ixon::Univ` universe levels. -/
inductive IxVMUniv where
  | zero : IxVMUniv
  | succ (u : IxVMUniv) : IxVMUniv
  | max (u v : IxVMUniv) : IxVMUniv
  | imax (u v : IxVMUniv) : IxVMUniv
  | var (idx : UInt64) : IxVMUniv
  deriving Repr, DecidableEq

/-- Heap representation predicate for `Ixon::Univ` values. -/
inductive RepIxVMUniv [NatCast F] (h : Heap F) : IxVMUniv → SourceValue F → Prop where
  | zero :
      RepIxVMUniv h .zero (.construct "Ixon::Univ" "Zero" [])
  | succ {u : IxVMUniv} {addr : Nat} {uVal : SourceValue F}
      (cell : h[addr]? = some uVal)
      (inner : RepIxVMUniv h u uVal) :
      RepIxVMUniv h (.succ u) (.construct "Ixon::Univ" "Succ" [.ptr (.enum "Ixon::Univ") addr])
  | max {u v : IxVMUniv} {a₁ a₂ : Nat} {uVal vVal : SourceValue F}
      (cell₁ : h[a₁]? = some uVal)
      (cell₂ : h[a₂]? = some vVal)
      (left : RepIxVMUniv h u uVal)
      (right : RepIxVMUniv h v vVal) :
      RepIxVMUniv h (.max u v)
        (.construct "Ixon::Univ" "Max"
          [.ptr (.enum "Ixon::Univ") a₁, .ptr (.enum "Ixon::Univ") a₂])
  | imax {u v : IxVMUniv} {a₁ a₂ : Nat} {uVal vVal : SourceValue F}
      (cell₁ : h[a₁]? = some uVal)
      (cell₂ : h[a₂]? = some vVal)
      (left : RepIxVMUniv h u uVal)
      (right : RepIxVMUniv h v vVal) :
      RepIxVMUniv h (.imax u v)
        (.construct "Ixon::Univ" "IMax"
          [.ptr (.enum "Ixon::Univ") a₁, .ptr (.enum "Ixon::Univ") a₂])
  | var {idx : UInt64} {idxVal : SourceValue F}
      (repIdx : RepU64 h idx idxVal) :
      RepIxVMUniv h (.var idx) (.construct "Ixon::Univ" "Var" [idxVal])

theorem RepIxVMUniv.mono [NatCast F] {h₁ h₂ : Heap F} {u : IxVMUniv} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepIxVMUniv h₁ u v) :
    RepIxVMUniv h₂ u v := by
  induction rep with
  | zero => exact .zero
  | succ cell _ ih => exact .succ (ext.getElem?_eq cell) ih
  | max cell₁ cell₂ _ _ ihl ihr =>
      exact .max (ext.getElem?_eq cell₁) (ext.getElem?_eq cell₂) ihl ihr
  | imax cell₁ cell₂ _ _ ihl ihr =>
      exact .imax (ext.getElem?_eq cell₁) (ext.getElem?_eq cell₂) ihl ihr
  | var repIdx => exact .var (repU64_heapMono₂ ext repIdx)

theorem HeapMono.repIxVMUniv [NatCast F] (u : IxVMUniv) :
    HeapMono (fun h v => RepIxVMUniv (F := F) h u v) :=
  fun _ _ _ ext rep => rep.mono ext

theorem RepIxVMUniv.det [Field F] (large : U32.Compatible F) {h : Heap F}
    {u₁ u₂ : IxVMUniv} {v : SourceValue F}
    (h₁ : RepIxVMUniv h u₁ v) (h₂ : RepIxVMUniv h u₂ v) : u₁ = u₂ := by
  induction h₁ generalizing u₂ with
  | zero =>
      revert h₂; generalize hv : Value.construct "Ixon::Univ" "Zero" [] = v'; intro h₂
      cases h₂ <;> (try (injection hv with _ hCtor _; exact absurd hCtor (by decide)))
      rfl
  | succ cell₁ _ ih =>
      revert h₂; generalize hv : Value.construct "Ixon::Univ" "Succ" [Value.ptr (Ty.enum "Ixon::Univ") _] = v'; intro h₂
      cases h₂ <;> (try (injection hv with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i cell₂ inner₂
      injection hv with _ _ hArgs
      injection hArgs with hPtr _
      injection hPtr with _ hAddr
      subst hAddr
      rw [cell₁] at cell₂
      injection cell₂ with hVal
      subst hVal
      exact congrArg IxVMUniv.succ (ih inner₂)
  | max cell₁ cell₂ _ _ ihl ihr =>
      revert h₂
      generalize hv : Value.construct "Ixon::Univ" "Max"
        [Value.ptr (Ty.enum "Ixon::Univ") _, Value.ptr (Ty.enum "Ixon::Univ") _] = v'
      intro h₂
      cases h₂ <;> (try (injection hv with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i cell₁' cell₂' left₂ right₂
      injection hv with _ _ hArgs
      injection hArgs with hPtr₁ hRest
      injection hRest with hPtr₂ _
      injection hPtr₁ with _ hAddr₁
      injection hPtr₂ with _ hAddr₂
      subst hAddr₁ hAddr₂
      rw [cell₁] at cell₁'
      rw [cell₂] at cell₂'
      injection cell₁' with hVal₁
      injection cell₂' with hVal₂
      subst hVal₁ hVal₂
      rw [ihl left₂, ihr right₂]
  | imax cell₁ cell₂ _ _ ihl ihr =>
      revert h₂
      generalize hv : Value.construct "Ixon::Univ" "IMax"
        [Value.ptr (Ty.enum "Ixon::Univ") _, Value.ptr (Ty.enum "Ixon::Univ") _] = v'
      intro h₂
      cases h₂ <;> (try (injection hv with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i cell₁' cell₂' left₂ right₂
      injection hv with _ _ hArgs
      injection hArgs with hPtr₁ hRest
      injection hRest with hPtr₂ _
      injection hPtr₁ with _ hAddr₁
      injection hPtr₂ with _ hAddr₂
      subst hAddr₁ hAddr₂
      rw [cell₁] at cell₁'
      rw [cell₂] at cell₂'
      injection cell₁' with hVal₁
      injection cell₂' with hVal₂
      subst hVal₁ hVal₂
      rw [ihl left₂, ihr right₂]
  | var repIdx₁ =>
      revert h₂; generalize hv : Value.construct "Ixon::Univ" "Var" [_] = v'; intro h₂
      cases h₂ <;> (try (injection hv with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repIdx₂
      injection hv with _ _ hArgs
      injection hArgs with hVal _
      subst hVal
      exact congrArg IxVMUniv.var (repU64_det large repIdx₁ repIdx₂)

/-! ## 3. `IxVMIExpr` (`&Ixon::Expr`) Representation, `HeapMono`, and Determinism -/

/-- Mathematical AST of `Ixon::Expr` wire expressions. -/
inductive IxVMIExpr (F : Type) where
  | srt (idx : UInt64) : IxVMIExpr F
  | var (idx : UInt64) : IxVMIExpr F
  | ref (idx : UInt64) (univs : _root_.List UInt64) : IxVMIExpr F
  | recur (idx : UInt64) (univs : _root_.List UInt64) : IxVMIExpr F
  | prj (typeRefIdx fieldIdx : UInt64) (val : IxVMIExpr F) : IxVMIExpr F
  | str (idx : UInt64) : IxVMIExpr F
  | nat (idx : UInt64) : IxVMIExpr F
  | app (func arg : IxVMIExpr F) : IxVMIExpr F
  | lam (contract : SourceValue F) (ty body : IxVMIExpr F) : IxVMIExpr F
  | all (binderContract valueContract : SourceValue F) (ty body : IxVMIExpr F) : IxVMIExpr F
  | letE (contract : SourceValue F) (ty val body : IxVMIExpr F) : IxVMIExpr F
  | share (idx : UInt64) : IxVMIExpr F

/-- Heap representation predicate for `&Ixon::Expr` pointers. -/
inductive RepIxVMIExpr [NatCast F] (u64ListEnum : String) (h : Heap F) :
    IxVMIExpr F → SourceValue F → Prop where
  | srt {addr : Nat} {idx : UInt64} {idxVal : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Srt" [idxVal]))
      (repIdx : RepU64 h idx idxVal) :
      RepIxVMIExpr u64ListEnum h (.srt idx) (.ptr (.enum "Ixon::Expr") addr)
  | var {addr : Nat} {idx : UInt64} {idxVal : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Var" [idxVal]))
      (repIdx : RepU64 h idx idxVal) :
      RepIxVMIExpr u64ListEnum h (.var idx) (.ptr (.enum "Ixon::Expr") addr)
  | ref {addr : Nat} {idx : UInt64} {univs : _root_.List UInt64}
      {idxVal univsPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Ref" [idxVal, univsPtr]))
      (repIdx : RepU64 h idx idxVal)
      (repUnivs : RepList u64ListEnum RepU64 h univs univsPtr) :
      RepIxVMIExpr u64ListEnum h (.ref idx univs) (.ptr (.enum "Ixon::Expr") addr)
  | recur {addr : Nat} {idx : UInt64} {univs : _root_.List UInt64}
      {idxVal univsPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Rec" [idxVal, univsPtr]))
      (repIdx : RepU64 h idx idxVal)
      (repUnivs : RepList u64ListEnum RepU64 h univs univsPtr) :
      RepIxVMIExpr u64ListEnum h (.recur idx univs) (.ptr (.enum "Ixon::Expr") addr)
  | prj {addr : Nat} {typeRefIdx fieldIdx : UInt64} {val : IxVMIExpr F}
      {tVal fVal valPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Prj" [tVal, fVal, valPtr]))
      (repT : RepU64 h typeRefIdx tVal)
      (repF : RepU64 h fieldIdx fVal)
      (repVal : RepIxVMIExpr u64ListEnum h val valPtr) :
      RepIxVMIExpr u64ListEnum h (.prj typeRefIdx fieldIdx val) (.ptr (.enum "Ixon::Expr") addr)
  | str {addr : Nat} {idx : UInt64} {idxVal : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Str" [idxVal]))
      (repIdx : RepU64 h idx idxVal) :
      RepIxVMIExpr u64ListEnum h (.str idx) (.ptr (.enum "Ixon::Expr") addr)
  | nat {addr : Nat} {idx : UInt64} {idxVal : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Nat" [idxVal]))
      (repIdx : RepU64 h idx idxVal) :
      RepIxVMIExpr u64ListEnum h (.nat idx) (.ptr (.enum "Ixon::Expr") addr)
  | app {addr : Nat} {func arg : IxVMIExpr F} {fnPtr argPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "App" [fnPtr, argPtr]))
      (repFn : RepIxVMIExpr u64ListEnum h func fnPtr)
      (repArg : RepIxVMIExpr u64ListEnum h arg argPtr) :
      RepIxVMIExpr u64ListEnum h (.app func arg) (.ptr (.enum "Ixon::Expr") addr)
  | lam {addr : Nat} {contract : SourceValue F} {ty body : IxVMIExpr F}
      {tyPtr bodyPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Lam" [contract, tyPtr, bodyPtr]))
      (repTy : RepIxVMIExpr u64ListEnum h ty tyPtr)
      (repBody : RepIxVMIExpr u64ListEnum h body bodyPtr) :
      RepIxVMIExpr u64ListEnum h (.lam contract ty body) (.ptr (.enum "Ixon::Expr") addr)
  | all {addr : Nat} {bc vc : SourceValue F} {ty body : IxVMIExpr F}
      {tyPtr bodyPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "All" [bc, vc, tyPtr, bodyPtr]))
      (repTy : RepIxVMIExpr u64ListEnum h ty tyPtr)
      (repBody : RepIxVMIExpr u64ListEnum h body bodyPtr) :
      RepIxVMIExpr u64ListEnum h (.all bc vc ty body) (.ptr (.enum "Ixon::Expr") addr)
  | letE {addr : Nat} {contract : SourceValue F} {ty val body : IxVMIExpr F}
      {tyPtr valPtr bodyPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Let" [contract, tyPtr, valPtr, bodyPtr]))
      (repTy : RepIxVMIExpr u64ListEnum h ty tyPtr)
      (repVal : RepIxVMIExpr u64ListEnum h val valPtr)
      (repBody : RepIxVMIExpr u64ListEnum h body bodyPtr) :
      RepIxVMIExpr u64ListEnum h (.letE contract ty val body) (.ptr (.enum "Ixon::Expr") addr)
  | share {addr : Nat} {idx : UInt64} {idxVal : SourceValue F}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Share" [idxVal]))
      (repIdx : RepU64 h idx idxVal) :
      RepIxVMIExpr u64ListEnum h (.share idx) (.ptr (.enum "Ixon::Expr") addr)

theorem RepIxVMIExpr.mono [NatCast F] {u64ListEnum : String} {h₁ h₂ : Heap F}
    {e : IxVMIExpr F} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepIxVMIExpr u64ListEnum h₁ e ptr) :
    RepIxVMIExpr u64ListEnum h₂ e ptr := by
  induction rep with
  | srt cell repIdx => exact .srt (ext.getElem?_eq cell) repIdx
  | var cell repIdx => exact .var (ext.getElem?_eq cell) repIdx
  | ref cell repIdx repUnivs =>
      exact .ref (ext.getElem?_eq cell) repIdx (repList_heapMono₂ u64ListEnum repU64_heapMono₂ ext repUnivs)
  | recur cell repIdx repUnivs =>
      exact .recur (ext.getElem?_eq cell) repIdx (repList_heapMono₂ u64ListEnum repU64_heapMono₂ ext repUnivs)
  | prj cell repT repF _ ih =>
      exact .prj (ext.getElem?_eq cell) repT repF ih
  | str cell repIdx => exact .str (ext.getElem?_eq cell) repIdx
  | nat cell repIdx => exact .nat (ext.getElem?_eq cell) repIdx
  | app cell _ _ ihFn ihArg =>
      exact .app (ext.getElem?_eq cell) ihFn ihArg
  | lam cell _ _ ihTy ihBody =>
      exact .lam (ext.getElem?_eq cell) ihTy ihBody
  | all cell _ _ ihTy ihBody =>
      exact .all (ext.getElem?_eq cell) ihTy ihBody
  | letE cell _ _ _ ihTy ihVal ihBody =>
      exact .letE (ext.getElem?_eq cell) ihTy ihVal ihBody
  | share cell repIdx => exact .share (ext.getElem?_eq cell) repIdx

theorem HeapMono.repIxVMIExpr [NatCast F] (u64ListEnum : String) (e : IxVMIExpr F) :
    HeapMono (fun h ptr => RepIxVMIExpr u64ListEnum h e ptr) :=
  fun _ _ _ ext rep => rep.mono ext

theorem RepIxVMIExpr.det [Field F] (large : U32.Compatible F) {u64ListEnum : String}
    {h : Heap F} {e₁ e₂ : IxVMIExpr F} {ptr : SourceValue F}
    (h₁ : RepIxVMIExpr u64ListEnum h e₁ ptr)
    (h₂ : RepIxVMIExpr u64ListEnum h e₂ ptr) :
    e₁ = e₂ := by
  induction h₁ generalizing e₂ with
  | srt cell₁ repIdx₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repIdx₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hV _
      subst hV
      exact congrArg IxVMIExpr.srt (repU64_det large repIdx₁ repIdx₂)
  | var cell₁ repIdx₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repIdx₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hV _
      subst hV
      exact congrArg IxVMIExpr.var (repU64_det large repIdx₁ repIdx₂)
  | ref cell₁ repIdx₁ repUnivs₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repIdx₂ repUnivs₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest; injection hRest with hV₂ _
      subst hV₁ hV₂
      rw [repU64_det large repIdx₁ repIdx₂,
        repList_det (repU64_det large) repUnivs₁ repUnivs₂]
  | recur cell₁ repIdx₁ repUnivs₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repIdx₂ repUnivs₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest; injection hRest with hV₂ _
      subst hV₁ hV₂
      rw [repU64_det large repIdx₁ repIdx₂,
        repList_det (repU64_det large) repUnivs₁ repUnivs₂]
  | prj cell₁ repT₁ repF₁ _ ih =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repT₂ repF₂ repVal₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest₁; injection hRest₁ with hV₂ hRest₂; injection hRest₂ with hV₃ _
      subst hV₁ hV₂ hV₃
      rw [repU64_det large repT₁ repT₂, repU64_det large repF₁ repF₂, ih repVal₂]
  | str cell₁ repIdx₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repIdx₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hV _
      subst hV
      exact congrArg IxVMIExpr.str (repU64_det large repIdx₁ repIdx₂)
  | nat cell₁ repIdx₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repIdx₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hV _
      subst hV
      exact congrArg IxVMIExpr.nat (repU64_det large repIdx₁ repIdx₂)
  | app cell₁ _ _ ihFn ihArg =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repFn₂ repArg₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest; injection hRest with hV₂ _
      subst hV₁ hV₂
      rw [ihFn repFn₂, ihArg repArg₂]
  | lam cell₁ _ _ ihTy ihBody =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repTy₂ repBody₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest₁; injection hRest₁ with hV₂ hRest₂; injection hRest₂ with hV₃ _
      subst hV₁ hV₂ hV₃
      rw [ihTy repTy₂, ihBody repBody₂]
  | all cell₁ _ _ ihTy ihBody =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repTy₂ repBody₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest₁; injection hRest₁ with hV₂ hRest₂
      injection hRest₂ with hV₃ hRest₃; injection hRest₃ with hV₄ _
      subst hV₁ hV₂ hV₃ hV₄
      rw [ihTy repTy₂, ihBody repBody₂]
  | letE cell₁ _ _ _ ihTy ihVal ihBody =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repTy₂ repVal₂ repBody₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest₁; injection hRest₁ with hV₂ hRest₂
      injection hRest₂ with hV₃ hRest₃; injection hRest₃ with hV₄ _
      subst hV₁ hV₂ hV₃ hV₄
      rw [ihTy repTy₂, ihVal repVal₂, ihBody repBody₂]
  | share cell₁ repIdx₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repIdx₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hV _
      subst hV
      exact congrArg IxVMIExpr.share (repU64_det large repIdx₁ repIdx₂)

/-! ## 4. `IxVMKUniv` (`KernelTypes::KLevel`) Representation, `HeapMono`, and Determinism -/

/-- Mathematical AST of `KernelTypes::KLevel` kernel universe levels. -/
inductive IxVMKUniv (F : Type) where
  | zero : IxVMKUniv F
  | succ (u : IxVMKUniv F) : IxVMKUniv F
  | max (u v : IxVMKUniv F) : IxVMKUniv F
  | imax (u v : IxVMKUniv F) : IxVMKUniv F
  | param (idx : F) : IxVMKUniv F
  deriving Repr, DecidableEq

/-- Heap representation predicate for `KernelTypes::KLevel = &KernelTypes::KLevelNode`. -/
inductive RepIxVMKUniv (h : Heap F) : IxVMKUniv F → SourceValue F → Prop where
  | zero {addr : Nat}
      (cell : h[addr]? = some (.construct "KernelTypes::KLevelNode" "Zero" [])) :
      RepIxVMKUniv h .zero (.ptr (.enum "KernelTypes::KLevelNode") addr)
  | succ {addr : Nat} {u : IxVMKUniv F} {uPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KLevelNode" "Succ" [uPtr]))
      (inner : RepIxVMKUniv h u uPtr) :
      RepIxVMKUniv h (.succ u) (.ptr (.enum "KernelTypes::KLevelNode") addr)
  | max {addr : Nat} {u v : IxVMKUniv F} {uPtr vPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KLevelNode" "Max" [uPtr, vPtr]))
      (left : RepIxVMKUniv h u uPtr)
      (right : RepIxVMKUniv h v vPtr) :
      RepIxVMKUniv h (.max u v) (.ptr (.enum "KernelTypes::KLevelNode") addr)
  | imax {addr : Nat} {u v : IxVMKUniv F} {uPtr vPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KLevelNode" "IMax" [uPtr, vPtr]))
      (left : RepIxVMKUniv h u uPtr)
      (right : RepIxVMKUniv h v vPtr) :
      RepIxVMKUniv h (.imax u v) (.ptr (.enum "KernelTypes::KLevelNode") addr)
  | param {addr : Nat} {idx : F}
      (cell : h[addr]? = some (.construct "KernelTypes::KLevelNode" "Param" [.field idx])) :
      RepIxVMKUniv h (.param idx) (.ptr (.enum "KernelTypes::KLevelNode") addr)

theorem RepIxVMKUniv.mono {h₁ h₂ : Heap F} {u : IxVMKUniv F} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepIxVMKUniv h₁ u ptr) :
    RepIxVMKUniv h₂ u ptr := by
  induction rep with
  | zero cell => exact .zero (ext.getElem?_eq cell)
  | succ cell _ ih => exact .succ (ext.getElem?_eq cell) ih
  | max cell _ _ ihl ihr => exact .max (ext.getElem?_eq cell) ihl ihr
  | imax cell _ _ ihl ihr => exact .imax (ext.getElem?_eq cell) ihl ihr
  | param cell => exact .param (ext.getElem?_eq cell)

theorem repIxVMKUniv_heapMono₂ : HeapMono₂ (RepIxVMKUniv (F := F)) :=
  fun _ _ _ _ ext rep => rep.mono ext

theorem HeapMono.repIxVMKUniv (u : IxVMKUniv F) :
    HeapMono (fun h ptr => RepIxVMKUniv h u ptr) :=
  fun _ _ _ ext rep => rep.mono ext

theorem RepIxVMKUniv.det {h : Heap F} {u₁ u₂ : IxVMKUniv F} {ptr : SourceValue F}
    (h₁ : RepIxVMKUniv h u₁ ptr) (h₂ : RepIxVMKUniv h u₂ ptr) : u₁ = u₂ := by
  induction h₁ generalizing u₂ with
  | zero cell₁ =>
      cases h₂ <;> rw [cell₁] at * <;> (clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
  | succ cell₁ _ ih =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i inner₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hV _
      subst hV
      exact congrArg IxVMKUniv.succ (ih inner₂)
  | max cell₁ _ _ ihl ihr =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i left₂ right₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest; injection hRest with hV₂ _
      subst hV₁ hV₂
      rw [ihl left₂, ihr right₂]
  | imax cell₁ _ _ ihl ihr =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i left₂ right₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest; injection hRest with hV₂ _
      subst hV₁ hV₂
      rw [ihl left₂, ihr right₂]
  | param cell₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hV _
      injection hV with hField
      subst hField
      rfl

/-! ## 5. `IxVMKExpr` (`KernelTypes::KExpr`) Representation, `HeapMono`, and Determinism -/

/-- Mathematical AST of `KernelTypes::KExpr` kernel expressions. A `λ` or `∀` carries its
binder datum as a level (D2, `KExprNode::Lam(ty, body, ℓ)`): the binder's codomain sort is zero
exactly when `ℓ` is, so the kernel's datum is the zero-ness of `ℓ`. -/
inductive IxVMKExpr (F : Type) where
  | bvar (idx : F) : IxVMKExpr F
  | sort (lvl : IxVMKUniv F) : IxVMKExpr F
  | const (name : Address) (lvls : _root_.List (IxVMKUniv F)) : IxVMKExpr F
  | app (func arg : IxVMKExpr F) : IxVMKExpr F
  | lam (ty body : IxVMKExpr F) (lvl : IxVMKUniv F) : IxVMKExpr F
  | forallE (ty body : IxVMKExpr F) (lvl : IxVMKUniv F) : IxVMKExpr F
  | letE (ty val body : IxVMKExpr F) : IxVMKExpr F
  | litNat (limbs : _root_.List UInt64) : IxVMKExpr F
  | litStr (bytes : _root_.List UInt8) : IxVMKExpr F
  | proj (typeName : Address) (idx : F) (structExpr : IxVMKExpr F) : IxVMKExpr F

/-- Heap representation predicate for `KernelTypes::KExpr = &KernelTypes::KExprNode`. -/
inductive RepIxVMKExpr [NatCast F] (addrTy : Ty) (lvlListEnum limbListEnum byteListEnum : String)
    (h : Heap F) : IxVMKExpr F → SourceValue F → Prop where
  | bvar {addr : Nat} {idx : F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "BVar" [.field idx])) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.bvar idx)
        (.ptr (.enum "KernelTypes::KExprNode") addr)
  | sort {addr : Nat} {lvl : IxVMKUniv F} {lvlPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "Srt" [lvlPtr]))
      (repLvl : RepIxVMKUniv h lvl lvlPtr) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.sort lvl)
        (.ptr (.enum "KernelTypes::KExprNode") addr)
  | const {addr : Nat} {name : Address} {lvls : _root_.List (IxVMKUniv F)}
      {namePtr lvlsPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "Const" [namePtr, lvlsPtr]))
      (repName : RepAddressRef addrTy h name namePtr)
      (repLvls : RepList lvlListEnum RepIxVMKUniv h lvls lvlsPtr) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.const name lvls)
        (.ptr (.enum "KernelTypes::KExprNode") addr)
  | app {addr : Nat} {func arg : IxVMKExpr F} {fnPtr argPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "App" [fnPtr, argPtr]))
      (repFn : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h func fnPtr)
      (repArg : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h arg argPtr) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.app func arg)
        (.ptr (.enum "KernelTypes::KExprNode") addr)
  | lam {addr : Nat} {ty body : IxVMKExpr F} {lvl : IxVMKUniv F} {tyPtr bodyPtr lvlPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "Lam" [tyPtr, bodyPtr, lvlPtr]))
      (repTy : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h ty tyPtr)
      (repBody : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h body bodyPtr)
      (repLvl : RepIxVMKUniv h lvl lvlPtr) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.lam ty body lvl)
        (.ptr (.enum "KernelTypes::KExprNode") addr)
  | forallE {addr : Nat} {ty body : IxVMKExpr F} {lvl : IxVMKUniv F}
      {tyPtr bodyPtr lvlPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "Forall" [tyPtr, bodyPtr, lvlPtr]))
      (repTy : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h ty tyPtr)
      (repBody : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h body bodyPtr)
      (repLvl : RepIxVMKUniv h lvl lvlPtr) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.forallE ty body lvl)
        (.ptr (.enum "KernelTypes::KExprNode") addr)
  | letE {addr : Nat} {ty val body : IxVMKExpr F} {tyPtr valPtr bodyPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "Let" [tyPtr, valPtr, bodyPtr]))
      (repTy : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h ty tyPtr)
      (repVal : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h val valPtr)
      (repBody : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h body bodyPtr) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.letE ty val body)
        (.ptr (.enum "KernelTypes::KExprNode") addr)
  | litNat {addr : Nat} {limbs : _root_.List UInt64} {limbsPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "Lit"
        [.construct "KernelTypes::KLiteral" "Nat" [limbsPtr]]))
      (repLimbs : RepList limbListEnum RepU64 h limbs limbsPtr) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.litNat limbs)
        (.ptr (.enum "KernelTypes::KExprNode") addr)
  | litStr {addr : Nat} {bytes : _root_.List UInt8} {bytesPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "Lit"
        [.construct "KernelTypes::KLiteral" "Str" [bytesPtr]]))
      (repBytes : RepByteStream byteListEnum h bytes bytesPtr) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.litStr bytes)
        (.ptr (.enum "KernelTypes::KExprNode") addr)
  | proj {addr : Nat} {typeName : Address} {idx : F} {structExpr : IxVMKExpr F}
      {namePtr structPtr : SourceValue F}
      (cell : h[addr]? = some (.construct "KernelTypes::KExprNode" "Proj"
        [namePtr, .field idx, structPtr]))
      (repName : RepAddressRef addrTy h typeName namePtr)
      (repStruct : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h structExpr structPtr) :
      RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h (.proj typeName idx structExpr)
        (.ptr (.enum "KernelTypes::KExprNode") addr)

theorem RepIxVMKExpr.mono [NatCast F] {addrTy : Ty} {lvlListEnum limbListEnum byteListEnum : String}
    {h₁ h₂ : Heap F} {e : IxVMKExpr F} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (rep : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h₁ e ptr) :
    RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h₂ e ptr := by
  induction rep with
  | bvar cell => exact .bvar (ext.getElem?_eq cell)
  | sort cell repLvl => exact .sort (ext.getElem?_eq cell) (repLvl.mono ext)
  | const cell repName repLvls =>
      exact .const (ext.getElem?_eq cell)
        (repAddressRef_heapMono₂ addrTy ext repName)
        (repList_heapMono₂ lvlListEnum repIxVMKUniv_heapMono₂ ext repLvls)
  | app cell _ _ ihFn ihArg =>
      exact .app (ext.getElem?_eq cell) ihFn ihArg
  | lam cell _ _ repLvl ihTy ihBody =>
      exact .lam (ext.getElem?_eq cell) ihTy ihBody (repLvl.mono ext)
  | forallE cell _ _ repLvl ihTy ihBody =>
      exact .forallE (ext.getElem?_eq cell) ihTy ihBody (repLvl.mono ext)
  | letE cell _ _ _ ihTy ihVal ihBody =>
      exact .letE (ext.getElem?_eq cell) ihTy ihVal ihBody
  | litNat cell repLimbs =>
      exact .litNat (ext.getElem?_eq cell)
        (repList_heapMono₂ limbListEnum repU64_heapMono₂ ext repLimbs)
  | litStr cell repBytes =>
      exact .litStr (ext.getElem?_eq cell)
        (repByteStream_heapMono₂ byteListEnum ext repBytes)
  | proj cell repName _ ihStruct =>
      exact .proj (ext.getElem?_eq cell)
        (repAddressRef_heapMono₂ addrTy ext repName) ihStruct

theorem HeapMono.repIxVMKExpr [NatCast F] (addrTy : Ty) (lvlListEnum limbListEnum byteListEnum : String)
    (e : IxVMKExpr F) :
    HeapMono (fun h ptr => RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h e ptr) :=
  fun _ _ _ ext rep => rep.mono ext

theorem RepIxVMKExpr.det [Field F] (large : U32.Compatible F)
    {addrTy : Ty} {lvlListEnum limbListEnum byteListEnum : String}
    {h : Heap F} {e₁ e₂ : IxVMKExpr F} {ptr : SourceValue F}
    (h₁ : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h e₁ ptr)
    (h₂ : RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h e₂ ptr) :
    e₁ = e₂ := by
  induction h₁ generalizing e₂ with
  | bvar cell₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hV _
      injection hV with hField
      subst hField
      rfl
  | sort cell₁ repLvl₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repLvl₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hV _
      subst hV
      exact congrArg IxVMKExpr.sort (repLvl₁.det repLvl₂)
  | const cell₁ repName₁ repLvls₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repName₂ repLvls₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest; injection hRest with hV₂ _
      subst hV₁ hV₂
      rw [repAddressRef_det large repName₁ repName₂,
        repList_det RepIxVMKUniv.det repLvls₁ repLvls₂]
  | app cell₁ _ _ ihFn ihArg =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repFn₂ repArg₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest; injection hRest with hV₂ _
      subst hV₁ hV₂
      rw [ihFn repFn₂, ihArg repArg₂]
  | lam cell₁ _ _ repLvl₁ ihTy ihBody =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repTy₂ repBody₂ repLvl₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest₁; injection hRest₁ with hV₂ hRest₂; injection hRest₂ with hV₃ _
      subst hV₁ hV₂ hV₃
      rw [ihTy repTy₂, ihBody repBody₂, repLvl₁.det repLvl₂]
  | forallE cell₁ _ _ repLvl₁ ihTy ihBody =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repTy₂ repBody₂ repLvl₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest₁; injection hRest₁ with hV₂ hRest₂; injection hRest₂ with hV₃ _
      subst hV₁ hV₂ hV₃
      rw [ihTy repTy₂, ihBody repBody₂, repLvl₁.det repLvl₂]
  | letE cell₁ _ _ _ ihTy ihVal ihBody =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repTy₂ repVal₂ repBody₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest₁; injection hRest₁ with hV₂ hRest₂; injection hRest₂ with hV₃ _
      subst hV₁ hV₂ hV₃
      rw [ihTy repTy₂, ihVal repVal₂, ihBody repBody₂]
  | litNat cell₁ repLimbs₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      · rename_i repLimbs₂ cell₂
        injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hLit _
        injection hLit with _ _ hLitArgs; injection hLitArgs with hPtr _
        subst hPtr
        exact congrArg IxVMKExpr.litNat (repList_det (repU64_det large) repLimbs₁ repLimbs₂)
      · rename_i _ cell₂
        injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hLit _
        injection hLit with _ hLitCtor _
        exact absurd hLitCtor (by decide)
  | litStr cell₁ repBytes₁ =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      · rename_i _ cell₂
        injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hLit _
        injection hLit with _ hLitCtor _
        exact absurd hLitCtor (by decide)
      · rename_i repBytes₂ cell₂
        injection cell₂ with hC; injection hC with _ _ hArgs; injection hArgs with hLit _
        injection hLit with _ _ hLitArgs; injection hLitArgs with hPtr _
        subst hPtr
        exact congrArg IxVMKExpr.litStr (repList_det (repU8_inj large) repBytes₁ repBytes₂)
  | proj cell₁ repName₁ _ ihStruct =>
      cases h₂ <;> (rw [cell₁] at *; clear cell₁; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
      rename_i repName₂ repStruct₂ cell₂
      injection cell₂ with hC; injection hC with _ _ hArgs
      injection hArgs with hV₁ hRest₁; injection hRest₁ with hV₂ hRest₂; injection hRest₂ with hV₃ _
      injection hV₂ with hField
      subst hV₁ hField hV₃
      rw [repAddressRef_det large repName₁ repName₂, ihStruct repStruct₂]

/-! ## 6. `IxVMRoleCtx` (`KernelRoles::RoleCtx`) Representation, `HeapMono`, and Determinism -/

/-- Mathematical AST of `KernelRoles::RoleEvidence`. -/
inductive IxVMRoleEvidence where
  | defeq : IxVMRoleEvidence
  | proof (addr : Address) : IxVMRoleEvidence

/-- Heap representation predicate for `KernelRoles::RoleEvidence`. -/
inductive RepRoleEvidence [NatCast F] (addrTy : Ty) (h : Heap F) :
    IxVMRoleEvidence → SourceValue F → Prop where
  | defeq :
      RepRoleEvidence addrTy h .defeq (.construct "KernelRoles::RoleEvidence" "Defeq" [])
  | proof {addr : Address} {addrPtr : SourceValue F}
      (repAddr : RepAddressRef addrTy h addr addrPtr) :
      RepRoleEvidence addrTy h (.proof addr)
        (.construct "KernelRoles::RoleEvidence" "Proof" [addrPtr])

theorem RepRoleEvidence.mono [NatCast F] {addrTy : Ty} {h₁ h₂ : Heap F}
    {ev : IxVMRoleEvidence} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepRoleEvidence addrTy h₁ ev v) :
    RepRoleEvidence addrTy h₂ ev v := by
  cases rep with
  | defeq => exact .defeq
  | proof repAddr => exact .proof (repAddressRef_heapMono₂ addrTy ext repAddr)

theorem repRoleEvidence_heapMono₂ [NatCast F] (addrTy : Ty) :
    HeapMono₂ (RepRoleEvidence (F := F) addrTy) :=
  fun _ _ _ _ ext rep => rep.mono ext

theorem RepRoleEvidence.det [Field F] (large : U32.Compatible F) {addrTy : Ty} {h : Heap F}
    {ev₁ ev₂ : IxVMRoleEvidence} {v : SourceValue F}
    (h₁ : RepRoleEvidence addrTy h ev₁ v) (h₂ : RepRoleEvidence addrTy h ev₂ v) :
    ev₁ = ev₂ := by
  revert h₂
  generalize hv : v = v'
  intro h₂
  cases h₁ with
  | defeq =>
      cases h₂ with
      | defeq => rfl
      | proof _ =>
          injection hv with _ hCtor _
          exact absurd hCtor (by decide)
  | proof repAddr₁ =>
      cases h₂ with
      | defeq =>
          injection hv with _ hCtor _
          exact absurd hCtor (by decide)
      | proof repAddr₂ =>
          injection hv with _ _ hArgs
          injection hArgs with hPtr _
          subst hPtr
          exact congrArg IxVMRoleEvidence.proof (repAddressRef_det large repAddr₁ repAddr₂)

/-- Mathematical model of `KernelRoles::RoleTableNode`. -/
structure IxVMRoleTable (F : Type) where
  binding : Address
  byRole : RBTree F Address
  byAddr : RBTree Address F

@[ext]
theorem IxVMRoleTable.ext {t₁ t₂ : IxVMRoleTable F}
    (hb : t₁.binding = t₂.binding)
    (hr : t₁.byRole = t₂.byRole)
    (ha : t₁.byAddr = t₂.byAddr) : t₁ = t₂ := by
  cases t₁; cases t₂
  dsimp only at hb hr ha
  rw [hb, hr, ha]

/-- Mathematical model of `KernelRoles::RoleCtxNode`. -/
inductive IxVMRoleCtx (F : Type) where
  | mk (table : IxVMRoleTable F) (limit : F) : IxVMRoleCtx F
  | assumed (table : IxVMRoleTable F) : IxVMRoleCtx F

/-- Label representation for `RoleMap<Bytes::AddressRef>` (`(color, roleKey, addr)`). -/
def RepRoleAddrLabel [NatCast F] (addrTy : Ty) (h : Heap F)
    (lbl : Nat × F × Address) (v : SourceValue F) : Prop :=
  ∃ addrPtr, v = .tuple [.field (lbl.1 : F), .field lbl.2.1, addrPtr] ∧
    RepAddressRef addrTy h lbl.2.2 addrPtr

theorem repRoleAddrLabel_heapMono₂ [NatCast F] (addrTy : Ty) :
    HeapMono₂ (RepRoleAddrLabel (F := F) addrTy) := by
  intro h₁ h₂ lbl v ext ⟨addrPtr, hv, hAddr⟩
  exact ⟨addrPtr, hv, repAddressRef_heapMono₂ addrTy ext hAddr⟩

theorem repRoleAddrLabel_det [Field F] (large : U32.Compatible F) {addrTy : Ty} {h : Heap F}
    {l₁ l₂ : Nat × F × Address} {v : SourceValue F}
    (hColor₁ : l₁.1 < 256) (hColor₂ : l₂.1 < 256)
    (h₁ : RepRoleAddrLabel addrTy h l₁ v) (h₂ : RepRoleAddrLabel addrTy h l₂ v) :
    l₁ = l₂ := by
  obtain ⟨ptr₁, rfl, hAddr₁⟩ := h₁
  obtain ⟨ptr₂, hEq, hAddr₂⟩ := h₂
  injection hEq with hList
  injection hList with hC hRest₁
  injection hRest₁ with hK hRest₂
  injection hRest₂ with hP _
  injection hC with hCField
  injection hK with hKField
  subst hP
  rcases l₁ with ⟨c₁, k₁, a₁⟩
  rcases l₂ with ⟨c₂, k₂, a₂⟩
  have hc := nat_lt_256_inj large hColor₁ hColor₂ hCField
  have ha := repAddressRef_det large hAddr₁ hAddr₂
  subst hc hKField ha
  rfl

/-- Heap representation predicate for `KernelRoles::RoleCtx`. -/
inductive RepRoleCtx [NatCast F] (addrTy : Ty) (byRoleEnum byAddrEnum : String)
    (RByRole : Heap F → (Nat × F × Address) → SourceValue F → Prop)
    (RByAddr : Heap F → (Nat × Address × F) → SourceValue F → Prop)
    (h : Heap F) : IxVMRoleCtx F → SourceValue F → Prop where
  | mk {ctxAddr tblAddr : Nat} {tbl : IxVMRoleTable F} {limit : F}
      {bindingPtr byRolePtr byAddrPtr evPtr : SourceValue F}
      (ctxCell : h[ctxAddr]? = some (.construct "KernelRoles::RoleCtxNode" "Mk"
        [.ptr (.enum "KernelRoles::RoleTableNode") tblAddr, .field limit]))
      (tblCell : h[tblAddr]? = some (.construct "KernelRoles::RoleTableNode" "Mk"
        [bindingPtr, byRolePtr, byAddrPtr, evPtr]))
      (repBinding : RepAddressRef addrTy h tbl.binding bindingPtr)
      (repByRole : RepRBTreePtr byRoleEnum "Nil" "Node" RByRole h tbl.byRole byRolePtr)
      (repByAddr : RepRBTreePtr byAddrEnum "Nil" "Node" RByAddr h tbl.byAddr byAddrPtr) :
      RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h (.mk tbl limit)
        (.ptr (.enum "KernelRoles::RoleCtxNode") ctxAddr)
  | assumed {ctxAddr tblAddr : Nat} {tbl : IxVMRoleTable F}
      {bindingPtr byRolePtr byAddrPtr evPtr : SourceValue F}
      (ctxCell : h[ctxAddr]? = some (.construct "KernelRoles::RoleCtxNode" "Assumed"
        [.ptr (.enum "KernelRoles::RoleTableNode") tblAddr]))
      (tblCell : h[tblAddr]? = some (.construct "KernelRoles::RoleTableNode" "Mk"
        [bindingPtr, byRolePtr, byAddrPtr, evPtr]))
      (repBinding : RepAddressRef addrTy h tbl.binding bindingPtr)
      (repByRole : RepRBTreePtr byRoleEnum "Nil" "Node" RByRole h tbl.byRole byRolePtr)
      (repByAddr : RepRBTreePtr byAddrEnum "Nil" "Node" RByAddr h tbl.byAddr byAddrPtr) :
      RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h (.assumed tbl)
        (.ptr (.enum "KernelRoles::RoleCtxNode") ctxAddr)

theorem RepRoleCtx.mono [NatCast F] {addrTy : Ty} {byRoleEnum byAddrEnum : String}
    {RByRole : Heap F → (Nat × F × Address) → SourceValue F → Prop}
    {RByAddr : Heap F → (Nat × Address × F) → SourceValue F → Prop}
    (hMonoRole : HeapMono₂ RByRole) (hMonoAddr : HeapMono₂ RByAddr)
    {h₁ h₂ : Heap F} {rc : IxVMRoleCtx F} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (rep : RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h₁ rc ptr) :
    RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h₂ rc ptr := by
  cases rep with
  | mk ctxCell tblCell repBinding repByRole repByAddr =>
      exact .mk (ext.getElem?_eq ctxCell) (ext.getElem?_eq tblCell)
        (repAddressRef_heapMono₂ addrTy ext repBinding)
        (RepRBTreePtr.mono hMonoRole ext repByRole)
        (RepRBTreePtr.mono hMonoAddr ext repByAddr)
  | assumed ctxCell tblCell repBinding repByRole repByAddr =>
      exact .assumed (ext.getElem?_eq ctxCell) (ext.getElem?_eq tblCell)
        (repAddressRef_heapMono₂ addrTy ext repBinding)
        (RepRBTreePtr.mono hMonoRole ext repByRole)
        (RepRBTreePtr.mono hMonoAddr ext repByAddr)

theorem HeapMono.repRoleCtx [NatCast F] (addrTy : Ty) (byRoleEnum byAddrEnum : String)
    {RByRole : Heap F → (Nat × F × Address) → SourceValue F → Prop}
    {RByAddr : Heap F → (Nat × Address × F) → SourceValue F → Prop}
    (hMonoRole : HeapMono₂ RByRole) (hMonoAddr : HeapMono₂ RByAddr)
    (rc : IxVMRoleCtx F) :
    HeapMono (fun h ptr => RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h rc ptr) :=
  fun _ _ _ ext rep => rep.mono hMonoRole hMonoAddr ext

theorem RepRoleCtx.det [Field F] (large : U32.Compatible F)
    {addrTy : Ty} {byRoleEnum byAddrEnum : String}
    {RByRole : Heap F → (Nat × F × Address) → SourceValue F → Prop}
    {RByAddr : Heap F → (Nat × Address × F) → SourceValue F → Prop}
    {h : Heap F}
    (hDetRole : ∀ {x₁ x₂ v}, RByRole h x₁ v → RByRole h x₂ v → x₁ = x₂)
    (hDetAddr : ∀ {x₁ x₂ v}, RByAddr h x₁ v → RByAddr h x₂ v → x₁ = x₂)
    {rc₁ rc₂ : IxVMRoleCtx F} {ptr : SourceValue F}
    (h₁ : RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h rc₁ ptr)
    (h₂ : RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h rc₂ ptr) :
    rc₁ = rc₂ := by
  cases h₁ with
  | mk ctxCell₁ tblCell₁ repBinding₁ repByRole₁ repByAddr₁ =>
      cases h₂ with
      | mk ctxCell₂ tblCell₂ repBinding₂ repByRole₂ repByAddr₂ =>
          rw [ctxCell₁] at ctxCell₂
          injection ctxCell₂ with hCtx
          injection hCtx with _ _ hCtxArgs
          injection hCtxArgs with hTblPtr hCtxRest
          injection hCtxRest with hLim _
          injection hTblPtr with _ hTblAddr
          injection hLim with hLimEq
          subst hTblAddr hLimEq
          rw [tblCell₁] at tblCell₂
          injection tblCell₂ with hTbl
          injection hTbl with _ _ hTblArgs
          injection hTblArgs with hB₁ hT₁
          injection hT₁ with hB₂ hT₂
          injection hT₂ with hB₃ _
          subst hB₁ hB₂ hB₃
          have hb := repAddressRef_det large repBinding₁ repBinding₂
          have hr := repRBTreePtr_det (by decide) hDetRole repByRole₁ repByRole₂
          have ha := repRBTreePtr_det (by decide) hDetAddr repByAddr₁ repByAddr₂
          rw [IxVMRoleTable.ext hb hr ha]
      | assumed ctxCell₂ _ _ _ _ =>
          rw [ctxCell₁] at ctxCell₂
          injection ctxCell₂ with hCtx
          injection hCtx with _ hCtor _
          exact absurd hCtor (by decide)
  | assumed ctxCell₁ tblCell₁ repBinding₁ repByRole₁ repByAddr₁ =>
      cases h₂ with
      | mk ctxCell₂ _ _ _ _ =>
          rw [ctxCell₁] at ctxCell₂
          injection ctxCell₂ with hCtx
          injection hCtx with _ hCtor _
          exact absurd hCtor (by decide)
      | assumed ctxCell₂ tblCell₂ repBinding₂ repByRole₂ repByAddr₂ =>
          rw [ctxCell₁] at ctxCell₂
          injection ctxCell₂ with hCtx
          injection hCtx with _ _ hCtxArgs
          injection hCtxArgs with hTblPtr _
          injection hTblPtr with _ hTblAddr
          subst hTblAddr
          rw [tblCell₁] at tblCell₂
          injection tblCell₂ with hTbl
          injection hTbl with _ _ hTblArgs
          injection hTblArgs with hB₁ hT₁
          injection hT₁ with hB₂ hT₂
          injection hT₂ with hB₃ _
          subst hB₁ hB₂ hB₃
          have hb := repAddressRef_det large repBinding₁ repBinding₂
          have hr := repRBTreePtr_det (by decide) hDetRole repByRole₁ repByRole₂
          have ha := repRBTreePtr_det (by decide) hDetAddr repByAddr₁ repByAddr₂
          rw [IxVMRoleTable.ext hb hr ha]

/-! ## 7. Ingress Stream Authentication & `TagN` Field-Decoding Correctness -/

/-- Ingress stream authentication in the Lean model: if the `len` bytes read at `idx` are fewer
than `2^32` (the range check `IxByteStream::read_finite_byte_stream` makes,
`UInt32::less_than_fields(0, len)`; `read_byte_stream` builds exactly `len` bytes by its own
recursion) and pass the model of `Blake3::verify_bytes_against` (field-wise equality of
`addressToFields` of the Lean `Blake3.digest`; `Blake3.verify_bytes_against_model_iff` relates it
to the model of `Blake3::hash`), then allocating them yields a heap-extended `RepByteStream` of
length `len < 2^32` whose BLAKE3 digest equals `expectedAddr`. It models the checks that the IxVM
functions `Ingress::load_verified_constant`, `Ingress::load_verified_blob` and
`KernelRoles::load_role_table` make, but is not a theorem about them. -/
theorem ingress_verify_stream_sound [Field F] (large : U32.Compatible F)
    (enumName : String) (stream : Nat → UInt8) (idx len : Nat) (h : Heap F)
    (expectedAddr : Address)
    (hLen : len < 2 ^ 32)
    (hVerify : Blake3.addressToFields F (Blake3.digest (readByteStream stream idx len)) =
      Blake3.addressToFields F expectedAddr) :
    let bytes := readByteStream stream idx len
    let allocated := allocByteStream enumName h bytes
    h.Extends allocated.2 ∧
      RepByteStream enumName allocated.2 bytes allocated.1 ∧
      bytes.length = len ∧
      len < U32.base ∧
      Blake3.digest bytes = expectedAddr := by
  obtain ⟨hExt, hRep, hLength⟩ := read_byte_stream_spec enumName stream idx len h
  exact ⟨hExt, hRep, hLength, by unfold U32.base; omega,
    (Blake3.verify_bytes_against_iff large (readByteStream stream idx len) expectedAddr).mp hVerify⟩

/-- Canonical `SourceValue F` representation of a decoded `Tag4` pair `(flag, value)`
(`(Field, UInt64::U64)` returned by `IxonDeserialize::get_tagn4`). -/
def RepTag4 [NatCast F] (h : Heap F) (tag : UInt8 × UInt64) (v : SourceValue F) : Prop :=
  ∃ valTuple, v = .tuple [.field (tag.1.toNat : F), valTuple] ∧
    RepU64 h tag.2 valTuple

theorem repTag4_heapMono₂ [NatCast F] : HeapMono₂ (RepTag4 (F := F)) := by
  intro h₁ h₂ tag v ext ⟨valTuple, hv, hVal⟩
  exact ⟨valTuple, hv, repU64_heapMono₂ ext hVal⟩

theorem repTag4_inj [Field F] (large : U32.Compatible F) {h : Heap F}
    {t₁ t₂ : UInt8 × UInt64} {v : SourceValue F}
    (h₁ : RepTag4 h t₁ v) (h₂ : RepTag4 h t₂ v) :
    t₁ = t₂ := by
  obtain ⟨val₁, rfl, hVal₁⟩ := h₁
  obtain ⟨val₂, hEq, hVal₂⟩ := h₂
  injection hEq with hList
  injection hList with hFlag hRest
  injection hRest with hVal _
  subst hVal
  rcases t₁ with ⟨f₁, w₁⟩
  rcases t₂ with ⟨f₂, w₂⟩
  have hf := repU8_inj large (h := ([] : Heap F)) rfl hFlag
  have hw := repU64_det large hVal₁ hVal₂
  subst hf hw
  rfl

/-- Uniqueness of splitting a header byte into `flag * 32 + low5` with `low5 < 32`. -/
theorem tag_header_split_unique {f₁ l₁ f₂ l₂ : Nat}
    (hl₁ : l₁ < 32) (hl₂ : l₂ < 32)
    (hEq : f₁ * 32 + l₁ = f₂ * 32 + l₂) :
    f₁ = f₂ ∧ l₁ = l₂ := by
  omega

/-- Uniqueness of `get_tagn4` header decomposition `low3 + 8 * cont + 16 * flag`
(`low3 < 8`, `cont < 2`). -/
theorem tagn4_header_split_unique {l₁ c₁ f₁ l₂ c₂ f₂ : Nat}
    (hl₁ : l₁ < 8) (hc₁ : c₁ < 2)
    (hl₂ : l₂ < 8) (hc₂ : c₂ < 2)
    (hEq : l₁ + 8 * c₁ + 16 * f₁ = l₂ + 8 * c₂ + 16 * f₂) :
    l₁ = l₂ ∧ c₁ = c₂ ∧ f₁ = f₂ := by
  omega

/-- Uniqueness of `get_tagn2` header decomposition `low5 + 32 * cont + 64 * flag`
(`low5 < 32`, `cont < 2`). -/
theorem tagn2_header_split_unique {l₁ c₁ f₁ l₂ c₂ f₂ : Nat}
    (hl₁ : l₁ < 32) (hc₁ : c₁ < 2)
    (hl₂ : l₂ < 32) (hc₂ : c₂ < 2)
    (hEq : l₁ + 32 * c₁ + 64 * f₁ = l₂ + 32 * c₂ + 64 * f₂) :
    l₁ = l₂ ∧ c₁ = c₂ ∧ f₁ = f₂ := by
  omega

/-- Natural-number value of up to 8 little-endian bytes, zero-padding higher bytes
(matching `IxonDeserialize::get_u64_le`). -/
def u64ValLeBytes (bytes : _root_.List UInt8) : Nat :=
  (bytes.getD 0 0).toNat +
  256 * (bytes.getD 1 0).toNat +
  65536 * (bytes.getD 2 0).toNat +
  16777216 * (bytes.getD 3 0).toNat +
  4294967296 * (bytes.getD 4 0).toNat +
  1099511627776 * (bytes.getD 5 0).toNat +
  281474976710656 * (bytes.getD 6 0).toNat +
  72057594037927936 * (bytes.getD 7 0).toNat

/-- Construct a `UInt64` from up to 8 little-endian bytes, zero-padding higher bytes
(matching `IxonDeserialize::get_u64_le`). -/
def u64OfLeBytes (bytes : _root_.List UInt8) : UInt64 :=
  UInt64.ofNat (u64ValLeBytes bytes)

theorem u64ValLeBytes_lt (bytes : _root_.List UInt8) :
    u64ValLeBytes bytes < 18446744073709551616 := by
  have h0 : (bytes.getD 0 0).toNat < 256 := (bytes.getD 0 0).toNat_lt
  have h1 : (bytes.getD 1 0).toNat < 256 := (bytes.getD 1 0).toNat_lt
  have h2 : (bytes.getD 2 0).toNat < 256 := (bytes.getD 2 0).toNat_lt
  have h3 : (bytes.getD 3 0).toNat < 256 := (bytes.getD 3 0).toNat_lt
  have h4 : (bytes.getD 4 0).toNat < 256 := (bytes.getD 4 0).toNat_lt
  have h5 : (bytes.getD 5 0).toNat < 256 := (bytes.getD 5 0).toNat_lt
  have h6 : (bytes.getD 6 0).toNat < 256 := (bytes.getD 6 0).toNat_lt
  have h7 : (bytes.getD 7 0).toNat < 256 := (bytes.getD 7 0).toNat_lt
  unfold u64ValLeBytes
  omega

theorem toNat_u64OfLeBytes (bytes : _root_.List UInt8) :
    (u64OfLeBytes bytes).toNat = u64ValLeBytes bytes := by
  rw [u64OfLeBytes, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (u64ValLeBytes_lt bytes)

theorem u64OfLeBytes_nil : (u64OfLeBytes []).toNat = 0 := by
  decide

theorem u64OfLeBytes_singleton (b0 : UInt8) :
    (u64OfLeBytes [b0]).toNat = b0.toNat := by
  rw [toNat_u64OfLeBytes]
  simp [u64ValLeBytes]

theorem u64OfLeBytes_pair (b0 b1 : UInt8) :
    (u64OfLeBytes [b0, b1]).toNat = b0.toNat + 256 * b1.toNat := by
  rw [toNat_u64OfLeBytes]
  simp [u64ValLeBytes]

/-- Mathematical correctness of the 2-byte `get_tagn_tail` case (`q < h ≤ 64`):
adding `lo + 2 * h = v0 + 256 * carry` and placing `q + carry` in the second limb
reconstructs `lo + 2 * h + 256 * q`. -/
theorem tagn_tail_two_byte_spec (lo v0 : UInt8) (q h carry : Nat)
    (hq : q < h) (hh : h ≤ 64) (hCarry : carry < 2)
    (hAdd : lo.toNat + 2 * h = v0.toNat + 256 * carry) :
    (u64OfLeBytes [v0, UInt8.ofNat (q + carry)]).toNat =
      lo.toNat + 2 * h + 256 * q := by
  rw [u64OfLeBytes_pair]
  have hqc : (UInt8.ofNat (q + carry)).toNat = q + carry := by
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [hqc]
  omega

end Aiur.Library.IxVMRep
