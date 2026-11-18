import IxVMRefinement.Iota.Scan
import IxVMRefinement.Subst.Spine
import IxVMRefinement.Decl.NativeCommon
import IxVMRefinement.L1.Ingress
import IxVMRefinement.L1.TraceRecords
import IxVMRefinement.Claim.TopProj
import IxVMRefinement.Obs

/-! # The nested-occurrence scan of the dispatch, as a function of the scanned term

`KernelModeled::block_is_modeled` answers at a block of one inductive type by scanning the
constructors for an application headed by an inductive type outside the block with an argument
that names a member (`ctors_nested`, `nested_scan`, `nested_scan_list`, `nested_mentions`,
`addr_is_inductive`, with `KernelWhnf::se_mentions` and `se_addr_in`). The scans read only the
shape of the heap term: its node kinds and the addresses of its constants. This module names
that shape and proves that each scan's answer is a function of it and of the record store.

* `ScanTree`, `TreeAt`: the shape of a heap term, independent of the heap; `TreeAt` is monotone
  and each load of a node fixes the tree's head constructor;
* `se_addr_in_exact`, `se_mentions_exact`, `nested_mentions_exact`: the membership scans are
  exact (`ScanTree.mentions`);
* `collect_spine_tree`, `peel_n_foralls_tree`: the spine and the peeled telescope;
* `Agrees`: an answer agrees with a value that may be unknown (`Option Bool`). The value is
  unknown where the store lacks a record the scan loads; a store that holds every canonical
  record the run hashed makes it known;
* `addr_is_inductive_agrees`: the head test against the store's record form (`isIndAt`);
* `nested_scan_agrees`, `nested_scan_list_agrees`: the scan against `nestedN`, the same
  left-to-right short-circuit computation over the tree.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace IxVM.Refinement.Route

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Core.Specs.Whnf
open IxVM.Consistency
open IxVM (F)

noncomputable section

/-! ## The shape of a heap term -/

/-- **The shape of a term as the routing scans read it**: node kinds and constant addresses.
Variables, sorts and literals are one leaf. -/
inductive ScanTree where
  | atom : ScanTree
  | const (a : _root_.Address) : ScanTree
  | app (f x : ScanTree) : ScanTree
  | lam (t b : ScanTree) : ScanTree
  | all (t b : ScanTree) : ScanTree
  | letE (t v b : ScanTree) : ScanTree
  | proj (x : ScanTree) : ScanTree

/-- The number of nodes. -/
def ScanTree.size : ScanTree → Nat
  | .atom => 1
  | .const _ => 1
  | .app f x => f.size + x.size + 1
  | .lam t b => t.size + b.size + 1
  | .all t b => t.size + b.size + 1
  | .letE t v b => t.size + v.size + b.size + 1
  | .proj x => x.size + 1

theorem ScanTree.size_pos (T : ScanTree) : 0 < T.size := by
  cases T <;> simp only [ScanTree.size] <;> omega

/-- The head of the application spine. -/
def ScanTree.head : ScanTree → ScanTree
  | .app f _ => f.head
  | .atom => .atom
  | .const a => .const a
  | .lam t b => .lam t b
  | .all t b => .all t b
  | .letE t v b => .letE t v b
  | .proj x => .proj x

/-- The arguments of the application spine, in order. -/
def ScanTree.args : ScanTree → List ScanTree
  | .app f x => f.args ++ [x]
  | .atom => []
  | .const _ => []
  | .lam _ _ => []
  | .all _ _ => []
  | .letE _ _ _ => []
  | .proj _ => []

/-- The address of a constant node. -/
def ScanTree.constAddr? : ScanTree → Option _root_.Address
  | .const a => some a
  | .atom => none
  | .app _ _ => none
  | .lam _ _ => none
  | .all _ _ => none
  | .letE _ _ _ => none
  | .proj _ => none

/-- The term after `n` leading `∀` nodes. -/
def ScanTree.peel : Nat → ScanTree → Option ScanTree
  | 0, T => some T
  | n + 1, .all _ b => ScanTree.peel n b
  | _ + 1, .atom => none
  | _ + 1, .const _ => none
  | _ + 1, .app _ _ => none
  | _ + 1, .lam _ _ => none
  | _ + 1, .letE _ _ _ => none
  | _ + 1, .proj _ => none

theorem ScanTree.head_size_le : ∀ T : ScanTree, T.head.size ≤ T.size
  | .app f x => by
    simp only [ScanTree.head, ScanTree.size]
    have := ScanTree.head_size_le f
    omega
  | .atom => Nat.le_refl _
  | .const _ => Nat.le_refl _
  | .lam _ _ => Nat.le_refl _
  | .all _ _ => Nat.le_refl _
  | .letE _ _ _ => Nat.le_refl _
  | .proj _ => Nat.le_refl _

theorem ScanTree.args_size_lt : ∀ (T A : ScanTree), A ∈ T.args → A.size < T.size
  | .app f x, A, hA => by
    simp only [ScanTree.args, List.mem_append, List.mem_singleton] at hA
    simp only [ScanTree.size]
    rcases hA with hA | hA
    · have := ScanTree.args_size_lt f A hA
      omega
    · subst hA
      omega
  | .atom, A, hA => by simp [ScanTree.args] at hA
  | .const _, A, hA => by simp [ScanTree.args] at hA
  | .lam _ _, A, hA => by simp [ScanTree.args] at hA
  | .all _ _, A, hA => by simp [ScanTree.args] at hA
  | .letE _ _ _, A, hA => by simp [ScanTree.args] at hA
  | .proj _, A, hA => by simp [ScanTree.args] at hA

/-- **The heap term at `p` has the shape `T`.** -/
inductive TreeAt (h : Heap F) : SourceValue F → ScanTree → Prop where
  | bvar {p : SourceValue F} {xs : List (SourceValue F)} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "BVar" xs) → TreeAt h p .atom
  | srt {p : SourceValue F} {xs : List (SourceValue F)} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Srt" xs) → TreeAt h p .atom
  | lit {p : SourceValue F} {xs : List (SourceValue F)} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Lit" xs) → TreeAt h p .atom
  | const {p ap lp : SourceValue F} {a : Bytes.Address} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Const" [ap, lp]) →
      Bytes.RepAddressRef addrTy h a ap → TreeAt h p (.const (ixAddr a))
  | app {p x y : SourceValue F} {Tx Ty : ScanTree} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "App" [x, y]) →
      TreeAt h x Tx → TreeAt h y Ty → TreeAt h p (.app Tx Ty)
  | lam {p x y l : SourceValue F} {Tx Ty : ScanTree} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Lam" [x, y, l]) →
      TreeAt h x Tx → TreeAt h y Ty → TreeAt h p (.lam Tx Ty)
  | all {p x y l : SourceValue F} {Tx Ty : ScanTree} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Forall" [x, y, l]) →
      TreeAt h x Tx → TreeAt h y Ty → TreeAt h p (.all Tx Ty)
  | letE {p x y z : SourceValue F} {Tx Ty Tz : ScanTree} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Let" [x, y, z]) →
      TreeAt h x Tx → TreeAt h y Ty → TreeAt h z Tz → TreeAt h p (.letE Tx Ty Tz)
  | proj {p ap i e : SourceValue F} {Te : ScanTree} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Proj" [ap, i, e]) →
      TreeAt h e Te → TreeAt h p (.proj Te)

theorem TreeAt.mono {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂) {p : SourceValue F}
    {T : ScanTree} (ht : TreeAt h₁ p T) : TreeAt h₂ p T := by
  induction ht with
  | bvar hl => exact .bvar (ext.loadValue_eq hl)
  | srt hl => exact .srt (ext.loadValue_eq hl)
  | lit hl => exact .lit (ext.loadValue_eq hl)
  | const hl ha =>
    exact .const (ext.loadValue_eq hl) (Bytes.repAddressRef_heapMono₂ addrTy ext ha)
  | app hl _ _ ihx ihy => exact .app (ext.loadValue_eq hl) ihx ihy
  | lam hl _ _ ihx ihy => exact .lam (ext.loadValue_eq hl) ihx ihy
  | all hl _ _ ihx ihy => exact .all (ext.loadValue_eq hl) ihx ihy
  | letE hl _ _ _ ihx ihy ihz => exact .letE (ext.loadValue_eq hl) ihx ihy ihz
  | proj hl _ ihe => exact .proj (ext.loadValue_eq hl) ihe

theorem treeAt_heapMono₂ : HeapMono₂ (fun (h₀ : Heap F) (X : ScanTree) (p₀ : SourceValue F) =>
    TreeAt h₀ p₀ X) :=
  fun _ _ _ _ ext r => r.mono ext

/-! ## A loaded node fixes the head of the tree -/

theorem TreeAt.app_inv {h : Heap F} {p x y : SourceValue F} {T : ScanTree} (ht : TreeAt h p T)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KExprNode" "App" [x, y])) :
    ∃ Tx Ty, T = .app Tx Ty ∧ TreeAt h x Tx ∧ TreeAt h y Ty := by
  cases ht with
  | app hl hx hy =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ _ hargs
    injection hargs with h1 hargs
    injection hargs with h2 _
    subst h1 h2
    exact ⟨_, _, rfl, hx, hy⟩
  | bvar hl | srt hl | lit hl | const hl _ | lam hl _ _ | all hl _ _ | letE hl _ _ _
  | proj hl _ =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ htag _
    exact absurd htag (by decide)

theorem TreeAt.lam_inv {h : Heap F} {p x y l : SourceValue F} {T : ScanTree}
    (ht : TreeAt h p T)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Lam" [x, y, l])) :
    ∃ Tx Ty, T = .lam Tx Ty ∧ TreeAt h x Tx ∧ TreeAt h y Ty := by
  cases ht with
  | lam hl hx hy =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ _ hargs
    injection hargs with h1 hargs
    injection hargs with h2 _
    subst h1 h2
    exact ⟨_, _, rfl, hx, hy⟩
  | bvar hl | srt hl | lit hl | const hl _ | app hl _ _ | all hl _ _ | letE hl _ _ _
  | proj hl _ =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ htag _
    exact absurd htag (by decide)

theorem TreeAt.all_inv {h : Heap F} {p x y l : SourceValue F} {T : ScanTree}
    (ht : TreeAt h p T)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Forall" [x, y, l])) :
    ∃ Tx Ty, T = .all Tx Ty ∧ TreeAt h x Tx ∧ TreeAt h y Ty := by
  cases ht with
  | all hl hx hy =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ _ hargs
    injection hargs with h1 hargs
    injection hargs with h2 _
    subst h1 h2
    exact ⟨_, _, rfl, hx, hy⟩
  | bvar hl | srt hl | lit hl | const hl _ | app hl _ _ | lam hl _ _ | letE hl _ _ _
  | proj hl _ =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ htag _
    exact absurd htag (by decide)

theorem TreeAt.let_inv {h : Heap F} {p x y z : SourceValue F} {T : ScanTree}
    (ht : TreeAt h p T)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Let" [x, y, z])) :
    ∃ Tx Ty Tz, T = .letE Tx Ty Tz ∧ TreeAt h x Tx ∧ TreeAt h y Ty ∧ TreeAt h z Tz := by
  cases ht with
  | letE hl hx hy hz =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ _ hargs
    injection hargs with h1 hargs
    injection hargs with h2 hargs
    injection hargs with h3 _
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, hx, hy, hz⟩
  | bvar hl | srt hl | lit hl | const hl _ | app hl _ _ | lam hl _ _ | all hl _ _
  | proj hl _ =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ htag _
    exact absurd htag (by decide)

theorem TreeAt.proj_inv {h : Heap F} {p ap i e : SourceValue F} {T : ScanTree}
    (ht : TreeAt h p T)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Proj" [ap, i, e])) :
    ∃ Te, T = .proj Te ∧ TreeAt h e Te := by
  cases ht with
  | proj hl he =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with h3 _
    subst h3
    exact ⟨_, rfl, he⟩
  | bvar hl | srt hl | lit hl | const hl _ | app hl _ _ | lam hl _ _ | all hl _ _
  | letE hl _ _ _ =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ htag _
    exact absurd htag (by decide)

theorem TreeAt.const_inv {h : Heap F} {p ap lp : SourceValue F} {T : ScanTree}
    (ht : TreeAt h p T)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Const" [ap, lp])) :
    ∃ a : Bytes.Address, T = .const (ixAddr a) ∧ Bytes.RepAddressRef addrTy h a ap := by
  cases ht with
  | const hl ha =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ _ hargs
    injection hargs with h1 _
    subst h1
    exact ⟨_, rfl, ha⟩
  | bvar hl | srt hl | lit hl | app hl _ _ | lam hl _ _ | all hl _ _ | letE hl _ _ _
  | proj hl _ =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ htag _
    exact absurd htag (by decide)

/-- A node that is no application, binder, `let` or projection is a leaf or a constant. -/
theorem TreeAt.leaf_inv {h : Heap F} {p v : SourceValue F} {T : ScanTree} (ht : TreeAt h p T)
    (ld : loadValue h p = .ok v)
    (hApp : ∀ vs : List (SourceValue F), vs.length = 2 →
      v ≠ .construct "KernelTypes::KExprNode" "App" vs)
    (hLam : ∀ vs : List (SourceValue F), vs.length = 3 →
      v ≠ .construct "KernelTypes::KExprNode" "Lam" vs)
    (hAll : ∀ vs : List (SourceValue F), vs.length = 3 →
      v ≠ .construct "KernelTypes::KExprNode" "Forall" vs)
    (hLet : ∀ vs : List (SourceValue F), vs.length = 3 →
      v ≠ .construct "KernelTypes::KExprNode" "Let" vs)
    (hProj : ∀ vs : List (SourceValue F), vs.length = 3 →
      v ≠ .construct "KernelTypes::KExprNode" "Proj" vs) :
    T = .atom ∨ ∃ (a : _root_.Address) (ap lp : SourceValue F), T = .const a ∧
      v = .construct "KernelTypes::KExprNode" "Const" [ap, lp] := by
  cases ht with
  | bvar hl => exact Or.inl rfl
  | srt hl => exact Or.inl rfl
  | lit hl => exact Or.inl rfl
  | const hl ha =>
    rw [hl] at ld
    injection ld with hv
    exact Or.inr ⟨_, _, _, rfl, hv.symm⟩
  | app hl _ _ =>
    rw [hl] at ld
    injection ld with hv
    exact (hApp [_, _] rfl hv.symm).elim
  | lam hl _ _ =>
    rw [hl] at ld
    injection ld with hv
    exact (hLam [_, _, _] rfl hv.symm).elim
  | all hl _ _ =>
    rw [hl] at ld
    injection ld with hv
    exact (hAll [_, _, _] rfl hv.symm).elim
  | letE hl _ _ _ =>
    rw [hl] at ld
    injection ld with hv
    exact (hLet [_, _, _] rfl hv.symm).elim
  | proj hl _ =>
    rw [hl] at ld
    injection ld with hv
    exact (hProj [_, _, _] rfl hv.symm).elim

/-- A node that is no constant has no constant address. -/
theorem TreeAt.not_const {h : Heap F} {p v : SourceValue F} {T : ScanTree} (ht : TreeAt h p T)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 2 →
      v ≠ .construct "KernelTypes::KExprNode" "Const" vs) :
    T.constAddr? = none := by
  cases ht with
  | const hl ha =>
    rw [hl] at ld
    injection ld with hv
    exact (hne [_, _] rfl hv.symm).elim
  | bvar _ => rfl
  | srt _ => rfl
  | lit _ => rfl
  | app _ _ _ => rfl
  | lam _ _ _ => rfl
  | all _ _ _ => rfl
  | letE _ _ _ _ => rfl
  | proj _ _ => rfl

/-! ## Answers -/

/-- The field an answer is returned as. -/
def bit (b : Bool) : SourceValue F := .field (if b = true then 1 else 0)

theorem bit_true : bit true = .field 1 := by simp [bit]

theorem bit_false : bit false = .field 0 := by simp [bit]

theorem bit_eq_one {b : Bool} (h : bit b = .field 1) : b = true := by
  cases b with
  | true => rfl
  | false =>
    rw [bit_false] at h
    exact absurd h.symm NatAux.field_one_ne_zero

theorem bit_ne_one {b : Bool} (h : bit b ≠ .field 1) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd bit_true h

/-- Membership of an address in a list, as an answer. -/
def memB (M : List _root_.Address) (a : _root_.Address) : Bool :=
  @ite Bool (a ∈ M) (Classical.propDecidable _) true false

theorem memB_pos {M : List _root_.Address} {a : _root_.Address} (h : a ∈ M) :
    memB M a = true := by
  unfold memB
  exact ite_eq_left h

theorem memB_neg {M : List _root_.Address} {a : _root_.Address} (h : a ∉ M) :
    memB M a = false := by
  unfold memB
  exact ite_eq_right h

theorem memB_cons_ne {M : List _root_.Address} {a b : _root_.Address} (hne : a ≠ b) :
    memB (b :: M) a = memB M a := by
  by_cases h : a ∈ M
  · rw [memB_pos h, memB_pos (List.mem_cons_of_mem _ h)]
  · rw [memB_neg h, memB_neg (by simp [hne, h])]

/-- **The term mentions an address of `M`** (the answer of `se_mentions`). A projection's
structure address is not read. -/
def ScanTree.mentions (M : List _root_.Address) : ScanTree → Bool
  | .atom => false
  | .const a => memB M a
  | .app f x => f.mentions M || x.mentions M
  | .lam t b => t.mentions M || b.mentions M
  | .all t b => t.mentions M || b.mentions M
  | .letE t v b => t.mentions M || (v.mentions M || b.mentions M)
  | .proj x => x.mentions M

/-! ## The membership scans -/

/-- **`se_addr_in` is exact**: membership of the address among the members' addresses. -/
theorem se_addr_in_exact :
    ∀ {ms : List Bytes.Address} {ap xs r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)} {a : Bytes.Address},
      Bytes.RepAddressRef addrTy h a ap → RepList addrListEnum RepAddr h ms xs →
      ObsFn Obs.W "KernelWhnf::se_addr_in" [ap, xs] h r h' cs →
      r = bit (memB (ms.map ixAddr) (ixAddr a)) ∧ h' = h := by
  intro ms
  induction ms with
  | nil =>
    intro ap xs r h h' cs a ha hms ev
    rcases Obs.«KernelWhnf::se_addr_in».obs ev with
      ⟨ld12, he20, he21, hc22⟩ |
      ⟨x_x, x_rest, m41, cs52, ld12, ev54, he75, he76, hc77⟩ |
      ⟨x_x, x_rest, v40, m41, cs52, cs85, ld12, ev54, hne78, ev87, hc104⟩
    · refine ⟨?_, he21⟩
      rw [he20, List.map_nil, memB_neg (by simp), bit_false]
    · obtain ⟨z, zs, hnil, -, -⟩ := RepList.cons_of_load hms ld12
      cases hnil
    · obtain ⟨z, zs, hnil, -, -⟩ := RepList.cons_of_load hms ld12
      cases hnil
  | cons b ms ih =>
    intro ap xs r h h' cs a ha hms ev
    rcases Obs.«KernelWhnf::se_addr_in».obs ev with
      ⟨ld12, he20, he21, hc22⟩ |
      ⟨x_x, x_rest, m41, cs52, ld12, ev54, he75, he76, hc77⟩ |
      ⟨x_x, x_rest, v40, m41, cs52, cs85, ld12, ev54, hne78, ev87, hc104⟩
    · have hnil := RepList.nil_of_load hms ld12
      cases hnil
    · obtain ⟨z, zs, hcons, hb, -⟩ := RepList.cons_of_load hms ld12
      injection hcons with e1 e2
      subst e1 e2
      obtain ⟨hr1, rfl⟩ := Lib.address_eq_spec ev54 ha hb
      have hab : a = b := by
        by_contra hne
        rw [ite_eq_right hne] at hr1
        exact NatAux.field_one_ne_zero hr1
      subst hab
      refine ⟨?_, he76⟩
      rw [he75, List.map_cons, memB_pos (by simp), bit_true]
    · obtain ⟨z, zs, hcons, hb, hms'⟩ := RepList.cons_of_load hms ld12
      injection hcons with e1 e2
      subst e1 e2
      obtain ⟨hr1, rfl⟩ := Lib.address_eq_spec ev54 ha hb
      have hab : a ≠ b := by
        intro e
        rw [ite_eq_left e] at hr1
        exact hne78 hr1
      obtain ⟨hr, hh⟩ := ih ha hms' ev87
      refine ⟨?_, hh⟩
      have hne : ixAddr a ≠ ixAddr b := fun e => hab (Claim.ixAddr_injective e)
      rw [hr, List.map_cons, memB_cons_ne hne]

/-- **`se_mentions` is exact**: the answer is `1` exactly where the term mentions a member. -/
theorem se_mentions_exact {ms : List Bytes.Address} :
    ∀ (n : Nat) {T : ScanTree} {e xs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      T.size ≤ n → TreeAt h e T → RepList addrListEnum RepAddr h ms xs →
      ObsFn Obs.W "KernelWhnf::se_mentions" [e, xs] h r h' cs →
      r = bit (T.mentions (ms.map ixAddr)) := by
  intro n
  induction n with
  | zero =>
    intro T e xs r h h' cs hn
    have := T.size_pos
    omega
  | succ n ih =>
    intro T e xs r h h' cs hn ht hms ev
    rcases Obs.«KernelWhnf::se_mentions».obs ev with
      ⟨x_a, w20, cs34, ld12, ev36, hc53⟩ |
      ⟨x_f, x_x, m72, cs83, ld12, ev85, he106, he107, hc108⟩ |
      ⟨x_f, x_x, v71, m72, cs83, cs116, ld12, ev85, hne109, ev118, hc135⟩ |
      ⟨x_t, x_b, w143, m160, cs171, ld12, ev173, he194, he195, hc196⟩ |
      ⟨x_t, x_b, w143, v159, m160, cs171, cs204, ld12, ev173, hne197, ev206, hc223⟩ |
      ⟨x_t, x_b, w231, m248, cs259, ld12, ev261, he282, he283, hc284⟩ |
      ⟨x_t, x_b, w231, v247, m248, cs259, cs292, ld12, ev261, hne285, ev294, hc311⟩ |
      ⟨x_t, x_v, x_b, m335, cs346, ld12, ev348, he369, he370, hc371⟩ |
      ⟨x_t, x_v, x_b, v334, m335, cs346, m377, cs388, ld12, ev348, hne372, ev390, he411, he412,
        hc413⟩ |
      ⟨x_t, x_v, x_b, v334, m335, cs346, v376, m377, cs388, cs421, ld12, ev348, hne372, ev390,
        hne414, ev423, hc440⟩ |
      ⟨w448, w449, x_inner, cs468, ld12, ev470, hc487⟩ |
      ⟨v1, ld12, hne54, hne136, hne224, hne312, hne441, hne488, he492, he493, hc494⟩
    · -- a constant
      obtain ⟨a, rfl, ha⟩ := ht.const_inv ld12
      obtain ⟨hr, -⟩ := se_addr_in_exact ha hms ev36
      rw [hr]
      simp only [ScanTree.mentions]
    · -- an application whose function mentions a member
      obtain ⟨Tf, Tx, rfl, hf, hx⟩ := ht.app_inv ld12
      simp only [ScanTree.size] at hn
      have c1 := ih (by omega) hf hms ev85
      have m1 := bit_eq_one c1.symm
      rw [he106]
      simp only [ScanTree.mentions, m1, Bool.true_or, bit_true]
    · obtain ⟨Tf, Tx, rfl, hf, hx⟩ := ht.app_inv ld12
      simp only [ScanTree.size] at hn
      have ext := ev85.heap_extends
      have c1 := ih (by omega) hf hms ev85
      have m1 := bit_ne_one (by rw [← c1]; exact hne109)
      have c2 := ih (by omega) (hx.mono ext) (se_addrs_mono ext hms) ev118
      rw [c2]
      simp only [ScanTree.mentions, m1, Bool.false_or]
    · obtain ⟨Tt, Tb, rfl, ht', hb'⟩ := ht.lam_inv ld12
      simp only [ScanTree.size] at hn
      have c1 := ih (by omega) ht' hms ev173
      have m1 := bit_eq_one c1.symm
      rw [he194]
      simp only [ScanTree.mentions, m1, Bool.true_or, bit_true]
    · obtain ⟨Tt, Tb, rfl, ht', hb'⟩ := ht.lam_inv ld12
      simp only [ScanTree.size] at hn
      have ext := ev173.heap_extends
      have c1 := ih (by omega) ht' hms ev173
      have m1 := bit_ne_one (by rw [← c1]; exact hne197)
      have c2 := ih (by omega) (hb'.mono ext) (se_addrs_mono ext hms) ev206
      rw [c2]
      simp only [ScanTree.mentions, m1, Bool.false_or]
    · obtain ⟨Tt, Tb, rfl, ht', hb'⟩ := ht.all_inv ld12
      simp only [ScanTree.size] at hn
      have c1 := ih (by omega) ht' hms ev261
      have m1 := bit_eq_one c1.symm
      rw [he282]
      simp only [ScanTree.mentions, m1, Bool.true_or, bit_true]
    · obtain ⟨Tt, Tb, rfl, ht', hb'⟩ := ht.all_inv ld12
      simp only [ScanTree.size] at hn
      have ext := ev261.heap_extends
      have c1 := ih (by omega) ht' hms ev261
      have m1 := bit_ne_one (by rw [← c1]; exact hne285)
      have c2 := ih (by omega) (hb'.mono ext) (se_addrs_mono ext hms) ev294
      rw [c2]
      simp only [ScanTree.mentions, m1, Bool.false_or]
    · obtain ⟨Tt, Tv, Tb, rfl, ht', hv', hb'⟩ := ht.let_inv ld12
      simp only [ScanTree.size] at hn
      have c1 := ih (by omega) ht' hms ev348
      have m1 := bit_eq_one c1.symm
      rw [he369]
      simp only [ScanTree.mentions, m1, Bool.true_or, bit_true]
    · obtain ⟨Tt, Tv, Tb, rfl, ht', hv', hb'⟩ := ht.let_inv ld12
      simp only [ScanTree.size] at hn
      have ext := ev348.heap_extends
      have c1 := ih (by omega) ht' hms ev348
      have m1 := bit_ne_one (by rw [← c1]; exact hne372)
      have c2 := ih (by omega) (hv'.mono ext) (se_addrs_mono ext hms) ev390
      have m2 := bit_eq_one c2.symm
      rw [he411]
      simp only [ScanTree.mentions, m1, m2, Bool.false_or, Bool.true_or, bit_true]
    · obtain ⟨Tt, Tv, Tb, rfl, ht', hv', hb'⟩ := ht.let_inv ld12
      simp only [ScanTree.size] at hn
      have ext1 := ev348.heap_extends
      have ext2 := ev390.heap_extends
      have c1 := ih (by omega) ht' hms ev348
      have m1 := bit_ne_one (by rw [← c1]; exact hne372)
      have c2 := ih (by omega) (hv'.mono ext1) (se_addrs_mono ext1 hms) ev390
      have m2 := bit_ne_one (by rw [← c2]; exact hne414)
      have c3 := ih (by omega) (hb'.mono (ext1.trans ext2))
        (se_addrs_mono (ext1.trans ext2) hms) ev423
      rw [c3]
      simp only [ScanTree.mentions, m1, m2, Bool.false_or]
    · obtain ⟨Te, rfl, he'⟩ := ht.proj_inv ld12
      simp only [ScanTree.size] at hn
      have c1 := ih (by omega) he' hms ev470
      rw [c1]
      simp only [ScanTree.mentions]
    · -- a leaf
      rcases ht.leaf_inv ld12 hne136 hne224 hne312 hne441 hne488 with rfl | ⟨a, ap, lp, -, hv⟩
      · rw [he492]
        simp only [ScanTree.mentions, bit_false]
      · exact (hne54 [_, _] rfl hv).elim

/-- **`nested_mentions` is exact**: some argument mentions a member. -/
theorem nested_mentions_exact {ms : List Bytes.Address} :
    ∀ {As : List ScanTree} {es xs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList kexprListEnum (fun h₀ X p₀ => TreeAt h₀ p₀ X) h As es →
      RepList addrListEnum RepAddr h ms xs →
      ObsFn Obs.W "KernelModeled::nested_mentions" [es, xs] h r h' cs →
      r = bit (As.any fun A => A.mentions (ms.map ixAddr)) := by
  intro As
  induction As with
  | nil =>
    intro es xs r h h' cs hAs hms ev
    rcases Obs.«KernelModeled::nested_mentions».obs ev with
      ⟨ld12, he20, he21, hc22⟩ |
      ⟨x_e, x_rest, m41, cs52, ld12, ev54, he75, he76, hc77⟩ |
      ⟨x_e, x_rest, v40, m41, cs52, cs85, ld12, ev54, hne78, ev87, hc104⟩
    · rw [he20]
      simp only [List.any_nil, bit_false]
    · obtain ⟨z, zs, hnil, -, -⟩ := RepList.cons_of_load hAs ld12
      cases hnil
    · obtain ⟨z, zs, hnil, -, -⟩ := RepList.cons_of_load hAs ld12
      cases hnil
  | cons A As ih =>
    intro es xs r h h' cs hAs hms ev
    rcases Obs.«KernelModeled::nested_mentions».obs ev with
      ⟨ld12, he20, he21, hc22⟩ |
      ⟨x_e, x_rest, m41, cs52, ld12, ev54, he75, he76, hc77⟩ |
      ⟨x_e, x_rest, v40, m41, cs52, cs85, ld12, ev54, hne78, ev87, hc104⟩
    · have hnil := RepList.nil_of_load hAs ld12
      cases hnil
    · obtain ⟨z, zs, hcons, hA, -⟩ := RepList.cons_of_load hAs ld12
      injection hcons with e1 e2
      subst e1 e2
      have c1 := se_mentions_exact (ms := ms) _ (Nat.le_refl _) hA hms ev54
      have m1 := bit_eq_one c1.symm
      rw [he75]
      simp only [List.any_cons, m1, Bool.true_or, bit_true]
    · obtain ⟨z, zs, hcons, hA, hrest⟩ := RepList.cons_of_load hAs ld12
      injection hcons with e1 e2
      subst e1 e2
      have ext := ev54.heap_extends
      have c1 := se_mentions_exact (ms := ms) _ (Nat.le_refl _) hA hms ev54
      have m1 := bit_ne_one (by rw [← c1]; exact hne78)
      have c2 := ih (hrest.mono treeAt_heapMono₂ ext) (se_addrs_mono ext hms) ev87
      rw [c2]
      simp only [List.any_cons, m1, Bool.false_or]

/-! ## The spine and the peeled telescope -/

/-- **`collect_spine` on a term of a given shape**: the head and the arguments, with theirs. -/
theorem collect_spine_tree :
    ∀ (n : Nat) {T : ScanTree} {e r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      T.size ≤ n → TreeAt h e T →
      ObsFn Obs.W "KernelTypes::collect_spine" [e] h r h' cs →
      ∃ hd sp, r = .tuple [hd, sp] ∧ TreeAt h' hd T.head ∧
        RepList kexprListEnum (fun h₀ X p₀ => TreeAt h₀ p₀ X) h' T.args sp := by
  intro n
  induction n with
  | zero =>
    intro T e r h h' cs hn
    have := T.size_pos
    omega
  | succ n ih =>
    intro T e r h h' cs hn ht ev
    match Obs.«KernelTypes::collect_spine».obs ev with
    | .App (ld12 := ld) (ev43 := e1) (he69 := hr) (ev88 := e2) (he105 := he) .. =>
      subst hr he
      obtain ⟨Tf, Tx, rfl, hf, hx⟩ := ht.app_inv ld
      simp only [ScanTree.size] at hn
      obtain ⟨hd, sp, htup, hH, hAs⟩ := ih (by omega) hf e1
      injection htup with hl
      injection hl with h1 hl
      injection hl with h2
      subst h1 h2
      refine ⟨_, _, rfl, ?_, ?_⟩
      · simp only [ScanTree.head]
        exact hH.mono e2.heap_extends
      · simp only [ScanTree.args]
        exact SubstAux.ksnoc treeAt_heapMono₂ e2 hAs (hx.mono e1.heap_extends)
    | .other (v1 := v1) (ld12 := ld) (hne107 := hne) (he115 := hr) (hm132 := hm)
        (he136 := he) .. =>
      subst hr hm he
      have hna : T.head = T ∧ T.args = [] := by
        cases ht with
        | app hl _ _ =>
          rw [hl] at ld
          injection ld with hv
          exact (hne [_, _] rfl hv.symm).elim
        | bvar _ => exact ⟨rfl, rfl⟩
        | srt _ => exact ⟨rfl, rfl⟩
        | lit _ => exact ⟨rfl, rfl⟩
        | const _ _ => exact ⟨rfl, rfl⟩
        | lam _ _ _ => exact ⟨rfl, rfl⟩
        | all _ _ _ => exact ⟨rfl, rfl⟩
        | letE _ _ _ _ => exact ⟨rfl, rfl⟩
        | proj _ _ => exact ⟨rfl, rfl⟩
      rw [hna.1, hna.2]
      exact ⟨e, _, rfl, ht.mono (Heap.Extends.snoc _ _), .nil (by simp)⟩

/-- **`peel_n_foralls` on a term of a given shape**: the term after `n` leading `∀` nodes. -/
theorem peel_n_foralls_tree :
    ∀ (n : Nat) {T : ScanTree} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 → TreeAt h pe T →
      ObsFn Obs.W "KernelCheck::peel_n_foralls" [pe, .field (n : F)] h r h' cs →
      ∃ T', T.peel n = some T' ∧ TreeAt h' r T'
  | 0, T, pe, r, h, h', cs, _, hT, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨T, rfl, hT⟩
    · exact absurd rfl hne
  | m + 1, T, pe, r, h, h', cs, hlt, hT, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨hv, _, _, _⟩ | ⟨w42, x_body, w43, cs62, v66, _, ld34, op87, ev64, _⟩
    · exact absurd hv (Decl.succ_field_ne_zero_bounded hlt)
    · obtain ⟨Tt, Tb, rfl, -, hb⟩ := hT.all_inv ld34
      rw [Decl.evalBinOp_sub_succ m op87] at ev64
      obtain ⟨T', hp, hT'⟩ := peel_n_foralls_tree m (by omega) hb ev64
      exact ⟨T', by simp only [ScanTree.peel]; exact hp, hT'⟩

/-! ## Answers that may be unknown -/

/-- Short-circuit disjunction of two answers, the first of which may be unknown. -/
def orElse : Option Bool → Option Bool → Option Bool
  | none, _ => none
  | some true, _ => some true
  | some false, o => o

/-- **The answer `r` agrees with the value `o`**: where `o` is known, `r` is it; and under
`cov` it is known. -/
structure Agrees (cov : Prop) (o : Option Bool) (r : SourceValue F) : Prop where
  value : ∀ v, o = some v → r = bit v
  known : cov → ∃ v, o = some v

theorem Agrees.pure {cov : Prop} {b : Bool} {r : SourceValue F} (h : r = bit b) :
    Agrees cov (some b) r :=
  ⟨fun v hv => by cases hv; exact h, fun _ => ⟨b, rfl⟩⟩

theorem Agrees.weaken {cov cov' : Prop} {o : Option Bool} {r : SourceValue F}
    (h : Agrees cov' o r) (hc : cov → cov') : Agrees cov o r :=
  ⟨h.value, fun c => h.known (hc c)⟩

theorem Agrees.orElse_one {cov : Prop} {o₁ o₂ : Option Bool} {r₁ r : SourceValue F}
    (h₁ : Agrees cov o₁ r₁) (hr₁ : r₁ = .field 1) (hr : r = .field 1) :
    Agrees cov (orElse o₁ o₂) r := by
  constructor
  · intro v hv
    cases o₁ with
    | none => cases (show (none : Option Bool) = some v from hv)
    | some a =>
      have ha := h₁.value a rfl
      rw [hr₁] at ha
      have hat : a = true := bit_eq_one ha.symm
      subst hat
      have hv' : some true = some v := hv
      cases hv'
      rw [hr, bit_true]
  · intro hc
    obtain ⟨a, ha⟩ := h₁.known hc
    subst ha
    have ha' := h₁.value a rfl
    rw [hr₁] at ha'
    have hat : a = true := bit_eq_one ha'.symm
    subst hat
    exact ⟨true, rfl⟩

theorem Agrees.orElse_other {cov : Prop} {o₁ o₂ : Option Bool} {r₁ r : SourceValue F}
    (h₁ : Agrees cov o₁ r₁) (hne : r₁ ≠ .field 1) (h₂ : Agrees cov o₂ r) :
    Agrees cov (orElse o₁ o₂) r := by
  constructor
  · intro v hv
    cases o₁ with
    | none => cases (show (none : Option Bool) = some v from hv)
    | some a =>
      have ha := h₁.value a rfl
      have haf : a = false := bit_ne_one (by rw [← ha]; exact hne)
      subst haf
      exact h₂.value v hv
  · intro hc
    obtain ⟨a, ha⟩ := h₁.known hc
    subst ha
    have ha' := h₁.value a rfl
    have haf : a = false := bit_ne_one (by rw [← ha']; exact hne)
    subst haf
    exact h₂.known hc

/-- Goodness and coverage pass to a part of a run. -/
theorem sub_good {E : Ixon.Env} {cs cs' : List (Call F)} (hsub : ∀ z ∈ cs', z ∈ cs)
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs) :
    ¬ View.HashedCollision { env := E } [] cs' ∧ Bounded cs' ∧
      (L1.CanonicalHashCoverage E cs → L1.CanonicalHashCoverage E cs') :=
  ⟨fun hcol => hnc (Core.collision_mono hsub hcol), Core.bounded_sub hsub hbd,
    fun h bytes value hh hsz hx => h bytes value (Core.hashed_mono hsub hh) hsz hx⟩

/-- **Within a run that hashes no collision, the bytes hashed at an address are unique.** -/
theorem hashed_inj_of_noCollision {V : View} {calls : List (Call F)}
    (hnc : ¬ V.HashedCollision [] calls) {b₁ b₂ : ByteArray}
    (h₁ : Hashed calls b₁) (h₂ : Hashed calls b₂)
    (he : Address.blake3Pure b₁ = Address.blake3Pure b₂) : b₁ = b₂ := by
  by_contra hne
  exact hnc (.inl ⟨Address.blake3Pure b₂, b₂, b₁, .inr (.inr ⟨h₂, rfl⟩), h₁, hne, he⟩)

/-! ## The head test -/

/-- The record is an inductive projection record. -/
def isIPrj (c : Ixon.Constant) : Bool :=
  match c.info with
  | .iPrj _ => true
  | .defn _ => false
  | .axio _ => false
  | .quot _ => false
  | .recr _ => false
  | .dPrj _ => false
  | .cPrj _ => false
  | .rPrj _ => false
  | .muts _ => false

/-- **Whether the store's record at `a` is an inductive projection record**; unknown where
the store holds no record at `a`. -/
def isIndAt (E : Ixon.Env) (a : _root_.Address) : Option Bool :=
  (recordOf E a).map isIPrj

/-- **The value `get_ci` returns is an `Induct` value exactly at an inductive projection
record.** -/
theorem getCIRaw_isInduct {calls : List (Call F)} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {a : _root_.Address} {c : Ixon.Constant} {r v : SourceValue F}
    (hres : L1.GetCIRawResult calls blobs h a c r) (hlv : loadValue h r = .ok v) :
    (isIPrj c = true ∧ ∃ vs : List (SourceValue F),
        v = .construct "KernelTypes::KConstantInfo" "Induct" vs ∧ vs.length = 8) ∨
      (isIPrj c = false ∧ ∀ vs : List (SourceValue F),
        v ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs) := by
  unfold L1.GetCIRawResult at hres
  unfold isIPrj
  cases hinfo : c.info with
  | defn d =>
    rw [hinfo] at hres
    obtain ⟨v', hlv', -, tyPtr, valPtr, hint, hv', -, -⟩ := hres
    have e := Except.ok.inj (hlv.symm.trans hlv')
    subst e
    refine Or.inr ⟨rfl, fun vs e => ?_⟩
    rw [hv'] at e
    cases hk : d.kind <;> simp only [L1.defnValShape, hk] at e <;>
      (injection e with _ htag _; exact absurd htag (by decide))
  | axio ax =>
    rw [hinfo] at hres
    obtain ⟨v', hlv', -, tyPtr, hv', -⟩ := hres
    have e := Except.ok.inj (hlv.symm.trans hlv')
    subst e
    refine Or.inr ⟨rfl, fun vs e => ?_⟩
    rw [hv'] at e
    injection e with _ htag _
    exact absurd htag (by decide)
  | quot q =>
    rw [hinfo] at hres
    obtain ⟨v', hlv', -, tyPtr, hv', -⟩ := hres
    have e := Except.ok.inj (hlv.symm.trans hlv')
    subst e
    refine Or.inr ⟨rfl, fun vs e => ?_⟩
    rw [hv'] at e
    injection e with _ htag _
    exact absurd htag (by decide)
  | recr rc =>
    rw [hinfo] at hres
    obtain ⟨v', hlv', -, -, -, -, -, -, tyPtr, rulesPtr, blkPtr, b, -, -, hv', -⟩ := hres
    have e := Except.ok.inj (hlv.symm.trans hlv')
    subst e
    refine Or.inr ⟨rfl, fun vs e => ?_⟩
    rw [hv'] at e
    injection e with _ htag _
    exact absurd htag (by decide)
  | dPrj p =>
    rw [hinfo] at hres
    obtain ⟨-, blkBytes, cb, ms, d, v', -, -, -, -, -, -, hlv', -, tyPtr, valPtr, hint, hv',
      -, -⟩ := hres
    have e := Except.ok.inj (hlv.symm.trans hlv')
    subst e
    refine Or.inr ⟨rfl, fun vs e => ?_⟩
    rw [hv'] at e
    cases hk : d.kind <;> simp only [L1.defnValShape, hk] at e <;>
      (injection e with _ htag _; exact absurd htag (by decide))
  | iPrj p =>
    rw [hinfo] at hres
    obtain ⟨-, blkBytes, cb, ms, ind, v', -, -, -, -, -, -, hlv', -, -, -, -, -, tyPtr, blkPtr,
      b, -, -, hv', -⟩ := hres
    have e := Except.ok.inj (hlv.symm.trans hlv')
    subst e
    exact Or.inl ⟨rfl, _, hv', rfl⟩
  | cPrj p =>
    rw [hinfo] at hres
    obtain ⟨-, -, blkBytes, cb, ms, ind, ct, v', -, -, -, -, -, -, -, hlv', -, -, -, -, -,
      tyPtr, blkPtr, b, -, -, hv', -⟩ := hres
    have e := Except.ok.inj (hlv.symm.trans hlv')
    subst e
    refine Or.inr ⟨rfl, fun vs e => ?_⟩
    rw [hv'] at e
    injection e with _ htag _
    exact absurd htag (by decide)
  | rPrj p =>
    rw [hinfo] at hres
    obtain ⟨-, blkBytes, cb, ms, rc, v', -, -, -, -, -, -, hlv', -, -, -, -, -, -, tyPtr,
      rulesPtr, blkPtr, b, -, -, hv', -⟩ := hres
    have e := Except.ok.inj (hlv.symm.trans hlv')
    subst e
    refine Or.inr ⟨rfl, fun vs e => ?_⟩
    rw [hv'] at e
    injection e with _ htag _
    exact absurd htag (by decide)
  | muts ms =>
    rw [hinfo] at hres
    exact hres.elim

/-- **`addr_is_inductive` against the store**: the answer is whether the record at the address
is an inductive projection record, where the store holds it; a store that covers the run
holds it. -/
theorem addr_is_inductive_agrees {E : Ixon.Env} {a : Bytes.Address} {ap r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn Obs.W "KernelModeled::addr_is_inductive" [ap] h r h' cs) :
    Agrees (L1.CanonicalHashCoverage E cs) (isIndAt E (ixAddr a)) r := by
  -- the record the run loaded at the address, and the answer on it
  have key : ∃ (raw : ByteArray) (c : Ixon.Constant), raw.size < 4294967296 ∧ Hashed cs raw ∧
      Address.blake3Pure raw = ixAddr a ∧ Ixon.deConstantExact raw = .ok c ∧
      r = bit (isIPrj c) := by
    rcases Obs.«KernelModeled::addr_is_inductive».obs ev with
      ⟨m2, p10, cs16, w33, w34, w35, w36, w37, w38, w39, w40, ev18, ld12, he81, he82, hc83⟩ |
      ⟨v1, m2, p10, cs16, ev18, ld12, hne84, he88, he89, hc90⟩
    · have hsub : ∀ z ∈ cs16, z ∈ cs := by
        rw [hc83]
        intro z hz
        simp [hz]
      obtain ⟨n1, b1, -⟩ := sub_good hsub hnc hbd
      obtain ⟨raw, c, hsz, hh, hba, hx, -, -⟩ := Claim.get_ci_head ha ev18
      obtain ⟨-, raw', c', blobs, hh', hba', hx', -, -, -, hres⟩ := L1.get_ci_spec b1 ha ev18
      have eraw : raw' = raw := hashed_inj_of_noCollision n1 hh' hh (hba'.trans hba.symm)
      subst eraw
      have ec : c' = c := Except.ok.inj (hx'.symm.trans hx)
      subst ec
      refine ⟨raw', c', hsz, Core.hashed_mono hsub hh, hba, hx, ?_⟩
      rcases getCIRaw_isInduct hres ld12 with ⟨hi, -⟩ | ⟨-, hno⟩
      · rw [he81, hi, bit_true]
      · exact (hno _ rfl).elim
    · have hsub : ∀ z ∈ cs16, z ∈ cs := by
        rw [hc90]
        intro z hz
        simp [hz]
      obtain ⟨n1, b1, -⟩ := sub_good hsub hnc hbd
      obtain ⟨raw, c, hsz, hh, hba, hx, -, -⟩ := Claim.get_ci_head ha ev18
      obtain ⟨-, raw', c', blobs, hh', hba', hx', -, -, -, hres⟩ := L1.get_ci_spec b1 ha ev18
      have eraw : raw' = raw := hashed_inj_of_noCollision n1 hh' hh (hba'.trans hba.symm)
      subst eraw
      have ec : c' = c := Except.ok.inj (hx'.symm.trans hx)
      subst ec
      refine ⟨raw', c', hsz, Core.hashed_mono hsub hh, hba, hx, ?_⟩
      rcases getCIRaw_isInduct hres ld12 with ⟨-, vs, hv, hlen⟩ | ⟨hi, -⟩
      · exact (hne84 vs hlen hv).elim
      · rw [he88, hi, bit_false]
  obtain ⟨raw, c, hsz, hh, hba, hx, hr⟩ := key
  constructor
  · intro v hv
    unfold isIndAt at hv
    cases hrec : recordOf E (ixAddr a) with
    | none =>
      rw [hrec] at hv
      cases hv
    | some c' =>
      rw [hrec] at hv
      have hv' : some (isIPrj c') = some v := hv
      cases hv'
      obtain ⟨lc, hget, hdec⟩ := LoadedReads.recordOf_inv hrec
      have eraw : raw = lc.rawBytes := Core.load_escape hget hnc raw hh hba
      rw [eraw, hdec] at hx
      have ec : c' = c := Except.ok.inj hx
      rw [ec]
      exact hr
  · intro hcov
    obtain ⟨⟨lc, c', hlc, hcached, hce⟩, hval⟩ := hcov raw c hh hsz hx
    have hrec : recordOf E (Address.blake3Pure raw) = some c' := by
      unfold recordOf
      rw [hlc]
      simp [hce, Except.toOption]
    refine ⟨isIPrj c', ?_⟩
    unfold isIndAt
    rw [← hba, hrec]
    rfl

/-! ## The scan -/

/-- The answer at a constant head: `0` at a member; otherwise the head test where an argument
mentions a member, and `0` where none does. -/
def hereConst (isInd : _root_.Address → Option Bool) (a : _root_.Address) :
    Bool → Bool → Option Bool
  | true, _ => some false
  | false, false => some false
  | false, true => isInd a

/-- The answer at the head of a spine: `hereConst` at a constant, the scan's answer `w` on the
head otherwise. -/
def hereOf (isInd : _root_.Address → Option Bool) (M : List _root_.Address) (H : ScanTree)
    (m : Bool) (w : Option Bool) : Option Bool :=
  match H.constAddr? with
  | some a => hereConst isInd a (memB M a) m
  | none => w

/-- **The answer of `nested_scan` on a tree**, by the scan's own left-to-right short-circuit
order, with the head test `isInd` and at most `n` levels of the tree (`none` below that; a tree
of `n` nodes needs no more). -/
def nestedN (isInd : _root_.Address → Option Bool) (M : List _root_.Address) :
    Nat → ScanTree → Option Bool
  | 0, _ => none
  | _ + 1, .atom => some false
  | _ + 1, .const _ => some false
  | n + 1, .lam t b => orElse (nestedN isInd M n t) (nestedN isInd M n b)
  | n + 1, .all t b => orElse (nestedN isInd M n t) (nestedN isInd M n b)
  | n + 1, .letE t v b =>
    orElse (nestedN isInd M n t) (orElse (nestedN isInd M n v) (nestedN isInd M n b))
  | n + 1, .proj x => nestedN isInd M n x
  | n + 1, .app f x =>
    orElse
      (hereOf isInd M (ScanTree.app f x).head
        ((ScanTree.app f x).args.any fun A => A.mentions M)
        (nestedN isInd M n (ScanTree.app f x).head))
      (((ScanTree.app f x).args.map (nestedN isInd M n)).foldr orElse (some false))

/-- **The specification of `nested_scan` at trees of at most `n` nodes.** -/
def ScanSpec (E : Ixon.Env) (ms : List Bytes.Address) (n : Nat) : Prop :=
  ∀ {T : ScanTree} {e xs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    T.size ≤ n → TreeAt h e T → RepList addrListEnum RepAddr h ms xs →
    ¬ View.HashedCollision { env := E } [] cs → Bounded cs →
    ObsFn Obs.W "KernelModeled::nested_scan" [e, xs] h r h' cs →
    Agrees (L1.CanonicalHashCoverage E cs) (nestedN (isIndAt E) (ms.map ixAddr) n T) r

/-- **`nested_scan_list` against the fold of the scan over the arguments.** -/
theorem nested_scan_list_agrees {E : Ixon.Env} {ms : List Bytes.Address} (n : Nat)
    (ihn : ScanSpec E ms n) :
    ∀ {As : List ScanTree} {es xs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ A ∈ As, A.size ≤ n) →
      RepList kexprListEnum (fun h₀ X p₀ => TreeAt h₀ p₀ X) h As es →
      RepList addrListEnum RepAddr h ms xs →
      ¬ View.HashedCollision { env := E } [] cs → Bounded cs →
      ObsFn Obs.W "KernelModeled::nested_scan_list" [es, xs] h r h' cs →
      Agrees (L1.CanonicalHashCoverage E cs)
        ((As.map (nestedN (isIndAt E) (ms.map ixAddr) n)).foldr orElse (some false)) r := by
  intro As
  induction As with
  | nil =>
    intro es xs r h h' cs hsz hAs hms hnc hbd ev
    rcases Obs.«KernelModeled::nested_scan_list».obs ev with
      ⟨ld12, he20, he21, hc22⟩ |
      ⟨x_e, x_rest, m41, cs52, ld12, ev54, he75, he76, hc77⟩ |
      ⟨x_e, x_rest, v40, m41, cs52, cs85, ld12, ev54, hne78, ev87, hc104⟩
    · simp only [List.map_nil, List.foldr_nil]
      exact Agrees.pure (by rw [he20, bit_false])
    · obtain ⟨z, zs, hnil, -, -⟩ := RepList.cons_of_load hAs ld12
      cases hnil
    · obtain ⟨z, zs, hnil, -, -⟩ := RepList.cons_of_load hAs ld12
      cases hnil
  | cons A As ih =>
    intro es xs r h h' cs hsz hAs hms hnc hbd ev
    rcases Obs.«KernelModeled::nested_scan_list».obs ev with
      ⟨ld12, he20, he21, hc22⟩ |
      ⟨x_e, x_rest, m41, cs52, ld12, ev54, he75, he76, hc77⟩ |
      ⟨x_e, x_rest, v40, m41, cs52, cs85, ld12, ev54, hne78, ev87, hc104⟩
    · have hnil := RepList.nil_of_load hAs ld12
      cases hnil
    · subst hc77
      obtain ⟨z, zs, hcons, hA, -⟩ := RepList.cons_of_load hAs ld12
      injection hcons with e1 e2
      subst e1 e2
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs52) (fun z hz => by simp [hz]) hnc hbd
      have a1 := (ihn (hsz _ (by simp)) hA hms n1 b1 ev54).weaken c1
      simp only [List.map_cons, List.foldr_cons]
      exact a1.orElse_one rfl he75
    · subst hc104
      obtain ⟨z, zs, hcons, hA, hrest⟩ := RepList.cons_of_load hAs ld12
      injection hcons with e1 e2
      subst e1 e2
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs52) (fun z hz => by simp [hz]) hnc hbd
      obtain ⟨n2, b2, c2⟩ := sub_good (cs' := cs85) (fun z hz => by simp [hz]) hnc hbd
      have ext := ev54.heap_extends
      have a1 := (ihn (hsz _ (by simp)) hA hms n1 b1 ev54).weaken c1
      have a2 := (ih (fun B hB => hsz B (List.mem_cons_of_mem _ hB))
        (hrest.mono treeAt_heapMono₂ ext) (se_addrs_mono ext hms) n2 b2 ev87).weaken c2
      simp only [List.map_cons, List.foldr_cons]
      exact a1.orElse_other hne78 a2

/-- **The answer at the head of a spine** (the `let`-bound match of `nested_scan`), given the
scan's specification at the head. -/
theorem nested_here_agrees {E : Ixon.Env} {ms : List Bytes.Address} {H : ScanTree}
    {As : List ScanTree} {w : Option Bool} {hd args e xs r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hH : TreeAt h hd H)
    (hAs : RepList kexprListEnum (fun h₀ X p₀ => TreeAt h₀ p₀ X) h As args)
    (hms : RepList addrListEnum RepAddr h ms xs)
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs)
    (ihH : ∀ {r' : SourceValue F} {h'' : Heap F} {cs' : List (Call F)},
      ¬ View.HashedCollision { env := E } [] cs' → Bounded cs' →
      ObsFn Obs.W "KernelModeled::nested_scan" [hd, xs] h r' h'' cs' →
      Agrees (L1.CanonicalHashCoverage E cs') w r')
    (sg : Obs.«KernelModeled::nested_scan».Seg1 hd args e xs h r h' cs) :
    Agrees (L1.CanonicalHashCoverage E cs)
        (hereOf (isIndAt E) (ms.map ixAddr) H (As.any fun A => A.mentions (ms.map ixAddr)) w)
        r ∧
      Heap.Extends h h' := by
  rcases sg with
    ⟨x_h, w86, m98, cs109, ld78, ev111, he132, he133, hc134⟩ |
    ⟨x_h, w86, v97, m98, cs109, m140, cs151, cs177, ld78, ev111, hne135, ev153, ev179, hc188⟩ |
    ⟨x_h, w86, v97, m98, cs109, v139, m140, cs151, ld78, ev111, hne135, ev153, hne189, he193,
      he194, hc195⟩ |
    ⟨v67, cs203, ld78, hne196, ev205, hc222⟩
  · -- a member at the head
    obtain ⟨a, rfl, ha⟩ := hH.const_inv ld78
    obtain ⟨hr1, hh1⟩ := se_addr_in_exact ha hms ev111
    have hm := bit_eq_one hr1.symm
    refine ⟨?_, by rw [he133]; exact ev111.heap_extends⟩
    show Agrees _ (hereConst (isIndAt E) (ixAddr a) (memB (ms.map ixAddr) (ixAddr a)) _) r
    rw [hm]
    exact Agrees.pure (by rw [he132, bit_false])
  · -- a constant outside the block with an argument that mentions a member
    subst hc188
    obtain ⟨a, rfl, ha⟩ := hH.const_inv ld78
    obtain ⟨hr1, hh1⟩ := se_addr_in_exact ha hms ev111
    subst hh1
    have hm := bit_ne_one (by rw [← hr1]; exact hne135)
    have c2 := nested_mentions_exact hAs hms ev153
    have hany := bit_eq_one c2.symm
    have ext2 := ev153.heap_extends
    obtain ⟨n3, b3, c3⟩ := sub_good (cs' := cs177) (fun z hz => by simp [hz]) hnc hbd
    have a3 := (addr_is_inductive_agrees n3 b3
      (Bytes.repAddressRef_heapMono₂ addrTy ext2 ha) ev179).weaken c3
    refine ⟨?_, ext2.trans ev179.heap_extends⟩
    show Agrees _ (hereConst (isIndAt E) (ixAddr a) (memB (ms.map ixAddr) (ixAddr a)) _) r
    rw [hm, hany]
    exact a3
  · -- a constant outside the block, no argument mentions a member
    obtain ⟨a, rfl, ha⟩ := hH.const_inv ld78
    obtain ⟨hr1, hh1⟩ := se_addr_in_exact ha hms ev111
    subst hh1
    have hm := bit_ne_one (by rw [← hr1]; exact hne135)
    have c2 := nested_mentions_exact hAs hms ev153
    have hany := bit_ne_one (by rw [← c2]; exact hne189)
    refine ⟨?_, by rw [he194]; exact ev153.heap_extends⟩
    show Agrees _ (hereConst (isIndAt E) (ixAddr a) (memB (ms.map ixAddr) (ixAddr a)) _) r
    rw [hm, hany]
    exact Agrees.pure (by rw [he193, bit_false])
  · -- another head: the scan on it
    subst hc222
    obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs203) (fun z hz => by simp [hz]) hnc hbd
    have hno := hH.not_const ld78 hne196
    refine ⟨?_, ev205.heap_extends⟩
    simp only [hereOf, hno]
    exact (ihH n1 b1 ev205).weaken c1

/-- **`nested_scan` against `nestedN`**, at every tree of at most `n` nodes. -/
theorem nested_scan_agrees {E : Ixon.Env} {ms : List Bytes.Address} :
    ∀ n : Nat, ScanSpec E ms n := by
  intro n
  induction n with
  | zero =>
    intro T e xs r h h' cs hn
    have := T.size_pos
    omega
  | succ n ih =>
    intro T e xs r h h' cs hn ht hms hnc hbd ev
    rcases Obs.«KernelModeled::nested_scan».obs ev with
      ⟨w20, w21, m33, cs43, x_head, x_args, m224, cs226, ld12, ev45, sg231, he246, he247,
        hc248⟩ |
      ⟨w20, w21, m33, cs43, x_head, x_args, v223, m224, cs226, cs256, ld12, ev45, sg231,
        hne249, ev258, hc275⟩ |
      ⟨x_t, x_b, w283, m300, cs311, ld12, ev313, he334, he335, hc336⟩ |
      ⟨x_t, x_b, w283, v299, m300, cs311, cs344, ld12, ev313, hne337, ev346, hc363⟩ |
      ⟨x_t, x_b, w371, m388, cs399, ld12, ev401, he422, he423, hc424⟩ |
      ⟨x_t, x_b, w371, v387, m388, cs399, cs432, ld12, ev401, hne425, ev434, hc451⟩ |
      ⟨x_t, x_v, x_b, m475, cs486, ld12, ev488, he509, he510, hc511⟩ |
      ⟨x_t, x_v, x_b, v474, m475, cs486, m517, cs528, ld12, ev488, hne512, ev530, he551, he552,
        hc553⟩ |
      ⟨x_t, x_v, x_b, v474, m475, cs486, v516, m517, cs528, cs561, ld12, ev488, hne512, ev530,
        hne554, ev563, hc580⟩ |
      ⟨w588, w589, x_x, cs608, ld12, ev610, hc627⟩ |
      ⟨v1, ld12, hne276, hne364, hne452, hne581, hne628, he632, he633, hc634⟩
    · -- an application whose head answers `1`
      subst hc248
      obtain ⟨Tf, Tx, rfl, hf, hx⟩ := ht.app_inv ld12
      obtain ⟨hd, sp, htup, hH, hAs⟩ := collect_spine_tree _ (Nat.le_refl _) ht ev45
      injection htup with hl
      injection hl with h1 hl
      injection hl with h2
      subst h1 h2
      have ext1 := ev45.heap_extends
      have hsH : (ScanTree.app Tf Tx).head.size ≤ n := by
        have h1 := ScanTree.head_size_le Tf
        simp only [ScanTree.head]
        simp only [ScanTree.size] at hn
        omega
      obtain ⟨n2, b2, c2⟩ := sub_good (cs' := cs226) (fun z hz => by simp [hz]) hnc hbd
      obtain ⟨aH, -⟩ := nested_here_agrees (E := E) (ms := ms) hH hAs (se_addrs_mono ext1 hms)
        n2 b2 (fun nc bd ev' => ih hsH hH (se_addrs_mono ext1 hms) nc bd ev') sg231
      simp only [nestedN]
      exact (aH.weaken c2).orElse_one rfl he246
    · -- an application whose head answers otherwise: the arguments
      subst hc275
      obtain ⟨Tf, Tx, rfl, hf, hx⟩ := ht.app_inv ld12
      obtain ⟨hd, sp, htup, hH, hAs⟩ := collect_spine_tree _ (Nat.le_refl _) ht ev45
      injection htup with hl
      injection hl with h1 hl
      injection hl with h2
      subst h1 h2
      have ext1 := ev45.heap_extends
      have hsH : (ScanTree.app Tf Tx).head.size ≤ n := by
        have h1 := ScanTree.head_size_le Tf
        simp only [ScanTree.head]
        simp only [ScanTree.size] at hn
        omega
      have hsA : ∀ A ∈ (ScanTree.app Tf Tx).args, A.size ≤ n := by
        intro A hA
        have h1 := ScanTree.args_size_lt _ A hA
        omega
      obtain ⟨n2, b2, c2⟩ := sub_good (cs' := cs226) (fun z hz => by simp [hz]) hnc hbd
      obtain ⟨n3, b3, c3⟩ := sub_good (cs' := cs256) (fun z hz => by simp [hz]) hnc hbd
      obtain ⟨aH, ext2⟩ := nested_here_agrees (E := E) (ms := ms) hH hAs
        (se_addrs_mono ext1 hms) n2 b2
        (fun nc bd ev' => ih hsH hH (se_addrs_mono ext1 hms) nc bd ev') sg231
      have aL := (nested_scan_list_agrees n ih hsA (hAs.mono treeAt_heapMono₂ ext2)
        (se_addrs_mono (ext1.trans ext2) hms) n3 b3 ev258).weaken c3
      simp only [nestedN]
      exact (aH.weaken c2).orElse_other hne249 aL
    · subst hc336
      obtain ⟨Tt, Tb, rfl, ht', hb'⟩ := ht.lam_inv ld12
      simp only [ScanTree.size] at hn
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs311) (fun z hz => by simp [hz]) hnc hbd
      have a1 := (ih (by omega) ht' hms n1 b1 ev313).weaken c1
      simp only [nestedN]
      exact a1.orElse_one rfl he334
    · subst hc363
      obtain ⟨Tt, Tb, rfl, ht', hb'⟩ := ht.lam_inv ld12
      simp only [ScanTree.size] at hn
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs311) (fun z hz => by simp [hz]) hnc hbd
      obtain ⟨n2, b2, c2⟩ := sub_good (cs' := cs344) (fun z hz => by simp [hz]) hnc hbd
      have ext := ev313.heap_extends
      have a1 := (ih (by omega) ht' hms n1 b1 ev313).weaken c1
      have a2 := (ih (by omega) (hb'.mono ext) (se_addrs_mono ext hms) n2 b2 ev346).weaken c2
      simp only [nestedN]
      exact a1.orElse_other hne337 a2
    · subst hc424
      obtain ⟨Tt, Tb, rfl, ht', hb'⟩ := ht.all_inv ld12
      simp only [ScanTree.size] at hn
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs399) (fun z hz => by simp [hz]) hnc hbd
      have a1 := (ih (by omega) ht' hms n1 b1 ev401).weaken c1
      simp only [nestedN]
      exact a1.orElse_one rfl he422
    · subst hc451
      obtain ⟨Tt, Tb, rfl, ht', hb'⟩ := ht.all_inv ld12
      simp only [ScanTree.size] at hn
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs399) (fun z hz => by simp [hz]) hnc hbd
      obtain ⟨n2, b2, c2⟩ := sub_good (cs' := cs432) (fun z hz => by simp [hz]) hnc hbd
      have ext := ev401.heap_extends
      have a1 := (ih (by omega) ht' hms n1 b1 ev401).weaken c1
      have a2 := (ih (by omega) (hb'.mono ext) (se_addrs_mono ext hms) n2 b2 ev434).weaken c2
      simp only [nestedN]
      exact a1.orElse_other hne425 a2
    · subst hc511
      obtain ⟨Tt, Tv, Tb, rfl, ht', hv', hb'⟩ := ht.let_inv ld12
      simp only [ScanTree.size] at hn
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs486) (fun z hz => by simp [hz]) hnc hbd
      have a1 := (ih (by omega) ht' hms n1 b1 ev488).weaken c1
      simp only [nestedN]
      exact a1.orElse_one rfl he509
    · subst hc553
      obtain ⟨Tt, Tv, Tb, rfl, ht', hv', hb'⟩ := ht.let_inv ld12
      simp only [ScanTree.size] at hn
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs486) (fun z hz => by simp [hz]) hnc hbd
      obtain ⟨n2, b2, c2⟩ := sub_good (cs' := cs528) (fun z hz => by simp [hz]) hnc hbd
      have ext := ev488.heap_extends
      have a1 := (ih (by omega) ht' hms n1 b1 ev488).weaken c1
      have a2 := (ih (by omega) (hv'.mono ext) (se_addrs_mono ext hms) n2 b2 ev530).weaken c2
      simp only [nestedN]
      exact a1.orElse_other hne512 (a2.orElse_one rfl he551)
    · subst hc580
      obtain ⟨Tt, Tv, Tb, rfl, ht', hv', hb'⟩ := ht.let_inv ld12
      simp only [ScanTree.size] at hn
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs486) (fun z hz => by simp [hz]) hnc hbd
      obtain ⟨n2, b2, c2⟩ := sub_good (cs' := cs528) (fun z hz => by simp [hz]) hnc hbd
      obtain ⟨n3, b3, c3⟩ := sub_good (cs' := cs561) (fun z hz => by simp [hz]) hnc hbd
      have ext1 := ev488.heap_extends
      have ext2 := ev530.heap_extends
      have a1 := (ih (by omega) ht' hms n1 b1 ev488).weaken c1
      have a2 := (ih (by omega) (hv'.mono ext1) (se_addrs_mono ext1 hms) n2 b2 ev530).weaken c2
      have a3 := (ih (by omega) (hb'.mono (ext1.trans ext2))
        (se_addrs_mono (ext1.trans ext2) hms) n3 b3 ev563).weaken c3
      simp only [nestedN]
      exact a1.orElse_other hne512 (a2.orElse_other hne554 a3)
    · subst hc627
      obtain ⟨Te, rfl, he'⟩ := ht.proj_inv ld12
      simp only [ScanTree.size] at hn
      obtain ⟨n1, b1, c1⟩ := sub_good (cs' := cs608) (fun z hz => by simp [hz]) hnc hbd
      simp only [nestedN]
      exact (ih (by omega) he' hms n1 b1 ev610).weaken c1
    · -- a leaf or a constant
      rcases ht.leaf_inv ld12 hne276 hne364 hne452 hne581 hne628 with rfl | ⟨a, ap, lp, rfl, -⟩
      · simp only [nestedN]
        exact Agrees.pure (by rw [he632, bit_false])
      · simp only [nestedN]
        exact Agrees.pure (by rw [he632, bit_false])

end

end IxVM.Refinement.Route
