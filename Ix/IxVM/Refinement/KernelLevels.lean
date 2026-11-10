import Ix.IxVM.Refinement.Mirrors.KernelLevels
import Ix.IxVM.Refinement.TagNWide
import Aiur.Library.IxVMRep
import IxC.Kernel.Level
import IxC.Kernel.Verify.Level

/-! # The KernelLevels slice: `RepKLevel` and universe level refinement

Track B, Phase 4 (`plans/ixvm-certification-gap.md`). On top of the generated
mirrors in `Ix.IxVM.Refinement.Mirrors.KernelLevels`, this module establishes:

* `RepKLevel` and `RepKLevelList`: the heap representation predicates connecting
  IxVM's `&KernelTypes::KLevelNode` pointers and `Lists::List<&KLevelNode>`
  spine lists on the Aiur heap to `Ix.Kernel.Level` and `List Ix.Kernel.Level`,
  together with heap monotonicity (`mono`, `HeapMono`, `HeapMono₂`),
  determinism (`det`), and the bridge to `Aiur.Library.RepIxVMKUniv`;
* `NLVar`, `NLEntry`, `RepNLVar`, `RepNLEntry`, and `RepNLEntries`: the heap
  representation predicates for IxVM's canonical normalizer entries
  (`KernelLevels::NLVar` and `KernelLevels::NLEntry`);
* Completeness (`*.Complete`), forward simulation (`*_run`), and `EvalFn`
  refinement (`*_refines`) theorems for:
  - structural and semantic queries (`level_eq`, `level_struct_eq`,
    `level_is_not_zero`, `level_offset_of`, `level_explicit_val`),
  - smart constructors and reduction (`level_max_offsets`,
    `level_max_subsumes`, `level_max_go`, `level_max`, `level_imax`,
    `level_reduce`),
  - parameter substitution `subst_level` (`level_inst_params`,
    `level_list_inst`, `Lists::drop`, `Lists::lookup`),
  - canonical universe normalization `norm` (`level_normalize`, `normalize_aux`,
    `normalize_imax_dispatch`, `nl_add_const`, `nl_add_var`,
    `nl_subsumption_walk`, `nl_skip_empty`),
  - universe comparison `is_geq_core` / `geqCore` (`level_leq`, `nl_le`,
    `nl_le_vars`, `nl_covers_const`, `nl_covers_var`, `nlvars_dominates`) and
    equivalence `is_eq_level` (`level_equal`, `nl_eq`). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace IxVM.Refinement.KernelLevels

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open Aiur.Library.List (RepList nodeEnumName)
open Aiur.Library.IxVMRep (IxVMKUniv RepIxVMKUniv repList_det)
open IxVM.Checked (F)
open IxVM.Refinement.TagN

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-! ## Enum names and heap cell loading helpers -/

/-- The runtime enum name of `KernelTypes::KLevelNode`. -/
abbrev klevelEnum : String := "KernelTypes::KLevelNode"

/-- The generic type `&KernelTypes::KLevelNode`. -/
abbrev klevelTy : Generic.Ty := .ptr (.named "KernelTypes::KLevelNode" [])

/-- The runtime enum name of `Lists::Node<&KernelTypes::KLevelNode>`. -/
abbrev klevelListEnum : String := nodeEnumName klevelTy

/-- The runtime enum name of `KernelLevels::NLVar`. -/
abbrev nlVarEnum : String := "KernelLevels::NLVar"

/-- The generic type `&KernelLevels::NLVar`. -/
abbrev nlVarTy : Generic.Ty := .ptr (.named "KernelLevels::NLVar" [])

/-- The runtime enum name of `Lists::Node<&KernelLevels::NLVar>`. -/
abbrev nlVarListEnum : String := nodeEnumName nlVarTy

/-- The runtime enum name of `KernelLevels::NLEntry`. -/
abbrev nlEntryEnum : String := "KernelLevels::NLEntry"

/-- The generic type `&KernelLevels::NLEntry`. -/
abbrev nlEntryTy : Generic.Ty := .ptr (.named "KernelLevels::NLEntry" [])

/-- The runtime enum name of `Lists::Node<&KernelLevels::NLEntry>`. -/
abbrev nlEntryListEnum : String := nodeEnumName nlEntryTy

/-- The runtime enum name of `Lists::Node<Field>` (guard parameter lists). -/
abbrev guardListEnum : String := byteStreamEnum

@[simp] theorem klevel_ctor :
    constructorName [] (.named "KernelTypes::KLevelNode" []) = klevelEnum := by
  decide +kernel

@[simp] theorem klevel_inst :
    instanceName [] "KernelTypes::KLevelNode" (some []) = klevelEnum := by
  decide +kernel

@[simp] theorem klevelList_ctor :
    constructorName [] (.named "Lists::Node" [klevelTy]) = klevelListEnum := by
  decide +kernel

@[simp] theorem klevelList_ctor_param :
    constructorName [("T", klevelTy)] (.named "Lists::Node" [.param "T"]) = klevelListEnum := by
  decide +kernel

@[simp] theorem klevelList_inst :
    instanceName [] "Lists::Node" (some [klevelTy]) = klevelListEnum := by
  decide +kernel

@[simp] theorem klevelList_inst_param :
    instanceName [("T", klevelTy)] "Lists::Node" (some [.param "T"]) = klevelListEnum := by
  decide +kernel

@[simp] theorem nlVar_ctor :
    constructorName [] (.named "KernelLevels::NLVar" []) = nlVarEnum := by
  decide +kernel

@[simp] theorem nlVar_inst :
    instanceName [] "KernelLevels::NLVar" (some []) = nlVarEnum := by
  decide +kernel

@[simp] theorem nlVarList_ctor :
    constructorName [] (.named "Lists::Node" [nlVarTy]) = nlVarListEnum := by
  decide +kernel

@[simp] theorem nlVarList_inst :
    instanceName [] "Lists::Node" (some [nlVarTy]) = nlVarListEnum := by
  decide +kernel

@[simp] theorem nlEntry_ctor :
    constructorName [] (.named "KernelLevels::NLEntry" []) = nlEntryEnum := by
  decide +kernel

@[simp] theorem nlEntry_inst :
    instanceName [] "KernelLevels::NLEntry" (some []) = nlEntryEnum := by
  decide +kernel

@[simp] theorem nlEntryList_ctor :
    constructorName [] (.named "Lists::Node" [nlEntryTy]) = nlEntryListEnum := by
  decide +kernel

@[simp] theorem nlEntryList_inst :
    instanceName [] "Lists::Node" (some [nlEntryTy]) = nlEntryListEnum := by
  decide +kernel

theorem loadValue_enum_cell {enumName : String} {heap : Heap F} {addr : Nat}
    {c : String} {xs : List (SourceValue F)}
    (cell : heap[addr]? = some (.construct enumName c xs)) :
    loadValue heap (.ptr (.enum enumName) addr) = .ok (.construct enumName c xs) := by
  simp [loadValue, cell, Value.type, bind, Except.bind, pure, Except.pure]

theorem natCast_lt_inj {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    (heq : (a : F) = (b : F)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at heq
  have hm : (4294967296 : Nat) ≤ Aiur.Library.U32.Goldilocks.modulus := by
    simp only [Aiur.Library.U32.Goldilocks.modulus]; omega
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq

theorem natCast_sub_eq_zero_iff {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    ((a : F) - (b : F) = 0) ↔ a = b := by
  rw [sub_eq_zero]
  exact ⟨natCast_lt_inj ha hb, fun h => h ▸ rfl⟩

/-! ## `RepKLevel`: Heap Representation of `Ix.Kernel.Level` -/

/-- Every universe parameter index in `l` is bounded by `bound`. -/
def ParamsLt (bound : Nat) : Ix.Kernel.Level → Prop
  | .zero => True
  | .succ u => ParamsLt bound u
  | .max u v => ParamsLt bound u ∧ ParamsLt bound v
  | .imax u v => ParamsLt bound u ∧ ParamsLt bound v
  | .param n => n < bound

/-- **Heap representation of `Ix.Kernel.Level` (`&KernelTypes::KLevelNode`)**.
Connects an `Ix.Kernel.Level` to a heap-allocated `KernelTypes::KLevelNode` tree
where every `.param n` index fits in a 32-bit unsigned integer (`n < 2^32`). -/
inductive RepKLevel (h : Heap F) : Ix.Kernel.Level → SourceValue F → Prop where
  | zero {addr : Nat}
      (cell : h[addr]? = some (.construct klevelEnum "Zero" [])) :
      RepKLevel h .zero (.ptr (.enum klevelEnum) addr)
  | succ {addr : Nat} {u : Ix.Kernel.Level} {uPtr : SourceValue F}
      (cell : h[addr]? = some (.construct klevelEnum "Succ" [uPtr]))
      (ih : RepKLevel h u uPtr) :
      RepKLevel h (.succ u) (.ptr (.enum klevelEnum) addr)
  | max {addr : Nat} {u v : Ix.Kernel.Level} {uPtr vPtr : SourceValue F}
      (cell : h[addr]? = some (.construct klevelEnum "Max" [uPtr, vPtr]))
      (ihu : RepKLevel h u uPtr)
      (ihv : RepKLevel h v vPtr) :
      RepKLevel h (.max u v) (.ptr (.enum klevelEnum) addr)
  | imax {addr : Nat} {u v : Ix.Kernel.Level} {uPtr vPtr : SourceValue F}
      (cell : h[addr]? = some (.construct klevelEnum "IMax" [uPtr, vPtr]))
      (ihu : RepKLevel h u uPtr)
      (ihv : RepKLevel h v vPtr) :
      RepKLevel h (.imax u v) (.ptr (.enum klevelEnum) addr)
  | param {addr : Nat} {n : Nat}
      (hn : n < 4294967296)
      (cell : h[addr]? = some (.construct klevelEnum "Param" [.field (n : F)])) :
      RepKLevel h (.param n) (.ptr (.enum klevelEnum) addr)

/-- **Monotonicity of `RepKLevel`** under `Heap.Extends`. -/
theorem RepKLevel.mono {h h' : Heap F} {l : Ix.Kernel.Level} {v : SourceValue F}
    (rep : RepKLevel h l v) (ext : Heap.Extends h h') : RepKLevel h' l v := by
  induction rep with
  | zero cell => exact .zero (ext.getElem?_eq cell)
  | succ cell _ ih => exact .succ (ext.getElem?_eq cell) ih
  | max cell _ _ ihu ihv => exact .max (ext.getElem?_eq cell) ihu ihv
  | imax cell _ _ ihu ihv => exact .imax (ext.getElem?_eq cell) ihu ihv
  | param hn cell => exact .param hn (ext.getElem?_eq cell)

theorem repKLevel_heapMono₂ : HeapMono₂ RepKLevel :=
  fun _ _ _ _ ext h => h.mono ext

theorem _root_.Aiur.Library.HeapMono.repKLevel (l : Ix.Kernel.Level) :
    HeapMono (fun h : Heap F => RepKLevel h l) :=
  fun _ _ _ ext h => h.mono ext

/-- **Every represented level has 32-bit parameter indices.** -/
theorem RepKLevel.paramsLt {h : Heap F} {l : Ix.Kernel.Level} {v : SourceValue F}
    (rep : RepKLevel h l v) : ParamsLt 4294967296 l := by
  induction rep with
  | zero _ => trivial
  | succ _ _ ih => exact ih
  | max _ _ _ ihu ihv => exact ⟨ihu, ihv⟩
  | imax _ _ _ ihu ihv => exact ⟨ihu, ihv⟩
  | param hn _ => exact hn

/-- **Every represented level pointer has type `.ptr (.enum klevelEnum) addr`.** -/
theorem RepKLevel.isPtr {h : Heap F} {l : Ix.Kernel.Level} {v : SourceValue F}
    (rep : RepKLevel h l v) : ∃ addr, v = .ptr (.enum klevelEnum) addr := by
  cases rep <;> exact ⟨_, rfl⟩

/-- **Determinism of `RepKLevel`**: a pointer in heap `h` represents at most
one `Ix.Kernel.Level`. -/
theorem RepKLevel.det {h : Heap F} {a b : Ix.Kernel.Level} {ptr : SourceValue F}
    (ha : RepKLevel h a ptr) (hb : RepKLevel h b ptr) : a = b := by
  induction ha generalizing b with
  | zero cellA =>
    cases hb <;> try rfl
    all_goals (rw [cellA] at *; injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide))
  | succ cellA _ ih =>
    cases hb <;> (rw [cellA] at *; clear cellA; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
    rename_i ihB cellB
    injection cellB with hnode
    injection hnode with _ _ hargs
    injection hargs with hu _
    subst hu
    exact congrArg Ix.Kernel.Level.succ (ih ihB)
  | max cellA _ _ ihu ihv =>
    cases hb <;> (rw [cellA] at *; clear cellA; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
    rename_i ihuB ihvB cellB
    injection cellB with hnode
    injection hnode with _ _ hargs
    injection hargs with hu hargs'
    injection hargs' with hv _
    subst hu; subst hv
    rw [ihu ihuB, ihv ihvB]
  | imax cellA _ _ ihu ihv =>
    cases hb <;> (rw [cellA] at *; clear cellA; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
    rename_i ihuB ihvB cellB
    injection cellB with hnode
    injection hnode with _ _ hargs
    injection hargs with hu hargs'
    injection hargs' with hv _
    subst hu; subst hv
    rw [ihu ihuB, ihv ihvB]
  | param hnA cellA =>
    cases hb <;> (rw [cellA] at *; clear cellA; try (injection ‹some _ = some _› with hC; injection hC with _ hCtor _; exact absurd hCtor (by decide)))
    rename_i hnB cellB
    injection cellB with hnode
    injection hnode with _ _ hargs
    injection hargs with hfield _
    injection hfield with heq
    exact congrArg Ix.Kernel.Level.param (natCast_lt_inj hnA hnB heq)

/-- Conversion from `Ix.Kernel.Level` to `Aiur.Library.IxVMRep.IxVMKUniv F`. -/
def levelToIxVMKUniv : Ix.Kernel.Level → IxVMKUniv F
  | .zero => .zero
  | .succ u => .succ (levelToIxVMKUniv u)
  | .max u v => .max (levelToIxVMKUniv u) (levelToIxVMKUniv v)
  | .imax u v => .imax (levelToIxVMKUniv u) (levelToIxVMKUniv v)
  | .param n => .param (n : F)

/-- **`RepKLevel` refines `Aiur.Library.IxVMRep.RepIxVMKUniv`.** -/
theorem RepKLevel.toRepIxVMKUniv {h : Heap F} {l : Ix.Kernel.Level} {ptr : SourceValue F}
    (rep : RepKLevel h l ptr) :
    RepIxVMKUniv h (levelToIxVMKUniv l) ptr := by
  induction rep with
  | zero cell => exact .zero cell
  | succ cell _ ih => exact .succ cell ih
  | max cell _ _ ihu ihv => exact .max cell ihu ihv
  | imax cell _ _ ihu ihv => exact .imax cell ihu ihv
  | param _ cell => exact .param cell

/-- **Heap representation of `List Ix.Kernel.Level`** (`Lists::List<&KLevelNode>`). -/
abbrev RepKLevelList (h : Heap F) : List Ix.Kernel.Level → SourceValue F → Prop :=
  RepList klevelListEnum RepKLevel h

theorem RepKLevelList.mono {h h' : Heap F} {ls : List Ix.Kernel.Level} {ptr : SourceValue F}
    (rep : RepKLevelList h ls ptr) (ext : Heap.Extends h h') :
    RepKLevelList h' ls ptr :=
  RepLinkedList.mono repKLevel_heapMono₂ ext rep

theorem RepKLevelList.det {h : Heap F} {as bs : List Ix.Kernel.Level} {ptr : SourceValue F}
    (ha : RepKLevelList h as ptr) (hb : RepKLevelList h bs ptr) : as = bs :=
  repList_det (fun ra rb => ra.det rb) ha hb

/-! ## Heap Allocation Helpers for `RepKLevel` -/

theorem RepKLevel.allocZero (h : Heap F) :
    let node : SourceValue F := .construct klevelEnum "Zero" []
    let ptr : SourceValue F := .ptr (.enum klevelEnum) h.length
    let h' : Heap F := h ++ [node]
    RepKLevel h' .zero ptr ∧ Heap.Extends h h' := by
  refine ⟨.zero (by simp), Heap.Extends.snoc h _⟩

theorem RepKLevel.allocSucc {h : Heap F} {u : Ix.Kernel.Level} {uPtr : SourceValue F}
    (repU : RepKLevel h u uPtr) :
    let node : SourceValue F := .construct klevelEnum "Succ" [uPtr]
    let ptr : SourceValue F := .ptr (.enum klevelEnum) h.length
    let h' : Heap F := h ++ [node]
    RepKLevel h' (.succ u) ptr ∧ Heap.Extends h h' := by
  have ext := Heap.Extends.snoc h (.construct klevelEnum "Succ" [uPtr])
  exact ⟨.succ (by simp) (repU.mono ext), ext⟩

theorem RepKLevel.allocMax {h : Heap F} {u v : Ix.Kernel.Level} {uPtr vPtr : SourceValue F}
    (repU : RepKLevel h u uPtr) (repV : RepKLevel h v vPtr) :
    let node : SourceValue F := .construct klevelEnum "Max" [uPtr, vPtr]
    let ptr : SourceValue F := .ptr (.enum klevelEnum) h.length
    let h' : Heap F := h ++ [node]
    RepKLevel h' (.max u v) ptr ∧ Heap.Extends h h' := by
  have ext := Heap.Extends.snoc h (.construct klevelEnum "Max" [uPtr, vPtr])
  exact ⟨.max (by simp) (repU.mono ext) (repV.mono ext), ext⟩

theorem RepKLevel.allocIMax {h : Heap F} {u v : Ix.Kernel.Level} {uPtr vPtr : SourceValue F}
    (repU : RepKLevel h u uPtr) (repV : RepKLevel h v vPtr) :
    let node : SourceValue F := .construct klevelEnum "IMax" [uPtr, vPtr]
    let ptr : SourceValue F := .ptr (.enum klevelEnum) h.length
    let h' : Heap F := h ++ [node]
    RepKLevel h' (.imax u v) ptr ∧ Heap.Extends h h' := by
  have ext := Heap.Extends.snoc h (.construct klevelEnum "IMax" [uPtr, vPtr])
  exact ⟨.imax (by simp) (repU.mono ext) (repV.mono ext), ext⟩

theorem RepKLevel.allocParam (h : Heap F) {n : Nat} (hn : n < 4294967296) :
    let node : SourceValue F := .construct klevelEnum "Param" [.field (n : F)]
    let ptr : SourceValue F := .ptr (.enum klevelEnum) h.length
    let h' : Heap F := h ++ [node]
    RepKLevel h' (.param n) ptr ∧ Heap.Extends h h' := by
  refine ⟨.param hn (by simp), Heap.Extends.snoc h _⟩

theorem RepKLevelList.allocNil (h : Heap F) :
    let node : SourceValue F := .construct klevelListEnum "Nil" []
    let ptr : SourceValue F := .ptr (.enum klevelListEnum) h.length
    let h' : Heap F := h ++ [node]
    RepKLevelList h' [] ptr ∧ Heap.Extends h h' := by
  refine ⟨.nil (by simp), Heap.Extends.snoc h _⟩

theorem RepKLevelList.allocCons {h : Heap F} {x : Ix.Kernel.Level} {xs : List Ix.Kernel.Level}
    {xPtr xsPtr : SourceValue F} (repX : RepKLevel h x xPtr) (repXs : RepKLevelList h xs xsPtr) :
    let node : SourceValue F := .construct klevelListEnum "Cons" [xPtr, xsPtr]
    let ptr : SourceValue F := .ptr (.enum klevelListEnum) h.length
    let h' : Heap F := h ++ [node]
    RepKLevelList h' (x :: xs) ptr ∧ Heap.Extends h h' := by
  have ext := Heap.Extends.snoc h (.construct klevelListEnum "Cons" [xPtr, xsPtr])
  exact ⟨.cons (by simp) (repX.mono ext) (repXs.mono ext), ext⟩

/-! ## `NLVar` and `NLEntry`: Normalizer Data Types and Heap Representation -/

/-- A variable-plus-offset pair `(u_param + offset)` in a normalized level entry. -/
structure NLVar where
  param : Nat
  offset : Nat
  deriving DecidableEq, Repr, Inhabited

abbrev NLVar.idx (v : NLVar) : Nat := v.param

@[simp] theorem NLVar.idx_mk (p o : Nat) : (NLVar.mk p o).param = p := rfl

/-- A guarded normal-form entry: active when all `p ∈ guards` have `φ p > 0`,
evaluating to `max constPart (max_{(p, k) ∈ vars} (φ p + k))`. -/
structure NLEntry where
  guards : List Nat
  constPart : Nat
  vars : List NLVar
  deriving DecidableEq, Repr, Inhabited

/-- Heap representation of a 32-bit guard parameter index (`Field`). -/
def RepGuard (_ : Heap F) (g : Nat) (v : SourceValue F) : Prop :=
  g < 4294967296 ∧ v = .field (g : F)

theorem repGuard_heapMono₂ : HeapMono₂ RepGuard :=
  fun _ _ _ _ _ h => h

theorem RepGuard.det {h : Heap F} {a b : Nat} {v : SourceValue F}
    (ha : RepGuard h a v) (hb : RepGuard h b v) : a = b := by
  rcases ha with ⟨hna, rfl⟩
  rcases hb with ⟨hnb, heq⟩
  injection heq with hfield
  exact natCast_lt_inj hna hnb hfield

/-- Heap representation of a guard parameter list (`Lists::List<Field>`). -/
abbrev RepGuardList (h : Heap F) : List Nat → SourceValue F → Prop :=
  RepList guardListEnum RepGuard h

theorem RepGuardList.mono {h h' : Heap F} {gs : List Nat} {ptr : SourceValue F}
    (rep : RepGuardList h gs ptr) (ext : Heap.Extends h h') : RepGuardList h' gs ptr :=
  RepLinkedList.mono repGuard_heapMono₂ ext rep

theorem RepGuardList.det {h : Heap F} {as bs : List Nat} {ptr : SourceValue F}
    (ha : RepGuardList h as ptr) (hb : RepGuardList h bs ptr) : as = bs :=
  repList_det (fun ra rb => ra.det rb) ha hb

theorem RepGuardList.allocNil (h : Heap F) :
    let node : SourceValue F := .construct guardListEnum "Nil" []
    let ptr : SourceValue F := .ptr (.enum guardListEnum) h.length
    let h' : Heap F := h ++ [node]
    RepGuardList h' [] ptr ∧ Heap.Extends h h' := by
  refine ⟨.nil (by simp), Heap.Extends.snoc h _⟩

theorem RepGuardList.allocCons {h : Heap F} {g : Nat} {gs : List Nat}
    {gsPtr : SourceValue F} (hg : g < 4294967296) (repGs : RepGuardList h gs gsPtr) :
    let node : SourceValue F := .construct guardListEnum "Cons" [.field (g : F), gsPtr]
    let ptr : SourceValue F := .ptr (.enum guardListEnum) h.length
    let h' : Heap F := h ++ [node]
    RepGuardList h' (g :: gs) ptr ∧ Heap.Extends h h' := by
  have ext := Heap.Extends.snoc h (.construct guardListEnum "Cons" [.field (g : F), gsPtr])
  exact ⟨.cons (by simp) ⟨hg, rfl⟩ (repGs.mono ext), ext⟩

/-- Heap representation of `KernelLevels::NLVar` (`&NLVar`). -/
inductive RepNLVar (h : Heap F) : NLVar → SourceValue F → Prop where
  | mk {addr : Nat} {v : NLVar}
      (hparam : v.param < 4294967296)
      (hoff : v.offset < 4294967296)
      (cell : h[addr]? = some (.construct nlVarEnum "Mk" [.field (v.param : F), .field (v.offset : F)])) :
      RepNLVar h v (.ptr (.enum nlVarEnum) addr)

theorem RepNLVar.mono {h h' : Heap F} {v : NLVar} {ptr : SourceValue F}
    (rep : RepNLVar h v ptr) (ext : Heap.Extends h h') : RepNLVar h' v ptr := by
  cases rep with
  | mk hp ho cell => exact .mk hp ho (ext.getElem?_eq cell)

theorem repNLVar_heapMono₂ : HeapMono₂ RepNLVar :=
  fun _ _ _ _ ext h => h.mono ext

theorem RepNLVar.det {h : Heap F} {a b : NLVar} {ptr : SourceValue F}
    (ha : RepNLVar h a ptr) (hb : RepNLVar h b ptr) : a = b := by
  cases ha with
  | mk hpa hoa cellA =>
    cases hb with
    | mk hpb hob cellB =>
      rw [cellA] at cellB
      injection cellB with hnode
      injection hnode with _ _ hargs
      injection hargs with hp hargs'
      injection hargs' with ho _
      injection hp with hp'
      injection ho with ho'
      cases a; cases b
      simp only [NLVar.mk.injEq] at *
      exact ⟨natCast_lt_inj hpa hpb hp', natCast_lt_inj hoa hob ho'⟩

theorem RepNLVar.alloc {p o : Nat} (hp : p < 4294967296) (ho : o < 4294967296) (h : Heap F) :
    let node : SourceValue F := .construct nlVarEnum "Mk" [.field (p : F), .field (o : F)]
    let ptr : SourceValue F := .ptr (.enum nlVarEnum) h.length
    let h' : Heap F := h ++ [node]
    RepNLVar h' ⟨p, o⟩ ptr ∧ Heap.Extends h h' := by
  refine ⟨.mk (v := ⟨p, o⟩) hp ho (by simp), Heap.Extends.snoc h _⟩

/-- Heap representation of `Lists::List<&KernelLevels::NLVar>`. -/
abbrev RepNLVarList (h : Heap F) : List NLVar → SourceValue F → Prop :=
  RepList nlVarListEnum RepNLVar h

theorem RepNLVarList.mono {h h' : Heap F} {vs : List NLVar} {ptr : SourceValue F}
    (rep : RepNLVarList h vs ptr) (ext : Heap.Extends h h') : RepNLVarList h' vs ptr :=
  RepLinkedList.mono repNLVar_heapMono₂ ext rep

theorem RepNLVarList.det {h : Heap F} {as bs : List NLVar} {ptr : SourceValue F}
    (ha : RepNLVarList h as ptr) (hb : RepNLVarList h bs ptr) : as = bs :=
  repList_det (fun ra rb => ra.det rb) ha hb

theorem RepNLVarList.allocNil (h : Heap F) :
    let node : SourceValue F := .construct nlVarListEnum "Nil" []
    let ptr : SourceValue F := .ptr (.enum nlVarListEnum) h.length
    let h' : Heap F := h ++ [node]
    RepNLVarList h' [] ptr ∧ Heap.Extends h h' := by
  refine ⟨.nil (by simp), Heap.Extends.snoc h _⟩

theorem RepNLVarList.allocCons {h : Heap F} {v : NLVar} {vs : List NLVar}
    {vPtr vsPtr : SourceValue F} (repV : RepNLVar h v vPtr) (repVs : RepNLVarList h vs vsPtr) :
    let node : SourceValue F := .construct nlVarListEnum "Cons" [vPtr, vsPtr]
    let ptr : SourceValue F := .ptr (.enum nlVarListEnum) h.length
    let h' : Heap F := h ++ [node]
    RepNLVarList h' (v :: vs) ptr ∧ Heap.Extends h h' := by
  have ext := Heap.Extends.snoc h (.construct nlVarListEnum "Cons" [vPtr, vsPtr])
  exact ⟨.cons (by simp) (repV.mono ext) (repVs.mono ext), ext⟩

/-- Heap representation of `KernelLevels::NLEntry` (`&NLEntry`). -/
inductive RepNLEntry (h : Heap F) : NLEntry → SourceValue F → Prop where
  | mk {addr : Nat} {e : NLEntry} {gPtr vPtr : SourceValue F}
      (hconst : e.constPart < 4294967296)
      (cell : h[addr]? = some (.construct nlEntryEnum "Mk" [gPtr, .field (e.constPart : F), vPtr]))
      (repG : RepGuardList h e.guards gPtr)
      (repV : RepNLVarList h e.vars vPtr) :
      RepNLEntry h e (.ptr (.enum nlEntryEnum) addr)

theorem RepNLEntry.mono {h h' : Heap F} {e : NLEntry} {ptr : SourceValue F}
    (rep : RepNLEntry h e ptr) (ext : Heap.Extends h h') : RepNLEntry h' e ptr := by
  cases rep with
  | mk hc cell repG repV =>
    exact .mk hc (ext.getElem?_eq cell) (repG.mono ext) (repV.mono ext)

theorem repNLEntry_heapMono₂ : HeapMono₂ RepNLEntry :=
  fun _ _ _ _ ext h => h.mono ext

theorem RepNLEntry.det {h : Heap F} {a b : NLEntry} {ptr : SourceValue F}
    (ha : RepNLEntry h a ptr) (hb : RepNLEntry h b ptr) : a = b := by
  cases ha with
  | mk hca cellA repGA repVA =>
    cases hb with
    | mk hcb cellB repGB repVB =>
      rw [cellA] at cellB
      injection cellB with hnode
      injection hnode with _ _ hargs
      injection hargs with hg hargs'
      injection hargs' with hc hargs''
      injection hargs'' with hv _
      injection hc with hc'
      subst hg; subst hv
      have hguards := repGA.det repGB
      have hvars := repVA.det repVB
      have hconst := natCast_lt_inj hca hcb hc'
      cases a; cases b
      simp only [NLEntry.mk.injEq] at *
      exact ⟨hguards, hconst, hvars⟩

theorem RepNLEntry.alloc {h : Heap F} {e : NLEntry} {gPtr vPtr : SourceValue F}
    (hc : e.constPart < 4294967296) (repG : RepGuardList h e.guards gPtr)
    (repV : RepNLVarList h e.vars vPtr) :
    let node : SourceValue F := .construct nlEntryEnum "Mk" [gPtr, .field (e.constPart : F), vPtr]
    let ptr : SourceValue F := .ptr (.enum nlEntryEnum) h.length
    let h' : Heap F := h ++ [node]
    RepNLEntry h' e ptr ∧ Heap.Extends h h' := by
  have ext := Heap.Extends.snoc h (.construct nlEntryEnum "Mk" [gPtr, .field (e.constPart : F), vPtr])
  exact ⟨.mk hc (by simp) (repG.mono ext) (repV.mono ext), ext⟩

/-- Heap representation of `Lists::List<&KernelLevels::NLEntry>`. -/
abbrev RepNLEntries (h : Heap F) : List NLEntry → SourceValue F → Prop :=
  RepList nlEntryListEnum RepNLEntry h

theorem RepNLEntries.mono {h h' : Heap F} {es : List NLEntry} {ptr : SourceValue F}
    (rep : RepNLEntries h es ptr) (ext : Heap.Extends h h') : RepNLEntries h' es ptr :=
  RepLinkedList.mono repNLEntry_heapMono₂ ext rep

theorem RepNLEntries.det {h : Heap F} {as bs : List NLEntry} {ptr : SourceValue F}
    (ha : RepNLEntries h as ptr) (hb : RepNLEntries h bs ptr) : as = bs :=
  repList_det (fun ra rb => ra.det rb) ha hb

theorem RepNLEntries.allocNil (h : Heap F) :
    let node : SourceValue F := .construct nlEntryListEnum "Nil" []
    let ptr : SourceValue F := .ptr (.enum nlEntryListEnum) h.length
    let h' : Heap F := h ++ [node]
    RepNLEntries h' [] ptr ∧ Heap.Extends h h' := by
  refine ⟨.nil (by simp), Heap.Extends.snoc h _⟩

theorem RepNLEntries.allocCons {h : Heap F} {e : NLEntry} {es : List NLEntry}
    {ePtr esPtr : SourceValue F} (repE : RepNLEntry h e ePtr) (repEs : RepNLEntries h es esPtr) :
    let node : SourceValue F := .construct nlEntryListEnum "Cons" [ePtr, esPtr]
    let ptr : SourceValue F := .ptr (.enum nlEntryListEnum) h.length
    let h' : Heap F := h ++ [node]
    RepNLEntries h' (e :: es) ptr ∧ Heap.Extends h h' := by
  have ext := Heap.Extends.snoc h (.construct nlEntryListEnum "Cons" [ePtr, esPtr])
  exact ⟨.cons (by simp) (repE.mono ext) (repEs.mono ext), ext⟩

theorem RepKLevel.mono' {h h' : Heap F} {l : Ix.Kernel.Level} {v : SourceValue F}
    (rep : RepKLevel h l v) (ext : Heap.Extends h h') : RepKLevel h' l v :=
  rep.mono ext

theorem RepNLVar.mono' {h h' : Heap F} {v : NLVar} {ptr : SourceValue F}
    (rep : RepNLVar h v ptr) (ext : Heap.Extends h h') : RepNLVar h' v ptr :=
  rep.mono ext

theorem RepNLEntry.mono' {h h' : Heap F} {e : NLEntry} {ptr : SourceValue F}
    (rep : RepNLEntry h e ptr) (ext : Heap.Extends h h') : RepNLEntry h' e ptr :=
  rep.mono ext

theorem _root_.Aiur.RepLinkedList.mono' {enumName nilCtor consCtor : String}
    {α : Type} {R : Heap F → α → SourceValue F → Prop}
    {h h' : Heap F} {xs : List α} {ptr : SourceValue F}
    (rep : RepLinkedList enumName nilCtor consCtor R h xs ptr)
    (ext : Heap.Extends h h')
    (hR : HeapMono₂ R := by first
      | exact repKLevel_heapMono₂
      | exact repGuard_heapMono₂
      | exact repNLVar_heapMono₂
      | exact repNLEntry_heapMono₂) :
    RepLinkedList enumName nilCtor consCtor R h' xs ptr :=
  RepLinkedList.mono hR ext rep

/-! ## Pure Mathematical Models & Semantic Equivalence to `Ix.Kernel.Level` -/

/-- Structural depth (height) of a `Level`, bounding all successor offsets. -/
def levelDepth : Ix.Kernel.Level → Nat
  | .zero => 0
  | .succ u => levelDepth u + 1
  | .max u v => Max.max (levelDepth u) (levelDepth v) + 1
  | .imax u v => Max.max (levelDepth u) (levelDepth v) + 1
  | .param _ => 0

/-- Pure specification of `KernelLevels::level_offset_of`: peels outer `.succ`
constructors into `(base, offset)`. -/
def levelOffsetOf : Ix.Kernel.Level → Ix.Kernel.Level × Nat
  | .succ inner =>
    let (base, k) := levelOffsetOf inner
    (base, k + 1)
  | l => (l, 0)

/-- Accumulator version of `levelOffsetOf` matching `KernelLevels::level_offset_of`. -/
def levelOffsetOfAcc : Ix.Kernel.Level → Nat → Ix.Kernel.Level × Nat
  | .succ inner, acc => levelOffsetOfAcc inner (acc + 1)
  | l, acc => (l, acc)

theorem levelOffsetOfAcc_eq (l : Ix.Kernel.Level) (acc : Nat) :
    levelOffsetOfAcc l acc = ((levelOffsetOf l).1, acc + (levelOffsetOf l).2) := by
  induction l generalizing acc with
  | succ inner ih =>
    simp only [levelOffsetOfAcc, levelOffsetOf, ih (acc + 1), Prod.mk.injEq, true_and]
    omega
  | _ => simp [levelOffsetOfAcc, levelOffsetOf]

theorem eval_levelOffsetOf (φ : Ix.Kernel.LevelParam → Nat) (l : Ix.Kernel.Level) :
    Ix.Kernel.Level.eval φ (levelOffsetOf l).1 + (levelOffsetOf l).2 = Ix.Kernel.Level.eval φ l := by
  induction l with
  | succ inner ih =>
    simp only [levelOffsetOf, Ix.Kernel.Level.eval]
    omega
  | _ => simp [levelOffsetOf, Ix.Kernel.Level.eval]

theorem levelOffsetOf_le_depth (l : Ix.Kernel.Level) :
    (levelOffsetOf l).2 ≤ levelDepth l := by
  induction l with
  | succ inner ih =>
    simp only [levelOffsetOf, levelDepth]
    omega
  | _ => simp [levelOffsetOf]

/-- Pure specification of `KernelLevels::level_explicit_val`: returns `some n`
when `l` is a pure numeral `.succ^n .zero`, and `none` otherwise. -/
def levelExplicitVal : Ix.Kernel.Level → Option Nat
  | .zero => some 0
  | .succ inner => (levelExplicitVal inner).map (· + 1)
  | _ => none

theorem eval_of_levelExplicitVal {l : Ix.Kernel.Level} {n : Nat}
    (h : levelExplicitVal l = some n) (φ : Ix.Kernel.LevelParam → Nat) :
    Ix.Kernel.Level.eval φ l = n := by
  induction l generalizing n with
  | zero =>
    simp only [levelExplicitVal, Option.some.injEq] at h
    subst h
    rfl
  | succ inner ih =>
    simp only [levelExplicitVal, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    simp [Ix.Kernel.Level.eval, ih hm]
  | max _ _ | imax _ _ | param _ =>
    simp [levelExplicitVal] at h

theorem levelExplicitVal_le_depth {l : Ix.Kernel.Level} {n : Nat}
    (h : levelExplicitVal l = some n) : n = levelDepth l := by
  induction l generalizing n with
  | zero =>
    simp only [levelExplicitVal, Option.some.injEq] at h
    subst h
    rfl
  | succ inner ih =>
    simp only [levelExplicitVal, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    simp [levelDepth, ih hm]
  | max _ _ | imax _ _ | param _ =>
    simp [levelExplicitVal] at h

/-- Pure specification of `KernelLevels::level_max_offsets`. -/
def levelMaxOffsets (a b : Ix.Kernel.Level) : Ix.Kernel.Level :=
  let (baseA, offA) := levelOffsetOf a
  let (baseB, offB) := levelOffsetOf b
  if baseA = baseB then
    if offA < offB then b else a
  else
    .max a b

theorem eval_levelMaxOffsets (φ : Ix.Kernel.LevelParam → Nat) (a b : Ix.Kernel.Level) :
    Ix.Kernel.Level.eval φ (levelMaxOffsets a b) =
      Max.max (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b) := by
  unfold levelMaxOffsets
  have ha := eval_levelOffsetOf φ a
  have hb := eval_levelOffsetOf φ b
  dsimp only
  split
  · rename_i heq
    rw [heq] at ha
    split <;> omega
  · rfl

/-- Pure specification of `KernelLevels::level_max_subsumes`. -/
def levelMaxSubsumes (m x : Ix.Kernel.Level) : Bool :=
  match m with
  | .max l r => if l = x then true else decide (r = x)
  | _ => false

theorem eval_of_levelMaxSubsumes {m x : Ix.Kernel.Level}
    (h : levelMaxSubsumes m x = true) (φ : Ix.Kernel.LevelParam → Nat) :
    Ix.Kernel.Level.eval φ x ≤ Ix.Kernel.Level.eval φ m := by
  cases m with
  | max l r =>
    simp only [levelMaxSubsumes] at h
    split at h
    · rename_i hl; subst hl; simp [Ix.Kernel.Level.eval]
    · simp only [decide_eq_true_eq] at h; subst h; simp [Ix.Kernel.Level.eval]
  | _ => simp [levelMaxSubsumes] at h

/-- Pure specification of `KernelLevels::level_max_go`. -/
def levelMaxGo (a b : Ix.Kernel.Level) : Ix.Kernel.Level :=
  if a = b then a
  else match a with
    | .zero => b
    | _ => match b with
      | .zero => a
      | _ =>
        if levelMaxSubsumes b a then b
        else if levelMaxSubsumes a b then a
        else levelMaxOffsets a b

theorem eval_levelMaxGo (φ : Ix.Kernel.LevelParam → Nat) (a b : Ix.Kernel.Level) :
    Ix.Kernel.Level.eval φ (levelMaxGo a b) =
      Max.max (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b) := by
  unfold levelMaxGo
  by_cases hab : a = b
  · subst hab; simp
  · simp only [hab, ↓reduceIte]
    have hRest :
        Ix.Kernel.Level.eval φ
          (if levelMaxSubsumes b a then b
           else if levelMaxSubsumes a b then a
           else levelMaxOffsets a b) =
        Max.max (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b) := by
      by_cases hsub1 : levelMaxSubsumes b a = true
      · have hle := eval_of_levelMaxSubsumes hsub1 φ
        simp only [hsub1, ↓reduceIte]; omega
      · simp only [Bool.not_eq_true] at hsub1
        simp only [hsub1, Bool.false_eq_true, ↓reduceIte]
        by_cases hsub2 : levelMaxSubsumes a b = true
        · have hle := eval_of_levelMaxSubsumes hsub2 φ
          simp only [hsub2, ↓reduceIte]; omega
        · simp only [Bool.not_eq_true] at hsub2
          simp only [hsub2, Bool.false_eq_true, ↓reduceIte, eval_levelMaxOffsets]
    cases a <;> cases b <;> first | (simp [Ix.Kernel.Level.eval]; done) | exact hRest

/-- Pure specification of `KernelLevels::level_max`. -/
def levelMax (a b : Ix.Kernel.Level) : Ix.Kernel.Level :=
  match levelExplicitVal a, levelExplicitVal b with
  | some na, some nb => if na < nb then b else a
  | _, _ => levelMaxGo a b

theorem eval_levelMax (φ : Ix.Kernel.LevelParam → Nat) (a b : Ix.Kernel.Level) :
    Ix.Kernel.Level.eval φ (levelMax a b) =
      Max.max (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b) := by
  unfold levelMax
  cases ha : levelExplicitVal a with
  | none => exact eval_levelMaxGo φ a b
  | some na =>
    cases hb : levelExplicitVal b with
    | none => exact eval_levelMaxGo φ a b
    | some nb =>
      have ea := eval_of_levelExplicitVal ha φ
      have eb := eval_of_levelExplicitVal hb φ
      dsimp only
      split <;> omega

/-- Soundness of `Ix.Kernel.Level.isNeverZero` (`KernelLevels::level_is_not_zero`). -/
theorem isNeverZero_eval_ne_zero {l : Ix.Kernel.Level} (h : l.isNeverZero = true)
    (φ : Ix.Kernel.LevelParam → Nat) : Ix.Kernel.Level.eval φ l ≠ 0 := by
  induction l with
  | zero => simp [Ix.Kernel.Level.isNeverZero] at h
  | succ u => simp [Ix.Kernel.Level.eval]
  | max u v ihu ihv =>
    simp only [Ix.Kernel.Level.isNeverZero, Bool.or_eq_true] at h
    simp only [Ix.Kernel.Level.eval]
    rcases h with hu | hv
    · have := ihu hu; omega
    · have := ihv hv; omega
  | imax u v _ ihv =>
    simp only [Ix.Kernel.Level.isNeverZero] at h
    have hv := ihv h
    simp only [Ix.Kernel.Level.eval, hv, ↓reduceIte]
    omega
  | param _ => simp [Ix.Kernel.Level.isNeverZero] at h

/-- Pure specification of `KernelLevels::level_imax`. -/
def levelIMax (a b : Ix.Kernel.Level) : Ix.Kernel.Level :=
  match b with
  | .zero => .zero
  | .succ _ => levelMax a b
  | _ =>
    if b.isNeverZero then levelMax a b
    else match a with
      | .zero => b
      | _ => if a = b then a else .imax a b

theorem eval_levelIMax (φ : Ix.Kernel.LevelParam → Nat) (a b : Ix.Kernel.Level) :
    Ix.Kernel.Level.eval φ (levelIMax a b) = Ix.Kernel.Level.eval φ (.imax a b) := by
  have hElse :
      Ix.Kernel.Level.eval φ
        (match a with | .zero => b | _ => if a = b then a else .imax a b) =
      Ix.Kernel.Level.eval φ (.imax a b) := by
    have hIf :
        Ix.Kernel.Level.eval φ (if a = b then a else .imax a b) =
        Ix.Kernel.Level.eval φ (.imax a b) := by
      by_cases heq : a = b
      · subst heq; simp [Ix.Kernel.Level.eval]
      · simp [heq]
    cases a with
    | zero => simp only [Ix.Kernel.Level.eval]; split_ifs <;> omega
    | succ _ | max _ _ | imax _ _ | param _ => exact hIf
  unfold levelIMax
  cases b with
  | zero => simp [Ix.Kernel.Level.eval]
  | succ u =>
    simp [Ix.Kernel.Level.eval, eval_levelMax]
  | max u v =>
    dsimp only
    by_cases hnz : (Ix.Kernel.Level.max u v).isNeverZero = true
    · have hne := isNeverZero_eval_ne_zero hnz φ
      simp only [Ix.Kernel.Level.eval] at hne
      simp [hnz, eval_levelMax, Ix.Kernel.Level.eval, hne]
    · simp only [Bool.not_eq_true] at hnz
      simp only [hnz, Bool.false_eq_true, ↓reduceIte]
      exact hElse
  | imax u v =>
    dsimp only
    by_cases hnz : (Ix.Kernel.Level.imax u v).isNeverZero = true
    · have hne := isNeverZero_eval_ne_zero hnz φ
      simp only [Ix.Kernel.Level.eval] at hne
      simp [hnz, eval_levelMax, Ix.Kernel.Level.eval, hne]
    · simp only [Bool.not_eq_true] at hnz
      simp only [hnz, Bool.false_eq_true, ↓reduceIte]
      exact hElse
  | param n =>
    dsimp only
    have hnz : (Ix.Kernel.Level.param n).isNeverZero = false := rfl
    simp only [hnz, Bool.false_eq_true, ↓reduceIte]
    exact hElse

/-- Pure specification of `KernelLevels::level_reduce`. -/
def levelReduce : Ix.Kernel.Level → Ix.Kernel.Level
  | .zero => .zero
  | .succ x => .succ (levelReduce x)
  | .max a b => levelMax (levelReduce a) (levelReduce b)
  | .imax a b => levelIMax (levelReduce a) (levelReduce b)
  | .param i => .param i

/-- **`levelReduce` preserves universe evaluation under every assignment.** -/
theorem eval_levelReduce (φ : Ix.Kernel.LevelParam → Nat) (l : Ix.Kernel.Level) :
    Ix.Kernel.Level.eval φ (levelReduce l) = Ix.Kernel.Level.eval φ l := by
  induction l with
  | zero => rfl
  | succ x ih => simp [levelReduce, Ix.Kernel.Level.eval, ih]
  | max a b iha ihb => simp [levelReduce, eval_levelMax, Ix.Kernel.Level.eval, iha, ihb]
  | imax a b iha ihb => simp [levelReduce, eval_levelIMax, Ix.Kernel.Level.eval, iha, ihb]
  | param _ => rfl

/-! ## Parameter Substitution (`subst_level` / `level_inst_params`) -/

/-- Pure partial specification of `KernelLevels::level_inst_params`: fails
(`none`) if any `.param i` is out of bounds (`i ≥ params.length`). -/
def levelInstParams (l : Ix.Kernel.Level) (params : List Ix.Kernel.Level) :
    Option Ix.Kernel.Level :=
  match l with
  | .zero => some .zero
  | .succ u => (levelInstParams u params).map .succ
  | .max a b => do
    let a' ← levelInstParams a params
    let b' ← levelInstParams b params
    some (levelMax a' b')
  | .imax a b => do
    let a' ← levelInstParams a params
    let b' ← levelInstParams b params
    some (levelIMax a' b')
  | .param i => params[i]?

/-- Pure total specification of `subst_level` (`KernelLevels::level_inst_params`
when `ParamsLt params.length l`). -/
def substLevel (l : Ix.Kernel.Level) (params : List Ix.Kernel.Level) : Ix.Kernel.Level :=
  match l with
  | .zero => .zero
  | .succ u => .succ (substLevel u params)
  | .max a b => levelMax (substLevel a params) (substLevel b params)
  | .imax a b => levelIMax (substLevel a params) (substLevel b params)
  | .param i => params[i]?.getD (.param i)

/-- Pure specification of `KernelLevels::level_list_inst`. -/
def substLevelList (lvls params : List Ix.Kernel.Level) : List Ix.Kernel.Level :=
  lvls.map (fun l => substLevel l params)

theorem levelInstParams_eq_some_iff {l : Ix.Kernel.Level} {params : List Ix.Kernel.Level} :
    (∃ r, levelInstParams l params = some r) ↔ ParamsLt params.length l := by
  induction l with
  | zero => simp [levelInstParams, ParamsLt]
  | succ u ih =>
    simp [levelInstParams, ParamsLt, Option.map_eq_some_iff, ih]
  | max a b iha ihb =>
    simp only [levelInstParams, ParamsLt, bind, Option.bind]
    constructor
    · rintro ⟨r, hr⟩
      cases ha : levelInstParams a params with
      | none => simp [ha] at hr
      | some a' =>
        cases hb : levelInstParams b params with
        | none => simp [ha, hb] at hr
        | some b' => exact ⟨iha.mp ⟨a', ha⟩, ihb.mp ⟨b', hb⟩⟩
    · rintro ⟨ha, hb⟩
      obtain ⟨a', ha'⟩ := iha.mpr ha
      obtain ⟨b', hb'⟩ := ihb.mpr hb
      exact ⟨levelMax a' b', by simp [ha', hb']⟩
  | imax a b iha ihb =>
    simp only [levelInstParams, ParamsLt, bind, Option.bind]
    constructor
    · rintro ⟨r, hr⟩
      cases ha : levelInstParams a params with
      | none => simp [ha] at hr
      | some a' =>
        cases hb : levelInstParams b params with
        | none => simp [ha, hb] at hr
        | some b' => exact ⟨iha.mp ⟨a', ha⟩, ihb.mp ⟨b', hb⟩⟩
    · rintro ⟨ha, hb⟩
      obtain ⟨a', ha'⟩ := iha.mpr ha
      obtain ⟨b', hb'⟩ := ihb.mpr hb
      exact ⟨levelIMax a' b', by simp [ha', hb']⟩
  | param i =>
    simp only [levelInstParams, ParamsLt, List.getElem?_eq_some_iff]
    exact ⟨fun ⟨r, h, _⟩ => h, fun h => ⟨params[i], h, rfl⟩⟩

theorem levelInstParams_eq_substLevel {l : Ix.Kernel.Level} {params : List Ix.Kernel.Level}
    (h : ParamsLt params.length l) :
    levelInstParams l params = some (substLevel l params) := by
  induction l with
  | zero => rfl
  | succ u ih =>
    simp [levelInstParams, substLevel, ih h]
  | max a b iha ihb =>
    simp [levelInstParams, substLevel, iha h.1, ihb h.2, bind, Option.bind]
  | imax a b iha ihb =>
    simp [levelInstParams, substLevel, iha h.1, ihb h.2, bind, Option.bind]
  | param i =>
    change i < params.length at h
    simp [levelInstParams, substLevel, List.getElem?_eq_getElem h]

/-- **`substLevel` evaluates identically to substituting `params` into the
valuation `φ`.** -/
theorem eval_substLevel (φ : Ix.Kernel.LevelParam → Nat) (l : Ix.Kernel.Level)
    (params : List Ix.Kernel.Level) :
    Ix.Kernel.Level.eval φ (substLevel l params) =
      Ix.Kernel.Level.eval
        (fun i => match params[i]? with | some p => Ix.Kernel.Level.eval φ p | none => φ i) l := by
  induction l with
  | zero => rfl
  | succ u ih => simp [substLevel, Ix.Kernel.Level.eval, ih]
  | max a b iha ihb => simp [substLevel, eval_levelMax, Ix.Kernel.Level.eval, iha, ihb]
  | imax a b iha ihb => simp [substLevel, eval_levelIMax, Ix.Kernel.Level.eval, iha, ihb]
  | param i =>
    simp only [substLevel, Ix.Kernel.Level.eval]
    cases params[i]? <;> rfl

theorem substFn_range_eq (φ : Ix.Kernel.LevelParam → Nat) (params : List Ix.Kernel.Level) (i : Nat) :
    Ix.Kernel.Level.substFn φ (List.range params.length) params i =
      match params[i]? with | some p => Ix.Kernel.Level.eval φ p | none => φ i := by
  have H : ∀ (k : Nat) (ps : List Ix.Kernel.Level),
      Ix.Kernel.Level.substFn φ ((List.range ps.length).map (· + k)) ps i =
        if k ≤ i then
          match ps[i - k]? with | some p => Ix.Kernel.Level.eval φ p | none => φ i
        else φ i := by
    intro k ps
    induction ps generalizing k with
    | nil =>
      simp [Ix.Kernel.Level.substFn]
    | cons p ps ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      have hmap : ((· + k) ∘ Nat.succ) = (· + (k + 1)) := by
        funext x; simp [Function.comp]; omega
      rw [hmap, Nat.zero_add]
      simp only [Ix.Kernel.Level.substFn]
      by_cases hki : k = i
      · subst hki; simp
      · simp only [hki, ↓reduceIte, ih (k + 1)]
        by_cases hle : k + 1 ≤ i
        · have hle' : k ≤ i := by omega
          have hsub : i - k = (i - (k + 1)) + 1 := by omega
          simp [hle, hle', hsub]
        · have hle' : ¬(k ≤ i) := by omega
          simp [hle, hle']
  have h0 := H 0 params
  simpa using h0

/-- **`substLevel` refines `Ix.Kernel.Level.subst (List.range params.length) params`
under every valuation `φ`.** -/
theorem eval_substLevel_eq_subst (φ : Ix.Kernel.LevelParam → Nat) (l : Ix.Kernel.Level)
    (params : List Ix.Kernel.Level) :
    Ix.Kernel.Level.eval φ (substLevel l params) =
      Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst (List.range params.length) params l) := by
  rw [eval_substLevel, Ix.Kernel.Level.eval_subst]
  congr 1
  funext i
  exact (substFn_range_eq φ params i).symm


/-! ## Pure Mathematical Model of the Géran Level Normalizer (`norm`, `geqCore`, `is_eq_level`) -/

/-- Lexicographic 3-way comparison of guard lists (`KernelLevels::glist_cmp`):
returns `0` when `a = b`, `1` when `a < b`, and `2` when `a > b`. -/
def glistCmp : List Nat → List Nat → Nat
  | [], [] => 0
  | [], _ :: _ => 1
  | _ :: _, [] => 2
  | x :: ar, y :: br =>
    if x < y then 1
    else if y < x then 2
    else glistCmp ar br

theorem glistCmp_refl (a : List Nat) : glistCmp a a = 0 := by
  induction a with
  | nil => rfl
  | cons x ar ih => simp [glistCmp, ih]

theorem glistCmp_eq_zero_iff {a b : List Nat} : glistCmp a b = 0 ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp [glistCmp]
  | cons x ar ih =>
    cases b with
    | nil => simp [glistCmp]
    | cons y br =>
      simp only [glistCmp, List.cons.injEq]
      by_cases hxy : x < y
      · simp [hxy]; omega
      · by_cases hyx : y < x
        · simp [hxy, hyx]; omega
        · have heq : x = y := by omega
          simp [hxy, hyx, heq, ih]

/-- Ordered subset check on sorted guard lists (`KernelLevels::glist_subset`). -/
def glistSubset : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xr, y :: yr =>
    if x < y then false
    else if y < x then glistSubset (x :: xr) yr
    else glistSubset xr yr
termination_by xs ys => xs.length + ys.length

/-- Length equality check on guard lists (`KernelLevels::glist_eq_len`). -/
def glistEqLen : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | _ :: ar, _ :: br => glistEqLen ar br

theorem glistEqLen_iff {a b : List Nat} : glistEqLen a b = true ↔ a.length = b.length := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp [glistEqLen]
  | cons x ar ih =>
    cases b with
    | nil => simp [glistEqLen]
    | cons y br => simp [glistEqLen, ih]

/-- Ordered insertion into a sorted guard list (`KernelLevels::glist_ordered_insert`).
Returns `(true, newList)` when `x` was newly inserted, and `(false, l)` when `x` was already present. -/
def glistOrderedInsert (x : Nat) : List Nat → Bool × List Nat
  | [] => (true, [x])
  | h :: r =>
    if x < h then (true, x :: h :: r)
    else if h < x then
      let (f, r2) := glistOrderedInsert x r
      (f, h :: r2)
    else (false, h :: r)

theorem glistOrderedInsert_mem (x : Nat) (l : List Nat) :
    ∀ y, y ∈ (glistOrderedInsert x l).2 ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil =>
    intro y; simp [glistOrderedInsert]
  | cons h r ih =>
    intro y
    simp only [glistOrderedInsert]
    by_cases hxh : x < h
    · simp [hxh]
    · by_cases hhx : h < x
      · simp only [hxh, hhx, ↓reduceIte, List.mem_cons, ih]
        tauto
      · have heq : x = h := by omega
        subst heq
        simp [hxh, List.mem_cons]

theorem glistOrderedInsert_false_mem {x : Nat} {l : List Nat}
    (h : (glistOrderedInsert x l).1 = false) : x ∈ l := by
  induction l with
  | nil => simp [glistOrderedInsert] at h
  | cons hd r ih =>
    simp only [glistOrderedInsert] at h
    by_cases hxh : x < hd
    · simp [hxh] at h
    · by_cases hhx : hd < x
      · simp only [hxh, hhx, ↓reduceIte] at h
        exact List.mem_cons_of_mem hd (ih h)
      · have heq : x = hd := by omega
        subst heq
        exact List.mem_cons_self ..

theorem glistOrderedInsert_false_snd {x : Nat} {l : List Nat}
    (h : (glistOrderedInsert x l).1 = false) : (glistOrderedInsert x l).2 = l := by
  induction l with
  | nil => simp [glistOrderedInsert] at h
  | cons hd r ih =>
    simp only [glistOrderedInsert] at h ⊢
    by_cases hxh : x < hd
    · simp [hxh] at h
    · by_cases hhx : hd < x
      · simp only [hxh, hhx, ↓reduceIte] at h ⊢
        rw [ih h]
      · simp [hxh, hhx]

/-- Ordered insertion / max-offset update in an `NLVar` list (`KernelLevels::nlvars_add`). -/
def nlvarsAdd : List NLVar → Nat → Nat → List NLVar
  | [], idx, k => [⟨idx, k⟩]
  | ⟨vi, vo⟩ :: rest, idx, k =>
    if idx < vi then ⟨idx, k⟩ :: ⟨vi, vo⟩ :: rest
    else if vi < idx then ⟨vi, vo⟩ :: nlvarsAdd rest idx k
    else if vo < k then ⟨vi, k⟩ :: rest
    else ⟨vi, vo⟩ :: rest

/-- Structural equality of `NLVar` lists (`KernelLevels::nlvars_eq`). -/
def nlvarsEq : List NLVar → List NLVar → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | ⟨xi, xo⟩ :: ar, ⟨yi, yo⟩ :: br =>
    if xi = yi then
      if xo = yo then nlvarsEq ar br
      else false
    else false

theorem nlvarsEq_iff {a b : List NLVar} : nlvarsEq a b = true ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp [nlvarsEq]
  | cons x ar ih =>
    rcases x with ⟨xi, xo⟩
    cases b with
    | nil => simp [nlvarsEq]
    | cons y br =>
      rcases y with ⟨yi, yo⟩
      simp only [nlvarsEq, List.cons.injEq, NLVar.mk.injEq]
      by_cases hi : xi = yi
      · by_cases ho : xo = yo
        · simp [hi, ho, ih]
        · simp [hi, ho]
      · simp [hi]

/-- Maximum offset in an `NLVar` list (`KernelLevels::nlvars_max_offset`). -/
def nlvarsMaxOffset : List NLVar → Nat
  | [] => 0
  | ⟨_, vo⟩ :: rest =>
    let m := nlvarsMaxOffset rest
    if m < vo then vo else m

/-- Subsumption filter on sorted `NLVar` lists (`KernelLevels::nlvars_subsume`). -/
def nlvarsSubsume : List NLVar → List NLVar → List NLVar
  | [], _ => []
  | xs@(_ :: _), [] => xs
  | (⟨xi, xo⟩ :: xr), (⟨yi, yo⟩ :: yr) =>
    if xi < yi then ⟨xi, xo⟩ :: nlvarsSubsume xr (⟨yi, yo⟩ :: yr)
    else if yi < xi then nlvarsSubsume (⟨xi, xo⟩ :: xr) yr
    else if yo < xo then ⟨xi, xo⟩ :: nlvarsSubsume xr yr
    else nlvarsSubsume xr yr
termination_by xs ys => xs.length + ys.length

/-- Ordered constant insertion into an `NLEntry` list (`KernelLevels::nl_add_const_go`). -/
def nlAddConstGo : List NLEntry → List Nat → Nat → List NLEntry
  | [], path, k => [⟨path, k, []⟩]
  | ⟨ep, ec, ev⟩ :: rest, path, k =>
    match glistCmp path ep with
    | 0 => if ec < k then ⟨ep, k, ev⟩ :: rest else ⟨ep, ec, ev⟩ :: rest
    | 1 => ⟨path, k, []⟩ :: ⟨ep, ec, ev⟩ :: rest
    | _ => ⟨ep, ec, ev⟩ :: nlAddConstGo rest path k

/-- Conditional constant insertion (`KernelLevels::nl_add_const`): skips `k = 0` and
skips `k = 1` when `path` is non-empty (since any active parameter in `path` is `≥ 1`). -/
def nlAddConst (acc : List NLEntry) (path : List Nat) (k : Nat) : List NLEntry :=
  match k with
  | 0 => acc
  | 1 =>
    match path with
    | [] => nlAddConstGo acc path 1
    | _ :: _ => acc
  | k => nlAddConstGo acc path k

/-- Ordered variable insertion into an `NLEntry` list (`KernelLevels::nl_add_var`). -/
def nlAddVar : List NLEntry → List Nat → Nat → Nat → List NLEntry
  | [], path, idx, k => [⟨path, 0, [⟨idx, k⟩]⟩]
  | ⟨ep, ec, ev⟩ :: rest, path, idx, k =>
    match glistCmp path ep with
    | 0 => ⟨ep, ec, nlvarsAdd ev idx k⟩ :: rest
    | 1 => ⟨path, 0, [⟨idx, k⟩]⟩ :: ⟨ep, ec, ev⟩ :: rest
    | _ => ⟨ep, ec, ev⟩ :: nlAddVar rest path idx k

/-- Fuel-indexed mutually recursive core of `normalize_aux` and `normalize_imax_dispatch`. -/
def normalizeStep : Nat → Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level) →
    List Nat → Nat → List NLEntry → List NLEntry
  | 0, _, _, _, acc => acc
  | fuel + 1, .inl l, path, k, acc =>
    match l with
    | .zero => nlAddConst acc path k
    | .succ inner => normalizeStep fuel (.inl inner) path (k + 1) acc
    | .max a b =>
      normalizeStep fuel (.inl b) path k (normalizeStep fuel (.inl a) path k acc)
    | .imax u b => normalizeStep fuel (.inr (u, b)) path k acc
    | .param idx =>
      match glistOrderedInsert idx path with
      | (true, newPath) =>
        nlAddVar (nlAddConst acc path k) newPath idx k
      | (false, _) =>
        if k = 0 then acc else nlAddVar acc path idx k
  | fuel + 1, .inr (a, b), path, k, acc =>
    match b with
    | .zero => nlAddConst acc path k
    | .succ v =>
      normalizeStep fuel (.inl v) path (k + 1) (normalizeStep fuel (.inl a) path k acc)
    | .max v w =>
      normalizeStep fuel (.inr (a, w)) path k (normalizeStep fuel (.inr (a, v)) path k acc)
    | .imax v w =>
      normalizeStep fuel (.inr (v, w)) path k (normalizeStep fuel (.inr (a, w)) path k acc)
    | .param idx =>
      match glistOrderedInsert idx path with
      | (true, newPath) =>
        normalizeStep fuel (.inl a) newPath k
          (nlAddVar (nlAddConst acc path k) newPath idx k)
      | (false, _) =>
        let acc2 := if k = 0 then acc else nlAddVar acc path idx k
        normalizeStep fuel (.inl a) path k acc2

/-- Upper bound on recursion depth of `normalize_aux` / `normalize_imax_dispatch`. -/
def normFuel : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level) → Nat
  | .inl l => 2 * (levelDepth l + 1) * (levelDepth l + 2)
  | .inr (a, b) =>
    let m := Max.max (levelDepth a) (levelDepth b) + 1
    2 * m * (m + 1) + levelDepth b + 1

/-- Pure specification of `KernelLevels::normalize_aux`. -/
def normalizeAux (l : Ix.Kernel.Level) (path : List Nat) (k : Nat) (acc : List NLEntry) :
    List NLEntry :=
  normalizeStep (normFuel (.inl l)) (.inl l) path k acc

/-- Pure specification of `KernelLevels::normalize_imax_dispatch`. -/
def normalizeIMaxDispatch (a b : Ix.Kernel.Level) (path : List Nat) (k : Nat) (acc : List NLEntry) :
    List NLEntry :=
  normalizeStep (normFuel (.inr (a, b))) (.inr (a, b)) path k acc

/-- Pure specification of `KernelLevels::nl_subsume_entry`. -/
def nlSubsumeEntry : NLEntry → List NLEntry → NLEntry
  | e, [] => e
  | ⟨p1, c1, v1⟩, ⟨p2, c2, v2⟩ :: srest =>
    if !(glistSubset p2 p1) then
      nlSubsumeEntry ⟨p1, c1, v1⟩ srest
    else
      let same := glistEqLen p1 p2
      let c1n :=
        if c1 = 0 then 0
        else
          let or1 := if same then true else decide (c2 < c1)
          let or2 :=
            match v2 with
            | [] => true
            | _ :: _ => decide (nlvarsMaxOffset v1 + 1 < c1)
          if or1 && or2 then c1 else 0
      let v1n :=
        if same then v1
        else
          match v2 with
          | [] => v1
          | _ :: _ => nlvarsSubsume v1 v2
      nlSubsumeEntry ⟨p1, c1n, v1n⟩ srest

/-- Pure specification of `KernelLevels::nl_subsumption_walk`. -/
def nlSubsumptionWalk (rem snapshot : List NLEntry) : List NLEntry :=
  rem.map (fun e => nlSubsumeEntry e snapshot)

/-- Pure specification of `KernelLevels::level_normalize` (`norm`). -/
def levelNormalize (l : Ix.Kernel.Level) : List NLEntry :=
  let seed : List NLEntry := [⟨[], 0, []⟩]
  let raw := normalizeAux l [] 0 seed
  nlSubsumptionWalk raw raw

/-- Pure specification of `KernelLevels::nl_skip_empty`. -/
def nlSkipEmpty : List NLEntry → List NLEntry
  | [] => []
  | (⟨p, c, v⟩ :: rest) =>
    if c = 0 then
      match v with
      | [] => nlSkipEmpty rest
      | _ :: _ => ⟨p, 0, v⟩ :: rest
    else ⟨p, c, v⟩ :: rest

theorem nlSkipEmpty_cons_length_lt {l : List NLEntry} {x : NLEntry} {ar : List NLEntry}
    (h : nlSkipEmpty l = x :: ar) : ar.length < l.length := by
  induction l with
  | nil => simp [nlSkipEmpty] at h
  | cons e rest ih =>
    rcases e with ⟨p, c, v⟩
    simp only [nlSkipEmpty] at h
    by_cases hc : c = 0
    · subst hc
      cases v with
      | nil =>
        have hlt := ih h
        simp only [List.length_cons]
        omega
      | cons _ _ =>
        injection h with _ har
        subst har
        simp [List.length_cons]
    · simp only [hc, ↓reduceIte] at h
      injection h with _ har
      subst har
      simp [List.length_cons]

theorem nlSkipEmpty_length_le (l : List NLEntry) : (nlSkipEmpty l).length ≤ l.length := by
  induction l with
  | nil => simp [nlSkipEmpty]
  | cons e rest ih =>
    rcases e with ⟨p, c, v⟩
    simp only [nlSkipEmpty]
    by_cases hc : c = 0
    · subst hc
      cases v <;> simp [List.length_cons] <;> omega
    · simp [hc]

/-- Pure specification of `KernelLevels::nl_eq`. -/
def nlEq (a0 b0 : List NLEntry) : Bool :=
  match ha : nlSkipEmpty a0, hb : nlSkipEmpty b0 with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | ⟨xp, xc, xv⟩ :: ar, ⟨yp, yc, yv⟩ :: br =>
    if glistCmp xp yp = 0 then
      if xc = yc then
        if nlvarsEq xv yv then nlEq ar br
        else false
      else false
    else false
termination_by a0.length + b0.length
decreasing_by
  have h1 := nlSkipEmpty_cons_length_lt ha
  have h2 := nlSkipEmpty_cons_length_lt hb
  omega

theorem nlEq_unfold (a0 b0 : List NLEntry) :
    nlEq a0 b0 =
      match nlSkipEmpty a0, nlSkipEmpty b0 with
      | [], [] => true
      | [], _ :: _ => false
      | _ :: _, [] => false
      | ⟨xp, xc, xv⟩ :: ar, ⟨yp, yc, yv⟩ :: br =>
        if glistCmp xp yp = 0 then
          if xc = yc then
            if nlvarsEq xv yv then nlEq ar br
            else false
          else false
        else false := by
  conv_lhs => unfold nlEq
  cases nlSkipEmpty a0 with
  | nil => cases nlSkipEmpty b0 <;> rfl
  | cons x ar =>
    rcases x with ⟨xp, xc, xv⟩
    cases nlSkipEmpty b0 with
    | nil => rfl
    | cons y br =>
      rcases y with ⟨yp, yc, yv⟩
      rfl

/-- Pure specification of `KernelLevels::nlvars_any_offset_geq`. -/
def nlvarsAnyOffsetGeq : List NLVar → Nat → Bool
  | [], _ => false
  | ⟨_, vo⟩ :: rest, c =>
    if !(vo + 1 < c) then true
    else nlvarsAnyOffsetGeq rest c

/-- Pure specification of `KernelLevels::nl_covers_const`. -/
def nlCoversConst : List NLEntry → List Nat → Nat → Bool
  | [], _, _ => false
  | ⟨p2, c2, v2⟩ :: rest, p1, c =>
    if !(glistSubset p2 p1) then nlCoversConst rest p1 c
    else
      let hit := if !(c2 < c) then true else nlvarsAnyOffsetGeq v2 c
      if hit then true else nlCoversConst rest p1 c

/-- Pure specification of `KernelLevels::nlvars_dominates`. -/
def nlvarsDominates : List NLVar → Nat → Nat → Bool
  | [], _, _ => false
  | ⟨vi, vo⟩ :: rest, w, off =>
    if vi = w then
      if !(vo < off) then true
      else nlvarsDominates rest w off
    else nlvarsDominates rest w off

/-- Pure specification of `KernelLevels::nl_covers_var`. -/
def nlCoversVar : List NLEntry → List Nat → Nat → Nat → Bool
  | [], _, _, _ => false
  | ⟨p2, _, v2⟩ :: rest, p1, w, off =>
    if !(glistSubset p2 p1) then nlCoversVar rest p1 w off
    else if nlvarsDominates v2 w off then true
    else nlCoversVar rest p1 w off

/-- Pure specification of `KernelLevels::nl_le_vars`. -/
def nlLeVars : List NLVar → List NLEntry → List Nat → Bool
  | [], _, _ => true
  | ⟨vi, vo⟩ :: rest, l2, p1 =>
    if nlCoversVar l2 p1 vi vo then nlLeVars rest l2 p1
    else false

/-- Pure specification of `KernelLevels::nl_le`. -/
def nlLe : List NLEntry → List NLEntry → Bool
  | [], _ => true
  | ⟨p1, c1, v1⟩ :: rest, l2 =>
    let cOk := if c1 = 0 then true else nlCoversConst l2 p1 c1
    if cOk then
      if nlLeVars v1 l2 p1 then nlLe rest l2
      else false
    else false

/-- Pure specification of `KernelLevels::level_leq` (`is_geq_core` / `geqCore`). -/
def levelLeq (a b : Ix.Kernel.Level) : Bool :=
  if a == b then true
  else
    match a with
    | .zero => true
    | _ => nlLe (levelNormalize a) (levelNormalize b)

/-- Pure specification of `KernelLevels::level_equal` (`is_eq_level`). -/
def levelEqual (a b : Ix.Kernel.Level) : Bool :=
  if a == b then true
  else nlEq (levelNormalize a) (levelNormalize b)

/-! ### Semantic Evaluation of `NLVar` and `NLEntry` Lists -/

/-- Whether every universe parameter in `p` is assigned a positive natural number by `φ`. -/
def guardActive (φ : Ix.Kernel.LevelParam → Nat) (p : List Nat) : Bool :=
  p.all (fun i => decide (0 < φ i))

theorem guardActive_eq_geranActive (φ : Ix.Kernel.LevelParam → Nat) (p : List Nat) :
    guardActive φ p = Ix.Kernel.Level.Geran.active φ p := rfl

theorem guardActive_iff {φ : Ix.Kernel.LevelParam → Nat} {p : List Nat} :
    guardActive φ p = true ↔ ∀ i ∈ p, 0 < φ i := by
  simp [guardActive]

/-- Evaluation of a single `NLVar` under `φ`. -/
def NLVar.eval (φ : Ix.Kernel.LevelParam → Nat) (v : NLVar) : Nat :=
  φ v.param + v.offset

/-- Evaluation of an `NLVar` list (maximum of its variable terms). -/
def evalNLVars (φ : Ix.Kernel.LevelParam → Nat) : List NLVar → Nat
  | [] => 0
  | v :: vs => Max.max (v.eval φ) (evalNLVars φ vs)

/-- Evaluation of a single `NLEntry` under `φ`. -/
def NLEntry.eval (φ : Ix.Kernel.LevelParam → Nat) (e : NLEntry) : Nat :=
  if guardActive φ e.guards then Max.max e.constPart (evalNLVars φ e.vars) else 0

/-- Evaluation of an `NLEntry` list under `φ` (maximum of its entries). -/
def evalNLEntries (φ : Ix.Kernel.LevelParam → Nat) : List NLEntry → Nat
  | [] => 0
  | e :: es => Max.max (e.eval φ) (evalNLEntries φ es)

/-- Well-formedness of an `NLEntry`: every variable in `e.vars` belongs to `e.guards`,
and `e.guards` is strictly sorted. -/
def NLEntry.WF (e : NLEntry) : Prop :=
  (∀ v ∈ e.vars, v.param ∈ e.guards) ∧ List.Pairwise (· < ·) e.guards

theorem evalNLVars_nlvarsAdd (φ : Ix.Kernel.LevelParam → Nat) (vars : List NLVar)
    (idx k : Nat) :
    evalNLVars φ (nlvarsAdd vars idx k) = Max.max (φ idx + k) (evalNLVars φ vars) := by
  induction vars with
  | nil =>
    simp [nlvarsAdd, evalNLVars, NLVar.eval]
  | cons v rest ih =>
    rcases v with ⟨vi, vo⟩
    simp only [nlvarsAdd]
    by_cases h1 : idx < vi
    · simp [h1, evalNLVars, NLVar.eval]
    · by_cases h2 : vi < idx
      · simp only [h1, h2, ↓reduceIte, evalNLVars, NLVar.eval, ih]
        omega
      · have heq : vi = idx := by omega
        subst heq
        by_cases h3 : vo < k
        · simp only [h1, h3, ↓reduceIte, evalNLVars, NLVar.eval]
          omega
        · simp only [h1, h3, ↓reduceIte, evalNLVars, NLVar.eval]
          omega

theorem evalNLEntries_nlAddConstGo (φ : Ix.Kernel.LevelParam → Nat) (acc : List NLEntry)
    (path : List Nat) (k : Nat) :
    evalNLEntries φ (nlAddConstGo acc path k) =
      Max.max (if guardActive φ path then k else 0) (evalNLEntries φ acc) := by
  induction acc with
  | nil =>
    simp [nlAddConstGo, evalNLEntries, NLEntry.eval, evalNLVars]
  | cons e rest ih =>
    rcases e with ⟨ep, ec, ev⟩
    simp only [nlAddConstGo]
    rcases hcmp : glistCmp path ep with _ | _ | n
    · have hep : path = ep := glistCmp_eq_zero_iff.mp hcmp
      subst hep
      by_cases hck : ec < k
      · simp only [hck, ↓reduceIte, evalNLEntries, NLEntry.eval]
        by_cases hp : guardActive φ path = true <;> simp [hp] <;> omega
      · simp only [hck, ↓reduceIte, evalNLEntries, NLEntry.eval]
        by_cases hp : guardActive φ path = true <;> simp [hp] <;> omega
    · simp only [evalNLEntries, NLEntry.eval, evalNLVars]
      by_cases hp : guardActive φ path = true <;> simp [hp] <;> omega
    · simp only [evalNLEntries, NLEntry.eval, ih]
      omega

theorem evalNLEntries_nlAddVar (φ : Ix.Kernel.LevelParam → Nat) (acc : List NLEntry)
    (path : List Nat) (idx k : Nat) :
    evalNLEntries φ (nlAddVar acc path idx k) =
      Max.max (if guardActive φ path then φ idx + k else 0) (evalNLEntries φ acc) := by
  induction acc with
  | nil =>
    simp [nlAddVar, evalNLEntries, NLEntry.eval, evalNLVars, NLVar.eval]
  | cons e rest ih =>
    rcases e with ⟨ep, ec, ev⟩
    simp only [nlAddVar]
    rcases hcmp : glistCmp path ep with _ | _ | n
    · have hep : path = ep := glistCmp_eq_zero_iff.mp hcmp
      subst hep
      simp only [evalNLEntries, NLEntry.eval, evalNLVars_nlvarsAdd]
      by_cases hp : guardActive φ path = true <;> simp [hp] <;> omega
    · simp only [evalNLEntries, NLEntry.eval, evalNLVars, NLVar.eval]
      by_cases hp : guardActive φ path = true <;> simp [hp] <;> omega
    · simp only [evalNLEntries, NLEntry.eval, ih]
      omega

theorem evalNLEntries_nlSkipEmpty (φ : Ix.Kernel.LevelParam → Nat) (l : List NLEntry) :
    evalNLEntries φ (nlSkipEmpty l) = evalNLEntries φ l := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨p, c, v⟩
    simp only [nlSkipEmpty]
    by_cases hc : c = 0
    · subst hc
      cases v with
      | nil =>
        simp [evalNLEntries, NLEntry.eval, evalNLVars, ih]
      | cons v0 vr =>
        simp [evalNLEntries]
    · simp [hc, evalNLEntries]

/-- **Soundness of `nlEq`**: if `nlEq a0 b0 = true`, then `a0` and `b0` evaluate to
the exact same natural number under every valuation `φ`. -/
theorem nlEq_sound {a0 b0 : List NLEntry} (h : nlEq a0 b0 = true)
    (φ : Ix.Kernel.LevelParam → Nat) :
    evalNLEntries φ a0 = evalNLEntries φ b0 := by
  suffices H : ∀ n, ∀ a b, a.length + b.length = n → nlEq a b = true →
      evalNLEntries φ a = evalNLEntries φ b by
    exact H _ a0 b0 rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn heq
    rw [nlEq_unfold] at heq
    rw [← evalNLEntries_nlSkipEmpty φ a, ← evalNLEntries_nlSkipEmpty φ b]
    cases ha : nlSkipEmpty a with
    | nil =>
      cases hb : nlSkipEmpty b with
      | nil => rfl
      | cons y br => simp [ha, hb] at heq
    | cons x ar =>
      rcases x with ⟨xp, xc, xv⟩
      cases hb : nlSkipEmpty b with
      | nil => simp [ha, hb] at heq
      | cons y br =>
        rcases y with ⟨yp, yc, yv⟩
        simp only [ha, hb] at heq
        by_cases hp : glistCmp xp yp = 0
        · have hpeq : xp = yp := glistCmp_eq_zero_iff.mp hp
          by_cases hc : xc = yc
          · by_cases hv : nlvarsEq xv yv = true
            · have hveq : xv = yv := nlvarsEq_iff.mp hv
              simp only [hp, hc, hv, ↓reduceIte] at heq
              have h1 := nlSkipEmpty_cons_length_lt ha
              have h2 := nlSkipEmpty_cons_length_lt hb
              have hlen : ar.length + br.length < n := by omega
              have ih_step := ih _ hlen ar br rfl heq
              simp [evalNLEntries, hpeq, hc, hveq, ih_step]
            · simp [hp, hc, hv] at heq
          · simp [hp, hc] at heq
        · simp [hp] at heq

theorem glistSubset_mem {xs ys : List Nat}
    (hs : List.Pairwise (· < ·) xs) (ht : List.Pairwise (· < ·) ys)
    (hsub : glistSubset xs ys = true) :
    ∀ z ∈ xs, z ∈ ys := by
  induction xs, ys using glistSubset.induct with
  | case1 => intro z hz; cases hz
  | case2 x xr => simp [glistSubset] at hsub
  | case3 x xr y yr hxy =>
    simp [glistSubset, hxy] at hsub
  | case4 x xr y yr hxy hyx ih =>
    simp only [glistSubset, hxy, hyx, ↓reduceIte] at hsub
    have ht' : List.Pairwise (· < ·) yr := (List.pairwise_cons.mp ht).2
    intro z hz
    exact List.mem_cons_of_mem y (ih hs ht' hsub z hz)
  | case5 x xr y yr hxy hyx ih =>
    simp only [glistSubset, hxy, hyx, ↓reduceIte] at hsub
    have heq : x = y := by omega
    subst heq
    have hs' : List.Pairwise (· < ·) xr := (List.pairwise_cons.mp hs).2
    have ht' : List.Pairwise (· < ·) yr := (List.pairwise_cons.mp ht).2
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hzr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem x (ih hs' ht' hsub z hzr)

theorem guardActive_of_subset {φ : Ix.Kernel.LevelParam → Nat} {p2 p1 : List Nat}
    (hsub : ∀ z ∈ p2, z ∈ p1) (hp1 : guardActive φ p1 = true) :
    guardActive φ p2 = true := by
  rw [guardActive_iff] at hp1 ⊢
  intro z hz
  exact hp1 z (hsub z hz)

theorem nlvarsAnyOffsetGeq_exists {vars : List NLVar} {c : Nat}
    (h : nlvarsAnyOffsetGeq vars c = true) :
    ∃ v ∈ vars, c ≤ v.offset + 1 := by
  induction vars with
  | nil => simp [nlvarsAnyOffsetGeq] at h
  | cons v rest ih =>
    rcases v with ⟨vi, vo⟩
    simp only [nlvarsAnyOffsetGeq] at h
    by_cases hlt : vo + 1 < c
    · simp only [hlt, not_true_eq_false, ↓reduceIte] at h
      obtain ⟨v', hv', hc⟩ := ih h
      exact ⟨v', List.mem_cons_of_mem _ hv', hc⟩
    · refine ⟨⟨vi, vo⟩, List.mem_cons_self .., ?_⟩
      dsimp only
      omega

theorem le_evalNLVars_of_mem {φ : Ix.Kernel.LevelParam → Nat} {vars : List NLVar} {v : NLVar}
    (hv : v ∈ vars) : v.eval φ ≤ evalNLVars φ vars := by
  induction vars with
  | nil => cases hv
  | cons hd rest ih =>
    rcases List.mem_cons.mp hv with rfl | hrest
    · simp [evalNLVars]
    · have := ih hrest
      simp only [evalNLVars]
      omega

theorem le_evalNLEntries_of_mem {φ : Ix.Kernel.LevelParam → Nat} {es : List NLEntry} {e : NLEntry}
    (he : e ∈ es) : e.eval φ ≤ evalNLEntries φ es := by
  induction es with
  | nil => cases he
  | cons hd rest ih =>
    rcases List.mem_cons.mp he with rfl | hrest
    · simp [evalNLEntries]
    · have := ih hrest
      simp only [evalNLEntries]
      omega

theorem nlCoversConst_sound {φ : Ix.Kernel.LevelParam → Nat} {l2 : List NLEntry}
    {p1 : List Nat} {c : Nat}
    (hp1_sort : List.Pairwise (· < ·) p1)
    (hl2_wf : ∀ e ∈ l2, e.WF)
    (hp1_act : guardActive φ p1 = true)
    (hcov : nlCoversConst l2 p1 c = true) :
    c ≤ evalNLEntries φ l2 := by
  induction l2 with
  | nil => simp [nlCoversConst] at hcov
  | cons e rest ih =>
    rcases e with ⟨p2, c2, v2⟩
    have he_wf := hl2_wf ⟨p2, c2, v2⟩ (List.mem_cons_self ..)
    have hrest_wf : ∀ e' ∈ rest, e'.WF := fun e' he' => hl2_wf e' (List.mem_cons_of_mem _ he')
    simp only [nlCoversConst] at hcov
    by_cases hsub : glistSubset p2 p1 = true
    · simp only [hsub, not_true_eq_false, ↓reduceIte] at hcov
      have hp2_act : guardActive φ p2 = true :=
        guardActive_of_subset (glistSubset_mem he_wf.2 hp1_sort hsub) hp1_act
      by_cases hlt : c2 < c
      · simp only [hlt, not_true_eq_false, ↓reduceIte] at hcov
        by_cases hany : nlvarsAnyOffsetGeq v2 c = true
        · obtain ⟨v, hv, hvo⟩ := nlvarsAnyOffsetGeq_exists hany
          have hvi_mem : v.param ∈ p2 := he_wf.1 v hv
          have hvi_pos : 0 < φ v.param := (guardActive_iff.mp hp2_act) v.param hvi_mem
          have hveval : c ≤ v.eval φ := by
            unfold NLVar.eval; omega
          have hvl : v.eval φ ≤ evalNLVars φ v2 := le_evalNLVars_of_mem hv
          simp only [evalNLEntries, NLEntry.eval, hp2_act, ↓reduceIte]
          omega
        · simp only [hany, ↓reduceIte] at hcov
          have hrest := ih hrest_wf hcov
          simp only [evalNLEntries]
          omega
      · simp only [evalNLEntries, NLEntry.eval, hp2_act, ↓reduceIte]
        omega
    · simp only [Bool.not_eq_true] at hsub
      simp only [hsub, Bool.not_false, ↓reduceIte] at hcov
      have hrest := ih hrest_wf hcov
      simp only [evalNLEntries]
      omega

theorem nlvarsDominates_exists {vars : List NLVar} {w off : Nat}
    (h : nlvarsDominates vars w off = true) :
    ∃ v ∈ vars, v.param = w ∧ off ≤ v.offset := by
  induction vars with
  | nil => simp [nlvarsDominates] at h
  | cons v rest ih =>
    rcases v with ⟨vi, vo⟩
    simp only [nlvarsDominates] at h
    by_cases hvi : vi = w
    · subst hvi
      by_cases hvo : vo < off
      · simp only [↓reduceIte, hvo, not_true_eq_false] at h
        obtain ⟨v', hv', hidx, hoff⟩ := ih h
        exact ⟨v', List.mem_cons_of_mem _ hv', hidx, hoff⟩
      · refine ⟨⟨vi, vo⟩, List.mem_cons_self .., rfl, ?_⟩
        dsimp only
        omega
    · simp only [hvi, ↓reduceIte] at h
      obtain ⟨v', hv', hidx, hoff⟩ := ih h
      exact ⟨v', List.mem_cons_of_mem _ hv', hidx, hoff⟩

theorem nlCoversVar_sound {φ : Ix.Kernel.LevelParam → Nat} {l2 : List NLEntry}
    {p1 : List Nat} {w off : Nat}
    (hp1_sort : List.Pairwise (· < ·) p1)
    (hl2_wf : ∀ e ∈ l2, e.WF)
    (hp1_act : guardActive φ p1 = true)
    (hcov : nlCoversVar l2 p1 w off = true) :
    φ w + off ≤ evalNLEntries φ l2 := by
  induction l2 with
  | nil => simp [nlCoversVar] at hcov
  | cons e rest ih =>
    rcases e with ⟨p2, c2, v2⟩
    have he_wf := hl2_wf ⟨p2, c2, v2⟩ (List.mem_cons_self ..)
    have hrest_wf : ∀ e' ∈ rest, e'.WF := fun e' he' => hl2_wf e' (List.mem_cons_of_mem _ he')
    simp only [nlCoversVar] at hcov
    by_cases hsub : glistSubset p2 p1 = true
    · simp only [hsub, not_true_eq_false, ↓reduceIte] at hcov
      have hp2_act : guardActive φ p2 = true :=
        guardActive_of_subset (glistSubset_mem he_wf.2 hp1_sort hsub) hp1_act
      by_cases hdom : nlvarsDominates v2 w off = true
      · obtain ⟨v, hv, hidx, hoff⟩ := nlvarsDominates_exists hdom
        have hveval : φ w + off ≤ v.eval φ := by
          unfold NLVar.eval; rw [hidx]; omega
        have hvl : v.eval φ ≤ evalNLVars φ v2 := le_evalNLVars_of_mem hv
        simp only [evalNLEntries, NLEntry.eval, hp2_act, ↓reduceIte]
        omega
      · simp only [hdom, ↓reduceIte] at hcov
        have hrest := ih hrest_wf hcov
        simp only [evalNLEntries]
        omega
    · simp only [Bool.not_eq_true] at hsub
      simp only [hsub, Bool.not_false, ↓reduceIte] at hcov
      have hrest := ih hrest_wf hcov
      simp only [evalNLEntries]
      omega

theorem nlLeVars_sound {φ : Ix.Kernel.LevelParam → Nat} {vars : List NLVar}
    {l2 : List NLEntry} {p1 : List Nat}
    (hp1_sort : List.Pairwise (· < ·) p1)
    (hl2_wf : ∀ e ∈ l2, e.WF)
    (hp1_act : guardActive φ p1 = true)
    (hvars : nlLeVars vars l2 p1 = true) :
    evalNLVars φ vars ≤ evalNLEntries φ l2 := by
  induction vars with
  | nil => simp [evalNLVars]
  | cons v rest ih =>
    rcases v with ⟨vi, vo⟩
    simp only [nlLeVars] at hvars
    by_cases hcov : nlCoversVar l2 p1 vi vo = true
    · simp only [hcov, ↓reduceIte] at hvars
      have h1 := nlCoversVar_sound hp1_sort hl2_wf hp1_act hcov
      have h2 := ih hvars
      simp only [evalNLVars, NLVar.eval]
      omega
    · simp [hcov] at hvars

/-- **Soundness of `nlLe`**: if every entry in `l1` has sorted guards, every entry in `l2`
is well-formed (`NLEntry.WF`), and `nlLe l1 l2 = true`, then `l1` is pointwise `≤ l2`
under every valuation `φ`. -/
theorem nlLe_sound {l1 l2 : List NLEntry}
    (hl1_sort : ∀ e ∈ l1, List.Pairwise (· < ·) e.guards)
    (hl2_wf : ∀ e ∈ l2, e.WF)
    (hle : nlLe l1 l2 = true) (φ : Ix.Kernel.LevelParam → Nat) :
    evalNLEntries φ l1 ≤ evalNLEntries φ l2 := by
  induction l1 with
  | nil => simp [evalNLEntries]
  | cons e rest ih =>
    rcases e with ⟨p1, c1, v1⟩
    have hp1_sort : List.Pairwise (· < ·) p1 := hl1_sort ⟨p1, c1, v1⟩ (List.mem_cons_self ..)
    have hrest_sort : ∀ e' ∈ rest, List.Pairwise (· < ·) e'.guards :=
      fun e' he' => hl1_sort e' (List.mem_cons_of_mem _ he')
    simp only [nlLe] at hle
    by_cases hc0 : c1 = 0
    · subst hc0
      simp only [↓reduceIte] at hle
      by_cases hvars : nlLeVars v1 l2 p1 = true
      · simp only [hvars, ↓reduceIte] at hle
        have hrest := ih hrest_sort hle
        simp only [evalNLEntries, NLEntry.eval]
        by_cases hp1_act : guardActive φ p1 = true
        · have hv := nlLeVars_sound hp1_sort hl2_wf hp1_act hvars
          simp [hp1_act]; omega
        · simp [hp1_act, hrest]
      · simp [hvars] at hle
    · simp only [hc0, ↓reduceIte] at hle
      by_cases hcov : nlCoversConst l2 p1 c1 = true
      · simp only [hcov, ↓reduceIte] at hle
        by_cases hvars : nlLeVars v1 l2 p1 = true
        · simp only [hvars, ↓reduceIte] at hle
          have hrest := ih hrest_sort hle
          simp only [evalNLEntries, NLEntry.eval]
          by_cases hp1_act : guardActive φ p1 = true
          · have hc := nlCoversConst_sound hp1_sort hl2_wf hp1_act hcov
            have hv := nlLeVars_sound hp1_sort hl2_wf hp1_act hvars
            simp [hp1_act]; omega
          · simp [hp1_act, hrest]
        · simp [hvars] at hle
      · simp [hcov] at hle

theorem glistOrderedInsert_pairwise (x : Nat) {l : List Nat}
    (hl : List.Pairwise (· < ·) l) :
    List.Pairwise (· < ·) (glistOrderedInsert x l).2 := by
  induction l with
  | nil =>
    simp [glistOrderedInsert]
  | cons hd r ih =>
    rw [List.pairwise_cons] at hl
    rcases hl with ⟨hhd, hr⟩
    simp only [glistOrderedInsert]
    by_cases hxh : x < hd
    · simp only [hxh, ↓reduceIte, List.pairwise_cons]
      refine ⟨fun y hy => ?_, hhd, hr⟩
      rcases List.mem_cons.mp hy with rfl | hyr
      · exact hxh
      · exact Nat.lt_trans hxh (hhd y hyr)
    · by_cases hhx : hd < x
      · simp only [hxh, hhx, ↓reduceIte, List.pairwise_cons]
        refine ⟨fun y hy => ?_, ih hr⟩
        rcases (glistOrderedInsert_mem x r y).mp hy with rfl | hyr
        · exact hhx
        · exact hhd y hyr
      · simp only [hxh, hhx, ↓reduceIte]
        exact List.pairwise_cons.mpr ⟨hhd, hr⟩

theorem nlvarsAdd_idx_mem (vars : List NLVar) (idx k : Nat) :
    ∀ v ∈ nlvarsAdd vars idx k, v.param = idx ∨ ∃ v' ∈ vars, v.param = v'.param := by
  induction vars with
  | nil =>
    intro v hv
    simp [nlvarsAdd] at hv
    subst hv; exact .inl rfl
  | cons hd rest ih =>
    rcases hd with ⟨vi, vo⟩
    intro v hv
    simp only [nlvarsAdd] at hv
    by_cases h1 : idx < vi
    · simp only [h1, ↓reduceIte, List.mem_cons] at hv
      rcases hv with rfl | rfl | hrest
      · exact .inl rfl
      · exact .inr ⟨⟨vi, vo⟩, List.mem_cons_self .., rfl⟩
      · exact .inr ⟨v, List.mem_cons_of_mem _ hrest, rfl⟩
    · by_cases h2 : vi < idx
      · simp only [h1, h2, ↓reduceIte, List.mem_cons] at hv
        rcases hv with rfl | hrest
        · exact .inr ⟨⟨vi, vo⟩, List.mem_cons_self .., rfl⟩
        · rcases ih v hrest with hidx | ⟨v', hv', heq⟩
          · exact .inl hidx
          · exact .inr ⟨v', List.mem_cons_of_mem _ hv', heq⟩
      · by_cases h3 : vo < k
        · simp only [h1, h2, h3, ↓reduceIte, List.mem_cons] at hv
          rcases hv with rfl | hrest
          · exact .inr ⟨⟨vi, vo⟩, List.mem_cons_self .., rfl⟩
          · exact .inr ⟨v, List.mem_cons_of_mem _ hrest, rfl⟩
        · simp only [h1, h2, h3, ↓reduceIte, List.mem_cons] at hv
          rcases hv with rfl | hrest
          · exact .inr ⟨⟨vi, vo⟩, List.mem_cons_self .., rfl⟩
          · exact .inr ⟨v, List.mem_cons_of_mem _ hrest, rfl⟩

theorem nlAddConstGo_wf {acc : List NLEntry} {path : List Nat} {k : Nat}
    (hpath : List.Pairwise (· < ·) path) (hacc : ∀ e ∈ acc, e.WF) :
    ∀ e ∈ nlAddConstGo acc path k, e.WF := by
  induction acc with
  | nil =>
    intro e he
    simp only [nlAddConstGo, List.mem_singleton] at he
    subst he
    exact ⟨(by intro v hv; cases hv), hpath⟩
  | cons hd rest ih =>
    rcases hd with ⟨ep, ec, ev⟩
    have hhd := hacc ⟨ep, ec, ev⟩ (List.mem_cons_self ..)
    have hrest : ∀ e' ∈ rest, e'.WF := fun e' he' => hacc e' (List.mem_cons_of_mem _ he')
    intro e he
    simp only [nlAddConstGo] at he
    rcases hcmp : glistCmp path ep with _ | _ | n
    · simp only [hcmp] at he
      by_cases hck : ec < k
      · simp only [hck, ↓reduceIte, List.mem_cons] at he
        rcases he with rfl | her
        · exact ⟨hhd.1, hhd.2⟩
        · exact hrest e her
      · simp only [hck, ↓reduceIte, List.mem_cons] at he
        rcases he with rfl | her
        · exact hhd
        · exact hrest e her
    · simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | rfl | her
      · exact ⟨(by intro v hv; cases hv), hpath⟩
      · exact hhd
      · exact hrest e her
    · simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | her
      · exact hhd
      · exact ih hrest e her

theorem nlAddConst_wf {acc : List NLEntry} {path : List Nat} {k : Nat}
    (hpath : List.Pairwise (· < ·) path) (hacc : ∀ e ∈ acc, e.WF) :
    ∀ e ∈ nlAddConst acc path k, e.WF := by
  unfold nlAddConst
  rcases k with _ | _ | k
  · exact hacc
  · cases path
    · exact nlAddConstGo_wf hpath hacc
    · exact hacc
  · exact nlAddConstGo_wf hpath hacc

theorem nlAddVar_wf {acc : List NLEntry} {path : List Nat} {idx k : Nat}
    (hpath : List.Pairwise (· < ·) path) (hidx : idx ∈ path) (hacc : ∀ e ∈ acc, e.WF) :
    ∀ e ∈ nlAddVar acc path idx k, e.WF := by
  induction acc with
  | nil =>
    intro e he
    simp only [nlAddVar, List.mem_singleton] at he
    subst he
    refine ⟨fun v hv => ?_, hpath⟩
    simp only [List.mem_singleton] at hv
    subst hv; exact hidx
  | cons hd rest ih =>
    rcases hd with ⟨ep, ec, ev⟩
    have hhd := hacc ⟨ep, ec, ev⟩ (List.mem_cons_self ..)
    have hrest : ∀ e' ∈ rest, e'.WF := fun e' he' => hacc e' (List.mem_cons_of_mem _ he')
    intro e he
    simp only [nlAddVar] at he
    rcases hcmp : glistCmp path ep with _ | _ | n
    · have hep : path = ep := glistCmp_eq_zero_iff.mp hcmp
      subst hep
      simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | her
      · refine ⟨fun v hv => ?_, hhd.2⟩
        rcases nlvarsAdd_idx_mem ev idx k v hv with hvi | ⟨v', hv', hvi⟩
        · rw [hvi]; exact hidx
        · rw [hvi]; exact hhd.1 v' hv'
      · exact hrest e her
    · simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | rfl | her
      · refine ⟨fun v hv => ?_, hpath⟩
        simp only [List.mem_singleton] at hv
        subst hv; exact hidx
      · exact hhd
      · exact hrest e her
    · simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | her
      · exact hhd
      · exact ih hrest e her

theorem normalizeStep_wf (fuel : Nat) :
    ∀ (arg : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level))
      (path : List Nat) (k : Nat) (acc : List NLEntry),
      List.Pairwise (· < ·) path →
      (∀ e ∈ acc, e.WF) →
      ∀ e ∈ normalizeStep fuel arg path k acc, e.WF := by
  induction fuel with
  | zero =>
    intro arg path k acc _ hacc
    exact hacc
  | succ fuel ih =>
    intro arg path k acc hpath hacc
    cases arg with
    | inl l =>
      cases l with
      | zero => exact nlAddConst_wf hpath hacc
      | succ inner => exact ih (.inl inner) path (k + 1) acc hpath hacc
      | max a b =>
        exact ih (.inl b) path k _ hpath (ih (.inl a) path k acc hpath hacc)
      | imax u b =>
        exact ih (.inr (u, b)) path k acc hpath hacc
      | param idx =>
        simp only [normalizeStep]
        cases hins : glistOrderedInsert idx path with
        | mk f newPath =>
          cases f with
          | true =>
            have hnew_sort : List.Pairwise (· < ·) newPath := by
              have := glistOrderedInsert_pairwise idx hpath
              rwa [hins] at this
            have hidx_new : idx ∈ newPath := by
              have := (glistOrderedInsert_mem idx path idx).mpr (.inl rfl)
              rwa [hins] at this
            exact nlAddVar_wf hnew_sort hidx_new (nlAddConst_wf hpath hacc)
          | false =>
            have hidx_mem : idx ∈ path :=
              glistOrderedInsert_false_mem (by rw [hins])
            by_cases hk : k = 0
            · simp [hk]; exact hacc
            · simp [hk]; exact nlAddVar_wf hpath hidx_mem hacc
    | inr ab =>
      rcases ab with ⟨a, b⟩
      cases b with
      | zero => exact nlAddConst_wf hpath hacc
      | succ v =>
        exact ih (.inl v) path (k + 1) _ hpath (ih (.inl a) path k acc hpath hacc)
      | max v w =>
        exact ih (.inr (a, w)) path k _ hpath (ih (.inr (a, v)) path k acc hpath hacc)
      | imax v w =>
        exact ih (.inr (v, w)) path k _ hpath (ih (.inr (a, w)) path k acc hpath hacc)
      | param idx =>
        simp only [normalizeStep]
        cases hins : glistOrderedInsert idx path with
        | mk f newPath =>
          cases f with
          | true =>
            have hnew_sort : List.Pairwise (· < ·) newPath := by
              have := glistOrderedInsert_pairwise idx hpath
              rwa [hins] at this
            have hidx_new : idx ∈ newPath := by
              have := (glistOrderedInsert_mem idx path idx).mpr (.inl rfl)
              rwa [hins] at this
            exact ih (.inl a) newPath k _ hnew_sort
              (nlAddVar_wf hnew_sort hidx_new (nlAddConst_wf hpath hacc))
          | false =>
            have hidx_mem : idx ∈ path :=
              glistOrderedInsert_false_mem (by rw [hins])
            have hacc2 : ∀ e ∈ (if k = 0 then acc else nlAddVar acc path idx k), e.WF := by
              by_cases hk : k = 0
              · simp [hk]; exact hacc
              · simp [hk]; exact nlAddVar_wf hpath hidx_mem hacc
            exact ih (.inl a) path k _ hpath hacc2

theorem nlvarsSubsume_subset (xs ys : List NLVar) :
    ∀ v ∈ nlvarsSubsume xs ys, v ∈ xs := by
  induction xs, ys using nlvarsSubsume.induct with
  | case1 => intro v hv; simp [nlvarsSubsume] at hv
  | case2 x xr => intro v hv; simpa [nlvarsSubsume] using hv
  | case3 xi xo xr yi yo yr hlt ih =>
    intro v hv
    simp only [nlvarsSubsume, hlt, ↓reduceIte, List.mem_cons] at hv
    rcases hv with rfl | hvr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih v hvr)
  | case4 xi xo xr yi yo yr hlt1 hlt2 ih =>
    intro v hv
    simp only [nlvarsSubsume, hlt1, hlt2, ↓reduceIte] at hv
    exact ih v hv
  | case5 xi xo xr yi yo yr hlt1 hlt2 hlt3 ih =>
    intro v hv
    simp only [nlvarsSubsume, hlt1, hlt2, hlt3, ↓reduceIte, List.mem_cons] at hv
    rcases hv with rfl | hvr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih v hvr)
  | case6 xi xo xr yi yo yr hlt1 hlt2 hlt3 ih =>
    intro v hv
    simp only [nlvarsSubsume, hlt1, hlt2, hlt3, ↓reduceIte] at hv
    exact List.mem_cons_of_mem _ (ih v hv)

theorem nlSubsumeEntry_wf {e : NLEntry} {snap : List NLEntry} (he : e.WF) :
    (nlSubsumeEntry e snap).WF := by
  induction snap generalizing e with
  | nil => exact he
  | cons s srest ih =>
    rcases e with ⟨p1, c1, v1⟩
    rcases s with ⟨p2, c2, v2⟩
    simp only [nlSubsumeEntry]
    split
    · exact ih he
    · apply ih
      refine ⟨fun v hv => ?_, he.2⟩
      by_cases hsame : glistEqLen p1 p2 = true
      · simp only [hsame, ↓reduceIte] at hv
        exact he.1 v hv
      · simp only [hsame, ↓reduceIte] at hv
        cases v2 with
        | nil => exact he.1 v hv
        | cons _ _ => exact he.1 v (nlvarsSubsume_subset v1 _ v hv)

theorem nlSubsumptionWalk_wf {rem snap : List NLEntry} (hrem : ∀ e ∈ rem, e.WF) :
    ∀ e ∈ nlSubsumptionWalk rem snap, e.WF := by
  intro e he
  simp only [nlSubsumptionWalk, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  exact nlSubsumeEntry_wf (hrem e0 he0)

/-- **Every entry produced by `levelNormalize l` is well-formed (`NLEntry.WF`).** -/
theorem levelNormalize_wf (l : Ix.Kernel.Level) :
    ∀ e ∈ levelNormalize l, e.WF := by
  apply nlSubsumptionWalk_wf
  apply normalizeStep_wf
  · exact List.Pairwise.nil
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨(by intro v hv; cases hv), List.Pairwise.nil⟩

/-- **Unconditional soundness of `nlLe` on normalized levels.** -/
theorem levelNormalize_nlLe_sound {a b : Ix.Kernel.Level}
    (h : nlLe (levelNormalize a) (levelNormalize b) = true)
    (φ : Ix.Kernel.LevelParam → Nat) :
    evalNLEntries φ (levelNormalize a) ≤ evalNLEntries φ (levelNormalize b) :=
  nlLe_sound (fun e he => (levelNormalize_wf a e he).2) (levelNormalize_wf b) h φ

/-- Invariant that every parameter in `path` is already bounded by `evalNLEntries φ acc`
whenever `path` is active under `φ`. -/
def GuardVarsCovered (path : List Nat) (acc : List NLEntry) : Prop :=
  ∀ idx ∈ path, ∀ φ, guardActive φ path = true → φ idx ≤ evalNLEntries φ acc

theorem GuardVarsCovered.nil (acc : List NLEntry) : GuardVarsCovered [] acc := by
  intro idx hmem; cases hmem

theorem GuardVarsCovered.mono {path : List Nat} {acc acc' : List NLEntry}
    (hcov : GuardVarsCovered path acc)
    (hle : ∀ φ, evalNLEntries φ acc ≤ evalNLEntries φ acc') :
    GuardVarsCovered path acc' := by
  intro idx hmem φ hact
  exact Nat.le_trans (hcov idx hmem φ hact) (hle φ)

theorem evalNLEntries_nlAddConst {path : List Nat} {acc : List NLEntry}
    (hcov : GuardVarsCovered path acc) (φ : Ix.Kernel.LevelParam → Nat) (k : Nat) :
    evalNLEntries φ (nlAddConst acc path k) =
      Max.max (if guardActive φ path then k else 0) (evalNLEntries φ acc) := by
  unfold nlAddConst
  rcases k with _ | _ | k
  · simp
  · cases path with
    | nil => exact evalNLEntries_nlAddConstGo φ acc [] 1
    | cons p0 ps =>
      simp only
      by_cases hact : guardActive φ (p0 :: ps) = true
      · have hp0_pos : 0 < φ p0 := (guardActive_iff.mp hact) p0 (List.mem_cons_self ..)
        have hp0_le : φ p0 ≤ evalNLEntries φ acc := hcov p0 (List.mem_cons_self ..) φ hact
        simp [hact]; omega
      · simp [hact]
  · exact evalNLEntries_nlAddConstGo φ acc path (k + 2)

theorem normFuel_succ (inner : Ix.Kernel.Level) :
    normFuel (.inl inner) < normFuel (.inl (.succ inner)) := by
  simp only [normFuel, levelDepth]
  nlinarith

theorem normFuel_max_left (a b : Ix.Kernel.Level) :
    normFuel (.inl a) < normFuel (.inl (.max a b)) := by
  simp only [normFuel, levelDepth]
  have : levelDepth a < Max.max (levelDepth a) (levelDepth b) + 1 := by omega
  nlinarith

theorem normFuel_max_right (a b : Ix.Kernel.Level) :
    normFuel (.inl b) < normFuel (.inl (.max a b)) := by
  simp only [normFuel, levelDepth]
  have : levelDepth b < Max.max (levelDepth a) (levelDepth b) + 1 := by omega
  nlinarith

theorem normFuel_imax (u b : Ix.Kernel.Level) :
    normFuel (.inr (u, b)) < normFuel (.inl (.imax u b)) := by
  simp only [normFuel, levelDepth]
  have hb : levelDepth b ≤ Max.max (levelDepth u) (levelDepth b) := Nat.le_max_right _ _
  nlinarith

theorem normFuel_inr_succ_a (a v : Ix.Kernel.Level) :
    normFuel (.inl a) < normFuel (.inr (a, .succ v)) := by
  simp only [normFuel, levelDepth]
  have ha : levelDepth a ≤ Max.max (levelDepth a) (levelDepth v + 1) := Nat.le_max_left _ _
  nlinarith

theorem normFuel_inr_succ_v (a v : Ix.Kernel.Level) :
    normFuel (.inl v) < normFuel (.inr (a, .succ v)) := by
  simp only [normFuel, levelDepth]
  have hv : levelDepth v < Max.max (levelDepth a) (levelDepth v + 1) := by omega
  nlinarith

theorem normFuel_inr_max_left (a v w : Ix.Kernel.Level) :
    normFuel (.inr (a, v)) < normFuel (.inr (a, .max v w)) := by
  simp only [normFuel, levelDepth]
  let m1 := Max.max (levelDepth a) (levelDepth v) + 1
  let m2 := Max.max (levelDepth a) (Max.max (levelDepth v) (levelDepth w) + 1) + 1
  have hm : m1 ≤ m2 := by omega
  have hmul : 2 * m1 * (m1 + 1) ≤ 2 * m2 * (m2 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm) (by omega)
  dsimp only [m1, m2] at hmul
  omega

theorem normFuel_inr_max_right (a v w : Ix.Kernel.Level) :
    normFuel (.inr (a, w)) < normFuel (.inr (a, .max v w)) := by
  simp only [normFuel, levelDepth]
  let m1 := Max.max (levelDepth a) (levelDepth w) + 1
  let m2 := Max.max (levelDepth a) (Max.max (levelDepth v) (levelDepth w) + 1) + 1
  have hm : m1 ≤ m2 := by omega
  have hmul : 2 * m1 * (m1 + 1) ≤ 2 * m2 * (m2 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm) (by omega)
  dsimp only [m1, m2] at hmul
  omega

theorem normFuel_inr_imax_right (a v w : Ix.Kernel.Level) :
    normFuel (.inr (a, w)) < normFuel (.inr (a, .imax v w)) := by
  simp only [normFuel, levelDepth]
  let m1 := Max.max (levelDepth a) (levelDepth w) + 1
  let m2 := Max.max (levelDepth a) (Max.max (levelDepth v) (levelDepth w) + 1) + 1
  have hm : m1 ≤ m2 := by omega
  have hmul : 2 * m1 * (m1 + 1) ≤ 2 * m2 * (m2 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm) (by omega)
  dsimp only [m1, m2] at hmul
  omega

theorem normFuel_inr_imax_vw (a v w : Ix.Kernel.Level) :
    normFuel (.inr (v, w)) < normFuel (.inr (a, .imax v w)) := by
  simp only [normFuel, levelDepth]
  have hm : Max.max (levelDepth v) (levelDepth w) + 1 ≤
      Max.max (levelDepth a) (Max.max (levelDepth v) (levelDepth w) + 1) := Nat.le_max_right _ _
  have hw : levelDepth w ≤ Max.max (levelDepth v) (levelDepth w) := Nat.le_max_right _ _
  nlinarith

theorem normFuel_inr_param (a : Ix.Kernel.Level) (idx : Nat) :
    normFuel (.inl a) < normFuel (.inr (a, .param idx)) := by
  simp only [normFuel, levelDepth]
  have ha : levelDepth a ≤ Max.max (levelDepth a) 0 := Nat.le_max_left _ _
  nlinarith

/-- Semantic target of `normalizeStep` on `.inl l` vs `.inr (a, b)`. -/
def normTargetEval (φ : Ix.Kernel.LevelParam → Nat) :
    Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level) → Nat
  | .inl l => Ix.Kernel.Level.eval φ l
  | .inr (a, b) => Ix.Kernel.Level.eval φ (.imax a b)

/-- **`normalizeStep` preserves the guard-coverage invariant and evaluates to
`Max.max (if guardActive φ path then normTargetEval φ arg + k else 0) (evalNLEntries φ acc)`
for every `fuel ≥ normFuel arg`.** -/
theorem evalNLEntries_normalizeStep :
    ∀ (fuel : Nat) (arg : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level))
      (path : List Nat) (k : Nat) (acc : List NLEntry),
      normFuel arg ≤ fuel →
      GuardVarsCovered path acc →
      (∀ φ, evalNLEntries φ (normalizeStep fuel arg path k acc) =
        Max.max (if guardActive φ path then normTargetEval φ arg + k else 0)
          (evalNLEntries φ acc)) ∧
      GuardVarsCovered path (normalizeStep fuel arg path k acc) := by
  intro fuel
  induction fuel with
  | zero =>
    intro arg path k acc hfuel
    cases arg with
    | inl l => simp [normFuel] at hfuel
    | inr ab => simp [normFuel] at hfuel
  | succ fuel ih =>
    intro arg path k acc hfuel hcov
    have h_step : ∀ φ, evalNLEntries φ (normalizeStep (fuel + 1) arg path k acc) =
        Max.max (if guardActive φ path then normTargetEval φ arg + k else 0)
          (evalNLEntries φ acc) := by
      intro φ
      cases arg with
      | inl l =>
        cases l with
        | zero =>
          simp [normalizeStep, normTargetEval, Ix.Kernel.Level.eval,
            evalNLEntries_nlAddConst hcov]
        | succ inner =>
          have hf : normFuel (.inl inner) ≤ fuel := by
            have := normFuel_succ inner; omega
          simp only [normalizeStep, (ih (.inl inner) path (k + 1) acc hf hcov).1 φ,
            normTargetEval, Ix.Kernel.Level.eval]
          by_cases hp : guardActive φ path = true <;> simp [hp] <;> omega
        | max a b =>
          have hfa : normFuel (.inl a) ≤ fuel := by
            have := normFuel_max_left a b; omega
          have hfb : normFuel (.inl b) ≤ fuel := by
            have := normFuel_max_right a b; omega
          obtain ⟨heval_a, hcov_a⟩ := ih (.inl a) path k acc hfa hcov
          obtain ⟨heval_b, _⟩ := ih (.inl b) path k _ hfb hcov_a
          simp only [normalizeStep, heval_b φ, heval_a φ, normTargetEval, Ix.Kernel.Level.eval]
          by_cases hp : guardActive φ path = true <;> simp [hp] <;> omega
        | imax u b =>
          have hf : normFuel (.inr (u, b)) ≤ fuel := by
            have := normFuel_imax u b; omega
          simp only [normalizeStep, (ih (.inr (u, b)) path k acc hf hcov).1 φ,
            normTargetEval]
        | param idx =>
          simp only [normalizeStep, normTargetEval, Ix.Kernel.Level.eval]
          cases hins : glistOrderedInsert idx path with
          | mk f newPath =>
            cases f with
            | true =>
              simp only [evalNLEntries_nlAddVar, evalNLEntries_nlAddConst hcov]
              have hact_new : guardActive φ newPath = (decide (0 < φ idx) && guardActive φ path) := by
                apply Bool.eq_iff_iff.mpr
                simp only [guardActive_iff, Bool.and_eq_true, decide_eq_true_eq]
                constructor
                · intro h
                  refine ⟨h idx ?_, fun y hy => h y ?_⟩
                  · have := (glistOrderedInsert_mem idx path idx).mpr (.inl rfl)
                    rwa [hins] at this
                  · have := (glistOrderedInsert_mem idx path y).mpr (.inr hy)
                    rwa [hins] at this
                · rintro ⟨hidx, hp⟩ y hy
                  have hy' : y ∈ (glistOrderedInsert idx path).2 := by rwa [hins]
                  rcases (glistOrderedInsert_mem idx path y).mp hy' with rfl | hyp
                  · exact hidx
                  · exact hp y hyp
              rw [hact_new]
              by_cases hp : guardActive φ path = true <;> by_cases hx : 0 < φ idx <;>
                simp [hp, hx] <;> omega
            | false =>
              have hidx_mem : idx ∈ path := glistOrderedInsert_false_mem (by rw [hins])
              by_cases hk : k = 0
              · subst hk
                simp only [↓reduceIte, Nat.add_zero]
                by_cases hp : guardActive φ path = true
                · have hle := hcov idx hidx_mem φ hp
                  simp [hp]; omega
                · simp [hp]
              · simp [hk, evalNLEntries_nlAddVar]
      | inr ab =>
        rcases ab with ⟨a, b⟩
        cases b with
        | zero =>
          simp [normalizeStep, normTargetEval, Ix.Kernel.Level.eval,
            evalNLEntries_nlAddConst hcov]
        | succ v =>
          have hfa : normFuel (.inl a) ≤ fuel := by
            have := normFuel_inr_succ_a a v; omega
          have hfv : normFuel (.inl v) ≤ fuel := by
            have := normFuel_inr_succ_v a v; omega
          obtain ⟨heval_a, hcov_a⟩ := ih (.inl a) path k acc hfa hcov
          obtain ⟨heval_v, _⟩ := ih (.inl v) path (k + 1) _ hfv hcov_a
          simp only [normalizeStep, heval_v φ, heval_a φ, normTargetEval, Ix.Kernel.Level.eval]
          by_cases hp : guardActive φ path = true <;> simp [hp] <;> omega
        | max v w =>
          have hfv : normFuel (.inr (a, v)) ≤ fuel := by
            have := normFuel_inr_max_left a v w; omega
          have hfw : normFuel (.inr (a, w)) ≤ fuel := by
            have := normFuel_inr_max_right a v w; omega
          obtain ⟨heval_v, hcov_v⟩ := ih (.inr (a, v)) path k acc hfv hcov
          obtain ⟨heval_w, _⟩ := ih (.inr (a, w)) path k _ hfw hcov_v
          simp only [normalizeStep, heval_w φ, heval_v φ, normTargetEval, Ix.Kernel.Level.eval]
          by_cases hp : guardActive φ path = true <;>
            by_cases hv0 : Ix.Kernel.Level.eval φ v = 0 <;>
            by_cases hw0 : Ix.Kernel.Level.eval φ w = 0 <;>
            simp [hp, hv0, hw0] <;> omega
        | imax v w =>
          have hfaw : normFuel (.inr (a, w)) ≤ fuel := by
            have := normFuel_inr_imax_right a v w; omega
          have hfvw : normFuel (.inr (v, w)) ≤ fuel := by
            have := normFuel_inr_imax_vw a v w; omega
          obtain ⟨heval_aw, hcov_aw⟩ := ih (.inr (a, w)) path k acc hfaw hcov
          obtain ⟨heval_vw, _⟩ := ih (.inr (v, w)) path k _ hfvw hcov_aw
          simp only [normalizeStep, heval_vw φ, heval_aw φ, normTargetEval, Ix.Kernel.Level.eval]
          by_cases hp : guardActive φ path = true <;>
            by_cases hw0 : Ix.Kernel.Level.eval φ w = 0 <;>
            by_cases hv0 : Ix.Kernel.Level.eval φ v = 0 <;>
            simp [hp, hw0, hv0] <;> omega
        | param idx =>
          have hfa : normFuel (.inl a) ≤ fuel := by
            have := normFuel_inr_param a idx; omega
          simp only [normalizeStep, normTargetEval, Ix.Kernel.Level.eval]
          cases hins : glistOrderedInsert idx path with
          | mk f newPath =>
            cases f with
            | true =>
              let acc1 := nlAddVar (nlAddConst acc path k) newPath idx k
              have hact_new : ∀ ψ, guardActive ψ newPath = (decide (0 < ψ idx) && guardActive ψ path) := by
                intro ψ
                apply Bool.eq_iff_iff.mpr
                simp only [guardActive_iff, Bool.and_eq_true, decide_eq_true_eq]
                constructor
                · intro h
                  refine ⟨h idx ?_, fun y hy => h y ?_⟩
                  · have := (glistOrderedInsert_mem idx path idx).mpr (.inl rfl)
                    rwa [hins] at this
                  · have := (glistOrderedInsert_mem idx path y).mpr (.inr hy)
                    rwa [hins] at this
                · rintro ⟨hidx, hp⟩ y hy
                  have hy' : y ∈ (glistOrderedInsert idx path).2 := by rwa [hins]
                  rcases (glistOrderedInsert_mem idx path y).mp hy' with rfl | hyp
                  · exact hidx
                  · exact hp y hyp
              have hcov_new : GuardVarsCovered newPath acc1 := by
                intro y hy ψ hactψ
                have hy' : y ∈ (glistOrderedInsert idx path).2 := by rwa [hins]
                have hboth := hact_new ψ
                rw [hactψ] at hboth
                have hpψ : guardActive ψ path = true := by
                  revert hboth
                  cases guardActive ψ path <;> simp
                simp only [acc1, evalNLEntries_nlAddVar, evalNLEntries_nlAddConst hcov, hactψ, ↓reduceIte]
                rcases (glistOrderedInsert_mem idx path y).mp hy' with rfl | hyp
                · omega
                · have := hcov y hyp ψ hpψ
                  omega
              obtain ⟨heval_a, _⟩ := ih (.inl a) newPath k acc1 hfa hcov_new
              simp only [heval_a φ, acc1, evalNLEntries_nlAddVar, evalNLEntries_nlAddConst hcov,
                normTargetEval, hact_new φ]
              by_cases hp : guardActive φ path = true <;>
                by_cases hx : 0 < φ idx <;>
                by_cases hx0 : φ idx = 0 <;>
                simp [hp, hx, hx0] <;> omega
            | false =>
              have hidx_mem : idx ∈ path := glistOrderedInsert_false_mem (by rw [hins])
              have hcov2 : GuardVarsCovered path (if k = 0 then acc else nlAddVar acc path idx k) := by
                apply hcov.mono
                intro ψ
                by_cases hk : k = 0
                · simp [hk]
                · simp [hk, evalNLEntries_nlAddVar]
              obtain ⟨heval_a, _⟩ := ih (.inl a) path k (if k = 0 then acc else nlAddVar acc path idx k) hfa hcov2
              simp only [heval_a φ, normTargetEval]
              by_cases hk : k = 0
              · subst hk
                simp only [↓reduceIte, Nat.add_zero]
                by_cases hp : guardActive φ path = true
                · have hpos : 0 < φ idx := (guardActive_iff.mp hp) idx hidx_mem
                  have hle : φ idx ≤ evalNLEntries φ acc := hcov idx hidx_mem φ hp
                  have hne0 : ¬ (φ idx = 0) := by omega
                  simp [hp, hne0]; omega
                · simp [hp]
              · simp only [hk, ↓reduceIte, evalNLEntries_nlAddVar]
                by_cases hp : guardActive φ path = true
                · have hpos : 0 < φ idx := (guardActive_iff.mp hp) idx hidx_mem
                  have hne0 : ¬ (φ idx = 0) := by omega
                  simp [hp, hne0]; omega
                · simp [hp]
    refine ⟨h_step, hcov.mono fun φ => ?_⟩
    rw [h_step φ]
    exact Nat.le_max_right _ _

/-- **`normalizeAux l [] 0 [⟨[], 0, []⟩]` evaluates to `Ix.Kernel.Level.eval φ l`
under every valuation `φ`.** -/
theorem evalNLEntries_normalizeAux_seed (φ : Ix.Kernel.LevelParam → Nat) (l : Ix.Kernel.Level) :
    evalNLEntries φ (normalizeAux l [] 0 [⟨[], 0, []⟩]) = Ix.Kernel.Level.eval φ l := by
  have hcov0 : GuardVarsCovered [] [⟨[], 0, []⟩] := GuardVarsCovered.nil _
  have h := (evalNLEntries_normalizeStep (normFuel (.inl l)) (.inl l) [] 0 [⟨[], 0, []⟩]
    (Nat.le_refl _) hcov0).1 φ
  simpa [normalizeAux, normTargetEval, guardActive, evalNLEntries, NLEntry.eval, evalNLVars] using h

theorem evalNLVars_nlvarsSubsume_le (φ : Ix.Kernel.LevelParam → Nat) (xs ys : List NLVar) :
    evalNLVars φ (nlvarsSubsume xs ys) ≤ evalNLVars φ xs := by
  have H : ∀ v ∈ nlvarsSubsume xs ys, v.eval φ ≤ evalNLVars φ xs :=
    fun v hv => le_evalNLVars_of_mem (nlvarsSubsume_subset xs ys v hv)
  suffices ∀ zs : List NLVar, (∀ v ∈ zs, v.eval φ ≤ evalNLVars φ xs) → evalNLVars φ zs ≤ evalNLVars φ xs from
    this (nlvarsSubsume xs ys) H
  intro zs hzs
  induction zs with
  | nil => simp [evalNLVars]
  | cons v rest ih =>
    simp only [evalNLVars]
    have h1 := hzs v (List.mem_cons_self ..)
    have h2 := ih (fun v' hv' => hzs v' (List.mem_cons_of_mem _ hv'))
    omega

theorem nlSubsumeEntry_eval_le (φ : Ix.Kernel.LevelParam → Nat) (e : NLEntry) (snap : List NLEntry) :
    (nlSubsumeEntry e snap).eval φ ≤ e.eval φ := by
  induction snap generalizing e with
  | nil => exact Nat.le_refl _
  | cons s srest ih =>
    rcases e with ⟨p1, c1, v1⟩
    rcases s with ⟨p2, c2, v2⟩
    cases v2 with
    | nil =>
      simp only [nlSubsumeEntry]
      split
      · exact ih ⟨p1, c1, v1⟩
      · apply Nat.le_trans (ih _)
        simp only [NLEntry.eval, ite_self]
        by_cases hp1 : guardActive φ p1 = true
        · simp only [hp1, ↓reduceIte]
          have hc_le :
              (if c1 = 0 then 0
               else if (if glistEqLen p1 p2 then true else decide (c2 < c1)) && true then c1 else 0) ≤ c1 := by
            split_ifs <;> omega
          omega
        · simp [hp1]
    | cons w0 wr =>
      simp only [nlSubsumeEntry]
      split
      · exact ih ⟨p1, c1, v1⟩
      · apply Nat.le_trans (ih _)
        simp only [NLEntry.eval]
        by_cases hp1 : guardActive φ p1 = true
        · simp only [hp1, ↓reduceIte]
          have hc_le :
              (if c1 = 0 then 0
               else if (if glistEqLen p1 p2 then true else decide (c2 < c1)) &&
                 decide (nlvarsMaxOffset v1 + 1 < c1) then c1 else 0) ≤ c1 := by
            split_ifs <;> omega
          have hv_le :
              evalNLVars φ (if glistEqLen p1 p2 then v1 else nlvarsSubsume v1 (w0 :: wr)) ≤
              evalNLVars φ v1 := by
            split
            · exact Nat.le_refl _
            · exact evalNLVars_nlvarsSubsume_le φ v1 (w0 :: wr)
          omega
        · simp [hp1]

theorem evalNLEntries_nlSubsumptionWalk_le (φ : Ix.Kernel.LevelParam → Nat)
    (rem snap : List NLEntry) :
    evalNLEntries φ (nlSubsumptionWalk rem snap) ≤ evalNLEntries φ rem := by
  induction rem with
  | nil => simp [nlSubsumptionWalk, evalNLEntries]
  | cons e rest ih =>
    simp only [nlSubsumptionWalk, List.map_cons, evalNLEntries] at ih ⊢
    have h1 := nlSubsumeEntry_eval_le φ e snap
    omega


theorem glistSubset_length_le {xs ys : List Nat} (h : glistSubset xs ys = true) :
    xs.length ≤ ys.length := by
  induction xs, ys using glistSubset.induct with
  | case1 => simp
  | case2 x xr => simp [glistSubset] at h
  | case3 x xr y yr hxy => simp [glistSubset, hxy] at h
  | case4 x xr y yr hxy hyx ih =>
    simp only [glistSubset, hxy, hyx, ↓reduceIte] at h
    have := ih h
    simp only [List.length_cons] at this ⊢
    omega
  | case5 x xr y yr hxy hyx ih =>
    simp only [glistSubset, hxy, hyx, ↓reduceIte] at h
    have := ih h
    simp only [List.length_cons]
    omega

theorem glistSubset_length_lt_of_eqLen_false {p2 p1 : List Nat}
    (hsub : glistSubset p2 p1 = true) (hne : glistEqLen p1 p2 = false) :
    p2.length < p1.length := by
  have hle := glistSubset_length_le hsub
  have hlen_ne : p1.length ≠ p2.length := fun h => by
    rw [glistEqLen_iff.mpr h] at hne
    cases hne
  omega

theorem nlvarsSubsume_mem_or_dominated {xs ys : List NLVar} {v : NLVar} (hv : v ∈ xs) :
    v ∈ nlvarsSubsume xs ys ∨ ∃ w ∈ ys, w.param = v.param ∧ v.offset ≤ w.offset := by
  induction xs, ys using nlvarsSubsume.induct with
  | case1 => cases hv
  | case2 x xr => simp only [nlvarsSubsume]; exact .inl hv
  | case3 xi xo xr yi yo yr hlt ih =>
    simp only [nlvarsSubsume, hlt, ↓reduceIte]
    rcases List.mem_cons.mp hv with rfl | hvr
    · exact .inl (List.mem_cons_self ..)
    · rcases ih hvr with hmem | hdom
      · exact .inl (List.mem_cons_of_mem _ hmem)
      · exact .inr hdom
  | case4 xi xo xr yi yo yr hlt1 hlt2 ih =>
    simp only [nlvarsSubsume, hlt1, hlt2, ↓reduceIte]
    rcases ih hv with hmem | ⟨w, hw, hidx, hoff⟩
    · exact .inl hmem
    · exact .inr ⟨w, List.mem_cons_of_mem _ hw, hidx, hoff⟩
  | case5 xi xo xr yi yo yr hlt1 hlt2 hlt3 ih =>
    simp only [nlvarsSubsume, hlt1, hlt2, hlt3, ↓reduceIte]
    rcases List.mem_cons.mp hv with rfl | hvr
    · exact .inl (List.mem_cons_self ..)
    · rcases ih hvr with hmem | ⟨w, hw, hidx, hoff⟩
      · exact .inl (List.mem_cons_of_mem _ hmem)
      · exact .inr ⟨w, List.mem_cons_of_mem _ hw, hidx, hoff⟩
  | case6 xi xo xr yi yo yr hlt1 hlt2 hlt3 ih =>
    simp only [nlvarsSubsume, hlt1, hlt2, hlt3, ↓reduceIte]
    rcases List.mem_cons.mp hv with rfl | hvr
    · refine .inr ⟨⟨yi, yo⟩, List.mem_cons_self .., ?_, ?_⟩
      · dsimp only; omega
      · dsimp only; omega
    · rcases ih hvr with hmem | ⟨w, hw, hidx, hoff⟩
      · exact .inl hmem
      · exact .inr ⟨w, List.mem_cons_of_mem _ hw, hidx, hoff⟩

theorem exists_mem_nlvarsMaxOffset {vars : List NLVar} (hne : vars ≠ []) :
    ∃ v ∈ vars, v.offset = nlvarsMaxOffset vars := by
  induction vars with
  | nil => contradiction
  | cons v rest ih =>
    rcases v with ⟨vi, vo⟩
    cases rest with
    | nil =>
      refine ⟨⟨vi, vo⟩, List.mem_cons_self .., ?_⟩
      change vo = if 0 < vo then vo else 0
      split_ifs <;> omega
    | cons r0 rr =>
      obtain ⟨w, hw, hwo⟩ := ih (List.cons_ne_nil r0 rr)
      rw [nlvarsMaxOffset]
      by_cases hlt : nlvarsMaxOffset (r0 :: rr) < vo
      · exact ⟨⟨vi, vo⟩, List.mem_cons_self .., by simp [hlt]⟩
      · exact ⟨w, List.mem_cons_of_mem _ hw, by simp [hlt, hwo]⟩

/-- Constant-1 invariant maintained by `nlAddConst` and `nlAddVar`: an entry has
`constPart = 1` only if its guard path is empty or its variable list is non-empty. -/
def NLEntry.ConstValid (e : NLEntry) : Prop :=
  e.constPart = 1 → e.guards = [] ∨ e.vars ≠ []

theorem nlvarsAdd_ne_nil (vars : List NLVar) (idx k : Nat) :
    nlvarsAdd vars idx k ≠ [] := by
  cases vars with
  | nil => simp [nlvarsAdd]
  | cons v rest =>
    rcases v with ⟨vi, vo⟩
    simp only [nlvarsAdd]
    split_ifs <;> simp

theorem nlAddConstGo_constValid {acc : List NLEntry} {path : List Nat} {k : Nat}
    (hk : k ≠ 1 ∨ path = []) (hacc : ∀ e ∈ acc, e.ConstValid) :
    ∀ e ∈ nlAddConstGo acc path k, e.ConstValid := by
  induction acc with
  | nil =>
    intro e he h1
    simp only [nlAddConstGo, List.mem_singleton] at he
    subst he
    rcases hk with hne | rfl
    · exact absurd h1 hne
    · exact .inl rfl
  | cons hd rest ih =>
    rcases hd with ⟨ep, ec, ev⟩
    have hhd := hacc ⟨ep, ec, ev⟩ (List.mem_cons_self ..)
    have hrest : ∀ e' ∈ rest, e'.ConstValid := fun e' he' => hacc e' (List.mem_cons_of_mem _ he')
    intro e he
    simp only [nlAddConstGo] at he
    rcases hcmp : glistCmp path ep with _ | _ | n
    · have hep : path = ep := glistCmp_eq_zero_iff.mp hcmp
      subst hep
      simp only [hcmp] at he
      by_cases hck : ec < k
      · simp only [hck, ↓reduceIte, List.mem_cons] at he
        rcases he with rfl | her
        · intro h1
          rcases hk with hne | rfl
          · exact absurd h1 hne
          · exact .inl rfl
        · exact hrest e her
      · simp only [hck, ↓reduceIte, List.mem_cons] at he
        rcases he with rfl | her
        · exact hhd
        · exact hrest e her
    · simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | rfl | her
      · intro h1
        rcases hk with hne | rfl
        · exact absurd h1 hne
        · exact .inl rfl
      · exact hhd
      · exact hrest e her
    · simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | her
      · exact hhd
      · exact ih hrest e her

theorem nlAddConst_constValid {acc : List NLEntry} {path : List Nat} {k : Nat}
    (hacc : ∀ e ∈ acc, e.ConstValid) :
    ∀ e ∈ nlAddConst acc path k, e.ConstValid := by
  unfold nlAddConst
  rcases k with _ | _ | k
  · exact hacc
  · cases path with
    | nil => exact nlAddConstGo_constValid (.inr rfl) hacc
    | cons _ _ => exact hacc
  · exact nlAddConstGo_constValid (.inl (by omega)) hacc

theorem nlAddVar_constValid {acc : List NLEntry} {path : List Nat} {idx k : Nat}
    (hacc : ∀ e ∈ acc, e.ConstValid) :
    ∀ e ∈ nlAddVar acc path idx k, e.ConstValid := by
  induction acc with
  | nil =>
    intro e he h1
    simp only [nlAddVar, List.mem_singleton] at he
    subst he
    simp at h1
  | cons hd rest ih =>
    rcases hd with ⟨ep, ec, ev⟩
    have hhd := hacc ⟨ep, ec, ev⟩ (List.mem_cons_self ..)
    have hrest : ∀ e' ∈ rest, e'.ConstValid := fun e' he' => hacc e' (List.mem_cons_of_mem _ he')
    intro e he
    simp only [nlAddVar] at he
    rcases hcmp : glistCmp path ep with _ | _ | n
    · simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | her
      · intro _
        exact .inr (nlvarsAdd_ne_nil ev idx k)
      · exact hrest e her
    · simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | rfl | her
      · intro h1; simp at h1
      · exact hhd
      · exact hrest e her
    · simp only [hcmp, List.mem_cons] at he
      rcases he with rfl | her
      · exact hhd
      · exact ih hrest e her

theorem normalizeStep_constValid (fuel : Nat) :
    ∀ (arg : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level))
      (path : List Nat) (k : Nat) (acc : List NLEntry),
      (∀ e ∈ acc, e.ConstValid) →
      ∀ e ∈ normalizeStep fuel arg path k acc, e.ConstValid := by
  induction fuel with
  | zero =>
    intro arg path k acc hacc
    exact hacc
  | succ fuel ih =>
    intro arg path k acc hacc
    cases arg with
    | inl l =>
      cases l with
      | zero => exact nlAddConst_constValid hacc
      | succ inner => exact ih (.inl inner) path (k + 1) acc hacc
      | max a b =>
        exact ih (.inl b) path k _ (ih (.inl a) path k acc hacc)
      | imax u b =>
        exact ih (.inr (u, b)) path k acc hacc
      | param idx =>
        simp only [normalizeStep]
        cases glistOrderedInsert idx path with
        | mk f newPath =>
          cases f with
          | true => exact nlAddVar_constValid (nlAddConst_constValid hacc)
          | false =>
            by_cases hk : k = 0
            · simp [hk]; exact hacc
            · simp [hk]; exact nlAddVar_constValid hacc
    | inr ab =>
      rcases ab with ⟨a, b⟩
      cases b with
      | zero => exact nlAddConst_constValid hacc
      | succ v =>
        exact ih (.inl v) path (k + 1) _ (ih (.inl a) path k acc hacc)
      | max v w =>
        exact ih (.inr (a, w)) path k _ (ih (.inr (a, v)) path k acc hacc)
      | imax v w =>
        exact ih (.inr (v, w)) path k _ (ih (.inr (a, w)) path k acc hacc)
      | param idx =>
        simp only [normalizeStep]
        cases glistOrderedInsert idx path with
        | mk f newPath =>
          cases f with
          | true =>
            exact ih (.inl a) newPath k _ (nlAddVar_constValid (nlAddConst_constValid hacc))
          | false =>
            have hacc2 : ∀ e ∈ (if k = 0 then acc else nlAddVar acc path idx k), e.ConstValid := by
              by_cases hk : k = 0
              · simp [hk]; exact hacc
              · simp [hk]; exact nlAddVar_constValid hacc
            exact ih (.inl a) path k _ hacc2

theorem nlSubsumeEntry_var_le {φ : Ix.Kernel.LevelParam → Nat}
    {snap srest : List NLEntry} {p1 : List Nat} {c1 : Nat} {v1 : List NLVar}
    {M : Nat}
    (hp1_sort : List.Pairwise (· < ·) p1)
    (hp1_act : guardActive φ p1 = true)
    (hsnap_wf : ∀ s ∈ snap, s.WF)
    (hsrest_sub : ∀ s ∈ srest, s ∈ snap)
    (h_short : ∀ s ∈ snap, s.guards.length < p1.length → s.eval φ ≤ M) :
    ∀ v ∈ v1, v.eval φ ≤ Max.max ((nlSubsumeEntry ⟨p1, c1, v1⟩ srest).eval φ) M := by
  induction srest generalizing c1 v1 with
  | nil =>
    intro v hv
    have hv_le : v.eval φ ≤ evalNLVars φ v1 := le_evalNLVars_of_mem hv
    simp only [nlSubsumeEntry, NLEntry.eval, hp1_act, ↓reduceIte]
    omega
  | cons s sr ih =>
    rcases s with ⟨p2, c2, v2⟩
    have hs_mem : ⟨p2, c2, v2⟩ ∈ snap := hsrest_sub ⟨p2, c2, v2⟩ (List.mem_cons_self ..)
    have hs_wf : (⟨p2, c2, v2⟩ : NLEntry).WF := hsnap_wf ⟨p2, c2, v2⟩ hs_mem
    have hsr_sub : ∀ s' ∈ sr, s' ∈ snap := fun s' hs' => hsrest_sub s' (List.mem_cons_of_mem _ hs')
    intro v hv
    simp only [nlSubsumeEntry]
    by_cases hsub : glistSubset p2 p1 = true
    · simp only [hsub, not_true_eq_false, ↓reduceIte]
      have hp2_act : guardActive φ p2 = true :=
        guardActive_of_subset (glistSubset_mem hs_wf.2 hp1_sort hsub) hp1_act
      by_cases hsame : glistEqLen p1 p2 = true
      · simp only [hsame, ↓reduceIte]
        exact ih hsr_sub v hv
      · simp only [Bool.not_eq_true] at hsame
        simp only [hsame, Bool.false_eq_true, ↓reduceIte]
        cases v2 with
        | nil =>
          exact ih hsr_sub v hv
        | cons w0 wr =>
          rcases nlvarsSubsume_mem_or_dominated (ys := w0 :: wr) hv with hmem | ⟨w, hw, hidx, hoff⟩
          · exact ih hsr_sub v hmem
          · have hlt_len : p2.length < p1.length := glistSubset_length_lt_of_eqLen_false hsub hsame
            have hs_le : (⟨p2, c2, w0 :: wr⟩ : NLEntry).eval φ ≤ M := h_short _ hs_mem hlt_len
            have hw_le : w.eval φ ≤ evalNLVars φ (w0 :: wr) := le_evalNLVars_of_mem hw
            have hvw : v.eval φ ≤ w.eval φ := by
              unfold NLVar.eval; rw [hidx]; omega
            simp only [NLEntry.eval, hp2_act, ↓reduceIte] at hs_le
            omega
    · simp only [Bool.not_eq_true] at hsub
      simp only [hsub, Bool.not_false, ↓reduceIte]
      exact ih hsr_sub v hv

theorem evalNLVars_le_of_forall {φ : Ix.Kernel.LevelParam → Nat} {vars : List NLVar} {B : Nat}
    (h : ∀ v ∈ vars, v.eval φ ≤ B) : evalNLVars φ vars ≤ B := by
  induction vars with
  | nil => simp [evalNLVars]
  | cons v rest ih =>
    simp only [evalNLVars]
    have h1 := h v (List.mem_cons_self ..)
    have h2 := ih (fun v' hv' => h v' (List.mem_cons_of_mem _ hv'))
    omega

theorem nlSubsumeEntry_const_le {φ : Ix.Kernel.LevelParam → Nat}
    {snap srest : List NLEntry} {p1 : List Nat} {c0 c1 : Nat} {v0 v1 : List NLVar}
    {M : Nat}
    (he0_wf : (⟨p1, c0, v0⟩ : NLEntry).WF)
    (he0_cv : (⟨p1, c0, v0⟩ : NLEntry).ConstValid)
    (hp1_act : guardActive φ p1 = true)
    (hc1_eq : c1 = c0 ∨ c1 = 0)
    (hv1_sub : ∀ v ∈ v1, v ∈ v0)
    (hv0_le : evalNLVars φ v0 ≤ M)
    (hsnap_wf : ∀ s ∈ snap, s.WF)
    (hsrest_sub : ∀ s ∈ srest, s ∈ snap)
    (h_short : ∀ s ∈ snap, s.guards.length < p1.length → s.eval φ ≤ M) :
    c1 ≤ Max.max ((nlSubsumeEntry ⟨p1, c1, v1⟩ srest).eval φ) M := by
  induction srest generalizing c1 v1 with
  | nil =>
    simp only [nlSubsumeEntry, NLEntry.eval, hp1_act, ↓reduceIte]
    omega
  | cons s sr ih =>
    rcases s with ⟨p2, c2, v2⟩
    have hs_mem : ⟨p2, c2, v2⟩ ∈ snap := hsrest_sub ⟨p2, c2, v2⟩ (List.mem_cons_self ..)
    have hs_wf : (⟨p2, c2, v2⟩ : NLEntry).WF := hsnap_wf ⟨p2, c2, v2⟩ hs_mem
    have hsr_sub : ∀ s' ∈ sr, s' ∈ snap := fun s' hs' => hsrest_sub s' (List.mem_cons_of_mem _ hs')
    simp only [nlSubsumeEntry]
    by_cases hsub : glistSubset p2 p1 = true
    · simp only [hsub, not_true_eq_false, ↓reduceIte]
      have hp2_act : guardActive φ p2 = true :=
        guardActive_of_subset (glistSubset_mem hs_wf.2 he0_wf.2 hsub) hp1_act
      by_cases hc1_zero : c1 = 0
      · omega
      · simp only [hc1_zero, ↓reduceIte]
        by_cases hsame : glistEqLen p1 p2 = true
        · cases v2 with
          | nil =>
            simp only [hsame, ↓reduceIte, Bool.and_self]
            exact ih hc1_eq hv1_sub hsr_sub
          | cons w0 wr =>
            simp only [hsame, ↓reduceIte, Bool.true_and]
            by_cases hor2 : decide (nlvarsMaxOffset v1 + 1 < c1) = true
            · simp only [hor2, ↓reduceIte]
              exact ih hc1_eq hv1_sub hsr_sub
            · simp only [Bool.not_eq_true] at hor2
              simp only [decide_eq_false_iff_not, Nat.not_lt] at hor2
              have hc1_le_v0 : c1 ≤ evalNLVars φ v0 := by
                by_cases hv1_nil : v1 = []
                · subst hv1_nil
                  simp only [nlvarsMaxOffset] at hor2
                  have hc1_one : c1 = 1 := by omega
                  have hc0_one : c0 = 1 := by rcases hc1_eq with rfl | rfl <;> omega
                  rcases he0_cv hc0_one with hp1_nil | hv0_ne
                  · have hw0_p2 : w0.param ∈ p2 := hs_wf.1 w0 (List.mem_cons_self ..)
                    have hw0_p1 : w0.param ∈ p1 := glistSubset_mem hs_wf.2 he0_wf.2 hsub w0.param hw0_p2
                    dsimp only at hp1_nil
                    rw [hp1_nil] at hw0_p1
                    cases hw0_p1
                  · obtain ⟨u0, hu0_v0, _⟩ := exists_mem_nlvarsMaxOffset hv0_ne
                    have hu0_p1 : u0.param ∈ p1 := he0_wf.1 u0 hu0_v0
                    have hu0_pos : 0 < φ u0.param := (guardActive_iff.mp hp1_act) u0.param hu0_p1
                    have hu0_le : u0.eval φ ≤ evalNLVars φ v0 := le_evalNLVars_of_mem hu0_v0
                    unfold NLVar.eval at hu0_le
                    omega
                · obtain ⟨u, hu_v1, hu_off⟩ := exists_mem_nlvarsMaxOffset hv1_nil
                  have hu_v0 : u ∈ v0 := hv1_sub u hu_v1
                  have hu_p1 : u.param ∈ p1 := he0_wf.1 u hu_v0
                  have hu_pos : 0 < φ u.param := (guardActive_iff.mp hp1_act) u.param hu_p1
                  have hu_le : u.eval φ ≤ evalNLVars φ v0 := le_evalNLVars_of_mem hu_v0
                  unfold NLVar.eval at hu_le
                  omega
              omega
        · simp only [Bool.not_eq_true] at hsame
          simp only [hsame, Bool.false_eq_true, ↓reduceIte]
          by_cases hc2_lt : decide (c2 < c1) = true
          · cases v2 with
            | nil =>
              simp only [hc2_lt, Bool.and_self, ↓reduceIte]
              exact ih hc1_eq hv1_sub hsr_sub
            | cons w0 wr =>
              simp only [hc2_lt, Bool.true_and]
              by_cases hor2 : decide (nlvarsMaxOffset v1 + 1 < c1) = true
              · simp only [hor2, ↓reduceIte]
                have hv1n_sub : ∀ v ∈ nlvarsSubsume v1 (w0 :: wr), v ∈ v0 :=
                  fun v hv => hv1_sub v (nlvarsSubsume_subset v1 (w0 :: wr) v hv)
                exact ih hc1_eq hv1n_sub hsr_sub
              · simp only [Bool.not_eq_true] at hor2
                simp only [decide_eq_false_iff_not, Nat.not_lt] at hor2
                have hc1_le_v0 : c1 ≤ evalNLVars φ v0 := by
                  by_cases hv1_nil : v1 = []
                  · subst hv1_nil
                    simp only [nlvarsMaxOffset] at hor2
                    have hc1_one : c1 = 1 := by omega
                    have hc0_one : c0 = 1 := by rcases hc1_eq with rfl | rfl <;> omega
                    rcases he0_cv hc0_one with hp1_nil | hv0_ne
                    · have hw0_p2 : w0.param ∈ p2 := hs_wf.1 w0 (List.mem_cons_self ..)
                      have hw0_p1 : w0.param ∈ p1 := glistSubset_mem hs_wf.2 he0_wf.2 hsub w0.param hw0_p2
                      dsimp only at hp1_nil
                      rw [hp1_nil] at hw0_p1
                      cases hw0_p1
                    · obtain ⟨u0, hu0_v0, _⟩ := exists_mem_nlvarsMaxOffset hv0_ne
                      have hu0_p1 : u0.param ∈ p1 := he0_wf.1 u0 hu0_v0
                      have hu0_pos : 0 < φ u0.param := (guardActive_iff.mp hp1_act) u0.param hu0_p1
                      have hu0_le : u0.eval φ ≤ evalNLVars φ v0 := le_evalNLVars_of_mem hu0_v0
                      unfold NLVar.eval at hu0_le
                      omega
                  · obtain ⟨u, hu_v1, hu_off⟩ := exists_mem_nlvarsMaxOffset hv1_nil
                    have hu_v0 : u ∈ v0 := hv1_sub u hu_v1
                    have hu_p1 : u.param ∈ p1 := he0_wf.1 u hu_v0
                    have hu_pos : 0 < φ u.param := (guardActive_iff.mp hp1_act) u.param hu_p1
                    have hu_le : u.eval φ ≤ evalNLVars φ v0 := le_evalNLVars_of_mem hu_v0
                    unfold NLVar.eval at hu_le
                    omega
                omega
          · simp only [Bool.not_eq_true] at hc2_lt
            simp only [decide_eq_false_iff_not, Nat.not_lt] at hc2_lt
            have hlt_len : p2.length < p1.length := glistSubset_length_lt_of_eqLen_false hsub hsame
            have hs_le : (⟨p2, c2, v2⟩ : NLEntry).eval φ ≤ M := h_short _ hs_mem hlt_len
            simp only [NLEntry.eval, hp2_act, ↓reduceIte] at hs_le
            omega
    · simp only [Bool.not_eq_true] at hsub
      simp only [hsub, Bool.not_false, ↓reduceIte]
      exact ih hc1_eq hv1_sub hsr_sub

theorem evalNLEntries_le_nlSubsumptionWalk {φ : Ix.Kernel.LevelParam → Nat}
    {snap : List NLEntry}
    (hsnap_wf : ∀ e ∈ snap, e.WF)
    (hsnap_cv : ∀ e ∈ snap, e.ConstValid) :
    evalNLEntries φ snap ≤ evalNLEntries φ (nlSubsumptionWalk snap snap) := by
  let M := evalNLEntries φ (nlSubsumptionWalk snap snap)
  have H_entry : ∀ n : Nat, ∀ e ∈ snap, e.guards.length = n → e.eval φ ≤ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro e he_mem hn
      rcases e with ⟨p1, c0, v0⟩
      dsimp only at hn
      have he_wf : (⟨p1, c0, v0⟩ : NLEntry).WF := hsnap_wf ⟨p1, c0, v0⟩ he_mem
      have he_cv : (⟨p1, c0, v0⟩ : NLEntry).ConstValid := hsnap_cv ⟨p1, c0, v0⟩ he_mem
      have h_short : ∀ s ∈ snap, s.guards.length < p1.length → s.eval φ ≤ M := by
        intro s hs hlt
        rw [hn] at hlt
        exact ih s.guards.length hlt s hs rfl
      have h_final_mem : nlSubsumeEntry ⟨p1, c0, v0⟩ snap ∈ nlSubsumptionWalk snap snap := by
        simp only [nlSubsumptionWalk, List.mem_map]
        exact ⟨⟨p1, c0, v0⟩, he_mem, rfl⟩
      have h_final_le : (nlSubsumeEntry ⟨p1, c0, v0⟩ snap).eval φ ≤ M :=
        le_evalNLEntries_of_mem h_final_mem
      simp only [NLEntry.eval]
      by_cases hp1_act : guardActive φ p1 = true
      · simp only [hp1_act, ↓reduceIte]
        have hv0_le : evalNLVars φ v0 ≤ M := by
          apply evalNLVars_le_of_forall
          intro v hv
          have h1 := nlSubsumeEntry_var_le (p1 := p1) (c1 := c0) he_wf.2 hp1_act hsnap_wf
            (fun s hs => hs) h_short v hv
          omega
        have hc0_le : c0 ≤ M := by
          have h2 := nlSubsumeEntry_const_le he_wf he_cv hp1_act (.inl rfl)
            (fun v hv => hv) hv0_le hsnap_wf (fun s hs => hs) h_short
          omega
        omega
      · simp [hp1_act]
  have H_all : ∀ rem : List NLEntry, (∀ e ∈ rem, e ∈ snap) → evalNLEntries φ rem ≤ M := by
    intro rem
    induction rem with
    | nil => intro _; simp [evalNLEntries]
    | cons e rest ihr =>
      intro hsub
      simp only [evalNLEntries]
      have h1 := H_entry e.guards.length e (hsub e (List.mem_cons_self ..)) rfl
      have h2 := ihr (fun e' he' => hsub e' (List.mem_cons_of_mem _ he'))
      omega
  exact H_all snap (fun e he => he)

/-- **`levelNormalize l` evaluates to `Ix.Kernel.Level.eval φ l` under every valuation `φ`.** -/
theorem evalNLEntries_levelNormalize (φ : Ix.Kernel.LevelParam → Nat) (l : Ix.Kernel.Level) :
    evalNLEntries φ (levelNormalize l) = Ix.Kernel.Level.eval φ l := by
  unfold levelNormalize
  dsimp only
  let raw := normalizeAux l [] 0 [⟨[], 0, []⟩]
  have hraw_wf : ∀ e ∈ raw, e.WF := by
    apply normalizeStep_wf
    · exact List.Pairwise.nil
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨(by intro v hv; cases hv), List.Pairwise.nil⟩
  have hraw_cv : ∀ e ∈ raw, e.ConstValid := by
    apply normalizeStep_constValid
    intro e he h1
    simp only [List.mem_singleton] at he
    subst he
    simp at h1
  have h_le : evalNLEntries φ (nlSubsumptionWalk raw raw) ≤ evalNLEntries φ raw :=
    evalNLEntries_nlSubsumptionWalk_le φ raw raw
  have h_ge : evalNLEntries φ raw ≤ evalNLEntries φ (nlSubsumptionWalk raw raw) :=
    evalNLEntries_le_nlSubsumptionWalk hraw_wf hraw_cv
  have h_eq : evalNLEntries φ (nlSubsumptionWalk raw raw) = evalNLEntries φ raw :=
    Nat.le_antisymm h_le h_ge
  rw [h_eq]
  exact evalNLEntries_normalizeAux_seed φ l

/-- **Pure soundness of `levelLeq`**: if `levelLeq a b = true`, then
`Ix.Kernel.Level.eval φ a ≤ Ix.Kernel.Level.eval φ b` for all `φ`. -/
theorem levelLeq_eq_true_sound {a b : Ix.Kernel.Level} (h : levelLeq a b = true)
    (φ : Ix.Kernel.LevelParam → Nat) :
    Ix.Kernel.Level.eval φ a ≤ Ix.Kernel.Level.eval φ b := by
  unfold levelLeq at h
  by_cases hab : (a == b) = true
  · have heq : a = b := eq_of_beq hab
    subst heq
    exact Nat.le_refl _
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at h
    cases a with
    | zero => simp [Ix.Kernel.Level.eval]
    | succ u | max u v | imax u v | param u =>
      have hle := levelNormalize_nlLe_sound h φ
      rwa [evalNLEntries_levelNormalize, evalNLEntries_levelNormalize] at hle

/-- **Pure soundness of `levelEqual`**: if `levelEqual a b = true`, then
`Ix.Kernel.Level.eval φ a = Ix.Kernel.Level.eval φ b` for all `φ`. -/
theorem levelEqual_eq_true_sound {a b : Ix.Kernel.Level} (h : levelEqual a b = true)
    (φ : Ix.Kernel.LevelParam → Nat) :
    Ix.Kernel.Level.eval φ a = Ix.Kernel.Level.eval φ b := by
  unfold levelEqual at h
  by_cases hab : (a == b) = true
  · have heq : a = b := eq_of_beq hab
    subst heq
    rfl
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at h
    have heq := nlEq_sound h φ
    rwa [evalNLEntries_levelNormalize, evalNLEntries_levelNormalize] at heq

/-- Fuel stability of `normalizeStep`: any `fuel ≥ normFuel arg` computes the exact same
`List NLEntry` as `normFuel arg`. -/
theorem normalizeStep_stable :
    ∀ (fuel1 fuel2 : Nat) (arg : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level))
      (path : List Nat) (k : Nat) (acc : List NLEntry),
      normFuel arg ≤ fuel1 →
      normFuel arg ≤ fuel2 →
      normalizeStep fuel1 arg path k acc = normalizeStep fuel2 arg path k acc := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 arg path k acc hf1 _
    cases arg with
    | inl l => simp [normFuel] at hf1
    | inr ab => simp [normFuel] at hf1
  | succ fuel1 ih =>
    intro fuel2 arg path k acc hf1 hf2
    cases fuel2 with
    | zero =>
      cases arg with
      | inl l => simp [normFuel] at hf2
      | inr ab => simp [normFuel] at hf2
    | succ fuel2 =>
      cases arg with
      | inl l =>
        cases l with
        | zero => rfl
        | succ inner =>
          have h1 : normFuel (.inl inner) ≤ fuel1 := by have := normFuel_succ inner; omega
          have h2 : normFuel (.inl inner) ≤ fuel2 := by have := normFuel_succ inner; omega
          exact ih fuel2 (.inl inner) path (k + 1) acc h1 h2
        | max a b =>
          have ha1 : normFuel (.inl a) ≤ fuel1 := by have := normFuel_max_left a b; omega
          have ha2 : normFuel (.inl a) ≤ fuel2 := by have := normFuel_max_left a b; omega
          have hb1 : normFuel (.inl b) ≤ fuel1 := by have := normFuel_max_right a b; omega
          have hb2 : normFuel (.inl b) ≤ fuel2 := by have := normFuel_max_right a b; omega
          simp only [normalizeStep, ih fuel2 (.inl a) path k acc ha1 ha2]
          exact ih fuel2 (.inl b) path k _ hb1 hb2
        | imax u b =>
          have h1 : normFuel (.inr (u, b)) ≤ fuel1 := by have := normFuel_imax u b; omega
          have h2 : normFuel (.inr (u, b)) ≤ fuel2 := by have := normFuel_imax u b; omega
          exact ih fuel2 (.inr (u, b)) path k acc h1 h2
        | param idx => rfl
      | inr ab =>
        rcases ab with ⟨a, b⟩
        cases b with
        | zero => rfl
        | succ v =>
          have ha1 : normFuel (.inl a) ≤ fuel1 := by have := normFuel_inr_succ_a a v; omega
          have ha2 : normFuel (.inl a) ≤ fuel2 := by have := normFuel_inr_succ_a a v; omega
          have hv1 : normFuel (.inl v) ≤ fuel1 := by have := normFuel_inr_succ_v a v; omega
          have hv2 : normFuel (.inl v) ≤ fuel2 := by have := normFuel_inr_succ_v a v; omega
          simp only [normalizeStep, ih fuel2 (.inl a) path k acc ha1 ha2]
          exact ih fuel2 (.inl v) path (k + 1) _ hv1 hv2
        | max v w =>
          have hv1 : normFuel (.inr (a, v)) ≤ fuel1 := by have := normFuel_inr_max_left a v w; omega
          have hv2 : normFuel (.inr (a, v)) ≤ fuel2 := by have := normFuel_inr_max_left a v w; omega
          have hw1 : normFuel (.inr (a, w)) ≤ fuel1 := by have := normFuel_inr_max_right a v w; omega
          have hw2 : normFuel (.inr (a, w)) ≤ fuel2 := by have := normFuel_inr_max_right a v w; omega
          simp only [normalizeStep, ih fuel2 (.inr (a, v)) path k acc hv1 hv2]
          exact ih fuel2 (.inr (a, w)) path k _ hw1 hw2
        | imax v w =>
          have haw1 : normFuel (.inr (a, w)) ≤ fuel1 := by have := normFuel_inr_imax_right a v w; omega
          have haw2 : normFuel (.inr (a, w)) ≤ fuel2 := by have := normFuel_inr_imax_right a v w; omega
          have hvw1 : normFuel (.inr (v, w)) ≤ fuel1 := by have := normFuel_inr_imax_vw a v w; omega
          have hvw2 : normFuel (.inr (v, w)) ≤ fuel2 := by have := normFuel_inr_imax_vw a v w; omega
          simp only [normalizeStep, ih fuel2 (.inr (a, w)) path k acc haw1 haw2]
          exact ih fuel2 (.inr (v, w)) path k _ hvw1 hvw2
        | param idx =>
          have ha1 : normFuel (.inl a) ≤ fuel1 := by have := normFuel_inr_param a idx; omega
          have ha2 : normFuel (.inl a) ≤ fuel2 := by have := normFuel_inr_param a idx; omega
          simp only [normalizeStep]
          cases glistOrderedInsert idx path with
          | mk f newPath =>
            cases f with
            | true => exact ih fuel2 (.inl a) newPath k _ ha1 ha2
            | false => exact ih fuel2 (.inl a) path k _ ha1 ha2

theorem normalizeAux_eq_of_le_fuel {fuel : Nat} {l : Ix.Kernel.Level}
    {path : List Nat} {k : Nat} {acc : List NLEntry}
    (hfuel : normFuel (.inl l) ≤ fuel) :
    normalizeStep fuel (.inl l) path k acc = normalizeAux l path k acc :=
  normalizeStep_stable fuel (normFuel (.inl l)) (.inl l) path k acc hfuel (Nat.le_refl _)

theorem normalizeIMaxDispatch_eq_of_le_fuel {fuel : Nat} {a b : Ix.Kernel.Level}
    {path : List Nat} {k : Nat} {acc : List NLEntry}
    (hfuel : normFuel (.inr (a, b)) ≤ fuel) :
    normalizeStep fuel (.inr (a, b)) path k acc = normalizeIMaxDispatch a b path k acc :=
  normalizeStep_stable fuel (normFuel (.inr (a, b))) (.inr (a, b)) path k acc hfuel (Nat.le_refl _)

/-! ### Structural Depth & Offset Bounds -/

theorem levelDepth_levelMaxOffsets_le (a b : Ix.Kernel.Level) :
    levelDepth (levelMaxOffsets a b) ≤ Max.max (levelDepth a) (levelDepth b) + 1 := by
  unfold levelMaxOffsets
  dsimp only
  split
  · split <;> [exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _);
               exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)]
  · simp [levelDepth]

theorem levelDepth_levelMaxGo_le (a b : Ix.Kernel.Level) :
    levelDepth (levelMaxGo a b) ≤ Max.max (levelDepth a) (levelDepth b) + 1 := by
  unfold levelMaxGo
  split
  · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
  · split
    · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
    · split
      · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
      · split
        · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
        · split
          · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
          · exact levelDepth_levelMaxOffsets_le a b

theorem levelDepth_levelMax_le (a b : Ix.Kernel.Level) :
    levelDepth (levelMax a b) ≤ Max.max (levelDepth a) (levelDepth b) + 1 := by
  unfold levelMax
  cases levelExplicitVal a with
  | none => exact levelDepth_levelMaxGo_le a b
  | some na =>
    cases levelExplicitVal b with
    | none => exact levelDepth_levelMaxGo_le a b
    | some nb =>
      dsimp only
      split <;> [exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _);
                 exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)]

theorem levelDepth_levelIMax_le (a b : Ix.Kernel.Level) :
    levelDepth (levelIMax a b) ≤ Max.max (levelDepth a) (levelDepth b) + 1 := by
  unfold levelIMax
  cases b with
  | zero => simp [levelDepth]
  | succ u => exact levelDepth_levelMax_le a (.succ u)
  | max u v | imax u v | param u =>
    dsimp only
    split
    · exact levelDepth_levelMax_le a _
    · cases a <;> (try exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)) <;>
        (dsimp only; split <;> [exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _);
                                simp [levelDepth]])

theorem levelDepth_levelReduce_le (l : Ix.Kernel.Level) :
    levelDepth (levelReduce l) ≤ levelDepth l := by
  induction l with
  | zero => simp [levelReduce, levelDepth]
  | succ u ih => simp only [levelReduce, levelDepth]; omega
  | max a b iha ihb =>
    simp only [levelReduce, levelDepth]
    have h := levelDepth_levelMax_le (levelReduce a) (levelReduce b)
    omega
  | imax a b iha ihb =>
    simp only [levelReduce, levelDepth]
    have h := levelDepth_levelIMax_le (levelReduce a) (levelReduce b)
    omega
  | param i => simp [levelReduce, levelDepth]

/-- Maximum `levelDepth` across a list of universe levels. -/
def maxLevelDepth : List Ix.Kernel.Level → Nat
  | [] => 0
  | l :: ls => Max.max (levelDepth l) (maxLevelDepth ls)

theorem levelDepth_le_maxLevelDepth {params : List Ix.Kernel.Level} {i : Nat} {p : Ix.Kernel.Level}
    (h : params[i]? = some p) : levelDepth p ≤ maxLevelDepth params := by
  induction params generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [maxLevelDepth]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have := ih h
      simp only [maxLevelDepth]
      omega

theorem levelDepth_substLevel_le (l : Ix.Kernel.Level) (params : List Ix.Kernel.Level) :
    levelDepth (substLevel l params) ≤ levelDepth l + maxLevelDepth params := by
  induction l with
  | zero => simp [substLevel, levelDepth]
  | succ u ih => simp only [substLevel, levelDepth]; omega
  | max a b iha ihb =>
    simp only [substLevel, levelDepth]
    have h := levelDepth_levelMax_le (substLevel a params) (substLevel b params)
    omega
  | imax a b iha ihb =>
    simp only [substLevel, levelDepth]
    have h := levelDepth_levelIMax_le (substLevel a params) (substLevel b params)
    omega
  | param i =>
    simp only [substLevel, levelDepth, Nat.zero_add]
    cases hp : params[i]? with
    | none => simp [levelDepth]
    | some p => exact levelDepth_le_maxLevelDepth hp


/-! ## `EvalFn W` Refinement Theorems (`*_refines`)

We now establish direct `EvalFn W` refinement theorems connecting the compiled
`KernelLevels` functions in `IxVM.Checked` to the pure specifications and
heap representation predicates (`RepKLevel`, `RepKLevelList`, `RepGuardList`,
`RepNLVarList`, `RepNLEntry`, `RepNLEntries`). -/

/-- `EvalFn W` refinement for `Fields::is_zero` on `a - b` for 32-bit `Nat`s. -/
theorem fieldsIsZero_sub_refines {h h' : Heap F} {r : SourceValue F}
    {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    (ev : EvalFn W "Fields::is_zero" [.field ((a : F) - (b : F))] h r h') :
    r = .field (if a == b then 1 else 0) ∧ h' = h := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«Fields::is_zero»)
    (by simp [IxVM.Checked.Fn.«Fields::is_zero», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«Fields::is_zero»] at ev
  rcases ev.matchValue_inv with ⟨_, _, _, _, ev0, hsel, ev⟩
  rcases ev0.var_inv with ⟨⟨⟩, rfl⟩
  rcases selectArm_literal_inv hsel with ⟨heq0, rfl, rfl⟩ | ⟨hne0, hsel⟩
  · rcases ev.literal_inv with ⟨rfl, rfl⟩
    injection heq0 with hsub
    have hab : a = b := (natCast_sub_eq_zero_iff ha hb).mp hsub
    subst hab
    simp
  · rcases selectArm_wildcard_inv hsel with ⟨rfl, rfl⟩
    rcases ev.literal_inv with ⟨rfl, rfl⟩
    have hab : a ≠ b := fun h => hne0 (congrArg Value.field ((natCast_sub_eq_zero_iff ha hb).mpr h))
    simp [hab]

/-- `EvalFn W` refinement for `Fields::is_zero` on `(a : F)` for a 32-bit `Nat`. -/
theorem fieldsIsZero_nat_refines {h h' : Heap F} {r : SourceValue F}
    {a : Nat} (ha : a < 4294967296)
    (ev : EvalFn W "Fields::is_zero" [.field (a : F)] h r h') :
    r = .field (if a == 0 then 1 else 0) ∧ h' = h := by
  have hsub : (a : F) = (a : F) - ((0 : Nat) : F) := by simp
  rw [hsub] at ev
  exact fieldsIsZero_sub_refines ha (by decide) ev

@[simp] theorem guardList_ctor :
    constructorName [] (.named "Lists::Node" [.field]) = guardListEnum :=
  node_ctor

@[simp] theorem guardList_inst :
    instanceName [] "Lists::Node" (some [.field]) = guardListEnum := by
  decide +kernel

theorem zmod_val_natCast_of_le {n : Nat} (hn : n ≤ 4294967296) :
    ((n : F)).val = n := by
  have hm : n < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; omega
  exact ZMod.val_natCast_of_lt hm

theorem mem_zip_map_iff {α β γ : Type} {l : List α} {f : α → β} {g : α → γ} {p : β × γ} :
    p ∈ (l.map f).zip (l.map g) ↔ ∃ x ∈ l, p = (f x, g x) := by
  induction l generalizing p with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact ⟨a, .inl rfl, rfl⟩
      · exact ⟨x, .inr hx, rfl⟩
    · rintro ⟨x, rfl | hx, rfl⟩
      · exact .inl rfl
      · exact .inr ⟨x, hx, rfl⟩

/-- The static map `UInt8::range_pair`. -/
def rangePairMap : Aiur.MapDecl := IxVM.Checked.coreTables.maps[2]'(by decide)

theorem find_rangePairMap :
    IxVM.Checked.coreTables.findMap? "UInt8::range_pair" = some rangePairMap := by
  decide +kernel

theorem rangePair_mapCall_inv {v1 v2 w : SourceValue F} {h h' : Heap F}
    (hm : mapCall IxVM.Checked.source.tables "UInt8::range_pair" [v1, v2] h = some (w, h')) :
    w = .tuple [] ∧ h' = h ∧
      ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F) := by
  unfold mapCall at hm
  cases looked : lookupMap IxVM.Checked.source.tables "UInt8::range_pair" [v1, v2] with
  | error _ => simp [looked] at hm
  | ok row =>
    simp only [looked, Option.some.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨hrow, rfl⟩
    subst hrow
    obtain ⟨map, key, found, -, -, extracted, mem, -⟩ := Aiur.lookupMap_spec looked
    change IxVM.Checked.coreTables.findMap? "UInt8::range_pair" = some map at found
    rw [find_rangePairMap, Option.some.injEq] at found
    subst found
    have rows : IxVM.Checked.coreTables.mapRows rangePairMap =
        IxVM.Checked.pairInputsTTable.rows.zip IxVM.Checked.pairUnitsTable.rows := by
      simp only [Aiur.Program.mapRows, show rangePairMap.input = "UInt8::pair_inputs" from rfl,
        show rangePairMap.output = "UInt8::pair_units" from rfl, IxVM.Checked.find_pairInputsT,
        IxVM.Checked.find_pairUnits]
    change (key, row) ∈ IxVM.Checked.coreTables.mapRows rangePairMap at mem
    rw [rows] at mem
    simp only [IxVM.Checked.pairInputsTTable, IxVM.Checked.pairUnitsTable, List.map_map] at mem
    obtain ⟨p, hp, hkr⟩ := mem_zip_map_iff.mp mem
    rcases p with ⟨a, b⟩
    simp only [IxVM.Checked.pairInputs, List.mem_flatMap, List.mem_map, List.mem_range,
      Prod.mk.injEq] at hp
    obtain ⟨a, ha, b, hb, rfl, rfl⟩ := hp
    simp only [Function.comp, IxVM.Checked.coreRow, IxVM.Checked.coreLeaf, List.map,
      Prod.mk.injEq] at hkr
    rcases hkr with ⟨rfl, rfl⟩
    have hv := Aiur.Value.toConstant_spec extracted
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    rcases hv with ⟨rfl, rfl⟩
    exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl, a, b, ha, hb, rfl, rfl⟩

theorem u8FromFields_eval_inv {x_a x_b r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt8::from_fields" [x_a, x_b] h r h') :
    r = .tuple [x_a, x_b] ∧ h' = h ∧
      ∃ a b : Nat, a < 256 ∧ b < 256 ∧ x_a = .field (a : F) ∧ x_b = .field (b : F) := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt8::from_fields».of_eval ev
  have run := hk0 (k0 + 1) (by omega)
  simp only [Mirrors.«UInt8::from_fields», bind, Option.bind] at run
  cases hm : mapCall IxVM.Checked.source.tables "UInt8::range_pair" [x_a, x_b] h with
  | none => simp [hm] at run
  | some wh =>
    simp only [hm, Option.some.injEq, Prod.mk.injEq] at run
    rcases wh with ⟨w, h1⟩
    obtain ⟨_, rfl, a, b, ha, hb, rfl, rfl⟩ := rangePair_mapCall_inv hm
    exact ⟨run.1.symm, run.2.symm, a, b, ha, hb, rfl, rfl⟩

theorem u32FromFields_eval_inv {raw r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt32::from_fields" [raw] h r h') :
    h' = h ∧ ∃ b0 b1 b2 b3 : Nat,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      r = .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)] := by
  have body := ev.function_inv IxVM.Checked.Lookup.«UInt32::from_fields»
    (by simp [IxVM.Checked.Fn.«UInt32::from_fields», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«UInt32::from_fields»] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨_, d15, _⟩ := d13.index_inv
  obtain ⟨_, rfl⟩ := d15.var_inv
  obtain ⟨v16, vs17, m18, rfl, d19, args20⟩ := args14.cons_inv
  obtain ⟨_, d21, _⟩ := d19.index_inv
  obtain ⟨_, rfl⟩ := d21.var_inv
  obtain ⟨rfl, rfl⟩ := args20.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, rfl, b0, b1, hb0, hb1, rfl, rfl⟩ := u8FromFields_eval_inv callee9
  obtain ⟨ys22, hp23, hl24, ml25⟩ := matchPattern_tuple_inv mt4
  rcases ys22 with _ | ⟨y26, _ | ⟨y27, _ | ⟨_, _⟩⟩⟩ <;> simp at hl24
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp23
  rcases hp23 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml25
  subst ml25
  obtain ⟨v28, m29, bs30, d31, mt32, d33⟩ := d5.letValue_inv
  obtain ⟨vs34, m35, args36, callee37⟩ := d31.call_inv
  obtain ⟨v38, vs39, m40, rfl, d41, args42⟩ := args36.cons_inv
  obtain ⟨_, d43, _⟩ := d41.index_inv
  obtain ⟨_, rfl⟩ := d43.var_inv
  obtain ⟨v44, vs45, m46, rfl, d47, args48⟩ := args42.cons_inv
  obtain ⟨_, d49, _⟩ := d47.index_inv
  obtain ⟨_, rfl⟩ := d49.var_inv
  obtain ⟨rfl, rfl⟩ := args48.nil_inv
  rw [instanceName_plain_some] at callee37
  obtain ⟨rfl, rfl, b2, b3, hb2, hb3, rfl, rfl⟩ := u8FromFields_eval_inv callee37
  obtain ⟨ys50, hp51, hl52, ml53⟩ := matchPattern_tuple_inv mt32
  rcases ys50 with _ | ⟨y54, _ | ⟨y55, _ | ⟨_, _⟩⟩⟩ <;> simp at hl52
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp51
  rcases hp51 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml53
  subst ml53
  obtain ⟨vs56, args57, rfl⟩ := d33.array_inv
  obtain ⟨v58, vs59, m60, rfl, d61, args62⟩ := args57.cons_inv
  obtain ⟨l63, rfl⟩ := d61.var_inv; simp at l63; subst l63
  obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
  obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
  obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
  obtain ⟨l75, rfl⟩ := d73.var_inv; simp at l75; subst l75
  obtain ⟨v76, vs77, m78, rfl, d79, args80⟩ := args74.cons_inv
  obtain ⟨l81, rfl⟩ := d79.var_inv; simp at l81; subst l81
  obtain ⟨rfl, rfl⟩ := args80.nil_inv
  exact ⟨rfl, b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl⟩

theorem u32Compact_eval_inv {b0 b1 b2 b3 : Nat} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt32::compact"
      [.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]] h r h') :
    r = .field ((Aiur.Library.U32.pack b0 b1 b2 b3 : Nat) : F) ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt32::compact».of_eval ev
  have run := hk0 (k0 + 2) (by omega)
  simp [Mirrors.«UInt32::compact», Mirrors.«UInt8::to_field», projectValue, evalBinOp] at run
  rcases run with ⟨rfl, rfl⟩
  refine ⟨?_, rfl⟩
  congr 1
  unfold Aiur.Library.U32.pack
  push_cast
  ring

theorem u32LessThanFields_complete : Mirrors.«UInt32::less_than_fields».Complete := by
  intro x_a x_b h h' r ev
  have body := ev.function_inv IxVM.Checked.Lookup.«UInt32::less_than_fields»
    (by simp [IxVM.Checked.Fn.«UInt32::less_than_fields», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«UInt32::less_than_fields»] at body
  obtain ⟨v_raw, m0, bs0, d_hint, mt0, d1⟩ := body.letValue_inv
  obtain ⟨_, _, d_key, _, _⟩ := d_hint.hint_inv
  obtain ⟨_, args_key, _⟩ := d_key.tuple_inv
  obtain ⟨_, _, _, _, d_ka, args_key1⟩ := args_key.cons_inv
  obtain ⟨_, rfl⟩ := d_ka.var_inv
  obtain ⟨_, _, _, _, d_kb, args_key2⟩ := args_key1.cons_inv
  obtain ⟨_, rfl⟩ := d_kb.var_inv
  obtain ⟨_, rfl⟩ := args_key2.nil_inv
  rw [matchPattern_bind] at mt0
  simp only [Except.ok.injEq, Option.some.injEq] at mt0
  subst mt0
  obtain ⟨v_left, m1, bs1, d_left, mt1, d2⟩ := d1.letValue_inv
  obtain ⟨_, _, args_l, call_l⟩ := d_left.call_inv
  obtain ⟨_, _, _, rfl, d_arg_l, nil_l⟩ := args_l.cons_inv
  obtain ⟨_, d_var_l, _⟩ := d_arg_l.project_inv
  obtain ⟨_, rfl⟩ := d_var_l.var_inv
  obtain ⟨rfl, rfl⟩ := nil_l.nil_inv
  rw [instanceName_plain_some] at call_l
  obtain ⟨rfl, a0, a1, a2, a3, ha0, ha1, ha2, ha3, rfl⟩ := u32FromFields_eval_inv call_l
  rw [matchPattern_bind] at mt1
  simp only [Except.ok.injEq, Option.some.injEq] at mt1
  subst mt1
  obtain ⟨v_diff, m2, bs2, d_diff, mt2, d3⟩ := d2.letValue_inv
  obtain ⟨_, _, args_d, call_d⟩ := d_diff.call_inv
  obtain ⟨_, _, _, rfl, d_arg_d, nil_d⟩ := args_d.cons_inv
  obtain ⟨_, d_var_d, _⟩ := d_arg_d.project_inv
  obtain ⟨_, rfl⟩ := d_var_d.var_inv
  obtain ⟨rfl, rfl⟩ := nil_d.nil_inv
  rw [instanceName_plain_some] at call_d
  obtain ⟨rfl, d0, d1_b, d2_b, d3_b, hd0, hd1, hd2, hd3, rfl⟩ := u32FromFields_eval_inv call_d
  rw [matchPattern_bind] at mt2
  simp only [Except.ok.injEq, Option.some.injEq] at mt2
  subst mt2
  obtain ⟨v_right, m3, bs3, d_right, mt3, d4⟩ := d3.letValue_inv
  obtain ⟨_, _, args_r, call_r⟩ := d_right.call_inv
  obtain ⟨_, _, _, rfl, d_arg_r, nil_r⟩ := args_r.cons_inv
  obtain ⟨_, d_var_r, _⟩ := d_arg_r.project_inv
  obtain ⟨_, rfl⟩ := d_var_r.var_inv
  obtain ⟨rfl, rfl⟩ := nil_r.nil_inv
  rw [instanceName_plain_some] at call_r
  obtain ⟨rfl, b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl⟩ := u32FromFields_eval_inv call_r
  rw [matchPattern_bind] at mt3
  simp only [Except.ok.injEq, Option.some.injEq] at mt3
  subst mt3
  obtain ⟨_, m4, bs4, d_eq_l, mt4, d5⟩ := d4.letValue_inv
  obtain ⟨vs_eq_l, args_eq_l, app_eq_l⟩ := d_eq_l.builtin_inv
  obtain ⟨v_el1, _, _, rfl, d_el1, args_el1⟩ := args_eq_l.cons_inv
  obtain ⟨l_el1, rfl⟩ := d_el1.var_inv; simp at l_el1; subst l_el1
  obtain ⟨v_el2, _, _, rfl, d_el2, nil_el⟩ := args_el1.cons_inv
  obtain ⟨_, _, args_cl, call_cl⟩ := d_el2.call_inv
  obtain ⟨_, _, _, rfl, d_var_cl, nil_cl⟩ := args_cl.cons_inv
  obtain ⟨l_cl, rfl⟩ := d_var_cl.var_inv; simp at l_cl; subst l_cl
  obtain ⟨rfl, rfl⟩ := nil_cl.nil_inv
  rw [instanceName_plain_some] at call_cl
  obtain ⟨rfl, rfl⟩ := u32Compact_eval_inv call_cl
  obtain ⟨rfl, rfl⟩ := nil_el.nil_inv
  simp only [Builtin.apply, evalAssertEq, Value.pointerFree, Bool.and_self,
    ↓reduceIte] at app_eq_l
  split_ifs at app_eq_l with h_pf_a h_xa
  subst h_xa
  rw [matchPattern_wildcard] at mt4
  simp only [Except.ok.injEq, Option.some.injEq] at mt4
  subst mt4
  obtain ⟨_, m5, bs5, d_eq_r, mt5, d6⟩ := d5.letValue_inv
  obtain ⟨vs_eq_r, args_eq_r, app_eq_r⟩ := d_eq_r.builtin_inv
  obtain ⟨v_er1, _, _, rfl, d_er1, args_er1⟩ := args_eq_r.cons_inv
  obtain ⟨l_er1, rfl⟩ := d_er1.var_inv; simp at l_er1; subst l_er1
  obtain ⟨v_er2, _, _, rfl, d_er2, nil_er⟩ := args_er1.cons_inv
  obtain ⟨_, _, args_cr, call_cr⟩ := d_er2.call_inv
  obtain ⟨_, _, _, rfl, d_var_cr, nil_cr⟩ := args_cr.cons_inv
  obtain ⟨l_cr, rfl⟩ := d_var_cr.var_inv; simp at l_cr; subst l_cr
  obtain ⟨rfl, rfl⟩ := nil_cr.nil_inv
  rw [instanceName_plain_some] at call_cr
  obtain ⟨rfl, rfl⟩ := u32Compact_eval_inv call_cr
  obtain ⟨rfl, rfl⟩ := nil_er.nil_inv
  simp only [Builtin.apply, evalAssertEq, Value.pointerFree, Bool.and_self,
    ↓reduceIte] at app_eq_r
  split_ifs at app_eq_r with h_pf_b h_xb
  subst h_xb
  rw [matchPattern_wildcard] at mt5
  simp only [Except.ok.injEq, Option.some.injEq] at mt5
  subst mt5
  obtain ⟨v_borrow, m6, bs6, d_borrow, mt6, d7⟩ := d6.letValue_inv
  obtain ⟨x_num, y_den, _, d_num, d_den, op_div⟩ := d_borrow.binary_inv
  obtain ⟨x_add, y_sub, _, d_add, d_sub, op_sub⟩ := d_num.binary_inv
  obtain ⟨x_cd, y_add, _, d_cd, d_b, op_add⟩ := d_add.binary_inv
  obtain ⟨_, _, args_cd, call_cd⟩ := d_cd.call_inv
  obtain ⟨_, _, _, rfl, d_var_cd, nil_cd⟩ := args_cd.cons_inv
  obtain ⟨l_cd, rfl⟩ := d_var_cd.var_inv; simp at l_cd; subst l_cd
  obtain ⟨rfl, rfl⟩ := nil_cd.nil_inv
  rw [instanceName_plain_some] at call_cd
  obtain ⟨rfl, rfl⟩ := u32Compact_eval_inv call_cd
  obtain ⟨l_b, rfl⟩ := d_b.var_inv; simp at l_b; subst l_b
  obtain ⟨l_a, rfl⟩ := d_sub.var_inv; simp at l_a; subst l_a
  obtain ⟨rfl, rfl⟩ := d_den.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at op_add
  subst op_add
  simp only [evalBinOp, Except.ok.injEq] at op_sub
  subst op_sub
  have hden_ne : (4294967296 : F) ≠ 0 := by decide
  simp only [evalBinOp, hden_ne, ↓reduceIte, Except.ok.injEq] at op_div
  subst op_div
  rw [matchPattern_bind] at mt6
  simp only [Except.ok.injEq, Option.some.injEq] at mt6
  subst mt6
  obtain ⟨_, m7, bs7, d_eq_b, mt7, d8⟩ := d7.letValue_inv
  obtain ⟨_, args_eq_b, app_eq_b⟩ := d_eq_b.builtin_inv
  obtain ⟨_, _, _, rfl, d_mul_b, args_eb1⟩ := args_eq_b.cons_inv
  obtain ⟨_, _, _, d_b1, d_b2, op_mul_b⟩ := d_mul_b.binary_inv
  obtain ⟨l_b1, rfl⟩ := d_b1.var_inv; simp at l_b1; subst l_b1
  obtain ⟨_, _, _, d_b21, d_b22, op_sub_b⟩ := d_b2.binary_inv
  obtain ⟨l_b21, rfl⟩ := d_b21.var_inv; simp at l_b21; subst l_b21
  obtain ⟨rfl, rfl⟩ := d_b22.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at op_sub_b
  subst op_sub_b
  simp only [evalBinOp, Except.ok.injEq] at op_mul_b
  subst op_mul_b
  obtain ⟨_, _, _, rfl, d_zero_b, nil_eb⟩ := args_eb1.cons_inv
  obtain ⟨rfl, rfl⟩ := d_zero_b.literal_inv
  obtain ⟨rfl, rfl⟩ := nil_eb.nil_inv
  simp only [Builtin.apply, evalAssertEq, Value.pointerFree, Value.field.injEq] at app_eq_b
  split_ifs at app_eq_b with _ h_valid
  rw [matchPattern_wildcard] at mt7
  simp only [Except.ok.injEq, Option.some.injEq] at mt7
  subst mt7
  obtain ⟨l_ret, rfl⟩ := d8.var_inv; simp at l_ret; subst l_ret
  have ha_lt := Aiur.Library.U32.pack_lt ha0 ha1 ha2 ha3
  have hb_lt := Aiur.Library.U32.pack_lt hb0 hb1 hb2 hb3
  have hd_lt := Aiur.Library.U32.pack_lt hd0 hd1 hd2 hd3
  have hbase_cast : ((Aiur.Library.U32.base : Nat) : F) = (4294967296 : F) := by
    unfold Aiur.Library.U32.base; norm_num
  have hvalid' :
      let borrow := (((Aiur.Library.U32.pack d0 d1_b d2_b d3_b : Nat) : F) +
        ((Aiur.Library.U32.pack b0 b1 b2 b3 : Nat) : F) -
        ((Aiur.Library.U32.pack a0 a1 a2 a3 : Nat) : F)) / (Aiur.Library.U32.base : F)
      borrow * (borrow - 1) = 0 := by
    rw [hbase_cast]; exact h_valid
  have hcmp := Aiur.Library.U32.compare_fields_sound
    Aiur.Library.U32.Goldilocks.compatible
    ((Aiur.Library.U32.pack a0 a1 a2 a3 : Nat) : F)
    ((Aiur.Library.U32.pack b0 b1 b2 b3 : Nat) : F)
    ha_lt hb_lt hd_lt rfl rfl hvalid'
  rw [hbase_cast] at hcmp
  have ha_val : ((Aiur.Library.U32.pack a0 a1 a2 a3 : Nat) : F).val =
      Aiur.Library.U32.pack a0 a1 a2 a3 :=
    zmod_val_natCast_of_le (by unfold Aiur.Library.U32.base at ha_lt; omega)
  have hb_val : ((Aiur.Library.U32.pack b0 b1 b2 b3 : Nat) : F).val =
      Aiur.Library.U32.pack b0 b1 b2 b3 :=
    zmod_val_natCast_of_le (by unfold Aiur.Library.U32.base at hb_lt; omega)
  refine ⟨1, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Mirrors.«UInt32::less_than_fields», ha_val, hb_val]
  have ha_lt' : Aiur.Library.U32.pack a0 a1 a2 a3 < 4294967296 := ha_lt
  have hb_lt' : Aiur.Library.U32.pack b0 b1 b2 b3 < 4294967296 := hb_lt
  simp [ha_lt', hb_lt', hcmp]

/-- `EvalFn W` refinement for `UInt32::less_than_fields` on bounded `Nat` values `≤ 4294967296`. -/
theorem u32LessThanFields_le_refines {h h' : Heap F} {r : SourceValue F} {a b : Nat}
    (ha : a ≤ 4294967296) (hb : b ≤ 4294967296)
    (ev : EvalFn W "UInt32::less_than_fields" [.field (a : F), .field (b : F)] h r h') :
    r = .field (if a < b then 1 else 0) ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := u32LessThanFields_complete ev
  have run := hk0 (k0 + 1) (by omega)
  simp only [Mirrors.«UInt32::less_than_fields», zmod_val_natCast_of_le ha,
    zmod_val_natCast_of_le hb] at run
  by_cases hlt : a < 4294967296 ∧ b < 4294967296
  · simp only [hlt.1, hlt.2, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at run
    exact ⟨run.1.symm, run.2.symm⟩
  · simp [hlt] at run

/-- `EvalFn W` refinement for `UInt32::less_than_fields` on 32-bit `Nat` values `< 4294967296`. -/
theorem u32LessThanFields_refines {h h' : Heap F} {r : SourceValue F} {a b : Nat}
    (ha : a < 4294967296) (hb : b < 4294967296)
    (ev : EvalFn W "UInt32::less_than_fields" [.field (a : F), .field (b : F)] h r h') :
    r = .field (if a < b then 1 else 0) ∧ h' = h :=
  u32LessThanFields_le_refines (Nat.le_of_lt ha) (Nat.le_of_lt hb) ev

/-- `EvalFn W` refinement for `UInt32::less_than_fields` on `(a : F) + 1` and `(b : F)` when `a, b < 4294967296`. -/
theorem u32LessThanFields_add_one_left_refines {h h' : Heap F} {r : SourceValue F} {a b : Nat}
    (ha : a < 4294967296) (hb : b < 4294967296)
    (ev : EvalFn W "UInt32::less_than_fields" [.field ((a : F) + 1), .field (b : F)] h r h') :
    r = .field (if a + 1 < b then 1 else 0) ∧ h' = h := by
  have hcast : ((a : F) + 1) = (((a + 1 : Nat) : F)) := by push_cast; rfl
  rw [hcast] at ev
  exact u32LessThanFields_le_refines (by omega) (Nat.le_of_lt hb) ev

theorem selectArm_ite_one_wildcard {types : Types} {h : Heap F} {P : Prop} [Decidable P]
    {e1 e0 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (if P then 1 else 0))
      [(.literal 1, e1), (.wildcard, e0)] = .ok (some (bs, body))) :
    (P ∧ bs = [] ∧ body = e1) ∨ (¬ P ∧ bs = [] ∧ body = e0) := by
  rcases selectArm_literal_inv sel with ⟨heq, rfl, rfl⟩ | ⟨hne, sel⟩
  · by_cases hP : P
    · exact .inl ⟨hP, rfl, rfl⟩
    · simp [hP] at heq
  · obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv sel
    by_cases hP : P
    · simp [hP] at hne
    · exact .inr ⟨hP, rfl, rfl⟩

theorem selectArm_ite_zero_wildcard {types : Types} {h : Heap F} {P : Prop} [Decidable P]
    {e0 e1 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (if P then 1 else 0))
      [(.literal 0, e0), (.wildcard, e1)] = .ok (some (bs, body))) :
    (¬ P ∧ bs = [] ∧ body = e0) ∨ (P ∧ bs = [] ∧ body = e1) := by
  rcases selectArm_literal_inv sel with ⟨heq, rfl, rfl⟩ | ⟨hne, sel⟩
  · by_cases hP : P
    · simp [hP] at heq
    · exact .inl ⟨hP, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv sel
    by_cases hP : P
    · exact .inr ⟨hP, rfl, rfl⟩
    · simp [hP] at hne

theorem selectArm_ite_one_zero {types : Types} {h : Heap F} {P : Prop} [Decidable P]
    {e1 e0 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (if P then 1 else 0))
      [(.literal 1, e1), (.literal 0, e0)] = .ok (some (bs, body))) :
    (P ∧ bs = [] ∧ body = e1) ∨ (¬ P ∧ bs = [] ∧ body = e0) := by
  rcases selectArm_literal_inv sel with ⟨heq, rfl, rfl⟩ | ⟨hne, sel⟩
  · by_cases hP : P
    · exact .inl ⟨hP, rfl, rfl⟩
    · simp [hP] at heq
  · rcases selectArm_literal_inv sel with ⟨heq0, rfl, rfl⟩ | ⟨hne0, sel⟩
    · by_cases hP : P
      · simp [hP] at heq0
      · exact .inr ⟨hP, rfl, rfl⟩
    · simp [SourceSemantics.selectArm] at sel

theorem selectArm_ite_zero_one {types : Types} {h : Heap F} {P : Prop} [Decidable P]
    {e0 e1 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (if P then 1 else 0))
      [(.literal 0, e0), (.literal 1, e1)] = .ok (some (bs, body))) :
    (¬ P ∧ bs = [] ∧ body = e0) ∨ (P ∧ bs = [] ∧ body = e1) := by
  rcases selectArm_literal_inv sel with ⟨heq0, rfl, rfl⟩ | ⟨hne0, sel⟩
  · by_cases hP : P
    · simp [hP] at heq0
    · exact .inl ⟨hP, rfl, rfl⟩
  · rcases selectArm_literal_inv sel with ⟨heq1, rfl, rfl⟩ | ⟨hne1, sel⟩
    · by_cases hP : P
      · exact .inr ⟨hP, rfl, rfl⟩
      · simp [hP] at heq1
    · simp [SourceSemantics.selectArm] at sel

theorem selectArm_bool_one_wildcard {types : Types} {h : Heap F} {b : Bool}
    {e1 e0 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (if b then 1 else 0))
      [(.literal 1, e1), (.wildcard, e0)] = .ok (some (bs, body))) :
    (b = true ∧ bs = [] ∧ body = e1) ∨ (b = false ∧ bs = [] ∧ body = e0) := by
  rcases selectArm_ite_one_wildcard (P := b = true) sel with ⟨hb, h1, h2⟩ | ⟨hnb, h1, h2⟩
  · exact .inl ⟨hb, h1, h2⟩
  · exact .inr ⟨Bool.eq_false_iff.mpr hnb, h1, h2⟩

theorem selectArm_bool_zero_wildcard {types : Types} {h : Heap F} {b : Bool}
    {e0 e1 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (if b then 1 else 0))
      [(.literal 0, e0), (.wildcard, e1)] = .ok (some (bs, body))) :
    (b = false ∧ bs = [] ∧ body = e0) ∨ (b = true ∧ bs = [] ∧ body = e1) := by
  rcases selectArm_ite_zero_wildcard (P := b = true) sel with ⟨hnb, h1, h2⟩ | ⟨hb, h1, h2⟩
  · exact .inl ⟨Bool.eq_false_iff.mpr hnb, h1, h2⟩
  · exact .inr ⟨hb, h1, h2⟩

theorem selectArm_bool_one_zero {types : Types} {h : Heap F} {b : Bool}
    {e1 e0 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (if b then 1 else 0))
      [(.literal 1, e1), (.literal 0, e0)] = .ok (some (bs, body))) :
    (b = true ∧ bs = [] ∧ body = e1) ∨ (b = false ∧ bs = [] ∧ body = e0) := by
  rcases selectArm_ite_one_zero (P := b = true) sel with ⟨hb, h1, h2⟩ | ⟨hnb, h1, h2⟩
  · exact .inl ⟨hb, h1, h2⟩
  · exact .inr ⟨Bool.eq_false_iff.mpr hnb, h1, h2⟩

theorem selectArm_bool_zero_one {types : Types} {h : Heap F} {b : Bool}
    {e0 e1 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (if b then 1 else 0))
      [(.literal 0, e0), (.literal 1, e1)] = .ok (some (bs, body))) :
    (b = false ∧ bs = [] ∧ body = e0) ∨ (b = true ∧ bs = [] ∧ body = e1) := by
  rcases selectArm_ite_zero_one (P := b = true) sel with ⟨hnb, h1, h2⟩ | ⟨hb, h1, h2⟩
  · exact .inl ⟨Bool.eq_false_iff.mpr hnb, h1, h2⟩
  · exact .inr ⟨hb, h1, h2⟩

theorem selectArm_sub_zero_wildcard {types : Types} {h : Heap F} {a b : Nat}
    (ha : a < 4294967296) (hb : b < 4294967296)
    {e0 e1 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field ((a : F) - (b : F)))
      [(.literal 0, e0), (.wildcard, e1)] = .ok (some (bs, body))) :
    (a = b ∧ bs = [] ∧ body = e0) ∨ (a ≠ b ∧ bs = [] ∧ body = e1) := by
  rcases selectArm_literal_inv sel with ⟨heq, rfl, rfl⟩ | ⟨hne, sel⟩
  · injection heq with hsub
    exact .inl ⟨(natCast_sub_eq_zero_iff ha hb).mp hsub, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv sel
    refine .inr ⟨fun h => hne (congrArg Value.field ((natCast_sub_eq_zero_iff ha hb).mpr h)), rfl, rfl⟩

theorem selectArm_nat_zero_wildcard {types : Types} {h : Heap F} {n : Nat}
    (hn : n ≤ 4294967296)
    {e0 e1 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (n : F))
      [(.literal 0, e0), (.wildcard, e1)] = .ok (some (bs, body))) :
    (n = 0 ∧ bs = [] ∧ body = e0) ∨ (n ≠ 0 ∧ bs = [] ∧ body = e1) := by
  rcases selectArm_literal_inv sel with ⟨heq, rfl, rfl⟩ | ⟨hne, sel⟩
  · injection heq with h0
    have hn0 : n = 0 := by
      have hv := congrArg ZMod.val h0
      simpa [zmod_val_natCast_of_le hn] using hv
    exact .inl ⟨hn0, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv sel
    refine .inr ⟨fun h => by subst h; exact hne (by simp), rfl, rfl⟩

theorem selectArm_nat_zero_one_wildcard {types : Types} {h : Heap F} {n : Nat}
    (hn : n < 4294967296)
    {e0 e1 e2 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (n : F))
      [(.literal 0, e0), (.literal 1, e1), (.wildcard, e2)] = .ok (some (bs, body))) :
    (n = 0 ∧ bs = [] ∧ body = e0) ∨
    (n = 1 ∧ bs = [] ∧ body = e1) ∨
    (n ≠ 0 ∧ n ≠ 1 ∧ bs = [] ∧ body = e2) := by
  rcases selectArm_literal_inv sel with ⟨heq0, rfl, rfl⟩ | ⟨hne0, sel⟩
  · injection heq0 with h0
    have hn0 : n = 0 := by
      have hv := congrArg ZMod.val h0
      simpa [zmod_val_natCast_of_le (Nat.le_of_lt hn)] using hv
    exact .inl ⟨hn0, rfl, rfl⟩
  · rcases selectArm_literal_inv sel with ⟨heq1, rfl, rfl⟩ | ⟨hne1, sel⟩
    · injection heq1 with h1
      have hn1 : n = 1 := by
        have hv := congrArg ZMod.val h1
        have h1_val : ((1 : F)).val = 1 := zmod_val_natCast_of_le (n := 1) (by decide)
        rw [zmod_val_natCast_of_le (Nat.le_of_lt hn), h1_val] at hv
        exact hv
      exact .inr (.inl ⟨hn1, rfl, rfl⟩)
    · obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv sel
      have hn0 : n ≠ 0 := fun h => by subst h; exact hne0 (by simp)
      have hn1 : n ≠ 1 := fun h => by subst h; exact hne1 (by simp)
      exact .inr (.inr ⟨hn0, hn1, rfl, rfl⟩)

theorem glistCmp_lt_three (a b : List Nat) : glistCmp a b < 3 := by
  induction a generalizing b with
  | nil => cases b <;> simp [glistCmp]
  | cons x ar ih =>
    cases b with
    | nil => simp [glistCmp]
    | cons y br =>
      simp only [glistCmp]
      split_ifs <;> try omega
      exact ih br

theorem selectArm_glistCmp {types : Types} {h : Heap F} (a b : List Nat)
    {e0 e1 e2 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (glistCmp a b : F))
      [(.literal 0, e0), (.literal 1, e1), (.wildcard, e2)] = .ok (some (bs, body))) :
    (glistCmp a b = 0 ∧ bs = [] ∧ body = e0) ∨
    (glistCmp a b = 1 ∧ bs = [] ∧ body = e1) ∨
    (glistCmp a b = 2 ∧ bs = [] ∧ body = e2) := by
  have hlt := glistCmp_lt_three a b
  rcases selectArm_nat_zero_one_wildcard (by omega) sel with h0 | h1 | ⟨hne0, hne1, hbs, hbody⟩
  · exact .inl h0
  · exact .inr (.inl h1)
  · exact .inr (.inr ⟨by omega, hbs, hbody⟩)

theorem selectArm_glistCmp_zero_wildcard {types : Types} {h : Heap F} (a b : List Nat)
    {e0 e1 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.field (glistCmp a b : F))
      [(.literal 0, e0), (.wildcard, e1)] = .ok (some (bs, body))) :
    (glistCmp a b = 0 ∧ bs = [] ∧ body = e0) ∨
    (glistCmp a b ≠ 0 ∧ bs = [] ∧ body = e1) := by
  have hlt := glistCmp_lt_three a b
  exact selectArm_nat_zero_wildcard (by omega) sel


theorem evalExpr_match_load_var_enum {types : Types} {locals : Environment F Nat}
    {name enumName ctor : String} {addr : Nat} {args : List (SourceValue F)}
    {arms : List (Generic.Pattern F × Generic.Expr F)} {before after : Heap F} {result : SourceValue F}
    (hfind : locals.find? (·.1 == name) = some (name, .ptr (.enum enumName) addr))
    (cell : before[addr]? = some (.construct enumName ctor args))
    (ev : EvalExpr W types locals (.matchValue (.load (.var name)) arms) before result after) :
    ∃ bs body,
      SourceSemantics.selectArm W types before (.construct enumName ctor args) arms = .ok (some (bs, body)) ∧
      EvalExpr W types (bs ++ locals) body before result after := by
  obtain ⟨_, _, bs, body, dScrut, sel, dArm⟩ := ev.matchValue_inv
  obtain ⟨_, dPtr, hload⟩ := dScrut.load_inv
  obtain ⟨hfind', rfl⟩ := dPtr.var_inv
  rw [hfind] at hfind'
  injection hfind' with hpair
  injection hpair with _ hptr
  subst hptr
  simp [loadValue, cell, Value.type] at hload
  cases hload
  exact ⟨bs, body, sel, dArm⟩

theorem evalExpr_add_inv {types : Types} {locals : Environment F Nat}
    {lhs rhs : Generic.Expr F} {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.binary .add lhs rhs) before result after) :
    ∃ a b middle,
      EvalExpr W types locals lhs before (.field a) middle ∧
      EvalExpr W types locals rhs middle (.field b) after ∧
      result = .field (a + b) := by
  obtain ⟨x, y, middle, dL, dR, hop⟩ := d.binary_inv
  cases x <;> cases y <;> simp [evalBinOp] at hop
  exact ⟨_, _, middle, dL, dR, hop.symm⟩

theorem evalExpr_sub_inv {types : Types} {locals : Environment F Nat}
    {lhs rhs : Generic.Expr F} {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.binary .sub lhs rhs) before result after) :
    ∃ a b middle,
      EvalExpr W types locals lhs before (.field a) middle ∧
      EvalExpr W types locals rhs middle (.field b) after ∧
      result = .field (a - b) := by
  obtain ⟨x, y, middle, dL, dR, hop⟩ := d.binary_inv
  cases x <;> cases y <;> simp [evalBinOp] at hop
  exact ⟨_, _, middle, dL, dR, hop.symm⟩

theorem evalExpr_mul_inv {types : Types} {locals : Environment F Nat}
    {lhs rhs : Generic.Expr F} {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.binary .mul lhs rhs) before result after) :
    ∃ a b middle,
      EvalExpr W types locals lhs before (.field a) middle ∧
      EvalExpr W types locals rhs middle (.field b) after ∧
      result = .field (a * b) := by
  obtain ⟨x, y, middle, dL, dR, hop⟩ := d.binary_inv
  cases x <;> cases y <;> simp [evalBinOp] at hop
  exact ⟨_, _, middle, dL, dR, hop.symm⟩

theorem evalExpr_tuple2_inv {types : Types} {locals : Environment F Nat}
    {e1 e2 : Generic.Expr F} {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.tuple [e1, e2]) before result after) :
    ∃ v1 v2 h1,
      EvalExpr W types locals e1 before v1 h1 ∧
      EvalExpr W types locals e2 h1 v2 after ∧
      result = .tuple [v1, v2] := by
  obtain ⟨_, dArgs, rfl⟩ := d.tuple_inv
  obtain ⟨v1, _, h1, rfl, d1, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v2, _, _, rfl, d2, dArgs⟩ := dArgs.cons_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨v1, v2, h1, d1, d2, rfl⟩

theorem _root_.Aiur.Generic.SourceSemantics.EvalExpr.var_inv'
    {types : Types} {locals : Environment F Nat}
    {name : String} {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.var name) before result after) :
    locals.find? (·.1 == name) = some (name, result) ∧ after = before :=
  d.var_inv

theorem evalExpr_call1_inv {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Generic.Ty)} {e1 : Generic.Expr F}
    {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.call name typeArgs [e1]) before result after) :
    ∃ v1 h1,
      EvalExpr W types locals e1 before v1 h1 ∧
      EvalFn W (instanceName types name typeArgs) [v1] h1 result after := by
  obtain ⟨_, h1, dArgs, dFn⟩ := d.call_inv
  obtain ⟨v1, _, _, rfl, d1, dArgs⟩ := dArgs.cons_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨v1, h1, d1, dFn⟩

theorem evalExpr_call2_inv {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Generic.Ty)} {e1 e2 : Generic.Expr F}
    {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.call name typeArgs [e1, e2]) before result after) :
    ∃ v1 v2 h1 h2,
      EvalExpr W types locals e1 before v1 h1 ∧
      EvalExpr W types locals e2 h1 v2 h2 ∧
      EvalFn W (instanceName types name typeArgs) [v1, v2] h2 result after := by
  obtain ⟨_, h2, dArgs, dFn⟩ := d.call_inv
  obtain ⟨v1, _, h1, rfl, d1, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v2, _, _, rfl, d2, dArgs⟩ := dArgs.cons_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨v1, v2, h1, h2, d1, d2, dFn⟩

theorem evalExpr_call3_inv {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Generic.Ty)} {e1 e2 e3 : Generic.Expr F}
    {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.call name typeArgs [e1, e2, e3]) before result after) :
    ∃ v1 v2 v3 h1 h2 h3,
      EvalExpr W types locals e1 before v1 h1 ∧
      EvalExpr W types locals e2 h1 v2 h2 ∧
      EvalExpr W types locals e3 h2 v3 h3 ∧
      EvalFn W (instanceName types name typeArgs) [v1, v2, v3] h3 result after := by
  obtain ⟨_, h3, dArgs, dFn⟩ := d.call_inv
  obtain ⟨v1, _, h1, rfl, d1, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v2, _, h2, rfl, d2, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v3, _, _, rfl, d3, dArgs⟩ := dArgs.cons_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨v1, v2, v3, h1, h2, h3, d1, d2, d3, dFn⟩

theorem evalExpr_call4_inv {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Generic.Ty)} {e1 e2 e3 e4 : Generic.Expr F}
    {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.call name typeArgs [e1, e2, e3, e4]) before result after) :
    ∃ v1 v2 v3 v4 h1 h2 h3 h4,
      EvalExpr W types locals e1 before v1 h1 ∧
      EvalExpr W types locals e2 h1 v2 h2 ∧
      EvalExpr W types locals e3 h2 v3 h3 ∧
      EvalExpr W types locals e4 h3 v4 h4 ∧
      EvalFn W (instanceName types name typeArgs) [v1, v2, v3, v4] h4 result after := by
  obtain ⟨_, h4, dArgs, dFn⟩ := d.call_inv
  obtain ⟨v1, _, h1, rfl, d1, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v2, _, h2, rfl, d2, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v3, _, h3, rfl, d3, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v4, _, _, rfl, d4, dArgs⟩ := dArgs.cons_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨v1, v2, v3, v4, h1, h2, h3, h4, d1, d2, d3, d4, dFn⟩

theorem evalExpr_call5_inv {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Generic.Ty)} {e1 e2 e3 e4 e5 : Generic.Expr F}
    {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.call name typeArgs [e1, e2, e3, e4, e5]) before result after) :
    ∃ v1 v2 v3 v4 v5 h1 h2 h3 h4 h5,
      EvalExpr W types locals e1 before v1 h1 ∧
      EvalExpr W types locals e2 h1 v2 h2 ∧
      EvalExpr W types locals e3 h2 v3 h3 ∧
      EvalExpr W types locals e4 h3 v4 h4 ∧
      EvalExpr W types locals e5 h4 v5 h5 ∧
      EvalFn W (instanceName types name typeArgs) [v1, v2, v3, v4, v5] h5 result after := by
  obtain ⟨_, h5, dArgs, dFn⟩ := d.call_inv
  obtain ⟨v1, _, h1, rfl, d1, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v2, _, h2, rfl, d2, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v3, _, h3, rfl, d3, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v4, _, h4, rfl, d4, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v5, _, _, rfl, d5, dArgs⟩ := dArgs.cons_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨v1, v2, v3, v4, v5, h1, h2, h3, h4, h5, d1, d2, d3, d4, d5, dFn⟩

theorem evalExpr_store_construct0_inv {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Generic.Ty)} {ctor : String}
    {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.store (.construct name typeArgs ctor [])) before result after) :
    result = .ptr (.enum (instanceName types name typeArgs)) before.length ∧
    after = before ++ [.construct (instanceName types name typeArgs) ctor []] := by
  obtain ⟨_, _, dCtor, rfl, rfl⟩ := d.store_inv
  obtain ⟨_, dArgs, rfl⟩ := dCtor.construct_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨by simp [Value.type], rfl⟩

theorem evalExpr_store_construct1_inv {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Generic.Ty)} {ctor : String} {e1 : Generic.Expr F}
    {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.store (.construct name typeArgs ctor [e1])) before result after) :
    ∃ v1 h1,
      EvalExpr W types locals e1 before v1 h1 ∧
      result = .ptr (.enum (instanceName types name typeArgs)) h1.length ∧
      after = h1 ++ [.construct (instanceName types name typeArgs) ctor [v1]] := by
  obtain ⟨_, h1, dCtor, rfl, rfl⟩ := d.store_inv
  obtain ⟨_, dArgs, rfl⟩ := dCtor.construct_inv
  obtain ⟨v1, _, _, rfl, d1, dArgs⟩ := dArgs.cons_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨v1, h1, d1, by simp [Value.type], rfl⟩

theorem evalExpr_store_construct2_inv {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Generic.Ty)} {ctor : String} {e1 e2 : Generic.Expr F}
    {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.store (.construct name typeArgs ctor [e1, e2])) before result after) :
    ∃ v1 v2 h1 h2,
      EvalExpr W types locals e1 before v1 h1 ∧
      EvalExpr W types locals e2 h1 v2 h2 ∧
      result = .ptr (.enum (instanceName types name typeArgs)) h2.length ∧
      after = h2 ++ [.construct (instanceName types name typeArgs) ctor [v1, v2]] := by
  obtain ⟨_, h2, dCtor, rfl, rfl⟩ := d.store_inv
  obtain ⟨_, dArgs, rfl⟩ := dCtor.construct_inv
  obtain ⟨v1, _, h1, rfl, d1, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v2, _, _, rfl, d2, dArgs⟩ := dArgs.cons_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨v1, v2, h1, h2, d1, d2, by simp [Value.type], rfl⟩

theorem evalExpr_store_construct3_inv {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Generic.Ty)} {ctor : String} {e1 e2 e3 : Generic.Expr F}
    {before after : Heap F} {result : SourceValue F}
    (d : EvalExpr W types locals (.store (.construct name typeArgs ctor [e1, e2, e3])) before result after) :
    ∃ v1 v2 v3 h1 h2 h3,
      EvalExpr W types locals e1 before v1 h1 ∧
      EvalExpr W types locals e2 h1 v2 h2 ∧
      EvalExpr W types locals e3 h2 v3 h3 ∧
      result = .ptr (.enum (instanceName types name typeArgs)) h3.length ∧
      after = h3 ++ [.construct (instanceName types name typeArgs) ctor [v1, v2, v3]] := by
  obtain ⟨_, h3, dCtor, rfl, rfl⟩ := d.store_inv
  obtain ⟨_, dArgs, rfl⟩ := dCtor.construct_inv
  obtain ⟨v1, _, h1, rfl, d1, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v2, _, h2, rfl, d2, dArgs⟩ := dArgs.cons_inv
  obtain ⟨v3, _, _, rfl, d3, dArgs⟩ := dArgs.cons_inv
  obtain ⟨rfl, rfl⟩ := dArgs.nil_inv
  exact ⟨v1, v2, v3, h1, h2, h3, d1, d2, d3, by simp [Value.type], rfl⟩


/-! ### Subsection 1: Structural & Query Functions (`level_is_not_zero`, `level_eq`, `level_struct_eq`, `level_offset_of`, `level_explicit_val`) -/

theorem selectArm_bool_pair_zero_zero {types : Types} {h : Heap F} (b1 b2 : Bool)
    {e0 e1 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h
      (.tuple [.field (if b1 then 1 else 0), .field (if b2 then 1 else 0)])
      [((.tuple [.literal 0, .literal 0]), e0), (.wildcard, e1)] = .ok (some (bs, body))) :
    ((b1 || b2) = false ∧ bs = [] ∧ body = e0) ∨
    ((b1 || b2) = true ∧ bs = [] ∧ body = e1) := by
  cases b1 <;> cases b2 <;> {
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_tuple, matchPattern_literal,
      matchPattern_wildcard, SourceSemantics.matchListWith,
      bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    simp
  }

/-- **`EvalFn W` refinement for `KernelLevels::level_is_not_zero`.** -/
theorem levelIsNotZero_refines {h h' : Heap F} {l : Ix.Kernel.Level}
    {ptr r : SourceValue F}
    (rep : RepKLevel h l ptr)
    (ev : EvalFn W "KernelLevels::level_is_not_zero" [ptr] h r h') :
    r = .field (if l.isNeverZero then 1 else 0) ∧ h' = h := by
  induction rep generalizing r h' with
  | zero cell =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_is_not_zero»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [Ix.Kernel.Level.isNeverZero]
  | succ cell _ _ =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_is_not_zero»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [Ix.Kernel.Level.isNeverZero]
  | max cell repA repB iha ihb =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_is_not_zero»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, bs2, body2, dTuple, sel2, dArm2⟩ := dArm.matchValue_inv
    obtain ⟨_, _, _, dCallA, dCallB, rfl⟩ := evalExpr_tuple2_inv dTuple
    obtain ⟨_, _, dVarA, dFnA⟩ := evalExpr_call1_inv dCallA
    obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
    simp only [instanceName] at dFnA
    obtain ⟨rfl, rfl⟩ := iha dFnA
    obtain ⟨_, _, dVarB, dFnB⟩ := evalExpr_call1_inv dCallB
    obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
    simp only [instanceName] at dFnB
    obtain ⟨rfl, rfl⟩ := ihb dFnB
    rcases selectArm_bool_pair_zero_zero _ _ sel2 with ⟨hor, rfl, rfl⟩ | ⟨hor, rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [Ix.Kernel.Level.isNeverZero, hor]
    · obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [Ix.Kernel.Level.isNeverZero, hor]
  | imax cell _ repB _ ihb =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_is_not_zero»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
      matchPattern_bind, SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, dVarB, dFnB⟩ := evalExpr_call1_inv dArm
    obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
    simp only [instanceName] at dFnB
    dsimp only [Ix.Kernel.Level.isNeverZero]
    exact ihb dFnB
  | param _ cell =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_is_not_zero»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_is_not_zero»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [Ix.Kernel.Level.isNeverZero]

theorem field_mul_bool_ite (b1 b2 : Bool) :
    ((if b1 then (1 : F) else 0) * (if b2 then (1 : F) else 0)) =
      if (b1 && b2) then (1 : F) else 0 := by
  cases b1 <;> cases b2 <;> simp

@[simp] theorem level_beq_succ (u v : Ix.Kernel.Level) :
    (Ix.Kernel.Level.succ u == Ix.Kernel.Level.succ v) = (u == v) := by
  simp [BEq.beq, Ix.Kernel.Level.beq]

@[simp] theorem level_beq_max (a1 a2 b1 b2 : Ix.Kernel.Level) :
    (Ix.Kernel.Level.max a1 a2 == Ix.Kernel.Level.max b1 b2) = ((a1 == b1) && (a2 == b2)) := by
  simp [BEq.beq, Ix.Kernel.Level.beq]

@[simp] theorem level_beq_imax (a1 a2 b1 b2 : Ix.Kernel.Level) :
    (Ix.Kernel.Level.imax a1 a2 == Ix.Kernel.Level.imax b1 b2) = ((a1 == b1) && (a2 == b2)) := by
  simp [BEq.beq, Ix.Kernel.Level.beq]

@[simp] theorem level_beq_param (i j : Nat) :
    (Ix.Kernel.Level.param i == Ix.Kernel.Level.param j) = decide (i = j) := by
  simp [BEq.beq, Ix.Kernel.Level.beq]

/-- **`EvalFn W` refinement for `KernelLevels::level_eq`.** -/
theorem levelEq_refines {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB r : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (ev : EvalFn W "KernelLevels::level_eq" [ptrA, ptrB] h r h') :
    r = .field (if a == b then 1 else 0) ∧ h' = h := by
  induction repA generalizing b ptrB r h' with
  | zero cellA =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | zero cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
    | succ cellB _ | max cellB _ _ | imax cellB _ _ | param _ cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
  | succ cellA repA1 ih1 =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | succ cellB repB1 =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, _, _, dVar1, dVar2, dFn⟩ := evalExpr_call2_inv dArm2
      obtain ⟨⟨⟩, rfl⟩ := dVar1.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVar2.var_inv'
      simp only [instanceName] at dFn
      obtain ⟨rfl, rfl⟩ := ih1 repB1 dFn
      simp
    | zero cellB | max cellB _ _ | imax cellB _ _ | param _ cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
  | max cellA repA1 repA2 ih1 ih2 =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | max cellB repB1 repB2 =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, _, dL, dR, rfl⟩ := evalExpr_mul_inv dArm2
      obtain ⟨_, _, _, _, dVarA1, dVarB1, dFn1⟩ := evalExpr_call2_inv dL
      obtain ⟨⟨⟩, rfl⟩ := dVarA1.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarB1.var_inv'
      simp only [instanceName] at dFn1
      obtain ⟨heq1, rfl⟩ := ih1 repB1 dFn1
      injection heq1 with h1_eq; subst h1_eq
      obtain ⟨_, _, _, _, dVarA2, dVarB2, dFn2⟩ := evalExpr_call2_inv dR
      obtain ⟨⟨⟩, rfl⟩ := dVarA2.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarB2.var_inv'
      simp only [instanceName] at dFn2
      obtain ⟨heq2, rfl⟩ := ih2 repB2 dFn2
      injection heq2 with h2_eq; subst h2_eq
      rw [field_mul_bool_ite]
      refine ⟨congrArg Value.field ?_, rfl⟩
      simp
    | zero cellB | succ cellB _ | imax cellB _ _ | param _ cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
  | imax cellA repA1 repA2 ih1 ih2 =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | imax cellB repB1 repB2 =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, _, dL, dR, rfl⟩ := evalExpr_mul_inv dArm2
      obtain ⟨_, _, _, _, dVarA1, dVarB1, dFn1⟩ := evalExpr_call2_inv dL
      obtain ⟨⟨⟩, rfl⟩ := dVarA1.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarB1.var_inv'
      simp only [instanceName] at dFn1
      obtain ⟨heq1, rfl⟩ := ih1 repB1 dFn1
      injection heq1 with h1_eq; subst h1_eq
      obtain ⟨_, _, _, _, dVarA2, dVarB2, dFn2⟩ := evalExpr_call2_inv dR
      obtain ⟨⟨⟩, rfl⟩ := dVarA2.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarB2.var_inv'
      simp only [instanceName] at dFn2
      obtain ⟨heq2, rfl⟩ := ih2 repB2 dFn2
      injection heq2 with h2_eq; subst h2_eq
      rw [field_mul_bool_ite]
      refine ⟨congrArg Value.field ?_, rfl⟩
      simp
    | zero cellB | succ cellB _ | max cellB _ _ | param _ cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
  | param hi cellA =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | param hj cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, dSub, dFn⟩ := evalExpr_call1_inv dArm2
      obtain ⟨_, _, _, dVarI, dVarJ, rfl⟩ := evalExpr_sub_inv dSub
      obtain ⟨⟨⟩, rfl⟩ := dVarI.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarJ.var_inv'
      simp only [instanceName] at dFn
      obtain ⟨rfl, rfl⟩ := fieldsIsZero_sub_refines hi hj dFn
      simp
    | zero cellB | succ cellB _ | max cellB _ _ | imax cellB _ _ =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp

/-- **`EvalFn W` refinement for `KernelLevels::level_struct_eq`.** -/
theorem levelStructEq_refines {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB r : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (ev : EvalFn W "KernelLevels::level_struct_eq" [ptrA, ptrB] h r h') :
    r = .field (if a == b then 1 else 0) ∧ h' = h := by
  induction repA generalizing b ptrB r h' with
  | zero cellA =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_struct_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_struct_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_struct_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | zero cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
    | succ cellB _ | max cellB _ _ | imax cellB _ _ | param _ cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
  | succ cellA repA1 ih1 =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_struct_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_struct_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_struct_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | succ cellB repB1 =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, _, _, dVar1, dVar2, dFn⟩ := evalExpr_call2_inv dArm2
      obtain ⟨⟨⟩, rfl⟩ := dVar1.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVar2.var_inv'
      simp only [instanceName] at dFn
      obtain ⟨rfl, rfl⟩ := ih1 repB1 dFn
      simp
    | zero cellB | max cellB _ _ | imax cellB _ _ | param _ cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
  | max cellA repA1 repA2 ih1 ih2 =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_struct_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_struct_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_struct_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | max cellB repB1 repB2 =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, _, dL, dR, rfl⟩ := evalExpr_mul_inv dArm2
      obtain ⟨_, _, _, _, dVarA1, dVarB1, dFn1⟩ := evalExpr_call2_inv dL
      obtain ⟨⟨⟩, rfl⟩ := dVarA1.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarB1.var_inv'
      simp only [instanceName] at dFn1
      obtain ⟨heq1, rfl⟩ := ih1 repB1 dFn1
      injection heq1 with h1_eq; subst h1_eq
      obtain ⟨_, _, _, _, dVarA2, dVarB2, dFn2⟩ := evalExpr_call2_inv dR
      obtain ⟨⟨⟩, rfl⟩ := dVarA2.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarB2.var_inv'
      simp only [instanceName] at dFn2
      obtain ⟨heq2, rfl⟩ := ih2 repB2 dFn2
      injection heq2 with h2_eq; subst h2_eq
      rw [field_mul_bool_ite]
      refine ⟨congrArg Value.field ?_, rfl⟩
      simp
    | zero cellB | succ cellB _ | imax cellB _ _ | param _ cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
  | imax cellA repA1 repA2 ih1 ih2 =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_struct_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_struct_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_struct_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | imax cellB repB1 repB2 =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, _, dL, dR, rfl⟩ := evalExpr_mul_inv dArm2
      obtain ⟨_, _, _, _, dVarA1, dVarB1, dFn1⟩ := evalExpr_call2_inv dL
      obtain ⟨⟨⟩, rfl⟩ := dVarA1.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarB1.var_inv'
      simp only [instanceName] at dFn1
      obtain ⟨heq1, rfl⟩ := ih1 repB1 dFn1
      injection heq1 with h1_eq; subst h1_eq
      obtain ⟨_, _, _, _, dVarA2, dVarB2, dFn2⟩ := evalExpr_call2_inv dR
      obtain ⟨⟨⟩, rfl⟩ := dVarA2.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarB2.var_inv'
      simp only [instanceName] at dFn2
      obtain ⟨heq2, rfl⟩ := ih2 repB2 dFn2
      injection heq2 with h2_eq; subst h2_eq
      rw [field_mul_bool_ite]
      refine ⟨congrArg Value.field ?_, rfl⟩
      simp
    | zero cellB | succ cellB _ | max cellB _ _ | param _ cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp
  | param hi cellA =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_struct_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_struct_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_struct_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | param hj cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dSub, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, dVarI, dVarJ, rfl⟩ := evalExpr_sub_inv dSub
      obtain ⟨⟨⟩, rfl⟩ := dVarI.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarJ.var_inv'
      rcases selectArm_sub_zero_wildcard hi hj sel3 with ⟨heq, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := dArm3.literal_inv
        simp [heq]
      · obtain ⟨rfl, rfl⟩ := dArm3.literal_inv
        simp [hne]
    | zero cellB | succ cellB _ | max cellB _ _ | imax cellB _ _ =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp

/-- **`EvalFn W` refinement for `KernelLevels::level_offset_of` with arbitrary accumulator `acc`.** -/
theorem levelOffsetOfAcc_refines {h h' : Heap F} {l : Ix.Kernel.Level}
    {ptr r : SourceValue F} {acc : Nat}
    (rep : RepKLevel h l ptr)
    (ev : EvalFn W "KernelLevels::level_offset_of" [ptr, .field (acc : F)] h r h') :
    ∃ basePtr,
      r = .tuple [basePtr, .field ((levelOffsetOfAcc l acc).2 : F)] ∧
      RepKLevel h (levelOffsetOfAcc l acc).1 basePtr ∧
      h' = h := by
  induction rep generalizing acc r h' with
  | succ cell repInner ih =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_offset_of»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_offset_of», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_offset_of»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, _, _, dVar, dAdd, dFn⟩ := evalExpr_call2_inv dArm
    obtain ⟨⟨⟩, rfl⟩ := dVar.var_inv'
    obtain ⟨_, _, _, dVarK, dLit1, rfl⟩ := evalExpr_add_inv dAdd
    obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dLit1.literal_inv
    simp only [instanceName] at dFn
    have hcast : ((acc : F) + 1) = (((acc + 1 : Nat) : F)) := by push_cast; rfl
    rw [hcast] at dFn
    simpa [levelOffsetOfAcc] using ih dFn
  | zero cell | max cell _ _ | imax cell _ _ | param _ cell =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_offset_of»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_offset_of», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_offset_of»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, _, dVarL, dVarK, rfl⟩ := evalExpr_tuple2_inv dArm
    obtain ⟨⟨⟩, rfl⟩ := dVarL.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
    first
    | exact ⟨_, rfl, .zero cell, rfl⟩
    | exact ⟨_, rfl, .max cell ‹_› ‹_›, rfl⟩
    | exact ⟨_, rfl, .imax cell ‹_› ‹_›, rfl⟩
    | exact ⟨_, rfl, .param ‹_› cell, rfl⟩

/-- **`EvalFn W` refinement for `KernelLevels::level_offset_of` at `acc = 0`.** -/
theorem levelOffsetOf_refines {h h' : Heap F} {l : Ix.Kernel.Level}
    {ptr r : SourceValue F}
    (rep : RepKLevel h l ptr)
    (ev : EvalFn W "KernelLevels::level_offset_of" [ptr, .field 0] h r h') :
    ∃ basePtr,
      r = .tuple [basePtr, .field ((levelOffsetOf l).2 : F)] ∧
      RepKLevel h (levelOffsetOf l).1 basePtr ∧
      h' = h := by
  have h0 : (0 : F) = ((0 : Nat) : F) := by simp
  rw [h0] at ev
  obtain ⟨basePtr, hr, hrep, hh⟩ := levelOffsetOfAcc_refines rep ev
  rw [levelOffsetOfAcc_eq, Nat.zero_add] at hr hrep
  exact ⟨basePtr, hr, hrep, hh⟩

theorem selectArm_explicitVal_tuple {types : Types} {h : Heap F} (opt : Option Nat)
    {varName : String} {e1 e0 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h
      (.tuple [.field (if opt.isSome then 1 else 0), .field (opt.getD 0 : F)])
      [((.tuple [(.literal 1), (.bind varName)]), e1), (.wildcard, e0)] = .ok (some (bs, body))) :
    (∃ n, opt = some n ∧ bs = [(varName, .field (n : F))] ∧ body = e1) ∨
    (opt = none ∧ bs = [] ∧ body = e0) := by
  cases opt with
  | none =>
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_tuple, matchPattern_literal,
      matchPattern_wildcard, SourceSemantics.matchListWith,
      bind, Except.bind, pure, Except.pure] at sel
    exact .inr ⟨rfl, sel.1, sel.2.symm⟩
  | some n =>
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_tuple, matchPattern_literal,
      matchPattern_bind, SourceSemantics.matchListWith,
      bind, Except.bind, pure, Except.pure] at sel
    exact .inl ⟨n, rfl, sel.1.symm, sel.2.symm⟩

/-- **`EvalFn W` refinement for `KernelLevels::level_explicit_val`.** -/
theorem levelExplicitVal_refines {h h' : Heap F} {l : Ix.Kernel.Level}
    {ptr r : SourceValue F}
    (rep : RepKLevel h l ptr)
    (ev : EvalFn W "KernelLevels::level_explicit_val" [ptr] h r h') :
    r = .tuple [
      .field (if (levelExplicitVal l).isSome then 1 else 0),
      .field ((levelExplicitVal l).getD 0 : F)
    ] ∧ h' = h := by
  induction rep generalizing r h' with
  | zero cell =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_explicit_val»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_explicit_val», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_explicit_val»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, _, dLit1, dLit0, rfl⟩ := evalExpr_tuple2_inv dArm
    obtain ⟨⟨⟩, rfl⟩ := dLit1.literal_inv
    obtain ⟨⟨⟩, rfl⟩ := dLit0.literal_inv
    simp [levelExplicitVal]
  | succ cell repInner ih =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_explicit_val»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_explicit_val», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_explicit_val»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, bs2, body2, dCall, sel2, dArm2⟩ := dArm.matchValue_inv
    obtain ⟨_, _, dVar, dFn⟩ := evalExpr_call1_inv dCall
    obtain ⟨⟨⟩, rfl⟩ := dVar.var_inv'
    simp only [instanceName] at dFn
    obtain ⟨rfl, rfl⟩ := ih dFn
    rcases selectArm_explicitVal_tuple _ sel2 with ⟨n, hopt, rfl, rfl⟩ | ⟨hopt, rfl, rfl⟩
    · obtain ⟨_, _, _, dLit1, dAdd, rfl⟩ := evalExpr_tuple2_inv dArm2
      obtain ⟨⟨⟩, rfl⟩ := dLit1.literal_inv
      obtain ⟨_, _, _, dVarN, dLitOne, rfl⟩ := evalExpr_add_inv dAdd
      obtain ⟨⟨⟩, rfl⟩ := dVarN.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dLitOne.literal_inv
      simp [levelExplicitVal, hopt]
    · obtain ⟨_, _, _, dLit0, dLit0', rfl⟩ := evalExpr_tuple2_inv dArm2
      obtain ⟨⟨⟩, rfl⟩ := dLit0.literal_inv
      obtain ⟨⟨⟩, rfl⟩ := dLit0'.literal_inv
      simp [levelExplicitVal, hopt]
  | max cell _ _ | imax cell _ _ | param _ cell =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_explicit_val»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::level_explicit_val», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::level_explicit_val»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, _, dLit0, dLit0', rfl⟩ := evalExpr_tuple2_inv dArm
    obtain ⟨⟨⟩, rfl⟩ := dLit0.literal_inv
    obtain ⟨⟨⟩, rfl⟩ := dLit0'.literal_inv
    simp [levelExplicitVal]


/-! ### Subsection 2: Smart Constructors (`level_max_offsets`, `level_max_subsumes`, `level_max_go`, `level_max`, `level_imax`) -/

/-- **`EvalFn W` refinement for `KernelLevels::level_max_offsets`.** -/
theorem levelMaxOffsets_refines {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB r : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (ha : levelDepth a < 4294967296) (hb : levelDepth b < 4294967296)
    (ev : EvalFn W "KernelLevels::level_max_offsets" [ptrA, ptrB] h r h') :
    RepKLevel h' (levelMaxOffsets a b) r ∧ Heap.Extends h h' := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_max_offsets»)
    (by simp [IxVM.Checked.Fn.«KernelLevels::level_max_offsets», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«KernelLevels::level_max_offsets»] at ev
  obtain ⟨_, _, bs1, body1, dCall1, sel1, dArm1⟩ := ev.matchValue_inv
  obtain ⟨_, _, _, _, dVarA, dLit0, dFn1⟩ := evalExpr_call2_inv dCall1
  obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
  obtain ⟨⟨⟩, rfl⟩ := dLit0.literal_inv
  simp only [instanceName] at dFn1
  obtain ⟨basePtrA, rfl, repBaseA, rfl⟩ := levelOffsetOf_refines repA dFn1
  simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_tuple, matchPattern_bind,
    SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel1
  obtain ⟨rfl, rfl⟩ := sel1
  obtain ⟨_, _, bs2, body2, dCall2, sel2, dArm2⟩ := dArm1.matchValue_inv
  obtain ⟨_, _, _, _, dVarB, dLit0', dFn2⟩ := evalExpr_call2_inv dCall2
  obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
  obtain ⟨⟨⟩, rfl⟩ := dLit0'.literal_inv
  simp only [instanceName] at dFn2
  obtain ⟨basePtrB, rfl, repBaseB, rfl⟩ := levelOffsetOf_refines repB dFn2
  simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_tuple, matchPattern_bind,
    SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
  obtain ⟨rfl, rfl⟩ := sel2
  obtain ⟨_, _, bs3, body3, dCall3, sel3, dArm3⟩ := dArm2.matchValue_inv
  obtain ⟨_, _, _, _, dVarBaseA, dVarBaseB, dFn3⟩ := evalExpr_call2_inv dCall3
  obtain ⟨⟨⟩, rfl⟩ := dVarBaseA.var_inv'
  obtain ⟨⟨⟩, rfl⟩ := dVarBaseB.var_inv'
  simp only [instanceName] at dFn3
  obtain ⟨rfl, rfl⟩ := levelStructEq_refines repBaseA repBaseB dFn3
  rcases selectArm_bool_one_zero sel3 with ⟨heq, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
  · have hbase : (levelOffsetOf a).1 = (levelOffsetOf b).1 := eq_of_beq heq
    obtain ⟨_, _, bs4, body4, dCall4, sel4, dArm4⟩ := dArm3.matchValue_inv
    obtain ⟨_, _, _, _, dVarOffA, dVarOffB, dFn4⟩ := evalExpr_call2_inv dCall4
    obtain ⟨⟨⟩, rfl⟩ := dVarOffA.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarOffB.var_inv'
    simp only [instanceName] at dFn4
    have hoffA : (levelOffsetOf a).2 < 4294967296 :=
      Nat.lt_of_le_of_lt (levelOffsetOf_le_depth a) ha
    have hoffB : (levelOffsetOf b).2 < 4294967296 :=
      Nat.lt_of_le_of_lt (levelOffsetOf_le_depth b) hb
    obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hoffA hoffB dFn4
    rcases selectArm_ite_one_zero sel4 with ⟨hlt, rfl, rfl⟩ | ⟨hnlt, rfl, rfl⟩
    · obtain ⟨⟨⟩, rfl⟩ := dArm4.var_inv'
      simp only [levelMaxOffsets, hbase, ↓reduceIte, hlt]
      exact ⟨repB, Heap.Extends.refl _⟩
    · obtain ⟨⟨⟩, rfl⟩ := dArm4.var_inv'
      simp only [levelMaxOffsets, hbase, ↓reduceIte, hnlt]
      exact ⟨repA, Heap.Extends.refl _⟩
  · have hbase : (levelOffsetOf a).1 ≠ (levelOffsetOf b).1 :=
      fun h => by rw [beq_iff_eq.mpr h] at hne; cases hne
    obtain ⟨_, _, _, _, dVarA2, dVarB2, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm3
    obtain ⟨⟨⟩, rfl⟩ := dVarA2.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarB2.var_inv'
    simp only [levelMaxOffsets, hbase, ↓reduceIte, klevel_inst]
    exact RepKLevel.allocMax repA repB

/-- **`EvalFn W` refinement for `KernelLevels::level_max_subsumes`.** -/
theorem levelMaxSubsumes_refines {h h' : Heap F} {m x : Ix.Kernel.Level}
    {ptrM ptrX r : SourceValue F}
    (repM : RepKLevel h m ptrM) (repX : RepKLevel h x ptrX)
    (ev : EvalFn W "KernelLevels::level_max_subsumes" [ptrM, ptrX] h r h') :
    r = .field (if levelMaxSubsumes m x then 1 else 0) ∧ h' = h := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_max_subsumes»)
    (by simp [IxVM.Checked.Fn.«KernelLevels::level_max_subsumes», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«KernelLevels::level_max_subsumes»] at ev
  cases repM with
  | max cellM repL repR =>
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellM ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, bs2, body2, dCall1, sel2, dArm2⟩ := dArm.matchValue_inv
    obtain ⟨_, _, _, _, dVarL, dVarX, dFn1⟩ := evalExpr_call2_inv dCall1
    obtain ⟨⟨⟩, rfl⟩ := dVarL.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarX.var_inv'
    simp only [instanceName] at dFn1
    obtain ⟨rfl, rfl⟩ := levelStructEq_refines repL repX dFn1
    rcases selectArm_bool_one_zero sel2 with ⟨heqL, rfl, rfl⟩ | ⟨hneL, rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      have hLx : _ = x := eq_of_beq heqL
      simp [levelMaxSubsumes, hLx]
    · have hLx : _ ≠ x := fun h => by rw [beq_iff_eq.mpr h] at hneL; cases hneL
      obtain ⟨_, _, _, _, dVarR, dVarX2, dFn2⟩ := evalExpr_call2_inv dArm2
      obtain ⟨⟨⟩, rfl⟩ := dVarR.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarX2.var_inv'
      simp only [instanceName] at dFn2
      obtain ⟨rfl, rfl⟩ := levelStructEq_refines repR repX dFn2
      simp [levelMaxSubsumes, hLx]
  | zero cellM | succ cellM _ | imax cellM _ _ | param _ cellM =>
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellM ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [levelMaxSubsumes]

/-- **`EvalFn W` refinement for `KernelLevels::level_max_go`.** -/
theorem levelMaxGo_refines {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB r : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (ha : levelDepth a < 4294967296) (hb : levelDepth b < 4294967296)
    (ev : EvalFn W "KernelLevels::level_max_go" [ptrA, ptrB] h r h') :
    RepKLevel h' (levelMaxGo a b) r ∧ Heap.Extends h h' := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_max_go»)
    (by simp [IxVM.Checked.Fn.«KernelLevels::level_max_go», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«KernelLevels::level_max_go»] at ev
  obtain ⟨_, _, bs1, body1, dCall1, sel1, dArm1⟩ := ev.matchValue_inv
  obtain ⟨_, _, _, _, dVarA, dVarB, dFn1⟩ := evalExpr_call2_inv dCall1
  obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
  obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
  simp only [instanceName] at dFn1
  obtain ⟨rfl, rfl⟩ := levelStructEq_refines repA repB dFn1
  rcases selectArm_bool_one_zero sel1 with ⟨heq, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
  · obtain ⟨⟨⟩, rfl⟩ := dArm1.var_inv'
    have hab : a = b := eq_of_beq heq
    simp only [levelMaxGo, hab, ↓reduceIte]
    exact ⟨hab ▸ repA, Heap.Extends.refl _⟩
  · have hab : a ≠ b := fun h => by rw [beq_iff_eq.mpr h] at hne; cases hne
    have repA' := repA
    cases repA with
    | zero cellA =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellA dArm1
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨⟨⟩, rfl⟩ := dArm2.var_inv'
      simp only [levelMaxGo, hab, ↓reduceIte]
      exact ⟨repB, Heap.Extends.refl _⟩
    | succ cellA _ | max cellA _ _ | imax cellA _ _ | param _ cellA =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellA dArm1
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      have repB' := repB
      cases repB with
      | zero cellB =>
        obtain ⟨bs3, body3, sel3, dArm3⟩ := evalExpr_match_load_var_enum rfl cellB dArm2
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel3
        obtain ⟨rfl, rfl⟩ := sel3
        obtain ⟨⟨⟩, rfl⟩ := dArm3.var_inv'
        simp only [levelMaxGo, hab, ↓reduceIte]
        exact ⟨repA', Heap.Extends.refl _⟩
      | succ cellB _ | max cellB _ _ | imax cellB _ _ | param _ cellB =>
        obtain ⟨bs3, body3, sel3, dArm3⟩ := evalExpr_match_load_var_enum rfl cellB dArm2
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel3
        obtain ⟨rfl, rfl⟩ := sel3
        obtain ⟨_, _, bs4, body4, dCall4, sel4, dArm4⟩ := dArm3.matchValue_inv
        obtain ⟨_, _, _, _, dVarB4, dVarA4, dFn4⟩ := evalExpr_call2_inv dCall4
        obtain ⟨⟨⟩, rfl⟩ := dVarB4.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarA4.var_inv'
        simp only [instanceName] at dFn4
        obtain ⟨rfl, rfl⟩ := levelMaxSubsumes_refines repB' repA' dFn4
        rcases selectArm_bool_one_zero sel4 with ⟨hsub1, rfl, rfl⟩ | ⟨hnsub1, rfl, rfl⟩
        · obtain ⟨⟨⟩, rfl⟩ := dArm4.var_inv'
          simp only [levelMaxGo, hab, hsub1, ↓reduceIte]
          exact ⟨repB', Heap.Extends.refl _⟩
        · obtain ⟨_, _, bs5, body5, dCall5, sel5, dArm5⟩ := dArm4.matchValue_inv
          obtain ⟨_, _, _, _, dVarA5, dVarB5, dFn5⟩ := evalExpr_call2_inv dCall5
          obtain ⟨⟨⟩, rfl⟩ := dVarA5.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarB5.var_inv'
          simp only [instanceName] at dFn5
          obtain ⟨rfl, rfl⟩ := levelMaxSubsumes_refines repA' repB' dFn5
          rcases selectArm_bool_one_zero sel5 with ⟨hsub2, rfl, rfl⟩ | ⟨hnsub2, rfl, rfl⟩
          · obtain ⟨⟨⟩, rfl⟩ := dArm5.var_inv'
            simp only [levelMaxGo, hab, hnsub1, Bool.false_eq_true, hsub2, ↓reduceIte]
            exact ⟨repA', Heap.Extends.refl _⟩
          · obtain ⟨_, _, _, _, dVarA6, dVarB6, dFn6⟩ := evalExpr_call2_inv dArm5
            obtain ⟨⟨⟩, rfl⟩ := dVarA6.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarB6.var_inv'
            simp only [instanceName] at dFn6
            simp only [levelMaxGo, hab, hnsub1, hnsub2, Bool.false_eq_true, ↓reduceIte]
            exact levelMaxOffsets_refines repA' repB' ha hb dFn6

/-- **`EvalFn W` refinement for `KernelLevels::level_max`.** -/
theorem levelMax_refines {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB r : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (ha : levelDepth a < 4294967296) (hb : levelDepth b < 4294967296)
    (ev : EvalFn W "KernelLevels::level_max" [ptrA, ptrB] h r h') :
    RepKLevel h' (levelMax a b) r ∧ Heap.Extends h h' := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_max»)
    (by simp [IxVM.Checked.Fn.«KernelLevels::level_max», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«KernelLevels::level_max»] at ev
  obtain ⟨_, _, bs1, body1, dCall1, sel1, dArm1⟩ := ev.matchValue_inv
  obtain ⟨_, _, dVarA, dFn1⟩ := evalExpr_call1_inv dCall1
  obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
  simp only [instanceName] at dFn1
  obtain ⟨rfl, rfl⟩ := levelExplicitVal_refines repA dFn1
  rcases selectArm_explicitVal_tuple _ sel1 with ⟨na, hna, rfl, rfl⟩ | ⟨hna, rfl, rfl⟩
  · obtain ⟨_, _, bs2, body2, dCall2, sel2, dArm2⟩ := dArm1.matchValue_inv
    obtain ⟨_, _, dVarB, dFn2⟩ := evalExpr_call1_inv dCall2
    obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
    simp only [instanceName] at dFn2
    obtain ⟨rfl, rfl⟩ := levelExplicitVal_refines repB dFn2
    rcases selectArm_explicitVal_tuple _ sel2 with ⟨nb, hnb, rfl, rfl⟩ | ⟨hnb, rfl, rfl⟩
    · obtain ⟨_, _, bs3, body3, dCall3, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, dVarNA, dVarNB, dFn3⟩ := evalExpr_call2_inv dCall3
      obtain ⟨⟨⟩, rfl⟩ := dVarNA.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarNB.var_inv'
      simp only [instanceName] at dFn3
      have hna_lt : na < 4294967296 := (levelExplicitVal_le_depth hna).symm ▸ ha
      have hnb_lt : nb < 4294967296 := (levelExplicitVal_le_depth hnb).symm ▸ hb
      obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hna_lt hnb_lt dFn3
      rcases selectArm_ite_one_zero sel3 with ⟨hlt, rfl, rfl⟩ | ⟨hnlt, rfl, rfl⟩
      · obtain ⟨⟨⟩, rfl⟩ := dArm3.var_inv'
        simp only [levelMax, hna, hnb, hlt, ↓reduceIte]
        exact ⟨repB, Heap.Extends.refl _⟩
      · obtain ⟨⟨⟩, rfl⟩ := dArm3.var_inv'
        simp only [levelMax, hna, hnb, hnlt, ↓reduceIte]
        exact ⟨repA, Heap.Extends.refl _⟩
    · obtain ⟨_, _, _, _, dVarA3, dVarB3, dFn3⟩ := evalExpr_call2_inv dArm2
      obtain ⟨⟨⟩, rfl⟩ := dVarA3.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarB3.var_inv'
      simp only [instanceName] at dFn3
      simp only [levelMax, hna, hnb]
      exact levelMaxGo_refines repA repB ha hb dFn3
  · obtain ⟨_, _, _, _, dVarA2, dVarB2, dFn2⟩ := evalExpr_call2_inv dArm1
    obtain ⟨⟨⟩, rfl⟩ := dVarA2.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarB2.var_inv'
    simp only [instanceName] at dFn2
    simp only [levelMax, hna]
    exact levelMaxGo_refines repA repB ha hb dFn2

/-- **`EvalFn W` refinement for `KernelLevels::level_imax`.** -/
theorem levelIMax_refines {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB r : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (ha : levelDepth a < 4294967296) (hb : levelDepth b < 4294967296)
    (ev : EvalFn W "KernelLevels::level_imax" [ptrA, ptrB] h r h') :
    RepKLevel h' (levelIMax a b) r ∧ Heap.Extends h h' := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_imax»)
    (by simp [IxVM.Checked.Fn.«KernelLevels::level_imax», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«KernelLevels::level_imax»] at ev
  have repB' := repB
  cases repB with
  | zero cellB =>
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellB ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dArm
    simp only [levelIMax, klevel_inst]
    exact RepKLevel.allocZero h
  | succ cellB repBInner =>
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellB ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, _, _, dVarA, dVarB, dFn⟩ := evalExpr_call2_inv dArm
    obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
    simp only [instanceName, levelIMax] at dFn ⊢
    exact levelMax_refines repA (.succ cellB repBInner) ha hb dFn
  | max cellB _ _ | imax cellB _ _ | param _ cellB =>
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellB ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, bs2, dCallNZ, hpatNZ, dLetNZ⟩ := dArm.letValue_inv
    obtain ⟨_, _, dVarBNZ, dFnNZ⟩ := evalExpr_call1_inv dCallNZ
    obtain ⟨⟨⟩, rfl⟩ := dVarBNZ.var_inv'
    simp only [instanceName] at dFnNZ
    obtain ⟨rfl, rfl⟩ := levelIsNotZero_refines repB' dFnNZ
    simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatNZ
    subst hpatNZ
    obtain ⟨_, _, bs3, body3, dVarNZ, sel3, dArm3⟩ := dLetNZ.matchValue_inv
    obtain ⟨⟨⟩, rfl⟩ := dVarNZ.var_inv'
    rcases selectArm_bool_one_zero sel3 with ⟨hnz, rfl, rfl⟩ | ⟨hnnz, rfl, rfl⟩
    · obtain ⟨_, _, _, _, dVarAM, dVarBM, dFnM⟩ := evalExpr_call2_inv dArm3
      obtain ⟨⟨⟩, rfl⟩ := dVarAM.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarBM.var_inv'
      simp only [instanceName] at dFnM
      simp only [levelIMax, hnz, ↓reduceIte]
      exact levelMax_refines repA repB' ha hb dFnM
    · have repA' := repA
      cases repA with
      | zero cellA =>
        obtain ⟨bs4, body4, sel4, dArm4⟩ := evalExpr_match_load_var_enum rfl cellA dArm3
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel4
        obtain ⟨rfl, rfl⟩ := sel4
        obtain ⟨⟨⟩, rfl⟩ := dArm4.var_inv'
        simp only [levelIMax, hnnz, Bool.false_eq_true, ↓reduceIte]
        exact ⟨repB', Heap.Extends.refl _⟩
      | succ cellA _ | max cellA _ _ | imax cellA _ _ | param _ cellA =>
        obtain ⟨bs4, body4, sel4, dArm4⟩ := evalExpr_match_load_var_enum rfl cellA dArm3
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel4
        obtain ⟨rfl, rfl⟩ := sel4
        obtain ⟨_, _, bs5, dCallEq, hpatEq, dLetEq⟩ := dArm4.letValue_inv
        obtain ⟨_, _, _, _, dVarAEq, dVarBEq, dFnEq⟩ := evalExpr_call2_inv dCallEq
        obtain ⟨⟨⟩, rfl⟩ := dVarAEq.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarBEq.var_inv'
        simp only [instanceName] at dFnEq
        obtain ⟨rfl, rfl⟩ := levelEq_refines repA' repB' dFnEq
        simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatEq
        subst hpatEq
        obtain ⟨_, _, bs6, body6, dVarEq, sel6, dArm6⟩ := dLetEq.matchValue_inv
        obtain ⟨⟨⟩, rfl⟩ := dVarEq.var_inv'
        rcases selectArm_bool_one_zero sel6 with ⟨heq, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
        · obtain ⟨⟨⟩, rfl⟩ := dArm6.var_inv'
          have hab : _ = _ := eq_of_beq heq
          simp only [levelIMax, hnnz, Bool.false_eq_true, hab, ↓reduceIte]
          exact ⟨hab ▸ repA', Heap.Extends.refl _⟩
        · have hab : _ ≠ _ := fun h => by rw [beq_iff_eq.mpr h] at hne; cases hne
          obtain ⟨_, _, _, _, dVarAC, dVarBC, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm6
          obtain ⟨⟨⟩, rfl⟩ := dVarAC.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarBC.var_inv'
          simp only [levelIMax, hnnz, Bool.false_eq_true, hab, ↓reduceIte, klevel_inst]
          exact RepKLevel.allocIMax repA' repB'


/-! ### Subsection 3: Parameter Instantiation & Reduction (`Lists::drop`, `Lists::lookup`, `level_inst_params`, `level_list_inst`, `level_reduce`) -/

/-- **`EvalFn W` refinement for `Lists::drop<&KLevelNode>`.** -/
theorem listsDrop_refines {h h' : Heap F} {ls : List Ix.Kernel.Level}
    {ptr r : SourceValue F} {n : Nat}
    (hn : n ≤ 4294967296)
    (rep : RepKLevelList h ls ptr)
    (ev : EvalFn W (Instance.mk "Lists::drop" [klevelTy]).symbol [ptr, .field (n : F)] h r h') :
    RepKLevelList h (ls.drop n) r ∧ h' = h := by
  induction n generalizing ls ptr r h' with
  | zero =>
    have ev := ev.function_inv (Mirrors.«Lists::drop».lookup klevelTy)
      (by simp [IxVM.Checked.Fn.«Lists::drop», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«Lists::drop»] at ev
    obtain ⟨_, _, bs, body, dVarN, sel, dArm⟩ := ev.matchValue_inv
    obtain ⟨⟨⟩, rfl⟩ := dVarN.var_inv'
    rcases selectArm_nat_zero_wildcard hn sel with ⟨_, rfl, rfl⟩ | ⟨hne, _, _⟩
    · obtain ⟨⟨⟩, rfl⟩ := dArm.var_inv'
      exact ⟨rep, rfl⟩
    · exact absurd rfl hne
  | succ n ih =>
    have ev := ev.function_inv (Mirrors.«Lists::drop».lookup klevelTy)
      (by simp [IxVM.Checked.Fn.«Lists::drop», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«Lists::drop»] at ev
    obtain ⟨_, _, bs, body, dVarN, sel, dArm⟩ := ev.matchValue_inv
    obtain ⟨⟨⟩, rfl⟩ := dVarN.var_inv'
    rcases selectArm_nat_zero_wildcard hn sel with ⟨heq0, _, _⟩ | ⟨_, rfl, rfl⟩
    · omega
    · obtain ⟨_, _, bs2, dLoad, hpat, dBody⟩ := dArm.letValue_inv
      obtain ⟨_, dCall, hload⟩ := dLoad.load_inv
      obtain ⟨_, _, _, _, dVarL, dSub, dFn⟩ := evalExpr_call2_inv dCall
      obtain ⟨⟨⟩, rfl⟩ := dVarL.var_inv'
      obtain ⟨_, _, _, dVarN2, dLit1, rfl⟩ := evalExpr_sub_inv dSub
      obtain ⟨⟨⟩, rfl⟩ := dVarN2.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dLit1.literal_inv
      rw [instanceName_some_one, subst_param_singleton] at dFn
      have hcast : (((n + 1 : Nat) : F) - 1) = (n : F) := by push_cast; ring
      rw [hcast] at dFn
      obtain ⟨repDrop, rfl⟩ := ih (by omega) rep dFn
      cases hdrop : ls.drop n with
      | nil =>
        rw [hdrop] at repDrop
        cases repDrop with
        | nil cell =>
          simp [loadValue, cell, Value.type] at hload
          subst hload
          simp (config := { decide := true }) [matchPattern_construct] at hpat
      | cons hd tl =>
        rw [hdrop] at repDrop
        cases repDrop with
        | cons cell repHd repTl =>
          simp [loadValue, cell, Value.type] at hload
          subst hload
          simp (config := { decide := true }) [matchPattern_construct, matchPattern_wildcard,
            matchPattern_bind, SourceSemantics.matchListWith,
            bind, Except.bind, pure, Except.pure] at hpat
          subst hpat
          obtain ⟨⟨⟩, rfl⟩ := dBody.var_inv'
          have hdrop_succ : ls.drop (n + 1) = tl := by
            rw [← List.drop_drop, hdrop]
            rfl
          rw [hdrop_succ]
          exact ⟨repTl, rfl⟩

/-- **`EvalFn W` refinement for `Lists::lookup<&KLevelNode>`.** -/
theorem listsLookup_refines {h h' : Heap F} {ls : List Ix.Kernel.Level}
    {ptr r : SourceValue F} {idx : Nat}
    (hidx : idx < 4294967296)
    (rep : RepKLevelList h ls ptr)
    (ev : EvalFn W (Instance.mk "Lists::lookup" [klevelTy]).symbol [ptr, .field (idx : F)] h r h') :
    ∃ l, ls[idx]? = some l ∧ RepKLevel h l r ∧ h' = h := by
  have ev := ev.function_inv (Mirrors.«Lists::lookup».lookup klevelTy)
    (by simp [IxVM.Checked.Fn.«Lists::lookup», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«Lists::lookup»] at ev
  obtain ⟨_, _, bs, dLoad, hpat, dBody⟩ := ev.letValue_inv
  obtain ⟨_, dCall, hload⟩ := dLoad.load_inv
  obtain ⟨_, _, _, _, dVarL, dVarI, dFn⟩ := evalExpr_call2_inv dCall
  obtain ⟨⟨⟩, rfl⟩ := dVarL.var_inv'
  obtain ⟨⟨⟩, rfl⟩ := dVarI.var_inv'
  rw [instanceName_some_one, subst_param_singleton] at dFn
  obtain ⟨repDrop, rfl⟩ := listsDrop_refines (Nat.le_of_lt hidx) rep dFn
  cases hdrop : ls.drop idx with
  | nil =>
    rw [hdrop] at repDrop
    cases repDrop with
    | nil cell =>
      simp [loadValue, cell, Value.type] at hload
      subst hload
      simp (config := { decide := true }) [matchPattern_construct] at hpat
  | cons hd tl =>
    rw [hdrop] at repDrop
    cases repDrop with
    | cons cell repHd repTl =>
      simp [loadValue, cell, Value.type] at hload
      subst hload
      simp (config := { decide := true }) [matchPattern_construct, matchPattern_bind,
        matchPattern_wildcard, SourceSemantics.matchListWith,
        bind, Except.bind, pure, Except.pure] at hpat
      subst hpat
      obtain ⟨⟨⟩, rfl⟩ := dBody.var_inv'
      have hget : ls[idx]? = some hd := by
        rw [← List.head?_drop, hdrop]
        rfl
      exact ⟨hd, hget, repHd, rfl⟩

/-- **`EvalFn W` refinement for `KernelLevels::level_inst_params` (`subst_level`).** -/
theorem levelInstParams_refines {h h' : Heap F} {l : Ix.Kernel.Level}
    {params : List Ix.Kernel.Level} {ptrL ptrParams r : SourceValue F}
    (repL : RepKLevel h l ptrL) (repParams : RepKLevelList h params ptrParams)
    (hd : levelDepth l + maxLevelDepth params < 4294967296)
    (ev : EvalFn W "KernelLevels::level_inst_params" [ptrL, ptrParams] h r h') :
    ParamsLt params.length l ∧ RepKLevel h' (substLevel l params) r ∧ Heap.Extends h h' := by
  induction l generalizing h h' ptrL ptrParams r with
  | zero =>
    cases repL with
    | zero cell =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_inst_params»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_inst_params», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_inst_params»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dArm
      simp only [ParamsLt, substLevel, klevel_inst, true_and]
      exact RepKLevel.allocZero h
  | succ u ih =>
    cases repL with
    | succ cell repU =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_inst_params»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_inst_params», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_inst_params»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, h1, dCall, rfl, rfl⟩ := evalExpr_store_construct1_inv dArm
      obtain ⟨_, _, _, _, dVarU, dVarP, dFn⟩ := evalExpr_call2_inv dCall
      obtain ⟨⟨⟩, rfl⟩ := dVarU.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarP.var_inv'
      simp only [instanceName] at dFn
      have hdU : levelDepth u + maxLevelDepth params < 4294967296 := by
        simp only [levelDepth] at hd; omega
      obtain ⟨hplt, repU', ext1⟩ := ih repU repParams hdU dFn
      obtain ⟨repSucc, ext2⟩ := RepKLevel.allocSucc repU'
      simp only [ParamsLt, substLevel, klevel_inst]
      exact ⟨hplt, repSucc, ext1.trans ext2⟩
  | max a b iha ihb =>
    cases repL with
    | max cell repA repB =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_inst_params»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_inst_params», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_inst_params»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, _, h1, h2, dCallA, dCallB, dFnMax⟩ := evalExpr_call2_inv dArm
      obtain ⟨_, _, _, _, dVarA, dVarP1, dFnA⟩ := evalExpr_call2_inv dCallA
      obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarP1.var_inv'
      simp only [instanceName] at dFnA
      have hdA : levelDepth a + maxLevelDepth params < 4294967296 := by
        simp only [levelDepth] at hd; omega
      have hdB : levelDepth b + maxLevelDepth params < 4294967296 := by
        simp only [levelDepth] at hd; omega
      obtain ⟨hpltA, repA', ext1⟩ := iha repA repParams hdA dFnA
      obtain ⟨_, _, _, _, dVarB, dVarP2, dFnB⟩ := evalExpr_call2_inv dCallB
      obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarP2.var_inv'
      simp only [instanceName] at dFnB
      obtain ⟨hpltB, repB', ext2⟩ := ihb (repB.mono' ext1) (repParams.mono' ext1) hdB dFnB
      simp only [instanceName] at dFnMax
      have hdA' : levelDepth (substLevel a params) < 4294967296 :=
        Nat.lt_of_le_of_lt (levelDepth_substLevel_le a params) hdA
      have hdB' : levelDepth (substLevel b params) < 4294967296 :=
        Nat.lt_of_le_of_lt (levelDepth_substLevel_le b params) hdB
      obtain ⟨repMax, ext3⟩ := levelMax_refines (repA'.mono' ext2) repB' hdA' hdB' dFnMax
      exact ⟨⟨hpltA, hpltB⟩, repMax, (ext1.trans ext2).trans ext3⟩
  | imax a b iha ihb =>
    cases repL with
    | imax cell repA repB =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_inst_params»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_inst_params», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_inst_params»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, _, h1, h2, dCallA, dCallB, dFnIMax⟩ := evalExpr_call2_inv dArm
      obtain ⟨_, _, _, _, dVarA, dVarP1, dFnA⟩ := evalExpr_call2_inv dCallA
      obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarP1.var_inv'
      simp only [instanceName] at dFnA
      have hdA : levelDepth a + maxLevelDepth params < 4294967296 := by
        simp only [levelDepth] at hd; omega
      have hdB : levelDepth b + maxLevelDepth params < 4294967296 := by
        simp only [levelDepth] at hd; omega
      obtain ⟨hpltA, repA', ext1⟩ := iha repA repParams hdA dFnA
      obtain ⟨_, _, _, _, dVarB, dVarP2, dFnB⟩ := evalExpr_call2_inv dCallB
      obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarP2.var_inv'
      simp only [instanceName] at dFnB
      obtain ⟨hpltB, repB', ext2⟩ := ihb (repB.mono' ext1) (repParams.mono' ext1) hdB dFnB
      simp only [instanceName] at dFnIMax
      have hdA' : levelDepth (substLevel a params) < 4294967296 :=
        Nat.lt_of_le_of_lt (levelDepth_substLevel_le a params) hdA
      have hdB' : levelDepth (substLevel b params) < 4294967296 :=
        Nat.lt_of_le_of_lt (levelDepth_substLevel_le b params) hdB
      obtain ⟨repIMax, ext3⟩ := levelIMax_refines (repA'.mono' ext2) repB' hdA' hdB' dFnIMax
      exact ⟨⟨hpltA, hpltB⟩, repIMax, (ext1.trans ext2).trans ext3⟩
  | param i =>
    cases repL with
    | param hi cell =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_inst_params»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_inst_params», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_inst_params»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, _, _, _, dVarP, dVarI, dFn⟩ := evalExpr_call2_inv dArm
      obtain ⟨⟨⟩, rfl⟩ := dVarP.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarI.var_inv'
      have hinst : instanceName [] "Lists::lookup" (some [klevelTy]) =
          (Instance.mk "Lists::lookup" [klevelTy]).symbol := by decide +kernel
      rw [hinst] at dFn
      obtain ⟨l', hget, repL', rfl⟩ := listsLookup_refines hi repParams dFn
      have hlt : i < params.length := (List.getElem?_eq_some_iff.mp hget).1
      simp only [ParamsLt, substLevel, hget, Option.getD_some]
      exact ⟨hlt, repL', Heap.Extends.refl _⟩

/-- **`EvalFn W` refinement for `KernelLevels::level_list_inst`.** -/
theorem levelListInst_refines {h h' : Heap F} {lvls params : List Ix.Kernel.Level}
    {ptrLvls ptrParams r : SourceValue F}
    (repLvls : RepKLevelList h lvls ptrLvls) (repParams : RepKLevelList h params ptrParams)
    (hd : ∀ l ∈ lvls, levelDepth l + maxLevelDepth params < 4294967296)
    (ev : EvalFn W "KernelLevels::level_list_inst" [ptrLvls, ptrParams] h r h') :
    (∀ l ∈ lvls, ParamsLt params.length l) ∧
    RepKLevelList h' (substLevelList lvls params) r ∧
    Heap.Extends h h' := by
  induction lvls generalizing h h' ptrLvls ptrParams r with
  | nil =>
    cases repLvls with
    | nil cell =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_list_inst»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_list_inst», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_list_inst»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dArm
      simp only [substLevelList, List.map_nil, klevelList_inst]
      exact And.intro (by intro l hl; cases hl) (RepKLevelList.allocNil _)
  | cons hdLvl tlLvls ih =>
    cases repLvls with
    | cons cell repHd repTl =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_list_inst»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_list_inst», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_list_inst»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, _, h1, h2, dCallHd, dCallTl, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm
      obtain ⟨_, _, _, _, dVarL, dVarP1, dFnHd⟩ := evalExpr_call2_inv dCallHd
      obtain ⟨⟨⟩, rfl⟩ := dVarL.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarP1.var_inv'
      simp only [instanceName] at dFnHd
      obtain ⟨hpltHd, repHd', ext1⟩ :=
        levelInstParams_refines repHd repParams (hd _ (List.mem_cons_self ..)) dFnHd
      obtain ⟨_, _, _, _, dVarRest, dVarP2, dFnTl⟩ := evalExpr_call2_inv dCallTl
      obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarP2.var_inv'
      simp only [instanceName] at dFnTl
      obtain ⟨hpltTl, repTl', ext2⟩ :=
        ih (repTl.mono' ext1) (repParams.mono' ext1)
          (fun l hl => hd l (List.mem_cons_of_mem _ hl)) dFnTl
      obtain ⟨repCons, ext3⟩ := RepKLevelList.allocCons (repHd'.mono' ext2) repTl'
      simp only [substLevelList, List.map_cons, klevelList_inst]
      refine ⟨?_, repCons, (ext1.trans ext2).trans ext3⟩
      intro l hl
      rcases List.mem_cons.mp hl with rfl | htl
      · exact hpltHd
      · exact hpltTl l htl

/-- **`EvalFn W` refinement for `KernelLevels::level_reduce`.** -/
theorem levelReduce_refines {h h' : Heap F} {l : Ix.Kernel.Level}
    {ptr r : SourceValue F}
    (rep : RepKLevel h l ptr)
    (hd : levelDepth l < 4294967296)
    (ev : EvalFn W "KernelLevels::level_reduce" [ptr] h r h') :
    RepKLevel h' (levelReduce l) r ∧ Heap.Extends h h' := by
  induction l generalizing h h' ptr r with
  | zero =>
    cases rep with
    | zero cell =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_reduce»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_reduce», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_reduce»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dArm
      simp only [levelReduce, klevel_inst]
      exact RepKLevel.allocZero _
  | param i =>
    cases rep with
    | param hi cell =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_reduce»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_reduce», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_reduce»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, _, dVarI, rfl, rfl⟩ := evalExpr_store_construct1_inv dArm
      obtain ⟨⟨⟩, rfl⟩ := dVarI.var_inv'
      simp only [levelReduce, klevel_inst]
      exact RepKLevel.allocParam _ hi
  | succ u ih =>
    cases rep with
    | succ cell repU =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_reduce»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_reduce», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_reduce»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, h1, dCall, rfl, rfl⟩ := evalExpr_store_construct1_inv dArm
      obtain ⟨_, _, dVarU, dFn⟩ := evalExpr_call1_inv dCall
      obtain ⟨⟨⟩, rfl⟩ := dVarU.var_inv'
      simp only [instanceName] at dFn
      have hdU : levelDepth u < 4294967296 := by simp only [levelDepth] at hd; omega
      obtain ⟨repU', ext1⟩ := ih repU hdU dFn
      obtain ⟨repSucc, ext2⟩ := RepKLevel.allocSucc repU'
      simp only [levelReduce, klevel_inst]
      exact ⟨repSucc, ext1.trans ext2⟩
  | max a b iha ihb =>
    cases rep with
    | max cell repA repB =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_reduce»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_reduce», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_reduce»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, _, h1, h2, dCallA, dCallB, dFnMax⟩ := evalExpr_call2_inv dArm
      obtain ⟨_, _, dVarA, dFnA⟩ := evalExpr_call1_inv dCallA
      obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
      simp only [instanceName] at dFnA
      have hdA : levelDepth a < 4294967296 := by simp only [levelDepth] at hd; omega
      have hdB : levelDepth b < 4294967296 := by simp only [levelDepth] at hd; omega
      obtain ⟨repA', ext1⟩ := iha repA hdA dFnA
      obtain ⟨_, _, dVarB, dFnB⟩ := evalExpr_call1_inv dCallB
      obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
      simp only [instanceName] at dFnB
      obtain ⟨repB', ext2⟩ := ihb (repB.mono' ext1) hdB dFnB
      simp only [instanceName] at dFnMax
      have hdA' : levelDepth (levelReduce a) < 4294967296 :=
        Nat.lt_of_le_of_lt (levelDepth_levelReduce_le a) hdA
      have hdB' : levelDepth (levelReduce b) < 4294967296 :=
        Nat.lt_of_le_of_lt (levelDepth_levelReduce_le b) hdB
      obtain ⟨repMax, ext3⟩ := levelMax_refines (repA'.mono' ext2) repB' hdA' hdB' dFnMax
      exact ⟨repMax, (ext1.trans ext2).trans ext3⟩
  | imax a b iha ihb =>
    cases rep with
    | imax cell repA repB =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_reduce»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::level_reduce», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::level_reduce»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cell ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, _, h1, h2, dCallA, dCallB, dFnIMax⟩ := evalExpr_call2_inv dArm
      obtain ⟨_, _, dVarA, dFnA⟩ := evalExpr_call1_inv dCallA
      obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
      simp only [instanceName] at dFnA
      have hdA : levelDepth a < 4294967296 := by simp only [levelDepth] at hd; omega
      have hdB : levelDepth b < 4294967296 := by simp only [levelDepth] at hd; omega
      obtain ⟨repA', ext1⟩ := iha repA hdA dFnA
      obtain ⟨_, _, dVarB, dFnB⟩ := evalExpr_call1_inv dCallB
      obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
      simp only [instanceName] at dFnB
      obtain ⟨repB', ext2⟩ := ihb (repB.mono' ext1) hdB dFnB
      simp only [instanceName] at dFnIMax
      have hdA' : levelDepth (levelReduce a) < 4294967296 :=
        Nat.lt_of_le_of_lt (levelDepth_levelReduce_le a) hdA
      have hdB' : levelDepth (levelReduce b) < 4294967296 :=
        Nat.lt_of_le_of_lt (levelDepth_levelReduce_le b) hdB
      obtain ⟨repIMax, ext3⟩ := levelIMax_refines (repA'.mono' ext2) repB' hdA' hdB' dFnIMax
      exact ⟨repIMax, (ext1.trans ext2).trans ext3⟩


/-! ### Subsection 4: Guard Lists & `NLVar` Lists (`glist_cmp`, `glist_subset`, `glist_eq_len`, `glist_ordered_insert`, `nlvars_add`, `nlvars_eq`, `nlvars_max_offset`, `nlvars_subsume`) -/

/-- **`EvalFn W` refinement for `KernelLevels::glist_cmp`.** -/
theorem glistCmp_refines {h h' : Heap F} {a b : List Nat}
    {ptrA ptrB r : SourceValue F}
    (repA : RepGuardList h a ptrA) (repB : RepGuardList h b ptrB)
    (ev : EvalFn W "KernelLevels::glist_cmp" [ptrA, ptrB] h r h') :
    r = .field (glistCmp a b : F) ∧ h' = h := by
  induction repA generalizing b ptrB r h' with
  | nil cellA =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_cmp»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::glist_cmp», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::glist_cmp»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | nil cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [glistCmp]
    | cons cellB _ _ =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [glistCmp]
  | cons cellA repX repAr ih =>
    rcases repX with ⟨hx, rfl⟩
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_cmp»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::glist_cmp», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::glist_cmp»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | nil cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [glistCmp]
    | cons cellB repY repBr =>
      rcases repY with ⟨hy, rfl⟩
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dCall1, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, dVarX, dVarY, dFn1⟩ := evalExpr_call2_inv dCall1
      obtain ⟨⟨⟩, rfl⟩ := dVarX.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarY.var_inv'
      simp only [instanceName] at dFn1
      obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hx hy dFn1
      rcases selectArm_ite_one_zero sel3 with ⟨hxy, rfl, rfl⟩ | ⟨hnxy, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := dArm3.literal_inv
        simp [glistCmp, hxy]
      · obtain ⟨_, _, bs4, body4, dCall2, sel4, dArm4⟩ := dArm3.matchValue_inv
        obtain ⟨_, _, _, _, dVarY2, dVarX2, dFn2⟩ := evalExpr_call2_inv dCall2
        obtain ⟨⟨⟩, rfl⟩ := dVarY2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarX2.var_inv'
        simp only [instanceName] at dFn2
        obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hy hx dFn2
        rcases selectArm_ite_one_zero sel4 with ⟨hyx, rfl, rfl⟩ | ⟨hnyx, rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := dArm4.literal_inv
          simp [glistCmp, hnxy, hyx]
        · obtain ⟨_, _, _, _, dVarAr, dVarBr, dFn3⟩ := evalExpr_call2_inv dArm4
          obtain ⟨⟨⟩, rfl⟩ := dVarAr.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarBr.var_inv'
          simp only [instanceName] at dFn3
          simpa [glistCmp, hnxy, hnyx] using ih repBr dFn3

/-- **`EvalFn W` refinement for `KernelLevels::glist_subset`.** -/
theorem glistSubset_refines {h h' : Heap F} {xs ys : List Nat}
    {ptrX ptrY r : SourceValue F}
    (repX : RepGuardList h xs ptrX) (repY : RepGuardList h ys ptrY)
    (ev : EvalFn W "KernelLevels::glist_subset" [ptrX, ptrY] h r h') :
    r = .field (if glistSubset xs ys then 1 else 0) ∧ h' = h := by
  induction xs, ys using glistSubset.induct generalizing ptrX ptrY r h' with
  | case1 ys =>
    cases repX with
    | nil cellX =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_subset»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::glist_subset», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::glist_subset»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨rfl, rfl⟩ := dArm.literal_inv
      simp [glistSubset]
  | case2 x xr =>
    cases repX with
    | cons cellX repHx repTx =>
      rcases repHx with ⟨hx, rfl⟩
      cases repY with
      | nil cellY =>
        have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_subset»)
          (by simp [IxVM.Checked.Fn.«KernelLevels::glist_subset», ControlLower.hasControl])
        simp only [IxVM.Checked.Fn.«KernelLevels::glist_subset»] at ev
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellY dArm
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
        obtain ⟨rfl, rfl⟩ := sel2
        obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
        simp [glistSubset]
  | case3 x xr y yr hxy =>
    cases repX with
    | cons cellX repHx repTx =>
      rcases repHx with ⟨hx, rfl⟩
      cases repY with
      | cons cellY repHy repTy =>
        rcases repHy with ⟨hy, rfl⟩
        have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_subset»)
          (by simp [IxVM.Checked.Fn.«KernelLevels::glist_subset», ControlLower.hasControl])
        simp only [IxVM.Checked.Fn.«KernelLevels::glist_subset»] at ev
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellY dArm
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
        obtain ⟨rfl, rfl⟩ := sel2
        obtain ⟨_, _, bs3, body3, dCall1, sel3, dArm3⟩ := dArm2.matchValue_inv
        obtain ⟨_, _, _, _, dVarX, dVarY, dFn1⟩ := evalExpr_call2_inv dCall1
        obtain ⟨⟨⟩, rfl⟩ := dVarX.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarY.var_inv'
        simp only [instanceName] at dFn1
        obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hx hy dFn1
        rcases selectArm_ite_one_zero sel3 with ⟨_, rfl, rfl⟩ | ⟨hnxy, _, _⟩
        · obtain ⟨rfl, rfl⟩ := dArm3.literal_inv
          simp [glistSubset, hxy]
        · exact absurd hxy hnxy
  | case4 x xr y yr hnxy hyx ih =>
    cases repX with
    | cons cellX repHx repTx =>
      rcases repHx with ⟨hx, rfl⟩
      cases repY with
      | cons cellY repHy repTy =>
        rcases repHy with ⟨hy, rfl⟩
        have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_subset»)
          (by simp [IxVM.Checked.Fn.«KernelLevels::glist_subset», ControlLower.hasControl])
        simp only [IxVM.Checked.Fn.«KernelLevels::glist_subset»] at ev
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellY dArm
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
        obtain ⟨rfl, rfl⟩ := sel2
        obtain ⟨_, _, bs3, body3, dCall1, sel3, dArm3⟩ := dArm2.matchValue_inv
        obtain ⟨_, _, _, _, dVarX, dVarY, dFn1⟩ := evalExpr_call2_inv dCall1
        obtain ⟨⟨⟩, rfl⟩ := dVarX.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarY.var_inv'
        simp only [instanceName] at dFn1
        obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hx hy dFn1
        rcases selectArm_ite_one_zero sel3 with ⟨hxy, _, _⟩ | ⟨_, rfl, rfl⟩
        · exact absurd hxy hnxy
        · obtain ⟨_, _, bs4, body4, dCall2, sel4, dArm4⟩ := dArm3.matchValue_inv
          obtain ⟨_, _, _, _, dVarY2, dVarX2, dFn2⟩ := evalExpr_call2_inv dCall2
          obtain ⟨⟨⟩, rfl⟩ := dVarY2.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarX2.var_inv'
          simp only [instanceName] at dFn2
          obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hy hx dFn2
          rcases selectArm_ite_one_zero sel4 with ⟨_, rfl, rfl⟩ | ⟨hnyx, _, _⟩
          · obtain ⟨_, _, _, _, dVarXs, dVarYr, dFn3⟩ := evalExpr_call2_inv dArm4
            obtain ⟨⟨⟩, rfl⟩ := dVarXs.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarYr.var_inv'
            simp only [instanceName] at dFn3
            simpa [glistSubset, hnxy, hyx] using ih (.cons cellX ⟨hx, rfl⟩ repTx) repTy dFn3
          · exact absurd hyx hnyx
  | case5 x xr y yr hnxy hnyx ih =>
    cases repX with
    | cons cellX repHx repTx =>
      rcases repHx with ⟨hx, rfl⟩
      cases repY with
      | cons cellY repHy repTy =>
        rcases repHy with ⟨hy, rfl⟩
        have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_subset»)
          (by simp [IxVM.Checked.Fn.«KernelLevels::glist_subset», ControlLower.hasControl])
        simp only [IxVM.Checked.Fn.«KernelLevels::glist_subset»] at ev
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellY dArm
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
        obtain ⟨rfl, rfl⟩ := sel2
        obtain ⟨_, _, bs3, body3, dCall1, sel3, dArm3⟩ := dArm2.matchValue_inv
        obtain ⟨_, _, _, _, dVarX, dVarY, dFn1⟩ := evalExpr_call2_inv dCall1
        obtain ⟨⟨⟩, rfl⟩ := dVarX.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarY.var_inv'
        simp only [instanceName] at dFn1
        obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hx hy dFn1
        rcases selectArm_ite_one_zero sel3 with ⟨hxy, _, _⟩ | ⟨_, rfl, rfl⟩
        · exact absurd hxy hnxy
        · obtain ⟨_, _, bs4, body4, dCall2, sel4, dArm4⟩ := dArm3.matchValue_inv
          obtain ⟨_, _, _, _, dVarY2, dVarX2, dFn2⟩ := evalExpr_call2_inv dCall2
          obtain ⟨⟨⟩, rfl⟩ := dVarY2.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarX2.var_inv'
          simp only [instanceName] at dFn2
          obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hy hx dFn2
          rcases selectArm_ite_one_zero sel4 with ⟨hyx, _, _⟩ | ⟨_, rfl, rfl⟩
          · exact absurd hyx hnyx
          · obtain ⟨_, _, _, _, dVarXr, dVarYr, dFn3⟩ := evalExpr_call2_inv dArm4
            obtain ⟨⟨⟩, rfl⟩ := dVarXr.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarYr.var_inv'
            simp only [instanceName] at dFn3
            simpa [glistSubset, hnxy, hnyx] using ih repTx repTy dFn3

/-- **`EvalFn W` refinement for `KernelLevels::glist_eq_len`.** -/
theorem glistEqLen_refines {h h' : Heap F} {a b : List Nat}
    {ptrA ptrB r : SourceValue F}
    (repA : RepGuardList h a ptrA) (repB : RepGuardList h b ptrB)
    (ev : EvalFn W "KernelLevels::glist_eq_len" [ptrA, ptrB] h r h') :
    r = .field (if glistEqLen a b then 1 else 0) ∧ h' = h := by
  induction repA generalizing b ptrB r h' with
  | nil cellA =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_eq_len»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::glist_eq_len», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::glist_eq_len»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | nil cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [glistEqLen]
    | cons cellB _ _ =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [glistEqLen]
  | cons cellA _ repAr ih =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_eq_len»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::glist_eq_len», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::glist_eq_len»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
      matchPattern_bind, SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | nil cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [glistEqLen]
    | cons cellB _ repBr =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        matchPattern_bind, SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, _, _, dVarAr, dVarBr, dFn⟩ := evalExpr_call2_inv dArm2
      obtain ⟨⟨⟩, rfl⟩ := dVarAr.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarBr.var_inv'
      simp only [instanceName] at dFn
      dsimp only [glistEqLen]
      exact ih repBr dFn

/-- **`EvalFn W` refinement for `KernelLevels::glist_ordered_insert`.** -/
theorem glistOrderedInsert_refines {h h' : Heap F} {x : Nat} {l : List Nat}
    {ptrL r : SourceValue F}
    (hx : x < 4294967296) (repL : RepGuardList h l ptrL)
    (ev : EvalFn W "KernelLevels::glist_ordered_insert" [.field (x : F), ptrL] h r h') :
    ∃ ptrOut,
      r = .tuple [.field (if (glistOrderedInsert x l).1 then 1 else 0), ptrOut] ∧
      RepGuardList h' (glistOrderedInsert x l).2 ptrOut ∧
      Heap.Extends h h' := by
  induction repL generalizing h' r with
  | nil cellL =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_ordered_insert»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::glist_ordered_insert», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::glist_ordered_insert»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, _, dLit1, dStoreCons, rfl⟩ := evalExpr_tuple2_inv dArm
    obtain ⟨⟨⟩, rfl⟩ := dLit1.literal_inv
    obtain ⟨_, _, _, _, dVarX, dStoreNil, rfl, rfl⟩ := evalExpr_store_construct2_inv dStoreCons
    obtain ⟨⟨⟩, rfl⟩ := dVarX.var_inv'
    obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNil
    simp only [glistOrderedInsert, guardList_inst]
    obtain ⟨repNil, ext1⟩ := RepGuardList.allocNil _
    obtain ⟨repCons, ext2⟩ := RepGuardList.allocCons hx repNil
    exact ⟨_, rfl, repCons, ext1.trans ext2⟩
  | cons cellL repHd repTl ih =>
    rcases repHd with ⟨hhd, rfl⟩
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::glist_ordered_insert»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::glist_ordered_insert», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::glist_ordered_insert»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, bs2, body2, dCall1, sel2, dArm2⟩ := dArm.matchValue_inv
    obtain ⟨_, _, _, _, dVarX, dVarH, dFn1⟩ := evalExpr_call2_inv dCall1
    obtain ⟨⟨⟩, rfl⟩ := dVarX.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarH.var_inv'
    simp only [instanceName] at dFn1
    obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hx hhd dFn1
    rcases selectArm_ite_one_zero sel2 with ⟨hxh, rfl, rfl⟩ | ⟨hnxh, rfl, rfl⟩
    · obtain ⟨_, _, _, dLit1, dStoreCons, rfl⟩ := evalExpr_tuple2_inv dArm2
      obtain ⟨⟨⟩, rfl⟩ := dLit1.literal_inv
      obtain ⟨_, _, _, _, dVarX2, dVarL, rfl, rfl⟩ := evalExpr_store_construct2_inv dStoreCons
      obtain ⟨⟨⟩, rfl⟩ := dVarX2.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarL.var_inv'
      simp only [glistOrderedInsert, hxh, ↓reduceIte, guardList_inst]
      obtain ⟨repCons, ext⟩ := RepGuardList.allocCons hx (.cons cellL ⟨hhd, rfl⟩ repTl)
      exact ⟨_, rfl, repCons, ext⟩
    · obtain ⟨_, _, bs3, body3, dCall2, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, dVarH2, dVarX2, dFn2⟩ := evalExpr_call2_inv dCall2
      obtain ⟨⟨⟩, rfl⟩ := dVarH2.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarX2.var_inv'
      simp only [instanceName] at dFn2
      obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hhd hx dFn2
      rcases selectArm_ite_zero_one sel3 with ⟨hnhx, rfl, rfl⟩ | ⟨hhx, rfl, rfl⟩
      · obtain ⟨_, _, _, dLit0, dVarL, rfl⟩ := evalExpr_tuple2_inv dArm3
        obtain ⟨⟨⟩, rfl⟩ := dLit0.literal_inv
        obtain ⟨⟨⟩, rfl⟩ := dVarL.var_inv'
        simp only [glistOrderedInsert, hnxh, hnhx, ↓reduceIte]
        exact ⟨_, rfl, .cons cellL ⟨hhd, rfl⟩ repTl, Heap.Extends.refl _⟩
      · obtain ⟨_, _, bs4, body4, dCall3, sel4, dArm4⟩ := dArm3.matchValue_inv
        obtain ⟨_, _, _, _, dVarX3, dVarR, dFn3⟩ := evalExpr_call2_inv dCall3
        obtain ⟨⟨⟩, rfl⟩ := dVarX3.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarR.var_inv'
        simp only [instanceName] at dFn3
        obtain ⟨ptrR2, rfl, repR2, ext1⟩ := ih dFn3
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_tuple, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel4
        obtain ⟨rfl, rfl⟩ := sel4
        obtain ⟨_, _, _, dVarF, dStoreCons, rfl⟩ := evalExpr_tuple2_inv dArm4
        obtain ⟨⟨⟩, rfl⟩ := dVarF.var_inv'
        obtain ⟨_, _, _, _, dVarH3, dVarR2, rfl, rfl⟩ := evalExpr_store_construct2_inv dStoreCons
        obtain ⟨⟨⟩, rfl⟩ := dVarH3.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarR2.var_inv'
        obtain ⟨repCons, ext2⟩ := RepGuardList.allocCons hhd repR2
        simp only [glistOrderedInsert, hnxh, hhx, ↓reduceIte, guardList_inst]
        exact ⟨_, rfl, repCons, ext1.trans ext2⟩

/-- **`EvalFn W` refinement for `KernelLevels::nlvars_add`.** -/
theorem nlvarsAdd_refines {h h' : Heap F} {vars : List NLVar} {idx k : Nat}
    {ptrVars r : SourceValue F}
    (repVars : RepNLVarList h vars ptrVars)
    (hidx : idx < 4294967296) (hk : k < 4294967296)
    (ev : EvalFn W "KernelLevels::nlvars_add" [ptrVars, .field (idx : F), .field (k : F)] h r h') :
    RepNLVarList h' (nlvarsAdd vars idx k) r ∧ Heap.Extends h h' := by
  induction repVars generalizing h' r with
  | nil cellVars =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_add»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_add», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_add»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, h1, h2, dStoreV, dStoreNil, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm
    obtain ⟨_, _, _, _, dVarIdx, dVarK, rfl, rfl⟩ := evalExpr_store_construct2_inv dStoreV
    obtain ⟨⟨⟩, rfl⟩ := dVarIdx.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
    obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNil
    simp only [nlvarsAdd, nlVar_inst, nlVarList_inst]
    obtain ⟨repV, ext1⟩ := RepNLVar.alloc hidx hk _
    obtain ⟨repNil, ext2⟩ := RepNLVarList.allocNil _
    obtain ⟨repCons, ext3⟩ := RepNLVarList.allocCons (repV.mono' ext2) repNil
    exact ⟨repCons, (ext1.trans ext2).trans ext3⟩
  | cons cellVars repV repRest ih =>
    cases repV with
    | mk hvi hvo cellV =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_add»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_add», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_add»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellV dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dCall1, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, dVarIdx, dVarVi, dFn1⟩ := evalExpr_call2_inv dCall1
      obtain ⟨⟨⟩, rfl⟩ := dVarIdx.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarVi.var_inv'
      simp only [instanceName] at dFn1
      obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hidx hvi dFn1
      rcases selectArm_ite_one_zero sel3 with ⟨hlt1, rfl, rfl⟩ | ⟨hnlt1, rfl, rfl⟩
      · obtain ⟨_, _, h1, h2, dStoreV, dVarVars, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm3
        obtain ⟨_, _, _, _, dVarIdx2, dVarK2, rfl, rfl⟩ := evalExpr_store_construct2_inv dStoreV
        obtain ⟨⟨⟩, rfl⟩ := dVarIdx2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarVars.var_inv'
        simp only [nlvarsAdd, hlt1, ↓reduceIte, nlVar_inst, nlVarList_inst]
        obtain ⟨repNewV, ext1⟩ := RepNLVar.alloc hidx hk _
        have repOrig : RepNLVarList _ (⟨_, _⟩ :: _) _ := .cons cellVars (.mk hvi hvo cellV) repRest
        obtain ⟨repCons, ext2⟩ := RepNLVarList.allocCons repNewV (repOrig.mono' ext1)
        exact ⟨repCons, ext1.trans ext2⟩
      · obtain ⟨_, _, bs4, body4, dCall2, sel4, dArm4⟩ := dArm3.matchValue_inv
        obtain ⟨_, _, _, _, dVarVi2, dVarIdx2, dFn2⟩ := evalExpr_call2_inv dCall2
        obtain ⟨⟨⟩, rfl⟩ := dVarVi2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarIdx2.var_inv'
        simp only [instanceName] at dFn2
        obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hvi hidx dFn2
        rcases selectArm_ite_one_zero sel4 with ⟨hlt2, rfl, rfl⟩ | ⟨hnlt2, rfl, rfl⟩
        · obtain ⟨_, _, h1, h2, dVarV, dCallRec, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm4
          obtain ⟨⟨⟩, rfl⟩ := dVarV.var_inv'
          obtain ⟨_, _, _, _, _, _, dVarRest, dVarIdx3, dVarK3, dFnRec⟩ := evalExpr_call3_inv dCallRec
          obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarIdx3.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarK3.var_inv'
          simp only [instanceName] at dFnRec
          obtain ⟨repRest', ext1⟩ := ih dFnRec
          have repV' := (RepNLVar.mk hvi hvo cellV).mono' ext1
          obtain ⟨repCons, ext2⟩ := RepNLVarList.allocCons repV' repRest'
          simp only [nlvarsAdd, hnlt1, hlt2, ↓reduceIte, nlVarList_inst]
          exact ⟨repCons, ext1.trans ext2⟩
        · obtain ⟨_, _, bs5, body5, dCall3, sel5, dArm5⟩ := dArm4.matchValue_inv
          obtain ⟨_, _, _, _, dVarVo, dVarK3, dFn3⟩ := evalExpr_call2_inv dCall3
          obtain ⟨⟨⟩, rfl⟩ := dVarVo.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarK3.var_inv'
          simp only [instanceName] at dFn3
          obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hvo hk dFn3
          rcases selectArm_ite_one_zero sel5 with ⟨hlt3, rfl, rfl⟩ | ⟨hnlt3, rfl, rfl⟩
          · obtain ⟨_, _, h1, h2, dStoreV, dVarRest, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm5
            obtain ⟨_, _, _, _, dVarVi3, dVarK4, rfl, rfl⟩ := evalExpr_store_construct2_inv dStoreV
            obtain ⟨⟨⟩, rfl⟩ := dVarVi3.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarK4.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
            simp only [nlvarsAdd, hnlt1, hnlt2, hlt3, ↓reduceIte, nlVar_inst, nlVarList_inst]
            obtain ⟨repNewV, ext1⟩ := RepNLVar.alloc hvi hk _
            obtain ⟨repCons, ext2⟩ := RepNLVarList.allocCons repNewV (repRest.mono' ext1)
            exact ⟨repCons, ext1.trans ext2⟩
          · obtain ⟨⟨⟩, rfl⟩ := dArm5.var_inv'
            simp only [nlvarsAdd, hnlt1, hnlt2, hnlt3, ↓reduceIte]
            exact ⟨.cons cellVars (.mk hvi hvo cellV) repRest, Heap.Extends.refl _⟩

/-- **`EvalFn W` refinement for `KernelLevels::nlvars_eq`.** -/
theorem nlvarsEq_refines {h h' : Heap F} {a b : List NLVar}
    {ptrA ptrB r : SourceValue F}
    (repA : RepNLVarList h a ptrA) (repB : RepNLVarList h b ptrB)
    (ev : EvalFn W "KernelLevels::nlvars_eq" [ptrA, ptrB] h r h') :
    r = .field (if nlvarsEq a b then 1 else 0) ∧ h' = h := by
  induction repA generalizing b ptrB r h' with
  | nil cellA =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_eq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    cases repB with
    | nil cellB =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [nlvarsEq]
    | cons cellB _ _ =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [nlvarsEq]
  | cons cellA repX repAr ih =>
    cases repX with
    | mk hxi hxo cellX =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_eq»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_eq», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_eq»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellA ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      cases repB with
      | nil cellB =>
        obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
        obtain ⟨rfl, rfl⟩ := sel2
        obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
        simp [nlvarsEq]
      | cons cellB repY repBr =>
        cases repY with
        | mk hyi hyo cellY =>
          obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellB dArm
          simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
            SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
          obtain ⟨rfl, rfl⟩ := sel2
          obtain ⟨bs3, body3, sel3, dArm3⟩ := evalExpr_match_load_var_enum rfl cellX dArm2
          simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
            SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel3
          obtain ⟨rfl, rfl⟩ := sel3
          obtain ⟨bs4, body4, sel4, dArm4⟩ := evalExpr_match_load_var_enum rfl cellY dArm3
          simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
            SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel4
          obtain ⟨rfl, rfl⟩ := sel4
          obtain ⟨_, _, bs5, body5, dSub1, sel5, dArm5⟩ := dArm4.matchValue_inv
          obtain ⟨_, _, _, dVarXi, dVarYi, rfl⟩ := evalExpr_sub_inv dSub1
          obtain ⟨⟨⟩, rfl⟩ := dVarXi.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarYi.var_inv'
          rcases selectArm_sub_zero_wildcard hxi hyi sel5 with ⟨heqI, rfl, rfl⟩ | ⟨hneI, rfl, rfl⟩
          · obtain ⟨_, _, bs6, body6, dSub2, sel6, dArm6⟩ := dArm5.matchValue_inv
            obtain ⟨_, _, _, dVarXo, dVarYo, rfl⟩ := evalExpr_sub_inv dSub2
            obtain ⟨⟨⟩, rfl⟩ := dVarXo.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarYo.var_inv'
            rcases selectArm_sub_zero_wildcard hxo hyo sel6 with ⟨heqO, rfl, rfl⟩ | ⟨hneO, rfl, rfl⟩
            · obtain ⟨_, _, _, _, dVarAr, dVarBr, dFn⟩ := evalExpr_call2_inv dArm6
              obtain ⟨⟨⟩, rfl⟩ := dVarAr.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarBr.var_inv'
              simp only [instanceName] at dFn
              simpa [nlvarsEq, heqI, heqO] using ih repBr dFn
            · obtain ⟨rfl, rfl⟩ := dArm6.literal_inv
              simp [nlvarsEq, heqI, hneO]
          · obtain ⟨rfl, rfl⟩ := dArm5.literal_inv
            simp [nlvarsEq, hneI]

theorem nlvarsMaxOffset_lt {h : Heap F} {vars : List NLVar} {ptr : SourceValue F}
    (rep : RepNLVarList h vars ptr) : nlvarsMaxOffset vars < 4294967296 := by
  induction rep with
  | nil _ => decide
  | cons _ repV _ ih =>
    cases repV with
    | mk _ hvo _ =>
      simp only [nlvarsMaxOffset]
      split_ifs <;> omega

/-- **`EvalFn W` refinement for `KernelLevels::nlvars_max_offset`.** -/
theorem nlvarsMaxOffset_refines {h h' : Heap F} {vars : List NLVar}
    {ptr r : SourceValue F}
    (rep : RepNLVarList h vars ptr)
    (ev : EvalFn W "KernelLevels::nlvars_max_offset" [ptr] h r h') :
    r = .field (nlvarsMaxOffset vars : F) ∧ h' = h := by
  induction rep generalizing r h' with
  | nil cellVars =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_max_offset»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_max_offset», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_max_offset»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [nlvarsMaxOffset]
  | cons cellVars repV repRest ih =>
    cases repV with
    | mk hvi hvo cellV =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_max_offset»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_max_offset», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_max_offset»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellV dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        matchPattern_bind, SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, dCallRec, hpatM, dBodyM⟩ := dArm2.letValue_inv
      obtain ⟨_, _, dVarRest, dFnRec⟩ := evalExpr_call1_inv dCallRec
      obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
      simp only [instanceName] at dFnRec
      obtain ⟨rfl, rfl⟩ := ih dFnRec
      simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatM
      subst hpatM
      obtain ⟨_, _, bs4, body4, dCallLt, sel4, dArm4⟩ := dBodyM.matchValue_inv
      obtain ⟨_, _, _, _, dVarM, dVarVo, dFnLt⟩ := evalExpr_call2_inv dCallLt
      obtain ⟨⟨⟩, rfl⟩ := dVarM.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarVo.var_inv'
      simp only [instanceName] at dFnLt
      obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines (nlvarsMaxOffset_lt repRest) hvo dFnLt
      rcases selectArm_ite_one_zero sel4 with ⟨hlt, rfl, rfl⟩ | ⟨hnlt, rfl, rfl⟩
      · obtain ⟨⟨⟩, rfl⟩ := dArm4.var_inv'
        simp [nlvarsMaxOffset, hlt]
      · obtain ⟨⟨⟩, rfl⟩ := dArm4.var_inv'
        simp [nlvarsMaxOffset, hnlt]

/-- **`EvalFn W` refinement for `KernelLevels::nlvars_subsume`.** -/
theorem nlvarsSubsume_refines {h h' : Heap F} {xs ys : List NLVar}
    {ptrX ptrY r : SourceValue F}
    (repX : RepNLVarList h xs ptrX) (repY : RepNLVarList h ys ptrY)
    (ev : EvalFn W "KernelLevels::nlvars_subsume" [ptrX, ptrY] h r h') :
    RepNLVarList h' (nlvarsSubsume xs ys) r ∧ Heap.Extends h h' := by
  induction xs, ys using nlvarsSubsume.induct generalizing h h' ptrX ptrY r with
  | case1 ys =>
    cases repX with
    | nil cellX =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_subsume»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨⟨⟩, rfl⟩ := dArm.var_inv'
      simp only [nlvarsSubsume]
      exact ⟨.nil cellX, Heap.Extends.refl _⟩
  | case2 x xr =>
    cases repX with
    | cons cellX repHx repTx =>
      cases repY with
      | nil cellY =>
        have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_subsume»)
          (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume», ControlLower.hasControl])
        simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume»] at ev
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellY dArm
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
        obtain ⟨rfl, rfl⟩ := sel2
        obtain ⟨⟨⟩, rfl⟩ := dArm2.var_inv'
        simp only [nlvarsSubsume]
        exact ⟨.cons cellX repHx repTx, Heap.Extends.refl _⟩
  | case3 xi xo xr yi yo yr hlt1 ih =>
    cases repX with
    | cons cellX repHx repTx =>
      cases repHx with
      | mk hxi hxo cellHx =>
        cases repY with
        | cons cellY repHy repTy =>
          cases repHy with
          | mk hyi hyo cellHy =>
            have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_subsume»)
              (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume», ControlLower.hasControl])
            simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume»] at ev
            obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
            obtain ⟨rfl, rfl⟩ := sel
            obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellY dArm
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
            obtain ⟨rfl, rfl⟩ := sel2
            obtain ⟨bs3, body3, sel3, dArm3⟩ := evalExpr_match_load_var_enum rfl cellHx dArm2
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel3
            obtain ⟨rfl, rfl⟩ := sel3
            obtain ⟨bs4, body4, sel4, dArm4⟩ := evalExpr_match_load_var_enum rfl cellHy dArm3
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel4
            obtain ⟨rfl, rfl⟩ := sel4
            obtain ⟨_, _, bs5, body5, dCall1, sel5, dArm5⟩ := dArm4.matchValue_inv
            obtain ⟨_, _, _, _, dVarXi, dVarYi, dFn1⟩ := evalExpr_call2_inv dCall1
            obtain ⟨⟨⟩, rfl⟩ := dVarXi.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarYi.var_inv'
            simp only [instanceName] at dFn1
            obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hxi hyi dFn1
            rcases selectArm_ite_one_zero sel5 with ⟨_, rfl, rfl⟩ | ⟨hnlt1, _, _⟩
            · obtain ⟨_, _, h1, h2, dVarX, dCallRec, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm5
              obtain ⟨⟨⟩, rfl⟩ := dVarX.var_inv'
              obtain ⟨_, _, _, _, dVarXr, dVarYs, dFnRec⟩ := evalExpr_call2_inv dCallRec
              obtain ⟨⟨⟩, rfl⟩ := dVarXr.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarYs.var_inv'
              simp only [instanceName] at dFnRec
              obtain ⟨repRec, ext1⟩ := ih repTx (.cons cellY (.mk hyi hyo cellHy) repTy) dFnRec
              obtain ⟨repCons, ext2⟩ := RepNLVarList.allocCons ((RepNLVar.mk hxi hxo cellHx).mono' ext1) repRec
              simp only [nlvarsSubsume, hlt1, ↓reduceIte, nlVarList_inst]
              exact ⟨repCons, ext1.trans ext2⟩
            · exact absurd hlt1 hnlt1
  | case4 xi xo xr yi yo yr hnlt1 hlt2 ih =>
    cases repX with
    | cons cellX repHx repTx =>
      cases repHx with
      | mk hxi hxo cellHx =>
        cases repY with
        | cons cellY repHy repTy =>
          cases repHy with
          | mk hyi hyo cellHy =>
            have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_subsume»)
              (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume», ControlLower.hasControl])
            simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume»] at ev
            obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
            obtain ⟨rfl, rfl⟩ := sel
            obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellY dArm
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
            obtain ⟨rfl, rfl⟩ := sel2
            obtain ⟨bs3, body3, sel3, dArm3⟩ := evalExpr_match_load_var_enum rfl cellHx dArm2
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel3
            obtain ⟨rfl, rfl⟩ := sel3
            obtain ⟨bs4, body4, sel4, dArm4⟩ := evalExpr_match_load_var_enum rfl cellHy dArm3
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel4
            obtain ⟨rfl, rfl⟩ := sel4
            obtain ⟨_, _, bs5, body5, dCall1, sel5, dArm5⟩ := dArm4.matchValue_inv
            obtain ⟨_, _, _, _, dVarXi, dVarYi, dFn1⟩ := evalExpr_call2_inv dCall1
            obtain ⟨⟨⟩, rfl⟩ := dVarXi.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarYi.var_inv'
            simp only [instanceName] at dFn1
            obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hxi hyi dFn1
            rcases selectArm_ite_one_zero sel5 with ⟨hlt1, _, _⟩ | ⟨_, rfl, rfl⟩
            · exact absurd hlt1 hnlt1
            · obtain ⟨_, _, bs6, body6, dCall2, sel6, dArm6⟩ := dArm5.matchValue_inv
              obtain ⟨_, _, _, _, dVarYi2, dVarXi2, dFn2⟩ := evalExpr_call2_inv dCall2
              obtain ⟨⟨⟩, rfl⟩ := dVarYi2.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarXi2.var_inv'
              simp only [instanceName] at dFn2
              obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hyi hxi dFn2
              rcases selectArm_ite_one_zero sel6 with ⟨_, rfl, rfl⟩ | ⟨hnlt2, _, _⟩
              · obtain ⟨_, _, _, _, dVarXs, dVarYr, dFnRec⟩ := evalExpr_call2_inv dArm6
                obtain ⟨⟨⟩, rfl⟩ := dVarXs.var_inv'
                obtain ⟨⟨⟩, rfl⟩ := dVarYr.var_inv'
                simp only [instanceName] at dFnRec
                simpa [nlvarsSubsume, hnlt1, hlt2] using
                  ih (.cons cellX (.mk hxi hxo cellHx) repTx) repTy dFnRec
              · exact absurd hlt2 hnlt2
  | case5 xi xo xr yi yo yr hnlt1 hnlt2 hlt3 ih =>
    cases repX with
    | cons cellX repHx repTx =>
      cases repHx with
      | mk hxi hxo cellHx =>
        cases repY with
        | cons cellY repHy repTy =>
          cases repHy with
          | mk hyi hyo cellHy =>
            have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_subsume»)
              (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume», ControlLower.hasControl])
            simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume»] at ev
            obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
            obtain ⟨rfl, rfl⟩ := sel
            obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellY dArm
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
            obtain ⟨rfl, rfl⟩ := sel2
            obtain ⟨bs3, body3, sel3, dArm3⟩ := evalExpr_match_load_var_enum rfl cellHx dArm2
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel3
            obtain ⟨rfl, rfl⟩ := sel3
            obtain ⟨bs4, body4, sel4, dArm4⟩ := evalExpr_match_load_var_enum rfl cellHy dArm3
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel4
            obtain ⟨rfl, rfl⟩ := sel4
            obtain ⟨_, _, bs5, body5, dCall1, sel5, dArm5⟩ := dArm4.matchValue_inv
            obtain ⟨_, _, _, _, dVarXi, dVarYi, dFn1⟩ := evalExpr_call2_inv dCall1
            obtain ⟨⟨⟩, rfl⟩ := dVarXi.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarYi.var_inv'
            simp only [instanceName] at dFn1
            obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hxi hyi dFn1
            rcases selectArm_ite_one_zero sel5 with ⟨hlt1, _, _⟩ | ⟨_, rfl, rfl⟩
            · exact absurd hlt1 hnlt1
            · obtain ⟨_, _, bs6, body6, dCall2, sel6, dArm6⟩ := dArm5.matchValue_inv
              obtain ⟨_, _, _, _, dVarYi2, dVarXi2, dFn2⟩ := evalExpr_call2_inv dCall2
              obtain ⟨⟨⟩, rfl⟩ := dVarYi2.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarXi2.var_inv'
              simp only [instanceName] at dFn2
              obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hyi hxi dFn2
              rcases selectArm_ite_one_zero sel6 with ⟨hlt2, _, _⟩ | ⟨_, rfl, rfl⟩
              · exact absurd hlt2 hnlt2
              · obtain ⟨_, _, bs7, body7, dCall3, sel7, dArm7⟩ := dArm6.matchValue_inv
                obtain ⟨_, _, _, _, dVarYo, dVarXo, dFn3⟩ := evalExpr_call2_inv dCall3
                obtain ⟨⟨⟩, rfl⟩ := dVarYo.var_inv'
                obtain ⟨⟨⟩, rfl⟩ := dVarXo.var_inv'
                simp only [instanceName] at dFn3
                obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hyo hxo dFn3
                rcases selectArm_ite_one_zero sel7 with ⟨_, rfl, rfl⟩ | ⟨hnlt3, _, _⟩
                · obtain ⟨_, _, h1, h2, dVarX, dCallRec, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm7
                  obtain ⟨⟨⟩, rfl⟩ := dVarX.var_inv'
                  obtain ⟨_, _, _, _, dVarXr, dVarYr, dFnRec⟩ := evalExpr_call2_inv dCallRec
                  obtain ⟨⟨⟩, rfl⟩ := dVarXr.var_inv'
                  obtain ⟨⟨⟩, rfl⟩ := dVarYr.var_inv'
                  simp only [instanceName] at dFnRec
                  obtain ⟨repRec, ext1⟩ := ih repTx repTy dFnRec
                  obtain ⟨repCons, ext2⟩ := RepNLVarList.allocCons ((RepNLVar.mk hxi hxo cellHx).mono' ext1) repRec
                  simp only [nlvarsSubsume, hnlt1, hnlt2, hlt3, ↓reduceIte, nlVarList_inst]
                  exact ⟨repCons, ext1.trans ext2⟩
                · exact absurd hlt3 hnlt3
  | case6 xi xo xr yi yo yr hnlt1 hnlt2 hnlt3 ih =>
    cases repX with
    | cons cellX repHx repTx =>
      cases repHx with
      | mk hxi hxo cellHx =>
        cases repY with
        | cons cellY repHy repTy =>
          cases repHy with
          | mk hyi hyo cellHy =>
            have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_subsume»)
              (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume», ControlLower.hasControl])
            simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_subsume»] at ev
            obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellX ev
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
            obtain ⟨rfl, rfl⟩ := sel
            obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellY dArm
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
            obtain ⟨rfl, rfl⟩ := sel2
            obtain ⟨bs3, body3, sel3, dArm3⟩ := evalExpr_match_load_var_enum rfl cellHx dArm2
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel3
            obtain ⟨rfl, rfl⟩ := sel3
            obtain ⟨bs4, body4, sel4, dArm4⟩ := evalExpr_match_load_var_enum rfl cellHy dArm3
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel4
            obtain ⟨rfl, rfl⟩ := sel4
            obtain ⟨_, _, bs5, body5, dCall1, sel5, dArm5⟩ := dArm4.matchValue_inv
            obtain ⟨_, _, _, _, dVarXi, dVarYi, dFn1⟩ := evalExpr_call2_inv dCall1
            obtain ⟨⟨⟩, rfl⟩ := dVarXi.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarYi.var_inv'
            simp only [instanceName] at dFn1
            obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hxi hyi dFn1
            rcases selectArm_ite_one_zero sel5 with ⟨hlt1, _, _⟩ | ⟨_, rfl, rfl⟩
            · exact absurd hlt1 hnlt1
            · obtain ⟨_, _, bs6, body6, dCall2, sel6, dArm6⟩ := dArm5.matchValue_inv
              obtain ⟨_, _, _, _, dVarYi2, dVarXi2, dFn2⟩ := evalExpr_call2_inv dCall2
              obtain ⟨⟨⟩, rfl⟩ := dVarYi2.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarXi2.var_inv'
              simp only [instanceName] at dFn2
              obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hyi hxi dFn2
              rcases selectArm_ite_one_zero sel6 with ⟨hlt2, _, _⟩ | ⟨_, rfl, rfl⟩
              · exact absurd hlt2 hnlt2
              · obtain ⟨_, _, bs7, body7, dCall3, sel7, dArm7⟩ := dArm6.matchValue_inv
                obtain ⟨_, _, _, _, dVarYo, dVarXo, dFn3⟩ := evalExpr_call2_inv dCall3
                obtain ⟨⟨⟩, rfl⟩ := dVarYo.var_inv'
                obtain ⟨⟨⟩, rfl⟩ := dVarXo.var_inv'
                simp only [instanceName] at dFn3
                obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hyo hxo dFn3
                rcases selectArm_ite_one_zero sel7 with ⟨hlt3, _, _⟩ | ⟨_, rfl, rfl⟩
                · exact absurd hlt3 hnlt3
                · obtain ⟨_, _, _, _, dVarXr, dVarYr, dFnRec⟩ := evalExpr_call2_inv dArm7
                  obtain ⟨⟨⟩, rfl⟩ := dVarXr.var_inv'
                  obtain ⟨⟨⟩, rfl⟩ := dVarYr.var_inv'
                  simp only [instanceName] at dFnRec
                  simpa [nlvarsSubsume, hnlt1, hnlt2, hnlt3] using ih repTx repTy dFnRec


/-! ### Subsection 5: Level Normalization (`nl_add_const_go`, `nl_add_const`, `nl_add_var`, `normalize_step`, `normalize_aux`, `normalize_imax_dispatch`, `nl_subsume_entry`, `nl_subsumption_walk`, `level_normalize`) -/

/-- **`EvalFn W` refinement for `KernelLevels::nl_add_const_go`.** -/
theorem nlAddConstGo_refines {h h' : Heap F} {acc : List NLEntry}
    {path : List Nat} {k : Nat} {ptrAcc ptrPath r : SourceValue F}
    (repAcc : RepNLEntries h acc ptrAcc) (repPath : RepGuardList h path ptrPath)
    (hk : k < 4294967296)
    (ev : EvalFn W "KernelLevels::nl_add_const_go" [ptrAcc, ptrPath, .field (k : F)] h r h') :
    RepNLEntries h' (nlAddConstGo acc path k) r ∧ Heap.Extends h h' := by
  induction repAcc generalizing h' r with
  | nil cellAcc =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_add_const_go»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nl_add_const_go», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nl_add_const_go»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellAcc ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, h1, h2, dStoreEntry, dStoreNilE, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm
    obtain ⟨_, _, _, _, _, _, dVarPath, dVarK, dStoreNilV, rfl, rfl⟩ :=
      evalExpr_store_construct3_inv dStoreEntry
    obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
    obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNilV
    obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNilE
    simp only [nlAddConstGo, nlVarList_inst, nlEntry_inst, nlEntryList_inst]
    obtain ⟨repNilV, ext1⟩ := RepNLVarList.allocNil _
    obtain ⟨repEntry, ext2⟩ := RepNLEntry.alloc (e := ⟨path, k, []⟩) hk (repPath.mono' ext1) repNilV
    obtain ⟨repNilE, ext3⟩ := RepNLEntries.allocNil _
    obtain ⟨repCons, ext4⟩ := RepNLEntries.allocCons (repEntry.mono' ext3) repNilE
    exact ⟨repCons, ((ext1.trans ext2).trans ext3).trans ext4⟩
  | cons cellAcc repE repRest ih =>
    cases repE with
    | mk hec cellE repEp repEv =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_add_const_go»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_add_const_go», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_add_const_go»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellAcc ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellE dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dCallCmp, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, dVarPath, dVarEp, dFnCmp⟩ := evalExpr_call2_inv dCallCmp
      obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarEp.var_inv'
      simp only [instanceName] at dFnCmp
      obtain ⟨rfl, rfl⟩ := glistCmp_refines repPath repEp dFnCmp
      rcases selectArm_glistCmp path _ sel3 with
        ⟨hcmp0, rfl, rfl⟩ | ⟨hcmp1, rfl, rfl⟩ | ⟨hcmp2, rfl, rfl⟩
      · obtain ⟨_, _, bs4, body4, dCallLt, sel4, dArm4⟩ := dArm3.matchValue_inv
        obtain ⟨_, _, _, _, dVarEc, dVarK, dFnLt⟩ := evalExpr_call2_inv dCallLt
        obtain ⟨⟨⟩, rfl⟩ := dVarEc.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        simp only [instanceName] at dFnLt
        obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hec hk dFnLt
        rcases selectArm_ite_one_zero sel4 with ⟨hlt, rfl, rfl⟩ | ⟨hnlt, rfl, rfl⟩
        · obtain ⟨_, _, h1, h2, dStoreEntry, dVarRest, rfl, rfl⟩ :=
            evalExpr_store_construct2_inv dArm4
          obtain ⟨_, _, _, _, _, _, dVarEp2, dVarK2, dVarEv, rfl, rfl⟩ :=
            evalExpr_store_construct3_inv dStoreEntry
          obtain ⟨⟨⟩, rfl⟩ := dVarEp2.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarEv.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
          simp only [nlAddConstGo, hcmp0, hlt, ↓reduceIte, nlEntry_inst, nlEntryList_inst]
          obtain ⟨repEntry', ext1⟩ := RepNLEntry.alloc (e := ⟨_, k, _⟩) hk repEp repEv
          obtain ⟨repCons, ext2⟩ := RepNLEntries.allocCons repEntry' (repRest.mono' ext1)
          exact ⟨repCons, ext1.trans ext2⟩
        · obtain ⟨⟨⟩, rfl⟩ := dArm4.var_inv'
          simp only [nlAddConstGo, hcmp0, hnlt, ↓reduceIte]
          exact ⟨.cons cellAcc (.mk hec cellE repEp repEv) repRest, Heap.Extends.refl _⟩
      · obtain ⟨_, _, h1, h2, dStoreEntry, dVarAcc, rfl, rfl⟩ :=
          evalExpr_store_construct2_inv dArm3
        obtain ⟨_, _, _, _, _, _, dVarPath2, dVarK2, dStoreNilV, rfl, rfl⟩ :=
          evalExpr_store_construct3_inv dStoreEntry
        obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
        obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNilV
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        simp only [nlAddConstGo, hcmp1, nlVarList_inst, nlEntry_inst, nlEntryList_inst]
        obtain ⟨repNilV, ext1⟩ := RepNLVarList.allocNil _
        obtain ⟨repEntry, ext2⟩ :=
          RepNLEntry.alloc (e := ⟨path, k, []⟩) hk (repPath.mono' ext1) repNilV
        have repOrig : RepNLEntries _ (⟨_, _, _⟩ :: _) _ :=
          .cons cellAcc (.mk hec cellE repEp repEv) repRest
        obtain ⟨repCons, ext3⟩ :=
          RepNLEntries.allocCons repEntry (repOrig.mono' (ext1.trans ext2))
        exact ⟨repCons, (ext1.trans ext2).trans ext3⟩
      · obtain ⟨_, _, h1, h2, dVarE, dCallRec, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm3
        obtain ⟨⟨⟩, rfl⟩ := dVarE.var_inv'
        obtain ⟨_, _, _, _, _, _, dVarRest, dVarPath2, dVarK2, dFnRec⟩ :=
          evalExpr_call3_inv dCallRec
        obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
        simp only [instanceName] at dFnRec
        obtain ⟨repRest', ext1⟩ := ih dFnRec
        have repE' := (RepNLEntry.mk hec cellE repEp repEv).mono' ext1
        obtain ⟨repCons, ext2⟩ := RepNLEntries.allocCons repE' repRest'
        simp only [nlAddConstGo, hcmp2, nlEntryList_inst]
        exact ⟨repCons, ext1.trans ext2⟩

/-- **`EvalFn W` refinement for `KernelLevels::nl_add_const`.** -/
theorem nlAddConst_refines {h h' : Heap F} {acc : List NLEntry}
    {path : List Nat} {k : Nat} {ptrAcc ptrPath r : SourceValue F}
    (repAcc : RepNLEntries h acc ptrAcc) (repPath : RepGuardList h path ptrPath)
    (hk : k < 4294967296)
    (ev : EvalFn W "KernelLevels::nl_add_const" [ptrAcc, ptrPath, .field (k : F)] h r h') :
    RepNLEntries h' (nlAddConst acc path k) r ∧ Heap.Extends h h' := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_add_const»)
    (by simp [IxVM.Checked.Fn.«KernelLevels::nl_add_const», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«KernelLevels::nl_add_const»] at ev
  obtain ⟨_, _, bs, body, dVarK, sel, dArm⟩ := ev.matchValue_inv
  obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
  rcases selectArm_nat_zero_one_wildcard hk sel with
    ⟨hk0, rfl, rfl⟩ | ⟨hk1, rfl, rfl⟩ | ⟨hk0, hk1, rfl, rfl⟩
  · subst hk0
    obtain ⟨⟨⟩, rfl⟩ := dArm.var_inv'
    simp only [nlAddConst]
    exact ⟨repAcc, Heap.Extends.refl _⟩
  · subst hk1
    cases repPath with
    | nil cellPath =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellPath dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, _, _, _, _, dVarAcc, dVarPath, dVarK2, dFnGo⟩ := evalExpr_call3_inv dArm2
      obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
      simp only [instanceName, nlAddConst] at dFnGo ⊢
      exact nlAddConstGo_refines repAcc (.nil cellPath) hk dFnGo
    | cons cellPath repHd repTl =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellPath dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨⟨⟩, rfl⟩ := dArm2.var_inv'
      simp only [nlAddConst]
      exact ⟨repAcc, Heap.Extends.refl _⟩
  · obtain ⟨_, _, _, _, _, _, dVarAcc, dVarPath, dVarK2, dFnGo⟩ := evalExpr_call3_inv dArm
    obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
    simp only [instanceName] at dFnGo
    have hnl : nlAddConst acc path k = nlAddConstGo acc path k := by
      rcases k with _ | _ | k'
      · exact absurd rfl hk0
      · exact absurd rfl hk1
      · rfl
    rw [hnl]
    exact nlAddConstGo_refines repAcc repPath hk dFnGo

/-- **`EvalFn W` refinement for `KernelLevels::nl_add_var`.** -/
theorem nlAddVar_refines {h h' : Heap F} {acc : List NLEntry}
    {path : List Nat} {idx k : Nat} {ptrAcc ptrPath r : SourceValue F}
    (repAcc : RepNLEntries h acc ptrAcc) (repPath : RepGuardList h path ptrPath)
    (hidx : idx < 4294967296) (hk : k < 4294967296)
    (ev : EvalFn W "KernelLevels::nl_add_var"
      [ptrAcc, ptrPath, .field (idx : F), .field (k : F)] h r h') :
    RepNLEntries h' (nlAddVar acc path idx k) r ∧ Heap.Extends h h' := by
  induction repAcc generalizing h' r with
  | nil cellAcc =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_add_var»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nl_add_var», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nl_add_var»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellAcc ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, h1, h2, dStoreEntry, dStoreNilE, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm
    obtain ⟨_, _, _, _, _, _, dVarPath, dLit0, dStoreConsV, rfl, rfl⟩ :=
      evalExpr_store_construct3_inv dStoreEntry
    obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dLit0.literal_inv
    obtain ⟨_, _, _, _, dStoreVar, dStoreNilV, rfl, rfl⟩ := evalExpr_store_construct2_inv dStoreConsV
    obtain ⟨_, _, _, _, dVarIdx, dVarK, rfl, rfl⟩ := evalExpr_store_construct2_inv dStoreVar
    obtain ⟨⟨⟩, rfl⟩ := dVarIdx.var_inv'
    obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
    obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNilV
    obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNilE
    simp only [nlAddVar, nlVar_inst, nlVarList_inst, nlEntry_inst, nlEntryList_inst]
    obtain ⟨repVar, ext1⟩ := RepNLVar.alloc hidx hk _
    obtain ⟨repNilV, ext2⟩ := RepNLVarList.allocNil _
    obtain ⟨repConsV, ext3⟩ := RepNLVarList.allocCons (repVar.mono' ext2) repNilV
    have h0_cast : (0 : F) = ((0 : Nat) : F) := by simp
    rw [h0_cast]
    obtain ⟨repEntry, ext4⟩ :=
      RepNLEntry.alloc (e := ⟨path, 0, [⟨idx, k⟩]⟩) (Nat.zero_lt_succ _)
        (repPath.mono' ((ext1.trans ext2).trans ext3)) repConsV
    obtain ⟨repNilE, ext5⟩ := RepNLEntries.allocNil _
    obtain ⟨repConsE, ext6⟩ := RepNLEntries.allocCons (repEntry.mono' ext5) repNilE
    exact ⟨repConsE, ((((ext1.trans ext2).trans ext3).trans ext4).trans ext5).trans ext6⟩
  | cons cellAcc repE repRest ih =>
    cases repE with
    | mk hec cellE repEp repEv =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_add_var»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_add_var», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_add_var»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellAcc ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellE dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dCallCmp, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, dVarPath, dVarEp, dFnCmp⟩ := evalExpr_call2_inv dCallCmp
      obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarEp.var_inv'
      simp only [instanceName] at dFnCmp
      obtain ⟨rfl, rfl⟩ := glistCmp_refines repPath repEp dFnCmp
      rcases selectArm_glistCmp path _ sel3 with
        ⟨hcmp0, rfl, rfl⟩ | ⟨hcmp1, rfl, rfl⟩ | ⟨hcmp2, rfl, rfl⟩
      · obtain ⟨_, _, h1, h2, dStoreEntry, dVarRest, rfl, rfl⟩ :=
          evalExpr_store_construct2_inv dArm3
        obtain ⟨_, _, _, _, _, _, dVarEp2, dVarEc, dCallAdd, rfl, rfl⟩ :=
          evalExpr_store_construct3_inv dStoreEntry
        obtain ⟨⟨⟩, rfl⟩ := dVarEp2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarEc.var_inv'
        obtain ⟨_, _, _, _, _, _, dVarEv, dVarIdx, dVarK, dFnAdd⟩ := evalExpr_call3_inv dCallAdd
        obtain ⟨⟨⟩, rfl⟩ := dVarEv.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarIdx.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        simp only [instanceName] at dFnAdd
        obtain ⟨repEv', ext1⟩ := nlvarsAdd_refines repEv hidx hk dFnAdd
        obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
        obtain ⟨repEntry', ext2⟩ :=
          RepNLEntry.alloc (e := ⟨_, _, nlvarsAdd _ idx k⟩) hec (repEp.mono' ext1) repEv'
        obtain ⟨repCons, ext3⟩ := RepNLEntries.allocCons repEntry' (repRest.mono' (ext1.trans ext2))
        simp only [nlAddVar, hcmp0, nlEntry_inst, nlEntryList_inst]
        exact ⟨repCons, (ext1.trans ext2).trans ext3⟩
      · obtain ⟨_, _, h1, h2, dStoreEntry, dVarAcc, rfl, rfl⟩ :=
          evalExpr_store_construct2_inv dArm3
        obtain ⟨_, _, _, _, _, _, dVarPath2, dLit0, dStoreConsV, rfl, rfl⟩ :=
          evalExpr_store_construct3_inv dStoreEntry
        obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dLit0.literal_inv
        obtain ⟨_, _, _, _, dStoreVar, dStoreNilV, rfl, rfl⟩ :=
          evalExpr_store_construct2_inv dStoreConsV
        obtain ⟨_, _, _, _, dVarIdx, dVarK, rfl, rfl⟩ := evalExpr_store_construct2_inv dStoreVar
        obtain ⟨⟨⟩, rfl⟩ := dVarIdx.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNilV
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        simp only [nlAddVar, hcmp1, nlVar_inst, nlVarList_inst, nlEntry_inst, nlEntryList_inst]
        obtain ⟨repVar, ext1⟩ := RepNLVar.alloc hidx hk _
        obtain ⟨repNilV, ext2⟩ := RepNLVarList.allocNil _
        obtain ⟨repConsV, ext3⟩ := RepNLVarList.allocCons (repVar.mono' ext2) repNilV
        have h0_cast : (0 : F) = ((0 : Nat) : F) := by simp
        rw [h0_cast]
        obtain ⟨repEntry, ext4⟩ :=
          RepNLEntry.alloc (e := ⟨path, 0, [⟨idx, k⟩]⟩) (Nat.zero_lt_succ _)
            (repPath.mono' ((ext1.trans ext2).trans ext3)) repConsV
        have repOrig : RepNLEntries _ (⟨_, _, _⟩ :: _) _ :=
          .cons cellAcc (.mk hec cellE repEp repEv) repRest
        obtain ⟨repConsE, ext5⟩ :=
          RepNLEntries.allocCons repEntry (repOrig.mono' (((ext1.trans ext2).trans ext3).trans ext4))
        exact ⟨repConsE, (((ext1.trans ext2).trans ext3).trans ext4).trans ext5⟩
      · obtain ⟨_, _, h1, h2, dVarE, dCallRec, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm3
        obtain ⟨⟨⟩, rfl⟩ := dVarE.var_inv'
        obtain ⟨_, _, _, _, _, _, _, _, dVarRest, dVarPath2, dVarIdx, dVarK, dFnRec⟩ :=
          evalExpr_call4_inv dCallRec
        obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarIdx.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        simp only [instanceName] at dFnRec
        obtain ⟨repRest', ext1⟩ := ih dFnRec
        have repE' := (RepNLEntry.mk hec cellE repEp repEv).mono' ext1
        obtain ⟨repCons, ext2⟩ := RepNLEntries.allocCons repE' repRest'
        simp only [nlAddVar, hcmp2, nlEntryList_inst]
        exact ⟨repCons, ext1.trans ext2⟩

theorem selectArm_orderedInsert_tuple {types : Types} {h : Heap F} (b : Bool) (ptrOut : SourceValue F)
    {e1 e0 : Generic.Expr F} {bs : Environment F Nat} {body : Generic.Expr F}
    (sel : SourceSemantics.selectArm W types h (.tuple [.field (if b then 1 else 0), ptrOut])
      [((.tuple [(.literal 1), (.bind "new_path")]), e1),
       ((.tuple [(.literal 0), .wildcard]), e0)] = .ok (some (bs, body))) :
    (b = true ∧ bs = [("new_path", ptrOut)] ∧ body = e1) ∨
    (b = false ∧ bs = [] ∧ body = e0) := by
  cases b <;> {
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_tuple, matchPattern_literal,
      matchPattern_bind, matchPattern_wildcard, SourceSemantics.matchListWith,
      bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    simp
  }

/-- Maximum structural depth of a `normalizeStep` argument. -/
def normArgDepth : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level) → Nat
  | .inl l => levelDepth l
  | .inr (a, b) => Max.max (levelDepth a) (levelDepth b)

/-- **`EvalFn W` refinement for `normalizeStep` (`normalize_aux` and `normalize_imax_dispatch`).** -/
theorem normalizeStep_refines (fuel : Nat) :
    ∀ {h h' : Heap F} (arg : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level))
      {path : List Nat} {k : Nat} {acc : List NLEntry}
      {ptrPath ptrAcc r : SourceValue F},
      normFuel arg ≤ fuel →
      normArgDepth arg + k < 4294967296 →
      RepGuardList h path ptrPath →
      RepNLEntries h acc ptrAcc →
      (match arg with
       | .inl l =>
         ∀ {ptrL}, RepKLevel h l ptrL →
           EvalFn W "KernelLevels::normalize_aux" [ptrL, ptrPath, .field (k : F), ptrAcc] h r h' →
           RepNLEntries h' (normalizeStep fuel (.inl l) path k acc) r ∧ Heap.Extends h h'
       | .inr (a, b) =>
         ∀ {ptrA ptrB}, RepKLevel h a ptrA → RepKLevel h b ptrB →
           EvalFn W "KernelLevels::normalize_imax_dispatch"
             [ptrA, ptrB, ptrPath, .field (k : F), ptrAcc] h r h' →
           RepNLEntries h' (normalizeStep fuel (.inr (a, b)) path k acc) r ∧ Heap.Extends h h') := by
  induction fuel with
  | zero =>
    intro h h' arg path k acc ptrPath ptrAcc r hfuel
    cases arg with
    | inl l => simp [normFuel] at hfuel
    | inr ab => simp [normFuel] at hfuel
  | succ fuel ih =>
    intro h h' arg path k acc ptrPath ptrAcc r hfuel hdepth repPath repAcc
    have hk : k < 4294967296 := by omega
    cases arg with
    | inl l =>
      intro ptrL repL ev
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::normalize_aux»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::normalize_aux», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::normalize_aux»] at ev
      cases repL with
      | zero cellL =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, _, _, _, _, dVarAcc, dVarPath, dVarK, dFn⟩ := evalExpr_call3_inv dArm
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        simp only [instanceName, normalizeStep] at dFn ⊢
        exact nlAddConst_refines repAcc repPath hk dFn
      | @succ _ inner _ cellL repInner =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, _, _, _, _, _, _, dVarInner, dVarPath, dAdd, dVarAcc, dFn⟩ :=
          evalExpr_call4_inv dArm
        obtain ⟨⟨⟩, rfl⟩ := dVarInner.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        obtain ⟨_, _, _, dVarK, dLit1, rfl⟩ := evalExpr_add_inv dAdd
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dLit1.literal_inv
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        simp only [instanceName] at dFn
        have hcast : ((k : F) + 1) = (((k + 1 : Nat) : F)) := by push_cast; rfl
        rw [hcast] at dFn
        have hf : normFuel (.inl inner) ≤ fuel := by have := normFuel_succ inner; omega
        have hd : normArgDepth (.inl inner) + (k + 1) < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        exact ih (.inl inner) hf hd repPath repAcc repInner dFn
      | @max _ a b _ _ cellL repA repB =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, _, _, _, _, _, _, dVarB, dVarPath, dVarK, dCallA, dFnB⟩ :=
          evalExpr_call4_inv dArm
        obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        obtain ⟨_, _, _, _, _, _, _, _, dVarA, dVarPath2, dVarK2, dVarAcc, dFnA⟩ :=
          evalExpr_call4_inv dCallA
        obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        simp only [instanceName] at dFnA dFnB
        have hfA : normFuel (.inl a) ≤ fuel := by have := normFuel_max_left a b; omega
        have hfB : normFuel (.inl b) ≤ fuel := by have := normFuel_max_right a b; omega
        have hdA : normArgDepth (.inl a) + k < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        have hdB : normArgDepth (.inl b) + k < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        obtain ⟨repAcc1, ext1⟩ := ih (.inl a) hfA hdA repPath repAcc repA dFnA
        obtain ⟨repAcc2, ext2⟩ :=
          ih (.inl b) hfB hdB (repPath.mono' ext1) repAcc1 (repB.mono' ext1) dFnB
        exact ⟨repAcc2, ext1.trans ext2⟩
      | @imax _ u b _ _ cellL repU repB =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, _, _, _, _, _, _, _, _, dVarU, dVarB, dVarPath, dVarK, dVarAcc, dFn⟩ :=
          evalExpr_call5_inv dArm
        obtain ⟨⟨⟩, rfl⟩ := dVarU.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        simp only [instanceName] at dFn
        have hf : normFuel (.inr (u, b)) ≤ fuel := by have := normFuel_imax u b; omega
        have hd : normArgDepth (.inr (u, b)) + k < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        exact ih (.inr (u, b)) hf hd repPath repAcc repU repB dFn
      | @param _ idx hidx cellL =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, bs2, body2, dCallIns, sel2, dArm2⟩ := dArm.matchValue_inv
        obtain ⟨_, _, _, _, dVarIdx, dVarPath, dFnIns⟩ := evalExpr_call2_inv dCallIns
        obtain ⟨⟨⟩, rfl⟩ := dVarIdx.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        simp only [instanceName] at dFnIns
        obtain ⟨ptrNewPath, rfl, repNewPath, ext1⟩ := glistOrderedInsert_refines hidx repPath dFnIns
        rcases selectArm_orderedInsert_tuple _ _ sel2 with
          ⟨hins, rfl, rfl⟩ | ⟨hins, rfl, rfl⟩
        · cases hpair : glistOrderedInsert idx path with
          | mk f np =>
            rw [hpair] at hins repNewPath
            subst hins
            obtain ⟨_, _, _, _, _, _, _, _, dCallConst, dVarNewPath, dVarIdx2, dVarK, dFnVar⟩ :=
              evalExpr_call4_inv dArm2
            obtain ⟨_, _, _, _, _, _, dVarAcc, dVarPath2, dVarK2, dFnConst⟩ :=
              evalExpr_call3_inv dCallConst
            obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
            simp only [instanceName] at dFnConst
            obtain ⟨repAcc1, ext2⟩ :=
              nlAddConst_refines (repAcc.mono' ext1) (repPath.mono' ext1) hk dFnConst
            obtain ⟨⟨⟩, rfl⟩ := dVarNewPath.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarIdx2.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
            simp only [instanceName] at dFnVar
            obtain ⟨repAcc2, ext3⟩ :=
              nlAddVar_refines repAcc1 (repNewPath.mono' ext2) hidx hk dFnVar
            simp only [normalizeStep, hpair, ↓reduceIte]
            exact ⟨repAcc2, (ext1.trans ext2).trans ext3⟩
        · obtain ⟨_, _, bs3, body3, dVarK, sel3, dArm3⟩ := dArm2.matchValue_inv
          obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
          rcases selectArm_nat_zero_wildcard (Nat.le_of_lt hk) sel3 with
            ⟨hk0, rfl, rfl⟩ | ⟨hk0, rfl, rfl⟩
          · obtain ⟨⟨⟩, rfl⟩ := dArm3.var_inv'
            simp only [normalizeStep]
            cases hpair : glistOrderedInsert idx path with
            | mk f np =>
              rw [hpair] at hins
              subst hins
              simp only [hk0, ↓reduceIte]
              exact ⟨repAcc.mono' ext1, ext1⟩
          · obtain ⟨_, _, _, _, _, _, _, _, dVarAcc, dVarPath2, dVarIdx2, dVarK2, dFnVar⟩ :=
              evalExpr_call4_inv dArm3
            obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarIdx2.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
            simp only [instanceName] at dFnVar
            obtain ⟨repAcc1, ext2⟩ :=
              nlAddVar_refines (repAcc.mono' ext1) (repPath.mono' ext1) hidx hk dFnVar
            simp only [normalizeStep]
            cases hpair : glistOrderedInsert idx path with
            | mk f np =>
              rw [hpair] at hins
              subst hins
              simp only [hk0, ↓reduceIte]
              exact ⟨repAcc1, ext1.trans ext2⟩
    | inr ab =>
      rcases ab with ⟨a, b⟩
      intro ptrA ptrB repA repB ev
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::normalize_imax_dispatch»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::normalize_imax_dispatch», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::normalize_imax_dispatch»] at ev
      cases repB with
      | zero cellB =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellB ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, _, _, _, _, dVarAcc, dVarPath, dVarK, dFn⟩ := evalExpr_call3_inv dArm
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        simp only [instanceName, normalizeStep] at dFn ⊢
        exact nlAddConst_refines repAcc repPath hk dFn
      | @succ _ v _ cellB repV =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellB ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, _, _, _, _, _, _, dVarV, dVarPath, dAdd, dCallA, dFnV⟩ :=
          evalExpr_call4_inv dArm
        obtain ⟨⟨⟩, rfl⟩ := dVarV.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        obtain ⟨_, _, _, dVarK, dLit1, rfl⟩ := evalExpr_add_inv dAdd
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dLit1.literal_inv
        obtain ⟨_, _, _, _, _, _, _, _, dVarA, dVarPath2, dVarK2, dVarAcc, dFnA⟩ :=
          evalExpr_call4_inv dCallA
        obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        simp only [instanceName] at dFnA dFnV
        have hfA : normFuel (.inl a) ≤ fuel := by have := normFuel_inr_succ_a a v; omega
        have hfV : normFuel (.inl v) ≤ fuel := by have := normFuel_inr_succ_v a v; omega
        have hdA : normArgDepth (.inl a) + k < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        have hdV : normArgDepth (.inl v) + (k + 1) < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        obtain ⟨repAcc1, ext1⟩ := ih (.inl a) hfA hdA repPath repAcc repA dFnA
        have hcast : ((k : F) + 1) = (((k + 1 : Nat) : F)) := by push_cast; rfl
        rw [hcast] at dFnV
        obtain ⟨repAcc2, ext2⟩ :=
          ih (.inl v) hfV hdV (repPath.mono' ext1) repAcc1 (repV.mono' ext1) dFnV
        exact ⟨repAcc2, ext1.trans ext2⟩
      | @max _ v w _ _ cellB repV repW =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellB ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, _, _, _, _, _, _, _, _, dVarA, dVarW, dVarPath, dVarK, dCallV, dFnW⟩ :=
          evalExpr_call5_inv dArm
        obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarW.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        obtain ⟨_, _, _, _, _, _, _, _, _, _, dVarA2, dVarV, dVarPath2, dVarK2, dVarAcc, dFnV⟩ :=
          evalExpr_call5_inv dCallV
        obtain ⟨⟨⟩, rfl⟩ := dVarA2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarV.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        simp only [instanceName] at dFnV dFnW
        have hfV : normFuel (.inr (a, v)) ≤ fuel := by have := normFuel_inr_max_left a v w; omega
        have hfW : normFuel (.inr (a, w)) ≤ fuel := by have := normFuel_inr_max_right a v w; omega
        have hdV : normArgDepth (.inr (a, v)) + k < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        have hdW : normArgDepth (.inr (a, w)) + k < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        obtain ⟨repAcc1, ext1⟩ := ih (.inr (a, v)) hfV hdV repPath repAcc repA repV dFnV
        obtain ⟨repAcc2, ext2⟩ :=
          ih (.inr (a, w)) hfW hdW (repPath.mono' ext1) repAcc1 (repA.mono' ext1) (repW.mono' ext1) dFnW
        exact ⟨repAcc2, ext1.trans ext2⟩
      | @imax _ v w _ _ cellB repV repW =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellB ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, _, _, _, _, _, _, _, _, dVarV, dVarW, dVarPath, dVarK, dCallAW, dFnVW⟩ :=
          evalExpr_call5_inv dArm
        obtain ⟨⟨⟩, rfl⟩ := dVarV.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarW.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
        obtain ⟨_, _, _, _, _, _, _, _, _, _, dVarA, dVarW2, dVarPath2, dVarK2, dVarAcc, dFnAW⟩ :=
          evalExpr_call5_inv dCallAW
        obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarW2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
        simp only [instanceName] at dFnAW dFnVW
        have hfAW : normFuel (.inr (a, w)) ≤ fuel := by have := normFuel_inr_imax_right a v w; omega
        have hfVW : normFuel (.inr (v, w)) ≤ fuel := by have := normFuel_inr_imax_vw a v w; omega
        have hdAW : normArgDepth (.inr (a, w)) + k < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        have hdVW : normArgDepth (.inr (v, w)) + k < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        obtain ⟨repAcc1, ext1⟩ := ih (.inr (a, w)) hfAW hdAW repPath repAcc repA repW dFnAW
        obtain ⟨repAcc2, ext2⟩ :=
          ih (.inr (v, w)) hfVW hdVW (repPath.mono' ext1) repAcc1 (repV.mono' ext1) (repW.mono' ext1) dFnVW
        exact ⟨repAcc2, ext1.trans ext2⟩
      | @param _ idx hidx cellB =>
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellB ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨_, _, bs2, body2, dCallIns, sel2, dArm2⟩ := dArm.matchValue_inv
        obtain ⟨_, _, _, _, dVarIdx, dVarPath, dFnIns⟩ := evalExpr_call2_inv dCallIns
        obtain ⟨⟨⟩, rfl⟩ := dVarIdx.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarPath.var_inv'
        simp only [instanceName] at dFnIns
        obtain ⟨ptrNewPath, rfl, repNewPath, ext1⟩ := glistOrderedInsert_refines hidx repPath dFnIns
        have hfA : normFuel (.inl a) ≤ fuel := by have := normFuel_inr_param a idx; omega
        have hdA : normArgDepth (.inl a) + k < 4294967296 := by
          simp only [normArgDepth, levelDepth] at hdepth ⊢; omega
        rcases selectArm_orderedInsert_tuple _ _ sel2 with
          ⟨hins, rfl, rfl⟩ | ⟨hins, rfl, rfl⟩
        · cases hpair : glistOrderedInsert idx path with
          | mk f np =>
            rw [hpair] at hins repNewPath
            subst hins
            obtain ⟨_, _, _, _, _, _, _, _, dVarA, dVarNewPath, dVarK, dCallVar, dFnA⟩ :=
              evalExpr_call4_inv dArm2
            obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarNewPath.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
            obtain ⟨_, _, _, _, _, _, _, _, dCallConst, dVarNewPath2, dVarIdx2, dVarK2, dFnVar⟩ :=
              evalExpr_call4_inv dCallVar
            obtain ⟨_, _, _, _, _, _, dVarAcc, dVarPath2, dVarK3, dFnConst⟩ :=
              evalExpr_call3_inv dCallConst
            obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarK3.var_inv'
            simp only [instanceName] at dFnConst
            obtain ⟨repAcc1, ext2⟩ :=
              nlAddConst_refines (repAcc.mono' ext1) (repPath.mono' ext1) hk dFnConst
            obtain ⟨⟨⟩, rfl⟩ := dVarNewPath2.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarIdx2.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
            simp only [instanceName] at dFnVar
            obtain ⟨repAcc2, ext3⟩ :=
              nlAddVar_refines repAcc1 (repNewPath.mono' ext2) hidx hk dFnVar
            simp only [instanceName] at dFnA
            obtain ⟨repAcc3, ext4⟩ :=
              ih (.inl a) hfA hdA (repNewPath.mono' (ext2.trans ext3)) repAcc2
                (repA.mono' ((ext1.trans ext2).trans ext3)) dFnA
            simp only [normalizeStep, hpair, ↓reduceIte]
            exact ⟨repAcc3, ((ext1.trans ext2).trans ext3).trans ext4⟩
        · cases hpair : glistOrderedInsert idx path with
          | mk f np =>
            rw [hpair] at hins
            subst hins
            obtain ⟨_, _, bs3, dMatchK, hpatAcc2, dCallA⟩ := dArm2.letValue_inv
            obtain ⟨_, _, bs4, body4, dVarK, sel4, dArm4⟩ := dMatchK.matchValue_inv
            obtain ⟨⟨⟩, rfl⟩ := dVarK.var_inv'
            rcases selectArm_nat_zero_wildcard (Nat.le_of_lt hk) sel4 with
              ⟨hk0, rfl, rfl⟩ | ⟨hk0, rfl, rfl⟩
            · subst hk0
              obtain ⟨⟨⟩, rfl⟩ := dArm4.var_inv'
              simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatAcc2
              subst hpatAcc2
              obtain ⟨_, _, _, _, _, _, _, _, dVarA, dVarPath2, dVarK2, dVarAcc2, dFnA⟩ :=
                evalExpr_call4_inv dCallA
              obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarAcc2.var_inv'
              simp only [instanceName] at dFnA
              obtain ⟨repAcc3, ext2⟩ :=
                ih (.inl a) hfA hdA (repPath.mono' ext1) (repAcc.mono' ext1) (repA.mono' ext1) dFnA
              simp only [normalizeStep, hpair, Bool.false_eq_true, ↓reduceIte]
              exact ⟨repAcc3, ext1.trans ext2⟩
            · obtain ⟨_, _, _, _, _, _, _, _, dVarAcc, dVarPath2, dVarIdx2, dVarK2, dFnVar⟩ :=
                evalExpr_call4_inv dArm4
              obtain ⟨⟨⟩, rfl⟩ := dVarAcc.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarPath2.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarIdx2.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarK2.var_inv'
              simp only [instanceName] at dFnVar
              obtain ⟨repAcc2, ext2⟩ :=
                nlAddVar_refines (repAcc.mono' ext1) (repPath.mono' ext1) hidx hk dFnVar
              simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatAcc2
              subst hpatAcc2
              obtain ⟨_, _, _, _, _, _, _, _, dVarA, dVarPath3, dVarK3, dVarAcc2, dFnA⟩ :=
                evalExpr_call4_inv dCallA
              obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarPath3.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarK3.var_inv'
              obtain ⟨⟨⟩, rfl⟩ := dVarAcc2.var_inv'
              simp only [instanceName] at dFnA
              obtain ⟨repAcc3, ext3⟩ :=
                ih (.inl a) hfA hdA (repPath.mono' (ext1.trans ext2)) repAcc2
                  (repA.mono' (ext1.trans ext2)) dFnA
              simp only [normalizeStep, hpair, hk0, Bool.false_eq_true, ↓reduceIte]
              exact ⟨repAcc3, (ext1.trans ext2).trans ext3⟩

/-- **`EvalFn W` refinement for `KernelLevels::normalize_aux`.** -/
theorem normalizeAux_refines {h h' : Heap F} {l : Ix.Kernel.Level}
    {path : List Nat} {k : Nat} {acc : List NLEntry}
    {ptrL ptrPath ptrAcc r : SourceValue F}
    (repL : RepKLevel h l ptrL) (repPath : RepGuardList h path ptrPath)
    (repAcc : RepNLEntries h acc ptrAcc)
    (hdepth : levelDepth l + k < 4294967296)
    (ev : EvalFn W "KernelLevels::normalize_aux" [ptrL, ptrPath, .field (k : F), ptrAcc] h r h') :
    RepNLEntries h' (normalizeAux l path k acc) r ∧ Heap.Extends h h' :=
  normalizeStep_refines (normFuel (.inl l)) (.inl l) (Nat.le_refl _) hdepth repPath repAcc repL ev

/-- **`EvalFn W` refinement for `KernelLevels::normalize_imax_dispatch`.** -/
theorem normalizeIMaxDispatch_refines {h h' : Heap F} {a b : Ix.Kernel.Level}
    {path : List Nat} {k : Nat} {acc : List NLEntry}
    {ptrA ptrB ptrPath ptrAcc r : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (repPath : RepGuardList h path ptrPath) (repAcc : RepNLEntries h acc ptrAcc)
    (hdepth : Max.max (levelDepth a) (levelDepth b) + k < 4294967296)
    (ev : EvalFn W "KernelLevels::normalize_imax_dispatch"
      [ptrA, ptrB, ptrPath, .field (k : F), ptrAcc] h r h') :
    RepNLEntries h' (normalizeIMaxDispatch a b path k acc) r ∧ Heap.Extends h h' :=
  normalizeStep_refines (normFuel (.inr (a, b))) (.inr (a, b)) (Nat.le_refl _)
    hdepth repPath repAcc repA repB ev

def nlSubsumeOr1 (p1 p2 : List Nat) (c1 c2 : Nat) : Bool :=
  if glistEqLen p1 p2 then true else decide (c2 < c1)

def nlSubsumeOr2 (v1 v2 : List NLVar) (c1 : Nat) : Bool :=
  match v2 with
  | [] => true
  | _ :: _ => decide (nlvarsMaxOffset v1 + 1 < c1)

def nlSubsumeC1n (p1 p2 : List Nat) (c1 c2 : Nat) (v1 v2 : List NLVar) : Nat :=
  if c1 = 0 then 0
  else if nlSubsumeOr1 p1 p2 c1 c2 && nlSubsumeOr2 v1 v2 c1 then c1 else 0

def nlSubsumeV1n (p1 p2 : List Nat) (v1 v2 : List NLVar) : List NLVar :=
  if glistEqLen p1 p2 then v1
  else match v2 with
    | [] => v1
    | _ :: _ => nlvarsSubsume v1 v2

theorem nlSubsumeEntry_cons (p1 : List Nat) (c1 : Nat) (v1 : List NLVar)
    (p2 : List Nat) (c2 : Nat) (v2 : List NLVar) (srest : List NLEntry) :
    nlSubsumeEntry ⟨p1, c1, v1⟩ (⟨p2, c2, v2⟩ :: srest) =
      if !(glistSubset p2 p1) then
        nlSubsumeEntry ⟨p1, c1, v1⟩ srest
      else
        nlSubsumeEntry ⟨p1, nlSubsumeC1n p1 p2 c1 c2 v1 v2, nlSubsumeV1n p1 p2 v1 v2⟩ srest := rfl

/-- **`EvalFn W` refinement for `KernelLevels::nl_subsume_entry`.** -/
theorem nlSubsumeEntry_refines {h h' : Heap F} {e : NLEntry} {snap : List NLEntry}
    {ptrE ptrSnap r : SourceValue F}
    (repE : RepNLEntry h e ptrE) (repSnap : RepNLEntries h snap ptrSnap)
    (ev : EvalFn W "KernelLevels::nl_subsume_entry" [ptrE, ptrSnap] h r h') :
    RepNLEntry h' (nlSubsumeEntry e snap) r ∧ Heap.Extends h h' := by
  induction snap generalizing h h' e ptrE ptrSnap r with
  | nil =>
    cases repSnap with
    | nil cellSnap =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_subsume_entry»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_subsume_entry», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_subsume_entry»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellSnap ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨⟨⟩, rfl⟩ := dArm.var_inv'
      simp only [nlSubsumeEntry]
      exact ⟨repE, Heap.Extends.refl _⟩
  | cons s srest ih =>
    rcases e with ⟨p1, c1, v1⟩
    rcases s with ⟨p2, c2, v2⟩
    cases repSnap with
    | cons cellSnap repS repSrest =>
      cases repE with
      | mk hc1 cellE repP1 repV1 =>
        dsimp only at hc1 cellE repP1 repV1
        cases repS with
        | mk hc2 cellS repP2 repV2 =>
          dsimp only at hc2 cellS repP2 repV2
          have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_subsume_entry»)
            (by simp [IxVM.Checked.Fn.«KernelLevels::nl_subsume_entry», ControlLower.hasControl])
          simp only [IxVM.Checked.Fn.«KernelLevels::nl_subsume_entry»] at ev
          obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellSnap ev
          simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
            SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
          obtain ⟨rfl, rfl⟩ := sel
          obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellE dArm
          simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
            SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
          obtain ⟨rfl, rfl⟩ := sel2
          obtain ⟨bs3, body3, sel3, dArm3⟩ := evalExpr_match_load_var_enum rfl cellS dArm2
          simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
            SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel3
          obtain ⟨rfl, rfl⟩ := sel3
          obtain ⟨_, _, bs4, body4, dCallSub, sel4, dArm4⟩ := dArm3.matchValue_inv
          obtain ⟨_, _, _, _, dVarP2, dVarP1, dFnSub⟩ := evalExpr_call2_inv dCallSub
          obtain ⟨⟨⟩, h_eq⟩ := dVarP2.var_inv'; have h_eq := h_eq.symm; subst h_eq
          obtain ⟨⟨⟩, h_eq⟩ := dVarP1.var_inv'; have h_eq := h_eq.symm; subst h_eq
          simp only [instanceName] at dFnSub
          obtain ⟨rfl, h_eq⟩ := glistSubset_refines repP2 repP1 dFnSub; have h_eq := h_eq.symm; subst h_eq
          rcases selectArm_bool_zero_wildcard sel4 with ⟨hnsub, rfl, rfl⟩ | ⟨hsub, rfl, rfl⟩
          · obtain ⟨_, _, _, _, dVarE, dVarSrest, dFnRec⟩ := evalExpr_call2_inv dArm4
            obtain ⟨⟨⟩, rfl⟩ := dVarE.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarSrest.var_inv'
            simp only [instanceName] at dFnRec
            simpa [nlSubsumeEntry, hnsub] using ih (.mk hc1 cellE repP1 repV1) repSrest dFnRec
          · obtain ⟨_, _, bs5, dCallEqLen, hpatSame, dLetSame⟩ := dArm4.letValue_inv
            obtain ⟨_, _, _, _, dVarP1', dVarP2', dFnEqLen⟩ := evalExpr_call2_inv dCallEqLen
            obtain ⟨⟨⟩, h_eq⟩ := dVarP1'.var_inv'; have h_eq := h_eq.symm; subst h_eq
            obtain ⟨⟨⟩, h_eq⟩ := dVarP2'.var_inv'; have h_eq := h_eq.symm; subst h_eq
            simp only [instanceName] at dFnEqLen
            obtain ⟨rfl, h_eq⟩ := glistEqLen_refines repP1 repP2 dFnEqLen; have h_eq := h_eq.symm; subst h_eq
            simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatSame
            subst hpatSame
            obtain ⟨vc1n, h_c1n, bs6, dMatchC1, hpatC1n, dLetC1n⟩ := dLetSame.letValue_inv
            have hc1n_eval : vc1n = .field (nlSubsumeC1n p1 p2 c1 c2 v1 v2 : F) ∧ h_c1n = h := by
              obtain ⟨_, _, bsC, bodyC, dVarC1, selC, dArmC⟩ := dMatchC1.matchValue_inv
              obtain ⟨⟨⟩, h_eq⟩ := dVarC1.var_inv'; have h_eq := h_eq.symm; subst h_eq
              rcases selectArm_nat_zero_wildcard (Nat.le_of_lt hc1) selC with
                ⟨hc1_0, rfl, rfl⟩ | ⟨hc1_0, rfl, rfl⟩
              · obtain ⟨rfl, h_eq⟩ := dArmC.literal_inv; have h_eq := h_eq.symm; subst h_eq
                simp [nlSubsumeC1n, hc1_0]
              · obtain ⟨vor1, h_or1, bsOr1, dMatchOr1, hpatOr1, dLetOr1⟩ := dArmC.letValue_inv
                have hor1_eval : vor1 = .field (if nlSubsumeOr1 p1 p2 c1 c2 then 1 else 0) ∧ h_or1 = h := by
                  obtain ⟨_, _, bsO1, bodyO1, dVarSame, selO1, dArmO1⟩ := dMatchOr1.matchValue_inv
                  obtain ⟨⟨⟩, h_eq⟩ := dVarSame.var_inv'; have h_eq := h_eq.symm; subst h_eq
                  rcases selectArm_bool_one_zero selO1 with ⟨hsame, rfl, rfl⟩ | ⟨hnsame, rfl, rfl⟩
                  · obtain ⟨rfl, h_eq⟩ := dArmO1.literal_inv; have h_eq := h_eq.symm; subst h_eq
                    simp [nlSubsumeOr1, hsame]
                  · obtain ⟨_, _, _, _, dVarC2, dVarC1', dFnLt⟩ := evalExpr_call2_inv dArmO1
                    obtain ⟨⟨⟩, h_eq⟩ := dVarC2.var_inv'; have h_eq := h_eq.symm; subst h_eq
                    obtain ⟨⟨⟩, h_eq⟩ := dVarC1'.var_inv'; have h_eq := h_eq.symm; subst h_eq
                    simp only [instanceName] at dFnLt
                    obtain ⟨rfl, h_eq⟩ := u32LessThanFields_refines hc2 hc1 dFnLt; have h_eq := h_eq.symm; subst h_eq
                    simp [nlSubsumeOr1, hnsame]
                obtain ⟨rfl, h_eq⟩ := hor1_eval; have h_eq := h_eq.symm; subst h_eq
                simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatOr1
                subst hpatOr1
                obtain ⟨vor2, h_or2, bsOr2, dMatchOr2, hpatOr2, dLetOr2⟩ := dLetOr1.letValue_inv
                have hor2_eval : vor2 = .field (if nlSubsumeOr2 v1 v2 c1 then 1 else 0) ∧ h_or2 = h := by
                  cases repV2 with
                  | nil cellV2 =>
                    obtain ⟨bsO2, bodyO2, selO2, dArmO2⟩ :=
                      evalExpr_match_load_var_enum rfl cellV2 dMatchOr2
                    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
                      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at selO2
                    obtain ⟨rfl, rfl⟩ := selO2
                    obtain ⟨rfl, h_eq⟩ := dArmO2.literal_inv; have h_eq := h_eq.symm; subst h_eq
                    simp [nlSubsumeOr2]
                  | cons cellV2 _ _ =>
                    obtain ⟨bsO2, bodyO2, selO2, dArmO2⟩ :=
                      evalExpr_match_load_var_enum rfl cellV2 dMatchOr2
                    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
                      matchPattern_wildcard, SourceSemantics.matchListWith,
                      bind, Except.bind, pure, Except.pure] at selO2
                    obtain ⟨rfl, rfl⟩ := selO2
                    obtain ⟨_, _, _, _, dAddMax, dVarC1', dFnLt⟩ := evalExpr_call2_inv dArmO2
                    obtain ⟨_, _, _, dCallMax, dLit1, rfl⟩ := evalExpr_add_inv dAddMax
                    obtain ⟨_, _, dVarV1, dFnMax⟩ := evalExpr_call1_inv dCallMax
                    obtain ⟨⟨⟩, h_eq⟩ := dVarV1.var_inv'; have h_eq := h_eq.symm; subst h_eq
                    simp only [instanceName] at dFnMax
                    obtain ⟨heqMax, h_eq⟩ := nlvarsMaxOffset_refines repV1 dFnMax; have h_eq := h_eq.symm; subst h_eq
                    injection heqMax with hmax_eq; subst hmax_eq
                    obtain ⟨⟨⟩, h_eq⟩ := dLit1.literal_inv; have h_eq := h_eq.symm; subst h_eq
                    obtain ⟨⟨⟩, h_eq⟩ := dVarC1'.var_inv'; have h_eq := h_eq.symm; subst h_eq
                    simp only [instanceName] at dFnLt
                    obtain ⟨rfl, h_eq⟩ :=
                      u32LessThanFields_add_one_left_refines (nlvarsMaxOffset_lt repV1) hc1 dFnLt
                    have h_eq := h_eq.symm; subst h_eq
                    simp [nlSubsumeOr2]
                obtain ⟨rfl, h_eq⟩ := hor2_eval; have h_eq := h_eq.symm; subst h_eq
                simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatOr2
                subst hpatOr2
                obtain ⟨_, _, bsM, bodyM, dMul, selM, dArmM⟩ := dLetOr2.matchValue_inv
                obtain ⟨_, _, _, dVarOr1, dVarOr2, rfl⟩ := evalExpr_mul_inv dMul
                obtain ⟨⟨⟩, h_eq⟩ := dVarOr1.var_inv'; have h_eq := h_eq.symm; subst h_eq
                obtain ⟨⟨⟩, h_eq⟩ := dVarOr2.var_inv'; have h_eq := h_eq.symm; subst h_eq
                rw [field_mul_bool_ite] at selM
                rcases selectArm_bool_zero_wildcard selM with ⟨hboth, rfl, rfl⟩ | ⟨hboth, rfl, rfl⟩
                · obtain ⟨rfl, h_eq⟩ := dArmM.literal_inv; have h_eq := h_eq.symm; subst h_eq
                  simp [nlSubsumeC1n, hc1_0, hboth]
                · obtain ⟨⟨⟩, h_eq⟩ := dArmM.var_inv'; have h_eq := h_eq.symm; subst h_eq
                  simp [nlSubsumeC1n, hc1_0, hboth]
            obtain ⟨rfl, h_eq⟩ := hc1n_eval; have h_eq := h_eq.symm; subst h_eq
            simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatC1n
            subst hpatC1n
            obtain ⟨vv1n, h_v1n, bs7, dMatchV1, hpatV1n, dCallRec⟩ := dLetC1n.letValue_inv
            have hv1n_eval : RepNLVarList h_v1n (nlSubsumeV1n p1 p2 v1 v2) vv1n ∧ Heap.Extends h h_v1n := by
              obtain ⟨_, _, bsV, bodyV, dVarSame, selV, dArmV⟩ := dMatchV1.matchValue_inv
              obtain ⟨⟨⟩, rfl⟩ := dVarSame.var_inv'
              rcases selectArm_bool_one_zero selV with ⟨hsame, rfl, rfl⟩ | ⟨hnsame, rfl, rfl⟩
              · obtain ⟨⟨⟩, rfl⟩ := dArmV.var_inv'
                simp only [nlSubsumeV1n, hsame, ↓reduceIte]
                exact ⟨repV1, Heap.Extends.refl _⟩
              · cases repV2 with
                | nil cellV2 =>
                  obtain ⟨bsV2, bodyV2, selV2, dArmV2⟩ :=
                    evalExpr_match_load_var_enum rfl cellV2 dArmV
                  simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
                    SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at selV2
                  obtain ⟨rfl, rfl⟩ := selV2
                  obtain ⟨⟨⟩, rfl⟩ := dArmV2.var_inv'
                  simp only [nlSubsumeV1n, hnsame, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨repV1, Heap.Extends.refl _⟩
                | cons cellV2 repHv2 repTv2 =>
                  obtain ⟨bsV2, bodyV2, selV2, dArmV2⟩ :=
                    evalExpr_match_load_var_enum rfl cellV2 dArmV
                  simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
                    matchPattern_wildcard, SourceSemantics.matchListWith,
                    bind, Except.bind, pure, Except.pure] at selV2
                  obtain ⟨rfl, rfl⟩ := selV2
                  obtain ⟨_, _, _, _, dVarV1, dVarV2, dFnSubV⟩ := evalExpr_call2_inv dArmV2
                  obtain ⟨⟨⟩, rfl⟩ := dVarV1.var_inv'
                  obtain ⟨⟨⟩, rfl⟩ := dVarV2.var_inv'
                  simp only [instanceName] at dFnSubV
                  simp only [nlSubsumeV1n, hnsame, Bool.false_eq_true, ↓reduceIte]
                  exact nlvarsSubsume_refines repV1 (.cons cellV2 repHv2 repTv2) dFnSubV
            obtain ⟨repV1n, ext1⟩ := hv1n_eval
            simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatV1n
            subst hpatV1n
            obtain ⟨_, _, h1, h2, dStoreEntry, dVarSrest, dFnRec⟩ := evalExpr_call2_inv dCallRec
            obtain ⟨_, _, _, _, _, _, dVarP1'', dVarC1n, dVarV1n, rfl, rfl⟩ :=
              evalExpr_store_construct3_inv dStoreEntry
            obtain ⟨⟨⟩, rfl⟩ := dVarP1''.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarC1n.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarV1n.var_inv'
            obtain ⟨⟨⟩, rfl⟩ := dVarSrest.var_inv'
            simp only [instanceName, nlEntry_inst] at dFnRec
            have hc1n_lt : nlSubsumeC1n p1 p2 c1 c2 v1 v2 < 4294967296 := by
              dsimp only [nlSubsumeC1n]
              split_ifs <;> omega
            obtain ⟨repE', ext2⟩ :=
              RepNLEntry.alloc (e := ⟨p1, nlSubsumeC1n p1 p2 c1 c2 v1 v2, nlSubsumeV1n p1 p2 v1 v2⟩)
                hc1n_lt (repP1.mono' ext1) repV1n
            obtain ⟨repOut, ext3⟩ := ih repE' (repSrest.mono' (ext1.trans ext2)) dFnRec
            simp only [nlSubsumeEntry_cons, hsub, not_true_eq_false, ↓reduceIte]
            exact ⟨repOut, (ext1.trans ext2).trans ext3⟩

/-- **`EvalFn W` refinement for `KernelLevels::nl_subsumption_walk`.** -/
theorem nlSubsumptionWalk_refines {h h' : Heap F} {rem snapshot : List NLEntry}
    {ptrRem ptrSnap r : SourceValue F}
    (repRem : RepNLEntries h rem ptrRem) (repSnap : RepNLEntries h snapshot ptrSnap)
    (ev : EvalFn W "KernelLevels::nl_subsumption_walk" [ptrRem, ptrSnap] h r h') :
    RepNLEntries h' (nlSubsumptionWalk rem snapshot) r ∧ Heap.Extends h h' := by
  induction rem generalizing h h' ptrRem ptrSnap r with
  | nil =>
    cases repRem with
    | nil cellRem =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_subsumption_walk»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_subsumption_walk», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_subsumption_walk»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellRem ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨⟨⟩, rfl⟩ := dArm.var_inv'
      simp only [nlSubsumptionWalk, List.map_nil]
      exact ⟨.nil cellRem, Heap.Extends.refl _⟩
  | cons e rest ih =>
    cases repRem with
    | cons cellRem repE repRest =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_subsumption_walk»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_subsumption_walk», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_subsumption_walk»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellRem ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨_, _, h1, h2, dCallSub, dCallWalk, rfl, rfl⟩ := evalExpr_store_construct2_inv dArm
      obtain ⟨_, _, _, _, dVarE, dVarSnap1, dFnSub⟩ := evalExpr_call2_inv dCallSub
      obtain ⟨⟨⟩, rfl⟩ := dVarE.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarSnap1.var_inv'
      simp only [instanceName] at dFnSub
      obtain ⟨repE', ext1⟩ := nlSubsumeEntry_refines repE repSnap dFnSub
      obtain ⟨_, _, _, _, dVarRest, dVarSnap2, dFnWalk⟩ := evalExpr_call2_inv dCallWalk
      obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarSnap2.var_inv'
      simp only [instanceName] at dFnWalk
      obtain ⟨repRest', ext2⟩ := ih (repRest.mono' ext1) (repSnap.mono' ext1) dFnWalk
      obtain ⟨repCons, ext3⟩ := RepNLEntries.allocCons (repE'.mono' ext2) repRest'
      simp only [nlSubsumptionWalk, List.map_cons, nlEntryList_inst]
      exact ⟨repCons, (ext1.trans ext2).trans ext3⟩

/-- **`EvalFn W` refinement for `KernelLevels::level_normalize` (`norm`).** -/
theorem levelNormalize_refines {h h' : Heap F} {l : Ix.Kernel.Level}
    {ptrL r : SourceValue F}
    (repL : RepKLevel h l ptrL)
    (hd : levelDepth l < 4294967296)
    (ev : EvalFn W "KernelLevels::level_normalize" [ptrL] h r h') :
    RepNLEntries h' (levelNormalize l) r ∧ Heap.Extends h h' := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_normalize»)
    (by simp [IxVM.Checked.Fn.«KernelLevels::level_normalize», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«KernelLevels::level_normalize»] at ev
  obtain ⟨vSeed, h1, bs1, dSeed, hpatSeed, dLetSeed⟩ := ev.letValue_inv
  obtain ⟨_, _, _, _, dStoreSeedEntry, dStoreSeedNil, rfl, rfl⟩ :=
    evalExpr_store_construct2_inv dSeed
  obtain ⟨_, _, _, _, _, _, dStoreNilG, dLit0, dStoreNilV, rfl, rfl⟩ :=
    evalExpr_store_construct3_inv dStoreSeedEntry
  obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNilG
  obtain ⟨⟨⟩, rfl⟩ := dLit0.literal_inv
  obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNilV
  obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreSeedNil
  simp only [guardList_inst, nlVarList_inst, nlEntry_inst, nlEntryList_inst] at hpatSeed dLetSeed
  obtain ⟨repNilG, ext1⟩ := RepGuardList.allocNil h
  obtain ⟨repNilV, ext2⟩ := RepNLVarList.allocNil _
  have h0_cast : (0 : F) = ((0 : Nat) : F) := by simp
  have repSeedEntry_ext :=
    RepNLEntry.alloc (e := ⟨[], 0, []⟩) (by decide) (repNilG.mono' ext2) repNilV
  dsimp only at repSeedEntry_ext
  rw [← h0_cast] at repSeedEntry_ext
  obtain ⟨repSeedEntry, ext3⟩ := repSeedEntry_ext
  obtain ⟨repNilE, ext4⟩ := RepNLEntries.allocNil _
  obtain ⟨repSeed, ext5⟩ := RepNLEntries.allocCons (repSeedEntry.mono' ext4) repNilE
  have extSeed : Heap.Extends h _ := (((ext1.trans ext2).trans ext3).trans ext4).trans ext5
  simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatSeed
  subst hpatSeed
  obtain ⟨vRaw, h2, bs2, dCallRaw, hpatRaw, dCallWalk⟩ := dLetSeed.letValue_inv
  obtain ⟨_, _, _, _, _, _, _, _, dVarL, dStoreNilPath, dLit0', dVarSeed, dFnAux⟩ :=
    evalExpr_call4_inv dCallRaw
  obtain ⟨⟨⟩, rfl⟩ := dVarL.var_inv'
  obtain ⟨rfl, rfl⟩ := evalExpr_store_construct0_inv dStoreNilPath
  obtain ⟨⟨⟩, rfl⟩ := dLit0'.literal_inv
  obtain ⟨⟨⟩, rfl⟩ := dVarSeed.var_inv'
  simp only [guardList_inst] at dFnAux
  simp only [instanceName] at dFnAux
  rw [h0_cast] at dFnAux
  obtain ⟨repNilPath, ext6⟩ := RepGuardList.allocNil _
  have hd0 : levelDepth l + 0 < 4294967296 := by omega
  obtain ⟨repRaw, ext7⟩ :=
    normalizeAux_refines (k := 0) (repL.mono' (extSeed.trans ext6)) repNilPath (repSeed.mono' ext6) hd0 dFnAux
  simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatRaw
  subst hpatRaw
  obtain ⟨_, _, _, _, dVarRaw1, dVarRaw2, dFnWalk⟩ := evalExpr_call2_inv dCallWalk
  obtain ⟨⟨⟩, rfl⟩ := dVarRaw1.var_inv'
  obtain ⟨⟨⟩, rfl⟩ := dVarRaw2.var_inv'
  simp only [instanceName] at dFnWalk
  obtain ⟨repWalk, ext8⟩ := nlSubsumptionWalk_refines repRaw repRaw dFnWalk
  exact ⟨repWalk, ((extSeed.trans ext6).trans ext7).trans ext8⟩


/-! ### Subsection 6: Normalized Level Comparison (`nl_skip_empty`, `nl_eq`, `nlvars_any_offset_geq`, `nl_covers_const`, `nlvars_dominates`, `nl_covers_var`, `nl_le_vars`, `nl_le`, `level_leq`, `level_equal`) -/

/-- **`EvalFn W` refinement for `KernelLevels::nl_skip_empty`.** -/
theorem nlSkipEmpty_refines {h h' : Heap F} {l : List NLEntry}
    {ptrL r : SourceValue F}
    (repL : RepNLEntries h l ptrL)
    (ev : EvalFn W "KernelLevels::nl_skip_empty" [ptrL] h r h') :
    RepNLEntries h (nlSkipEmpty l) r ∧ h' = h := by
  induction l generalizing ptrL r h' with
  | nil =>
    cases repL with
    | nil cellL =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_skip_empty»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_skip_empty», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_skip_empty»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨⟨⟩, rfl⟩ := dArm.var_inv'
      dsimp only [nlSkipEmpty]
      exact ⟨.nil cellL, rfl⟩
  | cons e rest ih =>
    rcases e with ⟨p, c, v⟩
    cases repL with
    | cons cellL repE repRest =>
      cases repE with
      | mk hc cellE repP repV =>
        dsimp only at hc cellE repP repV
        have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_skip_empty»)
          (by simp [IxVM.Checked.Fn.«KernelLevels::nl_skip_empty», ControlLower.hasControl])
        simp only [IxVM.Checked.Fn.«KernelLevels::nl_skip_empty»] at ev
        obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL ev
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
        obtain ⟨rfl, rfl⟩ := sel
        obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellE dArm
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
          matchPattern_bind, SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
        obtain ⟨rfl, rfl⟩ := sel2
        obtain ⟨_, _, bs3, body3, dVarC, sel3, dArm3⟩ := dArm2.matchValue_inv
        obtain ⟨⟨⟩, rfl⟩ := dVarC.var_inv'
        rcases selectArm_nat_zero_wildcard (Nat.le_of_lt hc) sel3 with ⟨hc0, rfl, rfl⟩ | ⟨hc0, rfl, rfl⟩
        · subst hc0
          cases repV with
          | nil cellV =>
            obtain ⟨bs4, body4, sel4, dArm4⟩ := evalExpr_match_load_var_enum rfl cellV dArm3
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel4
            obtain ⟨rfl, rfl⟩ := sel4
            obtain ⟨_, _, dVarRest, dFnRec⟩ := evalExpr_call1_inv dArm4
            obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
            simp only [instanceName] at dFnRec
            simpa [nlSkipEmpty] using ih repRest dFnRec
          | cons cellV repHv repTv =>
            obtain ⟨bs4, body4, sel4, dArm4⟩ := evalExpr_match_load_var_enum rfl cellV dArm3
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
              matchPattern_wildcard, SourceSemantics.matchListWith,
              bind, Except.bind, pure, Except.pure] at sel4
            obtain ⟨rfl, rfl⟩ := sel4
            obtain ⟨⟨⟩, rfl⟩ := dArm4.var_inv'
            dsimp only [nlSkipEmpty]
            exact ⟨.cons cellL (.mk hc cellE repP (.cons cellV repHv repTv)) repRest, rfl⟩
        · obtain ⟨⟨⟩, rfl⟩ := dArm3.var_inv'
          have hskip : nlSkipEmpty (⟨p, c, v⟩ :: rest) = ⟨p, c, v⟩ :: rest := by
            rcases c with _ | c'
            · exact absurd rfl hc0
            · rfl
          rw [hskip]
          exact ⟨.cons cellL (.mk hc cellE repP repV) repRest, rfl⟩

/-- **`EvalFn W` refinement for `KernelLevels::nl_eq`.** -/
theorem nlEq_refines {h h' : Heap F} {a0 b0 : List NLEntry}
    {ptrA0 ptrB0 r : SourceValue F}
    (repA0 : RepNLEntries h a0 ptrA0) (repB0 : RepNLEntries h b0 ptrB0)
    (ev : EvalFn W "KernelLevels::nl_eq" [ptrA0, ptrB0] h r h') :
    r = .field (if nlEq a0 b0 then 1 else 0) ∧ h' = h := by
  suffices H : ∀ n, ∀ {a0 b0 : List NLEntry} {ptrA0 ptrB0 r : SourceValue F} {h h' : Heap F},
      a0.length + b0.length = n →
      RepNLEntries h a0 ptrA0 →
      RepNLEntries h b0 ptrB0 →
      EvalFn W "KernelLevels::nl_eq" [ptrA0, ptrB0] h r h' →
      r = .field (if nlEq a0 b0 then 1 else 0) ∧ h' = h by
    exact H _ rfl repA0 repB0 ev
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a0 b0 ptrA0 ptrB0 r h h' hn repA0 repB0 ev
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_eq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nl_eq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nl_eq»] at ev
    obtain ⟨ptrA, h1, bs1, dCallSkipA, hpatA, dLetA⟩ := ev.letValue_inv
    obtain ⟨_, _, dVarA0, dFnSkipA⟩ := evalExpr_call1_inv dCallSkipA
    obtain ⟨⟨⟩, rfl⟩ := dVarA0.var_inv'
    simp only [instanceName] at dFnSkipA
    obtain ⟨repA, rfl⟩ := nlSkipEmpty_refines repA0 dFnSkipA
    simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatA
    subst hpatA
    obtain ⟨ptrB, h2, bs2, dCallSkipB, hpatB, dMatchA⟩ := dLetA.letValue_inv
    obtain ⟨_, _, dVarB0, dFnSkipB⟩ := evalExpr_call1_inv dCallSkipB
    obtain ⟨⟨⟩, rfl⟩ := dVarB0.var_inv'
    simp only [instanceName] at dFnSkipB
    obtain ⟨repB, rfl⟩ := nlSkipEmpty_refines repB0 dFnSkipB
    simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatB
    subst hpatB
    rw [nlEq_unfold]
    cases ha : nlSkipEmpty a0 with
    | nil =>
      rw [ha] at repA
      cases repA with
      | nil cellA =>
        obtain ⟨bsA, bodyA, selA, dArmA⟩ := evalExpr_match_load_var_enum rfl cellA dMatchA
        simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
          SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at selA
        obtain ⟨rfl, rfl⟩ := selA
        cases hb : nlSkipEmpty b0 with
        | nil =>
          rw [hb] at repB
          cases repB with
          | nil cellB =>
            obtain ⟨bsB, bodyB, selB, dArmB⟩ := evalExpr_match_load_var_enum rfl cellB dArmA
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
              SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at selB
            obtain ⟨rfl, rfl⟩ := selB
            obtain ⟨rfl, rfl⟩ := dArmB.literal_inv
            simp
        | cons y br =>
          rw [hb] at repB
          cases repB with
          | cons cellB _ _ =>
            obtain ⟨bsB, bodyB, selB, dArmB⟩ := evalExpr_match_load_var_enum rfl cellB dArmA
            simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
              matchPattern_wildcard, SourceSemantics.matchListWith,
              bind, Except.bind, pure, Except.pure] at selB
            obtain ⟨rfl, rfl⟩ := selB
            obtain ⟨rfl, rfl⟩ := dArmB.literal_inv
            simp
    | cons x ar =>
      rcases x with ⟨xp, xc, xv⟩
      rw [ha] at repA
      cases repA with
      | cons cellA repX repAr =>
        cases repX with
        | mk hxc cellX repXp repXv =>
          dsimp only at hxc cellX repXp repXv
          obtain ⟨bsA, bodyA, selA, dArmA⟩ := evalExpr_match_load_var_enum rfl cellA dMatchA
          simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
            SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at selA
          obtain ⟨rfl, rfl⟩ := selA
          cases hb : nlSkipEmpty b0 with
          | nil =>
            rw [hb] at repB
            cases repB with
            | nil cellB =>
              obtain ⟨bsB, bodyB, selB, dArmB⟩ :=
                evalExpr_match_load_var_enum rfl cellB dArmA
              simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
                SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at selB
              obtain ⟨rfl, rfl⟩ := selB
              obtain ⟨rfl, rfl⟩ := dArmB.literal_inv
              simp
          | cons y br =>
            rcases y with ⟨yp, yc, yv⟩
            rw [hb] at repB
            cases repB with
            | cons cellB repY repBr =>
              cases repY with
              | mk hyc cellY repYp repYv =>
                dsimp only at hyc cellY repYp repYv
                obtain ⟨bsB, bodyB, selB, dArmB⟩ :=
                  evalExpr_match_load_var_enum rfl cellB dArmA
                simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
                  matchPattern_bind, SourceSemantics.matchListWith,
                  bind, Except.bind, pure, Except.pure] at selB
                obtain ⟨rfl, rfl⟩ := selB
                obtain ⟨bsX, bodyX, selX, dArmX⟩ :=
                  evalExpr_match_load_var_enum rfl cellX dArmB
                simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
                  matchPattern_bind, SourceSemantics.matchListWith,
                  bind, Except.bind, pure, Except.pure] at selX
                obtain ⟨rfl, rfl⟩ := selX
                obtain ⟨bsY, bodyY, selY, dArmY⟩ :=
                  evalExpr_match_load_var_enum rfl cellY dArmX
                simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
                  matchPattern_bind, SourceSemantics.matchListWith,
                  bind, Except.bind, pure, Except.pure] at selY
                obtain ⟨rfl, rfl⟩ := selY
                obtain ⟨_, _, bsCmp, bodyCmp, dCallCmp, selCmp, dArmCmp⟩ := dArmY.matchValue_inv
                obtain ⟨_, _, _, _, dVarXp, dVarYp, dFnCmp⟩ := evalExpr_call2_inv dCallCmp
                obtain ⟨⟨⟩, rfl⟩ := dVarXp.var_inv'
                obtain ⟨⟨⟩, rfl⟩ := dVarYp.var_inv'
                simp only [instanceName] at dFnCmp
                obtain ⟨rfl, rfl⟩ := glistCmp_refines repXp repYp dFnCmp
                rcases selectArm_glistCmp_zero_wildcard _ _ selCmp with
                  ⟨hcmp0, rfl, rfl⟩ | ⟨hcmp0, rfl, rfl⟩
                · obtain ⟨_, _, bsSub, bodySub, dSub, selSub, dArmSub⟩ := dArmCmp.matchValue_inv
                  obtain ⟨_, _, _, dVarXc, dVarYc, rfl⟩ := evalExpr_sub_inv dSub
                  obtain ⟨⟨⟩, rfl⟩ := dVarXc.var_inv'
                  obtain ⟨⟨⟩, rfl⟩ := dVarYc.var_inv'
                  rcases selectArm_sub_zero_wildcard hxc hyc selSub with
                    ⟨heqC, rfl, rfl⟩ | ⟨hneC, rfl, rfl⟩
                  · obtain ⟨_, _, bsV, bodyV, dCallV, selV, dArmV⟩ := dArmSub.matchValue_inv
                    obtain ⟨_, _, _, _, dVarXv, dVarYv, dFnV⟩ := evalExpr_call2_inv dCallV
                    obtain ⟨⟨⟩, rfl⟩ := dVarXv.var_inv'
                    obtain ⟨⟨⟩, rfl⟩ := dVarYv.var_inv'
                    simp only [instanceName] at dFnV
                    obtain ⟨rfl, rfl⟩ := nlvarsEq_refines repXv repYv dFnV
                    rcases selectArm_bool_one_zero selV with
                      ⟨heqV, rfl, rfl⟩ | ⟨hneV, rfl, rfl⟩
                    · obtain ⟨_, _, _, _, dVarAr, dVarBr, dFnRec⟩ := evalExpr_call2_inv dArmV
                      obtain ⟨⟨⟩, rfl⟩ := dVarAr.var_inv'
                      obtain ⟨⟨⟩, rfl⟩ := dVarBr.var_inv'
                      simp only [instanceName] at dFnRec
                      have h1 := nlSkipEmpty_cons_length_lt ha
                      have h2 := nlSkipEmpty_cons_length_lt hb
                      have hlen : ar.length + br.length < n := by omega
                      simpa [hcmp0, heqC, heqV] using ih _ hlen rfl repAr repBr dFnRec
                    · obtain ⟨rfl, rfl⟩ := dArmV.literal_inv
                      simp [hcmp0, heqC, hneV]
                  · obtain ⟨rfl, rfl⟩ := dArmSub.literal_inv
                    simp [hcmp0, hneC]
                · obtain ⟨rfl, rfl⟩ := dArmCmp.literal_inv
                  simp [hcmp0]

/-- **`EvalFn W` refinement for `KernelLevels::nlvars_any_offset_geq`.** -/
theorem nlvarsAnyOffsetGeq_refines {h h' : Heap F} {vars : List NLVar} {c : Nat}
    {ptrVars r : SourceValue F}
    (repVars : RepNLVarList h vars ptrVars) (hc : c < 4294967296)
    (ev : EvalFn W "KernelLevels::nlvars_any_offset_geq" [ptrVars, .field (c : F)] h r h') :
    r = .field (if nlvarsAnyOffsetGeq vars c then 1 else 0) ∧ h' = h := by
  induction repVars generalizing r h' with
  | nil cellVars =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_any_offset_geq»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_any_offset_geq», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_any_offset_geq»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [nlvarsAnyOffsetGeq]
  | cons cellVars repV repRest ih =>
    cases repV with
    | mk hvi hvo cellV =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_any_offset_geq»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_any_offset_geq», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_any_offset_geq»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellV dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        matchPattern_bind, SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dCallLt, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, dAdd, dVarC, dFnLt⟩ := evalExpr_call2_inv dCallLt
      obtain ⟨_, _, _, dVarVo, dLit1, rfl⟩ := evalExpr_add_inv dAdd
      obtain ⟨⟨⟩, rfl⟩ := dVarVo.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dLit1.literal_inv
      obtain ⟨⟨⟩, rfl⟩ := dVarC.var_inv'
      simp only [instanceName] at dFnLt
      obtain ⟨rfl, rfl⟩ := u32LessThanFields_add_one_left_refines hvo hc dFnLt
      rcases selectArm_ite_zero_one sel3 with ⟨hnlt, rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := dArm3.literal_inv
        simp [nlvarsAnyOffsetGeq, hnlt]
      · obtain ⟨_, _, _, _, dVarRest, dVarC2, dFnRec⟩ := evalExpr_call2_inv dArm3
        obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarC2.var_inv'
        simp only [instanceName] at dFnRec
        simpa [nlvarsAnyOffsetGeq, hlt] using ih dFnRec

def nlCoversConstHit (c2 c : Nat) (v2 : List NLVar) : Bool :=
  if !(c2 < c) then true else nlvarsAnyOffsetGeq v2 c

theorem nlCoversConst_cons (p2 : List Nat) (c2 : Nat) (v2 : List NLVar)
    (rest : List NLEntry) (p1 : List Nat) (c : Nat) :
    nlCoversConst (⟨p2, c2, v2⟩ :: rest) p1 c =
      if !(glistSubset p2 p1) then nlCoversConst rest p1 c
      else if nlCoversConstHit c2 c v2 then true else nlCoversConst rest p1 c := rfl

/-- **`EvalFn W` refinement for `KernelLevels::nl_covers_const`.** -/
theorem nlCoversConst_refines {h h' : Heap F} {l2 : List NLEntry}
    {p1 : List Nat} {c : Nat} {ptrL2 ptrP1 r : SourceValue F}
    (repL2 : RepNLEntries h l2 ptrL2) (repP1 : RepGuardList h p1 ptrP1)
    (hc : c < 4294967296)
    (ev : EvalFn W "KernelLevels::nl_covers_const" [ptrL2, ptrP1, .field (c : F)] h r h') :
    r = .field (if nlCoversConst l2 p1 c then 1 else 0) ∧ h' = h := by
  induction repL2 generalizing r h' with
  | nil cellL2 =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_covers_const»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nl_covers_const», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nl_covers_const»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL2 ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [nlCoversConst]
  | @cons e rest _ _ _ cellL2 repE repRest ih =>
    rcases e with ⟨p2, c2, v2⟩
    cases repE with
    | mk hc2 cellE repP2 repV2 =>
      dsimp only at hc2 cellE repP2 repV2
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_covers_const»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_covers_const», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_covers_const»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL2 ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellE dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dCallSub, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, dVarP2, dVarP1, dFnSub⟩ := evalExpr_call2_inv dCallSub
      obtain ⟨⟨⟩, h_eq⟩ := dVarP2.var_inv'; have h_eq := h_eq.symm; subst h_eq
      obtain ⟨⟨⟩, h_eq⟩ := dVarP1.var_inv'; have h_eq := h_eq.symm; subst h_eq
      simp only [instanceName] at dFnSub
      obtain ⟨rfl, h_eq⟩ := glistSubset_refines repP2 repP1 dFnSub; have h_eq := h_eq.symm; subst h_eq
      rcases selectArm_bool_zero_wildcard sel3 with ⟨hnsub, rfl, rfl⟩ | ⟨hsub, rfl, rfl⟩
      · obtain ⟨_, _, _, _, _, _, dVarRest, dVarP1', dVarC, dFnRec⟩ := evalExpr_call3_inv dArm3
        obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarP1'.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarC.var_inv'
        simp only [instanceName] at dFnRec
        simpa [nlCoversConst, hnsub] using ih dFnRec
      · obtain ⟨vhit, h_hit, bsHit, dMatchLt, hpatHit, dMatchHit⟩ := dArm3.letValue_inv
        have hhit_eval : vhit = .field (if nlCoversConstHit c2 c v2 then 1 else 0) ∧ h_hit = h := by
          obtain ⟨_, _, bsLt, bodyLt, dCallLt, selLt, dArmLt⟩ := dMatchLt.matchValue_inv
          obtain ⟨_, _, _, _, dVarC2, dVarC, dFnLt⟩ := evalExpr_call2_inv dCallLt
          obtain ⟨⟨⟩, h_eq⟩ := dVarC2.var_inv'; have h_eq := h_eq.symm; subst h_eq
          obtain ⟨⟨⟩, h_eq⟩ := dVarC.var_inv'; have h_eq := h_eq.symm; subst h_eq
          simp only [instanceName] at dFnLt
          obtain ⟨rfl, h_eq⟩ := u32LessThanFields_refines hc2 hc dFnLt; have h_eq := h_eq.symm; subst h_eq
          rcases selectArm_ite_zero_one selLt with ⟨hnlt, rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩
          · obtain ⟨rfl, h_eq⟩ := dArmLt.literal_inv; have h_eq := h_eq.symm; subst h_eq
            simp [nlCoversConstHit, hnlt]
          · obtain ⟨_, _, _, _, dVarV2, dVarC', dFnAny⟩ := evalExpr_call2_inv dArmLt
            obtain ⟨⟨⟩, h_eq⟩ := dVarV2.var_inv'; have h_eq := h_eq.symm; subst h_eq
            obtain ⟨⟨⟩, h_eq⟩ := dVarC'.var_inv'; have h_eq := h_eq.symm; subst h_eq
            simp only [instanceName] at dFnAny
            obtain ⟨rfl, h_eq⟩ := nlvarsAnyOffsetGeq_refines repV2 hc dFnAny; have h_eq := h_eq.symm; subst h_eq
            simp [nlCoversConstHit, hlt]
        obtain ⟨rfl, h_eq⟩ := hhit_eval; have h_eq := h_eq.symm; subst h_eq
        simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatHit
        subst hpatHit
        obtain ⟨_, _, bsH, bodyH, dVarHit, selH, dArmH⟩ := dMatchHit.matchValue_inv
        obtain ⟨⟨⟩, rfl⟩ := dVarHit.var_inv'
        rcases selectArm_bool_one_zero selH with ⟨hhit, rfl, rfl⟩ | ⟨hnhit, rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := dArmH.literal_inv
          simp [nlCoversConst_cons, hsub, hhit]
        · obtain ⟨_, _, _, _, _, _, dVarRest, dVarP1', dVarC, dFnRec⟩ := evalExpr_call3_inv dArmH
          obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarP1'.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarC.var_inv'
          simp only [instanceName] at dFnRec
          simpa [nlCoversConst_cons, hsub, hnhit] using ih dFnRec

/-- **`EvalFn W` refinement for `KernelLevels::nlvars_dominates`.** -/
theorem nlvarsDominates_refines {h h' : Heap F} {vars : List NLVar} {w off : Nat}
    {ptrVars r : SourceValue F}
    (repVars : RepNLVarList h vars ptrVars)
    (hw : w < 4294967296) (hoff : off < 4294967296)
    (ev : EvalFn W "KernelLevels::nlvars_dominates"
      [ptrVars, .field (w : F), .field (off : F)] h r h') :
    r = .field (if nlvarsDominates vars w off then 1 else 0) ∧ h' = h := by
  induction repVars generalizing r h' with
  | nil cellVars =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_dominates»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_dominates», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_dominates»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [nlvarsDominates]
  | cons cellVars repV repRest ih =>
    cases repV with
    | mk hvi hvo cellV =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nlvars_dominates»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nlvars_dominates», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nlvars_dominates»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellV dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dSub, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, dVarVi, dVarW, rfl⟩ := evalExpr_sub_inv dSub
      obtain ⟨⟨⟩, rfl⟩ := dVarVi.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarW.var_inv'
      rcases selectArm_sub_zero_wildcard hvi hw sel3 with ⟨heqW, rfl, rfl⟩ | ⟨hneW, rfl, rfl⟩
      · obtain ⟨_, _, bs4, body4, dCallLt, sel4, dArm4⟩ := dArm3.matchValue_inv
        obtain ⟨_, _, _, _, dVarVo, dVarOff, dFnLt⟩ := evalExpr_call2_inv dCallLt
        obtain ⟨⟨⟩, rfl⟩ := dVarVo.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarOff.var_inv'
        simp only [instanceName] at dFnLt
        obtain ⟨rfl, rfl⟩ := u32LessThanFields_refines hvo hoff dFnLt
        rcases selectArm_ite_zero_one sel4 with ⟨hnlt, rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := dArm4.literal_inv
          simp [nlvarsDominates, heqW, hnlt]
        · obtain ⟨_, _, _, _, _, _, dVarRest, dVarW2, dVarOff2, dFnRec⟩ :=
            evalExpr_call3_inv dArm4
          obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarW2.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarOff2.var_inv'
          simp only [instanceName] at dFnRec
          simpa [nlvarsDominates, heqW, hlt] using ih dFnRec
      · obtain ⟨_, _, _, _, _, _, dVarRest, dVarW2, dVarOff2, dFnRec⟩ :=
          evalExpr_call3_inv dArm3
        obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarW2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarOff2.var_inv'
        simp only [instanceName] at dFnRec
        simpa [nlvarsDominates, hneW] using ih dFnRec

/-- **`EvalFn W` refinement for `KernelLevels::nl_covers_var`.** -/
theorem nlCoversVar_refines {h h' : Heap F} {l2 : List NLEntry}
    {p1 : List Nat} {w off : Nat} {ptrL2 ptrP1 r : SourceValue F}
    (repL2 : RepNLEntries h l2 ptrL2) (repP1 : RepGuardList h p1 ptrP1)
    (hw : w < 4294967296) (hoff : off < 4294967296)
    (ev : EvalFn W "KernelLevels::nl_covers_var"
      [ptrL2, ptrP1, .field (w : F), .field (off : F)] h r h') :
    r = .field (if nlCoversVar l2 p1 w off then 1 else 0) ∧ h' = h := by
  induction repL2 generalizing r h' with
  | nil cellL2 =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_covers_var»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nl_covers_var», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nl_covers_var»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL2 ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [nlCoversVar]
  | cons cellL2 repE repRest ih =>
    cases repE with
    | mk hc2 cellE repP2 repV2 =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_covers_var»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_covers_var», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_covers_var»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL2 ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellE dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        matchPattern_bind, SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dCallSub, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, dVarP2, dVarP1, dFnSub⟩ := evalExpr_call2_inv dCallSub
      obtain ⟨⟨⟩, rfl⟩ := dVarP2.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarP1.var_inv'
      simp only [instanceName] at dFnSub
      obtain ⟨rfl, rfl⟩ := glistSubset_refines repP2 repP1 dFnSub
      rcases selectArm_bool_zero_wildcard sel3 with ⟨hnsub, rfl, rfl⟩ | ⟨hsub, rfl, rfl⟩
      · obtain ⟨_, _, _, _, _, _, _, _, dVarRest, dVarP1', dVarW, dVarOff, dFnRec⟩ :=
          evalExpr_call4_inv dArm3
        obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarP1'.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarW.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarOff.var_inv'
        simp only [instanceName] at dFnRec
        simpa [nlCoversVar, hnsub] using ih dFnRec
      · obtain ⟨_, _, bs4, body4, dCallDom, sel4, dArm4⟩ := dArm3.matchValue_inv
        obtain ⟨_, _, _, _, _, _, dVarV2, dVarW, dVarOff, dFnDom⟩ := evalExpr_call3_inv dCallDom
        obtain ⟨⟨⟩, rfl⟩ := dVarV2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarW.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarOff.var_inv'
        simp only [instanceName] at dFnDom
        obtain ⟨rfl, rfl⟩ := nlvarsDominates_refines repV2 hw hoff dFnDom
        rcases selectArm_bool_one_zero sel4 with ⟨hdom, rfl, rfl⟩ | ⟨hndom, rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := dArm4.literal_inv
          simp [nlCoversVar, hsub, hdom]
        · obtain ⟨_, _, _, _, _, _, _, _, dVarRest, dVarP1', dVarW2, dVarOff2, dFnRec⟩ :=
            evalExpr_call4_inv dArm4
          obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarP1'.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarW2.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarOff2.var_inv'
          simp only [instanceName] at dFnRec
          simpa [nlCoversVar, hsub, hndom] using ih dFnRec

/-- **`EvalFn W` refinement for `KernelLevels::nl_le_vars`.** -/
theorem nlLeVars_refines {h h' : Heap F} {vars : List NLVar}
    {l2 : List NLEntry} {p1 : List Nat}
    {ptrVars ptrL2 ptrP1 r : SourceValue F}
    (repVars : RepNLVarList h vars ptrVars)
    (repL2 : RepNLEntries h l2 ptrL2)
    (repP1 : RepGuardList h p1 ptrP1)
    (ev : EvalFn W "KernelLevels::nl_le_vars" [ptrVars, ptrL2, ptrP1] h r h') :
    r = .field (if nlLeVars vars l2 p1 then 1 else 0) ∧ h' = h := by
  induction repVars generalizing r h' with
  | nil cellVars =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_le_vars»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nl_le_vars», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nl_le_vars»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [nlLeVars]
  | cons cellVars repV repRest ih =>
    cases repV with
    | mk hvi hvo cellV =>
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_le_vars»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_le_vars», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_le_vars»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellVars ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellV dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨_, _, bs3, body3, dCallCov, sel3, dArm3⟩ := dArm2.matchValue_inv
      obtain ⟨_, _, _, _, _, _, _, _, dVarL2, dVarP1, dVarVi, dVarVo, dFnCov⟩ :=
        evalExpr_call4_inv dCallCov
      obtain ⟨⟨⟩, rfl⟩ := dVarL2.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarP1.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarVi.var_inv'
      obtain ⟨⟨⟩, rfl⟩ := dVarVo.var_inv'
      simp only [instanceName] at dFnCov
      obtain ⟨rfl, rfl⟩ := nlCoversVar_refines repL2 repP1 hvi hvo dFnCov
      rcases selectArm_bool_zero_one sel3 with ⟨hncov, rfl, rfl⟩ | ⟨hcov, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := dArm3.literal_inv
        simp [nlLeVars, hncov]
      · obtain ⟨_, _, _, _, _, _, dVarRest, dVarL2', dVarP1', dFnRec⟩ := evalExpr_call3_inv dArm3
        obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarL2'.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarP1'.var_inv'
        simp only [instanceName] at dFnRec
        simpa [nlLeVars, hcov] using ih dFnRec

/-- **`EvalFn W` refinement for `KernelLevels::nl_le`.** -/
theorem nlLe_refines {h h' : Heap F} {l1 l2 : List NLEntry}
    {ptrL1 ptrL2 r : SourceValue F}
    (repL1 : RepNLEntries h l1 ptrL1) (repL2 : RepNLEntries h l2 ptrL2)
    (ev : EvalFn W "KernelLevels::nl_le" [ptrL1, ptrL2] h r h') :
    r = .field (if nlLe l1 l2 then 1 else 0) ∧ h' = h := by
  induction repL1 generalizing r h' with
  | nil cellL1 =>
    have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_le»)
      (by simp [IxVM.Checked.Fn.«KernelLevels::nl_le», ControlLower.hasControl])
    simp only [IxVM.Checked.Fn.«KernelLevels::nl_le»] at ev
    obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL1 ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [nlLe]
  | @cons e rest _ _ _ cellL1 repE repRest ih =>
    rcases e with ⟨p1, c1, v1⟩
    cases repE with
    | mk hc1 cellE repP1 repV1 =>
      dsimp only at hc1 cellE repP1 repV1
      have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::nl_le»)
        (by simp [IxVM.Checked.Fn.«KernelLevels::nl_le», ControlLower.hasControl])
      simp only [IxVM.Checked.Fn.«KernelLevels::nl_le»] at ev
      obtain ⟨bs, body, sel, dArm⟩ := evalExpr_match_load_var_enum rfl cellL1 ev
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
      obtain ⟨rfl, rfl⟩ := sel
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellE dArm
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_bind,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨vcOk, h_cOk, bsCOk, dMatchC1, hpatCOk, dMatchCOk⟩ := dArm2.letValue_inv
      let cOk_val : Bool := if c1 = 0 then true else nlCoversConst l2 p1 c1
      have hcOk_eval : vcOk = .field (if cOk_val then 1 else 0) ∧ h_cOk = h := by
        obtain ⟨_, _, bsC1, bodyC1, dVarC1, selC1, dArmC1⟩ := dMatchC1.matchValue_inv
        obtain ⟨⟨⟩, rfl⟩ := dVarC1.var_inv'
        rcases selectArm_nat_zero_wildcard (Nat.le_of_lt hc1) selC1 with
          ⟨hc1_0, rfl, rfl⟩ | ⟨hc1_0, rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := dArmC1.literal_inv
          simp [cOk_val, hc1_0]
        · obtain ⟨_, _, _, _, _, _, dVarL2, dVarP1, dVarC1', dFnCov⟩ := evalExpr_call3_inv dArmC1
          obtain ⟨⟨⟩, rfl⟩ := dVarL2.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarP1.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarC1'.var_inv'
          simp only [instanceName] at dFnCov
          obtain ⟨rfl, rfl⟩ := nlCoversConst_refines repL2 repP1 hc1 dFnCov
          simp [cOk_val, hc1_0]
      obtain ⟨rfl, rfl⟩ := hcOk_eval
      simp only [matchPattern_bind, Option.some.injEq, Except.ok.injEq] at hpatCOk
      subst hpatCOk
      obtain ⟨_, _, bs3, body3, dVarCOk, sel3, dArm3⟩ := dMatchCOk.matchValue_inv
      obtain ⟨⟨⟩, rfl⟩ := dVarCOk.var_inv'
      rcases selectArm_bool_zero_one sel3 with ⟨hncOk, rfl, rfl⟩ | ⟨hcOk, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := dArm3.literal_inv
        simp [nlLe, cOk_val, hncOk]
      · obtain ⟨_, _, bs4, body4, dCallVars, sel4, dArm4⟩ := dArm3.matchValue_inv
        obtain ⟨_, _, _, _, _, _, dVarV1, dVarL2, dVarP1, dFnVars⟩ := evalExpr_call3_inv dCallVars
        obtain ⟨⟨⟩, rfl⟩ := dVarV1.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarL2.var_inv'
        obtain ⟨⟨⟩, rfl⟩ := dVarP1.var_inv'
        simp only [instanceName] at dFnVars
        obtain ⟨rfl, rfl⟩ := nlLeVars_refines repV1 repL2 repP1 dFnVars
        rcases selectArm_bool_zero_one sel4 with ⟨hnvars, rfl, rfl⟩ | ⟨hvars, rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := dArm4.literal_inv
          simp [nlLe, cOk_val, hcOk, hnvars]
        · obtain ⟨_, _, _, _, dVarRest, dVarL2', dFnRec⟩ := evalExpr_call2_inv dArm4
          obtain ⟨⟨⟩, rfl⟩ := dVarRest.var_inv'
          obtain ⟨⟨⟩, rfl⟩ := dVarL2'.var_inv'
          simp only [instanceName] at dFnRec
          simpa [nlLe, cOk_val, hcOk, hvars] using ih dFnRec

/-- **`EvalFn W` refinement for `KernelLevels::level_leq` (`is_geq_core` / `geqCore`).** -/
theorem levelLeq_refines {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB r : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (hda : levelDepth a < 4294967296) (hdb : levelDepth b < 4294967296)
    (ev : EvalFn W "KernelLevels::level_leq" [ptrA, ptrB] h r h') :
    r = .field (if levelLeq a b then 1 else 0) ∧ Heap.Extends h h' := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_leq»)
    (by simp [IxVM.Checked.Fn.«KernelLevels::level_leq», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«KernelLevels::level_leq»] at ev
  obtain ⟨_, _, bs1, body1, dCallEq, sel1, dArm1⟩ := ev.matchValue_inv
  obtain ⟨_, _, _, _, dVarA, dVarB, dFnEq⟩ := evalExpr_call2_inv dCallEq
  obtain ⟨⟨⟩, h_eq⟩ := dVarA.var_inv'; have h_eq := h_eq.symm; subst h_eq
  obtain ⟨⟨⟩, h_eq⟩ := dVarB.var_inv'; have h_eq := h_eq.symm; subst h_eq
  simp only [instanceName] at dFnEq
  obtain ⟨rfl, h_eq⟩ := levelEq_refines repA repB dFnEq; have h_eq := h_eq.symm; subst h_eq
  rcases selectArm_bool_one_zero sel1 with ⟨heq, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := dArm1.literal_inv
    simp [levelLeq, heq, Heap.Extends.refl]
  · have hNormLe : ∀ {locals : Environment F Nat}
        (ha : locals.find? (·.1 == "a") = some ("a", ptrA))
        (hb : locals.find? (·.1 == "b") = some ("b", ptrB))
        (dCall : SourceSemantics.EvalExpr W [] locals
          (.call "KernelLevels::nl_le" (some [])
            [(.call "KernelLevels::level_normalize" (some []) [(.var "a")]),
             (.call "KernelLevels::level_normalize" (some []) [(.var "b")])]) h r h'),
        r = .field (if nlLe (levelNormalize a) (levelNormalize b) then 1 else 0) ∧
        Heap.Extends h h' := by
      intro locals ha hb dCall
      obtain ⟨vNormA, vNormB, h1, h2, dNormA, dNormB, dFnLe⟩ := evalExpr_call2_inv dCall
      obtain ⟨_, _, dVarA', dFnNormA⟩ := evalExpr_call1_inv dNormA
      obtain ⟨hfa, rfl⟩ := dVarA'.var_inv'
      rw [ha] at hfa
      injection hfa with hp
      injection hp with _ hptrA
      subst hptrA
      simp only [instanceName] at dFnNormA
      obtain ⟨repNormA, ext1⟩ := levelNormalize_refines repA hda dFnNormA
      obtain ⟨_, _, dVarB', dFnNormB⟩ := evalExpr_call1_inv dNormB
      obtain ⟨hfb, rfl⟩ := dVarB'.var_inv'
      rw [hb] at hfb
      injection hfb with hp
      injection hp with _ hptrB
      subst hptrB
      simp only [instanceName] at dFnNormB
      obtain ⟨repNormB, ext2⟩ := levelNormalize_refines (repB.mono' ext1) hdb dFnNormB
      simp only [instanceName] at dFnLe
      obtain ⟨rfl, rfl⟩ := nlLe_refines (repNormA.mono' ext2) repNormB dFnLe
      exact ⟨rfl, ext1.trans ext2⟩
    cases repA with
    | zero cellA =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellA dArm1
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [levelLeq, hne, Heap.Extends.refl]
    | succ cellA _ =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellA dArm1
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨hr, hext⟩ := hNormLe rfl rfl dArm2
      exact ⟨by simpa [levelLeq, hne] using hr, hext⟩
    | max cellA _ _ =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellA dArm1
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨hr, hext⟩ := hNormLe rfl rfl dArm2
      exact ⟨by simpa [levelLeq, hne] using hr, hext⟩
    | imax cellA _ _ =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellA dArm1
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨hr, hext⟩ := hNormLe rfl rfl dArm2
      exact ⟨by simpa [levelLeq, hne] using hr, hext⟩
    | param _ cellA =>
      obtain ⟨bs2, body2, sel2, dArm2⟩ := evalExpr_match_load_var_enum rfl cellA dArm1
      simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct, matchPattern_wildcard,
        SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel2
      obtain ⟨rfl, rfl⟩ := sel2
      obtain ⟨hr, hext⟩ := hNormLe rfl rfl dArm2
      exact ⟨by simpa [levelLeq, hne] using hr, hext⟩

/-- **`EvalFn W` refinement for `KernelLevels::level_equal` (`is_eq_level`).** -/
theorem levelEqual_refines {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB r : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (hda : levelDepth a < 4294967296) (hdb : levelDepth b < 4294967296)
    (ev : EvalFn W "KernelLevels::level_equal" [ptrA, ptrB] h r h') :
    r = .field (if levelEqual a b then 1 else 0) ∧ Heap.Extends h h' := by
  have ev := ev.function_inv (IxVM.Checked.Lookup.«KernelLevels::level_equal»)
    (by simp [IxVM.Checked.Fn.«KernelLevels::level_equal», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«KernelLevels::level_equal»] at ev
  obtain ⟨_, _, bs1, body1, dCallEq, sel1, dArm1⟩ := ev.matchValue_inv
  obtain ⟨_, _, _, _, dVarA, dVarB, dFnEq⟩ := evalExpr_call2_inv dCallEq
  obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
  obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
  simp only [instanceName] at dFnEq
  obtain ⟨rfl, rfl⟩ := levelEq_refines repA repB dFnEq
  rcases selectArm_bool_one_zero sel1 with ⟨heq, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := dArm1.literal_inv
    simp [levelEqual, heq, Heap.Extends.refl]
  · obtain ⟨vNormA, vNormB, h1, h2, dNormA, dNormB, dFnNlEq⟩ := evalExpr_call2_inv dArm1
    obtain ⟨_, _, dVarA', dFnNormA⟩ := evalExpr_call1_inv dNormA
    obtain ⟨⟨⟩, rfl⟩ := dVarA'.var_inv'
    simp only [instanceName] at dFnNormA
    obtain ⟨repNormA, ext1⟩ := levelNormalize_refines repA hda dFnNormA
    obtain ⟨_, _, dVarB', dFnNormB⟩ := evalExpr_call1_inv dNormB
    obtain ⟨⟨⟩, rfl⟩ := dVarB'.var_inv'
    simp only [instanceName] at dFnNormB
    obtain ⟨repNormB, ext2⟩ := levelNormalize_refines (repB.mono' ext1) hdb dFnNormB
    simp only [instanceName] at dFnNlEq
    obtain ⟨rfl, rfl⟩ := nlEq_refines (repNormA.mono' ext2) repNormB dFnNlEq
    simp [levelEqual, hne, ext1.trans ext2]


/-! ### Subsection 7: End-to-End Semantic Soundness Corollaries -/

/-- **End-to-end semantic soundness of `KernelLevels::level_reduce`**:
any execution of `KernelLevels::level_reduce` on a heap representation of `l`
produces a heap representation of `levelReduce l` whose universe evaluation under
every parameter assignment `φ` is identical to `l`. -/
theorem levelReduce_eval_sound {h h' : Heap F} {l : Ix.Kernel.Level}
    {ptrL r : SourceValue F}
    (repL : RepKLevel h l ptrL)
    (hd : levelDepth l < 4294967296)
    (ev : EvalFn W "KernelLevels::level_reduce" [ptrL] h r h') :
    ∃ l', RepKLevel h' l' r ∧ Heap.Extends h h' ∧
      ∀ φ, Ix.Kernel.Level.eval φ l' = Ix.Kernel.Level.eval φ l := by
  obtain ⟨rep', ext⟩ := levelReduce_refines repL hd ev
  exact ⟨levelReduce l, rep', ext, fun φ => eval_levelReduce φ l⟩

/-- **End-to-end semantic soundness of `KernelLevels::level_inst_params` (`subst_level`)**:
any execution of `KernelLevels::level_inst_params` on heap representations of `l` and `params`
(with `ParamsLt params.length l`) produces a heap representation of `substLevel l params`,
which evaluates identically to `Ix.Kernel.Level.subst (List.range params.length) params l`
under every parameter assignment `φ`. -/
theorem levelInstParams_eval_sound {h h' : Heap F} {l : Ix.Kernel.Level}
    {params : List Ix.Kernel.Level} {ptrL ptrParams r : SourceValue F}
    (repL : RepKLevel h l ptrL) (repParams : RepKLevelList h params ptrParams)
    (_hlt : ParamsLt params.length l)
    (hd : levelDepth l + maxLevelDepth params < 4294967296)
    (ev : EvalFn W "KernelLevels::level_inst_params" [ptrL, ptrParams] h r h') :
    ∃ l', RepKLevel h' l' r ∧ Heap.Extends h h' ∧
      ∀ φ, Ix.Kernel.Level.eval φ l' =
        Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst (List.range params.length) params l) := by
  obtain ⟨_, rep', ext⟩ := levelInstParams_refines repL repParams hd ev
  exact ⟨substLevel l params, rep', ext, fun φ => eval_substLevel_eq_subst φ l params⟩

/-- **End-to-end semantic soundness of `KernelLevels::level_leq` (`is_geq_core` / `geqCore`)**:
if `EvalFn W "KernelLevels::level_leq" [ptrA, ptrB] h (.field 1) h'`, then for every
universe parameter valuation `φ`, `Ix.Kernel.Level.eval φ a ≤ Ix.Kernel.Level.eval φ b`. -/
theorem levelLeq_sound {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (hda : levelDepth a < 4294967296) (hdb : levelDepth b < 4294967296)
    (ev : EvalFn W "KernelLevels::level_leq" [ptrA, ptrB] h (.field 1) h')
    (φ : Ix.Kernel.LevelParam → Nat) :
    Ix.Kernel.Level.eval φ a ≤ Ix.Kernel.Level.eval φ b := by
  obtain ⟨hr, _⟩ := levelLeq_refines repA repB hda hdb ev
  have htrue : levelLeq a b = true := by
    cases h : levelLeq a b
    · simp [h] at hr
    · rfl
  exact levelLeq_eq_true_sound htrue φ

/-- **End-to-end semantic soundness of `KernelLevels::level_equal` (`is_eq_level`)**:
if `EvalFn W "KernelLevels::level_equal" [ptrA, ptrB] h (.field 1) h'`, then for every
universe parameter valuation `φ`, `Ix.Kernel.Level.eval φ a = Ix.Kernel.Level.eval φ b`. -/
theorem levelEqual_sound {h h' : Heap F} {a b : Ix.Kernel.Level}
    {ptrA ptrB : SourceValue F}
    (repA : RepKLevel h a ptrA) (repB : RepKLevel h b ptrB)
    (hda : levelDepth a < 4294967296) (hdb : levelDepth b < 4294967296)
    (ev : EvalFn W "KernelLevels::level_equal" [ptrA, ptrB] h (.field 1) h')
    (φ : Ix.Kernel.LevelParam → Nat) :
    Ix.Kernel.Level.eval φ a = Ix.Kernel.Level.eval φ b := by
  obtain ⟨hr, _⟩ := levelEqual_refines repA repB hda hdb ev
  have htrue : levelEqual a b = true := by
    cases h : levelEqual a b
    · simp [h] at hr
    · rfl
  exact levelEqual_eq_true_sound htrue φ

end IxVM.Refinement.KernelLevels
