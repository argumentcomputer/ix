import IxVMRefinement.Binding.FamilyReconSites
import IxVMRefinement.Binding.FamilyReconAnswers
import IxVMRefinement.Binding.FamilyFlatLocal
import IxVMRefinement.Assembly.GuardRawExact
import IxVMRefinement.FamilyAlias.CallRecs
import IxVMRefinement.Obs.KernelGuard0
import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelModeled3

/-! # `KernelModeled::block_elim` computes the block's elimination offset (`BlockElim`)

`block_elim` loads the block's first inductive type, peels its parameter and index binders with
the classifier's head normalization (`KernelCheck::get_result_sort_level` over
`KernelGuard::head`) down to its result sort, and answers whether that sort's level is never
zero. This module reads that computation on exact open terms (`TmOExact`):

* `GuardDefnAnswers`, `GuardIndAnswers`: the single-call store reads the computation makes
  (`Ingress::get_ci` at a definition, at an inductive type), against a definition lookup and an
  inductive-type lookup; `guardIndAnswers_of_indAnswers` derives the second, at the store's
  lookup `indTypeAt`, from the reconstruction's `IndAnswers`; `guardDefnAnswers_of_run` and
  `guardIndAnswers_of_run` give both for a bounded run with its store;
* `definition_value_spec` (`KernelGuard::definition_value`): the looked-up value at the levels;
* `guard_head_spec` (`KernelGuard::head`): the returned term is the `GuardHead` of the input;
* `get_result_sort_level_spec` (`KernelCheck::get_result_sort_level`): the returned level is the
  `ResultSort` of the input after the given number of binders;
* `block_elim_resultSort`: `block_elim` answers the never-zero test of the result sort of the
  first type's looked-up type;
* **`block_elim_blockElim`**: on a block record of the run's store, `block_elim` answers the
  offset `BlockElim` pins, together with what `block_elim_spec` reads. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core (W KExpr KLevel KKey bmeta kexprEnum kexprListEnum klevelListEnum addrTy
  ixAddr addrListEnum)
open IxVM.Refinement.Decl (TmExact)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Refinement.Binding.FamilyFlat (GuardHead ResultSort BlockElim indTypeAt defnValAt
  membersAt indcAddrs keyAddr)
open IxVM.Consistency (Bounded)
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The single-call store reads -/

/-- **`Ingress::get_ci` at a definition answers the lookup `defVal`**: a load among the calls
`root`, with its own calls, that returns a `Defn` gives the looked-up level count and value, the
value represented exactly. -/
def GuardDefnAnswers (κ : _root_.Address → KKey)
    (defVal : _root_.Address → Option (Nat × KExpr)) (root : List (Call F)) : Prop :=
  ∀ {xa p xnl xty xval xsf xh : SourceValue F} {h m : Heap F} {cs : List (Call F)}
    {a : Bytes.Address},
    Bytes.RepAddressRef addrTy h a xa →
    ObsFn W "Ingress::get_ci" [xa] h p m cs →
    (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ root → (∀ c ∈ cs, c ∈ root) →
    loadValue m p = .ok (.construct "KernelTypes::KConstantInfo" "Defn" [xnl, xty, xval, xsf, xh]) →
    ∃ (nl : Nat) (val : KExpr),
      defVal (ixAddr a) = some (nl, val) ∧ xnl = .field (nl : F) ∧ nl < 4294967296 ∧
      TmOExact κ m val xval

/-- **`Ingress::get_ci` at an inductive type answers the lookup `indTy`**: a load among the calls
`root`, with its own calls, that returns an `Induct` gives the looked-up level count, type,
parameter count and index count (the counts below `2^56`, as a load bounds them), the type
represented exactly. -/
def GuardIndAnswers (κ : _root_.Address → KKey)
    (indTy : _root_.Address → Option (Nat × KExpr × Nat × Nat)) (root : List (Call F)) : Prop :=
  ∀ {xa p xnl xty xnp xni xnc xrec xblk xidx : SourceValue F} {h m : Heap F}
    {cs : List (Call F)} {a : Bytes.Address},
    Bytes.RepAddressRef addrTy h a xa →
    ObsFn W "Ingress::get_ci" [xa] h p m cs →
    (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ root → (∀ c ∈ cs, c ∈ root) →
    loadValue m p = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [xnl, xty, xnp, xni, xnc, xrec, xblk, xidx]) →
    ∃ (nl np ni : Nat) (ty : KExpr),
      indTy (ixAddr a) = some (nl, ty, np, ni) ∧
      xnl = .field (nl : F) ∧ xnp = .field (np : F) ∧ xni = .field (ni : F) ∧
      np < 72057594037927936 ∧ ni < 72057594037927936 ∧ TmOExact κ m ty xty

/-- An inductive type's data in the reconstruction's reading is its type in the flattening's. -/
theorem indTypeAt_of_indDataAt {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {a : _root_.Address}
    {d : IndData} (h : indDataAt t E a = some (some d)) :
    indTypeAt t E a = some (d.nl, d.ty, d.np, d.ni) := by
  unfold indDataAt at h
  unfold indTypeAt
  split at h
  · exact absurd h (by simp)
  · rename_i c hc
    split at h
    · rename_i p hp
      split at h
      · exact absurd h (by simp)
      · rename_i cb hcb
        split at h
        · rename_i ms hms
          split at h
          · rename_i ind hind
            split at h
            · exact absurd h (by simp)
            · rename_i ty hty
              injection h with h
              injection h with h
              subst h
              simp only [hc, hp, hcb, hms, hind, hty]
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- **The reconstruction's inductive read gives the flattening's**: `IndAnswers` at the store's
readings answers `indTypeAt`. -/
theorem guardIndAnswers_of_indAnswers {κ : _root_.Address → KKey} {t : Ix.Kernel.RoleTable}
    {E : Ixon.Env} {root : List (Call F)} (hI : IndAnswers root κ (ReconView.ofStore t E)) :
    GuardIndAnswers κ (indTypeAt t E) root := by
  intro xa p xnl xty xnp xni xnc xrec xblk xidx h m cs a ra ev hself hsub ld
  obtain ⟨d, ba, hind, hnl, hnp, hni, -, -, rfl, hty, rfl, rfl, -⟩ :=
    (hI ra ev hself hsub ld).1 _ _ _ _ _ _ _ _ rfl
  exact ⟨d.nl, d.np, d.ni, d.ty, indTypeAt_of_indDataAt hind, rfl, rfl, rfl, hnp, hni, hty⟩

/-- **`GuardDefnAnswers` of a run**, at the store's definition lookup: among the calls of a
bounded run with its store, the readings at whose loaded addresses mention only their level
parameters, a load that returns a `Defn` gives the store's definition at the address, its value
represented exactly. -/
theorem guardDefnAnswers_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) (hlv : LoadedLevelsDefined t E₀ calls) :
    GuardDefnAnswers (IxVM.Consistency.keyOf t) (defnValAt t E₀) calls := by
  intro xa p xnl xty xval xsf xh h m cs a ha ev hself hsub hld
  obtain ⟨X, hX, hsome, hnone⟩ := defnAt_of_load ht hS hH hbd (hlv hself ha) ha ev hsub hld
  cases X with
  | none => exact absurd rfl (hnone rfl _)
  | some nv =>
    obtain ⟨n, v⟩ := nv
    obtain ⟨xty', xval', xsf', xh', hci, hn, htm⟩ := hsome n v rfl
    have hargs := (Value.construct.inj hci).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨e1, -, e3, -, -⟩ := hargs
    exact ⟨n, v, defnValAt_of_defnAt hX, e1, hn, e3 ▸ htm⟩

/-- **`GuardIndAnswers` of a run**, at the store's inductive lookup: among the calls of a bounded
run with its store, the readings at whose loaded addresses mention only their level parameters, a
load that returns an `Induct` gives the store's inductive at the address, its type represented
exactly. -/
theorem guardIndAnswers_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) (hlv : LoadedLevelsDefined t E₀ calls) :
    GuardIndAnswers (IxVM.Consistency.keyOf t) (indTypeAt t E₀) calls :=
  guardIndAnswers_of_indAnswers (indAnswers_of_run ht hS hH hbd hlv)

/-! ## `KernelGuard::definition_value` -/

private theorem klevel_length' {us : List KLevel} {l r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : RepKLevelList h us l) : r = .field (us.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KLevelNode" [])) (R := RepKLevel)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev)
    (by
      rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol,
        ← IxVM.Refinement.Levels.klevelList_names]
      exact hl)

private theorem nat_eq_of_field_eq {a b : Nat} (ha : a < 18446744069414584321)
    (hb : b < 18446744069414584321)
    (heq : (Value.field (a : F) : SourceValue F) = .field (b : F)) : a = b := by
  have hv := congrArg ZMod.val (Value.field.inj heq)
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv

/-- **`KernelGuard::definition_value(a, us)`** is the looked-up value of the definition at `a`,
its level parameters instantiated positionally at `us`, whose count is the definition's. -/
theorem definition_value_spec {κ : _root_.Address → KKey}
    {defVal : _root_.Address → Option (Nat × KExpr)} {root : List (Call F)}
    (hD : GuardDefnAnswers κ defVal root)
    {a : Bytes.Address} {us : List KLevel} {xa xus r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (bd : Bounded root) (hroot : ∀ c ∈ cs, c ∈ root)
    (ra : Bytes.RepAddressRef addrTy h a xa) (rus : RepKLevelList h us xus)
    (ev : ObsFn W "KernelGuard::definition_value" [xa, xus] h r h' cs) :
    ∃ (nl : Nat) (val : KExpr),
      defVal (ixAddr a) = some (nl, val) ∧ us.length = nl ∧
      TmOExact κ h' (val.instantiateLevelParams (List.range us.length) us) r := by
  match Obs.«KernelGuard::definition_value».obs ev with
  | .run (m2 := m2) (ev17 := load) (ld11 := ld) (ev81 := len) (heq97 := heq)
      (ev103 := inst) (hc120 := hc) .. =>
    obtain ⟨nl, val, hdv, rfl, hnl, hval⟩ := hD ra load (hroot _ (by rw [hc]; simp))
      (fun c hm => hroot c (by rw [hc]; simp [hm])) ld
    have rus2 : RepKLevelList m2 us xus := rus.mono load.heap_extends
    have hus_lt : us.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd
        (hroot (⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [xus], m2⟩ : Call F)
          (by rw [hc]; simp)) (by simp) rus2
    obtain ⟨rfl, rfl⟩ := klevel_length' len rus2
    have hlen : us.length = nl := nat_eq_of_field_eq (by omega) (by omega) heq
    obtain ⟨k, rv⟩ := hval
    obtain ⟨R, rraw⟩ := rv.raw
    exact ⟨nl, val, hdv, hlen,
      ⟨k, (IxVM.Refinement.Decl.expr_inst_raw_exact rraw rus2 inst).toTmExact⟩⟩

/-! ## `KernelGuard::head` -/

private theorem guard_head_go {κ : _root_.Address → KKey}
    {defVal : _root_.Address → Option (Nat × KExpr)}
    {ka : KKey → Option _root_.Address} (hka : ∀ a, ka (κ a) = some a)
    {root : List (Call F)} (hD : GuardDefnAnswers κ defVal root) (bd : Bounded root) :
    ∀ fuel : Nat, ∀ {E : KExpr} {p budget r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      cs.length ≤ fuel → (∀ c ∈ cs, c ∈ root) → TmOExact κ h E p →
      ObsFn W "KernelGuard::head" [p, budget] h r h' cs →
      ∃ E', GuardHead defVal ka E E' ∧ TmOExact κ h' E' r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro E p budget r h h' cs hlen hroot hE ev
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ root :=
      fun hs c hm => hroot c (hs c hm)
    have bsub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono bd (sub hs)
    match Obs.«KernelGuard::head».obs ev with
    | .n0 (heq40 := he) .. | .other_other (heq453 := he) .. =>
      exact (zero_ne_one (Value.field.inj he)).elim
    | .other_Srt (ld60 := ld) (he75 := hr) (he76 := hh) .. =>
      subst hr hh
      obtain ⟨l, rfl, -⟩ := hE.sort_of_load ld
      exact ⟨_, .sort l, hE⟩
    | .other_Forall (ld60 := ld) (he104 := hr) (he105 := hh) .. =>
      subst hr hh
      obtain ⟨T, B, ℓ, rfl, -, -, -⟩ := hE.forallE_of_load ld
      exact ⟨_, .forallE T B (bmeta ℓ), hE⟩
    | .other_Lam (ld60 := ld) (he133 := hr) (he134 := hh) .. =>
      subst hr hh
      obtain ⟨T, B, ℓ, rfl, -, -, -⟩ := hE.lam_of_load ld
      exact ⟨_, .lam T B (bmeta ℓ), hE⟩
    | .other_Const (cs156 := children) (cs170 := loads) (ld60 := ld)
        (ev172 := value) (ev158 := child) (hc204 := hc) .. =>
      obtain ⟨a, us, rfl, ra, rus⟩ := hE.const_of_load ld
      have hload : ∀ cl ∈ loads, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hlt : children.length < fuel := by
        rw [hc] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      obtain ⟨nl, val, hdv, hnl, hV⟩ := definition_value_spec hD bd (sub hload) ra rus value
      obtain ⟨E', hG, hE'⟩ := ih children.length hlt (Nat.le_refl _) (sub hsub) hV child
      exact ⟨E', .const (hka _) hdv hnl hG, hE'⟩
    | .other_App (cs236 := first) (cs300 := subs) (cs286 := children)
        (ld60 := ld) (ev238 := funHead) (ld232 := lam) (ev302 := inst)
        (ev288 := child) (hc341 := hc) .. =>
      obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
      have hfst : ∀ cl ∈ first, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hinst : ∀ cl ∈ subs, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hlt1 : first.length < fuel := by
        rw [hc] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      have hlt : children.length < fuel := by
        rw [hc] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      obtain ⟨F', hGf, hF'⟩ := ih first.length hlt1 (Nat.le_refl _) (sub hfst) hf funHead
      obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := hF'.lam_of_load lam
      have hi := expr_inst1_tmOExact (bsub hinst) hB (ha.mono funHead.heap_extends) inst
      obtain ⟨E', hG, hE'⟩ := ih children.length hlt (Nat.le_refl _) (sub hsub) hi child
      exact ⟨E', .app hGf hG, hE'⟩
    | .other_Let (cs382 := subs) (cs368 := children) (ld60 := ld)
        (ev384 := inst) (ev370 := child) (hc423 := hc) .. =>
      obtain ⟨T, V, B, rfl, -, hV, hB⟩ := hE.letE_of_load ld
      have hinst : ∀ cl ∈ subs, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hlt : children.length < fuel := by
        rw [hc] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      have hi := expr_inst1_tmOExact (bsub hinst) hB hV inst
      exact ih children.length hlt (Nat.le_refl _) (sub hsub) hi child

/-- **`KernelGuard::head(e, fuel)`** returns the `GuardHead` of the term: over the definition
lookup the store reads answer (`GuardDefnAnswers`) and a key-address map inverting the keying,
the returned term is the one the deterministic head trace reaches, represented exactly. A heap
`let` cell is read as its reduct, so the trace takes no `let` step. -/
theorem guard_head_spec {κ : _root_.Address → KKey}
    {defVal : _root_.Address → Option (Nat × KExpr)}
    {ka : KKey → Option _root_.Address} (hka : ∀ a, ka (κ a) = some a)
    {root : List (Call F)} (hD : GuardDefnAnswers κ defVal root) (bd : Bounded root)
    {E : KExpr} {p budget r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hroot : ∀ c ∈ cs, c ∈ root) (hE : TmOExact κ h E p)
    (ev : ObsFn W "KernelGuard::head" [p, budget] h r h' cs) :
    ∃ E', GuardHead defVal ka E E' ∧ TmOExact κ h' E' r :=
  guard_head_go hka hD bd cs.length (Nat.le_refl _) hroot hE ev

/-! ## `KernelCheck::get_result_sort_level` -/

/-- **`KernelCheck::get_result_sort_level(rc, ty, n, types)`** returns the `ResultSort` of the
type after `n` binders: the level of the sort the head trace reaches under them. -/
theorem get_result_sort_level_spec {κ : _root_.Address → KKey}
    {defVal : _root_.Address → Option (Nat × KExpr)}
    {ka : KKey → Option _root_.Address} (hka : ∀ a, ka (κ a) = some a)
    {root : List (Call F)} (hD : GuardDefnAnswers κ defVal root) (bd : Bounded root) :
    ∀ (n : Nat) {E : KExpr} {xrc p xtys r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      n < 18446744069414584321 → (∀ c ∈ cs, c ∈ root) → TmOExact κ h E p →
      ObsFn W "KernelCheck::get_result_sort_level" [xrc, p, .field (n : F), xtys] h r h' cs →
      ∃ l, ResultSort defVal ka n E l ∧ RepKLevel h' l r := by
  intro n
  induction n with
  | zero =>
    intro E xrc p xtys r h h' cs hn hroot hE ev
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (cs12 := cs1) (ev14 := hd) (ld55 := ld) (he69 := hr) (he70 := hh) (hc71 := hc) .. =>
      subst hr hh
      obtain ⟨E', hG, hE'⟩ := guard_head_spec hka hD bd
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hE hd
      obtain ⟨l, rfl, rl⟩ := hE'.sort_of_load ld
      exact ⟨l, .zero hG, rl⟩
    | .other (hne73 := hne) .. =>
      exact absurd (by simp) hne
  | succ n ih =>
    intro E xrc p xtys r h h' cs hn hroot hE ev
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (hv43 := hv) .. =>
      exact absurd hv (field_succ_ne_zero n (by omega))
    | .other (m2 := m2) (cs12 := cs1) (cs115 := cs2) (ev14 := hd) (ld88 := ld) (op149 := op)
        (hm160 := hm) (ev117 := rec) (hc180 := hc) .. =>
      subst hm
      obtain ⟨E', hG, hE'⟩ := guard_head_spec hka hD bd
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hE hd
      obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := hE'.forallE_of_load ld
      obtain rfl := evalBinOp_sub_succ n op
      obtain ⟨l, hRS, rl⟩ := ih (by omega)
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (hB.mono (Heap.Extends.snoc _ _)) rec
      exact ⟨l, .succ hG hRS, rl⟩

/-! ## `KernelModeled::block_elim` -/

/-- **`KernelModeled::block_elim` answers the never-zero test of the first type's result sort**:
over the lookups the store reads answer, the block's first type has a looked-up level count,
type, parameter and index counts; the type's `ResultSort` after its parameters and indices is a
level `lvl`; the returned level count is the type's and the returned offset is `1` exactly when
`lvl` is never zero. -/
theorem block_elim_resultSort {κ : _root_.Address → KKey}
    {defVal : _root_.Address → Option (Nat × KExpr)}
    {indTy : _root_.Address → Option (Nat × KExpr × Nat × Nat)}
    {ka : KKey → Option _root_.Address} (hka : ∀ a, ka (κ a) = some a)
    {root : List (Call F)} (hD : GuardDefnAnswers κ defVal root)
    (hI : GuardIndAnswers κ indTy root) (bd : Bounded root)
    {typeAs : List Bytes.Address} {rc xtA bnl uo : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hroot : ∀ c ∈ cs, c ∈ root)
    (htA : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs xtA)
    (ev : ObsFn W "KernelModeled::block_elim" [rc, xtA] h (.tuple [bnl, uo]) h' cs) :
    ∃ (a0 : Bytes.Address) (restAs : List Bytes.Address) (nl np ni : Nat) (ty : KExpr)
      (lvl : KLevel),
      typeAs = a0 :: restAs ∧
      indTy (ixAddr a0) = some (nl, ty, np, ni) ∧
      ResultSort defVal ka (np + ni) ty lvl ∧
      bnl = .field (nl : F) ∧
      uo = .field (((if lvl.isNeverZero then 1 else 0 : Nat) : Nat) : F) := by
  match Obs.«KernelModeled::block_elim».obs ev with
  | .run (m27 := m27) (m103 := m103) (v118 := v118) (ld11 := ld11) (ev43 := load) (ld37 := ld37) (op147 := op)
      (hm159 := hm) (ev115 := rsl) (ev176 := peers) (he213 := he) (ev232 := nz)
      (hc242 := hc) .. =>
    subst hm
    obtain ⟨a0, restAs, rfl, ha0, -⟩ := Lib.rep_cons_of_load htA ld11
    obtain ⟨nl, np, ni, ty, hind, rfl, rfl, rfl, hnp, hni, hty⟩ := hI ha0 load
      (hroot _ (by rw [hc]; simp)) (fun c hm => hroot c (by rw [hc]; simp [hm])) ld37
    have hv : v118 = .field ((np + ni : Nat) : F) := by
      simp only [evalBinOp] at op
      injection op with hv
      rw [← hv]
      congr 1
      push_cast
      rfl
    subst hv
    obtain ⟨lvl, hRS, rl⟩ := get_result_sort_level_spec hka hD bd (np + ni) (by omega)
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (hty.mono (Heap.Extends.snoc _ _)) rsl
    obtain ⟨hr, -⟩ := IxVM.Refinement.Levels.levelIsNotZero_step nz _ rfl lvl
      (rl.mono peers.heap_extends)
    injection he with htup
    injection htup with hbnl htup
    injection htup with huo _
    refine ⟨a0, restAs, nl, np, ni, ty, lvl, rfl, hind, hRS, hbnl, ?_⟩
    rw [huo, hr]
    split <;> simp

end IxVM.Refinement.Binding.FamilyRecon

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Binding.FamilyFlat (BlockElim indTypeAt defnValAt membersAt indcAddrs
  keyAddr)
open IxVM.Refinement.Binding.FamilyRecon (GuardDefnAnswers GuardIndAnswers IndAnswers ReconView
  block_elim_resultSort guardIndAnswers_of_indAnswers)

set_option linter.unusedVariables false

/-- The members `build_flat_originals` reads of a block whose first member is an inductive type
start with that type's constant address. -/
theorem membersAt_cons_of_block {E₀ : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hB : FamBlockRecord E₀ B cb ms) {ind0 : Ixon.Inductive}
    (hms0 : ms[0]? = some (.indc ind0)) :
    ∃ rest, membersAt E₀ B = some (iprjAddr B 0 :: rest) := by
  have hl : ms.toList[0]? = some (.indc ind0) := by rw [Array.getElem?_toList]; exact hms0
  unfold membersAt
  simp only [hB.record, hB.muts]
  cases hml : ms.toList with
  | nil => rw [hml] at hl; exact absurd hl (by simp)
  | cons m tl =>
    rw [hml] at hl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    exact ⟨indcAddrs B (0 + 1) tl, rfl⟩

/-- **`KernelModeled::block_elim` computes the block's elimination offset**: on a block record
of the run's store, under a keying whose keys name their addresses and the store reads the
classifier makes (an inductive type's load answers `indTypeAt`, a definition's `defnValAt`), the
returned offset is the `off` that `BlockElim` pins for the block, and the returned level count
is the first member's. -/
theorem block_elim_blockElim {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {κ : _root_.Address → KKey} (hka : ∀ a, keyAddr t (κ a) = some a)
    (hD : GuardDefnAnswers κ (defnValAt t E₀) calls)
    (hI : GuardIndAnswers κ (indTypeAt t E₀) calls)
    (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hms_u64 : ms.size < UInt64.size)
    {typeAs : List Bytes.Address} {rc xtA bnl uo : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hsub : CallSub cs calls)
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (htA : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs xtA)
    (ev : ObsFn Obs.W "KernelModeled::block_elim" [rc, xtA] h (.tuple [bnl, uo]) h' cs) :
    ∃ (a0 : Bytes.Address) (restAs : List Bytes.Address) (ind0 : Ixon.Inductive) (off : Nat),
      typeAs = a0 :: restAs ∧
      ixAddr a0 = iprjAddr B 0 ∧
      ms[0]? = some (.indc ind0) ∧
      ind0.lvls.toNat < 4294967296 ∧
      bnl = .field (ind0.lvls.toNat : F) ∧
      BlockElim t E₀ B off ∧
      uo = .field (off : F) := by
  obtain ⟨a0, restAs, ind0, htyAs, ha0, hms0, hlt, hbnl, -⟩ :=
    block_elim_spec hbd hS hB hms_u64 hsub htypes htA ev
  obtain ⟨a0', restAs', nl, np, ni, ty, lvl, htyAs', hind, hRS, -, huo⟩ :=
    block_elim_resultSort hka hD hI hbd hsub htA ev
  obtain ⟨rfl, -⟩ := List.cons.inj (htyAs.symm.trans htyAs')
  obtain ⟨rest, hmem⟩ := membersAt_cons_of_block hB hms0
  rw [ha0] at hind
  exact ⟨a0, restAs, ind0, _, htyAs, ha0, hms0, hlt, hbnl,
    ⟨iprjAddr B 0, rest, nl, np, ni, ty, lvl, hmem, hind, hRS, rfl⟩, huo⟩

/-- **`block_elim` computes `BlockElim`'s offset under the role table's keying**, the inductive
read taken in the reconstruction's form (`IndAnswers` at the store's readings). -/
theorem block_elim_blockElim_keyOf {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (hwf : t.wf = true) {E₀ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hD : GuardDefnAnswers (IxVM.Consistency.keyOf t) (defnValAt t E₀) calls)
    (hI : IndAnswers calls (IxVM.Consistency.keyOf t) (ReconView.ofStore t E₀))
    (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hms_u64 : ms.size < UInt64.size)
    {typeAs : List Bytes.Address} {rc xtA bnl uo : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hsub : CallSub cs calls)
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (htA : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs xtA)
    (ev : ObsFn Obs.W "KernelModeled::block_elim" [rc, xtA] h (.tuple [bnl, uo]) h' cs) :
    ∃ (a0 : Bytes.Address) (restAs : List Bytes.Address) (ind0 : Ixon.Inductive) (off : Nat),
      typeAs = a0 :: restAs ∧
      ixAddr a0 = iprjAddr B 0 ∧
      ms[0]? = some (.indc ind0) ∧
      ind0.lvls.toNat < 4294967296 ∧
      bnl = .field (ind0.lvls.toNat : F) ∧
      BlockElim t E₀ B off ∧
      uo = .field (off : F) :=
  block_elim_blockElim (IxVM.Refinement.Binding.FamilyFlat.keyAddr_keyOf hwf) hD
    (guardIndAnswers_of_indAnswers hI) hbd hS hB hms_u64 hsub htypes htA ev

end IxVM.Refinement.Typing.FamilyAlias
