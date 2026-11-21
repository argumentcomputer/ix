import IxVMRefinement.Guard.TraceFunction

/-! # The checked field loop with the raw walk it made

`check_fields_open`, `check_fields_all` and `check_prop_fields_sorts` (`Guard/Fields.lean`) read
the classifier's field loop at the term seam: each field's sort, with the evidence of one
classifier call on some pointers that represent the field's domain. That evidence does not say
that the pointers are those of the telescope the loop walks.

The twins here follow the same observations and keep the raw data: the loop walks the raw
telescope `R` its type pointer reads as, classifies each field domain of `R` in the raw context
of the binders before it, and the sort it checks for a field has the zero-set of that field's
signature.

* `check_fields_traces_open`, `check_fields_traces_all`: the loop after and before its
  parameters, giving `RawDomainTraces` / `RawFieldTraces` over the run's own declared-type and
  definition loads (`RawTypeAt`, `RawDeltaAt`).
* `check_prop_fields_traces`: the outer check of a structure-like proposition, giving sorts
  with their `FieldSortsJ` witness, the field traces of the raw telescope from the empty
  context, and the zero-set agreement of the two, field by field.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

/-- A context list read at no opened variable is the empty raw context. -/
theorem RawContext.ofTypes_zero (rawKey : _root_.Address → KKey) {κ : _root_.Address → KKey}
    {Γ : Nat → KExpr} {h : Heap F} {p : SourceValue F}
    (represented : TypesRep κ Γ h 0 p) : RawContext rawKey h [] p := by
  cases represented with
  | nil cell => exact .nil cell

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel (Expr Level)
open Ix.Kernel.Rules (Infer Red)
open IxVM.Refinement.KernelLevels (RepKLevel)
open IxVM.Refinement.Decl (RawExprRep RawContext RawTypeAt RawDeltaAt RawSignatureTrace
  RawDomainTraces RawFieldTraces)

set_option maxHeartbeats 1600000

/-- **The field loop after its parameters, with its raw walk**: one sort per field with its
typing, the signature traces of the raw telescope's next `n` domains, and the zero-set
agreement of each sort with its field's signature. -/
theorem check_fields_traces_open (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (hc : ScopedCoreFacts c) (rootCalls : List (Call F)) :
    ∀ (n : Nat) {d k : Nat} {Γ : Nat → KExpr} {E body R : KExpr} {fvs context : List KExpr}
      {rc p ctx r : SourceValue F} {nf : F} {h h' : Heap F} {cs : List (Call F)},
      nf.val = n → Ix.Kernel.openPisAtFvars n E d = some (fvs, body) →
      CoreGood c cs → (∀ cl ∈ cs, cl ∈ rootCalls) → c.rc h rc → c.types Γ h d ctx →
      Tm c.κ d Γ h 0 E p → RawContext rawKey h context ctx → RawExprRep rawKey h k R p →
      ObsFn W "KernelGuard::check_fields" [rc, p, .field 0, .field nf, ctx] h r h' cs →
      ∃ sorts signatures : List KLevel, sorts.length = n ∧
        (∀ i < n, ∃ fv type u, fvs[i]? = some fv ∧ sorts[i]? = some u ∧
          Infer c.env .full (d + i) fv.fvarTypeD type ∧ Red c.env (d + i) type (.sort u)) ∧
        RawDomainTraces (RawTypeAt c rawKey rootCalls) (RawDeltaAt c rawKey rootCalls)
          n context R signatures ∧
        ∀ i < n, ∀ φ : Ix.Kernel.LevelParam → Nat,
          Level.eval φ (sorts.getD i .zero) = 0 ↔ Level.eval φ (signatures.getD i .zero) = 0 := by
  intro n
  induction n with
  | zero =>
    intros
    exact ⟨[], [], rfl, fun i hi => (Nat.not_lt_zero i hi).elim, .done _ _,
      fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ n ih =>
    intro d k Γ E body R fvs context rc p ctx r nf h h' cs hn hop hg subset hrc hctx hE rawCtx
      physical ev
    have hn0 : nf ≠ 0 := by intro equal; rw [equal, ZMod.val_zero] at hn; omega
    obtain ⟨image, raw⟩ := physical
    match Obs.«KernelGuard::check_fields».obs ev with
    | .n0_n0 (hv28 := zero) .. => exact (hn0 (Value.field.inj zero)).elim
    | .other (hne183 := nonzero) .. => exact (nonzero rfl).elim
    | .n0_other (x_dom := dom) (x_body := tail) (m70 := checkedHeap)
        (cs80 := first) (cs110 := rest) (v116 := remaining) (m154 := nextHeap)
        (ld48 := loaded) (ev82 := checked) (op151 := subtracted) (hm162 := allocated)
        (ev112 := walked) (hc182 := events) .. =>
      obtain ⟨D, B, metadata, rfl, hD, hB, _⟩ := hE.forallE_of_load loaded
      obtain ⟨RD, RB, ED, EB, binderLevel, rfl, rfl, rawDom, rawBody, _⟩ :=
        raw.raw_forallE_view loaded
      simp only [Ix.Kernel.openPisAtFvars] at hop
      rcases opened : Ix.Kernel.openPisAtFvars n (B.instantiate1 (.fvar d D)) (d + 1) with
        _ | ⟨fvs', body'⟩ <;> rw [opened] at hop
      · exact nomatch hop
      · simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have firstInside : ∀ cl ∈ first, cl ∈ cs := by intro cl member; rw [events]; simp [member]
        have restInside : ∀ cl ∈ rest, cl ∈ cs := by intro cl member; rw [events]; simp [member]
        obtain ⟨type, u, actual, signature, predicted, before, after, inner, infer, reduce, _, _,
          visited, observed, level, members, zero⟩ :=
            checked_sort_zero_iff hc (hg.sub firstInside) hrc hctx hD checked
        have innerInside : ∀ cl ∈ inner, cl ∈ cs :=
          fun cl member => firstInside cl (members cl member)
        obtain ⟨rawSignature, rawLevel, trace⟩ := sort_signature_raw_trace rawKey hc
          (hg.sub innerInside) (fun cl member => subset cl (innerInside cl member))
          (types_mono visited hctx) (hD.mono visited) (rawCtx.mono visited)
          (⟨_, rawDom.mono visited⟩ : RawExprRep rawKey before k RD dom) observed
        have same := level.det rawLevel
        subst same
        have remainingValue : remaining = .field (nf - 1) := NatAux.sub_ok subtracted
        subst remainingValue allocated
        have decremented : (nf - 1).val = n := by have := NatAux.val_sub_one hn0; omega
        have extension := checked.heap_extends
        have cellExtension :=
          Heap.Extends.snoc checkedHeap (.construct kexprListEnum "Cons" [dom, ctx])
        have allExtension := extension.trans cellExtension
        have newTypes := ProjAux.types_extend (types_mono extension hctx) (hD.mono extension)
        have newBody := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)
          (hB.mono allExtension)
        obtain ⟨sorts, signatures, length, fields, traces, zeros⟩ :=
          ih decremented opened (hg.sub restInside)
            (fun cl member => subset cl (restInside cl member))
            (hrc.mono allExtension) newTypes newBody
            (.cons List.getElem?_concat_length ⟨k, ⟨_, rawDom.mono allExtension⟩⟩
              (rawCtx.mono allExtension))
            (⟨_, rawBody.mono allExtension⟩ : RawExprRep rawKey _ (k + 1) RB tail) walked
        refine ⟨u :: sorts, signature :: signatures, by simp [length], fun i hi => ?_,
          .step trace traces, fun i hi φ => ?_⟩
        · cases i with
          | zero =>
            exact ⟨.fvar d D, type, u, rfl, rfl,
              by simpa only [Nat.add_zero, Expr.fvarTypeD] using infer,
              by simpa only [Nat.add_zero] using reduce⟩
          | succ i =>
            obtain ⟨fv, type', v, hfv, hv, infer', reduce'⟩ := fields i (by omega)
            exact ⟨fv, type', v, hfv, hv,
              by simpa only [Nat.add_assoc, Nat.add_comm 1 i] using infer',
              by simpa only [Nat.add_assoc, Nat.add_comm 1 i] using reduce'⟩
        · cases i with
          | zero => simpa only [List.getD_cons_zero] using zero φ
          | succ i => simpa only [List.getD_cons_succ] using zeros i (by omega) φ

/-- **The field loop from its parameters on, with its raw walk**: the parameter arm only moves
each parameter domain into the typed and the raw context. -/
theorem check_fields_traces_all (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (hc : ScopedCoreFacts c) (rootCalls : List (Call F)) :
    ∀ (nP : Nat) {nF d k : Nat} {Γ : Nat → KExpr} {E residual body R : KExpr}
      {parameters fvs context : List KExpr} {rc p ctx r : SourceValue F} {np nf : F}
      {h h' : Heap F} {cs : List (Call F)},
      np.val = nP → nf.val = nF →
      Ix.Kernel.openPisAtFvars nP E d = some (parameters, residual) →
      Ix.Kernel.openPisAtFvars nF residual (d + nP) = some (fvs, body) →
      CoreGood c cs → (∀ cl ∈ cs, cl ∈ rootCalls) → c.rc h rc → c.types Γ h d ctx →
      Tm c.κ d Γ h 0 E p → RawContext rawKey h context ctx → RawExprRep rawKey h k R p →
      ObsFn W "KernelGuard::check_fields" [rc, p, .field np, .field nf, ctx] h r h' cs →
      ∃ sorts signatures : List KLevel, sorts.length = nF ∧
        (∀ i < nF, ∃ fv type u, fvs[i]? = some fv ∧ sorts[i]? = some u ∧
          Infer c.env .full (d + nP + i) fv.fvarTypeD type ∧
          Red c.env (d + nP + i) type (.sort u)) ∧
        RawFieldTraces (RawTypeAt c rawKey rootCalls) (RawDeltaAt c rawKey rootCalls)
          nP nF context R signatures ∧
        ∀ i < nF, ∀ φ : Ix.Kernel.LevelParam → Nat,
          Level.eval φ (sorts.getD i .zero) = 0 ↔ Level.eval φ (signatures.getD i .zero) = 0 := by
  intro nP
  induction nP with
  | zero =>
    intro nF d k Γ E residual body R parameters fvs context rc p ctx r np nf h h' cs
      hn hf opened openedFields hg subset hrc hctx hE rawCtx physical ev
    have npZero := (ZMod.val_eq_zero np).mp hn
    subst np
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at opened
    obtain ⟨rfl, rfl⟩ := opened
    obtain ⟨sorts, signatures, length, fields, traces, zeros⟩ :=
      check_fields_traces_open rawKey hc rootCalls nF hf
        (by simpa only [Nat.add_zero] using openedFields) hg subset hrc hctx hE rawCtx
        physical ev
    exact ⟨sorts, signatures, length, by simpa only [Nat.add_zero] using fields,
      .fields traces, zeros⟩
  | succ nP ih =>
    intro nF d k Γ E residual body R parameters fvs context rc p ctx r np nf h h' cs
      hn hf opened openedFields hg subset hrc hctx hE rawCtx physical ev
    have hn0 : np ≠ 0 := by intro equal; rw [equal, ZMod.val_zero] at hn; omega
    obtain ⟨image, raw⟩ := physical
    match Obs.«KernelGuard::check_fields».obs ev with
    | .n0_n0 (hv14 := zero) .. | .n0_other (hv14 := zero) .. =>
      exact (hn0 (Value.field.inj zero)).elim
    | .other (x_dom := dom) (x_body := tail) (cs221 := rest)
        (v226 := remaining) (m266 := nextHeap) (ld197 := loaded)
        (op256 := subtracted) (hm274 := allocated) (ev223 := walked) (hc294 := events) .. =>
      obtain ⟨D, B, metadata, rfl, hD, hB, _⟩ := hE.forallE_of_load loaded
      obtain ⟨RD, RB, ED, EB, binderLevel, rfl, rfl, rawDom, rawBody, _⟩ :=
        raw.raw_forallE_view loaded
      simp only [Ix.Kernel.openPisAtFvars] at opened
      rcases openedTail : Ix.Kernel.openPisAtFvars nP (B.instantiate1 (.fvar d D)) (d + 1) with
        _ | ⟨parameters', residual'⟩ <;> rw [openedTail] at opened
      · exact nomatch opened
      · simp only [Option.some.injEq, Prod.mk.injEq] at opened
        obtain ⟨rfl, rfl⟩ := opened
        have restInside : ∀ cl ∈ rest, cl ∈ cs := by intro cl member; rw [events]; simp [member]
        have remainingValue : remaining = .field (np - 1) := NatAux.sub_ok subtracted
        subst remainingValue allocated
        have decremented : (np - 1).val = nP := by have := NatAux.val_sub_one hn0; omega
        have extension := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [dom, ctx])
        have newTypes := ProjAux.types_extend hctx hD
        have newBody := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)
          (hB.mono extension)
        have nextFields :
            Ix.Kernel.openPisAtFvars nF residual' (d + 1 + nP) = some (fvs, body) := by
          simpa only [Nat.add_assoc, Nat.add_comm 1 nP] using openedFields
        obtain ⟨sorts, signatures, length, fields, traces, zeros⟩ :=
          ih decremented hf openedTail nextFields (hg.sub restInside)
            (fun cl member => subset cl (restInside cl member))
            (hrc.mono extension) newTypes newBody
            (.cons List.getElem?_concat_length ⟨k, ⟨_, rawDom.mono extension⟩⟩
              (rawCtx.mono extension))
            (⟨_, rawBody.mono extension⟩ : RawExprRep rawKey _ (k + 1) RB tail) walked
        refine ⟨sorts, signatures, length, fun i hi => ?_, .parameter traces, zeros⟩
        obtain ⟨fv, type, u, hfv, hu, infer, reduce⟩ := fields i hi
        exact ⟨fv, type, u, hfv, hu,
          by simpa only [Nat.add_assoc, Nat.add_comm 1 nP] using infer,
          by simpa only [Nat.add_assoc, Nat.add_comm 1 nP] using reduce⟩

/-- **The outer check of a structure-like proposition, with its raw walk**: sorts with their
`FieldSortsJ` witness, the field traces of the raw telescope the type pointer reads as, from
the empty context, and the zero-set agreement of each sort with its field's signature. The
traces' answers are loads of the run `rootCalls`. -/
theorem check_prop_fields_traces (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (hc : ScopedCoreFacts c) {rootCalls : List (Call F)}
    {nP nF k : Nat} {Γ : Nat → KExpr} {E residual body R : KExpr}
    {parameters fvs : List KExpr} {rc level p r : SourceValue F} {np nf : F}
    {h h' : Heap F} {cs : List (Call F)} {u : KLevel}
    (hp : np.val = nP) (hf : nf.val = nF)
    (opened : Ix.Kernel.openPisAtFvars nP E 0 = some (parameters, residual))
    (openedFields : Ix.Kernel.openPisAtFvars nF residual nP = some (fvs, body))
    (hg : CoreGood c cs) (subset : ∀ cl ∈ cs, cl ∈ rootCalls) (hrc : c.rc h rc)
    (hE : Tm c.κ 0 Γ h 0 E p) (physical : RawExprRep rawKey h k R p)
    (represented : RepKLevel h u level) (zero : ∀ φ, Level.eval φ u = 0)
    (ev : ObsFn W "KernelGuard::check_prop_fields"
      [rc, level, .field 1, .field 0, p, .field np, .field nf] h r h' cs) :
    ∃ sorts signatures : List KLevel,
      Ix.Kernel.Semantics.FieldSortsJ Ix.Kernel.Model.rulesJ c.env true false u
        nP fvs [] nF sorts ∧
      RawFieldTraces (RawTypeAt c rawKey rootCalls) (RawDeltaAt c rawKey rootCalls)
        nP nF [] R signatures ∧
      ∀ i < nF, ∀ φ : Ix.Kernel.LevelParam → Nat,
        Level.eval φ (sorts.getD i .zero) = 0 ↔ Level.eval φ (signatures.getD i .zero) = 0 := by
  obtain ⟨before, context, inner, extension, types, walked, included⟩ :=
    check_prop_fields_call (Γ := Γ) hc hg represented zero ev
  obtain ⟨sorts, signatures, length, fields, traces, zeros⟩ :=
    check_fields_traces_all rawKey hc rootCalls nP hp hf opened
      (by simpa only [Nat.zero_add] using openedFields) (hg.sub included)
      (fun cl member => subset cl (included cl member)) (hrc.mono extension) types
      (hE.mono extension) (Decl.RawContext.ofTypes_zero rawKey types.1)
      (physical.mono extension) walked
  simp only [Nat.zero_add] at fields
  refine ⟨sorts, signatures, ⟨length, fun i hi => ?_⟩, traces, zeros⟩
  obtain ⟨fv, type, v, hfv, hv, infer, reduce⟩ := fields i hi
  exact ⟨fv, type, v, hfv, hv, infer, reduce, (fun impossible => nomatch impossible),
    (fun _ impossible => nomatch impossible)⟩

end IxVM.Refinement.Core.GuardData
