import IxC.Resource.Proof.F4Rules
import IxC.Resource.Proof.F4Inputs

/-!
# Soundness of Unchecked Default-Mode Bodies (`F4Default`)

Proves the unchecked `DefaultBodyOk` / `DefaultTerm` soundness branch for `F4`:
1. **`DefValOk`, `DefEnvOk`, `DefStep`, `DefaultCallIH`**: value, environment, state-evolution,
   and outer-budget call invariants parameterized by allowed open regions `A : List Nat` so
   checked callers can call default bodies/closures with borrowed arguments seamlessly.
2. **Default-mode operational wrappers**: `natValue`, `strValue`, `conform`, `bindAt`,
   `bindParamsM`, `ret`, `select`, `formClosure`, `makePap`.
3. **Inner strong induction on linear budget `B`**: simultaneous soundness of `evalS`,
   `evalListS`, `evalCallArgsS`, `spineS`, `callWithS`, `applyAllS`, `applyAltS`,
   `clo_default_funOk`, and `pap_default_funOk`.
4. **Top-level exports**: `enterS_default_sound` and `staticS_default_sound` at `B_call ≤ B + 1`
   from `DefaultCallIH P ext B` + `DefaultBodyOk` + `LamsClosed`.
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## 1. Core Predicates & Structural Helpers -/

/-- Well-formedness of a runtime value in default-mode evaluation with open-region allowance `A`. -/
def DefValOk (P : Prog) (ext : ExternOracle) (B : Nat) (st : St) (A : List Nat) (v : Val) : Prop :=
  ValBaseOk st v ∧
  DeepOpenUnder st.heap st.regions A v ∧
  NoOnceCell st.heap v ∧
  CtorFieldsOk P ext B st v ∧
  FunOkAt P ext B st .unknown false (fun _ => False) v

/-- Shift a de Bruijn scope under one binder (`0` is newly in scope; `i + 1` inherits `Scope i`). -/
def shiftScope (Scope : Nat → Prop) : Nat → Prop
  | 0 => True
  | i + 1 => Scope i

/-- Every in-scope binding in `env` has mode `.many` and satisfies `DefValOk`. -/
def DefEnvOk (P : Prog) (ext : ExternOracle) (B : Nat) (st : St) (A : List Nat)
    (Scope : Nat → Prop) (env : List Bnd) : Prop :=
  ∀ (i : Nat) (b : Bnd), Scope i → env[i]? = some b →
    b.mode = .many ∧ DefValOk P ext B st A b.val

/-- Location `l` is reachable from some in-scope binding of `env` in heap `h`. -/
def EnvReach (Scope : Nat → Prop) (h : Heap) (env : List Bnd) (l : Nat) : Prop :=
  ∃ (i : Nat) (b : Bnd), Scope i ∧ env[i]? = some b ∧ Reach h b.val l

/-- Uniform state-evolution invariant for default-mode evaluation steps:
no old heap location `< st.heap.objs.size` is ever mutated, open regions are restored,
and `statics`/`strs` only grow with fresh/static/num locations. -/
def DefStep (P : Prog) (ext : ExternOracle) (B_in B_out : Nat) (st st' : St) : Prop :=
  B_out ≤ B_in ∧
  StOk P ext B_out st' ∧
  st.heap.objs.size ≤ st'.heap.objs.size ∧
  st.heap.nextCap ≤ st'.heap.nextCap ∧
  st'.regions = st.regions ∧
  st.nextRegion ≤ st'.nextRegion ∧
  ArrayExtends st.statics st'.statics ∧
  ArrayExtends st.strs st'.strs ∧
  PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
  PreservesOnceShell st.heap st'.heap ∧
  StaticStrFresh st st'

/-- Outer-budget call induction hypothesis for default-interface definitions (supplied by `F4.lean`). -/
def DefaultCallIH (P : Prog) (ext : ExternOracle) (B : Nat) : Prop :=
  (∀ B_call, B_call ≤ B → PapsFunOk P ext B_call) ∧
  (∀ (B_call fuel : Nat) (r : Ref) (params : Array Param) (res : ResultMode) (rc : Cls)
     (rs : Skel) (body : Term) (vs : List Val) (st : St) (A : List Nat),
     B_call ≤ B →
     P.find? r = some (.body params res rc rs body) →
     DefaultIface (.body params res rc rs body) →
     vs.length = params.size →
     StOk P ext B_call st →
     (∀ v ∈ vs, DefValOk P ext B_call st A v) →
     (∀ k, (enterS P ext fuel params res rc body vs).run (st, B_call) ≠ .error (.violation k)) ∧
     ∀ rv st' B',
       (enterS P ext fuel params res rc body vs).run (st, B_call) = .ok (rv, (st', B')) →
         DefStep P ext B_call B' st st' ∧
         ClsSafe st'.heap rc rv ∧
         DefValOk P ext B' st' A rv ∧
         ∀ l, Reach st'.heap rv l →
           st.heap.objs.size ≤ l ∨ (∃ v ∈ vs, Reach st.heap v l) ∨ StaticStrLoc st l ∨ NumLoc st'.heap l) ∧
  (∀ (B_call fuel : Nat) (r : Ref) (res : ResultMode) (rc : Cls) (rs : Skel) (body : Term) (st : St),
     B_call ≤ B →
     P.find? r = some (.body #[] res rc rs body) →
     DefaultIface (.body #[] res rc rs body) →
     StOk P ext B_call st →
     (∀ k, (staticS P ext fuel r body rc).run (st, B_call) ≠ .error (.violation k)) ∧
     ∀ rv st' B',
       (staticS P ext fuel r body rc).run (st, B_call) = .ok (rv, (st', B')) →
         DefStep P ext B_call B' st st' ∧
         ClsSafe st'.heap rc rv ∧
         DefValOk P ext B' st' [] rv ∧
         ∀ l, Reach st'.heap rv l →
           st.heap.objs.size ≤ l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l)

/-! ### Monotonicity, framing, and region helpers -/

theorem DefValOk.mono {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st : St} {A : List Nat} {v : Val}
    (hle : B₁ ≤ B₂) (hv : DefValOk P ext B₂ st A v) : DefValOk P ext B₁ st A v :=
  ⟨hv.1, hv.2.1, hv.2.2.1, CtorFieldsOk_mono hle hv.2.2.2.1, FunOkAt_mono hle hv.2.2.2.2⟩

theorem DefValOk.mono_regs {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A₁ A₂ : List Nat} {v : Val}
    (hsub : ∀ x ∈ A₁, x ∈ A₂) (hv : DefValOk P ext B st A₁ v) : DefValOk P ext B st A₂ v :=
  ⟨hv.1, hv.2.1.mono hsub, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩

theorem DefValOk.filter_lt {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A : List Nat} {v : Val} (hv : DefValOk P ext B st A v) :
    DefValOk P ext B st (A.filter (· < st.nextRegion)) v := by
  refine ⟨hv.1, ?_, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩
  intro w hw r hr hopen
  exact List.mem_filter.mpr ⟨hv.2.1 w hw r hr hopen, decide_eq_true (hv.1.2.2.2 w hw r hr)⟩

theorem DefValOk.preserve_old {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat}
    {st st' : St} {A : List Nat} {v : Val}
    (hB : B₂ ≤ B₁)
    (hp : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap)
    (hrf : RegsFuture st st')
    (hv : DefValOk P ext B₁ st A v) : DefValOk P ext B₂ st' A v := by
  have hpv : PreservesLocs (Reach st.heap v) st.heap st'.heap :=
    hp.mono fun _ hr => hv.1.1.reach_lt_size hr
  exact ⟨ValBaseOk_congr hpv hrf.1 hv.1,
    (DeepOpenUnder_congr hpv).mpr (DeepOpenUnder_of_regsFuture hv.1.2.2.2 hv.2.1 hrf),
    NoOnceCell_congr hv.1.1 hpv hv.2.2.1,
    CtorFieldsOk_mono hB (CtorFieldsOk_congr hv.1.1 hpv hrf hv.2.2.2.1),
    FunOkAt_mono hB (FunOkAt_preserve_locs hpv hrf hv.2.2.2.2)⟩

theorem DefValOk.openRegion {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A : List Nat} {v : Val} (hv : DefValOk P ext B st A v) :
    DefValOk P ext B { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions } A v :=
  hv.preserve_old (st := st) (Nat.le_refl _) (PreservesLocs.refl _ _) (RegsFuture.openRegion st)

theorem DefValOk.closeRegion {P : Prog} {ext : ExternOracle} {B : Nat} {st : St} (s : Nat)
    {A : List Nat} {v : Val} (hv : DefValOk P ext B st A v) :
    DefValOk P ext B { st with regions := st.regions.filter (· != s) } A v :=
  hv.preserve_old (st := st) (Nat.le_refl _) (PreservesLocs.refl _ _) (RegsFuture.closeRegion st s)

theorem DefValOk_imm (P : Prog) (ext : ExternOracle) (B : Nat) (st : St) (A : List Nat) (i : Imm) :
    DefValOk P ext B st A (.imm i) := by
  refine ⟨ValBaseOk_imm st i, DeepOpenUnder_imm st.heap st.regions A i,
    NoOnceCell_imm st.heap i, CtorFieldsOk_imm P ext B st i, ?_⟩
  cases i with
  | irr => exact FunOkAt_imm_irr P ext B st .unknown
  | con _ => exact FunOkAt_nonCallable_imm P ext B st .unknown (by intro h; cases h)
  | bits _ => exact FunOkAt_nonCallable_imm P ext B st .unknown (by intro h; cases h)

theorem DefValOk_of_clsSafe {P : Prog} {ext : ExternOracle} {B : Nat} {st : St} {A : List Nat}
    {c : Cls} {v : Val} (hne : c ≠ .val) (hbase : ValBaseOk st v) (hcls : ClsSafe st.heap c v) :
    DefValOk P ext B st A v :=
  ⟨hbase, ClsSafe_deepOpenUnder_nil hne hcls, ClsSafe_noOnceCell hne hcls,
   ClsSafe_ctorFieldsOk P ext B st hne hcls, ClsSafe_funOkAt P ext B st .unknown hne hcls⟩

theorem DefValOk_of_sameShape {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat}
    {st₁ st₂ : St} {A₁ A₂ : List Nat} {v₁ v₂ : Val}
    (hB : B₂ ≤ B₁)
    (hloc : SameLoc v₁ v₂)
    (hsh : SameShapeOn (Reach st₁.heap v₁) st₁.heap st₂.heap)
    (hrf : RegsFuture st₁ st₂)
    (hbase₂ : ValBaseOk st₂ v₂)
    (hopen₂ : DeepOpenUnder st₂.heap st₂.regions A₂ v₂)
    (hv₁ : DefValOk P ext B₁ st₁ A₁ v₁) :
    DefValOk P ext B₂ st₂ A₂ v₂ :=
  ⟨hbase₂, hopen₂,
   NoOnceCell_of_sameShape hv₁.1.1 hsh hloc hv₁.2.2.1,
   CtorFieldsOk_mono hB (CtorFieldsOk_of_sameShape hv₁.1.1 hsh hloc hrf hv₁.2.2.2.1),
   FunOkAt_mono hB (FunOkAt_preserve_sameShape hloc hsh hrf hv₁.2.2.2.2)⟩

theorem open_close_regions_eq_def {st : St} (hregs : RegsOk st) :
    (st.nextRegion :: st.regions).filter (· != st.nextRegion) = st.regions := by
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine List.filter_eq_self.mpr ?_
  intro r hr
  simp [Nat.ne_of_lt (hregs.2.2 r hr).2]

theorem openUnder_singleton_of_deepOpenUnder_lt {h : Heap} {s : Nat} {rs A : List Nat} {v : Val}
    (hdou : DeepOpenUnder h (s :: rs) A v)
    (hlt : ∀ x ∈ A, x < s) :
    OpenUnder [s] [] v ∧ confinedTo s v = false := by
  have hns : s ∉ v.taint := by
    intro hmem
    have hsA : s ∈ A := hdou.self s hmem List.mem_cons_self
    exact Nat.lt_irrefl s (hlt s hsA)
  refine ⟨fun r hr hrm => ?_, confinedTo_eq_false.mpr hns⟩
  simp only [List.mem_singleton] at hrm
  subst hrm
  exact False.elim (hns hr)

theorem DefEnvOk.mono {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st : St}
    {A : List Nat} {Scope : Nat → Prop} {env : List Bnd}
    (hle : B₁ ≤ B₂) (he : DefEnvOk P ext B₂ st A Scope env) :
    DefEnvOk P ext B₁ st A Scope env :=
  fun i b hs hb => let ⟨hm, hv⟩ := he i b hs hb; ⟨hm, hv.mono hle⟩

theorem DefEnvOk.mono_regs {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A₁ A₂ : List Nat} {Scope : Nat → Prop} {env : List Bnd}
    (hsub : ∀ x ∈ A₁, x ∈ A₂) (he : DefEnvOk P ext B st A₁ Scope env) :
    DefEnvOk P ext B st A₂ Scope env :=
  fun i b hs hb => let ⟨hm, hv⟩ := he i b hs hb; ⟨hm, hv.mono_regs hsub⟩

theorem DefEnvOk.mono_scope {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A : List Nat} {Scope₁ Scope₂ : Nat → Prop} {env : List Bnd}
    (hsub : ∀ i, Scope₁ i → Scope₂ i) (he : DefEnvOk P ext B st A Scope₂ env) :
    DefEnvOk P ext B st A Scope₁ env :=
  fun i b hs hb => he i b (hsub i hs) hb

theorem DefEnvOk.filter_lt {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A : List Nat} {Scope : Nat → Prop} {env : List Bnd}
    (he : DefEnvOk P ext B st A Scope env) :
    DefEnvOk P ext B st (A.filter (· < st.nextRegion)) Scope env :=
  fun i b hs hb => let ⟨hm, hv⟩ := he i b hs hb; ⟨hm, hv.filter_lt⟩

theorem DefEnvOk.preserve_old {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat}
    {st st' : St} {A : List Nat} {Scope : Nat → Prop} {env : List Bnd}
    (hB : B₂ ≤ B₁)
    (hp : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap)
    (hrf : RegsFuture st st')
    (he : DefEnvOk P ext B₁ st A Scope env) : DefEnvOk P ext B₂ st' A Scope env :=
  fun i b hs hb => let ⟨hm, hv⟩ := he i b hs hb; ⟨hm, hv.preserve_old hB hp hrf⟩

theorem DefEnvOk.cons {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A : List Nat} {Scope : Nat → Prop} {env : List Bnd} {b : Bnd}
    (hm : b.mode = .many) (hv : DefValOk P ext B st A b.val)
    (he : DefEnvOk P ext B st A Scope env) :
    DefEnvOk P ext B st A (shiftScope Scope) (b :: env) := by
  intro i bd hsc hget
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    exact ⟨hm, hv⟩
  | succ k =>
    simp only [List.getElem?_cons_succ] at hget
    exact he k bd hsc hget

theorem EnvReach_cons {Scope : Nat → Prop} {h : Heap} {b : Bnd} {env : List Bnd} {l : Nat}
    (hr : EnvReach (shiftScope Scope) h (b :: env) l) :
    Reach h b.val l ∨ EnvReach Scope h env l := by
  obtain ⟨i, bd, hsc, hget, hrl⟩ := hr
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    exact Or.inl hrl
  | succ k =>
    simp only [List.getElem?_cons_succ] at hget
    exact Or.inr ⟨k, bd, hsc, hget, hrl⟩

theorem EnvReach_of_preserves_old {P : Prog} {ext : ExternOracle} {B : Nat}
    {st st' : St} {A : List Nat} {Scope : Nat → Prop} {env : List Bnd} {l : Nat}
    (he : DefEnvOk P ext B st A Scope env)
    (hp : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap)
    (hr : EnvReach Scope st'.heap env l) :
    EnvReach Scope st.heap env l := by
  obtain ⟨i, b, hsc, hget, hrl⟩ := hr
  have hv := (he i b hsc hget).2
  have hpv : PreservesLocs (Reach st.heap b.val) st.heap st'.heap :=
    hp.mono fun _ h => hv.1.1.reach_lt_size h
  exact ⟨i, b, hsc, hget, (Reach_congr hpv l).mp hrl⟩

theorem DefStep.refl {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    (hst : StOk P ext B st) : DefStep P ext B B st st :=
  ⟨Nat.le_refl _, hst, Nat.le_refl _, Nat.le_refl _, rfl, Nat.le_refl _,
   ArrayExtends.refl _, ArrayExtends.refl _, PreservesLocs.refl _ _,
   PreservesOnceShell.refl _, StaticStrFresh.refl _⟩

theorem DefStep.regsFuture {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st₁ st₂ : St}
    (hs : DefStep P ext B₁ B₂ st₁ st₂) : RegsFuture st₁ st₂ :=
  RegsFuture.same_regions hs.2.2.2.2.2.1 hs.2.2.2.2.1

theorem DefStep.preserves_old {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st₁ st₂ : St}
    (hs : DefStep P ext B₁ B₂ st₁ st₂) :
    PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap :=
  hs.2.2.2.2.2.2.2.2.1

theorem DefStep.staticStrFresh {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st₁ st₂ : St}
    (hs : DefStep P ext B₁ B₂ st₁ st₂) : StaticStrFresh st₁ st₂ :=
  hs.2.2.2.2.2.2.2.2.2.2

theorem DefStep.dec_in {P : Prog} {ext : ExternOracle} {B₀ B₁ B₂ : Nat} {st₁ st₂ : St}
    (hle : B₁ ≤ B₀) (hs : DefStep P ext B₁ B₂ st₁ st₂) : DefStep P ext B₀ B₂ st₁ st₂ :=
  ⟨Nat.le_trans hs.1 hle, hs.2⟩

theorem DefStep.dec_out {P : Prog} {ext : ExternOracle} {B₁ B₂ B₃ : Nat} {st₁ st₂ : St}
    (hle : B₃ ≤ B₂) (hs : DefStep P ext B₁ B₂ st₁ st₂) : DefStep P ext B₁ B₃ st₁ st₂ :=
  ⟨Nat.le_trans hle hs.1, StOk_mono hle hs.2.1, hs.2.2⟩

theorem DefStep.trans {P : Prog} {ext : ExternOracle} {B₁ B₂ B₃ : Nat} {st₁ st₂ st₃ : St}
    (h12 : DefStep P ext B₁ B₂ st₁ st₂) (h23 : DefStep P ext B₂ B₃ st₂ st₃) :
    DefStep P ext B₁ B₃ st₁ st₃ :=
  ⟨Nat.le_trans h23.1 h12.1,
   h23.2.1,
   Nat.le_trans h12.2.2.1 h23.2.2.1,
   Nat.le_trans h12.2.2.2.1 h23.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   Nat.le_trans h12.2.2.2.2.2.1 h23.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.1.trans h23.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h23.2.2.2.2.2.2.2.1,
   PreservesLocs.trans h12.2.2.2.2.2.2.2.2.1
     (h23.2.2.2.2.2.2.2.2.1.mono fun _ hl => Nat.lt_of_lt_of_le hl h12.2.2.1),
   h12.2.2.2.2.2.2.2.2.2.1.trans h23.2.2.2.2.2.2.2.2.2.1,
   StaticStrFresh.trans h12.2.2.1
     (h23.2.2.2.2.2.2.2.2.1.mono fun _ hl => StOk_staticStrLoc_lt h12.2.1 hl)
     h12.2.2.2.2.2.2.2.2.2.2 h23.2.2.2.2.2.2.2.2.2.2⟩

theorem DefStep.lift_val {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st₁ st₂ : St}
    {A : List Nat} {v : Val}
    (hs : DefStep P ext B₁ B₂ st₁ st₂) (hv : DefValOk P ext B₁ st₁ A v) :
    DefValOk P ext B₂ st₂ A v :=
  hv.preserve_old hs.1 hs.2.2.2.2.2.2.2.2.1 hs.regsFuture

theorem DefStep.lift_env {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st₁ st₂ : St}
    {A : List Nat} {Scope : Nat → Prop} {env : List Bnd}
    (hs : DefStep P ext B₁ B₂ st₁ st₂) (he : DefEnvOk P ext B₁ st₁ A Scope env) :
    DefEnvOk P ext B₂ st₂ A Scope env :=
  he.preserve_old hs.1 hs.2.2.2.2.2.2.2.2.1 hs.regsFuture

theorem DefStep.lift_numLoc {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st₁ st₂ : St} {l : Nat}
    (hs : DefStep P ext B₁ B₂ st₁ st₂) (hnum : NumLoc st₁.heap l) : NumLoc st₂.heap l := by
  obtain ⟨o, n, ho, hcell⟩ := hnum
  have hlt : l < st₁.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
  exact ⟨o, n, (hs.2.2.2.2.2.2.2.2.1 l hlt).trans ho, hcell⟩

theorem DefStep.of_preserves_old {P : Prog} {ext : ExternOracle} {B : Nat} {st st' : St}
    (hst : StOk P ext B st) (hst' : StOk P ext B st')
    (hsz : st.heap.objs.size ≤ st'.heap.objs.size)
    (hcap : st.heap.nextCap ≤ st'.heap.nextCap)
    (hreg : st'.regions = st.regions)
    (hnr : st.nextRegion ≤ st'.nextRegion)
    (hstat : st'.statics = st.statics)
    (hstr : st'.strs = st.strs)
    (hpres : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap) :
    DefStep P ext B B st st' :=
  ⟨Nat.le_refl _, hst', hsz, hcap, hreg, hnr,
   hstat ▸ ArrayExtends.refl _, hstr ▸ ArrayExtends.refl _, hpres,
   PreservesOnceShell.of_preservesLocs (hpres.mono fun _ ⟨_, _, _, ho, _⟩ =>
     (Array.getElem?_eq_some_iff.mp ho).1),
   StaticStrFresh_of_preserves_outside (S := fun _ => False) hst hstat hstr
     (hpres.mono fun _ h => h.1) (fun _ _ h => h)⟩

/-! ### `FreeVarIn`, `collect`, and `DefaultTerm` structural helpers -/

theorem FreeVarIn_succ {d : Nat} {t : Term} {x : Nat}
    (h : FreeVarIn d t (x + 1)) : FreeVarIn (d + 1) t x := by
  generalize hy : x + 1 = y at h
  induction h generalizing x with
  | @var d' i' c hle =>
    have hle' : d' + 1 ≤ i' := by omega
    have heq : i' - (d' + 1) = x := by omega
    rw [← heq]
    exact .var hle'
  | appL _ ih => exact .appL (ih hy)
  | appR _ ih => exact .appR (ih hy)
  | lam _ ih => exact .lam (ih hy)
  | letV _ ih => exact .letV (ih hy)
  | letB _ ih => exact .letB (ih hy)
  | proj _ ih => exact .proj (ih hy)
  | caseMj _ ih => exact .caseMj (ih hy)
  | caseAlt ha _ ih => exact .caseAlt ha (ih hy)
  | caseEx he _ ih => exact .caseEx he (ih hy)

theorem shiftScope_of_freeVarIn {Scope : Nat → Prop} {b : Term}
    (h : ∀ x, FreeVarIn 1 b x → Scope x) :
    ∀ x, FreeVarIn 0 b x → shiftScope Scope x := by
  intro x hx
  cases x with
  | zero => trivial
  | succ k => exact h k (FreeVarIn_succ hx)

theorem collect_defaultTerm {P : Prog} :
    ∀ (t : Term) (acc : List Term),
      DefaultTerm P t → (∀ a ∈ acc, DefaultTerm P a) →
      DefaultTerm P (collect t acc).1 ∧ ∀ a ∈ (collect t acc).2, DefaultTerm P a
  | .app f a c, acc, hdef, hacc => by
    cases hdef with
    | app hdf hda =>
      simp only [collect]
      exact collect_defaultTerm f (a :: acc) hdf (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hda
        · exact hacc x hx')
  | .irr, acc, hdef, hacc | .var .., acc, hdef, hacc | .const .., acc, hdef, hacc
  | .natLit _, acc, hdef, hacc | .strLit _, acc, hdef, hacc | .lam .., acc, hdef, hacc
  | .letE .., acc, hdef, hacc | .proj .., acc, hdef, hacc | .case .., acc, hdef, hacc => by
    exact ⟨hdef, hacc⟩

theorem collect_lamsClosed :
    ∀ (t : Term) (acc : List Term),
      LamsClosed t → (∀ a ∈ acc, LamsClosed a) →
      LamsClosed (collect t acc).1 ∧ ∀ a ∈ (collect t acc).2, LamsClosed a
  | .app f a c, acc, hlc, hacc => by
    cases hlc with
    | app hlcf hlca =>
      simp only [collect]
      exact collect_lamsClosed f (a :: acc) hlcf (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hlca
        · exact hacc x hx')
  | .irr, acc, hlc, hacc | .var .., acc, hlc, hacc | .const .., acc, hlc, hacc
  | .natLit _, acc, hlc, hacc | .strLit _, acc, hlc, hacc | .lam .., acc, hlc, hacc
  | .letE .., acc, hlc, hacc | .proj .., acc, hlc, hacc | .case .., acc, hlc, hacc => by
    exact ⟨hlc, hacc⟩

theorem collect_freeVarIn :
    ∀ (t : Term) (acc : List Term) (d x : Nat),
      (FreeVarIn d (collect t acc).1 x → FreeVarIn d t x) ∧
      (∀ a ∈ (collect t acc).2, FreeVarIn d a x → (∃ a' ∈ acc, FreeVarIn d a' x) ∨ FreeVarIn d t x)
  | .app f a c, acc, d, x => by
    simp only [collect]
    have ⟨ih1, ih2⟩ := collect_freeVarIn f (a :: acc) d x
    refine ⟨fun h => .appL (ih1 h), fun b hb hfx => ?_⟩
    rcases ih2 b hb hfx with ⟨a', ha', hfa'⟩ | hff
    · rcases List.mem_cons.mp ha' with rfl | ha''
      · exact Or.inr (.appR hfa')
      · exact Or.inl ⟨a', ha'', hfa'⟩
    · exact Or.inr (.appL hff)
  | .irr, acc, d, x | .var .., acc, d, x | .const .., acc, d, x
  | .natLit _, acc, d, x | .strLit _, acc, d, x | .lam .., acc, d, x
  | .letE .., acc, d, x | .proj .., acc, d, x | .case .., acc, d, x => by
    exact ⟨id, fun a ha hfa => Or.inl ⟨a, ha, hfa⟩⟩

/-! ## 2. Default-Mode Operational Wrappers -/

theorem natValue_default_sound {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A : List Nat} (k : Nat) (hst : StOk P ext B st) :
    ∃ v st', (natValue k).run st = .ok (v, st') ∧
      DefStep P ext B B st st' ∧
      DefValOk P ext B st' A v ∧
      ∀ l, Reach st'.heap v l → st.heap.objs.size ≤ l := by
  obtain ⟨v, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, hc', hdl, _, hacyc, _, hnum⟩ :=
    mkNum_ok natClass k st hst.1
  obtain ⟨loc, cap, o, rfl, ho, hcell, hocap, hge⟩ := hnum (by decide)
  have hst' : StOk P ext B st' :=
    StOk_of_preserves_old hst hc' hr (hnr ▸ Nat.le_refl _) hstat hstr hpres
  have hstep : DefStep P ext B B st st' :=
    DefStep.of_preserves_old hst hst' hsz hcap hr (hnr ▸ Nat.le_refl _) hstat hstr hpres
  have hcls : ClsSafe st'.heap .leaf (.ref loc cap []) :=
    ClsSafe.of_clsOk ⟨loc, cap, o, k, rfl, ho, hcell, hocap⟩
  have hbase : ValBaseOk st' (.ref loc cap []) :=
    ValBaseOk_of_deepLive hdl hacyc (DeepTaintsBounded_num ho hcell)
  refine ⟨.ref loc cap [], st', hrun, hstep,
    DefValOk_of_clsSafe (by decide) hbase hcls, fun l hl => ?_⟩
  rw [Reach_num_iff ho hcell] at hl
  subst hl
  exact hge

theorem strValue_default_sound {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A : List Nat} (s : String) (hst : StOk P ext B st) :
    ∃ v st', (strValue s).run st = .ok (v, st') ∧
      DefStep P ext B B st st' ∧
      DefValOk P ext B st' A v ∧
      ∀ l, Reach st'.heap v l → st.heap.objs.size ≤ l ∨ StaticStrLoc st l := by
  obtain ⟨v, st', hrun, hr, hnr, hstat, hstrExt, hsz, hcap, hpres, honceSh, hssf, hst',
    hbase, hopen, hcf, hno, hfun, hreach⟩ := strValue_sound (P := P) (ext := ext) (B := B) s hst
  refine ⟨v, st', hrun,
    ⟨Nat.le_refl _, hst', hsz, hcap, hr, hnr ▸ Nat.le_refl _, hstat ▸ ArrayExtends.refl _,
     hstrExt, hpres, honceSh, hssf⟩,
    ⟨hbase, hopen.mono (fun _ h => by cases h), hno, hcf,
     (FunOkAt_nonArrow_eq_unknown rfl).mp hfun⟩,
    hreach⟩

theorem conform_default_sound {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {A : List Nat} {c : Cls} {v : Val}
    (hst : StOk P ext B st) (hv : DefValOk P ext B st A v) :
    (conform c v).run st = .error .stuck ∨
    ∃ v' st', (conform c v).run st = .ok (v', st') ∧
      DefStep P ext B B st st' ∧
      ClsSafe st'.heap c v' ∧
      DefValOk P ext B st' A v' ∧
      ∀ l, Reach st'.heap v' l → st.heap.objs.size ≤ l ∨ Reach st.heap v l := by
  rcases conform_sound (P := P) (ext := ext) (B := B) (c := c) (sk := .unknown)
      (onceOnly := false) (Foot := fun _ => False)
      hst hv.1 hv.2.2.2.1 (fun _ => hv.2.2.1) hv.2.2.2.2 with hSt |
    ⟨v', st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst',
     hbase', hcls', hcf', hdou', hreach', _, _, hno', _, _, hfun'⟩
  · exact Or.inl hSt
  · right
    refine ⟨v', st', hrun,
      ⟨Nat.le_refl _, hst', hsz, hcap, hr, hnr ▸ Nat.le_refl _,
       hstat ▸ ArrayExtends.refl _, hstr ▸ ArrayExtends.refl _, hpres, honceSh, hssf⟩,
      hcls',
      ⟨hbase', by rw [hr]; exact hdou' st.regions A hv.2.1, hno' rfl, hcf', hfun'⟩,
      hreach'⟩

theorem bindAt_default_sound {P : Prog} {ext : ExternOracle} {B fuel s : Nat} {st : St}
    {A : List Nat} {c : Cls} {v : Val}
    (hst : StOk P ext B st) (hs : s < st.nextRegion) (hv : DefValOk P ext B st A v) :
    (bindAt P fuel s .many c v).run st = .error .stuck ∨
    (bindAt P fuel s .many c v).run st = .error .outOfFuel ∨
    ∃ bnd st', (bindAt P fuel s .many c v).run st = .ok (bnd, st') ∧
      bnd.mode = .many ∧
      DefStep P ext B B st st' ∧
      DefValOk P ext B st' A bnd.val ∧
      ∀ l, Reach st'.heap bnd.val l → st.heap.objs.size ≤ l ∨ Reach st.heap v l := by
  rcases bindAt_sound (P := P) (ext := ext) (B := B) (fuel := fuel) (s := s) (m := .many)
      (c := c) (sk := .unknown) (onceOnly := false) (Foot := fun _ => False) (v := v)
      hst hs (fun _ => hv.1) (fun _ => hv.2.2.2.1) (fun _ _ => hv.2.2.1) (fun _ => hv.2.2.2.2)
      (fun _ => rfl) (fun _ _ h => h) (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) with hSt | hOOF |
    ⟨bnd, st', hrun, hmode, hr, hnr, hstat, hstr, hsz, hcap, _, hpres, honceSh, hssf, hst',
     hbase', hcf', _, hplain', _, _, _, hdou', hreach', _⟩
  · exact Or.inl hSt
  · exact Or.inr (Or.inl hOOF)
  · right; right
    obtain ⟨_, hno', hfun'⟩ := hplain' (by decide) (by decide)
    have hpresOld : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap :=
      hpres.mono fun _ hlt => ⟨hlt, fun hu => by cases hu⟩
    refine ⟨bnd, st', hrun, hmode,
      ⟨Nat.le_refl _, hst', hsz, hcap, hr, hnr ▸ Nat.le_refl _,
       hstat ▸ ArrayExtends.refl _, hstr ▸ ArrayExtends.refl _, hpresOld, honceSh, hssf⟩,
      ⟨hbase', by simpa [BinderMode.isBorrowed, hr] using hdou' st.regions A (fun _ => hv.2.1),
       hno', hcf', hfun'⟩,
      fun l hl => (hreach' l hl).imp id (fun h => h.2)⟩

theorem bindParamsM_default_sound {P : Prog} {ext : ExternOracle} {B fuel s : Nat}
    (xs : List (Param × Val)) (env : List Bnd) (st : St) (A : List Nat)
    (hst : StOk P ext B st) (hs : s < st.nextRegion)
    (hxs : ∀ pv ∈ xs, pv.1.mode = .many ∧ DefValOk P ext B st A pv.2)
    (henv : ∀ b ∈ env, b.mode = .many ∧ DefValOk P ext B st A b.val) :
    (bindParamsM P fuel s xs env).run st = .error .stuck ∨
    (bindParamsM P fuel s xs env).run st = .error .outOfFuel ∨
    ∃ env' st', (bindParamsM P fuel s xs env).run st = .ok (env', st') ∧
      DefStep P ext B B st st' ∧
      (∀ b ∈ env', b.mode = .many ∧ DefValOk P ext B st' A b.val) ∧
      ∀ b ∈ env', ∀ l, Reach st'.heap b.val l →
        st.heap.objs.size ≤ l ∨ (∃ pv ∈ xs, Reach st.heap pv.2 l) ∨ (∃ b0 ∈ env, Reach st.heap b0.val l) := by
  induction xs generalizing env st with
  | nil =>
    right; right
    exact ⟨env, st, rfl, DefStep.refl hst, henv, fun b hb l hl => Or.inr (Or.inr ⟨b, hb, hl⟩)⟩
  | cons pv rest ih =>
    rcases pv with ⟨p, v⟩
    obtain ⟨hpMode, hvOk⟩ := hxs (p, v) List.mem_cons_self
    unfold bindParamsM
    rw [M_bind_run, hpMode]
    rcases bindAt_default_sound (P := P) (ext := ext) (B := B) (fuel := fuel) (s := s)
        (c := p.cls) hst hs hvOk with hSt | hOOF |
      ⟨bnd, st₁, hrun₁, hbm₁, hstep₁, hbv₁, hreach₁⟩
    · left; rw [hSt]
    · right; left; rw [hOOF]
    · rw [hrun₁]; dsimp only
      have hs₁ : s < st₁.nextRegion := Nat.lt_of_lt_of_le hs hstep₁.2.2.2.2.2.1
      have hxs₁ : ∀ q ∈ rest, q.1.mode = .many ∧ DefValOk P ext B st₁ A q.2 := by
        intro q hq
        obtain ⟨hm, hv⟩ := hxs q (List.mem_cons_of_mem _ hq)
        exact ⟨hm, hstep₁.lift_val hv⟩
      have henv₁ : ∀ b ∈ bnd :: env, b.mode = .many ∧ DefValOk P ext B st₁ A b.val := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact ⟨hbm₁, hbv₁⟩
        · obtain ⟨hm, hv⟩ := henv b hb'
          exact ⟨hm, hstep₁.lift_val hv⟩
      rcases ih (bnd :: env) st₁ hstep₁.2.1 hs₁ hxs₁ henv₁ with hSt2 | hOOF2 |
        ⟨env', st', hrun₂, hstep₂, henv', hreach₂⟩
      · exact Or.inl hSt2
      · exact Or.inr (Or.inl hOOF2)
      · right; right
        refine ⟨env', st', hrun₂, hstep₁.trans hstep₂, henv', fun b hb l hl => ?_⟩
        rcases hreach₂ b hb l hl with hge | ⟨q, hq, hrq⟩ | ⟨b0, hb0, hrb0⟩
        · exact Or.inl (Nat.le_trans hstep₁.2.2.1 hge)
        · have hvq := (hxs q (List.mem_cons_of_mem _ hq)).2
          have hpq : PreservesLocs (Reach st.heap q.2) st.heap st₁.heap :=
            hstep₁.2.2.2.2.2.2.2.2.1.mono fun _ h => hvq.1.1.reach_lt_size h
          exact Or.inr (Or.inl ⟨q, List.mem_cons_of_mem _ hq, (Reach_congr hpq l).mp hrq⟩)
        · rcases List.mem_cons.mp hb0 with rfl | hb0'
          · rcases hreach₁ l hrb0 with hge0 | hrv0
            · exact Or.inl hge0
            · exact Or.inr (Or.inl ⟨(p, v), List.mem_cons_self, hrv0⟩)
          · have hvb0 := (henv b0 hb0').2
            have hpb0 : PreservesLocs (Reach st.heap b0.val) st.heap st₁.heap :=
              hstep₁.2.2.2.2.2.2.2.2.1.mono fun _ h => hvb0.1.1.reach_lt_size h
            exact Or.inr (Or.inr ⟨b0, hb0', (Reach_congr hpb0 l).mp hrb0⟩)

theorem ret_default_sound {P : Prog} {ext : ExternOracle} {B fuel s cur : Nat} {st : St}
    {A : List Nat} {c : Cls} {v : Val}
    (hst : StOk P ext B st) (hcur : cur < st.nextRegion)
    (hv : DefValOk P ext B st A v) (hnoS : OpenUnder [s] [] v) :
    (ret P fuel s cur .shared c v).run st = .error .stuck ∨
    (ret P fuel s cur .shared c v).run st = .error .outOfFuel ∨
    ∃ v' st', (ret P fuel s cur .shared c v).run st = .ok (v', st') ∧
      DefStep P ext B B st st' ∧
      ClsSafe st'.heap c v' ∧
      DefValOk P ext B st' A v' ∧
      ∀ l, Reach st'.heap v' l → st.heap.objs.size ≤ l ∨ Reach st.heap v l := by
  rcases ret_sound (P := P) (ext := ext) (B := B) (fuel := fuel) (s := s) (cur := cur)
      (r := .shared) (c := c) (v := v) (sk := .unknown)
      hst hv.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2 hcur (fun h => by cases h)
      (fun _ => hnoS) (fun h => by cases h) (fun h => by cases h) with hSt | hOOF |
    ⟨v', st', hrun, hr, hnr, hstat, hstr, hsz, hcap, _, hpres, honceSh, hssf, hst',
     hbase', hcls', hno', hcf', hfun', _, hdouSU, _, hreach', _⟩
  · exact Or.inl hSt
  · exact Or.inr (Or.inl hOOF)
  · right; right
    have hpresOld : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap :=
      hpres.mono fun _ hlt => ⟨hlt, fun hu => by cases hu⟩
    refine ⟨v', st', hrun,
      ⟨Nat.le_refl _, hst', hsz, hcap, hr, hnr ▸ Nat.le_refl _,
       hstat ▸ ArrayExtends.refl _, hstr ▸ ArrayExtends.refl _, hpresOld, honceSh, hssf⟩,
      hcls',
      ⟨hbase', by rw [hr]; exact hdouSU st.regions A (Or.inl rfl) hv.2.1, hno', hcf', hfun'⟩,
      hreach'⟩

theorem select_default_sound {P : Prog} {ext : ExternOracle} {B : Nat}
    {k : CaseInfo} {mv : Val} {st : St} {A : List Nat}
    (hidx : CtorsIndexed P)
    (hdef : ∀ ctor ∈ (P.ctorsOf k.ind).toList, ∀ ind ci nP fs,
      P.ctorOf? ctor = some (ind, ci, nP, fs) →
      ∀ f ∈ fs.toList, f.mode = .many ∧ f.fmode = .inherited)
    (hst : StOk P ext B st) (hmv : DefValOk P ext B st A mv) :
    (select P k mv).run st = .error .stuck ∨
    ∃ cidx out st', (select P k mv).run st = .ok ((cidx, out), st') ∧
      DefStep P ext B B st st' ∧
      ∀ p ∈ out.toList, p.2 = false ∧ DefValOk P ext B st' A p.1 ∧
        ∀ l, Reach st'.heap p.1 l → st.heap.objs.size ≤ l ∨ Reach st.heap mv l := by
  rcases select_spec (P := P) (k := k) (mv := mv) (st := st) hidx hst.1 hmv.1.1 hmv.1.2.1 with hSt |
    ⟨cidx, out, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, hc', hoss, _, hbranches⟩
  · exact Or.inl hSt
  · right
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_old hst hc' hr (hnr ▸ Nat.le_refl _) hstat hstr hpres
    have hstep : DefStep P ext B B st st' :=
      DefStep.of_preserves_old hst hst' hsz hcap hr (hnr ▸ Nat.le_refl _) hstat hstr hpres
    have hsfMany : ∀ (ci : Nat) (f : Field), f ∈ (selectFieldsOf P k ci).toList → f.mode = .many := by
      intro ci f hf
      unfold selectFieldsOf at hf
      cases hc0 : (P.ctorsOf k.ind)[ci]? with
      | none => simp only [hc0] at hf; simp at hf
      | some ctor =>
        simp only [hc0] at hf
        cases hco : P.ctorOf? ctor with
        | none => simp only [hco] at hf; simp at hf
        | some q =>
          rcases q with ⟨ind, ci', nP, fs⟩
          simp only [hco] at hf
          have hcm : ctor ∈ (P.ctorsOf k.ind).toList :=
            Array.mem_toList_iff.mpr (Array.mem_of_getElem? hc0)
          exact (hdef ctor hcm ind ci' nP fs hco f hf).1
    refine ⟨cidx, out, st', hrun, hstep, ?_⟩
    rcases hbranches with ⟨_, hnat0 | hnat1⟩ | ⟨_, hirr | hwrap | hctor⟩
    · obtain ⟨_, rfl, _⟩ := hnat0
      intro p hp; simp at hp
    · obtain ⟨_, m, v, rfl, _, hdlv, hclsv, _, hacycv, _, hreachv⟩ := hnat1
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      obtain ⟨loc, cap, o, n, rfl, ho, hcell, hocap⟩ := hclsv
      have hbase : ValBaseOk st' (.ref loc cap []) :=
        ValBaseOk_of_deepLive hdlv hacycv (DeepTaintsBounded_num ho hcell)
      exact ⟨rfl, DefValOk_of_clsSafe (c := .leaf) (by decide) hbase
        (ClsSafe.of_clsOk ⟨loc, cap, o, n, rfl, ho, hcell, hocap⟩),
        fun l hl => Or.inl (hreachv l hl)⟩
    · obtain ⟨rfl, rfl⟩ := hirr
      intro p hp
      rw [Array.toList_map, List.mem_map] at hp
      obtain ⟨f, hf, rfl⟩ := hp
      have hm : f.mode = .many := hsfMany cidx f hf
      refine ⟨by rw [hm]; decide, DefValOk_imm P ext B st' A .irr, fun _ hl => by cases hl⟩
    · obtain ⟨rfl, rfl, wi, _, rfl, _⟩ := hwrap
      intro p hp
      let arr := (selectFieldsOf P k 0).map (fun f => (Val.imm .irr, f.mode == .erased))
      have hp' : p ∈ (arr.setIfInBounds wi (mv, false)).toList := by
        simpa only [arr, Array.set!_eq_setIfInBounds] using hp
      obtain ⟨i, hi, hpEq⟩ := List.mem_iff_getElem.mp hp'
      have hiArr : i < (arr.setIfInBounds wi (mv, false)).size := by simpa using hi
      have hiSz : i < arr.size := by simpa using hiArr
      have hget : (arr.setIfInBounds wi (mv, false))[i]? = some p := by
        rw [Array.getElem?_eq_getElem hiArr, ← Array.getElem_toList, hpEq]
      by_cases heq : i = wi
      · subst heq
        rw [Array.getElem?_setIfInBounds_self] at hget
        simp only [hiSz, ↓reduceIte] at hget
        cases hget
        exact ⟨rfl, hmv, fun l hl => Or.inr hl⟩
      · rw [Array.getElem?_setIfInBounds_ne (Ne.symm heq), Array.getElem?_eq_getElem hiSz] at hget
        cases hget
        have hi0 : i < (selectFieldsOf P k 0).size := by simpa [arr] using hiSz
        have hm : (selectFieldsOf P k 0)[i].mode = .many :=
          hsfMany 0 _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi0))
        dsimp only [arr]
        rw [Array.getElem_map]
        exact ⟨by rw [hm]; decide, DefValOk_imm P ext B st' A .irr, fun _ hl => by cases hl⟩
    · obtain ⟨loc, cap, t, o, r, fs, nP, fdefs, rfl, ho, hcapO, hcell, hctorR, hsfEq,
        houtSz, hfieldEach, _⟩ := hctor
      have hrMem : r ∈ (P.ctorsOf k.ind).toList :=
        Array.mem_toList_iff.mpr (Array.mem_of_getElem? (hidx r k.ind cidx nP fdefs hctorR))
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      have hiOut : i < out.size := by simpa using hi
      have hiFd : i < fdefs.size := houtSz ▸ hiOut
      have hfi : fdefs[i]? = some fdefs[i] := Array.getElem?_eq_getElem hiFd
      obtain ⟨v, hvOut, hnk, hkv⟩ := hfieldEach i fdefs[i] hfi
      rw [Array.getElem?_eq_getElem hiOut, Option.some.injEq] at hvOut
      have hfdMem : fdefs[i] ∈ fdefs.toList := Array.mem_toList_iff.mpr (Array.getElem_mem hiFd)
      have ⟨hm, hinh⟩ := hdef r hrMem k.ind cidx nP fdefs hctorR fdefs[i] hfdMem
      have herF : (fdefs[i].mode == .erased) = false := by rw [hm]; decide
      rw [Array.getElem_toList, hvOut]
      refine ⟨herF, ?_, ?_⟩
      · cases hfk : fdefs[i].kept with
        | false =>
          rw [hnk hfk]
          exact DefValOk_imm P ext B st' A .irr
        | true =>
          obtain ⟨hrawMem, hsame, hclsV, hdlV, hacycV, htv, _, _, hheldV, _, _, hdouV⟩ := hkv hfk
          have hrawOk : DefValOk P ext B st A (fs[i]?.getD (.imm .irr)) := by
            rcases hrawMem with hEq | hmem
            · rw [hEq]; exact DefValOk_imm P ext B st A .irr
            · have hvals : fs[i]?.getD (.imm .irr) ∈ o.cell.vals := by rw [hcell]; exact hmem
              have hheld : HeldBy st.heap (.ref loc cap t) (fs[i]?.getD (.imm .irr)) :=
                HeldBy_of_mem_vals ho hvals
              obtain ⟨hnoR, hfunR⟩ := hmv.2.2.2.1 loc o r fs _ .here ho hcell hmem
              exact ⟨hmv.1.sub hheld, hmv.2.1.sub hheld, hnoR, hmv.2.2.2.1.sub hheld, hfunR⟩
          have htbV : DeepTaintsBounded st'.heap st'.nextRegion v := by
            intro w hw x hx
            rw [hnr]
            rcases hheldV w hw with rfl | hwr
            · rcases htv x hx with hxr | ⟨_, hxt⟩
              · exact hrawOk.1.2.2.2 _ (HeldBy.refl _ _) x hxr
              · exact hmv.1.2.2.2 _ (HeldBy.refl _ _) x hxt
            · exact hrawOk.1.2.2.2 w hwr x hx
          have hbaseV : ValBaseOk st' v := ValBaseOk_of_deepLive hdlV hacycV htbV
          by_cases hcv : fdefs[i].cls = .val
          · have hlocV : SameLoc (fs[i]?.getD (.imm .irr)) v := by
              rcases hsame hcv with ⟨_, h1, h2⟩ | ⟨_, _, _, _, h1, h2⟩
              · rw [h1, h2]; rfl
              · rw [h1, h2]; rfl
            have hopenV : DeepOpenUnder st'.heap st'.regions A v := by
              rw [hr]; exact hdouV st.regions A hrawOk.2.1 (fun _ => hmv.2.1.self)
            exact DefValOk_of_sameShape (Nat.le_refl _) hlocV (hoss.to_sameShapeOn _)
              hstep.regsFuture hbaseV hopenV hrawOk
          · exact DefValOk_of_clsSafe hcv hbaseV (ClsSafe.of_clsOk hclsV)
      · intro l hl
        cases hfk : fdefs[i].kept with
        | false => rw [hnk hfk] at hl; cases hl
        | true =>
          obtain ⟨hrawMem, _, _, _, _, _, _, hreachV, _⟩ := hkv hfk
          rcases hreachV l hl with hge | hrawR
          · exact Or.inl hge
          · rcases hrawMem with hEq | hmem
            · rw [hEq] at hrawR; cases hrawR
            · exact Or.inr (.step ho (by rw [hcell]; exact hmem) hrawR)

theorem formClosure_default_sound {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {env : List Bnd} {p : Param} {res : ResultMode} {rc : Cls} {fvs : Array Nat} {body : Term}
    {st : St} {A : List Nat}
    (hst : StOk P ext B st)
    (hfvs : ∀ i ∈ fvs.toList, ∀ b, env[i]? = some b → b.mode = .many ∧ DefValOk P ext B st A b.val) :
    (formClosure P fuel env p res rc fvs body).run st = .error .stuck ∨
    (formClosure P fuel env p res rc fvs body).run st = .error .outOfFuel ∨
    ∃ rv env' taint cap st',
      (formClosure P fuel env p res rc fvs body).run st = .ok (rv, st') ∧
      DefStep P ext B B st st' ∧
      rv = .ref st.heap.objs.size cap taint ∧
      st'.heap.objs[st.heap.objs.size]? = some ⟨.clo env' p res rc fvs body, cap⟩ ∧
      ValBaseOk st' rv ∧
      DeepOpenUnder st'.heap st'.regions A rv ∧
      NoOnceCell st'.heap rv ∧
      CtorFieldsOk P ext B st' rv ∧
      (∀ i ∈ fvs.toList, ∃ b, env'[i]? = some b ∧ b.mode = .many ∧ DefValOk P ext B st' A b.val) ∧
      ∀ l, Reach st'.heap rv l →
        l = st.heap.objs.size ∨ ∃ i ∈ fvs.toList, ∃ b, env[i]? = some b ∧ Reach st.heap b.val l := by
  have hfvsSpec : ∀ i ∈ fvs.toList, ∀ b, env[i]? = some b →
      b.mode ≠ .erased ∧ DeepLive st.heap b.val ∧ AcyclicFrom st.heap b.val ∧
      (b.mode.isUnique = true →
        OwnTreeFull P st.heap b.val ∧ (b.mode.isBorrowed = false → OpenUnder st.regions [] b.val)) := by
    intro i hi b hb
    obtain ⟨hm, hv⟩ := hfvs i hi b hb
    exact ⟨by rw [hm]; decide, hv.1.1, hv.1.2.1, fun hu => by rw [hm] at hu; cases hu⟩
  have hdisjSpec : ∀ (a b : Nat) (ia ib : Nat) (ba bb : Bnd), a ≠ b →
      fvs.toList[a]? = some ia → fvs.toList[b]? = some ib →
      env[ia]? = some ba → env[ib]? = some bb → ba.mode.isUnique = true →
      ∀ l, OwnReach P st.heap ba.val l → ¬ Reach st.heap bb.val l := by
    intro a _ ia _ ba _ _ ha _ hba _ hu
    have hm := (hfvs ia (List.mem_of_getElem? ha) ba hba).1
    rw [hm] at hu; cases hu
  rcases formClosure_spec (P := P) (fuel := fuel) (env := env) (p := p) (res := res) (rc := rc)
      (fvs := fvs) (body := body) hst.1 hfvsSpec hdisjSpec with hSt | hOOF |
    ⟨rv, env', taint, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hc', hoss, hpres,
     ⟨cap, hrvEq, hoNew⟩, hcapEach, _, htIff, hdl', hacyc', _, hdou', hreach'⟩
  · exact Or.inl hSt
  · exact Or.inr (Or.inl hOOF)
  · right; right
    have hpresOld : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap := by
      intro l hlt
      refine hpres l ⟨hlt, fun i hi b hb hu => ?_⟩
      have hm := (hfvs i hi b hb).1
      rw [hm] at hu; cases hu
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_old hst hc' hr (hnr ▸ Nat.le_refl _) hstat hstr hpresOld
    have hstep : DefStep P ext B B st st' :=
      DefStep.of_preserves_old hst hst' (by omega) hcap hr (hnr ▸ Nat.le_refl _) hstat hstr hpresOld
    have hcapOk : ∀ i ∈ fvs.toList, ∃ b, env'[i]? = some b ∧ b.mode = .many ∧ DefValOk P ext B st' A b.val := by
      intro i hi
      obtain ⟨b0, v', hb0, he', hvsh, hdlv', hacycv'⟩ := hcapEach i hi
      obtain ⟨hm0, hv0⟩ := hfvs i hi b0 hb0
      have hlocV : SameLoc b0.val v' := SameLoc.of_valSameShape hvsh
      have htbV : DeepTaintsBounded st'.heap st'.nextRegion v' := by
        rw [hnr]
        refine DeepTaintsBounded_of_oldSameShape hv0.1.1 hoss hlocV ?_ hv0.1.2.2.2
        intro x hx
        rw [← hvsh.taint_eq] at hx
        exact hv0.1.2.2.2 _ (HeldBy.refl _ _) x hx
      have hdouV : DeepOpenUnder st'.heap st'.regions A v' := by
        rw [hr]
        intro w hw x hx hopen
        rcases hw with rfl | ⟨l, o₂, hr₂, ho₂, hm₂⟩
        · rw [← hvsh.taint_eq] at hx
          exact hv0.2.1.self x hx hopen
        · have hr₁ : Reach st.heap b0.val l :=
            Reach_of_sameShapeOn_rev hv0.1.1 (hoss.to_sameShapeOn _) hlocV hr₂
          have hlt₁ : l < st.heap.objs.size := hv0.1.1.reach_lt_size hr₁
          have ho₁ : st.heap.objs[l]? = some o₂ := (hpresOld l hlt₁).symm.trans ho₂
          exact hv0.2.1 w (Or.inr ⟨l, o₂, hr₁, ho₁, hm₂⟩) x hx hopen
      refine ⟨{ b0 with val := v' }, he', hm0,
        DefValOk_of_sameShape (Nat.le_refl _) hlocV (hoss.to_sameShapeOn _)
          hstep.regsFuture (ValBaseOk_of_deepLive hdlv' hacycv' htbV) hdouV hv0⟩
    have hvalsOk : ∀ w ∈ (Cell.clo env' p res rc fvs body).vals, DefValOk P ext B st' A w := by
      intro w hw
      simp only [Cell.vals, List.mem_filterMap] at hw
      obtain ⟨i, hi, hmap⟩ := hw
      obtain ⟨bd, hget, _, hok⟩ := hcapOk i hi
      rw [hget] at hmap; simp only [Option.map_some, Option.some.injEq] at hmap
      subst hmap; exact hok
    have htbRv : DeepTaintsBounded st'.heap st'.nextRegion rv := by
      intro w hw x hx
      rcases hw with rfl | ⟨l, o', hr', ho', hm'⟩
      · obtain ⟨i, hi, b, hb, hxb⟩ := (htIff x).mp hx
        rw [hnr]
        exact (hfvs i hi b hb).2.1.2.2.2 _ (HeldBy.refl _ _) x hxb
      · rw [hrvEq] at hr'
        cases hr' with
        | here =>
          rw [hoNew] at ho'; cases ho'
          exact (hvalsOk w hm').1.2.2.2 w (HeldBy.refl _ _) x hx
        | step ho0 hm0 hr1 =>
          rw [hoNew] at ho0; cases ho0
          exact (hvalsOk _ hm0).1.2.2.2 w (Or.inr ⟨l, o', hr1, ho', hm'⟩) x hx
    have hnoRv : NoOnceCell st'.heap rv := by
      intro l o' hr' ho' tgt sp hc
      rw [hrvEq] at hr'
      cases hr' with
      | here => rw [hoNew] at ho'; cases ho'; cases hc
      | step ho0 hm0 hr1 =>
        rw [hoNew] at ho0; cases ho0
        exact (hvalsOk _ hm0).2.2.1 l o' hr1 ho' tgt sp hc
    have hcfRv : CtorFieldsOk P ext B st' rv := by
      intro l o' r' fs' w hr' ho' hc hw
      rw [hrvEq] at hr'
      cases hr' with
      | here => rw [hoNew] at ho'; cases ho'; cases hc
      | step ho0 hm0 hr1 =>
        rw [hoNew] at ho0; cases ho0
        exact (hvalsOk _ hm0).2.2.2.1 l o' r' fs' w hr1 ho' hc hw
    refine ⟨rv, env', taint, cap, st', hrun, hstep, hrvEq, hoNew,
      ValBaseOk_of_deepLive hdl' hacyc' htbRv,
      by rw [hr]; exact hdou' st.regions A (fun i hi b hb => (hfvs i hi b hb).2.2.1),
      hnoRv, hcfRv, hcapOk, hreach'⟩

theorem makePap_default_sound {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {r : Ref} {params : Array Param} {vs : List Val} {st : St} {A : List Nat}
    (hst : StOk P ext B st)
    (hpm : ∀ p ∈ params.toList, p.mode = .many)
    (hvs : ∀ v ∈ vs, DefValOk P ext B st A v) :
    (makePap P fuel r params vs).run st = .error .outOfFuel ∨
    ∃ rv out cap st',
      (makePap P fuel r params vs).run st = .ok (rv, st') ∧
      DefStep P ext B B st st' ∧
      rv = .ref st.heap.objs.size cap (taints out.toList) ∧
      st'.heap.objs[st.heap.objs.size]? = some ⟨.pap r out, cap⟩ ∧
      ValBaseOk st' rv ∧
      DeepOpenUnder st'.heap st'.regions A rv ∧
      NoOnceCell st'.heap rv ∧
      CtorFieldsOk P ext B st' rv ∧
      (∀ w ∈ out.toList, DefValOk P ext B st' A w) ∧
      ∀ l, Reach st'.heap rv l → l = st.heap.objs.size ∨ ∃ v ∈ vs, Reach st.heap v l := by
  have hnotUniq : ∀ (i : Nat), ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = false := by
    intro i
    cases hp : params[i]? with
    | none => rfl
    | some p =>
      have hm := hpm p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp))
      simp [hm, BinderMode.isUnique]
  rcases makePap_sound (P := P) (ext := ext) (B := B) (fuel := fuel) (r := r) (params := params)
      (vs := vs) hst
      (fun v hv => let h := hvs v hv; ⟨h.1, h.2.2.1, h.2.2.2.1⟩)
      (fun i _ _ hu => by rw [hnotUniq i] at hu; cases hu)
      (fun i _ _ _ _ _ _ hu => by rw [hnotUniq i] at hu; cases hu) with hOOF |
    ⟨rv, out, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, _, hpres, honceSh, hssf, hst',
     ⟨cap, hrvEq, hoNew⟩, houtSz, houtProps, hbase', hno', hcf', hdou', hreach'⟩
  · exact Or.inl hOOF
  · right
    have hpresOld : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap :=
      hpres.mono fun _ hlt => ⟨hlt, fun i _ _ hu => by rw [hnotUniq i] at hu; cases hu⟩
    have hstep : DefStep P ext B B st st' :=
      ⟨Nat.le_refl _, hst', by omega, hcap, hr, hnr ▸ Nat.le_refl _,
       hstat ▸ ArrayExtends.refl _, hstr ▸ ArrayExtends.refl _, hpresOld, honceSh, hssf⟩
    have hdouRv : DeepOpenUnder st'.heap st'.regions A rv := by
      rw [hr]; exact hdou' st.regions A (fun v hv => (hvs v hv).2.1)
    have houtOk : ∀ w ∈ out.toList, DefValOk P ext B st' A w := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
      have hiOut : i < out.size := by simpa using hi
      have hiVs : i < vs.length := houtSz ▸ hiOut
      obtain ⟨w', hw', _, hbw', hnow', hcfw', hfunw'⟩ := houtProps i vs[i] (List.getElem?_eq_getElem hiVs)
      rw [Array.getElem?_eq_getElem hiOut, Option.some.injEq] at hw'
      subst hw'
      have hheld : HeldBy st'.heap rv out[i] := by
        rw [hrvEq]
        exact HeldBy_of_mem_vals hoNew (by simp [Cell.vals, Array.mem_toList_iff.mpr (Array.getElem_mem hiOut)])
      exact ⟨hbw', hdouRv.sub hheld, hnow', hcfw',
        hfunw' .unknown false (fun _ => False) (hvs vs[i] (List.getElem_mem hiVs)).2.2.2.2⟩
    exact ⟨rv, out, cap, st', hrun, hstep, hrvEq, hoNew, hbase', hdouRv, hno', hcf', houtOk, hreach'⟩

/-! ## 3. Inner Strong Induction on Linear Budget `B` -/

private theorem DefStep.open_close {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st st₁ : St}
    (hregs : RegsOk st)
    (hmid : DefStep P ext B₁ B₂
      { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions } st₁) :
    DefStep P ext B₁ B₂ st { st₁ with regions := st₁.regions.filter (· != st.nextRegion) } := by
  refine ⟨hmid.1, StOk_closeRegion st.nextRegion hmid.2.1,
    hmid.2.2.1, hmid.2.2.2.1, ?_, Nat.le_trans (Nat.le_succ _) hmid.2.2.2.2.2.1,
    hmid.2.2.2.2.2.2.1, hmid.2.2.2.2.2.2.2.1, hmid.2.2.2.2.2.2.2.2.1,
    hmid.2.2.2.2.2.2.2.2.2.1, hmid.2.2.2.2.2.2.2.2.2.2⟩
  dsimp only
  rw [hmid.2.2.2.2.1]
  exact open_close_regions_eq_def hregs

private theorem applyOneConformS_val_eq (P : Prog) (ext : ExternOracle) (fuel : Nat)
    (f a : Val) (st : St) (B : Nat) :
    (applyOneConformS P ext fuel f a .val).run (st, B) =
      (applyOneS P ext fuel f a .val).run (st, B) := by
  unfold applyOneConformS
  rw [MS_bind_run]
  cases (applyOneS P ext fuel f a .val).run (st, B) with
  | error e => rfl
  | ok p =>
    rcases p with ⟨g, sb⟩
    rcases sb with ⟨st₁, B₁⟩
    dsimp only
    rw [MS_liftM_run]
    rfl

private theorem deepOpenUnder_applyResultRegs_shared {h : Heap} {rs fRegs aRegs A' : List Nat}
    {c : Cls} {v : Val}
    (hsub : ∀ x ∈ A', x ∈ aRegs ++ fRegs)
    (hcls : ClsSafe h c v)
    (hdou : DeepOpenUnder h rs A' v) :
    DeepOpenUnder h rs (applyResultRegs { heap := h, regions := rs } .shared c fRegs aRegs) v := by
  cases c with
  | val =>
    dsimp only [applyResultRegs]
    simp only [show (Cls.val != Cls.val) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    exact hdou.mono hsub
  | irr | imm | leaf =>
    dsimp only [applyResultRegs]
    have hne : (Cls.irr != Cls.val) = true := rfl
    all_goals
      try simp only [show (Cls.irr != Cls.val) = true from rfl, ↓reduceIte]
      try simp only [show (Cls.imm != Cls.val) = true from rfl, ↓reduceIte]
      try simp only [show (Cls.leaf != Cls.val) = true from rfl, ↓reduceIte]
      exact ClsSafe_deepOpenUnder_nil (by decide) hcls

/-- Soundness predicate for `evalS` at budget `b`. -/
private def EvalSDefOk (P : Prog) (ext : ExternOracle) (b : Nat) : Prop :=
  ∀ (fuel : Nat) (env : List Bnd) (t : Term) (st : St) (A : List Nat) (Scope : Nat → Prop),
    DefaultTerm P t →
    LamsClosed t →
    (∀ x, FreeVarIn 0 t x → Scope x) →
    StOk P ext b st →
    DefEnvOk P ext b st A Scope env →
    (∀ k, (evalS P ext fuel env t).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (evalS P ext fuel env t).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ EnvReach Scope st.heap env l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l

/-- Soundness predicate for `spineS` at budget `b`. -/
private def SpineSDefOk (P : Prog) (ext : ExternOracle) (b : Nat) : Prop :=
  ∀ (fuel : Nat) (env : List Bnd) (head : Term) (args : List Term) (c : Cls)
    (st : St) (A : List Nat) (Scope : Nat → Prop),
    DefaultTerm P head →
    LamsClosed head →
    (∀ x, FreeVarIn 0 head x → Scope x) →
    (∀ a ∈ args, DefaultTerm P a ∧ LamsClosed a ∧ ∀ x, FreeVarIn 0 a x → Scope x) →
    StOk P ext b st →
    DefEnvOk P ext b st A Scope env →
    (∀ k, (spineS P ext fuel env head args c).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (spineS P ext fuel env head args c).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ EnvReach Scope st.heap env l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l

/-- Soundness predicate for `callWithS` at budget `b`. -/
private def CallWithSDefOk (P : Prog) (ext : ExternOracle) (b : Nat) : Prop :=
  ∀ (fuel : Nat) (r : Ref) (vs : List Val) (c : Cls) (st : St) (A : List Nat),
    (∀ d, P.find? r = some d → DefaultIface d) →
    StOk P ext b st →
    (∀ v ∈ vs, DefValOk P ext b st A v) →
    (∀ k, (callWithS P ext fuel r vs c).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (callWithS P ext fuel r vs c).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ (∃ v ∈ vs, Reach st.heap v l) ∨ StaticStrLoc st l ∨ NumLoc st'.heap l

/-- Soundness predicate for `applyAllS` at budget `b`. -/
private def ApplyAllSDefOk (P : Prog) (ext : ExternOracle) (b : Nat) : Prop :=
  ∀ (fuel : Nat) (f : Val) (vs : List Val) (c : Cls) (st : St) (A : List Nat),
    StOk P ext b st →
    DefValOk P ext b st A f →
    (∀ v ∈ vs, DefValOk P ext b st A v) →
    (∀ k, (applyAllS P ext fuel f vs c).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (applyAllS P ext fuel f vs c).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        ClsSafe st'.heap c rv ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨ (∃ v ∈ vs, Reach st.heap v l) ∨
          StaticStrLoc st l ∨ NumLoc st'.heap l

/-- Soundness predicate for `applyAltS` at budget `b`. -/
private def ApplyAltSDefOk (P : Prog) (ext : ExternOracle) (b : Nat) : Prop :=
  ∀ (fuel : Nat) (env : List Bnd) (t : Term) (args : List (Val × Bool))
    (st : St) (A : List Nat) (Scope : Nat → Prop),
    DefaultTerm P t →
    LamsClosed t →
    (∀ x, FreeVarIn 0 t x → Scope x) →
    StOk P ext b st →
    DefEnvOk P ext b st A Scope env →
    (∀ ae ∈ args, ae.2 = false ∧ DefValOk P ext b st A ae.1) →
    (∀ k, (applyAltS P ext fuel env t args).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (applyAltS P ext fuel env t args).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ EnvReach Scope st.heap env l ∨
          (∃ ae ∈ args, Reach st.heap ae.1 l) ∨ StaticStrLoc st l ∨ NumLoc st'.heap l

/-- `FunOkAt` predicate at budget `b` for a default-mode runtime closure cell. -/
private def CloDefFunOk (P : Prog) (ext : ExternOracle) (b : Nat) : Prop :=
  ∀ (st₀ : St) (loc cap : Nat) (env₀ : List Bnd) (p : Param) (rc : Cls)
    (fvs : Array Nat) (body : Term) (t : List Nat),
    st₀.heap.objs[loc]? = some ⟨.clo env₀ p .shared rc fvs body, cap⟩ →
    p.mode = .many →
    DefaultTerm P body →
    LamsClosed body →
    (∀ x, x ∈ fvs.toList ↔ FreeVarIn 1 body x) →
    (∀ i ∈ fvs.toList, ∃ bd, env₀[i]? = some bd ∧ bd.mode = .many ∧
      ValBaseOk st₀ bd.val ∧ NoOnceCell st₀.heap bd.val ∧
      CtorFieldsOk P ext b st₀ bd.val ∧
      FunOkAt P ext b st₀ .unknown false (fun _ => False) bd.val) →
    FunOkAt P ext b st₀ .unknown false (fun _ => False) (.ref loc cap t)

/-- `FunOkAt` predicate at budget `b` for a default-interface runtime `.pap` cell. -/
private def PapDefFunOk (P : Prog) (ext : ExternOracle) (b : Nat) : Prop :=
  ∀ (st₀ : St) (loc cap : Nat) (r : Ref) (args : Array Val) (t : List Nat),
    st₀.heap.objs[loc]? = some ⟨.pap r args, cap⟩ →
    (∀ d, P.find? r = some d → DefaultIface d) →
    (∀ w ∈ args.toList,
      ValBaseOk st₀ w ∧ NoOnceCell st₀.heap w ∧
      CtorFieldsOk P ext b st₀ w ∧
      FunOkAt P ext b st₀ .unknown false (fun _ => False) w) →
    FunOkAt P ext b st₀ .unknown false (fun _ => False) (.ref loc cap t)

private theorem evalListS_of_evalS {P : Prog} {ext : ExternOracle} {N : Nat}
    (heval : ∀ b ≤ N, EvalSDefOk P ext b) :
    ∀ (ts : List Term) (acc : List Val) (b fuel : Nat) (env : List Bnd)
      (st : St) (A : List Nat) (Scope : Nat → Prop),
      b ≤ N →
      (∀ t ∈ ts, DefaultTerm P t ∧ LamsClosed t ∧ ∀ x, FreeVarIn 0 t x → Scope x) →
      StOk P ext b st →
      DefEnvOk P ext b st A Scope env →
      (∀ v ∈ acc, DefValOk P ext b st A v) →
      (∀ k, (evalListS P ext fuel env ts acc).run (st, b) ≠ .error (.violation k)) ∧
      ∀ vs st' B',
        (evalListS P ext fuel env ts acc).run (st, b) = .ok (vs, (st', B')) →
          DefStep P ext b B' st st' ∧
          (∀ v ∈ vs, DefValOk P ext B' st' A v) ∧
          ∀ v ∈ vs, ∀ l, Reach st'.heap v l →
            st.heap.objs.size ≤ l ∨ (∃ v0 ∈ acc, Reach st.heap v0 l) ∨
            EnvReach Scope st.heap env l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
  intro ts
  induction ts with
  | nil =>
    intro acc b fuel env st A Scope _ _ hst _ hacc
    unfold evalListS
    refine ⟨(fun _ h => by cases h), fun vs st' B' h => ?_⟩
    cases h
    exact ⟨DefStep.refl hst, hacc, fun v hv l hl => Or.inr (Or.inl ⟨v, hv, hl⟩)⟩
  | cons a rest ih =>
    intro acc b fuel env st A Scope hb hts hst henv hacc
    obtain ⟨hda, hlca, hfva⟩ := hts a List.mem_cons_self
    obtain ⟨hnoV1, hok1⟩ := heval b hb fuel env a st A Scope hda hlca hfva hst henv
    have hunfold : (evalListS P ext fuel env (a :: rest) acc).run (st, b) =
        (match (evalS P ext fuel env a).run (st, b) with
         | .ok (v, (st₁, B₁)) => (evalListS P ext fuel env rest (acc ++ [v])).run (st₁, B₁)
         | .error e => .error e) := by
      conv => lhs; unfold evalListS
      rw [MS_bind_run]
      cases (evalS P ext fuel env a).run (st, b) with
      | error _ => rfl
      | ok p => rcases p with ⟨_, ⟨_, _⟩⟩; rfl
    cases he1 : (evalS P ext fuel env a).run (st, b) with
    | error e =>
      rw [hunfold, he1]
      refine ⟨(fun k hk => by cases hk; exact hnoV1 k he1), (fun _ _ _ h => by cases h)⟩
    | ok p1 =>
      rcases p1 with ⟨v, ⟨st₁, B₁⟩⟩
      rw [hunfold, he1]
      obtain ⟨hstep1, hv1, hreach1⟩ := hok1 v st₁ B₁ he1
      have hacc1 : ∀ u ∈ acc ++ [v], DefValOk P ext B₁ st₁ A u := by
        intro u hu
        rcases List.mem_append.mp hu with hu0 | hu1
        · exact hstep1.lift_val (hacc u hu0)
        · simp only [List.mem_singleton] at hu1; subst hu1; exact hv1
      obtain ⟨hnoV2, hok2⟩ := ih (acc ++ [v]) B₁ fuel env st₁ A Scope
        (Nat.le_trans hstep1.1 hb)
        (fun t ht => hts t (List.mem_cons_of_mem _ ht))
        hstep1.2.1 (hstep1.lift_env henv) hacc1
      refine ⟨hnoV2, fun vs st' B' h2 => ?_⟩
      obtain ⟨hstep2, hvs2, hreach2⟩ := hok2 vs st' B' h2
      refine ⟨hstep1.trans hstep2, hvs2, fun u hu l hl => ?_⟩
      rcases hreach2 u hu l hl with hge | ⟨v0, hv0, hrv0⟩ | her1 | hss1 | hnum2
      · exact Or.inl (Nat.le_trans hstep1.2.2.1 hge)
      · rcases List.mem_append.mp hv0 with hvAcc | hvNew
        · have hpv0 : PreservesLocs (Reach st.heap v0) st.heap st₁.heap :=
            hstep1.preserves_old.mono fun _ h => (hacc v0 hvAcc).1.1.reach_lt_size h
          exact Or.inr (Or.inl ⟨v0, hvAcc, (Reach_congr hpv0 l).mp hrv0⟩)
        · simp only [List.mem_singleton] at hvNew; subst hvNew
          rcases hreach1 l hrv0 with hge0 | her0 | hss0 | hnum1
          · exact Or.inl hge0
          · exact Or.inr (Or.inr (Or.inl her0))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1))))
      · exact Or.inr (Or.inr (Or.inl (EnvReach_of_preserves_old henv hstep1.preserves_old her1)))
      · rcases hstep1.staticStrFresh l hss1 with hge0 | hss0 | hnum1
        · exact Or.inl hge0
        · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hnum2)))

private theorem evalCallArgsS_of_evalS {P : Prog} {ext : ExternOracle} {N : Nat}
    (heval : ∀ b ≤ N, EvalSDefOk P ext b) :
    ∀ (d : Option RunDef) (ts : List (Term × Nat)) (acc : List Val) (b fuel : Nat) (env : List Bnd)
      (st : St) (A : List Nat) (Scope : Nat → Prop),
      b ≤ N →
      (∀ ti ∈ ts, DefaultTerm P ti.1 ∧ LamsClosed ti.1 ∧ ∀ x, FreeVarIn 0 ti.1 x → Scope x) →
      StOk P ext b st →
      DefEnvOk P ext b st A Scope env →
      (∀ v ∈ acc, DefValOk P ext b st A v) →
      (∀ k, (evalCallArgsS P ext fuel env d ts acc).run (st, b) ≠ .error (.violation k)) ∧
      ∀ vs st' B',
        (evalCallArgsS P ext fuel env d ts acc).run (st, b) = .ok (vs, (st', B')) →
          DefStep P ext b B' st st' ∧
          (∀ v ∈ vs, DefValOk P ext B' st' A v) ∧
          ∀ v ∈ vs, ∀ l, Reach st'.heap v l →
            st.heap.objs.size ≤ l ∨ (∃ v0 ∈ acc, Reach st.heap v0 l) ∨
            EnvReach Scope st.heap env l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
  intro d ts
  induction ts with
  | nil =>
    intro acc b fuel env st A Scope _ _ hst _ hacc
    unfold evalCallArgsS
    refine ⟨(fun _ h => by cases h), fun vs st' B' h => ?_⟩
    cases h
    exact ⟨DefStep.refl hst, hacc, fun v hv l hl => Or.inr (Or.inl ⟨v, hv, hl⟩)⟩
  | cons ai rest ih =>
    rcases ai with ⟨a, idx⟩
    intro acc b fuel env st A Scope hb hts hst henv hacc
    cases hsk : (match d with | some d0 => erasedAt d0 idx | none => false) with
    | true =>
      have hunfold : (evalCallArgsS P ext fuel env d ((a, idx) :: rest) acc).run (st, b) =
          (evalCallArgsS P ext fuel env d rest (acc ++ [.imm .irr])).run (st, b) := by
        conv => lhs; unfold evalCallArgsS
        cases d <;> dsimp only at hsk ⊢
        · cases hsk
        · simp only [hsk, ↓reduceIte, MS_bind_run, MS_pure_run]
      rw [hunfold]
      have hacc1 : ∀ u ∈ acc ++ [.imm .irr], DefValOk P ext b st A u := by
        intro u hu
        rcases List.mem_append.mp hu with hu0 | hu1
        · exact hacc u hu0
        · simp only [List.mem_singleton] at hu1; subst hu1; exact DefValOk_imm P ext b st A .irr
      obtain ⟨hnoV2, hok2⟩ := ih (acc ++ [.imm .irr]) b fuel env st A Scope hb
        (fun ti hti => hts ti (List.mem_cons_of_mem _ hti)) hst henv hacc1
      refine ⟨hnoV2, fun vs st' B' h2 => ?_⟩
      obtain ⟨hstep2, hvs2, hreach2⟩ := hok2 vs st' B' h2
      refine ⟨hstep2, hvs2, fun u hu l hl => ?_⟩
      rcases hreach2 u hu l hl with hge | ⟨v0, hv0, hrv0⟩ | her | hss | hnum
      · exact Or.inl hge
      · rcases List.mem_append.mp hv0 with hvAcc | hvIrr
        · exact Or.inr (Or.inl ⟨v0, hvAcc, hrv0⟩)
        · simp only [List.mem_singleton] at hvIrr; subst hvIrr; cases hrv0
      · exact Or.inr (Or.inr (Or.inl her))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hss)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hnum)))
    | false =>
      have hunfold : (evalCallArgsS P ext fuel env d ((a, idx) :: rest) acc).run (st, b) =
          (match (evalS P ext fuel env a).run (st, b) with
           | .ok (v, (st₁, B₁)) => (evalCallArgsS P ext fuel env d rest (acc ++ [v])).run (st₁, B₁)
           | .error e => .error e) := by
        conv => lhs; unfold evalCallArgsS
        cases d <;> dsimp only at hsk ⊢
        · simp only [Bool.false_eq_true, ↓reduceIte, MS_bind_run]
          cases (evalS P ext fuel env a).run (st, b) with
          | error _ => rfl
          | ok p => rcases p with ⟨_, ⟨_, _⟩⟩; rfl
        · simp only [hsk, Bool.false_eq_true, ↓reduceIte, MS_bind_run]
          cases (evalS P ext fuel env a).run (st, b) with
          | error _ => rfl
          | ok p => rcases p with ⟨_, ⟨_, _⟩⟩; rfl
      rw [hunfold]
      obtain ⟨hda, hlca, hfva⟩ := hts (a, idx) List.mem_cons_self
      obtain ⟨hnoV1, hok1⟩ := heval b hb fuel env a st A Scope hda hlca hfva hst henv
      cases he1 : (evalS P ext fuel env a).run (st, b) with
      | error e =>
        refine ⟨(fun k hk => by cases hk; exact hnoV1 k he1), (fun _ _ _ h => by cases h)⟩
      | ok p1 =>
        rcases p1 with ⟨v, ⟨st₁, B₁⟩⟩
        obtain ⟨hstep1, hv1, hreach1⟩ := hok1 v st₁ B₁ he1
        have hacc1 : ∀ u ∈ acc ++ [v], DefValOk P ext B₁ st₁ A u := by
          intro u hu
          rcases List.mem_append.mp hu with hu0 | hu1
          · exact hstep1.lift_val (hacc u hu0)
          · simp only [List.mem_singleton] at hu1; subst hu1; exact hv1
        obtain ⟨hnoV2, hok2⟩ := ih (acc ++ [v]) B₁ fuel env st₁ A Scope
          (Nat.le_trans hstep1.1 hb)
          (fun ti hti => hts ti (List.mem_cons_of_mem _ hti))
          hstep1.2.1 (hstep1.lift_env henv) hacc1
        refine ⟨hnoV2, fun vs st' B' h2 => ?_⟩
        obtain ⟨hstep2, hvs2, hreach2⟩ := hok2 vs st' B' h2
        refine ⟨hstep1.trans hstep2, hvs2, fun u hu l hl => ?_⟩
        rcases hreach2 u hu l hl with hge | ⟨v0, hv0, hrv0⟩ | her1 | hss1 | hnum2
        · exact Or.inl (Nat.le_trans hstep1.2.2.1 hge)
        · rcases List.mem_append.mp hv0 with hvAcc | hvNew
          · have hpv0 : PreservesLocs (Reach st.heap v0) st.heap st₁.heap :=
              hstep1.preserves_old.mono fun _ h => (hacc v0 hvAcc).1.1.reach_lt_size h
            exact Or.inr (Or.inl ⟨v0, hvAcc, (Reach_congr hpv0 l).mp hrv0⟩)
          · simp only [List.mem_singleton] at hvNew; subst hvNew
            rcases hreach1 l hrv0 with hge0 | her0 | hss0 | hnum1
            · exact Or.inl hge0
            · exact Or.inr (Or.inr (Or.inl her0))
            · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1))))
        · exact Or.inr (Or.inr (Or.inl (EnvReach_of_preserves_old henv hstep1.preserves_old her1)))
        · rcases hstep1.staticStrFresh l hss1 with hge0 | hss0 | hnum1
          · exact Or.inl hge0
          · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hnum2)))

private theorem cloDefFunOk_step {P : Prog} {ext : ExternOracle} {N : Nat}
    (heval : ∀ b ≤ N, EvalSDefOk P ext b) :
    CloDefFunOk P ext (N + 1) := by
  intro st₀ loc cap env₀ p rc fvs body t ho₀ hpMode hdef hlc hfvsIff hcaps₀
  rw [FunOkAt]
  dsimp only [arrowParts]
  intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc hsh hrf
    hfBase hfOpen hfCf haBase haOpen haCf _ _ _ _ _ _ harg
  cases f with
  | imm _ => cases hloc
  | ref loc' cap' t' =>
    simp only [SameLoc] at hloc
    subst hloc
    cases fuel with
    | zero =>
      simp only [applyOneConformS, MS_bind_run, applyOneS_fuel_zero]
      exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ n =>
      cases B_call with
      | zero =>
        simp only [applyOneConformS, MS_bind_run, applyOneS_budget_zero]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b' =>
        obtain ⟨o, ho, hcapEq⟩ := hfBase.1.self.1
        obtain ⟨o₂, ho₂, hcs⟩ := hsh loc ⟨.clo env₀ p .shared rc fvs body, cap⟩ .here ho₀
        rw [ho] at ho₂; cases ho₂
        cases hcell : o.cell with
        | ctor _ _ | num _ | str _ | pap _ _ | once _ _ =>
          rw [hcell] at hcs; cases hcs
        | clo env p' res' rc' fvs' body' =>
          rw [hcell] at hcs
          obtain ⟨rfl, rfl, rfl, rfl, rfl, hlenEq, henvSh⟩ := hcs
          -- Extract `DefValOk` for `a` and all captured bindings of `env` under `A' := (aRegs ++ fRegs).filter (· < st.nextRegion)`.
          let A' : List Nat := (aRegs ++ fRegs).filter (· < st.nextRegion)
          have hA'Sub : ∀ x ∈ A', x ∈ aRegs ++ fRegs := fun x hx => (List.mem_filter.mp hx).1
          have hA'Lt : ∀ x ∈ A', x < st.nextRegion := fun x hx =>
            of_decide_eq_true (List.mem_filter.mp hx).2
          obtain ⟨_, hargPlain, _, _⟩ := harg (by decide)
          obtain ⟨haNo, _, _, haFun⟩ := hargPlain (by decide)
          have haOk : DefValOk P ext b' st A' a :=
            (DefValOk.mono (Nat.le_succ _) ⟨haBase, haOpen.mono (fun _ h => List.mem_append_left _ h), haNo, haCf, haFun⟩).filter_lt
          have henvOk : DefEnvOk P ext b' st A' (fun i => i ∈ fvs.toList) env := by
            intro i bd hi hget
            obtain ⟨bd₀, hget₀, hm₀, hb₀, hno₀, hcf₀, hfun₀⟩ := hcaps₀ i hi
            have hshI := henvSh i
            rw [hget₀, hget] at hshI
            obtain ⟨hmEq, hvsh⟩ := hshI
            have hmemVal : bd.val ∈ o.cell.vals := by
              rw [hcell]; simp only [Cell.vals, List.mem_filterMap]
              exact ⟨i, hi, by rw [hget]; rfl⟩
            have hheldF : HeldBy st.heap (.ref loc cap' t') bd.val := HeldBy_of_mem_vals ho hmemVal
            have hmemVal₀ : bd₀.val ∈ (Obj.mk (.clo env₀ p .shared rc fvs body) cap).cell.vals := by
              simp only [Cell.vals, List.mem_filterMap]
              exact ⟨i, hi, by rw [hget₀]; rfl⟩
            have hshBd : SameShapeOn (Reach st₀.heap bd₀.val) st₀.heap st.heap :=
              hsh.mono fun x hx => .step ho₀ hmemVal₀ hx
            have hlocBd : SameLoc bd₀.val bd.val := SameLoc.of_valSameShape hvsh
            refine ⟨hmEq.symm.trans hm₀, ?_⟩
            exact (DefValOk_of_sameShape (A₁ := st₀.regions)
              (Nat.le_trans (Nat.le_succ _) (Nat.le_trans hB (Nat.le_succ _)))
              hlocBd hshBd hrf (hfBase.sub hheldF)
              ((hfOpen.sub hheldF).mono (fun _ h => List.mem_append_right _ h))
              ⟨hb₀, (fun _ _ _ _ hopen => hopen), hno₀, hcf₀, hfun₀⟩).filter_lt
          -- Unfold `applyOneConformS` through `openRegion` and `bindAt`.
          let s := st.nextRegion
          let cur := st.regions.headD 0
          let st₁ : St := { st with nextRegion := s + 1, regions := s :: st.regions }
          have hst₁ : StOk P ext b' st₁ := StOk_openRegion (StOk_mono (Nat.le_succ _) hst)
          have hstepBase : (applyOneConformS P ext (n + 1) (.ref loc cap' t') a c).run (st, b' + 1) =
              (match (bindAt P n s .many p.cls a).run st₁ with
               | .error e => .error e
               | .ok (b, st₂) =>
                 match (evalS P ext n (b :: env) body).run (st₂, b') with
                 | .error e => .error e
                 | .ok (r, (st₃, B₃)) =>
                   match (ret P n s cur .shared rc r).run st₃ with
                   | .error e => .error e
                   | .ok (r', st₄) =>
                     let st₅ := { st₄ with regions := st₄.regions.filter (· != s) }
                     match (conform c r').run st₅ with
                     | .error e => .error e
                     | .ok (g, st₆) =>
                       match (conform c g).run st₆ with
                       | .error e => .error e
                       | .ok (rv, st₇) => .ok (rv, (st₇, B₃))) := by
            unfold applyOneConformS
            rw [MS_bind_run, applyOneS, MS_bind_run, MS_spend_succ]; dsimp only
            rw [MS_bind_run, MS_liftM_run, obj_ok ho]; dsimp only
            have hcapBeq : (o.cap == cap') = true := by rw [hcapEq]; simp
            simp only [hcapBeq, ↓reduceIte, hcell]
            rw [MS_bind_run, MS_liftM_run]
            have hopen : openRegion.run st = .ok ((s, cur), st₁) := rfl
            rw [hopen]; dsimp only
            rw [MS_bind_run, MS_liftM_run, hpMode]
            cases hbRun : (bindAt P n s .many p.cls a).run st₁ with
            | error e => rfl
            | ok p₂ =>
              rcases p₂ with ⟨bnd, st₂⟩; dsimp only
              rw [MS_bind_run]
              cases hev : (evalS P ext n (bnd :: env) body).run (st₂, b') with
              | error e => rfl
              | ok p₃ =>
                rcases p₃ with ⟨r, ⟨st₃, B₃⟩⟩; dsimp only
                rw [MS_bind_run, MS_liftM_run]
                cases hret : (ret P n s cur .shared rc r).run st₃ with
                | error e => rfl
                | ok p₄ =>
                  rcases p₄ with ⟨r', st₄⟩; dsimp only
                  rw [MS_bind_run, MS_liftM_run]
                  have hclsR : (closeRegion s).run st₄ = .ok ((), { st₄ with regions := st₄.regions.filter (· != s) }) := rfl
                  rw [hclsR]; dsimp only
                  rw [MS_liftM_run]
                  cases hc1 : (conform c r').run { st₄ with regions := st₄.regions.filter (· != s) } with
                  | error e => rfl
                  | ok p₆ =>
                    rcases p₆ with ⟨g, st₆⟩; dsimp only
                    rw [MS_liftM_run]
                    cases hc2 : (conform c g).run st₆ <;> rfl
          rw [hstepBase]
          rcases bindAt_default_sound (P := P) (ext := ext) (B := b') (fuel := n) (s := s)
              (c := p.cls) hst₁ (Nat.lt_succ_self s) haOk.openRegion with hSt | hOOF |
            ⟨bnd, st₂, hbindRun, hbm, hstep12, hbv2, hreachBind⟩
          · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hbindRun]; dsimp only
            have henv2 : DefEnvOk P ext b' st₂ A' (shiftScope (fun i => i ∈ fvs.toList)) (bnd :: env) :=
              (hstep12.lift_env (henvOk.preserve_old (st := st) (Nat.le_refl _) (PreservesLocs.refl _ _) (RegsFuture.openRegion st))).cons hbm hbv2
            have hscopeBody : ∀ x, FreeVarIn 0 body x → shiftScope (fun i => i ∈ fvs.toList) x :=
              shiftScope_of_freeVarIn (fun x hx => (hfvsIff x).mpr hx)
            obtain ⟨hnoVEv, hokEv⟩ := heval b' (by omega) n (bnd :: env) body st₂ A'
              (shiftScope (fun i => i ∈ fvs.toList)) hdef hlc hscopeBody hstep12.2.1 henv2
            cases hev : (evalS P ext n (bnd :: env) body).run (st₂, b') with
            | error e =>
              refine ⟨(fun k hk => by cases hk; exact hnoVEv k hev), (fun _ _ _ h => by cases h)⟩
            | ok p₃ =>
              rcases p₃ with ⟨r, ⟨st₃, B₃⟩⟩; dsimp only
              obtain ⟨hstep23, hr3, hreachEv⟩ := hokEv r st₃ B₃ hev
              have hstep13 : DefStep P ext b' B₃ st₁ st₃ := hstep12.trans hstep23
              have hcurLt : cur < st₃.nextRegion := by
                have hcur0 : cur < s := by
                  dsimp only [cur]
                  cases hrg : st.regions with
                  | nil => exact hst.2.1.1
                  | cons r0 rs => exact (hst.2.1.2.2 r0 (by rw [hrg]; exact List.mem_cons_self)).2
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hcur0) hstep13.2.2.2.2.2.1
              have hopenS : OpenUnder [s] [] r :=
                (openUnder_singleton_of_deepOpenUnder_lt (hstep13.2.2.2.2.1 ▸ hr3.2.1) hA'Lt).1
              rcases ret_default_sound (P := P) (ext := ext) (B := B₃) (fuel := n) (s := s) (cur := cur)
                  (c := rc) hstep13.2.1 hcurLt hr3 hopenS with hStR | hOOFR |
                ⟨r', st₄, hretRun, hstep34, _, hr4, hreachRet⟩
              · rw [hStR]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              · rw [hOOFR]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              · rw [hretRun]; dsimp only
                have hstep14 : DefStep P ext b' B₃ st₁ st₄ := hstep13.trans hstep34
                let st₅ : St := { st₄ with regions := st₄.regions.filter (· != s) }
                have hstep05 : DefStep P ext (b' + 1) B₃ st st₅ :=
                  (hstep14.open_close hst.2.1).dec_in (Nat.le_succ _)
                have hr5 : DefValOk P ext B₃ st₅ A' r' := hr4.closeRegion s
                rcases conform_default_sound hstep05.2.1 hr5 with hStC1 |
                  ⟨g, st₆, hc1Run, hstep56, _, hg6, hreachC1⟩
                · rw [hStC1]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                · rw [hc1Run]; dsimp only
                  rcases conform_default_sound hstep56.2.1 hg6 with hStC2 |
                    ⟨rv, st₇, hc2Run, hstep67, hclsRv, hrv7, hreachC2⟩
                  · rw [hStC2]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                  · rw [hc2Run]; dsimp only
                    have hstep07 : DefStep P ext (b' + 1) B₃ st st₇ :=
                      (hstep05.trans hstep56).trans hstep67
                    have hdouRes : DeepOpenUnder st₇.heap st₇.regions
                        (applyResultRegs st .shared c fRegs aRegs) rv := by
                      have hregEq : st₇.regions = st.regions := hstep07.2.2.2.2.1
                      have h1 := deepOpenUnder_applyResultRegs_shared (h := st₇.heap) (rs := st₇.regions)
                        hA'Sub hclsRv hrv7.2.1
                      simpa [applyResultRegs, hregEq] using h1
                    refine ⟨(fun _ h => by cases h), fun rv' st' B' hok => ?_⟩
                    cases hok
                    refine ⟨hstep07.1, hstep07.2.1, hstep07.2.2.1, hstep07.2.2.2.1,
                      hstep07.2.2.2.2.1, hstep07.2.2.2.2.2.1, hstep07.2.2.2.2.2.2.1,
                      hstep07.2.2.2.2.2.2.2.1, hstep07.preserves_old.mono hFlt,
                      hstep07.2.2.2.2.2.2.2.2.2.1, hstep07.staticStrFresh,
                      hrv7.1, hclsRv, hdouRes, hrv7.2.2.2.1, ?_,
                      ⟨(fun _ => ⟨hrv7.2.2.1, hrv7.2.2.2.2⟩), (fun ht => by simp [BinderMode.isUnique, BinderMode.usage] at ht)⟩,
                      (fun h => by cases h.1)⟩
                    -- Reachability bound for `rv`
                    intro l hl7
                    have hstep57 : DefStep P ext B₃ B₃ st₅ st₇ := hstep56.trans hstep67
                    have hpres37 : PreservesLocs (fun l => l < st₃.heap.objs.size) st₃.heap st₇.heap :=
                      PreservesLocs.trans hstep34.preserves_old
                        (hstep57.preserves_old.mono fun _ h => Nat.lt_of_lt_of_le h hstep34.2.2.1)
                    have hliftNum37 : ∀ x, NumLoc st₃.heap x → NumLoc st₇.heap x := by
                      intro x ⟨o3, n3, ho3, hc3⟩
                      exact ⟨o3, n3, (hpres37 x (Array.getElem?_eq_some_iff.mp ho3).1).trans ho3, hc3⟩
                    rcases hreachC2 l hl7 with hge6 | hl6
                    · exact Or.inl (Nat.le_trans (Nat.le_trans hstep05.2.2.1 hstep56.2.2.1) hge6)
                    · rcases hreachC1 l hl6 with hge5 | hl5
                      · exact Or.inl (Nat.le_trans hstep05.2.2.1 hge5)
                      · rcases hreachRet l hl5 with hge3 | hl3
                        · exact Or.inl (Nat.le_trans hstep13.2.2.1 hge3)
                        · rcases hreachEv l hl3 with hge2 | her2 | hss2 | hnum3
                          · exact Or.inl (Nat.le_trans hstep12.2.2.1 hge2)
                          · rcases EnvReach_cons her2 with hrbnd | herEnv
                            · rcases hreachBind l hrbnd with hge1 | hra
                              · exact Or.inl hge1
                              · exact Or.inr (Or.inr (Or.inl hra))
                            · have henvSt₁ : DefEnvOk P ext b' st₁ A' (fun i => i ∈ fvs.toList) env :=
                                henvOk.preserve_old (st := st) (Nat.le_refl _) (PreservesLocs.refl _ _) (RegsFuture.openRegion st)
                              obtain ⟨i, bd, hi, hget, hrbd⟩ := EnvReach_of_preserves_old henvSt₁
                                hstep12.preserves_old herEnv
                              have hmemV : bd.val ∈ o.cell.vals := by
                                rw [hcell]; simp only [Cell.vals, List.mem_filterMap]
                                exact ⟨i, hi, by rw [hget]; rfl⟩
                              exact Or.inr (Or.inl (.step ho hmemV hrbd))
                          · rcases hstep12.staticStrFresh l hss2 with hge1 | hss1 | hnum2
                            · exact Or.inl hge1
                            · exact Or.inr (Or.inr (Or.inr (Or.inl hss1)))
                            · exact Or.inr (Or.inr (Or.inr (Or.inr (hliftNum37 l (hstep23.lift_numLoc hnum2)))))
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (hliftNum37 l hnum3))))

private theorem papDefFunOk_step {P : Prog} {ext : ExternOracle} {N : Nat}
    (hcall : ∀ b ≤ N, CallWithSDefOk P ext b) :
    PapDefFunOk P ext (N + 1) := by
  intro st₀ loc cap r args t ho₀ hdef hargs₀
  rw [FunOkAt]
  dsimp only [arrowParts]
  intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc hsh hrf
    hfBase hfOpen hfCf haBase haOpen haCf _ _ _ _ _ _ harg
  cases f with
  | imm _ => cases hloc
  | ref loc' cap' t' =>
    simp only [SameLoc] at hloc
    subst hloc
    cases fuel with
    | zero =>
      simp only [applyOneConformS, MS_bind_run, applyOneS_fuel_zero]
      exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ n =>
      cases B_call with
      | zero =>
        simp only [applyOneConformS, MS_bind_run, applyOneS_budget_zero]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b' =>
        obtain ⟨o, ho, hcapEq⟩ := hfBase.1.self.1
        obtain ⟨o₂, ho₂, hcs⟩ := hsh loc ⟨.pap r args, cap⟩ .here ho₀
        rw [ho] at ho₂; cases ho₂
        cases hcell : o.cell with
        | ctor _ _ | num _ | str _ | clo _ _ _ _ _ _ | once _ _ =>
          rw [hcell] at hcs; cases hcs
        | pap r' args' =>
          rw [hcell] at hcs
          obtain ⟨rfl, hszEq, hargSh⟩ := hcs
          let A' : List Nat := aRegs ++ fRegs
          obtain ⟨_, hargPlain, _, _⟩ := harg (by decide)
          obtain ⟨haNo, _, _, haFun⟩ := hargPlain (by decide)
          have haOk : DefValOk P ext b' st A' a :=
            DefValOk.mono (Nat.le_succ _)
              ⟨haBase, haOpen.mono (fun _ h => List.mem_append_left _ h), haNo, haCf, haFun⟩
          have hargsOk : ∀ w ∈ args'.toList, DefValOk P ext b' st A' w ∧ ∀ l, Reach st.heap w l → Reach st.heap (.ref loc cap' t') l := by
            intro w hw
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
            have hi' : i < args'.size := by simpa using hi
            have hi₀ : i < args.size := hszEq ▸ hi'
            have hmem₀ : args[i] ∈ args.toList := Array.mem_toList_iff.mpr (Array.getElem_mem hi₀)
            obtain ⟨hb₀, hno₀, hcf₀, hfun₀⟩ := hargs₀ args[i] hmem₀
            have hvsh := hargSh i hi₀ hi'
            have hmemVal : args'[i] ∈ o.cell.vals := by
              rw [hcell]; exact Array.mem_toList_iff.mpr (Array.getElem_mem hi')
            have hheldF : HeldBy st.heap (.ref loc cap' t') args'[i] := HeldBy_of_mem_vals ho hmemVal
            have hshW : SameShapeOn (Reach st₀.heap args[i]) st₀.heap st.heap :=
              hsh.mono fun x hx => .step ho₀ (by simp [Cell.vals, hmem₀]) hx
            rw [Array.getElem_toList]
            refine ⟨DefValOk_of_sameShape (A₁ := st₀.regions)
              (Nat.le_trans (Nat.le_succ _) (Nat.le_trans hB (Nat.le_succ _)))
              (SameLoc.of_valSameShape hvsh) hshW hrf (hfBase.sub hheldF)
              ((hfOpen.sub hheldF).mono (fun _ h => List.mem_append_right _ h))
              ⟨hb₀, (fun _ _ _ _ hopen => hopen), hno₀, hcf₀, hfun₀⟩,
              fun l hl => .step ho hmemVal hl⟩
          have hvsOk : ∀ v ∈ args'.toList ++ [a], DefValOk P ext b' st A' v := by
            intro v hv
            rcases List.mem_append.mp hv with hv1 | hv2
            · exact (hargsOk v hv1).1
            · simp only [List.mem_singleton] at hv2; subst hv2; exact haOk
          have hunfold : (applyOneConformS P ext (n + 1) (.ref loc cap' t') a c).run (st, b' + 1) =
              (match (callWithS P ext n r (args'.toList ++ [a]) c).run (st, b') with
               | .error e => .error e
               | .ok (g, (st₁, B₁)) =>
                 match (conform c g).run st₁ with
                 | .error e => .error e
                 | .ok (rv, st₂) => .ok (rv, (st₂, B₁))) := by
            unfold applyOneConformS
            rw [MS_bind_run, applyOneS, MS_bind_run, MS_spend_succ]; dsimp only
            rw [MS_bind_run, MS_liftM_run, obj_ok ho]; dsimp only
            have hcapBeq : (o.cap == cap') = true := by rw [hcapEq]; simp
            simp only [hcapBeq, ↓reduceIte, hcell]
            cases (callWithS P ext n r (args'.toList ++ [a]) c).run (st, b') with
            | error e => rfl
            | ok p1 =>
              rcases p1 with ⟨g, ⟨st₁, B₁⟩⟩; dsimp only
              rw [MS_liftM_run]
              cases (conform c g).run st₁ <;> rfl
          rw [hunfold]
          obtain ⟨hnoVC, hokC⟩ := hcall b' (by omega) n r (args'.toList ++ [a]) c st A'
            hdef (StOk_mono (Nat.le_succ _) hst) hvsOk
          cases hcRun : (callWithS P ext n r (args'.toList ++ [a]) c).run (st, b') with
          | error e =>
            refine ⟨(fun k hk => by cases hk; exact hnoVC k hcRun), (fun _ _ _ h => by cases h)⟩
          | ok p1 =>
            rcases p1 with ⟨g, ⟨st₁, B₁⟩⟩; dsimp only
            obtain ⟨hstep1, hg1, hreach1⟩ := hokC g st₁ B₁ hcRun
            rcases conform_default_sound hstep1.2.1 hg1 with hSt2 |
              ⟨rv, st₂, hc2Run, hstep2, hcls2, hrv2, hreach2⟩
            · rw [hSt2]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hc2Run]; dsimp only
              have hstep02 : DefStep P ext (b' + 1) B₁ st st₂ :=
                (hstep1.dec_in (Nat.le_succ _)).trans hstep2
              have hdouRes : DeepOpenUnder st₂.heap st₂.regions
                  (applyResultRegs st .shared c fRegs aRegs) rv := by
                have hregEq : st₂.regions = st.regions := hstep02.2.2.2.2.1
                have h1 := deepOpenUnder_applyResultRegs_shared (h := st₂.heap) (rs := st₂.regions)
                  (fun _ h => h) hcls2 hrv2.2.1
                simpa [applyResultRegs, hregEq] using h1
              refine ⟨(fun _ h => by cases h), fun rv' st' B' hok => ?_⟩
              cases hok
              refine ⟨hstep02.1, hstep02.2.1, hstep02.2.2.1, hstep02.2.2.2.1,
                hstep02.2.2.2.2.1, hstep02.2.2.2.2.2.1, hstep02.2.2.2.2.2.2.1,
                hstep02.2.2.2.2.2.2.2.1, hstep02.preserves_old.mono hFlt,
                hstep02.2.2.2.2.2.2.2.2.2.1, hstep02.staticStrFresh,
                hrv2.1, hcls2, hdouRes, hrv2.2.2.2.1, ?_,
                ⟨(fun _ => ⟨hrv2.2.2.1, hrv2.2.2.2.2⟩), (fun ht => by simp [BinderMode.isUnique, BinderMode.usage] at ht)⟩,
                (fun h => by cases h.1)⟩
              intro l hl2
              rcases hreach2 l hl2 with hge1 | hl1
              · exact Or.inl (Nat.le_trans hstep1.2.2.1 hge1)
              · rcases hreach1 l hl1 with hge0 | ⟨v, hv, hrv⟩ | hss0 | hnum1
                · exact Or.inl hge0
                · rcases List.mem_append.mp hv with hvArg | hvA
                  · exact Or.inr (Or.inl ((hargsOk v hvArg).2 l hrv))
                  · simp only [List.mem_singleton] at hvA; subst hvA
                    exact Or.inr (Or.inr (Or.inl hrv))
                · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1))))

private theorem applyAllS_step {P : Prog} {ext : ExternOracle} {N : Nat}
    (hall : ∀ b ≤ N, ApplyAllSDefOk P ext b) :
    ApplyAllSDefOk P ext (N + 1) := by
  intro fuel f vs c st A hst hf hvs
  cases fuel with
  | zero =>
    have h0 : (applyAllS P ext 0 f vs c).run (st, N + 1) = .error .outOfFuel := by
      unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; rfl
    rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n =>
    cases vs with
    | nil =>
      have hnil : (applyAllS P ext (n + 1) f [] c).run (st, N + 1) =
          (match (conform c f).run st with
           | .ok (rv, st') => .ok (rv, (st', N))
           | .error e => .error e) := by
        unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [MS_liftM_run]
        cases (conform c f).run st <;> rfl
      rw [hnil]
      rcases conform_default_sound (StOk_mono (Nat.le_succ _) hst) (hf.mono (Nat.le_succ _)) with hSt |
        ⟨rv, st', hrun, hstep, hcls, hrv, hreach⟩
      · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · rw [hrun]
        refine ⟨(fun _ h => by cases h), fun rv' st'' B' hok => ?_⟩
        cases hok
        exact ⟨hstep.dec_in (Nat.le_succ _), hcls, hrv, fun l hl =>
          (hreach l hl).imp id (fun hr => Or.inl hr)⟩
    | cons a rest =>
      have haOk := hvs a List.mem_cons_self
      -- Instantiate `f`'s `FunOkAt` at `B_call := N`, `Frame := (· < st.heap.objs.size)`, `fRegs := A`, `aRegs := A`.
      have hFunAt := hf.2.2.2.2
      rw [FunOkAt] at hFunAt
      dsimp only [arrowParts] at hFunAt
      have hCallInst : ∀ cStep,
          (∀ k, (applyOneConformS P ext n f a cStep).run (st, N) ≠ .error (.violation k)) ∧
          ∀ rv st' B',
            (applyOneConformS P ext n f a cStep).run (st, N) = .ok (rv, (st', B')) →
              DefStep P ext N B' st st' ∧
              ClsSafe st'.heap cStep rv ∧
              DefValOk P ext B' st' A rv ∧
              ∀ l, Reach st'.heap rv l →
                st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨ Reach st.heap a l ∨
                StaticStrLoc st l ∨ NumLoc st'.heap l := by
        intro cStep
        obtain ⟨hnoV, hok⟩ := hFunAt N n st f a cStep (fun l => l < st.heap.objs.size) A A false (fun _ => False)
          (Nat.le_refl _) (StOk_mono (Nat.le_succ _) hst) (fun _ h => StOk_staticStrLoc_lt hst h)
          (fun _ h => h) (SameLoc.refl f) (SameShapeOn.refl _ _) (RegsFuture.refl st)
          hf.1 hf.2.1 (CtorFieldsOk_mono (Nat.le_succ _) hf.2.2.2.1)
          haOk.1 haOk.2.1 (CtorFieldsOk_mono (Nat.le_succ _) haOk.2.2.2.1)
          (fun _ _ h => False.elim h) (fun _ _ h => False.elim h) (fun _ h => False.elim h)
          (fun _ _ h => False.elim h) (fun _ _ h => False.elim h) ⟨fun _ h => False.elim h, fun h => by cases h⟩
          (fun _ => ⟨(fun h => by cases h),
            (fun _ => ⟨haOk.2.2.1, rfl, fun _ h => h, FunOkAt_mono (Nat.le_succ _) haOk.2.2.2.2⟩),
            (fun h => by cases h), (fun h => by cases h.1)⟩)
        refine ⟨hnoV, fun rv st' B' hr => ?_⟩
        obtain ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf,
          hbase, hcls, hopen, hcf, hrb, ⟨hroF, _⟩, _⟩ := hok rv st' B' hr
        obtain ⟨hnoRv, hfunRv⟩ := hroF (by simp [BinderMode.isUnique, BinderMode.usage])
        have hopenA : DeepOpenUnder st'.heap st'.regions A rv := by
          refine hopen.mono (fun x hx => ?_)
          cases cStep with
          | val =>
            simp only [applyResultRegs, show (Cls.val != Cls.val) = false from rfl,
              Bool.false_eq_true, ↓reduceIte, List.mem_append] at hx
            rcases hx with h | h <;> exact h
          | irr | imm | leaf =>
            simp only [applyResultRegs] at hx
            first
            | (simp only [show (Cls.irr != Cls.val) = true from rfl, ↓reduceIte] at hx; cases hx)
            | (simp only [show (Cls.imm != Cls.val) = true from rfl, ↓reduceIte] at hx; cases hx)
            | (simp only [show (Cls.leaf != Cls.val) = true from rfl, ↓reduceIte] at hx; cases hx)
        exact ⟨⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf⟩,
          hcls, ⟨hbase, hopenA, hnoRv, hcf, hfunRv⟩, hrb⟩
      cases rest with
      | nil =>
        have hcons : (applyAllS P ext (n + 1) f [a] c).run (st, N + 1) =
            (match (applyOneS P ext n f a c).run (st, N) with
             | .error e => .error e
             | .ok (g, (st₁, B₁)) => (applyAllS P ext n g [] c).run (st₁, B₁)) := by
          conv => lhs; unfold applyAllS
          rw [MS_bind_run, MS_spend_succ]; dsimp only
          simp only [List.isEmpty_nil, ↓reduceIte]
          rw [MS_bind_run]
          cases (applyOneS P ext n f a c).run (st, N) with
          | error _ => rfl
          | ok p => rcases p with ⟨_, ⟨_, _⟩⟩; rfl
        rw [hcons]
        obtain ⟨hnoV, hok⟩ := hCallInst c
        cases h1 : (applyOneS P ext n f a c).run (st, N) with
        | error e =>
          refine ⟨(fun k hk => by cases hk; exact hnoV k (by unfold applyOneConformS; rw [MS_bind_run, h1])),
            (fun _ _ _ h => by cases h)⟩
        | ok p1 =>
          rcases p1 with ⟨g, ⟨st₁, B₁⟩⟩; dsimp only
          cases n with
          | zero =>
            rw [applyOneS_fuel_zero] at h1; cases h1
          | succ m =>
            cases B₁ with
            | zero =>
              have h0 : (applyAllS P ext (m + 1) g [] c).run (st₁, 0) = .error .outOfFuel := by
                unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
              rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            | succ B₂ =>
              have htail : (applyAllS P ext (m + 1) g [] c).run (st₁, B₂ + 1) =
                  (match (conform c g).run st₁ with
                   | .ok (rv, st₂) => .ok (rv, (st₂, B₂))
                   | .error e => .error e) := by
                unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [MS_liftM_run]
                cases (conform c g).run st₁ <;> rfl
              rw [htail]
              cases hcRun : (conform c g).run st₁ with
              | error e =>
                refine ⟨(fun k hk => by
                  cases hk
                  exact hnoV k (by unfold applyOneConformS; rw [MS_bind_run, h1]; dsimp only; rw [MS_liftM_run, hcRun])),
                  (fun _ _ _ h => by cases h)⟩
              | ok p2 =>
                rcases p2 with ⟨rv, st₂⟩; dsimp only
                have hcomb : (applyOneConformS P ext (m + 1) f a c).run (st, N) = .ok (rv, (st₂, B₂ + 1)) := by
                  unfold applyOneConformS; rw [MS_bind_run, h1]; dsimp only; rw [MS_liftM_run, hcRun]
                obtain ⟨hstep, hcls, hrv, hrb⟩ := hok rv st₂ (B₂ + 1) hcomb
                refine ⟨(fun _ h => by cases h), fun rv' st' B' h2 => ?_⟩
                cases h2
                refine ⟨(hstep.dec_in (Nat.le_succ _)).dec_out (Nat.le_succ _), hcls,
                  hrv.mono (Nat.le_succ _), fun l hl => ?_⟩
                rcases hrb l hl with hge | hrf | hra | hss | hnum
                · exact Or.inl hge
                · exact Or.inr (Or.inl hrf)
                · exact Or.inr (Or.inr (Or.inl ⟨a, List.mem_cons_self, hra⟩))
                · exact Or.inr (Or.inr (Or.inr (Or.inl hss)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr hnum)))
      | cons a2 rest' =>
        have hcons : (applyAllS P ext (n + 1) f (a :: a2 :: rest') c).run (st, N + 1) =
            (match (applyOneS P ext n f a .val).run (st, N) with
             | .error e => .error e
             | .ok (g, (st₁, B₁)) => (applyAllS P ext n g (a2 :: rest') c).run (st₁, B₁)) := by
          conv => lhs; unfold applyAllS
          rw [MS_bind_run, MS_spend_succ]; dsimp only
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
          rw [MS_bind_run]
          cases (applyOneS P ext n f a .val).run (st, N) with
          | error _ => rfl
          | ok p => rcases p with ⟨_, ⟨_, _⟩⟩; rfl
        rw [hcons]
        obtain ⟨hnoV, hok⟩ := hCallInst .val
        cases h1 : (applyOneS P ext n f a .val).run (st, N) with
        | error e =>
          refine ⟨(fun k hk => by cases hk; exact hnoV k (by rw [applyOneConformS_val_eq]; exact h1)),
            (fun _ _ _ h => by cases h)⟩
        | ok p1 =>
          rcases p1 with ⟨g, ⟨st₁, B₁⟩⟩; dsimp only
          obtain ⟨hstep1, _, hg1, hrb1⟩ := hok g st₁ B₁ (by rw [applyOneConformS_val_eq]; exact h1)
          have hrestOk : ∀ v ∈ a2 :: rest', DefValOk P ext B₁ st₁ A v :=
            fun v hv => hstep1.lift_val ((hvs v (List.mem_cons_of_mem _ hv)).mono (Nat.le_succ _))
          obtain ⟨hnoV2, hok2⟩ := hall B₁ hstep1.1 n g (a2 :: rest') c st₁ A hstep1.2.1 hg1 hrestOk
          refine ⟨hnoV2, fun rv st' B' h2 => ?_⟩
          obtain ⟨hstep2, hcls2, hrv2, hrb2⟩ := hok2 rv st' B' h2
          refine ⟨(hstep1.dec_in (Nat.le_succ _)).trans hstep2, hcls2, hrv2, fun l hl => ?_⟩
          rcases hrb2 l hl with hge1 | hrg1 | ⟨v, hv, hrv1⟩ | hss1 | hnum2
          · exact Or.inl (Nat.le_trans hstep1.2.2.1 hge1)
          · rcases hrb1 l hrg1 with hge0 | hrf0 | hra0 | hss0 | hnum1
            · exact Or.inl hge0
            · exact Or.inr (Or.inl hrf0)
            · exact Or.inr (Or.inr (Or.inl ⟨a, List.mem_cons_self, hra0⟩))
            · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1))))
          · have hv0 := hvs v (List.mem_cons_of_mem _ hv)
            have hpv : PreservesLocs (Reach st.heap v) st.heap st₁.heap :=
              hstep1.preserves_old.mono fun _ h => hv0.1.1.reach_lt_size h
            exact Or.inr (Or.inr (Or.inl ⟨v, List.mem_cons_of_mem _ hv, (Reach_congr hpv l).mp hrv1⟩))
          · rcases hstep1.staticStrFresh l hss1 with hge0 | hss0 | hnum1
            · exact Or.inl hge0
            · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hnum2)))

private theorem applyAltS_step {P : Prog} {ext : ExternOracle} {N : Nat}
    (heval : ∀ b ≤ N, EvalSDefOk P ext b)
    (hall : ∀ b ≤ N, ApplyAllSDefOk P ext b)
    (halt : ∀ b ≤ N, ApplyAltSDefOk P ext b) :
    ApplyAltSDefOk P ext (N + 1) := by
  intro fuel env t args st A Scope hdef hlc hfv hst henv hargs
  cases fuel with
  | zero =>
    have h0 : (applyAltS P ext 0 env t args).run (st, N + 1) = .error .outOfFuel := by
      unfold applyAltS; rw [MS_bind_run, MS_spend_succ]; rfl
    rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n =>
    cases args with
    | nil =>
      have hnil : (applyAltS P ext (n + 1) env t []).run (st, N + 1) =
          (evalS P ext n env t).run (st, N) := by
        conv => lhs; unfold applyAltS
        rw [MS_bind_run, MS_spend_succ]
      rw [hnil]
      obtain ⟨hnoV, hok⟩ := heval N (Nat.le_refl _) n env t st A Scope hdef hlc hfv
        (StOk_mono (Nat.le_succ _) hst) (henv.mono (Nat.le_succ _))
      refine ⟨hnoV, fun rv st' B' h => ?_⟩
      obtain ⟨hstep, hrv, hrb⟩ := hok rv st' B' h
      refine ⟨hstep.dec_in (Nat.le_succ _), hrv, fun l hl => ?_⟩
      rcases hrb l hl with h1 | h2 | h3 | h4
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
    | cons ae rest =>
      rcases ae with ⟨a, er⟩
      obtain ⟨herF, haOk⟩ := hargs (a, er) List.mem_cons_self
      subst herF
      have hnonLamBody : ∀ (t0 : Term),
          DefaultTerm P t0 → LamsClosed t0 → (∀ x, FreeVarIn 0 t0 x → Scope x) →
          (applyAltS P ext (n + 1) env t0 ((a, false) :: rest)).run (st, N + 1) =
            (match (evalS P ext n env t0).run (st, N) with
             | .error e => .error e
             | .ok (f, (st₁, B₁)) => (applyAllS P ext n f (((a, false) :: rest).map (·.1)) .val).run (st₁, B₁)) →
          (∀ k, (applyAltS P ext (n + 1) env t0 ((a, false) :: rest)).run (st, N + 1) ≠ .error (.violation k)) ∧
          ∀ rv st' B',
            (applyAltS P ext (n + 1) env t0 ((a, false) :: rest)).run (st, N + 1) = .ok (rv, (st', B')) →
              DefStep P ext (N + 1) B' st st' ∧
              DefValOk P ext B' st' A rv ∧
              ∀ l, Reach st'.heap rv l →
                st.heap.objs.size ≤ l ∨ EnvReach Scope st.heap env l ∨
                (∃ ae ∈ (a, false) :: rest, Reach st.heap ae.1 l) ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
        intro t0 hdef0 hlc0 hfv0 hEq
        rw [hEq]
        obtain ⟨hnoVE, hokE⟩ := heval N (Nat.le_refl _) n env t0 st A Scope hdef0 hlc0 hfv0
          (StOk_mono (Nat.le_succ _) hst) (henv.mono (Nat.le_succ _))
        cases hev : (evalS P ext n env t0).run (st, N) with
        | error e =>
          refine ⟨(fun k hk => by cases hk; exact hnoVE k hev), (fun _ _ _ h => by cases h)⟩
        | ok p1 =>
          rcases p1 with ⟨f, ⟨st₁, B₁⟩⟩; dsimp only
          obtain ⟨hstep1, hf1, hreach1⟩ := hokE f st₁ B₁ hev
          have hmapOk : ∀ v ∈ ((a, false) :: rest).map (·.1), DefValOk P ext B₁ st₁ A v := by
            intro v hv
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
            exact hstep1.lift_val ((hargs q hq).2.mono (Nat.le_succ _))
          obtain ⟨hnoVA, hokA⟩ := hall B₁ hstep1.1 n f (((a, false) :: rest).map (·.1)) .val st₁ A
            hstep1.2.1 hf1 hmapOk
          refine ⟨hnoVA, fun rv st' B' h2 => ?_⟩
          obtain ⟨hstep2, _, hrv2, hreach2⟩ := hokA rv st' B' h2
          refine ⟨(hstep1.dec_in (Nat.le_succ _)).trans hstep2, hrv2, fun l hl => ?_⟩
          rcases hreach2 l hl with hge1 | hrf1 | ⟨v, hv, hrv1⟩ | hss1 | hnum2
          · exact Or.inl (Nat.le_trans hstep1.2.2.1 hge1)
          · rcases hreach1 l hrf1 with hge0 | her0 | hss0 | hnum1
            · exact Or.inl hge0
            · exact Or.inr (Or.inl her0)
            · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1))))
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
            have hpq : PreservesLocs (Reach st.heap q.1) st.heap st₁.heap :=
              hstep1.preserves_old.mono fun _ h => (hargs q hq).2.1.1.reach_lt_size h
            exact Or.inr (Or.inr (Or.inl ⟨q, hq, (Reach_congr hpq l).mp hrv1⟩))
          · rcases hstep1.staticStrFresh l hss1 with hge0 | hss0 | hnum1
            · exact Or.inl hge0
            · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hnum2)))
      have hanyF : (((a, false) :: rest).any (·.2)) = false := by
        cases h : ((a, false) :: rest).any (·.2) with
        | false => rfl
        | true =>
          obtain ⟨q, hq, hq2⟩ := List.any_eq_true.mp h
          exact absurd ((hargs q hq).1) (by rw [hq2]; decide)
      cases t with
      | lam p res rc fvs body =>
        cases hdef with
        | lam hpMode hresEq hdefB =>
          subst hresEq
          cases hlc with
          | lam hlcB _ =>
            let s := st.nextRegion
            let cur := st.regions.headD 0
            let st₁ : St := { st with nextRegion := s + 1, regions := s :: st.regions }
            let A' : List Nat := A.filter (· < s)
            have hA'Sub : ∀ x ∈ A', x ∈ A := fun x hx => (List.mem_filter.mp hx).1
            have hA'Lt : ∀ x ∈ A', x < s := fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2
            have hunfold : (applyAltS P ext (n + 1) env (.lam p .shared rc fvs body) ((a, false) :: rest)).run (st, N + 1) =
                (match (bindAt P n s .many p.cls a).run st₁ with
                 | .error e => .error e
                 | .ok (b, st₂) =>
                   match (applyAltS P ext n (b :: env) body rest).run (st₂, N) with
                   | .error e => .error e
                   | .ok (r, (st₃, B₃)) =>
                     match (ret P n s cur .shared rc r).run st₃ with
                     | .error e => .error e
                     | .ok (r', st₄) => .ok (r', ({ st₄ with regions := st₄.regions.filter (· != s) }, B₃))) := by
              conv => lhs; unfold applyAltS
              rw [MS_bind_run, MS_spend_succ]; dsimp only
              rw [MS_bind_run, MS_liftM_run]
              have hopen : openRegion.run st = .ok ((s, cur), st₁) := rfl
              rw [hopen]; dsimp only
              rw [MS_bind_run, MS_liftM_run, hpMode]
              simp only [Bool.false_eq_true, ↓reduceIte]
              cases (bindAt P n s .many p.cls a).run st₁ with
              | error e => rfl
              | ok p₂ =>
                rcases p₂ with ⟨b, st₂⟩; dsimp only
                rw [MS_bind_run]
                cases (applyAltS P ext n (b :: env) body rest).run (st₂, N) with
                | error e => rfl
                | ok p₃ =>
                  rcases p₃ with ⟨r, ⟨st₃, B₃⟩⟩; dsimp only
                  rw [MS_bind_run, MS_liftM_run]
                  cases (ret P n s cur .shared rc r).run st₃ with
                  | error e => rfl
                  | ok p₄ =>
                    rcases p₄ with ⟨r', st₄⟩; dsimp only
                    rw [MS_bind_run, MS_liftM_run]
                    have hcls : (closeRegion s).run st₄ = .ok ((), { st₄ with regions := st₄.regions.filter (· != s) }) := rfl
                    rw [hcls]; rfl
            rw [hunfold]
            have hst₁ : StOk P ext N st₁ := StOk_openRegion (StOk_mono (Nat.le_succ _) hst)
            have ha₁ : DefValOk P ext N st₁ A' a := (haOk.mono (Nat.le_succ _)).filter_lt.openRegion
            rcases bindAt_default_sound (P := P) (ext := ext) (B := N) (fuel := n) (s := s)
                (c := p.cls) hst₁ (Nat.lt_succ_self s) ha₁ with hSt | hOOF |
              ⟨bnd, st₂, hbindRun, hbm, hstep12, hbv2, hreachBind⟩
            · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hbindRun]; dsimp only
              have henv1 : DefEnvOk P ext N st₁ A' Scope env :=
                (henv.mono (Nat.le_succ _)).filter_lt.preserve_old (st := st) (Nat.le_refl _) (PreservesLocs.refl _ _) (RegsFuture.openRegion st)
              have henv2 : DefEnvOk P ext N st₂ A' (shiftScope Scope) (bnd :: env) :=
                (hstep12.lift_env henv1).cons hbm hbv2
              have hrest2 : ∀ q ∈ rest, q.2 = false ∧ DefValOk P ext N st₂ A' q.1 := by
                intro q hq
                obtain ⟨hef, hqv⟩ := hargs q (List.mem_cons_of_mem _ hq)
                exact ⟨hef, hstep12.lift_val (hqv.mono (Nat.le_succ _)).filter_lt.openRegion⟩
              have hfvBody : ∀ x, FreeVarIn 0 body x → shiftScope Scope x :=
                shiftScope_of_freeVarIn (fun x hx => hfv x (.lam hx))
              obtain ⟨hnoVA, hokA⟩ := halt N (Nat.le_refl _) n (bnd :: env) body rest st₂ A'
                (shiftScope Scope) hdefB hlcB hfvBody hstep12.2.1 henv2 hrest2
              cases haltRun : (applyAltS P ext n (bnd :: env) body rest).run (st₂, N) with
              | error e =>
                refine ⟨(fun k hk => by cases hk; exact hnoVA k haltRun), (fun _ _ _ h => by cases h)⟩
              | ok p₃ =>
                rcases p₃ with ⟨r, ⟨st₃, B₃⟩⟩; dsimp only
                obtain ⟨hstep23, hr3, hreachA⟩ := hokA r st₃ B₃ haltRun
                have hstep13 : DefStep P ext N B₃ st₁ st₃ := hstep12.trans hstep23
                have hcurLt : cur < st₃.nextRegion := by
                  have hcur0 : cur < s := by
                    dsimp only [cur]
                    cases hrg : st.regions with
                    | nil => exact hst.2.1.1
                    | cons r0 rs => exact (hst.2.1.2.2 r0 (by rw [hrg]; exact List.mem_cons_self)).2
                  exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hcur0) hstep13.2.2.2.2.2.1
                have hopenS : OpenUnder [s] [] r :=
                  (openUnder_singleton_of_deepOpenUnder_lt (hstep13.2.2.2.2.1 ▸ hr3.2.1) hA'Lt).1
                rcases ret_default_sound (P := P) (ext := ext) (B := B₃) (fuel := n) (s := s) (cur := cur)
                    (c := rc) hstep13.2.1 hcurLt hr3 hopenS with hStR | hOOFR |
                  ⟨r', st₄, hretRun, hstep34, _, hr4, hreachRet⟩
                · rw [hStR]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                · rw [hOOFR]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                · rw [hretRun]; dsimp only
                  have hstep14 : DefStep P ext N B₃ st₁ st₄ := hstep13.trans hstep34
                  have hstep05 : DefStep P ext (N + 1) B₃ st { st₄ with regions := st₄.regions.filter (· != s) } :=
                    (hstep14.open_close hst.2.1).dec_in (Nat.le_succ _)
                  refine ⟨(fun _ h => by cases h), fun rv st' B' hok => ?_⟩
                  cases hok
                  refine ⟨hstep05, (hr4.closeRegion s).mono_regs hA'Sub, fun l hl4 => ?_⟩
                  rcases hreachRet l hl4 with hge3 | hl3
                  · exact Or.inl (Nat.le_trans hstep13.2.2.1 hge3)
                  · rcases hreachA l hl3 with hge2 | her2 | ⟨q, hq, hrq2⟩ | hss2 | hnum3
                    · exact Or.inl (Nat.le_trans hstep12.2.2.1 hge2)
                    · rcases EnvReach_cons her2 with hrbnd | herEnv
                      · rcases hreachBind l hrbnd with hge1 | hra
                        · exact Or.inl hge1
                        · exact Or.inr (Or.inr (Or.inl ⟨(a, false), List.mem_cons_self, hra⟩))
                      · exact Or.inr (Or.inl (EnvReach_of_preserves_old (st := st₁) henv1 hstep12.preserves_old herEnv))
                    · have hqv := (hargs q (List.mem_cons_of_mem _ hq)).2
                      have hpq : PreservesLocs (Reach st.heap q.1) st.heap st₂.heap :=
                        hstep12.preserves_old.mono fun _ h => hqv.1.1.reach_lt_size h
                      exact Or.inr (Or.inr (Or.inl ⟨q, List.mem_cons_of_mem _ hq, (Reach_congr hpq l).mp hrq2⟩))
                    · rcases hstep12.staticStrFresh l hss2 with hge1 | hss1 | hnum2
                      · exact Or.inl hge1
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hss1)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep34.lift_numLoc (hstep23.lift_numLoc hnum2)))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (hstep34.lift_numLoc hnum3))))
      | irr | var _ _ | natLit _ | strLit _ | const _ _ | app _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ =>
        exact hnonLamBody _ hdef hlc hfv (by
          conv => lhs; unfold applyAltS
          rw [MS_bind_run, MS_spend_succ]; dsimp only
          simp only [hanyF, Bool.false_eq_true, ↓reduceIte]
          rw [MS_bind_run]
          cases (evalS P ext n env _).run (st, N) with
          | error _ => rfl
          | ok p => rcases p with ⟨_, ⟨_, _⟩⟩; rfl)

private theorem callWithS_step {P : Prog} {ext : ExternOracle} {B N : Nat}
    (hext : ExternOk P ext)
    (hih : DefaultCallIH P ext B)
    (hNB : N ≤ B)
    (hall : ∀ b ≤ N, ApplyAllSDefOk P ext b)
    (hpap : ∀ b ≤ N, PapDefFunOk P ext b) :
    CallWithSDefOk P ext (N + 1) := by
  intro fuel r vs c st A hdef hst hvs
  cases fuel with
  | zero =>
    have h0 : (callWithS P ext 0 r vs c).run (st, N + 1) = .error .outOfFuel := by
      unfold callWithS; rw [MS_bind_run, MS_spend_succ]; rfl
    rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n =>
    have hstN : StOk P ext N st := StOk_mono (Nat.le_succ _) hst
    have hvsN : ∀ v ∈ vs, DefValOk P ext N st A v := fun v hv => (hvs v hv).mono (Nat.le_succ _)
    -- Helper for the `makePap` partial-application branches.
    have handlePap : ∀ (params : Array Param),
        (∀ p ∈ params.toList, p.mode = .many) →
        (∀ k, (liftM (makePap P n r params vs) : MS Val).run (st, N) ≠ .error (.violation k)) ∧
        ∀ rv st' B',
          (liftM (makePap P n r params vs) : MS Val).run (st, N) = .ok (rv, (st', B')) →
            DefStep P ext (N + 1) B' st st' ∧
            DefValOk P ext B' st' A rv ∧
            ∀ l, Reach st'.heap rv l →
              st.heap.objs.size ≤ l ∨ (∃ v ∈ vs, Reach st.heap v l) ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
      intro params hpm
      rw [MS_liftM_run]
      rcases makePap_default_sound (P := P) (ext := ext) (B := N) (fuel := n) (r := r)
          (params := params) (vs := vs) hstN hpm hvsN with hOOF |
        ⟨rv, out, cap, st', hrun, hstep, hrvEq, hoNew, hbase', hdou', hno', hcf', houtOk, hreach'⟩
      · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · rw [hrun]
        have hfunPap : FunOkAt P ext N st' .unknown false (fun _ => False) rv := by
          rw [hrvEq]
          exact hpap N (Nat.le_refl _) st' st.heap.objs.size cap r out (taints out.toList)
            hoNew hdef (fun w hw => let h := houtOk w hw; ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)
        refine ⟨(fun _ h => by cases h), fun rv' st'' B' hok => ?_⟩
        cases hok
        exact ⟨hstep.dec_in (Nat.le_succ _), ⟨hbase', hdou', hno', hcf', hfunPap⟩,
          fun l hl => (hreach' l hl).imp (fun heq => by omega) Or.inl⟩
    -- Helper for composing a saturated call returning `(f, (st₁, B₁))` with `applyAllS ... (vs.drop k) c`.
    have handleDrop : ∀ (k : Nat) (f : Val) (st₁ : St) (B₁ : Nat),
        DefStep P ext N B₁ st st₁ →
        DefValOk P ext B₁ st₁ A f →
        (∀ l, Reach st₁.heap f l →
          st.heap.objs.size ≤ l ∨ (∃ v ∈ vs, Reach st.heap v l) ∨ StaticStrLoc st l ∨ NumLoc st₁.heap l) →
        (∀ k', (applyAllS P ext n f (vs.drop k) c).run (st₁, B₁) ≠ .error (.violation k')) ∧
        ∀ rv st' B',
          (applyAllS P ext n f (vs.drop k) c).run (st₁, B₁) = .ok (rv, (st', B')) →
            DefStep P ext (N + 1) B' st st' ∧
            DefValOk P ext B' st' A rv ∧
            ∀ l, Reach st'.heap rv l →
              st.heap.objs.size ≤ l ∨ (∃ v ∈ vs, Reach st.heap v l) ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
      intro k f st₁ B₁ hstep1 hf1 hrf1
      have hdropOk : ∀ v ∈ vs.drop k, DefValOk P ext B₁ st₁ A v :=
        fun v hv => hstep1.lift_val (hvsN v (List.mem_of_mem_drop hv))
      obtain ⟨hnoVA, hokA⟩ := hall B₁ hstep1.1 n f (vs.drop k) c st₁ A hstep1.2.1 hf1 hdropOk
      refine ⟨hnoVA, fun rv st' B' h2 => ?_⟩
      obtain ⟨hstep2, _, hrv2, hrb2⟩ := hokA rv st' B' h2
      refine ⟨(hstep1.dec_in (Nat.le_succ _)).trans hstep2, hrv2, fun l hl => ?_⟩
      rcases hrb2 l hl with hge1 | hrf | ⟨v, hv, hrv1⟩ | hss1 | hnum2
      · exact Or.inl (Nat.le_trans hstep1.2.2.1 hge1)
      · rcases hrf1 l hrf with hge0 | hvs0 | hss0 | hnum1
        · exact Or.inl hge0
        · exact Or.inr (Or.inl hvs0)
        · exact Or.inr (Or.inr (Or.inl hss0))
        · exact Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1)))
      · have hvMem : v ∈ vs := List.mem_of_mem_drop hv
        have hpv : PreservesLocs (Reach st.heap v) st.heap st₁.heap :=
          hstep1.preserves_old.mono fun _ h => (hvs v hvMem).1.1.reach_lt_size h
        exact Or.inr (Or.inl ⟨v, hvMem, (Reach_congr hpv l).mp hrv1⟩)
      · rcases hstep1.staticStrFresh l hss1 with hge0 | hss0 | hnum1
        · exact Or.inl hge0
        · exact Or.inr (Or.inr (Or.inl hss0))
        · exact Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1)))
      · exact Or.inr (Or.inr (Or.inr hnum2))
    have hbase : (callWithS P ext (n + 1) r vs c).run (st, N + 1) =
        (match P.find? r with
         | some (.body params res rc _ body) =>
           if vs.length < params.size then (liftM (makePap P n r params vs)).run (st, N)
           else ((if params.size == 0 then staticS P ext n r body rc
                  else enterS P ext n params res rc body (vs.take params.size)) >>= fun f =>
                 applyAllS P ext n f (vs.drop params.size) c).run (st, N)
         | some (.ctor _ _ nP fields) =>
           if vs.length < nP + fields.size then (liftM (makePap P n r #[] vs)).run (st, N)
           else if vs.length > nP + fields.size then .error .stuck
           else (liftM (construct r fields (vs.drop nP) c)).run (st, N)
         | some (.prim p) =>
           if vs.length < p.arity then (liftM (makePap P n r #[] vs)).run (st, N)
           else if vs.length > p.arity then .error .stuck
           else (liftM (do conform c (← prim p vs))).run (st, N)
         | some (.extern params res rc _) =>
           if vs.length < params.size then (liftM (makePap P n r params vs)).run (st, N)
           else ((liftM (callExtern P ext n r params res rc (vs.take params.size))) >>= fun f =>
                 applyAllS P ext n f (vs.drop params.size) c).run (st, N)
         | some (.ind _) => .ok (.imm .irr, (st, N))
         | _ => .error .stuck) := by
      conv => lhs; unfold callWithS
      rw [MS_bind_run, MS_spend_succ]; dsimp only
      cases P.find? r with
      | none => rfl
      | some d =>
        cases d with
        | body params res rc _ body =>
          by_cases h1 : vs.length < params.size
          · simp only [h1, ↓reduceIte]
          · simp only [h1, ↓reduceIte]
            cases (params.size == 0) <;> rfl
        | ctor _ _ nP fields =>
          by_cases h1 : vs.length < nP + fields.size
          · simp only [h1, ↓reduceIte]
          · simp only [h1, ↓reduceIte]
            by_cases h2 : vs.length > nP + fields.size <;> simp only [h2, ↓reduceIte] <;> rfl
        | prim p =>
          by_cases h1 : vs.length < p.arity
          · simp only [h1, ↓reduceIte]
          · simp only [h1, ↓reduceIte]
            by_cases h2 : vs.length > p.arity <;> simp only [h2, ↓reduceIte] <;> rfl
        | extern params res rc _ =>
          by_cases h1 : vs.length < params.size <;> simp only [h1, ↓reduceIte] <;> rfl
        | ind _ => rfl
        | caseDef _ => rfl
        | stuck _ _ _ _ => rfl
    rw [hbase]
    cases hfind : P.find? r with
    | none => exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | some d =>
      have hdi : DefaultIface d := hdef d hfind
      cases d with
      | body params res rc rs body =>
        obtain ⟨hpmSk, hresEq, hrsDef⟩ := hdi
        by_cases hlt : vs.length < params.size
        · simp only [hlt, ↓reduceIte]
          exact handlePap params (fun p hp => (hpmSk p hp).1)
        · simp only [hlt, ↓reduceIte]
          rw [MS_bind_run]
          by_cases hzero : params.size = 0
          · have hzb : (params.size == 0) = true := by rw [hzero]; rfl
            simp only [hzb, ↓reduceIte]
            have hparamsEmpty : params = #[] := Array.eq_empty_of_size_eq_zero hzero
            subst hparamsEmpty
            obtain ⟨hnoVS, hokS⟩ := hih.2.2 N n r res rc rs body st hNB hfind ⟨hpmSk, hresEq, hrsDef⟩ hstN
            cases hsRun : (staticS P ext n r body rc).run (st, N) with
            | error e =>
              refine ⟨(fun k hk => by cases hk; exact hnoVS k hsRun), (fun _ _ _ h => by cases h)⟩
            | ok p1 =>
              rcases p1 with ⟨f, ⟨st₁, B₁⟩⟩; dsimp only
              obtain ⟨hstep1, _, hf1, hrf1⟩ := hokS f st₁ B₁ hsRun
              exact handleDrop 0 f st₁ B₁ hstep1 (hf1.mono_regs (fun _ h => by cases h))
                (fun l hl => (hrf1 l hl).imp id (fun h => Or.inr h))
          · have hzb : (params.size == 0) = false := beq_false_of_ne hzero
            simp only [hzb, Bool.false_eq_true, ↓reduceIte]
            have htakeLen : (vs.take params.size).length = params.size := by simp; omega
            have htakeOk : ∀ v ∈ vs.take params.size, DefValOk P ext N st A v :=
              fun v hv => hvsN v (List.mem_of_mem_take hv)
            obtain ⟨hnoVE, hokE⟩ := hih.2.1 N n r params res rc rs body (vs.take params.size) st A
              hNB hfind ⟨hpmSk, hresEq, hrsDef⟩ htakeLen hstN htakeOk
            cases heRun : (enterS P ext n params res rc body (vs.take params.size)).run (st, N) with
            | error e =>
              refine ⟨(fun k hk => by cases hk; exact hnoVE k heRun), (fun _ _ _ h => by cases h)⟩
            | ok p1 =>
              rcases p1 with ⟨f, ⟨st₁, B₁⟩⟩; dsimp only
              obtain ⟨hstep1, _, hf1, hrf1⟩ := hokE f st₁ B₁ heRun
              exact handleDrop params.size f st₁ B₁ hstep1 hf1
                (fun l hl => (hrf1 l hl).imp id (fun h => h.imp (fun ⟨v, hv, hr⟩ => ⟨v, List.mem_of_mem_take hv, hr⟩) id))
      | ctor ind ci nP fields =>
        by_cases hlt : vs.length < nP + fields.size
        · simp only [hlt, ↓reduceIte]
          exact handlePap #[] (fun _ h => by simp at h)
        · simp only [hlt, ↓reduceIte]
          by_cases hgt : vs.length > nP + fields.size
          · simp only [hgt, ↓reduceIte]
            exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · simp only [hgt, ↓reduceIte, MS_liftM_run]
            have hdropOk : ∀ (i : Nat) (f : Field) (v : Val),
                fields[i]? = some f → (vs.drop nP)[i]? = some v → f.kept = true →
                ValBaseOk st v ∧ NoOnceCell st.heap v ∧ CtorFieldsOk P ext N st v ∧
                FunOkAt P ext N st .unknown false (fun _ => False) v := by
              intro i f v _ hv _
              have hOk := hvsN v (List.mem_of_mem_drop (List.mem_of_getElem? hv))
              exact ⟨hOk.1, hOk.2.2.1, hOk.2.2.2.1, hOk.2.2.2.2⟩
            rcases construct_sound (P := P) (ext := ext) (B := N) (r := r) (fields := fields)
                (vs := vs.drop nP) (c := c) hstN hdropOk with hSt |
              ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, _, honceSh, hssf, hst',
               hbase', hno', hcf', hfun', hdou', hreach', _, _⟩
            · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hrun]
              refine ⟨(fun _ h => by cases h), fun rv' st'' B' hok => ?_⟩
              cases hok
              have hstep : DefStep P ext (N + 1) N st st' :=
                ⟨Nat.le_succ _, hst', hsz, hcap, hr, hnr ▸ Nat.le_refl _,
                 hstat ▸ ArrayExtends.refl _, hstr ▸ ArrayExtends.refl _, hpres, honceSh, hssf⟩
              have hdouRv : DeepOpenUnder st'.heap st'.regions A rv := by
                rw [hr]
                exact hdou' st.regions A (fun _ _ v _ hv _ => (hvsN v (List.mem_of_mem_drop (List.mem_of_getElem? hv))).2.1)
              refine ⟨hstep, ⟨hbase', hdouRv, hno', hcf', hfun'⟩, fun l hl => ?_⟩
              rcases hreach' l hl with hge | ⟨_, _, v, _, hv, _, hrv⟩
              · exact Or.inl hge
              · exact Or.inr (Or.inl ⟨v, List.mem_of_mem_drop (List.mem_of_getElem? hv), hrv⟩)
      | prim p =>
        by_cases hlt : vs.length < p.arity
        · simp only [hlt, ↓reduceIte]
          exact handlePap #[] (fun _ h => by simp at h)
        · simp only [hlt, ↓reduceIte]
          by_cases hgt : vs.length > p.arity
          · simp only [hgt, ↓reduceIte]
            exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · simp only [hgt, ↓reduceIte, MS_liftM_run]
            rcases prim_sound (P := P) (ext := ext) (B := N) (p := p) (vs := vs) (c := c)
                hstN (fun v hv => (hvsN v hv).1.1.self.1) with hSt |
              ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst',
               hbase', _, hdou', hcf', hno', hfun', _, hreach'⟩
            · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hrun]
              refine ⟨(fun _ h => by cases h), fun rv' st'' B' hok => ?_⟩
              cases hok
              have hstep : DefStep P ext (N + 1) N st st' :=
                ⟨Nat.le_succ _, hst', hsz, hcap, hr, hnr ▸ Nat.le_refl _,
                 hstat ▸ ArrayExtends.refl _, hstr ▸ ArrayExtends.refl _, hpres, honceSh, hssf⟩
              exact ⟨hstep, ⟨hbase', hdou'.mono (fun _ h => by cases h), hno', hcf', hfun'⟩,
                fun l hl => Or.inl (hreach' l hl)⟩
      | extern params res rc rs =>
        obtain ⟨hpmSk, hresEq, hrsDef⟩ := hdi
        subst hresEq
        by_cases hlt : vs.length < params.size
        · simp only [hlt, ↓reduceIte]
          exact handlePap params (fun p hp => (hpmSk p hp).1)
        · simp only [hlt, ↓reduceIte]
          rw [MS_bind_run, MS_liftM_run]
          have hargsExt : ∀ (i : Nat) (p : Param) (v : Val),
              params[i]? = some p → (vs.take params.size)[i]? = some v →
              (p.mode ≠ .erased →
                ValBaseOk st v ∧ DeepOpenUnder st.heap st.regions A v ∧
                NoOnceCell st.heap v ∧ CtorFieldsOk P ext N st v ∧
                FunOkAt P ext N st p.skel false (fun _ => False) v) ∧
              (p.mode.isUnique = true →
                OwnTreeFull P st.heap v ∧
                (∀ l, OwnReach P st.heap v l → ¬ (l < st.heap.objs.size)) ∧
                (p.mode.isBorrowed = false → OpenUnder st.regions [] v)) ∧
              (ResultMode.shared = .unique → rc = .val → p.mode = .many → p.cls ≠ .leaf →
                DeepOpenUnder st.heap st.regions [] v) := by
            intro i p v hp hv
            have ⟨hm, hsk⟩ := hpmSk p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp))
            have hOk := hvsN v (List.mem_of_mem_take (List.mem_of_getElem? hv))
            refine ⟨fun _ => ⟨hOk.1, hOk.2.1, hOk.2.2.1, hOk.2.2.2.1,
              (FunOkAt_default_equiv rfl hsk).mp hOk.2.2.2.2⟩,
              (fun hu => by rw [hm] at hu; cases hu),
              (fun h => by cases h)⟩
          have hdisjExt : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
              params[i]? = some pi → (vs.take params.size)[i]? = some vi →
              params[j]? = some pj → (vs.take params.size)[j]? = some vj →
              pi.mode.isUnique = true → pj.mode ≠ .erased →
              ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l := by
            intro _ _ pi _ _ _ _ hpi _ _ _ hu
            have hm := (hpmSk pi (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hpi))).1
            rw [hm] at hu; cases hu
          obtain ⟨hnoVE, hokE⟩ := callExtern_sound (P := P) (ext := ext) (B := N) (fuel := n)
            (Frame := fun l => l < st.heap.objs.size) (argRegs := A)
            hext hfind hstN (hih.1 N hNB) (fun _ h => StOk_staticStrLoc_lt hstN h) (fun _ h => h)
            hargsExt hdisjExt
          cases heRun : (callExtern P ext n r params .shared rc (vs.take params.size)).run st with
          | error e =>
            refine ⟨(fun k hk => by cases hk; exact hnoVE k heRun), (fun _ _ _ h => by cases h)⟩
          | ok p1 =>
            rcases p1 with ⟨f, st₁⟩; dsimp only
            obtain ⟨hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁, hpres₁, honce₁, hssf₁,
              hbase₁, _, hopen₁, hno₁, hcf₁, hfun₁, hreach₁, _⟩ := hokE f st₁ heRun
            have hstep1 : DefStep P ext N N st st₁ :=
              ⟨Nat.le_refl _, hst₁, hsz₁, hcap₁, hr₁, hnr₁,
               hstat₁ ▸ ArrayExtends.refl _, hstr₁ ▸ ArrayExtends.refl _, hpres₁, honce₁, hssf₁⟩
            have hopenA : DeepOpenUnder st₁.heap st₁.regions A f := by
              refine hopen₁.mono (fun x hx => ?_)
              cases rc with
              | val =>
                simp only [applyResultRegs, show (Cls.val != Cls.val) = false from rfl,
                  Bool.false_eq_true, ↓reduceIte, List.append_nil] at hx
                exact hx
              | irr | imm | leaf =>
                simp only [applyResultRegs] at hx
                first
                | (simp only [show (Cls.irr != Cls.val) = true from rfl, ↓reduceIte] at hx; cases hx)
                | (simp only [show (Cls.imm != Cls.val) = true from rfl, ↓reduceIte] at hx; cases hx)
                | (simp only [show (Cls.leaf != Cls.val) = true from rfl, ↓reduceIte] at hx; cases hx)
            have hf1 : DefValOk P ext N st₁ A f :=
              ⟨hbase₁, hopenA, hno₁, hcf₁, (FunOkAt_default_equiv hrsDef rfl).mp hfun₁⟩
            exact handleDrop params.size f st₁ N hstep1 hf1 (fun l hl => by
              rcases hreach₁ l hl with hge | ⟨_, _, vi, _, hvi, _, hrvi⟩ | hnum
              · exact Or.inl hge
              · exact Or.inr (Or.inl ⟨vi, List.mem_of_mem_take (List.mem_of_getElem? hvi), hrvi⟩)
              · exact Or.inr (Or.inr (Or.inr hnum)))
      | ind _ =>
        refine ⟨(fun _ h => by cases h), fun rv st' B' hok => ?_⟩
        cases hok
        exact ⟨(DefStep.refl hstN).dec_in (Nat.le_succ _), DefValOk_imm P ext N st A .irr,
          fun _ hl => by cases hl⟩
      | caseDef _ | stuck _ _ _ _ =>
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩

private theorem spineS_step {P : Prog} {ext : ExternOracle} {N : Nat}
    (heval : ∀ b ≤ N, EvalSDefOk P ext b)
    (hcall : ∀ b ≤ N, CallWithSDefOk P ext b)
    (hall : ∀ b ≤ N, ApplyAllSDefOk P ext b) :
    SpineSDefOk P ext (N + 1) := by
  intro fuel env head args c st A Scope hdefH hlcH hfvH hargs hst henv
  cases fuel with
  | zero =>
    have h0 : (spineS P ext 0 env head args c).run (st, N + 1) = .error .outOfFuel := by
      unfold spineS; rw [MS_bind_run, MS_spend_succ]; rfl
    rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n =>
    have hstN : StOk P ext N st := StOk_mono (Nat.le_succ _) hst
    have henvN : DefEnvOk P ext N st A Scope env := henv.mono (Nat.le_succ _)
    have hnonConst : ∀ (h0 : Term),
        DefaultTerm P h0 → LamsClosed h0 → (∀ x, FreeVarIn 0 h0 x → Scope x) →
        (spineS P ext (n + 1) env h0 args c).run (st, N + 1) =
          (match (evalS P ext n env h0).run (st, N) with
           | .error e => .error e
           | .ok (f, (st₁, B₁)) =>
             match (evalListS P ext n env args []).run (st₁, B₁) with
             | .error e => .error e
             | .ok (vs, (st₂, B₂)) => (applyAllS P ext n f vs c).run (st₂, B₂)) →
        (∀ k, (spineS P ext (n + 1) env h0 args c).run (st, N + 1) ≠ .error (.violation k)) ∧
        ∀ rv st' B',
          (spineS P ext (n + 1) env h0 args c).run (st, N + 1) = .ok (rv, (st', B')) →
            DefStep P ext (N + 1) B' st st' ∧
            DefValOk P ext B' st' A rv ∧
            ∀ l, Reach st'.heap rv l →
              st.heap.objs.size ≤ l ∨ EnvReach Scope st.heap env l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
      intro h0 hd0 hlc0 hfv0 hEq
      rw [hEq]
      obtain ⟨hnoV1, hok1⟩ := heval N (Nat.le_refl _) n env h0 st A Scope hd0 hlc0 hfv0 hstN henvN
      cases he1 : (evalS P ext n env h0).run (st, N) with
      | error e =>
        refine ⟨(fun k hk => by cases hk; exact hnoV1 k he1), (fun _ _ _ h => by cases h)⟩
      | ok p1 =>
        rcases p1 with ⟨f, ⟨st₁, B₁⟩⟩; dsimp only
        obtain ⟨hstep1, hf1, hrf1⟩ := hok1 f st₁ B₁ he1
        obtain ⟨hnoV2, hok2⟩ := evalListS_of_evalS heval args [] B₁ n env st₁ A Scope
          hstep1.1 hargs hstep1.2.1 (hstep1.lift_env henvN) (fun _ h => by cases h)
        cases he2 : (evalListS P ext n env args []).run (st₁, B₁) with
        | error e =>
          refine ⟨(fun k hk => by cases hk; exact hnoV2 k he2), (fun _ _ _ h => by cases h)⟩
        | ok p2 =>
          rcases p2 with ⟨vs, ⟨st₂, B₂⟩⟩; dsimp only
          obtain ⟨hstep2, hvs2, hreach2⟩ := hok2 vs st₂ B₂ he2
          have hstep12 : DefStep P ext N B₂ st st₂ := hstep1.trans hstep2
          obtain ⟨hnoV3, hok3⟩ := hall B₂ hstep12.1 n f vs c st₂ A hstep2.2.1 (hstep2.lift_val hf1) hvs2
          refine ⟨hnoV3, fun rv st' B' h3 => ?_⟩
          obtain ⟨hstep3, _, hrv3, hrb3⟩ := hok3 rv st' B' h3
          refine ⟨(hstep12.dec_in (Nat.le_succ _)).trans hstep3, hrv3, fun l hl => ?_⟩
          rcases hrb3 l hl with hge2 | hrf2 | ⟨v, hv, hrv2⟩ | hss2 | hnum3
          · exact Or.inl (Nat.le_trans hstep12.2.2.1 hge2)
          · have hpf : PreservesLocs (Reach st₁.heap f) st₁.heap st₂.heap :=
              hstep2.preserves_old.mono fun _ h => hf1.1.1.reach_lt_size h
            rcases hrf1 l ((Reach_congr hpf l).mp hrf2) with hge0 | her0 | hss0 | hnum1
            · exact Or.inl hge0
            · exact Or.inr (Or.inl her0)
            · exact Or.inr (Or.inr (Or.inl hss0))
            · exact Or.inr (Or.inr (Or.inr (hstep3.lift_numLoc (hstep2.lift_numLoc hnum1))))
          · rcases hreach2 v hv l hrv2 with hge1 | ⟨_, hnil, _⟩ | her1 | hss1 | hnum2
            · exact Or.inl (Nat.le_trans hstep1.2.2.1 hge1)
            · cases hnil
            · exact Or.inr (Or.inl (EnvReach_of_preserves_old henvN hstep1.preserves_old her1))
            · rcases hstep1.staticStrFresh l hss1 with hge0 | hss0 | hnum1
              · exact Or.inl hge0
              · exact Or.inr (Or.inr (Or.inl hss0))
              · exact Or.inr (Or.inr (Or.inr (hstep3.lift_numLoc (hstep2.lift_numLoc hnum1))))
            · exact Or.inr (Or.inr (Or.inr (hstep3.lift_numLoc hnum2)))
          · rcases hstep12.staticStrFresh l hss2 with hge0 | hss0 | hnum2
            · exact Or.inl hge0
            · exact Or.inr (Or.inr (Or.inl hss0))
            · exact Or.inr (Or.inr (Or.inr (hstep3.lift_numLoc hnum2)))
          · exact Or.inr (Or.inr (Or.inr hnum3))
    cases head with
    | const r rc0 =>
      cases hdefH with
      | const hdi =>
        have hconst : (spineS P ext (n + 1) env (.const r rc0) args c).run (st, N + 1) =
            (match (evalCallArgsS P ext n env (P.find? r) args.zipIdx []).run (st, N) with
             | .error e => .error e
             | .ok (vs, (st₁, B₁)) => (callWithS P ext n r vs c).run (st₁, B₁)) := by
          conv => lhs; unfold spineS
          rw [MS_bind_run, MS_spend_succ]; dsimp only
          rw [MS_bind_run]
          cases (evalCallArgsS P ext n env (P.find? r) args.zipIdx []).run (st, N) with
          | error _ => rfl
          | ok p => rcases p with ⟨_, ⟨_, _⟩⟩; rfl
        rw [hconst]
        have hzipOk : ∀ ti ∈ args.zipIdx, DefaultTerm P ti.1 ∧ LamsClosed ti.1 ∧ ∀ x, FreeVarIn 0 ti.1 x → Scope x := by
          intro ti hti
          obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hti
          have hlt : k < args.length := by simpa [List.length_zipIdx] using hk
          rw [List.getElem_zipIdx] at heq
          have hti1 : ti.1 = args[k] := (congrArg Prod.fst heq).symm
          rw [hti1]
          exact hargs args[k] (List.getElem_mem hlt)
        obtain ⟨hnoV1, hok1⟩ := evalCallArgsS_of_evalS heval (P.find? r) args.zipIdx [] N n env st A Scope
          (Nat.le_refl _) hzipOk hstN henvN (fun _ h => by cases h)
        cases he1 : (evalCallArgsS P ext n env (P.find? r) args.zipIdx []).run (st, N) with
        | error e =>
          refine ⟨(fun k hk => by cases hk; exact hnoV1 k he1), (fun _ _ _ h => by cases h)⟩
        | ok p1 =>
          rcases p1 with ⟨vs, ⟨st₁, B₁⟩⟩; dsimp only
          obtain ⟨hstep1, hvs1, hreach1⟩ := hok1 vs st₁ B₁ he1
          obtain ⟨hnoV2, hok2⟩ := hcall B₁ hstep1.1 n r vs c st₁ A hdi hstep1.2.1 hvs1
          refine ⟨hnoV2, fun rv st' B' h2 => ?_⟩
          obtain ⟨hstep2, hrv2, hrb2⟩ := hok2 rv st' B' h2
          refine ⟨(hstep1.dec_in (Nat.le_succ _)).trans hstep2, hrv2, fun l hl => ?_⟩
          rcases hrb2 l hl with hge1 | ⟨v, hv, hrv1⟩ | hss1 | hnum2
          · exact Or.inl (Nat.le_trans hstep1.2.2.1 hge1)
          · rcases hreach1 v hv l hrv1 with hge0 | ⟨_, hnil, _⟩ | her0 | hss0 | hnum1
            · exact Or.inl hge0
            · cases hnil
            · exact Or.inr (Or.inl her0)
            · exact Or.inr (Or.inr (Or.inl hss0))
            · exact Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1)))
          · rcases hstep1.staticStrFresh l hss1 with hge0 | hss0 | hnum1
            · exact Or.inl hge0
            · exact Or.inr (Or.inr (Or.inl hss0))
            · exact Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1)))
          · exact Or.inr (Or.inr (Or.inr hnum2))
    | irr | var _ _ | natLit _ | strLit _ | app _ _ _ | lam _ _ _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ =>
      exact hnonConst _ hdefH hlcH hfvH (by
        conv => lhs; unfold spineS
        rw [MS_bind_run, MS_spend_succ]; dsimp only
        rw [MS_bind_run]
        cases (evalS P ext n env _).run (st, N) with
        | error _ => rfl
        | ok p1 =>
          rcases p1 with ⟨f, ⟨st₁, B₁⟩⟩; dsimp only
          rw [MS_bind_run]
          cases (evalListS P ext n env args []).run (st₁, B₁) with
          | error _ => rfl
          | ok p2 => rcases p2 with ⟨_, ⟨_, _⟩⟩; rfl)

private theorem evalS_step {P : Prog} {ext : ExternOracle} {N : Nat}
    (hidx : CtorsIndexed P)
    (heval : ∀ b ≤ N, EvalSDefOk P ext b)
    (hspine : ∀ b ≤ N, SpineSDefOk P ext b)
    (hall : ∀ b ≤ N, ApplyAllSDefOk P ext b)
    (halt : ∀ b ≤ N, ApplyAltSDefOk P ext b)
    (hclo : ∀ b ≤ N, CloDefFunOk P ext b) :
    EvalSDefOk P ext (N + 1) := by
  intro fuel env t st A Scope hdef hlc hfv hst henv
  cases fuel with
  | zero =>
    have h0 : (evalS P ext 0 env t).run (st, N + 1) = .error .outOfFuel := by
      unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl
    rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n =>
    have hstN : StOk P ext N st := StOk_mono (Nat.le_succ _) hst
    have henvN : DefEnvOk P ext N st A Scope env := henv.mono (Nat.le_succ _)
    cases t with
    | irr =>
      have hrun : (evalS P ext (n + 1) env .irr).run (st, N + 1) = .ok (.imm .irr, (st, N)) := by
        unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl
      rw [hrun]
      refine ⟨(fun _ h => by cases h), fun rv st' B' h => ?_⟩
      cases h
      exact ⟨(DefStep.refl hstN).dec_in (Nat.le_succ _), DefValOk_imm P ext N st A .irr,
        fun _ hl => by cases hl⟩
    | var i c =>
      have hsc : Scope i := hfv i (by simpa using FreeVarIn.var (d := 0) (i := i) (c := c) (Nat.zero_le i))
      have hrun : (evalS P ext (n + 1) env (.var i c)).run (st, N + 1) =
          (match env[i]? with
           | none => .error .stuck
           | some b =>
             if b.mode == .erased then .error (.violation .erasedRead)
             else match (live b.val).run st with
               | .error e => .error e
               | .ok ((), st₁) =>
                 match (conform c b.val).run st₁ with
                 | .error e => .error e
                 | .ok (rv, st₂) => .ok (rv, (st₂, N))) := by
        unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [MS_liftM_run]
        cases env[i]? with
        | none => rfl
        | some b =>
          dsimp only
          cases (b.mode == .erased) with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, M_bind_run]
            cases (live b.val).run st with
            | error _ => rfl
            | ok p =>
              rcases p with ⟨⟨⟩, st₁⟩; dsimp only
              cases (conform c b.val).run st₁ <;> rfl
      rw [hrun]
      cases hget : env[i]? with
      | none => exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | some b =>
        obtain ⟨hm, hbv⟩ := henvN i b hsc hget
        have herF : (b.mode == .erased) = false := by rw [hm]; decide
        simp only [herF, Bool.false_eq_true, ↓reduceIte, live_ok hbv.1.1.self.1]
        rcases conform_default_sound hstN hbv with hSt | ⟨rv, st', hcr, hstep, _, hrv, hreach⟩
        · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        · rw [hcr]
          refine ⟨(fun _ h => by cases h), fun rv' st'' B' hok => ?_⟩
          cases hok
          refine ⟨hstep.dec_in (Nat.le_succ _), hrv, fun l hl => ?_⟩
          rcases hreach l hl with hge | hrb
          · exact Or.inl hge
          · exact Or.inr (Or.inl ⟨i, b, hsc, hget, hrb⟩)
    | natLit k =>
      obtain ⟨v, st', hnv, hstep, hv, hreach⟩ := natValue_default_sound (P := P) (ext := ext) (B := N) (A := A) k hstN
      have hrun : (evalS P ext (n + 1) env (.natLit k)).run (st, N + 1) = .ok (v, (st', N)) := by
        unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [MS_liftM_run, hnv]
      rw [hrun]
      refine ⟨(fun _ h => by cases h), fun rv st'' B' h => ?_⟩
      cases h
      exact ⟨hstep.dec_in (Nat.le_succ _), hv, fun l hl => Or.inl (hreach l hl)⟩
    | strLit s =>
      obtain ⟨v, st', hsv, hstep, hv, hreach⟩ := strValue_default_sound (P := P) (ext := ext) (B := N) (A := A) s hstN
      have hrun : (evalS P ext (n + 1) env (.strLit s)).run (st, N + 1) = .ok (v, (st', N)) := by
        unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [MS_liftM_run, hsv]
      rw [hrun]
      refine ⟨(fun _ h => by cases h), fun rv st'' B' h => ?_⟩
      cases h
      exact ⟨hstep.dec_in (Nat.le_succ _), hv, fun l hl => (hreach l hl).imp id (fun hss => Or.inr (Or.inl hss))⟩
    | const r c =>
      have hrun : (evalS P ext (n + 1) env (.const r c)).run (st, N + 1) =
          (spineS P ext n env (.const r c) [] c).run (st, N) := by
        unfold evalS; rw [MS_bind_run, MS_spend_succ]
      rw [hrun]
      obtain ⟨hnoV, hok⟩ := hspine N (Nat.le_refl _) n env (.const r c) [] c st A Scope
        hdef hlc hfv (fun _ h => by cases h) hstN henvN
      exact ⟨hnoV, fun rv st' B' h => let ⟨hs, hv, hr⟩ := hok rv st' B' h; ⟨hs.dec_in (Nat.le_succ _), hv, hr⟩⟩
    | app f a c =>
      have hrun : (evalS P ext (n + 1) env (.app f a c)).run (st, N + 1) =
          (spineS P ext n env (collect (.app f a c) []).1 (collect (.app f a c) []).2 c).run (st, N) := by
        unfold evalS; rw [MS_bind_run, MS_spend_succ]
      rw [hrun]
      obtain ⟨hdH, hdAs⟩ := collect_defaultTerm (.app f a c) [] hdef (fun _ h => by cases h)
      obtain ⟨hlcH, hlcAs⟩ := collect_lamsClosed (.app f a c) [] hlc (fun _ h => by cases h)
      have hfvH : ∀ x, FreeVarIn 0 (collect (.app f a c) []).1 x → Scope x :=
        fun x hx => hfv x ((collect_freeVarIn (.app f a c) [] 0 x).1 hx)
      have hargsOk : ∀ u ∈ (collect (.app f a c) []).2,
          DefaultTerm P u ∧ LamsClosed u ∧ ∀ x, FreeVarIn 0 u x → Scope x := by
        intro u hu
        refine ⟨hdAs u hu, hlcAs u hu, fun x hx => ?_⟩
        rcases (collect_freeVarIn (.app f a c) [] 0 x).2 u hu hx with ⟨_, hnil, _⟩ | hfvApp
        · cases hnil
        · exact hfv x hfvApp
      obtain ⟨hnoV, hok⟩ := hspine N (Nat.le_refl _) n env (collect (.app f a c) []).1
        (collect (.app f a c) []).2 c st A Scope hdH hlcH hfvH hargsOk hstN henvN
      exact ⟨hnoV, fun rv st' B' h => let ⟨hs, hv, hr⟩ := hok rv st' B' h; ⟨hs.dec_in (Nat.le_succ _), hv, hr⟩⟩
    | lam p res rc fvs body =>
      cases hdef with
      | lam hpMode hresEq hdefB =>
        subst hresEq
        cases hlc with
        | lam hlcB hfvsIff =>
          have hrun : (evalS P ext (n + 1) env (.lam p .shared rc fvs body)).run (st, N + 1) =
              (liftM (formClosure P n env p .shared rc fvs body)).run (st, N) := by
            unfold evalS; rw [MS_bind_run, MS_spend_succ]
          rw [hrun, MS_liftM_run]
          have hfvsOk : ∀ i ∈ fvs.toList, ∀ b, env[i]? = some b → b.mode = .many ∧ DefValOk P ext N st A b.val :=
            fun i hi b hb => henvN i b (hfv i (.lam ((hfvsIff i).mp hi))) hb
          rcases formClosure_default_sound hstN hfvsOk with hSt | hOOF |
            ⟨rv, env', taint, cap, st', hfcRun, hstep, hrvEq, hoNew, hbase', hdou', hno', hcf', hcapOk, hreach'⟩
          · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hfcRun]
            have hfunClo : FunOkAt P ext N st' .unknown false (fun _ => False) rv := by
              rw [hrvEq]
              exact hclo N (Nat.le_refl _) st' st.heap.objs.size cap env' p rc fvs body taint
                hoNew hpMode hdefB hlcB hfvsIff
                (fun i hi => let ⟨bd, hget, hm, hok⟩ := hcapOk i hi
                  ⟨bd, hget, hm, hok.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2⟩)
            refine ⟨(fun _ h => by cases h), fun rv' st'' B' hok => ?_⟩
            cases hok
            refine ⟨hstep.dec_in (Nat.le_succ _), ⟨hbase', hdou', hno', hcf', hfunClo⟩, fun l hl => ?_⟩
            rcases hreach' l hl with rfl | ⟨i, hi, b, hb, hrb⟩
            · exact Or.inl (Nat.le_refl _)
            · exact Or.inr (Or.inl ⟨i, b, hfv i (.lam ((hfvsIff i).mp hi)), hb, hrb⟩)
    | letE m d v b =>
      cases hdef with
      | letE hdefV hdefB =>
        cases hlc with
        | letE hlcV hlcB =>
          have hrun : (evalS P ext (n + 1) env (.letE (.value .many) d v b)).run (st, N + 1) =
              (match (evalS P ext n env v).run (st, N) with
               | .error e => .error e
               | .ok (x, (st₁, B₁)) =>
                 let s := st₁.nextRegion
                 let st₂ := { st₁ with nextRegion := s + 1, regions := s :: st₁.regions }
                 match (bindAt P n s .many d x).run st₂ with
                 | .error e => .error e
                 | .ok (bnd, st₃) =>
                   match (evalS P ext n (bnd :: env) b).run (st₃, B₁) with
                   | .error e => .error e
                   | .ok (r, (st₄, B₂)) =>
                     if confinedTo s r then .error (.violation .borrowEscape)
                     else .ok (r, ({ st₄ with regions := st₄.regions.filter (· != s) }, B₂))) := by
            conv => lhs; unfold evalS
            rw [MS_bind_run, MS_spend_succ]; dsimp only
            rw [MS_bind_run]
            cases (evalS P ext n env v).run (st, N) with
            | error _ => rfl
            | ok p1 =>
              rcases p1 with ⟨x, ⟨st₁, B₁⟩⟩; dsimp only
              rw [MS_bind_run, MS_liftM_run]
              have hopen : openRegion.run st₁ = .ok ((st₁.nextRegion, st₁.regions.headD 0),
                  { st₁ with nextRegion := st₁.nextRegion + 1, regions := st₁.nextRegion :: st₁.regions }) := rfl
              rw [hopen]; dsimp only
              rw [MS_bind_run, MS_liftM_run]; dsimp only [LetMode.binderMode]
              cases (bindAt P n st₁.nextRegion .many d x).run
                  { st₁ with nextRegion := st₁.nextRegion + 1, regions := st₁.nextRegion :: st₁.regions } with
              | error _ => rfl
              | ok p3 =>
                rcases p3 with ⟨bnd, st₃⟩; dsimp only
                rw [MS_bind_run]
                cases (evalS P ext n (bnd :: env) b).run (st₃, B₁) with
                | error _ => rfl
                | ok p4 =>
                  rcases p4 with ⟨r, ⟨st₄, B₂⟩⟩; dsimp only
                  cases hc : confinedTo st₁.nextRegion r with
                  | true => simp only [↓reduceIte, MS_bind_run, MS_liftM_run]; rfl
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte, MS_bind_run, MS_liftM_run]
                    have hcls : (closeRegion st₁.nextRegion).run st₄ =
                        .ok ((), { st₄ with regions := st₄.regions.filter (· != st₁.nextRegion) }) := rfl
                    rw [hcls]; rfl
          rw [hrun]
          obtain ⟨hnoVV, hokV⟩ := heval N (Nat.le_refl _) n env v st A Scope hdefV hlcV
            (fun x hx => hfv x (.letV hx)) hstN henvN
          cases hvRun : (evalS P ext n env v).run (st, N) with
          | error e =>
            refine ⟨(fun k hk => by cases hk; exact hnoVV k hvRun), (fun _ _ _ h => by cases h)⟩
          | ok p1 =>
            rcases p1 with ⟨x, ⟨st₁, B₁⟩⟩; dsimp only
            obtain ⟨hstep01, hx1, hreachV⟩ := hokV x st₁ B₁ hvRun
            let s := st₁.nextRegion
            let st₂ : St := { st₁ with nextRegion := s + 1, regions := s :: st₁.regions }
            let A' : List Nat := A.filter (· < s)
            have hA'Sub : ∀ y ∈ A', y ∈ A := fun y hy => (List.mem_filter.mp hy).1
            have hA'Lt : ∀ y ∈ A', y < s := fun y hy => of_decide_eq_true (List.mem_filter.mp hy).2
            have hst₂ : StOk P ext B₁ st₂ := StOk_openRegion hstep01.2.1
            rcases bindAt_default_sound (P := P) (ext := ext) (B := B₁) (fuel := n) (s := s)
                (c := d) hst₂ (Nat.lt_succ_self s) hx1.filter_lt.openRegion with hSt | hOOF |
              ⟨bnd, st₃, hbindRun, hbm, hstep23, hbv3, hreachBind⟩
            · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hbindRun]; dsimp only
              have henv1 : DefEnvOk P ext B₁ st₁ A' Scope env := (hstep01.lift_env henvN).filter_lt
              have henv2 : DefEnvOk P ext B₁ st₂ A' Scope env :=
                henv1.preserve_old (st := st₁) (Nat.le_refl _) (PreservesLocs.refl _ _) (RegsFuture.openRegion st₁)
              have henv3 : DefEnvOk P ext B₁ st₃ A' (shiftScope Scope) (bnd :: env) :=
                (hstep23.lift_env henv2).cons hbm hbv3
              have hfvB : ∀ y, FreeVarIn 0 b y → shiftScope Scope y :=
                shiftScope_of_freeVarIn (fun y hy => hfv y (.letB hy))
              obtain ⟨hnoVB, hokB⟩ := heval B₁ hstep01.1 n (bnd :: env) b st₃ A' (shiftScope Scope)
                hdefB hlcB hfvB hstep23.2.1 henv3
              cases hbRun : (evalS P ext n (bnd :: env) b).run (st₃, B₁) with
              | error e =>
                refine ⟨(fun k hk => by cases hk; exact hnoVB k hbRun), (fun _ _ _ h => by cases h)⟩
              | ok p4 =>
                rcases p4 with ⟨r, ⟨st₄, B₂⟩⟩; dsimp only
                obtain ⟨hstep34, hr4, hreachB⟩ := hokB r st₄ B₂ hbRun
                have hstep24 : DefStep P ext B₁ B₂ st₂ st₄ := hstep23.trans hstep34
                have hconfF : confinedTo st₁.nextRegion r = false :=
                  (openUnder_singleton_of_deepOpenUnder_lt (hstep24.2.2.2.2.1 ▸ hr4.2.1) hA'Lt).2
                simp only [hconfF, Bool.false_eq_true, ↓reduceIte]
                have hstep15 : DefStep P ext B₁ B₂ st₁ { st₄ with regions := st₄.regions.filter (· != s) } :=
                  hstep24.open_close hstep01.2.1.2.1
                refine ⟨(fun _ h => by cases h), fun rv st' B' hok => ?_⟩
                cases hok
                refine ⟨(hstep01.dec_in (Nat.le_succ _)).trans hstep15,
                  (hr4.closeRegion s).mono_regs hA'Sub, fun l hl4 => ?_⟩
                rcases hreachB l hl4 with hge3 | her3 | hss3 | hnum4
                · exact Or.inl (Nat.le_trans hstep01.2.2.1 (Nat.le_trans hstep23.2.2.1 hge3))
                · rcases EnvReach_cons her3 with hrbnd | herEnv3
                  · rcases hreachBind l hrbnd with hge2 | hrx
                    · exact Or.inl (Nat.le_trans hstep01.2.2.1 hge2)
                    · rcases hreachV l hrx with hge0 | her0 | hss0 | hnum1
                      · exact Or.inl hge0
                      · exact Or.inr (Or.inl her0)
                      · exact Or.inr (Or.inr (Or.inl hss0))
                      · exact Or.inr (Or.inr (Or.inr (hstep15.lift_numLoc hnum1)))
                  · have her1 : EnvReach Scope st₁.heap env l :=
                      EnvReach_of_preserves_old (st := st₂) henv2 hstep23.preserves_old herEnv3
                    exact Or.inr (Or.inl (EnvReach_of_preserves_old henvN hstep01.preserves_old her1))
                · rcases hstep23.staticStrFresh l hss3 with hge2 | hss2 | hnum3
                  · exact Or.inl (Nat.le_trans hstep01.2.2.1 hge2)
                  · rcases hstep01.staticStrFresh l hss2 with hge0 | hss0 | hnum1
                    · exact Or.inl hge0
                    · exact Or.inr (Or.inr (Or.inl hss0))
                    · exact Or.inr (Or.inr (Or.inr (hstep15.lift_numLoc hnum1)))
                  · exact Or.inr (Or.inr (Or.inr (hstep34.lift_numLoc hnum3)))
                · exact Or.inr (Or.inr (Or.inr hnum4))
    | proj s i e c =>
      cases hdef with
      | proj hctors hdefE =>
        cases hlc with
        | proj hlcE =>
          have hrun : (evalS P ext (n + 1) env (.proj s i e c)).run (st, N + 1) =
              (match (evalS P ext n env e).run (st, N) with
               | .error e' => .error e'
               | .ok (v, (st₁, B₁)) =>
                 match (projTail P s i v c).run st₁ with
                 | .error e' => .error e'
                 | .ok (rv, st₂) => .ok (rv, (st₂, B₁))) := by
            conv => lhs; unfold evalS
            rw [MS_bind_run, MS_spend_succ]; dsimp only
            rw [MS_bind_run]
            cases (evalS P ext n env e).run (st, N) with
            | error _ => rfl
            | ok p1 =>
              rcases p1 with ⟨v, ⟨st₁, B₁⟩⟩; dsimp only
              change (liftM (projTail P s i v c)).run (st₁, B₁) = _
              rw [MS_liftM_run]
              cases (projTail P s i v c).run st₁ <;> rfl
          rw [hrun]
          obtain ⟨hnoVE, hokE⟩ := heval N (Nat.le_refl _) n env e st A Scope hdefE hlcE
            (fun x hx => hfv x (.proj hx)) hstN henvN
          cases heRun : (evalS P ext n env e).run (st, N) with
          | error err =>
            refine ⟨(fun k hk => by cases hk; exact hnoVE k heRun), (fun _ _ _ h => by cases h)⟩
          | ok p1 =>
            rcases p1 with ⟨v, ⟨st₁, B₁⟩⟩; dsimp only
            obtain ⟨hstep1, hv1, hreach1⟩ := hokE v st₁ B₁ heRun
            have hnotEr : ∀ ctor ind ci nP fs f,
                (P.ctorsOf s)[0]? = some ctor → P.ctorOf? ctor = some (ind, ci, nP, fs) →
                fs[i]? = some f → f.mode ≠ .erased := by
              intro ctor ind ci nP fs f hc0 hco hfi
              have hcm := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hc0)
              have hfm := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hfi)
              rw [(hctors ctor hcm ind ci nP fs hco f hfm).1]; decide
            rcases proj_sound (P := P) (ext := ext) (B := B₁) (s := s) (i := i) (v := v) (c := c)
                (sk := .unknown) (A := A) hstep1.2.1 hv1.1 hv1.2.2.1 hv1.2.2.2.1 hv1.2.1
                hnotEr (fun _ => hv1.2.2.2.2) (Or.inl rfl) with hSt |
              ⟨rv, st₂, hpRun, hr2, hnr2, hstat2, hstr2, hsz2, hcap2, hpres2, _, honce2, hssf2,
               hst2, hbase2, _, hno2, hcf2, hfun2, hdou2, hreach2⟩
            · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hpRun]
              have hstep2 : DefStep P ext B₁ B₁ st₁ st₂ :=
                ⟨Nat.le_refl _, hst2, hsz2, hcap2, hr2, hnr2 ▸ Nat.le_refl _,
                 hstat2 ▸ ArrayExtends.refl _, hstr2 ▸ ArrayExtends.refl _, hpres2, honce2, hssf2⟩
              have hdouA : DeepOpenUnder st₂.heap st₂.regions A rv := by
                refine hdou2.mono (fun x hx => ?_)
                cases hc : (c == .val) <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hx
                · cases hx
                · exact hx
              refine ⟨(fun _ h => by cases h), fun rv' st' B' hok => ?_⟩
              cases hok
              refine ⟨(hstep1.dec_in (Nat.le_succ _)).trans hstep2,
                ⟨hbase2, hdouA, hno2, hcf2, hfun2⟩, fun l hl => ?_⟩
              rcases hreach2 l hl with hge1 | hrv1
              · exact Or.inl (Nat.le_trans hstep1.2.2.1 hge1)
              · rcases hreach1 l hrv1 with hge0 | her0 | hss0 | hnum1
                · exact Or.inl hge0
                · exact Or.inr (Or.inl her0)
                · exact Or.inr (Or.inr (Or.inl hss0))
                · exact Or.inr (Or.inr (Or.inr (hstep2.lift_numLoc hnum1)))
    | case k major alts extra c =>
      cases hdef with
      | case hctors hdefMj hdefAlts hdefEx =>
        cases hlc with
        | case hlcMj hlcAlts hlcEx =>
          let mjM : MS Val := match major with
            | .var j mc => liftM do
              let some b := env[j]? | stuckM
              if b.mode == .erased then violate .erasedRead
              live b.val
              let v ← conform mc b.val
              if b.mode.isUnique then transfer P n b.mode.isBorrowed v else pure v
            | t0 => evalS P ext n env t0
          have hmajorOk :
              (∀ k', mjM.run (st, N) ≠ .error (.violation k')) ∧
              ∀ mv st₁ B₁, mjM.run (st, N) = .ok (mv, (st₁, B₁)) →
                DefStep P ext N B₁ st st₁ ∧
                DefValOk P ext B₁ st₁ A mv ∧
                ∀ l, Reach st₁.heap mv l →
                  st.heap.objs.size ≤ l ∨ EnvReach Scope st.heap env l ∨ StaticStrLoc st l ∨ NumLoc st₁.heap l := by
            dsimp only [mjM]
            cases major with
            | var j mc =>
              have hsc : Scope j := hfv j (.caseMj (by simpa using FreeVarIn.var (d := 0) (i := j) (c := mc) (Nat.zero_le j)))
              have hvarUnfold : (liftM (do
                    let some b := env[j]? | stuckM
                    if b.mode == .erased then violate .erasedRead
                    live b.val
                    let v ← conform mc b.val
                    if b.mode.isUnique then transfer P n b.mode.isBorrowed v else pure v) : MS Val).run (st, N) =
                  (match env[j]? with
                   | none => .error .stuck
                   | some b =>
                     if b.mode == .erased then .error (.violation .erasedRead)
                     else match (live b.val).run st with
                       | .error e => .error e
                       | .ok ((), st₁) =>
                         match (conform mc b.val).run st₁ with
                         | .error e => .error e
                         | .ok (v, st₂) =>
                           if b.mode.isUnique then
                             match (transfer P n b.mode.isBorrowed v).run st₂ with
                             | .error e => .error e
                             | .ok (v', st₃) => .ok (v', (st₃, N))
                           else .ok (v, (st₂, N))) := by
                rw [MS_liftM_run]
                cases env[j]? with
                | none => rfl
                | some b =>
                  dsimp only
                  cases (b.mode == .erased) with
                  | true => rfl
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte, M_bind_run]
                    cases (live b.val).run st with
                    | error _ => rfl
                    | ok p =>
                      rcases p with ⟨⟨⟩, st₁⟩; dsimp only
                      cases (conform mc b.val).run st₁ with
                      | error _ => rfl
                      | ok p2 =>
                        rcases p2 with ⟨v, st₂⟩; dsimp only
                        cases b.mode.isUnique with
                        | false => rfl
                        | true =>
                          simp only [↓reduceIte]
                          cases (transfer P n b.mode.isBorrowed v).run st₂ <;> rfl
              rw [hvarUnfold]
              cases hget : env[j]? with
              | none => exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              | some b =>
                obtain ⟨hbm, hbv⟩ := henvN j b hsc hget
                have herF : (b.mode == .erased) = false := by rw [hbm]; decide
                have huF : b.mode.isUnique = false := by rw [hbm]; rfl
                simp only [herF, huF, Bool.false_eq_true, ↓reduceIte, live_ok hbv.1.1.self.1]
                rcases conform_default_sound hstN hbv with hSt | ⟨mv, st₁, hcr, hstep, _, hmv, hreach⟩
                · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                · rw [hcr]
                  refine ⟨(fun _ h => by cases h), fun mv' st₁' B₁ hok => ?_⟩
                  cases hok
                  refine ⟨hstep, hmv, fun l hl => ?_⟩
                  rcases hreach l hl with hge | hrb
                  · exact Or.inl hge
                  · exact Or.inr (Or.inl ⟨j, b, hsc, hget, hrb⟩)
            | irr | natLit _ | strLit _ | const _ _ | app _ _ _ | lam _ _ _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ =>
              exact heval N (Nat.le_refl _) n env _ st A Scope hdefMj hlcMj
                (fun x hx => hfv x (.caseMj hx)) hstN henvN
          have hcaseUnfold : (evalS P ext (n + 1) env (.case k major alts extra c)).run (st, N + 1) =
              (match mjM.run (st, N) with
               | .error e => .error e
               | .ok (mv, (st₁, B₁)) =>
                 match (select P k mv).run st₁ with
                 | .error e => .error e
                 | .ok ((j, fields), st₂) =>
                   match k.alts[j]?, alts[j]? with
                   | some alt, some altT =>
                     let args := alt.args.toList.map fun fa => match fa with
                       | .field i => fields[i]?.getD (.imm .irr, false)
                       | .irr => (.imm .irr, false)
                       | .unit => (.imm .irr, false)
                     match (applyAltS P ext n env altT args).run (st₂, B₁) with
                     | .error e => .error e
                     | .ok (r, (st₃, B₂)) =>
                       match (evalListS P ext n env extra.toList []).run (st₃, B₂) with
                       | .error e => .error e
                       | .ok (ex, (st₄, B₃)) => (applyAllS P ext n r ex c).run (st₄, B₃)
                   | _, _ => .error .stuck) := by
            conv => lhs; unfold evalS
            rw [MS_bind_run, MS_spend_succ]; dsimp only
            have hstepM : ∀ (m0 : MS Val),
                (m0 >>= fun mv => do
                  let (j, fields) ← liftM (select P k mv)
                  let some alt := k.alts[j]? | liftM stuckM
                  let some altT := alts[j]? | liftM stuckM
                  let args := alt.args.toList.map fun fa => match fa with
                    | .field i => fields[i]?.getD (.imm .irr, false)
                    | .irr => (.imm .irr, false)
                    | .unit => (.imm .irr, false)
                  let r ← applyAltS P ext n env altT args
                  let ex ← evalListS P ext n env extra.toList []
                  applyAllS P ext n r ex c).run (st, N) =
                (match m0.run (st, N) with
                 | .error e => .error e
                 | .ok (mv, (st₁, B₁)) =>
                   match (select P k mv).run st₁ with
                   | .error e => .error e
                   | .ok ((j, fields), st₂) =>
                     match k.alts[j]?, alts[j]? with
                     | some alt, some altT =>
                       let args := alt.args.toList.map fun fa => match fa with
                         | .field i => fields[i]?.getD (.imm .irr, false)
                         | .irr => (.imm .irr, false)
                         | .unit => (.imm .irr, false)
                       match (applyAltS P ext n env altT args).run (st₂, B₁) with
                       | .error e => .error e
                       | .ok (r, (st₃, B₂)) =>
                         match (evalListS P ext n env extra.toList []).run (st₃, B₂) with
                         | .error e => .error e
                         | .ok (ex, (st₄, B₃)) => (applyAllS P ext n r ex c).run (st₄, B₃)
                     | _, _ => .error .stuck) := by
              intro m0
              rw [MS_bind_run]
              cases m0.run (st, N) with
              | error _ => rfl
              | ok p1 =>
                rcases p1 with ⟨mv, ⟨st₁, B₁⟩⟩; dsimp only
                rw [MS_bind_run, MS_liftM_run]
                cases (select P k mv).run st₁ with
                | error _ => rfl
                | ok p2 =>
                  rcases p2 with ⟨⟨j, fields⟩, st₂⟩; dsimp only
                  cases k.alts[j]? with
                  | none => rfl
                  | some alt =>
                    dsimp only
                    cases alts[j]? with
                    | none => rfl
                    | some altT =>
                      dsimp only
                      rw [MS_bind_run]
                      cases (applyAltS P ext n env altT _).run (st₂, B₁) with
                      | error _ => rfl
                      | ok p3 =>
                        rcases p3 with ⟨r, ⟨st₃, B₂⟩⟩; dsimp only
                        rw [MS_bind_run]
                        cases (evalListS P ext n env extra.toList []).run (st₃, B₂) with
                        | error _ => rfl
                        | ok p4 => rcases p4 with ⟨_, ⟨_, _⟩⟩; rfl
            dsimp only [mjM]
            cases major <;> exact hstepM _
          rw [hcaseUnfold]
          cases hmj : mjM.run (st, N) with
          | error e =>
            refine ⟨(fun k' hk => by cases hk; exact hmajorOk.1 k' hmj), (fun _ _ _ h => by cases h)⟩
          | ok p1 =>
            rcases p1 with ⟨mv, ⟨st₁, B₁⟩⟩; dsimp only
            obtain ⟨hstep01, hmv1, hreachMj⟩ := hmajorOk.2 mv st₁ B₁ hmj
            rcases select_default_sound hidx hctors hstep01.2.1 hmv1 with hSt |
              ⟨j, fields, st₂, hselRun, hstep12, hfieldsOk⟩
            · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hselRun]; dsimp only
              have hstep02 : DefStep P ext N B₁ st st₂ := hstep01.trans hstep12
              cases haltK : k.alts[j]? with
              | none => exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              | some alt =>
                cases haltT : alts[j]? with
                | none => exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                | some altT =>
                  dsimp only
                  let args := alt.args.toList.map fun fa => match fa with
                    | .field i => fields[i]?.getD (.imm .irr, false)
                    | .irr => (.imm .irr, false)
                    | .unit => (.imm .irr, false)
                  have hargsOk : ∀ ae ∈ args, ae.2 = false ∧ DefValOk P ext B₁ st₂ A ae.1 ∧
                      ∀ l, Reach st₂.heap ae.1 l → st₁.heap.objs.size ≤ l ∨ Reach st₁.heap mv l := by
                    intro ae hae
                    obtain ⟨fa, _, rfl⟩ := List.mem_map.mp hae
                    cases fa with
                    | irr | unit => exact ⟨rfl, DefValOk_imm P ext B₁ st₂ A .irr, fun _ hl => by cases hl⟩
                    | field idx =>
                      dsimp only
                      cases hfi : fields[idx]? with
                      | none =>
                        rw [Option.getD_none]
                        exact ⟨rfl, DefValOk_imm P ext B₁ st₂ A .irr, fun _ hl => by cases hl⟩
                      | some q =>
                        rw [Option.getD_some]
                        exact hfieldsOk q (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hfi))
                  have haltMem : altT ∈ alts.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? haltT)
                  obtain ⟨hnoVA, hokA⟩ := halt B₁ hstep02.1 n env altT args st₂ A Scope
                    (hdefAlts altT haltMem) (hlcAlts altT haltMem) (fun x hx => hfv x (.caseAlt haltMem hx))
                    hstep02.2.1 (hstep02.lift_env henvN) (fun ae hae => ⟨(hargsOk ae hae).1, (hargsOk ae hae).2.1⟩)
                  cases haRun : (applyAltS P ext n env altT args).run (st₂, B₁) with
                  | error e =>
                    refine ⟨(fun k' hk => by cases hk; exact hnoVA k' haRun), (fun _ _ _ h => by cases h)⟩
                  | ok p3 =>
                    rcases p3 with ⟨r, ⟨st₃, B₂⟩⟩; dsimp only
                    obtain ⟨hstep23, hr3, hreachA⟩ := hokA r st₃ B₂ haRun
                    have hstep03 : DefStep P ext N B₂ st st₃ := hstep02.trans hstep23
                    have hexPred : ∀ e ∈ extra.toList, DefaultTerm P e ∧ LamsClosed e ∧ ∀ x, FreeVarIn 0 e x → Scope x :=
                      fun e he => ⟨hdefEx e he, hlcEx e he, fun x hx => hfv x (.caseEx he hx)⟩
                    obtain ⟨hnoVE, hokE⟩ := evalListS_of_evalS heval extra.toList [] B₂ n env st₃ A Scope
                      hstep03.1 hexPred hstep03.2.1 (hstep03.lift_env henvN) (fun _ h => by cases h)
                    cases heRun : (evalListS P ext n env extra.toList []).run (st₃, B₂) with
                    | error e =>
                      refine ⟨(fun k' hk => by cases hk; exact hnoVE k' heRun), (fun _ _ _ h => by cases h)⟩
                    | ok p4 =>
                      rcases p4 with ⟨ex, ⟨st₄, B₃⟩⟩; dsimp only
                      obtain ⟨hstep34, hex4, hreachEx⟩ := hokE ex st₄ B₃ heRun
                      have hstep04 : DefStep P ext N B₃ st st₄ := hstep03.trans hstep34
                      obtain ⟨hnoVAll, hokAll⟩ := hall B₃ hstep04.1 n r ex c st₄ A hstep04.2.1
                        (hstep34.lift_val hr3) hex4
                      refine ⟨hnoVAll, fun rv st' B' h5 => ?_⟩
                      obtain ⟨hstep45, _, hrv5, hreachAll⟩ := hokAll rv st' B' h5
                      have hstep25 : DefStep P ext B₁ B' st₂ st' := (hstep23.trans hstep34).trans hstep45
                      have hstep15 : DefStep P ext B₁ B' st₁ st' := hstep12.trans hstep25
                      refine ⟨(hstep04.dec_in (Nat.le_succ _)).trans hstep45, hrv5, fun l hl => ?_⟩
                      rcases hreachAll l hl with hge4 | hrr4 | ⟨v, hv, hrv4⟩ | hss4 | hnum5
                      · exact Or.inl (Nat.le_trans hstep04.2.2.1 hge4)
                      · have hpr : PreservesLocs (Reach st₃.heap r) st₃.heap st₄.heap :=
                          hstep34.preserves_old.mono fun _ h => hr3.1.1.reach_lt_size h
                        rcases hreachA l ((Reach_congr hpr l).mp hrr4) with hge2 | her2 | ⟨ae, hae, hrae⟩ | hss2 | hnum3
                        · exact Or.inl (Nat.le_trans hstep02.2.2.1 hge2)
                        · exact Or.inr (Or.inl (EnvReach_of_preserves_old henvN hstep02.preserves_old her2))
                        · rcases (hargsOk ae hae).2.2 l hrae with hge1 | hrmv
                          · exact Or.inl (Nat.le_trans hstep01.2.2.1 hge1)
                          · rcases hreachMj l hrmv with hge0 | her0 | hss0 | hnum1
                            · exact Or.inl hge0
                            · exact Or.inr (Or.inl her0)
                            · exact Or.inr (Or.inr (Or.inl hss0))
                            · exact Or.inr (Or.inr (Or.inr (hstep15.lift_numLoc hnum1)))
                        · rcases hstep02.staticStrFresh l hss2 with hge0 | hss0 | hnum2
                          · exact Or.inl hge0
                          · exact Or.inr (Or.inr (Or.inl hss0))
                          · exact Or.inr (Or.inr (Or.inr (hstep25.lift_numLoc hnum2)))
                        · exact Or.inr (Or.inr (Or.inr ((hstep34.trans hstep45).lift_numLoc hnum3)))
                      · rcases hreachEx v hv l hrv4 with hge3 | ⟨_, hnil, _⟩ | her3 | hss3 | hnum4
                        · exact Or.inl (Nat.le_trans hstep03.2.2.1 hge3)
                        · cases hnil
                        · exact Or.inr (Or.inl (EnvReach_of_preserves_old henvN hstep03.preserves_old her3))
                        · rcases hstep03.staticStrFresh l hss3 with hge0 | hss0 | hnum3
                          · exact Or.inl hge0
                          · exact Or.inr (Or.inr (Or.inl hss0))
                          · exact Or.inr (Or.inr (Or.inr ((hstep34.trans hstep45).lift_numLoc hnum3)))
                        · exact Or.inr (Or.inr (Or.inr (hstep45.lift_numLoc hnum4)))
                      · rcases hstep04.staticStrFresh l hss4 with hge0 | hss0 | hnum4
                        · exact Or.inl hge0
                        · exact Or.inr (Or.inr (Or.inl hss0))
                        · exact Or.inr (Or.inr (Or.inr (hstep45.lift_numLoc hnum4)))
                      · exact Or.inr (Or.inr (Or.inr hnum5))

/-- Core inner strong induction on budget `N ≤ B` establishing all 7 default-mode soundness
predicates simultaneously. -/
private theorem default_eval_ind {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : DefaultCallIH P ext B) :
    ∀ N ≤ B, ∀ b ≤ N,
      EvalSDefOk P ext b ∧ SpineSDefOk P ext b ∧ CallWithSDefOk P ext b ∧
      ApplyAllSDefOk P ext b ∧ ApplyAltSDefOk P ext b ∧
      CloDefFunOk P ext b ∧ PapDefFunOk P ext b := by
  have hzero : EvalSDefOk P ext 0 ∧ SpineSDefOk P ext 0 ∧ CallWithSDefOk P ext 0 ∧
      ApplyAllSDefOk P ext 0 ∧ ApplyAltSDefOk P ext 0 ∧
      CloDefFunOk P ext 0 ∧ PapDefFunOk P ext 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro fuel env t st _ _ _ _ _ _ _
      cases fuel with
      | zero => unfold evalS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ n => unfold evalS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    · intro fuel env h args c st _ _ _ _ _ _ _ _
      cases fuel with
      | zero => unfold spineS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ n => unfold spineS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    · intro fuel r vs c st _ _ _ _
      cases fuel with
      | zero => unfold callWithS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ n => unfold callWithS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    · intro fuel f vs c st _ _ _ _
      cases fuel with
      | zero => unfold applyAllS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ n =>
        cases vs with
        | nil => unfold applyAllS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        | cons _ _ => unfold applyAllS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    · intro fuel env t args st _ _ _ _ _ _ _ _
      cases fuel with
      | zero => unfold applyAltS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ n =>
        cases args with
        | nil => unfold applyAltS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        | cons _ _ => unfold applyAltS; rw [MS_bind_run, MS_spend_zero]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rw [FunOkAt]; trivial
    · intro _ _ _ _ _ _ _ _ _; rw [FunOkAt]; trivial
  intro N
  induction N with
  | zero =>
    intro _ b hb
    have h0 : b = 0 := Nat.eq_zero_of_le_zero hb
    subst h0; exact hzero
  | succ n ih =>
    intro hnB b hb
    by_cases hbn : b ≤ n
    · exact ih (Nat.le_of_succ_le hnB) b hbn
    · have hEq : b = n + 1 := by omega
      subst hEq
      have ih' := ih (Nat.le_of_succ_le hnB)
      exact ⟨evalS_step hidx (fun k hk => (ih' k hk).1) (fun k hk => (ih' k hk).2.1)
               (fun k hk => (ih' k hk).2.2.2.1) (fun k hk => (ih' k hk).2.2.2.2.1)
               (fun k hk => (ih' k hk).2.2.2.2.2.1),
             spineS_step (fun k hk => (ih' k hk).1) (fun k hk => (ih' k hk).2.2.1)
               (fun k hk => (ih' k hk).2.2.2.1),
             callWithS_step hext hih (Nat.le_of_succ_le hnB)
               (fun k hk => (ih' k hk).2.2.2.1) (fun k hk => (ih' k hk).2.2.2.2.2.2),
             applyAllS_step (fun k hk => (ih' k hk).2.2.2.1),
             applyAltS_step (fun k hk => (ih' k hk).1) (fun k hk => (ih' k hk).2.2.2.1)
               (fun k hk => (ih' k hk).2.2.2.2.1),
             cloDefFunOk_step (fun k hk => (ih' k hk).1),
             papDefFunOk_step (fun k hk => (ih' k hk).2.2.1)⟩

/-! ## 4. Exported Default-Mode Soundness Theorems -/

/-- Default-mode `evalS` soundness at any budget `b ≤ B` given `DefaultCallIH P ext B`. -/
theorem evalS_default_sound {P : Prog} {ext : ExternOracle} {B b fuel : Nat}
    {env : List Bnd} {t : Term} {st : St} {A : List Nat} {Scope : Nat → Prop}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : DefaultCallIH P ext B)
    (hb : b ≤ B) (hdef : DefaultTerm P t) (hlc : LamsClosed t)
    (hfv : ∀ x, FreeVarIn 0 t x → Scope x)
    (hst : StOk P ext b st) (henv : DefEnvOk P ext b st A Scope env) :
    (∀ k, (evalS P ext fuel env t).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (evalS P ext fuel env t).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ EnvReach Scope st.heap env l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l :=
  (default_eval_ind hidx hext hih B (Nat.le_refl _) b hb).1 fuel env t st A Scope hdef hlc hfv hst henv

/-- Default-mode `spineS` soundness at any budget `b ≤ B`. -/
theorem spineS_default_sound {P : Prog} {ext : ExternOracle} {B b fuel : Nat}
    {env : List Bnd} {head : Term} {args : List Term} {c : Cls}
    {st : St} {A : List Nat} {Scope : Nat → Prop}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : DefaultCallIH P ext B)
    (hb : b ≤ B) (hdefH : DefaultTerm P head) (hlcH : LamsClosed head)
    (hfvH : ∀ x, FreeVarIn 0 head x → Scope x)
    (hargs : ∀ a ∈ args, DefaultTerm P a ∧ LamsClosed a ∧ ∀ x, FreeVarIn 0 a x → Scope x)
    (hst : StOk P ext b st) (henv : DefEnvOk P ext b st A Scope env) :
    (∀ k, (spineS P ext fuel env head args c).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (spineS P ext fuel env head args c).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ EnvReach Scope st.heap env l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l :=
  (default_eval_ind hidx hext hih B (Nat.le_refl _) b hb).2.1 fuel env head args c st A Scope
    hdefH hlcH hfvH hargs hst henv

/-- Default-mode `callWithS` soundness at any budget `b ≤ B`. -/
theorem callWithS_default_sound {P : Prog} {ext : ExternOracle} {B b fuel : Nat}
    {r : Ref} {vs : List Val} {c : Cls} {st : St} {A : List Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : DefaultCallIH P ext B)
    (hb : b ≤ B) (hdef : ∀ d, P.find? r = some d → DefaultIface d)
    (hst : StOk P ext b st) (hvs : ∀ v ∈ vs, DefValOk P ext b st A v) :
    (∀ k, (callWithS P ext fuel r vs c).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (callWithS P ext fuel r vs c).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ (∃ v ∈ vs, Reach st.heap v l) ∨ StaticStrLoc st l ∨ NumLoc st'.heap l :=
  (default_eval_ind hidx hext hih B (Nat.le_refl _) b hb).2.2.1 fuel r vs c st A hdef hst hvs

/-- Default-mode `applyAllS` soundness at any budget `b ≤ B`. -/
theorem applyAllS_default_sound {P : Prog} {ext : ExternOracle} {B b fuel : Nat}
    {f : Val} {vs : List Val} {c : Cls} {st : St} {A : List Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : DefaultCallIH P ext B)
    (hb : b ≤ B) (hst : StOk P ext b st) (hf : DefValOk P ext b st A f)
    (hvs : ∀ v ∈ vs, DefValOk P ext b st A v) :
    (∀ k, (applyAllS P ext fuel f vs c).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (applyAllS P ext fuel f vs c).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        ClsSafe st'.heap c rv ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨ (∃ v ∈ vs, Reach st.heap v l) ∨
          StaticStrLoc st l ∨ NumLoc st'.heap l :=
  (default_eval_ind hidx hext hih B (Nat.le_refl _) b hb).2.2.2.1 fuel f vs c st A hst hf hvs

/-- Default-mode `applyAltS` soundness at any budget `b ≤ B`. -/
theorem applyAltS_default_sound {P : Prog} {ext : ExternOracle} {B b fuel : Nat}
    {env : List Bnd} {t : Term} {args : List (Val × Bool)}
    {st : St} {A : List Nat} {Scope : Nat → Prop}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : DefaultCallIH P ext B)
    (hb : b ≤ B) (hdef : DefaultTerm P t) (hlc : LamsClosed t)
    (hfv : ∀ x, FreeVarIn 0 t x → Scope x)
    (hst : StOk P ext b st) (henv : DefEnvOk P ext b st A Scope env)
    (hargs : ∀ ae ∈ args, ae.2 = false ∧ DefValOk P ext b st A ae.1) :
    (∀ k, (applyAltS P ext fuel env t args).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (applyAltS P ext fuel env t args).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ EnvReach Scope st.heap env l ∨
          (∃ ae ∈ args, Reach st.heap ae.1 l) ∨ StaticStrLoc st l ∨ NumLoc st'.heap l :=
  (default_eval_ind hidx hext hih B (Nat.le_refl _) b hb).2.2.2.2.1 fuel env t args st A Scope
    hdef hlc hfv hst henv hargs

/-- Runtime `.pap` of any `DefaultIface` constant holding valid default arguments satisfies
`FunOkAt` at any budget `B_call ≤ B + 1` given `DefaultCallIH P ext B`. -/
theorem pap_default_funOk {P : Prog} {ext : ExternOracle} {B B_call : Nat}
    {st₀ : St} {loc cap : Nat} {r : Ref} {args : Array Val} {t : List Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : DefaultCallIH P ext B)
    (hB : B_call ≤ B + 1)
    (ho₀ : st₀.heap.objs[loc]? = some ⟨.pap r args, cap⟩)
    (hdef : ∀ d, P.find? r = some d → DefaultIface d)
    (hargs₀ : ∀ w ∈ args.toList,
      ValBaseOk st₀ w ∧ NoOnceCell st₀.heap w ∧
      CtorFieldsOk P ext B_call st₀ w ∧
      FunOkAt P ext B_call st₀ .unknown false (fun _ => False) w) :
    FunOkAt P ext B_call st₀ .unknown false (fun _ => False) (.ref loc cap t) := by
  cases B_call with
  | zero => rw [FunOkAt]; trivial
  | succ b =>
    have hb : b ≤ B := Nat.le_of_succ_le_succ hB
    exact papDefFunOk_step (fun k hk => (default_eval_ind hidx hext hih B (Nat.le_refl _) k (Nat.le_trans hk hb)).2.2.1)
      st₀ loc cap r args t ho₀ hdef hargs₀

/-- Soundness of `enterS` for any unchecked `DefaultBodyOk` body at budget `B_call ≤ B + 1`
given `DefaultCallIH P ext B`. -/
theorem enterS_default_sound {P : Prog} {ext : ExternOracle} {B B_call fuel : Nat}
    {params : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel} {body : Term}
    {vs : List Val} {st : St} {A : List Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : DefaultCallIH P ext B)
    (hB : B_call ≤ B + 1)
    (hbody : DefaultBodyOk P params res rs body)
    (hlc : LamsClosed body)
    (hst : StOk P ext B_call st)
    (hvs : ∀ v ∈ vs, DefValOk P ext B_call st A v) :
    (∀ k, (enterS P ext fuel params res rc body vs).run (st, B_call) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (enterS P ext fuel params res rc body vs).run (st, B_call) = .ok (rv, (st', B')) →
        DefStep P ext B_call B' st st' ∧
        ClsSafe st'.heap rc rv ∧
        DefValOk P ext B' st' A rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ (∃ v ∈ vs, Reach st.heap v l) ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
  obtain ⟨hpmSk, hresEq, _, hdefBody⟩ := hbody
  subst hresEq
  cases fuel with
  | zero =>
    cases B_call with
    | zero =>
      have h0 : (enterS P ext 0 params .shared rc body vs).run (st, 0) = .error .outOfFuel := by
        unfold enterS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b =>
      have h0 : (enterS P ext 0 params .shared rc body vs).run (st, b + 1) = .error .outOfFuel := by
        unfold enterS; rw [MS_bind_run, MS_spend_succ]; rfl
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n =>
    cases B_call with
    | zero =>
      have h0 : (enterS P ext (n + 1) params .shared rc body vs).run (st, 0) = .error .outOfFuel := by
        unfold enterS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b =>
      have hbB : b ≤ B := Nat.le_of_succ_le_succ hB
      let s := st.nextRegion
      let cur := st.regions.headD 0
      let st₁ : St := { st with nextRegion := s + 1, regions := s :: st.regions }
      let A' : List Nat := A.filter (· < s)
      have hA'Sub : ∀ x ∈ A', x ∈ A := fun x hx => (List.mem_filter.mp hx).1
      have hA'Lt : ∀ x ∈ A', x < s := fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2
      have hunfold : (enterS P ext (n + 1) params .shared rc body vs).run (st, b + 1) =
          (match (bindParamsM P n s (params.toList.zip vs) []).run st₁ with
           | .error e => .error e
           | .ok (env, st₂) =>
             match (evalS P ext n env body).run (st₂, b) with
             | .error e => .error e
             | .ok (r, (st₃, B₃)) =>
               match (ret P n s cur .shared rc r).run st₃ with
               | .error e => .error e
               | .ok (r', st₄) => .ok (r', ({ st₄ with regions := st₄.regions.filter (· != s) }, B₃))) := by
        unfold enterS; rw [MS_bind_run, MS_spend_succ]; dsimp only
        rw [MS_bind_run, MS_liftM_run]
        have hopen : openRegion.run st = .ok ((s, cur), st₁) := rfl
        rw [hopen]; dsimp only
        rw [MS_bind_run, MS_liftM_run]
        cases (bindParamsM P n s (params.toList.zip vs) []).run st₁ with
        | error _ => rfl
        | ok p2 =>
          rcases p2 with ⟨env, st₂⟩; dsimp only
          rw [MS_bind_run]
          cases (evalS P ext n env body).run (st₂, b) with
          | error _ => rfl
          | ok p3 =>
            rcases p3 with ⟨r, ⟨st₃, B₃⟩⟩; dsimp only
            rw [MS_bind_run, MS_liftM_run]
            cases (ret P n s cur .shared rc r).run st₃ with
            | error _ => rfl
            | ok p4 =>
              rcases p4 with ⟨r', st₄⟩; dsimp only
              rw [MS_bind_run, MS_liftM_run]
              have hcls : (closeRegion s).run st₄ = .ok ((), { st₄ with regions := st₄.regions.filter (· != s) }) := rfl
              rw [hcls]; rfl
      rw [hunfold]
      have hst₁ : StOk P ext b st₁ := StOk_openRegion (StOk_mono (Nat.le_succ _) hst)
      have hxsOk : ∀ pv ∈ params.toList.zip vs, pv.1.mode = .many ∧ DefValOk P ext b st₁ A' pv.2 := by
        intro pv hpv
        have h1 : pv.1 ∈ params.toList := List.of_mem_zip hpv |>.1
        have h2 : pv.2 ∈ vs := List.of_mem_zip hpv |>.2
        exact ⟨(hpmSk pv.1 h1).1, ((hvs pv.2 h2).mono (Nat.le_succ _)).filter_lt.openRegion⟩
      rcases bindParamsM_default_sound (P := P) (ext := ext) (B := b) (fuel := n) (s := s)
          (params.toList.zip vs) [] st₁ A' hst₁ (Nat.lt_succ_self s) hxsOk (fun _ h => by cases h) with hSt | hOOF |
        ⟨env, st₂, hbindRun, hstep12, henv2, hreachBind⟩
      · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · rw [hbindRun]; dsimp only
        have henvOk2 : DefEnvOk P ext b st₂ A' (fun _ => True) env :=
          fun _ bd _ hget => henv2 bd (List.mem_of_getElem? hget)
        obtain ⟨hnoVE, hokE⟩ := evalS_default_sound hidx hext hih hbB hdefBody hlc
          (fun _ _ => trivial) hstep12.2.1 henvOk2
        cases hev : (evalS P ext n env body).run (st₂, b) with
        | error e =>
          refine ⟨(fun k hk => by cases hk; exact hnoVE k hev), (fun _ _ _ h => by cases h)⟩
        | ok p3 =>
          rcases p3 with ⟨r, ⟨st₃, B₃⟩⟩; dsimp only
          obtain ⟨hstep23, hr3, hreachEv⟩ := hokE r st₃ B₃ hev
          have hstep13 : DefStep P ext b B₃ st₁ st₃ := hstep12.trans hstep23
          have hcurLt : cur < st₃.nextRegion := by
            have hcur0 : cur < s := by
              dsimp only [cur]
              cases hrg : st.regions with
              | nil => exact hst.2.1.1
              | cons r0 rs => exact (hst.2.1.2.2 r0 (by rw [hrg]; exact List.mem_cons_self)).2
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hcur0) hstep13.2.2.2.2.2.1
          have hopenS : OpenUnder [s] [] r :=
            (openUnder_singleton_of_deepOpenUnder_lt (hstep13.2.2.2.2.1 ▸ hr3.2.1) hA'Lt).1
          rcases ret_default_sound (P := P) (ext := ext) (B := B₃) (fuel := n) (s := s) (cur := cur)
              (c := rc) hstep13.2.1 hcurLt hr3 hopenS with hStR | hOOFR |
            ⟨r', st₄, hretRun, hstep34, hcls4, hr4, hreachRet⟩
          · rw [hStR]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hOOFR]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hretRun]; dsimp only
            have hstep14 : DefStep P ext b B₃ st₁ st₄ := hstep13.trans hstep34
            have hstep05 : DefStep P ext (b + 1) B₃ st { st₄ with regions := st₄.regions.filter (· != s) } :=
              (hstep14.open_close hst.2.1).dec_in (Nat.le_succ _)
            refine ⟨(fun _ h => by cases h), fun rv st' B' hok => ?_⟩
            cases hok
            refine ⟨hstep05, hcls4, (hr4.closeRegion s).mono_regs hA'Sub, fun l hl4 => ?_⟩
            rcases hreachRet l hl4 with hge3 | hl3
            · exact Or.inl (Nat.le_trans hstep13.2.2.1 hge3)
            · rcases hreachEv l hl3 with hge2 | ⟨_, bd, _, hget, hrbd⟩ | hss2 | hnum3
              · exact Or.inl (Nat.le_trans hstep12.2.2.1 hge2)
              · rcases hreachBind bd (List.mem_of_getElem? hget) l hrbd with hge1 | ⟨pv, hpv, hrpv⟩ | ⟨_, hnil, _⟩
                · exact Or.inl hge1
                · exact Or.inr (Or.inl ⟨pv.2, (List.of_mem_zip hpv).2, hrpv⟩)
                · cases hnil
              · rcases hstep12.staticStrFresh l hss2 with hge1 | hss1 | hnum2
                · exact Or.inl hge1
                · exact Or.inr (Or.inr (Or.inl hss1))
                · exact Or.inr (Or.inr (Or.inr (hstep34.lift_numLoc (hstep23.lift_numLoc hnum2))))
              · exact Or.inr (Or.inr (Or.inr (hstep34.lift_numLoc hnum3)))

/-- Soundness of `staticS` for any unchecked 0-ary `DefaultBodyOk` body at budget `B_call ≤ B + 1`
given `DefaultCallIH P ext B`. -/
theorem staticS_default_sound {P : Prog} {ext : ExternOracle} {B B_call fuel : Nat}
    {r : Ref} {res : ResultMode} {rc : Cls} {rs : Skel} {body : Term} {st : St}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : DefaultCallIH P ext B)
    (hB : B_call ≤ B + 1)
    (hfind : P.find? r = some (.body #[] res rc rs body))
    (hbody : DefaultBodyOk P #[] res rs body)
    (hlc : LamsClosed body)
    (hst : StOk P ext B_call st) :
    (∀ k, (staticS P ext fuel r body rc).run (st, B_call) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (staticS P ext fuel r body rc).run (st, B_call) = .ok (rv, (st', B')) →
        DefStep P ext B_call B' st st' ∧
        ClsSafe st'.heap rc rv ∧
        DefValOk P ext B' st' [] rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
  obtain ⟨_, hresEq, hrsDef, hdefBody⟩ := hbody
  subst hresEq
  cases fuel with
  | zero =>
    cases B_call with
    | zero =>
      have h0 : (staticS P ext 0 r body rc).run (st, 0) = .error .outOfFuel := by
        unfold staticS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b =>
      have h0 : (staticS P ext 0 r body rc).run (st, b + 1) = .error .outOfFuel := by
        unfold staticS; rw [MS_bind_run, MS_spend_succ]; rfl
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n =>
    cases B_call with
    | zero =>
      have h0 : (staticS P ext (n + 1) r body rc).run (st, 0) = .error .outOfFuel := by
        unfold staticS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b =>
      have hbB : b ≤ B := Nat.le_of_succ_le_succ hB
      have hunfold : (staticS P ext (n + 1) r body rc).run (st, b + 1) =
          (match st.statics.find? (·.1 == r) with
           | some (_, v) =>
             match (live v).run st with
             | .error e => .error e
             | .ok ((), st₁) => .ok (v, (st₁, b))
           | none =>
             match (evalS P ext n [] body).run (st, b) with
             | .error e => .error e
             | .ok (v0, (st₁, B₁)) =>
               match (conform rc v0).run st₁ with
               | .error e => .error e
               | .ok (v, st₂) => .ok (v, ({ st₂ with statics := st₂.statics.push (r, v) }, B₁))) := by
        unfold staticS; rw [MS_bind_run, MS_spend_succ]; dsimp only
        rw [MS_bind_run, MS_liftM_run]
        have hget : (get : M St).run st = .ok (st, st) := rfl
        rw [hget]; dsimp only
        cases st.statics.find? (·.1 == r) with
        | some p =>
          rcases p with ⟨r', v⟩; dsimp only
          rw [MS_liftM_run, M_bind_run]
          cases (live v).run st with
          | error _ => rfl
          | ok pl => rcases pl with ⟨⟨⟩, st₁⟩; rfl
        | none =>
          dsimp only; rw [MS_bind_run]
          cases (evalS P ext n [] body).run (st, b) with
          | error _ => rfl
          | ok p1 =>
            rcases p1 with ⟨v0, ⟨st₁, B₁⟩⟩; dsimp only
            rw [MS_bind_run, MS_liftM_run]
            cases (conform rc v0).run st₁ with
            | error _ => rfl
            | ok p2 =>
              rcases p2 with ⟨v, st₂⟩; dsimp only
              rw [MS_bind_run, MS_liftM_run]
              have hmod : (modify fun s : St => { s with statics := s.statics.push (r, v) } : M Unit).run st₂ =
                  .ok ((), { st₂ with statics := st₂.statics.push (r, v) }) := rfl
              rw [hmod]; rfl
      rw [hunfold]
      cases hcache : st.statics.find? (·.1 == r) with
      | some p =>
        rcases p with ⟨r', v⟩
        have hmem : (r', v) ∈ st.statics.toList :=
          Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hcache)
        have hreq : r' = r := beq_iff_eq.mp (Array.find?_some (p := fun x : Ref × Val => x.1 == r) hcache)
        subst hreq
        obtain ⟨rc', rs', body', hfind', hbaseV, hclsV, hopenV, hnoV, hfunV, hcfV⟩ :=
          hst.2.2.1 r' v hmem
        rw [hfind] at hfind'; cases hfind'
        dsimp only
        rw [live_ok hbaseV.1.self.1]
        have hvOk : DefValOk P ext b st [] v :=
          DefValOk.mono (Nat.le_succ _)
            ⟨hbaseV, hopenV, hnoV, hcfV, (FunOkAt_default_equiv hrsDef rfl).mp hfunV⟩
        refine ⟨(fun _ h => by cases h), fun rv st' B' hok => ?_⟩
        cases hok
        exact ⟨(DefStep.refl (StOk_mono (Nat.le_succ _) hst)).dec_in (Nat.le_succ _), hclsV, hvOk,
          fun l hl => Or.inr (Or.inl (Or.inl ⟨r', v, hmem, hl⟩))⟩
      | none =>
        have hstB : StOk P ext b st := StOk_mono (Nat.le_succ _) hst
        have henvNil : DefEnvOk P ext b st [] (fun _ => True) [] := fun _ _ _ h => by simp at h
        obtain ⟨hnoVE, hokE⟩ := evalS_default_sound hidx hext hih hbB hdefBody hlc
          (fun _ _ => trivial) hstB henvNil
        cases hev : (evalS P ext n [] body).run (st, b) with
        | error e =>
          refine ⟨(fun k hk => by cases hk; exact hnoVE k hev), (fun _ _ _ h => by cases h)⟩
        | ok p1 =>
          rcases p1 with ⟨v0, ⟨st₁, B₁⟩⟩; dsimp only
          obtain ⟨hstep01, hv0, hreach0⟩ := hokE v0 st₁ B₁ hev
          rcases conform_default_sound hstep01.2.1 hv0 with hSt |
            ⟨v, st₂, hconfRun, hstep12, hcls2, hv2, hreach1⟩
          · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hconfRun]; dsimp only
            have hstep02 : DefStep P ext b B₁ st st₂ := hstep01.trans hstep12
            let st' : St := { st₂ with statics := st₂.statics.push (r, v) }
            have hst' : StOk P ext B₁ st' :=
              StOk_pushStatic hstep02.2.1 hfind hv2.1 hcls2 hv2.2.1 hv2.2.2.1
                ((FunOkAt_default_equiv rfl hrsDef).mp hv2.2.2.2.2) hv2.2.2.2.1
            have hreachV : ∀ l, Reach st₂.heap v l →
                st.heap.objs.size ≤ l ∨ StaticStrLoc st l ∨ NumLoc st₂.heap l := by
              intro l hl
              rcases hreach1 l hl with hge1 | hl1
              · exact Or.inl (Nat.le_trans hstep01.2.2.1 hge1)
              · rcases hreach0 l hl1 with hge0 | ⟨_, _, _, hget, _⟩ | hss0 | hnum1
                · exact Or.inl hge0
                · simp at hget
                · exact Or.inr (Or.inl hss0)
                · exact Or.inr (Or.inr (hstep12.lift_numLoc hnum1))
            have hssf' : StaticStrFresh st st' := by
              intro l hl
              rcases hl with ⟨r0, v0', hm, hr⟩ | ⟨s0, v0', hm, hr⟩
              · rw [show st'.statics.toList = st₂.statics.toList ++ [(r, v)] by
                    simp [st', Array.toList_push]] at hm
                rcases List.mem_append.mp hm with hmOld | hmNew
                · exact hstep02.staticStrFresh l (Or.inl ⟨r0, v0', hmOld, hr⟩)
                · simp only [List.mem_singleton, Prod.mk.injEq] at hmNew
                  obtain ⟨_, rfl⟩ := hmNew
                  exact hreachV l hr
              · exact hstep02.staticStrFresh l (Or.inr ⟨s0, v0', hm, hr⟩)
            have hstep0' : DefStep P ext (b + 1) B₁ st st' :=
              ⟨Nat.le_trans hstep02.1 (Nat.le_succ _), hst',
               hstep02.2.2.1, hstep02.2.2.2.1, hstep02.2.2.2.2.1, hstep02.2.2.2.2.2.1,
               hstep02.2.2.2.2.2.2.1.trans (ArrayExtends.push st₂.statics (r, v)),
               hstep02.2.2.2.2.2.2.2.1, hstep02.preserves_old,
               hstep02.2.2.2.2.2.2.2.2.2.1, hssf'⟩
            have hv' : DefValOk P ext B₁ st' [] v :=
              hv2.preserve_old (st := st₂) (Nat.le_refl _) (PreservesLocs.refl _ _)
                (RegsFuture.same_regions (Nat.le_refl _) rfl)
            refine ⟨(fun _ h => by cases h), fun rv st'' B' hok => ?_⟩
            cases hok
            exact ⟨hstep0', hcls2, hv', hreachV⟩

end IxC.Resource.Proof
