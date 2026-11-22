import IxC.Resource.Statement

/-!
# Soundness of All-Default Run Programs (`DefaultOk`)

Proves `IxC.Resource.DefaultOk` (`Statement.lean`): any run program whose
definitions all carry only default modes (`∀ r d, P.find? r = some d →
d.defaultModes = true`), run under an admissible extern oracle (`ExternOk P ext`)
and admissible inputs (`InputsOk P h params args`), never ends in a mode
violation at any fuel.

In an all-default program, no binder is erased, unique, borrowed, or once, no
result mode is unique or borrowed, no constructor field is erased or `@shared`,
and no `.once` cell is ever allocated. Every heap write is append-only (preserving
all existing cells and capabilities), every value in the heap, environments,
statics, and strings is live and untainted (`ValOk`), and no monitor in `Eval.lean`
can ever trigger a violation.
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## All-Default Predicates and Heap Monotonicity -/

/-- A program whose every definition carries only default modes. -/
def AllDefault (P : Prog) : Prop :=
  ∀ r d, P.find? r = some d → d.defaultModes = true

/-- A run term carries only default modes (at some syntactic depth). -/
def TermDefault (t : Term) : Prop :=
  ∃ n, Term.defaultModes n t = true

/-- Monotone heap extension: existing cells and their capabilities never change,
and `nextCap` only grows. -/
def HeapExt (h h' : Heap) : Prop :=
  h.objs.size ≤ h'.objs.size ∧
  h.nextCap ≤ h'.nextCap ∧
  ∀ (l : Nat) (o : Obj), h.objs[l]? = some o → h'.objs[l]? = some o

theorem HeapExt.refl (h : Heap) : HeapExt h h :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ ho => ho⟩

theorem HeapExt.trans {h₁ h₂ h₃ : Heap} (h12 : HeapExt h₁ h₂) (h23 : HeapExt h₂ h₃) :
    HeapExt h₁ h₃ :=
  ⟨Nat.le_trans h12.1 h23.1, Nat.le_trans h12.2.1 h23.2.1, fun l o ho => h23.2.2 l o (h12.2.2 l o ho)⟩

theorem valOk_mono {h h' : Heap} (hext : HeapExt h h') {v : Val} (hv : ValOk h v) : ValOk h' v := by
  cases v with
  | imm _ => trivial
  | ref loc cap t =>
    obtain ⟨rfl, o, ho, hcap⟩ := hv
    exact ⟨rfl, o, hext.2.2 loc o ho, hcap⟩

theorem valOk_taint_eq_nil {h : Heap} {v : Val} (hv : ValOk h v) : v.taint = [] := by
  cases v with
  | imm _ => rfl
  | ref _ _ t => exact hv.1

/-- Every binding in an environment is plain (`.many`) and `ValOk`. -/
def EnvDefOk (h : Heap) (env : List Bnd) : Prop :=
  ∀ b ∈ env, b.mode = .many ∧ ValOk h b.val

theorem EnvDefOk.mono {h h' : Heap} (hext : HeapExt h h') {env : List Bnd}
    (henv : EnvDefOk h env) : EnvDefOk h' env :=
  fun b hb => ⟨(henv b hb).1, valOk_mono hext (henv b hb).2⟩

/-- Cell invariant for an all-default execution: no `.once` cells, every closure
is default-mode with a default environment, and every stored value is `ValOk`. -/
def CellDefOk (h : Heap) : Cell → Prop
  | .ctor _ fs => ∀ w ∈ fs.toList, ValOk h w
  | .num _ | .str _ => True
  | .pap _ as => ∀ w ∈ as.toList, ValOk h w
  | .clo env p res _ _ body =>
      EnvDefOk h env ∧ p.mode = .many ∧ res = .shared ∧ TermDefault body
  | .once _ _ => False

theorem CellDefOk.mono {h h' : Heap} (hext : HeapExt h h') {c : Cell} (hc : CellDefOk h c) :
    CellDefOk h' c := by
  cases c with
  | ctor _ fs => exact fun w hw => valOk_mono hext (hc w hw)
  | num _ | str _ => trivial
  | pap _ as => exact fun w hw => valOk_mono hext (hc w hw)
  | clo env p res rc fvs body =>
      obtain ⟨henv, hp, hres, hbody⟩ := hc
      exact ⟨henv.mono hext, hp, hres, hbody⟩
  | once _ _ => exact hc

/-- Heap invariant for an all-default execution. -/
def HeapDefOk (h : Heap) : Prop :=
  ∀ (l : Nat) (o : Obj), h.objs[l]? = some o → o.cap < h.nextCap ∧ CellDefOk h o.cell

/-- Full state invariant for an all-default execution. -/
structure DefStOk (st : St) : Prop where
  heapOk : HeapDefOk st.heap
  staticsOk : ∀ p ∈ st.statics.toList, ValOk st.heap p.2
  strsOk : ∀ p ∈ st.strs.toList, ValOk st.heap p.2

/-! ## `TermDefault` Structural Decomposition -/

theorem TermDefault.app {f a : Term} {c : Cls} (h : TermDefault (.app f a c)) :
    TermDefault f ∧ TermDefault a := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [Term.defaultModes] at hn
  | succ n =>
    simp [Term.defaultModes, Bool.and_eq_true] at hn
    exact ⟨⟨n, hn.1⟩, ⟨n, hn.2⟩⟩

theorem TermDefault.lam {p : Param} {res : ResultMode} {rc : Cls} {fvs : Array Nat} {b : Term}
    (h : TermDefault (.lam p res rc fvs b)) :
    p.mode = .many ∧ res = .shared ∧ TermDefault b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [Term.defaultModes] at hn
  | succ n =>
    simp [Term.defaultModes, Bool.and_eq_true] at hn
    exact ⟨hn.1.1, hn.1.2, ⟨n, hn.2⟩⟩

theorem TermDefault.letE {m : LetMode} {d : Cls} {v b : Term}
    (h : TermDefault (.letE m d v b)) :
    m = .value .many ∧ TermDefault v ∧ TermDefault b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [Term.defaultModes] at hn
  | succ n =>
    simp [Term.defaultModes, Bool.and_eq_true] at hn
    exact ⟨hn.1.1, ⟨n, hn.1.2⟩, ⟨n, hn.2⟩⟩

theorem TermDefault.proj {s : Ref} {i : Nat} {e : Term} {c : Cls}
    (h : TermDefault (.proj s i e c)) : TermDefault e := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [Term.defaultModes] at hn
  | succ n =>
    simp [Term.defaultModes] at hn
    exact ⟨n, hn⟩

theorem TermDefault.case {k : CaseInfo} {mj : Term} {alts ex : Array Term} {c : Cls}
    (h : TermDefault (.case k mj alts ex c)) :
    TermDefault mj ∧ (∀ a ∈ alts.toList, TermDefault a) ∧ (∀ e ∈ ex.toList, TermDefault e) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [Term.defaultModes] at hn
  | succ n =>
    simp [Term.defaultModes, Bool.and_eq_true] at hn
    refine ⟨⟨n, hn.1.1⟩, ?_, ?_⟩
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have hi' : i < alts.size := by simpa using hi
      exact ⟨n, hn.1.2 i hi'⟩
    · intro e he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      have hi' : i < ex.size := by simpa using hi
      exact ⟨n, hn.2 i hi'⟩

theorem TermDefault.collect : ∀ (t : Term) (acc : List Term),
    TermDefault t → (∀ a ∈ acc, TermDefault a) →
    TermDefault (collect t acc).1 ∧ ∀ a ∈ (collect t acc).2, TermDefault a
  | .app f a _, acc, ht, hacc =>
    let ⟨hf, ha⟩ := ht.app
    TermDefault.collect f (a :: acc) hf fun x hx =>
      match List.mem_cons.mp hx with
      | .inl h => h ▸ ha
      | .inr hx' => hacc x hx'
  | .irr, _, ht, hacc => ⟨ht, hacc⟩
  | .var _ _, _, ht, hacc => ⟨ht, hacc⟩
  | .const _ _, _, ht, hacc => ⟨ht, hacc⟩
  | .lam _ _ _ _ _, _, ht, hacc => ⟨ht, hacc⟩
  | .letE _ _ _ _, _, ht, hacc => ⟨ht, hacc⟩
  | .case _ _ _ _ _, _, ht, hacc => ⟨ht, hacc⟩
  | .natLit _, _, ht, hacc => ⟨ht, hacc⟩
  | .strLit _, _, ht, hacc => ⟨ht, hacc⟩
  | .proj _ _ _ _, _, ht, hacc => ⟨ht, hacc⟩

/-! ## All-Default Definition Consequences -/

theorem AllDefault.body {P : Prog} (hP : AllDefault P) {r : Ref}
    {ps : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel} {t : Term}
    (hf : P.find? r = some (.body ps res rc rs t)) :
    (∀ p ∈ ps.toList, p.mode = .many) ∧ res = .shared ∧ TermDefault t := by
  have hd := hP r _ hf
  simp only [RunDef.defaultModes, Bool.and_eq_true, beq_iff_eq] at hd
  refine ⟨?_, hd.1.2, ⟨1 <<< 20, hd.2⟩⟩
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < ps.size := by simpa using hi
  simpa using (Array.all_eq_true.mp hd.1.1) i hi'

theorem AllDefault.extern {P : Prog} (hP : AllDefault P) {r : Ref}
    {ps : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel}
    (hf : P.find? r = some (.extern ps res rc rs)) :
    (∀ p ∈ ps.toList, p.mode = .many) ∧ res = .shared := by
  have hd := hP r _ hf
  simp only [RunDef.defaultModes, Bool.and_eq_true, beq_iff_eq] at hd
  refine ⟨?_, hd.2⟩
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < ps.size := by simpa using hi
  simpa using (Array.all_eq_true.mp hd.1) i hi'

theorem AllDefault.ctor {P : Prog} (hP : AllDefault P) {r ind : Ref} {ci nP : Nat}
    {fs : Array Field} (hf : P.ctorOf? r = some (ind, ci, nP, fs)) :
    ∀ f ∈ fs.toList, f.mode = .many ∧ f.fmode = .inherited := by
  unfold Prog.ctorOf? at hf
  cases hfind : P.find? r with
  | none => rw [hfind] at hf; cases hf
  | some d =>
    rw [hfind] at hf
    cases d with
    | ctor ind' ci' nP' fs' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨_, _, _, rfl⟩ := hf
      have hd := hP r _ hfind
      simp only [RunDef.defaultModes] at hd
      intro f hfm
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfm
      have hi' : i < fs'.size := by simpa using hi
      have hfi := Array.all_eq_true.mp hd i hi'
      simp only [Bool.and_eq_true, beq_iff_eq] at hfi
      exact hfi
    | _ => cases hf

/-! ## Helper Specs for Monadic Primitives -/

@[simp] theorem M_run_pure {α : Type} (a : α) (st : St) :
    ((pure a : M α).run st) = .ok (a, st) := rfl

@[simp] theorem M_run_throw {α : Type} (e : Stop) (st : St) :
    ((throw e : M α).run st) = .error e := rfl

@[simp] theorem M_run_stuck {α : Type} (st : St) :
    ((stuckM : M α).run st) = .error .stuck := rfl

@[simp] theorem M_run_get (st : St) :
    ((get : M St).run st) = .ok (st, st) := rfl

@[simp] theorem M_run_set (st' st : St) :
    ((set st' : M Unit).run st) = .ok ((), st') := rfl

@[simp] theorem M_run_modify (f : St → St) (st : St) :
    ((modify f : M Unit).run st) = .ok ((), f st) := rfl

theorem M_run_bind {α β : Type} (m : M α) (f : α → M β) (st : St) :
    ((m >>= f).run st) =
      match m.run st with
      | .ok (a, st') => (f a).run st'
      | .error e => .error e := by
  change (m.run st).bind (fun p => (f p.1).run p.2) = _
  cases m.run st <;> rfl

theorem M_run_obj (loc : Nat) (st : St) :
    (obj loc).run st =
      match st.heap.objs[loc]? with
      | some o => .ok (o, st)
      | none => .error .stuck := by
  unfold obj
  rw [M_run_bind, M_run_get]
  dsimp only
  cases st.heap.objs[loc]? <;> rfl

/-- Outcome specification for a monadic `M α` action under `DefStOk`: never
terminates in `.violation`, and on `.ok (a, st')` preserves `HeapExt` and `DefStOk`
with postcondition `Q st' a`. -/
def SafeM {α : Type} (st : St) (m : M α) (Q : St → α → Prop) : Prop :=
  match m.run st with
  | .ok (a, st') => HeapExt st.heap st'.heap ∧ DefStOk st' ∧ Q st' a
  | .error (.violation _) => False
  | .error .stuck | .error .outOfFuel => True

theorem SafeM.pure_intro {α : Type} {st : St} (hst : DefStOk st) {a : α}
    {Q : St → α → Prop} (hq : Q st a) : SafeM st (pure a) Q :=
  ⟨HeapExt.refl _, hst, hq⟩

theorem SafeM.stuck {α : Type} (st : St) (Q : St → α → Prop) : SafeM st stuckM Q := trivial

theorem SafeM.oof {α : Type} (st : St) (Q : St → α → Prop) : SafeM st (throw .outOfFuel) Q := trivial

theorem SafeM.bind {α β : Type} {st : St} {m : M α} {f : α → M β}
    {Q₁ : St → α → Prop} {Q₂ : St → β → Prop}
    (hm : SafeM st m Q₁)
    (hf : ∀ st₁ a, HeapExt st.heap st₁.heap → DefStOk st₁ → Q₁ st₁ a → SafeM st₁ (f a) Q₂) :
    SafeM st (m >>= f) Q₂ := by
  unfold SafeM at hm ⊢
  rw [M_run_bind]
  cases hmr : m.run st with
  | error e =>
    rw [hmr] at hm
    dsimp only
    cases e <;> exact hm
  | ok p =>
    rw [hmr] at hm
    dsimp only
    obtain ⟨hext1, hst1, hq1⟩ := hm
    have h2 := hf p.2 p.1 hext1 hst1 hq1
    unfold SafeM at h2
    cases hfr : (f p.1).run p.2 with
    | error e =>
      rw [hfr] at h2
      cases e <;> exact h2
    | ok q =>
      rw [hfr] at h2
      obtain ⟨hext2, hst2, hq2⟩ := h2
      exact ⟨hext1.trans hext2, hst2, hq2⟩

theorem SafeM.seq {α β : Type} {st : St} {m : M α} {n : M β}
    {Q₁ : St → α → Prop} {Q₂ : St → β → Prop}
    (hm : SafeM st m Q₁)
    (hn : ∀ st₁ a, HeapExt st.heap st₁.heap → DefStOk st₁ → Q₁ st₁ a → SafeM st₁ n Q₂) :
    SafeM st (do let _ ← m; n) Q₂ :=
  SafeM.bind hm hn

theorem SafeM.bind_stuck {α β : Type} (st : St) (f : α → M β) (Q : St → β → Prop) :
    SafeM st (stuckM >>= f) Q := by
  unfold SafeM
  simp only [M_run_bind, M_run_stuck]

theorem array_mem_toList_of_getElem? {α : Type} {arr : Array α} {i : Nat} {x : α}
    (h : arr[i]? = some x) : x ∈ arr.toList := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp h
  exact Array.mem_toList_iff.mpr (Array.getElem_mem hlt)

theorem list_mem_of_mem_zipIdx {α : Type} {l : List α} {x : α} {i : Nat}
    (h : (x, i) ∈ l.zipIdx) : x ∈ l := by
  have aux : ∀ (l : List α) (k : Nat), (x, i) ∈ l.zipIdx k → x ∈ l := by
    intro l
    induction l with
    | nil => intro k h; simp at h
    | cons a rest ih =>
      intro k h
      simp only [List.zipIdx_cons, List.mem_cons] at h
      rcases h with h | h
      · injection h with h1 _
        exact h1 ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih (k + 1) h)
  exact aux l 0 h

theorem array_mem_of_mem_set! {α : Type} {arr : Array α} {i : Nat} {v x : α}
    (h : x ∈ arr.set! i v) : x ∈ arr ∨ x = v := by
  unfold Array.set! Array.setIfInBounds at h
  split at h
  · obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp h
    have hj' : j < arr.size := by simpa using hj
    by_cases hji : j = i
    · subst hji; right; simp
    · left
      have : (arr.set i v ‹_›)[j] = arr[j] := Array.getElem_set_ne ‹_› hj' (by omega)
      rw [this]
      exact Array.getElem_mem hj'
  · exact Or.inl h

/-- Generic loop safety rule for `forIn` over a `List` in `M`. -/
theorem SafeM_forIn_list {α β : Type} {l : List α} {init : β}
    {f : α → β → M (ForInStep β)} {I : St → β → Prop} {st : St}
    (hst : DefStOk st) (hinit : I st init)
    (hstep : ∀ st₀ a b, a ∈ l → HeapExt st.heap st₀.heap → DefStOk st₀ → I st₀ b →
      SafeM st₀ (f a b) (fun st₁ s => match s with | .yield b' | .done b' => I st₁ b')) :
    SafeM st (forIn l init f) I := by
  induction l generalizing st init with
  | nil => exact SafeM.pure_intro hst hinit
  | cons a rest ih =>
    rw [List.forIn_cons]
    refine SafeM.bind (hstep st a init (List.mem_cons_self ..) (HeapExt.refl _) hst hinit) ?_
    intro st₁ step hext₁ hst₁ hI₁
    cases step with
    | done b => exact SafeM.pure_intro hst₁ hI₁
    | yield b =>
      exact ih hst₁ hI₁ fun st₀ x bx hx hext₀ hst₀ hI₀ =>
        hstep st₀ x bx (List.mem_cons_of_mem _ hx) (hext₁.trans hext₀) hst₀ hI₀

/-- Generic loop safety rule for `forIn` over an `Array` in `M`. -/
theorem SafeM_forIn_array {α β : Type} {arr : Array α} {init : β}
    {f : α → β → M (ForInStep β)} {I : St → β → Prop} {st : St}
    (hst : DefStOk st) (hinit : I st init)
    (hstep : ∀ st₀ a b, a ∈ arr.toList → HeapExt st.heap st₀.heap → DefStOk st₀ → I st₀ b →
      SafeM st₀ (f a b) (fun st₁ s => match s with | .yield b' | .done b' => I st₁ b')) :
    SafeM st (forIn arr init f) I := by
  rw [← Array.forIn_toList]
  exact SafeM_forIn_list hst hinit hstep

theorem SafeM_openRegion {st : St} (hst : DefStOk st) :
    SafeM st openRegion (fun st' _ => st'.heap = st.heap) := by
  unfold SafeM openRegion
  simp only [M_run_bind, M_run_get, M_run_set, M_run_pure]
  exact ⟨HeapExt.refl _, ⟨hst.heapOk, hst.staticsOk, hst.strsOk⟩, trivial⟩

theorem SafeM_closeRegion {st : St} (hst : DefStOk st) (r : Nat) :
    SafeM st (closeRegion r) (fun st' _ => st'.heap = st.heap) := by
  unfold SafeM closeRegion
  simp only [M_run_modify]
  exact ⟨HeapExt.refl _, ⟨hst.heapOk, hst.staticsOk, hst.strsOk⟩, trivial⟩

theorem SafeM_alloc {st : St} (hst : DefStOk st) {c : Cell} (hc : CellDefOk st.heap c) :
    SafeM st (alloc c []) (fun st' v => ValOk st'.heap v) := by
  unfold SafeM alloc freshCap
  simp only [M_run_bind, M_run_get, M_run_set, M_run_pure]
  let cap := st.heap.nextCap
  let loc := st.heap.objs.size
  let h' : Heap := { objs := st.heap.objs.push ⟨c, cap⟩, nextCap := cap + 1 }
  have hext : HeapExt st.heap h' := by
    refine ⟨by simp [h'], Nat.le_succ _, ?_⟩
    intro l o ho
    have hlt : l < st.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
    rw [show h'.objs[l]? = some st.heap.objs[l] from Array.getElem?_push_lt hlt,
        ← Array.getElem?_eq_getElem hlt]
    exact ho
  have hheap : HeapDefOk h' := by
    intro l o ho
    by_cases hlt : l < st.heap.objs.size
    · rw [show h'.objs[l]? = some st.heap.objs[l] from Array.getElem?_push_lt hlt,
          ← Array.getElem?_eq_getElem hlt] at ho
      obtain ⟨hcap, hcell⟩ := hst.heapOk l o ho
      exact ⟨Nat.lt_succ_of_lt hcap, hcell.mono hext⟩
    · have hlen : l < h'.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
      have heq : l = st.heap.objs.size := by simp [h'] at hlen; omega
      subst heq
      rw [show h'.objs[st.heap.objs.size]? = some ⟨c, cap⟩ by simp [h']] at ho
      cases ho
      exact ⟨Nat.lt_succ_self _, hc.mono hext⟩
  have hst' : DefStOk { st with heap := h' } :=
    ⟨hheap, fun p hp => valOk_mono hext (hst.staticsOk p hp),
      fun p hp => valOk_mono hext (hst.strsOk p hp)⟩
  have hv : ValOk h' (.ref loc cap []) :=
    ⟨rfl, ⟨c, cap⟩, by simp [h', loc], rfl⟩
  exact ⟨hext, hst', hv⟩

theorem SafeM_live {st : St} (hst : DefStOk st) {v : Val} (hv : ValOk st.heap v) :
    SafeM st (live v) (fun st' _ => st' = st) := by
  cases v with
  | imm _ => exact SafeM.pure_intro hst rfl
  | ref loc cap t =>
    obtain ⟨_, o, ho, hcap⟩ := hv
    unfold SafeM live
    simp only [M_run_bind, M_run_obj, ho, hcap, beq_self_eq_true, ↓reduceIte, M_run_pure]
    exact ⟨HeapExt.refl _, hst, trivial⟩

theorem SafeM_numOf? {st : St} (hst : DefStOk st) {v : Val} (hv : ValOk st.heap v) :
    SafeM st (numOf? v) (fun st' _ => st' = st) := by
  cases v with
  | imm i =>
    cases i <;> exact SafeM.pure_intro hst rfl
  | ref loc cap t =>
    obtain ⟨_, o, ho, hcap⟩ := hv
    unfold SafeM numOf?
    simp only [M_run_bind, M_run_obj, ho, hcap, beq_self_eq_true, ↓reduceIte]
    cases o.cell <;> exact ⟨HeapExt.refl _, hst, rfl⟩

theorem SafeM_isLeaf {st : St} (hst : DefStOk st) {v : Val} (hv : ValOk st.heap v) :
    SafeM st (isLeaf v) (fun st' _ => st' = st) := by
  unfold isLeaf
  by_cases hnat : natClass != .leaf
  · simp [hnat]; exact SafeM.pure_intro hst rfl
  · simp only [hnat, Bool.false_eq_true, ↓reduceIte]
    cases v with
    | imm _ => exact SafeM.pure_intro hst rfl
    | ref loc cap t =>
      obtain ⟨_, o, ho, _⟩ := hv
      unfold SafeM
      simp only [M_run_bind, M_run_obj, ho]
      cases o.cell <;> exact ⟨HeapExt.refl _, hst, rfl⟩

theorem SafeM_natValue {st : St} (hst : DefStOk st) (n : Nat) :
    SafeM st (natValue n) (fun st' v => ValOk st'.heap v) := by
  unfold natValue mkNum
  cases natClass with
  | imm => exact SafeM.pure_intro hst trivial
  | _ => exact SafeM_alloc hst trivial

theorem SafeM_strValue {st : St} (hst : DefStOk st) (s : String) :
    SafeM st (strValue s) (fun st' v => ValOk st'.heap v) := by
  unfold SafeM strValue
  simp only [M_run_bind, M_run_get]
  cases hfind : st.strs.find? (·.1 == s) with
  | some p =>
    have hmem : p ∈ st.strs.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
    have hp : ValOk st.heap p.2 := hst.strsOk p hmem
    have hlive := SafeM_live hst hp
    unfold SafeM at hlive
    simp only [M_run_bind]
    cases hlr : (live p.2).run st with
    | error e => rw [hlr] at hlive; cases e <;> exact hlive
    | ok q =>
      rw [hlr] at hlive
      obtain ⟨hext, hst', rfl⟩ := hlive
      simp only [M_run_pure]
      exact ⟨hext, hst', hp⟩
  | none =>
    have hall := SafeM_alloc hst (c := .str s) trivial
    unfold SafeM at hall
    simp only [M_run_bind]
    cases har : (alloc (.str s) []).run st with
    | error e => rw [har] at hall; cases e <;> exact hall
    | ok q =>
      rw [har] at hall
      obtain ⟨hext, hst', hv⟩ := hall
      simp only [M_run_modify, M_run_pure]
      refine ⟨hext, ⟨hst'.heapOk, hst'.staticsOk, ?_⟩, hv⟩
      intro p hp
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hst'.strsOk p hp
      · exact hv

theorem SafeM_conform {st : St} (hst : DefStOk st) (c : Cls) {v : Val} (hv : ValOk st.heap v) :
    SafeM st (conform c v) (fun st' v' => ValOk st'.heap v') := by
  cases c with
  | irr => exact SafeM.pure_intro hst trivial
  | val => exact SafeM.pure_intro hst hv
  | imm =>
    cases v with
    | imm i => exact SafeM.pure_intro hst trivial
    | ref loc cap t =>
      refine SafeM.bind (SafeM_numOf? hst hv) ?_
      intro st₁ mn _ hst₁ rfl
      cases mn with
      | some n => exact SafeM.pure_intro hst₁ trivial
      | none => exact SafeM.stuck st₁ _
  | leaf =>
    cases v with
    | imm i =>
      cases i with
      | bits n => exact SafeM_alloc hst trivial
      | _ => exact SafeM.stuck st _
    | ref loc cap t =>
      refine SafeM.bind (SafeM_numOf? hst hv) ?_
      intro st₁ mn _ hst₁ rfl
      cases mn with
      | some _ => exact SafeM.pure_intro hst₁ hv
      | none => exact SafeM.stuck st₁ _

theorem SafeM_readOut {st : St} (hst : DefStOk st) (inherit : Bool) {v : Val}
    (hv : ValOk st.heap v) :
    SafeM st (readOut inherit [] v) (fun st' v' => ValOk st'.heap v') := by
  unfold readOut
  refine SafeM.bind (SafeM_isLeaf hst hv) ?_
  intro st₁ b _ hst₁ rfl
  cases b with
  | true =>
    cases v with
    | imm _ => exact SafeM.pure_intro hst₁ hv
    | ref loc cap t =>
      obtain ⟨rfl, o, ho, hcap⟩ := hv
      exact SafeM.pure_intro hst₁ ⟨rfl, o, ho, hcap⟩
  | false =>
    cases inherit <;> exact SafeM.pure_intro hst₁ hv

theorem SafeM_bindAt_many {st : St} (hst : DefStOk st) (P : Prog) (fuel s : Nat) (c : Cls)
    {v : Val} (hv : ValOk st.heap v) :
    SafeM st (bindAt P fuel s .many c v) (fun st' b => b.mode = .many ∧ ValOk st'.heap b.val) := by
  unfold bindAt
  simp only [show (BinderMode.many == .erased) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    BinderMode.isUnique, BinderMode.isBorrowed, BinderMode.usage, Bool.false_and,
    show (Usage.many == .once) = false from rfl]
  refine SafeM.bind (SafeM_conform hst c hv) ?_
  intro st₁ v₁ _ hst₁ hv₁
  simp only [pure_bind]
  refine SafeM.bind (SafeM_isLeaf hst₁ hv₁) ?_
  intro st₂ _ _ hst₂ rfl
  exact SafeM.pure_intro hst₂ ⟨rfl, hv₁⟩

theorem SafeM_ret_shared {st : St} (hst : DefStOk st) (P : Prog) (fuel s cur : Nat) (c : Cls)
    {v : Val} (hv : ValOk st.heap v) :
    SafeM st (ret P fuel s cur .shared c v) (fun st' v' => ValOk st'.heap v') := by
  unfold ret
  refine SafeM.bind (SafeM_conform hst c hv) ?_
  intro st₁ v₁ _ hst₁ hv₁
  have ht : confinedTo s v₁ = false := by
    simp [confinedTo, valOk_taint_eq_nil hv₁]
  simp only [ht, Bool.false_eq_true, ↓reduceIte]
  exact SafeM.pure_intro hst₁ hv₁

theorem taints_eq_nil {h : Heap} {vs : List Val} (hvs : ∀ v ∈ vs, ValOk h v) :
    taints vs = [] := by
  unfold taints
  have aux : ∀ (acc : List Nat) (l : List Val), acc = [] → (∀ v ∈ l, ValOk h v) →
      l.foldl (fun t v => natUnion t v.taint) acc = [] := by
    intro acc l hacc hl
    induction l generalizing acc with
    | nil => exact hacc
    | cons v vs ih =>
      subst hacc
      have hv := valOk_taint_eq_nil (hl v (List.mem_cons_self ..))
      simp only [List.foldl_cons, hv, natUnion, List.foldl_nil]
      exact ih [] rfl (fun w hw => hl w (List.mem_cons_of_mem _ hw))
  exact aux [] vs rfl hvs

theorem SafeM_prim {st : St} (hst : DefStOk st) (p : Prim) {vs : List Val}
    (hvs : ∀ v ∈ vs, ValOk st.heap v) :
    SafeM st (prim p vs) (fun st' v => ValOk st'.heap v) := by
  unfold prim
  refine SafeM.bind (SafeM_forIn_list (I := fun st' _ => st' = st) hst rfl ?_) ?_
  · intro st₀ v acc hv _ hst₀ rfl
    refine SafeM.bind (SafeM_numOf? hst₀ (hvs v hv)) ?_
    intro st₁ mn _ hst₁ rfl
    cases mn with
    | some k => exact SafeM.pure_intro hst₁ rfl
    | none => exact SafeM.stuck st₁ _
  · intro st₁ ns _ hst₁ rfl
    cases p <;> cases ns with
    | nil =>
      first | exact SafeM_natValue hst₁ _ | exact SafeM.stuck st₁ _
    | cons a rest =>
      cases rest with
      | nil =>
        first | exact SafeM_natValue hst₁ _ | exact SafeM.stuck st₁ _
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          first | exact SafeM_natValue hst₁ _ | exact SafeM.pure_intro hst₁ trivial | exact SafeM.stuck st₁ _
        | cons _ _ => exact SafeM.stuck st₁ _

theorem SafeM_construct {st : St} (hst : DefStOk st) (r : Ref) (fields : Array Field)
    {vs : List Val} (hvs : ∀ v ∈ vs, ValOk st.heap v) (c : Cls) :
    SafeM st (construct r fields vs c) (fun st' v => ValOk st'.heap v) := by
  unfold construct
  refine SafeM.bind (SafeM_forIn_list
      (I := fun st' out => ∀ w ∈ out.toList, ValOk st'.heap w) hst (by simp) ?_) ?_
  · intro st₀ fv out hfv hext₀ hst₀ hout
    obtain ⟨f, v⟩ := fv
    have hv₀ : ValOk st₀.heap v := valOk_mono hext₀ (hvs v (List.of_mem_zip hfv).2)
    dsimp only
    cases f.kept with
    | true =>
      refine SafeM.bind (SafeM_conform hst₀ f.cls hv₀) ?_
      intro st₁ w hext₁ hst₁ hw
      refine SafeM.pure_intro hst₁ ?_
      intro u hu
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact valOk_mono hext₁ (hout u hu)
      · exact hw
    | false =>
      refine SafeM.bind (SafeM.pure_intro (Q := fun st' w => ValOk st'.heap w) hst₀ trivial) ?_
      intro st₁ w hext₁ hst₁ hw
      refine SafeM.pure_intro hst₁ ?_
      intro u hu
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact valOk_mono hext₁ (hout u hu)
      · exact hw
  · intro st₁ out _ hst₁ hout
    dsimp only
    by_cases hemp : ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).isEmpty
    · simp only [hemp, ↓reduceIte]
      exact SafeM.pure_intro hst₁ trivial
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      by_cases hwrap : (c == .imm || c == .leaf) &&
          ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).size == 1
      · simp only [hwrap, ↓reduceIte]
        cases hi : ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2))[0]? with
        | none => dsimp only; exact SafeM.bind_stuck st₁ _ _
        | some i =>
          dsimp only
          cases hv : out[i]? with
          | none => dsimp only; exact SafeM.bind_stuck st₁ _ _
          | some v =>
            dsimp only
            exact SafeM_conform hst₁ c (hout v (array_mem_toList_of_getElem? hv))
      · simp only [hwrap, Bool.false_eq_true, ↓reduceIte]
        rw [taints_eq_nil hout]
        exact SafeM_alloc hst₁ hout

theorem SafeM_makePap {st : St} (hst : DefStOk st) (P : Prog) (fuel : Nat) (r : Ref)
    (params : Array Param) (hps : ∀ p ∈ params.toList, p.mode = .many)
    {vs : List Val} (hvs : ∀ v ∈ vs, ValOk st.heap v) :
    SafeM st (makePap P fuel r params vs) (fun st' v => ValOk st'.heap v) := by
  unfold makePap
  refine SafeM.bind (SafeM_forIn_list
      (I := fun st' out => st' = st ∧ ∀ w ∈ out.toList, ValOk st'.heap w) hst ⟨rfl, by simp⟩ ?_) ?_
  · intro st₀ vi out hvi _ hst₀ ⟨rfl, hout⟩
    obtain ⟨v, i⟩ := vi
    have hm : (params[i]?.map (·.mode)).getD .many = .many := by
      cases hp : params[i]? with
      | none => rfl
      | some p =>
        simp [hps p (array_mem_toList_of_getElem? hp)]
    have hct : captureTransfers ((params[i]?.map (·.mode)).getD .many) = false := by
      rw [hm]; rfl
    dsimp only
    rw [hct]
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine SafeM.pure_intro hst₀ ⟨rfl, ?_⟩
    intro u hu
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | hu
    · exact hout u hu
    · rw [hu]; exact hvs v (list_mem_of_mem_zipIdx hvi)
  · intro st₁ out _ hst₁ ⟨rfl, hout⟩
    dsimp only
    rw [taints_eq_nil hout]
    exact SafeM_alloc hst₁ hout

theorem SafeM_formClosure {st : St} (hst : DefStOk st) (P : Prog) (fuel : Nat)
    {env : List Bnd} (henv : EnvDefOk st.heap env)
    {p : Param} {res : ResultMode} (hp : p.mode = .many) (hres : res = .shared)
    (rc : Cls) (fvs : Array Nat) {body : Term} (hbody : TermDefault body) :
    SafeM st (formClosure P fuel env p res rc fvs body) (fun st' v => ValOk st'.heap v) := by
  unfold formClosure
  refine SafeM.bind (SafeM_forIn_list
      (I := fun st' (et : List Bnd × List Nat) => st' = st ∧ EnvDefOk st'.heap et.1 ∧ et.2 = [])
      hst ⟨rfl, henv, rfl⟩ ?_) ?_
  · intro st₀ i et _ _ hst₀ ⟨rfl, henv', ht⟩
    obtain ⟨env', taint⟩ := et
    dsimp only at henv' ht
    subst ht
    cases hget : env[i]? with
    | none => exact SafeM.stuck st₀ _
    | some b =>
      obtain ⟨hbm, hbv⟩ := henv b (List.mem_of_getElem? hget)
      dsimp only
      simp only [hbm, show (BinderMode.many == .erased) = false from rfl, Bool.false_eq_true,
        ↓reduceIte, captureTransfers, BinderMode.isUnique, pure_bind]
      refine SafeM.bind (SafeM_live hst₀ hbv) ?_
      intro st₁ _ _ hst₁ rfl
      have hvt : b.val.taint = [] := valOk_taint_eq_nil hbv
      have hset : EnvDefOk st₁.heap (setBnd env' i b.val) := by
        have aux : ∀ (bs : List Bnd) (k : Nat), EnvDefOk st₁.heap bs →
            EnvDefOk st₁.heap (setBnd bs k b.val) := by
          intro bs
          induction bs with
          | nil => intro k _ x hx; simp [setBnd] at hx
          | cons b0 bs ihbs =>
            intro k hbs x hx
            cases k with
            | zero =>
              simp only [setBnd, List.mem_cons] at hx
              rcases hx with rfl | hx'
              · exact ⟨(hbs b0 (List.mem_cons_self ..)).1, hbv⟩
              · exact hbs x (List.mem_cons_of_mem _ hx')
            | succ k =>
              simp only [setBnd, List.mem_cons] at hx
              rcases hx with hx0 | hx'
              · rw [hx0]; exact hbs b0 (List.mem_cons_self ..)
              · exact ihbs k (fun y hy => hbs y (List.mem_cons_of_mem _ hy)) x hx'
        exact aux env' i henv'
      exact SafeM.pure_intro hst₁ ⟨rfl, hset, by simp [hvt, natUnion]⟩
  · intro st₁ res' _ hst₁ ⟨rfl, henv', ht⟩
    rw [ht]
    exact SafeM_alloc hst₁ ⟨henv', hp, hres, hbody⟩

theorem DataReach_ValOk {h : Heap} (hh : HeapDefOk h) {a : Val} (ha : ValOk h a)
    {l : Nat} (hr : DataReach h a l) :
    ∃ o, h.objs[l]? = some o ∧ CellDefOk h o.cell := by
  induction hr with
  | here =>
    obtain ⟨_, o, ho, _⟩ := ha
    exact ⟨o, ho, (hh _ o ho).2⟩
  | @step loc cap t o r fs v l' ho hcell hv _ ih =>
    have hcellOk : CellDefOk h (.ctor r fs) := by
      have := (hh loc o ho).2
      rwa [hcell] at this
    exact ih (hcellOk v hv)

theorem DataFieldOf_ValOk {h : Heap} (hh : HeapDefOk h) {a v : Val}
    (ha : ValOk h a) (hdf : DataFieldOf h a v) : ValOk h v := by
  obtain ⟨l, o, r, fs, hdr, ho, hcell, hv⟩ := hdf
  obtain ⟨o', ho', hcellOk⟩ := DataReach_ValOk hh ha hdr
  rw [ho] at ho'; cases ho'
  rw [hcell] at hcellOk
  exact hcellOk v hv

theorem SafeM_callExtern {P : Prog} (hP : AllDefault P) {ext : ExternOracle}
    (hextOk : ExternOk P ext) {st : St} (hst : DefStOk st) (fuel : Nat) (r : Ref)
    {ps : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel}
    (hfind : P.find? r = some (.extern ps res rc rs))
    {vs : List Val} (hvs : ∀ v ∈ vs, ValOk st.heap v) :
    SafeM st (callExtern P ext fuel r ps res rc vs) (fun st' v => ValOk st'.heap v) := by
  obtain ⟨hps, hres⟩ := hP.extern hfind
  subst hres
  unfold callExtern
  refine SafeM.bind (SafeM_openRegion hst) ?_
  intro st₁ sc _ hst₁ hheq₁
  have hvs₁ : ∀ v ∈ vs, ValOk st₁.heap v := by rw [hheq₁]; exact hvs
  refine SafeM.bind (SafeM_forIn_list
      (I := fun st' bs => ∀ b ∈ bs, ValOk st'.heap b) hst₁ (by simp) ?_) ?_
  · intro st₀ pv bs hpv hext₀ hst₀ hbs
    have hm := List.of_mem_zip hpv
    have hpm : pv.1.mode = .many := hps pv.1 hm.1
    have hv₀ : ValOk st₀.heap pv.2 := valOk_mono hext₀ (hvs₁ pv.2 hm.2)
    have hstep : SafeM st₀ (bindAt P fuel sc.1 pv.1.mode pv.1.cls pv.2)
        (fun st' b => b.mode = .many ∧ ValOk st'.heap b.val) := by
      rw [hpm]; exact SafeM_bindAt_many hst₀ P fuel sc.1 pv.1.cls hv₀
    refine SafeM.bind hstep ?_
    intro st₂ b hext₂ hst₂ ⟨_, hbv⟩
    refine SafeM.pure_intro hst₂ ?_
    intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact valOk_mono hext₂ (hbs u hu)
    · exact hbv
  · intro st₂ bs _ hst₂ hbs
    unfold SafeM
    simp only [M_run_bind, M_run_get]
    cases hcall : ext r bs st₂.heap with
    | none => trivial
    | some p =>
      obtain ⟨h', v⟩ := p
      obtain ⟨hsz, hnc, hold, hnew, hret, _⟩ := hextOk r ps .shared rc rs bs st₂.heap h' v hfind hcall
      have hext2 : HeapExt st₂.heap h' := by
        refine ⟨hsz, hnc, ?_⟩
        intro l o ho
        obtain ⟨o', ho', hdisj⟩ := hold l o ho
        rcases hdisj with ⟨hcell, hcap⟩ | ⟨_, _, i, p', a, hp', _, huniq, _⟩
        · cases o; cases o'; simp at hcell hcap; subst hcell; subst hcap; exact ho'
        · have hp'm : p' ∈ ps.toList := array_mem_toList_of_getElem? hp'
          rw [hps p' hp'm] at huniq
          cases huniq
      have hEFV : ∀ w, ExternFieldVal P ps bs st₂.heap h' w → ValOk h' w := by
        intro w hw
        rcases hw with ⟨i, rfl⟩ | ⟨loc, cap, o, rfl, _, ho, hcap, _⟩ | ⟨i, p', a, _, ha, _, hcase⟩
        · trivial
        · exact ⟨rfl, o, ho, hcap⟩
        · have haok : ValOk st₂.heap a := hbs a (List.mem_of_getElem? ha)
          rcases hcase with ⟨rfl, _⟩ | hdf
          · exact valOk_mono hext2 haok
          · exact valOk_mono hext2 (DataFieldOf_ValOk hst₂.heapOk haok hdf)
      have hERV : ValOk h' v := by
        rcases hret with ⟨i, rfl⟩ | ⟨loc, cap, o, rfl, _, ho, hcap, _⟩ | ⟨i, p', a, _, ha, _, hcase⟩
        · trivial
        · exact ⟨rfl, o, ho, hcap⟩
        · have haok : ValOk st₂.heap a := hbs a (List.mem_of_getElem? ha)
          rcases hcase with ⟨rfl, _⟩ | ⟨hdf, _⟩
          · exact valOk_mono hext2 haok
          · exact valOk_mono hext2 (DataFieldOf_ValOk hst₂.heapOk haok hdf)
      have hheap' : HeapDefOk h' := by
        intro l o ho
        by_cases hlt : l < st₂.heap.objs.size
        · obtain ⟨o0, ho0⟩ : ∃ o0, st₂.heap.objs[l]? = some o0 :=
            ⟨st₂.heap.objs[l], Array.getElem?_eq_getElem hlt⟩
          have hoEq := hext2.2.2 l o0 ho0
          rw [ho] at hoEq; injection hoEq with hoEq'; subst hoEq'
          obtain ⟨hcap0, hcell0⟩ := hst₂.heapOk l o ho0
          exact ⟨Nat.lt_of_lt_of_le hcap0 hnc, hcell0.mono hext2⟩
        · have hle : st₂.heap.objs.size ≤ l := Nat.le_of_not_lt hlt
          obtain ⟨hinp, hcap, hbody⟩ := hnew l o hle ho
          refine ⟨hcap, ?_⟩
          cases hc : o.cell with
          | ctor _ fs =>
            rw [hc] at hbody
            exact fun w hw => hEFV w (hbody w hw).1
          | num _ | str _ => trivial
          | pap _ as =>
            rw [hc] at hbody
            exact fun w hw => (hbody w hw).2.1
          | clo _ _ _ _ _ _ =>
            rw [hc] at hinp; exact False.elim hinp
          | once _ _ =>
            rw [hc] at hinp; exact False.elim hinp
      have hst₃ : DefStOk { st₂ with heap := h' } :=
        ⟨hheap', fun q hq => valOk_mono hext2 (hst₂.staticsOk q hq),
          fun q hq => valOk_mono hext2 (hst₂.strsOk q hq)⟩
      have hrest : SafeM { st₂ with heap := h' } (do
          let v ← ret P fuel sc.1 sc.2 .shared rc v
          closeRegion sc.1
          pure v) (fun st' v' => ValOk st'.heap v') := by
        refine SafeM.bind (SafeM_ret_shared hst₃ P fuel sc.1 sc.2 rc hERV) ?_
        intro st₄ v' _ hst₄ hv'
        refine SafeM.bind (SafeM_closeRegion hst₄ sc.1) ?_
        intro st₅ _ _ hst₅ hheq₅
        exact SafeM.pure_intro hst₅ (by rw [hheq₅]; exact hv')
      unfold SafeM at hrest
      rw [M_run_bind, M_run_set]
      dsimp only
      cases hr : ((do
          let v ← ret P fuel sc.1 sc.2 .shared rc v
          closeRegion sc.1
          pure v).run { st₂ with heap := h' }) with
      | error e => rw [hr] at hrest; cases e <;> exact hrest
      | ok q =>
        rw [hr] at hrest
        obtain ⟨hext3, hst', hv'⟩ := hrest
        exact ⟨hext2.trans hext3, hst', hv'⟩

theorem SafeM_select {P : Prog} (hP : AllDefault P) {st : St} (hst : DefStOk st)
    (k : CaseInfo) {mv : Val} (hmv : ValOk st.heap mv) :
    SafeM st (select P k mv) (fun st' res => ∀ p ∈ res.2.toList, ValOk st'.heap p.1 ∧ p.2 = false) := by
  unfold select
  have hfieldsDef : ∀ (ci : Nat) (f : Field),
      f ∈ (match (P.ctorsOf k.ind)[ci]? with
        | some c => match P.ctorOf? c with | some (_, _, _, fs) => fs | none => #[]
        | none => #[]).toList → f.mode = .many := by
    intro ci f hf
    cases hc : (P.ctorsOf k.ind)[ci]? with
    | none => rw [hc] at hf; simp at hf
    | some c =>
      rw [hc] at hf
      dsimp only at hf
      cases hco : P.ctorOf? c with
      | none => rw [hco] at hf; simp at hf
      | some q =>
        rw [hco] at hf
        exact (hP.ctor hco f hf).1
  have hirr : ∀ (ci : Nat), ∀ p ∈ ((match (P.ctorsOf k.ind)[ci]? with
        | some c => match P.ctorOf? c with | some (_, _, _, fs) => fs | none => #[]
        | none => #[]).map fun (f : Field) => (Val.imm .irr, f.mode == BinderMode.erased)).toList,
      ValOk st.heap p.1 ∧ p.2 = false := by
    intro ci p hp
    simp only [Array.toList_map, List.mem_map] at hp
    obtain ⟨f, hf, rfl⟩ := hp
    have hfm := hfieldsDef ci f hf
    exact ⟨trivial, by simp [hfm]⟩
  have hwrap : SafeM st (match P.wrapperField? k.ind with
        | some wi => pure (0, ((match (P.ctorsOf k.ind)[0]? with
            | some c => match P.ctorOf? c with | some (_, _, _, fs) => fs | none => #[]
            | none => #[]).map fun (f : Field) => (Val.imm .irr, f.mode == BinderMode.erased)).set! wi (mv, false))
        | none => stuckM)
      (fun st' res => ∀ p ∈ res.2.toList, ValOk st'.heap p.1 ∧ p.2 = false) := by
    cases hwi : P.wrapperField? k.ind with
    | none => exact SafeM.stuck st _
    | some wi =>
      refine SafeM.pure_intro hst ?_
      intro p hp
      have hmem := Array.mem_toList_iff.mp hp
      have hsub := array_mem_of_mem_set! hmem
      rcases hsub with hsub | rfl
      · exact hirr 0 p (Array.mem_toList_iff.mpr hsub)
      · exact ⟨hmv, rfl⟩
  by_cases hnat : P.nat == some k.ind
  · simp only [hnat, ↓reduceIte]
    refine SafeM.bind (SafeM_numOf? hst hmv) ?_
    intro st₁ mn _ hst₁ rfl
    cases mn with
    | none => exact SafeM.stuck st₁ _
    | some m =>
      cases m with
      | zero => exact SafeM.pure_intro hst₁ (by simp)
      | succ m =>
        refine SafeM.bind (SafeM_natValue hst₁ m) ?_
        intro st₂ v _ hst₂ hv
        exact SafeM.pure_intro hst₂ (by simp [hv])
  · simp only [hnat, Bool.false_eq_true, ↓reduceIte]
    cases mv with
    | imm i =>
      cases i with
      | con r =>
        dsimp only
        cases hco : P.ctorOf? r with
        | none => exact SafeM.stuck st _
        | some q =>
          dsimp only
          by_cases hind : q.1 == k.ind
          · simp only [hind, ↓reduceIte]
            exact SafeM.pure_intro hst (hirr q.2.1)
          · simp only [hind, Bool.false_eq_true, ↓reduceIte]
            exact hwrap
      | irr =>
        dsimp only
        by_cases hcs : (P.ctorsOf k.ind).size == 1
        · simp only [hcs, ↓reduceIte]
          exact SafeM.pure_intro hst (hirr 0)
        · simp only [hcs, Bool.false_eq_true, ↓reduceIte]
          exact SafeM.stuck st _
      | bits _ => exact hwrap
    | ref loc cap t =>
      obtain ⟨rfl, o, ho, hcap⟩ := hmv
      unfold SafeM
      simp only [M_run_bind, M_run_obj, ho, hcap, beq_self_eq_true, ↓reduceIte]
      cases hcell : o.cell with
      | num _ => dsimp only; exact hwrap
      | ctor r fs =>
        dsimp only
        cases hco : P.ctorOf? r with
        | none => simp only [M_run_stuck]
        | some q =>
          dsimp only
          obtain ⟨ind, cidx, nP, fdefs⟩ := q
          by_cases hind : ind == k.ind
          · simp only [hind, ↓reduceIte]
            have hfdef : ∀ f ∈ fdefs.toList, f.mode = .many := fun f hf => (hP.ctor hco f hf).1
            have hfsOk : ∀ w ∈ fs.toList, ValOk st.heap w := by
              have hok := (hst.heapOk loc o ho).2
              rw [hcell] at hok; exact hok
            have hbody : SafeM st (do
                let mut out : Array (Val × Bool) := #[]
                for (f, i) in fdefs.zipIdx do
                  let v ← readOut (f.fmode == .inherited) [] (fs[i]?.getD (.imm .irr))
                  let v ← if f.kept then conform f.cls v else pure (.imm .irr)
                  out := out.push (v, f.mode == .erased)
                pure (cidx, out))
                (fun st' res => ∀ p ∈ res.2.toList, ValOk st'.heap p.1 ∧ p.2 = false) := by
              refine SafeM.bind (SafeM_forIn_array
                  (I := fun st' out => ∀ p ∈ out.toList, ValOk st'.heap p.1 ∧ p.2 = false)
                  hst (by simp) ?_) ?_
              · intro st₀ fi out hfi hext₀ hst₀ hout
                obtain ⟨f, i⟩ := fi
                have hfm : f.mode = .many := by
                  have hmem := Array.mem_toList_iff.mp hfi
                  obtain ⟨idx, hidx, heq⟩ := Array.mem_iff_getElem.mp hmem
                  simp only [Array.getElem_zipIdx] at heq
                  have hlt : idx < fdefs.size := by simpa using hidx
                  have hfeq : f = fdefs[idx] := by
                    have := congrArg Prod.fst heq; exact this.symm
                  rw [hfeq]
                  exact hfdef fdefs[idx] (Array.mem_toList_iff.mpr (Array.getElem_mem hlt))
                have hfv : ValOk st₀.heap (fs[i]?.getD (.imm .irr)) := by
                  cases hget : fs[i]? with
                  | none => trivial
                  | some w =>
                    exact valOk_mono hext₀ (hfsOk w (array_mem_toList_of_getElem? hget))
                dsimp only
                refine SafeM.bind (SafeM_readOut hst₀ (f.fmode == .inherited) hfv) ?_
                intro st₁ v₁ hext₁ hst₁ hv₁
                cases f.kept with
                | true =>
                  refine SafeM.bind (SafeM_conform hst₁ f.cls hv₁) ?_
                  intro st₂ v₂ hext₂ hst₂ hv₂
                  refine SafeM.pure_intro hst₂ ?_
                  intro p hp
                  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
                  rcases hp with hp | rfl
                  · obtain ⟨hp1, hp2⟩ := hout p hp
                    exact ⟨valOk_mono (hext₁.trans hext₂) hp1, hp2⟩
                  · exact ⟨hv₂, by simp [hfm]⟩
                | false =>
                  refine SafeM.bind (SafeM.pure_intro (Q := fun st' w => ValOk st'.heap w) hst₁ trivial) ?_
                  intro st₂ v₂ hext₂ hst₂ hv₂
                  refine SafeM.pure_intro hst₂ ?_
                  intro p hp
                  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
                  rcases hp with hp | rfl
                  · obtain ⟨hp1, hp2⟩ := hout p hp
                    exact ⟨valOk_mono (hext₁.trans hext₂) hp1, hp2⟩
                  · exact ⟨hv₂, by simp [hfm]⟩
              · intro st₁ out _ hst₁ hout
                exact SafeM.pure_intro hst₁ hout
            exact hbody
          · simp only [hind, Bool.false_eq_true, ↓reduceIte, M_run_bind, M_run_stuck]
      | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ => simp only [M_run_stuck]

/-! ## Main Mutual Induction Over `Eval.lean`'s Evaluator -/

/-- Combined safety statement for all 8 mutually recursive functions of `Eval.lean`
at fuel `n` under `AllDefault P` and `ExternOk P ext`. -/
def EvalBundle (P : Prog) (ext : ExternOracle) (n : Nat) : Prop :=
  (∀ st env t, DefStOk st → EnvDefOk st.heap env → TermDefault t →
    SafeM st (eval P ext n env t) (fun st' v => ValOk st'.heap v)) ∧
  (∀ st env h args c, DefStOk st → EnvDefOk st.heap env → TermDefault h →
    (∀ a ∈ args, TermDefault a) →
    SafeM st (spine P ext n env h args c) (fun st' v => ValOk st'.heap v)) ∧
  (∀ st r vs c, DefStOk st → (∀ v ∈ vs, ValOk st.heap v) →
    SafeM st (callWith P ext n r vs c) (fun st' v => ValOk st'.heap v)) ∧
  (∀ st ps res rc body vs, DefStOk st →
    (∀ p ∈ ps.toList, p.mode = .many) → res = .shared → TermDefault body →
    (∀ v ∈ vs, ValOk st.heap v) →
    SafeM st (enter P ext n ps res rc body vs) (fun st' v => ValOk st'.heap v)) ∧
  (∀ st r body rc, DefStOk st → TermDefault body →
    SafeM st (static P ext n r body rc) (fun st' v => ValOk st'.heap v)) ∧
  (∀ st f vs c, DefStOk st → ValOk st.heap f → (∀ v ∈ vs, ValOk st.heap v) →
    SafeM st (applyAll P ext n f vs c) (fun st' v => ValOk st'.heap v)) ∧
  (∀ st f a c, DefStOk st → ValOk st.heap f → ValOk st.heap a →
    SafeM st (applyOne P ext n f a c) (fun st' v => ValOk st'.heap v)) ∧
  (∀ st env t args, DefStOk st → EnvDefOk st.heap env → TermDefault t →
    (∀ p ∈ args, ValOk st.heap p.1 ∧ p.2 = false) →
    SafeM st (applyAlt P ext n env t args) (fun st' v => ValOk st'.heap v))

theorem evalBundle_all {P : Prog} (hP : AllDefault P) {ext : ExternOracle}
    (hextOk : ExternOk P ext) (n : Nat) : EvalBundle P ext n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intros; rw [eval]; exact SafeM.oof _ _
    · intros; rw [spine]; exact SafeM.oof _ _
    · intros; rw [callWith]; exact SafeM.oof _ _
    · intros; rw [enter]; exact SafeM.oof _ _
    · intros; rw [static]; exact SafeM.oof _ _
    · intros; rw [applyAll]; exact SafeM.oof _ _
    · intros; rw [applyOne]; exact SafeM.oof _ _
    · intros; rw [applyAlt]; exact SafeM.oof _ _
  | succ n ih =>
    obtain ⟨ihEval, ihSpine, ihCall, ihEnter, ihStatic, ihAppAll, ihAppOne, ihAppAlt⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- 1. `eval`
    · intro st env t hst henv ht
      cases t with
      | irr => rw [eval]; exact SafeM.pure_intro hst trivial
      | var i c =>
        rw [eval]
        dsimp only
        cases hget : env[i]? with
        | none => exact SafeM.stuck st _
        | some b =>
          dsimp only
          obtain ⟨hbm, hbv⟩ := henv b (List.mem_of_getElem? hget)
          simp only [hbm, show (BinderMode.many == .erased) = false from rfl, Bool.false_eq_true, ↓reduceIte]
          refine SafeM.bind (SafeM_live hst hbv) ?_
          intro st₁ _ _ hst₁ rfl
          exact SafeM_conform hst₁ c hbv
      | natLit k => rw [eval]; exact SafeM_natValue hst k
      | strLit s => rw [eval]; exact SafeM_strValue hst s
      | const r c => rw [eval]; exact ihSpine st env (.const r c) [] c hst henv ht (by simp)
      | app f a c =>
        rw [eval]
        have hc := TermDefault.collect (.app f a c) [] ht (by simp)
        exact ihSpine st env (collect (.app f a c) []).1 (collect (.app f a c) []).2 c
          hst henv hc.1 hc.2
      | lam p res rc fvs body =>
        rw [eval]
        obtain ⟨hp, hres, hb⟩ := ht.lam
        exact SafeM_formClosure hst P n henv hp hres rc fvs hb
      | letE m d v b =>
        obtain ⟨rfl, hv, hb⟩ := ht.letE
        simp only [eval]
        refine SafeM.bind (ihEval st env v hst henv hv) ?_
        intro st₁ x hext₁ hst₁ hx
        refine SafeM.bind (SafeM_openRegion hst₁) ?_
        intro st₂ sc hext₂ hst₂ hheq₂
        have hx₂ : ValOk st₂.heap x := by rw [hheq₂]; exact hx
        refine SafeM.bind (SafeM_bindAt_many hst₂ P n sc.1 d hx₂) ?_
        intro st₃ bnd hext₃ hst₃ ⟨hbm, hbv⟩
        have henv₃ : EnvDefOk st₃.heap (bnd :: env) := by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact ⟨hbm, hbv⟩
          · exact ⟨(henv y hy').1, valOk_mono ((hext₁.trans hext₂).trans hext₃) (henv y hy').2⟩
        refine SafeM.bind (ihEval st₃ (bnd :: env) b hst₃ henv₃ hb) ?_
        intro st₄ r _ hst₄ hr
        have hconf : confinedTo sc.1 r = false := by simp [confinedTo, valOk_taint_eq_nil hr]
        simp only [hconf, Bool.false_eq_true, ↓reduceIte]
        refine SafeM.bind (SafeM_closeRegion hst₄ sc.1) ?_
        intro st₅ _ _ hst₅ hheq₅
        exact SafeM.pure_intro hst₅ (by rw [hheq₅]; exact hr)
      | proj s i e c =>
        rw [eval]
        dsimp only
        refine SafeM.bind (ihEval st env e hst henv ht.proj) ?_
        intro st₁ v _ hst₁ hv
        refine SafeM.bind (SafeM_live hst₁ hv) ?_
        intro st₂ _ _ hst₂ rfl
        cases hcs : (P.ctorsOf s)[0]? with
        | none => exact SafeM.stuck st₂ _
        | some ctor =>
          dsimp only
          cases hco : P.ctorOf? ctor with
          | none => exact SafeM.stuck st₂ _
          | some q =>
            dsimp only
            obtain ⟨_, _, _, fields⟩ := q
            cases hf : fields[i]? with
            | none => exact SafeM.stuck st₂ _
            | some f =>
              dsimp only
              have hfm := (hP.ctor hco f (array_mem_toList_of_getElem? hf)).1
              simp only [hfm, show (BinderMode.many == .erased) = false from rfl,
                Bool.false_eq_true, ↓reduceIte]
              by_cases hfirr : f.cls == .irr
              · simp only [hfirr, ↓reduceIte]
                exact SafeM.pure_intro hst₂ trivial
              · simp only [hfirr, Bool.false_eq_true, ↓reduceIte]
                have hasWrap : SafeM st₂
                    (if P.wrapperField? s == some i then conform c v else stuckM)
                    (fun st' v' => ValOk st'.heap v') := by
                  by_cases hw : P.wrapperField? s == some i
                  · simp only [hw, ↓reduceIte]; exact SafeM_conform hst₂ c hv
                  · simp only [hw, Bool.false_eq_true, ↓reduceIte]; exact SafeM.stuck st₂ _
                cases v with
                | imm _ => exact hasWrap
                | ref loc cap tv =>
                  obtain ⟨rfl, o, ho, _⟩ := hv
                  unfold SafeM
                  simp only [M_run_bind, M_run_obj, ho]
                  cases hcell : o.cell with
                  | num _ => exact hasWrap
                  | ctor r' fs =>
                    by_cases hr' : r' == ctor
                    · simp only [hr', ↓reduceIte]
                      cases hfsi : fs[i]? with
                      | none => trivial
                      | some fv =>
                        have hfv : ValOk st₂.heap fv := by
                          have hok := (hst₂.heapOk loc o ho).2
                          rw [hcell] at hok
                          exact hok fv (array_mem_toList_of_getElem? hfsi)
                        exact SafeM.bind (SafeM_readOut hst₂ (f.fmode == .inherited) hfv)
                          (fun st₃ u _ hst₃ hu => SafeM_conform hst₃ c hu)
                    · simp only [hr', Bool.false_eq_true, ↓reduceIte]; trivial
                  | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ => trivial
      | case k major alts extra c =>
        obtain ⟨hmj, halts, hextra⟩ := ht.case
        have hcont : ∀ st₁ mv, HeapExt st.heap st₁.heap → DefStOk st₁ → ValOk st₁.heap mv →
            SafeM st₁ (do
              let (cidx, fields) ← select P k mv
              let some alt := k.alts[cidx]? | stuckM
              let some altT := alts[cidx]? | stuckM
              let altArgs := alt.args.toList.map fun
                | .field i => fields[i]?.getD (.imm .irr, false)
                | .irr => (.imm .irr, false)
                | .unit => (.imm .irr, false)
              let r ← applyAlt P ext n env altT altArgs
              let mut ex : List Val := []
              for e in extra.toList do
                ex := ex ++ [← eval P ext n env e]
              applyAll P ext n r ex c) (fun st' v => ValOk st'.heap v) := by
          intro st₁ mv hext₁ hst₁ hmv
          refine SafeM.bind (SafeM_select hP hst₁ k hmv) ?_
          intro st₂ sel hext₂ hst₂ hsel
          obtain ⟨cidx, fields⟩ := sel
          dsimp only at hsel ⊢
          cases halt : k.alts[cidx]? with
          | none => exact SafeM.stuck st₂ _
          | some alt =>
            dsimp only
            cases haltT : alts[cidx]? with
            | none => exact SafeM.stuck st₂ _
            | some altT =>
              dsimp only
              have haltTOk : TermDefault altT :=
                halts altT (array_mem_toList_of_getElem? haltT)
              have hargsOk : ∀ p ∈ (alt.args.toList.map fun fa => match fa with
                  | .field i => fields[i]?.getD (.imm .irr, false)
                  | .irr => (.imm .irr, false)
                  | .unit => (.imm .irr, false)), ValOk st₂.heap p.1 ∧ p.2 = false := by
                intro p hp
                rw [List.mem_map] at hp
                obtain ⟨fa, _, rfl⟩ := hp
                cases fa with
                | irr | unit => exact ⟨trivial, rfl⟩
                | field i =>
                  dsimp only
                  cases hget : fields[i]? with
                  | none => exact ⟨trivial, rfl⟩
                  | some q =>
                    exact hsel q (array_mem_toList_of_getElem? hget)
              refine SafeM.bind (ihAppAlt st₂ env altT _ hst₂ (henv.mono (hext₁.trans hext₂)) haltTOk hargsOk) ?_
              intro st₃ r hext₃ hst₃ hr
              refine SafeM.bind (SafeM_forIn_list (init := ([] : List Val))
                  (I := fun st' vs => ∀ v ∈ vs, ValOk st'.heap v) hst₃ (fun _ hv => by cases hv) ?_) ?_
              · intro st₀ e acc he hext₀ hst₀ hacc
                have henv₀ : EnvDefOk st₀.heap env :=
                  henv.mono (((hext₁.trans hext₂).trans hext₃).trans hext₀)
                refine SafeM.bind (ihEval st₀ env e hst₀ henv₀ (hextra e he)) ?_
                intro st₄ w hext₄ hst₄ hw
                refine SafeM.pure_intro hst₄ ?_
                intro u hu
                simp only [List.mem_append, List.mem_singleton] at hu
                rcases hu with hu | rfl
                · exact valOk_mono hext₄ (hacc u hu)
                · exact hw
              · intro st₄ ex hext₄ hst₄ hex
                exact ihAppAll st₄ r ex c hst₄ (valOk_mono hext₄ hr) hex
        cases major with
        | var j mc =>
          simp only [eval]
          cases hget : env[j]? with
          | none => exact SafeM.bind_stuck st _ _
          | some b =>
            dsimp only
            obtain ⟨hbm, hbv⟩ := henv b (List.mem_of_getElem? hget)
            simp only [hbm, show (BinderMode.many == .erased) = false from rfl,
              Bool.false_eq_true, ↓reduceIte, BinderMode.isUnique, pure_bind]
            refine SafeM.bind (SafeM_live hst hbv) ?_
            intro st₁ _ _ hst₁ rfl
            refine SafeM.bind (SafeM_conform hst₁ mc hbv) ?_
            intro st₂ v₂ hext₂ hst₂ hv₂
            exact hcont st₂ v₂ hext₂ hst₂ hv₂
        | _ =>
          simp only [eval]
          exact SafeM.bind (ihEval st env _ hst henv hmj) hcont
    -- 2. `spine`
    · intro st env h args c hst henv hh hargs
      cases h with
      | const r rc =>
        simp only [spine]
        refine SafeM.bind (SafeM_forIn_list (init := ([] : List Val))
            (I := fun st' vs => ∀ v ∈ vs, ValOk st'.heap v) hst (fun _ hv => by cases hv) ?_) ?_
        · intro st₀ ai vs hai hext₀ hst₀ hvs
          obtain ⟨a, i⟩ := ai
          dsimp only
          split
          · split
            · simp only [pure_bind]
              refine SafeM.pure_intro hst₀ ?_
              intro u hu
              simp only [List.mem_append, List.mem_singleton] at hu
              rcases hu with hu | rfl
              · exact hvs u hu
              · trivial
            · refine SafeM.bind (ihEval st₀ env a hst₀ (henv.mono hext₀)
                (hargs a (list_mem_of_mem_zipIdx hai))) ?_
              intro st₁ w hext₁ hst₁ hw
              refine SafeM.pure_intro hst₁ ?_
              intro u hu
              simp only [List.mem_append, List.mem_singleton] at hu
              rcases hu with hu | rfl
              · exact valOk_mono hext₁ (hvs u hu)
              · exact hw
          · refine SafeM.bind (ihEval st₀ env a hst₀ (henv.mono hext₀)
              (hargs a (list_mem_of_mem_zipIdx hai))) ?_
            intro st₁ w hext₁ hst₁ hw
            refine SafeM.pure_intro hst₁ ?_
            intro u hu
            simp only [List.mem_append, List.mem_singleton] at hu
            rcases hu with hu | rfl
            · exact valOk_mono hext₁ (hvs u hu)
            · exact hw
        · intro st₁ vs _ hst₁ hvs
          exact ihCall st₁ r vs c hst₁ hvs
      | _ =>
        simp only [spine]
        refine SafeM.bind (ihEval st env _ hst henv hh) ?_
        intro st₁ fv hext₁ hst₁ hfv
        refine SafeM.bind (SafeM_forIn_list (init := ([] : List Val))
            (I := fun st' vs => ∀ v ∈ vs, ValOk st'.heap v) hst₁ (fun _ hv => by cases hv) ?_) ?_
        · intro st₀ a vs ha hext₀ hst₀ hvs
          refine SafeM.bind (ihEval st₀ env a hst₀ (henv.mono (hext₁.trans hext₀)) (hargs a ha)) ?_
          intro st₂ w hext₂ hst₂ hw
          refine SafeM.pure_intro hst₂ ?_
          intro u hu
          simp only [List.mem_append, List.mem_singleton] at hu
          rcases hu with hu | rfl
          · exact valOk_mono hext₂ (hvs u hu)
          · exact hw
        · intro st₂ vs hext₂ hst₂ hvs
          exact ihAppAll st₂ fv vs c hst₂ (valOk_mono hext₂ hfv) hvs
    -- 3. `callWith`
    · intro st r vs c hst hvs
      rw [callWith]
      cases hfind : P.find? r with
      | none => exact SafeM.stuck st _
      | some d =>
        cases d with
        | body params res rc rs body =>
          obtain ⟨hps, hres, hbody⟩ := hP.body hfind
          by_cases hlt : vs.length < params.size
          · simp only [hlt, ↓reduceIte]
            exact SafeM_makePap hst P n r params hps hvs
          · simp only [hlt, ↓reduceIte]
            by_cases hz : params.size == 0
            · simp only [hz, ↓reduceIte]
              refine SafeM.bind (ihStatic st r body rc hst hbody) ?_
              intro st₁ f hext₁ hst₁ hfv
              exact ihAppAll st₁ f (vs.drop params.size) c hst₁ hfv
                (fun v hv => valOk_mono hext₁ (hvs v (List.mem_of_mem_drop hv)))
            · simp only [hz, Bool.false_eq_true, ↓reduceIte]
              refine SafeM.bind (ihEnter st params res rc body (vs.take params.size) hst hps hres hbody
                (fun v hv => hvs v (List.mem_of_mem_take hv))) ?_
              intro st₁ f hext₁ hst₁ hfv
              exact ihAppAll st₁ f (vs.drop params.size) c hst₁ hfv
                (fun v hv => valOk_mono hext₁ (hvs v (List.mem_of_mem_drop hv)))
        | ctor ind ci nP fields =>
          by_cases hlt : vs.length < nP + fields.size
          · simp only [hlt, ↓reduceIte]
            exact SafeM_makePap hst P n r #[] (by simp) hvs
          · simp only [hlt, ↓reduceIte]
            by_cases hgt : vs.length > nP + fields.size
            · simp only [hgt, ↓reduceIte]; exact SafeM.stuck st _
            · simp only [hgt, ↓reduceIte]
              exact SafeM_construct hst r fields (fun v hv => hvs v (List.mem_of_mem_drop hv)) c
        | prim p =>
          by_cases hlt : vs.length < p.arity
          · simp only [hlt, ↓reduceIte]
            exact SafeM_makePap hst P n r #[] (by simp) hvs
          · simp only [hlt, ↓reduceIte]
            by_cases hgt : vs.length > p.arity
            · simp only [hgt, ↓reduceIte]; exact SafeM.stuck st _
            · simp only [hgt, ↓reduceIte]
              refine SafeM.bind (SafeM_prim hst p hvs) ?_
              intro st₁ v _ hst₁ hv
              exact SafeM_conform hst₁ c hv
        | extern params res rc rs =>
          obtain ⟨hps, _⟩ := hP.extern hfind
          by_cases hlt : vs.length < params.size
          · simp only [hlt, ↓reduceIte]
            exact SafeM_makePap hst P n r params hps hvs
          · simp only [hlt, ↓reduceIte]
            refine SafeM.bind (SafeM_callExtern hP hextOk hst n r hfind
              (fun v hv => hvs v (List.mem_of_mem_take hv))) ?_
            intro st₁ f hext₁ hst₁ hfv
            exact ihAppAll st₁ f (vs.drop params.size) c hst₁ hfv
              (fun v hv => valOk_mono hext₁ (hvs v (List.mem_of_mem_drop hv)))
        | ind _ => exact SafeM.pure_intro hst trivial
        | caseDef _ | stuck _ _ _ _ => exact SafeM.stuck st _
    -- 4. `enter`
    · intro st ps res rc body vs hst hps hres hbody hvs
      subst hres
      rw [enter]
      refine SafeM.bind (SafeM_openRegion hst) ?_
      intro st₁ sc _ hst₁ hheq₁
      have hvs₁ : ∀ v ∈ vs, ValOk st₁.heap v := by rw [hheq₁]; exact hvs
      refine SafeM.bind (SafeM_forIn_list
          (I := fun st' env => EnvDefOk st'.heap env) hst₁ (fun _ hb => by cases hb) ?_) ?_
      · intro st₀ pv env hpv hext₀ hst₀ henv
        have hm := List.of_mem_zip hpv
        have hpm : pv.1.mode = .many := hps pv.1 hm.1
        have hv₀ : ValOk st₀.heap pv.2 := valOk_mono hext₀ (hvs₁ pv.2 hm.2)
        have hstep : SafeM st₀ (bindAt P n sc.1 pv.1.mode pv.1.cls pv.2)
            (fun st' b => b.mode = .many ∧ ValOk st'.heap b.val) := by
          rw [hpm]; exact SafeM_bindAt_many hst₀ P n sc.1 pv.1.cls hv₀
        refine SafeM.bind hstep ?_
        intro st₂ b hext₂ hst₂ ⟨hbm, hbv⟩
        refine SafeM.pure_intro hst₂ ?_
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨hbm, hbv⟩
        · exact ⟨(henv y hy').1, valOk_mono hext₂ (henv y hy').2⟩
      · intro st₂ env _ hst₂ henv
        refine SafeM.bind (ihEval st₂ env body hst₂ henv hbody) ?_
        intro st₃ r _ hst₃ hr
        refine SafeM.bind (SafeM_ret_shared hst₃ P n sc.1 sc.2 rc hr) ?_
        intro st₄ r' _ hst₄ hr'
        refine SafeM.bind (SafeM_closeRegion hst₄ sc.1) ?_
        intro st₅ _ _ hst₅ hheq₅
        exact SafeM.pure_intro hst₅ (by rw [hheq₅]; exact hr')
    -- 5. `static`
    · intro st r body rc hst hbody
      rw [static]
      unfold SafeM
      simp only [M_run_bind, M_run_get]
      cases hfind : st.statics.find? (·.1 == r) with
      | some p =>
        have hmem : p ∈ st.statics.toList :=
          Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
        have hp : ValOk st.heap p.2 := hst.staticsOk p hmem
        have hlive := SafeM_live hst hp
        unfold SafeM at hlive
        simp only [M_run_bind]
        cases hlr : (live p.2).run st with
        | error e => rw [hlr] at hlive; cases e <;> exact hlive
        | ok q =>
          rw [hlr] at hlive
          obtain ⟨hext, hst', rfl⟩ := hlive
          simp only [M_run_pure]
          exact ⟨hext, hst', hp⟩
      | none =>
        have hev := SafeM.bind (ihEval st [] body hst (fun _ hb => by cases hb) hbody)
          (fun st₁ v _ hst₁ hv => SafeM_conform hst₁ rc hv)
        unfold SafeM at hev
        simp only [M_run_bind]
        cases her : (eval P ext n [] body).run st with
        | error e =>
          rw [M_run_bind, her] at hev
          cases e <;> exact hev
        | ok q1 =>
          rw [M_run_bind, her] at hev
          dsimp only at hev ⊢
          cases hcr : (conform rc q1.1).run q1.2 with
          | error e =>
            rw [hcr] at hev
            cases e <;> exact hev
          | ok q2 =>
            rw [hcr] at hev
            obtain ⟨hext, hst', hv⟩ := hev
            simp only [M_run_modify, M_run_pure]
            refine ⟨hext, ⟨hst'.heapOk, ?_, hst'.strsOk⟩, hv⟩
            intro p hp
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · exact hst'.staticsOk p hp
            · exact hv
    -- 6. `applyAll`
    · intro st f vs c hst hf hvs
      cases vs with
      | nil => rw [applyAll]; exact SafeM_conform hst c hf
      | cons a rest =>
        rw [applyAll]
        refine SafeM.bind (ihAppOne st f a (if rest.isEmpty then c else .val) hst hf
          (hvs a (List.mem_cons_self ..))) ?_
        intro st₁ g hext₁ hst₁ hg
        exact ihAppAll st₁ g rest c hst₁ hg
          (fun v hv => valOk_mono hext₁ (hvs v (List.mem_cons_of_mem _ hv)))
    -- 7. `applyOne`
    · intro st f a c hst hf ha
      cases f with
      | imm i =>
        cases i with
        | irr => rw [applyOne]; exact SafeM.pure_intro hst trivial
        | con _ | bits _ => simp only [applyOne]; exact SafeM.stuck st _
      | ref loc cap t =>
        rw [applyOne]
        obtain ⟨rfl, o, ho, hcap⟩ := hf
        unfold SafeM
        simp only [M_run_bind, M_run_obj, ho, hcap, beq_self_eq_true, ↓reduceIte]
        have hcellOk := (hst.heapOk loc o ho).2
        cases hcell : o.cell with
        | clo env p res rc fvs body =>
          rw [hcell] at hcellOk
          obtain ⟨henv, hpm, hres, hbody⟩ := hcellOk
          subst hres
          have hrun : SafeM st (do
              let (s, cur) ← openRegion
              let b ← bindAt P n s p.mode p.cls a
              let r ← eval P ext n (b :: env) body
              let r ← ret P n s cur .shared rc r
              closeRegion s
              conform c r) (fun st' v => ValOk st'.heap v) := by
            refine SafeM.bind (SafeM_openRegion hst) ?_
            intro st₁ sc _ hst₁ hheq₁
            have ha₁ : ValOk st₁.heap a := by rw [hheq₁]; exact ha
            have henv₁ : EnvDefOk st₁.heap env := by rw [hheq₁]; exact henv
            have hbind : SafeM st₁ (bindAt P n sc.1 p.mode p.cls a)
                (fun st₂ b => b.mode = .many ∧ ValOk st₂.heap b.val) := by
              rw [hpm]; exact SafeM_bindAt_many hst₁ P n sc.1 p.cls ha₁
            refine SafeM.bind hbind ?_
            intro st₂ b hext₂ hst₂ ⟨hbm, hbv⟩
            have henv₂ : EnvDefOk st₂.heap (b :: env) := by
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy'
              · exact ⟨hbm, hbv⟩
              · exact ⟨(henv₁ y hy').1, valOk_mono hext₂ (henv₁ y hy').2⟩
            refine SafeM.bind (ihEval st₂ (b :: env) body hst₂ henv₂ hbody) ?_
            intro st₃ r _ hst₃ hr
            refine SafeM.bind (SafeM_ret_shared hst₃ P n sc.1 sc.2 rc hr) ?_
            intro st₄ r' _ hst₄ hr'
            refine SafeM.bind (SafeM_closeRegion hst₄ sc.1) ?_
            intro st₅ _ _ hst₅ hheq₅
            exact SafeM_conform hst₅ c (by rw [hheq₅]; exact hr')
          exact hrun
        | pap r args =>
          rw [hcell] at hcellOk
          have hargs : ∀ v ∈ args.toList ++ [a], ValOk st.heap v := by
            intro v hv
            simp only [List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · exact hcellOk v hv
            · exact ha
          exact ihCall st r (args.toList ++ [a]) c hst hargs
        | once _ _ =>
          rw [hcell] at hcellOk
          exact False.elim hcellOk
        | ctor _ _ | num _ | str _ => trivial
    -- 8. `applyAlt`
    · intro st env t args hst henv ht hargs
      cases args with
      | nil => rw [applyAlt]; exact ihEval st env t hst henv ht
      | cons p rest =>
        obtain ⟨a, er⟩ := p
        obtain ⟨ha, her⟩ := hargs (a, er) (List.mem_cons_self ..)
        subst her
        cases t with
        | lam pm res rc fvs body =>
          rw [applyAlt]
          dsimp only
          obtain ⟨hpm, hres, hbody⟩ := ht.lam
          subst hres
          refine SafeM.bind (SafeM_openRegion hst) ?_
          intro st₁ sc _ hst₁ hheq₁
          have ha₁ : ValOk st₁.heap a := by rw [hheq₁]; exact ha
          have hbind : SafeM st₁ (bindAt P n sc.1 pm.mode pm.cls a)
              (fun st₂ b => b.mode = .many ∧ ValOk st₂.heap b.val) := by
            rw [hpm]; exact SafeM_bindAt_many hst₁ P n sc.1 pm.cls ha₁
          refine SafeM.bind hbind ?_
          intro st₂ b hext₂ hst₂ ⟨hbm, hbv⟩
          have henv₂ : EnvDefOk st₂.heap (b :: env) := by
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact ⟨hbm, hbv⟩
            · exact ⟨(henv y hy').1, by rw [hheq₁] at hext₂; exact valOk_mono hext₂ (henv y hy').2⟩
          have hrest₂ : ∀ q ∈ rest, ValOk st₂.heap q.1 ∧ q.2 = false := by
            intro q hq
            obtain ⟨hq1, hq2⟩ := hargs q (List.mem_cons_of_mem _ hq)
            exact ⟨by rw [hheq₁] at hext₂; exact valOk_mono hext₂ hq1, hq2⟩
          refine SafeM.bind (ihAppAlt st₂ (b :: env) body rest hst₂ henv₂ hbody hrest₂) ?_
          intro st₃ r _ hst₃ hr
          refine SafeM.bind (SafeM_ret_shared hst₃ P n sc.1 sc.2 rc hr) ?_
          intro st₄ r' _ hst₄ hr'
          refine SafeM.bind (SafeM_closeRegion hst₄ sc.1) ?_
          intro st₅ _ _ hst₅ hheq₅
          exact SafeM.pure_intro hst₅ (by rw [hheq₅]; exact hr')
        | _ =>
          simp only [applyAlt]
          have hany : ((a, false) :: rest).any (·.2) = false := by
            simp only [List.any_eq_false, List.mem_cons, forall_eq_or_imp, Bool.false_eq_true,
              not_false_eq_true, true_and]
            intro q hq
            have hq2 := (hargs q (List.mem_cons_of_mem _ hq)).2
            simp [hq2]
          simp only [hany, Bool.false_eq_true, ↓reduceIte]
          refine SafeM.bind (ihEval st env _ hst henv ht) ?_
          intro st₁ fv hext₁ hst₁ hfv
          have hmap : ∀ v ∈ (((a, false) :: rest).map (·.1)), ValOk st₁.heap v := by
            intro v hv
            rw [List.mem_map] at hv
            obtain ⟨q, hq, rfl⟩ := hv
            exact valOk_mono hext₁ (hargs q hq).1
          exact ihAppAll st₁ fv (((a, false) :: rest).map (·.1)) .val hst₁ hfv hmap

/-! ## `InputsOk` Establishes Initial `DefStOk` and `ValOk` -/

theorem defStOk_of_heapOk {P : Prog} {h : Heap} (hh : HeapOk P h) : DefStOk { heap := h } := by
  refine ⟨?_, by simp, by simp⟩
  intro l o ho
  obtain ⟨hinp, hcap, hvals⟩ := hh l o ho
  refine ⟨hcap, ?_⟩
  cases hc : o.cell with
  | ctor _ fs =>
    rw [hc] at hvals
    exact fun w hw => (hvals w hw).1
  | num _ | str _ => trivial
  | pap _ as =>
    rw [hc] at hvals
    exact fun w hw => (hvals w hw).1
  | clo _ _ _ _ _ _ =>
    rw [hc] at hinp; exact False.elim hinp
  | once _ _ =>
    rw [hc] at hinp; exact False.elim hinp

/-! ## Main Theorem: `DefaultOk` -/

/-- **All-default run programs never violate (`IxC.Resource.DefaultOk`).** -/
theorem defaultOk : DefaultOk := by
  intro P ext fuel r h params res rc rs t args k hDef hExt hFind hInp
  obtain ⟨hps, hres, ht⟩ := AllDefault.body hDef hFind
  obtain ⟨hlen, hheap, hargs, _⟩ := hInp
  have hst0 : DefStOk { heap := h } := defStOk_of_heapOk hheap
  have hvs : ∀ v ∈ args, ValOk h v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hi' : i < params.size := hlen ▸ hi
    exact (hargs i params[i] args[i] (Array.getElem?_eq_getElem hi')
      (List.getElem?_eq_getElem hi)).1
  have hsafe := (evalBundle_all hDef hExt fuel).2.2.2.1
    { heap := h } params res rc t args hst0 hps hres ht hvs
  dsimp only [runR, SafeM] at hsafe ⊢
  rw [hFind]
  have hne : (args.length != params.size) = false := by simp [hlen]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  cases hrun : (enter P ext fuel params res rc t args).run { heap := h } with
  | ok _ => simp
  | error e =>
    rw [hrun] at hsafe
    cases e with
    | violation k' => exact False.elim hsafe
    | stuck | outOfFuel => simp

end IxC.Resource.Proof
