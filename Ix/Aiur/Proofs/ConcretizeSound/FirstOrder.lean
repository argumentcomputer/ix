module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.FnFree

/-!
`FirstOrderReturn` bridge: typed→concrete `Typ.FirstOrder` preservation
helpers, `concretizeBuild`'s FO-on-outputs invariant, drain
`NewFunctionsFO` chain + `PendingArgsFO` companion. Extracted from
`ConcretizeSound.lean` 2026-04-29.
-/

public section

namespace Aiur

open Source

/-! ### `FirstOrderReturn` bridge — typedDecls → concrete decls.

Composes the structural preservation lemmas (`rewriteTyp`, `typToConcrete`)
through concretize's pipeline (drain + `concretizeBuild` + `step4Lower` fold)
to lift `Typed.Decls.FirstOrderReturn` to `Concrete.Decls.FirstOrderReturn`.

Source-side is handled by `WellFormed.FirstOrderReturn` directly (parallel to
`DirectDatatypeDAGAcyclic`): the user-facing obligation quantifies over the
post-`checkAndSimplify` typedDecls, so the bridge at
`CompilerCorrect.compile_correct` collapses to a single hypothesis
application into `concretize_preserves_FirstOrderReturn`. -/

/-- The empty substitution trivially maps no globals. Used to discharge
`rewriteTyp_preserves_FirstOrder`'s `_hsubstFO` hypothesis at `emptySubst`. -/
theorem emptySubst_FO : ∀ (g : Global) (t' : Typ),
    (fun (_ : Global) => (none : Option Typ)) g = some t' → Typ.FirstOrder t' := by
  intro g t' hget; cases hget

/-! ### Helpers for `FirstOrder` preservation lemmas below. -/

/-- Membership in `(arr.attach.map f)` exposes the preimage directly. -/
theorem mem_of_attach_map {α β : Type _}
    (arr : Array α) (f : {x // x ∈ arr} → β) {b : β}
    (h : b ∈ arr.attach.map f) :
    ∃ (a : α) (ha : a ∈ arr), f ⟨a, ha⟩ = b := by
  rw [Array.mem_iff_getElem] at h
  obtain ⟨i, hi, heq⟩ := h
  have hi' : i < arr.attach.size := by
    rw [Array.size_map] at hi; exact hi
  have hi'' : i < arr.size := by
    rw [Array.size_attach] at hi'; exact hi'
  refine ⟨arr[i]'hi'', Array.getElem_mem hi'', ?_⟩
  rw [← heq]
  rw [Array.getElem_map]
  congr 1
  apply Subtype.eq
  simp [Array.getElem_attach]

/-- Pointwise FO-propagation through `List.mapM`. -/
theorem List.mem_mapM_ok_forall {α β ε : Type}
    {f : α → Except ε β} {P : α → Prop} {Q : β → Prop}
    (hstep : ∀ x, P x → ∀ fx, f x = .ok fx → Q fx) :
    ∀ (l : List α) (ls : List β),
      (∀ x ∈ l, P x) →
      l.mapM f = .ok ls →
      ∀ y ∈ ls, Q y
  | [], ls, _, h, y, hy => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases hy
  | (x :: xs), ls, hP, h, y, hy => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i fx hfx
    split at h
    · cases h
    rename_i fxs hfxs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases hy with
    | head _ =>
      exact hstep x (hP x (List.Mem.head _)) y hfx
    | tail _ hy' =>
      exact List.mem_mapM_ok_forall hstep xs fxs
        (fun z hz => hP z (List.Mem.tail _ hz)) hfxs y hy'

/-- Array-level counterpart. -/
theorem Array.mem_mapM_ok_forall {α β ε : Type}
    {f : α → Except ε β} {P : α → Prop} {Q : β → Prop}
    (hstep : ∀ x, P x → ∀ fx, f x = .ok fx → Q fx)
    (a : Array α) (bs : Array β)
    (hP : ∀ x ∈ a, P x)
    (h : a.mapM f = .ok bs) :
    ∀ y ∈ bs, Q y := by
  intro y hy
  have h' : a.toList.mapM f = .ok bs.toList := by
    rw [Array.mapM_eq_mapM_toList] at h
    cases hres : a.toList.mapM f with
    | error e =>
      rw [hres] at h
      cases h
    | ok ls =>
      rw [hres] at h
      simp only [Functor.map, Except.map, Except.ok.injEq] at h
      have hbs : bs.toList = ls := by rw [← h]
      rw [hbs]
  have hPl : ∀ x ∈ a.toList, P x :=
    fun x hx => hP x (Array.mem_toList_iff.mp hx)
  have hylist : y ∈ bs.toList := Array.mem_toList_iff.mpr hy
  exact List.mem_mapM_ok_forall hstep a.toList bs.toList hPl h' y hylist

/-- `rewriteTyp` preserves `Typ.FirstOrder`. Structural induction on the
`Typ.FirstOrder` predicate. -/
theorem rewriteTyp_preserves_FirstOrder
    (subst : Global → Option Typ) (mono : MonoMap) {t : Typ}
    (hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t')
    (hFO : Typ.FirstOrder t) :
    Typ.FirstOrder (rewriteTyp subst mono t) := by
  induction hFO with
  | unit => unfold rewriteTyp; exact .unit
  | field => unfold rewriteTyp; exact .field
  | mvar n => unfold rewriteTyp; exact .mvar n
  | ref g =>
    unfold rewriteTyp
    cases hsub : subst g with
    | none => simp only [hsub, Option.getD_none]; exact .ref g
    | some t' =>
      simp only [hsub, Option.getD_some]
      exact hsubstFO g t' hsub
  | @tuple ts _ ih =>
    unfold rewriteTyp
    refine .tuple ?_
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ ht'
    subst ht0eq
    exact ih t0 ht0mem
  | @array t n _ iht =>
    unfold rewriteTyp
    exact .array iht
  | @pointer t _ iht =>
    unfold rewriteTyp
    exact .pointer iht
  | @app g args _ ih =>
    unfold rewriteTyp
    cases hm : mono[(g, args)]? with
    | some concName =>
      simp only [hm]
      exact .ref concName
    | none =>
      simp only [hm]
      refine .app ?_
      intro t' ht'
      obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map args _ ht'
      subst ht0eq
      exact ih t0 ht0mem

/-- `typToConcrete` lifts `Typ.FirstOrder` to `Concrete.Typ.FirstOrder`.
Structural induction on `Typ.FirstOrder`; `.mvar` arm errors (contradicts
`hrun`). -/
theorem typToConcrete_preserves_FirstOrder
    {mono : Std.HashMap (Global × Array Typ) Global} {t : Typ} {t' : Concrete.Typ}
    (hFO : Typ.FirstOrder t)
    (hrun : typToConcrete mono t = .ok t') :
    Concrete.Typ.FirstOrder t' := by
  induction hFO generalizing t' with
  | unit =>
    unfold typToConcrete at hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hrun
    subst hrun
    exact .unit
  | field =>
    unfold typToConcrete at hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hrun
    subst hrun
    exact .field
  | mvar n =>
    unfold typToConcrete at hrun
    cases hrun
  | ref g =>
    unfold typToConcrete at hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hrun
    subst hrun
    exact .ref g
  | @tuple ts htsFO ih =>
    unfold typToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i ls hls
    simp only [Except.ok.injEq] at hrun
    subst hrun
    refine .tuple ?_
    intro t0 ht0mem
    have hls' : ts.mapM (typToConcrete mono) = .ok ls := by
      rw [Array.mapM_subtype (g := fun t => typToConcrete mono t) (fun _ _ => rfl)] at hls
      rw [Array.unattach_attach] at hls
      exact hls
    refine Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts)
      (Q := Concrete.Typ.FirstOrder)
      ?_ ts ls (fun x hx => hx) hls' t0 ht0mem
    intro x hxMem fx hfx
    exact ih x hxMem hfx
  | @array t n _ iht =>
    unfold typToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i ct hct
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .array (iht hct)
  | @pointer t _ iht =>
    unfold typToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i ct hct
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .pointer (iht hct)
  | @app g args _ _ =>
    unfold typToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · rename_i concName _
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .ref concName
    · rename_i _
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .ref g

/-! ### `concretizeBuild` FO-on-outputs invariant. -/

/-- FO-on-function-outputs invariant for partial builds. -/
def FOInv (acc : Typed.Decls) : Prop :=
  ∀ g f, acc.getByKey g = some (.function f) → Typ.FirstOrder f.output

theorem FOInv_default : FOInv (default : Typed.Decls) := by
  intro g f hget
  exfalso
  have : (default : Typed.Decls).getByKey g = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[g]?).bind _ = none
    have : (default : Typed.Decls).indices[g]? = none := by
      show ((default : Std.HashMap Global Nat))[g]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [this] at hget; cases hget

theorem fromSource_preserves_FOInv
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (htdFO : Typed.Decls.FirstOrderReturn typedDecls) :
    FOInv
      (typedDecls.pairs.foldl
        (fun acc p =>
          let (key, d) := p
          match d with
          | .function f =>
            if f.params.isEmpty then
              let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp (fun _ => none) mono t)
              let newOutput := rewriteTyp (fun _ => none) mono f.output
              let newBody := rewriteTypedTerm typedDecls (fun _ => none) mono f.body
              acc.insert key (.function
                { f with inputs := newInputs, output := newOutput, body := newBody })
            else acc
          | .dataType dt =>
            if dt.params.isEmpty then
              let newCtors := dt.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) }
              acc.insert key (.dataType { dt with constructors := newCtors })
            else acc
          | .constructor dt c =>
            if dt.params.isEmpty then
              let newArgTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono)
              let newCtor : Constructor := { c with argTypes := newArgTypes }
              let rewrittenCtors := dt.constructors.map fun c' =>
                { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) mono) }
              let newDt : DataType := { dt with constructors := rewrittenCtors }
              acc.insert key (.constructor newDt newCtor)
            else acc)
        default) := by
  refine Array.foldl_induction
    (motive := fun _ acc => FOInv acc) FOInv_default ?_
  intro i acc hinv
  intro g f hget
  generalize hpr : typedDecls.pairs[i.val] = pr at hget
  have hprmem : pr ∈ typedDecls.pairs := by
    rw [← hpr]; exact Array.getElem_mem i.isLt
  obtain ⟨key, d⟩ := pr
  cases d with
  | function tf =>
    by_cases hparams : tf.params.isEmpty
    · simp only [hparams, if_true] at hget
      by_cases hkey : (key == g) = true
      · have hkeyEq : key = g := LawfulBEq.eq_of_beq hkey
        subst hkeyEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
        rw [← hget]
        apply rewriteTyp_preserves_FirstOrder (fun _ => none) mono
          emptySubst_FO
        exact htdFO key tf (IndexMap.getByKey_of_mem_pairs _ _ _
          (Array.mem_toList_iff.mpr hprmem))
      · have hne : (key == g) = false := Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hinv g f hget
    · simp only [hparams, if_false] at hget
      exact hinv g f hget
  | dataType dt =>
    by_cases hparams : dt.params.isEmpty
    · simp only [hparams, if_true] at hget
      by_cases hkey : (key == g) = true
      · have hkeyEq : key = g := LawfulBEq.eq_of_beq hkey
        subst hkeyEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (key == g) = false := Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hinv g f hget
    · simp only [hparams, if_false] at hget
      exact hinv g f hget
  | constructor dt c =>
    by_cases hparams : dt.params.isEmpty
    · simp only [hparams, if_true] at hget
      by_cases hkey : (key == g) = true
      · have hkeyEq : key = g := LawfulBEq.eq_of_beq hkey
        subst hkeyEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (key == g) = false := Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hinv g f hget
    · simp only [hparams, if_false] at hget
      exact hinv g f hget

theorem withNewDts_preserves_FOInv
    (mono : MonoMap) (newDataTypes : Array DataType) (init : Typed.Decls)
    (hinit : FOInv init) :
    FOInv
      (newDataTypes.foldl
        (fun acc dt =>
          let rewrittenCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          let acc' := acc.insert dt.name (.dataType newDt)
          rewrittenCtors.foldl
            (fun acc'' c =>
              let cName := dt.name.pushNamespace c.nameHead
              acc''.insert cName (.constructor newDt c))
            acc')
        init) := by
  refine Array.foldl_induction (motive := fun _ acc => FOInv acc) hinit ?_
  intro i acc hacc
  generalize hdt : newDataTypes[i.val] = dt
  let newDt : DataType := { dt with
    constructors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) } }
  have hAccInsDt : FOInv (acc.insert dt.name (.dataType newDt)) := by
    intro k tf hget
    by_cases hkey : (dt.name == k) = true
    · have hkeyEq : dt.name = k := LawfulBEq.eq_of_beq hkey
      subst hkeyEq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
    · have hne : (dt.name == k) = false := Bool.not_eq_true _ |>.mp hkey
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hacc k tf hget
  have hInner :
      ∀ (cs : List Constructor) (accInit : Typed.Decls),
        FOInv accInit →
        FOInv (cs.foldl
          (fun acc'' c =>
            let cName := dt.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          accInit) := by
    intro cs
    induction cs with
    | nil => intro accInit hAccInit; exact hAccInit
    | cons c rest ih =>
      intro accInit hAccInit
      apply ih
      intro k tf hget
      by_cases hkey : (dt.name.pushNamespace c.nameHead == k) = true
      · have hkeyEq : dt.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkey
        subst hkeyEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (dt.name.pushNamespace c.nameHead == k) = false :=
          Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hAccInit k tf hget
  exact hInner _ _ hAccInsDt

theorem newFunctions_preserves_FOInv
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (init : Typed.Decls)
    (hinit : FOInv init)
    (hnfFO : ∀ f ∈ newFunctions, Typ.FirstOrder f.output) :
    FOInv
      (newFunctions.foldl
        (fun acc f =>
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp (fun _ => none) mono t)
          let newOutput := rewriteTyp (fun _ => none) mono f.output
          let newBody := rewriteTypedTerm typedDecls (fun _ => none) mono f.body
          let newF : Typed.Function :=
            { f with inputs := newInputs, output := newOutput, body := newBody }
          acc.insert f.name (.function newF))
        init) := by
  refine Array.foldl_induction (motive := fun _ acc => FOInv acc) hinit ?_
  intro i acc hacc
  intro g f hget
  generalize htf : newFunctions[i.val] = tf at hget
  have htfmem : tf ∈ newFunctions := by
    rw [← htf]; exact Array.getElem_mem i.isLt
  by_cases hkey : (tf.name == g) = true
  · have hkeyEq : tf.name = g := LawfulBEq.eq_of_beq hkey
    subst hkeyEq
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
    rw [← hget]
    apply rewriteTyp_preserves_FirstOrder (fun _ => none) mono emptySubst_FO
    exact hnfFO tf htfmem
  · have hne : (tf.name == g) = false := Bool.not_eq_true _ |>.mp hkey
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hacc g f hget

/-- `concretizeBuild` preserves FO on every function output.
Requires: FO on every function in `typedDecls` (hypothesis) and FO on every
function in `newFunctions` (drain invariant). -/
theorem concretizeBuild_preserves_FirstOrderReturn
    {typedDecls : Typed.Decls} {mono : MonoMap}
    {newFunctions : Array Typed.Function} {newDataTypes : Array DataType}
    (htdFO : Typed.Decls.FirstOrderReturn typedDecls)
    (hnfFO : ∀ f ∈ newFunctions, Typ.FirstOrder f.output) :
    ∀ g f, (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey g
            = some (.function f) → Typ.FirstOrder f.output := by
  unfold concretizeBuild
  have h1 := fromSource_preserves_FOInv typedDecls mono htdFO
  have h2 := withNewDts_preserves_FOInv mono newDataTypes _ h1
  exact newFunctions_preserves_FOInv typedDecls mono newFunctions _ h2 hnfFO

/-- `step4Lower` applied to a function entry yields a concrete function with
`output := typToConcrete emptyMono f.output`. FO lifts via
`typToConcrete_preserves_FirstOrder`. -/
theorem step4Lower_function_preserves_FirstOrder
    {acc : Concrete.Decls} {name : Global} {f : Typed.Function}
    {r : Concrete.Decls}
    (hrun : step4Lower acc (name, .function f) = .ok r)
    (hfFO : Typ.FirstOrder f.output) :
    ∃ cf, r.getByKey name = some (.function cf) ∧ Concrete.Typ.FirstOrder cf.output := by
  unfold step4Lower at hrun
  simp only [bind, Except.bind, pure, Except.pure] at hrun
  split at hrun
  · rename_i err _ ; cases hrun
  rename_i _cInputs _hInputs
  split at hrun
  · rename_i err _ ; cases hrun
  rename_i cOutput hOutput
  split at hrun
  · rename_i err _ ; cases hrun
  rename_i _cBody _hBody
  simp only [Except.ok.injEq] at hrun
  subst hrun
  let cf : Concrete.Function :=
    { name := f.name, inputs := _cInputs, output := cOutput,
      body := _cBody, entry := f.entry }
  refine ⟨cf, ?_, ?_⟩
  · rw [IndexMap.getByKey_insert_self]
  · exact typToConcrete_preserves_FirstOrder hfFO hOutput

/-- `step4Lower` fold preserves the FO-on-outputs invariant.

Invariant:
`P acc := ∀ g cf, acc.getByKey g = some (.function cf) → Concrete.Typ.FirstOrder cf.output`.

Per-step:
- function arm dispatches to `step4Lower_function_preserves_FirstOrder`.
- dataType / constructor arms insert non-function entries; the self-case
  cannot hit `.function cf`, the other-case appeals to the prior
  invariant via `IndexMap.getByKey_insert_of_beq_false`. -/
theorem step4Lower_fold_preserves_FirstOrderReturn
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmdFO : ∀ g f, monoDecls.getByKey g = some (.function f) → Typ.FirstOrder f.output)
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∀ g f, concDecls.getByKey g = some (.function f) →
           Concrete.Typ.FirstOrder f.output := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  let P : Concrete.Decls → Prop := fun acc =>
    ∀ g cf, acc.getByKey g = some (.function cf) → Concrete.Typ.FirstOrder cf.output
  have hPdefault : P (default : Concrete.Decls) := by
    intro g cf hget
    exfalso
    have hne : (default : Concrete.Decls).getByKey g = none := by
      unfold IndexMap.getByKey
      show ((default : Concrete.Decls).indices[g]?).bind _ = none
      have : (default : Concrete.Decls).indices[g]? = none := by
        show ((default : Std.HashMap Global Nat))[g]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  apply List.foldlM_except_invariant monoDecls.pairs.toList _ _ _ _ hfold
  · exact hPdefault
  intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
  cases d with
  | function f =>
    have hfFO : Typ.FirstOrder f.output := by
      apply hmdFO name f
      exact IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    obtain ⟨cf, hcf_get, hcf_fo⟩ := step4Lower_function_preserves_FirstOrder hstep hfFO
    intro k tf hget
    by_cases hkn : (name == k) = true
    · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [hcf_get] at hget
      simp only [Option.some.injEq, Concrete.Declaration.function.injEq] at hget
      rw [← hget]; exact hcf_fo
    · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
      unfold step4Lower at hstep
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · rename_i err _ ; cases hstep
      split at hstep
      · rename_i err _ ; cases hstep
      split at hstep
      · rename_i err _ ; cases hstep
      simp only [Except.ok.injEq] at hstep
      subst hstep
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hPacc k tf hget
  | dataType dt =>
    unfold step4Lower at hstep
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · rename_i err _ ; cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    intro k tf hget
    by_cases hkn : (name == k) = true
    · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
    · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hPacc k tf hget
  | constructor dt c =>
    unfold step4Lower at hstep
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · rename_i err _ ; cases hstep
    split at hstep
    · rename_i err _ ; cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    intro k tf hget
    by_cases hkn : (name == k) = true
    · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
    · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hPacc k tf hget

/-- Composition modulo the drain-invariant `hnfFO_any_drained`: every
function produced by drain's specialization pipeline has FO output.
Caller at `CompilerCorrect.compile_correct` discharges this under
`FullyMonomorphic` (drain emits no new templates). -/
theorem concretize_preserves_FirstOrderReturn_of_drainInv
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hP : Typed.Decls.FirstOrderReturn typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hnfFO_any_drained :
      ∀ drained, concretizeDrain typedDecls (concretizeDrainFuel typedDecls)
        { pending := concretizeSeed typedDecls, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained →
        ∀ f ∈ drained.newFunctions, Typ.FirstOrder f.output) :
    ∀ g f, concDecls.getByKey g = some (.function f) →
           Concrete.Typ.FirstOrder f.output := by
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · rename_i err _ ; cases hconc
  rename_i drained hdrain
  have hnfFO := hnfFO_any_drained drained hdrain
  have hmdFO : ∀ g f,
      (concretizeBuild typedDecls drained.mono drained.newFunctions drained.newDataTypes).getByKey g
        = some (.function f) → Typ.FirstOrder f.output :=
    concretizeBuild_preserves_FirstOrderReturn hP hnfFO
  exact step4Lower_fold_preserves_FirstOrderReturn hmdFO hconc

/-! ### Drain `NewFunctionsFO` chain.

Threads through the substitution-FO side condition of
`Typ.instantiate_preserves_FirstOrder` via the `DrainState.PendingArgsFO`
companion invariant (every pending entry's args are FO; defined below at
`DrainState.PendingArgsFO`). The chain takes `PendingArgsFO` as a
hypothesis and uses `mkParamSubst_some_mem` to derive that every
substitution image is in `entry.2`, hence FO.

The companion invariant's seed-init + iter-preservation are packaged as
`concretize_PendingArgsFO_bridge` (single F=1 leaf, blocked on a typed-side
`AppRefTArgsFO` hypothesis — see that bridge's docstring). -/

/-- `Typ.FirstOrder` implies `Typ.AppRefTArgsFO`. Mechanical: FirstOrder's
constructors all map to corresponding AppRefTArgsFO constructors with the
same recursion pattern; `.app` provides `hargsFO` from the FirstOrder premise
and `hargsRec` via IH. -/
theorem Typ.FirstOrder.toAppRefTArgsFO {t : Typ}
    (hFO : Typ.FirstOrder t) : Typed.Typ.AppRefTArgsFO t := by
  induction hFO with
  | unit => exact .unit
  | field => exact .field
  | mvar n => exact .mvar n
  | ref g => exact .ref g
  | tuple h ih => exact .tuple (fun t ht => ih t ht)
  | array h ih => exact .array ih
  | pointer h ih => exact .pointer ih
  | app hargs ih =>
      exact .app (fun t ht => hargs t ht) (fun t ht => ih t ht)

/-- `Typ.instantiate` preserves `Typ.FirstOrder`. Same shape as
`rewriteTyp_preserves_FirstOrder` minus the mono-map branch. -/
theorem Typ.instantiate_preserves_FirstOrder
    (subst : Global → Option Typ) {t : Typ}
    (hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t')
    (hFO : Typ.FirstOrder t) :
    Typ.FirstOrder (Typ.instantiate subst t) := by
  induction hFO with
  | unit => unfold Typ.instantiate; exact .unit
  | field => unfold Typ.instantiate; exact .field
  | mvar n => unfold Typ.instantiate; exact .mvar n
  | ref g =>
    unfold Typ.instantiate
    cases hsub : subst g with
    | none => simp only [hsub, Option.getD_none]; exact .ref g
    | some t' =>
      simp only [hsub, Option.getD_some]
      exact hsubstFO g t' hsub
  | @tuple ts _ ih =>
    unfold Typ.instantiate
    refine .tuple ?_
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ ht'
    subst ht0eq
    exact ih t0 ht0mem
  | @array t n _ iht =>
    unfold Typ.instantiate
    exact .array iht
  | @pointer t _ iht =>
    unfold Typ.instantiate
    exact .pointer iht
  | @app g args _ ih =>
    unfold Typ.instantiate
    refine .app ?_
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map args _ ht'
    subst ht0eq
    exact ih t0 ht0mem

/-- `mkParamSubst []` is the empty substitution. -/
theorem mkParamSubst_nil (args : Array Typ) :
    mkParamSubst [] args = fun _ => none := by
  funext g
  unfold mkParamSubst
  simp [List.zip_nil_left]

/-- Empty substitution is identity on `Typ`. Recursively unfolds through every
arm of `Typ.instantiate`; `attach.map` arms collapse via stdlib `pmap_eq_self`
+ `map_attach_eq_pmap`. -/
theorem Typ.instantiate_empty_id : ∀ (t : Typ),
    Typ.instantiate (fun _ => none) t = t
  | .unit => by simp [Typ.instantiate]
  | .field => by simp [Typ.instantiate]
  | .mvar n => by simp [Typ.instantiate]
  | .ref g => by simp [Typ.instantiate]
  | .pointer t => by
      unfold Typ.instantiate
      rw [Typ.instantiate_empty_id t]
  | .array t n => by
      unfold Typ.instantiate
      rw [Typ.instantiate_empty_id t]
  | .tuple ts => by
      unfold Typ.instantiate
      congr 1
      rw [Array.map_attach_eq_pmap]
      apply Array.pmap_eq_self.mpr
      intro a ha
      exact Typ.instantiate_empty_id a
  | .app g args => by
      unfold Typ.instantiate
      congr 1
      rw [Array.map_attach_eq_pmap]
      apply Array.pmap_eq_self.mpr
      intro a ha
      exact Typ.instantiate_empty_id a
  | .function ins out => by
      unfold Typ.instantiate
      congr 1
      · rw [List.map_attach_eq_pmap]
        apply List.pmap_eq_self.mpr
        intro a ha
        exact Typ.instantiate_empty_id a
      · exact Typ.instantiate_empty_id out
  termination_by t => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ha; grind)
      | (have := List.sizeOf_lt_of_mem ha; grind)

/-- Empty substitution is identity on typed terms. Mechanical 37-arm
structural induction; each arm dispatches to `Typ.instantiate_empty_id`
on type annotations + recursive `substInTypedTerm_empty_id` on subterms. -/
theorem substInTypedTerm_empty_id : ∀ (t : Typed.Term),
    substInTypedTerm (fun _ => none) t = t
  | .unit τ e => by
      unfold substInTypedTerm; rw [Typ.instantiate_empty_id τ]
  | .var τ e x => by
      unfold substInTypedTerm; rw [Typ.instantiate_empty_id τ]
  | .ref τ e g tArgs => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ]
      congr 1
      -- Show `tArgs.map (Typ.instantiate (fun _ => none)) = tArgs` via toList.
      apply Array.toList_inj.mp
      simp only [Array.toList_map]
      induction tArgs.toList with
      | nil => rfl
      | cons hd tl ih =>
        simp only [List.map_cons]
        rw [Typ.instantiate_empty_id hd, ih]
  | .field τ e v => by
      unfold substInTypedTerm; rw [Typ.instantiate_empty_id τ]
  | .tuple τ e ts => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ]
      congr 1
      rw [Array.map_attach_eq_pmap]
      apply Array.pmap_eq_self.mpr
      intro a ha
      exact substInTypedTerm_empty_id a
  | .array τ e ts => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ]
      congr 1
      rw [Array.map_attach_eq_pmap]
      apply Array.pmap_eq_self.mpr
      intro a ha
      exact substInTypedTerm_empty_id a
  | .ret τ e r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id r]
  | .let τ e p v b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id v,
          substInTypedTerm_empty_id b]
  | .match τ e scrut bs => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id scrut]
      congr 1
      rw [List.map_attach_eq_pmap]
      apply List.pmap_eq_self.mpr
      intro ⟨p, b⟩ ha
      exact congrArg (Prod.mk p) (substInTypedTerm_empty_id b)
  | .app τ e g tArgs args u => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ]
      congr 1
      · -- Show `tArgs.map (Typ.instantiate (fun _ => none)) = tArgs` via toList.
        apply Array.toList_inj.mp
        simp only [Array.toList_map]
        induction tArgs.toList with
        | nil => rfl
        | cons hd tl ih =>
          simp only [List.map_cons]
          rw [Typ.instantiate_empty_id hd, ih]
      · rw [List.map_attach_eq_pmap]
        apply List.pmap_eq_self.mpr
        intro a ha
        exact substInTypedTerm_empty_id a
  | .add τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .sub τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .mul τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .eqZero τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .proj τ e a n => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .get τ e a n => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .slice τ e a i j => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .set τ e a n v => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id v]
  | .store τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .load τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .ptrVal τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .assertEq τ e a b r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b, substInTypedTerm_empty_id r]
  | .ioGetInfo τ e k => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id k]
  | .ioSetInfo τ e k i l r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id k,
          substInTypedTerm_empty_id i, substInTypedTerm_empty_id l,
          substInTypedTerm_empty_id r]
  | .ioRead τ e i n => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id i]
  | .ioWrite τ e d r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id d,
          substInTypedTerm_empty_id r]
  | .u8BitDecomposition τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .u8ShiftLeft τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .u8ShiftRight τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .u8Xor τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8Add τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8Sub τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8And τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8Or τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8LessThan τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u32LessThan τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .debug τ e l t r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id r]
      cases t with
      | none => rfl
      | some sub =>
        simp only
        rw [substInTypedTerm_empty_id sub]
  termination_by t => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have : ∀ {α} [SizeOf α] (a : α), sizeOf a < sizeOf (some a) := by
           intros; show _ < 1 + _; omega
         grind)
      | (have hmem : _ ∈ _ := ‹_ ∈ _›
         have := Array.sizeOf_lt_of_mem hmem
         grind)
      | (have hmem : _ ∈ _ := ‹_ ∈ _›
         have := List.sizeOf_lt_of_mem hmem
         grind)

/-- List-level analogue of `mem_of_attach_map`. Used by both
`substInTypedTerm_preserves_RefsDt` (immediately below) and the typed-term
rewrite chain further down. -/
theorem list_mem_of_attach_map {α β : Type _}
    (l : List α) (f : {x // x ∈ l} → β) {b : β}
    (h : b ∈ l.attach.map f) :
    ∃ (a : α) (ha : a ∈ l), f ⟨a, ha⟩ = b := by
  rw [List.mem_map] at h
  obtain ⟨⟨a, ha⟩, _hmem, hfeq⟩ := h
  exact ⟨a, ha, hfeq⟩

/-- `Typ.instantiate` preserves `Typ.AppRefTArgsFO`. The `.app` arm needs
both `hargsFO` and `hargsRec` re-established on the substituted args. -/
theorem Typ.instantiate_preserves_AppRefTArgsFO
    (subst : Global → Option Typ) {t : Typ}
    (hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t')
    (hsubstAR : ∀ g t', subst g = some t' → Typed.Typ.AppRefTArgsFO t')
    (hAR : Typed.Typ.AppRefTArgsFO t) :
    Typed.Typ.AppRefTArgsFO (Typ.instantiate subst t) := by
  induction hAR with
  | unit => unfold Typ.instantiate; exact .unit
  | field => unfold Typ.instantiate; exact .field
  | mvar n => unfold Typ.instantiate; exact .mvar n
  | ref g =>
    unfold Typ.instantiate
    cases hsub : subst g with
    | none => simp only [hsub, Option.getD_none]; exact .ref g
    | some t' =>
      simp only [hsub, Option.getD_some]
      exact hsubstAR g t' hsub
  | @tuple ts _ ih =>
    unfold Typ.instantiate
    refine .tuple ?_
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ ht'
    subst ht0eq
    exact ih t0 ht0mem
  | @array t n _ iht =>
    unfold Typ.instantiate
    exact .array iht
  | @pointer t _ iht =>
    unfold Typ.instantiate
    exact .pointer iht
  | @app g args hargsFO hargsRec ih =>
    unfold Typ.instantiate
    refine .app ?_ ?_
    · intro t' ht'
      obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map args _ ht'
      subst ht0eq
      exact Typ.instantiate_preserves_FirstOrder subst hsubstFO (hargsFO t0 ht0mem)
    · intro t' ht'
      obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map args _ ht'
      subst ht0eq
      exact ih t0 ht0mem
  | @function ins out hins hout ih_ins ih_out =>
    unfold Typ.instantiate
    refine .function ?_ ih_out
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := list_mem_of_attach_map ins _ ht'
    subst ht0eq
    exact ih_ins t0 ht0mem

/-- `collectInTyp` preserves the FO-pending invariant: under
`AppRefTArgsFO τ` and seen carrying FO type-args, every collected entry
carries FO type-args. -/
theorem collectInTyp_PendingArgsFO_step {τ : Typ}
    (hAR : Typed.Typ.AppRefTArgsFO τ) :
    ∀ (seen : Std.HashSet (Global × Array Typ)),
      (∀ entry ∈ seen, ∀ t ∈ entry.2, Typ.FirstOrder t) →
      ∀ entry ∈ collectInTyp seen τ, ∀ t ∈ entry.2, Typ.FirstOrder t := by
  induction hAR with
  | unit => intro seen hseen; unfold collectInTyp; exact hseen
  | field => intro seen hseen; unfold collectInTyp; exact hseen
  | mvar n => intro seen hseen; unfold collectInTyp; exact hseen
  | ref g => intro seen hseen; unfold collectInTyp; exact hseen
  | @tuple ts _h ih =>
    intro seen hseen
    unfold collectInTyp
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typ.FirstOrder t) hseen
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @array t n _ iht =>
    intro seen hseen
    unfold collectInTyp
    exact iht seen hseen
  | @pointer t _ iht =>
    intro seen hseen
    unfold collectInTyp
    exact iht seen hseen
  | @app g args hargsFO _hargsRec ih =>
    intro seen hseen
    unfold collectInTyp
    have hafter : ∀ entry ∈ args.attach.foldl
        (fun s ⟨t, _⟩ => collectInTyp s t) seen,
        ∀ t ∈ entry.2, Typ.FirstOrder t := by
      apply Array.foldl_induction
        (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
          ∀ entry ∈ acc, ∀ t ∈ entry.2, Typ.FirstOrder t) hseen
      intro i acc hinv
      obtain ⟨t, ht⟩ := args.attach[i.val]'i.isLt
      exact ih t ht acc hinv
    intro entry hent t ht
    rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
    · -- (g, args) == entry, so entry = (g, args).
      have hpair : (g, args) = entry := LawfulBEq.eq_of_beq hbeq
      rw [← hpair] at ht
      exact hargsFO t ht
    · exact hafter entry hin t ht
  | @function ins out _h_ins _h_out ih_ins ih_out =>
    intro seen hseen
    unfold collectInTyp
    -- ins is List, ins.attach.foldl produces accumulator; then collectInTyp _ out.
    have hafter_ins : ∀ entry ∈ ins.attach.foldl
        (fun s ⟨t, _⟩ => collectInTyp s t) seen,
        ∀ t' ∈ entry.2, Typ.FirstOrder t' := by
      -- List.foldl induction with strengthened motive.
      have aux : ∀ (l : List {x // x ∈ ins}) (acc : Std.HashSet (Global × Array Typ)),
          (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typ.FirstOrder t') →
          ∀ entry ∈ l.foldl (fun s ⟨t, _⟩ => collectInTyp s t) acc,
            ∀ t' ∈ entry.2, Typ.FirstOrder t' := by
        intro l
        induction l with
        | nil => intro acc hacc entry hent; exact hacc entry hent
        | cons hd tl ih_l =>
          intro acc hacc
          simp only [List.foldl_cons]
          apply ih_l
          obtain ⟨t, ht⟩ := hd
          exact ih_ins t ht acc hacc
      exact aux ins.attach seen hseen
    exact ih_out _ hafter_ins

/-- `collectInTypedTerm` preserves the FO-pending invariant. -/
theorem collectInTypedTerm_PendingArgsFO_step {term : Typed.Term}
    (hAR : Typed.Term.AppRefTArgsFO term) :
    ∀ (seen : Std.HashSet (Global × Array Typ)),
      (∀ entry ∈ seen, ∀ t ∈ entry.2, Typ.FirstOrder t) →
      ∀ entry ∈ collectInTypedTerm seen term, ∀ t ∈ entry.2, Typ.FirstOrder t := by
  -- Helper: chain collectInTyp + a continuation; preserves the invariant.
  -- The `.tuple/.array/.match/.app` arms iterate via attach.foldl.
  -- For brevity, lift each arm using L4a (collectInTyp) + IH chains.
  induction hAR with
  | unit htyp => intro seen hseen; unfold collectInTypedTerm
                 exact collectInTyp_PendingArgsFO_step htyp seen hseen
  | var htyp => intro seen hseen; unfold collectInTypedTerm
                exact collectInTyp_PendingArgsFO_step htyp seen hseen
  | @ref typ e g tArgs htyp hArgsFO hArgsRec =>
    intro seen hseen
    unfold collectInTypedTerm
    -- collectInTyp on typ, then tArgs.foldl collectInTyp.
    have h_typ := collectInTyp_PendingArgsFO_step htyp seen hseen
    -- tArgs.foldl preserves invariant via collectInTyp_PendingArgsFO_step on each element.
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typ.FirstOrder t) h_typ
    intro i acc hinv
    have hti : Typed.Typ.AppRefTArgsFO (tArgs[i.val]'i.isLt) :=
      hArgsRec _ (Array.getElem_mem _)
    exact collectInTyp_PendingArgsFO_step hti acc hinv
  | field htyp => intro seen hseen; unfold collectInTypedTerm
                  exact collectInTyp_PendingArgsFO_step htyp seen hseen
  | @tuple typ e ts htyp _h ih =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_PendingArgsFO_step htyp seen hseen
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typ.FirstOrder t) h_typ
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @array typ e ts htyp _h ih =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_PendingArgsFO_step htyp seen hseen
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typ.FirstOrder t) h_typ
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @ret typ e sub htyp _h ih =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ih _ (collectInTyp_PendingArgsFO_step htyp seen hseen)
  | @«let» typ e pat v b htyp _hv _hb ihv ihb =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihb _ (ihv _ (collectInTyp_PendingArgsFO_step htyp seen hseen))
  | @«match» typ e scrut cases htyp _hscrut _hcases ihscrut ih_cases =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_PendingArgsFO_step htyp seen hseen
    have h_scrut := ihscrut _ h_typ
    -- cases is List, so .attach.foldl is List.foldl. Use List induction.
    have aux : ∀ (l : List {x // x ∈ cases}) (acc : Std.HashSet (Global × Array Typ)),
        (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typ.FirstOrder t') →
        ∀ entry ∈ l.foldl
          (fun s x => match x with | ⟨(_, b), _⟩ => collectInTypedTerm s b) acc,
          ∀ t' ∈ entry.2, Typ.FirstOrder t' := by
      intro l
      induction l with
      | nil => intro acc hacc entry hent; exact hacc entry hent
      | cons hd tl ih_l =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih_l
        obtain ⟨pc, hpc⟩ := hd
        obtain ⟨pat, b⟩ := pc
        exact ih_cases ⟨pat, b⟩ hpc acc hacc
    exact aux cases.attach _ h_scrut
  | @app typ e g tArgs args u htyp hArgsFO _hArgsRec _hargs ihargs =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_PendingArgsFO_step htyp seen hseen
    have h_tArgs : ∀ entry ∈ tArgs.foldl collectInTyp (collectInTyp seen typ),
        ∀ t ∈ entry.2, Typ.FirstOrder t := by
      apply Array.foldl_induction
        (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
          ∀ entry ∈ acc, ∀ t ∈ entry.2, Typ.FirstOrder t) h_typ
      intro i acc hinv
      have hti : Typed.Typ.AppRefTArgsFO (tArgs[i.val]'i.isLt) :=
        Typ.FirstOrder.toAppRefTArgsFO (hArgsFO _ (Array.getElem_mem _))
      exact collectInTyp_PendingArgsFO_step hti acc hinv
    -- args is List, so .attach.foldl is List.foldl.
    have aux : ∀ (l : List {x // x ∈ args}) (acc : Std.HashSet (Global × Array Typ)),
        (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typ.FirstOrder t') →
        ∀ entry ∈ l.foldl (fun s ⟨a, _⟩ => collectInTypedTerm s a) acc,
          ∀ t' ∈ entry.2, Typ.FirstOrder t' := by
      intro l
      induction l with
      | nil => intro acc hacc entry hent; exact hacc entry hent
      | cons hd tl ih_l =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih_l
        obtain ⟨a, ha⟩ := hd
        exact ihargs a ha acc hacc
    exact aux args.attach _ h_tArgs
  | @add typ e a b htyp _ha _hb iha ihb | @sub typ e a b htyp _ha _hb iha ihb
  | @mul typ e a b htyp _ha _hb iha ihb | @u8Xor typ e a b htyp _ha _hb iha ihb
  | @u8Add typ e a b htyp _ha _hb iha ihb | @u8Sub typ e a b htyp _ha _hb iha ihb
  | @u8And typ e a b htyp _ha _hb iha ihb | @u8Or typ e a b htyp _ha _hb iha ihb
  | @u8LessThan typ e a b htyp _ha _hb iha ihb
  | @u32LessThan typ e a b htyp _ha _hb iha ihb =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihb _ (iha _ (collectInTyp_PendingArgsFO_step htyp seen hseen))
  | @eqZero typ e a htyp _ha iha | @store typ e a htyp _ha iha
  | @load typ e a htyp _ha iha | @ptrVal typ e a htyp _ha iha
  | @u8BitDecomposition typ e a htyp _ha iha
  | @u8ShiftLeft typ e a htyp _ha iha | @u8ShiftRight typ e a htyp _ha iha
  | @ioGetInfo typ e a htyp _ha iha =>
    intro seen hseen
    unfold collectInTypedTerm
    exact iha _ (collectInTyp_PendingArgsFO_step htyp seen hseen)
  | @proj typ e a n htyp _ha iha | @get typ e a n htyp _ha iha =>
    intro seen hseen
    unfold collectInTypedTerm
    exact iha _ (collectInTyp_PendingArgsFO_step htyp seen hseen)
  | @slice typ e a i j htyp _ha iha =>
    intro seen hseen
    unfold collectInTypedTerm
    exact iha _ (collectInTyp_PendingArgsFO_step htyp seen hseen)
  | @«set» typ e a n v htyp _ha _hv iha ihv =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihv _ (iha _ (collectInTyp_PendingArgsFO_step htyp seen hseen))
  | @assertEq typ e a b r htyp _ha _hb _hr iha ihb ihr =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihr _ (ihb _ (iha _ (collectInTyp_PendingArgsFO_step htyp seen hseen)))
  | @ioSetInfo typ e k i l r htyp _hk _hi _hl _hr ihk ihi ihl ihr =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihr _ (ihl _ (ihi _ (ihk _ (collectInTyp_PendingArgsFO_step htyp seen hseen))))
  | @ioRead typ e i n htyp _hi ihi =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihi _ (collectInTyp_PendingArgsFO_step htyp seen hseen)
  | @ioWrite typ e d r htyp _hd _hr ihd ihr =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihr _ (ihd _ (collectInTyp_PendingArgsFO_step htyp seen hseen))
  | @debug typ e label t r htyp _ht _hr iht ihr =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_PendingArgsFO_step htyp seen hseen
    have h_t : ∀ entry ∈ (match t with | some t => collectInTypedTerm (collectInTyp seen typ) t
                                       | none => collectInTyp seen typ),
        ∀ t' ∈ entry.2, Typ.FirstOrder t' := by
      cases t with
      | none => exact h_typ
      | some tval => exact iht tval rfl _ h_typ
    exact ihr _ h_t

/-- `collectCalls` preserves the FO-pending invariant. Term-level only;
no type-annotation collection. The `.app`/`.ref` insertion points are at
`(g, tArgs)` or `(dt.name, tArgs)` — `Term.AppRefTArgsFO`'s `hArgsFO`
provides `∀ t ∈ tArgs, FirstOrder t` directly. -/
theorem collectCalls_PendingArgsFO_step {decls : Typed.Decls} {term : Typed.Term}
    (hAR : Typed.Term.AppRefTArgsFO term) :
    ∀ (seen : Std.HashSet (Global × Array Typ)),
      (∀ entry ∈ seen, ∀ t ∈ entry.2, Typ.FirstOrder t) →
      ∀ entry ∈ collectCalls decls seen term, ∀ t ∈ entry.2, Typ.FirstOrder t := by
  induction hAR with
  | unit _ => intro seen hseen; unfold collectCalls; exact hseen
  | var _ => intro seen hseen; unfold collectCalls; exact hseen
  | @ref typ e g tArgs _htyp hArgsFO _hArgsRec =>
    intro seen hseen
    show ∀ entry ∈ collectCalls decls seen (.ref typ e g tArgs), _
    unfold collectCalls
    by_cases htA : tArgs.isEmpty = true
    · rw [if_pos htA]; exact hseen
    · rw [if_neg htA]
      cases hg : decls.getByKey g with
      | none => exact hseen
      | some d =>
        cases d with
        | function f =>
          intro entry hent t ht
          rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
          · have hpair : (g, tArgs) = entry := LawfulBEq.eq_of_beq hbeq
            rw [← hpair] at ht; exact hArgsFO t ht
          · exact hseen entry hin t ht
        | dataType _ => exact hseen
        | constructor dt _ =>
          intro entry hent t ht
          rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
          · have hpair : (dt.name, tArgs) = entry := LawfulBEq.eq_of_beq hbeq
            rw [← hpair] at ht; exact hArgsFO t ht
          · exact hseen entry hin t ht
  | field _ => intro seen hseen; unfold collectCalls; exact hseen
  | @tuple typ e ts _htyp _h ih =>
    intro seen hseen
    unfold collectCalls
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typ.FirstOrder t) hseen
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @array typ e ts _htyp _h ih =>
    intro seen hseen
    unfold collectCalls
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typ.FirstOrder t) hseen
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @ret typ e sub _htyp _h ih => intro seen hseen; unfold collectCalls; exact ih _ hseen
  | @«let» typ e pat v b _htyp _hv _hb ihv ihb =>
    intro seen hseen; unfold collectCalls; exact ihb _ (ihv _ hseen)
  | @«match» typ e scrut cases _htyp _hscrut _hcases ihscrut ih_cases =>
    intro seen hseen
    unfold collectCalls
    have h_scrut := ihscrut _ hseen
    have aux : ∀ (l : List {x // x ∈ cases}) (acc : Std.HashSet (Global × Array Typ)),
        (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typ.FirstOrder t') →
        ∀ entry ∈ l.foldl
          (fun s x => match x with | ⟨(_, b), _⟩ => collectCalls decls s b) acc,
          ∀ t' ∈ entry.2, Typ.FirstOrder t' := by
      intro l
      induction l with
      | nil => intro acc hacc entry hent; exact hacc entry hent
      | cons hd tl ih_l =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih_l
        obtain ⟨pc, hpc⟩ := hd
        obtain ⟨pat, b⟩ := pc
        exact ih_cases ⟨pat, b⟩ hpc acc hacc
    exact aux cases.attach _ h_scrut
  | @app typ e g tArgs args u _htyp hArgsFO _hArgsRec _hargs ihargs =>
    intro seen hseen
    unfold collectCalls
    -- args.attach.foldl (List), then insert based on decls lookup.
    have h_after_args : ∀ entry ∈ args.attach.foldl
        (fun s ⟨a, _⟩ => collectCalls decls s a) seen,
        ∀ t' ∈ entry.2, Typ.FirstOrder t' := by
      have aux : ∀ (l : List {x // x ∈ args}) (acc : Std.HashSet (Global × Array Typ)),
          (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typ.FirstOrder t') →
          ∀ entry ∈ l.foldl (fun s ⟨a, _⟩ => collectCalls decls s a) acc,
            ∀ t' ∈ entry.2, Typ.FirstOrder t' := by
        intro l
        induction l with
        | nil => intro acc hacc entry hent; exact hacc entry hent
        | cons hd tl ih_l =>
          intro acc hacc
          simp only [List.foldl_cons]
          apply ih_l
          obtain ⟨a, ha⟩ := hd
          exact ihargs a ha acc hacc
      exact aux args.attach _ hseen
    by_cases htA : tArgs.isEmpty = true
    · rw [if_pos htA]; exact h_after_args
    · rw [if_neg htA]
      cases hg : decls.getByKey g with
      | none => exact h_after_args
      | some d =>
        cases d with
        | function f =>
          intro entry hent t ht
          rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
          · have hpair : (g, tArgs) = entry := LawfulBEq.eq_of_beq hbeq
            rw [← hpair] at ht; exact hArgsFO t ht
          · exact h_after_args entry hin t ht
        | dataType _ => exact h_after_args
        | constructor dt _ =>
          intro entry hent t ht
          rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
          · have hpair : (dt.name, tArgs) = entry := LawfulBEq.eq_of_beq hbeq
            rw [← hpair] at ht; exact hArgsFO t ht
          · exact h_after_args entry hin t ht
  | @add typ e a b _htyp _ha _hb iha ihb | @sub typ e a b _htyp _ha _hb iha ihb
  | @mul typ e a b _htyp _ha _hb iha ihb | @u8Xor typ e a b _htyp _ha _hb iha ihb
  | @u8Add typ e a b _htyp _ha _hb iha ihb | @u8Sub typ e a b _htyp _ha _hb iha ihb
  | @u8And typ e a b _htyp _ha _hb iha ihb | @u8Or typ e a b _htyp _ha _hb iha ihb
  | @u8LessThan typ e a b _htyp _ha _hb iha ihb
  | @u32LessThan typ e a b _htyp _ha _hb iha ihb =>
    intro seen hseen; unfold collectCalls; exact ihb _ (iha _ hseen)
  | @eqZero typ e a _htyp _ha iha | @store typ e a _htyp _ha iha
  | @load typ e a _htyp _ha iha | @ptrVal typ e a _htyp _ha iha
  | @u8BitDecomposition typ e a _htyp _ha iha
  | @u8ShiftLeft typ e a _htyp _ha iha | @u8ShiftRight typ e a _htyp _ha iha
  | @ioGetInfo typ e a _htyp _ha iha =>
    intro seen hseen; unfold collectCalls; exact iha _ hseen
  | @proj typ e a n _htyp _ha iha | @get typ e a n _htyp _ha iha =>
    intro seen hseen; unfold collectCalls; exact iha _ hseen
  | @slice typ e a i j _htyp _ha iha =>
    intro seen hseen; unfold collectCalls; exact iha _ hseen
  | @«set» typ e a n v _htyp _ha _hv iha ihv =>
    intro seen hseen; unfold collectCalls; exact ihv _ (iha _ hseen)
  | @assertEq typ e a b r _htyp _ha _hb _hr iha ihb ihr =>
    intro seen hseen; unfold collectCalls; exact ihr _ (ihb _ (iha _ hseen))
  | @ioSetInfo typ e k i l r _htyp _hk _hi _hl _hr ihk ihi ihl ihr =>
    intro seen hseen; unfold collectCalls; exact ihr _ (ihl _ (ihi _ (ihk _ hseen)))
  | @ioRead typ e i n _htyp _hi ihi =>
    intro seen hseen; unfold collectCalls; exact ihi _ hseen
  | @ioWrite typ e d r _htyp _hd _hr ihd ihr =>
    intro seen hseen; unfold collectCalls; exact ihr _ (ihd _ hseen)
  | @debug typ e label t r _htyp _ht _hr iht ihr =>
    intro seen hseen
    unfold collectCalls
    have h_t : ∀ entry ∈ (match t with
                          | some t => collectCalls decls seen t
                          | none => seen),
        ∀ t' ∈ entry.2, Typ.FirstOrder t' := by
      cases t with
      | none => exact hseen
      | some tval => exact iht tval rfl _ hseen
    exact ihr _ h_t

/-- `substInTypedTerm` preserves `Typed.Term.RefsDt` structurally. The
substitution rewrites only `Typ`-level annotations and leaves every
`Typed.Term`-level global (`.ref _ _ g _`, `.app _ _ g _ _ _`, ctor names,
etc.) unchanged, so the predicate's witness for each `.ref` subterm
transports verbatim. Replaces the `f.params = []` reduction in the
`NewFunctionsTermRefsDt` drain chain. -/
theorem substInTypedTerm_preserves_RefsDt
    {decls : Typed.Decls} {body : Typed.Term} {subst : Global → Option Typ}
    (hbody : Typed.Term.RefsDt decls body) :
    Typed.Term.RefsDt decls (substInTypedTerm subst body) := by
  induction hbody with
  | unit => unfold substInTypedTerm; exact .unit
  | var => unfold substInTypedTerm; exact .var
  | @ref typ e g tArgs hdt =>
    unfold substInTypedTerm
    -- Sig amendment 2026-05-04 (RefsDt-defect): the `.ref` arm carries the
    -- structural disjunct `dt.params.isEmpty ∨ ¬ tArgs.isEmpty`. `substInTypedTerm`
    -- maps `tArgs` element-wise, preserving `.size` (and hence `.isEmpty`),
    -- so the disjunct transports verbatim.
    obtain ⟨dt, c, hget, hdisj⟩ := hdt
    refine .ref ⟨dt, c, hget, ?_⟩
    rcases hdisj with hp | hne
    · exact Or.inl hp
    · refine Or.inr ?_
      intro hempty
      apply hne
      -- `tArgs.map _` has the same size as `tArgs`, so emptiness transfers.
      have hsize : (tArgs.map (Typ.instantiate subst)).size = tArgs.size :=
        Array.size_map ..
      have hempty_eq : tArgs.map (Typ.instantiate subst) = #[] := by
        simpa [Array.isEmpty] using hempty
      have h0 : (tArgs.map (Typ.instantiate subst)).size = 0 := by
        rw [hempty_eq]; rfl
      have htargs0 : tArgs.size = 0 := hsize ▸ h0
      simpa [Array.isEmpty] using (Array.eq_empty_iff_size_eq_zero.mpr htargs0)
  | field => unfold substInTypedTerm; exact .field
  | @tuple typ e ts _ ih =>
    unfold substInTypedTerm
    refine .tuple ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | @array typ e ts _ ih =>
    unfold substInTypedTerm
    refine .array ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | ret _ ihr =>
    unfold substInTypedTerm; exact .ret ihr
  | «let» _ _ ihv ihb =>
    unfold substInTypedTerm; exact .let ihv ihb
  | @«match» typ e scrut cases _ _ ihscrut ihcases =>
    unfold substInTypedTerm
    refine .match ihscrut ?_
    intro pc hpc
    obtain ⟨p0, hp0mem, hp0eq⟩ := list_mem_of_attach_map cases _ hpc
    subst hp0eq
    exact ihcases p0 hp0mem
  | @app typ e g tArgs args u _ ih =>
    unfold substInTypedTerm
    refine .app ?_
    intro a ha
    obtain ⟨a0, ha0mem, ha0eq⟩ := list_mem_of_attach_map args _ ha
    subst ha0eq
    exact ih a0 ha0mem
  | add _ _ iha ihb => unfold substInTypedTerm; exact .add iha ihb
  | sub _ _ iha ihb => unfold substInTypedTerm; exact .sub iha ihb
  | mul _ _ iha ihb => unfold substInTypedTerm; exact .mul iha ihb
  | eqZero _ iha => unfold substInTypedTerm; exact .eqZero iha
  | proj _ iha => unfold substInTypedTerm; exact .proj iha
  | get _ iha => unfold substInTypedTerm; exact .get iha
  | slice _ iha => unfold substInTypedTerm; exact .slice iha
  | «set» _ _ iha ihv => unfold substInTypedTerm; exact .set iha ihv
  | store _ iha => unfold substInTypedTerm; exact .store iha
  | load _ iha => unfold substInTypedTerm; exact .load iha
  | ptrVal _ iha => unfold substInTypedTerm; exact .ptrVal iha
  | assertEq _ _ _ iha ihb ihr =>
    unfold substInTypedTerm; exact .assertEq iha ihb ihr
  | ioGetInfo _ ihk => unfold substInTypedTerm; exact .ioGetInfo ihk
  | ioSetInfo _ _ _ _ ihk ihi ihl ihr =>
    unfold substInTypedTerm; exact .ioSetInfo ihk ihi ihl ihr
  | ioRead _ ihi => unfold substInTypedTerm; exact .ioRead ihi
  | ioWrite _ _ ihd ihr => unfold substInTypedTerm; exact .ioWrite ihd ihr
  | u8BitDecomposition _ iha => unfold substInTypedTerm; exact .u8BitDecomposition iha
  | u8ShiftLeft _ iha => unfold substInTypedTerm; exact .u8ShiftLeft iha
  | u8ShiftRight _ iha => unfold substInTypedTerm; exact .u8ShiftRight iha
  | u8Xor _ _ iha ihb => unfold substInTypedTerm; exact .u8Xor iha ihb
  | u8Add _ _ iha ihb => unfold substInTypedTerm; exact .u8Add iha ihb
  | u8Sub _ _ iha ihb => unfold substInTypedTerm; exact .u8Sub iha ihb
  | u8And _ _ iha ihb => unfold substInTypedTerm; exact .u8And iha ihb
  | u8Or  _ _ iha ihb => unfold substInTypedTerm; exact .u8Or iha ihb
  | u8LessThan  _ _ iha ihb => unfold substInTypedTerm; exact .u8LessThan iha ihb
  | u32LessThan _ _ iha ihb => unfold substInTypedTerm; exact .u32LessThan iha ihb
  | @debug typ e label t r ht hr iht ihr =>
    unfold substInTypedTerm
    refine .debug ?_ ihr
    intro tval htval
    cases t with
    | none => cases htval
    | some sub =>
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub rfl

/-- `substInTypedTerm` preserves `Typed.Term.AppRefTArgsFO`. The substitution
rewrites only `Typ`-level annotations + `tArgs`; for `.ref/.app`, the new
`tArgs` is `tArgs.map (Typ.instantiate subst)`. Re-establish `hArgsFO` per
mapped element via `Typ.instantiate_preserves_FirstOrder`, and `hArgsRec`
per mapped element via `Typ.instantiate_preserves_AppRefTArgsFO` (L2). -/
theorem substInTypedTerm_preserves_AppRefTArgsFO
    {body : Typed.Term} {subst : Global → Option Typ}
    (hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t')
    (hsubstAR : ∀ g t', subst g = some t' → Typed.Typ.AppRefTArgsFO t')
    (hbody : Typed.Term.AppRefTArgsFO body) :
    Typed.Term.AppRefTArgsFO (substInTypedTerm subst body) := by
  induction hbody with
  | unit htyp =>
    unfold substInTypedTerm
    exact .unit (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp)
  | var htyp =>
    unfold substInTypedTerm
    exact .var (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp)
  | @ref typ e g tArgs htyp hArgsFO hArgsRec =>
    unfold substInTypedTerm
    refine .ref
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp)
      ?_ ?_
    · intro t' ht'
      rw [Array.mem_map] at ht'
      obtain ⟨t0, ht0mem, ht0eq⟩ := ht'
      subst ht0eq
      exact Typ.instantiate_preserves_FirstOrder subst hsubstFO (hArgsFO t0 ht0mem)
    · intro t' ht'
      rw [Array.mem_map] at ht'
      obtain ⟨t0, ht0mem, ht0eq⟩ := ht'
      subst ht0eq
      exact Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR
        (hArgsRec t0 ht0mem)
  | field htyp =>
    unfold substInTypedTerm
    exact .field (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp)
  | @tuple typ e ts htyp _h ih =>
    unfold substInTypedTerm
    refine .tuple
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | @array typ e ts htyp _h ih =>
    unfold substInTypedTerm
    refine .array
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | @ret typ e r htyp _h ih =>
    unfold substInTypedTerm
    exact .ret (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) ih
  | @«let» typ e p v b htyp _hv _hb ihv ihb =>
    unfold substInTypedTerm
    exact .let
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) ihv ihb
  | @«match» typ e scrut cases htyp _hscrut _hcases ihscrut ihcases =>
    unfold substInTypedTerm
    refine .match
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp)
      ihscrut ?_
    intro pc hpc
    obtain ⟨p0, hp0mem, hp0eq⟩ := list_mem_of_attach_map cases _ hpc
    subst hp0eq
    exact ihcases p0 hp0mem
  | @app typ e g tArgs args u htyp hArgsFO hArgsRec _hargs ihargs =>
    unfold substInTypedTerm
    refine .app
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp)
      ?_ ?_ ?_
    · intro t' ht'
      rw [Array.mem_map] at ht'
      obtain ⟨t0, ht0mem, ht0eq⟩ := ht'
      subst ht0eq
      exact Typ.instantiate_preserves_FirstOrder subst hsubstFO (hArgsFO t0 ht0mem)
    · intro t' ht'
      rw [Array.mem_map] at ht'
      obtain ⟨t0, ht0mem, ht0eq⟩ := ht'
      subst ht0eq
      exact Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR
        (hArgsRec t0 ht0mem)
    · intro a ha
      obtain ⟨a0, ha0mem, ha0eq⟩ := list_mem_of_attach_map args _ ha
      subst ha0eq
      exact ihargs a0 ha0mem
  | add htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .add (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | sub htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .sub (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | mul htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .mul (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | eqZero htyp _ iha =>
    unfold substInTypedTerm
    exact .eqZero (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | proj htyp _ iha =>
    unfold substInTypedTerm
    exact .proj (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | get htyp _ iha =>
    unfold substInTypedTerm
    exact .get (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | slice htyp _ iha =>
    unfold substInTypedTerm
    exact .slice (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | «set» htyp _ _ iha ihv =>
    unfold substInTypedTerm
    exact .set (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihv
  | store htyp _ iha =>
    unfold substInTypedTerm
    exact .store (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | load htyp _ iha =>
    unfold substInTypedTerm
    exact .load (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | ptrVal htyp _ iha =>
    unfold substInTypedTerm
    exact .ptrVal (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | assertEq htyp _ _ _ iha ihb ihr =>
    unfold substInTypedTerm
    exact .assertEq
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb ihr
  | ioGetInfo htyp _ ihk =>
    unfold substInTypedTerm
    exact .ioGetInfo (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) ihk
  | ioSetInfo htyp _ _ _ _ ihk ihi ihl ihr =>
    unfold substInTypedTerm
    exact .ioSetInfo
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) ihk ihi ihl ihr
  | ioRead htyp _ ihi =>
    unfold substInTypedTerm
    exact .ioRead (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) ihi
  | ioWrite htyp _ _ ihd ihr =>
    unfold substInTypedTerm
    exact .ioWrite (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) ihd ihr
  | u8BitDecomposition htyp _ iha =>
    unfold substInTypedTerm
    exact .u8BitDecomposition
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | u8ShiftLeft htyp _ iha =>
    unfold substInTypedTerm
    exact .u8ShiftLeft (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | u8ShiftRight htyp _ iha =>
    unfold substInTypedTerm
    exact .u8ShiftRight (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha
  | u8Xor htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8Xor (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | u8Add htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8Add (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | u8Sub htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8Sub (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | u8And htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8And (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | u8Or htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8Or (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | u8LessThan htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8LessThan
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | u32LessThan htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u32LessThan
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) iha ihb
  | @debug typ e label t r htyp ht _hr iht ihr =>
    unfold substInTypedTerm
    refine .debug
      (Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR htyp) ?_ ihr
    intro tval htval
    cases t with
    | none => cases htval
    | some sub =>
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub rfl

/-- Init clause for `concretize_PendingArgsFO_bridge`: the seed set of
pending entries (built by `concretizeSeed`) preserves the FO-args invariant
under `Typed.Decls.AppRefTArgsFO`. -/
theorem concretizeSeed_PendingArgsFO {decls : Typed.Decls}
    (hARFO : Typed.Decls.AppRefTArgsFO decls) :
    ∀ entry ∈ concretizeSeed decls, ∀ t ∈ entry.2, Typ.FirstOrder t := by
  unfold concretizeSeed
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
      ∀ entry ∈ acc, ∀ t ∈ entry.2, Typ.FirstOrder t)
  · intro entry hent
    -- empty HashSet has no entries.
    simp at hent
  · intro i acc hinv
    let p := decls.pairs[i.val]'i.isLt
    have hpmem : p ∈ decls.pairs.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem _)
    have hp_get : decls.getByKey p.1 = some p.2 :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hpmem
    cases hd : p.snd with
    | function f =>
      simp only [hd]
      by_cases hp : f.params.isEmpty = true
      · rw [if_pos hp]
        -- Apply L4a (output type), L4a per input type, L4b (body), L4c (body).
        obtain ⟨h_inputs, h_output, h_body⟩ := hARFO.1 p.1 f (by rw [← hd]; exact hp_get)
        -- After collectInTyp acc f.output.
        have h1 : ∀ entry ∈ collectInTyp acc f.output, ∀ t ∈ entry.2, Typ.FirstOrder t :=
          collectInTyp_PendingArgsFO_step h_output acc hinv
        -- After f.inputs.foldl.
        have h2 : ∀ entry ∈ f.inputs.foldl (fun s (_, t) => collectInTyp s t)
            (collectInTyp acc f.output), ∀ t ∈ entry.2, Typ.FirstOrder t := by
          have aux : ∀ (l : List (Local × Typ)) (acc' : Std.HashSet (Global × Array Typ)),
              (∀ entry ∈ acc', ∀ t ∈ entry.2, Typ.FirstOrder t) →
              (∀ p ∈ l, Typed.Typ.AppRefTArgsFO p.2) →
              ∀ entry ∈ l.foldl (fun s (_, t) => collectInTyp s t) acc',
                ∀ t ∈ entry.2, Typ.FirstOrder t := by
            intro l
            induction l with
            | nil => intro acc' hacc' _ entry hent; exact hacc' entry hent
            | cons hd' tl ih_l =>
              intro acc' hacc' hcs
              simp only [List.foldl_cons]
              apply ih_l
              · obtain ⟨_, t⟩ := hd'
                exact collectInTyp_PendingArgsFO_step
                  (hcs (_, t) List.mem_cons_self) acc' hacc'
              · intro p' hp'; exact hcs p' (List.mem_cons_of_mem _ hp')
          apply aux f.inputs _ h1
          intro p' hp'
          have hpmem_typed : p'.2 ∈ f.inputs.map Prod.snd := by
            obtain ⟨l, t⟩ := p'
            exact List.mem_map.mpr ⟨(l, t), hp', rfl⟩
          exact h_inputs p'.2 hpmem_typed
        -- After collectInTypedTerm body.
        have h3 := collectInTypedTerm_PendingArgsFO_step h_body _ h2
        -- After collectCalls body.
        exact collectCalls_PendingArgsFO_step h_body _ h3
      · rw [if_neg hp]; exact hinv
    | dataType dt =>
      simp only [hd]
      by_cases hp : dt.params.isEmpty = true
      · rw [if_pos hp]
        have h_dt := hARFO.2.1 p.1 dt (by rw [← hd]; exact hp_get)
        -- dt.constructors.foldl + per-c c.argTypes.foldl collectInTyp.
        have aux_inner : ∀ (l : List Typ) (acc' : Std.HashSet (Global × Array Typ)),
            (∀ entry ∈ acc', ∀ t ∈ entry.2, Typ.FirstOrder t) →
            (∀ t ∈ l, Typed.Typ.AppRefTArgsFO t) →
            ∀ entry ∈ l.foldl collectInTyp acc',
              ∀ t ∈ entry.2, Typ.FirstOrder t := by
          intro l
          induction l with
          | nil => intro acc' hacc' _ entry hent; exact hacc' entry hent
          | cons hd' tl ih_l =>
            intro acc' hacc' hcs
            simp only [List.foldl_cons]
            apply ih_l
            · exact collectInTyp_PendingArgsFO_step
                (hcs hd' List.mem_cons_self) acc' hacc'
            · intro t' ht'; exact hcs t' (List.mem_cons_of_mem _ ht')
        have aux : ∀ (cs : List Constructor) (acc' : Std.HashSet (Global × Array Typ)),
            (∀ entry ∈ acc', ∀ t ∈ entry.2, Typ.FirstOrder t) →
            (∀ c ∈ cs, ∀ t ∈ c.argTypes, Typed.Typ.AppRefTArgsFO t) →
            ∀ entry ∈ cs.foldl (fun s c => c.argTypes.foldl collectInTyp s) acc',
              ∀ t ∈ entry.2, Typ.FirstOrder t := by
          intro cs
          induction cs with
          | nil => intro acc' hacc' _ entry hent; exact hacc' entry hent
          | cons hd' tl ih_l =>
            intro acc' hacc' hcs
            simp only [List.foldl_cons]
            apply ih_l
            · exact aux_inner hd'.argTypes acc' hacc'
                (fun t ht => hcs hd' List.mem_cons_self t ht)
            · intro c hc; exact hcs c (List.mem_cons_of_mem _ hc)
        exact aux dt.constructors _ hinv h_dt
      · rw [if_neg hp]; exact hinv
    | constructor _ _ =>
      simp only [hd]; exact hinv

/-- Drain-state invariant: every new function has a first-order output. -/
def DrainState.NewFunctionsFO (st : DrainState) : Prop :=
  ∀ f ∈ st.newFunctions, Typ.FirstOrder f.output

theorem DrainState.NewFunctionsFO.init
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewFunctionsFO
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  intro f hf
  simp only [Array.not_mem_empty] at hf

/-! #### `PendingArgsFO` — companion invariant.

The drain leaf below needs the substitution-side condition of
`Typ.instantiate_preserves_FirstOrder` discharged. The substitution is
`mkParamSubst f.params entry.2`; its image is exactly the entries of
`entry.2` paired with `f.params`. So we need `∀ t ∈ entry.2, Typ.FirstOrder
t`. Enforce as a drain-state invariant carried alongside `NewFunctionsFO`.

Seed-init + iter-preservation are bundled into a single F=1 leaf
`concretize_PendingArgsFO_bridge` further below — closing requires a
typed-side hypothesis `Typed.Decls.AppRefTArgsFO` (every `.app/.ref tArgs`
in any function body / data-type / type-annotation has FO `tArgs`), which
is a new conjunct that would need to be wired into `WellFormed`. The
4-level chain through `concretize_drain_preserves_NewFunctionsFO` is F=0
modulo that bridge. -/

@[expose] def DrainState.PendingArgsFO (st : DrainState) : Prop :=
  ∀ entry ∈ st.pending, ∀ t ∈ entry.2, Typ.FirstOrder t

/-- Helper: if `mkParamSubst params args g = some t'`, then `t' ∈ args`.

Proof by induction on `params.zip args.toList`. Generalize the accumulator
so the recursion has free state. -/
theorem mkParamSubst_some_mem_aux
    (l : List (String × Typ)) :
    ∀ (acc : Std.HashMap Global Typ) (g : Global) (t' : Typ),
      (l.foldl (fun m (p : String × Typ) => m.insert (Global.init p.1) p.2) acc)[g]? = some t' →
      acc[g]? = some t' ∨ ∃ p ∈ l, p.2 = t' := by
  induction l with
  | nil =>
    intro acc g t' h
    simp only [List.foldl_nil] at h
    exact Or.inl h
  | cons hd tl ih =>
    intro acc g t' h
    simp only [List.foldl_cons] at h
    rcases ih (acc.insert (Global.init hd.1) hd.2) g t' h with hL | hR
    · -- hL : (acc.insert ..)[g]? = some t'
      rw [Std.HashMap.getElem?_insert] at hL
      by_cases hkeq : (Global.init hd.1 == g) = true
      · simp [hkeq] at hL
        subst hL
        exact Or.inr ⟨hd, List.mem_cons_self, rfl⟩
      · have hkeqf : (Global.init hd.1 == g) = false :=
          Bool.not_eq_true _ |>.mp hkeq
        simp [hkeqf] at hL
        exact Or.inl hL
    · -- hR : ∃ p ∈ tl, p.snd = t'
      rcases hR with ⟨p, hpmem, hpeq⟩
      exact Or.inr ⟨p, List.mem_cons_of_mem _ hpmem, hpeq⟩

theorem mkParamSubst_some_mem
    (params : List String) (args : Array Typ) {g : Global} {t' : Typ}
    (h : mkParamSubst params args g = some t') :
    t' ∈ args := by
  unfold mkParamSubst at h
  simp only at h
  rcases mkParamSubst_some_mem_aux _ ∅ g t' h with hempty | ⟨p, hpmem, hpeq⟩
  · simp at hempty
  · -- p ∈ params.zip args.toList ⟹ p.snd ∈ args.toList ⟹ p.snd ∈ args
    have hin_args : p.2 ∈ args.toList := (List.of_mem_zip hpmem).2
    rw [← hpeq]
    exact Array.mem_toList_iff.mp hin_args

/-- Helper: if `g`'s lookup in `acc` is some, every foldl-insert step preserves
that property. Pure stdlib reasoning over `Std.HashMap.insert`. -/
theorem mkParamSubst_acc_some_preserved
    (l : List (String × Typ)) (g : Global) :
    ∀ (acc : Std.HashMap Global Typ),
      (∃ t, acc[g]? = some t) →
      ∃ t, (l.foldl (fun m (p : String × Typ) => m.insert (Global.init p.1) p.2) acc)[g]? = some t := by
  induction l with
  | nil => intro acc h; simpa using h
  | cons hd tl ih =>
    intro acc ⟨t, hget⟩
    simp only [List.foldl_cons]
    apply ih
    rw [Std.HashMap.getElem?_insert]
    by_cases hkeq : (Global.init hd.1 == g) = true
    · exact ⟨hd.2, by simp [hkeq]⟩
    · have hkeqf : (Global.init hd.1 == g) = false := Bool.not_eq_true _ |>.mp hkeq
      exact ⟨t, by simp [hkeqf, hget]⟩

/-- Helper: foldl over `l : List (String × Typ)` starting from any `acc`.
If some `(p, _) ∈ l` has `Global.init p = g`, the final lookup at `g` is some. -/
theorem mkParamSubst_total_aux
    (l : List (String × Typ)) (g : Global)
    (h_in : ∃ p ∈ l, g = Global.init p.1) :
    ∀ (acc : Std.HashMap Global Typ),
      ∃ t, (l.foldl (fun m (p : String × Typ) => m.insert (Global.init p.1) p.2) acc)[g]? = some t := by
  induction l with
  | nil =>
    obtain ⟨p, hpmem, _⟩ := h_in
    cases hpmem
  | cons hd tl ih =>
    intro acc
    obtain ⟨p, hpmem, hpeq⟩ := h_in
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hpmem with hhd | htl
    · -- p = hd, so the head insert places `Global.init hd.1 = g ↦ hd.2`.
      -- After all subsequent inserts, that lookup persists or is overwritten
      -- by a later same-key insert (still some).
      apply mkParamSubst_acc_some_preserved
      refine ⟨hd.2, ?_⟩
      rw [Std.HashMap.getElem?_insert]
      have hkeq : (Global.init hd.1 == g) = true := by
        rw [hhd] at hpeq
        rw [hpeq]
        exact BEq.rfl
      simp [hkeq]
    · exact ih ⟨p, htl, hpeq⟩ _

/-- The substitution `mkParamSubst params args` is total on globals of the
structural form `Global.init p` for any `p ∈ params`, given matching arity. -/
theorem mkParamSubst_total_on_params
    (params : List String) (args : Array Typ)
    (h_arity : args.size = params.length)
    {g : Global} (h_in : ∃ p ∈ params, g = Global.init p) :
    ∃ t, mkParamSubst params args g = some t := by
  unfold mkParamSubst
  simp only
  -- Lift `∃ p ∈ params, g = Global.init p` to `∃ p ∈ params.zip args.toList,
  -- g = Global.init p.1` using `h_arity`.
  obtain ⟨p, hpmem, hpeq⟩ := h_in
  -- Find the index of `p` in `params`.
  obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hpmem
  -- The corresponding zip entry exists since `args.size = params.length`.
  have hi_lt_args : i < args.toList.length := by
    rw [Array.length_toList]; omega
  have hzip_mem : (p, args.toList[i]'hi_lt_args) ∈ params.zip args.toList := by
    have hzget : (params.zip args.toList)[i]'(by
        rw [List.length_zip]; omega) = (p, args.toList[i]'hi_lt_args) := by
      rw [List.getElem_zip]
      simp [hi_eq]
    exact hzget ▸ List.getElem_mem _
  exact mkParamSubst_total_aux (params.zip args.toList) g
    ⟨(p, args.toList[i]'hi_lt_args), hzip_mem, hpeq⟩ ∅

/-- Drain leaf: when the function-arm of `concretizeDrainEntry` specializes
template `f` against `args`, the new function's output `Typ.instantiate subst
f.output` is FO. Two side conditions: (i) `f.output` FO (from `hP`) and
(ii) the substitution maps every variable to an FO type — discharged via
the new `PendingArgsFO` companion invariant (every pending entry carries FO
type-args); `mkParamSubst_some_mem` then derives `t' ∈ entry.2` for every
substituted `t'`, and `hpargs` gives FO. -/
theorem concretizeDrainEntry_preserves_NewFunctionsFO
    {decls : Typed.Decls} (hP : Typed.Decls.FirstOrderReturn decls)
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsFO state)
    (entry : Global × Array Typ)
    (hentryFO : ∀ t ∈ entry.2, Typ.FirstOrder t)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    DrainState.NewFunctionsFO state' := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f' hf'mem
        rcases Array.mem_push.mp hf'mem with hin | heq
        · exact hinv f' hin
        · subst heq
          simp only
          apply Typ.instantiate_preserves_FirstOrder
          · intro g t' hsub
            -- `t' ∈ entry.2` via mkParamSubst_some_mem; then `hentryFO`.
            exact hentryFO t' (mkParamSubst_some_mem _ _ hsub)
          · exact hP entry.1 f hf_get
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f hf; exact hinv f hf
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

theorem concretizeDrainEntry_list_foldlM_preserves_NewFunctionsFO
    {decls : Typed.Decls} (hP : Typed.Decls.FirstOrderReturn decls)
    (L : List (Global × Array Typ))
    (hLargsFO : ∀ entry ∈ L, ∀ t ∈ entry.2, Typ.FirstOrder t)
    (state0 state' : DrainState)
    (hinv0 : DrainState.NewFunctionsFO state0)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    DrainState.NewFunctionsFO state' := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hhdFO : ∀ t ∈ hd.2, Typ.FirstOrder t :=
        hLargsFO hd List.mem_cons_self
      have htlFO : ∀ entry ∈ tl, ∀ t ∈ entry.2, Typ.FirstOrder t :=
        fun e he => hLargsFO e (List.mem_cons_of_mem _ he)
      have hinv1 : DrainState.NewFunctionsFO s'' :=
        concretizeDrainEntry_preserves_NewFunctionsFO hP hinv0 hd hhdFO hs''
      exact ih htlFO s'' hinv1 hstep

theorem concretizeDrainIter_preserves_NewFunctionsFO
    {decls : Typed.Decls} (hP : Typed.Decls.FirstOrderReturn decls)
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsFO state)
    (hpargs : DrainState.PendingArgsFO state)
    (hstep : concretizeDrainIter decls state = .ok state') :
    DrainState.NewFunctionsFO state' := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : DrainState.NewFunctionsFO state0 := hinv
  -- Each entry in `state.pending.toArray.toList` has FO args by `hpargs`.
  have hLargsFO : ∀ entry ∈ state.pending.toArray.toList,
      ∀ t ∈ entry.2, Typ.FirstOrder t := by
    intro entry hentry t ht
    apply hpargs entry _ t ht
    rw [Array.mem_toList_iff] at hentry
    exact (Std.HashSet.mem_toArray.mp hentry)
  exact concretizeDrainEntry_list_foldlM_preserves_NewFunctionsFO hP
    state.pending.toArray.toList hLargsFO state0 state' hinv0 hstep

theorem concretize_drain_preserves_NewFunctionsFO
    {decls : Typed.Decls} (hP : Typed.Decls.FirstOrderReturn decls)
    (fuel : Nat) (init : DrainState)
    (hinv : DrainState.NewFunctionsFO init)
    (hpargs_init : DrainState.PendingArgsFO init)
    (hpargs_chain : ∀ s s', DrainState.PendingArgsFO s →
      concretizeDrainIter decls s = .ok s' → DrainState.PendingArgsFO s')
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    DrainState.NewFunctionsFO drained := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : DrainState.NewFunctionsFO state' :=
          concretizeDrainIter_preserves_NewFunctionsFO hP hinv hpargs_init hstate'
        have hpargs' : DrainState.PendingArgsFO state' :=
          hpargs_chain init state' hpargs_init hstate'
        exact ih state' hinv' hpargs' hdrain

/-! ### `PendingArgsFO` — companion invariant + chain.

The substitution-FO side condition of the FO drain leaf is discharged by a
companion drain invariant `DrainState.PendingArgsFO` (every pending entry's
args are FO), threaded through the 4-level drain chain. Init
(`concretizeSeed_preserves_PendingArgsFO`) and chain-preservation
(`concretizeDrainEntry_preserves_PendingArgsFO`) are F=1 leaves below.
The `WellFormed` field needed to discharge them (`Typed.Decls.AppRefTArgsFO
decls`) is not yet wired; the BLOCKED notes on each leaf describe the
closure path.

The previous approach took a universal `hparamsEmpty : ∀ g f, ... →
f.params = []` to make `subst = ∅`. That hypothesis is structurally false
for polymorphic source — a non-entry polymorphic function is a
counterexample — so it cannot be discharged from `WellFormed t` alone.

Sister lemma `concretize_preserves_TermRefsDt` drops `hparamsEmpty` via
`substInTypedTerm_preserves_RefsDt` — the path is the same in shape, but
`RefsDt` only checks term-level globals (untouched by substitution),
whereas `FirstOrder` must inspect substituted *types*. -/

/-- Drain entry leaf: `concretizeDrainEntry` preserves `PendingArgsFO`.
The substitution image is FO via `mkParamSubst_some_mem` + `hentryFO`. -/
theorem concretizeDrainEntry_preserves_PendingArgsFO
    {decls : Typed.Decls} (hARFO : Typed.Decls.AppRefTArgsFO decls)
    {state state' : DrainState}
    (hinv : DrainState.PendingArgsFO state)
    (entry : Global × Array Typ)
    (hentryFO : ∀ t ∈ entry.2, Typ.FirstOrder t)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    DrainState.PendingArgsFO state' := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    -- Build subst-FO and subst-AR helpers.
    have hentryAR : ∀ t ∈ entry.2, Typed.Typ.AppRefTArgsFO t :=
      fun t ht => Typ.FirstOrder.toAppRefTArgsFO (hentryFO t ht)
    -- Pending (post drain entry) — start from state.pending with hinv.
    have hinv_pending : ∀ p ∈ state.pending, ∀ t ∈ p.2, Typ.FirstOrder t := hinv
    split at hstep
    · rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        -- subst = mkParamSubst f.params entry.2.
        -- Substitution image is in entry.2 → FO via hentryFO; AR via toAppRefTArgsFO.
        let subst := mkParamSubst f.params entry.2
        have hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t' :=
          fun g t' h => hentryFO t' (mkParamSubst_some_mem _ _ h)
        have hsubstAR : ∀ g t', subst g = some t' → Typed.Typ.AppRefTArgsFO t' :=
          fun g t' h => Typ.FirstOrder.toAppRefTArgsFO (hsubstFO g t' h)
        obtain ⟨h_inputs, h_output, h_body⟩ := hARFO.1 entry.1 f hf_get
        -- new outputs/inputs/body have AppRefTArgsFO via L2/L3.
        have hnewOutputAR : Typed.Typ.AppRefTArgsFO (Typ.instantiate subst f.output) :=
          Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR h_output
        have hnewInputs_AR : ∀ p ∈ f.inputs.map (fun (l, t) => (l, Typ.instantiate subst t)),
            Typed.Typ.AppRefTArgsFO p.2 := by
          intro p hp
          rw [List.mem_map] at hp
          obtain ⟨⟨l, t⟩, ht_mem, ht_eq⟩ := hp
          subst ht_eq
          exact Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR
            (h_inputs t (List.mem_map.mpr ⟨(l, t), ht_mem, rfl⟩))
        have hnewBodyAR : Typed.Term.AppRefTArgsFO (substInTypedTerm subst f.body) :=
          substInTypedTerm_preserves_AppRefTArgsFO hsubstFO hsubstAR h_body
        -- Now the pending update: chain L4a (output) → L4a per input → L4b → L4c.
        intro p hp
        -- p ∈ collectCalls (collectInTypedTerm (foldl collectInTyp (collectInTyp pending newOutput) newInputs) newBody) newBody
        have h1 : ∀ p' ∈ collectInTyp state.pending (Typ.instantiate subst f.output),
            ∀ t ∈ p'.2, Typ.FirstOrder t :=
          collectInTyp_PendingArgsFO_step hnewOutputAR _ hinv_pending
        have h2 : ∀ p' ∈ (f.inputs.map (fun (l, t) => (l, Typ.instantiate subst t))).foldl
            (fun s (_, t) => collectInTyp s t)
            (collectInTyp state.pending (Typ.instantiate subst f.output)),
            ∀ t ∈ p'.2, Typ.FirstOrder t := by
          have aux : ∀ (l : List (Local × Typ)) (acc : Std.HashSet (Global × Array Typ)),
              (∀ p' ∈ acc, ∀ t ∈ p'.2, Typ.FirstOrder t) →
              (∀ p' ∈ l, Typed.Typ.AppRefTArgsFO p'.2) →
              ∀ p' ∈ l.foldl (fun s (_, t) => collectInTyp s t) acc,
                ∀ t ∈ p'.2, Typ.FirstOrder t := by
            intro l
            induction l with
            | nil => intro acc hacc _ p' hp'; exact hacc p' hp'
            | cons hd tl ih_l =>
              intro acc hacc hcs
              simp only [List.foldl_cons]
              apply ih_l
              · obtain ⟨_, t⟩ := hd
                exact collectInTyp_PendingArgsFO_step
                  (hcs (_, t) List.mem_cons_self) acc hacc
              · intro p' hp'; exact hcs p' (List.mem_cons_of_mem _ hp')
          exact aux _ _ h1 hnewInputs_AR
        have h3 := collectInTypedTerm_PendingArgsFO_step hnewBodyAR _ h2
        have h4 := collectCalls_PendingArgsFO_step (decls := decls) hnewBodyAR _ h3
        exact h4 p hp
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        let subst := mkParamSubst dt.params entry.2
        have hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t' :=
          fun g t' h => hentryFO t' (mkParamSubst_some_mem _ _ h)
        have hsubstAR : ∀ g t', subst g = some t' → Typed.Typ.AppRefTArgsFO t' :=
          fun g t' h => Typ.FirstOrder.toAppRefTArgsFO (hsubstFO g t' h)
        have h_dt := hARFO.2.1 entry.1 dt hdt_get
        intro p hp
        -- p ∈ newCtors.foldl (fun s c => c.argTypes.foldl collectInTyp s) state.pending
        -- where newCtors = dt.constructors.map (fun c => { c with argTypes := c.argTypes.map (instantiate subst) })
        have aux_inner : ∀ (l : List Typ) (acc : Std.HashSet (Global × Array Typ)),
            (∀ p' ∈ acc, ∀ t ∈ p'.2, Typ.FirstOrder t) →
            (∀ t ∈ l, Typed.Typ.AppRefTArgsFO t) →
            ∀ p' ∈ l.foldl collectInTyp acc, ∀ t ∈ p'.2, Typ.FirstOrder t := by
          intro l
          induction l with
          | nil => intro acc hacc _ p' hp'; exact hacc p' hp'
          | cons hd tl ih_l =>
            intro acc hacc hcs
            simp only [List.foldl_cons]
            apply ih_l
            · exact collectInTyp_PendingArgsFO_step
                (hcs hd List.mem_cons_self) acc hacc
            · intro t' ht'; exact hcs t' (List.mem_cons_of_mem _ ht')
        have aux : ∀ (cs : List Constructor) (acc : Std.HashSet (Global × Array Typ)),
            (∀ p' ∈ acc, ∀ t ∈ p'.2, Typ.FirstOrder t) →
            (∀ c ∈ cs, ∀ t ∈ c.argTypes, Typed.Typ.AppRefTArgsFO t) →
            ∀ p' ∈ cs.foldl (fun s c => c.argTypes.foldl collectInTyp s) acc,
              ∀ t ∈ p'.2, Typ.FirstOrder t := by
          intro cs
          induction cs with
          | nil => intro acc hacc _ p' hp'; exact hacc p' hp'
          | cons hd tl ih_l =>
            intro acc hacc hcs
            simp only [List.foldl_cons]
            apply ih_l
            · exact aux_inner hd.argTypes acc hacc
                (fun t ht => hcs hd List.mem_cons_self t ht)
            · intro c hc; exact hcs c (List.mem_cons_of_mem _ hc)
        -- Apply aux on the rewritten ctors.
        let newCtors := dt.constructors.map fun c =>
          ({ c with argTypes := c.argTypes.map (Typ.instantiate subst) } : Constructor)
        have hnewCtors_AR : ∀ c ∈ newCtors, ∀ t ∈ c.argTypes, Typed.Typ.AppRefTArgsFO t := by
          intro c hc t ht
          rw [List.mem_map] at hc
          obtain ⟨c0, hc0_mem, hc0_eq⟩ := hc
          subst hc0_eq
          rw [List.mem_map] at ht
          obtain ⟨t0, ht0_mem, ht0_eq⟩ := ht
          subst ht0_eq
          exact Typ.instantiate_preserves_AppRefTArgsFO subst hsubstFO hsubstAR
            (h_dt c0 hc0_mem t0 ht0_mem)
        exact aux newCtors _ hinv_pending hnewCtors_AR p hp
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

/-- List foldlM lift of the entry leaf. -/
theorem concretizeDrainEntry_list_foldlM_preserves_PendingArgsFO
    {decls : Typed.Decls} (hARFO : Typed.Decls.AppRefTArgsFO decls)
    (L : List (Global × Array Typ))
    (hLargsFO : ∀ entry ∈ L, ∀ t ∈ entry.2, Typ.FirstOrder t)
    (state0 state' : DrainState)
    (hinv0 : DrainState.PendingArgsFO state0)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    DrainState.PendingArgsFO state' := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hhdFO : ∀ t ∈ hd.2, Typ.FirstOrder t :=
        hLargsFO hd List.mem_cons_self
      have htlFO : ∀ entry ∈ tl, ∀ t ∈ entry.2, Typ.FirstOrder t :=
        fun e he => hLargsFO e (List.mem_cons_of_mem _ he)
      have hinv1 : DrainState.PendingArgsFO s'' :=
        concretizeDrainEntry_preserves_PendingArgsFO hARFO hinv0 hd hhdFO hs''
      exact ih htlFO s'' hinv1 hstep

/-- Drain iter lift. -/
theorem concretizeDrainIter_preserves_PendingArgsFO
    {decls : Typed.Decls} (hARFO : Typed.Decls.AppRefTArgsFO decls)
    {state state' : DrainState}
    (hpargs : DrainState.PendingArgsFO state)
    (hstep : concretizeDrainIter decls state = .ok state') :
    DrainState.PendingArgsFO state' := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : DrainState.PendingArgsFO state0 := by
    intro entry hentry
    exact (Std.HashSet.not_mem_empty hentry).elim
  have hLargsFO : ∀ entry ∈ state.pending.toArray.toList,
      ∀ t ∈ entry.2, Typ.FirstOrder t := by
    intro entry hentry t ht
    apply hpargs entry _ t ht
    rw [Array.mem_toList_iff] at hentry
    exact (Std.HashSet.mem_toArray.mp hentry)
  exact concretizeDrainEntry_list_foldlM_preserves_PendingArgsFO hARFO
    state.pending.toArray.toList hLargsFO state0 state' hinv0 hstep

/-! **PendingArgsFO bridge (F=1)**: combined seed-init + iter-level
preservation of `DrainState.PendingArgsFO`. Closure: structural induction
over `collectInTyp` / `collectInTypedTerm` / `collectCalls` (init clause)
+ `concretizeDrainEntry` step (iter clause). -/

theorem concretize_PendingArgsFO_bridge
    (decls : Typed.Decls)
    (_hARFO : Typed.Decls.AppRefTArgsFO decls) :
    DrainState.PendingArgsFO
        { pending := concretizeSeed decls, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } ∧
    (∀ s s', DrainState.PendingArgsFO s →
      concretizeDrainIter decls s = .ok s' → DrainState.PendingArgsFO s') :=
  ⟨concretizeSeed_PendingArgsFO _hARFO,
   fun _ _ hpargs hstep =>
     concretizeDrainIter_preserves_PendingArgsFO _hARFO hpargs hstep⟩

theorem concretize_preserves_FirstOrderReturn
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hP : Typed.Decls.FirstOrderReturn typedDecls)
    (hARFO : Typed.Decls.AppRefTArgsFO typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls) :
    Concrete.Decls.FirstOrderReturn concDecls := by
  intro g f hget
  apply concretize_preserves_FirstOrderReturn_of_drainInv hP hconc _ g f hget
  intro drained hdrain f' hfmem
  have hinit := DrainState.NewFunctionsFO.init (concretizeSeed typedDecls)
  have ⟨hpargs_init, hpargs_chain⟩ :=
    concretize_PendingArgsFO_bridge typedDecls hARFO
  exact concretize_drain_preserves_NewFunctionsFO hP _ _ hinit hpargs_init
    hpargs_chain hdrain f' hfmem


end Aiur

end -- public section
