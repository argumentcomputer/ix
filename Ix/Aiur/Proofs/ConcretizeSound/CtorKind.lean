module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.Shapes

/-!
PLAN_3B Phase A.2/A.3 (typed↔monoDecls↔concDecls ctor kind correspondence)
+ reverse origin classification + explicit-structure variants + Phase 0
(`concretizeBuild` lifts every newDt/newFn name) + explicit-structure
`concretizeBuild_at_newDt_name`. Extracted from `ConcretizeSound.lean`
2026-04-29.
-/

public section

namespace Aiur

open Source

/-! ### PLAN_3B Phase A.3 — monoDecls↔concDecls ctor kind correspondence (forward).

Trivial specialization of `step4Lower_fold_kind_at_key` to the constructor case. -/
theorem step4Lower_preserves_ctor_kind_fwd
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {dt : DataType} {c : Constructor}
    (hget_mono : monoDecls.getByKey g = some (.constructor dt c))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt cd_c, concDecls.getByKey g = some (.constructor cdt cd_c) := by
  have h := step4Lower_fold_kind_at_key hget_mono hfold
  simp only at h
  exact h

/-- Phase A.3 dataType analog: trivial specialization of
`step4Lower_fold_kind_at_key` to the dataType case. -/
theorem step4Lower_preserves_dataType_kind_fwd
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {dt : DataType}
    (hget_mono : monoDecls.getByKey g = some (.dataType dt))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt, concDecls.getByKey g = some (.dataType cdt) := by
  have h := step4Lower_fold_kind_at_key hget_mono hfold
  simp only at h
  exact h

/-- Phase A.3 function analog: trivial specialization of
`step4Lower_fold_kind_at_key` to the function case. -/
theorem step4Lower_preserves_function_kind_fwd
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {f : Typed.Function}
    (hget_mono : monoDecls.getByKey g = some (.function f))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cf, concDecls.getByKey g = some (.function cf) := by
  have h := step4Lower_fold_kind_at_key hget_mono hfold
  simp only at h
  exact h

/-! ### PLAN_3B Phase A.2 — typed↔monoDecls ctor kind correspondence.

Trace through the three folds of `concretizeBuild`:
* `fromSource` fold processes the unique `(g, .ctor td_dt td_c)` pair under
  `td_dt.params = []`, inserting `.constructor` at `g`. Other pairs have
  key ≠ `g` (IndexMap key uniqueness) so their inserts don't touch `g`.
* `withNewDts` fold inserts at `dt.name` (`.dataType`) and at
  `dt.name.pushNamespace c.nameHead` (`.constructor`). Under `hDtNotKey`,
  no `.dataType` insertion at `g`. Possible `.constructor` insertion at
  `cName = g` preserves ctor-kind.
* `newFunctions` fold inserts at `f.name` (`.function`). Under `hFnNotKey`,
  no insertion at `g`.
-/

-- `Global.ne_pushNamespace` moved upstream to `ConcretizeSound/Layout.lean`
-- 2026-05-04 to support `layoutMap_dataType_size_extract`.

namespace PhaseA2

/-- Local named copy of the `srcStep` lambda from `concretizeBuild`'s
`fromSource` fold. -/
def srcStep (decls : Typed.Decls) (mono : MonoMap) :
    Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
  fun acc p =>
    let emptySubst : Global → Option Typ := fun _ => none
    let (key, d) := p
    match d with
    | .function f =>
      if f.params.isEmpty then
        acc.insert key (.function
          { f with
            inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
            output := rewriteTyp emptySubst mono f.output,
            body := rewriteTypedTerm decls emptySubst mono f.body })
      else acc
    | .dataType dt =>
      if dt.params.isEmpty then
        let newCtors := dt.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
        acc.insert key (.dataType { dt with constructors := newCtors })
      else acc
    | .constructor dt c =>
      if dt.params.isEmpty then
        let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
        let newCtor : Constructor := { c with argTypes := newArgTypes }
        let rewrittenCtors := dt.constructors.map fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
        let newDt : DataType := { dt with constructors := rewrittenCtors }
        acc.insert key (.constructor newDt newCtor)
      else acc

/-- Local named copy of the `dtStep` lambda from `concretizeBuild`'s
`withNewDts` fold. -/
@[expose] def dtStep (mono : MonoMap) :
    Typed.Decls → DataType → Typed.Decls :=
  fun acc dt =>
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    let acc' := acc.insert dt.name (.dataType newDt)
    rewrittenCtors.foldl
      (fun acc'' c =>
        let cName := dt.name.pushNamespace c.nameHead
        acc''.insert cName (.constructor newDt c))
      acc'

/-- Local named copy of the `fnStep` lambda from `concretizeBuild`'s outer fold. -/
@[expose] def fnStep (decls : Typed.Decls) (mono : MonoMap) :
    Typed.Decls → Typed.Function → Typed.Decls :=
  fun acc f =>
    let emptySubst : Global → Option Typ := fun _ => none
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body })

/-- `concretizeBuild` re-expressed via the named step functions. -/
theorem concretizeBuild_eq
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType) :
    concretizeBuild decls mono newFunctions newDataTypes =
      newFunctions.foldl (fnStep decls mono)
        (newDataTypes.foldl (dtStep mono)
          (decls.pairs.foldl (srcStep decls mono) default)) := by
  rfl

/-- A single step of `srcStep` on a pair with key `≠ g` preserves `getByKey g`. -/
theorem srcStep_preserves_other_key
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} (acc : Typed.Decls) (p : Global × Typed.Declaration)
    (hne : (p.1 == g) = false) :
    (srcStep decls mono acc p).getByKey g = acc.getByKey g := by
  unfold srcStep
  obtain ⟨k, d⟩ := p
  cases d with
  | function f =>
    by_cases hp : f.params.isEmpty
    · simp [hp]; rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
    · simp [hp]
  | dataType dt =>
    by_cases hp : dt.params.isEmpty
    · simp [hp]; rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
    · simp [hp]
  | constructor dt c =>
    by_cases hp : dt.params.isEmpty
    · simp [hp]; rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
    · simp [hp]

/-- A `srcStep` foldl over a list with no pair having key `g` preserves `getByKey g`. -/
theorem srcStep_foldl_no_g_preserves
    (decls : Typed.Decls) (mono : MonoMap) {g : Global} :
    ∀ (xs : List (Global × Typed.Declaration)) (init : Typed.Decls),
      (∀ p ∈ xs, (p.1 == g) = false) →
      (xs.foldl (srcStep decls mono) init).getByKey g = init.getByKey g
  | [], init, _ => rfl
  | p :: rest, init, hne => by
    simp only [List.foldl_cons]
    have h1 : (srcStep decls mono init p).getByKey g = init.getByKey g :=
      srcStep_preserves_other_key decls mono init p (hne p List.mem_cons_self)
    have ih := srcStep_foldl_no_g_preserves decls mono rest (srcStep decls mono init p)
      (fun p' hp' => hne p' (List.mem_cons_of_mem _ hp'))
    rw [ih, h1]

/-- A single step of `srcStep` on the target `(g, .ctor td_dt td_c)` pair under
`td_dt.params = []` produces a `.constructor` entry at `g`. -/
theorem srcStep_at_g_inserts_ctor
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hdt_params : td_dt.params = []) :
    ∃ md_dt md_c,
      (srcStep decls mono acc (g, .constructor td_dt td_c)).getByKey g =
        some (.constructor md_dt md_c) := by
  unfold srcStep
  have hp : td_dt.params.isEmpty = true := by rw [hdt_params]; rfl
  let emptySubst : Global → Option Typ := fun _ => none
  let newCtor : Constructor := { td_c with
    argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { td_dt with
    constructors := td_dt.constructors.map fun c' =>
      { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) } }
  simp only [hp, if_true]
  exact ⟨newDt, newCtor, IndexMap.getByKey_insert_self _ _ _⟩

/-- `fromSource` fold inserts `.constructor` at `g` (split-pattern proof). -/
theorem fromSource_inserts_ctor_at_key
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hget : decls.getByKey g = some (.constructor td_dt td_c))
    (hdt_params : td_dt.params = []) :
    ∃ md_dt md_c,
      (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
        some (.constructor md_dt md_c) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.constructor td_dt td_c) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  -- Key uniqueness via IndexMap.
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.constructor td_dt td_c) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  -- Split list at the unique occurrence.
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  -- Pre and post lists have no pair with key g.
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.constructor td_dt td_c) ∈ pre := hp_eq ▸ hp
      -- Same pair appears twice in decls.pairs.toList — contradicts IndexMap uniqueness.
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.constructor td_dt td_c) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp
        exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  -- Compose.
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  have hpre_eq : (List.foldl (srcStep decls mono) default pre).getByKey g = none := by
    have := srcStep_foldl_no_g_preserves decls mono pre default hno_g_pre
    rw [this]
    -- default IndexMap has none at every key.
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[g]?).bind _ = none
    have : (default : Typed.Decls).indices[g]? = none := by
      show ((default : Std.HashMap Global Nat))[g]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  obtain ⟨md_dt, md_c, hstep⟩ := srcStep_at_g_inserts_ctor decls mono
    (List.foldl (srcStep decls mono) default pre) hdt_params (g := g) (td_dt := td_dt) (td_c := td_c)
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact ⟨md_dt, md_c, hstep⟩

/-- Inner ctor-fold preserves ctor-kind at `g` (each step inserts `.constructor`). -/
theorem dtCtorFold_preserves_ctor_kind
    (mono : MonoMap) (dt : DataType) (newDt : DataType)
    {g : Global}
    (cs : List Constructor) (acc : Typed.Decls)
    (hacc : ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) :
    ∃ md_dt md_c,
      (cs.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc).getByKey g = some (.constructor md_dt md_c) := by
  induction cs generalizing acc with
  | nil => exact hacc
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih
    by_cases hbeq : (dt.name.pushNamespace c.nameHead == g) = true
    · refine ⟨newDt, c, ?_⟩
      have heq : (dt.name.pushNamespace c.nameHead) = g := LawfulBEq.eq_of_beq hbeq
      show ((acc.insert (dt.name.pushNamespace c.nameHead)
        (.constructor newDt c)).getByKey g) = some (.constructor newDt c)
      rw [heq]
      exact IndexMap.getByKey_insert_self _ _ _
    · have hne : (dt.name.pushNamespace c.nameHead == g) = false :=
        Bool.not_eq_true _ |>.mp hbeq
      obtain ⟨md_dt, md_c, hget⟩ := hacc
      refine ⟨md_dt, md_c, ?_⟩
      show ((acc.insert (dt.name.pushNamespace c.nameHead)
        (.constructor newDt c)).getByKey g) = some (.constructor md_dt md_c)
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hget

/-- A single step of `dtStep` on a `dt` with `dt.name ≠ g` preserves ctor-kind at `g`. -/
theorem dtStep_preserves_ctor_kind
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType)
    {g : Global}
    (hdt_ne : dt.name ≠ g)
    (hacc : ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) :
    ∃ md_dt md_c, (dtStep mono acc dt).getByKey g = some (.constructor md_dt md_c) := by
  unfold dtStep
  have hbeq_dt_name : (dt.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hdt_ne
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  have hacc_after_dtinsert : ∃ md_dt md_c,
      (acc.insert dt.name (Typed.Declaration.dataType newDt)).getByKey g =
        some (.constructor md_dt md_c) := by
    obtain ⟨md_dt, md_c, hget⟩ := hacc
    refine ⟨md_dt, md_c, ?_⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt_name]
    exact hget
  exact dtCtorFold_preserves_ctor_kind mono dt newDt rewrittenCtors _ hacc_after_dtinsert

/-- `dtStep` Array foldl preserves ctor-kind at `g` under `hDtNotKey`. -/
theorem dtStep_foldl_preserves_ctor_kind
    (mono : MonoMap) (newDataTypes : Array DataType) (init : Typed.Decls)
    {g : Global}
    (hinit : ∃ md_dt md_c, init.getByKey g = some (.constructor md_dt md_c))
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g) :
    ∃ md_dt md_c,
      (newDataTypes.foldl (dtStep mono) init).getByKey g =
        some (.constructor md_dt md_c) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) hinit
  intro i acc hinv
  have hdt_ne : (newDataTypes[i.val]'i.isLt).name ≠ g :=
    hDtNotKey _ (Array.getElem_mem _)
  exact dtStep_preserves_ctor_kind mono acc _ hdt_ne hinv

/-- A single step of `fnStep` on `f` with `f.name ≠ g` preserves ctor-kind at `g`. -/
theorem fnStep_preserves_ctor_kind
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global}
    (hfn_ne : f.name ≠ g)
    (hacc : ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) :
    ∃ md_dt md_c, (fnStep decls mono acc f).getByKey g = some (.constructor md_dt md_c) := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨md_dt, md_c, hget⟩ := hacc
  refine ⟨md_dt, md_c, ?_⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

/-- `fnStep` Array foldl preserves ctor-kind at `g` under `hFnNotKey`. -/
theorem fnStep_foldl_preserves_ctor_kind
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {g : Global}
    (hinit : ∃ md_dt md_c, init.getByKey g = some (.constructor md_dt md_c))
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ md_dt md_c,
      (newFunctions.foldl (fnStep decls mono) init).getByKey g =
        some (.constructor md_dt md_c) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) hinit
  intro i acc hinv
  have hfn_ne : (newFunctions[i.val]'i.isLt).name ≠ g :=
    hFnNotKey _ (Array.getElem_mem _)
  exact fnStep_preserves_ctor_kind decls mono acc _ hfn_ne hinv

/-- Phase A.2 main: `concretizeBuild` preserves ctor-kind from typed→monoDecls. -/
theorem concretizeBuild_preserves_ctor_kind_fwd
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hget : decls.getByKey g = some (.constructor td_dt td_c))
    (hdt_params : td_dt.params = [])
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ md_dt md_c,
      (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
        some (.constructor md_dt md_c) := by
  rw [concretizeBuild_eq]
  have h1 := fromSource_inserts_ctor_at_key decls mono hget hdt_params
  have h2 := dtStep_foldl_preserves_ctor_kind mono newDataTypes _ h1 hDtNotKey
  exact fnStep_foldl_preserves_ctor_kind decls mono newFunctions _ h2 hFnNotKey

/-! #### Reverse origin-classification helpers for `concretizeBuild`.

Used by `concretize_under_fullymono_preserves_ctor_kind_bwd` to dispatch the
4 sub-cases of `concretize_build_excludes_polymorphic`. -/

/-- `fnStep` foldl preserves ctor-kind at `g` even without `f.name ≠ g`
hypothesis: if every `f.name ≠ g`, value is unchanged; if some `f.name = g`,
last writer overrides to `.function`, contradicting the ctor witness in init. -/
theorem fnStep_foldl_no_g_preserves
    (decls : Typed.Decls) (mono : MonoMap) {g : Global} :
    ∀ (xs : List Typed.Function) (init : Typed.Decls),
      (∀ f ∈ xs, f.name ≠ g) →
      (xs.foldl (fnStep decls mono) init).getByKey g = init.getByKey g
  | [], _, _ => rfl
  | f :: rest, init, hne => by
    simp only [List.foldl_cons]
    have h1 : (fnStep decls mono init f).getByKey g = init.getByKey g := by
      unfold fnStep
      have hbeq : (f.name == g) = false := by
        rw [beq_eq_false_iff_ne]; exact hne f List.mem_cons_self
      exact IndexMap.getByKey_insert_of_beq_false _ _ hbeq
    have ih := fnStep_foldl_no_g_preserves decls mono rest (fnStep decls mono init f)
      (fun f' hf' => hne f' (List.mem_cons_of_mem _ hf'))
    rw [ih, h1]

/-- Helper: `dtStep` foldl preserves `getByKey g` when no dt and no
ctor-name in `xs` has key `g`. -/
theorem dtStep_foldl_no_g_preserves
    (mono : MonoMap) {g : Global} :
    ∀ (xs : List DataType) (init : Typed.Decls),
      (∀ dt ∈ xs, dt.name ≠ g) →
      (∀ dt ∈ xs, ∀ c ∈ dt.constructors,
        dt.name.pushNamespace c.nameHead ≠ g) →
      (xs.foldl (dtStep mono) init).getByKey g = init.getByKey g
  | [], _, _, _ => rfl
  | hd :: tl, init, hno_dt, hno_ctor => by
    simp only [List.foldl_cons]
    have hd_name_ne : hd.name ≠ g := hno_dt hd List.mem_cons_self
    have hd_ctor_ne : ∀ c ∈ hd.constructors,
        hd.name.pushNamespace c.nameHead ≠ g :=
      fun c hc => hno_ctor hd List.mem_cons_self c hc
    have ih := dtStep_foldl_no_g_preserves mono tl (dtStep mono init hd)
      (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt))
      (fun dt hdt c hc => hno_ctor dt (List.mem_cons_of_mem _ hdt) c hc)
    rw [ih]
    -- dtStep mono init hd preserves getByKey g.
    unfold dtStep
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := hd.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { hd with constructors := rewrittenCtors }
    have hbeq_dt_name : (hd.name == g) = false := by
      rw [beq_eq_false_iff_ne]; exact hd_name_ne
    have hctor_inner : ∀ (cs : List Constructor) (acc' : Typed.Decls),
        (∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g) →
        IndexMap.getByKey (cs.foldl (fun acc'' c =>
          acc''.insert (hd.name.pushNamespace c.nameHead)
            (.constructor newDt c)) acc') g = acc'.getByKey g := by
      intro cs
      induction cs with
      | nil => intros; rfl
      | cons c0 rest ih_cs =>
        intro acc' hne
        simp only [List.foldl_cons]
        have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
          hne c0 List.mem_cons_self
        have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
          rw [beq_eq_false_iff_ne]; exact hnc0
        rw [ih_cs _ (fun c'' hc'' => hne c'' (List.mem_cons_of_mem _ hc''))]
        exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
    have hd_rw_ctor_ne : ∀ c ∈ rewrittenCtors,
        hd.name.pushNamespace c.nameHead ≠ g := by
      intro c' hc'
      simp only [List.mem_map, rewrittenCtors] at hc'
      obtain ⟨c0, hc0, hc0_eq⟩ := hc'
      rw [← hc0_eq]
      exact hd_ctor_ne c0 hc0
    rw [hctor_inner _ _ hd_rw_ctor_ne]
    exact IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt_name

/-- Reverse origin: if `concretizeBuild` has `.constructor` at `g`, then either
source has `.constructor` at `g` with monomorphic params, or there is a
`newDataTypes` constructor whose mangled key matches `g` (origin 4). -/
theorem concretizeBuild_ctor_origin
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {cd_dt : DataType} {cd_c : Constructor}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.constructor cd_dt cd_c)) :
    (∃ src_dt src_c, decls.getByKey g = some (.constructor src_dt src_c) ∧
        src_dt.params = []) ∨
    (∃ dt ∈ newDataTypes, ∃ c ∈ dt.constructors,
        dt.name.pushNamespace c.nameHead = g) := by
  rw [concretizeBuild_eq] at hget
  rw [← Array.foldl_toList] at hget
  rw [show (newDataTypes.foldl (dtStep mono) (decls.pairs.foldl (srcStep decls mono) default))
      = (newDataTypes.toList.foldl (dtStep mono) (decls.pairs.toList.foldl (srcStep decls mono) default))
      from by rw [← Array.foldl_toList, ← Array.foldl_toList]] at hget
  -- Outer `fnStep` fold: every `fnStep` insert produces `.function`.
  -- If any f.name = g, the LAST writer in fnStep fold overrides to .function,
  -- contradicting the .ctor witness.
  by_cases hfn_ex : ∃ f ∈ newFunctions.toList, f.name = g
  · exfalso
    obtain ⟨f, hf_mem, hf_name⟩ := hfn_ex
    -- Split list at f, every fnStep insert produces .function at f.name = g.
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf_mem
    have hfold_decompose : (newFunctions.toList.foldl (fnStep decls mono)
        (newDataTypes.toList.foldl (dtStep mono)
          (decls.pairs.toList.foldl (srcStep decls mono) default))).getByKey g
        = ((post.foldl (fnStep decls mono))
            ((fnStep decls mono)
              (pre.foldl (fnStep decls mono)
                (newDataTypes.toList.foldl (dtStep mono)
                  (decls.pairs.toList.foldl (srcStep decls mono) default))) f)).getByKey g := by
      rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [hfold_decompose] at hget
    -- The mid value (after fnStep on f) has .function at g.
    have hmid_fn : ∃ newF, (fnStep decls mono
        (pre.foldl (fnStep decls mono)
          (newDataTypes.toList.foldl (dtStep mono)
            (decls.pairs.toList.foldl (srcStep decls mono) default))) f).getByKey g
        = some (.function newF) := by
      unfold fnStep
      rw [hf_name]
      exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
    -- Post fold preserves .function at g (every step is an insert; if f'.name = g
    -- it stays .function, otherwise unchanged).
    have hpost_pres : ∀ (xs : List Typed.Function) (acc : Typed.Decls),
        (∃ newF, acc.getByKey g = some (.function newF)) →
        ∃ newF, (xs.foldl (fnStep decls mono) acc).getByKey g
          = some (.function newF) := by
      intro xs
      induction xs with
      | nil => intro acc h; exact h
      | cons f' rest ih =>
        intro acc h
        simp only [List.foldl_cons]
        apply ih
        by_cases hbeq : (f'.name == g) = true
        · unfold fnStep
          rw [LawfulBEq.eq_of_beq hbeq]
          exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
        · have hne : (f'.name == g) = false := Bool.not_eq_true _ |>.mp hbeq
          obtain ⟨newF, hget⟩ := h
          unfold fnStep
          exact ⟨newF, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
    obtain ⟨newF, hnewF⟩ := hpost_pres post _ hmid_fn
    rw [hnewF] at hget
    cases hget
  · -- No fnStep wrote at g. Outer fold preserves getByKey g.
    have hfn_pres : (newFunctions.toList.foldl (fnStep decls mono)
        (newDataTypes.toList.foldl (dtStep mono)
          (decls.pairs.toList.foldl (srcStep decls mono) default))).getByKey g
        = (newDataTypes.toList.foldl (dtStep mono)
          (decls.pairs.toList.foldl (srcStep decls mono) default)).getByKey g := by
      apply fnStep_foldl_no_g_preserves
      intro f hf heq
      exact hfn_ex ⟨f, hf, heq⟩
    rw [hfn_pres] at hget
    -- Now examine dtStep fold. Case-split on origin 3/4 vs neither.
    by_cases hctor_ex : ∃ dt ∈ newDataTypes.toList,
        ∃ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead = g
    · obtain ⟨dt, hdt_mem, c, hc_mem, hc_eq⟩ := hctor_ex
      exact Or.inr ⟨dt, Array.mem_toList_iff.mp hdt_mem, c, hc_mem, hc_eq⟩
    · -- No origin 4. Sub-case on origin 3.
      by_cases hdt_ex : ∃ dt ∈ newDataTypes.toList, dt.name = g
      · -- Origin 3 only: the dtStep at dt.name = g overrides to .dataType.
        -- Then subsequent dtStep_foldl preserves up to LAST origin-3-writer.
        -- We need: last writer for dt.name = g produces .dataType, contradicting .ctor.
        exfalso
        -- Find the LAST dt in newDataTypes.toList with dt.name = g.
        have hlast_dt : ∀ (xs : List DataType) (init : Typed.Decls),
            (∀ dt ∈ xs, ∀ c ∈ dt.constructors,
              dt.name.pushNamespace c.nameHead ≠ g) →
            (∃ dt ∈ xs, dt.name = g) →
            ∃ ddt, (xs.foldl (dtStep mono) init).getByKey g = some (.dataType ddt) := by
          intro xs
          induction xs with
          | nil => intro _ _ ⟨_, hm, _⟩; cases hm
          | cons hd tl ih =>
            intro init hno_ctor hex
            simp only [List.foldl_cons]
            by_cases htl_ex : ∃ dt ∈ tl, dt.name = g
            · exact ih _ (fun dt hdt c hc => hno_ctor dt (List.mem_cons_of_mem _ hdt) c hc)
                htl_ex
            · obtain ⟨dt_ex, hdt_ex_mem, hdt_ex_eq⟩ := hex
              have hdt_is_hd : dt_ex = hd := by
                rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                · rfl
                · exact absurd ⟨dt_ex, htl_mem, hdt_ex_eq⟩ htl_ex
              subst hdt_is_hd
              -- All tl: dt.name ≠ g (so dtStep_foldl_no_g_preserves applies on tl).
              have hno_dt_tl : ∀ dt' ∈ tl, dt'.name ≠ g := by
                intro dt' hdt' heq
                exact htl_ex ⟨dt', hdt', heq⟩
              have hno_ctor_tl : ∀ dt' ∈ tl, ∀ c' ∈ dt'.constructors,
                  dt'.name.pushNamespace c'.nameHead ≠ g :=
                fun dt' hdt' c' hc' =>
                  hno_ctor dt' (List.mem_cons_of_mem _ hdt') c' hc'
              rw [dtStep_foldl_no_g_preserves mono tl _ hno_dt_tl hno_ctor_tl]
              -- dtStep init dt_ex with dt_ex.name = g: outer insert at dt_ex.name = g
              -- produces .dataType, then inner ctor fold inserts at
              -- dt_ex.name.pushNamespace c.nameHead. Since hno_ctor on dt_ex says
              -- those keys ≠ g, the final value at g is .dataType.
              unfold dtStep
              let emptySubst : Global → Option Typ := fun _ => none
              let rewrittenCtors := dt_ex.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
              let newDt : DataType := { dt_ex with constructors := rewrittenCtors }
              have hctor_inner : ∀ (cs : List Constructor) (acc' : Typed.Decls),
                  (∀ c ∈ cs, dt_ex.name.pushNamespace c.nameHead ≠ g) →
                  IndexMap.getByKey (cs.foldl (fun acc'' c =>
                    acc''.insert (dt_ex.name.pushNamespace c.nameHead)
                      (.constructor newDt c)) acc') g = acc'.getByKey g := by
                intro cs
                induction cs with
                | nil => intros; rfl
                | cons c0 rest ih_cs =>
                  intro acc' hne
                  simp only [List.foldl_cons]
                  have hnc0 : dt_ex.name.pushNamespace c0.nameHead ≠ g :=
                    hne c0 List.mem_cons_self
                  have hnc0_beq : (dt_ex.name.pushNamespace c0.nameHead == g) = false := by
                    rw [beq_eq_false_iff_ne]; exact hnc0
                  rw [ih_cs _ (fun c'' hc'' => hne c'' (List.mem_cons_of_mem _ hc''))]
                  exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
              have hctor_ne : ∀ c ∈ rewrittenCtors,
                  dt_ex.name.pushNamespace c.nameHead ≠ g := by
                intro c' hc'
                simp only [List.mem_map, rewrittenCtors] at hc'
                obtain ⟨c0, hc0, hc0_eq⟩ := hc'
                rw [← hc0_eq]
                exact hno_ctor dt_ex List.mem_cons_self c0 hc0
              show ∃ ddt, IndexMap.getByKey (rewrittenCtors.foldl
                  (fun acc'' c =>
                    acc''.insert (dt_ex.name.pushNamespace c.nameHead)
                      (.constructor newDt c))
                  (init.insert dt_ex.name (.dataType newDt))) g
                = some (.dataType ddt)
              rw [hctor_inner _ _ hctor_ne]
              refine ⟨newDt, ?_⟩
              rw [← hdt_ex_eq]
              exact IndexMap.getByKey_insert_self _ _ _
        have hno_ctor_all : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g := by
          intro dt hdt c hc heq
          exact hctor_ex ⟨dt, hdt, c, hc, heq⟩
        obtain ⟨ddt_v, hfinal⟩ := hlast_dt newDataTypes.toList _ hno_ctor_all hdt_ex
        rw [hfinal] at hget
        cases hget
      · -- Neither origin 3 nor origin 4: dtStep fold preserves getByKey g.
        have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
          intro dt hdt heq; exact hdt_ex ⟨dt, hdt, heq⟩
        have hno_ctor : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g := by
          intro dt hdt c hc heq; exact hctor_ex ⟨dt, hdt, c, hc, heq⟩
        rw [dtStep_foldl_no_g_preserves mono newDataTypes.toList _
          hno_dt_name hno_ctor] at hget
        -- Now hget says fromSource has .ctor at g. Trace back via srcStep fold.
        left
        have hsrc_shape : ∀ (pairs : List (Global × Typed.Declaration))
            (init : Typed.Decls),
            (∀ p ∈ pairs, decls.getByKey p.1 = some p.2) →
            (pairs.foldl (srcStep decls mono) init).getByKey g
              = some (.constructor cd_dt cd_c) →
            (∃ src_dt src_c, decls.getByKey g = some (.constructor src_dt src_c) ∧
              src_dt.params = []) ∨
            init.getByKey g = some (.constructor cd_dt cd_c) := by
          intro pairs
          induction pairs with
          | nil =>
            intro init _ hfold
            right; exact hfold
          | cons hd tl ih =>
            intro init hpairs hfold
            simp only [List.foldl_cons] at hfold
            have hpairs_tl : ∀ p ∈ tl, decls.getByKey p.1 = some p.2 :=
              fun p hp => hpairs p (List.mem_cons_of_mem _ hp)
            have hpairs_hd : decls.getByKey hd.1 = some hd.2 :=
              hpairs hd List.mem_cons_self
            rcases ih (srcStep decls mono init hd) hpairs_tl hfold with hleft | hmid
            · exact Or.inl hleft
            · obtain ⟨k, dd⟩ := hd
              simp only at hmid hpairs_hd
              cases dd with
              | function f =>
                by_cases hp : f.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    rw [hkeq] at hmid
                    rw [IndexMap.getByKey_insert_self] at hmid
                    cases hmid
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
              | dataType dt =>
                by_cases hp : dt.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    rw [hkeq] at hmid
                    rw [IndexMap.getByKey_insert_self] at hmid
                    cases hmid
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
              | constructor dt c =>
                by_cases hp : dt.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    refine Or.inl ⟨dt, c, ?_, ?_⟩
                    · rw [← hkeq]; exact hpairs_hd
                    · cases hdp : dt.params with
                      | nil => rfl
                      | cons _ _ => rw [hdp] at hp; cases hp
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
        have hdefault_none : (default : Typed.Decls).getByKey g = none := by
          unfold IndexMap.getByKey
          show ((default : Typed.Decls).indices[g]?).bind _ = none
          have : (default : Typed.Decls).indices[g]? = none := by
            show ((default : Std.HashMap Global Nat))[g]? = none
            exact Std.HashMap.getElem?_empty
          rw [this]; rfl
        have hpairs_hyp : ∀ p ∈ decls.pairs.toList, decls.getByKey p.1 = some p.2 := by
          intro p hp
          rcases p with ⟨a, b⟩
          exact IndexMap.getByKey_of_mem_pairs _ _ _ hp
        rcases hsrc_shape decls.pairs.toList default hpairs_hyp hget with hleft | hmid
        · exact hleft
        · rw [hdefault_none] at hmid
          cases hmid

/-! #### Explicit-structure variants of Phase A.2 ctor-kind preservation.

The existential `concretizeBuild_preserves_ctor_kind_fwd` is sufficient for the
A.2 main lemma but downstream proofs (e.g. structural matching against the
typed-side datatype/constructor shape) need to know the *specific* monoDt/monoC
produced by the empty-substitution rewrite. Mirrors the existential chain:
`srcStep_at_g_inserts_ctor` → `fromSource_inserts_ctor_at_key` →
`dtStep_foldl_preserves_ctor_kind` → `fnStep_foldl_preserves_ctor_kind` →
`concretizeBuild_preserves_ctor_kind_fwd`. -/

/-- Explicit-structure variant of `srcStep_at_g_inserts_ctor`: returns the
*specific* `(newDt, newCtor)` produced by the empty-substitution rewrite. -/
theorem srcStep_at_g_inserts_ctor_explicit
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hdt_params : td_dt.params = []) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c' =>
      { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { td_dt with constructors := rewrittenCtors }
    let newCtor : Constructor :=
      { td_c with argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
    (srcStep decls mono acc (g, .constructor td_dt td_c)).getByKey g =
      some (.constructor newDt newCtor) := by
  unfold srcStep
  have hp : td_dt.params.isEmpty = true := by rw [hdt_params]; rfl
  simp only [hp, if_true]
  exact IndexMap.getByKey_insert_self _ _ _

/-- Explicit-structure variant of `fromSource_inserts_ctor_at_key`: returns the
*specific* `(newDt, newCtor)` produced by the empty-substitution rewrite. The
proof mirrors the split-pattern proof in `fromSource_inserts_ctor_at_key`,
using `srcStep_at_g_inserts_ctor_explicit` at the unique occurrence. -/
theorem fromSource_inserts_ctor_at_key_explicit
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hget : decls.getByKey g = some (.constructor td_dt td_c))
    (hdt_params : td_dt.params = []) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c' =>
      { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { td_dt with constructors := rewrittenCtors }
    let newCtor : Constructor :=
      { td_c with argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
    (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
      some (.constructor newDt newCtor) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.constructor td_dt td_c) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.constructor td_dt td_c) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.constructor td_dt td_c) ∈ pre := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.constructor td_dt td_c) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp
        exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact srcStep_at_g_inserts_ctor_explicit decls mono
    (List.foldl (srcStep decls mono) default pre) hdt_params (g := g)
    (td_dt := td_dt) (td_c := td_c)

/-- `dtStep` foldl preserves an *exact* value at `g` under both
`hDtNotKey` (no outer dt-insert overrides) and `hCtorNotKey` (no inner
ctor-fold insert overrides). Reduces to `dtStep_foldl_no_g_preserves` (which
already has the correct hypothesis pattern). -/
theorem dtStep_foldl_preserves_explicit_at_g
    (mono : MonoMap) (newDataTypes : Array DataType)
    {g : Global} {dummy : Typed.Declaration}
    (init : Typed.Decls)
    (hinit : init.getByKey g = some dummy)
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g)
    (hCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g) :
    (newDataTypes.foldl (dtStep mono) init).getByKey g = some dummy := by
  rw [← Array.foldl_toList]
  have hno_dt_list : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
    intro dt hdt; exact hDtNotKey dt (Array.mem_toList_iff.mp hdt)
  have hno_ctor_list : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g := by
    intro dt hdt c hc; exact hCtorNotKey dt (Array.mem_toList_iff.mp hdt) c hc
  rw [dtStep_foldl_no_g_preserves mono newDataTypes.toList init hno_dt_list hno_ctor_list]
  exact hinit

/-- `fnStep` foldl preserves an *exact* value at `g` under `hFnNotKey`. -/
theorem fnStep_foldl_preserves_explicit_at_g
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    {g : Global} {dummy : Typed.Declaration}
    (init : Typed.Decls)
    (hinit : init.getByKey g = some dummy)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    (newFunctions.foldl (fnStep decls mono) init).getByKey g = some dummy := by
  rw [← Array.foldl_toList]
  have hno_fn_list : ∀ f ∈ newFunctions.toList, f.name ≠ g := by
    intro f hf; exact hFnNotKey f (Array.mem_toList_iff.mp hf)
  rw [fnStep_foldl_no_g_preserves decls mono newFunctions.toList init hno_fn_list]
  exact hinit

/-- Explicit-structure version of `concretizeBuild_preserves_ctor_kind_fwd`:
under the disjointness hypotheses + typed `.ctor` at g, mono `.ctor` at g
has SPECIFIC structure derivable from typed dt + ctor via empty-subst rewriteTyp. -/
theorem concretizeBuild_at_typed_ctor_explicit
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hget : typedDecls.getByKey g = some (.constructor td_dt td_c))
    (hdt_params : td_dt.params = [])
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g)
    (hCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let monoDt : DataType := { td_dt with constructors := rewrittenCtors }
    let monoC : Constructor :=
      { td_c with argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
    (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey g =
      some (.constructor monoDt monoC) := by
  rw [concretizeBuild_eq]
  have h1 := fromSource_inserts_ctor_at_key_explicit typedDecls mono hget hdt_params
  have h2 := dtStep_foldl_preserves_explicit_at_g mono newDataTypes _ h1
    hDtNotKey hCtorNotKey
  exact fnStep_foldl_preserves_explicit_at_g typedDecls mono newFunctions _ h2 hFnNotKey

-- `concretizeBuild_at_typed_function_explicit` defined later in this file
-- (after `fromSource_inserts_function_at_key_explicit` to satisfy forward-ref).

/-! #### Generalized explicit-structure under FullyMono + StrongNewNameShape.

`concretizeBuild_at_typed_ctor_explicit` requires `hCtorNotKey` (no origin 4
fires at `g`). Under `FullyMono` + `StrongNewNameShape`, origin 4 IS possible
(drain pushes a `newDt` for `td_dt` since `td_dt.params = []` ⇒ the args=#[]
self-instantiation is registered, and `withNewDts`'s ctor-fold inserts at
`td_dt.name.pushNamespace td_c.nameHead = g` overriding `fromSource`).

The KEY INSIGHT: under `StrongNewNameShape`, every `dt' ∈ drained.newDataTypes`
has constructors whose `nameHead`s match its source-typed origin's
constructors `nameHead`s positionally. For a `dt'` whose `pushNamespace`
matches `g`, injectivity of `pushNamespace` plus `Typed.Decls.CtorIsKey`
(which gives `g = td_dt.name.pushNamespace td_c.nameHead`) plus IndexMap key
uniqueness identify the source origin as `td_dt`. So the override at `g`
yields a `monoDt` whose `nameHead`-positional structure agrees with `td_dt`,
and a `monoC` with `nameHead = td_c.nameHead`. -/

/-- Structural predicate: a typed declaration at `g` is a `.constructor`
whose datatype `nameHead`-structure matches `td_dt` positionally and whose
constructor `nameHead` equals `td_c.nameHead`. The "general" target shape
satisfied by both `fromSource`'s Case-A output (rewritten `td_dt`) and
`withNewDts`'s Case-B override (rewritten `dt'` with `dt'`'s nameHeads
matching `td_dt`'s by `StrongNewNameShape`). -/
def MatchesTdShape (td_dt : DataType) (td_c : Constructor)
    (d : Typed.Declaration) : Prop :=
  ∃ md_dt md_c, d = .constructor md_dt md_c ∧
    md_dt.constructors.length = td_dt.constructors.length ∧
    md_c.nameHead = td_c.nameHead ∧
    (∀ i (hi : i < td_dt.constructors.length),
      ∃ hi' : i < md_dt.constructors.length,
      (md_dt.constructors[i]'hi').nameHead = (td_dt.constructors[i]'hi).nameHead) ∧
    -- Positional structural equality at td_c's position. At any position i
    -- where td_dt[i] = td_c, md_dt[i] structurally equals md_c.
    (∀ i (hi : i < td_dt.constructors.length),
      (td_dt.constructors[i]'hi) = td_c → ∃ hi' : i < md_dt.constructors.length,
      (md_dt.constructors[i]'hi') = md_c)

/-- The Case-A explicit value (rewritten `td_dt`, rewritten `td_c`) satisfies
`MatchesTdShape`. `rewriteTyp` only touches `argTypes`, leaving `nameHead`
intact, so length and positional `nameHead`s are preserved by the inner map. -/
theorem MatchesTdShape_caseA
    (mono : MonoMap) (td_dt : DataType) (td_c : Constructor) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c' =>
      { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
    let monoDt : DataType := { td_dt with constructors := rewrittenCtors }
    let monoC : Constructor :=
      { td_c with argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
    MatchesTdShape td_dt td_c (.constructor monoDt monoC) := by
  refine ⟨_, _, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [List.length_map]
  · intro i hi
    have hi' : i < td_dt.constructors.length := hi
    refine ⟨by simp only [List.length_map]; exact hi', ?_⟩
    simp only [List.getElem_map]
  · intro i hi heq
    refine ⟨by simp only [List.length_map]; exact hi, ?_⟩
    simp only [List.getElem_map]
    rw [heq]

/-- Inner ctor fold preserves `MatchesTdShape`. Either the inner insert at
`dt'.name.pushNamespace c.nameHead` doesn't hit `g` (preserving the inductive
value), or it does — at which point we must build a `MatchesTdShape` witness
for `(.constructor newDt' c)`. The build-witness function `hWit` is supplied
externally: it produces the `MatchesTdShape` package whenever a constructor's
pushed-key matches `g`. -/
theorem dtCtorFold_preserves_MatchesTdShape
    (dt' : DataType) (newDt' : DataType)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (cs : List Constructor)
    (hWit : ∀ c ∈ cs, dt'.name.pushNamespace c.nameHead = g →
      MatchesTdShape td_dt td_c (.constructor newDt' c))
    (acc : Typed.Decls)
    (hacc : ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) :
    ∃ d, (cs.foldl
        (fun acc'' c =>
          let cName := dt'.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt' c))
        acc).getByKey g = some d ∧ MatchesTdShape td_dt td_c d := by
  induction cs generalizing acc with
  | nil => exact hacc
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun c' hc' => hWit c' (List.mem_cons_of_mem _ hc'))
    by_cases hbeq : (dt'.name.pushNamespace c.nameHead == g) = true
    · have heq : dt'.name.pushNamespace c.nameHead = g := LawfulBEq.eq_of_beq hbeq
      refine ⟨.constructor newDt' c, ?_, hWit c List.mem_cons_self heq⟩
      show ((acc.insert (dt'.name.pushNamespace c.nameHead)
        (.constructor newDt' c)).getByKey g) = some (.constructor newDt' c)
      rw [heq]; exact IndexMap.getByKey_insert_self _ _ _
    · have hne : (dt'.name.pushNamespace c.nameHead == g) = false :=
        Bool.not_eq_true _ |>.mp hbeq
      obtain ⟨d, hget, hM⟩ := hacc
      refine ⟨d, ?_, hM⟩
      show ((acc.insert (dt'.name.pushNamespace c.nameHead)
        (.constructor newDt' c)).getByKey g) = some d
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget

/-- Single dtStep preserves `MatchesTdShape` at `g` under `dt'.name ≠ g`
(outer dt-insert doesn't touch g) plus a per-`dt'` post-rewrite witness
builder. The builder takes a (post-rewrite) constructor `c` whose pushed-key
matches `g` and produces the `MatchesTdShape` package. Caller phrases the
witness in terms of the rewritten `newDt'` (via the same let-binding here) so
it lines up with what the inner ctor-fold actually inserts. -/
theorem dtStep_preserves_MatchesTdShape
    (mono : MonoMap) (acc : Typed.Decls) (dt' : DataType)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hdt_ne : dt'.name ≠ g)
    (hWit : ∀ c ∈ dt'.constructors.map (fun c' =>
        { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) mono) }),
      dt'.name.pushNamespace c.nameHead = g →
      MatchesTdShape td_dt td_c (.constructor
        { dt' with constructors := dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) mono) }) } c))
    (hacc : ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) :
    ∃ d, (dtStep mono acc dt').getByKey g = some d ∧
      MatchesTdShape td_dt td_c d := by
  unfold dtStep
  have hbeq_dt_name : (dt'.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hdt_ne
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt'.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt' : DataType := { dt' with constructors := rewrittenCtors }
  -- After outer dt-insert: still has same shape at g.
  have hacc' : ∃ d, (acc.insert dt'.name (Typed.Declaration.dataType newDt')).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    obtain ⟨d, hget, hM⟩ := hacc
    refine ⟨d, ?_, hM⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt_name]; exact hget
  exact dtCtorFold_preserves_MatchesTdShape dt' newDt'
    rewrittenCtors hWit _ hacc'

/-- fnStep preserves `MatchesTdShape` at `g` under `f.name ≠ g`. -/
theorem fnStep_preserves_MatchesTdShape
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hfn_ne : f.name ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) :
    ∃ d, (fnStep decls mono acc f).getByKey g = some d ∧
      MatchesTdShape td_dt td_c d := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨d, hget, hM⟩ := hacc
  refine ⟨d, ?_, hM⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]; exact hget

/-- **Generalized explicit-structure**: under `FullyMono` + `StrongNewNameShape`
on drained, the `concretizeBuild` result at `g` (where `typedDecls` has
`.constructor td_dt td_c`) carries the same `nameHead`-positional structure as
`td_dt` + `td_c`, *even when origin 4 fires* (i.e., `withNewDts` overrides at
`g`).

Note on signature: the spec strategy needs the typed-side fact
`g = td_dt.name.pushNamespace td_c.nameHead` to bridge origin 4 back to
`td_dt`. This is supplied via the `Typed.Decls.CtorIsKey typedDecls`
hypothesis (a structural invariant of `checkAndSimplify`'s output, derivable
at the call site via `checkAndSimplify_preserves_ctorIsKey` / equivalent —
already proven for the `Typed.Decls.CtorIsKey` predicate downstream). -/
theorem concretizeBuild_at_typed_ctor_explicit_general
    (typedDecls : Typed.Decls) (drained : DrainState)
    (hStrong : drained.StrongNewNameShape typedDecls)
    (hfn_params_empty : ∀ k f,
      typedDecls.getByKey k = some (.function f) → f.params = [])
    (hdt_params_empty : ∀ k dt,
      typedDecls.getByKey k = some (.dataType dt) → dt.params = [])
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hg_pushed : g = td_dt.name.pushNamespace td_c.nameHead)
    (hget : typedDecls.getByKey g = some (.constructor td_dt td_c))
    (hdt_companion : typedDecls.getByKey td_dt.name = some (.dataType td_dt))
    (_hc_mem : td_c ∈ td_dt.constructors)
    (hdt_distinct : ∀ i j (hi : i < td_dt.constructors.length)
                              (hj : j < td_dt.constructors.length),
        (td_dt.constructors[i]'hi).nameHead = (td_dt.constructors[j]'hj).nameHead → i = j) :
    ∃ md_dt md_c,
      (concretizeBuild typedDecls drained.mono drained.newFunctions
          drained.newDataTypes).getByKey g = some (.constructor md_dt md_c) ∧
      md_dt.constructors.length = td_dt.constructors.length ∧
      md_c.nameHead = td_c.nameHead ∧
      (∀ i (hi : i < td_dt.constructors.length),
        ∃ hi' : i < md_dt.constructors.length,
        (md_dt.constructors[i]'hi').nameHead = (td_dt.constructors[i]'hi).nameHead) ∧
      -- Positional structural equality at td_c's position.
      (∀ i (hi : i < td_dt.constructors.length),
        (td_dt.constructors[i]'hi) = td_c → ∃ hi' : i < md_dt.constructors.length,
        (md_dt.constructors[i]'hi') = md_c) := by
  -- `td_dt.params = []` (FullyMono).
  have hdt_params : td_dt.params = [] := hdt_params_empty td_dt.name td_dt hdt_companion
  -- Disjointness for newDataTypes (outer dt-key ≠ g).
  have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ g := by
    intro dt' hmem heq
    obtain ⟨g_orig, args, dt_orig, hname, hget_orig, hargs_sz, _⟩ :=
      hStrong.2 dt' hmem
    have hdt_orig_params := hdt_params_empty g_orig dt_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : dt'.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    rw [hname_eq] at heq
    rw [heq] at hget_orig
    rw [hget] at hget_orig
    cases hget_orig
  -- Disjointness for newFunctions.
  have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
    intro f hmem heq
    obtain ⟨g_orig, args, f_orig, hname, hget_orig, hargs_sz⟩ :=
      hStrong.1 f hmem
    have hf_orig_params := hfn_params_empty g_orig f_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hf_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : f.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    rw [hname_eq] at heq
    rw [heq] at hget_orig
    rw [hget] at hget_orig
    cases hget_orig
  -- Per-`dt' ∈ drained.newDataTypes` post-rewrite witness builder. When dt'
  -- writes at g (i.e., `dt'.name.pushNamespace c.nameHead = g` for some c),
  -- the prefix injection forces `dt'.name = td_dt.name`, so by IndexMap key
  -- uniqueness `dt_orig = td_dt`, and `dt'.constructors.map nameHead =
  -- td_dt.constructors.map nameHead`. Combined with `c.nameHead = td_c.nameHead`
  -- (from suffix injection), the rewritten newDt' + c produces the desired
  -- `MatchesTdShape` package. When dt' does NOT write at g, the witness is
  -- vacuous (premise unsatisfiable).
  have hPerDtWit : ∀ dt' ∈ drained.newDataTypes,
      ∀ c ∈ dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }),
      dt'.name.pushNamespace c.nameHead = g →
        MatchesTdShape td_dt td_c (.constructor
          { dt' with constructors := dt'.constructors.map (fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }) } c) := by
    intro dt' hmem c hcmem hpush
    -- Suffix + prefix injectivity from pushed-key equality.
    rw [hg_pushed] at hpush
    -- hpush : dt'.name.pushNamespace c.nameHead = td_dt.name.pushNamespace td_c.nameHead
    have h_name_eq : Lean.Name.str dt'.name.toName c.nameHead =
        Lean.Name.str td_dt.name.toName td_c.nameHead := by
      have := hpush
      unfold Global.pushNamespace at this
      exact Global.mk.inj this
    have hToName : dt'.name.toName = td_dt.name.toName := by injection h_name_eq
    have hSuffix : c.nameHead = td_c.nameHead := by injection h_name_eq
    have hdt_name_eq : dt'.name = td_dt.name := by
      cases hd : dt'.name; cases hT : td_dt.name
      rw [hd, hT] at hToName
      simp only [Global.toName] at hToName
      congr 1
    -- StrongNewNameShape on dt': nameHead-positional correspondence to dt_orig.
    obtain ⟨g_orig, args, dt_orig, hname, hget_orig, hargs_sz, hctors_nh⟩ :=
      hStrong.2 dt' hmem
    have hdt_orig_params := hdt_params_empty g_orig dt_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hgorig_pre : dt'.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    have hgorig_eq : g_orig = td_dt.name := by rw [← hgorig_pre]; exact hdt_name_eq
    have hdt_orig_eq : dt_orig = td_dt := by
      rw [hgorig_eq] at hget_orig
      rw [hdt_companion] at hget_orig
      cases hget_orig; rfl
    rw [hdt_orig_eq] at hctors_nh
    -- hctors_nh : dt'.constructors.map nameHead = td_dt.constructors.map nameHead.
    have hLen : dt'.constructors.length = td_dt.constructors.length := by
      have := congrArg List.length hctors_nh
      simp [List.length_map] at this
      exact this
    -- Per-position nameHead correspondence between dt'.constructors and
    -- td_dt.constructors (used for both MatchesTdShape clauses below).
    have hPosNH : ∀ i (hi : i < td_dt.constructors.length),
        ∃ hi' : i < dt'.constructors.length,
        (dt'.constructors[i]'hi').nameHead = (td_dt.constructors[i]'hi).nameHead := by
      intro i hi
      have hi' : i < dt'.constructors.length := by rw [hLen]; exact hi
      refine ⟨hi', ?_⟩
      have hi_dt : i < (dt'.constructors.map (·.nameHead)).length := by
        rw [List.length_map]; exact hi'
      have hi_td : i < (td_dt.constructors.map (·.nameHead)).length := by
        rw [List.length_map]; exact hi
      have h_nh :
          (dt'.constructors.map (·.nameHead))[i]'hi_dt =
          (td_dt.constructors.map (·.nameHead))[i]'hi_td := by
        congr 1
      rw [List.getElem_map, List.getElem_map] at h_nh
      exact h_nh
    -- Now build MatchesTdShape for `(.constructor newDt' c)` where `newDt'` =
    -- `{ dt' with constructors := rewrittenCtors }` and rewrittenCtors length =
    -- dt'.constructors.length.
    refine ⟨_, c, rfl, ?_, hSuffix, ?_, ?_⟩
    · simp only [List.length_map]; exact hLen
    · intro i hi
      have hi' : i < dt'.constructors.length := by rw [hLen]; exact hi
      refine ⟨by simp only [List.length_map]; exact hi', ?_⟩
      simp only [List.getElem_map]
      exact (hPosNH i hi).2
    · -- Positional structural equality at td_c's position.
      -- Strategy: `c ∈ rewrittenCtors`, so `c = rewrittenCtors[k]` for some k.
      -- `c.nameHead = td_c.nameHead = td_dt[i].nameHead` (via heq).
      -- `rewrittenCtors[k].nameHead = dt'[k].nameHead = td_dt[k].nameHead`
      -- (via hctors_nh). By distinctness on td_dt nameHeads, k = i.
      -- So `rewrittenCtors[i] = c`, hence `newDt'.constructors[i] = c = md_c`.
      intro i hi heq
      have hi'_dt' : i < dt'.constructors.length := by rw [hLen]; exact hi
      have hi'_new : i < (dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none)
            drained.mono) })).length := by simp only [List.length_map]; exact hi'_dt'
      refine ⟨hi'_new, ?_⟩
      -- Identify k from c ∈ rewrittenCtors.
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hcmem
      have hk_lt_dt' : k < dt'.constructors.length := by
        simp only [List.length_map] at hk_lt; exact hk_lt
      -- c.nameHead = rewrittenCtors[k].nameHead = dt'.constructors[k].nameHead.
      have hk_nh_c : c.nameHead = (dt'.constructors[k]'hk_lt_dt').nameHead := by
        rw [← hk_eq]; simp only [List.getElem_map]
      -- dt'.constructors[k].nameHead = td_dt.constructors[k].nameHead via hctors_nh.
      have hk_lt_td : k < td_dt.constructors.length := by rw [← hLen]; exact hk_lt_dt'
      have hk_nh_td : (dt'.constructors[k]'hk_lt_dt').nameHead =
          (td_dt.constructors[k]'hk_lt_td).nameHead := (hPosNH k hk_lt_td).2
      -- Combine: c.nameHead = td_dt[k].nameHead. And c.nameHead = td_c.nameHead.
      -- And td_dt[i] = td_c (by heq) so td_dt[i].nameHead = td_c.nameHead.
      have hk_eq_i : k = i := by
        apply hdt_distinct k i hk_lt_td hi
        -- Goal: td_dt[k].nameHead = td_dt[i].nameHead.
        rw [← hk_nh_td, ← hk_nh_c, hSuffix, ← heq]
      subst hk_eq_i
      -- Now newDt'.constructors[i] = rewrittenCtors[i] = c.
      have hgoal : (dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none)
            drained.mono) }))[k]'hk_lt = c := hk_eq
      exact hgoal
  -- Compose: starting from fromSource's Case-A explicit value, dtStep fold
  -- preserves `MatchesTdShape` (per-dt' via hPerDtWit), then fnStep fold
  -- preserves it (under hFnNotKey).
  rw [concretizeBuild_eq]
  -- Step 1: fromSource produces Case-A `MatchesTdShape`.
  have h0 : ∃ d, (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    have h := fromSource_inserts_ctor_at_key_explicit typedDecls drained.mono hget hdt_params
    refine ⟨_, h, ?_⟩
    exact MatchesTdShape_caseA drained.mono td_dt td_c
  -- Step 2: dtStep foldl preserves it.
  have h1 : ∃ d, (drained.newDataTypes.foldl (dtStep drained.mono)
      (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default)).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) =>
        ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) h0
    intro i acc hinv
    have hdt_mem : drained.newDataTypes[i.val]'i.isLt ∈ drained.newDataTypes :=
      Array.getElem_mem _
    have hdt_ne := hDtNotKey _ hdt_mem
    have hWit_i := hPerDtWit _ hdt_mem
    exact dtStep_preserves_MatchesTdShape drained.mono acc _ hdt_ne hWit_i hinv
  -- Step 3: fnStep foldl preserves it.
  have h2 : ∃ d, (drained.newFunctions.foldl (fnStep typedDecls drained.mono)
      (drained.newDataTypes.foldl (dtStep drained.mono)
        (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default))).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) =>
        ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) h1
    intro i acc hinv
    have hf_mem : drained.newFunctions[i.val]'i.isLt ∈ drained.newFunctions :=
      Array.getElem_mem _
    have hf_ne := hFnNotKey _ hf_mem
    exact fnStep_preserves_MatchesTdShape typedDecls drained.mono acc _ hf_ne hinv
  -- Unpack the final `MatchesTdShape` into the goal's existential structure.
  obtain ⟨d, hd, ⟨md_dt, md_c, hd_eq, hLen, hNH, hPos, hStruct⟩⟩ := h2
  rw [hd_eq] at hd
  exact ⟨md_dt, md_c, hd, hLen, hNH, hPos, hStruct⟩

/-! #### Phase A.2 — typed↔monoDecls dataType kind correspondence (forward).

Mirrors the ctor variant. For source/typed `.dataType` at `g`:
* `fromSource` fold processes the unique `(g, .dataType td_dt)` pair under
  `td_dt.params = []`, inserting `.dataType` at `g`.
* `withNewDts` fold inserts `.dataType` at `dt'.name` and `.constructor` at
  each `dt'.name.pushNamespace c.nameHead`. The `dt'.name = g` case re-inserts
  `.dataType` (kind preserved); under `hDtCtorNotKey`, no inner ctor key
  equals `g`.
* `newFunctions` fold inserts `.function` at `f.name`. Under `hFnNotKey`,
  no insertion at `g`.
-/

/-- A single step of `srcStep` on the target `(g, .dataType td_dt)` pair
under `td_dt.params = []` produces a `.dataType` entry at `g`. -/
theorem srcStep_at_g_inserts_dataType
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {td_dt : DataType}
    (hdt_params : td_dt.params = []) :
    ∃ md_dt,
      (srcStep decls mono acc (g, .dataType td_dt)).getByKey g =
        some (.dataType md_dt) := by
  unfold srcStep
  have hp : td_dt.params.isEmpty = true := by rw [hdt_params]; rfl
  let emptySubst : Global → Option Typ := fun _ => none
  let newDt : DataType := { td_dt with
    constructors := td_dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) } }
  simp only [hp, if_true]
  exact ⟨newDt, IndexMap.getByKey_insert_self _ _ _⟩

/-- `fromSource` fold inserts `.dataType` at `g` when source has `.dataType`
at `g`. -/
theorem fromSource_inserts_dataType_at_key
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {td_dt : DataType}
    (hget : decls.getByKey g = some (.dataType td_dt))
    (hdt_params : td_dt.params = []) :
    ∃ md_dt,
      (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
        some (.dataType md_dt) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.dataType td_dt) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.dataType td_dt) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.dataType td_dt) ∈ pre := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.dataType td_dt) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp
        exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  obtain ⟨md_dt, hstep⟩ := srcStep_at_g_inserts_dataType decls mono
    (List.foldl (srcStep decls mono) default pre) hdt_params (g := g) (td_dt := td_dt)
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact ⟨md_dt, hstep⟩

/-- Explicit-structure variant of `srcStep_at_g_inserts_dataType`: returns
the *specific* `monoDt` produced by the empty-substitution rewrite. -/
theorem srcStep_at_g_inserts_dataType_explicit
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {td_dt : DataType}
    (hdt_params : td_dt.params = []) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let monoDt : DataType := { td_dt with constructors := rewrittenCtors }
    (srcStep decls mono acc (g, .dataType td_dt)).getByKey g =
      some (.dataType monoDt) := by
  unfold srcStep
  have hp : td_dt.params.isEmpty = true := by rw [hdt_params]; rfl
  simp only [hp, if_true]
  exact IndexMap.getByKey_insert_self _ _ _

/-- Explicit-structure variant of `fromSource_inserts_dataType_at_key`: returns
the *specific* `monoDt` produced by the empty-substitution rewrite. Mirrors
`fromSource_inserts_ctor_at_key_explicit`. -/
theorem fromSource_inserts_dataType_at_key_explicit
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {td_dt : DataType}
    (hget : decls.getByKey g = some (.dataType td_dt))
    (hdt_params : td_dt.params = []) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let monoDt : DataType := { td_dt with constructors := rewrittenCtors }
    (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
      some (.dataType monoDt) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.dataType td_dt) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.dataType td_dt) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.dataType td_dt) ∈ pre := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]; simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.dataType td_dt) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]; simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact srcStep_at_g_inserts_dataType_explicit decls mono
    (List.foldl (srcStep decls mono) default pre) hdt_params (g := g) (td_dt := td_dt)

/-- Explicit-structure variant of `concretizeBuild_preserves_dataType_kind_fwd`:
under disjointness hypotheses + typed `.dataType` at g, mono `.dataType` at g
has SPECIFIC structure derivable from typed dt via empty-subst rewriteTyp. -/
theorem concretizeBuild_at_typed_dataType_explicit
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {td_dt : DataType}
    (hget : typedDecls.getByKey g = some (.dataType td_dt))
    (hdt_params : td_dt.params = [])
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g)
    (hCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let monoDt : DataType := { td_dt with constructors := rewrittenCtors }
    (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey g =
      some (.dataType monoDt) := by
  rw [concretizeBuild_eq]
  have h1 := fromSource_inserts_dataType_at_key_explicit typedDecls mono hget hdt_params
  have h2 := dtStep_foldl_preserves_explicit_at_g mono newDataTypes _ h1
    hDtNotKey hCtorNotKey
  exact fnStep_foldl_preserves_explicit_at_g typedDecls mono newFunctions _ h2 hFnNotKey

/-- A single step of `srcStep` on the target `(g, .function tf)` pair under
`tf.params = []` produces a `.function` entry at `g`. -/
theorem srcStep_at_g_inserts_function
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {tf : Typed.Function}
    (hf_params : tf.params = []) :
    ∃ md_f,
      (srcStep decls mono acc (g, .function tf)).getByKey g =
        some (.function md_f) := by
  unfold srcStep
  have hp : tf.params.isEmpty = true := by rw [hf_params]; rfl
  let emptySubst : Global → Option Typ := fun _ => none
  let newF : Typed.Function :=
    { tf with
      inputs := tf.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
      output := rewriteTyp emptySubst mono tf.output,
      body := rewriteTypedTerm decls emptySubst mono tf.body }
  simp only [hp, if_true]
  exact ⟨newF, IndexMap.getByKey_insert_self _ _ _⟩

/-- Explicit-structure variant of `srcStep_at_g_inserts_function`: returns the
*specific* `monoF` produced by the empty-substitution rewrite. -/
theorem srcStep_at_g_inserts_function_explicit
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {tf : Typed.Function}
    (hf_params : tf.params = []) :
    let emptySubst : Global → Option Typ := fun _ => none
    let monoF : Typed.Function :=
      { tf with
        inputs := tf.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono tf.output,
        body := rewriteTypedTerm decls emptySubst mono tf.body }
    (srcStep decls mono acc (g, .function tf)).getByKey g =
      some (.function monoF) := by
  unfold srcStep
  have hp : tf.params.isEmpty = true := by rw [hf_params]; rfl
  simp only [hp, if_true]
  exact IndexMap.getByKey_insert_self _ _ _

/-- Strengthened `srcStep_at_g_inserts_function`: also returns
`md_f.inputs.map (·.1) = tf.inputs.map (·.1)`. -/
theorem srcStep_at_g_inserts_function_inputs
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {tf : Typed.Function}
    (hf_params : tf.params = []) :
    ∃ md_f,
      (srcStep decls mono acc (g, .function tf)).getByKey g =
        some (.function md_f) ∧ md_f.inputs.map (·.1) = tf.inputs.map (·.1) := by
  unfold srcStep
  have hp : tf.params.isEmpty = true := by rw [hf_params]; rfl
  let emptySubst : Global → Option Typ := fun _ => none
  let newF : Typed.Function :=
    { tf with
      inputs := tf.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
      output := rewriteTyp emptySubst mono tf.output,
      body := rewriteTypedTerm decls emptySubst mono tf.body }
  simp only [hp, if_true]
  refine ⟨newF, IndexMap.getByKey_insert_self _ _ _, ?_⟩
  -- newF.inputs = tf.inputs.map (l, t) ↦ (l, rewriteTyp emptySubst mono t).
  -- Goal: that map's `(·.1)` projection = tf.inputs.map (·.1).
  show (tf.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)).map (·.1)
      = tf.inputs.map (·.1)
  rw [List.map_map]
  apply List.map_congr_left
  intro lt _; rfl

/-- Strengthened `fromSource_inserts_function_at_key`: returns a `.function`
entry at `g` whose inputs labels match `tf.inputs`. -/
theorem fromSource_inserts_function_at_key_inputs
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {tf : Typed.Function}
    (hget : decls.getByKey g = some (.function tf))
    (hf_params : tf.params = []) :
    ∃ md_f,
      (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
        some (.function md_f) ∧ md_f.inputs.map (·.1) = tf.inputs.map (·.1) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.function tf) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.function tf) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.function tf) ∈ pre := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.function tf) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp
        exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  obtain ⟨md_f, hstep, hin⟩ := srcStep_at_g_inserts_function_inputs decls mono
    (List.foldl (srcStep decls mono) default pre) hf_params (g := g) (tf := tf)
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact ⟨md_f, hstep, hin⟩

/-- `fromSource` fold inserts `.function` at `g` when typed has `.function tf`
at `g` with `tf.params = []`. -/
theorem fromSource_inserts_function_at_key
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {tf : Typed.Function}
    (hget : decls.getByKey g = some (.function tf))
    (hf_params : tf.params = []) :
    ∃ md_f,
      (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
        some (.function md_f) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.function tf) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.function tf) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.function tf) ∈ pre := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.function tf) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp
        exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  obtain ⟨md_f, hstep⟩ := srcStep_at_g_inserts_function decls mono
    (List.foldl (srcStep decls mono) default pre) hf_params (g := g) (tf := tf)
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact ⟨md_f, hstep⟩

/-- Explicit-structure variant of `fromSource_inserts_function_at_key`: returns
the *specific* `monoF` produced by the empty-substitution rewrite. Mirrors
`fromSource_inserts_ctor_at_key_explicit`. -/
theorem fromSource_inserts_function_at_key_explicit
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {tf : Typed.Function}
    (hget : decls.getByKey g = some (.function tf))
    (hf_params : tf.params = []) :
    let emptySubst : Global → Option Typ := fun _ => none
    let monoF : Typed.Function :=
      { tf with
        inputs := tf.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono tf.output,
        body := rewriteTypedTerm decls emptySubst mono tf.body }
    (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
      some (.function monoF) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.function tf) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.function tf) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.function tf) ∈ pre := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.function tf) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp
        exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.function tf) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.function tf) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact srcStep_at_g_inserts_function_explicit decls mono
    (List.foldl (srcStep decls mono) default pre) hf_params (g := g) (tf := tf)

/-- Explicit-structure variant of fn at a typed source-fn key. Mirrors
`concretizeBuild_at_typed_ctor_explicit`. Under disjointness with newDts/newFns,
the `concretizeBuild` output at `g` is the explicit `.function monoF` produced
by `srcStep`'s rewrite of `tf`. -/
theorem concretizeBuild_at_typed_function_explicit
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {tf : Typed.Function}
    (hget : typedDecls.getByKey g = some (.function tf))
    (hf_params : tf.params = [])
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g)
    (hCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g) :
    let emptySubst : Global → Option Typ := fun _ => none
    let monoF : Typed.Function :=
      { tf with
        inputs := tf.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono tf.output,
        body := rewriteTypedTerm typedDecls emptySubst mono tf.body }
    (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey g =
      some (.function monoF) := by
  rw [concretizeBuild_eq]
  have h1 := fromSource_inserts_function_at_key_explicit typedDecls mono hget hf_params
  have h2 := dtStep_foldl_preserves_explicit_at_g mono newDataTypes _ h1
    hDtNotKey hCtorNotKey
  exact fnStep_foldl_preserves_explicit_at_g typedDecls mono newFunctions _ h2 hFnNotKey

/-- Inner ctor-fold preserves dataType-kind at `g` when no inner ctor key
equals `g`. -/
theorem dtCtorFold_preserves_dataType_kind
    (mono : MonoMap) (dt : DataType) (newDt : DataType)
    {g : Global} :
    ∀ (cs : List Constructor) (acc : Typed.Decls)
      (_hCtorNotKey : ∀ c ∈ cs, dt.name.pushNamespace c.nameHead ≠ g)
      (_hacc : ∃ md_dt, acc.getByKey g = some (.dataType md_dt)),
    ∃ md_dt,
      (cs.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc).getByKey g = some (.dataType md_dt)
  | [], _, _, hacc => hacc
  | c :: rest, acc, hCtorNotKey, hacc => by
    simp only [List.foldl_cons]
    have hne : (dt.name.pushNamespace c.nameHead == g) = false := by
      rw [beq_eq_false_iff_ne]; exact hCtorNotKey c List.mem_cons_self
    have hacc' : ∃ md_dt,
        (acc.insert (dt.name.pushNamespace c.nameHead)
          (.constructor newDt c)).getByKey g = some (.dataType md_dt) := by
      obtain ⟨md_dt, hget⟩ := hacc
      refine ⟨md_dt, ?_⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hget
    exact dtCtorFold_preserves_dataType_kind mono dt newDt rest _
      (fun c' hc' => hCtorNotKey c' (List.mem_cons_of_mem _ hc')) hacc'

/-- A single step of `dtStep` preserves dataType-kind at `g` when no inner
ctor key equals `g`. The `dt.name = g` case re-inserts `.dataType`. -/
theorem dtStep_preserves_dataType_kind
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType)
    {g : Global}
    (hCtorNotKey : ∀ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead ≠ g)
    (hacc : ∃ md_dt, acc.getByKey g = some (.dataType md_dt)) :
    ∃ md_dt, (dtStep mono acc dt).getByKey g = some (.dataType md_dt) := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- After the dt.name insert, kind at g is `.dataType` (either we re-insert
  -- newDt at g, or the insert is at a different key and acc's value is preserved).
  have hacc_after_dtinsert : ∃ md_dt,
      (acc.insert dt.name (Typed.Declaration.dataType newDt)).getByKey g =
        some (.dataType md_dt) := by
    by_cases hbeq : (dt.name == g) = true
    · refine ⟨newDt, ?_⟩
      have heq : dt.name = g := LawfulBEq.eq_of_beq hbeq
      rw [heq]
      exact IndexMap.getByKey_insert_self _ _ _
    · have hne : (dt.name == g) = false := Bool.not_eq_true _ |>.mp hbeq
      obtain ⟨md_dt, hget⟩ := hacc
      refine ⟨md_dt, ?_⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hget
  -- Inner ctor fold: rewrittenCtors share nameHeads with dt.constructors.
  have hCtorNotKey' : ∀ c ∈ rewrittenCtors,
      dt.name.pushNamespace c.nameHead ≠ g := by
    intro c hc
    -- c ∈ rewrittenCtors = dt.constructors.map (fun c' => { c' with argTypes := ... }).
    have hmap : c ∈ dt.constructors.map (fun c' =>
        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }) := hc
    obtain ⟨c_orig, hc_orig_mem, hc_orig_eq⟩ := List.mem_map.mp hmap
    have hnh : c.nameHead = c_orig.nameHead := by rw [← hc_orig_eq]
    rw [hnh]
    exact hCtorNotKey c_orig hc_orig_mem
  exact dtCtorFold_preserves_dataType_kind mono dt newDt rewrittenCtors _ hCtorNotKey' hacc_after_dtinsert

/-- `dtStep` Array foldl preserves dataType-kind at `g` under
`hDtCtorNotKey`. -/
theorem dtStep_foldl_preserves_dataType_kind
    (mono : MonoMap) (newDataTypes : Array DataType) (init : Typed.Decls)
    {g : Global}
    (hinit : ∃ md_dt, init.getByKey g = some (.dataType md_dt))
    (hDtCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g) :
    ∃ md_dt,
      (newDataTypes.foldl (dtStep mono) init).getByKey g =
        some (.dataType md_dt) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_dt, acc.getByKey g = some (.dataType md_dt)) hinit
  intro i acc hinv
  have hCtorNotKey : ∀ c ∈ (newDataTypes[i.val]'i.isLt).constructors,
      (newDataTypes[i.val]'i.isLt).name.pushNamespace c.nameHead ≠ g :=
    hDtCtorNotKey _ (Array.getElem_mem _)
  exact dtStep_preserves_dataType_kind mono acc _ hCtorNotKey hinv

/-- A single step of `fnStep` on `f` with `f.name ≠ g` preserves
dataType-kind at `g`. -/
theorem fnStep_preserves_dataType_kind
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global}
    (hfn_ne : f.name ≠ g)
    (hacc : ∃ md_dt, acc.getByKey g = some (.dataType md_dt)) :
    ∃ md_dt, (fnStep decls mono acc f).getByKey g = some (.dataType md_dt) := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨md_dt, hget⟩ := hacc
  refine ⟨md_dt, ?_⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

/-- `fnStep` Array foldl preserves dataType-kind at `g` under `hFnNotKey`. -/
theorem fnStep_foldl_preserves_dataType_kind
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {g : Global}
    (hinit : ∃ md_dt, init.getByKey g = some (.dataType md_dt))
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ md_dt,
      (newFunctions.foldl (fnStep decls mono) init).getByKey g =
        some (.dataType md_dt) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_dt, acc.getByKey g = some (.dataType md_dt)) hinit
  intro i acc hinv
  have hfn_ne : (newFunctions[i.val]'i.isLt).name ≠ g :=
    hFnNotKey _ (Array.getElem_mem _)
  exact fnStep_preserves_dataType_kind decls mono acc _ hfn_ne hinv

/-- Phase A.2 main: `concretizeBuild` preserves dataType-kind from
typed→monoDecls. -/
theorem concretizeBuild_preserves_dataType_kind_fwd
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {td_dt : DataType}
    (hget : decls.getByKey g = some (.dataType td_dt))
    (hdt_params : td_dt.params = [])
    (hDtCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ md_dt,
      (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
        some (.dataType md_dt) := by
  rw [concretizeBuild_eq]
  have h1 := fromSource_inserts_dataType_at_key decls mono hget hdt_params
  have h2 := dtStep_foldl_preserves_dataType_kind mono newDataTypes _ h1 hDtCtorNotKey
  exact fnStep_foldl_preserves_dataType_kind decls mono newFunctions _ h2 hFnNotKey

/-! #### Phase 0 — `concretizeBuild` lifts every newDt/newFn name to a
mono-decl entry. Used by `concretize_produces_mono_correspondence` to discharge
`dt_lifts` / `fn_lifts` / `has_new_decl`'s cd-existence prerequisite. -/

/-- A single step of `dtStep` on `dt` always inserts `.dataType` at `dt.name`
(the inner ctor fold inserts at `dt.name.pushNamespace c.nameHead ≠ dt.name`,
so the `.dataType` at `dt.name` is never disturbed). -/
theorem dtStep_inserts_dataType_at_self
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType) :
    ∃ md_dt, (dtStep mono acc dt).getByKey dt.name = some (.dataType md_dt) := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- After the dt.name insert, kind at dt.name is `.dataType newDt`.
  -- The inner ctor fold inserts only at keys `dt.name.pushNamespace c.nameHead`,
  -- which differ from `dt.name` (Global.ne_pushNamespace).
  have hpreserve :
      ∀ (cs : List Constructor) (acc' : Typed.Decls)
        (_h : ∃ md, acc'.getByKey dt.name = some (.dataType md)),
        ∃ md, IndexMap.getByKey
          (cs.foldl (fun acc'' c =>
            acc''.insert (dt.name.pushNamespace c.nameHead)
              (.constructor newDt c)) acc') dt.name = some (.dataType md) := by
    intro cs
    induction cs with
    | nil => intro acc' h; exact h
    | cons c rest ih =>
      intro acc' h
      simp only [List.foldl_cons]
      apply ih
      have hne : dt.name ≠ dt.name.pushNamespace c.nameHead :=
        Global.ne_pushNamespace dt.name c.nameHead
      have hbeq : (dt.name.pushNamespace c.nameHead == dt.name) = false := by
        rw [beq_eq_false_iff_ne]; exact (Ne.symm hne)
      obtain ⟨md, hmd⟩ := h
      refine ⟨md, ?_⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
      exact hmd
  apply hpreserve
  refine ⟨newDt, ?_⟩
  exact IndexMap.getByKey_insert_self _ _ _

/-- `dtStep` foldl over a list, when `dt` ∈ list and no other step's ctor-key
collides with `dt.name`, ends with `.dataType` at `dt.name`. -/
theorem dtStep_foldl_list_inserts_at_dt_name
    (mono : MonoMap) {dt : DataType} :
    ∀ (xs : List DataType) (init : Typed.Decls)
      (_hmem : dt ∈ xs)
      (_hCtorNotKey : ∀ dt' ∈ xs, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ dt.name),
    ∃ md_dt, (xs.foldl (dtStep mono) init).getByKey dt.name =
      some (.dataType md_dt)
  | [], _, hmem, _ => by cases hmem
  | hd :: rest, init, hmem, hCtorNotKey => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · -- dt = hd. Apply dtStep_inserts_dataType_at_self at hd, then preserve over rest.
      subst hmem_hd
      have h1 := dtStep_inserts_dataType_at_self mono init dt
      -- Continue over rest; need rest's ctor-keys don't equal dt.name.
      have hrest_ctor : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := by
        intro dt' hdt' c hc
        exact hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      clear hCtorNotKey
      -- Convert `rest.foldl ...` to Array form to leverage `dtStep_foldl_preserves_dataType_kind`.
      have heq : rest.foldl (dtStep mono) (dtStep mono init dt)
          = rest.toArray.foldl (dtStep mono) (dtStep mono init dt) := by
        rw [Array.foldl_toList]
      rw [heq]
      apply dtStep_foldl_preserves_dataType_kind mono rest.toArray _ h1
      intro dt' hdt' c hc
      have hdt'_list : dt' ∈ rest := by
        have := Array.mem_toList_iff.mpr hdt'
        simpa using this
      exact hrest_ctor dt' hdt'_list c hc
    · -- dt ∈ rest. Use IH on rest; prepend dtStep mono init hd.
      have hrest_ctor : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := by
        intro dt' hdt' c hc
        exact hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      exact dtStep_foldl_list_inserts_at_dt_name mono rest
        (dtStep mono init hd) hmem_rest hrest_ctor

/-- `dtStep` Array foldl inserts `.dataType` at `dt.name` for every `dt ∈
newDataTypes`, under the disjointness `hDtCtorNotKey`. -/
theorem dtStep_foldl_inserts_at_dt_name
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name) :
    ∃ md_dt,
      (newDataTypes.foldl (dtStep mono) init).getByKey dt.name =
        some (.dataType md_dt) := by
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  have hCtor' : ∀ dt' ∈ newDataTypes.toList, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name := by
    intro dt' hdt'; exact hDtCtorNotKey dt' (Array.mem_toList_iff.mp hdt')
  exact dtStep_foldl_list_inserts_at_dt_name mono newDataTypes.toList init hmem' hCtor'

/-- A single `fnStep` step preserves `.function`-kind at any key `g` (regardless
of `f.name = g` or not). When `f.name = g`, the insert overrides to a fresh
`.function`; when `f.name ≠ g`, the insert preserves the prior value. -/
theorem fnStep_preserves_function_kind
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global}
    (hacc : ∃ md_f, acc.getByKey g = some (.function md_f)) :
    ∃ md_f, (fnStep decls mono acc f).getByKey g = some (.function md_f) := by
  unfold fnStep
  by_cases hbeq : (f.name == g) = true
  · let emptySubst : Global → Option Typ := fun _ => none
    let newF : Typed.Function :=
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body }
    refine ⟨newF, ?_⟩
    have heq : f.name = g := LawfulBEq.eq_of_beq hbeq
    rw [← heq]
    exact IndexMap.getByKey_insert_self _ _ _
  · have hbeq' : (f.name == g) = false := Bool.not_eq_true _ |>.mp hbeq
    obtain ⟨md_f, hget⟩ := hacc
    refine ⟨md_f, ?_⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq']
    exact hget

/-- `fnStep` foldl preserves `.function`-kind at any key (no disjointness
needed: `fnStep` always inserts `.function`, so re-inserting at the same key
doesn't change the kind). -/
theorem fnStep_foldl_preserves_function_kind
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {g : Global}
    (hinit : ∃ md_f, init.getByKey g = some (.function md_f)) :
    ∃ md_f, (newFunctions.foldl (fnStep decls mono) init).getByKey g =
      some (.function md_f) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_f, acc.getByKey g = some (.function md_f)) hinit
  intro i acc hinv
  exact fnStep_preserves_function_kind decls mono acc _ hinv

/-- Strengthened single-step `fnStep`: when every `f' ∈ newFunctions` with
`f'.name = g` has `f'.inputs.map (·.1) = expected`, a single fnStep preserves
the `.function`-kind AND the inputs-label projection at `g`. -/
theorem fnStep_preserves_function_kind_inputs
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global} {expected : List Local}
    (hf_inputs : f.name = g → f.inputs.map (·.1) = expected)
    (hacc : ∃ md_f, acc.getByKey g = some (.function md_f) ∧
      md_f.inputs.map (·.1) = expected) :
    ∃ md_f, (fnStep decls mono acc f).getByKey g = some (.function md_f) ∧
      md_f.inputs.map (·.1) = expected := by
  unfold fnStep
  by_cases hbeq : (f.name == g) = true
  · have heq : f.name = g := LawfulBEq.eq_of_beq hbeq
    let emptySubst : Global → Option Typ := fun _ => none
    let newF : Typed.Function :=
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body }
    refine ⟨newF, ?_, ?_⟩
    · rw [← heq]
      exact IndexMap.getByKey_insert_self _ _ _
    · -- newF.inputs.map (·.1) = f.inputs.map (·.1) = expected (via hf_inputs heq).
      show (f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)).map (·.1) = expected
      rw [List.map_map]
      have heq2 : (List.map ((fun x => x.1) ∘ fun (l, t) => (l, rewriteTyp emptySubst mono t)) f.inputs)
          = f.inputs.map (·.1) := by
        apply List.map_congr_left
        intro lt _; rfl
      rw [heq2]; exact hf_inputs heq
  · have hbeq' : (f.name == g) = false := Bool.not_eq_true _ |>.mp hbeq
    obtain ⟨md_f, hget, hin⟩ := hacc
    refine ⟨md_f, ?_, hin⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq']
    exact hget

/-- List-form: `fnStep` foldl preserves `.function`-kind + inputs-label
projection at `g` when every fn in the list targeting `g` has the property. -/
theorem fnStep_foldl_list_preserves_function_kind_inputs
    (decls : Typed.Decls) (mono : MonoMap) {g : Global} {expected : List Local} :
    ∀ (xs : List Typed.Function) (init : Typed.Decls),
      (∀ f' ∈ xs, f'.name = g → f'.inputs.map (·.1) = expected) →
      (∃ md_f, init.getByKey g = some (.function md_f) ∧
        md_f.inputs.map (·.1) = expected) →
      ∃ md_f, (xs.foldl (fnStep decls mono) init).getByKey g =
        some (.function md_f) ∧ md_f.inputs.map (·.1) = expected
  | [], init, _, hinit => hinit
  | hd :: tl, init, hfn_inputs, hinit => by
    simp only [List.foldl_cons]
    apply fnStep_foldl_list_preserves_function_kind_inputs decls mono tl
    · intro f' hf' heq
      exact hfn_inputs f' (List.mem_cons_of_mem _ hf') heq
    · exact fnStep_preserves_function_kind_inputs decls mono init hd
        (fun heq => hfn_inputs hd List.mem_cons_self heq) hinit

/-- Strengthened fold version of `fnStep_foldl_preserves_function_kind`: also
preserves the `inputs.map (·.1) = expected` invariant when every fn in the
fold range that targets `g` has that property. -/
theorem fnStep_foldl_preserves_function_kind_inputs
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {g : Global} {expected : List Local}
    (hfn_inputs : ∀ f' ∈ newFunctions, f'.name = g →
      f'.inputs.map (·.1) = expected)
    (hinit : ∃ md_f, init.getByKey g = some (.function md_f) ∧
      md_f.inputs.map (·.1) = expected) :
    ∃ md_f, (newFunctions.foldl (fnStep decls mono) init).getByKey g =
      some (.function md_f) ∧ md_f.inputs.map (·.1) = expected := by
  rw [← Array.foldl_toList]
  exact fnStep_foldl_list_preserves_function_kind_inputs decls mono
    newFunctions.toList init
    (fun f' hf' heq => hfn_inputs f' (Array.mem_toList_iff.mp hf') heq)
    hinit

/-- `fnStep` foldl inserts `.function` at `f.name` for every `f ∈
newFunctions`. The list-form does case-analysis on whether the head equals f
or recurses on the tail. -/
theorem fnStep_foldl_list_inserts_at_fn_name
    (decls : Typed.Decls) (mono : MonoMap) {f : Typed.Function} :
    ∀ (xs : List Typed.Function) (init : Typed.Decls)
      (_hmem : f ∈ xs),
    ∃ md_f, (xs.foldl (fnStep decls mono) init).getByKey f.name =
      some (.function md_f)
  | [], _, hmem => by cases hmem
  | hd :: rest, init, hmem => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · -- f = hd. fnStep on f inserts `.function` at f.name. Then preserve over rest.
      subst hmem_hd
      let emptySubst : Global → Option Typ := fun _ => none
      let newF : Typed.Function :=
        { f with
          inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
          output := rewriteTyp emptySubst mono f.output,
          body := rewriteTypedTerm decls emptySubst mono f.body }
      have hstep : ∃ md_f, (fnStep decls mono init f).getByKey f.name =
          some (.function md_f) := by
        refine ⟨newF, ?_⟩
        unfold fnStep
        exact IndexMap.getByKey_insert_self _ _ _
      -- Convert rest's foldl to Array form via fnStep_foldl_preserves_function_kind.
      have heq' : rest.foldl (fnStep decls mono) (fnStep decls mono init f)
          = rest.toArray.foldl (fnStep decls mono) (fnStep decls mono init f) := by
        rw [Array.foldl_toList]
      rw [heq']
      exact fnStep_foldl_preserves_function_kind decls mono rest.toArray
        (fnStep decls mono init f) hstep
    · -- f ∈ rest. Recurse.
      exact fnStep_foldl_list_inserts_at_fn_name decls mono rest
        (fnStep decls mono init hd) hmem_rest

/-- `fnStep` Array foldl inserts `.function` at `f.name` for every `f ∈
newFunctions`. -/
theorem fnStep_foldl_inserts_at_fn_name
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {f : Typed.Function} (hmem : f ∈ newFunctions) :
    ∃ md_f,
      (newFunctions.foldl (fnStep decls mono) init).getByKey f.name =
        some (.function md_f) := by
  rw [← Array.foldl_toList]
  exact fnStep_foldl_list_inserts_at_fn_name decls mono newFunctions.toList init
    (Array.mem_toList_iff.mpr hmem)

/-- Inner ctor-fold (used inside `dtStep`) preserves containsKey. -/
theorem dtCtorFold_preserves_containsKey
    (newDt : DataType) (cName : String → Global) (newD : Constructor → Typed.Declaration)
    {g : Global} :
    ∀ (cs : List Constructor) (acc : Typed.Decls),
      acc.containsKey g →
      (cs.foldl (fun acc'' c => acc''.insert (cName c.nameHead) (newD c)) acc).containsKey g
  | [], _, h => h
  | c :: rest, acc, h => by
    simp only [List.foldl_cons]
    exact dtCtorFold_preserves_containsKey newDt cName newD rest _
      (IndexMap.containsKey_insert_preserves _ _ _ _ h)

/-- `dtStep` is insert-only: containsKey is preserved across single steps. -/
theorem dtStep_preserves_containsKey
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType) {g : Global}
    (hacc : acc.containsKey g) :
    (dtStep mono acc dt).containsKey g := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- After acc.insert dt.name, containsKey preserved; then the ctor fold preserves.
  have hafter : (acc.insert dt.name (.dataType newDt)).containsKey g :=
    IndexMap.containsKey_insert_preserves _ _ _ _ hacc
  exact dtCtorFold_preserves_containsKey newDt
    (fun s => dt.name.pushNamespace s) (fun c => .constructor newDt c)
    rewrittenCtors _ hafter

/-- `dtStep` foldl preserves containsKey. -/
theorem dtStep_foldl_preserves_containsKey
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {g : Global}
    (hinit : init.containsKey g) :
    (newDataTypes.foldl (dtStep mono) init).containsKey g := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => acc.containsKey g) hinit
  intro i acc hinv
  exact dtStep_preserves_containsKey mono acc _ hinv

/-- `dtStep mono acc dt` always sets `containsKey dt.name`. -/
theorem dtStep_inserts_containsKey_self
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType) :
    (dtStep mono acc dt).containsKey dt.name := by
  obtain ⟨md_dt, hget⟩ := dtStep_inserts_dataType_at_self mono acc dt
  exact (IndexMap.getByKey_isSome_iff_containsKey _ _).mp (by rw [hget]; rfl)

/-- `fnStep` is insert-only: containsKey is preserved. -/
theorem fnStep_preserves_containsKey
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global} (hacc : acc.containsKey g) :
    (fnStep decls mono acc f).containsKey g := by
  unfold fnStep
  exact IndexMap.containsKey_insert_preserves _ _ _ _ hacc

/-- `fnStep` foldl preserves containsKey. -/
theorem fnStep_foldl_preserves_containsKey
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {g : Global}
    (hinit : init.containsKey g) :
    (newFunctions.foldl (fnStep decls mono) init).containsKey g := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => acc.containsKey g) hinit
  intro i acc hinv
  exact fnStep_preserves_containsKey decls mono acc _ hinv

/-- For every `dt ∈ newDataTypes`, `concretizeBuild`'s output contains `dt.name`
as a key (kind not specified — could be `.dataType` or `.constructor` if a
later inner-ctor key collides). Used to discharge cd-existence in
`concretize_produces_mono_correspondence`'s `has_new_decl` and `dt_lifts`. -/
theorem concretizeBuild_containsKey_newDt_name
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes) :
    (concretizeBuild typedDecls mono newFunctions newDataTypes).containsKey dt.name := by
  rw [concretizeBuild_eq]
  apply fnStep_foldl_preserves_containsKey
  -- Reduce dtStep foldl to a list-form split at dt's position, then preserve.
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem'
  rw [hsplit, List.foldl_append, List.foldl_cons]
  -- After the dtStep on dt, containsKey dt.name is set. Then foldl over post preserves.
  have h1 : (dtStep mono (List.foldl (dtStep mono) (typedDecls.pairs.foldl
      (srcStep typedDecls mono) default) pre) dt).containsKey dt.name :=
    dtStep_inserts_containsKey_self mono _ dt
  -- Convert post.foldl to Array form.
  have hconv : List.foldl (dtStep mono) (dtStep mono (List.foldl (dtStep mono)
      (typedDecls.pairs.foldl (srcStep typedDecls mono) default) pre) dt) post
      = post.toArray.foldl (dtStep mono) (dtStep mono (List.foldl (dtStep mono)
        (typedDecls.pairs.foldl (srcStep typedDecls mono) default) pre) dt) := by
    rw [Array.foldl_toList]
  rw [hconv]
  exact dtStep_foldl_preserves_containsKey mono post.toArray _ h1

/-- Inner ctor-fold inserts `.constructor newDt c'` at
`dt.name.pushNamespace nh` whenever some `c' ∈ cs` has `c'.nameHead = nh`.
After the matching insertion, `dtCtorFold_preserves_ctor_kind` handles
preservation across the rest of the fold (each subsequent ctor insert is
also a `.constructor`, so the kind is preserved unconditionally). -/
theorem dtCtorFold_inserts_at_nameHead
    (mono : MonoMap) (dt : DataType) (newDt : DataType) (nh : String) :
    ∀ (cs : List Constructor) (acc : Typed.Decls)
      (_hmem : ∃ c' ∈ cs, c'.nameHead = nh),
    ∃ md_dt md_c,
      (cs.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc).getByKey (dt.name.pushNamespace nh) = some (.constructor md_dt md_c) ∧
      md_dt = newDt
  | [], _, hmem => by
      obtain ⟨_, hc_mem, _⟩ := hmem
      cases hc_mem
  | c :: rest, acc, hmem => by
    simp only [List.foldl_cons]
    by_cases hnh : c.nameHead = nh
    · -- This step inserts at `dt.name.pushNamespace nh`. After it, the value
      -- is `.constructor newDt c`. Inner-fold preserves dt-companion = newDt.
      have hinner_pres : ∀ (cs' : List Constructor) (acc' : Typed.Decls)
          (_h : ∃ md_dt md_c,
            acc'.getByKey (dt.name.pushNamespace nh) =
              some (.constructor md_dt md_c) ∧ md_dt = newDt),
          ∃ md_dt md_c,
            (cs'.foldl
              (fun acc'' c'' =>
                let cName := dt.name.pushNamespace c''.nameHead
                acc''.insert cName (.constructor newDt c''))
              acc').getByKey (dt.name.pushNamespace nh) =
                some (.constructor md_dt md_c) ∧ md_dt = newDt := by
        intro cs'
        induction cs' with
        | nil => intro _ h; exact h
        | cons c'' rest' ih =>
          intro acc' hacc'
          simp only [List.foldl_cons]
          apply ih
          obtain ⟨md_dt, md_c, hget, hname⟩ := hacc'
          by_cases hbeq : (dt.name.pushNamespace c''.nameHead ==
              dt.name.pushNamespace nh) = true
          · refine ⟨newDt, c'', ?_, rfl⟩
            have heq : dt.name.pushNamespace c''.nameHead =
                dt.name.pushNamespace nh := LawfulBEq.eq_of_beq hbeq
            show ((acc'.insert (dt.name.pushNamespace c''.nameHead) _).getByKey _)
              = some _
            rw [heq]; exact IndexMap.getByKey_insert_self _ _ _
          · have hne : (dt.name.pushNamespace c''.nameHead ==
                dt.name.pushNamespace nh) = false :=
              Bool.not_eq_true _ |>.mp hbeq
            refine ⟨md_dt, md_c, ?_, hname⟩
            show ((acc'.insert (dt.name.pushNamespace c''.nameHead) _).getByKey _)
              = some _
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
            exact hget
      have h1 : ∃ md_dt md_c,
          (acc.insert (dt.name.pushNamespace c.nameHead)
            (.constructor newDt c)).getByKey (dt.name.pushNamespace nh) =
            some (.constructor md_dt md_c) ∧ md_dt = newDt := by
        refine ⟨newDt, c, ?_, rfl⟩
        rw [hnh]
        exact IndexMap.getByKey_insert_self _ _ _
      exact hinner_pres rest _ h1
    · obtain ⟨c', hc'_mem, hc'_nh⟩ := hmem
      rw [List.mem_cons] at hc'_mem
      rcases hc'_mem with rfl | hc'_rest
      · exact absurd hc'_nh hnh
      · exact dtCtorFold_inserts_at_nameHead mono dt newDt nh rest _
          ⟨c', hc'_rest, hc'_nh⟩

/-- A single step of `dtStep` on `dt` with `c ∈ dt.constructors` always sets
ctor-kind at `dt.name.pushNamespace c.nameHead` (the inner ctor fold inserts
the rewritten counterpart of `c` at this key). -/
theorem dtStep_inserts_ctor_at_self_ctor
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType)
    {c : Constructor} (hc : c ∈ dt.constructors) :
    ∃ md_dt md_c,
      (dtStep mono acc dt).getByKey (dt.name.pushNamespace c.nameHead) =
        some (.constructor md_dt md_c) := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c' =>
    { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- Find rewritten counterpart of c, with same nameHead.
  have hrewmem : ∃ c'' ∈ rewrittenCtors, c''.nameHead = c.nameHead := by
    refine ⟨{ c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }, ?_, rfl⟩
    exact List.mem_map_of_mem hc
  obtain ⟨md_dt, md_c, hget, _hname⟩ :=
    dtCtorFold_inserts_at_nameHead mono dt newDt c.nameHead rewrittenCtors _ hrewmem
  exact ⟨md_dt, md_c, hget⟩

/-- A single step of `dtStep` on `dt'` (possibly different from the target dt)
preserves ctor-kind at `g`, provided `dt'.name ≠ g`. The inner ctor fold
either re-inserts a `.constructor` at `g` (preserving ctor-kind) or doesn't
hit `g` (preserving the existing ctor entry). -/
theorem dtStep_preserves_ctor_kind_at_unconditional
    (mono : MonoMap) (acc : Typed.Decls) (dt' : DataType)
    {g : Global}
    (hdt'_ne : dt'.name ≠ g)
    (hacc : ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) :
    ∃ md_dt md_c, (dtStep mono acc dt').getByKey g = some (.constructor md_dt md_c) :=
  dtStep_preserves_ctor_kind mono acc dt' hdt'_ne hacc

/-- `dtStep` Array foldl preserves ctor-kind at `g` under `hDtNotKey`. The
inner ctor fold's potential re-insertion at `g` is benign — it inserts a
`.constructor`, preserving ctor-kind. -/
theorem dtStep_foldl_preserves_ctor_kind_at
    (mono : MonoMap) (newDataTypes : Array DataType) (init : Typed.Decls)
    {g : Global}
    (hinit : ∃ md_dt md_c, init.getByKey g = some (.constructor md_dt md_c))
    (hDtNotKey : ∀ dt' ∈ newDataTypes, dt'.name ≠ g) :
    ∃ md_dt md_c,
      (newDataTypes.foldl (dtStep mono) init).getByKey g =
        some (.constructor md_dt md_c) :=
  dtStep_foldl_preserves_ctor_kind mono newDataTypes init hinit hDtNotKey

/-- `dtStep` foldl over a list inserts ctor-kind at `dt.name.pushNamespace
c.nameHead` for `dt ∈ xs` and `c ∈ dt.constructors`, under `hDtNotKey`. -/
theorem dtStep_foldl_list_inserts_at_dt_ctor_name
    (mono : MonoMap) {dt : DataType} {c : Constructor} (hc : c ∈ dt.constructors) :
    ∀ (xs : List DataType) (init : Typed.Decls)
      (_hmem : dt ∈ xs)
      (_hDtNotKey : ∀ dt' ∈ xs, dt'.name ≠ dt.name.pushNamespace c.nameHead),
    ∃ md_dt md_c,
      (xs.foldl (dtStep mono) init).getByKey (dt.name.pushNamespace c.nameHead) =
        some (.constructor md_dt md_c)
  | [], _, hmem, _ => by cases hmem
  | hd :: rest, init, hmem, hDtNotKey => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · subst hmem_hd
      have h1 := dtStep_inserts_ctor_at_self_ctor mono init dt hc
      have hrest_dt : ∀ dt' ∈ rest, dt'.name ≠ dt.name.pushNamespace c.nameHead := by
        intro dt' hdt'
        exact hDtNotKey dt' (List.mem_cons_of_mem _ hdt')
      have heq : rest.foldl (dtStep mono) (dtStep mono init dt)
          = rest.toArray.foldl (dtStep mono) (dtStep mono init dt) := by
        rw [Array.foldl_toList]
      rw [heq]
      apply dtStep_foldl_preserves_ctor_kind_at mono rest.toArray _ h1
      intro dt' hdt'
      have hdt'_list : dt' ∈ rest := by
        have := Array.mem_toList_iff.mpr hdt'
        simpa using this
      exact hrest_dt dt' hdt'_list
    · have hrest_dt : ∀ dt' ∈ rest, dt'.name ≠ dt.name.pushNamespace c.nameHead := by
        intro dt' hdt'
        exact hDtNotKey dt' (List.mem_cons_of_mem _ hdt')
      exact dtStep_foldl_list_inserts_at_dt_ctor_name mono hc rest
        (dtStep mono init hd) hmem_rest hrest_dt

/-- `dtStep` Array foldl inserts ctor-kind at `dt.name.pushNamespace c.nameHead`
for every `dt ∈ newDataTypes` and `c ∈ dt.constructors`, under
`hDtNotKey`. -/
theorem dtStep_foldl_inserts_at_dt_ctor_name
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {dt : DataType} (hmem : dt ∈ newDataTypes)
    {c : Constructor} (hc : c ∈ dt.constructors)
    (hDtNotKey : ∀ dt' ∈ newDataTypes, dt'.name ≠ dt.name.pushNamespace c.nameHead) :
    ∃ md_dt md_c,
      (newDataTypes.foldl (dtStep mono) init).getByKey
        (dt.name.pushNamespace c.nameHead) = some (.constructor md_dt md_c) := by
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  have hDt' : ∀ dt' ∈ newDataTypes.toList, dt'.name ≠ dt.name.pushNamespace c.nameHead := by
    intro dt' hdt'
    exact hDtNotKey dt' (Array.mem_toList_iff.mp hdt')
  exact dtStep_foldl_list_inserts_at_dt_ctor_name mono hc newDataTypes.toList init
    hmem' hDt'

/-- Key lemma for `concretize_produces_mono_correspondence`'s `ctor_lifts` arm:
every `dt ∈ newDataTypes` and `c ∈ dt.constructors` has `.constructor _ _` at
`dt.name.pushNamespace c.nameHead` in `concretizeBuild`'s output, under
disjointness with newFunctions names and other newDataTypes names. -/
theorem concretizeBuild_at_newDt_ctor_name
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes)
    {c : Constructor} (hc : c ∈ dt.constructors)
    (hDtNotKey : ∀ dt' ∈ newDataTypes,
      dt'.name ≠ dt.name.pushNamespace c.nameHead)
    (hFnNotKey : ∀ f ∈ newFunctions,
      f.name ≠ dt.name.pushNamespace c.nameHead) :
    ∃ md_dt md_c,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey
        (dt.name.pushNamespace c.nameHead) =
        some (.constructor md_dt md_c) := by
  rw [concretizeBuild_eq]
  have h2 := dtStep_foldl_inserts_at_dt_ctor_name mono newDataTypes
    (typedDecls.pairs.foldl (srcStep typedDecls mono) default) hmem hc hDtNotKey
  exact fnStep_foldl_preserves_ctor_kind typedDecls mono newFunctions _ h2 hFnNotKey

/-! #### Existence-explicit version of `concretizeBuild_at_newDt_ctor_name`.

Returns the structural fact that `md_c.argTypes` is the empty-substitution
`rewriteTyp` of the argTypes of SOME ctor `c' ∈ dt.constructors` with
`c'.nameHead = c.nameHead`. This is enough to lift `c'.argTypes`-side
`AppRefToDt` into `md_c.argTypes`-side `AppRefToDtOrNewDt` via
`rewriteTyp_preserves_AppRefToDtOrNewDt`. We do NOT pin down exactly which
`c'` (could be the last one in `dt.constructors` with that nameHead under
inner ctor-fold last-writer-wins semantics, but any such `c'` works since
`CtorArgsAppRefToDt` covers ALL ctors of `dt`). -/

/-- Structural payload: at the cd ctor key, the typed declaration is
`.constructor` whose constructor's argTypes is the pointwise rewriteTyp of
SOME `c' ∈ dt'.constructors` for some `dt' ∈ newDataTypes`. The umbrella
applies `drained.CtorArgsAppRefToDt tds` (covering ALL dts/ctors in
newDataTypes) to lift `c'.argTypes` ⊆ AppRefToDt-safe to AppRefToDtOrNewDt-
safe via `rewriteTyp_preserves_AppRefToDtOrNewDt`. -/
@[expose] def CtorArgsRewrittenFrom (newDataTypes : List DataType) (mono : MonoMap)
    (d : Typed.Declaration) : Prop :=
  ∃ md_dt md_c, d = .constructor md_dt md_c ∧
    ∃ dt' ∈ newDataTypes, ∃ c' ∈ dt'.constructors,
      md_c.argTypes = c'.argTypes.map (rewriteTyp (fun _ => none) mono)

/-- Helper: rewrittenCtors_origin lifted to per-element witness. -/
theorem rewrittenCtors_origin
    (mono : MonoMap) (dt : DataType) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := dt.constructors.map fun c' =>
      { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
    ∀ c'' ∈ rewrittenCtors, ∃ c0 ∈ dt.constructors,
      c''.nameHead = c0.nameHead ∧
      c''.argTypes = c0.argTypes.map (rewriteTyp emptySubst mono) := by
  intro emptySubst rewrittenCtors c'' hc''
  obtain ⟨c0, hc0_mem, hc0_eq⟩ := List.mem_map.mp hc''
  refine ⟨c0, hc0_mem, ?_, ?_⟩
  · rw [← hc0_eq]
  · rw [← hc0_eq]

/-- The inner ctor fold (over `cs` with each c'' ∈ cs being a rewrittenCtor
of `dt'`) writes `.constructor newDt' c''`, satisfying
`CtorArgsRewrittenFrom wholeList mono` provided `dt' ∈ wholeList`. -/
theorem dtCtorFold_writes_CtorArgsRewrittenFrom_at_dt_ctor
    (mono : MonoMap) (dt' : DataType) (newDt' : DataType)
    (wholeList : List DataType) (hwhole : dt' ∈ wholeList) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := dt'.constructors.map fun c0 =>
      { c0 with argTypes := c0.argTypes.map (rewriteTyp emptySubst mono) }
    ∀ {c : Constructor} (hc : c ∈ dt'.constructors)
      (acc : Typed.Decls),
    ∃ d,
      (rewrittenCtors.foldl
        (fun acc'' c'' =>
          let cName := dt'.name.pushNamespace c''.nameHead
          acc''.insert cName (.constructor newDt' c''))
        acc).getByKey (dt'.name.pushNamespace c.nameHead) = some d ∧
      CtorArgsRewrittenFrom wholeList mono d := by
  intro emptySubst rewrittenCtors c hc acc
  -- The c-image is in rewrittenCtors with same nameHead; some later c''-image
  -- (possibly the c-image itself) is the LAST writer at the key.
  -- Generic inner-fold lemma: starts from "no value at key" and returns SOME.
  -- Given hc, we know ∃ c-image ∈ rewrittenCtors with matching nameHead.
  -- Strategy: show that after the fold, IF some c''-image in cs has matching
  -- nameHead, the value at the key is `.constructor newDt' c''_last` where
  -- c''_last is the LAST such image.
  -- Since `rewrittenCtors` is the result of `dt'.constructors.map`, every
  -- c'' ∈ rewrittenCtors has a c0 ∈ dt'.constructors with matching nameHead
  -- and argTypes mapping (via rewrittenCtors_origin). So whichever c''_last
  -- wins, the predicate holds.
  -- Use a generic helper that takes a per-element origin witness.
  have hinner_writes : ∀ (cs : List Constructor) (acc' : Typed.Decls)
      (_hper : ∀ c'' ∈ cs, ∃ c0 ∈ dt'.constructors,
          c''.nameHead = c0.nameHead ∧
          c''.argTypes = c0.argTypes.map (rewriteTyp emptySubst mono))
      (_hmem : ∃ c'' ∈ cs, c''.nameHead = c.nameHead),
    ∃ d,
      (cs.foldl
        (fun acc'' c'' =>
          let cName := dt'.name.pushNamespace c''.nameHead
          acc''.insert cName (.constructor newDt' c''))
        acc').getByKey (dt'.name.pushNamespace c.nameHead) = some d ∧
      CtorArgsRewrittenFrom wholeList mono d := by
    intro cs
    induction cs with
    | nil => intro _ _ ⟨_, hm, _⟩; cases hm
    | cons c'' rest ih_inner =>
      intro acc' hper hmem
      simp only [List.foldl_cons]
      by_cases hrest_match : ∃ c''' ∈ rest, c'''.nameHead = c.nameHead
      · -- Recurse: rest covers some matching c'''.
        apply ih_inner
        · intro c4 hc4; exact hper c4 (List.mem_cons_of_mem _ hc4)
        · exact hrest_match
      · -- No matching in rest. Either c''.nameHead = c.nameHead (write here, then
        -- rest preserves), or contradiction with hmem (must be c'').
        by_cases hnh : c''.nameHead = c.nameHead
        · -- Write at key, then preserve through rest.
          obtain ⟨c0, hc0_mem, hc0_nh, hc0_arg⟩ := hper c'' List.mem_cons_self
          have hwrite : ∃ d,
              (acc'.insert (dt'.name.pushNamespace c''.nameHead)
                (.constructor newDt' c'')).getByKey
                  (dt'.name.pushNamespace c.nameHead) = some d ∧
              CtorArgsRewrittenFrom wholeList mono d := by
            rw [hnh]
            refine ⟨.constructor newDt' c'', IndexMap.getByKey_insert_self _ _ _, ?_⟩
            refine ⟨newDt' , c'', rfl, dt', hwhole, c0, hc0_mem, hc0_arg⟩
          -- Preserve through rest (no c''' ∈ rest with matching nameHead, so
          -- no insert at the key).
          have hrest_pres : ∀ (cs' : List Constructor) (acc'' : Typed.Decls)
              (_hno : ∀ c''' ∈ cs', c'''.nameHead ≠ c.nameHead)
              (_hacc : ∃ d, acc''.getByKey (dt'.name.pushNamespace c.nameHead) = some d ∧
                CtorArgsRewrittenFrom wholeList mono d),
            ∃ d,
              (cs'.foldl
                (fun a' c''' =>
                  let cName := dt'.name.pushNamespace c'''.nameHead
                  a'.insert cName (.constructor newDt' c'''))
                acc'').getByKey (dt'.name.pushNamespace c.nameHead) = some d ∧
              CtorArgsRewrittenFrom wholeList mono d := by
            intro cs'
            induction cs' with
            | nil => intro _ _ h; exact h
            | cons c5 rest5 ih5 =>
              intro acc'' hno hacc''
              simp only [List.foldl_cons]
              apply ih5
              · intro c6 hc6; exact hno c6 (List.mem_cons_of_mem _ hc6)
              · obtain ⟨d, hget, hM⟩ := hacc''
                refine ⟨d, ?_, hM⟩
                have hne : (dt'.name.pushNamespace c5.nameHead ==
                    dt'.name.pushNamespace c.nameHead) = false := by
                  rw [beq_eq_false_iff_ne]
                  intro hkey_eq
                  apply hno c5 List.mem_cons_self
                  -- pushNamespace inj on str-side.
                  have h1 : (dt'.name.pushNamespace c5.nameHead).toName =
                      (dt'.name.pushNamespace c.nameHead).toName := by
                    rw [hkey_eq]
                  have h2 : Lean.Name.str dt'.name.toName c5.nameHead =
                      Lean.Name.str dt'.name.toName c.nameHead := h1
                  injection h2
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hget
          have hno_rest : ∀ c''' ∈ rest, c'''.nameHead ≠ c.nameHead := by
            intro c''' hc''' heq
            exact hrest_match ⟨c''', hc''', heq⟩
          exact hrest_pres rest _ hno_rest hwrite
        · -- c''.nameHead ≠ c.nameHead, so hmem must come from rest.
          obtain ⟨c''', hc'''_mem, hc'''_nh⟩ := hmem
          rw [List.mem_cons] at hc'''_mem
          rcases hc'''_mem with rfl | hc'''_rest
          · exact absurd hc'''_nh hnh
          · exact absurd ⟨c''', hc'''_rest, hc'''_nh⟩ hrest_match
  have hper := rewrittenCtors_origin mono dt'
  have hmem_witness : ∃ c'' ∈ rewrittenCtors, c''.nameHead = c.nameHead := by
    refine ⟨{ c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }, ?_, rfl⟩
    exact List.mem_map_of_mem hc
  exact hinner_writes rewrittenCtors _ hper hmem_witness

/-- A single step of `dtStep` on `dt` with `c ∈ dt.constructors` sets
`CtorArgsRewrittenFrom wholeList mono` at `dt.name.pushNamespace c.nameHead`,
provided `dt ∈ wholeList`. -/
theorem dtStep_inserts_CtorArgsRewrittenFrom_self
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType)
    (wholeList : List DataType) (hwhole : dt ∈ wholeList)
    {c : Constructor} (hc : c ∈ dt.constructors) :
    ∃ d, (dtStep mono acc dt).getByKey (dt.name.pushNamespace c.nameHead) = some d ∧
      CtorArgsRewrittenFrom wholeList mono d := by
  unfold dtStep
  -- After outer dt-insert (at dt.name ≠ pushNamespace key), inner ctor fold writes.
  exact dtCtorFold_writes_CtorArgsRewrittenFrom_at_dt_ctor mono dt _ wholeList hwhole hc _

/-- A single step of `dtStep` on `dt'` (any) preserves
`CtorArgsRewrittenFrom wholeList mono` at `g`, provided either:
- `dt'.name ≠ g` AND no c'' ∈ dt'.constructors has dt'.name.pushNamespace c''.nameHead = g
  (so the dtStep doesn't write at g), OR
- `dt' ∈ wholeList` (so even if it writes at g, the new value still satisfies the predicate).
This lemma takes the SECOND form: dt' ∈ wholeList. -/
theorem dtStep_preserves_CtorArgsRewrittenFrom_via_wholeList
    (mono : MonoMap) (acc : Typed.Decls) (dt' : DataType)
    (wholeList : List DataType) (hwhole : dt' ∈ wholeList)
    {g : Global}
    (hdt'_ne : dt'.name ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ CtorArgsRewrittenFrom wholeList mono d) :
    ∃ d, (dtStep mono acc dt').getByKey g = some d ∧
      CtorArgsRewrittenFrom wholeList mono d := by
  unfold dtStep
  have hbeq_dt'_name : (dt'.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hdt'_ne
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt'.constructors.map fun c' =>
    { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt' : DataType := { dt' with constructors := rewrittenCtors }
  -- After outer dt-insert: still satisfies predicate at g.
  have hacc_after : ∃ d,
      (acc.insert dt'.name (Typed.Declaration.dataType newDt')).getByKey g = some d ∧
      CtorArgsRewrittenFrom wholeList mono d := by
    obtain ⟨d, hget, hM⟩ := hacc
    refine ⟨d, ?_, hM⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt'_name]
    exact hget
  -- Inner ctor fold: each insert is `.constructor newDt' c''`. If at g, value
  -- still satisfies CtorArgsRewrittenFrom wholeList mono (via dt' ∈ wholeList).
  -- If not at g, value preserved.
  have hper := rewrittenCtors_origin mono dt'
  -- Generic inner preservation lemma.
  have hinner : ∀ (cs : List Constructor) (acc' : Typed.Decls)
      (_hper : ∀ c'' ∈ cs, ∃ c0 ∈ dt'.constructors,
        c''.nameHead = c0.nameHead ∧
        c''.argTypes = c0.argTypes.map (rewriteTyp emptySubst mono))
      (_hacc : ∃ d, acc'.getByKey g = some d ∧ CtorArgsRewrittenFrom wholeList mono d),
    ∃ d,
      (cs.foldl
        (fun acc'' c'' =>
          let cName := dt'.name.pushNamespace c''.nameHead
          acc''.insert cName (.constructor newDt' c''))
        acc').getByKey g = some d ∧
      CtorArgsRewrittenFrom wholeList mono d := by
    intro cs
    induction cs with
    | nil => intro _ _ h; exact h
    | cons c'' rest ih_inner =>
      intro acc' hper' hacc'
      simp only [List.foldl_cons]
      apply ih_inner
      · intro c''' hc'''; exact hper' c''' (List.mem_cons_of_mem _ hc''')
      · by_cases hbeq : (dt'.name.pushNamespace c''.nameHead == g) = true
        · obtain ⟨c0, hc0_mem, hc0_nh, hc0_arg⟩ := hper' c'' List.mem_cons_self
          refine ⟨.constructor newDt' c'', ?_, ?_⟩
          · rw [LawfulBEq.eq_of_beq hbeq]; exact IndexMap.getByKey_insert_self _ _ _
          · refine ⟨newDt', c'', rfl, dt', hwhole, c0, hc0_mem, hc0_arg⟩
        · have hne : (dt'.name.pushNamespace c''.nameHead == g) = false :=
            Bool.not_eq_true _ |>.mp hbeq
          obtain ⟨d, hget, hM⟩ := hacc'
          refine ⟨d, ?_, hM⟩
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hget
  exact hinner rewrittenCtors _ hper hacc_after

/-- `dtStep` foldl over a list inserts `CtorArgsRewrittenFrom wholeList mono`
at `dt.name.pushNamespace c.nameHead`, where `wholeList ⊇ xs ∋ dt`, under
outer-disjointness `hDtNotKey`. The predicate's existential is over `wholeList`,
so subsequent dtSteps on dt' ∈ xs ⊆ wholeList preserve the predicate even when
they overwrite at the key (the new value still has dt' ∈ wholeList witness). -/
theorem dtStep_foldl_list_inserts_CtorArgsRewrittenFrom
    (mono : MonoMap) {dt : DataType} {c : Constructor} (hc : c ∈ dt.constructors)
    (wholeList : List DataType) :
    ∀ (xs : List DataType) (init : Typed.Decls)
      (_hsub : ∀ dt' ∈ xs, dt' ∈ wholeList)
      (_hmem : dt ∈ xs)
      (_hDtNotKey : ∀ dt' ∈ xs, dt'.name ≠ dt.name.pushNamespace c.nameHead),
    ∃ d,
      (xs.foldl (dtStep mono) init).getByKey
        (dt.name.pushNamespace c.nameHead) = some d ∧
      CtorArgsRewrittenFrom wholeList mono d
  | [], _, _, hmem, _ => by cases hmem
  | hd :: rest, init, hsub, hmem, hDtNotKey => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · subst hmem_hd
      have hwhole : dt ∈ wholeList := hsub dt List.mem_cons_self
      have h1 := dtStep_inserts_CtorArgsRewrittenFrom_self mono init dt wholeList hwhole hc
      -- Preserve through rest via the wholeList variant.
      have hrest_pres : ∀ (l : List DataType) (acc : Typed.Decls)
          (_hl_sub : ∀ dt' ∈ l, dt' ∈ wholeList)
          (_hl_dt_ne : ∀ dt' ∈ l, dt'.name ≠ dt.name.pushNamespace c.nameHead)
          (_hacc : ∃ d, acc.getByKey (dt.name.pushNamespace c.nameHead) = some d ∧
            CtorArgsRewrittenFrom wholeList mono d),
        ∃ d, (l.foldl (dtStep mono) acc).getByKey
          (dt.name.pushNamespace c.nameHead) = some d ∧
          CtorArgsRewrittenFrom wholeList mono d := by
        intro l
        induction l with
        | nil => intro acc _ _ h; exact h
        | cons hd' tl ih =>
          intro acc hl_sub hl_dt_ne hacc
          simp only [List.foldl_cons]
          apply ih
          · intro dt' hdt'; exact hl_sub dt' (List.mem_cons_of_mem _ hdt')
          · intro dt' hdt'; exact hl_dt_ne dt' (List.mem_cons_of_mem _ hdt')
          · -- One dtStep on hd' preserves.
            have hhd'_whole : hd' ∈ wholeList := hl_sub hd' List.mem_cons_self
            have hhd'_ne : hd'.name ≠ dt.name.pushNamespace c.nameHead :=
              hl_dt_ne hd' List.mem_cons_self
            exact dtStep_preserves_CtorArgsRewrittenFrom_via_wholeList
              mono acc hd' wholeList hhd'_whole hhd'_ne hacc
      have hrest_sub : ∀ dt' ∈ rest, dt' ∈ wholeList :=
        fun dt' hdt' => hsub dt' (List.mem_cons_of_mem _ hdt')
      have hrest_dt : ∀ dt' ∈ rest, dt'.name ≠ dt.name.pushNamespace c.nameHead :=
        fun dt' hdt' => hDtNotKey dt' (List.mem_cons_of_mem _ hdt')
      exact hrest_pres rest _ hrest_sub hrest_dt h1
    · have hrest_sub : ∀ dt' ∈ rest, dt' ∈ wholeList :=
        fun dt' hdt' => hsub dt' (List.mem_cons_of_mem _ hdt')
      have hrest_dt : ∀ dt' ∈ rest, dt'.name ≠ dt.name.pushNamespace c.nameHead :=
        fun dt' hdt' => hDtNotKey dt' (List.mem_cons_of_mem _ hdt')
      exact dtStep_foldl_list_inserts_CtorArgsRewrittenFrom mono hc wholeList rest
        (dtStep mono init hd) hrest_sub hmem_rest hrest_dt

/-- `dtStep` Array foldl variant of `dtStep_foldl_list_inserts_CtorArgsRewrittenFrom`
specialized to wholeList = newDataTypes.toList. -/
theorem dtStep_foldl_inserts_CtorArgsRewrittenFrom
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {dt : DataType} (hmem : dt ∈ newDataTypes)
    {c : Constructor} (hc : c ∈ dt.constructors)
    (hDtNotKey : ∀ dt' ∈ newDataTypes, dt'.name ≠ dt.name.pushNamespace c.nameHead) :
    ∃ d,
      (newDataTypes.foldl (dtStep mono) init).getByKey
        (dt.name.pushNamespace c.nameHead) = some d ∧
      CtorArgsRewrittenFrom newDataTypes.toList mono d := by
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  have hDt' : ∀ dt' ∈ newDataTypes.toList, dt'.name ≠ dt.name.pushNamespace c.nameHead := by
    intro dt' hdt'
    exact hDtNotKey dt' (Array.mem_toList_iff.mp hdt')
  have hsub : ∀ dt' ∈ newDataTypes.toList, dt' ∈ newDataTypes.toList := fun _ h => h
  exact dtStep_foldl_list_inserts_CtorArgsRewrittenFrom mono hc newDataTypes.toList
    newDataTypes.toList init hsub hmem' hDt'

/-- A single step of `fnStep` on `f` with `f.name ≠ g` preserves
`CtorArgsRewrittenFrom wholeList mono` at `g`. -/
theorem fnStep_preserves_CtorArgsRewrittenFrom
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {wholeList : List DataType} {g : Global}
    (hfn_ne : f.name ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ CtorArgsRewrittenFrom wholeList mono d) :
    ∃ d, (fnStep decls mono acc f).getByKey g = some d ∧
      CtorArgsRewrittenFrom wholeList mono d := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨d, hget, hM⟩ := hacc
  refine ⟨d, ?_, hM⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

/-- `fnStep` Array foldl preserves `CtorArgsRewrittenFrom wholeList mono` at
`g` under `hFnNotKey`. -/
theorem fnStep_foldl_preserves_CtorArgsRewrittenFrom
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {wholeList : List DataType} {g : Global}
    (hinit : ∃ d, init.getByKey g = some d ∧ CtorArgsRewrittenFrom wholeList mono d)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ d, (newFunctions.foldl (fnStep decls mono) init).getByKey g = some d ∧
      CtorArgsRewrittenFrom wholeList mono d := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ d, acc.getByKey g = some d ∧ CtorArgsRewrittenFrom wholeList mono d) hinit
  intro i acc hinv
  have hfn_ne : (newFunctions[i.val]'i.isLt).name ≠ g :=
    hFnNotKey _ (Array.getElem_mem _)
  exact fnStep_preserves_CtorArgsRewrittenFrom decls mono acc _ hfn_ne hinv

/-- Explicit-existence form of `concretizeBuild_at_newDt_ctor_name`: for any
`dt ∈ newDataTypes` and `c ∈ dt.constructors`, the value at
`dt.name.pushNamespace c.nameHead` in concretizeBuild is `.constructor md_dt
md_c` where `md_c.argTypes = c'.argTypes.map (rewriteTyp ∅ mono)` for SOME
`c' ∈ dt'.constructors` for SOME `dt' ∈ newDataTypes` (not necessarily the
input `dt`).

Disjointness premises:
* `hDtNotKey`: no newDt has dt'.name = the key.
* `hFnNotKey`: no newFn has fn.name = the key.

This is enough for the umbrella's `BLOCKED-A.1-ctor-md_AR-newDt` discharge:
- `c'.argTypes` are AppRefToDt-safe by `drained.CtorArgsAppRefToDt tds` (since
  it covers ALL dts in newDataTypes, including the witness dt').
- `rewriteTyp ∅ mono` of an AppRefToDt-safe type is AppRefToDtOrNewDt-safe
  via `rewriteTyp_preserves_AppRefToDtOrNewDt`. -/
theorem concretizeBuild_at_newDt_ctor_name_explicit
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes)
    {c : Constructor} (hc : c ∈ dt.constructors)
    (hDtNotKey : ∀ dt' ∈ newDataTypes,
      dt'.name ≠ dt.name.pushNamespace c.nameHead)
    (hFnNotKey : ∀ f ∈ newFunctions,
      f.name ≠ dt.name.pushNamespace c.nameHead) :
    ∃ d,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey
        (dt.name.pushNamespace c.nameHead) = some d ∧
      CtorArgsRewrittenFrom newDataTypes.toList mono d := by
  rw [concretizeBuild_eq]
  have h2 := dtStep_foldl_inserts_CtorArgsRewrittenFrom mono newDataTypes
    (typedDecls.pairs.foldl (srcStep typedDecls mono) default) hmem hc hDtNotKey
  exact fnStep_foldl_preserves_CtorArgsRewrittenFrom typedDecls mono newFunctions
    _ h2 hFnNotKey

/-! #### `concretizeBuild_at_newDt_ctor_name_dt_companion`: gives the
dt-companion at the .ctor entry as `{dt with constructors := rewrittenCtors}`.
Strengthens `concretizeBuild_at_newDt_ctor_name` to expose the dt-companion's
structural form. Used by D3e closure to identify md_dt''' = md_dt. -/

/-- Predicate: a typed declaration is `.constructor md_dt _` where md_dt has
the canonical rewritten-from-`dt` form. -/
@[expose] def DtCompanionRewrittenFrom (mono : MonoMap) (dt : DataType)
    (d : Typed.Declaration) : Prop :=
  ∃ md_dt md_c, d = .constructor md_dt md_c ∧
    md_dt = { dt with constructors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) } }

/-- Inner ctor fold writes a value at `dt.name.pushNs c.nameHead` with the
specified newDt as dt-companion. The c-image (last writer) is some image
in rewrittenCtors with matching nameHead — its identity doesn't matter
for the dt-companion structure. -/
theorem dtCtorFold_writes_DtCompanionRewrittenFrom_at_dt_ctor
    (mono : MonoMap) (dt : DataType) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := dt.constructors.map fun c0 =>
      { c0 with argTypes := c0.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    ∀ {c : Constructor} (hc : c ∈ dt.constructors)
      (acc : Typed.Decls),
    ∃ d,
      (rewrittenCtors.foldl
        (fun acc'' c'' =>
          acc''.insert (dt.name.pushNamespace c''.nameHead)
            (.constructor newDt c''))
        acc).getByKey (dt.name.pushNamespace c.nameHead) = some d ∧
      DtCompanionRewrittenFrom mono dt d := by
  intro emptySubst rewrittenCtors newDt c hc acc
  -- Generic inner-fold: given there's some c'' ∈ cs with matching nameHead,
  -- the value at the key is `.constructor newDt _` with newDt fixed.
  have hinner : ∀ (cs : List Constructor) (acc' : Typed.Decls)
      (_hmem : ∃ c'' ∈ cs, c''.nameHead = c.nameHead),
    ∃ d,
      (cs.foldl
        (fun acc'' c'' =>
          acc''.insert (dt.name.pushNamespace c''.nameHead)
            (.constructor newDt c''))
        acc').getByKey (dt.name.pushNamespace c.nameHead) = some d ∧
      DtCompanionRewrittenFrom mono dt d := by
    intro cs
    induction cs with
    | nil => intro _ ⟨_, hmem, _⟩; cases hmem
    | cons hd rest ih =>
      intro acc' hmem
      simp only [List.foldl_cons]
      by_cases hexist : ∃ c'' ∈ rest, c''.nameHead = c.nameHead
      · exact ih _ hexist
      · -- hd is the LAST writer at the key.
        rcases hmem with ⟨c'', hc''_mem, hc''_nh⟩
        rw [List.mem_cons] at hc''_mem
        rcases hc''_mem with hc''_eq | hc''_in_rest
        · have hhd_nh : hd.nameHead = c.nameHead := by rw [← hc''_eq]; exact hc''_nh
          have hrest_nokey : ∀ c2 ∈ rest, dt.name.pushNamespace c2.nameHead ≠
              dt.name.pushNamespace c.nameHead := by
            intro c2 hc2 heq2
            have hc2_nh : c2.nameHead = c.nameHead := by
              have h' : dt.name.toName.mkStr c2.nameHead = dt.name.toName.mkStr c.nameHead := by
                unfold Global.pushNamespace at heq2
                exact Global.mk.inj heq2
              have h'' : Lean.Name.str dt.name.toName c2.nameHead =
                  Lean.Name.str dt.name.toName c.nameHead := h'
              injection h''
            exact hexist ⟨c2, hc2, hc2_nh⟩
          have hacc_after : ∃ d,
              (acc'.insert (dt.name.pushNamespace hd.nameHead)
                (.constructor newDt hd)).getByKey
                  (dt.name.pushNamespace c.nameHead) = some d ∧
                DtCompanionRewrittenFrom mono dt d := by
            rw [hhd_nh]
            refine ⟨.constructor newDt hd, IndexMap.getByKey_insert_self _ _ _, ?_⟩
            exact ⟨newDt, hd, rfl, rfl⟩
          have hpreserve : ∀ (cs2 : List Constructor) (acc2 : Typed.Decls)
              (_hno : ∀ c2 ∈ cs2, dt.name.pushNamespace c2.nameHead ≠
                dt.name.pushNamespace c.nameHead)
              (_hacc : ∃ d, acc2.getByKey (dt.name.pushNamespace c.nameHead) = some d ∧
                DtCompanionRewrittenFrom mono dt d),
            ∃ d, (cs2.foldl
              (fun acc'' c'' =>
                acc''.insert (dt.name.pushNamespace c''.nameHead)
                  (.constructor newDt c'')) acc2).getByKey
                    (dt.name.pushNamespace c.nameHead) = some d ∧
              DtCompanionRewrittenFrom mono dt d := by
            intro cs2
            induction cs2 with
            | nil => intro acc2 _ h; exact h
            | cons hd2 rest2 ih2 =>
              intro acc2 hno hacc
              simp only [List.foldl_cons]
              have hne : (dt.name.pushNamespace hd2.nameHead ==
                  dt.name.pushNamespace c.nameHead) = false := by
                rw [beq_eq_false_iff_ne]
                exact hno hd2 List.mem_cons_self
              obtain ⟨d, hget, hM⟩ := hacc
              apply ih2 _ (fun c2 hc2 => hno c2 (List.mem_cons_of_mem _ hc2))
              refine ⟨d, ?_, hM⟩
              rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget
          exact hpreserve _ _ hrest_nokey hacc_after
        · exact absurd ⟨c'', hc''_in_rest, hc''_nh⟩ hexist
  apply hinner
  refine ⟨{ c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }, ?_, rfl⟩
  exact List.mem_map_of_mem hc

/-- Single dtStep on `dt` inserts `.constructor newDt _` at the ctor key,
where newDt is the rewritten form of `dt`. -/
theorem dtStep_inserts_DtCompanionRewrittenFrom_self
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType)
    {c : Constructor} (hc : c ∈ dt.constructors) :
    ∃ d, (dtStep mono acc dt).getByKey (dt.name.pushNamespace c.nameHead) =
      some d ∧ DtCompanionRewrittenFrom mono dt d := by
  unfold dtStep
  exact dtCtorFold_writes_DtCompanionRewrittenFrom_at_dt_ctor mono dt hc _

/-- dtStep on `dt'` (different from target `dt`) preserves the .ctor entry's
dt-companion at K = `dt.name.pushNs c.nameHead` when `dt'.name ≠ K` and no
inner ctor of `dt'` writes to K. -/
theorem dtStep_preserves_DtCompanionRewrittenFrom
    (mono : MonoMap) (acc : Typed.Decls) (dt' target_dt : DataType)
    {K : Global}
    (hdt'_ne : dt'.name ≠ K)
    (hCtorNotKey : ∀ c ∈ dt'.constructors, dt'.name.pushNamespace c.nameHead ≠ K)
    (hacc : ∃ d, acc.getByKey K = some d ∧ DtCompanionRewrittenFrom mono target_dt d) :
    ∃ d, (dtStep mono acc dt').getByKey K = some d ∧
      DtCompanionRewrittenFrom mono target_dt d := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt'.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt' : DataType := { dt' with constructors := rewrittenCtors }
  have hbeq_dt' : (dt'.name == K) = false := by
    rw [beq_eq_false_iff_ne]; exact hdt'_ne
  have hacc_after : ∃ d,
      (acc.insert dt'.name (Typed.Declaration.dataType newDt')).getByKey K =
        some d ∧ DtCompanionRewrittenFrom mono target_dt d := by
    obtain ⟨d, hget, hM⟩ := hacc
    refine ⟨d, ?_, hM⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt']
    exact hget
  have hCtorNotKey' : ∀ c ∈ rewrittenCtors,
      dt'.name.pushNamespace c.nameHead ≠ K := by
    intro c hc
    obtain ⟨c_orig, hc_orig_mem, hc_orig_eq⟩ := List.mem_map.mp hc
    have hnh : c.nameHead = c_orig.nameHead := by rw [← hc_orig_eq]
    rw [hnh]
    exact hCtorNotKey c_orig hc_orig_mem
  have hpreserve : ∀ (cs : List Constructor) (acc2 : Typed.Decls)
      (_hno : ∀ c2 ∈ cs, dt'.name.pushNamespace c2.nameHead ≠ K)
      (_hacc : ∃ d, acc2.getByKey K = some d ∧
        DtCompanionRewrittenFrom mono target_dt d),
    ∃ d, (cs.foldl
      (fun acc'' c =>
        acc''.insert (dt'.name.pushNamespace c.nameHead)
          (.constructor newDt' c)) acc2).getByKey K = some d ∧
      DtCompanionRewrittenFrom mono target_dt d := by
    intro cs
    induction cs with
    | nil => intro _ _ h; exact h
    | cons hd rest ih =>
      intro acc2 hno hacc
      simp only [List.foldl_cons]
      have hne : (dt'.name.pushNamespace hd.nameHead == K) = false := by
        rw [beq_eq_false_iff_ne]; exact hno hd List.mem_cons_self
      obtain ⟨d, hget, hM⟩ := hacc
      apply ih _ (fun c2 hc2 => hno c2 (List.mem_cons_of_mem _ hc2))
      refine ⟨d, ?_, hM⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget
  exact hpreserve _ _ hCtorNotKey' hacc_after

theorem fnStep_preserves_DtCompanionRewrittenFrom
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    (target_dt : DataType)
    {K : Global} (hfn_ne : f.name ≠ K)
    (hacc : ∃ d, acc.getByKey K = some d ∧ DtCompanionRewrittenFrom mono target_dt d) :
    ∃ d, (fnStep decls mono acc f).getByKey K = some d ∧
      DtCompanionRewrittenFrom mono target_dt d := by
  unfold fnStep
  have hbeq : (f.name == K) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨d, hget, hM⟩ := hacc
  refine ⟨d, ?_, hM⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

/-- dtStep foldl over a list inserts `.constructor newDt _` with the canonical
dt-companion form at `dt.name.pushNs c.nameHead`, under
`hOtherDtNotKey` (no other newDt has name = K, so dtStep on others doesn't override
the .dataType outer key) AND `hOtherInnerCtorNotKey` (no other newDt's inner ctor
hits K). -/
theorem dtStep_foldl_list_inserts_DtCompanionRewrittenFrom
    (mono : MonoMap) {dt : DataType} {c : Constructor} (hc : c ∈ dt.constructors) :
    ∀ (xs : List DataType) (init : Typed.Decls)
      (_hmem : dt ∈ xs)
      (_hOtherDtNotKey : ∀ dt' ∈ xs, dt'.name ≠ dt.name.pushNamespace c.nameHead)
      (_hOtherInnerCtorNotKey : ∀ dt' ∈ xs, dt' ≠ dt → ∀ c2 ∈ dt'.constructors,
        dt'.name.pushNamespace c2.nameHead ≠ dt.name.pushNamespace c.nameHead),
    ∃ d, (xs.foldl (dtStep mono) init).getByKey
      (dt.name.pushNamespace c.nameHead) = some d ∧
      DtCompanionRewrittenFrom mono dt d
  | [], _, hmem, _, _ => by cases hmem
  | hd :: rest, init, hmem, hOtherDtNotKey, hOtherInnerCtorNotKey => by
    -- We use a single preserve lemma that handles dt' = dt (re-insertion of
    -- the SAME canonical value preserves DtCompanionRewrittenFrom). Case-split
    -- on hd = dt vs hd ≠ dt outside; recurse on rest.
    simp only [List.foldl_cons]
    -- Strengthened preserve through ANY xs, allowing same-dt re-insertion.
    have hpreserve : ∀ (ys : List DataType) (acc : Typed.Decls)
        (_hOther : ∀ dt' ∈ ys, dt'.name ≠ dt.name.pushNamespace c.nameHead)
        (_hOtherInner : ∀ dt' ∈ ys, dt' ≠ dt → ∀ c2 ∈ dt'.constructors,
          dt'.name.pushNamespace c2.nameHead ≠ dt.name.pushNamespace c.nameHead)
        (_hacc : ∃ d, acc.getByKey (dt.name.pushNamespace c.nameHead) = some d ∧
          DtCompanionRewrittenFrom mono dt d),
      ∃ d, (ys.foldl (dtStep mono) acc).getByKey
        (dt.name.pushNamespace c.nameHead) = some d ∧
        DtCompanionRewrittenFrom mono dt d := by
      intro ys
      induction ys with
      | nil => intro _ _ _ h; exact h
      | cons dt' rest' ih =>
        intro acc hOther hInner hacc
        simp only [List.foldl_cons]
        have hdt'_ne : dt'.name ≠ dt.name.pushNamespace c.nameHead :=
          hOther dt' List.mem_cons_self
        have hStep : ∃ d, (dtStep mono acc dt').getByKey
            (dt.name.pushNamespace c.nameHead) = some d ∧
            DtCompanionRewrittenFrom mono dt d := by
          by_cases hdt'_eq : dt' = dt
          · -- dt' = dt: re-insertion. Use dtStep_inserts_DtCompanionRewrittenFrom_self
            -- which produces the canonical form regardless of prior acc state.
            have hhc : c ∈ dt'.constructors := by rw [hdt'_eq]; exact hc
            have h := dtStep_inserts_DtCompanionRewrittenFrom_self mono acc dt' hhc
            -- Convert dt'.name to dt.name via hdt'_eq.
            obtain ⟨d, hget, hM⟩ := h
            refine ⟨d, ?_, ?_⟩
            · -- hget : ... .getByKey (dt'.name.pushNs c.nameHead) = some d
              -- goal : ... .getByKey (dt.name.pushNs c.nameHead) = some d
              rw [show dt.name = dt'.name from by rw [hdt'_eq]]
              exact hget
            · -- DtCompanionRewrittenFrom mono dt' d → DtCompanionRewrittenFrom mono dt d.
              rw [hdt'_eq] at hM
              exact hM
          · -- dt' ≠ dt: use preserves with hOtherInner for inner ctor disjointness.
            have hCtorNK : ∀ c2 ∈ dt'.constructors,
                dt'.name.pushNamespace c2.nameHead ≠ dt.name.pushNamespace c.nameHead :=
              hInner dt' List.mem_cons_self hdt'_eq
            exact dtStep_preserves_DtCompanionRewrittenFrom mono acc dt' dt
              hdt'_ne hCtorNK hacc
        exact ih _ (fun dt'' hdt'' => hOther dt'' (List.mem_cons_of_mem _ hdt''))
          (fun dt'' hdt'' => hInner dt'' (List.mem_cons_of_mem _ hdt''))
          hStep
    -- Now process hd then rest. Split on whether dt = hd or dt ∈ rest.
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · -- dt = hd: dtStep at hd inserts canonical form. Preserve through rest.
      -- Use hmem_hd to identify hd's role, but don't subst (dt is binding-bound).
      have hhc : c ∈ hd.constructors := by rw [← hmem_hd]; exact hc
      have h1 := dtStep_inserts_DtCompanionRewrittenFrom_self mono init hd hhc
      -- h1 : ∃ d, ... .getByKey (hd.name.pushNs c.nameHead) = some d ∧ DtCompanionRewrittenFrom mono hd d.
      -- Convert to dt-form via hmem_hd.
      have h1' : ∃ d, (dtStep mono init hd).getByKey
          (dt.name.pushNamespace c.nameHead) = some d ∧
          DtCompanionRewrittenFrom mono dt d := by
        rw [hmem_hd]
        exact h1
      apply hpreserve rest _ (fun dt' hdt' => hOtherDtNotKey dt' (List.mem_cons_of_mem _ hdt'))
        (fun dt' hdt' => hOtherInnerCtorNotKey dt' (List.mem_cons_of_mem _ hdt'))
        h1'
    · -- dt ∈ rest. dtStep at hd may or may not affect K.
      by_cases hhd_eq : hd = dt
      · have hhc : c ∈ hd.constructors := by rw [hhd_eq]; exact hc
        have h1 := dtStep_inserts_DtCompanionRewrittenFrom_self mono init hd hhc
        have h1' : ∃ d, (dtStep mono init hd).getByKey
            (dt.name.pushNamespace c.nameHead) = some d ∧
            DtCompanionRewrittenFrom mono dt d := by
          rw [← hhd_eq]
          exact h1
        apply hpreserve rest _ (fun dt' hdt' => hOtherDtNotKey dt' (List.mem_cons_of_mem _ hdt'))
          (fun dt' hdt' => hOtherInnerCtorNotKey dt' (List.mem_cons_of_mem _ hdt'))
          h1'
      · exact dtStep_foldl_list_inserts_DtCompanionRewrittenFrom mono hc rest
          (dtStep mono init hd) hmem_rest
          (fun dt' hdt' => hOtherDtNotKey dt' (List.mem_cons_of_mem _ hdt'))
          (fun dt' hdt' => hOtherInnerCtorNotKey dt' (List.mem_cons_of_mem _ hdt'))

/-- Strengthened version of `concretizeBuild_at_newDt_ctor_name`: identifies
the dt-companion at the .ctor entry as the canonical rewritten form of `dt`. -/
theorem concretizeBuild_at_newDt_ctor_name_dt_companion
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes)
    {c : Constructor} (hc : c ∈ dt.constructors)
    (hOtherDtNotKey : ∀ dt' ∈ newDataTypes,
      dt'.name ≠ dt.name.pushNamespace c.nameHead)
    (hOtherInnerCtorNotKey : ∀ dt' ∈ newDataTypes, dt' ≠ dt →
      ∀ c2 ∈ dt'.constructors,
        dt'.name.pushNamespace c2.nameHead ≠ dt.name.pushNamespace c.nameHead)
    (hFnNotKey : ∀ f ∈ newFunctions,
      f.name ≠ dt.name.pushNamespace c.nameHead) :
    ∃ d,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey
        (dt.name.pushNamespace c.nameHead) = some d ∧
      DtCompanionRewrittenFrom mono dt d := by
  rw [concretizeBuild_eq]
  -- Use dtStep_foldl_list_inserts_DtCompanionRewrittenFrom + fnStep preservation.
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  have hOther' : ∀ dt' ∈ newDataTypes.toList,
      dt'.name ≠ dt.name.pushNamespace c.nameHead :=
    fun dt' hdt' => hOtherDtNotKey dt' (Array.mem_toList_iff.mp hdt')
  have hInner' : ∀ dt' ∈ newDataTypes.toList, dt' ≠ dt →
      ∀ c2 ∈ dt'.constructors,
        dt'.name.pushNamespace c2.nameHead ≠ dt.name.pushNamespace c.nameHead :=
    fun dt' hdt' => hOtherInnerCtorNotKey dt' (Array.mem_toList_iff.mp hdt')
  rw [show (newDataTypes.foldl (dtStep mono)
        (typedDecls.pairs.foldl (srcStep typedDecls mono) default)
      : Typed.Decls) = newDataTypes.toList.foldl (dtStep mono)
        (typedDecls.pairs.foldl (srcStep typedDecls mono) default)
    from by rw [← Array.foldl_toList]]
  rw [show (newFunctions.foldl (fnStep typedDecls mono)
        (newDataTypes.toList.foldl (dtStep mono)
          (typedDecls.pairs.foldl (srcStep typedDecls mono) default))
      : Typed.Decls) = newFunctions.toList.foldl (fnStep typedDecls mono)
        (newDataTypes.toList.foldl (dtStep mono)
          (typedDecls.pairs.foldl (srcStep typedDecls mono) default))
    from by rw [← Array.foldl_toList]]
  have h2 := dtStep_foldl_list_inserts_DtCompanionRewrittenFrom mono hc
    newDataTypes.toList (typedDecls.pairs.foldl (srcStep typedDecls mono) default)
    hmem' hOther' hInner'
  obtain ⟨d, hget, hM⟩ := h2
  -- Generic fnStep fold preservation of DtCompanionRewrittenFrom.
  have hfn_pres : ∀ (xs : List Typed.Function) (acc : Typed.Decls)
      (_hno : ∀ f ∈ xs, f.name ≠ dt.name.pushNamespace c.nameHead)
      (_hacc : ∃ d, acc.getByKey (dt.name.pushNamespace c.nameHead) = some d ∧
        DtCompanionRewrittenFrom mono dt d),
    ∃ d, (xs.foldl (fnStep typedDecls mono) acc).getByKey
      (dt.name.pushNamespace c.nameHead) = some d ∧
      DtCompanionRewrittenFrom mono dt d := by
    intro xs
    induction xs with
    | nil => intro _ _ h; exact h
    | cons hd rest ih =>
      intro acc hno hacc
      simp only [List.foldl_cons]
      have hne : hd.name ≠ dt.name.pushNamespace c.nameHead :=
        hno hd List.mem_cons_self
      have hStep := fnStep_preserves_DtCompanionRewrittenFrom typedDecls mono acc hd dt
        hne hacc
      exact ih _ (fun f hf => hno f (List.mem_cons_of_mem _ hf)) hStep
  apply hfn_pres
  · intro f hf; exact hFnNotKey f (Array.mem_toList_iff.mp hf)
  · exact ⟨d, hget, hM⟩

/-- Key lemma for `concretize_produces_mono_correspondence`'s `dt_lifts` arm:
every newly-pushed datatype's name is keyed to a `.dataType` in
`concretizeBuild`'s output, under disjointness with newFunctions names. -/
theorem concretizeBuild_at_newDt_name
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ dt.name) :
    ∃ md_dt,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey dt.name =
        some (.dataType md_dt) := by
  rw [concretizeBuild_eq]
  have h2 := dtStep_foldl_inserts_at_dt_name mono newDataTypes
    (typedDecls.pairs.foldl (srcStep typedDecls mono) default) hmem hDtCtorNotKey
  exact fnStep_foldl_preserves_dataType_kind typedDecls mono newFunctions _ h2 hFnNotKey

/-- Key lemma for `concretize_produces_mono_correspondence`'s `fn_lifts` arm:
every newly-pushed function's name is keyed to a `.function` in
`concretizeBuild`'s output. The fnStep fold ALWAYS yields `.function` at any
`f.name` regardless of prior dtStep state (since fnStep insert overrides). -/
theorem concretizeBuild_at_newFn_name
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {f : Typed.Function} (hmem : f ∈ newFunctions) :
    ∃ md_f,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey f.name =
        some (.function md_f) := by
  rw [concretizeBuild_eq]
  exact fnStep_foldl_inserts_at_fn_name typedDecls mono newFunctions _ hmem

/-! #### Explicit-structure version of `concretizeBuild_at_newDt_name`.

Mirrors `concretizeBuild_at_typed_ctor_explicit_general` but for the
`.dataType`-at-newDt-name case. Carries length + per-position nameHead
correspondence between the resulting `md_dt` and the source `dt` (the newDt
processed by `dtStep`). -/

/-- Structural payload: `d` is `.dataType md_dt` with `md_dt.name = dt.name`,
constructors-list length-equal, and per-position `nameHead`-equal to `dt`'s
constructors. -/
def DtMatchesNH (dt : DataType) (d : Typed.Declaration) : Prop :=
  ∃ md_dt, d = .dataType md_dt ∧
    md_dt.name = dt.name ∧
    md_dt.constructors.length = dt.constructors.length ∧
    (∀ i (hi : i < dt.constructors.length)
        (hi' : i < md_dt.constructors.length),
      (md_dt.constructors[i]'hi').nameHead = (dt.constructors[i]'hi).nameHead)

/-- The literal `newDt = {dt with constructors := rewrittenCtors}` produced
by `dtStep mono _ dt` satisfies `DtMatchesNH dt`. -/
theorem DtMatchesNH_self
    (mono : MonoMap) (dt : DataType) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    DtMatchesNH dt (.dataType newDt) := by
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp only [List.length_map]
  · intro i hi _hi'
    simp only [List.getElem_map]

/-- Inner ctor-fold preserves `DtMatchesNH` at `g` when no inner ctor key
equals `g`. -/
theorem dtCtorFold_preserves_DtMatchesNH
    (mono : MonoMap) (dt : DataType) (newDt : DataType) (target_dt : DataType)
    {g : Global} :
    ∀ (cs : List Constructor) (acc : Typed.Decls)
      (_hCtorNotKey : ∀ c ∈ cs, dt.name.pushNamespace c.nameHead ≠ g)
      (_hacc : ∃ d, acc.getByKey g = some d ∧ DtMatchesNH target_dt d),
    ∃ d,
      (cs.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc).getByKey g = some d ∧ DtMatchesNH target_dt d
  | [], _, _, hacc => hacc
  | c :: rest, acc, hCtorNotKey, hacc => by
    simp only [List.foldl_cons]
    have hne : (dt.name.pushNamespace c.nameHead == g) = false := by
      rw [beq_eq_false_iff_ne]; exact hCtorNotKey c List.mem_cons_self
    have hacc' : ∃ d,
        (acc.insert (dt.name.pushNamespace c.nameHead)
          (.constructor newDt c)).getByKey g = some d ∧ DtMatchesNH target_dt d := by
      obtain ⟨d, hget, hM⟩ := hacc
      refine ⟨d, ?_, hM⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hget
    exact dtCtorFold_preserves_DtMatchesNH mono dt newDt target_dt rest _
      (fun c' hc' => hCtorNotKey c' (List.mem_cons_of_mem _ hc')) hacc'

/-- A single step of `dtStep` on `dt` (= target_dt) inserts `.dataType newDt`
at `dt.name` with the structural payload of `target_dt = dt`. -/
theorem dtStep_inserts_DtMatchesNH_self
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType) :
    ∃ d, (dtStep mono acc dt).getByKey dt.name = some d ∧ DtMatchesNH dt d := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- After dt.name insert: value is `.dataType newDt` satisfying `DtMatchesNH dt`.
  have hacc_after : ∃ d,
      (acc.insert dt.name (Typed.Declaration.dataType newDt)).getByKey dt.name =
        some d ∧ DtMatchesNH dt d := by
    refine ⟨.dataType newDt, IndexMap.getByKey_insert_self _ _ _, ?_⟩
    exact DtMatchesNH_self mono dt
  -- Inner ctor fold preserves: each inner-key is `dt.name.pushNamespace c.nameHead`
  -- which differs from `dt.name` by `Global.ne_pushNamespace`.
  have hCtorNotKey : ∀ c ∈ rewrittenCtors,
      dt.name.pushNamespace c.nameHead ≠ dt.name :=
    fun c _ => (Global.ne_pushNamespace dt.name c.nameHead).symm
  exact dtCtorFold_preserves_DtMatchesNH mono dt newDt dt rewrittenCtors _
    hCtorNotKey hacc_after

/-- A single step of `dtStep` on `dt'` preserves `DtMatchesNH target_dt` at
`g` when `dt'.name ≠ g` (so the outer insert misses `g`) and no inner ctor
key of `dt'` equals `g`. -/
theorem dtStep_preserves_DtMatchesNH
    (mono : MonoMap) (acc : Typed.Decls) (dt' : DataType) (target_dt : DataType)
    {g : Global}
    (hdt'_ne : dt'.name ≠ g)
    (hCtorNotKey : ∀ c ∈ dt'.constructors, dt'.name.pushNamespace c.nameHead ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ DtMatchesNH target_dt d) :
    ∃ d, (dtStep mono acc dt').getByKey g = some d ∧ DtMatchesNH target_dt d := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt'.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt' : DataType := { dt' with constructors := rewrittenCtors }
  -- After outer insert at dt'.name (≠ g), preserved.
  have hbeq_dt' : (dt'.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hdt'_ne
  have hacc_after : ∃ d,
      (acc.insert dt'.name (Typed.Declaration.dataType newDt')).getByKey g =
        some d ∧ DtMatchesNH target_dt d := by
    obtain ⟨d, hget, hM⟩ := hacc
    refine ⟨d, ?_, hM⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt']
    exact hget
  -- Inner ctor fold preserves; rewrittenCtors share nameHeads with dt'.constructors.
  have hCtorNotKey' : ∀ c ∈ rewrittenCtors,
      dt'.name.pushNamespace c.nameHead ≠ g := by
    intro c hc
    have hmap : c ∈ dt'.constructors.map (fun c' =>
        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }) := hc
    obtain ⟨c_orig, hc_orig_mem, hc_orig_eq⟩ := List.mem_map.mp hmap
    have hnh : c.nameHead = c_orig.nameHead := by rw [← hc_orig_eq]
    rw [hnh]
    exact hCtorNotKey c_orig hc_orig_mem
  exact dtCtorFold_preserves_DtMatchesNH mono dt' newDt' target_dt rewrittenCtors _
    hCtorNotKey' hacc_after

/-- `dtStep` foldl over a list inserts `.dataType` with `DtMatchesNH dt` at
`dt.name` for `dt ∈ xs`, under `hCtorNotKey` (no newDt's ctor inner-key equals
`dt.name`) and `hOtherDtNotKey` (no OTHER dt' ∈ xs has `dt'.name = dt.name`). -/
theorem dtStep_foldl_list_inserts_DtMatchesNH_at_dt_name
    (mono : MonoMap) {dt : DataType} :
    ∀ (xs : List DataType) (init : Typed.Decls)
      (_hmem : dt ∈ xs)
      (_hCtorNotKey : ∀ dt' ∈ xs, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ dt.name)
      (_hOtherDtNotKey : ∀ dt' ∈ xs, dt' ≠ dt → dt'.name ≠ dt.name),
    ∃ d, (xs.foldl (dtStep mono) init).getByKey dt.name = some d ∧
      DtMatchesNH dt d
  | [], _, hmem, _, _ => by cases hmem
  | hd :: rest, init, hmem, hCtorNotKey, hOtherDtNotKey => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · subst hmem_hd
      have h1 := dtStep_inserts_DtMatchesNH_self mono init dt
      have hrest_ctor : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := by
        intro dt' hdt' c hc
        exact hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      -- For each dt' ∈ rest with dt' ≠ dt, dt'.name ≠ dt.name.
      -- We strengthen: ALL dt' ∈ rest have dt'.name ≠ dt.name OR dt' = dt.
      -- The dt' = dt case is handled by structural equality: dtStep on the
      -- same dt produces the same newDt, so DtMatchesNH dt is preserved.
      -- Wait — but if dt' = dt, then dt'.name = dt.name, so the hypothesis
      -- hOtherDtNotKey doesn't fire (dt' ≠ dt is false → vacuous). To handle
      -- the dt' = dt case, observe: dtStep mono _ dt produces value with
      -- DtMatchesNH dt (by dtStep_inserts_DtMatchesNH_self). So a duplicate dt
      -- in rest would just re-overwrite with the same DtMatchesNH-correct value.
      have hrest_dt_struct : ∀ dt' ∈ rest, dt' = dt ∨ dt'.name ≠ dt.name := by
        intro dt' hdt'
        by_cases h : dt' = dt
        · left; exact h
        · right; exact hOtherDtNotKey dt' (List.mem_cons_of_mem _ hdt') h
      clear hCtorNotKey hOtherDtNotKey
      -- Generic preservation across rest.
      have hpreserve : ∀ (ys : List DataType) (acc : Typed.Decls),
          (∀ dt' ∈ ys, ∀ c ∈ dt'.constructors,
            dt'.name.pushNamespace c.nameHead ≠ dt.name) →
          (∀ dt' ∈ ys, dt' = dt ∨ dt'.name ≠ dt.name) →
          (∃ d, acc.getByKey dt.name = some d ∧ DtMatchesNH dt d) →
          ∃ d, (ys.foldl (dtStep mono) acc).getByKey dt.name = some d ∧
            DtMatchesNH dt d := by
        intro ys
        induction ys with
        | nil => intro acc _ _ h; exact h
        | cons dt' rest' ih =>
          intro acc hCtorAll hOrAll h
          simp only [List.foldl_cons]
          have hCtorNotKey_dt' : ∀ c ∈ dt'.constructors,
              dt'.name.pushNamespace c.nameHead ≠ dt.name :=
            hCtorAll dt' List.mem_cons_self
          have hOr_dt' : dt' = dt ∨ dt'.name ≠ dt.name :=
            hOrAll dt' List.mem_cons_self
          -- Step on dt': either dt' = dt (overwrites with self DtMatchesNH-good
          -- value) or dt'.name ≠ dt.name (outer insert misses dt.name).
          have hStep : ∃ d, (dtStep mono acc dt').getByKey dt.name = some d ∧
              DtMatchesNH dt d := by
            rcases hOr_dt' with hdteq | hne
            · -- dt' = dt: dtStep on dt overwrites with `.dataType newDt`
              -- satisfying DtMatchesNH dt.
              subst hdteq
              exact dtStep_inserts_DtMatchesNH_self mono acc dt'
            · exact dtStep_preserves_DtMatchesNH mono acc dt' dt hne
                hCtorNotKey_dt' h
          exact ih (dtStep mono acc dt')
            (fun dt'' hdt'' c hc => hCtorAll dt'' (List.mem_cons_of_mem _ hdt'') c hc)
            (fun dt'' hdt'' => hOrAll dt'' (List.mem_cons_of_mem _ hdt''))
            hStep
      exact hpreserve rest _ hrest_ctor hrest_dt_struct h1
    · -- dt ∈ rest. Use IH on rest.
      have hrest_ctor : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := by
        intro dt' hdt' c hc
        exact hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      have hrest_other : ∀ dt' ∈ rest, dt' ≠ dt → dt'.name ≠ dt.name := by
        intro dt' hdt' hne
        exact hOtherDtNotKey dt' (List.mem_cons_of_mem _ hdt') hne
      exact dtStep_foldl_list_inserts_DtMatchesNH_at_dt_name mono rest
        (dtStep mono init hd) hmem_rest hrest_ctor hrest_other

/-- `dtStep` Array foldl inserts `.dataType` with `DtMatchesNH dt` at `dt.name`
for `dt ∈ newDataTypes`, under disjointness hypotheses. -/
theorem dtStep_foldl_inserts_DtMatchesNH_at_dt_name
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name)
    (hOtherDtNotKey : ∀ dt' ∈ newDataTypes, dt' ≠ dt → dt'.name ≠ dt.name) :
    ∃ d, (newDataTypes.foldl (dtStep mono) init).getByKey dt.name = some d ∧
      DtMatchesNH dt d := by
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  have hCtor' : ∀ dt' ∈ newDataTypes.toList, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name := by
    intro dt' hdt'; exact hDtCtorNotKey dt' (Array.mem_toList_iff.mp hdt')
  have hOther' : ∀ dt' ∈ newDataTypes.toList, dt' ≠ dt → dt'.name ≠ dt.name := by
    intro dt' hdt'; exact hOtherDtNotKey dt' (Array.mem_toList_iff.mp hdt')
  exact dtStep_foldl_list_inserts_DtMatchesNH_at_dt_name mono
    newDataTypes.toList init hmem' hCtor' hOther'

/-- `fnStep` preserves `DtMatchesNH` at `g` under `f.name ≠ g`. -/
theorem fnStep_preserves_DtMatchesNH
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    (target_dt : DataType)
    {g : Global} (hfn_ne : f.name ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ DtMatchesNH target_dt d) :
    ∃ d, (fnStep decls mono acc f).getByKey g = some d ∧
      DtMatchesNH target_dt d := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨d, hget, hM⟩ := hacc
  refine ⟨d, ?_, hM⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

/-- `fnStep` Array foldl preserves `DtMatchesNH` at `g` under `hFnNotKey`. -/
theorem fnStep_foldl_preserves_DtMatchesNH
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) (target_dt : DataType) {g : Global}
    (hinit : ∃ d, init.getByKey g = some d ∧ DtMatchesNH target_dt d)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ d, (newFunctions.foldl (fnStep decls mono) init).getByKey g = some d ∧
      DtMatchesNH target_dt d := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ d, acc.getByKey g = some d ∧ DtMatchesNH target_dt d) hinit
  intro i acc hinv
  have hfn_ne : (newFunctions[i.val]'i.isLt).name ≠ g :=
    hFnNotKey _ (Array.getElem_mem _)
  exact fnStep_preserves_DtMatchesNH decls mono acc _ target_dt hfn_ne hinv

/-! #### Full structural witness `DtRewrittenFrom`. Mirrors `DtMatchesNH`
but carries per-position `argTypes` rewriting (mapped via `rewriteTyp ∅ mono`)
from the source `dt`'s constructors. Strictly stronger. -/

/-- A typed declaration is `.dataType md_dt` with `md_dt.constructors` being
exactly `dt.constructors.map (fun c => { c with argTypes := c.argTypes.map (rewriteTyp ∅ mono) })`. -/
def DtRewrittenFrom (mono : MonoMap) (dt : DataType) (d : Typed.Declaration) : Prop :=
  ∃ md_dt, d = .dataType md_dt ∧
    md_dt.name = dt.name ∧
    md_dt.params = dt.params ∧
    md_dt.constructors = dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) }

/-- The literal `newDt = {dt with constructors := rewrittenCtors}` produced
by `dtStep mono _ dt` satisfies `DtRewrittenFrom mono dt`. -/
theorem DtRewrittenFrom_self
    (mono : MonoMap) (dt : DataType) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    DtRewrittenFrom mono dt (.dataType newDt) :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- Inner ctor-fold preserves `DtRewrittenFrom` at `g` when no inner ctor key
equals `g`. -/
theorem dtCtorFold_preserves_DtRewrittenFrom
    (mono : MonoMap) (dt : DataType) (newDt : DataType) (target_dt : DataType)
    {g : Global} :
    ∀ (cs : List Constructor) (acc : Typed.Decls)
      (_hCtorNotKey : ∀ c ∈ cs, dt.name.pushNamespace c.nameHead ≠ g)
      (_hacc : ∃ d, acc.getByKey g = some d ∧ DtRewrittenFrom mono target_dt d),
    ∃ d,
      (cs.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc).getByKey g = some d ∧ DtRewrittenFrom mono target_dt d
  | [], _, _, hacc => hacc
  | c :: rest, acc, hCtorNotKey, hacc => by
    simp only [List.foldl_cons]
    have hne : (dt.name.pushNamespace c.nameHead == g) = false := by
      rw [beq_eq_false_iff_ne]; exact hCtorNotKey c List.mem_cons_self
    have hacc' : ∃ d,
        (acc.insert (dt.name.pushNamespace c.nameHead)
          (.constructor newDt c)).getByKey g = some d ∧
          DtRewrittenFrom mono target_dt d := by
      obtain ⟨d, hget, hM⟩ := hacc
      refine ⟨d, ?_, hM⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hget
    exact dtCtorFold_preserves_DtRewrittenFrom mono dt newDt target_dt rest _
      (fun c' hc' => hCtorNotKey c' (List.mem_cons_of_mem _ hc')) hacc'

/-- `dtStep` on `dt` (= target_dt) inserts `.dataType newDt` at `dt.name`
satisfying `DtRewrittenFrom mono dt`. -/
theorem dtStep_inserts_DtRewrittenFrom_self
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType) :
    ∃ d, (dtStep mono acc dt).getByKey dt.name = some d ∧
      DtRewrittenFrom mono dt d := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  have hacc_after : ∃ d,
      (acc.insert dt.name (Typed.Declaration.dataType newDt)).getByKey dt.name =
        some d ∧ DtRewrittenFrom mono dt d :=
    ⟨.dataType newDt, IndexMap.getByKey_insert_self _ _ _, DtRewrittenFrom_self mono dt⟩
  have hCtorNotKey : ∀ c ∈ rewrittenCtors,
      dt.name.pushNamespace c.nameHead ≠ dt.name :=
    fun c _ => (Global.ne_pushNamespace dt.name c.nameHead).symm
  exact dtCtorFold_preserves_DtRewrittenFrom mono dt newDt dt rewrittenCtors _
    hCtorNotKey hacc_after

/-- A single step of `dtStep` on `dt'` preserves `DtRewrittenFrom mono target_dt`
at `g` when `dt'.name ≠ g` and no inner ctor key of `dt'` equals `g`. -/
theorem dtStep_preserves_DtRewrittenFrom
    (mono : MonoMap) (acc : Typed.Decls) (dt' : DataType) (target_dt : DataType)
    {g : Global}
    (hdt'_ne : dt'.name ≠ g)
    (hCtorNotKey : ∀ c ∈ dt'.constructors, dt'.name.pushNamespace c.nameHead ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ DtRewrittenFrom mono target_dt d) :
    ∃ d, (dtStep mono acc dt').getByKey g = some d ∧
      DtRewrittenFrom mono target_dt d := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt'.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt' : DataType := { dt' with constructors := rewrittenCtors }
  have hbeq_dt' : (dt'.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hdt'_ne
  have hacc_after : ∃ d,
      (acc.insert dt'.name (Typed.Declaration.dataType newDt')).getByKey g =
        some d ∧ DtRewrittenFrom mono target_dt d := by
    obtain ⟨d, hget, hM⟩ := hacc
    refine ⟨d, ?_, hM⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt']
    exact hget
  have hCtorNotKey' : ∀ c ∈ rewrittenCtors,
      dt'.name.pushNamespace c.nameHead ≠ g := by
    intro c hc
    have hmap : c ∈ dt'.constructors.map (fun c' =>
        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }) := hc
    obtain ⟨c_orig, hc_orig_mem, hc_orig_eq⟩ := List.mem_map.mp hmap
    have hnh : c.nameHead = c_orig.nameHead := by rw [← hc_orig_eq]
    rw [hnh]
    exact hCtorNotKey c_orig hc_orig_mem
  exact dtCtorFold_preserves_DtRewrittenFrom mono dt' newDt' target_dt rewrittenCtors _
    hCtorNotKey' hacc_after

/-- `dtStep` foldl over a list inserts `.dataType` with `DtRewrittenFrom mono dt`
at `dt.name` for `dt ∈ xs`, under `hCtorNotKey` and `hOtherDtNotKey`. -/
theorem dtStep_foldl_list_inserts_DtRewrittenFrom_at_dt_name
    (mono : MonoMap) {dt : DataType} :
    ∀ (xs : List DataType) (init : Typed.Decls)
      (_hmem : dt ∈ xs)
      (_hCtorNotKey : ∀ dt' ∈ xs, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ dt.name)
      (_hOtherDtNotKey : ∀ dt' ∈ xs, dt' ≠ dt → dt'.name ≠ dt.name),
    ∃ d, (xs.foldl (dtStep mono) init).getByKey dt.name = some d ∧
      DtRewrittenFrom mono dt d
  | [], _, hmem, _, _ => by cases hmem
  | hd :: rest, init, hmem, hCtorNotKey, hOtherDtNotKey => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · subst hmem_hd
      have h1 := dtStep_inserts_DtRewrittenFrom_self mono init dt
      have hrest_dt_struct : ∀ dt' ∈ rest, dt' = dt ∨ dt'.name ≠ dt.name := by
        intro dt' hdt'
        by_cases h : dt' = dt
        · left; exact h
        · right; exact hOtherDtNotKey dt' (List.mem_cons_of_mem _ hdt') h
      have hpreserve : ∀ (ys : List DataType) (acc : Typed.Decls),
          (∀ dt' ∈ ys, ∀ c ∈ dt'.constructors,
            dt'.name.pushNamespace c.nameHead ≠ dt.name) →
          (∀ dt' ∈ ys, dt' = dt ∨ dt'.name ≠ dt.name) →
          (∃ d, acc.getByKey dt.name = some d ∧ DtRewrittenFrom mono dt d) →
          ∃ d, (ys.foldl (dtStep mono) acc).getByKey dt.name = some d ∧
            DtRewrittenFrom mono dt d := by
        intro ys
        induction ys with
        | nil => intro acc _ _ h; exact h
        | cons dt' rest' ih =>
          intro acc hCtorAll hOrAll h
          simp only [List.foldl_cons]
          have hCtorNotKey_dt' : ∀ c ∈ dt'.constructors,
              dt'.name.pushNamespace c.nameHead ≠ dt.name :=
            hCtorAll dt' List.mem_cons_self
          have hOr_dt' : dt' = dt ∨ dt'.name ≠ dt.name :=
            hOrAll dt' List.mem_cons_self
          have hStep : ∃ d, (dtStep mono acc dt').getByKey dt.name = some d ∧
              DtRewrittenFrom mono dt d := by
            rcases hOr_dt' with hdteq | hne
            · subst hdteq
              exact dtStep_inserts_DtRewrittenFrom_self mono acc dt'
            · exact dtStep_preserves_DtRewrittenFrom mono acc dt' dt hne
                hCtorNotKey_dt' h
          exact ih (dtStep mono acc dt')
            (fun dt'' hdt'' c hc => hCtorAll dt'' (List.mem_cons_of_mem _ hdt'') c hc)
            (fun dt'' hdt'' => hOrAll dt'' (List.mem_cons_of_mem _ hdt''))
            hStep
      have hCtor_rest : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := fun dt' hdt' c hc =>
        hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      exact hpreserve rest _ hCtor_rest hrest_dt_struct h1
    · have hCtor_rest : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := fun dt' hdt' c hc =>
        hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      have hOther_rest : ∀ dt' ∈ rest, dt' ≠ dt → dt'.name ≠ dt.name :=
        fun dt' hdt' hne => hOtherDtNotKey dt' (List.mem_cons_of_mem _ hdt') hne
      exact dtStep_foldl_list_inserts_DtRewrittenFrom_at_dt_name mono rest
        (dtStep mono init hd) hmem_rest hCtor_rest hOther_rest

theorem dtStep_foldl_inserts_DtRewrittenFrom_at_dt_name
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name)
    (hOtherDtNotKey : ∀ dt' ∈ newDataTypes, dt' ≠ dt → dt'.name ≠ dt.name) :
    ∃ d, (newDataTypes.foldl (dtStep mono) init).getByKey dt.name = some d ∧
      DtRewrittenFrom mono dt d := by
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  have hCtor' : ∀ dt' ∈ newDataTypes.toList, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name := by
    intro dt' hdt'; exact hDtCtorNotKey dt' (Array.mem_toList_iff.mp hdt')
  have hOther' : ∀ dt' ∈ newDataTypes.toList, dt' ≠ dt → dt'.name ≠ dt.name := by
    intro dt' hdt'; exact hOtherDtNotKey dt' (Array.mem_toList_iff.mp hdt')
  exact dtStep_foldl_list_inserts_DtRewrittenFrom_at_dt_name mono
    newDataTypes.toList init hmem' hCtor' hOther'

theorem fnStep_preserves_DtRewrittenFrom
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    (target_dt : DataType)
    {g : Global} (hfn_ne : f.name ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ DtRewrittenFrom mono target_dt d) :
    ∃ d, (fnStep decls mono acc f).getByKey g = some d ∧
      DtRewrittenFrom mono target_dt d := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨d, hget, hM⟩ := hacc
  refine ⟨d, ?_, hM⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

theorem fnStep_foldl_preserves_DtRewrittenFrom
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) (target_dt : DataType) {g : Global}
    (hinit : ∃ d, init.getByKey g = some d ∧ DtRewrittenFrom mono target_dt d)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ d, (newFunctions.foldl (fnStep decls mono) init).getByKey g = some d ∧
      DtRewrittenFrom mono target_dt d := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ d, acc.getByKey g = some d ∧ DtRewrittenFrom mono target_dt d) hinit
  intro i acc hinv
  have hfn_ne : (newFunctions[i.val]'i.isLt).name ≠ g :=
    hFnNotKey _ (Array.getElem_mem _)
  exact fnStep_preserves_DtRewrittenFrom decls mono acc _ target_dt hfn_ne hinv

/-- Stronger explicit-structure version of `concretizeBuild_at_newDt_name_explicit`:
in addition to length+nameHead, gives the FULL `argTypes` rewriting per ctor. -/
theorem concretizeBuild_at_newDt_name_full_explicit
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ dt.name)
    (hOtherDtNotKey : ∀ dt' ∈ newDataTypes, dt' ≠ dt → dt'.name ≠ dt.name) :
    ∃ md_dt,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey dt.name =
        some (.dataType md_dt) ∧
      md_dt.name = dt.name ∧
      md_dt.params = dt.params ∧
      md_dt.constructors = dt.constructors.map fun c =>
        { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) } := by
  rw [concretizeBuild_eq]
  have h2 := dtStep_foldl_inserts_DtRewrittenFrom_at_dt_name mono newDataTypes
    (typedDecls.pairs.foldl (srcStep typedDecls mono) default) hmem hDtCtorNotKey
    hOtherDtNotKey
  have h3 := fnStep_foldl_preserves_DtRewrittenFrom typedDecls mono newFunctions _
    dt h2 hFnNotKey
  obtain ⟨d, hget, hM⟩ := h3
  obtain ⟨md_dt, hd_eq, hName, hParams, hCtors⟩ := hM
  refine ⟨md_dt, ?_, hName, hParams, hCtors⟩
  rw [hget, hd_eq]

/-- Explicit-structure version of `concretizeBuild_at_newDt_name`: under the
disjointness hypotheses + uniqueness within `newDataTypes` (any other newDt
with the same name as `dt` is structurally equal to `dt`), the
`concretizeBuild` result at `dt.name` carries `DtMatchesNH dt` (length and
per-position nameHead correspondence with `dt`'s constructors). -/
theorem concretizeBuild_at_newDt_name_explicit
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ dt.name)
    (hOtherDtNotKey : ∀ dt' ∈ newDataTypes, dt' ≠ dt → dt'.name ≠ dt.name) :
    ∃ md_dt,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey dt.name =
        some (.dataType md_dt) ∧
      md_dt.name = dt.name ∧
      md_dt.constructors.length = dt.constructors.length ∧
      (∀ i (hi : i < dt.constructors.length)
          (hi' : i < md_dt.constructors.length),
        (md_dt.constructors[i]'hi').nameHead = (dt.constructors[i]'hi).nameHead) := by
  rw [concretizeBuild_eq]
  have h2 := dtStep_foldl_inserts_DtMatchesNH_at_dt_name mono newDataTypes
    (typedDecls.pairs.foldl (srcStep typedDecls mono) default) hmem hDtCtorNotKey
    hOtherDtNotKey
  have h3 := fnStep_foldl_preserves_DtMatchesNH typedDecls mono newFunctions _
    dt h2 hFnNotKey
  obtain ⟨d, hget, hM⟩ := h3
  obtain ⟨md_dt, hd_eq, hName, hLen, hPos⟩ := hM
  refine ⟨md_dt, ?_, hName, hLen, hPos⟩
  rw [hget, hd_eq]

/-! #### Full structural witness `FnRewrittenFrom`. Mirrors `DtRewrittenFrom`
but for newFunctions: carries the explicit `inputs.map (·.snd ↦ rewriteTyp ∅ mono ·)`
and `rewriteTyp ∅ mono output` rewriting. -/

/-- A typed declaration is `.function md_f` where `md_f.inputs` and
`md_f.output` are exactly `f.inputs` and `f.output` rewritten via
`rewriteTyp ∅ mono`. -/
def FnRewrittenFrom (decls : Typed.Decls) (mono : MonoMap)
    (f : Typed.Function) (d : Typed.Declaration) : Prop :=
  ∃ md_f, d = .function md_f ∧
    md_f.name = f.name ∧
    md_f.inputs = f.inputs.map (fun (l, t) => (l, rewriteTyp (fun _ => none) mono t)) ∧
    md_f.output = rewriteTyp (fun _ => none) mono f.output ∧
    md_f.body = rewriteTypedTerm decls (fun _ => none) mono f.body

/-- A single `fnStep` on `f` inserts `.function newF` at `f.name` with
`FnRewrittenFrom decls mono f`. -/
theorem fnStep_inserts_FnRewrittenFrom_self
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function) :
    ∃ d, (fnStep decls mono acc f).getByKey f.name = some d ∧
      FnRewrittenFrom decls mono f d := by
  unfold fnStep
  let emptySubst : Global → Option Typ := fun _ => none
  let newF : Typed.Function :=
    { f with
      inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
      output := rewriteTyp emptySubst mono f.output,
      body := rewriteTypedTerm decls emptySubst mono f.body }
  refine ⟨.function newF, IndexMap.getByKey_insert_self _ _ _, ?_⟩
  exact ⟨newF, rfl, rfl, rfl, rfl, rfl⟩

/-- A single `fnStep` on `f'` preserves `FnRewrittenFrom decls mono target_f` at `g`
when `f'.name ≠ g`. -/
theorem fnStep_preserves_FnRewrittenFrom
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f' : Typed.Function)
    (target_f : Typed.Function)
    {g : Global} (hfn_ne : f'.name ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ FnRewrittenFrom decls mono target_f d) :
    ∃ d, (fnStep decls mono acc f').getByKey g = some d ∧
      FnRewrittenFrom decls mono target_f d := by
  unfold fnStep
  have hbeq : (f'.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨d, hget, hM⟩ := hacc
  refine ⟨d, ?_, hM⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

/-- `fnStep` foldl over a list preserves `FnRewrittenFrom mono f` at `f.name`
under: `f ∈ xs` and any other f' ∈ xs has either f' = f (same insert) or
f'.name ≠ f.name (insert misses). -/
theorem fnStep_foldl_list_inserts_FnRewrittenFrom_at_fn_name
    (decls : Typed.Decls) (mono : MonoMap) {f : Typed.Function} :
    ∀ (xs : List Typed.Function) (init : Typed.Decls)
      (_hmem : f ∈ xs)
      (_hOtherFnNotKey : ∀ f' ∈ xs, f' ≠ f → f'.name ≠ f.name),
    ∃ d, (xs.foldl (fnStep decls mono) init).getByKey f.name = some d ∧
      FnRewrittenFrom decls mono f d
  | [], _, hmem, _ => by cases hmem
  | hd :: rest, init, hmem, hOtherFnNotKey => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · subst hmem_hd
      have h1 := fnStep_inserts_FnRewrittenFrom_self decls mono init f
      have hrest_struct : ∀ f' ∈ rest, f' = f ∨ f'.name ≠ f.name := by
        intro f' hf'
        by_cases h : f' = f
        · left; exact h
        · right; exact hOtherFnNotKey f' (List.mem_cons_of_mem _ hf') h
      have hpreserve : ∀ (ys : List Typed.Function) (acc : Typed.Decls),
          (∀ f' ∈ ys, f' = f ∨ f'.name ≠ f.name) →
          (∃ d, acc.getByKey f.name = some d ∧ FnRewrittenFrom decls mono f d) →
          ∃ d, (ys.foldl (fnStep decls mono) acc).getByKey f.name = some d ∧
            FnRewrittenFrom decls mono f d := by
        intro ys
        induction ys with
        | nil => intro acc _ h; exact h
        | cons f' rest' ih =>
          intro acc hOrAll h
          simp only [List.foldl_cons]
          have hOr_f' : f' = f ∨ f'.name ≠ f.name :=
            hOrAll f' List.mem_cons_self
          have hStep : ∃ d, (fnStep decls mono acc f').getByKey f.name = some d ∧
              FnRewrittenFrom decls mono f d := by
            rcases hOr_f' with hfeq | hne
            · subst hfeq
              exact fnStep_inserts_FnRewrittenFrom_self decls mono acc f'
            · exact fnStep_preserves_FnRewrittenFrom decls mono acc f' f hne h
          exact ih (fnStep decls mono acc f')
            (fun f'' hf'' => hOrAll f'' (List.mem_cons_of_mem _ hf''))
            hStep
      exact hpreserve rest _ hrest_struct h1
    · have hOther_rest : ∀ f' ∈ rest, f' ≠ f → f'.name ≠ f.name :=
        fun f' hf' hne => hOtherFnNotKey f' (List.mem_cons_of_mem _ hf') hne
      exact fnStep_foldl_list_inserts_FnRewrittenFrom_at_fn_name decls mono rest
        (fnStep decls mono init hd) hmem_rest hOther_rest

theorem fnStep_foldl_inserts_FnRewrittenFrom_at_fn_name
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {f : Typed.Function} (hmem : f ∈ newFunctions)
    (hOtherFnNotKey : ∀ f' ∈ newFunctions, f' ≠ f → f'.name ≠ f.name) :
    ∃ d, (newFunctions.foldl (fnStep decls mono) init).getByKey f.name = some d ∧
      FnRewrittenFrom decls mono f d := by
  rw [← Array.foldl_toList]
  have hmem' : f ∈ newFunctions.toList := Array.mem_toList_iff.mpr hmem
  have hOther' : ∀ f' ∈ newFunctions.toList, f' ≠ f → f'.name ≠ f.name :=
    fun f' hf' => hOtherFnNotKey f' (Array.mem_toList_iff.mp hf')
  exact fnStep_foldl_list_inserts_FnRewrittenFrom_at_fn_name decls mono
    newFunctions.toList init hmem' hOther'

/-- Stronger explicit-structure version of `concretizeBuild_at_newFn_name`:
gives the FULL `inputs`/`output`/`body` rewriting per fn. -/
theorem concretizeBuild_at_newFn_name_full_explicit
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {f : Typed.Function} (hmem : f ∈ newFunctions)
    (hOtherFnNotKey : ∀ f' ∈ newFunctions, f' ≠ f → f'.name ≠ f.name) :
    ∃ md_f,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey f.name =
        some (.function md_f) ∧
      md_f.name = f.name ∧
      md_f.inputs = f.inputs.map (fun (l, t) => (l, rewriteTyp (fun _ => none) mono t)) ∧
      md_f.output = rewriteTyp (fun _ => none) mono f.output ∧
      md_f.body = rewriteTypedTerm typedDecls (fun _ => none) mono f.body := by
  rw [concretizeBuild_eq]
  have h := fnStep_foldl_inserts_FnRewrittenFrom_at_fn_name typedDecls mono newFunctions
    (newDataTypes.foldl (dtStep mono)
      (typedDecls.pairs.foldl (srcStep typedDecls mono) default))
    hmem hOtherFnNotKey
  obtain ⟨d, hget, hM⟩ := h
  obtain ⟨md_f, hd_eq, hName, hInputs, hOutput, hBody⟩ := hM
  refine ⟨md_f, ?_, hName, hInputs, hOutput, hBody⟩
  rw [hget, hd_eq]

/-! #### Single-key entry-restricted explicit-structure variant.

Mirror of `concretizeBuild_at_typed_ctor_explicit_general` but with
**single-key** params hypothesis (`td_dt.params = []` for the queried `g`)
and **`ConcretizeUniqueNames`** in lieu of universal `params_empty`. The
universal-`params_empty` consumers in `_explicit_general` (deriving
`hDtNotKey`/`hFnNotKey` and the `hPerDtWit` builder's `args = #[]` step)
are replaced by `ConcretizeUniqueNames` applied to a colliding
`concretizeName` equation against `concretizeName _ #[]`. This is the
entry-restricted variant referenced from `compile_correct`'s
`hCtorAgreesAll`-index discharge — the per-key `dt_src.params = []`
hypothesis is derivable at the call site via `concretizeBuild_ctor_origin`'s
2-way classification (origin 1 directly, origin 4 contradicted via
`mkDecls_ctor_companion` + uniqueness). -/
theorem concretizeBuild_at_typed_ctor_at_entry_fwd
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {drained : DrainState}
    (hdrain : concretizeDrain typedDecls (concretizeDrainFuel typedDecls)
      { pending := concretizeSeed typedDecls, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } = .ok drained)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hUniqueNames : Typed.Decls.ConcretizeUniqueNames typedDecls)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hg_pushed : g = td_dt.name.pushNamespace td_c.nameHead)
    (hget : typedDecls.getByKey g = some (.constructor td_dt td_c))
    (hdt_companion : typedDecls.getByKey td_dt.name = some (.dataType td_dt))
    (hdt_params : td_dt.params = [])
    (_hc_mem : td_c ∈ td_dt.constructors)
    (hdt_distinct : ∀ i j (hi : i < td_dt.constructors.length)
                              (hj : j < td_dt.constructors.length),
        (td_dt.constructors[i]'hi).nameHead = (td_dt.constructors[j]'hj).nameHead → i = j) :
    ∃ (md_dt : DataType) (md_c : Constructor),
      (concretizeBuild typedDecls drained.mono drained.newFunctions
          drained.newDataTypes).getByKey g = some (.constructor md_dt md_c) ∧
      md_dt.constructors.length = td_dt.constructors.length ∧
      md_c.nameHead = td_c.nameHead ∧
      (∀ i (hi : i < td_dt.constructors.length),
        ∃ hi' : i < md_dt.constructors.length,
        (md_dt.constructors[i]'hi').nameHead = (td_dt.constructors[i]'hi).nameHead) ∧
      (∀ i (hi : i < td_dt.constructors.length),
        (td_dt.constructors[i]'hi) = td_c → ∃ hi' : i < md_dt.constructors.length,
        (md_dt.constructors[i]'hi') = md_c) := by
  -- StrongNewNameShape preserved through drain.
  have hStrong := concretize_drain_preserves_StrongNewNameShape _ _
    (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  -- step4Lower keys-iff for lifting from build to concDecls.
  have hconc_orig := hconc
  unfold Typed.Decls.concretize at hconc_orig
  simp only [bind, Except.bind] at hconc_orig
  rw [hdrain] at hconc_orig
  have hkeys_iff := concretize_step_4_keys_of_fold step4Lower
    step4Lower_inserts hconc_orig
  -- Helper: lift `containsKey` on the build to `getByKey ≠ none` on concDecls.
  have hbuild_to_conc : ∀ name, (concretizeBuild typedDecls drained.mono
      drained.newFunctions drained.newDataTypes).getByKey name ≠ none →
      ∃ d, concDecls.getByKey name = some d := by
    intro name hbuild
    have hBuildContains : (concretizeBuild typedDecls drained.mono
        drained.newFunctions drained.newDataTypes).containsKey name := by
      rw [← IndexMap.getByKey_ne_none_iff_containsKey]; exact hbuild
    have hconc_contains : concDecls.containsKey name := (hkeys_iff name).mp hBuildContains
    have hconc_get_ne : concDecls.getByKey name ≠ none := by
      rw [IndexMap.getByKey_ne_none_iff_containsKey]; exact hconc_contains
    cases hg : concDecls.getByKey name with
    | none => exact absurd hg hconc_get_ne
    | some d => exact ⟨d, rfl⟩
  -- Existence at `g` in the build.
  have hbuild_g : (concretizeBuild typedDecls drained.mono drained.newFunctions
      drained.newDataTypes).getByKey g ≠ none := by
    rw [concretizeBuild_eq]
    have h_src := fromSource_inserts_ctor_at_key typedDecls drained.mono hget hdt_params
    obtain ⟨_, _, hSrcGet⟩ := h_src
    have hSrcContains :
        (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default).containsKey g :=
      (IndexMap.getByKey_isSome_iff_containsKey _ _).mp (by rw [hSrcGet]; rfl)
    have hDtContains := dtStep_foldl_preserves_containsKey drained.mono drained.newDataTypes _
      hSrcContains
    have hBuildContains := fnStep_foldl_preserves_containsKey typedDecls drained.mono
      drained.newFunctions _ hDtContains
    rw [IndexMap.getByKey_ne_none_iff_containsKey]; exact hBuildContains
  have hConc_g_some : ∃ d, concDecls.getByKey g = some d := hbuild_to_conc g hbuild_g
  -- Existence at `td_dt.name` in the build (used in `hPerDtWit`).
  have hbuild_tdname : (concretizeBuild typedDecls drained.mono drained.newFunctions
      drained.newDataTypes).getByKey td_dt.name ≠ none := by
    rw [concretizeBuild_eq]
    have h_src := fromSource_inserts_dataType_at_key typedDecls drained.mono
      hdt_companion hdt_params
    obtain ⟨_, hSrcGet⟩ := h_src
    have hSrcContains :
        (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default).containsKey
          td_dt.name :=
      (IndexMap.getByKey_isSome_iff_containsKey _ _).mp (by rw [hSrcGet]; rfl)
    have hDtContains := dtStep_foldl_preserves_containsKey drained.mono drained.newDataTypes _
      hSrcContains
    have hBuildContains := fnStep_foldl_preserves_containsKey typedDecls drained.mono
      drained.newFunctions _ hDtContains
    rw [IndexMap.getByKey_ne_none_iff_containsKey]; exact hBuildContains
  have hConc_tdname : ∃ d, concDecls.getByKey td_dt.name = some d :=
    hbuild_to_conc td_dt.name hbuild_tdname
  -- Disjointness for newDataTypes (outer dt-key ≠ g) — via uniqueness.
  have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ g := by
    intro dt' hmem heq
    obtain ⟨g_orig, args, dt_orig, hname, hget_orig, _hargs_sz, _⟩ :=
      hStrong.2 dt' hmem
    have hcn_eq : concretizeName g_orig args = g := by rw [← hname]; exact heq
    have hcn_eq2 : concretizeName g_orig args = concretizeName g #[] := by
      rw [hcn_eq]; exact (concretizeName_empty_args g).symm
    have hWit' : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [hcn_eq]; exact hConc_g_some
    obtain ⟨hg_eq, _⟩ := hUniqueNames hconc g_orig g args #[] hcn_eq2 hWit'
    rw [hg_eq] at hget_orig
    rw [hget] at hget_orig
    cases hget_orig
  -- Disjointness for newFunctions — via uniqueness.
  have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
    intro f hmem heq
    obtain ⟨g_orig, args, _f_orig, hname, hget_orig, _hargs_sz⟩ :=
      hStrong.1 f hmem
    have hcn_eq : concretizeName g_orig args = g := by rw [← hname]; exact heq
    have hcn_eq2 : concretizeName g_orig args = concretizeName g #[] := by
      rw [hcn_eq]; exact (concretizeName_empty_args g).symm
    have hWit' : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [hcn_eq]; exact hConc_g_some
    obtain ⟨hg_eq, _⟩ := hUniqueNames hconc g_orig g args #[] hcn_eq2 hWit'
    rw [hg_eq] at hget_orig
    rw [hget] at hget_orig
    cases hget_orig
  -- Per-`dt' ∈ drained.newDataTypes` post-rewrite witness builder.
  -- Identical structural shape to `_explicit_general`'s `hPerDtWit`, but the
  -- `args = #[]` derivation now uses `ConcretizeUniqueNames` on the
  -- `concretizeName g_orig args = td_dt.name = concretizeName td_dt.name #[]`
  -- equation (anchored at the typed-side `.dataType` companion at
  -- `td_dt.name`).
  have hPerDtWit : ∀ dt' ∈ drained.newDataTypes,
      ∀ c ∈ dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }),
      dt'.name.pushNamespace c.nameHead = g →
        MatchesTdShape td_dt td_c (.constructor
          { dt' with constructors := dt'.constructors.map (fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }) } c) := by
    intro dt' hmem c hcmem hpush
    -- Suffix + prefix injectivity from pushed-key equality.
    rw [hg_pushed] at hpush
    have h_name_eq : Lean.Name.str dt'.name.toName c.nameHead =
        Lean.Name.str td_dt.name.toName td_c.nameHead := by
      have := hpush
      unfold Global.pushNamespace at this
      exact Global.mk.inj this
    have hToName : dt'.name.toName = td_dt.name.toName := by injection h_name_eq
    have hSuffix : c.nameHead = td_c.nameHead := by injection h_name_eq
    have hdt_name_eq : dt'.name = td_dt.name := by
      cases hd : dt'.name; cases hT : td_dt.name
      rw [hd, hT] at hToName
      congr 1
    -- StrongNewNameShape on dt'.
    obtain ⟨g_orig, args, dt_orig, hname, hget_orig, _hargs_sz, hctors_nh⟩ :=
      hStrong.2 dt' hmem
    -- Uniqueness: `concretizeName g_orig args = dt'.name = td_dt.name =
    -- concretizeName td_dt.name #[]`. With concDecls existence at td_dt.name,
    -- ConcretizeUniqueNames forces `g_orig = td_dt.name` and `args = #[]`.
    have hcn_eq : concretizeName g_orig args = dt'.name := hname.symm
    have hcn_eq2 : concretizeName g_orig args = concretizeName td_dt.name #[] := by
      rw [hcn_eq, hdt_name_eq]; exact (concretizeName_empty_args td_dt.name).symm
    have hWit' : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [hcn_eq, hdt_name_eq]; exact hConc_tdname
    obtain ⟨hgorig_eq_tdname, _hargs_empty⟩ :=
      hUniqueNames hconc g_orig td_dt.name args #[] hcn_eq2 hWit'
    have hdt_orig_eq : dt_orig = td_dt := by
      rw [hgorig_eq_tdname] at hget_orig
      rw [hdt_companion] at hget_orig
      cases hget_orig; rfl
    rw [hdt_orig_eq] at hctors_nh
    have hLen : dt'.constructors.length = td_dt.constructors.length := by
      have := congrArg List.length hctors_nh
      simp [List.length_map] at this
      exact this
    have hPosNH : ∀ i (hi : i < td_dt.constructors.length),
        ∃ hi' : i < dt'.constructors.length,
        (dt'.constructors[i]'hi').nameHead = (td_dt.constructors[i]'hi).nameHead := by
      intro i hi
      have hi' : i < dt'.constructors.length := by rw [hLen]; exact hi
      refine ⟨hi', ?_⟩
      have hi_dt : i < (dt'.constructors.map (·.nameHead)).length := by
        rw [List.length_map]; exact hi'
      have hi_td : i < (td_dt.constructors.map (·.nameHead)).length := by
        rw [List.length_map]; exact hi
      have h_nh :
          (dt'.constructors.map (·.nameHead))[i]'hi_dt =
          (td_dt.constructors.map (·.nameHead))[i]'hi_td := by
        congr 1
      rw [List.getElem_map, List.getElem_map] at h_nh
      exact h_nh
    refine ⟨_, c, rfl, ?_, hSuffix, ?_, ?_⟩
    · simp only [List.length_map]; exact hLen
    · intro i hi
      have hi' : i < dt'.constructors.length := by rw [hLen]; exact hi
      refine ⟨by simp only [List.length_map]; exact hi', ?_⟩
      simp only [List.getElem_map]
      exact (hPosNH i hi).2
    · intro i hi heq
      have hi'_dt' : i < dt'.constructors.length := by rw [hLen]; exact hi
      have hi'_new : i < (dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none)
            drained.mono) })).length := by simp only [List.length_map]; exact hi'_dt'
      refine ⟨hi'_new, ?_⟩
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hcmem
      have hk_lt_dt' : k < dt'.constructors.length := by
        simp only [List.length_map] at hk_lt; exact hk_lt
      have hk_nh_c : c.nameHead = (dt'.constructors[k]'hk_lt_dt').nameHead := by
        rw [← hk_eq]; simp only [List.getElem_map]
      have hk_lt_td : k < td_dt.constructors.length := by rw [← hLen]; exact hk_lt_dt'
      have hk_nh_td : (dt'.constructors[k]'hk_lt_dt').nameHead =
          (td_dt.constructors[k]'hk_lt_td).nameHead := (hPosNH k hk_lt_td).2
      have hk_eq_i : k = i := by
        apply hdt_distinct k i hk_lt_td hi
        rw [← hk_nh_td, ← hk_nh_c, hSuffix, ← heq]
      subst hk_eq_i
      have hgoal : (dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none)
            drained.mono) }))[k]'hk_lt = c := hk_eq
      exact hgoal
  -- Compose.
  rw [concretizeBuild_eq]
  have h0 : ∃ d, (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    have h := fromSource_inserts_ctor_at_key_explicit typedDecls drained.mono hget hdt_params
    refine ⟨_, h, ?_⟩
    exact MatchesTdShape_caseA drained.mono td_dt td_c
  have h1 : ∃ d, (drained.newDataTypes.foldl (dtStep drained.mono)
      (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default)).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) =>
        ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) h0
    intro i acc hinv
    have hdt_mem : drained.newDataTypes[i.val]'i.isLt ∈ drained.newDataTypes :=
      Array.getElem_mem _
    have hdt_ne := hDtNotKey _ hdt_mem
    have hWit_i := hPerDtWit _ hdt_mem
    exact dtStep_preserves_MatchesTdShape drained.mono acc _ hdt_ne hWit_i hinv
  have h2 : ∃ d, (drained.newFunctions.foldl (fnStep typedDecls drained.mono)
      (drained.newDataTypes.foldl (dtStep drained.mono)
        (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default))).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) =>
        ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) h1
    intro i acc hinv
    have hf_mem : drained.newFunctions[i.val]'i.isLt ∈ drained.newFunctions :=
      Array.getElem_mem _
    have hf_ne := hFnNotKey _ hf_mem
    exact fnStep_preserves_MatchesTdShape typedDecls drained.mono acc _ hf_ne hinv
  obtain ⟨d, hd, ⟨md_dt, md_c, hd_eq, hLen, hNH, hPos, hStruct⟩⟩ := h2
  rw [hd_eq] at hd
  exact ⟨md_dt, md_c, hd, hLen, hNH, hPos, hStruct⟩

end PhaseA2

namespace DirectDagBody

/-! #### Origin-split lemmas: backward classification of `concretizeBuild` output.

Moved 2026-05-01 from `SizeBound.lean` so that downstream consumers in
`RefClosed.lean` (e.g., the `.function` arm of `Toplevel.concretize_produces_refClosed_entry`)
can reference them. SizeBound is downstream of RefClosed, so origin lemmas
defined there were unreachable from RefClosed.

`listFoldl_shape_bwd` and `listFoldl_last_writer_shape` are utility helpers
used by both `concretizeBuild_function_origin` (here) and
`concretizeBuild_dataType_origin` (still in SizeBound, will follow). -/

/-- Generic `List.foldl` backward dichotomy: either some element has key `g`,
or the fold preserves `getByKey g`. -/
theorem listFoldl_shape_bwd
    {β : Type _}
    (step : Typed.Decls → β → Typed.Decls)
    (toKey : β → Global)
    (hstep_other : ∀ (acc : Typed.Decls) (b : β) (g' : Global),
      (toKey b == g') = false →
      (step acc b).getByKey g' = acc.getByKey g') :
    ∀ (xs : List β) (init : Typed.Decls) (g : Global),
      (∃ b ∈ xs, toKey b = g) ∨
      (xs.foldl step init).getByKey g = init.getByKey g := by
  intro xs init g
  induction xs generalizing init with
  | nil => right; rfl
  | cons hd tl ih =>
    by_cases hkey : toKey hd = g
    · left; exact ⟨hd, List.mem_cons_self, hkey⟩
    · have hne : (toKey hd == g) = false := by
        rw [beq_eq_false_iff_ne]; exact hkey
      simp only [List.foldl_cons]
      rcases ih (step init hd) with ⟨b, hb, heq⟩ | hpreserve
      · left; exact ⟨b, List.mem_cons_of_mem _ hb, heq⟩
      · right
        rw [hpreserve]
        exact hstep_other init hd g hne

/-- If `∃ b ∈ xs, toKey b = g`, the last such `b`'s insert determines the
value at `g` after `xs.foldl step init`. -/
theorem listFoldl_last_writer_shape
    {β : Type _}
    (step : Typed.Decls → β → Typed.Decls)
    (toKey : β → Global)
    (hstep_other : ∀ (acc : Typed.Decls) (b : β) (g' : Global),
      (toKey b == g') = false →
      (step acc b).getByKey g' = acc.getByKey g')
    (hstep_kind : ∀ (acc : Typed.Decls) (b : β),
      ∃ d_ins, (step acc b).getByKey (toKey b) = some d_ins) :
    ∀ (xs : List β) (init : Typed.Decls) (g : Global),
      (∃ b ∈ xs, toKey b = g) →
      ∃ d, (xs.foldl step init).getByKey g = some d ∧
        ∃ b ∈ xs, toKey b = g ∧
          ∃ acc_pre, (step acc_pre b).getByKey g = some d := by
  intro xs
  induction xs with
  | nil => intro _ _ ⟨_, hmem, _⟩; cases hmem
  | cons hd tl ih =>
    intro init g ⟨b, hmem, hbeq⟩
    simp only [List.foldl_cons]
    by_cases htl_ex : ∃ b' ∈ tl, toKey b' = g
    · obtain ⟨d, hd_eq, b', hb'mem, hb'eq, acc_pre, hacc_pre⟩ := ih (step init hd) g htl_ex
      exact ⟨d, hd_eq, b', List.mem_cons_of_mem _ hb'mem, hb'eq, acc_pre, hacc_pre⟩
    · rcases List.mem_cons.mp hmem with hbhd | htl
      · subst hbhd
        obtain ⟨d_ins, hd_ins⟩ := hstep_kind init b
        refine ⟨d_ins, ?_, b, List.mem_cons_self, hbeq, init, ?_⟩
        · have htl_preserve : (tl.foldl step (step init b)).getByKey g
              = (step init b).getByKey g := by
            rcases listFoldl_shape_bwd step toKey hstep_other tl (step init b) g with
              ⟨b', hb'mem, hb'eq⟩ | hp
            · exact absurd ⟨b', hb'mem, hb'eq⟩ htl_ex
            · exact hp
          rw [htl_preserve]
          rw [← hbeq]; exact hd_ins
        · rw [← hbeq]; exact hd_ins
      · exact absurd ⟨b, htl, hbeq⟩ htl_ex

/-- For any key `g` with `(concretizeBuild decls mono newFunctions newDataTypes).getByKey g
    = some (.function f_mono)`, one of:
- Source has `.function f_src` at `g` with `f_src.params = []`, OR
- `∃ f ∈ newFunctions, f.name = g`. -/
theorem concretizeBuild_function_origin
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {f_mono : Typed.Function}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.function f_mono)) :
    (∃ f_src, decls.getByKey g = some (.function f_src) ∧ f_src.params = []) ∨
    (∃ f ∈ newFunctions, f.name = g) := by
  let emptySubst : Global → Option Typ := fun _ => none
  let srcStep : Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
    fun acc p =>
      match p.2 with
      | .function f =>
        if f.params.isEmpty then
          acc.insert p.1 (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm decls emptySubst mono f.body })
        else acc
      | .dataType dt =>
        if dt.params.isEmpty then
          let newCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          acc.insert p.1 (.dataType { dt with constructors := newCtors })
        else acc
      | .constructor dt c =>
        if dt.params.isEmpty then
          let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
          let newCtor : Constructor := { c with argTypes := newArgTypes }
          let rewrittenCtors := dt.constructors.map fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          acc.insert p.1 (.constructor newDt newCtor)
        else acc
  let dtStep : Typed.Decls → DataType → Typed.Decls := fun acc dt =>
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    let acc' := acc.insert dt.name (.dataType newDt)
    rewrittenCtors.foldl
      (fun acc'' c =>
        let cName := dt.name.pushNamespace c.nameHead
        acc''.insert cName (.constructor newDt c))
      acc'
  let fnStep : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body })
  let fromSource := decls.pairs.toList.foldl srcStep default
  let withNewDts := newDataTypes.toList.foldl dtStep fromSource
  have hconc_eq :
      concretizeBuild decls mono newFunctions newDataTypes =
        newFunctions.toList.foldl fnStep withNewDts := by
    show concretizeBuild decls mono newFunctions newDataTypes =
      newFunctions.toList.foldl fnStep
        (newDataTypes.toList.foldl dtStep
          (decls.pairs.toList.foldl srcStep default))
    unfold concretizeBuild
    repeat rw [← Array.foldl_toList]
    rfl
  rw [hconc_eq] at hget
  have hfn_preserves_other : ∀ (acc : Typed.Decls) (f : Typed.Function) (g' : Global),
      (f.name == g') = false →
      (fnStep acc f).getByKey g' = acc.getByKey g' := by
    intro acc f g' hne
    show (acc.insert f.name _).getByKey g' = acc.getByKey g'
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne
  rcases listFoldl_shape_bwd fnStep Typed.Function.name hfn_preserves_other
    newFunctions.toList withNewDts g with
    hfn_ex | hfn_preserve
  · obtain ⟨f, hf_mem, hf_eq⟩ := hfn_ex
    exact Or.inr ⟨f, Array.mem_toList_iff.mp hf_mem, hf_eq⟩
  · rw [hfn_preserve] at hget
    have hdt_pres_lemma : ∀ (xs : List DataType) (init : Typed.Decls),
          (∀ dt ∈ xs, dt.name ≠ g) →
          (∀ dt ∈ xs, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g) →
          (xs.foldl dtStep init).getByKey g = init.getByKey g := by
        intro xs
        induction xs with
        | nil => intros; rfl
        | cons hd tl ih =>
          intro init hno_dt hno_ctor
          simp only [List.foldl_cons]
          have hnd_name : hd.name ≠ g := hno_dt hd List.mem_cons_self
          have hnd_ctor : ∀ c ∈ hd.constructors,
              hd.name.pushNamespace c.nameHead ≠ g :=
            fun c hc => hno_ctor hd List.mem_cons_self c hc
          have ih_tl := ih (dtStep init hd)
            (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt))
            (fun dt hdt c hc => hno_ctor dt (List.mem_cons_of_mem _ hdt) c hc)
          rw [ih_tl]
          have hnd_beq : (hd.name == g) = false := by
            rw [beq_eq_false_iff_ne]; exact hnd_name
          have h_inner : ∀ (cs : List Constructor) (acc' : Typed.Decls)
              (_hne_cs : ∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g)
              (body : Constructor → Typed.Declaration),
              IndexMap.getByKey (cs.foldl (fun acc'' c =>
                acc''.insert (hd.name.pushNamespace c.nameHead) (body c)) acc') g
              = acc'.getByKey g := by
            intro cs
            induction cs with
            | nil => intros; rfl
            | cons c0 rest ih_cs =>
              intro acc' hne body
              simp only [List.foldl_cons]
              have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
                hne c0 List.mem_cons_self
              have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
                rw [beq_eq_false_iff_ne]; exact hnc0
              have := ih_cs (acc'.insert (hd.name.pushNamespace c0.nameHead) (body c0))
                (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')) body
              rw [this]
              exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
          have hnd_ctor_rw : ∀ c ∈ (hd.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }),
              hd.name.pushNamespace c.nameHead ≠ g := by
            intro c' hc'
            simp only [List.mem_map] at hc'
            obtain ⟨c0, hc0, hc0_eq⟩ := hc'
            rw [← hc0_eq]
            exact hnd_ctor c0 hc0
          rw [h_inner _ _ hnd_ctor_rw _]
          exact IndexMap.getByKey_insert_of_beq_false _ _ hnd_beq
    have hkey_lemma_nonfn :
        ∀ (xs : List DataType) (init : Typed.Decls),
          (∃ dt ∈ xs, dt.name = g) ∨
          (∃ dt ∈ xs, ∃ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead = g) →
          ∃ d, (xs.foldl dtStep init).getByKey g = some d ∧
            (∀ f, d ≠ .function f) := by
      intro xs
      induction xs with
      | nil =>
        intro _ hex
        rcases hex with ⟨_, hm, _⟩ | ⟨_, hm, _⟩ <;> cases hm
      | cons hd tl ih =>
        intro init hex
        simp only [List.foldl_cons]
        by_cases htl_ex : (∃ dt ∈ tl, dt.name = g) ∨
            (∃ dt ∈ tl, ∃ c ∈ dt.constructors,
              dt.name.pushNamespace c.nameHead = g)
        · exact ih _ htl_ex
        · have htl_no_dt : ∀ dt' ∈ tl, dt'.name ≠ g := by
            intro dt' hdt' heq
            exact htl_ex (Or.inl ⟨dt', hdt', heq⟩)
          have htl_no_ctor : ∀ dt' ∈ tl, ∀ c' ∈ dt'.constructors,
              dt'.name.pushNamespace c'.nameHead ≠ g := by
            intro dt' hdt' c' hc' heq
            exact htl_ex (Or.inr ⟨dt', hdt', c', hc', heq⟩)
          rw [hdt_pres_lemma tl _ htl_no_dt htl_no_ctor]
          let rewrittenCtors := hd.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { hd with constructors := rewrittenCtors }
          show ∃ d, IndexMap.getByKey (rewrittenCtors.foldl
              (fun acc'' c =>
                acc''.insert (hd.name.pushNamespace c.nameHead)
                  (.constructor newDt c))
              (init.insert hd.name (.dataType newDt))) g = some d ∧
            (∀ f, d ≠ .function f)
          by_cases hinner_ex : ∃ c' ∈ rewrittenCtors,
              hd.name.pushNamespace c'.nameHead = g
          · have hctor_fold : ∀ (cs : List Constructor) (acc' : Typed.Decls),
                (∃ c' ∈ cs, hd.name.pushNamespace c'.nameHead = g) →
                ∃ cdt cc, (cs.foldl (fun acc'' c' =>
                  acc''.insert (hd.name.pushNamespace c'.nameHead)
                    (.constructor newDt c')) acc').getByKey g
                  = some (.constructor cdt cc) := by
              intro cs
              induction cs with
              | nil => intro _ ⟨_, hm, _⟩; cases hm
              | cons c0 rest ih_cs =>
                intro acc' hex_cs
                simp only [List.foldl_cons]
                by_cases hrest_ex : ∃ c' ∈ rest,
                    hd.name.pushNamespace c'.nameHead = g
                · exact ih_cs _ hrest_ex
                · obtain ⟨c_last, hc_last_mem, hc_last_eq⟩ := hex_cs
                  have hc_last_is_c0 : c_last = c0 := by
                    rcases List.mem_cons.mp hc_last_mem with rfl | hrest_mem
                    · rfl
                    · exact absurd ⟨c_last, hrest_mem, hc_last_eq⟩ hrest_ex
                  subst hc_last_is_c0
                  have hrest_pres : ∀ (xs : List Constructor) (init' : Typed.Decls),
                      (∀ c' ∈ xs, hd.name.pushNamespace c'.nameHead ≠ g) →
                      IndexMap.getByKey (xs.foldl (fun acc'' c' =>
                        acc''.insert (hd.name.pushNamespace c'.nameHead)
                          (.constructor newDt c')) init') g = init'.getByKey g := by
                    intro xs
                    induction xs with
                    | nil => intros; rfl
                    | cons c1 rest' ih_r =>
                      intro init' hne_all
                      simp only [List.foldl_cons]
                      have hnc1 : hd.name.pushNamespace c1.nameHead ≠ g :=
                        hne_all c1 List.mem_cons_self
                      have hnc1_beq :
                          (hd.name.pushNamespace c1.nameHead == g) = false := by
                        rw [beq_eq_false_iff_ne]; exact hnc1
                      rw [ih_r _ (fun c'' hc'' =>
                        hne_all c'' (List.mem_cons_of_mem _ hc''))]
                      exact IndexMap.getByKey_insert_of_beq_false _ _ hnc1_beq
                  have hrest_ne : ∀ c' ∈ rest,
                      hd.name.pushNamespace c'.nameHead ≠ g := by
                    intro c' hc' heq
                    exact hrest_ex ⟨c', hc', heq⟩
                  rw [hrest_pres rest _ hrest_ne]
                  refine ⟨newDt, c_last, ?_⟩
                  rw [← hc_last_eq]
                  exact IndexMap.getByKey_insert_self _ _ _
            obtain ⟨cdt_v, cc_v, hfinal⟩ := hctor_fold _ _ hinner_ex
            exact ⟨_, hfinal, fun _ h => by cases h⟩
          · have hno_inner_g : ∀ c ∈ rewrittenCtors,
                hd.name.pushNamespace c.nameHead ≠ g := by
              intro c hc heq
              exact hinner_ex ⟨c, hc, heq⟩
            have h_inner_pres : ∀ (cs : List Constructor) (acc' : Typed.Decls)
                (_hne : ∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g),
                IndexMap.getByKey (cs.foldl (fun acc'' c =>
                  acc''.insert (hd.name.pushNamespace c.nameHead)
                    (.constructor newDt c)) acc') g
                = acc'.getByKey g := by
              intro cs
              induction cs with
              | nil => intros; rfl
              | cons c0 rest ih_cs =>
                intro acc' hne
                simp only [List.foldl_cons]
                have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
                  hne c0 List.mem_cons_self
                have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
                  rw [beq_eq_false_iff_ne]; exact hnc0
                rw [ih_cs _ (fun c'' hc'' => hne c'' (List.mem_cons_of_mem _ hc''))]
                exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
            rw [h_inner_pres _ _ hno_inner_g]
            have hhd_eq : hd.name = g := by
              rcases hex with ⟨dt_ex, hdt_ex_mem, hdt_ex_eq⟩ | ⟨dt_ex, hdt_ex_mem, c_ex, hc_ex_mem, hc_ex_eq⟩
              · have : dt_ex = hd := by
                  rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                  · rfl
                  · exact absurd hdt_ex_eq (htl_no_dt dt_ex htl_mem)
                rw [← this]; exact hdt_ex_eq
              · exfalso
                have hdt_is_hd : dt_ex = hd := by
                  rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                  · rfl
                  · exact absurd hc_ex_eq (htl_no_ctor dt_ex htl_mem c_ex hc_ex_mem)
                subst hdt_is_hd
                let c_ex_rw : Constructor :=
                  { c_ex with argTypes := c_ex.argTypes.map (rewriteTyp emptySubst mono) }
                have h_rw_mem : c_ex_rw ∈ rewrittenCtors := by
                  rw [List.mem_map]
                  exact ⟨c_ex, hc_ex_mem, rfl⟩
                exact hno_inner_g _ h_rw_mem hc_ex_eq
            refine ⟨.dataType newDt, ?_, fun _ h => by cases h⟩
            rw [← hhd_eq]
            exact IndexMap.getByKey_insert_self _ _ _
    by_cases hdt_or_ctor_ex :
        (∃ dt ∈ newDataTypes.toList, dt.name = g) ∨
        (∃ dt ∈ newDataTypes.toList, ∃ c ∈ dt.constructors,
          dt.name.pushNamespace c.nameHead = g)
    · exfalso
      obtain ⟨d, hd_eq, hd_nfn⟩ :=
        hkey_lemma_nonfn newDataTypes.toList fromSource hdt_or_ctor_ex
      rw [hd_eq] at hget
      simp only [Option.some.injEq] at hget
      exact hd_nfn _ hget
    · have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
        intro dt hdt heq
        exact hdt_or_ctor_ex (Or.inl ⟨dt, hdt, heq⟩)
      have hno_ctor : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
          dt.name.pushNamespace c.nameHead ≠ g := by
        intro dt hdt c hc heq
        exact hdt_or_ctor_ex (Or.inr ⟨dt, hdt, c, hc, heq⟩)
      rw [hdt_pres_lemma newDataTypes.toList fromSource hno_dt_name hno_ctor] at hget
      show (∃ f_src, decls.getByKey g = some (.function f_src) ∧ f_src.params = []) ∨ _
      have hsrc_shape : ∀ (pairs : List (Global × Typed.Declaration))
          (init : Typed.Decls),
          (∀ p ∈ pairs, decls.getByKey p.1 = some p.2) →
          (pairs.foldl srcStep init).getByKey g = some (.function f_mono) →
          (∃ f_src, decls.getByKey g = some (.function f_src)
            ∧ f_src.params = []) ∨
          init.getByKey g = some (.function f_mono) := by
        intro pairs
        induction pairs with
        | nil =>
          intro init _ hfold
          right; exact hfold
        | cons hd tl ih =>
          intro init hpairs hfold
          simp only [List.foldl_cons] at hfold
          have hpairs_tl : ∀ p ∈ tl, decls.getByKey p.1 = some p.2 :=
            fun p hp => hpairs p (List.mem_cons_of_mem _ hp)
          have hpairs_hd : decls.getByKey hd.1 = some hd.2 := hpairs hd List.mem_cons_self
          rcases ih (srcStep init hd) hpairs_tl hfold with hleft | hmid
          · exact Or.inl hleft
          · obtain ⟨k, dd⟩ := hd
            simp only at hmid hpairs_hd
            cases dd with
            | function f =>
              by_cases hp : f.params.isEmpty = true
              · simp only [srcStep, hp, if_true] at hmid
                by_cases hk : (k == g) = true
                · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                  refine Or.inl ⟨f, ?_, ?_⟩
                  · rw [← hkeq]; exact hpairs_hd
                  · cases hfp : f.params with
                    | nil => rfl
                    | cons _ _ => rw [hfp] at hp; cases hp
                · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                  exact Or.inr hmid
              · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                exact Or.inr hmid
            | dataType dt =>
              by_cases hp : dt.params.isEmpty = true
              · simp only [srcStep, hp, if_true] at hmid
                by_cases hk : (k == g) = true
                · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                  rw [hkeq] at hmid
                  rw [IndexMap.getByKey_insert_self] at hmid
                  cases hmid
                · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                  exact Or.inr hmid
              · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                exact Or.inr hmid
            | constructor dt c =>
              by_cases hp : dt.params.isEmpty = true
              · simp only [srcStep, hp, if_true] at hmid
                by_cases hk : (k == g) = true
                · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                  rw [hkeq] at hmid
                  rw [IndexMap.getByKey_insert_self] at hmid
                  cases hmid
                · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                  exact Or.inr hmid
              · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                exact Or.inr hmid
      have hdefault_none : (default : Typed.Decls).getByKey g = none := by
        unfold IndexMap.getByKey
        show ((default : Typed.Decls).indices[g]?).bind _ = none
        have : (default : Typed.Decls).indices[g]? = none := by
          show ((default : Std.HashMap Global Nat))[g]? = none
          exact Std.HashMap.getElem?_empty
        rw [this]; rfl
      have hpairs_hyp : ∀ p ∈ decls.pairs.toList, decls.getByKey p.1 = some p.2 := by
        intro p hp
        rcases p with ⟨a, b⟩
        exact IndexMap.getByKey_of_mem_pairs _ _ _ hp
      rcases hsrc_shape decls.pairs.toList default hpairs_hyp hget with hleft | hmid
      · exact Or.inl hleft
      · rw [hdefault_none] at hmid
        cases hmid

/-- For any key `g` with `(concretizeBuild decls mono newFunctions newDataTypes).getByKey g
    = some (.dataType dt_mono)`, one of:
- Source has `.dataType dt_src` at `g` with `dt_src.params = []`, OR
- `∃ dt ∈ newDataTypes, dt.name = g`.

Moved 2026-05-04 from `SizeBound.lean` so that downstream consumers in
`RefClosed.lean` (the `.dataType` arm of `Toplevel.concretize_produces_refClosed_entry`)
can reference it. -/
theorem concretizeBuild_dataType_origin
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {dt_mono : DataType}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.dataType dt_mono)) :
    (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) ∨
    (∃ dt ∈ newDataTypes, dt.name = g) := by
  let emptySubst : Global → Option Typ := fun _ => none
  let srcStep : Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
    fun acc p =>
      match p.2 with
      | .function f =>
        if f.params.isEmpty then
          acc.insert p.1 (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm decls emptySubst mono f.body })
        else acc
      | .dataType dt =>
        if dt.params.isEmpty then
          let newCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          acc.insert p.1 (.dataType { dt with constructors := newCtors })
        else acc
      | .constructor dt c =>
        if dt.params.isEmpty then
          let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
          let newCtor : Constructor := { c with argTypes := newArgTypes }
          let rewrittenCtors := dt.constructors.map fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          acc.insert p.1 (.constructor newDt newCtor)
        else acc
  let dtStep : Typed.Decls → DataType → Typed.Decls := fun acc dt =>
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    let acc' := acc.insert dt.name (.dataType newDt)
    rewrittenCtors.foldl
      (fun acc'' c =>
        let cName := dt.name.pushNamespace c.nameHead
        acc''.insert cName (.constructor newDt c))
      acc'
  let fnStep : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body })
  let fromSource := decls.pairs.toList.foldl srcStep default
  let withNewDts := newDataTypes.toList.foldl dtStep fromSource
  have hconc_eq :
      concretizeBuild decls mono newFunctions newDataTypes =
        newFunctions.toList.foldl fnStep withNewDts := by
    show concretizeBuild decls mono newFunctions newDataTypes =
      newFunctions.toList.foldl fnStep
        (newDataTypes.toList.foldl dtStep
          (decls.pairs.toList.foldl srcStep default))
    unfold concretizeBuild
    repeat rw [← Array.foldl_toList]
    rfl
  rw [hconc_eq] at hget
  have hfn_preserves_other : ∀ (acc : Typed.Decls) (f : Typed.Function) (g' : Global),
      (f.name == g') = false →
      (fnStep acc f).getByKey g' = acc.getByKey g' := by
    intro acc f g' hne
    show (acc.insert f.name _).getByKey g' = acc.getByKey g'
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne
  have hfn_kind : ∀ (acc : Typed.Decls) (f : Typed.Function),
      ∃ d_ins, (fnStep acc f).getByKey f.name = some d_ins ∧
        ∃ f_ins, d_ins = .function f_ins := by
    intro acc f
    refine ⟨_, IndexMap.getByKey_insert_self _ _ _, _, rfl⟩
  rcases listFoldl_shape_bwd fnStep Typed.Function.name hfn_preserves_other
    newFunctions.toList withNewDts g with
    hfn_ex | hfn_preserve
  · exfalso
    have hkind_simple : ∀ (acc : Typed.Decls) (f : Typed.Function),
        ∃ d_ins, (fnStep acc f).getByKey f.name = some d_ins := fun acc f =>
      ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
    obtain ⟨d, hd_eq, f_last, _, hf_last_key, acc_pre, hacc_pre⟩ :=
      listFoldl_last_writer_shape fnStep Typed.Function.name hfn_preserves_other
        hkind_simple newFunctions.toList withNewDts g hfn_ex
    rw [hd_eq] at hget
    have hins_val : (fnStep acc_pre f_last).getByKey g = some (.function
        { f_last with
          inputs := f_last.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
          output := rewriteTyp emptySubst mono f_last.output,
          body := rewriteTypedTerm decls emptySubst mono f_last.body }) := by
      show (acc_pre.insert f_last.name _).getByKey g = some _
      rw [← hf_last_key]
      exact IndexMap.getByKey_insert_self _ _ _
    rw [hins_val] at hacc_pre
    simp only [Option.some.injEq] at hacc_pre
    rw [← hacc_pre] at hget
    cases hget
  · rw [hfn_preserve] at hget
    by_cases hdt_ex : ∃ dt ∈ newDataTypes.toList, dt.name = g
    · obtain ⟨dt, hdtmem, hdteq⟩ := hdt_ex
      exact Or.inr ⟨dt, Array.mem_toList_iff.mp hdtmem, hdteq⟩
    · have hdt_pres_lemma : ∀ (xs : List DataType) (init : Typed.Decls),
            (∀ dt ∈ xs, dt.name ≠ g) →
            (∀ dt ∈ xs, ∀ c ∈ dt.constructors,
              dt.name.pushNamespace c.nameHead ≠ g) →
            (xs.foldl dtStep init).getByKey g = init.getByKey g := by
          intro xs
          induction xs with
          | nil => intros; rfl
          | cons hd tl ih =>
            intro init hno_dt hno_ctor
            simp only [List.foldl_cons]
            have hnd_name : hd.name ≠ g := hno_dt hd List.mem_cons_self
            have hnd_ctor : ∀ c ∈ hd.constructors,
                hd.name.pushNamespace c.nameHead ≠ g :=
              fun c hc => hno_ctor hd List.mem_cons_self c hc
            have ih_tl := ih (dtStep init hd)
              (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt))
              (fun dt hdt c hc => hno_ctor dt (List.mem_cons_of_mem _ hdt) c hc)
            rw [ih_tl]
            have hnd_beq : (hd.name == g) = false := by
              rw [beq_eq_false_iff_ne]; exact hnd_name
            have h_inner : ∀ (cs : List Constructor) (acc' : Typed.Decls)
                (_hne_cs : ∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g)
                (body : Constructor → Typed.Declaration),
                IndexMap.getByKey (cs.foldl (fun acc'' c =>
                  acc''.insert (hd.name.pushNamespace c.nameHead) (body c)) acc') g
                = acc'.getByKey g := by
              intro cs
              induction cs with
              | nil => intros; rfl
              | cons c0 rest ih_cs =>
                intro acc' hne body
                simp only [List.foldl_cons]
                have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
                  hne c0 List.mem_cons_self
                have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
                  rw [beq_eq_false_iff_ne]; exact hnc0
                have := ih_cs (acc'.insert (hd.name.pushNamespace c0.nameHead) (body c0))
                  (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')) body
                rw [this]
                exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
            have hnd_ctor_rw : ∀ c ∈ (hd.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }),
                hd.name.pushNamespace c.nameHead ≠ g := by
              intro c' hc'
              simp only [List.mem_map] at hc'
              obtain ⟨c0, hc0, hc0_eq⟩ := hc'
              rw [← hc0_eq]
              exact hnd_ctor c0 hc0
            rw [h_inner _ _ hnd_ctor_rw _]
            exact IndexMap.getByKey_insert_of_beq_false _ _ hnd_beq
      by_cases hctor_ex : ∃ dt ∈ newDataTypes.toList,
          ∃ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead = g
      · exfalso
        have hkey_lemma :
            ∀ (xs : List DataType) (init : Typed.Decls),
              (∀ dt ∈ xs, dt.name ≠ g) →
              (∃ dt ∈ xs, ∃ c ∈ dt.constructors,
                dt.name.pushNamespace c.nameHead = g) →
              ∃ cdt cc, (xs.foldl dtStep init).getByKey g
                = some (.constructor cdt cc) := by
          intro xs
          induction xs with
          | nil =>
            intro _ _ ⟨_, hm, _⟩; cases hm
          | cons hd tl ih =>
            intro init hno_dt hex
            simp only [List.foldl_cons]
            by_cases htl_ex : ∃ dt ∈ tl, ∃ c ∈ dt.constructors,
                dt.name.pushNamespace c.nameHead = g
            · exact ih _ (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt)) htl_ex
            · obtain ⟨dt_ex, hdt_ex_mem, c_ex, hc_ex_mem, hc_ex_eq⟩ := hex
              have hdt_is_hd : dt_ex = hd := by
                rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                · rfl
                · exact absurd ⟨dt_ex, htl_mem, c_ex, hc_ex_mem, hc_ex_eq⟩ htl_ex
              subst hdt_is_hd
              have hno_dt_tl : ∀ dt' ∈ tl, dt'.name ≠ g :=
                fun dt' hdt' => hno_dt dt' (List.mem_cons_of_mem _ hdt')
              have hno_ctor_tl : ∀ dt' ∈ tl, ∀ c' ∈ dt'.constructors,
                  dt'.name.pushNamespace c'.nameHead ≠ g := by
                intro dt' hdt' c' hc' heq
                exact htl_ex ⟨dt', hdt', c', hc', heq⟩
              rw [hdt_pres_lemma tl _ hno_dt_tl hno_ctor_tl]
              have hdt_ex_name_ne : dt_ex.name ≠ g :=
                hno_dt dt_ex List.mem_cons_self
              have hctor_ex_rw_dt : ∃ c' ∈ dt_ex.constructors.map fun c =>
                  { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) },
                  dt_ex.name.pushNamespace c'.nameHead = g := by
                refine ⟨{ c_ex with argTypes := c_ex.argTypes.map (rewriteTyp emptySubst mono) },
                  ?_, hc_ex_eq⟩
                rw [List.mem_map]
                exact ⟨c_ex, hc_ex_mem, rfl⟩
              have hctor_fold : ∀ (cs : List Constructor) (acc' : Typed.Decls)
                  (rdt : DataType),
                  (∃ c' ∈ cs, dt_ex.name.pushNamespace c'.nameHead = g) →
                  ∃ cdt cc, (cs.foldl (fun acc'' c' =>
                    acc''.insert (dt_ex.name.pushNamespace c'.nameHead)
                      (.constructor rdt c')) acc').getByKey g
                    = some (.constructor cdt cc) := by
                intro cs
                induction cs with
                | nil => intro _ _ ⟨_, hm, _⟩; cases hm
                | cons c0 rest ih_cs =>
                  intro acc' rdt hex_cs
                  simp only [List.foldl_cons]
                  by_cases hrest_ex : ∃ c' ∈ rest,
                      dt_ex.name.pushNamespace c'.nameHead = g
                  · exact ih_cs _ rdt hrest_ex
                  · obtain ⟨c_last, hc_last_mem, hc_last_eq⟩ := hex_cs
                    have hc_last_is_c0 : c_last = c0 := by
                      rcases List.mem_cons.mp hc_last_mem with rfl | hrest_mem
                      · rfl
                      · exact absurd ⟨c_last, hrest_mem, hc_last_eq⟩ hrest_ex
                    subst hc_last_is_c0
                    have hrest_pres : ∀ (xs : List Constructor) (init' : Typed.Decls),
                        (∀ c' ∈ xs, dt_ex.name.pushNamespace c'.nameHead ≠ g) →
                        IndexMap.getByKey (xs.foldl (fun acc'' c' =>
                          acc''.insert (dt_ex.name.pushNamespace c'.nameHead)
                            (.constructor rdt c')) init') g = init'.getByKey g := by
                      intro xs
                      induction xs with
                      | nil => intros; rfl
                      | cons c1 rest' ih_r =>
                        intro init' hne_all
                        simp only [List.foldl_cons]
                        have hnc1 : dt_ex.name.pushNamespace c1.nameHead ≠ g :=
                          hne_all c1 List.mem_cons_self
                        have hnc1_beq :
                            (dt_ex.name.pushNamespace c1.nameHead == g) = false := by
                          rw [beq_eq_false_iff_ne]; exact hnc1
                        rw [ih_r _ (fun c'' hc'' =>
                          hne_all c'' (List.mem_cons_of_mem _ hc''))]
                        exact IndexMap.getByKey_insert_of_beq_false _ _ hnc1_beq
                    have hrest_ne : ∀ c' ∈ rest,
                        dt_ex.name.pushNamespace c'.nameHead ≠ g := by
                      intro c' hc' heq
                      exact hrest_ex ⟨c', hc', heq⟩
                    rw [hrest_pres rest _ hrest_ne]
                    refine ⟨rdt, c_last, ?_⟩
                    rw [← hc_last_eq]
                    exact IndexMap.getByKey_insert_self _ _ _
              exact hctor_fold _ _ _ hctor_ex_rw_dt
        have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
          intro dt hdt heq
          exact hdt_ex ⟨dt, hdt, heq⟩
        obtain ⟨cdt_v, cc_v, hfinal⟩ :=
          hkey_lemma newDataTypes.toList fromSource hno_dt_name hctor_ex
        rw [hfinal] at hget
        cases hget
      · have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
          intro dt hdt heq
          exact hdt_ex ⟨dt, hdt, heq⟩
        have hno_ctor : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g := by
          intro dt hdt c hc heq
          exact hctor_ex ⟨dt, hdt, c, hc, heq⟩
        rw [hdt_pres_lemma newDataTypes.toList fromSource hno_dt_name hno_ctor] at hget
        show (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) ∨ _
        have hsrc_shape : ∀ (pairs : List (Global × Typed.Declaration))
            (init : Typed.Decls),
            (∀ p ∈ pairs, decls.getByKey p.1 = some p.2) →
            (pairs.foldl srcStep init).getByKey g = some (.dataType dt_mono) →
            (∃ dt_src, decls.getByKey g = some (.dataType dt_src)
              ∧ dt_src.params = []) ∨
            init.getByKey g = some (.dataType dt_mono) := by
          intro pairs
          induction pairs with
          | nil =>
            intro init _ hfold
            right; exact hfold
          | cons hd tl ih =>
            intro init hpairs hfold
            simp only [List.foldl_cons] at hfold
            have hpairs_tl : ∀ p ∈ tl, decls.getByKey p.1 = some p.2 :=
              fun p hp => hpairs p (List.mem_cons_of_mem _ hp)
            have hpairs_hd : decls.getByKey hd.1 = some hd.2 := hpairs hd List.mem_cons_self
            rcases ih (srcStep init hd) hpairs_tl hfold with hleft | hmid
            · exact Or.inl hleft
            · obtain ⟨k, dd⟩ := hd
              simp only at hmid hpairs_hd
              cases dd with
              | function f =>
                by_cases hp : f.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    rw [hkeq] at hmid
                    rw [IndexMap.getByKey_insert_self] at hmid
                    cases hmid
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
              | dataType dt =>
                by_cases hp : dt.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    refine Or.inl ⟨dt, ?_, ?_⟩
                    · rw [← hkeq]; exact hpairs_hd
                    · cases hdp : dt.params with
                      | nil => rfl
                      | cons _ _ => rw [hdp] at hp; cases hp
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
              | constructor dt c =>
                by_cases hp : dt.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    rw [hkeq] at hmid
                    rw [IndexMap.getByKey_insert_self] at hmid
                    cases hmid
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
        have hdefault_none : (default : Typed.Decls).getByKey g = none := by
          unfold IndexMap.getByKey
          show ((default : Typed.Decls).indices[g]?).bind _ = none
          have : (default : Typed.Decls).indices[g]? = none := by
            show ((default : Std.HashMap Global Nat))[g]? = none
            exact Std.HashMap.getElem?_empty
          rw [this]; rfl
        have hpairs_hyp : ∀ p ∈ decls.pairs.toList, decls.getByKey p.1 = some p.2 := by
          intro p hp
          rcases p with ⟨a, b⟩
          exact IndexMap.getByKey_of_mem_pairs _ _ _ hp
        rcases hsrc_shape decls.pairs.toList default hpairs_hyp hget with hleft | hmid
        · exact Or.inl hleft
        · rw [hdefault_none] at hmid
          cases hmid

end DirectDagBody

end Aiur

end -- public section
