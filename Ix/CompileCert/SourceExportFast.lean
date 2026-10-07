import Ix.CompileCert.Indexed

/-! # The source export on the DAG, with indexed lookups (M7 WP-F)

`exportSourceDeclarations` (the source fold's input, bound by the structure field
`SourceNormalizedInstallation.exported`) and `exportSourceGroups` (read by the model
proposal) were written for cones of a few thousand declarations. On one global cone
(every W-certified constant of a library) these parts of them do not scale:

* `Source.find`, a list scan, once per group member (`sourceGroupDependencies`,
  `exportSourceInductive`): quadratic in the source;
* the references of a group (`sourceTermRefs`, through `exprRefs`) are collected as a
  list over the **tree** of every expression (Init+Std has a proof of 2.6·10⁹ tree nodes
  and 6,980 DAG nodes) and deduplicated by `eraseDups`, quadratic in the occurrences;
* the groups are accumulated by `groups ++ [g]`, quadratic in the source;
* `SourceGroupsCover` is decided by list `Nodup` and list membership, quadratic;
* `orderSourceGroups` asks `available.contains` (a list) for every dependency of every
  pending group in every round.

This module computes the **same functions** without those costs and substitutes them by
`@[csimp]` (`exportSourceGroups_eq_fast`, `exportSourceDeclarations_eq_fast`), so every
statement and proof keeps reading the definitions in `Translate.lean`. The method, for
each replaced function: a copy parameterised by the lookups and helpers it calls
(`…P`), equal to the original at the original's arguments by `rfl`; then the fast
instance, equal to the copy by the lemmas below.

* `sourceIndex`: the declarations under their names in a hash map, the first of a name
  winning as in `Source.find` (`sourceIndex_get`: an equation, no uniqueness assumed);
* `depsWalk`: the dependency list `(refs.filter (!members.contains ·)).eraseDups`
  computed by one walk of the expressions' **DAG**, in the arrangement of WP-B's
  `refsInShared` (`Indexed.lean`) and IxC's `beqMemo`: a memo from node addresses to
  visited nodes, confirmed by identity (`withPtrEq`), behind `Squash`; every entry
  carries the proof that its node's references are already in the output, and the state
  carries the proof that every entry's output is a suffix of the current one
  (`DepState.memo_ok`). The result is `keepNew members refs []`, the loop of `eraseDups`
  after the filter (`eraseDups_filter_eq_keepNew`): the same list, element for element;
* `buildSourceGroupsA`: the groups in an array (`forIn_rep`: the two loops agree up to
  `Array.toList`);
* `coverFast`: `SourceGroupsCover` decided with hash sets (M3's `nodupBy`), sound
  (`coverFast_sound`); a refusal falls back to the list decision, so the decision is
  the same in both directions;
* `orderF`: `orderSourceGroups` with the available names in a hash set (`orderF_eq`);
* `ciBeq`, `declBeq`: `Kernel.ConstantInfo` and `Kernel.Declaration` equality field by
  field, the expressions through `Kernel.Expr.beq` (IxC's `beqMemo`, WP-B), a pointer test
  first; substituted for the derived instances by `@[csimp]` (`Subsingleton.elim`), as
  WP-B did for `DirectEntry`, so the source installation's `Sublist` and model-proposal
  comparisons below this module run on the DAG.

Trust: the compiler's substitution on these kernel-checked equations and the runtime's
`withPtrAddr`/`withPtrEq`, as for WP-B's walks and the certified kernel's `beqMemo`. No
hash is consulted as equality: the hash maps and sets are keyed by names (confirmed by
`Lean.Name`'s lawful `BEq`) and by addresses (confirmed by identity). -/

namespace Ix.CompileCert

/-! ## The source index -/

/-- A value proved equal to a given one: a subsingleton (the type of a memoised walk's answer). -/
instance subsingletonEqSubtype {α : Sort u} (x : α) : Subsingleton {a : α // a = x} :=
  ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => by subst ha; subst hb; rfl⟩

/-- The source's declarations under their names, built from the back so that the first
declaration of a name wins, as `Source.find` returns it. -/
def sourceIndex (s : Source) : Std.HashMap Lean.Name Lean.ConstantInfo :=
  s.declarations.foldr (fun ci m => m.insert ci.name ci) {}

theorem sourceIndex_go (ds : List Lean.ConstantInfo) (n : Lean.Name) :
    (ds.foldr (fun ci m => m.insert ci.name ci) ({} : Std.HashMap Lean.Name Lean.ConstantInfo))[n]? =
      ds.find? (fun c => c.name == n) := by
  induction ds with
  | nil => simp
  | cons ci cs ih =>
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, ih, List.find?_cons]
    by_cases h : ci.name = n
    · subst h; simp
    · simp [beq_eq_false_iff_ne.mpr h]

/-- The index computes `Source.find`, for every name. -/
theorem sourceIndex_get (s : Source) (n : Lean.Name) : (sourceIndex s)[n]? = s.find n :=
  sourceIndex_go s.declarations n

theorem sourceIndex_find (s : Source) : (fun n => (sourceIndex s)[n]?) = s.find :=
  funext (sourceIndex_get s)

/-! ## The dependency list, as a left fold -/

/-- Process `l` from the left, putting in front of `acc` every name that is neither in
`excl` nor already in `acc`: the loop of `eraseDups`, after `filter (!excl.contains ·)`. -/
def keepNew (excl : List Lean.Name) : List Lean.Name → List Lean.Name → List Lean.Name
  | [], acc => acc
  | n :: l, acc => if (excl.contains n || acc.any (n == ·)) = true then keepNew excl l acc
      else keepNew excl l (n :: acc)

theorem eraseDupsLoop_filter_eq_keepNew (excl : List Lean.Name) :
    ∀ (l acc : List Lean.Name),
      List.eraseDupsBy.loop (· == ·) (l.filter (fun n => !excl.contains n)) acc =
        (keepNew excl l acc).reverse
  | [], acc => by simp [List.eraseDupsBy.loop, keepNew]
  | n :: l, acc => by
    rw [List.filter_cons]
    cases hx : excl.contains n
    · cases ha : acc.any (n == ·)
      · simp only [Bool.not_false, ↓reduceIte, List.eraseDupsBy.loop, keepNew, hx, ha, Bool.false_or,
          Bool.false_eq_true]
        exact eraseDupsLoop_filter_eq_keepNew excl l (n :: acc)
      · simp only [Bool.not_false, ↓reduceIte, List.eraseDupsBy.loop, keepNew, hx, ha, Bool.false_or]
        exact eraseDupsLoop_filter_eq_keepNew excl l acc
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, keepNew, hx, Bool.true_or]
      exact eraseDupsLoop_filter_eq_keepNew excl l acc

/-- The dependency list of `sourceGroupDependencies` is `keepNew`'s, reversed. -/
theorem eraseDups_filter_eq_keepNew (excl l : List Lean.Name) :
    (l.filter (fun n => !excl.contains n)).eraseDups = (keepNew excl l []).reverse :=
  eraseDupsLoop_filter_eq_keepNew excl l []

theorem keepNew_append (excl : List Lean.Name) :
    ∀ (a b acc : List Lean.Name), keepNew excl (a ++ b) acc = keepNew excl b (keepNew excl a acc)
  | [], _, _ => rfl
  | n :: a, b, acc => by
    simp only [List.cons_append, keepNew]
    split <;> exact keepNew_append excl a b _

theorem keepNew_suffix (excl : List Lean.Name) :
    ∀ (l acc : List Lean.Name), acc <:+ keepNew excl l acc
  | [], acc => List.suffix_refl acc
  | n :: l, acc => by
    simp only [keepNew]
    split
    · exact keepNew_suffix excl l acc
    · exact (List.suffix_cons n acc).trans (keepNew_suffix excl l (n :: acc))

theorem any_beq_iff (acc : List Lean.Name) (n : Lean.Name) : acc.any (n == ·) = true ↔ n ∈ acc := by
  simp only [List.any_eq_true, beq_iff_eq]
  exact ⟨fun ⟨b, hb, e⟩ => e ▸ hb, fun h => ⟨n, h, rfl⟩⟩

theorem keepNew_covers (excl : List Lean.Name) :
    ∀ (l acc : List Lean.Name), ∀ n ∈ l, excl.contains n = true ∨ n ∈ keepNew excl l acc
  | [], _, n, hn => by simp at hn
  | m :: l, acc, n, hn => by
    simp only [keepNew]
    rcases List.mem_cons.mp hn with rfl | hn
    · split
      · rename_i h
        rcases Bool.or_eq_true_iff.mp h with h | h
        · exact .inl h
        · exact .inr ((keepNew_suffix excl l acc).subset ((any_beq_iff acc _).mp h))
      · exact .inr ((keepNew_suffix excl l (_ :: acc)).subset List.mem_cons_self)
    · split
      · exact keepNew_covers excl l acc n hn
      · exact keepNew_covers excl l (m :: acc) n hn

theorem keepNew_absorb (excl : List Lean.Name) :
    ∀ (l acc : List Lean.Name), (∀ n ∈ l, excl.contains n = true ∨ n ∈ acc) → keepNew excl l acc = acc
  | [], _, _ => rfl
  | n :: l, acc, h => by
    have hn := h n List.mem_cons_self
    have : (excl.contains n || acc.any (n == ·)) = true := by
      rcases hn with hn | hn
      · rw [hn, Bool.true_or]
      · rw [(any_beq_iff acc n).mpr hn, Bool.or_true]
    simp only [keepNew, this, ↓reduceIte]
    exact keepNew_absorb excl l acc (fun m hm => h m (List.mem_cons_of_mem n hm))

/-! ## The dependency walk on the DAG -/

section Deps

variable (excl : List Lean.Name)

/-- A memo entry: a visited node, the output after its visit, and the proof that every
reference of the node is excluded or in that output. -/
structure DepEntry where
  node : Lean.Expr
  acc : List Lean.Name
  ok : ∀ n ∈ exprRefs node, excl.contains n = true ∨ n ∈ acc

/-- The walk's state: the output so far (reversed), a hash set of the excluded and output
names, the memo, and the two invariants. -/
structure DepState where
  acc : List Lean.Name
  seen : Std.HashSet Lean.Name
  memo : Std.HashMap Nat (DepEntry excl)
  seen_ok : ∀ n, seen.contains n = true ↔ excl.contains n = true ∨ n ∈ acc
  memo_ok : ∀ (k : Nat) (q : DepEntry excl), memo[k]? = some q → q.acc <:+ acc

/-- The state after processing the names `l` from `st`: its output is `keepNew`'s. -/
structure DepRes (l : List Lean.Name) (st : DepState excl) where
  out : DepState excl
  eq : out.acc = keepNew excl l st.acc

abbrev DepOut (l : List Lean.Name) (st : DepState excl) := Squash (DepRes excl l st)

/-- The initial state: nothing output, the excluded names seen. -/
def DepState.init : DepState excl where
  acc := []
  seen := Std.HashSet.ofList excl
  memo := {}
  seen_ok := by intro n; simp [Std.HashSet.contains_ofList]
  memo_ok := by intro k q h; simp at h

theorem keepNew_single (n : Lean.Name) (acc : List Lean.Name) :
    keepNew excl [n] acc = if (excl.contains n || acc.any (n == ·)) = true then acc else n :: acc := by
  simp only [keepNew]

/-- One name. -/
def depStep (st : DepState excl) (n : Lean.Name) : DepRes excl [n] st :=
  if h : st.seen.contains n = true then
    ⟨st, by
      have : (excl.contains n || st.acc.any (n == ·)) = true := by
        rcases (st.seen_ok n).mp h with h | h
        · rw [h, Bool.true_or]
        · rw [(any_beq_iff st.acc n).mpr h, Bool.or_true]
      rw [keepNew_single]; simp only [this, ↓reduceIte]⟩
  else
    have hn : ¬ (excl.contains n || st.acc.any (n == ·)) = true := by
      intro h'
      apply h
      rcases Bool.or_eq_true_iff.mp h' with h' | h'
      · exact (st.seen_ok n).mpr (.inl h')
      · exact (st.seen_ok n).mpr (.inr ((any_beq_iff st.acc n).mp h'))
    ⟨{ acc := n :: st.acc, seen := st.seen.insert n, memo := st.memo
       seen_ok := by
         intro m
         rw [Std.HashSet.contains_insert, Bool.or_eq_true, st.seen_ok m, beq_iff_eq, List.mem_cons]
         constructor
         · rintro (rfl | h | h)
           · exact .inr (.inl rfl)
           · exact .inl h
           · exact .inr (.inr h)
         · rintro (h | rfl | h)
           · exact .inr (.inl h)
           · exact .inl rfl
           · exact .inr (.inr h)
       memo_ok := fun k q hq => (st.memo_ok k q hq).trans (List.suffix_cons n st.acc) },
     by rw [keepNew_single]; simp only [hn, Bool.false_eq_true, ↓reduceIte]⟩

/-- A list of names. -/
def depSteps : (l : List Lean.Name) → (st : DepState excl) → DepRes excl l st
  | [], st => ⟨st, rfl⟩
  | n :: l, st =>
    let r₁ := depStep excl st n
    let r₂ := depSteps l r₁.out
    ⟨r₂.out, by rw [r₂.eq, r₁.eq, ← keepNew_append]; rfl⟩

/-- Two consecutive results compose. -/
def DepRes.seq {a b : List Lean.Name} {st : DepState excl} (r₁ : DepRes excl a st)
    (r₂ : DepRes excl b r₁.out) : DepRes excl (a ++ b) st :=
  ⟨r₂.out, by rw [r₂.eq, r₁.eq, keepNew_append]⟩

/-- The memo after visiting `e`: an entry for `e` under `key`. -/
def DepRes.record (e : Lean.Expr) {st : DepState excl} (key : Nat) (r : DepRes excl (exprRefs e) st) :
    DepRes excl (exprRefs e) st :=
  ⟨{ acc := r.out.acc, seen := r.out.seen
     memo := r.out.memo.insert key ⟨e, r.out.acc, by
        intro n hn
        rw [r.eq]
        exact keepNew_covers excl (exprRefs e) st.acc n hn⟩
     seen_ok := r.out.seen_ok
     memo_ok := by
        intro k q hq
        rw [Std.HashMap.getElem?_insert] at hq
        split at hq
        · cases hq; exact List.suffix_refl _
        · exact r.out.memo_ok k q hq },
   r.eq⟩

/-- Is the memo entry under `key` the node `e`? Confirmed by identity (`withPtrEq`), whose
pure meaning decides that every reference of `e` is excluded or already output. -/
@[inline] def depProbe (st : DepState excl) (key : Nat) (e : Lean.Expr) :
    { b : Bool // b = true → ∀ n ∈ exprRefs e, excl.contains n = true ∨ n ∈ st.acc } :=
  match hq : st.memo[key]? with
  | none => ⟨false, fun h => Bool.noConfusion h⟩
  | some q => ⟨withPtrEq q.node e (fun _ => decide (∀ n ∈ exprRefs e, excl.contains n = true ∨ n ∈ st.acc))
      (fun same => by
        subst same
        exact decide_eq_true fun n hn => (q.ok n hn).imp id (fun h => (st.memo_ok key q hq).subset h)),
    fun h => of_decide_eq_true h⟩

/-- The DAG walk: probe under the node's address; on a miss, process the node's
references in `exprRefs`' order (children through the walk) and record the node. -/
def depGo (st : DepState excl) (e : @& Lean.Expr) : DepOut excl (exprRefs e) st :=
  withPtrAddr e (fun pa =>
    let hit := depProbe excl st pa.toNat e
    if hh : hit.1 = true then Squash.mk ⟨st, (keepNew_absorb excl _ _ (hit.2 hh)).symm⟩
    else
      let node : DepOut excl (exprRefs e) st := match e with
        | .const n _ => Squash.mk (depStep excl st n)
        | .app f a =>
          Squash.lift (depGo st f) fun r₁ => Squash.lift (depGo r₁.out a) fun r₂ =>
            Squash.mk (r₁.seq excl r₂)
        | .lam _ t b _ =>
          Squash.lift (depGo st t) fun r₁ => Squash.lift (depGo r₁.out b) fun r₂ =>
            Squash.mk (r₁.seq excl r₂)
        | .forallE _ t b _ =>
          Squash.lift (depGo st t) fun r₁ => Squash.lift (depGo r₁.out b) fun r₂ =>
            Squash.mk (r₁.seq excl r₂)
        | .letE _ t v b _ =>
          Squash.lift (depGo st t) fun r₁ => Squash.lift (depGo r₁.out v) fun r₂ =>
            Squash.lift (depGo r₂.out b) fun r₃ => Squash.mk ((r₁.seq excl r₂).seq excl r₃)
        | .mdata _ b => depGo st b
        | .proj n _ b =>
          let r₁ := depStep excl st n
          Squash.lift (depGo r₁.out b) fun r₂ => Squash.mk (r₁.seq excl r₂)
        | .lit (.natVal _) => Squash.mk (depSteps excl _ st)
        | .lit (.strVal _) => Squash.mk (depSteps excl _ st)
        | .bvar _ | .fvar _ | .mvar _ | .sort _ => Squash.mk ⟨st, rfl⟩
      Squash.lift node fun r => Squash.mk (r.record excl e pa.toNat))
    (fun _ _ => Subsingleton.elim _ _)

/-- The items of one declaration, in `sourceTermRefs`' order: expressions walked, names
taken as they are. -/
def depItems (ci : Lean.ConstantInfo) : List (Lean.Expr ⊕ Lean.Name) :=
  .inl ci.type :: match ci with
  | .defnInfo v => [.inl v.value]
  | .thmInfo v => [.inl v.value]
  | .opaqueInfo v => [.inl v.value]
  | .recInfo v => v.rules.flatMap (fun r => [.inr r.ctor, .inl r.rhs])
  | .ctorInfo v => [.inr v.induct]
  | _ => []

def itemRefs : Lean.Expr ⊕ Lean.Name → List Lean.Name
  | .inl e => exprRefs e
  | .inr n => [n]

theorem rules_items (rules : List Lean.RecursorRule) :
    rules.flatMap (fun r => r.ctor :: exprRefs r.rhs) =
      (rules.flatMap (fun r => [Sum.inr r.ctor, Sum.inl r.rhs])).flatMap itemRefs := by
  induction rules with
  | nil => rfl
  | cons r rs ih => simp [List.flatMap_cons, itemRefs, ih]

theorem sourceTermRefs_items (ci : Lean.ConstantInfo) :
    sourceTermRefs ci = (depItems ci).flatMap itemRefs := by
  cases ci <;> simp [sourceTermRefs, depItems, itemRefs, List.flatMap_cons, rules_items]

/-- A list of items, threading one state (so the memo is shared). -/
def depItemsGo : (items : List (Lean.Expr ⊕ Lean.Name)) → (st : DepState excl) →
    DepOut excl (items.flatMap itemRefs) st
  | [], st => Squash.mk ⟨st, rfl⟩
  | .inl e :: items, st => Squash.lift (depGo excl st e) fun r₁ =>
      Squash.lift (depItemsGo items r₁.out) fun r₂ => Squash.mk (r₁.seq excl r₂)
  | .inr n :: items, st =>
      let r₁ := depStep excl st n
      Squash.lift (depItemsGo items r₁.out) fun r₂ => Squash.mk (r₁.seq excl r₂)

/-- The walk's answer: a subsingleton. -/
def depsWalkVal (cis : List Lean.ConstantInfo) :
    { acc : List Lean.Name // acc = keepNew excl ((cis.flatMap depItems).flatMap itemRefs) [] } :=
  Squash.lift (depItemsGo excl (cis.flatMap depItems) (DepState.init excl)) fun r => ⟨r.out.acc, r.eq⟩

/-- **The dependency list on the DAG**: `(refs.filter (!excl.contains ·)).eraseDups` for
the references of `cis`, element for element. -/
def depsWalk (cis : List Lean.ConstantInfo) : List Lean.Name := (depsWalkVal excl cis).val.reverse

theorem depsWalk_eq (cis : List Lean.ConstantInfo) :
    depsWalk excl cis = ((cis.map sourceTermRefs).flatten.filter (fun n => !excl.contains n)).eraseDups := by
  rw [depsWalk, (depsWalkVal excl cis).property, eraseDups_filter_eq_keepNew, List.flatMap_assoc]
  simp only [← sourceTermRefs_items]
  try rfl

end Deps

/-! ## Groups: copies parameterised by their lookups, and their fast instances -/

/-- `sourceGroupDependencies` with the lookup given: `sourceGroupDependenciesP s.find` is
`sourceGroupDependencies s` by `rfl`. -/
def sourceGroupDependenciesP (find : Lean.Name → Option Lean.ConstantInfo) (members : List Lean.Name) :
    ExportM (List Lean.Name) := do
  let refs ← members.mapM fun n => do
    let some ci := find n | throw s!"source group member is missing: {n}"
    return sourceTermRefs ci
  return (refs.flatten.filter fun n => !members.contains n).eraseDups

theorem sourceGroupDependenciesP_find (s : Source) (members : List Lean.Name) :
    sourceGroupDependenciesP s.find members = sourceGroupDependencies s members := rfl

/-- A member's declaration, or the error of `sourceGroupDependencies`. -/
def findMember (find : Lean.Name → Option Lean.ConstantInfo) (n : Lean.Name) : ExportM Lean.ConstantInfo :=
  match find n with
  | some ci => pure ci
  | none => throw s!"source group member is missing: {n}"

/-- `sourceGroupDependencies` with the lookup given and the dependency list on the DAG. -/
def sourceGroupDependenciesF (find : Lean.Name → Option Lean.ConstantInfo) (members : List Lean.Name) :
    ExportM (List Lean.Name) := do
  let cis ← members.mapM (findMember find)
  return depsWalk members cis

theorem mapM_map_except {α β γ : Type} (f : β → γ) (G : α → ExportM γ) (H : α → ExportM β)
    (hGH : ∀ a, G a = f <$> H a) : ∀ l : List α, l.mapM G = List.map f <$> l.mapM H
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, hGH, mapM_map_except f G H hGH l]
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    cases H a <;> (try rfl)
    cases l.mapM H <;> rfl

theorem sourceGroupDependenciesF_eq (find : Lean.Name → Option Lean.ConstantInfo) (members : List Lean.Name) :
    sourceGroupDependenciesF find members = sourceGroupDependenciesP find members := by
  unfold sourceGroupDependenciesF sourceGroupDependenciesP
  conv => rhs; rw [mapM_map_except sourceTermRefs _ (findMember find) (by
    intro n
    simp only [findMember]
    cases find n <;> rfl) members]
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases members.mapM (findMember find) with
  | error e => rfl
  | ok cis => simp only [depsWalk_eq]

/-- `exportSourceInductive` with its lookup and dependency function given:
`exportSourceInductiveP s.find (sourceGroupDependencies s)` is `exportSourceInductive s` by
`rfl`. -/
def exportSourceInductiveP (find : Lean.Name → Option Lean.ConstantInfo)
    (deps : List Lean.Name → ExportM (List Lean.Name)) (owner : Lean.InductiveVal) :
    ExportM SourceDeclGroup := do
  unless owner.all.contains owner.name do throw "source inductive is absent from its own group"
  let mut names := owner.all
  let mut types := []
  let mut ctors := []
  for n in owner.all do
    let some (.inductInfo iv) := find n | throw s!"source inductive member missing: {n}"
    unless iv.all == owner.all && iv.numParams == owner.numParams do
      throw s!"inconsistent source inductive group: {n}"
    let .induct cv _ ← exportSourceEntry (.inductInfo iv) | throw "source inductive kind mismatch"
    types := types ++ [Kernel.ConstantInfo.indInfo cv {}]
    names := names ++ iv.ctors
    for (name, index) in iv.ctors.zipIdx do
      let some (.ctorInfo ctor) := find name | throw s!"source constructor missing: {name}"
      unless ctor.induct == n && ctor.cidx == index && ctor.numParams == iv.numParams do
        throw s!"source constructor ownership mismatch: {name}"
      let .ctor cv np nf ← exportSourceEntry (.ctorInfo ctor) | throw "source constructor kind mismatch"
      ctors := ctors ++ [Kernel.ConstantInfo.ctorInfo cv np nf]
  let recNames := owner.all.map (·.str "rec") ++
    (List.range owner.numNested).filterMap (fun i => owner.all.head?.map (·.str s!"rec_{i + 1}"))
  let mut recs := []
  for n in recNames do
    let some (.recInfo rv) := find n | throw s!"source recursor missing: {n}"
    unless rv.all == owner.all do throw s!"source recursor group mismatch: {n}"
    let .recursor cv major numArgs rules ← exportSourceEntry (.recInfo rv)
      | throw "source recursor kind mismatch"
    recs := recs ++ [Kernel.ConstantInfo.recInfo cv major numArgs rules]
  names := names ++ recNames
  return ⟨names, ← deps names, .indDecl (types ++ ctors ++ recs) owner.numParams⟩

theorem exportSourceInductiveP_find (s : Source) (owner : Lean.InductiveVal) :
    exportSourceInductiveP s.find (sourceGroupDependencies s) owner = exportSourceInductive s owner := rfl

/-- `buildSourceGroups` with its helpers given: `buildSourceGroupsP (exportSourceInductive s)
(sourceGroupDependencies s) s.declarations` is `buildSourceGroups s` by `rfl`. -/
def buildSourceGroupsP (inductive_ : Lean.InductiveVal → ExportM SourceDeclGroup)
    (deps : List Lean.Name → ExportM (List Lean.Name)) (declarations : List Lean.ConstantInfo) :
    ExportM (List SourceDeclGroup) := do
  let mut groups := []
  for ci in declarations do
    match ci with
    | .inductInfo iv =>
      if iv.all.head? == some iv.name then groups := groups ++ [← inductive_ iv]
    | .ctorInfo _ | .recInfo _ => pure ()
    | _ =>
      let entry ← exportSourceEntry ci
      let declaration ← match entry with
        | .axiom cv => pure (.axiomDecl cv)
        | .defn cv value hint => pure (.defnDecl cv value hint)
        | .thm cv value => pure (.thmDecl cv value)
        | .opaque cv value => pure (.opaqueDecl cv value)
        | .quot k cv => pure (.quotDecl k cv)
        | _ => throw "source singleton kind mismatch"
      groups := groups ++ [⟨[ci.name], ← deps [ci.name], declaration⟩]
  return groups

theorem buildSourceGroupsP_find (s : Source) :
    buildSourceGroupsP (exportSourceInductive s) (sourceGroupDependencies s) s.declarations =
      buildSourceGroups s := rfl

/-- The declaration of a singleton group, or the error of `buildSourceGroups`. -/
def singletonDeclaration (ci : Lean.ConstantInfo) : ExportM Kernel.Declaration := do
  let entry ← exportSourceEntry ci
  match entry with
  | .axiom cv => pure (.axiomDecl cv)
  | .defn cv value hint => pure (.defnDecl cv value hint)
  | .thm cv value => pure (.thmDecl cv value)
  | .opaque cv value => pure (.opaqueDecl cv value)
  | .quot k cv => pure (.quotDecl k cv)
  | _ => throw "source singleton kind mismatch"

/-- One step of the group loop, the groups in an array. -/
def buildStepA (inductive_ : Lean.InductiveVal → ExportM SourceDeclGroup)
    (deps : List Lean.Name → ExportM (List Lean.Name)) (ci : Lean.ConstantInfo)
    (groups : Array SourceDeclGroup) : ExportM (ForInStep (Array SourceDeclGroup)) :=
  match ci with
  | .inductInfo iv =>
    if (iv.all.head? == some iv.name) = true then do
      let g ← inductive_ iv
      pure (.yield (groups.push g))
    else pure (.yield groups)
  | .ctorInfo _ => pure (.yield groups)
  | .recInfo _ => pure (.yield groups)
  | _ => do
    let declaration ← singletonDeclaration ci
    let d ← deps [ci.name]
    pure (.yield (groups.push ⟨[ci.name], d, declaration⟩))

/-- The group loop with an array accumulator. -/
def buildSourceGroupsA (inductive_ : Lean.InductiveVal → ExportM SourceDeclGroup)
    (deps : List Lean.Name → ExportM (List Lean.Name)) (declarations : List Lean.ConstantInfo) :
    ExportM (List SourceDeclGroup) := do
  let groups ← forIn declarations (#[] : Array SourceDeclGroup) (buildStepA inductive_ deps)
  return groups.toList

/-- Two `forIn` loops over the same list agree up to a map of their accumulators when their
steps do. -/
theorem forIn_rep {α β γ : Type} (rep : γ → β) (f : α → β → ExportM (ForInStep β))
    (g : α → γ → ExportM (ForInStep γ))
    (step : ∀ a c, f a (rep c) = (fun r => match r with
      | .done c => ForInStep.done (rep c) | .yield c => .yield (rep c)) <$> g a c) :
    ∀ (l : List α) (b : β) (c : γ), b = rep c → forIn l b f = rep <$> forIn l c g
  | [], b, c, h => by subst h; rfl
  | a :: l, b, c, h => by
    subst h
    rw [List.forIn_cons, List.forIn_cons, step]
    simp only [bind, Except.bind, Functor.map, Except.map]
    cases g a c with
    | error e => rfl
    | ok r =>
      cases r with
      | done c' => rfl
      | yield c' =>
        have := forIn_rep rep f g step l (rep c') c' rfl
        simp only [Functor.map, Except.map] at this
        exact this

theorem buildSourceGroupsA_eq (inductive_ : Lean.InductiveVal → ExportM SourceDeclGroup)
    (deps : List Lean.Name → ExportM (List Lean.Name)) (declarations : List Lean.ConstantInfo) :
    buildSourceGroupsA inductive_ deps declarations = buildSourceGroupsP inductive_ deps declarations := by
  unfold buildSourceGroupsA buildSourceGroupsP
  dsimp only
  rw [forIn_rep Array.toList _ (buildStepA inductive_ deps) ?step declarations [] #[] rfl]
  · simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    cases forIn declarations #[] (buildStepA inductive_ deps) <;> rfl
  · intro ci c
    cases ci <;> simp only [buildStepA, singletonDeclaration]
    case inductInfo iv =>
      split
      · simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
        cases inductive_ iv <;> simp
      · rfl
    all_goals
      simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    all_goals
      cases exportSourceEntry _ with
      | error e => rfl
      | ok entry =>
        cases entry <;> simp only
        all_goals first
          | rfl
          | (cases deps _ <;> simp)

/-- **`buildSourceGroups` on the index, the DAG and an array.** -/
def buildSourceGroupsF (s : Source) : ExportM (List SourceDeclGroup) :=
  let idx := sourceIndex s
  let find := fun n => idx[n]?
  buildSourceGroupsA (exportSourceInductiveP find (sourceGroupDependenciesF find))
    (sourceGroupDependenciesF find) s.declarations

theorem buildSourceGroupsF_eq (s : Source) : buildSourceGroupsF s = buildSourceGroups s := by
  unfold buildSourceGroupsF
  simp only [buildSourceGroupsA_eq, sourceIndex_find]
  rw [show sourceGroupDependenciesF s.find = sourceGroupDependencies s from
    funext fun members => (sourceGroupDependenciesF_eq _ members).trans (sourceGroupDependenciesP_find s members)]
  rfl

/-! ## `SourceGroupsCover` with hash sets -/

/-- `SourceGroupsCover` decided with hash sets (M3's `nodupBy` for the members). -/
def coverFast (s : Source) (groups : List SourceDeclGroup) : Bool :=
  let members := groups.flatMap SourceDeclGroup.members
  let names := Std.HashSet.ofList s.names
  let memberSet := Std.HashSet.ofList members
  nodupBy {} members && s.names.all memberSet.contains && members.all names.contains &&
    groups.all fun g => decide (g.declaration.names = g.members.map sourceName)

theorem coverFast_sound {s : Source} {groups : List SourceDeclGroup} (h : coverFast s groups = true) :
    SourceGroupsCover s groups := by
  simp only [coverFast, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨nd, hnames⟩, hmembers⟩, hdecls⟩ := h
  exact ⟨nodup_of_nodupBy nd, fun n hn => mem_of_set (hnames n hn),
    fun n hn => mem_of_set (hmembers n hn), hdecls⟩

/-- `validateSourceGroups` deciding coverage with hash sets first; a refusal falls back to the
list decision, so the result is the same. -/
def validateSourceGroupsF (s : Source) (groups : List SourceDeclGroup) : ExportM (List SourceDeclGroup) :=
  if coverFast s groups then .ok groups else validateSourceGroups s groups

theorem validateSourceGroupsF_eq (s : Source) (groups : List SourceDeclGroup) :
    validateSourceGroupsF s groups = validateSourceGroups s groups := by
  unfold validateSourceGroupsF
  split
  · rename_i h
    simp [validateSourceGroups, coverFast_sound h]
  · rfl

/-- `exportSourceGroups` on the index, the DAG, an array and hash sets. -/
def exportSourceGroupsF (s : Source) : ExportM (List SourceDeclGroup) := do
  validateSourceGroupsF s (← buildSourceGroupsF s)

theorem exportSourceGroupsF_eq (s : Source) : exportSourceGroupsF s = exportSourceGroups s := by
  simp only [exportSourceGroupsF, exportSourceGroups, buildSourceGroupsF_eq, validateSourceGroupsF_eq]

/-- Compiled code runs the fast group export wherever it calls `exportSourceGroups`. -/
@[csimp] theorem exportSourceGroups_eq_fast : @exportSourceGroups = @exportSourceGroupsF := by
  funext s
  exact (exportSourceGroupsF_eq s).symm

/-! ## The order, with the available names in a hash set -/

/-- `orderSourceGroups` with a hash set of the available names. -/
def orderF : Nat → List SourceDeclGroup → Std.HashSet Lean.Name → List Kernel.Declaration →
    ExportM (List Kernel.Declaration)
  | _, [], _, output => .ok output
  | 0, _ :: _, _, _ => .error "source declaration scheduling budget exhausted"
  | fuel + 1, groups@(_ :: _), available, output => do
    let ready := groups.filter fun g => g.dependencies.all available.contains
    if ready.isEmpty then throw "source declaration dependencies are unresolved or cyclic"
    let pending := groups.filter fun g => !g.dependencies.all available.contains
    orderF fuel pending (ready.foldl (fun set g => g.members.foldl (·.insert ·) set) available)
      (output ++ ready.map SourceDeclGroup.declaration)

theorem foldl_insert_contains (set : Std.HashSet Lean.Name) :
    ∀ (names : List Lean.Name) (n : Lean.Name),
      (names.foldl (·.insert ·) set).contains n = (set.contains n || names.contains n)
  | [], n => by simp
  | m :: names, n => by
    rw [List.foldl_cons, foldl_insert_contains, Std.HashSet.contains_insert, List.contains_cons]
    have hb : (m == n) = (n == m) := by
      by_cases h : m = n
      · subst h; rfl
      · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]
    rw [hb]
    cases set.contains n <;> cases (n == m) <;> cases names.contains n <;> rfl

theorem foldl_groups_contains (set : Std.HashSet Lean.Name) :
    ∀ (ready : List SourceDeclGroup) (n : Lean.Name),
      (ready.foldl (fun set g => g.members.foldl (·.insert ·) set) set).contains n =
        (set.contains n || (ready.flatMap SourceDeclGroup.members).contains n)
  | [], n => by simp
  | g :: ready, n => by
    rw [List.foldl_cons, foldl_groups_contains, foldl_insert_contains, List.flatMap_cons,
      List.contains_append, Bool.or_assoc]

theorem orderF_eq : ∀ (fuel : Nat) (groups : List SourceDeclGroup) (set : Std.HashSet Lean.Name)
    (available : List Lean.Name) (output : List Kernel.Declaration),
    (∀ n, set.contains n = available.contains n) →
      orderF fuel groups set output = orderSourceGroups fuel groups available output
  | fuel, [], _, _, _, _ => by cases fuel <;> rfl
  | 0, _ :: _, _, _, _, _ => rfl
  | fuel + 1, g :: groups, set, available, output, same => by
    have hfun : set.contains = available.contains := funext same
    simp only [orderF, orderSourceGroups, hfun]
    simp only [bind, Except.bind]
    split
    · rfl
    · apply orderF_eq
      intro n
      rw [foldl_groups_contains, same, List.contains_append]

theorem orderF_empty (fuel : Nat) (groups : List SourceDeclGroup) :
    orderF fuel groups {} [] = orderSourceGroups fuel groups [] [] :=
  orderF_eq fuel groups {} [] [] (by intro n; simp)

/-- `exportSourceDeclarations` with the fast group export and the hash-set order. -/
def exportSourceDeclarationsF (s : Source) : ExportM (Array Kernel.Declaration) := do
  let groups ← exportSourceGroupsF s
  return (← orderF (groups.length + 1) groups {} []).toArray

theorem exportSourceDeclarationsF_eq (s : Source) :
    exportSourceDeclarationsF s = exportSourceDeclarations s := by
  simp only [exportSourceDeclarationsF, exportSourceDeclarations, exportSourceGroupsF_eq, orderF_empty]

/-- Compiled code runs the fast export wherever it calls `exportSourceDeclarations`. -/
@[csimp] theorem exportSourceDeclarations_eq_fast :
    @exportSourceDeclarations = @exportSourceDeclarationsF := by
  funext s
  exact (exportSourceDeclarationsF_eq s).symm

/-! ## Constants and declarations compared on the DAG -/

/-- Expression lists by `Kernel.Expr.beq`. -/
def exprsBeq : List Kernel.Expr → List Kernel.Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => Kernel.Expr.beq a b && exprsBeq as bs
  | _, _ => false

theorem exprsBeq_iff : ∀ {as bs : List Kernel.Expr}, exprsBeq as bs = true ↔ as = bs
  | [], [] => by simp [exprsBeq]
  | [], _ :: _ => by simp [exprsBeq]
  | _ :: _, [] => by simp [exprsBeq]
  | a :: as, b :: bs => by simp [exprsBeq, exprsBeq_iff, Kernel.Expr.beq]

/-- Projection tables by their fields, the bodies through `Kernel.Expr.beq`. -/
def projTableBeq (a b : Kernel.ProjTable) : Bool :=
  decide (a.structName = b.structName) && decide (a.levelParams = b.levelParams) &&
    decide (a.numParams = b.numParams) && decide (a.ctor = b.ctor) && decide (a.numFields = b.numFields) &&
    decide (a.structSort = b.structSort) && exprsBeq a.bodies.toList b.bodies.toList &&
    decide (a.guards = b.guards) && decide (a.off = b.off)

theorem projTableBeq_iff {a b : Kernel.ProjTable} : projTableBeq a b = true ↔ a = b := by
  cases a; cases b
  simp only [projTableBeq, Bool.and_eq_true, decide_eq_true_eq, exprsBeq_iff, Array.toList_inj,
    Kernel.ProjTable.mk.injEq, and_assoc]

/-- Constants by their fields, every expression through `Kernel.Expr.beq`. -/
def ciBeq : Kernel.ConstantInfo → Kernel.ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b => constantValBeq a b
  | .defnInfo a v h, .defnInfo b w k => constantValBeq a b && Kernel.Expr.beq v w && decide (h = k)
  | .thmInfo a v, .thmInfo b w => constantValBeq a b && Kernel.Expr.beq v w
  | .indInfo a c, .indInfo b d => constantValBeq a b && decide (c = d)
  | .ctorInfo a p f, .ctorInfo b q g => constantValBeq a b && decide (p = q) && decide (f = g)
  | .recInfo a m p rs, .recInfo b n q ss =>
    constantValBeq a b && decide (m = n) && decide (p = q) && recRulesBeq rs ss
  | .projInfo s, .projInfo t => projTableBeq s t
  | _, _ => false

theorem ciBeq_iff {a b : Kernel.ConstantInfo} : ciBeq a b = true ↔ a = b := by
  cases a <;> cases b <;>
    simp [ciBeq, constantValBeq_iff, recRulesBeq_iff, projTableBeq_iff, Kernel.Expr.beq, and_assoc]

def cisBeq : List Kernel.ConstantInfo → List Kernel.ConstantInfo → Bool
  | [], [] => true
  | a :: as, b :: bs => ciBeq a b && cisBeq as bs
  | _, _ => false

theorem cisBeq_iff : ∀ {as bs : List Kernel.ConstantInfo}, cisBeq as bs = true ↔ as = bs
  | [], [] => by simp [cisBeq]
  | [], _ :: _ => by simp [cisBeq]
  | _ :: _, [] => by simp [cisBeq]
  | a :: as, b :: bs => by simp [cisBeq, cisBeq_iff, ciBeq_iff]

/-- `Kernel.ConstantInfo` equality: a pointer test, then the fields on the DAG. -/
def ciDecEqShared (a b : Kernel.ConstantInfo) : Decidable (a = b) :=
  withPtrEqDecEq a b (fun _ => decidable_of_iff _ ciBeq_iff)

/-- Compiled code decides constant equality through `ciDecEqShared`. -/
@[csimp] theorem instDecidableEqConstantInfo_eq_shared :
    @Kernel.instDecidableEqConstantInfo = @ciDecEqShared := by
  funext a b
  exact Subsingleton.elim _ _

/-- Declarations by their fields, every expression through `Kernel.Expr.beq`. -/
def declBeq : Kernel.Declaration → Kernel.Declaration → Bool
  | .axiomDecl a, .axiomDecl b => constantValBeq a b
  | .defnDecl a v h, .defnDecl b w k => constantValBeq a b && Kernel.Expr.beq v w && decide (h = k)
  | .thmDecl a v, .thmDecl b w => constantValBeq a b && Kernel.Expr.beq v w
  | .opaqueDecl a v, .opaqueDecl b w => constantValBeq a b && Kernel.Expr.beq v w
  | .basisDecl k, .basisDecl l => decide (k = l)
  | .indDecl bs n, .indDecl cs m => cisBeq bs cs && decide (n = m)
  | .quotDecl k a, .quotDecl l b => decide (k = l) && constantValBeq a b
  | _, _ => false

theorem declBeq_iff {a b : Kernel.Declaration} : declBeq a b = true ↔ a = b := by
  cases a <;> cases b <;>
    simp [declBeq, constantValBeq_iff, cisBeq_iff, Kernel.Expr.beq, and_assoc]

/-- `Kernel.Declaration` equality: a pointer test, then the fields on the DAG. -/
def declDecEqShared (a b : Kernel.Declaration) : Decidable (a = b) :=
  withPtrEqDecEq a b (fun _ => decidable_of_iff _ declBeq_iff)

/-- Compiled code decides declaration equality through `declDecEqShared`. -/
@[csimp] theorem instDecidableEqDeclaration_eq_shared :
    @Kernel.instDecidableEqDeclaration = @declDecEqShared := by
  funext a b
  exact Subsingleton.elim _ _

end Ix.CompileCert
