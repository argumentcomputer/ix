import Ix.CompileCert.CheckCompiled

/-! # The indexed W check

`checkAssociation` decides every predicate of W over `List`s: a source or map
lookup is `List.find?`, made at every constant node of every exported
expression, and the stream membership of `DirectMatch` is list membership in
the whole reader output. That is fine on fixture cones and hopeless on a
library (Init+Std has about 98k addresses, Mathlib 783k).

This module decides the *same* propositions, and builds the *same*
`AcceptedAssociation`, through indexed procedures, each proved sound:

* **Small contexts.** A source declaration is exported in a small context
  `cy` whose source and map are sub-lists of the input's (taken from the
  input by untrusted index hints). Because the input's source names and map
  keys are unique (`DirectDomain`), every successful lookup in `cy` is the
  lookup in the full context (`Extends`), so every successful export in `cy`
  is the export in the full context (`directExport_refines`,
  `exportBlock_refines`, ...). Nothing about the hints is trusted: a wrong
  hint makes the small export fail, never succeed wrongly.
* **Hash sets** for the global facts (unique names, closure, map coverage,
  touched definition blocks), with `Std.HashSet.contains_ofList`.
* **Positions** for stream membership: a hinted position whose element is
  structurally equal (derived `DecidableEq`) to the expected entry.

The result is an `AcceptedAssociation`, so `faithful_sound`'s conclusion
follows from its fields (`checkIndexed_sound`). -/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-! ## Lookups in a sub-list of a list with unique keys -/

theorem nodup_map_inj {α β : Type} {key : β → α} : ∀ {L : List β}, (L.map key).Nodup →
    ∀ {x y : β}, x ∈ L → y ∈ L → key x = key y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | z :: L, nd, x, y, hx, hy, same => by
    rw [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨y, hy', same.symm⟩) nd.1
    · exact absurd (List.mem_map.mpr ⟨x, hx', same⟩) nd.1
    · exact nodup_map_inj nd.2 hx' hy' same

/-- A successful lookup in a sub-list is the lookup in the list, when keys
are unique in the list. -/
theorem find?_of_sub {α β : Type} (key : β → α) {L M : List β} (nodup : (L.map key).Nodup)
    (sub : ∀ x ∈ M, x ∈ L) {p : β → Bool} {n : α} (hp : ∀ x, p x = true ↔ key x = n) {x : β}
    (found : M.find? p = some x) : L.find? p = some x := by
  have hpx := List.find?_some found
  have hxL := sub x (List.mem_of_find?_eq_some found)
  cases hy : L.find? p with
  | none => exact absurd hpx (List.find?_eq_none.mp hy x hxL)
  | some y =>
    have hyL := List.mem_of_find?_eq_some hy
    have hpy := List.find?_some hy
    exact congrArg some (nodup_map_inj nodup hyL hxL (((hp y).mp hpy).trans ((hp x).mp hpx).symm))

theorem mem_of_hinted {α : Type} {L : List α} {hints : List Nat} {x : α}
    (h : x ∈ hints.filterMap (fun i => L.toArray[i]?)) : x ∈ L := by
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp h
  exact List.mem_toArray.mp (Array.mem_of_getElem? hi)

/-! ## Unique keys by hash set -/

def nodupBy {α : Type} [BEq α] [Hashable α] : Std.HashSet α → List α → Bool
  | _, [] => true
  | seen, a :: rest => !seen.contains a && nodupBy (seen.insert a) rest

theorem nodupBy_sound {α : Type} [BEq α] [Hashable α] [LawfulBEq α] :
    ∀ {seen : Std.HashSet α} {l : List α}, nodupBy seen l = true →
      l.Nodup ∧ ∀ a ∈ l, seen.contains a = false
  | _, [], _ => ⟨List.nodup_nil, by simp⟩
  | seen, a :: rest, h => by
    simp only [nodupBy, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨nd, fresh⟩ := nodupBy_sound h.2
    refine ⟨List.nodup_cons.mpr ⟨fun ha => ?_, nd⟩, ?_⟩
    · have := fresh a ha
      rw [Std.HashSet.contains_insert] at this
      simp at this
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact h.1
      · have := fresh b hb'
        rw [Std.HashSet.contains_insert] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.2

theorem nodup_of_nodupBy {α : Type} [BEq α] [Hashable α] [LawfulBEq α] {l : List α}
    (h : nodupBy {} l = true) : l.Nodup :=
  (nodupBy_sound h).1

theorem mem_of_set {α : Type} [BEq α] [Hashable α] [LawfulBEq α] {l : List α} {a : α}
    (h : (Std.HashSet.ofList l).contains a = true) : a ∈ l := by
  rw [Std.HashSet.contains_ofList] at h
  exact List.contains_iff_mem.mp h

theorem set_contains_iff {α : Type} [BEq α] [Hashable α] [LawfulBEq α] {l : List α} {a : α} :
    (Std.HashSet.ofList l).contains a = true ↔ a ∈ l := by
  rw [Std.HashSet.contains_ofList]
  exact List.contains_iff_mem

/-! ## A list's `all`, on several tasks

`allPar p workers l` evaluates `p` on every element of `l`, split into
`workers` strided sublists (element `j` goes to task `j % workers`, which
spreads the expensive declarations of one namespace over the tasks), each
conjoined in its own task. Success implies `l.all p` (`allPar_true`;
`Task.spawn fn` is `⟨fn ()⟩`), so a decision through it is a decision of the
same proposition; the tasks only change when the parts are evaluated. -/

/-- The elements of `l` (numbered from `j`) whose number is `i` modulo `w`. -/
def strideOf {α : Type} (w i : Nat) : Nat → List α → List α
  | _, [] => []
  | j, x :: xs => if j % w = i then x :: strideOf w i (j + 1) xs else strideOf w i (j + 1) xs

theorem mem_strideOf {α : Type} {w : Nat} (hw : 0 < w) :
    ∀ {j : Nat} {l : List α} {x : α}, x ∈ l → ∃ i, i < w ∧ x ∈ strideOf w i j l
  | j, y :: ys, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨j % w, Nat.mod_lt _ hw, by simp [strideOf]⟩
    · obtain ⟨i, hi, hm⟩ := mem_strideOf hw (j := j + 1) hx
      refine ⟨i, hi, ?_⟩
      unfold strideOf
      split
      · exact List.mem_cons_of_mem _ hm
      · exact hm

def allPar {α : Type} (p : α → Bool) (workers : Nat) (l : List α) : Bool :=
  ((List.range (max workers 1)).map
    fun i => Task.spawn fun _ => (strideOf (max workers 1) i 0 l).all p).all Task.get

theorem allPar_true {α : Type} {p : α → Bool} {workers : Nat} {l : List α}
    (h : allPar p workers l = true) : l.all p = true := by
  unfold allPar at h
  rw [List.all_map] at h
  have parts : ∀ i ∈ List.range (max workers 1),
      (strideOf (max workers 1) i 0 l).all p = true := fun i hi =>
    List.all_eq_true.mp h i hi
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, hm⟩ := mem_strideOf (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _))
    (j := 0) hx
  exact List.all_eq_true.mp (parts i (List.mem_range.mpr hi)) x hm

/-! ## Refinement of partial computations -/

/-- Every success of `x` is a success of `y`, with the same value. -/
def Refines {ε α : Type} (x y : Except ε α) : Prop := ∀ a, x = .ok a → y = .ok a

theorem throw_ne_ok {ε α : Type} (e : ε) (a : α) : (throw e : Except ε α) ≠ .ok a := by
  intro h; cases h

theorem Refines.rfl' {ε α : Type} (x : Except ε α) : Refines x x := fun _ h => h

theorem Refines.bind {ε α β : Type} {x y : Except ε α} {f g : α → Except ε β}
    (hx : Refines x y) (hf : ∀ a, Refines (f a) (g a)) : Refines (x >>= f) (y >>= g) := by
  intro b hb
  cases hxa : x with
  | error e => rw [hxa] at hb; exact absurd hb (by intro h; cases h)
  | ok a =>
    rw [hxa] at hb
    rw [hx a hxa]
    exact hf a b hb

theorem Refines.mapM {ε α β : Type} {f g : α → Except ε β} (h : ∀ a, Refines (f a) (g a)) :
    ∀ (l : List α), Refines (l.mapM f) (l.mapM g)
  | [] => Refines.rfl' _
  | a :: rest => by
    simp only [List.mapM_cons]
    exact Refines.bind (h a) fun b => Refines.bind (Refines.mapM h rest) fun _ => Refines.rfl' _

/-! ## Contexts that extend a small context -/

/-- Every successful lookup of `cy` is a lookup of `cx`. -/
structure Extends (cx cy : ExportContext) : Prop where
  source : ∀ n c, cy.source.find n = some c → cx.source.find n = some c
  map : ∀ n e, cy.map.find? (fun e => e.source == n) = some e →
    cx.map.find? (fun e => e.source == n) = some e
  pins : cy.pins = cx.pins

theorem Extends.mapFind {cx cy : ExportContext} (h : Extends cx cy) {n : Lean.Name}
    {r : Kernel.ConstRef Address} (hr : cy.map.find n = some r) : cx.map.find n = some r := by
  unfold SourceMap.find at hr ⊢
  cases he : cy.map.find? (fun e => e.source == n) with
  | none => simp [he] at hr
  | some e => rw [h.map n e he]; simpa [he] using hr

theorem memberName_refines {cx cy : ExportContext} (h : Extends cx cy) (n : Lean.Name) :
    Refines (cy.memberName n) (cx.memberName n) := by
  intro k hk
  unfold ExportContext.memberName at hk ⊢
  cases hr : cy.map.find n with
  | none => simp only [hr] at hk; exact absurd hk (throw_ne_ok _ _)
  | some r =>
    rw [h.mapFind hr, ← h.pins]
    simpa only [hr] using hk

theorem Refines.of_throw {ε α : Type} (e : ε) (y : Except ε α) : Refines (throw e) y :=
  fun _ h => absurd h (throw_ne_ok _ _)
theorem Refines.forIn {ε α β : Type} {f g : α → β → Except ε (ForInStep β)}
    (h : ∀ a b, Refines (f a b) (g a b)) : ∀ (l : List α) (init : β),
      Refines (forIn l init f) (forIn l init g)
  | [], _ => Refines.rfl' _
  | a :: rest, init => by
    simp only [List.forIn_cons]
    refine Refines.bind (h a init) fun r => ?_
    cases r with
    | done b => exact Refines.rfl' _
    | yield b => exact Refines.forIn h rest b

theorem Refines.of_throw_bind {ε α β : Type} (e : ε) (k : α → Except ε β) (y : Except ε β) :
    Refines (throw e >>= k) y :=
  fun _ h => absurd h (by intro h'; cases h')


theorem Refines.ite {ε α : Type} {c : Prop} [Decidable c] {a a' b b' : Except ε α}
    (h1 : c → Refines a b) (h2 : ¬c → Refines a' b') :
    Refines (if c then a else a') (if c then b else b') := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h1 hc
  · simp only [hc, ↓reduceIte]; exact h2 hc

theorem name_refines {cx cy : ExportContext} (h : Extends cx cy) (n : Lean.Name) :
    Refines (cy.name n) (cx.name n) := by
  unfold ExportContext.name
  cases hc : cy.source.find n with
  | none => exact Refines.of_throw _ _
  | some ci =>
    rw [h.source n ci hc]
    cases ci <;> dsimp only
    case recInfo v =>
      split
      all_goals first
        | exact Refines.of_throw _ _
        | exact Refines.ite
            (fun _ => Refines.bind (memberName_refines h _) fun _ => Refines.rfl' _)
            (fun _ => Refines.bind (Refines.rfl' _) fun _ =>
              Refines.bind (memberName_refines h _) fun _ => Refines.rfl' _)
    all_goals exact memberName_refines h n

theorem plainLevels_refines {cx cy : ExportContext} (h : Extends cx cy) (ci : Lean.ConstantInfo) :
    Refines (cy.plainLevels ci) (cx.plainLevels ci) := by
  unfold ExportContext.plainLevels
  cases hr : cy.map.find ci.name with
  | none => exact Refines.of_throw _ _
  | some r =>
    rw [h.mapFind hr, ← h.pins]
    exact Refines.rfl' _

/-- Close a refinement goal between two copies of the same program, one over
`cy`, one over `cx`, by its binds, conditionals and the lookup lemmas. -/
syntax "refines" : tactic

macro_rules
  | `(tactic| refines) => `(tactic| first
    | with_reducible exact Refines.rfl' _
    | with_reducible exact Refines.of_throw _ _
    | with_reducible exact Refines.of_throw_bind _ _ _
    | (refine Refines.ite (fun _ => ?_) (fun _ => ?_) <;> refines)
    | (refine Refines.bind ?_ (fun _ => ?_) <;> refines)
    | (refine Refines.mapM (fun _ => ?_) _ <;> refines)
    | (refine Refines.forIn (fun _ _ => ?_) _ _ <;> refines)
    | (split <;> first
        | (rename_i heq; rw [Extends.source ‹Extends _ _› _ _ heq]; dsimp only; refines)
        | refines))

macro_rules
  | `(tactic| refines) => `(tactic| first
    | with_reducible exact name_refines ‹Extends _ _› _
    | with_reducible exact memberName_refines ‹Extends _ _› _
    | with_reducible exact plainLevels_refines ‹Extends _ _› _)

theorem levels_refines {cx cy : ExportContext} (h : Extends cx cy) (ci : Lean.ConstantInfo) :
    Refines (cy.levels ci) (cx.levels ci) := by
  unfold ExportContext.levels
  cases ci <;> dsimp only
  case ctorInfo v =>
    cases hi : cy.source.find v.induct with
    | none => exact Refines.of_throw _ _
    | some ind => rw [h.source _ _ hi]; dsimp only; refines
  case recInfo v =>
    cases hr : cy.map.find (Lean.ConstantInfo.recInfo v).name with
    | none => exact Refines.of_throw _ _
    | some r =>
      rw [h.mapFind hr, ← h.pins]
      dsimp only
      split
      · refines
      · split
        · rename_i first _
          cases hi : cy.source.find first with
          | none => exact Refines.of_throw _ _
          | some ind => rw [h.source _ _ hi]; dsimp only; refines
        · exact Refines.of_throw _ _
  all_goals exact plainLevels_refines h _

theorem exportLevel_context (cx cy : ExportContext) (s : List Lean.Name) (t : List Kernel.Name) :
    exportLevel ⟨cy, s, t⟩ = exportLevel ⟨cx, s, t⟩ := rfl

theorem exportExpr_refines {cx cy : ExportContext} (h : Extends cx cy) (s : List Lean.Name)
    (t : List Kernel.Name) : ∀ e, Refines (exportExpr ⟨cy, s, t⟩ e) (exportExpr ⟨cx, s, t⟩ e)
  | .bvar _ => Refines.rfl' _
  | .sort u => by
    simp only [exportExpr]; rw [exportLevel_context cx cy]; exact Refines.rfl' _
  | .const n us => by
    simp only [exportExpr]; rw [exportLevel_context cx cy]
    exact Refines.bind (name_refines h n) fun _ => Refines.rfl' _
  | .app f a => by
    simp only [exportExpr]
    exact Refines.bind (exportExpr_refines h s t f) fun _ =>
      Refines.bind (exportExpr_refines h s t a) fun _ => Refines.rfl' _
  | .lam _ ty b _ => by
    simp only [exportExpr]
    exact Refines.bind (exportExpr_refines h s t ty) fun _ =>
      Refines.bind (exportExpr_refines h s t b) fun _ => Refines.rfl' _
  | .forallE _ ty b _ => by
    simp only [exportExpr]
    exact Refines.bind (exportExpr_refines h s t ty) fun _ =>
      Refines.bind (exportExpr_refines h s t b) fun _ => Refines.rfl' _
  | .letE _ ty v b _ => by
    simp only [exportExpr]
    exact Refines.bind (exportExpr_refines h s t ty) fun _ =>
      Refines.bind (exportExpr_refines h s t v) fun _ =>
        Refines.bind (exportExpr_refines h s t b) fun _ => Refines.rfl' _
  | .lit (.natVal _) => Refines.rfl' _
  | .lit (.strVal _) => Refines.rfl' _
  | .proj n _ e => by
    simp only [exportExpr]
    exact Refines.bind (name_refines h n) fun _ =>
      Refines.bind (exportExpr_refines h s t e) fun _ => Refines.rfl' _
  | .mdata _ e => by simp only [exportExpr]; exact exportExpr_refines h s t e
  | .fvar _ => Refines.of_throw _ _
  | .mvar _ => Refines.of_throw _ _

macro_rules
  | `(tactic| refines) => `(tactic| first
    | with_reducible exact levels_refines ‹Extends _ _› _
    | with_reducible exact exportExpr_refines ‹Extends _ _› _ _ _)


theorem directExport_refines {cx cy : ExportContext} (h : Extends cx cy) (ci : Lean.ConstantInfo) :
    Refines (directExport cy ci) (directExport cx ci) := by
  unfold directExport
  cases ci <;> dsimp only <;> refines


macro_rules
  | `(tactic| refines) => `(tactic| first
    | with_reducible exact directExport_refines ‹Extends _ _› _)

theorem exportBlock_refines {cx cy : ExportContext} (h : Extends cx cy) (owner : Lean.InductiveVal) :
    Refines (exportBlock cy owner) (exportBlock cx owner) := by
  unfold exportBlock
  dsimp only
  refines


/-! ## Transfer of the per-declaration predicates -/

theorem blockMatch_transfer {cx cy : ExportContext} (h : Extends cx cy) {state : State}
    {ci : Lean.ConstantInfo} (hb : BlockMatch cy state ci) : BlockMatch cx state ci := by
  cases ci with
  | inductInfo iv =>
    unfold BlockMatch at hb ⊢
    dsimp only at hb ⊢
    cases hn : cy.name iv.name <;> cases he : exportBlock cy iv <;> simp only [hn, he] at hb
    rw [name_refines h _ _ hn, exportBlock_refines h _ _ he]
    exact hb
  | _ => trivial

theorem optionMapM_transfer {α β : Type} {f g : α → Option β}
    (h : ∀ a b, f a = some b → g a = some b) :
    ∀ (l : List α) {r : List β}, l.mapM f = some r → l.mapM g = some r
  | [], _, hr => hr
  | a :: rest, r, hr => by
    simp only [List.mapM_cons, bind, Option.bind] at hr ⊢
    cases hf : f a with
    | none => simp [hf] at hr
    | some b =>
      rw [h a b hf]
      simp only [hf] at hr
      cases hm : rest.mapM f with
      | none => simp [hm] at hr
      | some bs =>
        rw [optionMapM_transfer h rest hm]
        simpa [hm] using hr

theorem groupImage_transfer {cx cy : ExportContext} (h : Extends cx cy) {ci : Lean.ConstantInfo}
    (hg : (definitionGroupImage cy ci).isSome = true) :
    (definitionGroupImage cx ci).isSome = true := by
  cases hm : definitionGroupImage cy ci with
  | none => simp [hm] at hg
  | some r =>
    have step : ∀ n b, (do return (n, ← cy.map.find n) : Option _) = some b →
        (do return (n, ← cx.map.find n) : Option _) = some b := by
      intro n b hb
      cases hf : cy.map.find n with
      | none => simp [hf] at hb
      | some t => rw [h.mapFind hf]; simpa [hf] using hb
    have hx : definitionGroupImage cx ci = some r := by
      unfold definitionGroupImage at hm ⊢
      exact optionMapM_transfer step _ hm
    rw [hx]; rfl

theorem nameAgrees_transfer {cx cy : ExportContext} (h : Extends cx cy) {n : Lean.Name}
    {target : Kernel.Name} (ha : NameAgrees cy n target) : NameAgrees cx n target := by
  unfold NameAgrees at ha ⊢
  cases hn : cy.name n with
  | error _ => simp [hn] at ha
  | ok k => rw [name_refines h n k hn]; simpa [hn] using ha

theorem sourceRecordFlags_transfer {cx cy : ExportContext} (h : Extends cx cy) {reader : Ctx}
    {e : MapEntry} (hf : sourceRecordFlags cy reader e = true) : sourceRecordFlags cx reader e = true := by
  unfold sourceRecordFlags at hf ⊢
  cases hs : cy.source.find e.source with
  | none => simp [hs] at hf
  | some c => rw [h.source _ _ hs]; simpa [hs] using hf

/-! ## Small contexts from position hints -/

/-- The source declarations and map entries at the given positions. The
positions are untrusted: they only decide which lookups can succeed. -/
def smallContext (srcArr : Array Lean.ConstantInfo) (mapArr : Array MapEntry) (pins : Pins)
    (sourceAt mapAt : List Nat) : ExportContext :=
  ⟨⟨sourceAt.filterMap (srcArr[·]?)⟩, mapAt.filterMap (mapArr[·]?), pins⟩

theorem smallContext_extends {cx : ExportContext} {srcArr : Array Lean.ConstantInfo}
    {mapArr : Array MapEntry} (hs : srcArr.toList = cx.source.declarations)
    (hm : mapArr.toList = cx.map) (nd : cx.source.names.Nodup)
    (ndm : (cx.map.map MapEntry.source).Nodup) (sourceAt mapAt : List Nat) :
    Extends cx (smallContext srcArr mapArr cx.pins sourceAt mapAt) where
  source n c found := by
    unfold Source.find at found ⊢
    refine find?_of_sub Lean.ConstantInfo.name nd (fun x hx => ?_) (fun x => beq_iff_eq) found
    obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hx
    rw [← hs]
    exact Array.mem_def.mp (Array.mem_of_getElem? hi)
  map n e found := by
    refine find?_of_sub MapEntry.source ndm (fun x hx => ?_) (fun x => beq_iff_eq) found
    obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hx
    rw [← hm]
    exact Array.mem_def.mp (Array.mem_of_getElem? hi)
  pins := rfl

/-! ## Stream membership and raw records by position -/

/-- The declaration's export in the small context is the entry at the hinted
position of the (hint-quotiented) reader stream. -/
def directAt (cy : ExportContext) (entries : Array DirectEntry) (position : Nat)
    (ci : Lean.ConstantInfo) : Bool :=
  match directExport cy ci with
  | .ok e => decide (entries[position]? = some e.withoutHint)
  | .error _ => false

theorem directAt_sound {cx cy : ExportContext} (h : Extends cx cy) {entries : Array DirectEntry}
    {stream : List DirectEntry} (he : entries.toList = compatibleEntries stream) {position : Nat}
    {ci : Lean.ConstantInfo} (hd : directAt cy entries position ci = true) :
    DirectMatch cx stream ci := by
  unfold directAt at hd
  cases hx : directExport cy ci with
  | error _ => simp [hx] at hd
  | ok e =>
    simp only [hx, decide_eq_true_eq] at hd
    unfold DirectMatch
    rw [directExport_refines h ci e hx]
    show e.withoutHint ∈ compatibleEntries stream
    rw [← he]
    exact Array.mem_def.mp (Array.mem_of_getElem? hd)

/-- The raw (pre-normalisation) reader reading of the declaration's own record,
found at the hinted position of the decoded records. -/
def rawAt (cy : ExportContext) (constants : Array (Address × Ixon.Constant)) (position : Nat)
    (reader : Ctx) (ci : Lean.ConstantInfo) : Bool :=
  match directExport cy ci, cy.map.find? (fun e => e.source == ci.name), constants[position]? with
  | .ok expected, some entry, some (owner, record) =>
    decide (owner = entry.record) && decide (RawEntryMatch reader owner record expected)
  | _, _, _ => false

theorem rawAt_sound {cx cy : ExportContext} (h : Extends cx cy)
    {constants : Array (Address × Ixon.Constant)} {decoded : List (Address × Ixon.Constant)}
    (hc : constants.toList = decoded) (nd : (decoded.map Prod.fst).Nodup) {position : Nat}
    {reader : Ctx} {ci : Lean.ConstantInfo} (hr : rawAt cy constants position reader ci = true) :
    RawSourceMatch cx reader decoded ci := by
  unfold rawAt at hr
  cases hx : directExport cy ci with
  | error _ => simp [hx] at hr
  | ok expected =>
    cases hm : cy.map.find? (fun e => e.source == ci.name) with
    | none => simp [hx, hm] at hr
    | some entry =>
      cases hp : constants[position]? with
      | none => simp [hx, hm, hp] at hr
      | some row =>
        obtain ⟨owner, record⟩ := row
        simp only [hx, hm, hp, Bool.and_eq_true, decide_eq_true_eq] at hr
        obtain ⟨same, matched⟩ := hr
        have mem : (owner, record) ∈ decoded := by
          rw [← hc]; exact Array.mem_def.mp (Array.mem_of_getElem? hp)
        have found : decoded.find? (fun p => decide (p.1 = entry.record)) = some (owner, record) :=
          find?_of_sub (M := [(owner, record)]) Prod.fst nd
            (fun x hx => (List.mem_singleton.mp hx) ▸ mem)
            (fun x => decide_eq_true_iff) (by simp [same])
        unfold RawSourceMatch
        rw [directExport_refines h ci expected hx]
        have hrec : rawSourceRecord cx decoded ci = some (owner, record) := by
          unfold rawSourceRecord
          rw [h.map _ _ hm]
          exact found
        rw [hrec]
        exact matched

/-! ## Global facts by hash set -/

/-- Every reference of an expression satisfies `p`: `exprRefs` without
building its list (one walk, no appends). -/
def refsIn (p : Lean.Name → Bool) : Lean.Expr → Bool
  | .const n _ => p n
  | .app f a => refsIn p f && refsIn p a
  | .lam _ t b _ | .forallE _ t b _ => refsIn p t && refsIn p b
  | .letE _ t v b _ => refsIn p t && refsIn p v && refsIn p b
  | .mdata _ b => refsIn p b
  | .proj n _ b => p n && refsIn p b
  | .lit (.natVal _) => p `Nat && p `Nat.zero && p `Nat.succ
  | .lit (.strVal _) => p `String && p `String.ofList && p `List && p `List.nil &&
      p `List.cons && p `Char && p `Char.ofNat
  | _ => true

theorem refsIn_sound {p : Lean.Name → Bool} :
    ∀ {e : Lean.Expr}, refsIn p e = true → ∀ n ∈ exprRefs e, p n = true
  | .const _ _, h, n, hn => by simp_all [refsIn, exprRefs]
  | .app f a, h, n, hn => by
    simp only [refsIn, Bool.and_eq_true] at h
    simp only [exprRefs, List.mem_append] at hn
    exact hn.elim (refsIn_sound h.1 n) (refsIn_sound h.2 n)
  | .lam _ t b _, h, n, hn | .forallE _ t b _, h, n, hn => by
    simp only [refsIn, Bool.and_eq_true] at h
    simp only [exprRefs, List.mem_append] at hn
    exact hn.elim (refsIn_sound h.1 n) (refsIn_sound h.2 n)
  | .letE _ t v b _, h, n, hn => by
    simp only [refsIn, Bool.and_eq_true] at h
    simp only [exprRefs, List.mem_append] at hn
    rcases hn with (hn | hn) | hn
    · exact refsIn_sound h.1.1 n hn
    · exact refsIn_sound h.1.2 n hn
    · exact refsIn_sound h.2 n hn
  | .mdata _ b, h, n, hn => refsIn_sound (e := b) h n hn
  | .proj _ _ b, h, n, hn => by
    simp only [refsIn, Bool.and_eq_true] at h
    simp only [exprRefs, List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact h.1
    · exact refsIn_sound h.2 n hn
  | .lit (.natVal _), h, n, hn => by
    simp only [refsIn, Bool.and_eq_true] at h
    simp only [exprRefs, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;> simp_all
  | .lit (.strVal _), h, n, hn => by
    simp only [refsIn, Bool.and_eq_true] at h
    simp only [exprRefs, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  | .bvar _, _, n, hn | .fvar _, _, n, hn | .mvar _, _, n, hn | .sort _, _, n, hn => by
    simp [exprRefs] at hn

/-- Every name of `declarationRefs c` satisfies `p`, without building it. -/
def declRefsIn (p : Lean.Name → Bool) (c : Lean.ConstantInfo) : Bool :=
  refsIn p c.type && match c with
  | .defnInfo v => v.all.all p && refsIn p v.value
  | .thmInfo v => v.all.all p && refsIn p v.value
  | .opaqueInfo v => v.all.all p && refsIn p v.value
  | .recInfo v =>
    (v.all ++ v.all.map (·.str "rec") ++
      (List.range (v.numMotives - v.all.length)).filterMap
        (fun i => v.all.head?.map (·.str s!"rec_{i + 1}"))).all p &&
    v.rules.all (fun r => p r.ctor && refsIn p r.rhs)
  | c => (declarationRefs c).all p

theorem declRefsIn_sound {p : Lean.Name → Bool} {c : Lean.ConstantInfo}
    (h : declRefsIn p c = true) : ∀ n ∈ declarationRefs c, p n = true := by
  intro n hn
  unfold declRefsIn at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨ht, hc⟩ := h
  unfold declarationRefs at hn
  rw [List.mem_append] at hn
  rcases hn with hn | hn
  · exact refsIn_sound ht n hn
  cases c <;> simp only [List.all_eq_true, Bool.and_eq_true] at hc
  case defnInfo v | thmInfo v | opaqueInfo v =>
    simp only [List.mem_append] at hn
    exact hn.elim (hc.1 n) (refsIn_sound hc.2 n)
  case recInfo v =>
    simp only [List.mem_append, List.mem_flatMap, List.mem_cons] at hn
    rcases hn with hn | ⟨r, hr, rfl | hn⟩
    · exact hc.1 n (by simpa only [List.mem_append] using hn)
    · exact (hc.2 r hr).1
    · exact refsIn_sound (hc.2 r hr).2 n hn
  all_goals (first
    | exact hc n (by simp only [declarationRefs, List.mem_append]; exact .inr hn)
    | simp_all [declarationRefs])

/-- `DirectDomain` decided with hash sets. -/
def domainFast (workers : Nat) (s : Source) (roots : List Lean.Name) (m : SourceMap) : Bool :=
  let names := Std.HashSet.ofList s.names
  let keys := Std.HashSet.ofList (m.map MapEntry.source)
  nodupBy {} s.names && roots.all names.contains &&
    allPar (fun c => declRefsIn names.contains c) workers s.declarations &&
    nodupBy {} (m.map MapEntry.source) && s.names.all keys.contains &&
    m.all (fun e => names.contains e.source) &&
    m.all (fun e => e.record.hash.size == 32 && e.target.block.hash.size == 32)

theorem domainFast_sound {workers : Nat} {s : Source} {roots : List Lean.Name} {m : SourceMap}
    (h : domainFast workers s roots m = true) : DirectDomain s roots m := by
  simp only [domainFast, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨nd, hroots⟩, hrefs⟩, ndm⟩, hcover⟩, hkeys⟩, hsize⟩ := h
  have hrefs := List.all_eq_true.mp (allPar_true hrefs)
  simp only [List.all_eq_true] at hroots hcover hkeys hsize
  refine ⟨⟨nodup_of_nodupBy nd, fun n hn => mem_of_set (hroots n hn),
    fun c hc n hn => mem_of_set (declRefsIn_sound (hrefs c hc) n hn)⟩,
    nodup_of_nodupBy ndm, fun n hn => mem_of_set (hcover n hn),
    fun e he => mem_of_set (hkeys e he), fun e he => ?_⟩
  simpa only [Bool.and_eq_true, beq_iff_eq] using hsize e he

/-- A hash set of addresses under their decidable equality (the derived `BEq`
of `Address` is not known lawful). -/
abbrev AddressSet := @Std.HashSet Address instBEqOfDecidableEq instHashableAddress

def addressSet (l : List Address) : AddressSet :=
  @Std.HashSet.ofList Address instBEqOfDecidableEq _ l

def addressIn (s : AddressSet) (a : Address) : Bool :=
  @Std.HashSet.contains Address instBEqOfDecidableEq _ s a

theorem addressIn_set {l : List Address} {a : Address} :
    addressIn (addressSet l) a = true ↔ a ∈ l := by
  unfold addressIn addressSet
  exact @set_contains_iff Address instBEqOfDecidableEq _ _ l a

def addressesNodup (l : List Address) : Bool :=
  @nodupBy Address instBEqOfDecidableEq _ {} l

theorem addressesNodup_sound {l : List Address} (h : addressesNodup l = true) : l.Nodup :=
  @nodup_of_nodupBy Address instBEqOfDecidableEq _ _ l h

/-- `definitionBlockCovered` with the map's touched blocks and targets in hash
sets. -/
def coveredFast (blocks : AddressSet) (targets : Std.HashSet (Kernel.ConstRef Address))
    (owner : Address) (record : Ixon.Constant) : Bool :=
  match record.info with
  | .muts members =>
    if members.all (fun | .defn _ => true | _ => false) && addressIn blocks owner then
      (List.range members.size).all fun index => targets.contains (.member owner index)
    else true
  | _ => true

theorem coveredFast_eq (cx : ExportContext) (owner : Address) (record : Ixon.Constant) :
    coveredFast (addressSet (cx.map.map (·.target.block)))
      (Std.HashSet.ofList (cx.map.map MapEntry.target)) owner record =
      definitionBlockCovered cx owner record := by
  have touched : addressIn (addressSet (cx.map.map (·.target.block))) owner =
      cx.map.any (fun e => decide (e.target.block = owner)) := by
    apply Bool.eq_iff_iff.mpr
    rw [addressIn_set, List.any_eq_true, List.mem_map]
    constructor
    · rintro ⟨e, he, same⟩; exact ⟨e, he, decide_eq_true same⟩
    · rintro ⟨e, he, same⟩; exact ⟨e, he, of_decide_eq_true same⟩
  have member : ∀ index, (Std.HashSet.ofList (cx.map.map MapEntry.target)).contains
      (.member owner index) = cx.map.any (fun e => decide (e.target = .member owner index)) := by
    intro index
    apply Bool.eq_iff_iff.mpr
    rw [set_contains_iff, List.any_eq_true, List.mem_map]
    constructor
    · rintro ⟨e, he, same⟩; exact ⟨e, he, decide_eq_true same⟩
    · rintro ⟨e, he, same⟩; exact ⟨e, he, of_decide_eq_true same⟩
  unfold coveredFast definitionBlockCovered
  cases record.info with
  | muts members => simp only [touched, member]; rfl
  | _ => rfl

/-! ## The indexed association -/

/-- Untrusted position hints, per source name: the positions (in the source
and in the map) of the declarations and entries its export reads, its position
in the reader stream, and the position of its record. -/
structure Hints where
  sourceAt : Lean.Name → List Nat
  mapAt : Lean.Name → List Nat
  entryAt : Lean.Name → Nat
  recordAt : Lean.Name → Nat
  /-- How many tasks evaluate the per-declaration checks (`allPar`). -/
  workers : Nat := 1

/-- What every per-declaration check shares, computed once. -/
structure Shared where
  cx : ExportContext
  reader : Ctx
  state : State
  srcArr : Array Lean.ConstantInfo
  mapArr : Array MapEntry
  entries : Array DirectEntry
  constants : Array (Address × Ixon.Constant)

def Shared.small (sh : Shared) (hints : Hints) (n : Lean.Name) : ExportContext :=
  smallContext sh.srcArr sh.mapArr sh.cx.pins (hints.sourceAt n) (hints.mapAt n)

/-- One source declaration: correspondence (direct or raw), its inductive
block, and its definition group's map coverage, all in its small context. -/
def Shared.declCheck (sh : Shared) (hints : Hints) (ci : Lean.ConstantInfo) : Bool :=
  let cy := sh.small hints ci.name
  (directAt cy sh.entries (hints.entryAt ci.name) ci ||
    rawAt cy sh.constants (hints.recordAt ci.name) sh.reader ci) &&
  decide (BlockMatch cy sh.state ci) && (definitionGroupImage cy ci).isSome

/-- One map entry: its record resolves to its target, the target's reader name
is the source's exported name, and recursor flags agree. -/
def Shared.entryCheck (sh : Shared) (hints : Hints) (e : MapEntry) : Bool :=
  let cy := sh.small hints e.source
  decide (resolve sh.reader.store e.record = some e.target) &&
    decide (NameAgrees cy e.source (sh.reader.nameOf e.target)) && sourceRecordFlags cy sh.reader e

def Shared.ofArtifact (input : Input) (artifact : AdmittedArtifact input.toArtifactInput) : Shared :=
  { cx := ⟨input.source, input.map, artifact.pins⟩
    reader := streamContext artifact.pins artifact.prelude artifact.constants input.blobs input.hint
    state := artifact.readerState
    srcArr := input.source.declarations.toArray
    mapArr := input.map.toArray
    entries := (compatibleEntries (streamEntries artifact.declarations)).toArray
    constants := artifact.constants.toArray }

theorem Shared.small_extends {input : Input} {artifact : AdmittedArtifact input.toArtifactInput}
    (domain : DirectDomain input.source input.roots input.map) (hints : Hints) (n : Lean.Name) :
    Extends (Shared.ofArtifact input artifact).cx ((Shared.ofArtifact input artifact).small hints n) :=
  smallContext_extends (List.toList_toArray) (List.toList_toArray) domain.1.1 domain.2.1 _ _

/-- `checkAssociation`'s propositions, decided by the indexed procedures. The
result is the same `AcceptedAssociation`. -/
def checkIndexed (input : Input) (artifact : AdmittedArtifact input.toArtifactInput)
    (hints : Hints) : Except Decline (AcceptedAssociation input) :=
  if hd : domainFast hints.workers input.source input.roots input.map = true then
    let sh := Shared.ofArtifact input artifact
    if hm : input.map.all (sh.entryCheck hints) = true then
      if hn : addressesNodup (artifact.constants.map Prod.fst) = true then
        if hs : allPar (sh.declCheck hints) hints.workers input.source.declarations = true then
          let blocks := addressSet (input.map.map (·.target.block))
          let targets := Std.HashSet.ofList (input.map.map MapEntry.target)
          if hg : artifact.constants.all (fun row => coveredFast blocks targets row.1 row.2) = true then
            have domain := domainFast_sound hd
            have ext := Shared.small_extends (artifact := artifact) domain hints
            .ok ⟨artifact, domain,
              fun e he => by
                have c := List.all_eq_true.mp hm e he
                simp only [Shared.entryCheck, Bool.and_eq_true, decide_eq_true_eq] at c
                exact ⟨c.1.1, nameAgrees_transfer (ext e.source) c.1.2,
                  sourceRecordFlags_transfer (ext e.source) c.2⟩,
              fun ci hci => by
                have c := List.all_eq_true.mp (allPar_true hs) ci hci
                simp only [Shared.declCheck, Bool.and_eq_true, Bool.or_eq_true] at c
                rcases c.1.1 with direct | raw
                · exact .inl (directAt_sound (ext ci.name) List.toList_toArray direct)
                · exact .inr (rawAt_sound (ext ci.name) List.toList_toArray
                    (addressesNodup_sound hn) raw),
              fun ci hci => by
                have c := List.all_eq_true.mp (allPar_true hs) ci hci
                simp only [Shared.declCheck, Bool.and_eq_true, decide_eq_true_eq] at c
                exact blockMatch_transfer (ext ci.name) c.1.2,
              ⟨fun ci hci => by
                have c := List.all_eq_true.mp (allPar_true hs) ci hci
                simp only [Shared.declCheck, Bool.and_eq_true] at c
                exact groupImage_transfer (ext ci.name) c.2,
              fun row hrow => by
                have c := List.all_eq_true.mp hg row hrow
                rw [← coveredFast_eq]
                exact c⟩⟩
          else .error .definitionGroupCorrespondence
        else .error .correspondence
      else .error (.setup "decoded records repeat an address")
    else .error .mapMismatch
  else .error .sourceDomain

/-- Every accepted association, however decided, carries `faithful_sound`'s
conclusion: admission of the exact bytes, the closed domain, source
correspondence in the reader stream, whole-block correspondence and
definition-group coverage. -/
theorem AcceptedAssociation.faithful {input : Input} (accepted : AcceptedAssociation input) :
    checkBytes input.limits input.records input.blobs input.hint = .ok accepted.env ∧
    DirectDomain input.source input.roots input.map ∧
    SourceCorrespondence ⟨input.source, input.map, accepted.pins⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      accepted.constants accepted.declarations ∧
    BlockCorrespondence ⟨input.source, input.map, accepted.pins⟩ accepted.readerState ∧
    DefinitionGroupsCovered ⟨input.source, input.map, accepted.pins⟩ accepted.constants :=
  ⟨accepted.admitted, accepted.domain, accepted.correspondence,
    accepted.block_correspondence, accepted.definition_groups⟩

/-- **What a Certified verdict means.** Success of the indexed check implies
the conclusion of `faithful_sound` for the whole input, hence for every source
declaration in it. -/
theorem checkIndexed_sound {input : Input} {artifact : AdmittedArtifact input.toArtifactInput}
    {hints : Hints} {accepted : AcceptedAssociation input}
    (_h : checkIndexed input artifact hints = .ok accepted) :
    checkBytes input.limits input.records input.blobs input.hint = .ok accepted.env ∧
    DirectDomain input.source input.roots input.map ∧
    SourceCorrespondence ⟨input.source, input.map, accepted.pins⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      accepted.constants accepted.declarations ∧
    BlockCorrespondence ⟨input.source, input.map, accepted.pins⟩ accepted.readerState ∧
    DefinitionGroupsCovered ⟨input.source, input.map, accepted.pins⟩ accepted.constants :=
  accepted.faithful

end Ix.CompileCert
