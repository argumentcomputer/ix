import Ix.CompileCert.Loop
import Ix.CompileCert.InductiveReading
import Ix.CompileCert.MutualArtifact
import Ix.LeanIngress

/-! # What Source mode admits of an inductive block (R12)

The donor's `SourceConstructorPositions` read constructor positions off the
old source export (CT-02's `SourceExportFast`). Source mode is now
`Ix.LeanIngress`, which reads the compiler's own input, an `Ix.Environment`:
an inductive block is a group (`inductiveGroup`, Lean's layout checked) and
its conversion (`convertInductive`, the reader's checks). This file reads
what those two functions check:

* **positions** (`inductiveGroup_spec`): every member is in the environment
  as an inductive of the block, and its constructors are in the
  environment, in order, each at its position (`cidx = j`);
* **safety, parameters and telescopes** (`convertInductive_spec`): no
  member or constructor is unsafe, the members share `numParams`, and each
  constructor's type converts (`Ix.LeanIngress.ingressExpr`) to a term with
  exactly `numParams + numFields` leading binders; such a type is a source
  telescope of that many binders ending in a non-binder
  (`strip_of_ingress`), the form `InductiveReading.inductive_reads` asks
  for;
* **the compiler resolves the same constructors** (`collect_lookups`,
  `mkIndc_lookups`): `lookupInductiveConstructors` and `MutConst.mkIndc`
  look each constructor name up in the compile environment, so where that
  environment agrees with Source's on the block (`Ix.Cert.compile` compiles
  the environment Source mode checks) they return Source's constructors.

`inductive_reads_source` is `InductiveReading.inductive_reads` with its
safety, position and telescope premises discharged by Source admission of
the block (`Admits`: the block's group converts). `mkIndc_positions` gives
R9a's `MutualProjections.ConstructorPositions` for the compiler's mutual
members.

**What remains** (N-READS): the self references (`scope`, `ctorScope`):
that the family's name reads as its key (`names`, R13's published maps),
and that no constructor of the family occurs in the family's own types. The
ingress does not check the latter; the fold does, when it types the
inductive before its constructors exist, so it is a fact of Source
acceptance through `Ix.Kernel.Cached.checkDecls`, not of the ingress. And
Source acceptance (`checkSource … = .ok _`) reaches a group's conversion
only through the schedule (`Ix.LeanIngress.scheduleOf`), whose order
(`orderOf`) is a `while` loop and so has no unfolding: `Admits` is the
group's own conversion, which is what the schedule requires of it. -/

namespace Ix.CompileCert.SourceConstructorPositions

open Ix.LeanIngress (Group Converted inductiveGroup convertInductive Numbering)
open Ix.Kernel.Reader (ReadError piTeleLen)
open Ix.CompileCert.Loop

/-! ## The group: Lean's layout -/

/-- The value `inductiveGroup` records for a block member `n`: the
inductive the environment has under `n`, if it names the block. -/
def memberValue (env : Ix.Environment) (block : Array Ix.Name) (n : Ix.Name) : Option Ix.InductiveVal :=
  match env.consts.get? n with
  | some (.inductInfo v) => if (v.all.isEqv block Ix.Name.beqRaw) = true then some v else none
  | _ => none

/-- The value `inductiveGroup` records for the constructor `x.1` of `owner`
at position `x.2`: the constructor the environment has under that name, if
it names `owner` and declares that position. -/
def ctorValue (env : Ix.Environment) (owner : Ix.Name) (x : Ix.Name × Nat) : Option Ix.ConstructorVal :=
  match env.consts.get? x.1 with
  | some (.ctorInfo cv) =>
    if (Ix.Name.beqRaw cv.induct owner) = true then if (cv.cidx == x.2) = true then some cv else none
    else none
  | _ => none

/-- An invalid group. -/
def Invalid (g : Group) : Prop := ∃ names e, g = .invalid names e

theorem memberValue_some {env : Ix.Environment} {block : Array Ix.Name} {n : Ix.Name} {v : Ix.InductiveVal}
    (value : memberValue env block n = some v) :
    env.consts.get? n = some (.inductInfo v) ∧ (v.all.isEqv block Ix.Name.beqRaw) = true := by
  unfold memberValue at value
  split at value
  · rename_i w found
    by_cases same : (w.all.isEqv block Ix.Name.beqRaw) = true
    · simp only [same, ite_true, Option.some.injEq] at value
      subst value
      exact ⟨found, same⟩
    · simp only [same] at value
      cases value
  · cases value

theorem ctorValue_some {env : Ix.Environment} {owner : Ix.Name} {x : Ix.Name × Nat} {cv : Ix.ConstructorVal}
    (value : ctorValue env owner x = some cv) :
    env.consts.get? x.1 = some (.ctorInfo cv) ∧ (Ix.Name.beqRaw cv.induct owner) = true ∧ cv.cidx = x.2 := by
  unfold ctorValue at value
  split at value
  · rename_i w found
    by_cases owned : (Ix.Name.beqRaw w.induct owner) = true
    · by_cases placed : (w.cidx == x.2) = true
      · simp only [owned, placed, ite_true, Option.some.injEq] at value
        subst value
        exact ⟨found, owned, by simpa using placed⟩
      · simp only [owned, placed, ite_true] at value
        cases value
    · simp only [owned] at value
      cases value
  · cases value

/-- The constructors' values of `owner`, in order, if every one has one. -/
def ctorsValue (env : Ix.Environment) (owner : Ix.Name) : List (Ix.Name × Nat) → Option (List Ix.ConstructorVal)
  | [] => some []
  | x :: xs =>
    match ctorValue env owner x, ctorsValue env owner xs with
    | some b, some bs => some (b :: bs)
    | _, _ => none

theorem ctorsValue_forall₂ (env : Ix.Environment) (owner : Ix.Name) :
    ∀ {l : List (Ix.Name × Nat)} {bs : List Ix.ConstructorVal},
      ctorsValue env owner l = some bs ↔ List.Forall₂ (fun x b => ctorValue env owner x = some b) l bs := by
  intro l
  induction l with
  | nil =>
    intro bs
    cases bs with
    | nil => simp [ctorsValue]
    | cons b bs =>
      constructor
      · intro value; cases value
      · intro holds; cases holds
  | cons x l ih =>
    intro bs
    unfold ctorsValue
    constructor
    · intro value
      split at value
      · rename_i b rest head tail
        cases value
        exact .cons head (ih.mp tail)
      · cases value
    · intro holds
      cases holds with
      | cons head tail =>
        rw [head, ih.mpr tail]

/-- The value `inductiveGroup` records for a member's constructors. -/
def classValue (env : Ix.Environment) (v : Ix.InductiveVal) : Option (Array Ix.ConstructorVal) :=
  (ctorsValue env v.cnst.name v.ctors.zipIdx.toList).map List.toArray

theorem forall₂_some_unique {α β : Type} {H : α → Option β} :
    ∀ {l : List α} {bs cs : List β}, List.Forall₂ (fun x b => H x = some b) l bs →
      List.Forall₂ (fun x b => H x = some b) l cs → bs = cs := by
  intro l bs cs left right
  induction left generalizing cs with
  | nil => cases right; rfl
  | cons head _ ih =>
    cases right with
    | cons head' tail' =>
      rw [head] at head'
      cases head'
      rw [ih tail']

set_option hygiene false in
/-- The member loop's step obligations, on its inline step. -/
local macro "member_step" : tactic => `(tactic| (
  intro n p
  refine ⟨fun b value => ?_, fun value => ?_⟩
  · obtain ⟨found, same⟩ := memberValue_some value
    simp only [found, same, ite_true]
  · unfold memberValue at value
    cases found : env.consts.get? n with
    | none => simp only; exact ⟨_, _, rfl, _, _, rfl⟩
    | some ci =>
      rw [found] at value
      cases ci with
      | inductInfo v =>
        by_cases same : (v.all.isEqv first.all Ix.Name.beqRaw) = true
        · simp only [same, ite_true] at value; cases value
        · simp only [same]; exact ⟨_, _, rfl, _, _, rfl⟩
      | _ => simp only; exact ⟨_, _, rfl, _, _, rfl⟩))

set_option hygiene false in
/-- The constructor loop's step obligations, on its inline step, for the
member `v`. -/
local macro "ctor_step" : tactic => `(tactic| (
  intro x q
  refine ⟨fun b value => ?_, fun value => ?_⟩
  · obtain ⟨found, owned, placed⟩ := ctorValue_some value
    simp only [found, owned, placed, beq_self_eq_true, ite_true]
  · unfold ctorValue at value
    cases found : env.consts.get? x.1 with
    | none => simp only; exact ⟨_, _, rfl, _, _, rfl⟩
    | some ci =>
      rw [found] at value
      cases ci with
      | ctorInfo cv =>
        by_cases owned : (Ix.Name.beqRaw cv.induct v.cnst.name) = true
        · by_cases placed : (cv.cidx == x.2) = true
          · simp only [owned, placed, ite_true] at value; cases value
          · simp only [owned, placed, ite_true]; exact ⟨_, _, rfl, _, _, rfl⟩
        · simp only [owned]; exact ⟨_, _, rfl, _, _, rfl⟩
      | _ => simp only; exact ⟨_, _, rfl, _, _, rfl⟩))

set_option hygiene false in
/-- The member-constructors loop's step obligations, on its inline step. -/
local macro "class_step" : tactic => `(tactic| (
  intro v p
  refine ⟨fun cs value => ?_, fun value => ?_⟩
  · obtain ⟨l, found, rfl⟩ := Option.map_eq_some_iff.mp value
    have holds := (ctorsValue_forall₂ env v.cnst.name).mp found
    split
    · rename_i r heq
      exact (no_exit (R := Invalid) (H := ctorValue env v.cnst.name) heq (by ctor_step) holds).elim
    · rename_i heq
      obtain ⟨bs, values, pushed⟩ := pushed_of_fst (R := Invalid) (H := ctorValue env v.cnst.name) heq
        (by ctor_step)
      rw [pushed, forall₂_some_unique values holds]
      simp
  · split
    · rename_i r heq
      exact ⟨r, _, rfl, exit_of_fst (R := Invalid) (H := ctorValue env v.cnst.name) heq (by ctor_step)⟩
    · rename_i heq
      obtain ⟨bs, values, _⟩ := pushed_of_fst (R := Invalid) (H := ctorValue env v.cnst.name) heq
        (by ctor_step)
      have found := (ctorsValue_forall₂ env v.cnst.name).mpr values
      unfold classValue at value
      rw [found] at value
      cases value))

/-- **What `inductiveGroup` checks**: a block group `.inductive types ctors
recs` lists the block's members, each the inductive the environment has
under its name, naming the block (`memberValue`); and each member's
constructors, each the constructor the environment has under the member's
constructor name at that position, naming the member, with that position as
its index (`classValue`, `ctorValue`). The names are compared structurally
(`Ix.Name.beqRaw`, CQ2.25), the positions exactly. -/
theorem inductiveGroup_spec (env : Ix.Environment) (first : Ix.InductiveVal) (cands : Array Ix.RecursorVal)
    (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal)) (recs : Array Ix.RecursorVal)
    (h : inductiveGroup env first cands = .inductive types ctors recs) :
    List.Forall₂ (fun n v => memberValue env first.all n = some v) first.all.toList types.toList ∧
      List.Forall₂ (fun v cs => classValue env v = some cs) types.toList ctors.toList := by
  unfold inductiveGroup at h
  simp only [Id.run, idBind, idPure] at h
  split at h
  · rename_i r heq
    obtain ⟨_, _, rfl⟩ := exit_of_fst (R := Invalid) (H := memberValue env first.all) heq (by member_step)
    cases h
  · rename_i none₁
    obtain ⟨bs, members, pushed⟩ := pushed_of_fst (R := Invalid) (H := memberValue env first.all) none₁
      (by member_step)
    split at h
    · rename_i r heq
      obtain ⟨_, _, rfl⟩ := exit_of_fst (R := Invalid) (H := classValue env) heq (by class_step)
      cases h
    · rename_i none₂
      obtain ⟨css, classes, pushed₂⟩ := pushed_of_fst (R := Invalid) (H := classValue env) none₂
        (by class_step)
      split at h
      · injection h with typesEq ctorsEq _
        rw [pushed] at typesEq classes
        rw [pushed₂] at ctorsEq
        subst typesEq ctorsEq
        simp only [Array.toList_append, List.nil_append] at classes ⊢
        exact ⟨members, classes⟩
      · cases h

/-! ## The conversion: the reader's checks -/

section Conversion

open Ix.LeanIngress (ingressExpr ingressExprs nameExprs exprsOf)

/-- A term Source mode converted: some numbering's conversion of the
item's term (the batching compares numberings structurally, so the numbering
used is an equal one; the statement does not depend on which). -/
def Converts (item : Numbering × Ix.Expr) (k : Ix.Kernel.Reader.CExpr .source) : Prop :=
  ∃ τ : Numbering, ingressExpr τ.pos item.2 = .ok k

/-- `exprsOf`'s loop invariant over the items processed: the conversions
written so far are of the items before the pending run, and the pending
run's terms are the rest. -/
def ExprsInv (pre : List (Numbering × Ix.Expr))
    (s : Array (Ix.Kernel.Reader.CExpr .source) × Option (Numbering × Array Ix.Expr)) : Prop :=
  ∃ done pend, pre = done ++ pend ∧ List.Forall₂ Converts done s.1.toList ∧
    match s.2 with
    | none => pend = []
    | some (_, es) => pend.map Prod.snd = es.toList

theorem flush_ok {τ : Numbering} {es : Array Ix.Expr} {out out' : Array (Ix.Kernel.Reader.CExpr .source)}
    {done pend : List (Numbering × Ix.Expr)} (prior : List.Forall₂ Converts done out.toList)
    (terms : pend.map Prod.snd = es.toList)
    (ran : (match ingressExprs τ.pos es.toList with
      | .ok ks => Except.ok (out ++ (nameExprs es.toList ks).toArray)
      | .error e => Except.error (ReadError.malformed (toString "source term: " ++ toString e))) = .ok out') :
    List.Forall₂ Converts (done ++ pend) out'.toList := by
  split at ran
  · rename_i ks converted
    cases ran
    rw [Ix.LeanIngress.nameExprs_eq, Array.toList_append, List.toList_toArray]
    refine forall₂_append prior ?_
    have each := mapM_forall₂ (ingressExpr τ.pos) converted
    rw [← terms] at each
    clear terms converted
    induction pend generalizing ks with
    | nil => cases each; exact .nil
    | cons item pend ih =>
      cases each with
      | cons head tail => exact .cons ⟨τ, head⟩ (by simpa using ih _ tail)
  · cases ran

/-- **`exprsOf` converts every item**: its result is, item by item, a
conversion of the item's term. -/
theorem exprsOf_spec {items : Array (Numbering × Ix.Expr)} {ks : Array (Ix.Kernel.Reader.CExpr .source)}
    (ran : exprsOf items = .ok ks) : List.Forall₂ Converts items.toList ks.toList := by
  unfold exprsOf at ran
  simp only at ran
  obtain ⟨s, loop, final⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
  have inv := forIn_inv_array ExprsInv _ items ?step ⟨[], [], rfl, .nil, rfl⟩ loop
  · obtain ⟨done, pend, whole, prior, pending⟩ := inv
    split at final
    · rename_i τ es run
      rw [run] at pending
      obtain ⟨out, flushed, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok final
      cases returned
      rw [whole]
      exact flush_ok prior pending flushed
    · rename_i none_
      cases run : s.2 with
      | some p => exact absurd run (by rcases p with ⟨τ, es⟩; exact none_ τ es)
      | none =>
        rw [run] at pending
        cases final
        rw [whole, pending, List.append_nil]
        exact prior
  · intro pre x post st r _ holds stepped
    obtain ⟨done, pend, whole, prior, pending⟩ := holds
    split at stepped
    · rename_i τ es run
      rw [run] at pending
      split at stepped
      · cases stepped
        refine ⟨_, rfl, done, pend ++ [x], by rw [whole, List.append_assoc], prior, ?_⟩
        show (pend ++ [x]).map Prod.snd = (es.push x.2).toList
        rw [List.map_append, pending]
        simp
      · obtain ⟨out, flushed, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok stepped
        cases returned
        refine ⟨_, rfl, done ++ pend, [x], by rw [whole], flush_ok prior pending flushed, rfl⟩
    · rename_i run
      rw [run] at pending
      cases stepped
      refine ⟨_, rfl, done, [x], by rw [whole, pending, List.append_nil], prior, rfl⟩

theorem drop_cons {α : Type} {l : List α} {n : Nat} {a : α} {rest : List α} (h : l.drop n = a :: rest) :
    l[n]? = some a ∧ l.drop (n + 1) = rest := by
  constructor
  · have := congrArg List.head? h
    rw [List.head?_drop] at this
    simpa using this
  · rw [← List.tail_drop, h]
    rfl

theorem drop_of_append {α : Type} {l pre post : List α} {x : α} (h : pre ++ x :: post = l) :
    l.drop pre.length = x :: post := by
  rw [← h, List.drop_left]

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ {i : Nat} {a : α}, l[i]? = some a →
      ∃ b, m[i]? = some b ∧ R a b := by
  intro l m holds
  induction holds with
  | nil => intro i a found; simp at found
  | cons head _ ih =>
    intro i a found
    cases i with
    | zero => simp at found; subst found; exact ⟨_, rfl, head⟩
    | succ i => simpa using ih (by simpa using found)

theorem getElem!_of_toList {α : Type} [Inhabited α] {xs : Array α} {i : Nat} {b : α}
    (h : xs.toList[i]? = some b) : xs[i]! = b := by
  have bound : i < xs.size := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simpa using this
  rw [getElem!_pos xs i bound]
  have := (List.getElem?_eq_some_iff.mp h).2
  simpa using this

/-- The item `convertInductive` converts for a constructor's type. -/
def ctorItem (c : Ix.ConstructorVal) : Numbering × Ix.Expr := ({ names := c.cnst.levelParams }, c.cnst.type)

/-- The constructor items of a list of constructor classes, in order. -/
def ctorItems (L : List (Array Ix.ConstructorVal)) : List (Numbering × Ix.Expr) :=
  L.flatMap fun cs => cs.toList.map ctorItem

/-- **A Source-checked constructor telescope**: the constructor's type
converts to a term with exactly `nPd + numFields` leading binders. -/
def TelescopeOk (nPd : Nat) (c : Ix.ConstructorVal) : Prop :=
  ∃ (τ : Numbering) (k : Ix.Kernel.Reader.CExpr .source),
    ingressExpr τ.pos c.cnst.type = .ok k ∧ nPd + c.numFields = piTeleLen k

/-- The constructor loop's invariant over the constructors processed: the
items left start with the remaining constructors' items, and every
processed constructor's telescope checked. -/
def InnerInv {σ : Type} (its : List (Numbering × Ix.Expr)) (nPd : Nat) (cs : List Ix.ConstructorVal)
    (more : List (Numbering × Ix.Expr)) (pre : List Ix.ConstructorVal) (s : Nat × σ) : Prop :=
  its.drop s.1 = (cs.drop pre.length).map ctorItem ++ more ∧ ∀ c ∈ pre, TelescopeOk nPd c

/-- The constructor classes' loop invariant. -/
def OuterInv {σ : Type} (its : List (Numbering × Ix.Expr)) (nPd : Nat) (full : List (Array Ix.ConstructorVal))
    (more : List (Numbering × Ix.Expr)) (pre : List (Array Ix.ConstructorVal)) (s : Nat × σ) : Prop :=
  its.drop s.1 = ctorItems (full.drop pre.length) ++ more ∧ ∀ cs ∈ pre, ∀ c ∈ cs.toList, TelescopeOk nPd c

/-- The conversion's check of a constructor at item `i`: the converted
term at `i` is a conversion of the constructor's type. -/
theorem telescope_at {items : Array (Numbering × Ix.Expr)} {ks : Array (Ix.Kernel.Reader.CExpr .source)}
    (converted : List.Forall₂ Converts items.toList ks.toList) {i nPd : Nat} {c : Ix.ConstructorVal}
    (at_ : items.toList[i]? = some (ctorItem c)) (checked : (nPd + c.numFields == piTeleLen ks[i]!) = true) :
    TelescopeOk nPd c := by
  obtain ⟨k, found, τ, conv⟩ := forall₂_getElem? converted at_
  rw [getElem!_of_toList found] at checked
  exact ⟨τ, k, conv, by simpa using checked⟩

set_option hygiene false in
/-- The constructor loop's step, on its inline step. -/
local macro "inner_step" : tactic => `(tactic| (
  intro pre' c post' st r whole' holds' stepped'
  obtain ⟨cursor, checkedAll⟩ := holds'
  rw [drop_of_append whole', List.map_cons, List.cons_append] at cursor
  obtain ⟨at_, next⟩ := drop_cons cursor
  split at stepped'
  · rename_i checked
    cases stepped'
    refine ⟨_, rfl, ?_, ?_⟩
    · show items.toList.drop (st.1 + 1) = _
      rw [next, List.length_append, List.length_singleton, ← List.drop_drop, drop_of_append whole']
      rfl
    · intro c' present
      rcases List.mem_append.mp present with old | new
      · exact checkedAll c' old
      · rw [List.mem_singleton.mp new]
        exact telescope_at converted at_ checked
  · cases stepped'))

/-- `convertInductive`'s items: the types', then the constructors', then
the recursors'. -/
theorem items_layout {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {C : Array (Numbering × Ix.Expr)} {ks : Array (Ix.Kernel.Reader.CExpr .source)}
    (ran : exprsOf (types.map (fun v => (({ names := v.cnst.levelParams } : Numbering), v.cnst.type)) ++
      ctors.flatMap (fun x => x.map ctorItem) ++ C) = .ok ks) :
    ∃ (items : Array (Numbering × Ix.Expr)) (more : List (Numbering × Ix.Expr)), exprsOf items = .ok ks ∧
      items.toList.drop types.size = ctorItems ctors.toList ++ more :=
  ⟨_, C.toList, ran, by
    rw [Array.toList_append, Array.toList_append, List.append_assoc,
      List.drop_left' (by simp)]
    simp [ctorItems, Array.toList_flatMap]⟩

/-- **What `convertInductive` checks**: a converted block has a first
member; no member and no constructor is unsafe; the members share the first
member's `numParams`; and every constructor's type converts to a term with
exactly `numParams + numFields` leading binders. -/
theorem convertInductive_spec (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
    (recs : Array Ix.RecursorVal) (conv : Converted) (ran : convertInductive types ctors recs = .ok conv) :
    ∃ first, types[0]? = some first ∧
      (∀ v ∈ types.toList, v.isUnsafe = false) ∧
      (∀ cs ∈ ctors.toList, ∀ c ∈ cs.toList, c.isUnsafe = false) ∧
      (∀ v ∈ types.toList, v.numParams = first.numParams) ∧
      (∀ cs ∈ ctors.toList, ∀ c ∈ cs.toList, TelescopeOk first.numParams c) := by
  unfold convertInductive at ran
  split at ran
  · rename_i first firstEq
    simp only at ran
    split at ran
    · cases ran
    · rename_i safe
      split at ran
      · rename_i params
        obtain ⟨ks, convertedEq, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
        obtain ⟨items, more, itemsEq, layout⟩ := items_layout convertedEq
        have converted := exprsOf_spec itemsEq
        obtain ⟨s₁, typesLoop, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
        obtain ⟨s₂, ctorsLoop, _⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
        have typesCount := forIn_inv_array (fun (pre : List Ix.InductiveVal) (s : Nat × _) => s.1 = pre.length)
          _ types (by
            intro pre v post st r _ holds stepped
            cases stepped
            exact ⟨_, rfl, by simp [holds]⟩) rfl typesLoop
        simp only [Array.length_toList] at typesCount
        have outer := forIn_inv_array (OuterInv items.toList first.numParams ctors.toList more) _ ctors ?outerStep
          (⟨by show items.toList.drop s₁.1 = _; rw [typesCount, layout]; rfl, by simp⟩) ctorsLoop
        · refine ⟨first, firstEq, ?_, ?_, ?_, outer.2⟩
          · intro v present
            cases unsafeV : v.isUnsafe
            · rfl
            · refine absurd ?_ safe
              rw [Bool.or_eq_true, Bool.or_eq_true]
              exact .inl (.inl (Array.any_eq_true'.mpr ⟨v, Array.mem_def.mpr present, unsafeV⟩))
          · intro cs present c inside
            cases unsafeC : c.isUnsafe
            · rfl
            · refine absurd ?_ safe
              rw [Bool.or_eq_true, Bool.or_eq_true]
              exact .inl (.inr (Array.any_eq_true'.mpr ⟨cs, Array.mem_def.mpr present,
                Array.any_eq_true'.mpr ⟨c, Array.mem_def.mpr inside, unsafeC⟩⟩))
          · intro v present
            exact beq_iff_eq.mp (Array.all_eq_true'.mp params v (Array.mem_def.mpr present))
        · intro pre cs post st r whole holds stepped
          obtain ⟨cursor, checkedAll⟩ := holds
          rw [drop_of_append whole] at cursor
          obtain ⟨inner, innerLoop, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok stepped
          cases returned
          have innerInv := forIn_inv_array (InnerInv items.toList first.numParams cs.toList (ctorItems post ++ more))
            _ cs (by inner_step)
            (⟨by show items.toList.drop st.1 = _; rw [cursor]; simp [ctorItems], by simp⟩) innerLoop
          refine ⟨_, rfl, ?_, ?_⟩
          · show items.toList.drop inner.1 = ctorItems (ctors.toList.drop (pre ++ [cs]).length) ++ more
            rw [innerInv.1, List.drop_length, List.map_nil, List.nil_append, List.length_append,
              List.length_singleton, ← List.drop_drop, drop_of_append whole]
            rfl
          · intro cs' present
            rcases List.mem_append.mp present with old | new
            · exact checkedAll cs' old
            · rw [List.mem_singleton.mp new]
              exact innerInv.2
      · cases ran
  · cases ran

/-! ## Telescopes -/

open Ix.CompileCert.ReaderSourceSpines (sourceStrip SourceNonForall sourceStrip_zero) in
/-- **A converted type with `n` leading binders is a source telescope of
`n` binders ending in a non-binder**: the conversion keeps every binder
(`mdata` erased, a contract frame on a binder kept on that binder), so the
source, read through its metadata, has exactly the conversion's binders. -/
theorem strip_of_ingress (σ : Ix.Name → Ix.Kernel.LevelParam) :
    ∀ (e : Ix.Expr) (k : Ix.Kernel.Reader.CExpr .source) (n : Nat), ingressExpr σ e = .ok k → piTeleLen k = n →
      ∃ types body, sourceStrip n e = some (types, body) ∧ SourceNonForall body := by
  intro e
  induction e with
  | bvar i h =>
    intro k n ran count
    cases ran
    rw [Ix.Kernel.Expr.mkBvar_eq] at count
    subst count
    exact ⟨[], _, sourceStrip_zero _, trivial⟩
  | fvar _ _ => intro k n ran; cases ran
  | mvar _ _ => intro k n ran; cases ran
  | sort u h =>
    intro k n ran count
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases ran
    subst count
    exact ⟨[], _, sourceStrip_zero _, trivial⟩
  | const c us h =>
    intro k n ran count
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases ran
    subst count
    exact ⟨[], _, sourceStrip_zero _, trivial⟩
  | app f a h _ _ =>
    intro k n ran count
    rw [Ix.LeanIngress.ingressExpr_app] at ran
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases ran
    subst count
    exact ⟨[], _, sourceStrip_zero _, trivial⟩
  | lam name t b bi h _ _ =>
    intro k n ran count
    rw [Ix.LeanIngress.ingressExpr_lam] at ran
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases ran
    subst count
    exact ⟨[], _, sourceStrip_zero _, trivial⟩
  | forallE name t b bi h _ ihb =>
    intro k n ran count
    rw [Ix.LeanIngress.ingressExpr_forallE] at ran
    obtain ⟨x, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    obtain ⟨y, body, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases ran
    subst count
    obtain ⟨types, residual, strip, last⟩ := ihb y (piTeleLen y) body rfl
    refine ⟨t :: types, residual, ?_, last⟩
    show sourceStrip (piTeleLen y + 1) (.forallE name t b bi h) = _
    simp only [sourceStrip, strip, Option.map_some]
  | letE name t v b nd h _ _ _ =>
    intro k n ran count
    rw [Ix.LeanIngress.ingressExpr_letE] at ran
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases ran
    subst count
    exact ⟨[], _, sourceStrip_zero _, trivial⟩
  | lit l h =>
    intro k n ran count
    cases l <;> cases ran <;> subst count <;> exact ⟨[], _, sourceStrip_zero _, trivial⟩
  | mdata d e h ih =>
    intro k n ran count
    rw [Ix.LeanIngress.ingressExpr_mdata] at ran
    unfold Ix.LeanIngress.ingressMData at ran
    split at ran
    · obtain ⟨c, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
      obtain ⟨x, inner, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
      unfold Ix.LeanIngress.withContract at ran
      split at ran
      · cases ran
        subst count
        exact ⟨[], _, sourceStrip_zero _, trivial⟩
      · cases ran
        obtain ⟨types, residual, strip, last⟩ := ih _ n inner (by simpa [piTeleLen] using count)
        cases n with
        | zero => simp [piTeleLen] at count
        | succ m => exact ⟨types, residual, strip, last⟩
      · cases ran
        subst count
        exact ⟨[], _, sourceStrip_zero _, trivial⟩
      · cases ran
    · obtain ⟨types, residual, strip, last⟩ := ih k n ran count
      cases n with
      | zero =>
        rw [sourceStrip_zero] at strip
        cases strip
        exact ⟨[], _, sourceStrip_zero _, last⟩
      | succ m => exact ⟨types, residual, strip, last⟩
  | proj s i b h _ =>
    intro k n ran count
    rw [Ix.LeanIngress.ingressExpr_proj] at ran
    obtain ⟨_, _, ran⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases ran
    subst count
    exact ⟨[], _, sourceStrip_zero _, trivial⟩

end Conversion

/-! ## The compiler resolves the constructors through its environment -/

section Compiler

open Ix.CompileM

theorem find_ok (name : Ix.Name) (context : CompileEnv × BlockEnv) (state : BlockState) {c : Ix.ConstantInfo}
    (ran : rawRun (findConst name) context state = (.ok c, state)) : context.1.env.get? name = some c := by
  simp only [findConst, rawRun_bind, rawRun_read] at ran
  cases found : context.1.env.get? name with
  | none => rw [found] at ran; cases ran
  | some c' => rw [found] at ran; cases ran; rfl

theorem find_run (name : Ix.Name) (context : CompileEnv × BlockEnv) (state : BlockState) :
    ∃ outcome, rawRun (findConst name) context state = (outcome, state) :=
  ⟨_, Prod.ext rfl (EmissionDispatch.find_state name context state)⟩

/-- **The family's constructors are the compile environment's**: under an
environment without call-site plans, `collectInductiveConstructors` returns,
after what it started with, the constructor the environment has under each
name, in order. -/
theorem collect_lookups (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true) :
    ∀ (names : List Ix.Name) (acc : Array Ix.ConstructorVal) (state : BlockState) (out : Array Ix.ConstructorVal),
      (rawRun (collectInductiveConstructors names acc) context state).1 = .ok out →
      ∃ cs, List.Forall₂ (fun n c => context.1.env.get? n = some (.ctorInfo c)) names cs ∧
        out = acc ++ cs.toArray := by
  intro names
  induction names with
  | nil =>
    intro acc state out ran
    cases ran
    exact ⟨[], .nil, by simp⟩
  | cons name rest ih =>
    intro acc state out ran
    rw [collectInductiveConstructors, rawRun_bind] at ran
    obtain ⟨outcome, found⟩ := find_run name context state
    rw [found] at ran
    cases outcome with
    | error e => cases ran
    | ok value =>
      have looked := find_ok name context state found
      cases value with
      | ctorInfo cv =>
        simp only [rawRun_bind, EmissionDispatch.audit_free context free] at ran
        obtain ⟨cs, holds, done⟩ := ih (acc.push cv) state out ran
        exact ⟨cv :: cs, .cons looked holds, by rw [done]; simp⟩
      | _ => cases ran

/-- **A mutual member's constructors are the compile environment's**:
`MutConst.mkIndc` returns the inductive with the constructor the
environment has under each of its constructor names, in order. -/
theorem collectMut_lookups (context : CompileEnv × BlockEnv) :
    ∀ (names : List Ix.Name) (acc : Array Ix.ConstructorVal) (state : BlockState) (out : Array Ix.ConstructorVal),
      (rawRun (collectMutConstConstructors names acc) context state).1 = .ok out →
      ∃ cs, List.Forall₂ (fun n c => context.1.env.get? n = some (.ctorInfo c)) names cs ∧
        out = acc ++ cs.toArray := by
  intro names
  induction names with
  | nil =>
    intro acc state out ran
    cases ran
    exact ⟨[], .nil, by simp⟩
  | cons name rest ih =>
    intro acc state out ran
    rw [collectMutConstConstructors, rawRun_bind] at ran
    obtain ⟨outcome, found⟩ := find_run name context state
    rw [found] at ran
    cases outcome with
    | error e => cases ran
    | ok value =>
      have looked := find_ok name context state found
      cases value with
      | ctorInfo cv =>
        obtain ⟨cs, holds, done⟩ := ih (acc.push cv) state out ran
        exact ⟨cv :: cs, .cons looked holds, by rw [done]; simp⟩
      | _ => cases ran

theorem mkIndc_lookups (context : CompileEnv × BlockEnv) (i : Ix.InductiveVal) (state : BlockState)
    {m : Ix.MutConst} (ran : (rawRun (MutConst.mkIndc i) context state).1 = .ok m) :
    ∃ cs, List.Forall₂ (fun n c => context.1.env.get? n = some (.ctorInfo c)) i.ctors.toList cs ∧
      m = .indc ⟨i.cnst.name, i.cnst.levelParams, i.cnst.type, i.numParams, i.numIndices, i.all, cs.toArray,
        i.numNested, i.isRec, i.isReflexive, i.isUnsafe⟩ := by
  unfold MutConst.mkIndc at ran
  rw [rawRun_bind] at ran
  cases collected : rawRun (collectMutConstConstructors i.ctors.toList #[]) context state with
  | mk outcome after =>
    rw [collected] at ran
    cases outcome with
    | error e => cases ran
    | ok out =>
      cases ran
      obtain ⟨cs, holds, done⟩ := collectMut_lookups context i.ctors.toList #[] state out
        (by rw [collected])
      refine ⟨cs, holds, ?_⟩
      rw [done, Array.empty_append]

end Compiler

/-! ## Source admission -/

section Admission

open Ix.CompileCert.ReaderSourceSpines (sourceStrip SourceNonForall)

/-- `inductiveGroup` lays a block out or refuses it. -/
theorem inductiveGroup_cases (env : Ix.Environment) (first : Ix.InductiveVal) (cands : Array Ix.RecursorVal) :
    Invalid (inductiveGroup env first cands) ∨
      ∃ types ctors recs, inductiveGroup env first cands = .inductive types ctors recs := by
  generalize h : inductiveGroup env first cands = g
  unfold inductiveGroup at h
  simp only [Id.run, idBind, idPure] at h
  split at h
  · rename_i r heq
    exact .inl (h ▸ exit_of_fst (R := Invalid) (H := memberValue env first.all) heq (by member_step))
  · split at h
    · rename_i r heq
      exact .inl (h ▸ exit_of_fst (R := Invalid) (H := classValue env) heq (by class_step))
    · split at h
      · exact .inr ⟨_, _, _, h.symm⟩
      · exact .inl ⟨_, _, h.symm⟩

/-- **Source mode admits the inductive block `first` heads**: the block's
group (`inductiveGroup`, whatever recursors it finds) converts. This is
what `Ix.LeanIngress.scheduleOf` requires of the group before lowering it. -/
def Admits (env : Ix.Environment) (first : Ix.InductiveVal) : Prop :=
  ∃ cands converted, Ix.LeanIngress.convert (inductiveGroup env first cands) = .ok converted

theorem admits_layout {env : Ix.Environment} {first : Ix.InductiveVal} (admits : Admits env first) :
    ∃ cands types ctors recs converted, inductiveGroup env first cands = .inductive types ctors recs ∧
      convertInductive types ctors recs = .ok converted := by
  obtain ⟨cands, converted, ran⟩ := admits
  rcases inductiveGroup_cases env first cands with ⟨names, e, invalid⟩ | ⟨types, ctors, recs, layout⟩
  · rw [invalid] at ran
    cases ran
  · rw [layout] at ran
    exact ⟨cands, types, ctors, recs, converted, layout, ran⟩

theorem forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ {a : α}, a ∈ l → ∃ b ∈ m, R a b := by
  intro l m holds
  induction holds with
  | nil => intro a present; cases present
  | cons head _ ih =>
    intro a present
    rcases List.mem_cons.mp present with rfl | later
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨b, inside, related⟩ := ih later
      exact ⟨b, List.mem_cons_of_mem _ inside, related⟩

/-- The constructors the environment has under a member's constructor names
are the ones the group recorded, each at its position. -/
theorem ctors_agree (env : Ix.Environment) (owner : Ix.Name) :
    ∀ (l : List Ix.Name) (k : Nat) {cs ds : List Ix.ConstructorVal},
      List.Forall₂ (fun x cv => ctorValue env owner x = some cv) (l.zipIdx k) cs →
      List.Forall₂ (fun n c => env.consts.get? n = some (.ctorInfo c)) l ds →
      ds = cs ∧ ∀ j (inside : j < cs.length), cs[j].cidx = k + j := by
  intro l
  induction l with
  | nil =>
    intro k cs ds recorded looked
    cases recorded
    cases looked
    exact ⟨rfl, fun j inside => absurd inside (Nat.not_lt_zero j)⟩
  | cons n l ih =>
    intro k cs ds recorded looked
    rw [List.zipIdx_cons] at recorded
    cases recorded with
    | cons head tail =>
      cases looked with
      | cons found rest =>
        obtain ⟨present, _, placed⟩ := ctorValue_some head
        rw [found] at present
        cases present
        obtain ⟨same, positions⟩ := ih (k + 1) tail rest
        refine ⟨by rw [same], fun j inside => ?_⟩
        cases j with
        | zero => exact placed
        | succ j =>
          have := positions j (by simpa using inside)
          simp only [List.getElem_cons_succ, this]
          omega

/-- **What Source admission gives a member of the block**: the member is
safe, and the constructors the environment has under its constructor names
are at their positions, safe, and each a source telescope of the member's
parameters and its fields ending in a non-binder. -/
theorem admitted_member {env : Ix.Environment} {first : Ix.InductiveVal} (admits : Admits env first)
    {source : Ix.InductiveVal} (member : source.cnst.name ∈ first.all.toList)
    (found : env.consts.get? source.cnst.name = some (.inductInfo source)) :
    source.isUnsafe = false ∧ ∀ constructors : Array Ix.ConstructorVal,
      List.Forall₂ (fun n c => env.consts.get? n = some (.ctorInfo c)) source.ctors.toList constructors.toList →
      (∀ j (inside : j < constructors.size), constructors[j].cidx = j) ∧
      (∀ ctor ∈ constructors.toList, ctor.isUnsafe = false) ∧
      (∀ ctor ∈ constructors.toList, ∃ types body,
        sourceStrip (source.numParams + ctor.numFields) ctor.cnst.type = some (types, body) ∧
          SourceNonForall body) := by
  obtain ⟨cands, types, ctors, recs, converted, layout, conversion⟩ := admits_layout admits
  obtain ⟨members, classes⟩ := inductiveGroup_spec env first cands types ctors recs layout
  obtain ⟨v, memberIn, recorded⟩ := forall₂_mem members member
  obtain ⟨present, _⟩ := memberValue_some recorded
  rw [found] at present
  cases present
  obtain ⟨cs, classIn, classed⟩ := forall₂_mem classes memberIn
  obtain ⟨l, listed, rfl⟩ := Option.map_eq_some_iff.mp classed
  have recordedCtors := (ctorsValue_forall₂ env source.cnst.name).mp listed
  obtain ⟨head, firstEq, safe, ctorSafe, params, telescopes⟩ := convertInductive_spec types ctors recs converted
    conversion
  refine ⟨safe source memberIn, fun constructors looked => ?_⟩
  rw [Array.toList_zipIdx] at recordedCtors
  obtain ⟨same, positions⟩ := ctors_agree env source.cnst.name source.ctors.toList 0 recordedCtors looked
  have members' : ∀ ctor ∈ constructors.toList, ctor ∈ (List.toArray l).toList := by
    intro ctor inside
    rw [same] at inside
    simpa using inside
  refine ⟨fun j inside => ?_, fun ctor inside => ctorSafe _ classIn ctor (members' ctor inside),
    fun ctor inside => ?_⟩
  · have bound : j < l.length := by rw [← same]; simpa using inside
    have eq : constructors[j] = l[j] := List.getElem_of_eq same (by simpa using inside)
    rw [eq]
    simpa using positions j bound
  · obtain ⟨τ, k, conv, count⟩ := telescopes _ classIn ctor (members' ctor inside)
    rw [params source memberIn]
    exact strip_of_ingress τ.pos ctor.cnst.type k _ conv count.symm

theorem forall₂_mono_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → (∀ a ∈ l, ∀ b, R a b → S a b) → List.Forall₂ S l m := by
  intro l m holds implies
  induction holds with
  | nil => exact .nil
  | cons head _ ih =>
    exact .cons (implies _ List.mem_cons_self _ head)
      (ih fun a inside b related => implies a (List.mem_cons_of_mem _ inside) b related)

open Ix.CompileM in
/-- **`inductive_reads`' Source premises from Source admission**: if Source
mode admits the block of a member `source` of the compile environment's
input, and the compile environment resolves `source`'s constructor names as
that input does, then the member is safe and the constructors the
compiler's dispatch resolves are safe, at their positions, and source
telescopes of the parameters and their fields. -/
theorem source_premises (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    {env : Ix.Environment} {first : Ix.InductiveVal} (admits : Admits env first) {source : Ix.InductiveVal}
    (member : source.cnst.name ∈ first.all.toList)
    (sourceFound : env.consts.get? source.cnst.name = some (.inductInfo source))
    (agree : ∀ n ∈ source.ctors.toList, context.1.env.get? n = env.consts.get? n)
    {constructors : Array Ix.ConstructorVal} {before : BlockState}
    (found : (rawRun (lookupInductiveConstructors source)
      (EmissionDispatch.singletonContext source.cnst.name context) before).1 = .ok constructors) :
    source.isUnsafe = false ∧ (∀ ctor ∈ constructors.toList, ctor.isUnsafe = false) ∧
      (∀ j (inside : j < constructors.size), constructors[j].cidx = j) ∧
      (∀ ctor ∈ constructors.toList, ∃ types body,
        sourceStrip (source.numParams + ctor.numFields) ctor.cnst.type = some (types, body) ∧
          SourceNonForall body) := by
  obtain ⟨cs, looked, rfl⟩ := collect_lookups (EmissionDispatch.singletonContext source.cnst.name context) free
    source.ctors.toList #[] before constructors found
  have looked' : List.Forall₂ (fun n c => env.consts.get? n = some (.ctorInfo c)) source.ctors.toList
      (#[] ++ cs.toArray).toList := by
    simpa using forall₂_mono_mem looked fun n inside c resolved => (agree n inside).symm.trans resolved
  obtain ⟨safe, facts⟩ := admitted_member admits member sourceFound
  obtain ⟨positions, ctorSafe, arity⟩ := facts _ looked'
  exact ⟨safe, ctorSafe, positions, arity⟩

open Ix.CompileM in
/-- **R9a's `ConstructorPositions` for the compiler's mutual members**: a
member `MutConst.mkIndc` builds for an inductive of a Source-admitted block,
in a compile environment that resolves its constructor names as Source's
input does, declares its constructors' positions. -/
theorem mkIndc_positions (context : CompileEnv × BlockEnv) {env : Ix.Environment} {first : Ix.InductiveVal}
    (admits : Admits env first) {i : Ix.InductiveVal} (member : i.cnst.name ∈ first.all.toList)
    (found : env.consts.get? i.cnst.name = some (.inductInfo i))
    (agree : ∀ n ∈ i.ctors.toList, context.1.env.get? n = env.consts.get? n)
    {state : BlockState} {m : Ix.MutConst} (ran : (rawRun (MutConst.mkIndc i) context state).1 = .ok m) :
    MutualProjections.ConstructorPositions m := by
  obtain ⟨cs, looked, rfl⟩ := mkIndc_lookups context i state ran
  have looked' : List.Forall₂ (fun n c => env.consts.get? n = some (.ctorInfo c)) i.ctors.toList
      cs.toArray.toList := by
    simpa using forall₂_mono_mem looked fun n inside c resolved => (agree n inside).symm.trans resolved
  exact ((admitted_member admits member found).2 _ looked').1

section Reading

open Ix.CompileM Ix.CompileCert.ExpressionState Ix.CompileCert.InductiveReading
open Ix.Kernel (Mode LevelParam ConstRef)
open Ix.Kernel.Reader
open Ix.Sharing.Verify (BlockWireTablesWF BlockResultCodecWF)

variable {md : Mode} (cx : Ctx md) (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam)
  (bindings : Bindings)

/-- **A compiled standalone inductive of a Source-admitted block is read
back as its source** (`InductiveReading.inductive_reads` with its safety,
position and telescope premises discharged): the inductive is a member of a
block Source mode admits (`Admits`), the compile environment resolves its
constructor names as Source's input does, and the rest is
`inductive_reads`' (the self references stay premises: the family's own
name read as its key, and no constructor of the family in its types). -/
theorem inductive_reads_source (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names)
    {env : Ix.Environment} {first : Ix.InductiveVal} (admits : Admits env first) (source : Ix.InductiveVal)
    (member : source.cnst.name ∈ first.all.toList)
    (sourceFound : env.consts.get? source.cnst.name = some (.inductInfo source))
    (agree : ∀ n ∈ source.ctors.toList, context.1.env.get? n = env.consts.get? n)
    (constructors : Array Ix.ConstructorVal) {before after : BlockState} {output : BlockResult}
    (found : (rawRun (lookupInductiveConstructors source)
      (EmissionDispatch.singletonContext source.cnst.name context) before).1 = .ok constructors)
    (state : State md) {shape : BlockShape} (indexed : cx.index.blocks[output.blockAddr]? = some shape)
    (order : shape.order = #[0]) {key : CName md} (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (ctorKey : Nat → CName md)
    (ctorKeyed : ∀ j, j < constructors.size → cx.memberKey (.ctor output.blockAddr 0 j) = .ok (ctorKey j))
    (scope : ConstsSatisfy (SelfName (familyBlock source constructors context)
      (inductiveSelf cx output.blockAddr) names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors.toList, ConstsSatisfy (SelfName (familyBlock source constructors context)
      (inductiveSelf cx output.blockAddr) names) ctor.cnst.type)
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (widths : PreseedWire.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    BlockResultCodecWF output ∧ ProjectionLayout.InductiveLayout source constructors output ∧
      ∃ type ctorTypes, related names σ source source.cnst.type type ∧
        List.Forall₂ (related names σ source) (constructors.toList.map (·.cnst.type)) ctorTypes ∧
        readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
          readRecursors (ExpressionRead.withBlockBlobs cx after) (List.range source.cnst.levelParams.size)
              shape.recs >>= fun recs =>
            lowerInductive state (sourceBlock key ctorKey type ctorTypes source constructors recs) := by
  obtain ⟨safe, ctorSafe, positions, arity⟩ :=
    source_premises context free admits member sourceFound agree found
  exact inductive_reads cx names σ bindings context free aligned external source constructors found state indexed
    order keyed ctorKey ctorKeyed scope ctorScope safe ctorSafe positions arity clean wire widths ran

end Reading

end Admission

end Ix.CompileCert.SourceConstructorPositions
