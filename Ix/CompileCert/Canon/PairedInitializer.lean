import Ix.CompileCert.Canon.AliasInitialization
import Ix.CompileCert.Canon.NameTablesRelated
import Ix.CompileCert.Canon.AllocationHistory

/-!
Proof-only full-result transport for the actual generic member initializer.
This file does not replace a public endpoint or add premises to
one. The callback-view relation and structural reference correspondence below
are internal initialization obligations; deriving them from the original raw
source/collapse presentation remains separate.

Unlike a success-only state invariant, `ResultRelated` retains the actual
first missing lookup and its renamed error text. `StatesRelated` fixes every
field by the exact ordered `XSt.push` fold, including all empty caches/maps.
The actual alias builders establish alias agreement. Arbitrary callback and
protection-thunk arguments are not replaced by a finite environment.
-/

namespace Ix.CompileCert.Canon.PairedInitializer

open Ix.Compile.Canon
open Ix (Name Expr)
open AliasInitialization

/-- The constructor triple read by `initialMembers`, in source order. There
is no constructor-prefix or cached-hash requirement. -/
structure SourceCtorRelated (σ : Name → Name) (S : Name → Prop)
    (left right : Name × Expr × Nat) : Prop where
  name : right.1 = σ left.1
  type : ERen σ S left.2.1 right.2.1
  fields : right.2.2 = left.2.2

/-- Exactly the view fields this initializer reads. Other context fields
are not silently identified; context/universe transport is a later bridge. -/
structure ViewsRelated (σ : Name → Name) (S : Name → Prop)
    (left right : IndView) : Prop where
  type : ERen σ S left.type right.type
  indices : right.numIndices = left.numIndices
  ctors : LRel (SourceCtorRelated σ S) left.ctors.toList right.ctors.toList

structure CtorsRelated (σ : Name → Name) (S : Name → Prop)
    (left right : XCtor) : Prop where
  name : right.name = σ left.name
  type : ERen σ S left.typ right.typ
  fields : right.nFields = left.nFields

structure MembersRelated (σ : Name → Name) (S : Name → Prop)
    (left right : XMember) : Prop where
  supported : S left.name
  name : right.name = σ left.name
  owner : right.sourceOwner = σ left.sourceOwner
  type : ERen σ S left.typ right.typ
  ctors : LRel (CtorsRelated σ S) left.ctors.toList right.ctors.toList
  params : right.nParams = left.nParams
  indices : right.nIndices = left.nIndices

/-- The exact record built by the actual initializer. -/
def memberOf (count : Nat) (aliases : Std.HashMap Name Name)
    (name : Name) (view : IndView) : XMember :=
  { name, sourceOwner := name, typ := canonicalizeConstNames aliases view.type,
    ctors := view.ctors.map fun (cn,ct,nf) =>
      { name := cn, typ := canonicalizeConstNames aliases ct, nFields := nf : XCtor },
    nParams := count, nIndices := view.numIndices }

def missing (name : Name) : String :=
  s!"expand: {namePretty name} is not an inductive"

def readMember (ind? : Name → Option IndView) (count : Nat)
    (aliases : Std.HashMap Name Name) (name : Name) : Except String XMember :=
  match ind? name with
  | none => .error (missing name)
  | some view => .ok (memberOf count aliases name view)

/-- Errors are not collapsed to an arbitrary error relation: they have the
exact paired query spelling used by the initializer. -/
inductive ResultRelated {α β : Type} (σ : Name → Name) (S : Name → Prop)
    (R : α → β → Prop) : Except String α → Except String β → Prop
  | ok {left right} : R left right → ResultRelated σ S R (.ok left) (.ok right)
  | missing (name : Name) : S name →
      ResultRelated σ S R (.error (PairedInitializer.missing name))
        (.error (PairedInitializer.missing (σ name)))

theorem ResultRelated.map {α β γ δ : Type} {σ : Name → Name} {S : Name → Prop}
    {R : α → β → Prop} {T : γ → δ → Prop}
    {left : Except String α} {right : Except String β}
    (related : ResultRelated σ S R left right)
    (f : α → γ) (g : β → δ) (preserves : ∀ a b, R a b → T (f a) (g b)) :
    ResultRelated σ S T (Except.map f left) (Except.map g right) := by
  cases related with
  | ok values => exact .ok (preserves _ _ values)
  | missing name supported => exact .missing name supported

private theorem map_related {α β γ δ : Type} {R : α → β → Prop} {T : γ → δ → Prop}
    {left : List α} {right : List β} (related : LRel R left right)
    (f : α → γ) (g : β → δ) (preserves : ∀ a b, R a b → T (f a) (g b)) :
    LRel T (left.map f) (right.map g) := by
  induction related with
  | nil => exact .nil
  | cons head rest ih => exact .cons (preserves _ _ head) ih

/-- Alias rewriting transports every actual initial constructor and member
payload, including the real names, owner, parameter/index and field counts. -/
theorem memberOf_related {σ : Name → Name} {S : Name → Prop}
    {leftAliases rightAliases : Std.HashMap Name Name}
    (aliases : MapsRelated σ S leftAliases rightAliases)
    {left right : IndView} (views : ViewsRelated σ S left right)
    {name : Name} (supported : S name) (count : Nat) :
    MembersRelated σ S (memberOf count leftAliases name left)
      (memberOf count rightAliases (σ name) right) := by
  refine ⟨supported,rfl,rfl,canonicalize_related aliases views.type,?_,rfl,views.indices⟩
  simp only [memberOf, Array.toList_map]
  apply map_related views.ctors
  intro a b related
  obtain ⟨an,aty,af⟩ := a
  obtain ⟨bn,bt,bf⟩ := b
  exact ⟨related.name,canonicalize_related aliases related.type,related.fields⟩

theorem readMember_related {σ : Name → Name} {S : Name → Prop}
    {leftAliases rightAliases : Std.HashMap Name Name}
    (aliases : MapsRelated σ S leftAliases rightAliases)
    {leftInd rightInd : Name → Option IndView} {name : Name} (supported : S name)
    (views : TableResultRelated (ViewsRelated σ S) (leftInd name) (rightInd (σ name)))
    (count : Nat) :
    ResultRelated σ S (MembersRelated σ S)
      (readMember leftInd count leftAliases name)
      (readMember rightInd count rightAliases (σ name)) := by
  cases leftFound : leftInd name <;> cases rightFound : rightInd (σ name) <;>
    rw [leftFound,rightFound] at views
  · simpa only [readMember,leftFound,rightFound] using
      (ResultRelated.missing (R := MembersRelated σ S) name supported)
  · cases views
  · cases views
  · cases views with
    | some related =>
      simpa only [readMember,leftFound,rightFound] using
        ResultRelated.ok (memberOf_related aliases related supported count)

/-- Build the whole initial state, not a projection of selected fields. -/
def stateOf (members : List XMember) : XSt := members.foldl XSt.push ({} : XSt)

/-- The fold changes only the two real `push` fields. This equality also
covers arbitrary prepopulated states and preserves all other fields exactly. -/
theorem push_fold (members : List XMember) (st : XSt) :
    members.foldl XSt.push st =
      { st with
        types := st.types ++ members.toArray
        typeNames := members.foldl (fun names member => names.insert member.name ()) st.typeNames } := by
  induction members generalizing st with
  | nil => simp
  | cons member rest ih =>
    rw [List.foldl_cons, ih]
    simp only [XSt.push, List.foldl_cons]
    congr 1
    apply Array.toList_inj.mp
    simp only [Array.toList_append, Array.toList_push,
      List.append_assoc, List.singleton_append]

theorem stateOf_eq (members : List XMember) :
    stateOf members =
      { ({} : XSt) with
        types := members.toArray
        typeNames := members.foldl (fun names member => names.insert member.name ()) ({} : NameSet) } := by
  simpa only [stateOf, Array.empty_append] using push_fold members ({} : XSt)

/-- Every state field is fixed by its actual constructor sequence. No
unconstrained auxiliary map, cache, error or protection list is existentially
hidden by this relation. -/
def StatesRelated (σ : Name → Name) (S : Name → Prop) (left right : XSt) : Prop :=
  ∃ leftMembers rightMembers,
    LRel (MembersRelated σ S) leftMembers rightMembers ∧
    left = stateOf leftMembers ∧ right = stateOf rightMembers

theorem StatesRelated.types {σ : Name → Name} {S : Name → Prop}
    {left right : XSt} (related : StatesRelated σ S left right) :
    LRel (MembersRelated σ S) left.types.toList right.types.toList := by
  obtain ⟨xs,ys,members,rfl,rfl⟩ := related
  simpa only [stateOf_eq, List.toList_toArray] using members

/-- Real cold-cache/empty-allocation fields are derived. In particular the
actual first allocator forbidden list is its own fixed protection thunk. -/
theorem stateOf_fields (members : List XMember) :
    (stateOf members).auxToNested = {} ∧ (stateOf members).auxCtorMap = {} ∧
      (stateOf members).seen = {} ∧ (stateOf members).keyError = none ∧
      (stateOf members).nextAuxIdx = 1 ∧ (stateOf members).sourceNames? = none ∧
      (stateOf members).allocatedNames = [] ∧ (stateOf members).allocatedCtorRoots = [] := by
  rw [stateOf_eq]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem stateOf_protection (cx : ExpansionCore.Ctx) (members : List XMember) :
    ExpansionHistory.CacheCorrect cx (stateOf members) ∧
      (stateOf members).allocatedNames ++ ExpansionCore.sourceNames cx (stateOf members) =
        cx.protect () := by
  rw [stateOf_eq]
  exact ⟨.inl rfl,rfl⟩

private theorem fold_names_related {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    (references : ∀ n, S n → R (keyName n) (keyName (σ n)))
    {xs ys : List XMember} (members : LRel (MembersRelated σ S) xs ys)
    {left right : NameSet}
    (tables : NameTablesRelated R (fun (_ _ : Unit) => True) left right) :
    NameTablesRelated R (fun (_ _ : Unit) => True)
      (xs.foldl (fun table member => table.insert member.name ()) left)
      (ys.foldl (fun table member => table.insert member.name ()) right) := by
  induction members generalizing left right with
  | nil => exact tables
  | @cons x y xs ys member rest ih =>
    apply ih
    apply tables.insert names x.name y.name _ () () trivial
    rw [member.name]
    exact references x.name member.supported

/-- The actual initial name table relation follows from ordered insertion,
including duplicates and structural overwrites. No final table agreement is
assumed. The reference relation is still an internal source-support bridge. -/
theorem StatesRelated.typeNames {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    (references : ∀ n, S n → R (keyName n) (keyName (σ n)))
    {left right : XSt} (related : StatesRelated σ S left right) :
    NameTablesRelated R (fun (_ _ : Unit) => True) left.typeNames right.typeNames := by
  obtain ⟨xs,ys,members,rfl,rfl⟩ := related
  rw [stateOf_eq, stateOf_eq]
  exact fold_names_related names references members (NameTablesRelated.empty R _)

theorem StatesRelated.protection {σ : Name → Name} {S : Name → Prop}
    {left right : XSt} (related : StatesRelated σ S left right)
    (leftCtx rightCtx : ExpansionCore.Ctx) :
    ExpansionHistory.CacheCorrect leftCtx left ∧
      ExpansionHistory.CacheCorrect rightCtx right ∧
      left.allocatedNames ++ ExpansionCore.sourceNames leftCtx left = leftCtx.protect () ∧
      right.allocatedNames ++ ExpansionCore.sourceNames rightCtx right = rightCtx.protect () := by
  obtain ⟨xs,ys,members,rfl,rfl⟩ := related
  exact ⟨(stateOf_protection leftCtx xs).1,(stateOf_protection rightCtx ys).1,
    (stateOf_protection leftCtx xs).2,(stateOf_protection rightCtx ys).2⟩

/-- A complete computation equality, including missing lookups. It factors
the real always-yield initializer without assuming it succeeds. -/
private theorem forIn_push_eq (read : Name → Except String XMember)
    (ordered : List Name) (st : XSt) :
    forIn ordered st (fun name state => do
      let member ← read name
      pure (.yield (state.push member))) =
      Except.map (fun members => members.foldl XSt.push st) (ordered.mapM read) := by
  induction ordered generalizing st with
  | nil => rfl
  | cons name rest ih =>
    rw [List.forIn_cons, List.mapM_cons]
    cases found : read name with
    | error message => rfl
    | ok member =>
      change forIn rest (st.push member) (fun name state => do
        let member ← read name
        pure (.yield (state.push member))) = _
      exact (ih (st.push member)).trans (by cases rest.mapM read <;> rfl)

theorem initialMembers_eq (cx : ExpansionCore.Ctx) (ordered : Array Name)
    (aliases : Std.HashMap Name Name) :
    ExpansionHistory.initialMembers cx ordered aliases =
      Except.map stateOf (ordered.toList.mapM (readMember cx.ind? cx.nParams aliases)) := by
  calc
    _ = forIn ordered ({} : XSt) (fun name st => do
      let member ← readMember cx.ind? cx.nParams aliases name
      pure (.yield (st.push member))) := by
        unfold ExpansionHistory.initialMembers
        congr 1
        funext name st
        cases found : cx.ind? name <;>
          simp only [found, readMember, missing, memberOf, bind, Except.bind, pure, Except.pure]
    _ = _ := by
      rw [← Array.forIn_toList]
      exact forIn_push_eq (readMember cx.ind? cx.nParams aliases) ordered.toList ({} : XSt)

private theorem mapM_related {σ : Name → Name} {S : Name → Prop}
    {leftRead rightRead : Name → Except String XMember} (ordered : List Name)
    (reads : ∀ n ∈ ordered, ResultRelated σ S (MembersRelated σ S)
      (leftRead n) (rightRead (σ n))) :
    ResultRelated σ S (LRel (MembersRelated σ S))
      (ordered.mapM leftRead) ((ordered.map σ).mapM rightRead) := by
  induction ordered with
  | nil => exact .ok .nil
  | cons name rest ih =>
    have head := reads name List.mem_cons_self
    have tail := ih (fun n member => reads n (List.mem_cons_of_mem _ member))
    rw [List.map_cons, List.mapM_cons, List.mapM_cons]
    generalize leftHead : leftRead name = lh at head ⊢
    generalize rightHead : rightRead (σ name) = rh at head ⊢
    cases head with
    | missing query supported => exact .missing query supported
    | ok member =>
      generalize leftTail : rest.mapM leftRead = lt at tail ⊢
      generalize rightTail : (rest.map σ).mapM rightRead = rt at tail ⊢
      cases tail with
      | missing query supported => exact .missing query supported
      | ok rest => exact .ok (.cons member rest)

/-- Actual initializer transport using the actual alias builders. Neither a
preconstructed alias relation nor a successful initializer is a premise.
The arbitrary callback observation premise is internal: the original-source
reader bridge must establish it before an endpoint may use this theorem. -/
theorem initialMembers_related {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (classes : Array (Array Name)) (classesSupported : ∀ cls ∈ classes, ∀ n ∈ cls, S n)
    (leftCtx rightCtx : ExpansionCore.Ctx) (params : rightCtx.nParams = leftCtx.nParams)
    (ordered : Array Name) (supported : ∀ n ∈ ordered, S n)
    (views : ∀ n ∈ ordered, TableResultRelated (ViewsRelated σ S)
      (leftCtx.ind? n) (rightCtx.ind? (σ n))) :
    ResultRelated σ S (StatesRelated σ S)
      (ExpansionHistory.initialMembers leftCtx ordered (aliasesOf classes))
      (ExpansionHistory.initialMembers rightCtx (ordered.map σ)
        (aliasesOf (classes.map (fun cls => cls.map σ)))) := by
  rw [initialMembers_eq, initialMembers_eq, Array.toList_map, params]
  have reads : ∀ n ∈ ordered.toList,
      ResultRelated σ S (MembersRelated σ S)
        (readMember leftCtx.ind? leftCtx.nParams (aliasesOf classes) n)
        (readMember rightCtx.ind? leftCtx.nParams
          (aliasesOf (classes.map (fun cls => cls.map σ))) (σ n)) := by
    intro n member
    have member' : n ∈ ordered := by simpa using member
    exact readMember_related (aliasesOf_related hinj classes classesSupported)
      (supported n member') (views n member') leftCtx.nParams
  exact (mapM_related ordered.toList reads).map stateOf stateOf
    (fun xs ys members => ⟨xs,ys,members,rfl,rfl⟩)

/-- Both success and refusal outcomes of the real initializer are accounted
for. On success the table/cache/protection facts are derived from the whole
state construction; on refusal the actual renamed missing query is retained. -/
theorem initialMembers_outcomes {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    (references : ∀ n, S n → R (keyName n) (keyName (σ n)))
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (classes : Array (Array Name)) (classesSupported : ∀ cls ∈ classes, ∀ n ∈ cls, S n)
    (leftCtx rightCtx : ExpansionCore.Ctx) (params : rightCtx.nParams = leftCtx.nParams)
    (ordered : Array Name) (supported : ∀ n ∈ ordered, S n)
    (views : ∀ n ∈ ordered, TableResultRelated (ViewsRelated σ S)
      (leftCtx.ind? n) (rightCtx.ind? (σ n))) :
    (∃ left right,
      ExpansionHistory.initialMembers leftCtx ordered (aliasesOf classes) = .ok left ∧
      ExpansionHistory.initialMembers rightCtx (ordered.map σ)
        (aliasesOf (classes.map (fun cls => cls.map σ))) = .ok right ∧
      StatesRelated σ S left right ∧
      NameTablesRelated R (fun (_ _ : Unit) => True) left.typeNames right.typeNames ∧
      ExpansionHistory.CacheCorrect leftCtx left ∧
      ExpansionHistory.CacheCorrect rightCtx right ∧
      left.allocatedNames ++ ExpansionCore.sourceNames leftCtx left = leftCtx.protect () ∧
      right.allocatedNames ++ ExpansionCore.sourceNames rightCtx right = rightCtx.protect ()) ∨
    (∃ query, S query ∧
      ExpansionHistory.initialMembers leftCtx ordered (aliasesOf classes) = .error (missing query) ∧
      ExpansionHistory.initialMembers rightCtx (ordered.map σ)
        (aliasesOf (classes.map (fun cls => cls.map σ))) = .error (missing (σ query))) := by
  have related := initialMembers_related hinj classes classesSupported leftCtx rightCtx params
    ordered supported views
  generalize leftRun : ExpansionHistory.initialMembers leftCtx ordered (aliasesOf classes) = left at related
  generalize rightRun : ExpansionHistory.initialMembers rightCtx (ordered.map σ)
    (aliasesOf (classes.map (fun cls => cls.map σ))) = right at related
  cases related with
  | ok states =>
    exact .inl ⟨_,_,rfl,rfl,states,StatesRelated.typeNames names references states,
      StatesRelated.protection states leftCtx rightCtx⟩
  | missing query queryIn => exact .inr ⟨query,queryIn,rfl,rfl⟩

end Ix.CompileCert.Canon.PairedInitializer
