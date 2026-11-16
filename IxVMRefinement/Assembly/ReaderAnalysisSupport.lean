import Ix.IxVM.Consistency.Statement
import Ix.Cert.RecursorIndex
import IxC.Kernel.Ixon.ShapeSpec

/-! # Reference support of the reader's recursor analysis

Symbolic telescope normalization and head walks use only references in the recursor type
or its sharing table, including let-bound values. Analysis therefore transfers using
agreement on those references, without requiring agreement at unused reference-table entries.
-/

namespace IxVM.Refinement.Assembly.ReaderAnalysis

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency (exprRefIdxs usedRefIdxs mutRefIdxs)
open Ix.Cert.RecursorIndex (analyseWith analyse_eq recursorAnalysis_spec)
open Ix.Cert (recursorAnalysis?)

def RefsIn (P : Nat → Prop) (e : Ixon.Expr) : Prop :=
  ∀ i ∈ exprRefIdxs e, P i

def SharingRefsIn (P : Nat → Prop) (c : Ixon.Constant) : Prop :=
  ∀ (i : Nat) (e : Ixon.Expr), c.sharing[i]? = some e → RefsIn P e

theorem refsIn_all {P : Nat → Prop} {ty body : Ixon.Expr} (h : RefsIn P (.all ty body)) :
    RefsIn P ty ∧ RefsIn P body := by
  constructor <;> intro i hi
  · exact h i (by simp [exprRefIdxs, hi])
  · exact h i (by simp [exprRefIdxs, hi])

theorem refsIn_app {P : Nat → Prop} {f a : Ixon.Expr} (h : RefsIn P (.app f a)) :
    RefsIn P f ∧ RefsIn P a := by
  constructor <;> intro i hi
  · exact h i (by simp [exprRefIdxs, hi])
  · exact h i (by simp [exprRefIdxs, hi])

theorem unshare_refs {P : Nat → Prop} {c : Ixon.Constant} (shared : SharingRefsIn P c)
    {e : Ixon.Expr} (h : RefsIn P e) : RefsIn P (unshare c e) := by
  have walk : ∀ fuel e, RefsIn P e → RefsIn P (unshare.go c fuel e) := by
    intro fuel
    induction fuel with
    | zero => exact fun _ h => h
    | succ fuel ih =>
      intro e h
      cases e with
      | share i =>
        simp only [unshare.go]
        cases found : c.sharing[i.toNat]? with
        | none => exact h
        | some value => exact ih value (shared _ _ found)
      | _ => exact h
  exact walk _ _ h

theorem appHead_refs {P : Nat → Prop} {c : Ixon.Constant} (shared : SharingRefsIn P c)
    (fuel : Nat) {e : Ixon.Expr} (h : RefsIn P e) : RefsIn P (appHead c fuel e) := by
  induction fuel generalizing e with
  | zero => exact h
  | succ fuel ih =>
    have exposed := unshare_refs shared h
    simp only [appHead]
    cases head : unshare c e with
    | app f a =>
      rw [head] at exposed
      exact ih (refsIn_app exposed).1
    | _ => simpa only [head] using exposed

theorem stripAll_refs {P : Nat → Prop} {c : Ixon.Constant} (shared : SharingRefsIn P c)
    (count : Nat) {e : Ixon.Expr} (h : RefsIn P e) {domains : List Ixon.Expr} {body : Ixon.Expr}
    (ran : stripAll c count e = some (domains, body)) :
    (∀ domain ∈ domains, RefsIn P domain) ∧ RefsIn P body := by
  induction count generalizing e domains body with
  | zero =>
    cases ran
    exact ⟨by simp, h⟩
  | succ count ih =>
    have exposed := unshare_refs shared h
    simp only [stripAll] at ran
    cases head : unshare c e with
    | all ty rest =>
      rw [head] at ran exposed
      obtain ⟨⟨tail, last⟩, walked, returned⟩ := Option.bind_eq_some_iff.mp ran
      cases Option.some.inj returned
      obtain ⟨tailRefs, lastRefs⟩ := ih (refsIn_all exposed).2 walked
      exact ⟨fun d hd => (List.mem_cons.mp hd).elim
        (fun same => by subst d; exact (refsIn_all exposed).1) (tailRefs d), lastRefs⟩
    | _ => simp [head] at ran

theorem stripAllFull_refs {P : Nat → Prop} {c : Ixon.Constant} (shared : SharingRefsIn P c)
    (fuel : Nat) {e : Ixon.Expr} (h : RefsIn P e) :
    (∀ domain ∈ (stripAllFull c fuel e).1, RefsIn P domain) ∧
      RefsIn P (stripAllFull c fuel e).2 := by
  induction fuel generalizing e with
  | zero => exact ⟨by simp [stripAllFull], h⟩
  | succ fuel ih =>
    have exposed := unshare_refs shared h
    simp only [stripAllFull]
    cases head : unshare c e with
    | all ty rest =>
      rw [head] at exposed
      have later := ih (refsIn_all exposed).2
      exact ⟨fun d hd => (List.mem_cons.mp hd).elim
        (fun same => by subst d; exact (refsIn_all exposed).1) (later.1 d), later.2⟩
    | _ => exact ⟨by simp, by simpa only [head] using exposed⟩

private theorem mapM_mono_on {α β : Type} {f g : α → Option β} {Q : β → Prop} :
    ∀ (xs : List α) (ys : List β),
      (∀ x ∈ xs, ∀ y, f x = some y → g x = some y ∧ Q y) →
      xs.mapM f = some ys → xs.mapM g = some ys ∧ ∀ y ∈ ys, Q y
  | [], ys, _, ran => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at ran
    subst ys
    exact ⟨rfl, by simp⟩
  | x :: xs, ys, step, ran => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ran
    obtain ⟨y, first, tail, rest, rfl⟩ := ran
    obtain ⟨first', qy⟩ := step x List.mem_cons_self y first
    obtain ⟨rest', qt⟩ := mapM_mono_on xs tail
      (fun a ha => step a (List.mem_cons_of_mem _ ha)) rest
    refine ⟨?_, fun a ha => (List.mem_cons.mp ha).elim (fun same => by subst a; exact qy) (qt a)⟩
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    exact ⟨y, first', tail, rest', rfl⟩

theorem rawRefs_of_refsIn {P : Nat → Prop} {raw : Ixon.Expr} (supported : RefsIn P raw) :
    Shape.RawRefs P raw := by
  induction raw with
  | ref i us => exact supported _ (by simp [exprRefIdxs])
  | prj i field value ih =>
    exact ⟨supported _ (by simp [exprRefIdxs]),
      ih (fun j present => supported j (by simp [exprRefIdxs, present]))⟩
  | app function arg ihf iha | lam function arg ihf iha | all function arg ihf iha =>
    exact ⟨ihf (fun j present => supported j (by simp [exprRefIdxs, present])),
      iha (fun j present => supported j (by simp [exprRefIdxs, present]))⟩
  | letE nonDep mode type value body iht ihv ihb =>
    exact ⟨iht (fun j present => supported j (by simp [exprRefIdxs, present])),
      ihv (fun j present => supported j (by simp [exprRefIdxs, present])),
      ihb (fun j present => supported j (by simp [exprRefIdxs, present]))⟩
  | _ => trivial

/-- Normalized analysis only queries heads supported by the raw type and sharing table. -/
theorem analyseWith_mono_supported {P : Nat → Prop} {Q : ConstRef _root_.Address → Prop}
    {c : Ixon.Constant} {r : Ixon.Recursor} (shared : SharingRefsIn P c)
    (typeRefs : RefsIn P r.typ)
    {h₁ h₂ : Shape.Head → Option (ConstRef _root_.Address)}
    (heads : ∀ (e : Shape.Head), e.Refs P → ∀ q, h₁ e = some q → h₂ e = some q ∧ Q q)
    {x : Nat × Array (ConstRef _root_.Address) × ConstRef _root_.Address}
    (ran : analyseWith c r h₁ = some x) :
    analyseWith c r h₂ = some x ∧ (∀ q ∈ x.2.1, Q q) ∧ Q x.2.2 := by
  unfold analyseWith at ran ⊢
  simp only [bind, Option.bind_eq_some_iff, pure] at ran ⊢
  obtain ⟨⟨motive, inputs, last⟩, analysed, carriers, carrierRan, major, majorRan, returned⟩ := ran
  have supported := Shape.analyse_refs (P := P) (fun raw present => by
    obtain ⟨i, found⟩ := Array.mem_iff_getElem?.mp present
    exact rawRefs_of_refsIn (shared i raw found)) (rawRefs_of_refsIn typeRefs) analysed
  cases Option.some.inj returned
  rw [Array.mapM_eq_mapM_toList, Option.map_eq_map,
    Option.map_eq_some_iff] at carrierRan
  obtain ⟨ys, ysRan, rfl⟩ := carrierRan
  obtain ⟨ysRan', ysQ⟩ := mapM_mono_on _ ys (g := h₂) (Q := Q)
    (fun input present => heads input (supported.1 input (Array.mem_toList_iff.mp present))) ysRan
  obtain ⟨majorRan', majorQ⟩ := heads last supported.2 major majorRan
  refine ⟨⟨(motive, inputs, last), analysed, ys.toArray, ?_, major, majorRan', rfl⟩,
    fun q hq => ysQ q (by simpa using hq), majorQ⟩
  rw [Array.mapM_eq_mapM_toList, ysRan']
  rfl

theorem resolveShapeHead_mono_supported {P : Nat → Prop} {D : _root_.Address → Prop}
    {c : Ixon.Constant} {owner : _root_.Address} {s₁ s₂ : Store} (own : D owner)
    (references : ∀ i, P i → ∀ a, c.refs[i]? = some a → ∀ q,
      resolve s₁ a = some q → resolve s₂ a = some q ∧ D q.block)
    {head : Shape.Head} (supported : head.Refs P) {q : ConstRef _root_.Address}
    (ran : resolveShapeHead s₁ owner c head = some q) :
    resolveShapeHead s₂ owner c head = some q ∧ D q.block := by
  cases head with
  | ref i =>
    obtain ⟨a, found, resolved⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨resolved', ownerIn⟩ := references i supported a found q resolved
    exact ⟨Option.bind_eq_some_iff.mpr ⟨a, found, resolved'⟩, ownerIn⟩
  | recur i =>
    refine ⟨ran, ?_⟩
    have same : q.block = owner := by
      simp only [resolveShapeHead] at ran
      split at ran <;> split at ran <;> cases ran <;> rfl
    rwa [same]

/-- A head walk requires agreement only at the reference indices supported by its input. -/
theorem headRef_mono_supported {P : Nat → Prop} {D : _root_.Address → Prop}
    {c : Ixon.Constant} {owner : _root_.Address} {s₁ s₂ : Store}
    (shared : SharingRefsIn P c) (own : D owner)
    (references : ∀ i, P i → ∀ a, c.refs[i]? = some a → ∀ q,
      resolve s₁ a = some q → resolve s₂ a = some q ∧ D q.block)
    {e : Ixon.Expr} (supported : RefsIn P e) {q : ConstRef _root_.Address}
    (ran : headRef s₁ owner c e = some q) :
    headRef s₂ owner c e = some q ∧ D q.block := by
  have headRefs := appHead_refs shared spineFuel supported
  unfold headRef at ran ⊢
  cases head : appHead c spineFuel e with
  | ref i us =>
    simp only [head] at ran ⊢
    obtain ⟨a, found, resolved⟩ := Option.bind_eq_some_iff.mp ran
    rw [head] at headRefs
    have used : P i.toNat := headRefs i.toNat (by simp [exprRefIdxs])
    obtain ⟨resolved', ownerIn⟩ := references _ used a found q resolved
    exact ⟨Option.bind_eq_some_iff.mpr ⟨a, found, resolved'⟩, ownerIn⟩
  | recur i us =>
    simp only [head] at ran ⊢
    refine ⟨ran, ?_⟩
    have same : q.block = owner := by
      split at ran <;> split at ran <;> cases ran <;> rfl
    rwa [same]
  | _ => simp [head] at ran

/-- The raw record footprint contains the references of every sharing-table expression. -/
theorem sharing_used (c : Ixon.Constant) : SharingRefsIn (fun i => i ∈ usedRefIdxs c) c := by
  intro j e found i present
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨e, Array.mem_toList_iff.mpr (Array.mem_of_getElem? found), present⟩

/-- The raw record footprint contains the type of every actual recursor payload. -/
theorem recursor_type_used {c : Ixon.Constant} {j : Nat} {r : Ixon.Recursor}
    (member : (j, r) ∈ recursorMembers c) : RefsIn (fun i => i ∈ usedRefIdxs c) r.typ := by
  have source := Ix.CompileCert.ReaderIndex.member_source c j r member
  intro i present
  cases info : c.info with
  | recr value =>
    simp only [info] at source
    obtain ⟨_, rfl⟩ := source
    simp [usedRefIdxs, info, present]
  | muts ms =>
    simp only [info] at source
    simp only [usedRefIdxs, info]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨.recr r, Array.mem_toList_iff.mpr
      (Array.mem_of_getElem? source), by simp [mutRefIdxs, present]⟩
  | _ => simp [info] at source

/-- A successful filing analysis transfers using only used raw references and the records
of the carrier blocks it actually resolves. Both premises are local to this record. -/
theorem analysis_transfer_used {s₁ s₂ : Store} {owner : _root_.Address}
    {c : Ixon.Constant} {j : Nat} {r : Ixon.Recursor}
    (member : (j, r) ∈ recursorMembers c) {D : _root_.Address → Prop} (own : D owner)
    (references : ∀ i ∈ usedRefIdxs c, ∀ a, c.refs[i]? = some a → ∀ q,
      resolve s₁ a = some q → resolve s₂ a = some q ∧ D q.block)
    (records : ∀ a bc, D a → s₁ a = some bc → s₂ a = some bc)
    {y : _root_.Address × Nat × Array (ConstRef _root_.Address) × ConstRef _root_.Address}
    (ran : recursorAnalysis? s₁ owner c r = some y) :
    recursorAnalysis? s₂ owner c r = some y ∧
      (∀ q ∈ y.2.2.1, D q.block) ∧ D y.2.2.2.block := by
  obtain ⟨block, motive, carriers, major⟩ := y
  obtain ⟨analysis, firstIndex, blockRecord, members, slot, first, firstCarrier,
    blockFound, blockInfo, firstInductive, valid⟩ := recursorAnalysis_spec.mp ran
  rw [analyse_eq] at analysis
  obtain ⟨analysis', supported, majorSupported⟩ := analyseWith_mono_supported
    (Q := fun q => D q.block) (sharing_used c) (recursor_type_used member)
    (fun e h q ran => resolveShapeHead_mono_supported own references h ran) analysis
  have blockSupported : D block := by
    have h := supported _ (Array.mem_of_getElem? firstCarrier)
    simpa using h
  exact ⟨recursorAnalysis_spec.mpr ⟨by rw [analyse_eq]; exact analysis', firstIndex,
    blockRecord, members, slot, first, firstCarrier, records _ _ blockSupported blockFound,
    blockInfo, firstInductive, valid⟩, supported, majorSupported⟩

/-- A block reached by the syntactic analysis is the record's own block or the owner of
an actually resolved used reference. -/
def UsedOwner (s : Store) (owner : _root_.Address) (c : Ixon.Constant)
    (target : _root_.Address) : Prop :=
  target = owner ∨ ∃ i ∈ usedRefIdxs c, ∃ a, c.refs[i]? = some a ∧
    ∃ value, s a = some value ∧ (resolveSource s a value).isSome ∧
      Ix.Cert.ownerOf a value = target

theorem analysis_used_owners {s : Store} {owner : _root_.Address}
    {c : Ixon.Constant} {j : Nat} {r : Ixon.Recursor}
    (member : (j, r) ∈ recursorMembers c)
    {y : _root_.Address × Nat × Array (ConstRef _root_.Address) × ConstRef _root_.Address}
    (ran : recursorAnalysis? s owner c r = some y) :
    UsedOwner s owner c y.1 ∧
      (∀ q ∈ y.2.2.1, UsedOwner s owner c q.block) ∧ UsedOwner s owner c y.2.2.2.block := by
  have transported := analysis_transfer_used (s₂ := s) member
    (D := UsedOwner s owner c) (.inl rfl)
    (fun i used a reference q resolved => by
      obtain ⟨value, found, source⟩ := Option.bind_eq_some_iff.mp resolved
      exact ⟨resolved, .inr ⟨i, used, a, reference, value, found,
        by rw [source]; rfl, (Ix.Cert.RecursorIndex.resolveSource_block source).symm⟩⟩)
    (fun _ _ _ found => found) ran
  obtain ⟨analysis, firstIndex, blockRecord, members, slot, first, firstCarrier, rest⟩ :=
    recursorAnalysis_spec.mp ran
  have firstSupported := transported.2.1 _ (Array.mem_of_getElem? firstCarrier)
  exact ⟨firstSupported, transported.2⟩

end IxVM.Refinement.Assembly.ReaderAnalysis
