import Ix.Cert.ProjectionRoots

/-! Ordered row provenance for the actual retained reader loops. -/
namespace Ix.Cert.ProjectionRoots
open Ix.Kernel Ix.Kernel.Reader Ix.CompileCert.InductiveReading Ix.CompileCert.Loop
abbrev Row (md : Mode) := CVal md × Nat × Nat
def ctorInputs (x : Nat × Ixon.Inductive) : List (Nat × Ixon.Constructor × Nat) :=
  x.2.ctors.toList.zipIdx.map fun (c, j) => (x.1, c, j)
def TypeRow {md : Mode} (cx : Ctx md) (a : Address) (mr : MemberReader md)
    (x : Nat × Ixon.Inductive) (y : Row md) : Prop := typeStep cx a mr x #[] = .ok (.yield #[y])
def CtorRow {md : Mode} (cx : Ctx md) (a : Address) (mr : MemberReader md) (n : Nat)
    (x : Nat × Ixon.Constructor × Nat) (y : Row md) : Prop :=
  ctorStep cx a mr n x.1 (x.2.1, x.2.2) (#[], []) = .ok (.yield (#[y], [y.1.name]))

theorem Trace.type_rows {md : Mode} {cx : Ctx md} {st a c ms} (tr : Trace cx st a c ms) :
    List.Forall₂ (TypeRow cx a (.mk' cx c id (blockSelf cx a ms)))
      (tr.shape.order.filterMap (indcAt ms)).toList tr.rb.types.toList := by
  apply forIn_push_array _ _ _ ?_ tr.types
  intro x acc out run
  rcases x with ⟨i, ind⟩
  unfold typeStep at run
  obtain ⟨key, keyed, run⟩ := except_bind_ok.mp run
  obtain ⟨ty, read, run⟩ := except_bind_ok.mp run
  simp only [pure, Except.pure, Except.ok.injEq] at run
  subst out
  exact ⟨_, rfl, by simp [TypeRow, typeStep, keyed, read, bind, Except.bind, pure, Except.pure]⟩

private theorem ctor_frame {md : Mode} {cx : Ctx md} {a : Address} {mr : MemberReader md} {n i x acc out}
    (run : ctorStep cx a mr n i x acc = .ok out) :
    ∃ y, out = .yield (acc.1.push y, acc.2 ++ [y.1.name]) ∧ CtorRow cx a mr n (i, x.1, x.2) y := by
  rcases x with ⟨ctor, j⟩
  by_cases hi : ctor.cidx.toNat == j
  case neg => simp [ctorStep, hi, malformed, bind, Except.bind] at run
  by_cases hu : ctor.isUnsafe
  case pos => simp [ctorStep, hi, hu, declined, bind, Except.bind] at run
  simp only [ctorStep, hi, hu, ↓reduceIte, bind, Except.bind] at run
  obtain ⟨key, keyed, run⟩ := except_bind_ok.mp run
  obtain ⟨ty, read, run⟩ := except_bind_ok.mp run
  by_cases ha : n + ctor.fields.toNat == piTeleLen ty
  case neg => simp [ha, malformed] at run
  simp only [ha, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at run
  subst out
  refine ⟨_, rfl, ?_⟩
  simp [CtorRow, ctorStep, hi, hu, keyed, read, ha, bind, Except.bind, pure, Except.pure]

private theorem ctor_inner {md : Mode} (cx : Ctx md) (a : Address) (mr : MemberReader md) (n i : Nat)
    (xs : Array (Ixon.Constructor × Nat)) {init out : Array (Row md) × List (CName md)}
    (run : forIn xs init (ctorStep cx a mr n i) = .ok out) :
    ∃ ys, out.1 = init.1 ++ ys.toArray ∧ List.Forall₂ (fun x y => CtorRow cx a mr n (i, x.1, x.2) y) xs.toList ys := by
  apply forIn_inv_array (fun pre s => ∃ ys, s.1 = init.1 ++ ys.toArray ∧ List.Forall₂ (fun x y => CtorRow cx a mr n (i, x.1, x.2) y) pre ys) _ xs ?_ ?_ run
  · intro pre x post s r _ held step
    obtain ⟨ys, eq, rows⟩ := held
    obtain ⟨y, rfl, row⟩ := ctor_frame step
    exact ⟨_, rfl, ys ++ [y], by simp [eq], forall₂_append rows (.cons row .nil)⟩
  · exact ⟨[], by simp, .nil⟩

private theorem rows_map {α β γ : Type} {Q : β → γ → Prop} {f : α → β} {xs ys}
    (h : List.Forall₂ (fun x y => Q (f x) y) xs ys) : List.Forall₂ Q (xs.map f) ys := by
  induction h with | nil => exact .nil | cons head _ ih => exact .cons head ih
theorem Trace.ctor_rows {md : Mode} {cx : Ctx md} {st a c ms} (tr : Trace cx st a c ms) :
    List.Forall₂ (CtorRow cx a (.mk' cx c id (blockSelf cx a ms)) tr.rb.numParams)
      ((tr.shape.order.filterMap (indcAt ms)).toList.flatMap ctorInputs) tr.rb.ctors.toList := by
  apply forIn_inv_array (fun pre s => List.Forall₂ (CtorRow cx a (.mk' cx c id (blockSelf cx a ms)) tr.rb.numParams) (pre.flatMap ctorInputs) s.1.toList) _ _ ?_ .nil tr.ctors
  intro pre x post s r _ rows run
  rcases x with ⟨i, ind⟩
  unfold ctorClassStep at run
  obtain ⟨inner, innerRun, run⟩ := except_bind_ok.mp run
  obtain ⟨ys, eq, more⟩ := ctor_inner _ _ _ _ _ _ innerRun
  simp only [pure, Except.pure, Except.ok.injEq] at run
  subst r
  refine ⟨_, rfl, ?_⟩
  simpa [ctorInputs, eq] using forall₂_append rows (rows_map more)

structure Choice where
  motive : Nat
  rowIndex : Nat
  position : Nat
  prepared : Nat
  row : Row .anon
def memberInfo (ref : ConstRef Address) (r : Row .anon) : CInfo .anon :=
  match ref with | .member .. => .indInfo r.1 {} | .ctor .. => .ctorInfo r.1 r.2.1 r.2.2
def familyList (rb : BlockRead .anon) : List (CInfo .anon) :=
  match CtxAgree.indDeclOf rb with | .indDecl cs _ => cs | _ => []
def Matches (ref : ConstRef Address) (xs : List (Nat × Ixon.Inductive)) (rb : BlockRead .anon)
    (ds : Array (Declaration .anon)) (s : Choice) : Prop :=
  (match ref with
    | .member _ i => xs[s.motive]?.map Prod.fst = some i ∧ s.rowIndex = s.motive ∧
        s.position = s.motive ∧ rb.types.toList[s.rowIndex]? = some s.row
    | .ctor _ i j => xs[s.motive]?.map Prod.fst = some i ∧
        s.rowIndex = (xs.take s.motive |>.flatMap ctorInputs).length + j ∧
        ((xs.flatMap ctorInputs)[s.rowIndex]?).map (fun x => (x.1, x.2.2)) = some (i, j) ∧
        s.position = rb.types.size + s.rowIndex ∧ rb.ctors.toList[s.rowIndex]? = some s.row) ∧
  (familyList rb)[s.position]? = some (memberInfo ref s.row) ∧ ds[s.prepared]? = some (CtxAgree.indDeclOf rb)
instance (ref xs rb ds s) : Decidable (Matches ref xs rb ds s) := by unfold Matches; cases ref <;> infer_instance
structure MemberCheck (cx : Ctx .anon) (root : Address) (ref : ConstRef Address)
    (xs : List (Nat × Ixon.Inductive)) (rb : BlockRead .anon) (ds : Array (Declaration .anon)) where
  choice : Choice
  valid : Matches ref xs rb ds choice
  rootKey : cx.keyAt root = .ok choice.row.1.name
  memberKey : cx.memberKey ref = .ok choice.row.1.name
  address : cx.addressOf ref = .ok root
private def witnessed {α : Type} (x : ReadM α) : Except String { a // x = .ok a } :=
  match x with | .error e => .error s!"projection member: {e}" | .ok a => .ok ⟨a, rfl⟩

/-- Exact structural checks on raw guard inputs. Authentication/provenance
requires the genuine receipt's scan; arbitrary MemberCheck data is not admission. -/
def checkMember (cx : Ctx .anon) (root : Address) (ref : ConstRef Address)
    (xs : List (Nat × Ixon.Inductive)) (rb : BlockRead .anon) (ds : Array (Declaration .anon)) :
    Except String (MemberCheck cx root ref xs rb ds) := do
  let i := match ref with | .member _ i | .ctor _ i _ => i
  let some motive := xs.findIdx? (fun x => x.1 == i) | throw "projection member: motive is unavailable"
  let k := match ref with | .member .. => motive | .ctor _ _ j => (xs.take motive |>.flatMap ctorInputs).length + j
  let values := match ref with | .member .. => rb.types.toList | .ctor .. => rb.ctors.toList
  let some row := values[k]? | throw "projection member: emitted row is unavailable"
  let position := match ref with | .member .. => motive | .ctor .. => rb.types.size + k
  let some prepared := ds.findIdx? (fun d => decide (d = CtxAgree.indDeclOf rb))
    | throw "projection member: complete prepared family is unavailable"
  let s : Choice := ⟨motive, k, position, prepared, row⟩
  let rootKey ← witnessed (cx.keyAt root)
  let memberKey ← witnessed (cx.memberKey ref)
  let addr ← witnessed (cx.addressOf ref)
  if keys : rootKey.val = row.1.name ∧ memberKey.val = row.1.name ∧ addr.val = root then
    if hm : Matches ref xs rb ds s then
      return ⟨s, hm, keys.1 ▸ rootKey.property, keys.2.1 ▸ memberKey.property, keys.2.2 ▸ addr.property⟩
    else throw "projection member: exact member/order/family check failed"
  else throw "projection member: key or address correspondence failed"

private theorem row_at {α β : Type} {Q : α → β → Prop} {xs ys x y} {i : Nat}
    (rows : List.Forall₂ Q xs ys) (hx : xs[i]? = some x) (hy : ys[i]? = some y) : Q x y := by
  induction rows generalizing i with
  | nil => simp at hx
  | cons head tail ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy; cases hx; cases hy; exact head
    | succ i => exact ih hx hy
def RowSource (cx : Ctx .anon) (mr : MemberReader .anon) (n : Nat) (ref : ConstRef Address)
    (xs : List (Nat × Ixon.Inductive)) (s : Choice) : Prop := match ref with
  | .member a i => ∃ ind, xs[s.rowIndex]? = some (i, ind) ∧ TypeRow cx a mr (i, ind) s.row
  | .ctor a i j => ∃ ctor, (xs.flatMap ctorInputs)[s.rowIndex]? = some (i, ctor, j) ∧ CtorRow cx a mr n (i, ctor, j) s.row
theorem MemberCheck.row_source {cx : Ctx .anon} {st ref c ms root ds}
    (tr : Trace cx st ref.block c ms)
    (g : MemberCheck cx root ref (tr.shape.order.filterMap (indcAt ms)).toList tr.rb ds) :
    RowSource cx (.mk' cx c id (blockSelf cx ref.block ms)) tr.rb.numParams ref
      (tr.shape.order.filterMap (indcAt ms)).toList g.choice := by
  cases ref with
  | member a i =>
    obtain ⟨source, index, _, target⟩ := g.valid.1
    obtain ⟨⟨i', ind⟩, atSource, same⟩ := Option.map_eq_some_iff.mp source
    cases same
    rw [← index] at atSource
    exact ⟨ind, atSource, row_at tr.type_rows atSource target⟩
  | ctor a i j =>
    obtain ⟨_, _, source, _, target⟩ := g.valid.1
    obtain ⟨⟨i', ctor, j'⟩, atSource, same⟩ := Option.map_eq_some_iff.mp source
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact ⟨ctor, atSource, row_at tr.ctor_rows atSource target⟩

theorem member_original {binding limits records blobs hint receipt j}
    (accepted : DefinitionSnapshots.checkReceipt binding limits records blobs hint = .ok receipt)
    (packet : Packet limits records j) (located : locateBytes limits records j = .ok packet) :
    let l := packet.location; let cx := Admission.streamContext Address.admissionHash receipt.table receipt.pre packet.constants blobs hint
    ∀ st (tr : Trace cx st l.reference.block l.owner l.members), scanOwner cx receipt.pre.state l = .ok ⟨st, tr⟩ →
    ∀ g : MemberCheck cx l.address l.reference (tr.shape.order.filterMap (indcAt l.members)).toList tr.rb receipt.ds,
      checkMember cx l.address l.reference (tr.shape.order.filterMap (indcAt l.members)).toList tr.rb receipt.ds = .ok g →
      ∃ fin decls, AdmittedTargetFronts.RecordAt cx receipt.pre.state fin packet.constants decls l.ownerPosition l.reference.block l.owner st tr.read ∧
        Frontend.preparePrelude receipt.pre.ix decls = receipt.ds ∧ RowSource cx (.mk' cx l.owner id (blockSelf cx l.reference.block l.members)) tr.rb.numParams l.reference (tr.shape.order.filterMap (indcAt l.members)).toList g.choice := by
  intro l cx st tr scanned g _checked
  obtain ⟨fin, decls, st', tr', atOwner, prepared, run⟩ := scanOwner_same accepted packet located
  cases Except.ok.inj (scanned.symm.trans run)
  exact ⟨fin, decls, atOwner, prepared, g.row_source tr⟩

universe w
/-- One actual accepting fuel, with no assumption about how many constants
the current declaration installs or how their raw syntax is stored. -/
def IndexedRun {md : Mode} (ev : Evidences md) (ds : List (Declaration md)) (final : Env md)
    (i : Nat) (d : Declaration md) (F : Nat) (before after : Env md) : Prop :=
  let step := checkDecl .verified (fueledOps .verified F) ev
  ds[i]? = some d ∧ checkDeclsPure .verified (fueledOps .verified F) ev ds = .ok final ∧
  (ds.take i).foldlM step Env.empty = .ok before ∧ step before d = .ok after ∧
  (ds.drop (i + 1)).foldlM step after = .ok final

private theorem indexed_run {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
    {final : Env md} {i F : Nat} {d : Declaration md}
    (whole : checkDeclsPure .verified (fueledOps .verified F) ev ds = .ok final)
    (atDecl : ds[i]? = some d) : ∃ before after, IndexedRun ev ds final i d F before after := by
  obtain ⟨bound, atValue⟩ := List.getElem?_eq_some_iff.mp atDecl
  have split : ds = ds.take i ++ d :: ds.drop (i + 1) := by
    have eq := List.take_append_drop i ds
    rw [List.drop_eq_getElem_cons bound, atValue] at eq
    exact eq.symm
  have run := whole
  unfold checkDeclsPure at run
  rw [split] at run
  obtain ⟨before, pref, rest⟩ := foldlM_append_ok run
  rw [List.foldlM_cons] at rest
  obtain ⟨after, current, suffix⟩ := except_bind_ok.mp rest
  exact ⟨before, after, atDecl, whole, pref, current, suffix⟩

/-- The SAME guarded family index and genuine receipt supply the actual
family check trace. No checker executes here and no value claim is added. -/
theorem member_family_front (V : Type w) [SetTheory V] {binding limits records blobs hint receipt j}
    (accepted : DefinitionSnapshots.checkReceipt binding limits records blobs hint = .ok receipt)
    (packet : Packet limits records j) (located : locateBytes limits records j = .ok packet) :
    let l := packet.location; let cx := Admission.streamContext Address.admissionHash receipt.table receipt.pre packet.constants blobs hint
    ∀ st (tr : Trace cx st l.reference.block l.owner l.members), scanOwner cx receipt.pre.state l = .ok ⟨st, tr⟩ →
    ∀ g : MemberCheck cx l.address l.reference (tr.shape.order.filterMap (indcAt l.members)).toList tr.rb receipt.ds,
      checkMember cx l.address l.reference (tr.shape.order.filterMap (indcAt l.members)).toList tr.rb receipt.ds = .ok g →
      ∃ fin decls F before after, AdmittedTargetFronts.RecordAt cx receipt.pre.state fin packet.constants decls l.ownerPosition l.reference.block l.owner st tr.read ∧
        Frontend.preparePrelude receipt.pre.ix decls = receipt.ds ∧ RowSource cx (.mk' cx l.owner id (blockSelf cx l.reference.block l.members)) tr.rb.numParams l.reference (tr.shape.order.filterMap (indcAt l.members)).toList g.choice ∧
        IndexedRun receipt.ev receipt.ds.toList receipt.env g.choice.prepared (CtxAgree.indDeclOf tr.rb) F before after := by
  intro l cx st tr scanned g checked
  obtain ⟨fin, decls, owner, prepared, row⟩ := member_original accepted packet located st tr scanned g checked
  obtain ⟨_, _, _, run, _⟩ := DefinitionSnapshots.checkReceipt_ok accepted
  obtain ⟨F, whole⟩ := Cached.checkDecls_refines_ref V rfl run
  have atDecl : receipt.ds.toList[g.choice.prepared]? = some (CtxAgree.indDeclOf tr.rb) := by simpa using g.valid.2.2
  obtain ⟨before, after, front⟩ := indexed_run whole atDecl
  exact ⟨fin, decls, F, before, after, owner, prepared, row, front⟩

end Ix.Cert.ProjectionRoots
