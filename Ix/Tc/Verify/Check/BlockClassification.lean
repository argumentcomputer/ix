import Ix.Tc.Verify.Check.BlockRouting

/-!
# Coordinated block classification

Production classifies a block by loading every ordered member, accumulating
three shape flags, and accepting exactly one homogeneous flag.  This module
proves that process against `ExactCheckBlock`: every successful lookup is the
immutable catalog entry, the accumulator records the catalogued kind, and a
successful classifier result is exactly that kind.  Both success and error
paths preserve the caller's invariant through lazy ingress.
-/

namespace Ix.Tc

namespace RecM.BlockClassFlags

/-- Proof-side description of recording one member of a known exact kind. -/
def mark (flags : BlockClassFlags) : CheckBlockKind → BlockClassFlags
  | .defn => { flags with sawDefn := true }
  | .inductive' => { flags with sawInductiveLike := true }
  | .recursor => { flags with sawRecr := true }

/-- A catalog declaration owned by one coordinated kind makes production's
shape recorder perform exactly the corresponding flag update. -/
theorem note_of_member
    {catalog : Catalog} {block member : KId .anon}
    {kind : CheckBlockKind} {concrete : KConst .anon}
    (h : concrete.IsMemberOfKind catalog block kind)
    (flags : BlockClassFlags) :
    flags.note member concrete = .ok (mark flags kind) := by
  cases kind <;> cases concrete <;>
    simp [KConst.IsMemberOfKind, KConst.IsDefinitionMemberOf,
      KConst.IsInductiveMemberOf, KConst.IsRecursorMemberOf, note, mark]
      at h ⊢

/-- The flag state after observing at least one member of one kind. -/
def only (kind : CheckBlockKind) : BlockClassFlags :=
  mark BlockClassFlags.empty kind

@[simp] theorem mark_only (kind : CheckBlockKind) :
    mark (only kind) kind = only kind := by
  cases kind <;> rfl

theorem foldl_mark_only (kind : CheckBlockKind)
    (members : List (KId .anon)) :
    members.foldl (fun acc _ => mark acc kind) (only kind) = only kind := by
  induction members with
  | nil => rfl
  | cons member rest ih => simpa using ih

/-- Starting empty and observing a nonempty homogeneous list leaves exactly
one kind flag set. -/
theorem foldl_mark_empty_of_nonempty (kind : CheckBlockKind)
    {members : List (KId .anon)} (h : members ≠ []) :
    members.foldl (fun acc _ => mark acc kind) BlockClassFlags.empty =
      only kind := by
  cases members with
  | nil => contradiction
  | cons member rest =>
      simpa [only] using foldl_mark_only kind rest

@[simp] theorem finish_only (kind : CheckBlockKind) :
    BlockClassFlags.finish (m := .anon) (only kind) = .ok kind := by
  cases kind <;> rfl

end RecM.BlockClassFlags

namespace RecM

/-- Classification's ordered member scan preserves any invariant preserved
by lazy ingress.  This frame theorem deliberately makes no semantic claim
about the resulting flags; exact-kind correctness is proved below. -/
theorem collectBlockClassFlags_wf
    {I : TcState .anon → Prop} {methods : Methods .anon}
    (hfault : TcM.LazyFaultPreserves I)
    (members : List (KId .anon)) (flags : BlockClassFlags)
    (state : TcState .anon) :
    TcM.WF I state
      ((collectBlockClassFlags members flags).run methods)
      (fun _ _ => True) := by
  induction members generalizing flags state with
  | nil =>
      simpa [collectBlockClassFlags] using
        (TcM.WF.pure (I := I) (s := state) (a := flags) fun _ => trivial)
  | cons member rest ih =>
      unfold collectBlockClassFlags
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.WF.bind (TcM.getConst_loaded_wf hfault member state)
      intro concrete after _
      cases hnote : flags.note member concrete with
      | error err =>
          simpa only using
            (TcM.WF.throw (I := I) (s := after) fun _ => trivial)
      | ok next =>
          simpa only using ih next after

/-- The complete classifier, including empty/mixed-block errors, preserves
any invariant preserved by lazy ingress. -/
theorem classifyBlock_wf
    {I : TcState .anon → Prop} {methods : Methods .anon}
    (hfault : TcM.LazyFaultPreserves I)
    (members : Array (KId .anon)) (state : TcState .anon) :
    TcM.WF I state ((classifyBlock members).run methods)
      (fun _ _ => True) := by
  unfold classifyBlock
  split
  · exact TcM.WF.throw fun _ => trivial
  · apply TcM.WF.bind
      (collectBlockClassFlags_wf hfault members.toList
        BlockClassFlags.empty state)
    intro flags after _
    match hfinish : BlockClassFlags.finish (m := .anon) flags with
    | .error err =>
        simp only [hfinish]
        exact TcM.WF.throw (I := I) (s := after)
          (Q := fun _ _ => True) (E := fun _ _ => True) fun _ => trivial
    | .ok kind =>
        simp only [hfinish]
        exact TcM.WF.pure (I := I) (s := after) (a := kind)
          (Q := fun _ _ => True) (E := fun _ _ => True) fun _ => trivial

/-- The ordered production census preserves an arbitrary caller invariant
and returns exactly the fold of the known homogeneous kind.  `hloaded` is the
only representation premise: it prevents lazy ingress from substituting a
different declaration under the same member key. -/
theorem collectBlockClassFlags_exact_wf
    {I : TcState .anon → Prop} {world : VerifyWorld}
    {methods : Methods .anon} {block : KId .anon}
    {kind : CheckBlockKind}
    (hloaded : ∀ {state}, I state →
      LoadedAgrees world.catalog state.env)
    (hfault : TcM.LazyFaultPreserves I)
    (members : List (KId .anon))
    (hcoord : ∀ id ∈ members,
      world.catalog.CoordinatedMember block kind id)
    (flags : BlockClassFlags) (state : TcState .anon) :
    TcM.WF I state
      ((collectBlockClassFlags members flags).run methods)
      (fun result _ => result = members.foldl
        (fun acc _ => BlockClassFlags.mark acc kind) flags) := by
  induction members generalizing flags state with
  | nil =>
      simpa [collectBlockClassFlags] using
        (TcM.WF.pure (I := I) (s := state) (a := flags) fun _ => rfl)
  | cons member rest ih =>
      unfold collectBlockClassFlags
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.WF.bind
        (TcM.WF.withInv (TcM.getConst_loaded_wf hfault member state))
      intro concrete after hpost
      have hcatalogFound : world.catalog member = some concrete :=
        hloaded hpost.1 hpost.2
      obtain ⟨expected, hcatalog, hshape⟩ := hcoord member (by simp)
      have hconcrete : concrete = expected :=
        Option.some.inj (hcatalogFound.symm.trans hcatalog)
      subst concrete
      rw [BlockClassFlags.note_of_member hshape]
      simpa using ih (fun id hid => hcoord id (by simp [hid]))
        (BlockClassFlags.mark flags kind) after

/-- Complete classifier correctness for an exact immutable block.  A lazy
fault may still make the computation fail, but every outcome preserves `I`,
and every successful result equals the exact catalog kind. -/
theorem classifyBlock_exact_wf
    {I : TcState .anon → Prop} {world : VerifyWorld}
    {methods : Methods .anon} {block : KId .anon}
    {kind : CheckBlockKind} {members : Array (KId .anon)}
    (hloaded : ∀ {state}, I state →
      LoadedAgrees world.catalog state.env)
    (hfault : TcM.LazyFaultPreserves I)
    (hexact : ExactCheckBlock world block members kind)
    (state : TcState .anon) :
    TcM.WF I state ((classifyBlock members).run methods)
      (fun result _ => result = kind) := by
  unfold classifyBlock
  have hpositive := hexact.nonempty
  have hsize : members.size ≠ 0 := by omega
  simp only [Array.isEmpty, hsize]
  apply TcM.WF.bind
    (collectBlockClassFlags_exact_wf hloaded hfault members.toList
      (fun id hid => hexact.coordinated (by simpa using hid))
      BlockClassFlags.empty state)
  intro flags after hflags
  have hlist : members.toList ≠ [] := by
    intro hempty
    have : members.size = 0 := by
      simpa using congrArg List.length hempty
    exact hsize this
  rw [hflags, BlockClassFlags.foldl_mark_empty_of_nonempty kind hlist]
  simpa [BlockClassFlags.finish_only] using
    (TcM.WF.pure (I := I) (s := after) (a := kind) fun _ => rfl)

/-- Concrete success corollary used to refine an existential body trace to
the exact catalog kind. -/
theorem classifyBlock_success_exact
    {I : TcState .anon → Prop} {world : VerifyWorld}
    {methods : Methods .anon} {block : KId .anon}
    {expected actual : CheckBlockKind}
    {members : Array (KId .anon)} {before after : TcState .anon}
    (hloaded : ∀ {state}, I state →
      LoadedAgrees world.catalog state.env)
    (hfault : TcM.LazyFaultPreserves I)
    (hexact : ExactCheckBlock world block members expected)
    (hbefore : I before)
    (hrun : (classifyBlock members).run methods before = .ok actual after) :
    I after ∧ actual = expected := by
  have hpost := classifyBlock_exact_wf (methods := methods) hloaded hfault
    hexact before hbefore
  rw [hrun] at hpost
  exact hpost

end RecM

end Ix.Tc
