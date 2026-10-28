import Ix.Cert.BlockEmission
import Ix.Cert.DefinitionBlocks

/-! # A block of definitions, each member at its own level parameters

`BlockEmission.mutualBlock_correct` reads a block whose members share their level parameters,
as an inductive block's do. The members of a definition group need not: the compiler compiles
each member under its own level parameters (`compileDefinitionData`), from the clean state the
previous member leaves (its expression cache cleared). `members_each` keeps each member's own
relation (`relOf`), and `defsBlock_each` carries the members' roots through the block's sharing
to the emitted record: the record is a block of definitions keeping their sources' headers, and
its member reader reads each member's type and value as terms related to the member's, at the
member's own level parameters. -/

namespace Ix.Cert.DefinitionEmission

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM MemberReader)
open Ix.Cert.BlockEmission (PayloadOf memberSources memberLps mutContext rel)

/-! ## Lists -/

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} (H : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {k : List β}, List.Forall₂ R l k → List.Forall₂ S l k
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hr rr => .cons (H _ _ hr) (forall₂_imp H rr)

theorem forall₂_flatMap_pair {α γ β δ : Type} {R : β → δ → Prop} (px py : α → β) (qx qy : γ → δ) :
    ∀ {l : List α} {k : List γ},
      List.Forall₂ R (l.flatMap fun a => [px a, py a]) (k.flatMap fun c => [qx c, qy c]) →
      List.Forall₂ (fun a c => R (px a) (qx c) ∧ R (py a) (qy c)) l k
  | [], [], _ => .nil
  | a :: l, c :: k, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.forall₂_cons] at h
    exact .cons ⟨h.1, h.2.1⟩ (forall₂_flatMap_pair px py qx qy h.2.2)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem forall₂_and {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {k : List β}, List.Forall₂ R l k → List.Forall₂ S l k →
      List.Forall₂ (fun a b => R a b ∧ S a b) l k
  | [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, .cons hr rr, .cons hs ss => .cons ⟨hr, hs⟩ (forall₂_and rr ss)

theorem forall₂_defns {P : MutConst → Ixon.MutConst → Prop} :
    ∀ (defs : List Ix.Def) (qs : List Ixon.Definition),
      List.Forall₂ P (defs.map MutConst.defn) (qs.map Ixon.MutConst.defn) →
      List.Forall₂ (fun d q => P (.defn d) (.defn q)) defs qs
  | [], [], _ => .nil
  | d :: defs, q :: qs, h => by
    rw [List.map_cons, List.map_cons, List.forall₂_cons] at h
    exact .cons h.1 (forall₂_defns defs qs h.2)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem forall₂_of_map_eq {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {k : List β}, l.map f = k.map g → List.Forall₂ (fun a b => f a = g b) l k
  | [], [], _ => .nil
  | a :: l, b :: k, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_of_map_eq h.2)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem forall₂_join {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop} :
    ∀ {l : List α} {m : List β} {k : List γ}, List.Forall₂ R l m → List.Forall₂ S k m →
      List.Forall₂ (fun a c => ∃ b, R a b ∧ S c b) l k
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons hr rr, .cons hs ss => .cons ⟨_, hr, hs⟩ (forall₂_join rr ss)

section Blocks

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
  (names : Ix.Name → CName md → Prop) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx param self

/-- A definition member's payload declares as many level parameters as its source has. -/
def LvlsOf (m : MutConst) (p : Ixon.MutConst) : Prop :=
  ∀ d q, m = .defn d → p = .defn q → q.lvls.toNat = d.levelParams.size

/-- The relation member `m`'s roots are read in: at its own level parameters, under its own
numbering `σOf m`. -/
abbrev relOf (σOf : MutConst → Ix.Name → LevelParam) (m : MutConst) : Ix.Expr → CExpr md → Prop :=
  rel param names (σOf m) (memberLps m)

/-- **The members of a block, one per class, each in its own relation.** -/
theorem members_each (σOf : MutConst → Ix.Name → LevelParam) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) :
    ∀ (ms : List MutConst) (acc : MutConstCompileState) {before after : BlockState}
      {state : MutConstCompileState},
      (∀ m ∈ ms, ∀ e ∈ memberSources m, ConstsSatisfy (SelfName context.2 self names) e) →
      (∀ m ∈ ms, Good cx param self (relOf param names σOf m) bindings before) →
      rawRun (compileMutConstMembers ms acc) context before = (.ok state, after) →
      ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
        ∃ ps : List Ixon.MutConst, state.payloads = acc.payloads ++ ps.toArray ∧
          List.Forall₂ (fun m p => PayloadOf m p ∧ LvlsOf m p ∧
            SharingRoots.RootsRead (reader after) (relOf param names σOf m) (memberSources m)
              (mutConstRootExprs p)) ms ps
  | [], acc, before, after, state, _, _, ran => by
    rw [compileMutConstMembers, rawRun_pure] at ran
    cases ran
    exact ⟨ExpressionRead.Extends.refl _, [], by simp, .nil⟩
  | m :: ms, acc, before, after, state, scopes, good, ran => by
    rw [compileMutConstMembers] at ran
    obtain ⟨member, middle, memberRan, restRan⟩ := bind_ok ran
    obtain ⟨clean₁, growth₁, payload₁, roots₁⟩ := BlockEmission.member_correct cx param self names (σOf m)
      bindings context aligned external m (scopes m List.mem_cons_self) (good m List.mem_cons_self)
      memberRan
    have lvls₁ : LvlsOf m member.payload := by
      intro d q hm hq
      subst hm
      obtain ⟨out, outRan, hp⟩ := BlockEmission.member_defn d memberRan
      rw [hp] at hq
      cases hq
      exact Emission.definitionData_header d _ _ _ _ outRan
    obtain ⟨growth₂, ps, hps, rest⟩ := members_each σOf context aligned external ms _
      (fun m' hm => scopes m' (List.mem_cons_of_mem _ hm)) (fun _ _ => clean₁.good cx param self _) restRan
    refine ⟨extends_trans growth₁ growth₂, member.payload :: ps, ?_,
      .cons ⟨payload₁, lvls₁, SharingRoots.RootsRead.grow growth₂ roots₁⟩ rest⟩
    rw [hps]
    simp [MutConstCompileState.addMember]

end Blocks

/-- The record's roots read as the in-flight reader read the payload's. -/
theorem build_reads {md : Mode} (context : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (state : BlockState) (limits : Ix.Sharing.Exact.Limits)
    (info : Ixon.ConstantInfo) (out : Ixon.Constant)
    (ran : buildConstantWithSharing limits info state.refs state.univs = .ok out) :
    SharingRoots.erase out.info = SharingRoots.erase info ∧
      (constantInfoRootExprs out.info).toList.map
          (MemberReader.mk' (ExpressionRead.withBlockBlobs context state) out param self).read =
        (constantInfoRootExprs info).toList.map (ExpressionRead.blockReader context param self state).read := by
  obtain ⟨erased, _, _, reads⟩ := SharingRoots.build_roots limits info state.refs state.univs out ran
  refine ⟨erased, ?_⟩
  have same := congrArg Array.toList (reads (ExpressionRead.withBlockBlobs context state) param self)
  simp only [Array.toList_map] at same
  rw [same]
  apply List.map_congr_left
  intro root _
  exact SharingRoots.unshared_read context param self state info root

theorem payload_defns : ∀ (defs : List Ix.Def) (ps : List Ixon.MutConst),
    List.Forall₂ PayloadOf (defs.map MutConst.defn) ps → ∃ qs : List Ixon.Definition, ps = qs.map .defn
  | [], ps, h => by
    cases h
    exact ⟨[], rfl⟩
  | d :: defs, ps, h => by
    rw [List.map_cons] at h
    cases h with
    | cons hp rest =>
      obtain ⟨qs, rfl⟩ := payload_defns defs _ rest
      obtain ⟨q, rfl, -⟩ := hp
      exact ⟨q :: qs, rfl⟩

theorem defns_of_erase : ∀ (ms : List Ixon.MutConst) (qs : List Ixon.Definition),
    ms.map SharingRoots.eraseMut = qs.map (fun q => SharingRoots.eraseMut (.defn q)) →
    ∃ ts : List Ixon.Definition, ms = ts.map .defn ∧
      List.Forall₂ (fun t q => t.kind = q.kind ∧ t.safety = q.safety ∧ t.lvls = q.lvls) ts qs
  | [], [], _ => ⟨[], rfl, .nil⟩
  | m :: ms, q :: qs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨ts, rfl, hr⟩ := defns_of_erase ms qs h₂
    cases m with
    | defn t =>
      simp only [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots, Ixon.MutConst.defn.injEq,
        Ixon.Definition.mk.injEq] at h₁
      exact ⟨t :: ts, rfl, .cons ⟨h₁.1, h₁.2.1, h₁.2.2.1⟩ hr⟩
    | indc i => simp [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots] at h₁
    | recr r => simp [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots] at h₁
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem defns_roots (ts : List Ixon.Definition) :
    (constantInfoRootExprs (.muts (ts.map Ixon.MutConst.defn).toArray)).toList =
      ts.flatMap fun t => [t.typ, t.value] := by
  simp only [constantInfoRootExprs, List.toList_toArray, List.flatMap_map]
  rfl

section Definitions

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
  (names : Ix.Name → CName md → Prop) (bindings : Bindings)

/-- **A definition block compiled in its members' order, as its record**: the record is a block of
definitions keeping their sources' headers, and its member reader reads each member's type and
value as terms related to the member's, at the member's own level parameters. -/
theorem defsBlock_each (σOf : MutConst → Ix.Name → LevelParam) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (defs : List Ix.Def) (two : 2 ≤ defs.length)
    (scopes : ∀ m ∈ defs.map MutConst.defn, ∀ e ∈ memberSources m,
      ConstsSatisfy (SelfName (mutContext (defs.map MutConst.defn) context).2 self names) e)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileMutualBlock (defs.map MutConst.defn)) context before = (.ok output, after)) :
    ∃ targets : List Ixon.Definition, output.block.info = .muts (targets.map Ixon.MutConst.defn).toArray ∧
      List.Forall₂ (fun d t => t = Emission.definitionPayload d t.typ t.value ∧ t.lvls.toNat = d.levelParams.size ∧
        (∃ type, (EmissionBlocks.recordReader cx param self after output.block).read t.typ = .ok type ∧
          relOf param names σOf (.defn d) d.type type) ∧
        (∃ value, (EmissionBlocks.recordReader cx param self after output.block).read t.value = .ok value ∧
          relOf param names σOf (.defn d) d.value value)) defs targets := by
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, seededState, seeded, compiled⟩ := bind_ok ran
  have kept : ∀ m ∈ defs.map MutConst.defn, Good cx param self (relOf param names σOf m) bindings seededState :=
    fun m _ => (EmissionBlocks.preseed_then cx param self bindings (related := relOf param names σOf m)
      (context := mutContext (defs.map MutConst.defn) context) aligned
      (clean.good cx param self _) seeded).1
  unfold compileMutualPayload at compiled
  obtain ⟨payload, middle, payloadRan, finished⟩ := bind_ok compiled
  unfold compileMutConsts at payloadRan
  obtain ⟨state, middle', classesRan, finish⟩ := bind_ok payloadRan
  rw [rawRun_pure] at finish
  cases finish
  obtain ⟨_, ps, hps, each⟩ := members_each cx param self names bindings σOf
    (mutContext (defs.map MutConst.defn) context) aligned external (defs.map MutConst.defn) {}
    scopes kept classesRan
  obtain ⟨same, _, built⟩ := ProjectionLayout.finish_mutual_ok _ _ _ _ finished
  subst same
  simp only [hps] at built
  have hps' : (({} : MutConstCompileState).payloads ++ ps.toArray) = ps.toArray := by
    simp
  rw [hps'] at built
  unfold buildCompiledMutualBlock at built
  -- the payloads are definitions
  obtain ⟨qs, rfl⟩ := payload_defns defs ps (forall₂_imp (fun _ _ h => h.1) each)
  have hlen : qs.length = defs.length := by
    simpa using (DefinitionBlocks.forall₂_length each).symm
  have hs : standaloneMutConstInfo? (qs.map Ixon.MutConst.defn).toArray = none := by
    rcases qs with _ | ⟨q, _ | ⟨q₂, rest⟩⟩
    · simp at hlen; omega
    · simp at hlen; omega
    · rfl
  rw [hs] at built
  obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
  cases Except.ok.inj returned
  obtain ⟨erased, reads⟩ := build_reads cx param self _ _ _ block hb
  -- the record's definitions keep the payloads' headers
  have hblock : ∃ ts : List Ixon.Definition, block.info = .muts (ts.map Ixon.MutConst.defn).toArray ∧
      List.Forall₂ (fun t q => t.kind = q.kind ∧ t.safety = q.safety ∧ t.lvls = q.lvls) ts qs := by
    cases hinfo : block.info with
    | muts ms =>
      rw [hinfo] at erased
      simp only [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, Ixon.ConstantInfo.muts.injEq] at erased
      have hl : ms.toList.map SharingRoots.eraseMut = qs.map (fun q => SharingRoots.eraseMut (.defn q)) := by
        have := congrArg Array.toList erased
        simp only [Array.toList_map, List.map_toArray, List.map_map, Function.comp_def] at this
        exact this
      obtain ⟨ts, hms, hr⟩ := defns_of_erase ms.toList qs hl
      exact ⟨ts, by rw [← hms], hr⟩
    | _ => rw [hinfo] at erased; simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots] at erased
  obtain ⟨ts, hinfo, headers⟩ := hblock
  rw [hinfo, defns_roots, defns_roots] at reads
  -- the record's roots read as the payloads' did
  have readsF := forall₂_flatMap_pair Ixon.Definition.typ Ixon.Definition.value Ixon.Definition.typ
    Ixon.Definition.value (forall₂_of_map_eq reads)
  -- each payload keeps its source's header and its roots read as related terms
  have each' : List.Forall₂ (fun d q => q = Emission.definitionPayload d q.typ q.value ∧
      q.lvls.toNat = d.levelParams.size ∧
      (∃ t, relOf param names σOf (.defn d) d.type t ∧
        (ExpressionRead.blockReader cx param self after).read q.typ = .ok t) ∧
      (∃ t, relOf param names σOf (.defn d) d.value t ∧
        (ExpressionRead.blockReader cx param self after).read q.value = .ok t)) defs qs :=
    forall₂_imp (fun d q h => by
      obtain ⟨⟨target, ht, hp⟩, lv, roots⟩ := h
      cases ht
      simp only [SharingRoots.RootsRead, memberSources, mutConstRootExprs, List.forall₂_cons] at roots
      exact ⟨hp, lv d _ rfl rfl, roots.1, roots.2.1⟩) (forall₂_defns defs qs each)
  refine ⟨ts, hinfo, forall₂_imp (fun d t h => ?_) (forall₂_join each' (forall₂_and headers readsF))⟩
  obtain ⟨q, ⟨hq, hlv, ⟨tT, rT, hT⟩, ⟨tV, rV, hV⟩⟩, ⟨hk, hs, hl⟩, eT, eV⟩ := h
  refine ⟨?_, by rw [hl]; exact hlv, ⟨tT, eT.trans hT, rT⟩, ⟨tV, eV.trans hV, rV⟩⟩
  rw [hq] at hk hs hl
  obtain ⟨kind, safety, lvls, typ, value⟩ := t
  simp only [Emission.definitionPayload] at hk hs hl ⊢
  rw [hk, hs, hl]

end Definitions

/--
info: 'Ix.Cert.DefinitionEmission.defsBlock_each' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms defsBlock_each

end Ix.Cert.DefinitionEmission
