import Ix.Cert.RecordReadings
import Ix.Cert.DefinitionEmission
import Ix.Cert.DefinitionDeps
import Ix.Cert.DefinitionOrder
import Ix.CompileCert.Canon.Ctx

/-! # A definition block reads as quotient Source's group

The reader reads a definition block of several members in `defOrder` over the members each
member names by `recur`, each member at its hint; quotient Source lowers a group of several
definitions in `defOrder` over the members each converted member mentions, each member at its
hint. A compiled block's member names member `j` by `recur` exactly where its Lean terms mention
member `j`'s name (`DefinitionOrder.recurDeps_read` through a reading with fresh member keys,
`DefinitionDeps.related_occurs`), and a converted member mentions member `j`'s key exactly where
its Lean terms mention a name of that ingress key (`DefinitionDeps.ingress_occurs`); for names
exact at the members' ingress names the two orders agree (`DefinitionOrder.defOrder_congr`).
Each member then reads as quotient Source's member renamed, as a singleton does
(`RecordReadings.definition_reads`); under a hint a definition's lowering does not read the
heights, so the block's running heights do not matter.

* `convertDefinitions_block`: what quotient Source converts a group of several definitions to.
* `forIn_decls`: a loop that pushes one declaration per item.
* `definition_block_reads`: a compiled definition block reads, in a closure's context and from
  any state related to quotient Source's, as quotient Source's group renamed. -/

namespace Ix.Cert.DefinitionBlockReads

open Ix.Kernel Ix.Kernel.Reader
open Ix.LeanIngress (FiberMap Numbering ingressKey ingressExpr canonLevelIn mapLevels)
open Ix.CompileCert.ExpressionState (Related)
open Ix.CompileCert.UniversePipeline (LevelMeaning)
open Ix.Cert.RecordReadings (sourceNames quotientMember)

/-! ## Quotient Source's conversion -/

/-- **A group of several definitions converts** to its members, each under its own numbering
and ingress key, every member safe, in `defOrder` over their dependency sets. -/
theorem convertDefinitions_block {members : Array Ix.ConstantInfo} {c : Ix.LeanIngress.Converted}
    (h : Ix.LeanIngress.convertDefinitions members = .ok c) (hsize : 2 ≤ members.size) :
    ∃ (ms : Array Ix.LeanIngress.DefMember) (order : Array Nat), ms.size = members.size ∧
      (∀ k (hk : k < members.size), ∃ s v t' v', Ix.LeanIngress.definitionShape members[k] = some s ∧
        Ix.LeanIngress.definitionValue members[k] = some v ∧
        ingressExpr (Numbering.mk members[k].getCnst.levelParams false).pos members[k].getCnst.type = .ok t' ∧
        ingressExpr (Numbering.mk members[k].getCnst.levelParams false).pos v = .ok v' ∧
        safetyDeclineOf s.1 s.2.1 = none ∧
        ms[k]? = some ⟨⟨ingressKey members[k].getCnst.name,
          (Numbering.mk members[k].getCnst.levelParams false).params, t'⟩, v', s.1, s.2.1, s.2.2⟩) ∧
      defOrder (DefinitionBlocks.depsOf ms) = some order ∧ c = .definitions (order.map (ms[·]!)) := by
  unfold Ix.LeanIngress.convertDefinitions at h
  obtain ⟨shapes, hshapes, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  have F := ReaderUnits.array_mapM_ok hshapes
  have hlen : shapes.size = members.size := by
    simpa using (DefinitionBlocks.forall₂_length F).symm
  have hshape : ∀ k (hk : k < members.size), ∃ s v, Ix.LeanIngress.definitionShape members[k] = some s ∧
      Ix.LeanIngress.definitionValue members[k] = some v ∧ shapes.toList[k]? = some (members[k], s, v) := by
    intro k hk
    obtain ⟨y, hy, hf⟩ := DefinitionBlocks.forall₂_getElem? F (k := k) (a := members[k]) (by simp [hk])
    split at hf
    · rename_i s v hs hv
      simp only [pure, Except.pure, Except.ok.injEq] at hf
      exact ⟨s, v, hs, hv, by rw [hy, hf]⟩
    · cases hf
  have hgt : shapes.size > 1 := by omega
  simp only [hgt, ↓reduceIte] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rename_i noDecline
    have safe : ∀ x ∈ shapes.toList, Ix.Kernel.Reader.safetyDeclineOf x.2.1.1 x.2.1.2.1 = none := by
      intro x hx
      cases hw : Ix.Kernel.Reader.safetyDeclineOf x.2.1.1 x.2.1.2.1 with
      | none => rfl
      | some w =>
        exfalso
        cases hfs : shapes.findSome? (fun (_, (k, s, _), _) => Ix.Kernel.Reader.safetyDeclineOf k s) with
        | some w' => exact noDecline w' hfs
        | none =>
          rw [Array.findSome?_eq_none_iff] at hfs
          have := hfs x (Array.mem_toList_iff.mp hx)
          obtain ⟨ci, ⟨kd, sf, hint⟩, v⟩ := x
          dsimp only at hw this
          rw [hw] at this
          cases this
    obtain ⟨ks, hks, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    have hms : ¬ (shapes.zipIdx.size ≤ 1) := by simp; omega
    simp only [Array.size_map, hms, ↓reduceIte] at h
    split at h
    · rename_i order hdef
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨_, order, by simp [hlen], fun k hk => ?_, hdef, h.symm⟩
      obtain ⟨s, v, hs, hv, hsh⟩ := hshape k hk
      have hitems := SourceConversion.exprsOf_exact hks
      have hlist : (Array.flatMap (fun x : Ix.ConstantInfo × (Ix.DefKind × Ix.DefinitionSafety ×
            ReducibilityHint) × Ix.Expr =>
          #[((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.1.getCnst.type),
            ((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.2.2)]) shapes).toList =
          shapes.toList.flatMap fun x => [((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.1.getCnst.type),
            ((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.2.2)] := by
        simp [Array.toList_flatMap]
      rw [hlist] at hitems
      obtain ⟨h0, h1⟩ := DefinitionBlocks.flatMap_pair_getElem? (fun x : Ix.ConstantInfo ×
          (Ix.DefKind × Ix.DefinitionSafety × ReducibilityHint) × Ix.Expr =>
            ((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.1.getCnst.type))
        (fun x => ((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.2.2)) shapes.toList k
      rw [hsh] at h0 h1
      obtain ⟨t', ht', hσ⟩ := DefinitionBlocks.forall₂_getElem? hitems h0
      obtain ⟨v', hv', hτ⟩ := DefinitionBlocks.forall₂_getElem? hitems h1
      refine ⟨s, v, t', v', hs, hv, hσ, hτ, safe _ (List.mem_of_getElem? hsh), ?_⟩
      have hk0 : ks[2 * k]! = t' := by
        rw [Array.getElem?_toList] at ht'
        simp [getElem!_def, ht']
      have hk1 : ks[2 * k + 1]! = v' := by
        rw [Array.getElem?_toList] at hv'
        simp [getElem!_def, hv']
      have hshk : shapes[k]? = some (members[k], s, v) := by
        rw [← Array.getElem?_toList]
        exact hsh
      simp [Array.getElem?_zipIdx, hshk, hk0, hk1]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The lowering at a hint -/

/-- **Under a hint, a definition's lowering does not read the heights.** -/
theorem lowerDefinition_heights {md : Mode} (h : ReducibilityHint) (st : State md)
    (heights heights' : CName md → Nat) (cv : CVal md) (value : CExpr md) (kind : Ix.DefKind)
    (safety : Ix.DefinitionSafety) :
    lowerDefinition (some h) st heights cv value kind safety =
      lowerDefinition (some h) st heights' cv value kind safety := by
  unfold lowerDefinition
  simp only [Option.getD_some]

/-! ## The block's loops -/

theorem forIn_out {α S D ε : Type} (f : α → S → Except ε (ForInStep S)) (out : S → Array D) (d : α → D) :
    ∀ (l : List α), (∀ a ∈ l, ∀ s, ∃ s', f a s = .ok (.yield s') ∧ out s' = (out s).push (d a)) →
      ∀ s, ∃ s', forIn l s f = .ok s' ∧ out s' = out s ++ (l.map d).toArray
  | [], _, s => ⟨s, by rw [List.forIn_nil]; rfl, by simp⟩
  | a :: l, step, s => by
    obtain ⟨s₁, ha, h₁⟩ := step a List.mem_cons_self s
    obtain ⟨s₂, hl, h₂⟩ := forIn_out f out d l (fun b hb => step b (List.mem_cons_of_mem _ hb)) s₁
    refine ⟨s₂, ?_, ?_⟩
    · rw [List.forIn_cons, ha]
      exact hl
    · rw [h₂, h₁]
      simp

theorem forIn_bind_ok {α S D ε β : Type} (f : α → S → Except ε (ForInStep S)) (out : S → Array D) (d : α → D)
    (l : List α) (s : S) (k : S → Except ε β) (P : β → Prop)
    (step : ∀ a ∈ l, ∀ s, ∃ s', f a s = .ok (.yield s') ∧ out s' = (out s).push (d a))
    (hk : ∀ s', out s' = out s ++ (l.map d).toArray → ∃ b, k s' = .ok b ∧ P b) :
    ∃ b, (forIn l s f >>= k) = .ok b ∧ P b := by
  obtain ⟨s', hl, ho⟩ := forIn_out f out d l step s
  obtain ⟨b, hb, hp⟩ := hk s' ho
  exact ⟨b, by rw [hl]; exact hb, hp⟩

/-- The self references of a block of `N` members at `owner`. -/
abbrev blockSelf {md : Mode} (cx : Ctx md) (owner : Address) (N : Nat) : Nat → Option (ReadM (CName md)) :=
  fun k => if k < N then some (cx.memberKey (.member owner k)) else none

/-- **The reader on a definition block** whose members are safe, in an order: it reads each
member in the order at its own position. -/
theorem readRecord_defs {md : Mode} {cx : Ctx md} {st : State md} {owner : Address} {c : Ixon.Constant}
    {ts : List Ixon.Definition} (hc : c.info = .muts (ts.map Ixon.MutConst.defn).toArray) (hne : ts ≠ [])
    (safe : ∀ t ∈ ts, safetyDecline t = none) {order : Array Nat}
    (hord : defOrder (ts.toArray.map (recurDeps c)) = some order) (d : Nat → CDecl md) {N : Nat}
    (hN : ts.length = N)
    (step : ∀ i ∈ order.toList, ∀ heights : CName md → Nat, ∃ rw,
      readDefinition cx st heights (.member owner i) (List.range ts.toArray[i]!.lvls.toNat)
        (MemberReader.mk' cx c id (blockSelf cx owner N))
        ts.toArray[i]! = .ok (d i, rw)) :
    ∃ r, readRecord cx st owner c = .ok r ∧ StreamRename.Plain r ∧ r.decls = (order.toList.map d).toArray := by
  subst hN
  unfold readRecord
  rw [hc]
  simp only
  split
  · rename_i hany
    simp at hany
  split
  · rename_i hall
    obtain ⟨t, ts', rfl⟩ := List.exists_cons_of_ne_nil hne
    simp at hall
  split
  · generalize hD : Array.filterMap _ (List.map Ixon.MutConst.defn ts).toArray = D
    have hD' : D = ts.toArray := by
      rw [← hD]
      simp [Function.comp_def]
    subst hD'
    have hfind : ts.toArray.findSome? safetyDecline = none :=
      Array.findSome?_eq_none_iff.mpr (fun t ht => safe t (by simpa using ht))
    rw [hfind, hord]
    simp only [List.size_toArray, List.length_map]
    rw [← Array.forIn_toList]
    refine forIn_bind_ok _ (fun s => s.2.1) d _ _ _
      (fun r => StreamRename.Plain r ∧ r.decls = (order.toList.map d).toArray) ?_ ?_
    · intro i hi s
      obtain ⟨rw, hrd⟩ := step i hi (fun n => s.1.getD n (st.heights.getD n 0))
      rw [hrd]
      simp only [bind, Except.bind]
      split <;> split <;> exact ⟨_, rfl, rfl⟩
    · intro s' hs'
      refine ⟨_, rfl, ⟨rfl, rfl, rfl⟩, ?_⟩
      rw [hs']
      simp
  · rename_i hall
    simp at hall

theorem forIn_out_inv {α S D ε : Type} (f : α → S → Except ε (ForInStep S)) (out : S → Array D)
    (R : α → D → Prop)
    (step : ∀ a s s₁, f a s = .ok s₁ → ∃ s' d, s₁ = .yield s' ∧ out s' = (out s).push d ∧ R a d) :
    ∀ (l : List α) (s s' : S), forIn l s f = .ok s' →
      ∃ ds : List D, out s' = out s ++ ds.toArray ∧ List.Forall₂ R l ds
  | [], s, s', h => by
    rw [List.forIn_nil] at h
    cases h
    exact ⟨[], by simp, .nil⟩
  | a :: l, s, s', h => by
    rw [List.forIn_cons] at h
    obtain ⟨s₁, hs₁, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨s'', d, rfl, ho, hr⟩ := step a s s₁ hs₁
    obtain ⟨ds, ho', hrs⟩ := forIn_out_inv f out R step l s'' s' h
    refine ⟨d :: ds, ?_, .cons hr hrs⟩
    rw [ho', ho]
    simp

/-- **Quotient Source on a group of several definitions**: each member lowered in turn. -/
theorem lower_defs {st : State .source} {ms : Array Ix.LeanIngress.DefMember}
    {r : Read .source} (h : Ix.LeanIngress.lower st (.definitions ms) = .ok r) :
    ∃ ds : List (CDecl .source), r.decls = ds.toArray ∧ StreamRename.Plain r ∧ List.Forall₂ (fun m decl => ∃ rw,
      lowerDefinition (some m.hint) st (st.heights.getD · 0) m.cv m.value m.kind m.safety = .ok (decl, rw))
        ms.toList ds := by
  unfold Ix.LeanIngress.lower at h
  delta Ix.LeanIngress.lower.match_6 at h
  dsimp only at h
  split at h
  · rename_i hsz
    obtain ⟨l⟩ := ms
    obtain _ | ⟨m, _ | ⟨_, _⟩⟩ := l
    · cases hsz
    · simp only at h
      obtain ⟨⟨decl, rw⟩, hd, h⟩ := RecordTransfer.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨[decl], rfl, ⟨rfl, rfl, rfl⟩, .cons ⟨rw, hd⟩ .nil⟩
    · simp at hsz
  · obtain ⟨s, hs, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [← Array.forIn_toList] at hs
    obtain ⟨ds, ho, hr⟩ := forIn_out_inv _ (fun s => s.2.1) (fun m decl => ∃ rw, lowerDefinition (some m.hint)
        st (st.heights.getD · 0) m.cv m.value m.kind m.safety = .ok (decl, rw)) (fun m s q hq => by
          obtain ⟨⟨decl, rw⟩, hd, hq⟩ := RecordTransfer.bind_ok hq
          rw [lowerDefinition_heights _ _ _ (st.heights.getD · 0)] at hd
          dsimp only at hq
          split at hq <;> split at hq <;>
          · simp only [pure, Except.pure, Except.ok.injEq] at hq
            subst hq
            exact ⟨_, _, rfl, rfl, rw, hd⟩) _ _ _ hs
    exact ⟨ds, by rw [ho]; simp, ⟨rfl, rfl, rfl⟩, hr⟩

/-! ## One member -/

/-- **A member read as related terms lowers as quotient Source's member renamed**, at its hint,
whatever the heights on either side. -/
theorem member_lower {ρ : FiberMap} {f : Mode.Id .source → Mode.Id .anon} {P : KeyScope .source}
    (hP : P.Pre) (hf : InjOn f P) {source : Ix.Def} (nodup : source.levelParams.toList.Nodup)
    {tA vA : CExpr .anon}
    (typeRel : Related (sourceNames ρ f)
      (LevelMeaning source.levelParams.toList (Numbering.mk source.levelParams false).pos id) source.type tA)
    (valueRel : Related (sourceNames ρ f)
      (LevelMeaning source.levelParams.toList (Numbering.mk source.levelParams false).pos id) source.value vA)
    {t' v' : CExpr .source}
    (ht' : ingressExpr (Numbering.mk source.levelParams false).pos source.type = .ok t')
    (hv' : ingressExpr (Numbering.mk source.levelParams false).pos source.value = .ok v')
    {m0 : Ix.LeanIngress.DefMember} {hint0 h : ReducibilityHint}
    (hm0 : m0 = ⟨⟨ingressKey source.name, (Numbering.mk source.levelParams false).params, t'⟩, v',
      source.kind, source.safety, hint0⟩)
    {stS : State .source} {stA : State .anon} (hst : StreamRename.StateRen f P stS stA)
    (ownersGood : ∀ k : Key .source, k.Good P → ∀ o, stS.projOwners[k]? = some o → o.Good P)
    (typeGood : (quotientMember ρ m0 h).cv.type.Good P) (valueGood : (quotientMember ρ m0 h).value.Good P)
    {heightsS : CName .source → Nat} {heightsA : CName .anon → Nat} {declS : CDecl .source} {rwS : Bool}
    (lowS : lowerDefinition (some h) stS heightsS (quotientMember ρ m0 h).cv (quotientMember ρ m0 h).value
      (quotientMember ρ m0 h).kind (quotientMember ρ m0 h).safety = .ok (declS, rwS)) :
    lowerDefinition (some h) stA heightsA
      ⟨(Ix.LeanIngress.Key.subst ρ (ingressKey source.name)).map f, List.range source.levelParams.size, tA⟩ vA
      source.kind source.safety = .ok (declS.mapKeys f, rwS) := by
  obtain ⟨convT, hconvT, htypeEq⟩ := RecordReadings.related_renamed (RecordReadings.pos_inj nodup)
    (RecordReadings.pos_aligned nodup) typeRel
  obtain ⟨convV, hconvV, hvalueEq⟩ := RecordReadings.related_renamed (RecordReadings.pos_inj nodup)
    (RecordReadings.pos_aligned nodup) valueRel
  rw [ht', Except.ok.injEq] at hconvT
  rw [hv', Except.ok.injEq] at hconvV
  subst hconvT hconvV
  have hqm : quotientMember ρ m0 h =
      ⟨⟨Ix.LeanIngress.Key.subst ρ (ingressKey source.name), List.range source.levelParams.size,
        mapLevels (canonLevelIn (List.range source.levelParams.size)) (Ix.LeanIngress.Expr.substKeys ρ t')⟩,
        mapLevels (canonLevelIn (List.range source.levelParams.size)) (Ix.LeanIngress.Expr.substKeys ρ v'),
        source.kind, source.safety, h⟩ := by
    rw [quotientMember, RecordReadings.defMember_canon, hm0]
    simp only [Ix.LeanIngress.DefMember.substKeys, Ix.LeanIngress.ConstantVal.substKeys,
      RecordReadings.params_nodup nodup]
  rw [RecordReadings.params_map_pos, RecordReadings.params_nodup nodup] at htypeEq hvalueEq
  have agree : CtxAgree.ProjectionAgree f P stS stA := ⟨hst.owners, ownersGood, hst.levels⟩
  have lowR := CtxAgree.lowerDefinition_mapKeys hP hf agree (heights := fun _ => 0) (heights' := fun _ => 0)
    (fun _ _ => rfl) typeGood valueGood (some h) (quotientMember ρ m0 h).kind (quotientMember ρ m0 h).safety
  rw [lowerDefinition_heights h stS (fun _ => 0) heightsS, lowS] at lowR
  rw [lowerDefinition_heights h stA heightsA (fun _ => 0), htypeEq, hvalueEq]
  rw [hqm] at lowR
  exact lowR

/-! ## The block's own context -/

section Ctx

variable {defs : List Ix.Def}

theorem flatten_singletons {α : Type} : ∀ l : List α, (l.map ([·])).flatten = l
  | [] => rfl
  | a :: l => by simp [flatten_singletons l]

theorem defs_distinct (distinct : Ix.CompileCert.Canon.KeysDistinct (defs.map MutConst.defn)) :
    Ix.CompileCert.Canon.KeysDistinct ((defs.map MutConst.defn).map ([·])).flatten := by
  rw [flatten_singletons]
  exact distinct

theorem ctx_defs_val (distinct : Ix.CompileCert.Canon.KeysDistinct (defs.map MutConst.defn)) {n : Ix.Name}
    {j : Nat} (h : (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[n]? = some j) :
    ∃ hj : j < defs.length, defs[j].name = n := by
  obtain ⟨j', C, m, hC, hm, hcase⟩ := Ix.CompileCert.Canon.ctx_val (defs_distinct distinct) h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hC
  obtain ⟨m0, ⟨d, hd, rfl⟩, rfl⟩ := hC
  rw [List.mem_singleton] at hm
  subst hm
  have hj : j' < defs.length := (List.getElem?_eq_some_iff.mp hd).1
  have hdj : defs[j'] = d := (List.getElem?_eq_some_iff.mp hd).2
  rcases hcase with ⟨hname, rfl⟩ | ⟨k, c, hc, -, -⟩
  · exact ⟨hj, by rw [hdj]; exact hname⟩
  · simp [MutConst.ctors] at hc

theorem ctx_defs_member (distinct : Ix.CompileCert.Canon.KeysDistinct (defs.map MutConst.defn)) {j : Nat}
    (hj : j < defs.length) :
    (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[defs[j].name]? = some j :=
  Ix.CompileCert.Canon.ctx_member (defs_distinct distinct) (C := [MutConst.defn defs[j]])
    (m := MutConst.defn defs[j]) (by simp [hj]) (List.mem_singleton_self _)

end Ctx


/-! ## The block -/

section Block

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.DefinitionDeps (ConstOcc)

/-- The names a block's terms are read at to see its `recur` references: a member as a fresh
key, any other name as the compile environment's binding of it reads. -/
def taggedNames (defs : List Ix.Def) (env : CompileEnv) (bindings : Bindings) (cx : Ctx .anon)
    (n : Ix.Name) (k : CName .anon) : Prop :=
  match (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[n]? with
  | some j => k = DefinitionOrder.freshKey cx j
  | none => ∃ a, lookupBinding env bindings n = some a ∧ cx.keyAt a = .ok k

variable {defs : List Ix.Def} {env : CompileEnv} {bindings : Bindings} {cx : Ctx .anon}

theorem taggedNames_func : ∀ n k k', taggedNames defs env bindings cx n k →
    taggedNames defs env bindings cx n k' → k = k' := by
  intro n k k' h h'
  cases hc : (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[n]? with
  | some j =>
    simp only [taggedNames, hc] at h h'
    rw [h, h']
  | none =>
    simp only [taggedNames, hc] at h h'
    obtain ⟨a, ha, hk⟩ := h
    obtain ⟨a', ha', hk'⟩ := h'
    rw [ha] at ha'
    cases ha'
    rw [hk] at hk'
    cases hk'
    rfl

theorem taggedNames_iff (distinct : Canon.KeysDistinct (defs.map MutConst.defn)) {j : Nat}
    (hj : j < defs.length) (n : Ix.Name) :
    taggedNames defs env bindings cx n (DefinitionOrder.freshKey cx j) ↔ n = defs[j].name := by
  constructor
  · intro h
    cases hc : (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[n]? with
    | some j' =>
      simp only [taggedNames, hc] at h
      have := DefinitionOrder.freshKey_inj cx _ _ h
      subst this
      exact (ctx_defs_val distinct hc).2.symm
    | none =>
      simp only [taggedNames, hc] at h
      obtain ⟨a, -, hk⟩ := h
      exact absurd rfl (DefinitionOrder.freshKey_fresh cx a _ hk j)
  · rintro rfl
    simp only [taggedNames, ctx_defs_member distinct hj]

/-- Quotient Source's group at the block's hints. -/
theorem quotient_defs {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint} {H : Nat → ReducibilityHint}
    {ms : Array Ix.LeanIngress.DefMember} {order : Array Nat}
    (hinted : ∀ k ∈ order, hints ms[k]!.cv.name = some (H k)) :
    ((Ix.LeanIngress.Converted.definitions (order.map (ms[·]!))).withHints hints).quotient ρ =
      .definitions (order.map fun k => quotientMember ρ ms[k]! (H k)) := by
  simp only [Ix.LeanIngress.Converted.withHints, Ix.LeanIngress.Converted.quotient,
    Ix.LeanIngress.Converted.substKeys, Ix.LeanIngress.Converted.canon, Array.map_map]
  congr 1
  apply Array.map_congr_left
  intro k hk
  simp only [Function.comp_apply, hinted k hk, quotientMember]

end Block


/-- A result's declaration, or `dflt` on an error. -/
def decOf {D ε : Type} (dflt : D) : Except ε (D × Bool) → D
  | .ok p => p.1
  | .error _ => dflt

theorem forall₂_ok_map {α D ε : Type} (G : α → Except ε (D × Bool)) (dflt : D) :
    ∀ (l : List α) (ds : List D), List.Forall₂ (fun a d => ∃ rw, G a = .ok (d, rw)) l ds →
      ds = l.map (fun a => decOf dflt (G a)) ∧ ∀ a ∈ l, ∃ rw, G a = .ok (decOf dflt (G a), rw)
  | [], [], _ => ⟨rfl, fun _ h => by cases h⟩
  | a :: l, d :: ds, .cons ⟨rw, hg⟩ rest => by
    obtain ⟨hds, hok⟩ := forall₂_ok_map G dflt l ds rest
    refine ⟨by rw [hds, List.map_cons, hg]; rfl, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨rw, by rw [hg]; rfl⟩
    · exact hok b hb

theorem map_defn_inj : ∀ {ts ts' : List Ixon.Definition},
    ts.map Ixon.MutConst.defn = ts'.map Ixon.MutConst.defn → ts = ts'
  | [], [], _ => rfl
  | t :: ts, t' :: ts', h => by
    simp only [List.map_cons, List.cons.injEq, Ixon.MutConst.defn.injEq] at h
    rw [h.1, map_defn_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem quotientMember_hint (ρ : FiberMap) (m : Ix.LeanIngress.DefMember) (h : ReducibilityHint) :
    (quotientMember ρ m h).hint = h := by
  rw [quotientMember, RecordReadings.defMember_canon]
  rfl

/-! ## Premises the closure discharges

Two of `definition_block_reads`'s premises follow from facts the closure has: a block's members
are a set of names (`keysDistinct_of_pairwise`), and quotient Source's checker accepts a
declaration only at distinct level parameters (`nodup_of_params`). -/

theorem levelParam_nodup_iff : ∀ l : List LevelParam, LevelParam.nodup l = true ↔ l.Nodup
  | [] => by simp [LevelParam.nodup]
  | n :: ns => by
    simp [LevelParam.nodup, List.nodup_cons, levelParam_nodup_iff ns]

/-- **Distinct level-parameter positions are distinct names**: the checker requires a
declaration's positions distinct (`LevelParam.nodup`), and equal names have one position. -/
theorem nodup_of_params {lps : Array Ix.Name}
    (h : LevelParam.nodup (Numbering.mk lps false).params = true) : lps.toList.Nodup := by
  rw [levelParam_nodup_iff] at h
  simp only [Ix.LeanIngress.Numbering.params] at h
  exact List.Pairwise.of_map _ (fun a b hab e => hab (by rw [e])) h

/-- **A block's members, from a set of names, are distinct**: names a hash set holds compare
unequal (`Std.HashSet.distinct_toList`), so they differ. -/
theorem keysDistinct_of_pairwise {defs : List Ix.Def}
    (h : (defs.map (·.name)).Pairwise (fun a b => (a == b) = false)) :
    Ix.CompileCert.Canon.KeysDistinct (defs.map MutConst.defn) := by
  have hk : (defs.map MutConst.defn).flatMap Ix.CompileCert.Canon.keysOf = defs.map (·.name) := by
    clear h
    induction defs with
    | nil => rfl
    | cons d ds ih => simp [Ix.CompileCert.Canon.keysOf, MutConst.name, MutConst.ctors, ih]
  unfold Ix.CompileCert.Canon.KeysDistinct
  rw [hk]
  refine h.imp fun {a b} hab e => ?_
  subst e
  have : (a == a) = true := Address.beq_iff_eq.mpr rfl
  rw [this] at hab
  cases hab

/-- **A declaration's level positions are distinct**, where it has them as a definition, theorem
or opaque: what the checker requires before it installs one. -/
def DeclNodup {md : Mode} : CDecl md → Prop
  | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ => LevelParam.nodup cv.levelParams = true
  | _ => True

theorem lowerDefinition_nodup {md : Mode} {st : State md} {heights : CName md → Nat} {cv : CVal md}
    {value : CExpr md} {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {h : ReducibilityHint}
    {decl : CDecl md} {rw : Bool}
    (hl : lowerDefinition (some h) st heights cv value kind safety = .ok (decl, rw)) (hd : DeclNodup decl) :
    LevelParam.nodup cv.levelParams = true := by
  unfold lowerDefinition at hl
  cases hs : safetyDeclineOf kind safety with
  | some why => simp [hs, declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hl
  | none =>
    cases kind <;> simp [hs, pure, Except.pure] at hl <;> (obtain ⟨rfl, -⟩ := hl; exact hd)

theorem quotientMember_levelParams (ρ : FiberMap) (m : Ix.LeanIngress.DefMember) (h : ReducibilityHint) :
    (quotientMember ρ m h).cv.levelParams = m.cv.levelParams := by
  rw [quotientMember, RecordReadings.defMember_canon]
  rfl

section Main

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.DefinitionDeps (ConstOcc)

/-- **A compiled definition block reads, in a closure's context and from any state related to
quotient Source's, as quotient Source's group renamed.**

The block is compiled in its members' order (`defs`, the compiler's views of `members`), one
member per class, from a clean state in which no member is bound in the resolution map
(`unresolved`), the block's own or the environment's. The
compile run's reading context `cx₁` reads the environment's names as quotient Source's renamed,
and the closure's context `cx` reads the record's references as `cx₁` does, the members' keys as
quotient Source's renamed and their hints as quotient Source's hints. The members' names are
distinct, quotient Source's declarations of the group have distinct level positions, and a name
a member's terms mention with a member's ingress key is that member. -/
theorem definition_block_reads {ρ : FiberMap} {f : Mode.Id .source → Mode.Id .anon}
    {P : KeyScope .source} (hP : P.Pre) (hf : InjOn f P)
    {members : Array Ix.ConstantInfo} (two : 2 ≤ members.size) {defs : List Ix.Def}
    (views : List.Forall₂ (fun ci d => EmissionDispatch.sourceData ci = some d) members.toList defs)
    (distinct : Canon.KeysDistinct (defs.map MutConst.defn))
    (exactNames : ∀ i (hi : i < defs.length) j (hj : j < defs.length) n,
      ConstOcc n defs[i].type ∨ ConstOcc n defs[i].value →
        ingressKey n = ingressKey defs[j].name → n = defs[j].name)
    (context : CompileEnv × BlockEnv)
    {bindings : Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before)
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before =
      (.ok output, after))
    (unresolved : ∀ d ∈ defs, bindings.get? d.name = none ∧ context.1.nameToAddr.get? d.name = none)
    {cx₁ cx : Ctx .anon} (aligned : ∀ a, cx₁.blob a = context.1.blobs.get? a)
    {names : Ix.Name → CName .anon → Prop} (external : BindingsCorrect context.1 bindings cx₁ names)
    (self : ∀ k (hk : k < defs.length), names defs[k].name ((Ix.LeanIngress.Key.subst ρ (ingressKey defs[k].name)).map f))
    (agree : ∀ k (hk : k < defs.length), ∀ n key, (GraphWalk.Refs n defs[k].type ∨ GraphWalk.Refs n defs[k].value) →
      names n key → sourceNames ρ f n key)
    (refs : RecordTransfer.RefsLe output.block (ExpressionRead.withBlockBlobs cx₁ after) cx)
    {owner : Address}
    (keys : ∀ k (hk : k < defs.length),
      cx.memberKey (.member owner k) = .ok ((Ix.LeanIngress.Key.subst ρ (ingressKey defs[k].name)).map f))
    {hints : CName .source → Option ReducibilityHint} {H : Nat → ReducibilityHint}
    (hinted : ∀ k (hk : k < defs.length),
      cx.hint (.member owner k) = some (H k) ∧ hints (ingressKey defs[k].name) = some (H k))
    {c : Ix.LeanIngress.Converted} (conv : Ix.LeanIngress.convertDefinitions members = .ok c)
    {stS : State .source}
    (ownersGood : ∀ k : Key .source, k.Good P → ∀ o, stS.projOwners[k]? = some o → o.Good P)
    (good : ∀ qms, (c.withHints hints).quotient ρ = .definitions qms →
      ∀ m ∈ qms.toList, m.cv.type.Good P ∧ m.value.Good P)
    {rS : Read .source} (lowered : Ix.LeanIngress.lower stS ((c.withHints hints).quotient ρ) = .ok rS)
    (levels : ∀ d ∈ rS.decls, DeclNodup d) :
    ∀ stA : State .anon, StreamRename.StateRen f P stS stA →
      ∃ rA, readRecord cx stA owner output.block = .ok rA ∧ StreamRename.Plain rA ∧
        rA.decls = rS.decls.map (Declaration.mapKeys f) := by
  intro stA hst
  have hlen : members.size = defs.length := by
    simpa using DefinitionBlocks.forall₂_length views
  -- what the compiler's view says of each member
  have facts : ∀ k (hk : k < defs.length),
      (members[k]'(by omega)).getCnst.name = defs[k].name ∧
        (members[k]'(by omega)).getCnst.levelParams = defs[k].levelParams ∧
        (members[k]'(by omega)).getCnst.type = defs[k].type ∧
        Ix.LeanIngress.definitionValue (members[k]'(by omega)) = some defs[k].value ∧
        ∃ hint, Ix.LeanIngress.definitionShape (members[k]'(by omega)) = some (defs[k].kind, defs[k].safety, hint) := by
    intro k hk
    have := DefinitionBlocks.forall₂_getElem views k (by simp; omega) hk
    simp only [Array.getElem_toList] at this
    exact RecordReadings.sourceData_facts this
  -- quotient Source's conversion
  obtain ⟨ms, order, hmsize, hms, hdef, rfl⟩ := convertDefinitions_block conv two
  have src : ∀ k (hk : k < defs.length), ∃ t' v' hint0,
      ingressExpr (Numbering.mk defs[k].levelParams false).pos defs[k].type = .ok t' ∧
      ingressExpr (Numbering.mk defs[k].levelParams false).pos defs[k].value = .ok v' ∧
      safetyDeclineOf defs[k].kind defs[k].safety = none ∧
      ms[k]! = ⟨⟨ingressKey defs[k].name, (Numbering.mk defs[k].levelParams false).params, t'⟩, v',
        defs[k].kind, defs[k].safety, hint0⟩ := by
    intro k hk
    obtain ⟨hname, hlps, htype, hvalue, hint0, hshape⟩ := facts k hk
    obtain ⟨s, v, t', v', hs, hv, ht', hv', hsafe, hmk⟩ := hms k (by omega)
    rw [hshape, Option.some.injEq] at hs
    rw [hvalue, Option.some.injEq] at hv
    subst hs hv
    rw [hlps, htype] at ht'
    rw [hlps] at hv'
    rw [hname, hlps] at hmk
    refine ⟨t', v', hint0, ht', hv', hsafe, ?_⟩
    rw [getElem!_pos ms k (by omega)]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans hmk)
  -- the compiled block, read in the closure's names
  have scopesA : ∀ m ∈ defs.map MutConst.defn, ∀ e ∈ BlockEmission.memberSources m,
      ConstsSatisfy (SelfName (BlockEmission.mutContext ((defs.map MutConst.defn).map ([·])) context).2
        (blockSelf cx owner defs.length) names) e := by
    intro _ _ e _
    refine constsSatisfy_of_forall (fun n index found => ?_) e
    change (MutConst.ctx ((defs.map MutConst.defn).map ([·]))).get? n = some index at found
    rw [Std.TreeMap.get?_eq_getElem?] at found
    obtain ⟨hj, hname⟩ := ctx_defs_val distinct found
    refine ⟨(Ix.LeanIngress.Key.subst ρ (ingressKey defs[index].name)).map f,
      by simp only [blockSelf, hj, ↓reduceIte, keys index hj], ?_⟩
    rw [← hname]
    exact self index hj
  obtain ⟨ts, hinfo, each⟩ := DefinitionEmission.defsBlock_each cx₁ id (blockSelf cx owner defs.length)
    names bindings (fun m => (Numbering.mk m.levelParams false).pos) context aligned external
    defs (by omega) scopesA clean ran
  have hlenT : ts.length = defs.length := (DefinitionBlocks.forall₂_length each).symm
  -- the compiled block, read with each member as a fresh key
  have externalT : BindingsCorrect context.1 bindings cx₁ (taggedNames defs context.1 bindings cx₁) := by
    intro n a hb
    have hnone : (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[n]? = none := by
      cases hc : (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[n]? with
      | none => rfl
      | some j =>
        exfalso
        obtain ⟨hj, hname⟩ := ctx_defs_val distinct hc
        have hd := List.getElem_mem hj
        rw [← hname] at hb
        simp only [lookupBinding, (unresolved _ hd).1, (unresolved _ hd).2, Option.orElse] at hb
        cases hb
    obtain ⟨key, hk, -⟩ := external n a hb
    exact ⟨key, hk, by simp only [taggedNames, hnone]; exact ⟨a, hb, hk⟩⟩
  have scopesT : ∀ m ∈ defs.map MutConst.defn, ∀ e ∈ BlockEmission.memberSources m,
      ConstsSatisfy (SelfName (BlockEmission.mutContext ((defs.map MutConst.defn).map ([·])) context).2
        (DefinitionOrder.tagSelf defs.length (DefinitionOrder.freshKey cx₁))
        (taggedNames defs context.1 bindings cx₁)) e := by
    intro _ _ e _
    refine constsSatisfy_of_forall (fun n index found => ?_) e
    change (MutConst.ctx ((defs.map MutConst.defn).map ([·]))).get? n = some index at found
    rw [Std.TreeMap.get?_eq_getElem?] at found
    obtain ⟨hj, -⟩ := ctx_defs_val distinct found
    exact ⟨_, by simp only [DefinitionOrder.tagSelf, hj, ↓reduceIte]; rfl,
      by simp only [taggedNames, found]⟩
  obtain ⟨ts', hinfo', eachT⟩ := DefinitionEmission.defsBlock_each cx₁ id
    (DefinitionOrder.tagSelf defs.length (DefinitionOrder.freshKey cx₁)) (taggedNames defs context.1 bindings cx₁)
    bindings (fun m => (Numbering.mk m.levelParams false).pos) context aligned externalT defs (by omega)
    scopesT clean ran
  have hts : ts' = ts := by
    rw [hinfo] at hinfo'
    simp only [Ixon.ConstantInfo.muts.injEq] at hinfo'
    exact map_defn_inj (by simpa using (congrArg Array.toList hinfo').symm)
  subst hts
  -- the members each member names by `recur`, and those its Lean terms mention
  have readerDeps : ∀ i (hi : i < defs.length) j (hj : j < defs.length),
      j ∈ recurDeps output.block (ts'[i]'(by omega)) ↔
        ConstOcc defs[j].name defs[i].type ∨ ConstOcc defs[j].name defs[i].value := by
    intro i hi j hj
    obtain ⟨-, -, ⟨tT, hTread, hTrel⟩, ⟨tV, hVread, hVrel⟩⟩ :=
      DefinitionBlocks.forall₂_getElem eachT i hi (by omega)
    rw [DefinitionOrder.recurDeps_read (cx := ExpressionRead.withBlockBlobs cx₁ after) (DefinitionOrder.freshKey_inj cx₁)
      (fun a k h j => DefinitionOrder.freshKey_fresh cx₁ a k h j) hTread hVread j,
      DefinitionDeps.related_occurs taggedNames_func hTrel, DefinitionDeps.related_occurs taggedNames_func hVrel]
    simp only [taggedNames_iff distinct hj, exists_eq_right]
  have sourceDeps : ∀ i (hi : i < defs.length) j (hj : j < defs.length),
      j ∈ (DefinitionBlocks.depsOf ms)[i]! ↔
        ConstOcc defs[j].name defs[i].type ∨ ConstOcc defs[j].name defs[i].value := by
    intro i hi j hj
    rw [DefinitionDeps.depsOf_mem ms (by omega) j]
    obtain ⟨ti, vi, h0i, hti, hvi, _, hmi⟩ := src i hi
    obtain ⟨tj, vj, h0j, _, _, _, hmj⟩ := src j hj
    rw [getElem!_pos ms i (by omega)] at hmi
    rw [getElem!_pos ms j (by omega)] at hmj
    simp only [hmi, hmj, Bool.or_eq_true]
    rw [DefinitionDeps.ingress_occurs _ _ _ hti, DefinitionDeps.ingress_occurs _ _ _ hvi]
    constructor
    · rintro ⟨-, ⟨n, hn, he⟩ | ⟨n, hn, he⟩⟩
      · exact .inl (exactNames i hi j hj n (.inl hn) he ▸ hn)
      · exact .inr (exactNames i hi j hj n (.inr hn) he ▸ hn)
    · rintro (h | h)
      · exact ⟨by omega, .inl ⟨_, h, rfl⟩⟩
      · exact ⟨by omega, .inr ⟨_, h, rfl⟩⟩
  -- so the reader's order is quotient Source's
  have hord : defOrder (ts'.toArray.map (recurDeps output.block)) = some order := by
    rw [← hdef]
    apply DefinitionOrder.defOrder_congr (by simp [hlenT, DefinitionBlocks.depsOf]; omega)
    intro i hi j hj hji
    simp only [Array.size_map, List.size_toArray] at hi hj
    rw [getElem!_pos _ i (by simp; omega), Array.getElem_map, List.getElem_toArray,
      readerDeps i (by omega) j (by omega), sourceDeps i (by omega) j (by omega)]
  have hlt : ∀ i ∈ order.toList, i < defs.length := by
    intro i hi
    have := DefinitionOrder.defOrder_lt _ _ hdef i (Array.mem_toList_iff.mp hi)
    simp only [DefinitionBlocks.depsOf, Array.size_map] at this
    omega
  -- quotient Source's lowering
  have hq := quotient_defs (ρ := ρ) (hints := hints) (H := H) (ms := ms) (order := order) (fun k hk => by
    have hk' := hlt k (Array.mem_toList_iff.mpr hk)
    obtain ⟨_, _, _, _, _, _, hm⟩ := src k hk'
    rw [hm]
    exact (hinted k hk').2)
  rw [hq] at lowered good
  obtain ⟨ds, hds, -, hdsF⟩ := lower_defs lowered
  rw [Array.toList_map] at hdsF
  let G : Ix.LeanIngress.DefMember → ReadM (CDecl .source × Bool) := fun m =>
    lowerDefinition (some m.hint) stS (stS.heights.getD · 0) m.cv m.value m.kind m.safety
  obtain ⟨hdsEq, sourceOk⟩ := forall₂_ok_map G (.axiomDecl ⟨.role default, [], .sort .zero⟩) _ ds hdsF
  -- the reader on the block
  have safeT : ∀ t ∈ ts', safetyDecline t = none := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨hpay, -⟩ := DefinitionBlocks.forall₂_getElem each k (by omega) hk
    obtain ⟨_, _, _, _, _, hsafe, _⟩ := src k (by omega)
    rw [safetyDecline, hpay]
    exact hsafe
  obtain ⟨rA, hread, hplain, hdecls⟩ := readRecord_defs (cx := cx) (st := stA) (owner := owner) hinfo
    (by intro h; simp [h] at hlenT; omega) safeT
    hord (fun i => (decOf (.axiomDecl ⟨.role default, [], .sort .zero⟩)
      (G (quotientMember ρ ms[i]! (H i)))).mapKeys f) hlenT (by
    intro i hio heights
    have hi := hlt i hio
    obtain ⟨hpay, hlv, ⟨tA, hTread, hTrel⟩, ⟨vA, hVread, hVrel⟩⟩ :=
      DefinitionBlocks.forall₂_getElem each i hi (by omega)
    obtain ⟨t', v', h0, ht', hv', -, hm⟩ := src i hi
    obtain ⟨rwS, lowS⟩ := sourceOk _ (List.mem_map.mpr ⟨i, hio, rfl⟩)
    have hT := RecordTransfer.read_le refs id _ _ hTread
    have hV := RecordTransfer.read_le refs id _ _ hVread
    have hkind : ts'[i].kind = defs[i].kind := by rw [hpay]; rfl
    have hsafety : ts'[i].safety = defs[i].safety := by rw [hpay]; rfl
    have hgood := good _ rfl (quotientMember ρ ms[i]! (H i)) (by
      rw [Array.toList_map]
      exact List.mem_map.mpr ⟨i, hio, rfl⟩)
    refine ⟨rwS, ?_⟩
    rw [getElem!_pos ts'.toArray i (by simp; omega), List.getElem_toArray]
    simp only [readDefinition, keys i hi, hT, hV, (hinted i hi).1, bind, Except.bind]
    rw [hkind, hsafety, hlv]
    have lowS' : lowerDefinition (some (H i)) stS (stS.heights.getD · 0) (quotientMember ρ ms[i]! (H i)).cv
        (quotientMember ρ ms[i]! (H i)).value (quotientMember ρ ms[i]! (H i)).kind
        (quotientMember ρ ms[i]! (H i)).safety =
          .ok (decOf (.axiomDecl ⟨.role default, [], .sort .zero⟩) (G (quotientMember ρ ms[i]! (H i))), rwS) := by
      have := lowS
      simp only [G, quotientMember_hint] at this ⊢
      exact this
    -- the member's level parameters are distinct: its Source declaration is accepted
    have nodup : defs[i].levelParams.toList.Nodup := by
      have hmem : decOf (.axiomDecl ⟨.role default, [], .sort .zero⟩) (G (quotientMember ρ ms[i]! (H i))) ∈
          rS.decls := by
        rw [hds, hdsEq, List.mem_toArray]
        exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨i, hio, rfl⟩, rfl⟩
      have hlp := lowerDefinition_nodup lowS' (levels _ hmem)
      rw [quotientMember_levelParams, hm] at hlp
      exact nodup_of_params hlp
    exact member_lower hP hf nodup (RecordReadings.related_mono hTrel fun n k r hn => agree i hi n k (.inl r) hn)
      (RecordReadings.related_mono hVrel fun n k r hn => agree i hi n k (.inr r) hn) ht' hv' hm hst ownersGood hgood.1
      hgood.2 lowS')
  refine ⟨rA, hread, hplain, ?_⟩
  rw [hdecls, hds, hdsEq, List.map_map]
  simp [List.map_toArray]

end Main

/--
info: 'Ix.Cert.DefinitionBlockReads.definition_block_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms definition_block_reads


end Ix.Cert.DefinitionBlockReads
