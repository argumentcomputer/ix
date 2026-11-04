import Ix.Cert.CtxAgreeOwners

/-! # Projection-field writes and their ordered entries

Every owner constructed from a good BlockRead has good keys and recursor
type. Projection-iota recognition and the recorded level commute with key
renaming without injectivity or scope premises. The exact noteGenerated,
commit and stream-fold formulas expose projection owners and levels in
their update order, including arbitrary generated-prefix lengths.

UnitAgree plus owner-list agreement transports the two entry lists of
already-paired reads. These local facts do not establish the actual Source
and Ixon stream correspondence or ProjectionAgree. Raw/kept retained-index
classification and the level consistency of dropped generated declarations
remain separate obligations. Counter equality is not asserted, and no final
compiler-correctness premise is added.
-/

namespace Ix.Cert.CtxAgree

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Frontend

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}

theorem ownersOf_good {rb : BlockRead md} (good : rb.Good P) :
    ∀ o ∈ ownersOf rb, o.Good P := by
  intro o member
  unfold ownersOf projRecOwners at member
  dsimp only at member
  split at member
  · simp at member
  · split at member
    · simp at member
    · obtain ⟨⟨ty, i⟩, hty, returned⟩ := List.mem_filterMap.mp member
      have source := List.fst_mem_of_mem_zipIdx hty
      obtain ⟨⟨⟨cv, nP, nI⟩, cs⟩, hs, equal⟩ := List.mem_map.mp source
      dsimp only at equal
      subst ty
      have hcv := good.1 _ (List.of_mem_zip hs).1
      have hcs := good.2.2.1 cs (List.of_mem_zip hs).2
      dsimp only at returned
      cases cs with
      | nil => cases returned
      | cons C rest =>
        cases rest with
        | cons => cases returned
        | nil =>
          obtain ⟨_, _, returned⟩ := Option.bind_eq_some_iff.mp returned
          obtain ⟨⟨bs, body⟩, _, returned⟩ := Option.bind_eq_some_iff.mp returned
          cases body <;> try cases returned
          case sort level =>
            obtain ⟨_, _, returned⟩ := Option.bind_eq_some_iff.mp returned
            obtain ⟨_, _, returned⟩ := Option.bind_eq_some_iff.mp returned
            obtain ⟨row, hr, returned⟩ := Option.bind_eq_some_iff.mp returned
            obtain ⟨_, _, returned⟩ := Option.bind_eq_some_iff.mp returned
            have mappedMem := List.mem_of_getElem? hr
            obtain ⟨⟨rcv, counts, rules⟩, recMem, rfl⟩ := List.mem_map.mp mappedMem
            cases returned
            exact ⟨hcv.1, hcs C (List.mem_singleton_self _),
              (good.2.2.2 _ recMem).1.1, (good.2.2.2 _ recMem).1.2⟩

theorem lowerInductive_owners_good {rb : BlockRead md} (good : rb.Good P)
    {st : State md} {r : Read md} (lowered : lowerInductive st rb = .ok r) :
    ∀ o ∈ r.owners, o.Good P := by
  rw [lowerInductive_owners lowered]
  exact ownersOf_good good

theorem isProjIota_mapKeys (k : Key md) : (k.map f).isProjIota = k.isProjIota := by
  cases k <;> try rfl
  case aux base shape => cases shape <;> rfl

theorem projIotaLevel_mapKeys (ty : CExpr md) : projIotaLevel (ty.mapKeys f) = projIotaLevel ty := by
  unfold projIotaLevel
  rw [← Expr.mapKeys_piResult, ← Expr.mapKeys_getAppFn]
  generalize ty.piResult.getAppFn = head
  cases head <;> try rfl
  case const key levels =>
    cases levels with
    | nil => rfl
    | cons level rest =>
      cases rest with
      | cons => rfl
      | nil =>
        cases key <;> try rfl
        case role role => cases role <;> rfl

/-- Exactly the level entry learned from a generated declaration. -/
def projLevelEntry : CDecl md → Option (CName md × Ix.Kernel.Level)
  | .thmDecl cv _ =>
    if cv.name.isProjIota then (projIotaLevel cv.type).map (cv.name, ·) else none
  | _ => none

theorem projLevelEntry_mapKeys (d : CDecl md) :
    projLevelEntry (d.mapKeys f) = (projLevelEntry d).map fun (k, level) => (k.map f, level) := by
  cases d <;> try rfl
  case thmDecl cv value =>
    simp only [Declaration.mapKeys, projLevelEntry, ConstantVal.mapKeys,
      isProjIota_mapKeys, projIotaLevel_mapKeys]
    split
    · cases projIotaLevel cv.type <;> rfl
    · rfl

theorem note_projOwners (st : State md) (d : CDecl md) : (st.note d).projOwners = st.projOwners := by
  cases d <;> (refine foldl_keep State.projOwners _ (fun s e => ?_) _ _; rfl)

theorem note_projLevels (st : State md) (d : CDecl md) : (st.note d).projLevels = st.projLevels := by
  cases d <;> (refine foldl_keep State.projLevels _ (fun s e => ?_) _ _; rfl)

theorem noteGenerated_projOwners (st : State md) (d : CDecl md) :
    (st.noteGenerated d).projOwners = st.projOwners := by
  unfold State.noteGenerated
  split <;> (try split) <;> (try split) <;> simp only [note_projOwners]

theorem noteGenerated_projLevels (st : State md) (d : CDecl md) :
    (st.noteGenerated d).projLevels = insOpt projLevelEntry st.projLevels d := by
  cases d <;> simp only [State.noteGenerated, projLevelEntry, insOpt, note_projLevels]
  case thmDecl cv value =>
    split
    · cases projIotaLevel cv.type <;> rfl
    · rfl

theorem foldl_zipIdx_take {α σ : Type} (g : σ → α → σ) :
    ∀ (xs : List α) (k n : Nat) (s : σ),
      (xs.zipIdx k).foldl (fun s x => if x.2 < n then g s x.1 else s) s =
        (xs.take (n - k)).foldl g s := by
  intro xs
  induction xs with
  | nil => intros; simp only [List.zipIdx_nil, List.take_nil, List.foldl_nil]
  | cons x xs ih =>
    intro k n s
    rw [List.zipIdx_cons, List.foldl_cons]
    by_cases before : k < n
    · have count : n - k = (n - (k + 1)) + 1 := by omega
      simp only [before, ite_true, count, List.take_succ_cons, List.foldl_cons]
      exact ih (k + 1) n _
    · have zero : n - k = 0 := by omega
      have zero' : n - (k + 1) = 0 := by omega
      simp only [before, ite_false, ih, zero, zero', List.take_zero, List.foldl_nil]

theorem foldl_filterMap_insOpt {α β γ : Type} [BEq α] [Hashable α]
    (g : γ → Option (α × β)) : ∀ (xs : List γ) (m : Std.HashMap α β),
      (xs.filterMap g).foldl (insOpt some) m = xs.foldl (insOpt g) m := by
  intro xs
  induction xs with
  | nil => intros; rfl
  | cons x xs ih =>
    intro m
    cases hg : g x <;> simp only [List.filterMap_cons, hg, List.foldl_cons, insOpt, ih]

/-- Projection-field entries in their exact update order. -/
def ownerEntries (r : Read md) : List (CName md × ProjRecOwner md) := r.owners.map fun o => (o.T, o)
def levelEntries (r : Read md) : List (CName md × Ix.Kernel.Level) :=
  (r.decls.toList.take r.generated).filterMap projLevelEntry

theorem commit_projOwners (st : State md) (r : Read md) :
    (st.commit r).projOwners = (ownerEntries r).foldl (insOpt some) st.projOwners := by
  rw [commit_eq]
  simp only
  rw [commit_decls State.projOwners (fun m _ => m) r _ note_projOwners
    (fun s d => by rw [noteGenerated_projOwners, note_projOwners]), foldl_self]
  rw [foldl_keep State.projOwners (fun s (x : CName md × InModel.BlockRec md) =>
      { s with indBlocks := s.indBlocks.insert x.1 x.2 })
    (fun _ _ => rfl)]
  rw [ownerEntries, List.foldl_map]
  exact foldl_proj State.projOwners _ _ (fun _ _ => rfl) _ _

theorem commit_projLevels (st : State md) (r : Read md) :
    (st.commit r).projLevels = (levelEntries r).foldl (insOpt some) st.projLevels := by
  rw [levelEntries, foldl_filterMap_insOpt, commit_eq]
  simp only
  rw [foldl_proj State.projLevels _
    (fun m (x : CDecl md × Nat) => if x.2 < r.generated then insOpt projLevelEntry m x.1 else m)
    (fun s x => by split <;> simp only [noteGenerated_projLevels, note_projLevels])]
  rw [foldl_zipIdx_take, Nat.sub_zero,
    commit_pre_keep State.projLevels r st (fun _ _ => rfl) (fun _ _ => rfl)]

def ownersIn (rs : List (Read md)) : List (CName md × ProjRecOwner md) := rs.flatMap ownerEntries
def levelsIn (rs : List (Read md)) : List (CName md × Ix.Kernel.Level) := rs.flatMap levelEntries

theorem fold_projection_fields (st : State md) (rs : List (Read md)) :
    (rs.foldl State.commit st).projOwners = (ownersIn rs).foldl (insOpt some) st.projOwners ∧
    (rs.foldl State.commit st).projLevels = (levelsIn rs).foldl (insOpt some) st.projLevels := by
  constructor
  · rw [ownersIn, foldl_flatMap']
    exact foldl_proj State.projOwners _ _ (fun s r => commit_projOwners s r) rs st
  · rw [levelsIn, foldl_flatMap']
    exact foldl_proj State.projLevels _ _ (fun s r => commit_projLevels s r) rs st

/-- Owner-list agreement transports its ordered field entries. -/
theorem ownerEntries_mapKeys {rS : Read md} {rA : Read md'}
    (owners : rA.owners = rS.owners.map (ProjRecOwner.mapKeys f)) :
    ownerEntries rA = (ownerEntries rS).map fun (k, o) => (k.map f, o.mapKeys f) := by
  simp only [ownerEntries, owners, List.map_map]
  rfl

/-- Equal generated-prefix lengths transport level writes without a scope or
injectivity premise, including prefixes longer than the declaration array. -/
theorem UnitAgree.level_entries {rS : Read md} {rA : Read md'} (h : UnitAgree f rS rA) :
    levelEntries rA = (levelEntries rS).map fun (k, level) => (k.map f, level) := by
  simp only [levelEntries, h.1, h.2.1, Array.toList_map, ← List.map_take,
    List.filterMap_map, List.map_filterMap, Function.comp_def, projLevelEntry_mapKeys]

/-- The two projection-field entry lists agree for already-paired reads.
This does not supply a correspondence between actual stream prefixes. -/
theorem UnitAgree.projection_entries {rS : Read md} {rA : Read md'}
    (h : UnitAgree f rS rA) (owners : rA.owners = rS.owners.map (ProjRecOwner.mapKeys f)) :
    ownerEntries rA = (ownerEntries rS).map (fun (k, o) => (k.map f, o.mapKeys f)) ∧
      levelEntries rA = (levelEntries rS).map (fun (k, level) => (k.map f, level)) :=
  ⟨ownerEntries_mapKeys owners, h.level_entries⟩

end Ix.Cert.CtxAgree
