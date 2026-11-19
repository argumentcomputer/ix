import IxVMRefinement.TwinFamily.StoreAr
import IxVMRefinement.StatementRel.LoadedReadsCanonRec
import IxVMRefinement.StatementRel.ReadsMono
import IxVMRefinement.Assembly.TypingRecLateStored

/-! # The reload of a twin recursor

The twin's step stores, under the key of each constant address of the second record (a
recursor member of a block of recursors), the checked recursor. The fold's clause asks that it
reloads as itself (`Decl.ReloadsAs`): every load of the address in a run good for the store
represents it. The circuit's load of a recursor member's projection record represents the
member's canonical annotated constant (`LoadedReads.reloadsAs_rprj`, from its reading), so the
reload holds when the checked recursor is that constant up to the rules' install bits
(`reloadsAs_recr_rules`).

* `reads_rprj`: the inversion of `Reads` at a recursor projection record;
* `TwinMemberLoaded`: what the circuit side owes of one member, given its reading: the reading's
  level count, scope and K clause, and the checked type and rules the canonical annotation of the
  read ones (the circuit loads the member's annotated form, `Ingress::get_ci`);
* `TwinLoadFacts`: that at every member, and the second record's references stored;
* `twinMember_reloads`: the reload of each checked twin recursor, after the step, from these. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Core (KExpr)
open IxVM.Refinement.Decl (twinPosRulesJ)
open Ix.Kernel (ConstantInfo ConstantVal RecRule LevelParam)
open Ix.Kernel.Semantics (ConstantValCheckJ TwinRecPart)

set_option linter.unusedVariables false

/-! ## Lists -/

/-- A `List.Forall₂` over an indexed list, at the list. -/
theorem lforall₂_of_zipIdx {α β : Type} {R : α × Nat → β → Prop} {S : α → β → Prop}
    (H : ∀ p b, R p b → S p.1 b) :
    ∀ {l : List α} {n : Nat} {l' : List β}, List.Forall₂ R (l.zipIdx n) l' → List.Forall₂ S l l'
  | [], _, l', h => by
    have h' : List.Forall₂ R [] l' := h
    cases h'
    exact .nil
  | a :: l, n, l', h => by
    have h' : List.Forall₂ R ((a, n) :: l.zipIdx (n + 1)) l' := h
    cases h' with
    | cons hr ht => exact .cons (H _ _ hr) (lforall₂_of_zipIdx H ht)

/-- A `List.Forall₂` with a fact of every element of the right list. -/
theorem lforall₂_and_mem {α β : Type} {R : α → β → Prop} {Q : β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → (∀ b ∈ l', Q b) →
      List.Forall₂ (fun a b => R a b ∧ Q b) l l'
  | _, _, .nil, _ => .nil
  | _, _, .cons hr ht, hQ =>
    .cons ⟨hr, hQ _ (List.mem_cons.mpr (Or.inl rfl))⟩
      (lforall₂_and_mem ht fun b hb => hQ b (List.mem_cons.mpr (Or.inr hb)))

/-- A `List.Forall₂` under an implication. -/
theorem lforall₂_mono {α β : Type} {R S : α → β → Prop} (H : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons hr hs => .cons (H _ _ hr) (lforall₂_mono H hs)

/-! ## The reading of a recursor projection record -/

/-- **`Reads` at a recursor projection record**: the record names a recursor member of its
block, which declares the read constant. -/
theorem reads_rprj {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {x : _root_.Address}
    {c : Ixon.Constant} {p : Ixon.RecursorProj} {ci₀ : ConstantInfo .anon}
    (hrec : recordOf E₀ x = some c) (hinfo : c.info = .rPrj p) (h : Reads t E₀ x ci₀) :
    ∃ cb ms rc, MemberAt (recordOf E₀) x c p.block cb ms p.idx.toNat (.recr rc) ∧
      RecReads t (recordOf E₀) (fun y => E₀.blobs.get? y) cb (blockSelf t p.block ms)
        (keyOf t x) rc ci₀ := by
  unfold Reads ReadsIn at h
  obtain ⟨c', hc', hr⟩ := h
  have e : c' = c := Option.some.inj (hc'.symm.trans hrec)
  rw [e, hinfo] at hr
  exact hr

/-! ## What the circuit side owes of a member -/

/-- **The circuit's loaded form of one twin member**, given its reading (the block `cb` with
members `ms`, the projection `p`, the recursor `rc`, the read level parameters `ps`, type `ty₀`
and rules `rules₀`) and the checked recursor (`cvW'`, `rulesW'`): the level count is the
record's, the read type and rules are closed and over `ps`, a K recursor has one rule, the
checked type is the canonical annotation of the read type at the member's root, and the checked
rules agree with the canonical rules on field counts and right-hand sides, with the K bit and
parameter count of a K rule. -/
structure TwinMemberLoaded (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
    (p : Ixon.RecursorProj) (rc : Ixon.Recursor) (ps : List LevelParam) (ty₀ : KExpr)
    (rules₀ : List (RecRule .anon)) (cvW' : ConstantVal .anon)
    (rulesW' : List (RecRule .anon)) : Prop where
  lvls : ps.length = rc.lvls.toNat
  tyBounded : ty₀.looseBVarsBounded 0 = true
  tyLevels : ty₀.allLevelParamsDefined ps = true
  rulesScoped : ∀ rl ∈ rules₀,
    rl.rhs.looseBVarsBounded 0 = true ∧ rl.rhs.allLevelParamsDefined ps = true
  notK : rc.k = false
  ty : LoadedReads.canonAnn cb ps ((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) rc.typ
    ty₀ = some cvW'.type
  rules : ∃ rls : List (RecRule .anon),
    LoadedReads.canonRules cb ps rc.k rc.params.toNat
      (((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1) rc.rules.toList rules₀ =
        some rls ∧
    List.Forall₂ (fun rl rl' : RecRule .anon => rl'.nfields = rl.nfields ∧ rl'.rhs = rl.rhs)
      rls rulesW' ∧
    (∀ rl rl', rls = [rl] → rulesW' = [rl'] → rl.k = true →
      rl'.k = true ∧ rl'.ctorParams = rl.ctorParams)

theorem TwinMemberLoaded.kOne {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {p : Ixon.RecursorProj} {rc : Ixon.Recursor} {ps : List LevelParam} {ty₀ : KExpr}
    {rules₀ : List (RecRule .anon)} {cvW' : ConstantVal .anon} {rulesW' : List (RecRule .anon)}
    (h : TwinMemberLoaded cb ms p rc ps ty₀ rules₀ cvW' rulesW') :
    rc.k = true → rc.rules.size = 1 :=
  fun hk => absurd (h.notK.symm.trans hk) Bool.false_ne_true

/-- **What the circuit side owes for the reload of a twin record**, over its parts `ws`: the
references the second record `c` at `A` uses are stored at the environment the step is handed;
each part's member is unroled (`assert_no_role`), and, at its reading, is loaded as the part's
checked recursor (`TwinMemberLoaded`). -/
structure TwinLoadFacts (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (A : _root_.Address) (c : Ixon.Constant) (ws : List (TwinRecPart .anon)) : Prop where
  usedStored : Decl.UsedRefsStored t env c
  noRole : ∀ w ∈ ws, ∀ r, w.cvW.name ≠ .role r
  loaded : ∀ w ∈ ws, ∀ (ms : Array Ixon.MutConst) (p : Ixon.RecursorProj) (rc : Ixon.Recursor),
    c.info = .muts ms → p.block = A → ms[p.idx.toNat]? = some (.recr rc) →
    w.cvW.name = keyOf t (memberAddr A p.idx.toNat (.recr rc)) →
    RecReads t (recordOf E₀) (fun y => E₀.blobs.get? y) c (blockSelf t A ms) w.cvW.name rc
      (.recInfo w.cvW w.mI w.rP w.rulesW) →
    TwinMemberLoaded c ms p rc w.cvW.levelParams w.cvW.type w.rulesW w.cvW' w.rulesW'

/-! ## The reload -/

/-- **Each checked twin recursor reloads as itself** after the step, at any environment `env₂`
that finds what the handed environment finds and stores each member of the block: from the
second record's reading, its parts' front doors, and what the circuit side owes
(`TwinLoadFacts`). -/
theorem twinMember_reloads {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {A : _root_.Address} {c : Ixon.Constant}
    {rs' : Array Ixon.MutConst} {blk : List (ConstantInfo .anon)}
    {ws : List (TwinRecPart .anon)}
    (ht : t.check = .ok ()) (hSS : StepStore calls t E₀ E) (hA : FamRecRecord E₀ A c rs')
    (hreads : TwinDeclReads t E₀ A c blk)
    (hblock : blk = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW))
    (hfront : ∀ w ∈ ws, ConstantValCheckJ twinPosRulesJ env w.cvW w.cvW')
    (hL : TwinLoadFacts t E₀ env A c ws)
    (hext : ∀ k, (env.find? k).isSome = true → (env₂.find? k).isSome = true)
    (hstored₂ : ∀ ci ∈ blk, (env₂.find? ci.name).isSome = true) :
    ∀ w ∈ ws, Decl.ReloadsAs E t env₂ (.recInfo w.cvW' w.mI w.rP w.rulesW') := by
  intro w hw
  have hci : ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW ∈ blk := by
    rw [hblock]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  obtain ⟨x, hx, hname, hrd⟩ := hreads.2.1 _ hci
  have hname' : w.cvW.name = keyOf t x := hname
  -- the constant address is a recursor member's
  rcases hx with ⟨-, hs⟩ | ⟨ms, i, m, hms, hm, hxm⟩
  · exact (standalone_not_block hs ⟨rs', hA.muts⟩).elim
  have hrs : rs' = ms := Ixon.ConstantInfo.muts.inj (hA.muts.symm.trans hms)
  rw [← hrs] at hm
  have hm' : rs'.toList[i]? = some m := by simpa only [Array.getElem?_toList] using hm
  obtain ⟨r, hr⟩ := hA.recrs m (List.mem_of_getElem? hm')
  subst hr
  rcases hxm with hxm | ⟨ind, j, hind, -, -⟩
  swap
  · cases hind
  subst hxm
  -- its projection record and its reading
  have hP : recordOf E₀ (memberAddr A i (.recr r)) = some (memberProjection A i (.recr r)) :=
    hA.members i _ hm
  obtain ⟨cb, ms', rc, hMA, hRR⟩ := reads_rprj (p := ⟨i.toUInt64, A⟩) hP rfl hrd
  obtain ⟨hcb, hcbm, hmem, -, hxa, -⟩ := hMA
  have ecb : cb = c := Option.some.inj (hcb.symm.trans hA.record)
  rw [ecb] at hcbm hRR
  -- what the circuit side owes at this member
  have hRR' : RecReads t (recordOf E₀) (fun y => E₀.blobs.get? y) c (blockSelf t A ms')
      w.cvW.name rc (.recInfo w.cvW w.mI w.rP w.rulesW) := by
    rw [hname']
    exact hRR
  have hML := hL.loaded w hw ms' ⟨i.toUInt64, A⟩ rc hcbm rfl hmem
    (hname'.trans (congrArg (keyOf t) hxa)) hRR'
  obtain ⟨tyP, ty, kF, kM, B', Bm, i', im, ind, indM, ps, rules, -, -, -, -, -, hps, hty, -,
    hrules, hci₀⟩ := hRR
  obtain ⟨hcv, hmI, hrP, hrl⟩ := ConstantInfo.recInfo.inj hci₀
  have hps' : w.cvW.levelParams = ps := by rw [hcv]
  have hty' : w.cvW.type = ty := by rw [hcv]
  rw [hps', hty', hrl] at hML
  obtain ⟨rls, hcR, hagree, hK⟩ := hML.rules
  have hcn := LoadedReads.canonRec_eq (key := keyOf t (memberAddr A i (.recr r))) hML.ty hcR
  -- the read rules, over the step's store
  have hrules₁ : List.Forall₂ (fun (ru : Ixon.RecursorRule) (rl₀ : RecRule .anon) =>
      rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun y => E₀.blobs.get? y) c (Ix.Kernel.Reader.recParam ps)
        (blockSelf t A ms')).read ru.rhs = .ok rl₀.rhs) rc.rules.toList rules :=
    lforall₂_of_zipIdx (fun q rl h => by
      obtain ⟨rhs, hread, hrl⟩ := h
      subst hrl
      exact ⟨rfl, hread⟩) hrules
  have hrulesE : List.Forall₂ (fun (ru : Ixon.RecursorRule) (rl₀ : RecRule .anon) =>
      rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun y => E.blobs.get? y) c (Ix.Kernel.Reader.recParam ps)
        (blockSelf t A ms')).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules :=
    lforall₂_mono (fun ru rl₀ h => ⟨h.1.1,
      ReaderReads.exprReader_mono (blob := fun y => E₀.blobs.get? y)
        (blob' := fun y => E.blobs.get? y) hSS.runBlob h.1.2,
      h.2.1, h.2.2⟩) (lforall₂_and_mem hrules₁ hML.rulesScoped)
  -- what the second record uses, and the block, stored after the step
  have hused : Decl.UsedRefsStored t env₂ c := by
    intro k hk y hy
    obtain ⟨ci, hci'⟩ := hL.usedStored k hk y hy
    exact Option.isSome_iff_exists.mp (hext _ (by simp [hci']))
  have hblkS : LoadedReads.BlockStored t env₂ A ms' := by
    intro y hy
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
    obtain ⟨m', hm'', hye⟩ := LoadedReads.blockRecurAddrs_get hj
    have hcy : ConstAddrOf A c y := Or.inr ⟨ms', j, m', hcbm, hm'', Or.inl hye⟩
    obtain ⟨ci, hci', hn⟩ := hreads.2.2 y hcy
    have hs := hstored₂ ci hci'
    rw [hn] at hs
    exact Option.isSome_iff_exists.mp hs
  -- the canonical constant reloads, and so does the checked recursor
  have hrel := LoadedReads.reloadsAs_rprj (E' := E) (env := env₂) (p := ⟨i.toUInt64, A⟩) ht
    (hSS.held hP) rfl (hSS.held hA.record) hcbm hmem hML.lvls
    (by rw [hps]; exact Decl.recLps_perm_range _ _)
    (ReaderReads.exprReader_mono (blob := fun y => E₀.blobs.get? y)
      (blob' := fun y => E.blobs.get? y) hSS.runBlob hty) hML.tyBounded hML.tyLevels hrulesE
    hML.kOne
    hused hblkS hcn
  have hfin := reloadsAs_recr_rules hrel (fun k => rfl) hagree hK
  have hcv' : w.cvW' = ⟨keyOf t (memberAddr A i (.recr r)), ps, w.cvW'.type⟩ := by
    have e1 : w.cvW'.name = keyOf t (memberAddr A i (.recr r)) :=
      (hfront w hw).name_eq.trans hname'
    have e2 : w.cvW'.levelParams = ps := (hfront w hw).levelParams_eq.trans hps'
    calc w.cvW' = ⟨w.cvW'.name, w.cvW'.levelParams, w.cvW'.type⟩ := rfl
      _ = _ := by rw [e1, e2]
  rw [hcv', hmI, hrP]
  exact hfin

/-- Unpack `recordOf E a = some c` to its stored lazy constant and exact decoding. -/
theorem recordOf_unpack {E : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf E a = some c) :
    ∃ lc, E.consts.get? a = some lc ∧ Ixon.deConstantExact lc.rawBytes = .ok c := by
  unfold recordOf at h
  cases hget : E.consts.get? a with
  | none =>
    rw [hget] at h
    cases (h : (none : Option Ixon.Constant) = some c)
  | some lc =>
    rw [hget] at h
    refine ⟨lc, rfl, ?_⟩
    have h' : (Ixon.deConstantExact lc.rawBytes).toOption = some c := h
    cases hd : Ixon.deConstantExact lc.rawBytes with
    | error _ => rw [hd] at h'; cases h'
    | ok c' =>
      rw [hd] at h'
      have e : c' = c := Option.some.inj h'
      rw [e]

/-- An unroled address's table key is `.id a`. -/
theorem keyOf_eq_id_of_noRole {t : Ix.Kernel.RoleTable} {a : _root_.Address}
    (h : ∀ r, keyOf t a ≠ .role r) : keyOf t a = .id a := by
  unfold keyOf at h ⊢
  cases hf : t.bound.find? (·.2 == a) with
  | none => rfl
  | some rp => exact absurd (by simp [hf]) (h rp.1)

/-- **Each twin recursor is non-K at its record in `E`** (`Core.RecNotKAt`): from the second
record's reading, `TwinLoadFacts.noRole`, and `TwinMemberLoaded.notK`. -/
theorem twinRecs_recNotKAt {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {A : _root_.Address} {c : Ixon.Constant}
    {rs' : Array Ixon.MutConst} {blk : List (ConstantInfo .anon)}
    {ws : List (TwinRecPart .anon)}
    (hSS : StepStore calls t E₀ E) (hA : FamRecRecord E₀ A c rs')
    (hreads : TwinDeclReads t E₀ A c blk)
    (hblock : blk = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW))
    (hfront : ∀ w ∈ ws, ConstantValCheckJ twinPosRulesJ env w.cvW w.cvW')
    (hL : TwinLoadFacts t E₀ env A c ws) :
    ∀ w ∈ ws, Core.RecNotKAt E w.cvW'.name := by
  intro w hw
  have hci : ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW ∈ blk := by
    rw [hblock]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  obtain ⟨x, hx, hname, hrd⟩ := hreads.2.1 _ hci
  have hname' : w.cvW.name = keyOf t x := hname
  rcases hx with ⟨-, hs⟩ | ⟨ms, i, m, hms, hm, hxm⟩
  · exact (standalone_not_block hs ⟨rs', hA.muts⟩).elim
  have hrs : rs' = ms := Ixon.ConstantInfo.muts.inj (hA.muts.symm.trans hms)
  rw [← hrs] at hm
  have hm' : rs'.toList[i]? = some m := by simpa only [Array.getElem?_toList] using hm
  obtain ⟨r, hr⟩ := hA.recrs m (List.mem_of_getElem? hm')
  subst hr
  rcases hxm with hxm | ⟨ind, j, hind, -, -⟩
  swap
  · cases hind
  subst hxm
  have hP : recordOf E₀ (memberAddr A i (.recr r)) = some (memberProjection A i (.recr r)) :=
    hA.members i _ hm
  obtain ⟨cb, ms', rc, hMA, hRR⟩ := reads_rprj (p := ⟨i.toUInt64, A⟩) hP rfl hrd
  obtain ⟨hcb, hcbm, hmem, -, hxa, -⟩ := hMA
  have ecb : cb = c := Option.some.inj (hcb.symm.trans hA.record)
  rw [ecb] at hcbm hRR
  have hRR' : RecReads t (recordOf E₀) (fun y => E₀.blobs.get? y) c (blockSelf t A ms')
      w.cvW.name rc (.recInfo w.cvW w.mI w.rP w.rulesW) := by
    rw [hname']
    exact hRR
  have hML := hL.loaded w hw ms' ⟨i.toUInt64, A⟩ rc hcbm rfl hmem
    (hname'.trans (congrArg (keyOf t) hxa)) hRR'
  have hid : keyOf t (memberAddr A i (.recr r)) = .id (memberAddr A i (.recr r)) :=
    keyOf_eq_id_of_noRole (fun ro hro => hL.noRole w hw ro (hname'.trans hro))
  obtain ⟨lc0, hlc0, hd0⟩ := recordOf_unpack (hSS.held hP)
  obtain ⟨lcb, hlcb, hdb⟩ := recordOf_unpack (hSS.held hA.record)
  exact ⟨memberAddr A i (.recr r), lc0, lcb, memberProjection A i (.recr r), c, ⟨i.toUInt64, A⟩,
    ms', rc, ((hfront w hw).name_eq.trans hname').trans hid, hlc0, hd0, rfl, hlcb, hdb, hcbm,
    hmem, hML.notK⟩

end IxVM.Refinement.Typing.TwinFamily
