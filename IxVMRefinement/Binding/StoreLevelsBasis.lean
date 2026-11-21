import IxVMRefinement.Binding.StoreLevelsDef
import IxVMRefinement.StatementRel.StoreInhabit
import IxVMRefinement.Ingress.ConvertExpr

/-! # Decidable level-parameter and inductive-parameter coherence for the basis store

Proves `unitLevelsAndParamsOk_of_basis` and `Binding.storeLevelsParams_basis` directly over
`StoreInhabit.basisRows` via decidable boolean checks proved sound against `MemberReader`. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open IxVM.Consistency
open IxVM.Refinement.Core (KExpr KLevel KKey)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

private def univVarsLt (n : Nat) : Ixon.Univ → Bool
  | .zero => true
  | .succ u => univVarsLt n u
  | .max a b => univVarsLt n a && univVarsLt n b
  | .imax a b => univVarsLt n a && univVarsLt n b
  | .var i => decide (i.toNat < n)

private theorem convUniv_allParamsDefined {n : Nat} :
    ∀ u : Ixon.Univ, univVarsLt n u = true →
      (Ix.Kernel.Reader.convUniv id u).allParamsDefined (List.range n) = true
  | .zero, _ => rfl
  | .succ u, h => convUniv_allParamsDefined u h
  | .max a b, h => by
    simp only [univVarsLt, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Reader.convUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨convUniv_allParamsDefined a h.1, convUniv_allParamsDefined b h.2⟩
  | .imax a b, h => by
    simp only [univVarsLt, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Reader.convUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨convUniv_allParamsDefined a h.1, convUniv_allParamsDefined b h.2⟩
  | .var i, h => by
    simp only [univVarsLt, decide_eq_true_eq] at h
    simp only [Ix.Kernel.Reader.convUniv, id, Ix.Kernel.Level.allParamsDefined, List.contains_eq_mem,
      decide_eq_true_eq, List.mem_range]
    exact h

private def univIdxOk (univs : Array Ixon.Univ) (n : Nat) (i : UInt64) : Bool :=
  match univs[i.toNat]? with
  | some u => univVarsLt n u
  | none => true

private def exprUnivsLtGo (univs : Array Ixon.Univ) (n : Nat) (tbl : Array Bool) :
    Ixon.Expr → Bool
  | .var _ | .str _ | .nat _ => true
  | .sort i => univIdxOk univs n i
  | .ref _ us | .recur _ us => us.toList.all (univIdxOk univs n)
  | .prj _ _ v => exprUnivsLtGo univs n tbl v
  | .app f a => exprUnivsLtGo univs n tbl f && exprUnivsLtGo univs n tbl a
  | .lam t b | .all t b => exprUnivsLtGo univs n tbl t && exprUnivsLtGo univs n tbl b
  | .letE _ _ t v b =>
    exprUnivsLtGo univs n tbl t && exprUnivsLtGo univs n tbl v && exprUnivsLtGo univs n tbl b
  | .share i => tbl.getD i.toNat true

private def buildUnivsOkTblGo (univs : Array Ixon.Univ) (n : Nat) :
    Array Bool → List Ixon.Expr → Array Bool
  | acc, [] => acc
  | acc, e :: es => buildUnivsOkTblGo univs n (acc.push (exprUnivsLtGo univs n acc e)) es

private def exprUnivsOk (src : Ixon.Constant) (n : Nat) (e : Ixon.Expr) : Bool :=
  exprUnivsLtGo src.univs n (buildUnivsOkTblGo src.univs n #[] src.sharing.toList) e

private theorem ecx_level_allParamsDefined {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat} {i : UInt64} {l : KLevel}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id))
    (hok : univIdxOk univs n i = true)
    (hl : ecx.level i = .ok l) :
    l.allParamsDefined (List.range n) = true := by
  unfold Ix.Kernel.Reader.ECx.level at hl
  rw [hunivs, Array.getElem?_map] at hl
  unfold univIdxOk at hok
  cases hget : univs[i.toNat]? with
  | none => rw [hget] at hl; simp [Ix.Kernel.Reader.malformed] at hl
  | some u =>
    rw [hget] at hl hok
    simp only [Option.map_some] at hl
    have heq : Ix.Kernel.Reader.convUniv id u = l := Except.ok.inj hl
    rw [← heq]
    exact convUniv_allParamsDefined u hok

private theorem ecx_levels_allParamsDefined {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id)) :
    ∀ (us : List UInt64) (ls : List KLevel),
      us.all (univIdxOk univs n) = true →
      us.mapM ecx.level = .ok ls →
      ls.all (Ix.Kernel.Level.allParamsDefined (List.range n)) = true
  | [], ls, _, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | u :: us, ls, hok, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hl : ecx.level u with
    | error _ => rw [hl] at h; cases h
    | ok l =>
      rw [hl] at h
      cases hls : us.mapM ecx.level with
      | error _ => rw [hls] at h; cases h
      | ok ls' =>
        rw [hls] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨ecx_level_allParamsDefined hunivs hok.1 hl,
          ecx_levels_allParamsDefined hunivs us ls' hok.2 hls⟩

private theorem convExpr_allLevelParamsDefined {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat}
    {shareTbl : Array (Ix.Kernel.Reader.ReadM KExpr)} {okTbl : Array Bool}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id))
    (htbl : ∀ i E_rd, shareTbl[i]? = some (.ok E_rd) → okTbl.getD i true = true →
      E_rd.allLevelParamsDefined (List.range n) = true) :
    ∀ (e : Ixon.Expr) (E_rd : KExpr),
      exprUnivsLtGo univs n okTbl e = true →
      Ix.Kernel.Reader.convExpr ecx shareTbl e = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range n) = true
  | .var i, E_rd, _, h => by
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [Ix.Kernel.Expr.mkBvar_eq]; rfl
  | .sort i, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hl : ecx.level i with
    | error _ => rw [hl] at h; cases h
    | ok l =>
      rw [hl] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ecx_level_allParamsDefined hunivs hok hl
  | .ref i us, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hk : ecx.keyAt i with
    | error _ => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h
      cases hls : ecx.levels us with
      | error _ => rw [hls] at h; cases h
      | ok ls =>
        rw [hls] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ecx_levels_allParamsDefined hunivs us.toList ls hok hls
  | .recur i us, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr] at h
    cases hs : ecx.self i.toNat with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs] at h
      simp only [bind, Except.bind] at h
      cases hm : m with
      | error _ => rw [hm] at h; cases h
      | ok k =>
        rw [hm] at h
        cases hls : ecx.levels us with
        | error _ => rw [hls] at h; cases h
        | ok ls =>
          rw [hls] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ecx_levels_allParamsDefined hunivs us.toList ls hok hls
  | .prj i f v, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hk : ecx.keyAt i with
    | error _ => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h
      cases hv : Ix.Kernel.Reader.convExpr ecx shareTbl v with
      | error _ => rw [hv] at h; cases h
      | ok ev =>
        rw [hv] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact convExpr_allLevelParamsDefined hunivs htbl v ev hok hv
  | .str i, E_rd, _, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hb : ecx.blobAt i with
    | error _ => rw [hb] at h; cases h
    | ok bs =>
      rw [hb] at h; dsimp only at h
      cases hs : String.fromUTF8? bs with
      | none => rw [hs] at h; cases h
      | some s =>
        rw [hs] at h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; rfl
  | .nat i, E_rd, _, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hn : ecx.natAt i with
    | error _ => rw [hn] at h; cases h
    | ok m =>
      rw [hn] at h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
  | .app f a, E_rd, hok, h => by
    simp only [exprUnivsLtGo, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hf : Ix.Kernel.Reader.convExpr ecx shareTbl f with
    | error _ => rw [hf] at h; cases h
    | ok ef =>
      rw [hf] at h
      cases ha : Ix.Kernel.Reader.convExpr ecx shareTbl a with
      | error _ => rw [ha] at h; cases h
      | ok ea =>
        rw [ha] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
        exact ⟨convExpr_allLevelParamsDefined hunivs htbl f ef hok.1 hf,
          convExpr_allLevelParamsDefined hunivs htbl a ea hok.2 ha⟩
  | .lam t b, E_rd, hok, h => by
    simp only [exprUnivsLtGo, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases ht : Ix.Kernel.Reader.convExpr ecx shareTbl t with
    | error _ => rw [ht] at h; cases h
    | ok et =>
      rw [ht] at h
      cases hb : Ix.Kernel.Reader.convExpr ecx shareTbl b with
      | error _ => rw [hb] at h; cases h
      | ok eb =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true,
          Ix.Kernel.BinderMeta.leanNever, Ix.Kernel.PropWhen.paramsDefined]
        exact ⟨⟨convExpr_allLevelParamsDefined hunivs htbl t et hok.1 ht,
          convExpr_allLevelParamsDefined hunivs htbl b eb hok.2 hb⟩, rfl⟩
  | .all t b, E_rd, hok, h => by
    simp only [exprUnivsLtGo, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases ht : Ix.Kernel.Reader.convExpr ecx shareTbl t with
    | error _ => rw [ht] at h; cases h
    | ok et =>
      rw [ht] at h
      cases hb : Ix.Kernel.Reader.convExpr ecx shareTbl b with
      | error _ => rw [hb] at h; cases h
      | ok eb =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true,
          Ix.Kernel.BinderMeta.leanNever, Ix.Kernel.PropWhen.paramsDefined]
        exact ⟨⟨convExpr_allLevelParamsDefined hunivs htbl t et hok.1 ht,
          convExpr_allLevelParamsDefined hunivs htbl b eb hok.2 hb⟩, rfl⟩
  | .letE _ _ t v b, E_rd, hok, h => by
    simp only [exprUnivsLtGo, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases ht : Ix.Kernel.Reader.convExpr ecx shareTbl t with
    | error _ => rw [ht] at h; cases h
    | ok et =>
      rw [ht] at h
      cases hv : Ix.Kernel.Reader.convExpr ecx shareTbl v with
      | error _ => rw [hv] at h; cases h
      | ok ev =>
        rw [hv] at h
        cases hb : Ix.Kernel.Reader.convExpr ecx shareTbl b with
        | error _ => rw [hb] at h; cases h
        | ok eb =>
          rw [hb] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
          exact ⟨⟨convExpr_allLevelParamsDefined hunivs htbl t et hok.1.1 ht,
            convExpr_allLevelParamsDefined hunivs htbl v ev hok.1.2 hv⟩,
            convExpr_allLevelParamsDefined hunivs htbl b eb hok.2 hb⟩
  | .share i, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr] at h
    cases hg : shareTbl[i.toNat]? with
    | none => rw [hg] at h; cases h
    | some r =>
      rw [hg] at h; dsimp only at h
      exact htbl i.toNat E_rd (by rw [hg, h]) hok

private theorem buildUnivsOkTblGo_sound {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id)) :
    ∀ (es : List Ixon.Expr) (shareAcc : Array (Ix.Kernel.Reader.ReadM KExpr))
      (okAcc : Array Bool),
      shareAcc.size = okAcc.size →
      (∀ i E_rd, shareAcc[i]? = some (.ok E_rd) → okAcc.getD i true = true →
        E_rd.allLevelParamsDefined (List.range n) = true) →
      ∀ i E_rd, (Ingress.buildShareTblGo ecx shareAcc es)[i]? = some (.ok E_rd) →
        (buildUnivsOkTblGo univs n okAcc es).getD i true = true →
        E_rd.allLevelParamsDefined (List.range n) = true
  | [], shareAcc, okAcc, _, hinv, i, E_rd, hs, hok => hinv i E_rd hs hok
  | e :: es, shareAcc, okAcc, hsz, hinv, i, E_rd, hs, hok => by
    refine buildUnivsOkTblGo_sound hunivs es
      (shareAcc.push (Ix.Kernel.Reader.convExpr ecx shareAcc e))
      (okAcc.push (exprUnivsLtGo univs n okAcc e)) (by simp [hsz]) ?_ i E_rd hs hok
    intro j E' hj hokj
    by_cases hlt : j < shareAcc.size
    · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt] at hj
      have hlt' : j < okAcc.size := by omega
      have hgetd : (okAcc.push (exprUnivsLtGo univs n okAcc e)).getD j true = okAcc.getD j true := by
        simp [Array.getD, hlt', Array.size_push, Nat.lt_succ_of_lt hlt', Array.getElem_push_lt hlt']
      rw [hgetd] at hokj
      exact hinv j E' hj hokj
    · have hj_eq : j = shareAcc.size := by
        have hlt_p := (Array.getElem?_eq_some_iff.mp hj).1
        simp only [Array.size_push] at hlt_p; omega
      subst hj_eq
      rw [Array.getElem?_push_size] at hj
      have hconv := Option.some.inj hj
      have hgetd : (okAcc.push (exprUnivsLtGo univs n okAcc e)).getD shareAcc.size true =
          exprUnivsLtGo univs n okAcc e := by
        simp [Array.getD, hsz]
      rw [hgetd] at hokj
      exact convExpr_allLevelParamsDefined hunivs hinv e E' hokj hconv

private theorem exprUnivsOk_sound {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {n : Nat} {e : Ixon.Expr} {E_rd : KExpr}
    (hok : exprUnivsOk src n e = true)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read e = .ok E_rd) :
    E_rd.allLevelParamsDefined (List.range n) = true := by
  obtain ⟨hecx, htbl⟩ := Ingress.memberReader_mk'_eq cx src id self
  unfold Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl] at hread
  have hinv := buildUnivsOkTblGo_sound
    (ecx := ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv id), self⟩)
    (univs := src.univs) (n := n) rfl src.sharing.toList #[] #[] rfl
    (fun i _ h => by simp at h)
  exact convExpr_allLevelParamsDefined rfl hinv e E_rd hok hread

private def constLevelsOkBool (c : Ixon.Constant) : Bool :=
  match c.info with
  | .defn d =>
    if d.kind == .defn then decide (d.lvls.toNat < 4294967296) && exprUnivsOk c d.lvls.toNat d.value
    else true
  | .muts ms =>
    ms.toList.all fun m =>
      match m with
      | .defn d =>
        if d.kind == .defn then decide (d.lvls.toNat < 4294967296) && exprUnivsOk c d.lvls.toNat d.value
        else true
      | .indc ind =>
        decide (ind.lvls.toNat < 4294967296) && exprUnivsOk c ind.lvls.toNat ind.typ &&
          ind.ctors.toList.all fun ct =>
            decide (ct.lvls.toNat < 4294967296) && exprUnivsOk c ct.lvls.toNat ct.typ
      | .recr r =>
        decide (r.lvls.toNat < 4294967296) && exprUnivsOk c r.lvls.toNat r.typ &&
          r.rules.toList.all fun ru => exprUnivsOk c r.lvls.toNat ru.rhs
  | _ => true

private def constIndParamsOkBool (c : Ixon.Constant) : Bool :=
  match c.info with
  | .muts ms =>
    ms.toList.all fun m =>
      match m with
      | .indc ind =>
        ind.ctors.toList.all (fun ct => ct.params == ind.params) &&
          ms.toList.all fun m2 =>
            match m2 with
            | .indc ind2 => ind2.params == ind.params
            | _ => true
      | _ => true
  | _ => true

set_option maxRecDepth 200000 in
private theorem basisRows_levelsOk_bool :
    StoreInhabit.basisRows.all (fun e => constLevelsOkBool e.2) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
private theorem basisRows_indParamsOk_bool :
    StoreInhabit.basisRows.all (fun e => constIndParamsOkBool e.2) = true := by
  decide +kernel

private theorem basisRow_constLevelsOk {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf StoreInhabit.basisStore a = some c) :
    constLevelsOkBool c = true :=
  List.all_eq_true.mp basisRows_levelsOk_bool (a, c) (StoreInhabit.store_record_inv h)

private theorem basisRow_constIndParamsOk {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf StoreInhabit.basisStore a = some c) :
    constIndParamsOkBool c = true :=
  List.all_eq_true.mp basisRows_indParamsOk_bool (a, c) (StoreInhabit.store_record_inv h)

/-- Every record of `StoreInhabit.basisStore` satisfies `UnitLevelsAndParamsOk` at any blob env. -/
theorem unitLevelsAndParamsOk_of_basis {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {c : Ixon.Constant}
    (hb : recordOf StoreInhabit.basisStore a = some c) :
    UnitLevelsAndParamsOk t E₀ a c := by
  have hlv := basisRow_constLevelsOk hb
  have hpr := basisRow_constIndParamsOk hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hci hdk
    simp only [constLevelsOkBool, hci, hdk] at hlv
    change (decide (d.lvls.toNat < 4294967296) && exprUnivsOk c d.lvls.toNat d.value) = true at hlv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlv
    exact ⟨hlv.1, fun E_rd hr => exprUnivsOk_sound hlv.2 hr⟩
  · intro ms i d hci hi hdk
    simp only [constLevelsOkBool, hci, List.all_eq_true] at hlv
    have hm := hlv (.defn d) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    simp only [hdk] at hm
    change (decide (d.lvls.toNat < 4294967296) && exprUnivsOk c d.lvls.toNat d.value) = true at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    exact ⟨hm.1, fun E_rd hr => exprUnivsOk_sound hm.2 hr⟩
  · intro ms i ind hci hi
    simp only [constLevelsOkBool, hci, List.all_eq_true] at hlv
    simp only [constIndParamsOkBool, hci, List.all_eq_true] at hpr
    have hml := hlv (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    have hmp := hpr (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hml hmp
    refine ⟨⟨hml.1.1, fun E_rd hr => exprUnivsOk_sound hml.1.2 hr⟩, ?_, ?_⟩
    · intro j ct hj
      have hct := hml.2 ct (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj))
      have hctp := hmp.1 ct (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj))
      exact ⟨hct.1, fun E_rd hr => exprUnivsOk_sound hct.2 hr, beq_iff_eq.mp hctp⟩
    · intro i₂ ind₂ hi₂
      have hp2 := hmp.2 (.indc ind₂) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi₂))
      exact (beq_iff_eq.mp hp2).symm
  · intro ms k r hci hk
    simp only [constLevelsOkBool, hci, List.all_eq_true] at hlv
    have hm := hlv (.recr r) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hm
    refine ⟨hm.1.1, fun E_rd hr => exprUnivsOk_sound hm.1.2 hr, ?_⟩
    intro j ru E_rd hj hr
    have hru := hm.2 ru (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj))
    exact exprUnivsOk_sound hru hr

end IxVM.Refinement.Binding.FamilyRecon

namespace IxVM.Refinement.Binding

/-- **Blob-independent level-parameter well-scopedness and inductive parameter coherence on the
basis store.** -/
theorem storeLevelsParams_basis (t : Ix.Kernel.RoleTable) :
    StoreLevelsParams t StoreInhabit.basisStore :=
  storeLevelsParams_of_units StoreInhabit.store_usedClosed
    (fun _ _ _ h => FamilyRecon.unitLevelsAndParamsOk_of_basis h)

end IxVM.Refinement.Binding
