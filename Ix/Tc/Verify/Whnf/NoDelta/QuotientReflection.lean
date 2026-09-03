import Ix.Tc.Verify.Whnf.NoDelta.Quotient

/-!
# Quotient reduction reflection

This module turns the successful production `tryQuotReduce` path into the
semantic `QuotientReductionReflection` consumed by the no-delta reducer.  The
only conditional input is a pair of Theory-level contraction laws.  They
mention no Ix state, addresses, hashes, support predicates, or executions and
are the narrow temporary interface intended to be replaced by Lean4Lean's
constructive quotient result.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Theory-only quotient contraction laws expected from Lean4Lean L4L-19B.

Both laws are deliberately phrased after the quotient major has been related
to an exact `Quot.mk` application.  The Ix adapter below owns the proof of that
relation from the real recursive-WHNF callback and owns all concrete spine and
suffix alignment. -/
structure QuotientReductionLaws (env : Lean4Lean.VEnv) : Prop where
  lift : ∀ {uvars : Nat} {Gamma : List VExpr}
      {liftLevels mkLevels : List Lean4Lean.VLevel}
      {alpha relation beta fn respects ctorAlpha ctorRelation representative
        major : VExpr},
    env.WF →
    env.defeqs Lean4Lean.quotDefEq →
    VExpr.WF env uvars Gamma
      (.app
        (VExpr.appN (.const ``Quot.lift liftLevels)
          [alpha, relation, beta, fn, respects])
        major) →
    env.IsDefEqU uvars Gamma major
      (VExpr.appN (.const ``Quot.mk mkLevels)
        [ctorAlpha, ctorRelation, representative]) →
    ∃ domain codomain,
      env.HasType uvars Gamma fn (.forallE domain codomain) ∧
      env.HasType uvars Gamma representative domain ∧
      env.IsDefEqU uvars Gamma
        (.app
          (VExpr.appN (.const ``Quot.lift liftLevels)
            [alpha, relation, beta, fn, respects])
          major)
        (.app fn representative)
  ind : ∀ {uvars : Nat} {Gamma : List VExpr}
      {indLevels mkLevels : List Lean4Lean.VLevel}
      {alpha relation motive fn ctorAlpha ctorRelation representative
        major : VExpr},
    env.WF →
    VExpr.WF env uvars Gamma
      (.app
        (VExpr.appN (.const ``Quot.ind indLevels)
          [alpha, relation, motive, fn])
        major) →
    env.IsDefEqU uvars Gamma major
      (VExpr.appN (.const ``Quot.mk mkLevels)
        [ctorAlpha, ctorRelation, representative]) →
    ∃ domain codomain,
      env.HasType uvars Gamma fn (.forallE domain codomain) ∧
      env.HasType uvars Gamma representative domain ∧
      env.IsDefEqU uvars Gamma
        (.app
          (VExpr.appN (.const ``Quot.ind indLevels)
            [alpha, relation, motive, fn])
          major)
        (.app fn representative)

namespace RecM

private theorem array_extract_to_end_eq_drop
    {alpha : Type} (values : Array alpha) (start : Nat) :
    (values.extract start values.size).toList =
      values.toList.drop start := by
  rw [Array.toList_extract]
  simp only [List.extract_eq_take_drop]
  have hvaluesLength : values.toList.length = values.size := by simp
  have hdropLength :
      (values.toList.drop start).length = values.size - start := by
    rw [List.length_drop, hvaluesLength]
  rw [← hdropLength]
  exact List.take_length

private theorem array_extract_after_split
    {alpha : Type} [Inhabited alpha] {values : Array alpha} {index : Nat}
    {prior later : List alpha}
    (hvalues : values.toList = prior ++ values[index]! :: later)
    (hindex : index = prior.length) :
    (values.extract (index + 1) values.size).toList = later := by
  rw [array_extract_to_end_eq_drop, hvalues, hindex]
  simp

private theorem list_eq_four_of_length
    {alpha : Type} {values : List alpha} (h : values.length = 4) :
    ∃ a b c d, values = [a, b, c, d] := by
  rcases values with _ | ⟨a, values⟩
  · simp at h
  rcases values with _ | ⟨b, values⟩
  · simp at h
  rcases values with _ | ⟨c, values⟩
  · simp at h
  rcases values with _ | ⟨d, values⟩
  · simp at h
  have hnil : values = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
  subst values
  exact ⟨a, b, c, d, rfl⟩

private theorem list_eq_five_of_length
    {alpha : Type} {values : List alpha} (h : values.length = 5) :
    ∃ a b c d e, values = [a, b, c, d, e] := by
  rcases values with _ | ⟨a, values⟩
  · simp at h
  rcases values with _ | ⟨b, values⟩
  · simp at h
  rcases values with _ | ⟨c, values⟩
  · simp at h
  rcases values with _ | ⟨d, values⟩
  · simp at h
  rcases values with _ | ⟨e, values⟩
  · simp at h
  have hnil : values = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
  subst values
  exact ⟨a, b, c, d, e, rfl⟩

private theorem list_eq_three_of_length
    {alpha : Type} {values : List alpha} (h : values.length = 3) :
    ∃ a b c, values = [a, b, c] := by
  rcases values with _ | ⟨a, values⟩
  · simp at h
  rcases values with _ | ⟨b, values⟩
  · simp at h
  rcases values with _ | ⟨c, values⟩
  · simp at h
  have hnil : values = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
  subst values
  exact ⟨a, b, c, rfl⟩

namespace TrAppSpine

/-- Invert an exact three-argument translated spine. -/
theorem three
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {head a b c : KExpr .anon} {resultV : VExpr}
    (h : TrAppSpine env uvars nameOf trProj Delta head [a, b, c]
      resultV) :
    ∃ headV aV bV cV,
      TrKExprS env uvars nameOf trProj Delta head headV ∧
      TrKExprS env uvars nameOf trProj Delta a aV ∧
      TrKExprS env uvars nameOf trProj Delta b bV ∧
      TrKExprS env uvars nameOf trProj Delta c cV ∧
      resultV = VExpr.appN headV [aV, bV, cV] := by
  obtain ⟨headV, hhead, hsuffix⟩ := h.toSuffix
  have h3 : TrAppSuffix env uvars nameOf trProj Delta headV
      ([a, b] ++ [c]) resultV := by simpa using hsuffix
  obtain ⟨v2, cV, _, _, h2, _, _, hc, rfl⟩ := h3.unsnoc
  have h2' : TrAppSuffix env uvars nameOf trProj Delta headV
      ([a] ++ [b]) v2 := by simpa using h2
  obtain ⟨v1, bV, _, _, h1, _, _, hb, rfl⟩ := h2'.unsnoc
  have h1' : TrAppSuffix env uvars nameOf trProj Delta headV
      ([] ++ [a]) v1 := by simpa using h1
  obtain ⟨v0, aV, _, _, h0, _, _, ha, rfl⟩ := h1'.unsnoc
  obtain ⟨argValues, hvalues⟩ := TrAppSuffix.Values.ofSuffix h0
  obtain ⟨_, hv0⟩ := hvalues.nil_inv
  subst v0
  exact ⟨headV, aV, bV, cV, hhead, ha, hb, hc, rfl⟩

/-- Invert an exact four-argument translated spine. -/
theorem four
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {head a b c d : KExpr .anon} {resultV : VExpr}
    (h : TrAppSpine env uvars nameOf trProj Delta head [a, b, c, d]
      resultV) :
    ∃ headV aV bV cV dV,
      TrKExprS env uvars nameOf trProj Delta head headV ∧
      TrKExprS env uvars nameOf trProj Delta a aV ∧
      TrKExprS env uvars nameOf trProj Delta b bV ∧
      TrKExprS env uvars nameOf trProj Delta c cV ∧
      TrKExprS env uvars nameOf trProj Delta d dV ∧
      resultV = VExpr.appN headV [aV, bV, cV, dV] := by
  obtain ⟨headV, hhead, hsuffix⟩ := h.toSuffix
  have h4 : TrAppSuffix env uvars nameOf trProj Delta headV
      ([a, b, c] ++ [d]) resultV := by simpa using hsuffix
  obtain ⟨v3, dV, _, _, h3, _, _, hd, rfl⟩ := h4.unsnoc
  have h3' : TrAppSuffix env uvars nameOf trProj Delta headV
      ([a, b] ++ [c]) v3 := by simpa using h3
  obtain ⟨v2, cV, _, _, h2, _, _, hc, rfl⟩ := h3'.unsnoc
  have h2' : TrAppSuffix env uvars nameOf trProj Delta headV
      ([a] ++ [b]) v2 := by simpa using h2
  obtain ⟨v1, bV, _, _, h1, _, _, hb, rfl⟩ := h2'.unsnoc
  have h1' : TrAppSuffix env uvars nameOf trProj Delta headV
      ([] ++ [a]) v1 := by simpa using h1
  obtain ⟨v0, aV, _, _, h0, _, _, ha, rfl⟩ := h1'.unsnoc
  obtain ⟨argValues, hvalues⟩ := TrAppSuffix.Values.ofSuffix h0
  obtain ⟨_, hv0⟩ := hvalues.nil_inv
  subst v0
  exact ⟨headV, aV, bV, cV, dV, hhead, ha, hb, hc, hd, rfl⟩

/-- Invert an exact five-argument translated spine. -/
theorem five
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {head a b c d e : KExpr .anon} {resultV : VExpr}
    (h : TrAppSpine env uvars nameOf trProj Delta head [a, b, c, d, e]
      resultV) :
    ∃ headV aV bV cV dV eV,
      TrKExprS env uvars nameOf trProj Delta head headV ∧
      TrKExprS env uvars nameOf trProj Delta a aV ∧
      TrKExprS env uvars nameOf trProj Delta b bV ∧
      TrKExprS env uvars nameOf trProj Delta c cV ∧
      TrKExprS env uvars nameOf trProj Delta d dV ∧
      TrKExprS env uvars nameOf trProj Delta e eV ∧
      resultV = VExpr.appN headV [aV, bV, cV, dV, eV] := by
  obtain ⟨headV, hhead, hsuffix⟩ := h.toSuffix
  have h5 : TrAppSuffix env uvars nameOf trProj Delta headV
      ([a, b, c, d] ++ [e]) resultV := by simpa using hsuffix
  obtain ⟨v4, eV, _, _, h4, _, _, he, rfl⟩ := h5.unsnoc
  have h4' : TrAppSuffix env uvars nameOf trProj Delta headV
      ([a, b, c] ++ [d]) v4 := by simpa using h4
  obtain ⟨v3, dV, _, _, h3, _, _, hd, rfl⟩ := h4'.unsnoc
  have h3' : TrAppSuffix env uvars nameOf trProj Delta headV
      ([a, b] ++ [c]) v3 := by simpa using h3
  obtain ⟨v2, cV, _, _, h2, _, _, hc, rfl⟩ := h3'.unsnoc
  have h2' : TrAppSuffix env uvars nameOf trProj Delta headV
      ([a] ++ [b]) v2 := by simpa using h2
  obtain ⟨v1, bV, _, _, h1, _, _, hb, rfl⟩ := h2'.unsnoc
  have h1' : TrAppSuffix env uvars nameOf trProj Delta headV
      ([] ++ [a]) v1 := by simpa using h1
  obtain ⟨v0, aV, _, _, h0, _, _, ha, rfl⟩ := h1'.unsnoc
  obtain ⟨argValues, hvalues⟩ := TrAppSuffix.Values.ofSuffix h0
  obtain ⟨_, hv0⟩ := hvalues.nil_inv
  subst v0
  exact ⟨headV, aV, bV, cV, dV, eV, hhead, ha, hb, hc, hd, he, rfl⟩

end TrAppSpine

namespace TrKExprS

/-- A translated constant whose address has an exact trusted-name binding has
that name in its Theory syntax. -/
theorem const_name
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {id : KId .anon} {us : Array (KUniv .anon)}
    {info : ExprInfo .anon} {value : VExpr} {name : Lean.Name}
    (h : TrKExprS env uvars nameOf trProj Delta (.const id us info) value)
    (hname : nameOf id.addr = some name) :
    value = .const name (us.toList.map KUniv.toVLevel) := by
  let .const actualName _ _ _ := h
  rw [hname] at actualName
  cases actualName
  rfl

end TrKExprS

/-- Semantic core of the `Quot.lift` production branch.  The premises are
the exact split produced by `TrAppSpine.splitAt`, the recursive callback post,
and the pure suffix result selected by the production intern plan. -/
theorem quotientLiftMeaning
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx} {prims : Primitives .anon}
    (theory : WhnfTheory trProj world uvars)
    (laws : QuotientReductionLaws world.venv)
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (hregistered : world.venv.defeqs Lean4Lean.quotDefEq)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source : KExpr .anon} {sourceV : VExpr}
    {id : KId .anon} {us : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {args : Array (KExpr .anon)}
    {priorArgs laterArgs : List (KExpr .anon)} {priorV majorV : VExpr}
    {majorWhnf : KExpr .anon} {mkId : KId .anon}
    {mkUs : Array (KUniv .anon)} {mkInfo : ExprInfo .anon}
    {mkArgs : Array (KExpr .anon)} {result : KExpr .anon}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hlift : id.addr = prims.quotLift.addr)
    (hargs : args.toList = priorArgs ++ args[5]! :: laterArgs)
    (hindex : 5 = priorArgs.length)
    (hprior : TrAppSpine world.venv uvars world.nameOf trProj Delta
      (.const id us headInfo) priorArgs priorV)
    (hthrough : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkApp
        (priorArgs.foldl KExpr.mkApp (.const id us headInfo)) args[5]!)
      (.app priorV majorV))
    (hsuffix : TrAppSuffix world.venv uvars world.nameOf trProj Delta
      (.app priorV majorV) laterArgs sourceV)
    (hmajorPost : WhnfPost trProj world uvars Delta majorV majorWhnf)
    (hmkSpine : majorWhnf.collectSpine =
      (.const mkId mkUs mkInfo, mkArgs))
    (hctor : mkId.addr = prims.quotCtor.addr)
    (hmkSize : mkArgs.size = 3)
    (hresult : result = laterArgs.foldl KExpr.mkApp
      (KExpr.mkApp args[3]! mkArgs[2]!)) :
    WhnfMeaning trProj world uvars Delta source result := by
  have hpriorLength : priorArgs.length = 5 := hindex.symm
  obtain ⟨arg0, arg1, arg2, fnArg, respectsArg, rfl⟩ :=
    list_eq_five_of_length hpriorLength
  obtain ⟨liftHeadV, alpha, relation, beta, fn, respects,
      hliftHeadTr, _, _, _, hfnTr, _, hpriorShape⟩ := hprior.five
  have hliftName : world.nameOf id.addr = some ``Quot.lift := by
    rw [hlift]
    exact htable.quotLift.2
  have hliftHead : liftHeadV =
      .const ``Quot.lift (us.toList.map KUniv.toVLevel) :=
    Ix.Tc.RecM.TrKExprS.const_name hliftHeadTr hliftName
  rw [hliftHead] at hpriorShape
  subst priorV

  have hargsSize : args.size = 6 + laterArgs.length := by
    have hlength := congrArg List.length hargs
    simp only [Array.length_toList, List.length_append, List.length_cons,
      List.length_nil] at hlength
    omega
  have hfnIndex : 3 < args.size := by omega
  have hfnArg : args[3]! = fnArg := by
    have hget : args.toList[3]? = some fnArg := by
      rw [hargs]
      rfl
    rw [Array.getElem?_toList,
      Array.getElem?_eq_getElem hfnIndex] at hget
    have heq := Option.some.inj hget
    simpa only [getElem!_pos args 3 hfnIndex] using heq

  obtain ⟨majorWhnfV, hmajorWhnfTr, hmajorEq⟩ := hmajorPost
  have hmkTyped := trAppSpine_of_collectSpine hmajorWhnfTr hmkSpine
  have hmkLength : mkArgs.toList.length = 3 := by simpa using hmkSize
  obtain ⟨ctorAlphaArg, ctorRelationArg, representativeArg, hmkList⟩ :=
    list_eq_three_of_length hmkLength
  rw [hmkList] at hmkTyped
  obtain ⟨mkHeadV, ctorAlpha, ctorRelation, representative,
      hmkHeadTr, _, _, hrepresentativeTr, hmkShape⟩ := hmkTyped.three
  have hmkName : world.nameOf mkId.addr = some ``Quot.mk := by
    rw [hctor]
    exact htable.quotCtor.2
  have hmkHead : mkHeadV =
      .const ``Quot.mk (mkUs.toList.map KUniv.toVLevel) :=
    Ix.Tc.RecM.TrKExprS.const_name hmkHeadTr hmkName
  rw [hmkHead] at hmkShape
  subst majorWhnfV

  have hrepresentativeIndex : 2 < mkArgs.size := by omega
  have hrepresentativeArg : mkArgs[2]! = representativeArg := by
    have hget : mkArgs.toList[2]? = some representativeArg := by
      rw [hmkList]
      rfl
    rw [Array.getElem?_toList,
      Array.getElem?_eq_getElem hrepresentativeIndex] at hget
    have heq := Option.some.inj hget
    simpa only [getElem!_pos mkArgs 2 hrepresentativeIndex] using heq

  have hredexWF : VExpr.WF world.venv uvars Delta.toCtx
      (.app
        (VExpr.appN
          (.const ``Quot.lift (us.toList.map KUniv.toVLevel))
          [alpha, relation, beta, fn, respects])
        majorV) :=
    hthrough.wf world.venvWF.ordered theory.literalWF
      theory.projections.wf hDelta
  obtain ⟨domain, codomain, hfnType, hrepresentativeType, hreduce⟩ :=
    laws.lift world.venvWF hregistered hredexWF hmajorEq
  have hbaseTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkApp args[3]! mkArgs[2]!) (.app fn representative) := by
    rw [hfnArg, hrepresentativeArg, KExpr.mkApp_shape]
    exact .app hfnType hrepresentativeType hfnTr hrepresentativeTr
  obtain ⟨resultV, hresultTr, hresultEq⟩ :=
    hsuffix.rebase world.venvWF hDelta hbaseTr hreduce
  rw [← hresult] at hresultTr
  exact ⟨sourceV, resultV, hsource, hresultTr, hresultEq⟩

/-- Semantic core of the `Quot.ind` production branch.  As for
`quotientLiftMeaning`, Ix proves the exact source split, normalized constructor
shape, callback relation, and rebuilt suffix; the supplied law is purely a
Theory statement. -/
theorem quotientIndMeaning
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx} {prims : Primitives .anon}
    (theory : WhnfTheory trProj world uvars)
    (laws : QuotientReductionLaws world.venv)
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source : KExpr .anon} {sourceV : VExpr}
    {id : KId .anon} {us : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {args : Array (KExpr .anon)}
    {priorArgs laterArgs : List (KExpr .anon)} {priorV majorV : VExpr}
    {majorWhnf : KExpr .anon} {mkId : KId .anon}
    {mkUs : Array (KUniv .anon)} {mkInfo : ExprInfo .anon}
    {mkArgs : Array (KExpr .anon)} {result : KExpr .anon}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hind : id.addr = prims.quotInd.addr)
    (hargs : args.toList = priorArgs ++ args[4]! :: laterArgs)
    (hindex : 4 = priorArgs.length)
    (hprior : TrAppSpine world.venv uvars world.nameOf trProj Delta
      (.const id us headInfo) priorArgs priorV)
    (hthrough : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkApp
        (priorArgs.foldl KExpr.mkApp (.const id us headInfo)) args[4]!)
      (.app priorV majorV))
    (hsuffix : TrAppSuffix world.venv uvars world.nameOf trProj Delta
      (.app priorV majorV) laterArgs sourceV)
    (hmajorPost : WhnfPost trProj world uvars Delta majorV majorWhnf)
    (hmkSpine : majorWhnf.collectSpine =
      (.const mkId mkUs mkInfo, mkArgs))
    (hctor : mkId.addr = prims.quotCtor.addr)
    (hmkSize : mkArgs.size = 3)
    (hresult : result = laterArgs.foldl KExpr.mkApp
      (KExpr.mkApp args[3]! mkArgs[2]!)) :
    WhnfMeaning trProj world uvars Delta source result := by
  have hpriorLength : priorArgs.length = 4 := hindex.symm
  obtain ⟨arg0, arg1, arg2, fnArg, rfl⟩ :=
    list_eq_four_of_length hpriorLength
  obtain ⟨indHeadV, alpha, relation, motive, fn,
      hindHeadTr, _, _, _, hfnTr, hpriorShape⟩ := hprior.four
  have hindName : world.nameOf id.addr = some ``Quot.ind := by
    rw [hind]
    exact htable.quotInd.2
  have hindHead : indHeadV =
      .const ``Quot.ind (us.toList.map KUniv.toVLevel) :=
    Ix.Tc.RecM.TrKExprS.const_name hindHeadTr hindName
  rw [hindHead] at hpriorShape
  subst priorV

  have hargsSize : args.size = 5 + laterArgs.length := by
    have hlength := congrArg List.length hargs
    simp only [Array.length_toList, List.length_append, List.length_cons,
      List.length_nil] at hlength
    omega
  have hfnIndex : 3 < args.size := by omega
  have hfnArg : args[3]! = fnArg := by
    have hget : args.toList[3]? = some fnArg := by
      rw [hargs]
      rfl
    rw [Array.getElem?_toList,
      Array.getElem?_eq_getElem hfnIndex] at hget
    have heq := Option.some.inj hget
    simpa only [getElem!_pos args 3 hfnIndex] using heq

  obtain ⟨majorWhnfV, hmajorWhnfTr, hmajorEq⟩ := hmajorPost
  have hmkTyped := trAppSpine_of_collectSpine hmajorWhnfTr hmkSpine
  have hmkLength : mkArgs.toList.length = 3 := by simpa using hmkSize
  obtain ⟨ctorAlphaArg, ctorRelationArg, representativeArg, hmkList⟩ :=
    list_eq_three_of_length hmkLength
  rw [hmkList] at hmkTyped
  obtain ⟨mkHeadV, ctorAlpha, ctorRelation, representative,
      hmkHeadTr, _, _, hrepresentativeTr, hmkShape⟩ := hmkTyped.three
  have hmkName : world.nameOf mkId.addr = some ``Quot.mk := by
    rw [hctor]
    exact htable.quotCtor.2
  have hmkHead : mkHeadV =
      .const ``Quot.mk (mkUs.toList.map KUniv.toVLevel) :=
    Ix.Tc.RecM.TrKExprS.const_name hmkHeadTr hmkName
  rw [hmkHead] at hmkShape
  subst majorWhnfV

  have hrepresentativeIndex : 2 < mkArgs.size := by omega
  have hrepresentativeArg : mkArgs[2]! = representativeArg := by
    have hget : mkArgs.toList[2]? = some representativeArg := by
      rw [hmkList]
      rfl
    rw [Array.getElem?_toList,
      Array.getElem?_eq_getElem hrepresentativeIndex] at hget
    have heq := Option.some.inj hget
    simpa only [getElem!_pos mkArgs 2 hrepresentativeIndex] using heq

  have hredexWF : VExpr.WF world.venv uvars Delta.toCtx
      (.app
        (VExpr.appN
          (.const ``Quot.ind (us.toList.map KUniv.toVLevel))
          [alpha, relation, motive, fn])
        majorV) :=
    hthrough.wf world.venvWF.ordered theory.literalWF
      theory.projections.wf hDelta
  obtain ⟨domain, codomain, hfnType, hrepresentativeType, hreduce⟩ :=
    laws.ind world.venvWF hredexWF hmajorEq
  have hbaseTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkApp args[3]! mkArgs[2]!) (.app fn representative) := by
    rw [hfnArg, hrepresentativeArg, KExpr.mkApp_shape]
    exact .app hfnType hrepresentativeType hfnTr hrepresentativeTr
  obtain ⟨resultV, hresultTr, hresultEq⟩ :=
    hsuffix.rebase world.venvWF hDelta hbaseTr hreduce
  rw [← hresult] at hresultTr
  exact ⟨sourceV, resultV, hsource, hresultTr, hresultEq⟩

/-! ## Production success traces -/

/-- Exact dynamic trace of a successful selected quotient branch.  The trace
retains every effectful boundary; all spine tests between them are recorded
as equations against the actual callback result. -/
inductive QuotientSelectedSuccessTrace
    (methods : Methods .anon) (prims : Primitives .anon)
    (args : Array (KExpr .anon)) (fIdx majorIdx : Nat)
    (s : TcState .anon) : KExpr .anon → TcState .anon → Prop where
  | intro {majorWhnf : KExpr .anon} {afterWhnf afterBase : TcState .anon}
      {mkId : KId .anon} {mkUs : Array (KUniv .anon)}
      {mkInfo : ExprInfo .anon} {mkArgs : Array (KExpr .anon)}
      {base result : KExpr .anon} {sf : TcState .anon}
      (hcallback : (whnfRec args[majorIdx]!).run methods s =
        .ok majorWhnf afterWhnf)
      (hmkSpine : majorWhnf.collectSpine =
        (.const mkId mkUs mkInfo, mkArgs))
      (hctor : (mkId.addr != prims.quotCtor.addr) = false)
      (hsize : (mkArgs.size != 3) = false)
      (hintern : TcM.intern
        (KExpr.mkApp args[fIdx]! mkArgs[2]!) afterWhnf =
          .ok base afterBase)
      (hfinish : (finishAppResult base args (majorIdx + 1)).run methods
        afterBase = .ok result sf) :
      QuotientSelectedSuccessTrace methods prims args fIdx majorIdx s
        result sf

namespace QuotientSelectedSuccessTrace

/-- Invert a successful execution of the common production body into its
callback, constructor-recognition, and two intern phases. -/
theorem complete
    {methods : Methods .anon} {prims : Primitives .anon}
    {args : Array (KExpr .anon)} {fIdx majorIdx : Nat}
    {s sf : TcState .anon} {result : KExpr .anon}
    (hrun : (tryQuotReduceSelected prims args fIdx majorIdx).run methods s =
      .ok (some result) sf) :
    QuotientSelectedSuccessTrace methods prims args fIdx majorIdx s
      result sf := by
  unfold tryQuotReduceSelected at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((whnfRec args[majorIdx]!).run methods) _ s = _ at hrun
  unfold EStateM.bind at hrun
  match hcallback : (whnfRec args[majorIdx]!).run methods s with
  | .error err afterWhnf =>
      rw [hcallback] at hrun
      contradiction
  | .ok majorWhnf afterWhnf =>
      rw [hcallback] at hrun
      simp only at hrun
      generalize hmkSpine : majorWhnf.collectSpine = mkSpine at hrun
      rcases mkSpine with ⟨mkHead, mkArgs⟩
      cases mkHead with
      | const mkId mkUs mkInfo =>
          cases hctor : (mkId.addr != prims.quotCtor.addr) with
          | true =>
              simp only [hctor, if_true] at hrun
              cases hrun
          | false =>
              simp only [hctor, Bool.false_eq_true, if_false] at hrun
              cases hsize : (mkArgs.size != 3) with
              | true =>
                  simp only [hsize, if_true] at hrun
                  cases hrun
              | false =>
                  simp only [hsize, Bool.false_eq_true, if_false] at hrun
                  rw [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
                  change EStateM.bind (TcM.intern _) _ afterWhnf = _ at hrun
                  unfold EStateM.bind at hrun
                  match hintern : TcM.intern
                      (KExpr.mkApp args[fIdx]! mkArgs[2]!) afterWhnf with
                  | .error err afterBase =>
                      rw [hintern] at hrun
                      contradiction
                  | .ok base afterBase =>
                      rw [hintern] at hrun
                      simp only at hrun
                      rw [projectionDefinitionFinish_eq] at hrun
                      rw [ReaderT.run_bind] at hrun
                      change EStateM.bind
                        ((finishAppResult base args (majorIdx + 1)).run
                          methods) _ afterBase = _ at hrun
                      unfold EStateM.bind at hrun
                      match hfinish :
                          (finishAppResult base args (majorIdx + 1)).run
                            methods afterBase with
                      | .error err afterFinish =>
                          rw [hfinish] at hrun
                          contradiction
                      | .ok final afterFinish =>
                          rw [hfinish] at hrun
                          simp only at hrun
                          rcases hrun with ⟨rfl, rfl⟩
                          exact .intro hcallback hmkSpine hctor hsize
                            hintern hfinish
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          simp only at hrun
          cases hrun

/-- All semantic inputs recovered from a successful selected branch after Ix
has discharged its callback, finite-support, collision, and suffix-plan
obligations. -/
def SemanticInputs
    (trProj : RawProjRel) (world : VerifyWorld) (uvars : Nat)
    (Delta : KVLCtx) (prims : Primitives .anon)
    (sourceV : VExpr)
    (id : KId .anon) (us : Array (KUniv .anon))
    (headInfo : ExprInfo .anon) (args : Array (KExpr .anon))
    (fIdx majorIdx : Nat) (result : KExpr .anon) : Prop :=
  ∃ (priorArgs laterArgs : List (KExpr .anon)) (priorV majorV : VExpr)
      (majorWhnf : KExpr .anon) (mkId : KId .anon)
      (mkUs : Array (KUniv .anon)) (mkInfo : ExprInfo .anon)
      (mkArgs : Array (KExpr .anon)),
    args.toList = priorArgs ++ args[majorIdx]! :: laterArgs ∧
    majorIdx = priorArgs.length ∧
    TrAppSpine world.venv uvars world.nameOf trProj Delta
      (.const id us headInfo) priorArgs priorV ∧
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkApp
        (priorArgs.foldl KExpr.mkApp (.const id us headInfo))
        args[majorIdx]!) (.app priorV majorV) ∧
    TrAppSuffix world.venv uvars world.nameOf trProj Delta
      (.app priorV majorV) laterArgs sourceV ∧
    WhnfPost trProj world uvars Delta majorV majorWhnf ∧
    majorWhnf.collectSpine = (.const mkId mkUs mkInfo, mkArgs) ∧
    mkId.addr = prims.quotCtor.addr ∧
    mkArgs.size = 3 ∧
    result = laterArgs.foldl KExpr.mkApp
      (KExpr.mkApp args[fIdx]! mkArgs[2]!)

/-- Turn the dynamic trace into exact semantic inputs.  In particular, this
proves that collision-free interning returned the requested base expression
and that the production suffix loop returned the finite plan's pure fold. -/
theorem semanticInputs
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : QuotientReductionRequestCensus requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {flags : WhnfFlags} {mode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags mode)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    {id : KId .anon} {us : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {args : Array (KExpr .anon)}
    {fIdx majorIdx : Nat} {s sf : TcState .anon}
    {result : KExpr .anon}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars
      methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hspine : source.collectSpine = (.const id us headInfo, args))
    (hmajorIdx : majorIdx < args.size)
    (trace : QuotientSelectedSuccessTrace methods s.prims args fIdx
      majorIdx s result sf) :
    SemanticInputs trProj world uvars Delta s.prims sourceV id us
      headInfo args fIdx majorIdx result := by
  cases trace with
  | intro hcallback hmkSpine hctor hsize hintern hfinish =>
      have hmajorSupport : support args[majorIdx]! := by
        have hsupported :=
          (context.inputs.spine hsourceSupport hspine).2 majorIdx hmajorIdx
        simpa only [getElem!_pos args majorIdx hmajorIdx] using hsupported
      have hmajorGet : args[majorIdx]? = some args[majorIdx]! := by
        rw [getElem?_pos args majorIdx hmajorIdx,
          getElem!_pos args majorIdx hmajorIdx]
      have hmajorList : args.toList[majorIdx]? =
          some args[majorIdx]! := by
        rw [Array.getElem?_toList]
        exact hmajorGet
      have hspineTr := trAppSpine_of_collectSpine hsource hspine
      obtain ⟨priorArgs, laterArgs, priorV, majorV, hargs, hindex,
          hprior, _hmajor, hthrough, hsuffix⟩ :=
        hspineTr.splitAt hmajorList
      have hcallbackPost :=
        whnfRec_wf hmajorSupport _hmajor methods hmethods hI
      rw [hcallback] at hcallbackPost
      change WhnfStateInv .noAccel semantics trProj world support uvars
          Delta _ ∧ support _ ∧
          WhnfPost trProj world uvars Delta majorV _ at hcallbackPost
      obtain ⟨hbaseSupport, final, plan⟩ :=
        census.reduce (prims := s.prims) (fIdx := fIdx)
          (majorIdx := majorIdx) hsourceSupport hspine hmkSpine rfl
          hctor hsize
      obtain ⟨predictedBaseState, hinternExact, hIBase, _⟩ :=
        TcM.intern_whnf_eval context.collisionFree hbaseSupport
          hcallbackPost.1
      have hinternEq := hintern.symm.trans hinternExact
      cases hinternEq
      obtain ⟨predictedFinalState, hfinishExact, _hIFinal, _⟩ :=
        plan.eval hrun hIBase
      have hfinishEq := hfinish.symm.trans hfinishExact
      cases hfinishEq
      have hlater :
          (args.extract (majorIdx + 1) args.size).toList = laterArgs :=
        array_extract_after_split hargs hindex
      have hresult := plan.result_eq_foldl
      rw [hlater] at hresult
      exact ⟨priorArgs, laterArgs, priorV, majorV, _, _, _, _, _,
        hargs, hindex, hprior, hthrough, hsuffix, hcallbackPost.2.2,
        hmkSpine, bne_eq_false_iff_eq.mp hctor,
        bne_eq_false_iff_eq.mp hsize, hresult⟩

/-- A selected lift trace has the semantic meaning required by WHNF. -/
theorem liftMeaning
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : QuotientReductionRequestCensus requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {flags : WhnfFlags} {mode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags mode)
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (laws : QuotientReductionLaws world.venv)
    {Delta : KVLCtx} {methods : Methods .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    {id : KId .anon} {us : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {args : Array (KExpr .anon)}
    {s sf : TcState .anon} {result : KExpr .anon}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars
      methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hspine : source.collectSpine = (.const id us headInfo, args))
    (hlift : id.addr = s.prims.quotLift.addr)
    (hmajorIdx : 5 < args.size)
    (trace : QuotientSelectedSuccessTrace methods s.prims args 3 5 s
      result sf) :
    WhnfMeaning trProj world uvars Delta source result := by
  obtain ⟨priorArgs, laterArgs, priorV, majorV, majorWhnf, mkId, mkUs,
      mkInfo, mkArgs, hargs, hindex, hprior, hthrough, hsuffix,
      hmajorPost, hmkSpine, hctor, hmkSize, hresult⟩ :=
    trace.semanticInputs hrun census context hmethods hI hsourceSupport
      hsource hspine hmajorIdx
  exact quotientLiftMeaning theory laws (context.stateTable hI)
    context.quotientDefEq hI.2.1.wf hsource hlift hargs hindex hprior
    hthrough hsuffix hmajorPost hmkSpine hctor hmkSize hresult

/-- A selected induction trace has the semantic meaning required by WHNF. -/
theorem indMeaning
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : QuotientReductionRequestCensus requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {flags : WhnfFlags} {mode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags mode)
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (laws : QuotientReductionLaws world.venv)
    {Delta : KVLCtx} {methods : Methods .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    {id : KId .anon} {us : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {args : Array (KExpr .anon)}
    {s sf : TcState .anon} {result : KExpr .anon}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars
      methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hspine : source.collectSpine = (.const id us headInfo, args))
    (hind : id.addr = s.prims.quotInd.addr)
    (hmajorIdx : 4 < args.size)
    (trace : QuotientSelectedSuccessTrace methods s.prims args 3 4 s
      result sf) :
    WhnfMeaning trProj world uvars Delta source result := by
  obtain ⟨priorArgs, laterArgs, priorV, majorV, majorWhnf, mkId, mkUs,
      mkInfo, mkArgs, hargs, hindex, hprior, hthrough, hsuffix,
      hmajorPost, hmkSpine, hctor, hmkSize, hresult⟩ :=
    trace.semanticInputs hrun census context hmethods hI hsourceSupport
      hsource hspine hmajorIdx
  exact quotientIndMeaning theory laws (context.stateTable hI)
    hI.2.1.wf hsource hind hargs hindex hprior hthrough hsuffix
    hmajorPost hmkSpine hctor hmkSize hresult

end QuotientSelectedSuccessTrace

end RecM

namespace QuotientReductionReflection

/-- Construct the complete production reflection field from the narrow
Theory-only quotient laws.  Every successful run is inverted through the
actual primitive read, address route, arity guard, recursive callback,
constructor check, base intern, and trailing suffix loop. -/
theorem of_laws
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (run : RunAssumptions initial program requests support)
    (census : QuotientReductionRequestCensus requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {flags : WhnfFlags} {mode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags mode)
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (laws : QuotientReductionLaws world.venv) :
    QuotientReductionReflection semantics trProj world support := by
  constructor
  intro uvars Delta methods source result sourceV s sf hmethods
    hsourceSupport hsource hI hrun
  unfold RecM.tryQuotReduce at hrun
  generalize hspine : source.collectSpine = spine at hrun
  rcases spine with ⟨head, args⟩
  cases head with
  | const id us headInfo =>
      rw [ReaderT.run_bind] at hrun
      change EStateM.bind
        ((RecM.prims : RecM .anon (Primitives .anon)).run methods) _ s = _
        at hrun
      unfold EStateM.bind at hrun
      rw [RecM.prims_run] at hrun
      simp only at hrun
      cases hlift : (id.addr == s.prims.quotLift.addr) with
      | true =>
          simp only [hlift, if_true] at hrun
          by_cases hsmall : args.size < 6
          · simp only [hsmall, if_pos] at hrun
            cases hrun
          · simp only [hsmall, if_false] at hrun
            have hmajorIdx : 5 < args.size := by omega
            have trace :=
              RecM.QuotientSelectedSuccessTrace.complete hrun
            exact trace.liftMeaning run census context (theory uvars) laws
              hmethods hI hsourceSupport hsource hspine
              (beq_iff_eq.mp hlift) hmajorIdx
      | false =>
          simp only [hlift, Bool.false_eq_true, if_false] at hrun
          cases hind : (id.addr == s.prims.quotInd.addr) with
          | false =>
              simp only [hind, Bool.false_eq_true, if_false] at hrun
              cases hrun
          | true =>
              simp only [hind, if_true] at hrun
              by_cases hsmall : args.size < 5
              · simp only [hsmall, if_pos] at hrun
                cases hrun
              · simp only [hsmall, if_false] at hrun
                have hmajorIdx : 4 < args.size := by omega
                have trace :=
                  RecM.QuotientSelectedSuccessTrace.complete hrun
                exact trace.indMeaning run census context (theory uvars)
                  laws hmethods hI hsourceSupport hsource hspine
                  (beq_iff_eq.mp hind) hmajorIdx
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      simp only at hrun
      cases hrun

end QuotientReductionReflection
end Ix.Tc
