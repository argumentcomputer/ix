import Ix.CompileCert.Pj.InstalledHeaderSource
import IxC.Kernel.Verify.Inductives.FixRec
import IxC.Kernel.Verify.Inductives.StructRec
import IxC.Kernel.Verify.Extend.Inversions

/-!
The actual native recursor generator supplies the motive-domain match.

This leaf follows `structMotiveTyI` and `structRecTyR`: the stored former's
dependent domains are re-emitted verbatim while only the outer binder data
is reset. The Pj reader sees exactly those domains, so `matchMotive` is a
derived result for this real generator branch, not an added caller law.

The native generator spells the inductive's own formal universe parameters
in the motive. The identity-instantiation lemma below is used at that
actual stored spelling; this is not a restriction on semantic valuations
or on the arbitrary-universe lemmas in InstalledHeaderSource.
The general modeled/nested, export/family and recursive-header bridges
remain obligations. This additive source is UNCOMPILED.
-/

namespace Ix.CompileCert.Pj.GeneratedHeader

open InstalledHeader

/-- A proof-side view of the actual `replacePisPw` binder operation.
Only the outer datum changes; domain expressions (including their own
annotations) and their dependent order stay intact. -/
def resetOuter (pw : Kernel.PropWhen) (bs : Telescope) : Telescope :=
  bs.map fun b => (b.1, (⟨pw⟩ : Kernel.BinderMeta))

theorem lowerBVars_zero (e : Kernel.Expr) (cutoff : Nat) :
    e.lowerBVars 0 cutoff = e := by
  induction e generalizing cutoff <;>
    simp_all only [Kernel.Expr.lowerBVars, Nat.sub_zero, ite_self]

theorem stripAllPis_piJoin_sort (bs : Telescope) (s : Kernel.Level) :
    stripAllPis (piJoin bs (.sort s)) = (bs, .sort s) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨domain, meta⟩ := b
    simp only [piJoin, stripAllPis, ih]

theorem replacePisPw_piJoin (pw : Kernel.PropWhen) (bs : Telescope)
    (oldBody newBody : Kernel.Expr) :
    Kernel.Expr.replacePisPw pw bs.length (piJoin bs oldBody) newBody =
      some (piJoin (resetOuter pw bs) newBody) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨domain, meta⟩ := b
    simp only [List.length_cons, piJoin, Kernel.Expr.replacePisPw, ih,
      resetOuter, List.map_cons, Option.map_some]

/-- A reconstructed motive is read exactly at its real first-motive
position. No `Check`, well-scopedness or metadata premise is needed. -/
theorem readMotive_zero_type (np : Nat) (m : MotiveRd) :
    readMotive 0 (m.type np, m.binderMeta) = some m := by
  cases m
  simp only [readMotive, lowerBVars_zero, MotiveRd.type, MotiveRd.tele,
    stripAllPis_piJoin_sort, List.getLast?_concat, List.dropLast_concat,
    Option.bind_some, MotiveRd.majTy, Kernel.Expr.getAppFn_mkAppN,
    Kernel.Expr.getAppFn, Option.pure_def]

/-- The exact reader data of the native generator's first motive. -/
def nativeMotive (T : Kernel.Name) (lps : List Kernel.Name) (indices : Telescope)
    (level : Kernel.Level) (outer : Kernel.BinderMeta) : MotiveRd :=
  { ind := T, indUs := lps.map Kernel.Level.param,
    idxs := resetOuter .never indices, majMeta := ⟨.never⟩,
    sort := level, binderMeta := outer }

theorem structMotiveTyI_piJoin (T : Kernel.Name) (lps : List Kernel.Name)
    (np : Nat) (indices : Telescope) (level : Kernel.Level)
    (oldBody : Kernel.Expr) (outer : Kernel.BinderMeta) :
    Kernel.structMotiveTyI T lps np indices.length level (piJoin indices oldBody) =
      some ((nativeMotive T lps indices level outer).type np) := by
  simp only [Kernel.structMotiveTyI, replacePisPw_piJoin, nativeMotive,
    MotiveRd.type, MotiveRd.tele, piJoin_append, piJoin, MotiveRd.majTy,
    resetOuter, List.length_map, Kernel.structFamI, Kernel.structPsAt,
    bvarsAt, Nat.zero_add, Nat.add_zero]

/-- The generated motive's entire dependent-domain match succeeds at the
actual installed former. Arbitrary parameter annotations reset by the
outer recursor binder walk are accounted for, not equated to the former's. -/
theorem matchMotive_native {env : Kernel.Env} {cv : Kernel.ConstantVal}
    {caps : Kernel.IndCaps} (parameters indices : Telescope) (sort level : Kernel.Level)
    (pw : Kernel.PropWhen) (outer : Kernel.BinderMeta)
    (lookup : env.find? cv.name = some (.indInfo cv caps))
    (shape : cv.type = piJoin parameters (piJoin indices (.sort sort))) :
    matchMotive env (resetOuter pw parameters)
        (nativeMotive cv.name cv.levelParams indices level outer) =
      some ⟨parameters, indices, sort⟩ := by
  have parsed : read env (resetOuter pw parameters).length
      (nativeMotive cv.name cv.levelParams indices level outer) =
        some ⟨parameters, indices, sort⟩ := by
    simp only [read, nativeMotive, resetOuter, List.length_map, lookup,
      ite_eq_left (Eq.refl cv.levelParams.length), Kernel.Expr.instantiateLevelParams_self,
      shape, readType_piJoin]
  have domains : parameters.map Prod.fst = (resetOuter pw parameters).map Prod.fst ∧
      indices.map Prod.fst =
        (nativeMotive cv.name cv.levelParams indices level outer).idxs.map Prod.fst := by
    exact ⟨(List.map_map).symm, (List.map_map).symm⟩
  simpa only [matchMotive, parsed, ite_eq_left domains]

/-- The actual recursive generator places that motive immediately after
the same parameter domains. The rest of the recursor is the actual output
of its minor/major construction, with no restriction on the constructor list. -/
theorem structRecTyR_motive_prefix {T : Kernel.Name} {lps : List Kernel.Name}
    {elim : Kernel.Name} {large : Bool} {tty recTy : Kernel.Expr}
    {ctors : List (Kernel.Name × Nat × Kernel.Expr × List Nat)}
    (parameters indices : Telescope) (sort : Kernel.Level)
    (shape : tty = piJoin parameters (piJoin indices (.sort sort)))
    (generated : Kernel.structRecTyR T lps elim large parameters.length indices.length
      tty ctors = some recTy) :
    ∃ minors,
      recTy.stripPis parameters.length =
        some (resetOuter (Kernel.Level.zeronessOf (Kernel.structElimLevel elim large)) parameters,
          .forallE ((nativeMotive T lps indices (Kernel.structElimLevel elim large)
            ⟨Kernel.Level.zeronessOf (Kernel.structElimLevel elim large)⟩).type parameters.length)
            minors ⟨Kernel.Level.zeronessOf (Kernel.structElimLevel elim large)⟩) := by
  obtain ⟨tbs, itele, motiveTy, _major, minors, prefixRead, motive, _, _, rebuilt⟩ :=
    Kernel.structRecTyR_unfold generated
  have storedPrefix : tty.stripPis parameters.length =
      some (parameters, piJoin indices (.sort sort)) := by
    rw [shape]
    exact stripPis_piJoin _ _
  have pieces : (tbs, itele) = (parameters, piJoin indices (.sort sort)) :=
    Option.some.inj (prefixRead.symm.trans storedPrefix)
  have indexTele : itele = piJoin indices (.sort sort) := congrArg Prod.snd pieces
  rw [indexTele] at motive
  have motiveEq : motiveTy =
      (nativeMotive T lps indices (Kernel.structElimLevel elim large)
        ⟨Kernel.Level.zeronessOf (Kernel.structElimLevel elim large)⟩).type parameters.length :=
    Option.some.inj (motive.symm.trans (structMotiveTyI_piJoin T lps parameters.length
      indices (Kernel.structElimLevel elim large) (.sort sort) _))
  have actual := Kernel.replacePisPw_stripPis parameters.length rebuilt storedPrefix
  refine ⟨minors, ?_⟩
  simpa only [resetOuter, motiveEq] using actual

/-- In the actual generated prefix, both the motive read and the domain
match are derived. The caller supplies the stored former and generator
run, not either reader predicate. -/
theorem motive_match_of_structRecTyR {env : Kernel.Env} {cv : Kernel.ConstantVal}
    {caps : Kernel.IndCaps} {elim : Kernel.Name} {large : Bool} {recTy : Kernel.Expr}
    {ctors : List (Kernel.Name × Nat × Kernel.Expr × List Nat)}
    (parameters indices : Telescope) (sort : Kernel.Level)
    (lookup : env.find? cv.name = some (.indInfo cv caps))
    (shape : cv.type = piJoin parameters (piJoin indices (.sort sort)))
    (generated : Kernel.structRecTyR cv.name cv.levelParams elim large
      parameters.length indices.length cv.type ctors = some recTy) :
    ∃ minors m,
      recTy.stripPis parameters.length =
        some (resetOuter (Kernel.Level.zeronessOf (Kernel.structElimLevel elim large)) parameters,
          .forallE (m.type parameters.length) minors m.binderMeta) ∧
      readMotive 0 (m.type parameters.length, m.binderMeta) = some m ∧
      matchMotive env
        (resetOuter (Kernel.Level.zeronessOf (Kernel.structElimLevel elim large)) parameters) m =
          some ⟨parameters, indices, sort⟩ := by
  obtain ⟨minors, prefixRead⟩ := structRecTyR_motive_prefix parameters indices sort shape generated
  refine ⟨minors, nativeMotive cv.name cv.levelParams indices
    (Kernel.structElimLevel elim large)
    ⟨Kernel.Level.zeronessOf (Kernel.structElimLevel elim large)⟩, prefixRead, ?_, ?_⟩
  · exact readMotive_zero_type _ _
  · exact matchMotive_native parameters indices sort _ _ _ lookup shape

/-- The real constant checker supplies unchanged names/formals and
freshness of its OUTPUT name; no caller-side freshness law is assumed. -/
theorem checkedConstant_fields {mode : Kernel.CheckMode} {fuel : Nat}
    {env : Kernel.Env} {cv cvA : Kernel.ConstantVal}
    (accepted : Kernel.checkConstantVal (Kernel.fueledOps mode fuel) env cv = .ok cvA) :
    cvA.name = cv.name ∧ cvA.levelParams = cv.levelParams ∧ env.find? cvA.name = none := by
  obtain ⟨fresh, _, _, _, _, _, _type, _stype, _level, _, _, _, _, _, stored⟩ :=
    Kernel.checkConstantVal_inv accepted
  simpa only [stored] using (show cv.name = cv.name ∧ cv.levelParams = cv.levelParams ∧
    env.find? cv.name = none from ⟨rfl, rfl, fresh⟩)

/-- A list of constructor conses does not shadow a different name. This
internal structural lemma is consumed below with inequalities DERIVED
from every actual constructor check. -/
theorem consSumCtors_lookup_of_ne (np : Nat) (n : Kernel.Name) (ci : Kernel.ConstantInfo) :
    ∀ (cs : List (Kernel.ConstantVal × Nat)) (env : Kernel.Env),
      (∀ c ∈ cs, c.1.name ≠ n) → env.find? n = some ci →
      (Kernel.consSumCtors np cs env).find? n = some ci := by
  intro cs
  induction cs with
  | nil => intro env _ lookup; exact lookup
  | cons c cs ih =>
    intro env names lookup
    apply ih ⟨.ctorInfo c.1 np c.2 :: env.consts⟩
      (fun c' present => names c' (List.mem_cons_of_mem _ present))
    rw [Kernel.Env.find?_cons, if_neg (names c List.mem_cons_self)]
    exact lookup

/-- Every existing lookup survives the ACTUAL ordered constructor stage
and its conses. All constructor-output freshness facts are obtained from
the corresponding successful checks; duplicates or missing output entries
are not assumed away by a new premise. -/
theorem checkSumCtors_lookup {mode : Kernel.CheckMode} {fuel : Nat}
    {before env : Kernel.Env} {T : Kernel.Name} {lps : List Kernel.Name}
    {np ni : Nat} {sort : Kernel.Level} {isProp large : Bool} {cvT : Kernel.ConstantVal}
    {cs ctorsA : List (Kernel.ConstantVal × Nat)} {sortss : List (List Kernel.Level)}
    (accepted : Kernel.checkSumCtors (Kernel.fueledOps mode fuel) before env T lps np ni
      sort isProp large cvT cs = .ok (ctorsA, sortss))
    {n : Kernel.Name} {ci : Kernel.ConstantInfo} (lookup : env.find? n = some ci) :
    (Kernel.consSumCtors np ctorsA env).find? n = some ci := by
  obtain ⟨length, _, every⟩ := Kernel.checkSumCtors_inv accepted
  apply consSumCtors_lookup_of_ne np n ci ctorsA env ?_ lookup
  intro cA present equal
  obtain ⟨j, storedAt⟩ := List.getElem?_of_mem present
  have storedBound : j < ctorsA.length := (List.getElem?_eq_some_iff.mp storedAt).1
  have sourceBound : j < cs.length := by simpa only [length] using storedBound
  obtain ⟨_, _sorts, _, constructor⟩ :=
    every j cs[j] cA (List.getElem?_eq_getElem sourceBound) storedAt
  obtain ⟨_type, checked⟩ := (Kernel.checkSumCtor_shape constructor).1
  have fresh := (checkedConstant_fields checked).2.2
  rw [equal, lookup] at fresh
  exact nomatch fresh

/-- Exactly the recursor cons made in `checkNativeTail`, before the
optional structure projection-table stage. All rule fields are retained. -/
def nativeRecStore (env : Kernel.Env) (p : Kernel.NativeParts)
    (cvR : Kernel.ConstantVal) (ctors : List (Kernel.ConstantVal × Nat))
    (rhss : List Kernel.Expr) : Kernel.Env :=
  ⟨.recInfo cvR p.majorIdx p.rulePrefix
    (Kernel.sumRules env.find? cvR.name p.nP p.majorIdx p.rulePrefix cvR.type ctors rhss)
    :: env.consts⟩

/-- The real recursor check supplies freshness, so its exact installation
preserves every existing lookup without another caller assumption. -/
theorem checkNativeRec_lookup {mode : Kernel.CheckMode} {fuel : Nat}
    {env : Kernel.Env} {p : Kernel.NativeParts} {cvT cvR : Kernel.ConstantVal}
    {ctors : List (Kernel.ConstantVal × Nat)} {rhss : List Kernel.Expr}
    (accepted : Kernel.checkNativeRec (Kernel.fueledOps mode fuel) env p cvT ctors =
      .ok (cvR, rhss))
    {n : Kernel.Name} {ci : Kernel.ConstantInfo} (lookup : env.find? n = some ci) :
    (nativeRecStore env p cvR ctors rhss).find? n = some ci := by
  obtain ⟨_cvRi, _recTy, _sty, _level, checked, _, _, _, _, _, _, _, _, _, stored⟩ :=
    Kernel.checkNativeRec_shape accepted
  have fresh : env.find? cvR.name = none := by
    have original := (Kernel.checkConstantVal_inv checked).1
    simpa only [stored] using original
  exact Kernel.Env.find?_cons_of_fresh fresh lookup

/-- Actual native-pass and recursor-stage success supplies BOTH the stored
lookup and the complete generated motive-domain match. The existential
prefix is a prefix of the actual stored recursor type, not a reconstructed
alternative declaration. No reader-success, freshness, telescope-shape or
motive-domain predicate is supplied by the caller.

The conclusion is at the exact pre-projection-table store of the direct
route. Transport through the optional table and the general modeled/nested
source route remain separate original-domain obligations. -/
theorem motive_match_of_checked_native
    {mode : Kernel.CheckMode} {passFuel recFuel : Nat} {before : Kernel.Env}
    {p₀ : Kernel.NativeParts} {isRec settled : Bool} {q : Kernel.NativePass Kernel.Env}
    {cvR : Kernel.ConstantVal} {rhss : List Kernel.Expr}
    (passed : Kernel.checkNativePass (Kernel.fueledOps mode passFuel) before p₀ isRec =
      .ok (q, settled))
    (recursor : Kernel.checkNativeRec (Kernel.fueledOps mode recFuel)
      (Kernel.consSumCtors q.p.nP q.ctorsA q.env₁) q.p q.cvTa q.ctorsA = .ok (cvR, rhss)) :
    ∃ (parameters indices : Telescope) (sort : Kernel.Level) (minors : Kernel.Expr) (m : MotiveRd),
      parameters.length = q.p.nP ∧ indices.length = q.p.nIdx ∧
      cvR.type.stripPis q.p.nP =
        some (resetOuter (Kernel.Level.zeronessOf (Kernel.structElimLevel q.p.elim q.p.large))
          parameters, .forallE (m.type q.p.nP) minors m.binderMeta) ∧
      readMotive 0 (m.type q.p.nP, m.binderMeta) = some m ∧
      matchMotive
        (nativeRecStore (Kernel.consSumCtors q.p.nP q.ctorsA q.env₁) q.p cvR q.ctorsA rhss)
        (resetOuter (Kernel.Level.zeronessOf (Kernel.structElimLevel q.p.elim q.p.large))
          parameters) m = some ⟨parameters, indices, sort⟩ := by
  obtain ⟨p₁, kinds, former, constructors, _, record, _⟩ := Kernel.checkNativePass_inv passed
  obtain ⟨original, sort, sourceName, sourceLevels, checked, completed, environment,
      bs, storedSort⟩ := Kernel.checkSumInd_shape former
  have fields := checkedConstant_fields checked
  have name : q.p.cvT.name = q.cvTa.name := by
    rw [record]
    change p₁.cvT.name = q.cvTa.name
    rw [completed]
    exact (fields.1.trans sourceName).symm
  have levels : q.p.cvT.levelParams = q.cvTa.levelParams := by
    rw [record]
    change p₁.cvT.levelParams = q.cvTa.levelParams
    rw [completed]
    exact (fields.2.1.trans sourceLevels).symm
  have np : q.p.nP = p₀.nP := by
    simp only [record, Kernel.NativeParts.withKinds, Kernel.NativeParts.complete,
      completed, Kernel.InductiveShape.withSort]
  have ni : q.p.nIdx = p₀.nIdx := by
    simp only [record, Kernel.NativeParts.withKinds, Kernel.NativeParts.complete,
      completed, Kernel.InductiveShape.withSort]
  have formerLookup : q.env₁.find? q.cvTa.name =
      some (.indInfo q.cvTa (Kernel.nativeCapsAt p₁ isRec)) := by
    rw [environment]
    exact Kernel.Env.find?_cons_self _ _
  have constructorLookup : (Kernel.consSumCtors q.p.nP q.ctorsA q.env₁).find? q.cvTa.name =
      some (.indInfo q.cvTa (Kernel.nativeCapsAt p₁ isRec)) := by
    have preserved := checkSumCtors_lookup constructors formerLookup
    simpa only [record, Kernel.NativeParts.withKinds] using preserved
  have installedLookup := checkNativeRec_lookup recursor constructorLookup
  obtain ⟨_cvRi, recTy, _sty, _level, _, generated, _, _, _, _, _, _, _, _, recStored⟩ :=
    Kernel.checkNativeRec_shape recursor
  obtain ⟨header, parameterLength, indexLength⟩ := readType_of_stripSort storedSort
  let parameters := bs.take p₀.nP
  let indices := bs.drop p₀.nP
  have plen : parameters.length = q.p.nP := parameterLength.trans np.symm
  have ilen : indices.length = q.p.nIdx := indexLength.trans ni.symm
  have shape : q.cvTa.type = piJoin parameters (piJoin indices (.sort sort)) :=
    (readType_sound header).1
  have recType : cvR.type = recTy := congrArg Kernel.ConstantVal.type recStored
  have generated' : Kernel.structRecTyR q.cvTa.name q.cvTa.levelParams q.p.elim q.p.large
      parameters.length indices.length q.cvTa.type (Kernel.nativeCtors4 q.ctorsA q.p.kinds) =
        some cvR.type := by
    rw [plen, ilen, recType, ← name, ← levels]
    exact generated
  obtain ⟨minors, m, prefixRead, motiveRead, matched⟩ :=
    motive_match_of_structRecTyR parameters indices sort installedLookup shape generated'
  refine ⟨parameters, indices, sort, minors, m, plen, ilen, ?_, ?_, matched⟩
  · simpa only [plen] using prefixRead
  · simpa only [plen] using motiveRead

end Ix.CompileCert.Pj.GeneratedHeader

#print axioms Ix.CompileCert.Pj.GeneratedHeader.lowerBVars_zero
#print axioms Ix.CompileCert.Pj.GeneratedHeader.stripAllPis_piJoin_sort
#print axioms Ix.CompileCert.Pj.GeneratedHeader.replacePisPw_piJoin
#print axioms Ix.CompileCert.Pj.GeneratedHeader.readMotive_zero_type
#print axioms Ix.CompileCert.Pj.GeneratedHeader.structMotiveTyI_piJoin
#print axioms Ix.CompileCert.Pj.GeneratedHeader.matchMotive_native
#print axioms Ix.CompileCert.Pj.GeneratedHeader.structRecTyR_motive_prefix
#print axioms Ix.CompileCert.Pj.GeneratedHeader.motive_match_of_structRecTyR
#print axioms Ix.CompileCert.Pj.GeneratedHeader.checkedConstant_fields
#print axioms Ix.CompileCert.Pj.GeneratedHeader.consSumCtors_lookup_of_ne
#print axioms Ix.CompileCert.Pj.GeneratedHeader.checkSumCtors_lookup
#print axioms Ix.CompileCert.Pj.GeneratedHeader.checkNativeRec_lookup
#print axioms Ix.CompileCert.Pj.GeneratedHeader.motive_match_of_checked_native
