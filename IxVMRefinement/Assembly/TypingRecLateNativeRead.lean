import IxVMRefinement.StatementRel.LoadedReads
import IxVMRefinement.Ingress.ConvertExpr
import IxVMRefinement.Decl.Common
import IxCK.Kernel.Verify.InstLevels

/-! # Reading a recursor's expressions under its level parameters

The kernel reader reads an Ixon expression with a level-parameter naming `param`, which enters
only through the member's universe table (`src.univs.map (convUniv param)`). A recursor's
expressions are read with `recParam ps` (universe variable `i` is the `i`-th of its level
parameters `ps`), every other member's with `id` (universe variable `i` is the parameter `i`).
When `ps` is a permutation of the positions `0, …, ps.length - 1`, the two readings agree up to
the renaming `posOf ps` of the parameters to positions:

* `convUniv_recParam_invPos`, `subst_convUniv_recParam`: per universe, `posOf`'s substitution
  maps the reading under `recParam ps` to the reading under `id`;
* `convExpr_readPos`: per expression, against sharing tables related entrywise by the renaming
  (`readPos`), the reading under `id` is the renamed reading under `recParam ps`, errors
  included;
* `buildShareTbl_readPos`: the sharing tables are so related;
* `read_recParam_posOf`: a reading under `recParam ps` is renamed back to the reading under the
  positions;
* `read_recParam_scoped`: the scoping of a reading under `ps` (closed, level parameters among
  `ps`) follows from the scoping of the reading under the positions.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

namespace IxVM.Refinement.Typing

open IxVM.Consistency (exprReader readCtx)

/-! ## Universes -/

/-- The reading of a universe under `recParam ps` is the inverse renaming `invPosLevel ps` of its
reading under `id`. -/
theorem convUniv_recParam_invPos (ps : List Ix.Kernel.LevelParam) :
    ∀ u : Ixon.Univ, Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u =
      Ingress.invPosLevel ps (Ix.Kernel.Reader.convUniv id u)
  | .zero => rfl
  | .succ u => congrArg Ix.Kernel.Level.succ (convUniv_recParam_invPos ps u)
  | .max a b =>
    congrArg₂ Ix.Kernel.Level.max (convUniv_recParam_invPos ps a) (convUniv_recParam_invPos ps b)
  | .imax a b =>
    congrArg₂ Ix.Kernel.Level.imax (convUniv_recParam_invPos ps a)
      (convUniv_recParam_invPos ps b)
  | .var i => by
    show Ix.Kernel.Level.param (ps.getD i.toNat i.toNat) =
      Ingress.invPosLevel ps (Ix.Kernel.Level.param i.toNat)
    unfold Ingress.invPosLevel
    split
    · next hi =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] <;> rfl
    · next hi =>
      have hle : ps.length ≤ i.toNat := Nat.le_of_not_lt hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle] <;> rfl

/-- **Per universe**: for a permutation `ps` of the positions, `posOf ps`'s substitution maps the
reading under `recParam ps` to the reading under `id`. -/
theorem subst_convUniv_recParam {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (u : Ixon.Univ) :
    Ix.Kernel.Level.subst ps (Core.posLevels ps)
        (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u) =
      Ix.Kernel.Reader.convUniv id u := by
  rw [convUniv_recParam_invPos ps u]
  exact Ingress.subst_posLevels_invPosLevel hperm _

/-- The universe tables under `id` and under `recParam ps`, entrywise. -/
theorem univs_recParam {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (src : Ixon.Constant) (k : Nat) :
    (src.univs.map (Ix.Kernel.Reader.convUniv id))[k]? =
      ((src.univs.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)))[k]?).map
        (Ix.Kernel.Level.subst ps (Core.posLevels ps)) := by
  simp only [Array.getElem?_map]
  cases src.univs[k]? with
  | none => rfl
  | some u =>
    show some (Ix.Kernel.Reader.convUniv id u) =
      some (Ix.Kernel.Level.subst ps (Core.posLevels ps)
        (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u))
    rw [subst_convUniv_recParam hperm u]

/-! ## Expression contexts related by the renaming -/

/-- A reading renamed by `posOf ps` (errors kept). -/
def readPos (ps : List Ix.Kernel.LevelParam) (r : Ix.Kernel.Reader.ReadM Core.KExpr) :
    Ix.Kernel.Reader.ReadM Core.KExpr :=
  Core.posOf ps <$> r

/-- Two expression contexts that differ only in their universe tables, the second's levels
being the first's under `posOf ps`'s substitution. -/
structure ReadPosRel (ps : List Ix.Kernel.LevelParam) (ecx₁ ecx₂ : Ix.Kernel.Reader.ECx .anon) :
    Prop where
  hkey : ∀ i, ecx₂.keyAt i = ecx₁.keyAt i
  hblob : ∀ i, ecx₂.blobAt i = ecx₁.blobAt i
  hnat : ∀ i, ecx₂.natAt i = ecx₁.natAt i
  hself : ecx₂.self = ecx₁.self
  hlevel : ∀ i, ecx₂.level i = Ix.Kernel.Level.subst ps (Core.posLevels ps) <$> ecx₁.level i

theorem ecx_keyAt_univs (cx : Ix.Kernel.Reader.Ctx .anon) (src : Ixon.Constant)
    (U U' : Array Ix.Kernel.Level) (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
    (i : UInt64) :
    Ix.Kernel.Reader.ECx.keyAt (⟨cx, src, U, self⟩ : Ix.Kernel.Reader.ECx .anon) i =
      Ix.Kernel.Reader.ECx.keyAt (⟨cx, src, U', self⟩ : Ix.Kernel.Reader.ECx .anon) i := rfl

theorem ecx_blobAt_univs (cx : Ix.Kernel.Reader.Ctx .anon) (src : Ixon.Constant)
    (U U' : Array Ix.Kernel.Level) (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
    (i : UInt64) :
    Ix.Kernel.Reader.ECx.blobAt (⟨cx, src, U, self⟩ : Ix.Kernel.Reader.ECx .anon) i =
      Ix.Kernel.Reader.ECx.blobAt (⟨cx, src, U', self⟩ : Ix.Kernel.Reader.ECx .anon) i := rfl

theorem ecx_natAt_univs (cx : Ix.Kernel.Reader.Ctx .anon) (src : Ixon.Constant)
    (U U' : Array Ix.Kernel.Level) (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
    (i : UInt64) :
    Ix.Kernel.Reader.ECx.natAt (⟨cx, src, U, self⟩ : Ix.Kernel.Reader.ECx .anon) i =
      Ix.Kernel.Reader.ECx.natAt (⟨cx, src, U', self⟩ : Ix.Kernel.Reader.ECx .anon) i := rfl

/-- A universe-table lookup through an entrywise map of the tables. -/
theorem ecx_level_of_univs {ecx₁ ecx₂ : Ix.Kernel.Reader.ECx .anon}
    {g : Ix.Kernel.Level → Ix.Kernel.Level}
    (hu : ∀ k : Nat, ecx₂.univs[k]? = (ecx₁.univs[k]?).map g) (i : UInt64) :
    ecx₂.level i = g <$> ecx₁.level i := by
  unfold Ix.Kernel.Reader.ECx.level
  rw [hu i.toNat]
  cases ecx₁.univs[i.toNat]? <;> rfl

/-- The member contexts of the readings under `recParam ps` and under `id` are related. -/
theorem readPosRel_recParam {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (cx : Ix.Kernel.Reader.Ctx .anon)
    (src : Ixon.Constant) (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)) :
    ReadPosRel ps
      ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)), self⟩
      ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv id), self⟩ :=
  ⟨fun i => ecx_keyAt_univs cx src _ _ self i,
   fun i => ecx_blobAt_univs cx src _ _ self i,
   fun i => ecx_natAt_univs cx src _ _ self i,
   rfl,
   ecx_level_of_univs
     (ecx₁ := ⟨cx, src,
       src.univs.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)), self⟩)
     (ecx₂ := ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv id), self⟩)
     (univs_recParam hperm src)⟩

/-- A list of universe-table lookups through related contexts. -/
theorem levels_readPos {ps : List Ix.Kernel.LevelParam} {ecx₁ ecx₂ : Ix.Kernel.Reader.ECx .anon}
    (hlevel : ∀ i, ecx₂.level i = Ix.Kernel.Level.subst ps (Core.posLevels ps) <$> ecx₁.level i)
    (us : Array UInt64) :
    ecx₂.levels us =
      List.map (Ix.Kernel.Level.subst ps (Core.posLevels ps)) <$> ecx₁.levels us := by
  unfold Ix.Kernel.Reader.ECx.levels
  generalize us.toList = L
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.mapM_cons]
    rw [hlevel a, ih]
    cases Ix.Kernel.Reader.ECx.level ecx₁ a <;>
      cases List.mapM (Ix.Kernel.Reader.ECx.level ecx₁) L <;> rfl

theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl

/-! ## Expressions -/

/-- **Per expression**: against sharing tables related entrywise by the renaming, the reading
in the second context is the renamed reading in the first, errors included. -/
theorem convExpr_readPos {ps : List Ix.Kernel.LevelParam}
    {ecx₁ ecx₂ : Ix.Kernel.Reader.ECx .anon} (R : ReadPosRel ps ecx₁ ecx₂)
    (tbl : Array (Ix.Kernel.Reader.ReadM Core.KExpr)) :
    ∀ e : Ixon.Expr, Ix.Kernel.Reader.convExpr ecx₂ (tbl.map (readPos ps)) e =
      readPos ps (Ix.Kernel.Reader.convExpr ecx₁ tbl e) := by
  have hlevels := levels_readPos R.hlevel
  intro e
  induction e with
  | sort i =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [R.hlevel i]
    cases Ix.Kernel.Reader.ECx.level ecx₁ i <;> rfl
  | var i =>
    simp only [Ix.Kernel.Reader.convExpr, Ix.Kernel.Expr.mkBvar_eq] <;> rfl
  | ref i us =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [R.hkey i, hlevels us]
    cases Ix.Kernel.Reader.ECx.keyAt ecx₁ i <;>
      cases Ix.Kernel.Reader.ECx.levels ecx₁ us <;> rfl
  | recur i us =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [R.hself, hlevels us]
    cases Ix.Kernel.Reader.ECx.self ecx₁ i.toNat with
    | none => rfl
    | some n =>
      cases n <;> cases Ix.Kernel.Reader.ECx.levels ecx₁ us <;> rfl
  | prj i fld v ih =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [R.hkey i, ih]
    cases Ix.Kernel.Reader.ECx.keyAt ecx₁ i <;>
      cases Ix.Kernel.Reader.convExpr ecx₁ tbl v <;> rfl
  | str i =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [R.hblob i]
    cases Ix.Kernel.Reader.ECx.blobAt ecx₁ i with
    | error err => rfl
    | ok b =>
      simp only [except_ok_bind]
      cases String.fromUTF8? b <;> rfl
  | nat i =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [R.hnat i]
    cases Ix.Kernel.Reader.ECx.natAt ecx₁ i <;> rfl
  | app f a ihf iha =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [ihf, iha]
    cases Ix.Kernel.Reader.convExpr ecx₁ tbl f <;>
      cases Ix.Kernel.Reader.convExpr ecx₁ tbl a <;> rfl
  | lam t b iht ihb =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [iht, ihb]
    cases Ix.Kernel.Reader.convExpr ecx₁ tbl t <;>
      cases Ix.Kernel.Reader.convExpr ecx₁ tbl b <;> rfl
  | all t b iht ihb =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [iht, ihb]
    cases Ix.Kernel.Reader.convExpr ecx₁ tbl t <;>
      cases Ix.Kernel.Reader.convExpr ecx₁ tbl b <;> rfl
  | letE nd lm t v b iht ihv ihb =>
    simp only [Ix.Kernel.Reader.convExpr]
    rw [iht, ihv, ihb]
    cases Ix.Kernel.Reader.convExpr ecx₁ tbl t <;>
      cases Ix.Kernel.Reader.convExpr ecx₁ tbl v <;>
        cases Ix.Kernel.Reader.convExpr ecx₁ tbl b <;> rfl
  | share i =>
    simp only [Ix.Kernel.Reader.convExpr, Array.getElem?_map]
    cases tbl[i.toNat]? <;> rfl

/-- The sharing tables, from any related accumulators. -/
theorem buildShareTblGo_readPos {ps : List Ix.Kernel.LevelParam}
    {ecx₁ ecx₂ : Ix.Kernel.Reader.ECx .anon} (R : ReadPosRel ps ecx₁ ecx₂) :
    ∀ (es : List Ixon.Expr) (acc : Array (Ix.Kernel.Reader.ReadM Core.KExpr)),
      Ingress.buildShareTblGo ecx₂ (acc.map (readPos ps)) es =
        (Ingress.buildShareTblGo ecx₁ acc es).map (readPos ps) := by
  intro es
  induction es with
  | nil => intro acc; rfl
  | cons e es ih =>
    intro acc
    simp only [Ingress.buildShareTblGo]
    rw [convExpr_readPos R acc e, ← Array.map_push (f := readPos ps)]
    exact ih _

/-- **The sharing tables are related**: the table under the second context is the first's,
renamed entrywise. -/
theorem buildShareTbl_readPos {ps : List Ix.Kernel.LevelParam}
    {ecx₁ ecx₂ : Ix.Kernel.Reader.ECx .anon} (R : ReadPosRel ps ecx₁ ecx₂)
    (L : List Ixon.Expr) :
    Ingress.buildShareTbl ecx₂ L = (Ingress.buildShareTbl ecx₁ L).map (readPos ps) := by
  have h := buildShareTblGo_readPos R L #[]
  rw [Array.map_empty] at h
  exact h

/-- **The member reader under the positions is the renamed reader under `recParam ps`**, on every
expression, errors included. -/
theorem mk'_read_recParam {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (cx : Ix.Kernel.Reader.Ctx .anon)
    (src : Ixon.Constant) (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
    (e : Ixon.Expr) :
    (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read e =
      readPos ps
        ((Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read e) := by
  obtain ⟨he₁, ht₁⟩ := Ingress.memberReader_mk'_eq cx src (Ix.Kernel.Reader.recParam ps) self
  obtain ⟨he₂, ht₂⟩ := Ingress.memberReader_mk'_eq cx src id self
  have R := readPosRel_recParam hperm cx src self
  unfold Ix.Kernel.Reader.MemberReader.read
  rw [he₁, ht₁, he₂, ht₂, buildShareTbl_readPos R]
  exact convExpr_readPos R _ e

/-- Reading under a recursor's level parameters `ps` (a permutation of the positions) is
reading under the positions, renamed back by `posOf ps`. -/
theorem read_recParam_posOf {t : Ix.Kernel.RoleTable} {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ps : List Ix.Kernel.LevelParam} (hperm : ps.Perm (List.range ps.length))
    {e : Ixon.Expr} {E : Ix.Kernel.Expr .anon}
    (h : (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read e = .ok E) :
    (exprReader t blob src id self).read e = .ok (Core.posOf ps E) := by
  have h2 := mk'_read_recParam hperm (readCtx t blob) src self e
  have h' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam ps) self).read e = .ok E := h
  rw [h'] at h2
  exact h2

/-- The scoping of a reading under `ps` from the scoping of the reading under the positions. -/
theorem read_recParam_scoped {t : Ix.Kernel.RoleTable} {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) {e : Ixon.Expr} {E E₀ : Ix.Kernel.Expr .anon}
    (h : (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read e = .ok E)
    (h₀ : (exprReader t blob src id self).read e = .ok E₀)
    (hlbb : E₀.looseBVarsBounded 0 = true)
    (hdef : E₀.allLevelParamsDefined (List.range ps.length) = true) :
    E.looseBVarsBounded 0 = true ∧ E.allLevelParamsDefined ps = true := by
  have h1 := h₀.symm.trans (read_recParam_posOf hperm h)
  cases h1
  exact ⟨(Ix.Kernel.Expr.looseBVarsBounded_instantiateLevelParams ps (Core.posLevels ps)
      E 0).symm.trans hlbb,
    Decl.allLevelParamsDefined_of_posOf_perm hperm hdef⟩

end IxVM.Refinement.Typing
