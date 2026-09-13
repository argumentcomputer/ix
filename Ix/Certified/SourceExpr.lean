/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Ixon

/-! Structural meaning of original Ixon expressions. References retain their
actual table positions and wrapper ownership; sharing expands only through
the original constant's sharing table. This relation has no typing premise. -/

namespace Ix.Certified

open Ix.Theory

def MemberMeaning (objects : Objects) (block : Address) (index : UInt64)
    (member : Ixon.MutConst) : Prop :=
  ∃ source members, lookup objects block = some source ∧ source.info = .muts members ∧
    members[index.toNat]? = some member

theorem mutMember_iff {objects : Objects} {block : Address} {index : UInt64} {member : Ixon.MutConst} :
    mutMember? objects block index = some member ↔ MemberMeaning objects block index member := by
  constructor
  · intro h
    unfold mutMember? at h
    cases hs : lookup objects block with
    | none => simp [hs] at h
    | some source =>
      cases hi : source.info <;> simp [hs, hi] at h
      exact ⟨source, _, hs, hi, h⟩
  · rintro ⟨source, members, hs, hi, hm⟩
    simp [mutMember?, hs, hi, hm]

def ReferenceTarget (objects : Objects) (address : Address) (source : Ixon.Constant)
    (ref : ConstRef Address) : Prop :=
  match source.info with
  | .defn _ | .recr _ | .axio _ | .quot _ => ref = .member address 0
  | .iPrj projection =>
    (∃ family, MemberMeaning objects projection.block projection.idx (.indc family)) ∧
      ref = .member projection.block projection.idx.toNat
  | .rPrj projection =>
    (∃ recursor, MemberMeaning objects projection.block projection.idx (.recr recursor)) ∧
      ref = .member projection.block projection.idx.toNat
  | .dPrj projection =>
    (∃ definition, MemberMeaning objects projection.block projection.idx (.defn definition)) ∧
      ref = .member projection.block projection.idx.toNat
  | .cPrj projection =>
    (∃ family ctor, MemberMeaning objects projection.block projection.idx (.indc family) ∧
      family.ctors[projection.cidx.toNat]? = some ctor) ∧
      ref = .ctor projection.block projection.idx.toNat projection.cidx.toNat
  | .muts _ => False

def ReferenceMeaning (objects : Objects) (address : Address) (ref : ConstRef Address) : Prop :=
  ∃ source, lookup objects address = some source ∧ ReferenceTarget objects address source ref

theorem resolveReference_iff {objects : Objects} {address : Address} {ref : ConstRef Address} :
    resolveReference? objects address = some ref ↔ ReferenceMeaning objects address ref := by
  cases hs : lookup objects address with
  | none => simp [resolveReference?, ReferenceMeaning, hs]
  | some source =>
    simp only [ReferenceMeaning, hs, Option.some.injEq]
    unfold resolveReference?
    simp only [hs, bind, Option.bind_some]
    unfold ReferenceTarget
    rcases source with ⟨info, sharing, references, universes⟩
    cases info
    all_goals dsimp only
    all_goals try solve | simp [eq_comm]
    all_goals simp only [← mutMember_iff]
    all_goals rename_i projection
    all_goals cases hm : mutMember? objects projection.block projection.idx with
    | none => simp [hm]
    | some member =>
      cases member <;> simp [hm, eq_comm, exists_and_left]

      all_goals rename_i family
      all_goals cases hf : family.ctors[projection.cidx.toNat]? <;> simp [eq_comm]

theorem ReferenceMeaning.unique {objects : Objects} {address : Address} {left right : ConstRef Address}
    (hl : ReferenceMeaning objects address left) (hr : ReferenceMeaning objects address right) : left = right :=
  Option.some.inj ((resolveReference_iff.mpr hl).symm.trans (resolveReference_iff.mpr hr))

def sourceLevelValue (levels : List Nat) : Ixon.Univ → Nat
  | .zero => 0
  | .succ level => sourceLevelValue levels level + 1
  | .max left right => max (sourceLevelValue levels left) (sourceLevelValue levels right)
  | .imax left right =>
    if sourceLevelValue levels right = 0 then 0 else max (sourceLevelValue levels left) (sourceLevelValue levels right)
  | .var index => levels.getD index.toNat 0

theorem readLevel_value (level : Ixon.Univ) (levels : List Nat) :
    (readLevel level).eval levels = sourceLevelValue levels level := by
  induction level <;> simp_all [readLevel, VLevel.eval, VLevel.natIMax, sourceLevelValue]

inductive LevelsReading (source : Ixon.Constant) : List UInt64 → List VLevel → Prop where
  | nil : LevelsReading source [] []
  | cons {index indices level levels} : source.univs[index.toNat]? = some level →
      LevelsReading source indices levels →
      LevelsReading source (index :: indices) (readLevel level :: levels)

theorem readLevelsList_sound {source : Ixon.Constant} {indices : List UInt64} {levels : List VLevel}
    (h : indices.mapM (fun index => (source.univs[index.toNat]?).map readLevel) = some levels) :
    LevelsReading source indices levels := by
  induction indices generalizing levels with
  | nil =>
    simp at h
    subst levels
    exact .nil
  | cons index indices ih =>
    cases hi : source.univs[index.toNat]? with
    | none => simp [List.mapM_cons, hi] at h
    | some level =>
      cases ht : indices.mapM (fun index => (source.univs[index.toNat]?).map readLevel) with
      | none => simp [List.mapM_cons, hi, ht] at h
      | some tail =>
        simp [List.mapM_cons, hi, ht] at h
        subst levels
        exact .cons hi (ih ht)

theorem readLevels_sound {source : Ixon.Constant} {indices : Array UInt64} {levels : List VLevel}
    (h : readLevels? source indices = some levels) : LevelsReading source indices.toList levels :=
  readLevelsList_sound h

theorem LevelsReading.unique {source : Ixon.Constant} {indices : List UInt64} {left right : List VLevel}
    (hl : LevelsReading source indices left) (hr : LevelsReading source indices right) : left = right := by
  induction hl generalizing right with
  | nil => cases hr; rfl
  | cons hs _ ih =>
    cases hr with
    | cons ht hr =>
      cases Option.some.inj (hs.symm.trans ht)
      exact congrArg (_ :: ·) (ih hr)

/-- A reading of the original source syntax, including all reference and
sharing-table lookups. Unsupported binder modes and literal forms have no
constructor in this relation. -/
inductive ExprReading (objects : Objects) (naturals : Naturals) (block : Address) (source : Ixon.Constant) :
    Ixon.Expr → VExpr Address → Prop where
  | var (index) : ExprReading objects naturals block source (.var index) (.bvar index.toNat)
  | sort {index level} : source.univs[index.toNat]? = some level →
      ExprReading objects naturals block source (.sort index) (.sort (readLevel level))
  | ref {index indices address ref levels} : source.refs[index.toNat]? = some address →
      ReferenceMeaning objects address ref → LevelsReading source indices.toList levels →
      ExprReading objects naturals block source (.ref index indices) (.const ref levels)
  | recur {index indices levels} : LevelsReading source indices.toList levels →
      ExprReading objects naturals block source (.recur index indices) (.const (.member block index.toNat) levels)
  | app {f a fr ar} : ExprReading objects naturals block source f fr →
      ExprReading objects naturals block source a ar →
      ExprReading objects naturals block source (.app f a) (.app fr ar)
  | lam {A b Ar br} : ExprReading objects naturals block source A Ar →
      ExprReading objects naturals block source b br →
      ExprReading objects naturals block source (.lam .many A b) (.lam Ar br)
  | all {A B Ar Br} : ExprReading objects naturals block source A Ar →
      ExprReading objects naturals block source B Br →
      ExprReading objects naturals block source (.all .many .shared A B) (.forallE Ar Br)
  | prj {owner field value address ownerSource projection ref reading} :
      source.refs[owner.toNat]? = some address → lookup objects address = some ownerSource →
      ownerSource.info = .iPrj projection → ReferenceMeaning objects address ref →
      ExprReading objects naturals block source value reading →
      ExprReading objects naturals block source (.prj owner field value) (.proj ref field.toNat reading)
  | nat {index address value} : source.refs[index.toNat]? = some address → lookup naturals address = some value →
      ExprReading objects naturals block source (.nat index) (.natLit value)
  | share {index shared reading} : source.sharing[index.toNat]? = some shared →
      ExprReading objects naturals block source shared reading →
      ExprReading objects naturals block source (.share index) reading

theorem readExpr_sound {fuel : Nat} {objects : Objects} {naturals : Naturals} {block : Address}
    {source : Ixon.Constant} {expression : Ixon.Expr} {reading : VExpr Address}
    (h : readExpr? fuel objects naturals block source expression = some reading) :
    ExprReading objects naturals block source expression reading := by
  induction fuel generalizing expression reading with
  | zero => simp [readExpr?] at h
  | succ fuel ih =>
    cases expression with
    | var index =>
      simp [readExpr?] at h
      subst reading
      exact .var index
    | sort index =>
      simp only [readExpr?, Option.map_eq_some_iff] at h
      obtain ⟨level, hl, rfl⟩ := h
      exact .sort hl
    | ref index indices =>
      simp only [readExpr?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨address, ha, ref, hr, levels, hl, rfl⟩ := h
      exact .ref ha (resolveReference_iff.mp hr) (readLevels_sound hl)
    | recur index indices =>
      simp only [readExpr?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨levels, hl, rfl⟩ := h
      exact .recur (readLevels_sound hl)
    | app f a =>
      simp only [readExpr?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨fr, hf, ar, ha, rfl⟩ := h
      exact .app (ih hf) (ih ha)
    | lam uses A b =>
      cases uses <;> simp only [readExpr?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      all_goals try contradiction
      obtain ⟨Ar, hA, br, hb, rfl⟩ := h
      exact .lam (ih hA) (ih hb)
    | all uses owned A B =>
      cases uses <;> cases owned <;>
        simp only [readExpr?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      all_goals try contradiction
      obtain ⟨Ar, hA, Br, hB, rfl⟩ := h
      exact .all (ih hA) (ih hB)
    | prj owner field value =>
      simp only [readExpr?, bind, Option.bind_eq_some_iff] at h
      obtain ⟨address, ha, ownerSource, hs, h⟩ := h
      cases hp : ownerSource.info <;> simp only [hp] at h
      all_goals try contradiction
      simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨ref, hr, reading, hv, rfl⟩ := h
      exact .prj ha hs hp (resolveReference_iff.mp hr) (ih hv)
    | nat index =>
      simp only [readExpr?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨address, ha, value, hv, rfl⟩ := h
      exact .nat ha hv
    | share index =>
      simp only [readExpr?, bind, Option.bind_eq_some_iff] at h
      obtain ⟨shared, hs, hr⟩ := h
      exact .share hs (ih hr)
    | str | letE => simp [readExpr?] at h

/-- The original tables determine one expanded expression. Neither fuel nor
a different sharing-expansion derivation can change the statement. -/
theorem ExprReading.unique {objects : Objects} {naturals : Naturals} {block : Address}
    {source : Ixon.Constant} {expression : Ixon.Expr} {left right : VExpr Address}
    (hl : ExprReading objects naturals block source expression left)
    (hr : ExprReading objects naturals block source expression right) : left = right := by
  induction hl generalizing right with
  | var => cases hr; rfl
  | sort hs =>
    cases hr with
    | sort ht => cases Option.some.inj (hs.symm.trans ht); rfl
  | ref ha hm hl =>
    cases hr with
    | ref hb hn hr =>
      cases Option.some.inj (ha.symm.trans hb)
      exact congr (congrArg VExpr.const (hm.unique hn)) (hl.unique hr)
  | recur hl =>
    cases hr with
    | recur hr => exact congrArg (VExpr.const _) (hl.unique hr)
  | app _ _ ihf iha =>
    cases hr with
    | app hf ha => exact congr (congrArg VExpr.app (ihf hf)) (iha ha)
  | lam _ _ ihA ihb =>
    cases hr with
    | lam hA hb => exact congr (congrArg VExpr.lam (ihA hA)) (ihb hb)
  | all _ _ ihA ihB =>
    cases hr with
    | all hA hB => exact congr (congrArg VExpr.forallE (ihA hA)) (ihB hB)
  | prj ha _ _ hm _ ih =>
    cases hr with
    | prj hb _ _ hn hv =>
      cases Option.some.inj (ha.symm.trans hb)
      exact congr (congrArg (fun r e => VExpr.proj r _ e) (hm.unique hn)) (ih hv)
  | nat ha hv =>
    cases hr with
    | nat hb hw =>
      cases Option.some.inj (ha.symm.trans hb)
      exact congrArg VExpr.natLit (Option.some.inj (hv.symm.trans hw))
  | share hs _ ih =>
    cases hr with
    | share ht hr =>
      cases Option.some.inj (hs.symm.trans ht)
      exact ih hr

theorem readExpr_fuel_independent {fuel₁ fuel₂ : Nat} {objects : Objects} {naturals : Naturals}
    {block : Address} {source : Ixon.Constant} {expression : Ixon.Expr} {left right : VExpr Address}
    (hl : readExpr? fuel₁ objects naturals block source expression = some left)
    (hr : readExpr? fuel₂ objects naturals block source expression = some right) : left = right :=
  (readExpr_sound hl).unique (readExpr_sound hr)

end Ix.Certified
