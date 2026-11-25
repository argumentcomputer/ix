import IxCCGrounding.PcProp

/-!
# `Lit.str` denotation, adequacy, and string-widened root soundness (`IxCCGrounding.StrLit`, G4)

This module widens `IxCCGrounding` to support `String` literals (`Term.strLit`, `Value.str`,
`Literal.strVal`, `Obs.bytes`) directly over `Ix.Kernel.Model`, without modifying the landed
`corrSB` / `groundCheck` / `groundCheckW` / `groundCheckWP` deciders (preserving all existing
decline-corpus test assertions):

1. **`StrBasis` & `strBasisB`**: verifies that the 7 string-literal role constants (`String`,
   `String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat`) plus `NatBasis` are
   stored with the exact types checked by `Ix.Kernel.strLitSupported`.
2. **Model denotation & membership (`str_den`, `str_mem`, `strSet_indep`)**: proves that in every
   `Ix.Kernel.Model V env` satisfying `StrBasis env`, `.lit (.strVal s)` denotes `strSet M φ s`
   (the constructor form `String.ofList [Char.ofNat c₀, …]`), lies in `M.cval stringName φ`, and is
   independent of the level assignment `φ`.
3. **Readback & UTF-8 injectivity (`readback_str`, `str_toUTF8_toList_inj`)**: proves that
   `Obs.bytes s.toUTF8.toList` uniquely identifies `.str s`.
4. **String-admitting check (`corrStrSB`, `groundCheckStrWPP`) & root soundness
   (`rootSound_678AGpStrWPP_of_check`)**: widens `corrSB` to admit `.strLit s ↔ .lit (.strVal s)`
   into `TermCorrS.strLit` / `Runs.strLit`, and extends first-order root types to `FoTyStr`
   (`Nat`, `String`, enumerations), proving full end-to-end root soundness with words,
   `PUnit.casesOn` at ordinary & `Prop` instances, and `String` literals directly over
   `Ix.Kernel.Model`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Result)

universe w

/-! ## `StrBasis`: the stored string-literal basis -/

/-- The kernel environment stores the `Nat` basis and the 7 string-literal role constants
(`String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat`) at the shapes
checked by `Ix.Kernel.strLitSupported`. -/
structure StrBasis (env : KEnv) : Prop where
  nat : NatBasis env
  string : ∃ ci : ConstantInfo .anon, env.find? stringName = some ci ∧
    ci.toConstantVal.levelParams = [] ∧ ci.toConstantVal.type = .sort (.succ .zero)
  char : ∃ ci : ConstantInfo .anon, env.find? charName = some ci ∧
    ci.toConstantVal.levelParams = [] ∧ ci.toConstantVal.type = .sort (.succ .zero)
  charOfNat : ∃ (ci : ConstantInfo .anon) (mb : BinderMeta),
    env.find? charOfNatName = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type = .forallE (.const natName []) (.const charName []) mb
  list : ∃ (ci : ConstantInfo .anon) (p : LevelParam) (mb : BinderMeta),
    env.find? listName = some ci ∧ ci.toConstantVal.levelParams = [p] ∧
    ci.toConstantVal.type = .forallE (.sort (.succ (.param p))) (.sort (.succ (.param p))) mb
  listNil : ∃ (ci : ConstantInfo .anon) (p : LevelParam) (mb : BinderMeta),
    env.find? listNilName = some ci ∧ ci.toConstantVal.levelParams = [p] ∧
    ci.toConstantVal.type =
      .forallE (.sort (.succ (.param p))) (.app (.const listName [.param p]) (.bvar 0)) mb
  listCons : ∃ (ci : ConstantInfo .anon) (p : LevelParam) (mb1 mb2 mb3 : BinderMeta),
    env.find? listConsName = some ci ∧ ci.toConstantVal.levelParams = [p] ∧
    ci.toConstantVal.type =
      .forallE (.sort (.succ (.param p)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const listName [.param p]) (.bvar 1))
            (.app (.const listName [.param p]) (.bvar 2)) mb3) mb2) mb1
  stringOfList : ∃ (ci : ConstantInfo .anon) (mb : BinderMeta),
    env.find? stringOfListName = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type =
      .forallE (.app (.const listName [.zero]) (.const charName [])) (.const stringName []) mb

/-- Decidable check for `StrBasis env`: `natBasisB` plus the kernel's `strLitSupported`. -/
def strBasisB (env : KEnv) : Bool :=
  natBasisB env && strLitSupported env

/-- **`strBasisB` is sound.** -/
theorem strBasis_of_check {env : KEnv} (h : strBasisB env = true) : StrBasis env := by
  simp only [strBasisB, strLitSupported, Bool.and_eq_true] at h
  obtain ⟨hNat, ⟨⟨⟨⟨⟨⟨⟨_, hStr⟩, hSOL⟩, hList⟩, hNil⟩, hCons⟩, hChar⟩, hCON⟩⟩ := h
  refine ⟨natBasis_of hNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hf : env.find? stringName with
    | none => simp [stringTyOk, hf] at hStr
    | some ci =>
      simp only [stringTyOk, hf, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hStr
      exact ⟨ci, rfl, hStr.1, hStr.2⟩
  · cases hf : env.find? charName with
    | none => simp [charTyOk, hf] at hChar
    | some ci =>
      simp only [charTyOk, hf, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hChar
      exact ⟨ci, rfl, hChar.1, hChar.2⟩
  · cases hf : env.find? charOfNatName with
    | none => simp [charOfNatTyOk, hf] at hCON
    | some ci =>
      simp only [charOfNatTyOk, hf, Bool.and_eq_true, List.isEmpty_iff] at hCON
      obtain ⟨hlp, hty⟩ := hCON
      cases ht : ci.toConstantVal.type with
      | forallE d b mb =>
        rw [ht] at hty
        cases d with
        | const c1 us1 =>
          cases us1 with
          | nil =>
            cases b with
            | const c2 us2 =>
              cases us2 with
              | nil =>
                simp only [Bool.and_eq_true, beq_iff_eq] at hty
                exact ⟨ci, mb, rfl, hlp, by rw [ht, hty.1, hty.2]⟩
              | cons _ _ => simp at hty
            | _ => simp at hty
          | cons _ _ => simp at hty
        | _ => simp at hty
      | _ => rw [ht] at hty; simp at hty
  · cases hf : env.find? listName with
    | none => simp [listTyOk, hf] at hList
    | some ci =>
      simp only [listTyOk, hf] at hList
      cases hlp : ci.toConstantVal.levelParams with
      | nil => rw [hlp] at hList; cases hList
      | cons p rest =>
        cases rest with
        | cons _ _ => rw [hlp] at hList; cases hList
        | nil =>
          rw [hlp] at hList
          cases ht : ci.toConstantVal.type with
          | forallE d b mb =>
            rw [ht] at hList
            cases d with
            | sort u1 =>
              cases b with
              | sort u2 =>
                simp only [Bool.and_eq_true, beq_iff_eq] at hList
                exact ⟨ci, p, mb, rfl, hlp, by rw [ht, hList.1, hList.2]⟩
              | _ => simp at hList
            | _ => simp at hList
          | _ => rw [ht] at hList; cases hList
  · cases hf : env.find? listNilName with
    | none => simp [listNilTyOk, hf] at hNil
    | some ci =>
      simp only [listNilTyOk, hf] at hNil
      cases hlp : ci.toConstantVal.levelParams with
      | nil => rw [hlp] at hNil; cases hNil
      | cons p rest =>
        cases rest with
        | cons _ _ => rw [hlp] at hNil; cases hNil
        | nil =>
          rw [hlp] at hNil
          cases ht : ci.toConstantVal.type with
          | forallE d b mb =>
            rw [ht] at hNil
            cases d with
            | sort u1 =>
              cases b with
              | app f a =>
                cases f with
                | const l1 us1 =>
                  cases a with
                  | bvar i =>
                    cases i with
                    | zero =>
                      simp only [Bool.and_eq_true, beq_iff_eq] at hNil
                      exact ⟨ci, p, mb, rfl, hlp, by rw [ht, hNil.1.1, hNil.1.2, hNil.2]⟩
                    | succ _ => simp at hNil
                  | _ => simp at hNil
                | _ => simp at hNil
              | _ => simp at hNil
            | _ => simp at hNil
          | _ => rw [ht] at hNil; cases hNil
  · cases hf : env.find? listConsName with
    | none => simp [listConsTyOk, hf] at hCons
    | some ci =>
      simp only [listConsTyOk, hf] at hCons
      cases hlp : ci.toConstantVal.levelParams with
      | nil => rw [hlp] at hCons; cases hCons
      | cons p rest =>
        cases rest with
        | cons _ _ => rw [hlp] at hCons; cases hCons
        | nil =>
          rw [hlp] at hCons
          cases ht : ci.toConstantVal.type with
          | forallE d1 b1 mb1 =>
            rw [ht] at hCons
            cases d1 with
            | sort u1 =>
              cases b1 with
              | forallE d2 b2 mb2 =>
                cases d2 with
                | bvar i0 =>
                  cases i0 with
                  | zero =>
                    cases b2 with
                    | forallE d3 b3 mb3 =>
                      cases d3 with
                      | app f1 a1 =>
                        cases f1 with
                        | const l1 us1 =>
                          cases a1 with
                          | bvar i1 =>
                            cases i1 with
                            | zero => simp at hCons
                            | succ i1' =>
                              cases i1' with
                              | zero =>
                                cases b3 with
                                | app f2 a2 =>
                                  cases f2 with
                                  | const l2 us2 =>
                                    cases a2 with
                                    | bvar i2 =>
                                      cases i2 with
                                      | zero => simp at hCons
                                      | succ i2' =>
                                        cases i2' with
                                        | zero => simp at hCons
                                        | succ i2'' =>
                                          cases i2'' with
                                          | zero =>
                                            simp only [Bool.and_eq_true, beq_iff_eq] at hCons
                                            obtain ⟨⟨⟨⟨hu1, hl1⟩, hl2⟩, hus1⟩, hus2⟩ := hCons
                                            exact ⟨ci, p, mb1, mb2, mb3, rfl, hlp, by
                                              rw [ht, hu1, hl1, hl2, hus1, hus2]⟩
                                          | succ _ => simp at hCons
                                    | _ => simp at hCons
                                  | _ => simp at hCons
                                | _ => simp at hCons
                              | succ _ => simp at hCons
                          | _ => simp at hCons
                        | _ => simp at hCons
                      | _ => simp at hCons
                    | _ => simp at hCons
                  | succ _ => simp at hCons
                | _ => simp at hCons
              | _ => simp at hCons
            | _ => simp at hCons
          | _ => rw [ht] at hCons; cases hCons
  · cases hf : env.find? stringOfListName with
    | none => simp [stringOfListTyOk, hf] at hSOL
    | some ci =>
      simp only [stringOfListTyOk, hf, Bool.and_eq_true, List.isEmpty_iff] at hSOL
      obtain ⟨hlp, hty⟩ := hSOL
      cases ht : ci.toConstantVal.type with
      | forallE d b mb =>
        rw [ht] at hty
        cases d with
        | app f a =>
          cases f with
          | const l1 us1 =>
            cases a with
            | const c1 us2 =>
              cases us2 with
              | nil =>
                cases b with
                | const c2 us3 =>
                  cases us3 with
                  | nil =>
                    simp only [Bool.and_eq_true, beq_iff_eq] at hty
                    obtain ⟨⟨⟨hl1, hus1⟩, hc1⟩, hc2⟩ := hty
                    exact ⟨ci, mb, rfl, hlp, by rw [ht, hl1, hus1, hc1, hc2]⟩
                  | cons _ _ => simp at hty
                | _ => simp at hty
              | cons _ _ => simp at hty
            | _ => simp at hty
          | _ => simp at hty
        | _ => simp at hty
      | _ => rw [ht] at hty; simp at hty

/-! ## Model denotation and membership for `Lit.str` -/

/-- Recursive expression form of the character list in `strLitToConstructor`. -/
def strListE : List Char → KExpr
  | [] => .app (.const listNilName [.zero]) (.const charName [])
  | c :: cs =>
    .app (.app (.app (.const listConsName [.zero]) (.const charName []))
      (.app (.const charOfNatName []) (.lit (.natVal c.toNat))))
      (strListE cs)

theorem strListE_foldr : ∀ cs : List Char,
    cs.foldr
      (fun c (e : KExpr) =>
        .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e)
      (.app (.const listNilName [.zero]) (.const charName [])) = strListE cs
  | [] => rfl
  | c :: cs => by rw [List.foldr_cons, strListE_foldr cs, strListE]

theorem strLitToConstructor_eq_strListE (s : String) :
    (strLitToConstructor (md := .anon)) s =
      .app (.const stringOfListName []) (strListE s.toList) := by
  unfold strLitToConstructor
  rw [strListE_foldr s.toList]

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- The model element of a character `c : Char` (`Char.ofNat (lit c.toNat)`). -/
noncomputable def charSet (M : Model V env) (φ : LevelParam → Nat) (c : Char) : V :=
  app (M.cval charOfNatName φ) (litSet M φ c.toNat)

/-- The model element of a character list (`List.nil Char` / `List.cons Char (charSet c) ...`). -/
noncomputable def strListSet (M : Model V env) (φ : LevelParam → Nat) : List Char → V
  | [] => app (M.cval listNilName (fun _ => 0)) (M.cval charName φ)
  | c :: cs =>
    app (app (app (M.cval listConsName (fun _ => 0)) (M.cval charName φ))
      (charSet M φ c)) (strListSet M φ cs)

/-- The model element of a string literal (`String.ofList (strListSet s.toList)`). -/
noncomputable def strSet (M : Model V env) (φ : LevelParam → Nat) (s : String) : V :=
  app (M.cval stringOfListName φ) (strListSet M φ s.toList)

/-- A constant with a single level parameter `[p]`, instantiated at `[.zero]`, denotes
`M.cval n (fun _ => 0)` (by `CvalParams`). -/
theorem den_const_zero1 {M : Model V env} (hcv : CvalParams M) {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {n : KKey} {ci : ConstantInfo .anon} {p : LevelParam} {X : V}
    (hf : env.find? n = some ci) (hl : ci.toConstantVal.levelParams = [p]) :
    Denotes M.cval env φ ρ (.const n [.zero]) X ↔ X = M.cval n (fun _ => 0) := by
  have heq : M.cval n (Level.substFn φ [p] [.zero]) = M.cval n (fun _ => 0) :=
    hcv n ci hf _ _ fun q hq => by
      rw [hl, List.mem_singleton] at hq
      subst hq
      simp [Level.substFn, Level.eval]
  constructor
  · intro h
    cases h with
    | const hf' _ =>
      rw [hf] at hf'; cases hf'
      rw [hl]
      exact heq
  · rintro rfl
    rw [← heq]
    have h' := Denotes.const (cval := M.cval) (env := env) (φ := φ) (ρ := ρ) (us := [.zero])
      hf (by rw [hl]; rfl)
    rwa [hl] at h'

theorem char_den (M : Model V env) (hS : StrBasis env) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (c : Char) (X : V) :
    Denotes M.cval env φ ρ (.app (.const charOfNatName []) (.lit (.natVal c.toNat))) X ↔
      X = charSet M φ c := by
  obtain ⟨ci, _, hf, hlp, _⟩ := hS.charOfNat
  have hF := natFacts M hS.nat φ
  rw [den_app]
  constructor
  · rintro ⟨F, A, hF', hA', rfl⟩
    rw [(den_const0 hf hlp).mp hF', (lit_den M hF ρ c.toNat A).mp hA']
    rfl
  · rintro rfl
    exact ⟨_, _, (den_const0 hf hlp).mpr rfl, (lit_den M hF ρ c.toNat _).mpr rfl, rfl⟩

theorem strList_den (M : Model V env) (hcv : CvalParams M) (hS : StrBasis env)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∀ (cs : List Char) (X : V),
      Denotes M.cval env φ ρ (strListE cs) X ↔ X = strListSet M φ cs
  | [], X => by
    obtain ⟨ciN, pN, _, hfN, hlpN, _⟩ := hS.listNil
    obtain ⟨ciC, hfC, hlpC, _⟩ := hS.char
    simp only [strListE, strListSet, den_app]
    constructor
    · rintro ⟨F, A, hF, hA, rfl⟩
      rw [(den_const_zero1 hcv hfN hlpN).mp hF, (den_const0 hfC hlpC).mp hA]
    · rintro rfl
      exact ⟨_, _, (den_const_zero1 hcv hfN hlpN).mpr rfl, (den_const0 hfC hlpC).mpr rfl, rfl⟩
  | c :: cs, X => by
    obtain ⟨ciK, pK, _, _, _, hfK, hlpK, _⟩ := hS.listCons
    obtain ⟨ciC, hfC, hlpC, _⟩ := hS.char
    rw [strListE, strListSet]
    constructor
    · intro h
      obtain ⟨F3, A3, hF3, hA3, rfl⟩ := den_app.mp h
      obtain ⟨F2, A2, hF2, hA2, rfl⟩ := den_app.mp hF3
      obtain ⟨F1, A1, hF1, hA1, rfl⟩ := den_app.mp hF2
      rw [(den_const_zero1 hcv hfK hlpK).mp hF1, (den_const0 hfC hlpC).mp hA1,
        (char_den M hS φ ρ c A2).mp hA2, (strList_den M hcv hS φ ρ cs A3).mp hA3]
    · rintro rfl
      exact .app (.app (.app ((den_const_zero1 hcv hfK hlpK).mpr rfl)
        ((den_const0 hfC hlpC).mpr rfl)) ((char_den M hS φ ρ c _).mpr rfl))
        ((strList_den M hcv hS φ ρ cs _).mpr rfl)

/-- **A `String` literal denotes `strSet M φ s`** in every `Ix.Kernel.Model` satisfying
`StrBasis env`, in every variable environment `ρ`. -/
theorem str_den (M : Model V env) (hcv : CvalParams M) (hS : StrBasis env)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) (s : String) (X : V) :
    Denotes M.cval env φ ρ (.lit (.strVal s)) X ↔ X = strSet M φ s := by
  obtain ⟨ciS, _, hfS, hlpS, _⟩ := hS.stringOfList
  constructor
  · intro h
    cases h with
    | strLit h' =>
      rw [strLitToConstructor_eq_strListE, den_app] at h'
      obtain ⟨F, A, hF, hA, rfl⟩ := h'
      rw [(den_const0 hfS hlpS).mp hF, (strList_den M hcv hS φ ρ s.toList A).mp hA]
      rfl
  · rintro rfl
    refine .strLit ?_
    rw [strLitToConstructor_eq_strListE]
    exact .app ((den_const0 hfS hlpS).mpr rfl) ((strList_den M hcv hS φ ρ s.toList _).mpr rfl)

/-- Every character element lies in `Char`. -/
theorem char_mem (M : Model V env) (hS : StrBasis env) (φ : LevelParam → Nat) (c : Char) :
    charSet M φ c ∈ˢ M.cval charName φ := by
  obtain ⟨ci, mb, hf, _, hty⟩ := hS.charOfNat
  obtain ⟨ciC, hfC, hlpC, _⟩ := hS.char
  have hF := natFacts M hS.nat φ
  obtain ⟨T, hT, hm⟩ := mem_key M hf φ (fun _ => empty)
  rw [hty] at hT
  obtain ⟨B, hB, hmem⟩ :=
    app_mem_den_pi hT ((hF.natD _ _).mpr rfl) hm (lit_mem M hF c.toNat)
  rwa [(den_const0 hfC hlpC).mp hB] at hmem

/-- `Char` lies in `univ 1` (`Type 0`). -/
theorem char_mem_univ1 (M : Model V env) (hS : StrBasis env) (φ : LevelParam → Nat) :
    M.cval charName φ ∈ˢ (univ 1 : V) := by
  obtain ⟨ciC, hfC, _, htyC⟩ := hS.char
  obtain ⟨T, hT, hm⟩ := mem_key M hfC φ (fun _ => empty)
  rw [htyC] at hT
  have hTe := den_sort.mp hT
  simpa [Level.eval] using hTe ▸ hm

/-- Every character-list element lies in `List.{0} Char`. -/
theorem strList_mem (M : Model V env) (hcv : CvalParams M) (hS : StrBasis env)
    (φ : LevelParam → Nat) :
    ∀ cs : List Char,
      strListSet M φ cs ∈ˢ app (M.cval listName (fun _ => 0)) (M.cval charName φ)
  | [] => by
    obtain ⟨ciN, pN, mbN, hfN, hlpN, htyN⟩ := hS.listNil
    obtain ⟨ciL, pL, _, hfL, hlpL, _⟩ := hS.list
    have hChar1 := char_mem_univ1 M hS φ
    obtain ⟨T, hT, hm⟩ := mem_key M hfN (fun _ => 0) (fun _ => empty)
    rw [htyN] at hT
    have hU : Denotes M.cval env (fun _ => 0) (fun _ => empty) (.sort (.succ (.param pN))) (univ 1) := by
      rw [den_sort]; simp [Level.eval]
    obtain ⟨B, hB, hmem⟩ := app_mem_den_pi hT hU hm hChar1
    rw [den_app] at hB
    obtain ⟨FL, AL, hFL, hAL, rfl⟩ := hB
    have hFLe : FL = M.cval listName (fun _ => 0) := by
      cases hFL with
      | const hfL' _ =>
        rw [hfL] at hfL'; cases hfL'
        exact hcv listName ciL hfL _ _ fun q hq => by
          rw [hlpL, List.mem_singleton] at hq; subst hq
          rw [hlpL]; simp [Level.substFn, Level.eval]
    have hALe : AL = M.cval charName φ := den_bvar.mp hAL
    rw [hFLe, hALe] at hmem
    exact hmem
  | c :: cs => by
    obtain ⟨ciK, pK, mb1, mb2, mb3, hfK, hlpK, htyK⟩ := hS.listCons
    obtain ⟨ciL, pL, _, hfL, hlpL, _⟩ := hS.list
    have hChar1 := char_mem_univ1 M hS φ
    have hcm := char_mem M hS φ c
    have hcsm := strList_mem M hcv hS φ cs
    obtain ⟨T, hT, hm⟩ := mem_key M hfK (fun _ => 0) (fun _ => empty)
    rw [htyK] at hT
    have hU : Denotes M.cval env (fun _ => 0) (fun _ => empty) (.sort (.succ (.param pK))) (univ 1) := by
      rw [den_sort]; simp [Level.eval]
    obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hT hU hm hChar1
    obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 .bvar hm1 hcm
    have hListChar : ∀ (i : Nat) (ρ' : BVarIdx → V), ρ' i = M.cval charName φ →
        Denotes M.cval env (fun _ => 0) ρ' (.app (.const listName [.param pK]) (.bvar i))
          (app (M.cval listName (fun _ => 0)) (M.cval charName φ)) := by
      intro i ρ' hi
      refine .app ?_ (den_bvar.mpr hi.symm)
      have hconst := Denotes.const (cval := M.cval) (env := env) (φ := fun _ => 0) (ρ := ρ')
        (us := [.param pK]) hfL (by rw [hlpL]; rfl)
      have heq : M.cval listName (Level.substFn (fun _ => 0) ciL.toConstantVal.levelParams [.param pK]) =
          M.cval listName (fun _ => 0) :=
        hcv listName ciL hfL _ _ fun q hq => by
          rw [hlpL, List.mem_singleton] at hq; subst hq
          rw [hlpL]; simp [Level.substFn, Level.eval]
      rwa [heq] at hconst
    obtain ⟨B3, hB3, hm3⟩ :=
      app_mem_den_pi hB2 (hListChar 1 _ rfl) hm2 hcsm
    have hB3e := Denotes_functional hB3 (hListChar 2 _ rfl)
    rw [hB3e] at hm3
    exact hm3

/-- **Every string literal's denotation lies in `String`.** -/
theorem str_mem (M : Model V env) (hcv : CvalParams M) (hS : StrBasis env)
    (φ : LevelParam → Nat) (s : String) :
    strSet M φ s ∈ˢ M.cval stringName φ := by
  obtain ⟨ciS, mbS, hfS, _, htyS⟩ := hS.stringOfList
  obtain ⟨ciL, pL, _, hfL, hlpL, _⟩ := hS.list
  obtain ⟨ciC, hfC, hlpC, _⟩ := hS.char
  obtain ⟨ciStr, hfStr, hlpStr, _⟩ := hS.string
  obtain ⟨T, hT, hm⟩ := mem_key M hfS φ (fun _ => empty)
  rw [htyS] at hT
  have hDom : Denotes M.cval env φ (fun _ => empty)
      (.app (.const listName [.zero]) (.const charName []))
      (app (M.cval listName (fun _ => 0)) (M.cval charName φ)) :=
    .app ((den_const_zero1 hcv hfL hlpL).mpr rfl) ((den_const0 hfC hlpC).mpr rfl)
  obtain ⟨B, hB, hmem⟩ := app_mem_den_pi hT hDom hm (strList_mem M hcv hS φ s.toList)
  rwa [(den_const0 hfStr hlpStr).mp hB] at hmem

/-- `charSet` is independent of the level assignment `φ`. -/
theorem charSet_indep (M : Model V env) (hcv : CvalParams M) (hS : StrBasis env)
    (φ ψ : LevelParam → Nat) (c : Char) : charSet M φ c = charSet M ψ c := by
  obtain ⟨ci, _, hf, hlp, _⟩ := hS.charOfNat
  have h1 : M.cval charOfNatName φ = M.cval charOfNatName ψ :=
    hcv charOfNatName ci hf φ ψ fun p hp => by rw [hlp] at hp; cases hp
  have h2 : litSet M φ c.toNat = litSet M ψ c.toNat := litSet_indep_cv M hcv hS.nat φ ψ c.toNat
  simp only [charSet, h1, h2]

/-- `strListSet` is independent of the level assignment `φ`. -/
theorem strListSet_indep (M : Model V env) (hcv : CvalParams M) (hS : StrBasis env)
    (φ ψ : LevelParam → Nat) : ∀ cs : List Char, strListSet M φ cs = strListSet M ψ cs
  | [] => by
    obtain ⟨ciC, hfC, hlpC, _⟩ := hS.char
    have hC : M.cval charName φ = M.cval charName ψ :=
      hcv charName ciC hfC φ ψ fun p hp => by rw [hlpC] at hp; cases hp
    simp only [strListSet, hC]
  | c :: cs => by
    obtain ⟨ciC, hfC, hlpC, _⟩ := hS.char
    have hC : M.cval charName φ = M.cval charName ψ :=
      hcv charName ciC hfC φ ψ fun p hp => by rw [hlpC] at hp; cases hp
    simp only [strListSet, hC, charSet_indep M hcv hS φ ψ c, strListSet_indep M hcv hS φ ψ cs]

/-- **`strSet` is independent of the level assignment `φ`.** -/
theorem strSet_indep (M : Model V env) (hcv : CvalParams M) (hS : StrBasis env)
    (φ ψ : LevelParam → Nat) (s : String) : strSet M φ s = strSet M ψ s := by
  obtain ⟨ci, _, hf, hlp, _⟩ := hS.stringOfList
  have h1 : M.cval stringOfListName φ = M.cval stringOfListName ψ :=
    hcv stringOfListName ci hf φ ψ fun p hp => by rw [hlp] at hp; cases hp
  simp only [strSet, h1, strListSet_indep M hcv hS φ ψ s.toList]

/-- A `Value.str s` related by `RelV` relates to `strSet M φ s`. -/
theorem relV_str_eq {M : Model V env} {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {S : CId → Prop} {Ok : CId → Levels → Prop} (hcv : CvalParams M) (hS : StrBasis env)
    (φ : LevelParam → Nat) {s : String} {X : V} (h : RelV M p κ lpsOf S Ok (.str s) X) :
    X = strSet M φ s := by
  cases h with
  | @str _ _ ψ ρ hden =>
    rw [(str_den M hcv hS ψ ρ s X).mp hden]
    exact strSet_indep M hcv hS ψ φ s

/-- Introducing `RelV` for `Value.str s`. -/
theorem relV_str_intro {M : Model V env} {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {S : CId → Prop} {Ok : CId → Levels → Prop} (hcv : CvalParams M) (hS : StrBasis env)
    (φ : LevelParam → Nat) (s : String) :
    RelV M p κ lpsOf S Ok (.str s) (strSet M φ s) :=
  .str ((str_den M hcv hS φ (fun _ => empty) s _).mpr rfl)

end Sem

/-! ## Readback and UTF-8 injectivity -/

private theorem byteArray_toList_loop (bs : ByteArray) :
    ∀ (k i : Nat) (r : List UInt8), bs.size - i = k →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i
  | 0, i, r, h => by
    unfold ByteArray.toList.loop
    rw [ite_eq_right (show ¬ i < bs.size by omega)]
    rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; change bs.size ≤ i; omega),
      List.append_nil]
  | k + 1, i, r, h => by
    have hi : i < bs.size := by omega
    unfold ByteArray.toList.loop
    rw [ite_eq_left hi, byteArray_toList_loop bs k (i + 1) _ (by omega),
      List.drop_eq_getElem_cons (i := i) (by rw [Array.length_toList]; exact hi)]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    congr 2
    simp [ByteArray.get!, getElem!_pos bs.data i hi]

theorem byteArray_toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [byteArray_toList_loop bs _ 0 [] rfl]
  simp

/-- UTF-8 byte list representation is injective on `String`. -/
theorem str_toUTF8_toList_inj {s₁ s₂ : String} (h : s₁.toUTF8.toList = s₂.toUTF8.toList) :
    s₁ = s₂ := by
  rw [byteArray_toList_eq_data, byteArray_toList_eq_data] at h
  have hd : s₁.toUTF8.data = s₂.toUTF8.data := Array.toList_inj.mp h
  have hba : s₁.toByteArray = s₂.toByteArray := by
    cases h1 : s₁.toByteArray
    cases h2 : s₂.toByteArray
    have : s₁.toUTF8 = s₁.toByteArray := rfl
    have : s₂.toUTF8 = s₂.toByteArray := rfl
    simp_all
  exact String.toByteArray_inj.mp hba

/-- If `readbackAll` observes `.bytes bs`, the value is `.str s` with `s.toUTF8.toList = bs`. -/
theorem readback_str {p : Program} {v : Value} {bs : List UInt8}
    (h : IxCC.Src.readbackAll p v = some (.bytes bs)) :
    ∃ s : String, v = .str s ∧ s.toUTF8.toList = bs := by
  cases v with
  | str s =>
    simp only [IxCC.Src.readbackAll, IxCC.Src.readback, Option.some.injEq,
      IxCC.Sem.Obs.bytes.injEq] at h
    exact ⟨s, rfl, h⟩
  | con c ls ps fs =>
    simp only [IxCC.Src.readbackAll, IxCC.Src.readback] at h
    cases hf : IxCC.Src.readbackFields p (fun _ _ _ => true) c ls 0 fs <;> simp [hf] at h
  | _ => simp [IxCC.Src.readbackAll, IxCC.Src.readback] at h

/-! ## String-admitting correspondence check (`corrStrSB`, `groundCheckStrWPP`) -/

/-- `corrSB` widened to admit string literals `.strLit s ↔ .lit (.strVal s)` (without changing
`corrSB` itself, preserving all existing decline-corpus test assertions). -/
def corrStrSB (κ : CId → KKey) (lps : List Nat) : Sig → Term → KExpr → Bool
  | σ, .var i, e => match σ[i]? with | some (some e') => decide (e' = e) | _ => false
  | _, .sort u, .sort l => univCorrB lps u l
  | _, .const c us, .const k ls =>
    decide (k = κ c) && us.length == ls.length && (us.zip ls).all fun (u, l) => univCorrB lps u l
  | σ, .app f a _ _, .app f' a' => corrStrSB κ lps σ f f' && corrStrSB κ lps σ a a'
  | σ, .lam _ d b, .lam d' b' _ => corrStrSB κ lps σ d d' && corrStrSB κ lps (liftσ σ) b b'
  | σ, .pi _ d c, .forallE d' c' _ => corrStrSB κ lps σ d d' && corrStrSB κ lps (liftσ σ) c c'
  | σ, .proj s i x, .proj k j x' => decide (k = κ s) && i == j && corrStrSB κ lps σ x x'
  | _, .natLit n, .lit (.natVal m) => n == m
  | _, .strLit s, .lit (.strVal s') => s == s'
  | σ, .letE _ _ _ _ v b, e =>
    match zcopy b e with
    | some v' =>
      (if subAt0B v' e then corrStrSB κ lps σ v v'
        else if cloShapeB b e v' then
          corrStrSB κ lps (σ.map (·.map (Expr.liftLooseBVars 1 0))) v (v'.liftLooseBVars 1 0)
        else
          match witSite? b e with
          | some (Δ, cp) => corrStrSB κ lps (σ.map (·.map (Expr.liftLooseBVars Δ.length 0))) v cp
          | none => false) &&
        corrStrSB κ lps (some v' :: σ) b e
    | none => corrStrSB κ lps (none :: σ) b e
  | _, _, _ => false

/-- **`corrStrSB` is sound** for `TermCorrS` (including `.strLit`). -/
theorem termCorrS_of_corrStrSB {κ : CId → KKey} {lps : List Nat} :
    ∀ (σ : Sig) (t : Term) (e : KExpr), corrStrSB κ lps σ t e = true → TermCorrS κ lps σ t e := by
  intro σ t
  induction t generalizing σ with
  | var i =>
    intro e h
    simp only [corrStrSB] at h
    split at h
    · rename_i e' he
      simp only [decide_eq_true_eq] at h
      subst h
      exact .var he
    · cases h
  | sort u =>
    intro e h; cases e <;> simp [corrStrSB] at h; exact .sort (univCorr_of_check _ _ h)
  | const c us =>
    intro e h
    cases e <;> simp only [corrStrSB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.all_eq_true, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, hlen⟩, hall⟩ := h
    refine .const hlen fun i u l hu hl => univCorr_of_check _ _ ?_
    exact hall (u, l) (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hu, hl⟩))
  | app f a m r ihf iha =>
    intro e h; cases e <;> simp [corrStrSB] at h; exact .app (ihf _ _ h.1) (iha _ _ h.2)
  | lam b d body ihd ihb =>
    intro e h; cases e <;> simp [corrStrSB] at h; exact .lam (ihd _ _ h.1) (ihb _ _ h.2)
  | pi b d c ihd ihc =>
    intro e h; cases e <;> simp [corrStrSB] at h; exact .pi (ihd _ _ h.1) (ihc _ _ h.2)
  | letE nonDep m r ty v b _ ihv ihb =>
    intro e h
    simp only [corrStrSB] at h
    split at h
    · rename_i v' hz
      simp only [Bool.and_eq_true] at h
      obtain ⟨hv, hb⟩ := h
      cases hsub : subAt0B v' e
      · simp only [hsub, Bool.false_eq_true, ↓reduceIte] at hv
        cases hcs : cloShapeB b e v'
        · simp only [hcs, Bool.false_eq_true, ↓reduceIte] at hv
          cases hws : witSite? b e with
          | none => rw [hws] at hv; cases hv
          | some p =>
            simp only [hws] at hv
            obtain ⟨Δ, cp⟩ := p
            obtain ⟨v1, hz1, _, _, hcp, _, _⟩ := witSite?_spec hws
            rw [hz] at hz1
            cases hz1
            subst hcp
            exact .letWit hz hws (ihv _ _ hv) (ihb _ _ hb)
        · simp only [hcs, ↓reduceIte] at hv
          cases b with
          | lam bz d body =>
            cases e with
            | lam A b' mb =>
              simp only [cloShapeB] at hcs
              exact .letClo hz hsub hcs (ihv _ _ hv) (ihb _ _ hb)
            | _ => simp [cloShapeB] at hcs
          | _ => simp [cloShapeB] at hcs
      · simp only [hsub, ↓reduceIte] at hv
        exact .letLive hz hsub (ihv _ _ hv) (ihb _ _ hb)
    · rename_i hz
      exact .letDead hz (ihb _ _ h)
  | proj s i x ih =>
    intro e h
    cases e <;> simp only [corrStrSB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.false_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, hx⟩ := h
    exact .proj (ih _ _ hx)
  | natLit n =>
    intro e h
    cases e with
    | lit l => cases l <;> simp [corrStrSB] at h; subst h; exact .natLit
    | _ => simp [corrStrSB] at h
  | strLit s =>
    intro e h
    cases e with
    | lit l => cases l <;> simp [corrStrSB] at h; subst h; exact .strLit
    | _ => simp [corrStrSB] at h

def eqnCorrStrB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat) (c : CId) :
    Bool :=
  match p.table.resolveOf c with
  | some (.eqn thm body) =>
    match eqnData? env (κ c) (κ thm) with
    | some d => corrStrSB κ (lpsOf c) [] body d.body
    | none => false
  | _ => true

def valueCorrStrB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat) (c : CId) :
    Bool :=
  match p.table.resolveOf c, p.decl? c, env.find? (κ c) with
  | none, some (.defn .defn .safe _ _ v), some (.defnInfo _ val _) =>
    corrStrSB κ (lpsOf c) [] v val
  | _, _, _ => true

/-- **The string-widened Pc-Prop conjuncts**: `checkPartsWP` with `"eqnCorr"` and `"valueCorr"`
checked by `corrStrSB`. -/
def checkPartsStrWP (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : List (String × Bool) :=
  (checkPartsWP p env κ lpsOf ann Sl).map fun nb =>
    if nb.1 = "eqnCorr" then ("eqnCorrStr", Sl.all (eqnCorrStrB p env κ lpsOf))
    else if nb.1 = "valueCorr" then ("valueCorrStr", Sl.all (valueCorrStrB p env κ lpsOf))
    else nb

/-- **The string-widened Pc-Prop check**: `checkPartsStrWP` plus `punitSortB` on `Sl`. -/
def groundCheckStrWPP (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  (checkPartsStrWP p env κ lpsOf ann Sl).all (·.2) && Sl.all (punitSortB p env κ)

section StrCheck

variable {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat}
  {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}

theorem mem_checkPartsStrWP {name : String} {b : Bool}
    (hm : (name, b) ∈ checkParts p env κ lpsOf ann Sl)
    (hn : name ≠ "noWord" ∧ name ≠ "caseRec" ∧ name ≠ "caseShape" ∧
      name ≠ "eqnCorr" ∧ name ≠ "valueCorr") :
    (name, b) ∈ checkPartsStrWP p env κ lpsOf ann Sl := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hn
  exact List.mem_map.mpr ⟨(name, b), mem_checkPartsWP hm ⟨h1, h2, h3⟩, by simp [h4, h5]⟩

theorem sansKS_of_checkStrWPP (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    CheckSansKS p env κ lpsOf ann Sl := by
  have h1 := (Bool.and_eq_true _ _ ▸ h).1
  exact fun _ _ hm hn => List.all_eq_true.mp h1 _ (mem_checkPartsStrWP hm hn)

theorem word_of_checkStrWPP (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    wordB p env κ lpsOf Sl = true := by
  have h1 := (Bool.and_eq_true _ _ ▸ h).1
  have hmWP : ("word", wordB p env κ lpsOf Sl) ∈ checkPartsWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("word", wordB p env κ lpsOf Sl),
      List.mem_map.mpr ⟨("noWord", Sl.all (noWordB p)), by simp [checkParts, checkPartsWith],
        by simp⟩, by simp⟩
  have hm : ("word", wordB p env κ lpsOf Sl) ∈ checkPartsStrWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("word", wordB p env κ lpsOf Sl), hmWP, by simp⟩
  exact List.all_eq_true.mp h1 _ hm

theorem caseRecP_of_checkStrWPP (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    ∀ c, c ∈ Sl → caseRecPB p env κ ann Sl c = true := by
  have h1 := (Bool.and_eq_true _ _ ▸ h).1
  have hmWP : ("caseRecP", Sl.all (caseRecPB p env κ ann Sl)) ∈ checkPartsWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("caseRec", Sl.all (caseRecB p env κ)),
      List.mem_map.mpr ⟨("caseRec", Sl.all (caseRecB p env κ)), by simp [checkParts, checkPartsWith],
        by simp⟩, by simp⟩
  have hm : ("caseRecP", Sl.all (caseRecPB p env κ ann Sl)) ∈ checkPartsStrWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("caseRecP", Sl.all (caseRecPB p env κ ann Sl)), hmWP, by simp⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp h1 _ hm)

theorem caseShapeP_of_checkStrWPP (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    ∀ c, c ∈ Sl → caseShapePB p env κ c = true := by
  have h1 := (Bool.and_eq_true _ _ ▸ h).1
  have hmWP : ("caseShapeP", Sl.all (caseShapePB p env κ)) ∈ checkPartsWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("caseShape", Sl.all (caseShapeB p env κ)),
      List.mem_map.mpr ⟨("caseShape", Sl.all (caseShapeB p env κ)),
        by simp [checkParts, checkPartsWith], by simp⟩, by simp⟩
  have hm : ("caseShapeP", Sl.all (caseShapePB p env κ)) ∈ checkPartsStrWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("caseShapeP", Sl.all (caseShapePB p env κ)), hmWP, by simp⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp h1 _ hm)

theorem eqnCorrStr_of_checkStrWPP (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    ∀ c, c ∈ Sl → eqnCorrStrB p env κ lpsOf c = true := by
  have h1 := (Bool.and_eq_true _ _ ▸ h).1
  have hmWP : ("eqnCorr", Sl.all (eqnCorrB p env κ lpsOf)) ∈ checkPartsWP p env κ lpsOf ann Sl :=
    mem_checkPartsWP (by simp [checkParts, checkPartsWith]) (by decide)
  have hm : ("eqnCorrStr", Sl.all (eqnCorrStrB p env κ lpsOf)) ∈
      checkPartsStrWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("eqnCorr", Sl.all (eqnCorrB p env κ lpsOf)), hmWP, by simp⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp h1 _ hm)

theorem valueCorrStr_of_checkStrWPP (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    ∀ c, c ∈ Sl → valueCorrStrB p env κ lpsOf c = true := by
  have h1 := (Bool.and_eq_true _ _ ▸ h).1
  have hmWP : ("valueCorr", Sl.all (valueCorrB p env κ lpsOf)) ∈ checkPartsWP p env κ lpsOf ann Sl :=
    mem_checkPartsWP (by simp [checkParts, checkPartsWith]) (by decide)
  have hm : ("valueCorrStr", Sl.all (valueCorrStrB p env κ lpsOf)) ∈
      checkPartsStrWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("valueCorr", Sl.all (valueCorrB p env κ lpsOf)), hmWP, by simp⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp h1 _ hm)

theorem caseRecK_of_checkStrWPP (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    CaseRecK (KindsP p) p env κ (· ∈ Sl) := by
  intro c r hc hr
  have h0 := caseRecP_of_checkStrWPP h c hc
  simp only [caseRecPB, hr, Bool.and_eq_true] at h0
  obtain ⟨h1, h2⟩ := h0
  refine ⟨?_, ?_⟩
  · split at h1
    · rename_i hk; exact .inl hk
    · rename_i hk; exact .inr (.inl hk)
    · rename_i w srcs hk
      exact .inr (.inr ⟨w, by rw [hk, srcs_nil_of_punit h1]⟩)
    · cases h1
  · split at h2
    · rename_i ci hf; exact ⟨ci, hf, of_decide_eq_true h2⟩
    · cases h2

theorem caseFactsReadP_of_checkStrWPP (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    CaseFactsReadP p env κ (· ∈ Sl) := by
  intro c r hc hr hk
  have h1 := caseShapeP_of_checkStrWPP h c hc
  have h2 : caseProgOkB p env κ Sl c = true :=
    List.all_eq_true.mp (sansKS_of_checkStrWPP h "caseProg" (Sl.all (caseProgOkB p env κ Sl))
      (by simp [checkParts, checkPartsWith]) (by decide)) c hc
  obtain ⟨sh, hsh, hst⟩ : ∃ sh, caseShape? env (κ c) (κ r) = some sh ∧
      CaseStoredWith (fun _ _ => True) env (κ c) (κ r) sh := by
    simp only [caseShapePB, hr] at h1
    split at h1
    · rename_i he; exact absurd he hk
    · split at h1
      · rename_i sh hsh
        exact ⟨sh, hsh, caseStoredWith_of_check (fun _ => trivial) h1⟩
      · cases h1
    · split at h1
      · rename_i sh hsh
        exact ⟨sh, hsh, CaseStoredWith.mono (fun _ _ _ => trivial) (caseStored_of_check h1)⟩
      · cases h1
  refine ⟨sh, hsh, hst, ?_⟩
  simp only [caseProgOkB, hr, hsh] at h2
  exact caseProg_of_check h2

theorem punitPropFacts_of_checkStrWPP (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    PUnitPropFacts p env κ (· ∈ Sl) := by
  intro c r w srcs hc hr hk
  have hrec := caseRecP_of_checkStrWPP h c hc
  simp only [caseRecPB, hr, hk, Bool.and_eq_true] at hrec
  have hpu : punitShapeB p env κ ann Sl c r w srcs = true := hrec.1
  have hps := List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ h).2 c hc
  simp only [punitSortB, hr, hk] at hps
  cases hsh : caseShape? env (κ c) (κ r) with
  | none => rw [hsh] at hps; cases hps
  | some sh =>
    simp only [hsh] at hps
    cases hfd : env.find? sh.ind with
    | none => rw [hfd] at hps; cases hps
    | some ciD =>
      simp only [hfd] at hps
      cases ciD with
      | indInfo cvD caps =>
        simp only at hps
        cases htyD : cvD.type with
        | sort s =>
          have hcl := List.all_eq_true.mp hpu
          cases hdr : p.decl? r with
          | none =>
            have hf := hcl ("recrDecl", false) (by simp [punitClauses, hsh, hdr])
            cases hf
          | some dr =>
            cases dr with
            | recr sf kk lvls np nmot nmin ni ind rules ty =>
              have hnp : (np == 0 && sh.nP == 0) = true :=
                hcl ("np", np == 0 && sh.nP == 0) (by simp [punitClauses, hsh, hdr])
              have hnP0 : sh.nP = 0 := by
                simp only [Bool.and_eq_true, beq_iff_eq] at hnp
                exact hnp.2
              have hct : (sh.ctors.map (·.nF) == [0]) = true :=
                hcl ("oneCtorNoField", sh.ctors.map (·.nF) == [0]) (by simp [punitClauses, hsh, hdr])
              have hct' : sh.ctors.map (·.nF) = [0] := beq_iff_eq.mp hct
              have hctors : ∃ cs, sh.ctors = [cs] ∧ cs.nF = 0 := by
                cases hcs : sh.ctors with
                | nil => rw [hcs] at hct'; cases hct'
                | cons cs rest =>
                  rw [hcs] at hct'
                  cases rest with
                  | nil =>
                    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hct'
                    exact ⟨cs, rfl, hct'⟩
                  | cons _ _ => simp at hct'
              have hfam : famSort? env sh.ind = some (cvD.levelParams, s) := by
                simp [famSort?, hfd, htyD, finalSort]
              have hw := hcl ("w", pwNamed sh.lps w ==
                  some (Level.zeronessOf (Level.subst cvD.levelParams sh.indLevels s))) (by
                simp [punitClauses, hsh, hdr, hfam])
              exact ⟨sh, rfl, ⟨hnP0, hctors, ⟨cvD, caps, s, hfd, htyD, beq_iff_eq.mp hw⟩⟩⟩
            | _ =>
              have hf := hcl ("recrDecl", false) (by simp [punitClauses, hsh, hdr])
              cases hf
        | _ => rw [htyD] at hps; cases hps
      | _ => cases hps

theorem groundFactsStrWPP_of_check (h : groundCheckStrWPP p env κ lpsOf ann Sl = true) :
    GroundFactsWithK (RecFacts p env κ lpsOf (· ∈ Sl)) (WordFacts p env κ lpsOf (· ∈ Sl))
      (KindsP p) p env κ lpsOf ann (· ∈ Sl) :=
  groundFactsWKS_of_sansKS (sansKS_of_checkStrWPP h) (wordFacts_of_check (word_of_checkStrWPP h))
    (caseRecK_of_checkStrWPP h)
    (fun c thm body d hc hr hd => by
      have h2 := eqnCorrStr_of_checkStrWPP h c hc
      simp only [eqnCorrStrB, hr, hd] at h2
      exact termCorrS_of_corrStrSB _ _ _ h2)
    (fun c lvls ty v cv val hint hc hr hd hf => by
      have h1 := valueCorrStr_of_checkStrWPP h c hc
      simp only [valueCorrStrB, hr, hd, hf] at h1
      exact termCorrS_of_corrStrSB _ _ _ h1)

end StrCheck

/-! ## First-order `String` root soundness (`FoTyStr`, `rootSound_678AGpStrWPP_of_check`) -/

/-- First-order types widened with `String`. -/
inductive FoTyStr where
  | nat
  | str
  | enum (ind : CId)
  deriving DecidableEq

def FoTyStr.kexpr (κ : CId → KKey) : FoTyStr → KExpr
  | .nat => .const natName []
  | .str => .const stringName []
  | .enum D => .const (κ D) []

inductive FoValStr (p : Program) (κ : CId → KKey) : FoTyStr → Value → KExpr → Prop
  | nat (n : Nat) : FoValStr p κ .nat (.lit n) (litE n)
  | str (s : String) : FoValStr p κ .str (.str s) (.lit (.strVal s))
  | enum {D c : CId} {i : Nat} {safe : Bool} {cs : List CId} {ty : Term} :
      p.decl? D = some (.induct safe 0 0 0 ty cs) → cs[i]? = some c →
      FoValStr p κ (.enum D) (.con c [] [] []) (.const (κ c) [])

inductive FoArgsStr (p : Program) (κ : CId → KKey) :
    List FoTyStr → List Value → List KExpr → Prop
  | nil : FoArgsStr p κ [] [] []
  | cons {t : FoTyStr} {ts : List FoTyStr} {x : Value} {xs : List Value}
      {e : KExpr} {es : List KExpr} :
      FoValStr p κ t x e → FoArgsStr p κ ts xs es → FoArgsStr p κ (t :: ts) (x :: xs) (e :: es)

inductive FoObsStr (p : Program) (κ : CId → KKey) : FoTyStr → IxCC.Sem.Obs → KExpr → Prop
  | nat (w : Nat) : FoObsStr p κ .nat (.nat w) (litE w)
  | str (s : String) : FoObsStr p κ .str (.bytes s.toUTF8.toList) (.lit (.strVal s))
  | enum {D c : CId} {i : Nat} {safe : Bool} {cs : List CId} {ty : Term} :
      p.decl? D = some (.induct safe 0 0 0 ty cs) → cs[i]? = some c →
      FoObsStr p κ (.enum D) (.ctor i []) (.const (κ c) [])

def ResultTagStr (p : Program) (env : KEnv) (κ : CId → KKey) (S : CId → Prop) :
    FoTyStr → IxCC.Sem.Obs → Prop
  | .nat, _ => True
  | .str, _ => True
  | .enum D, .ctor i [] =>
    ∀ (safe : Bool) (ty : Term) (cs : List CId) (c' : CId),
      p.decl? D = some (.induct safe 0 0 0 ty cs) → cs[i]? = some c' →
      ∀ c, S c → readTag p c = i → (∃ (cv : ConstantVal .anon) (np : Nat),
        env.find? (κ c) = some (.ctorInfo cv np 0)) → κ c = κ c'
  | .enum _, _ => True

structure RootFactsStr (p : Program) (env : KEnv) (κ : CId → KKey) (ann : IxCC.Src.Relevance.Ann)
    (S : CId → Prop) (root : CId) (args : List FoTyStr) (res : FoTyStr) : Prop where
  mem : S root
  ok : Ok p ann root []
  stored : ∃ ci : ConstantInfo .anon, env.find? (κ root) = some ci ∧
    ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type =
      piTele (args.map fun t => (t.kexpr κ, { pw := PropWhen.never })) (res.kexpr κ)
  enums : ∀ D, (FoTyStr.enum D ∈ args ∨ res = .enum D) → EnumStored p env κ S D

theorem foArgsStr_length {p : Program} {κ : CId → KKey} :
    ∀ {ts : List FoTyStr} {xs : List Value} {es : List KExpr},
      FoArgsStr p κ ts xs es → es.length = ts.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => by simp [foArgsStr_length h]

section StrRoot

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- **`rootSound_coreWK` widened to `FoTyStr` (`Nat`, `String`, enumerations).** -/
theorem rootSound_str_coreWK (hL : LawsCore M) (hSB : StrBasis env) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTyStr} {res : FoTyStr} {R Wd : Prop} {Kd : CId → Prop}
    (hG : GroundFactsWithK R Wd Kd p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFactsStr p env κ ann (· ∈ Sl) root args res)
    {Ok' : CId → Levels → Prop} (hAllK : ∀ k, AllP M p κ lpsOf (· ∈ Sl) Ok' k)
    (hOkR : Ok' root [])
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgsStr p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTagStr p env κ (· ∈ Sl) res o)
    (hO : FoObsStr p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  have hN := hG.natBasis
  have hF0 := natFacts M hN φ
  have hAll := hAllK k
  obtain ⟨ci, hfr, hlr, htr⟩ := hR.stored
  rw [IxCC.Src.run_eq] at hrun
  obtain ⟨f, hf, happ⟩ := Result.bind_eq_ok_iff.mp hrun
  obtain ⟨ci2, hf2, hlps⟩ := hG.faith.stored root hR.mem
  rw [hfr] at hf2
  cases hf2
  have hlv : LvAt φ (lpsOf root) [] := by rw [← hlps, hlr]; intro i q h; simp at h
  have hrelf := hAll.evalConst [] root f φ hf hR.mem hOkR hlv
  obtain ⟨F, Es, hFd, hEs, rfl⟩ := (den_mkAppN es).mp hX
  obtain rfl : F = M.cval (κ root) φ := (den_const0 hfr hlr).mp hFd
  obtain ⟨ciStr, hfStr, hlpStr, _⟩ := hSB.string
  have hargs : ∀ {ts : List FoTyStr} {xs : List Value} {es : List KExpr} {Es : List V},
      (∀ D, FoTyStr.enum D ∈ ts → FoTyStr.enum D ∈ args) → FoArgsStr p κ ts xs es →
      DenotesList M.cval env φ ρ es Es →
      RelSlots M p κ lpsOf (· ∈ Sl) Ok' (xs.map .val) Es ∧
        ∀ (E : BVarIdx → V), Fits M.cval env φ E
          (piTele (ts.map fun t => (t.kexpr κ, { pw := PropWhen.never })) (res.kexpr κ)) Es
          (pushAll Es E) (res.kexpr κ) := by
    intro ts xs es Es hsub hA hEs
    induction hA generalizing Es with
    | nil => cases hEs; exact ⟨.nil, fun E => by rw [pushAll_nil]; exact .nil⟩
    | @cons t ts x xs e es hv _ ih =>
      cases hEs with
      | @cons _ _ Y Ys hY hYs =>
      obtain ⟨ih1, ih2⟩ := ih (fun D h => hsub D (List.mem_cons_of_mem _ h)) hYs
      have hYrel : RelV M p κ lpsOf (· ∈ Sl) Ok' x Y ∧
          ∀ ρ' Z, Denotes M.cval env φ ρ' (t.kexpr κ) Z → Y ∈ˢ Z := by
        cases hv with
        | nat n =>
          rw [(lit_den M hF0 ρ n Y).mp hY]
          exact ⟨relV_lit_intro hN φ n, fun ρ' Z hZ => by
            rw [(hF0.natD ρ' Z).mp hZ]; exact lit_mem M hF0 n⟩
        | str s =>
          rw [(str_den M hL.cval_params hSB φ ρ s Y).mp hY]
          exact ⟨relV_str_intro hL.cval_params hSB φ s, fun ρ' Z hZ => by
            rw [(den_const0 hfStr hlpStr).mp hZ]; exact str_mem M hL.cval_params hSB φ s⟩
        | @enum D c i safe cs ty hd hc =>
          have hE := hR.enums D (Or.inl (hsub D (List.mem_cons_self ..)))
          obtain ⟨hrel, hden, hmem⟩ := enum_argWK (M := M) (Ok' := Ok') hG.faith hE hd hc φ
          rw [(hden ρ Y).mp hY]
          exact ⟨hrel, fun ρ' Z hZ => hmem ρ' Z hZ⟩
      refine ⟨.cons (.val hYrel.1) ih1, fun E => ?_⟩
      obtain ⟨Z, hZ⟩ : ∃ Z, Denotes M.cval env φ E (t.kexpr κ) Z := by
        cases t with
        | nat => exact ⟨_, (hF0.natD E _).mpr rfl⟩
        | str => exact ⟨_, (den_const0 hfStr hlpStr).mpr rfl⟩
        | enum D =>
          obtain ⟨_, _, _, _, ⟨ciD, hfD, hlD⟩, _⟩ :=
            hR.enums D (Or.inl (hsub D (List.mem_cons_self ..)))
          exact ⟨_, (den_const0 hfD hlD).mpr rfl⟩
      have h2 := ih2 (push Y E)
      rw [← pushAll_cons] at h2
      exact .cons hZ (hYrel.2 E Z hZ) (by simpa using h2)
  obtain ⟨hrelEs, hfitEs⟩ := hargs (fun D h => h) hA hEs
  obtain ⟨TT, hTT, hmem⟩ := mem_key M hfr φ ρ
  rw [htr] at hTT
  have hchain : AppChain (M.cval (κ root) φ) Es :=
    appChain_of_fits _ _ hTT hmem (hfitEs ρ) (by
      have := denotesList_length hEs
      have hl := foArgsStr_length hA
      simp; omega) (fun b hb => by
        simp only [List.mem_map] at hb
        obtain ⟨_, _, rfl⟩ := hb
        simp [regime])
  have hrelv := hAll.applyAll f (xs.map .val) v _ Es happ hrelf hrelEs hchain
  cases hO with
  | nat w =>
    obtain rfl := readback_nat hrb
    rw [relV_lit_eq hL hN φ hrelv]
    exact (lit_den M hF0 ρ w _).mpr rfl
  | str s =>
    obtain ⟨s', rfl, hbytes⟩ := readback_str hrb
    have hse : s' = s := str_toUTF8_toList_inj hbytes
    rw [hse] at hrelv
    rw [relV_str_eq hL.cval_params hSB φ hrelv]
    exact (str_den M hL.cval_params hSB φ ρ s _).mpr rfl
  | @enum D c i safe cs ty hd hc =>
    obtain ⟨c'', ls, ps, rfl, htag⟩ := readback_ctor hrb
    have hE := hR.enums D (Or.inr rfl)
    obtain ⟨_, hden, _⟩ := enum_argWK (M := M) (Ok' := Ok') hG.faith hE hd hc φ
    obtain ⟨_, _, _, hd', _, hcs, _⟩ := hE
    rw [hd] at hd'
    injection hd' with hd''
    injection hd'' with _ _ _ _ _ hcs
    subst hcs
    obtain ⟨_, _, cvc, hfc, hlc, _⟩ := hcs i c hc
    generalize hXv : Es.foldl app (M.cval (κ root) φ) = Xv at hrelv ⊢
    cases hrelv with
    | @con _ _ _ _ ψ cvC' np' nf' Ps Fs _ _ _ hSc'' _ hf'' hPl hFl _ hfs' _ =>
      have hnf0 : nf' = 0 := by rw [← hFl]; cases hfs'; rfl
      subst hnf0
      have hkeq : κ c'' = κ c := hRT _ _ _ c hd hc c'' hSc'' htag ⟨cvC', np', hf''⟩
      rw [hkeq, hfc] at hf''
      injection hf'' with hf''
      injection hf'' with e1 e2 _
      subst e1 e2
      obtain rfl : Ps = [] := List.eq_nil_of_length_eq_zero hPl
      obtain rfl : Fs = [] := List.eq_nil_of_length_eq_zero hFl
      have hcv : M.cval (κ c) ψ = M.cval (κ c) φ :=
        hL.cval_params (κ c) (.ctorInfo cvc 0 0) hfc ψ φ fun p hp => by
          simp [ConstantInfo.toConstantVal, hlc] at hp
      exact (hden ρ _).mpr (by simp [hkeq, hcv])

/-- **Full end-to-end string-widened Pc-Prop root soundness**, directly over `Ix.Kernel.Model`:
admits word entries, `PUnit.casesOn` at ordinary & `Prop` instances (no `pcInstB`), and `Lit.str`
everywhere (in bodies, equations, and as first-order root arguments & `Obs.bytes` results). -/
theorem rootSound_678AGStrWPP_of_check {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTyStr} {res : FoTyStr} {Inst : List (CId × Levels)}
    (hchk : groundCheckStrWPP p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hsb : strBasisB env = true)
    (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p env κ lpsOf ann Sl = true)
    (hR : RootFactsStr p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgsStr p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTagStr p env κ (· ∈ Sl) res o)
    (hO : FoObsStr p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  obtain ⟨hseeds, hI, hU⟩ := instFacts_of_check hinst
  have hLN := lawsNoCanon_of_model M (litDefs_of_check hld)
  have hG := groundFactsStrWPP_of_check hchk
  have hC := caseFactsReadP_of_checkStrWPP hchk
  have hPU := punitPropFacts_of_checkStrWPP hchk
  have hNC := noCanonA_of_check hnc
  have hT := sitesOk_of_headRegime M.defn_value M.graded
    (headRegimeS_of_sansKS (sansKS_of_checkStrWPP hchk) hhr)
  exact rootSound_str_coreWK hLN.core (strBasis_of_check hsb) hG hR
    (allPK (fundHypsK_of_instWPP hLN.core (.inr hNC.recs) hG hT hI hU
      (caseFires_of_instWP hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hG.natBasis hC
        hNC hU)
      (caseSubFires_of_instWPP hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hC hNC hPU)
      (wordFires_of_facts hLN.core M.proj_law M.graded hG.natBasis hG.faith.words)))
    ⟨hR.ok, hseeds root (List.mem_singleton_self _)⟩ hA hrun hrb hRT hO φ ρ X hX

/-- **`rootSound_678AGpStrWPP_of_check`**: every check on `selEnv`, the conclusion for the reading,
directly over `Ix.Kernel.Model` with words, `PUnit.casesOn` at `Prop`, and `Lit.str`. -/
theorem rootSound_678AGpStrWPP_of_check {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTyStr} {res : FoTyStr} {Inst : List (CId × Levels)}
    (hchk : groundCheckStrWPP p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hnc : noCanonAB p (selEnv p env κ Sl) κ Sl = true)
    (hld : litDefsB (selEnv p env κ Sl) = true)
    (hsb : strBasisB (selEnv p env κ Sl) = true)
    (hinst : instCheckB p (selEnv p env κ Sl) κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hR : RootFactsStr p (selEnv p env κ Sl) κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgsStr p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o)
    (hRT : ResultTagStr p (selEnv p env κ Sl) κ (· ∈ Sl) res o)
    (hO : FoObsStr p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  have hS := selRetype_selEnv p env κ Sl
  obtain ⟨M', hc⟩ := model_selRetype M hS
  have hden := denotes_selRetype hS M.cval φ
  have h := rootSound_678AGStrWPP_of_check (M := M') hchk hnc hld hsb hinst hhr hR hA hrun hrb
    hRT hO φ ρ X (by rw [hc, hden]; exact hX)
  rw [hc, hden] at h
  exact h

end StrRoot

end IxCC.Grounding
