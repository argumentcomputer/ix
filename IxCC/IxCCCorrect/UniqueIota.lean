import IxCCCorrect.Unique
import IxCCGrounding.RecFlat

/-!
# The answer is unique, through the `Bool` recursor (`IxCCCorrect.UniqueIota`)

`IxCCCorrect.Unique` separates numerals in a model from a stored theorem `Bool.true = Bool.false →
False`, which no committed closure stores. This module separates `Bool.true` from `Bool.false`
through the **ι-law of the `Bool` recursor** instead (`Model.iota_rule`), so it needs no witness in
the committed bytes:

```lean
agrees_unique_iota : (∃ V : Type u, Nonempty (SetTheory V)) → numeralBasisIB acc.env = true →
  claim.abi.result = .nat → Agrees claim acc xs a → Agrees claim acc xs b → a = b
```

**The argument** (`bool_true_ne_false_iota`). Apply the stored `Bool.rec.{u}` at `u := 1` to the
motive `fun _ => Prop` (the graph `lamR 1 ⟦Bool⟧ (fun _ => univ 0)`), the minor premises `∅` (a
false proposition) and `eqv ∅ ∅` (a true one), and a major premise. ι at the `true` rule
(`flatIota_noLevels`) makes the application `eqv ∅ ∅` at `Bool.true`; at the `false` rule, `∅` at
`Bool.false`. If the two constructors denoted one set, the two applications would be one set, and
`pt ∈ eqv ∅ ∅` would be a member of `∅`.

**What it reads of the environment** (`numeralBasisIB`, decided): `Nat` and its constructors,
`Bool` and its constructors, `Nat.beq` without level parameters, the `Nat` roles as definitions
(`LitDefs`), and at the role key `Bool.rec` a recursor of `Bool.rec`'s shape (`boolRecB`: one level
parameter, the type `{motive : Bool → Sort u} → motive false → motive true → (t : Bool) → motive t`,
whose motive binder is not a proposition at `u = 1`, and the two rules `false ↦ λ m f t, f`,
`true ↦ λ m f t, t`). A role table binds `Bool.rec` whenever it binds `Bool` (`Role.block`), and the
kernel validates its type against `boolRecSpecTy` at install. No `Eq` and no theorem is read.
-/

set_option autoImplicit false

namespace IxCC.Correct

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Grounding

universe u

/-! ## The `Bool` recursor, decided -/

/-- The key the role table gives `Bool.rec`. -/
abbrev boolRecKey : KKey := roleKey .boolRec

/-- The assignment of every level parameter to `1`. -/
def oneLv : LevelParam → Nat := fun _ => 1

/-- The domains of the first `n` `λ`s of a term, and what is under them. -/
def lamDoms : Nat → KExpr → Option (List KExpr × KExpr)
  | 0, e => some ([], e)
  | n + 1, .lam d b _ => (lamDoms n b).map fun r => (d :: r.1, r.2)
  | _ + 1, _ => none

theorem lamDoms_sound : ∀ (n : Nat) {e body : KExpr} {ds : List KExpr},
    lamDoms n e = some (ds, body) →
    ∃ bs : List (KExpr × BinderMeta), e = lamTele bs body ∧ bs.map (·.1) = ds
  | 0, e, body, ds, h => by
    simp only [lamDoms, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩
  | n + 1, e, body, ds, h => by
    cases e with
    | lam d b m =>
      simp only [lamDoms, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨ds', body'⟩, hr, rfl, rfl⟩ := h
      obtain ⟨bs, rfl, hbs⟩ := lamDoms_sound n hr
      exact ⟨(d, m) :: bs, rfl, by simp [hbs]⟩
    | _ => simp [lamDoms] at h

/-- **The stored `Bool` recursor**, as the ι argument reads it. -/
structure BoolRecStored (env : KEnv) : Prop where
  stored : ∃ (cvr : ConstantVal .anon) (r0 r1 : RecRule .anon) (p : LevelParam)
      (m0 m1 m2 m3 m4 : BinderMeta) (b0 b1 : List (KExpr × BinderMeta)),
    env.find? boolRecKey = some (.recInfo cvr 3 3 [r0, r1]) ∧ cvr.levelParams = [p] ∧
    cvr.type = .forallE (.forallE boolK (.sort (.param p)) m1)
      (.forallE (.app (.bvar 0) (.const boolFalseName []))
        (.forallE (.app (.bvar 1) (.const boolTrueName []))
          (.forallE boolK (.app (.bvar 3) (.bvar 0)) m4) m3) m2) m0 ∧
    m1.pw.holds oneLv = false ∧
    r0.ctor = boolFalseName ∧ r1.ctor = boolTrueName ∧
    r0.rhs = lamTele b0 (.bvar 1) ∧
    b0.map (·.1) = [.forallE boolK (.sort (.param p)) m1, .app (.bvar 0) (.const boolFalseName []),
      .app (.bvar 1) (.const boolTrueName [])] ∧
    r1.rhs = lamTele b1 (.bvar 0) ∧
    b1.map (·.1) = [.forallE boolK (.sort (.param p)) m1, .app (.bvar 0) (.const boolFalseName []),
      .app (.bvar 1) (.const boolTrueName [])]

/-- `BoolRecStored`, decided. -/
def boolRecB (env : KEnv) : Bool :=
  match env.find? boolRecKey with
  | some (.recInfo cvr 3 3 [r0, r1]) =>
    match cvr.levelParams with
    | [p] =>
      match cvr.type with
      | .forallE (.forallE e0 e1 m1) (.forallE d1 (.forallE d2 (.forallE d3 b _) _) _) _ =>
        decide (e0 = boolK) && decide (e1 = .sort (.param p)) && !(m1.pw.holds oneLv) &&
          decide (d1 = .app (.bvar 0) (.const boolFalseName [])) &&
          decide (d2 = .app (.bvar 1) (.const boolTrueName [])) &&
          decide (d3 = boolK) && decide (b = .app (.bvar 3) (.bvar 0)) &&
          decide (r0.ctor = boolFalseName) && decide (r1.ctor = boolTrueName) &&
          decide (lamDoms 3 r0.rhs = some ([.forallE e0 e1 m1, d1, d2], .bvar 1)) &&
          decide (lamDoms 3 r1.rhs = some ([.forallE e0 e1 m1, d1, d2], .bvar 0))
      | _ => false
    | _ => false
  | _ => false

theorem boolRecStored_of_check {env : KEnv} (h : boolRecB env = true) : BoolRecStored env := by
  unfold boolRecB at h
  split at h
  · rename_i cvr r0 r1 hf
    split at h
    · rename_i p hlp
      split at h
      · rename_i e0 e1 m1 d1 d2 d3 b m4 m3 m2 m0 hty
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he0, he1⟩, hpw⟩, hd1⟩, hd2⟩, hd3⟩, hb⟩, hc0⟩, hc1⟩, hr0⟩, hr1⟩ := h
        subst he0 he1 hd1 hd2 hd3 hb
        obtain ⟨b0, hb0, hbs0⟩ := lamDoms_sound 3 hr0
        obtain ⟨b1, hb1, hbs1⟩ := lamDoms_sound 3 hr1
        exact ⟨cvr, r0, r1, p, m0, m1, m2, m3, m4, b0, b1, hf, hlp, hty, hpw, hc0, hc1, hb0, hbs0,
          hb1, hbs1⟩
      · cases h
    · cases h
  · cases h

/-! ## `Bool.true ≠ Bool.false`, by ι -/

section Sem

variable {V : Type u} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **`Bool.true` and `Bool.false` denote different sets in every model** of an environment
that stores `Bool`, its constructors and its recursor (by ι; no stored theorem). -/
theorem bool_true_ne_false_iota (M : Model V env) (hB : BoolBasis env) (hR : BoolRecStored env)
    (φ : LevelParam → Nat) : M.cval boolTrueName φ ≠ M.cval boolFalseName φ := by
  intro heq
  obtain ⟨cvr, r0, r1, p, m0, m1, m2, m3, m4, b0, b1, hf, hlp, hty, hpw, hc0, hc1, hrhs0, hbs0,
    hrhs1, hbs1⟩ := hR.stored
  obtain ⟨cvB, capsB, hfB, hlB⟩ := hB.bool
  obtain ⟨cvT, hfT, hlT, htT⟩ := hB.bTrue
  obtain ⟨cvFa, hfFa, hlFa, htFa⟩ := hB.bFalse
  have hcv : CvalParams M := M.cval_params
  -- the constructors at the assignment `oneLv`
  have heq1 : M.cval boolTrueName oneLv = M.cval boolFalseName oneLv := by
    rw [hcv _ _ hfT oneLv φ (by simp [ConstantInfo.toConstantVal, hlT]),
      hcv _ _ hfFa oneLv φ (by simp [ConstantInfo.toConstantVal, hlFa]), heq]
  have hBl : (ConstantInfo.indInfo cvB capsB).toConstantVal.levelParams = [] := by
    simp [ConstantInfo.toConstantVal, hlB]
  have hBD : ∀ ρ : BVarIdx → V, Denotes M.cval env oneLv ρ boolK (M.cval boolKey oneLv) :=
    fun ρ => (den_const0 hfB hBl).mpr rfl
  have hctorMem : ∀ {c : KKey} {cv : ConstantVal .anon}, env.find? c = some (.ctorInfo cv 0 0) →
      cv.type = boolK → M.cval c oneLv ∈ˢ M.cval boolKey oneLv := by
    intro c cv hfc htc
    obtain ⟨T, hT, hm⟩ := mem_key M hfc oneLv (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, htc] at hT
    rwa [(den_const0 hfB hBl).mp hT] at hm
  have hTm := hctorMem hfT htT
  have hFm := hctorMem hfFa htFa
  -- the arguments: the motive `fun _ => Prop`, a false and a true proposition
  let Mot : V := lamR 1 (M.cval boolKey oneLv) (fun _ => univ 0)
  let A : V := empty
  let B : V := eqv (empty : V) empty
  have hreg : regime oneLv m1.pw = 1 := by simp [regime, hpw]
  have hMot : Mot ∈ˢ piR (regime oneLv m1.pw) (M.cval boolKey oneLv) (fun _ => univ (Level.eval oneLv (.param p))) := by
    rw [hreg]
    exact lamR_mem fun _ _ => univ_mem_univ 0
  have hAppMot : ∀ {x : V}, x ∈ˢ M.cval boolKey oneLv → app Mot x = univ 0 :=
    fun hx => app_lamR_pos (by decide) hx
  have hfit : ∀ K, K ∈ˢ M.cval boolKey oneLv →
      Fits M.cval env oneLv (fun _ => empty) cvr.type [Mot, A, B, K]
        (push K (push B (push A (push Mot (fun _ => empty))))) (.app (.bvar 3) (.bvar 0)) := by
    intro K hK
    rw [hty]
    refine .cons (.pi (hBD _) (fun _ _ => .sort) (fun h => absurd h (by rw [hreg]; decide))) hMot ?_
    refine .cons (.app .bvar ((den_const0 hfFa (by simp [ConstantInfo.toConstantVal, hlFa])).mpr rfl))
      (by show A ∈ˢ app Mot (M.cval boolFalseName oneLv); rw [hAppMot hFm]; exact empty_mem_univ 0) ?_
    refine .cons (.app .bvar ((den_const0 hfT (by simp [ConstantInfo.toConstantVal, hlT])).mpr rfl))
      (by show B ∈ˢ app Mot (M.cval boolTrueName oneLv); rw [hAppMot hTm]; exact eqv_mem_univ _ _) ?_
    exact .cons (hBD _) hK .nil
  have htyT : cvr.type = piTele [(.forallE boolK (.sort (.param p)) m1, m0),
      (.app (.bvar 0) (.const boolFalseName []), m2), (.app (.bvar 1) (.const boolTrueName []), m3)]
      (.forallE boolK (.app (.bvar 3) (.bvar 0)) m4) := by rw [hty]; rfl
  have hpb : piBody 3 cvr.type = .forallE boolK (.app (.bvar 3) (.bvar 0)) m4 := by rw [hty]; rfl
  -- ι at `true`: the application is `B`
  obtain ⟨XT, hXT, hfoldT⟩ := flatIota_noLevels (ψ := oneLv) M M.iota_rule hcv hf htyT rfl
    (krl := r1) (by simp) (by rw [hc1]; exact hfT) hlT (by rw [htT]; rfl) hrhs1
    (by rw [hbs1]; rfl) (by decide : 0 < 3) (hfit _ hTm) rfl hpb rfl (by rw [hlT]; rfl)
    (by rw [hc1]; rfl)
  -- ι at `false`: the application is `A`
  obtain ⟨XF, hXF, hfoldF⟩ := flatIota_noLevels (ψ := oneLv) M M.iota_rule hcv hf htyT rfl
    (krl := r0) (by simp) (by rw [hc0]; exact hfFa) hlFa (by rw [htFa]; rfl) hrhs0
    (by rw [hbs0]; rfl) (by decide : 1 < 3) (hfit _ hFm) rfl hpb rfl (by rw [hlFa]; rfl)
    (by rw [hc0]; rfl)
  have hXT' : XT = B := by simpa using hXT.symm
  have hXF' : XF = A := by simpa using hXF.symm
  have hAB : B = A := by
    rw [← hXT', ← hXF', ← hfoldT, ← hfoldF, heq1]
  have hpt : (pt : V) ∈ˢ B := pt_mem_eqv_self _
  rw [hAB] at hpt
  exact not_mem_empty _ hpt

end Sem

/-! ## Numerals, and the answer -/

/-- **What separates numerals by ι**, each a stored fact: `Nat` and its constructors, `Bool` and
its constructors and recursor, `Nat.beq` without level parameters, the `Nat` roles stored as
definitions. -/
structure NumeralBasisI (env : KEnv) : Prop where
  nat : NatBasis env
  bool : BoolBasis env
  beq : NatBeqStored env
  litDefs : LitDefs env
  boolRec : BoolRecStored env

/-- `NumeralBasisI`, decided. -/
def numeralBasisIB (env : KEnv) : Bool :=
  natBasisB env && boolBasisB env && natBeqStoredB env && litDefsB env && boolRecB env

theorem numeralBasisI_of_check {env : KEnv} (h : numeralBasisIB env = true) :
    NumeralBasisI env := by
  simp only [numeralBasisIB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨natBasis_of h1, boolBasis_of_check h2, natBeqStored_of_check h3, litDefs_of_check h4,
    boolRecStored_of_check h5⟩

/-- **Two numerals with the same denotation as one term are equal**, where a model exists and the
environment stores what separates numerals by ι. -/
theorem sameDenotation_lit_unique_iota {env : KEnv} (hB : NumeralBasisI env)
    {V : Type u} [Ix.Kernel.SetTheory V] (M : Model V env) {t : KExpr} {a b : Nat}
    (ha : SameDenotation.{u} env t (litE a)) (hb : SameDenotation.{u} env t (litE b)) : a = b := by
  obtain ⟨X, hX, hXa⟩ := ha V M (fun _ => 0) (fun _ => empty)
  obtain ⟨Y, hY, hYb⟩ := hb V M (fun _ => 0) (fun _ => empty)
  obtain rfl : X = Y := Denotes_functional hX hY
  have hF := natFacts M hB.nat (fun _ => 0)
  have h1 : X = litSet M (fun _ => 0) a := (lit_den M hF (fun _ => empty) a X).mp hXa
  have h2 : X = litSet M (fun _ => 0) b := (lit_den M hF (fun _ => empty) b X).mp hYb
  exact litSet_inj M (natAccel_of_litOps M.lit_ops hB.litDefs) hB.nat hB.bool hB.beq
    (bool_true_ne_false_iota M hB.bool hB.boolRec (fun _ => 0)) (h1.symm.trans h2)

/-- **The answer is unique** at a `Nat` result, if a set theory with the kernel's universes exists
and the admitted environment stores what separates numerals by ι (`numeralBasisIB`): no witness
theorem is needed. -/
theorem agrees_unique_iota {claim : Claim} {acc : Src.KernelFront.Accepted}
    (hV : ∃ V : Type u, Nonempty (Ix.Kernel.SetTheory V))
    (hB : numeralBasisIB acc.env = true) (hres : claim.abi.result = ResTy.nat)
    {xs : List Nat} {a b : Answer} (ha : Agrees.{u} claim acc xs a) (hb : Agrees.{u} claim acc xs b) :
    a = b := by
  obtain ⟨V, ⟨inst⟩⟩ := hV
  haveI : Ix.Kernel.SetTheory V := inst
  obtain ⟨M⟩ := accepted_has_model V acc
  unfold Agrees at ha hb
  obtain ⟨t1, o1, hk1, ht1, hs1⟩ := ha
  obtain ⟨t2, o2, hk2, ht2, hs2⟩ := hb
  rw [hk1] at hk2
  cases hk2
  cases a with
  | node _ _ => simp [answerTerm, hres] at ht1
  | nat na =>
    cases b with
    | node _ _ => simp [answerTerm, hres] at ht2
    | nat nb =>
      simp only [answerTerm, hres, Option.some.injEq] at ht1 ht2
      subst ht1
      subst ht2
      exact congrArg Answer.nat (sameDenotation_lit_unique_iota (numeralBasisI_of_check hB) M hs1 hs2)

end IxCC.Correct
