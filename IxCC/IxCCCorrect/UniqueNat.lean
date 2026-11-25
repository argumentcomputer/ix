import IxCCCorrect.UniqueIota
import IxCCGrounding.RecRun

/-!
# The answer is unique, through the `Nat` recursor (`IxCCCorrect.UniqueNat`)

`IxCCCorrect.UniqueIota` separates numerals through `Nat.beq`'s literal law and the `Bool`
recursor, so it needs `Nat.beq` stored; 23 of the 55 committed closures do not store it. This
module separates numerals through the **ι-law of the `Nat` recursor** (role `.natRec`, bound with
`Nat` by `Role.block`), which needs neither `Nat.beq` nor `Bool`:

```lean
agrees_unique_rec : (∃ V : Type u, Nonempty (SetTheory V)) → numeralBasisNB acc.env = true →
  claim.abi.result = .nat → Agrees claim acc xs a → Agrees claim acc xs b → a = b
```

* **zero is not a successor** (`zero_ne_succ_rec`): `Nat.rec.{1}` at the motive `fun _ => Prop`,
  the minors `∅` and `fun _ _ => eqv ∅ ∅`, is `∅` at `zero` and `eqv ∅ ∅` at `succ x` (ι at the
  `zero` rule, `flatIota_noLevels`; at the `succ` rule, `noParamsIota`, then β through
  `succ n ih` with the recursive call a member of the motive's fibre, `fits_app_mem`);
* **the successor is injective** (`succ_inj_rec`): at the motive `fun _ => Nat` and the minors
  `zero` and `fun n _ => n`, the recursor is the predecessor on successors;
* so `litSet` is injective (`litSet_inj_rec`), by induction.

What it reads of the environment (`numeralBasisNB`, decided): `Nat` and its constructors
(`NatBasis`), `Nat` stored at `Sort 1`, and at `Nat.rec`'s role key a recursor of `Nat.rec`'s shape
(`natRecB`: one level parameter, the pinned type and rules of `IxCK/Kernel/Basis/Nat.lean` up to
binder data, its motive and successor binders not propositions at `u = 1`).
-/

set_option autoImplicit false

namespace IxCC.Correct

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Grounding

universe u

/-! ## `Nat.rec`, decided -/

/-- The key the role table gives `Nat.rec`. -/
abbrev natRecKey : KKey := roleKey .natRec

/-- The successor minor premise's type, in the `motive`/`zero` context, at binder data `mN mI`. -/
def natSuccMinor (mN mI : BinderMeta) : KExpr :=
  .forallE natK (.forallE (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app succK (.bvar 1))) mI) mN

/-- The successor rule's body, under its four λs: `succ n (Nat.rec motive zero succ n)`. -/
def natSuccBody (p : LevelParam) : KExpr :=
  .app (.app (.bvar 1) (.bvar 0))
    (.app (.app (.app (.app (.const natRecKey [.param p]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))

/-- **The stored `Nat` recursor**, as the ι argument reads it. -/
structure NatRecStored (env : KEnv) : Prop where
  natSort : ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon),
    env.find? natName = some (.indInfo cv caps) ∧ cv.levelParams = [] ∧
    cv.type = .sort (.succ .zero)
  stored : ∃ (cvr : ConstantVal .anon) (r0 r1 : RecRule .anon) (p : LevelParam)
      (m0 m1 m2 m3 m4 mN mI : BinderMeta) (b0 b1 : List (KExpr × BinderMeta)),
    env.find? natRecKey = some (.recInfo cvr 3 3 [r0, r1]) ∧ cvr.levelParams = [p] ∧
    cvr.type = .forallE (.forallE natK (.sort (.param p)) m1)
      (.forallE (.app (.bvar 0) zeroK)
        (.forallE (natSuccMinor mN mI)
          (.forallE natK (.app (.bvar 3) (.bvar 0)) m4) m3) m2) m0 ∧
    m1.pw.holds oneLv = false ∧ mN.pw.holds oneLv = false ∧ mI.pw.holds oneLv = false ∧
    r0.ctor = natZeroName ∧ r1.ctor = natSuccName ∧
    r0.rhs = lamTele b0 (.bvar 1) ∧
    b0.map (·.1) = [.forallE natK (.sort (.param p)) m1, .app (.bvar 0) zeroK, natSuccMinor mN mI] ∧
    r1.rhs = lamTele b1 (natSuccBody p) ∧
    b1.map (·.1) = [.forallE natK (.sort (.param p)) m1, .app (.bvar 0) zeroK, natSuccMinor mN mI,
      natK]

/-- `NatRecStored`, decided. -/
def natRecB (env : KEnv) : Bool :=
  (match env.find? natName with
    | some (.indInfo cv _) => cv.levelParams.isEmpty && decide (cv.type = .sort (.succ .zero))
    | _ => false) &&
  match env.find? natRecKey with
  | some (.recInfo cvr 3 3 [r0, r1]) =>
    match cvr.levelParams with
    | [p] =>
      match cvr.type with
      | .forallE (.forallE e0 e1 m1) (.forallE d1
          (.forallE (.forallE n0 (.forallE i0 i1 mI) mN) (.forallE d3 b _) _) _) _ =>
        decide (e0 = natK) && decide (e1 = .sort (.param p)) && !(m1.pw.holds oneLv) &&
          !(mN.pw.holds oneLv) && !(mI.pw.holds oneLv) &&
          decide (d1 = .app (.bvar 0) zeroK) && decide (n0 = natK) &&
          decide (i0 = .app (.bvar 2) (.bvar 0)) &&
          decide (i1 = .app (.bvar 3) (.app succK (.bvar 1))) &&
          decide (d3 = natK) && decide (b = .app (.bvar 3) (.bvar 0)) &&
          decide (r0.ctor = natZeroName) && decide (r1.ctor = natSuccName) &&
          decide (lamDoms 3 r0.rhs = some ([.forallE e0 e1 m1, d1,
            .forallE n0 (.forallE i0 i1 mI) mN], .bvar 1)) &&
          decide (lamDoms 4 r1.rhs = some ([.forallE e0 e1 m1, d1,
            .forallE n0 (.forallE i0 i1 mI) mN, natK], natSuccBody p))
      | _ => false
    | _ => false
  | _ => false

theorem natRecStored_of_check {env : KEnv} (h : natRecB env = true) : NatRecStored env := by
  unfold natRecB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hN, h⟩ := h
  refine ⟨?_, ?_⟩
  · split at hN
    · rename_i cv caps hf
      simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hN
      exact ⟨cv, caps, hf, hN.1, hN.2⟩
    · cases hN
  · split at h
    · rename_i cvr r0 r1 hf
      split at h
      · rename_i p hlp
        split at h
        · rename_i e0 e1 m1 d1 n0 i0 i1 mI mN d3 b m4 m3 m2 m0 hty
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he0, he1⟩, hp1⟩, hpN⟩, hpI⟩, hd1⟩, hn0⟩, hi0⟩, hi1⟩, hd3⟩, hb⟩,
            hc0⟩, hc1⟩, hr0⟩, hr1⟩ := h
          subst he0 he1 hd1 hn0 hi0 hi1 hd3 hb
          obtain ⟨b0, hb0, hbs0⟩ := lamDoms_sound 3 hr0
          obtain ⟨b1, hb1, hbs1⟩ := lamDoms_sound 4 hr1
          exact ⟨cvr, r0, r1, p, m0, m1, m2, m3, m4, mN, mI, b0, b1, hf, hlp, hty, hp1, hpN, hpI,
            hc0, hc1, hb0, hbs0, hb1, hbs1⟩
        · cases h
      · cases h
    · cases h

/-! ## Numerals are separated, by ι at `Nat.rec` -/

section Sem

variable {V : Type u} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **Zero is no successor, and the successor is injective**, on `Nat`'s set at `oneLv`, in every
model of an environment that stores `Nat`, its constructors and its recursor. -/
theorem natRec_sep (M : Model V env) (hN : NatBasis env) (hR : NatRecStored env) :
    (∀ x, x ∈ˢ M.cval natName oneLv →
      M.cval natZeroName oneLv ≠ app (M.cval natSuccName oneLv) x) ∧
    (∀ x y, x ∈ˢ M.cval natName oneLv → y ∈ˢ M.cval natName oneLv →
      app (M.cval natSuccName oneLv) x = app (M.cval natSuccName oneLv) y → x = y) := by
  obtain ⟨cvN, capsN, hfN, hlN, htN⟩ := hR.natSort
  obtain ⟨cvr, r0, r1, p, m0, m1, m2, m3, m4, mN, mI, b0, b1, hf, hlp, hty, hp1, hpN, hpI, hc0,
    hc1, hrhs0, hbs0, hrhs1, hbs1⟩ := hR.stored
  obtain ⟨cvZ, hfZ, -, htZ, hlZ⟩ := hN.zero
  obtain ⟨cvS, hfS, -, htS, hlS⟩ := hN.succ
  have hcv : CvalParams M := M.cval_params
  have hF := natFacts M hN oneLv
  let ρ : BVarIdx → V := fun _ => empty
  let NatS : V := M.cval natName oneLv
  have hNatU : NatS ∈ˢ (univ 1 : V) := by
    obtain ⟨T, hT, hm⟩ := mem_key M hfN oneLv ρ
    simp only [ConstantInfo.toConstantVal, htN] at hT
    rw [den_sort.mp hT] at hm
    exact hm
  have hr1 : regime oneLv m1.pw = 1 := by simp [regime, hp1]
  have hrN : regime oneLv mN.pw = 1 := by simp [regime, hpN]
  have hrI : regime oneLv mI.pw = 1 := by simp [regime, hpI]
  have hlv : Level.eval oneLv (.param p) = 1 := rfl
  -- the arguments fit the recursor's type, for any motive and minors of the right sets
  have hfitG : ∀ (Mot Z S K : V),
      Mot ∈ˢ piR 1 NatS (fun _ => univ 1) → Z ∈ˢ app Mot (M.cval natZeroName oneLv) →
      S ∈ˢ piR 1 NatS (fun n => piR 1 (app Mot n) (fun _ => app Mot (app (M.cval natSuccName oneLv) n))) →
      K ∈ˢ NatS →
      Fits M.cval env oneLv ρ cvr.type [Mot, Z, S, K]
        (push K (push S (push Z (push Mot ρ)))) (.app (.bvar 3) (.bvar 0)) := by
    intro Mot Z S K hMot hZ hS hK
    rw [hty]
    refine .cons (Denotes.pi (A := NatS) (B := fun _ => univ (Level.eval oneLv (.param p)))
      ((hF.natD _ _).mpr rfl) (fun _ _ => .sort) (fun h => absurd h (by rw [hr1]; decide)))
      (by rw [hr1, hlv]; exact hMot) ?_
    refine .cons (.app .bvar ((hF.zeroD _ _).mpr rfl)) hZ ?_
    refine .cons (Denotes.pi (A := NatS)
      (B := fun n => piR (regime oneLv mI.pw) (app Mot n)
        (fun _ => app Mot (app (M.cval natSuccName oneLv) n)))
      ((hF.natD _ _).mpr rfl)
      (fun n _ => Denotes.pi (A := app Mot n)
        (B := fun _ => app Mot (app (M.cval natSuccName oneLv) n))
        (.app .bvar .bvar) (fun _ _ => .app .bvar (.app ((hF.succD _ _).mpr rfl) .bvar))
        (fun h => absurd h (by rw [hrI]; decide)))
      (fun h => absurd h (by rw [hrN]; decide))) (by rw [hrN, hrI]; exact hS) ?_
    exact .cons ((hF.natD _ _).mpr rfl) hK .nil
  have htyT : cvr.type = piTele [(.forallE natK (.sort (.param p)) m1, m0),
      (.app (.bvar 0) zeroK, m2), (natSuccMinor mN mI, m3)]
      (.forallE natK (.app (.bvar 3) (.bvar 0)) m4) := by rw [hty]; rfl
  have hpb : piBody 3 cvr.type = .forallE natK (.app (.bvar 3) (.bvar 0)) m4 := by rw [hty]; rfl
  have hRcD : ∀ ρ' : BVarIdx → V,
      Denotes M.cval env oneLv ρ' (.const natRecKey [.param p]) (M.cval natRecKey oneLv) := by
    intro ρ'
    have h1 := Denotes.const (cval := M.cval) (env := env) (φ := oneLv) (ρ := ρ')
      (us := [.param p]) hf (by simp [ConstantInfo.toConstantVal, hlp])
    simp only [ConstantInfo.toConstantVal, hlp] at h1
    rwa [show Level.substFn oneLv [p] [.param p] = oneLv from substFn_self oneLv [p]] at h1
  -- the two rules
  have hrules : ∀ (Mot Z S : V),
      Mot ∈ˢ piR 1 NatS (fun _ => univ 1) → Z ∈ˢ app Mot (M.cval natZeroName oneLv) →
      S ∈ˢ piR 1 NatS (fun n => piR 1 (app Mot n) (fun _ => app Mot (app (M.cval natSuccName oneLv) n))) →
      [Mot, Z, S, M.cval natZeroName oneLv].foldl app (M.cval natRecKey oneLv) = Z ∧
      ∀ x, x ∈ˢ NatS →
        [Mot, Z, S, app (M.cval natSuccName oneLv) x].foldl app (M.cval natRecKey oneLv) =
          app (app S x) ([Mot, Z, S, x].foldl app (M.cval natRecKey oneLv)) ∧
        [Mot, Z, S, x].foldl app (M.cval natRecKey oneLv) ∈ˢ app Mot x := by
    intro Mot Z S hMot hZ hS
    refine ⟨?_, fun x hx => ⟨?_, ?_⟩⟩
    · obtain ⟨X, hX, hfold⟩ := flatIota_noLevels (ψ := oneLv) M M.iota_rule hcv hf htyT rfl
        (krl := r0) (by simp) (by rw [hc0]; exact hfZ) hlZ (by rw [htZ]; rfl) hrhs0
        (by rw [hbs0]; rfl) (by decide : 1 < 3) (hfitG Mot Z S _ hMot hZ hS hF.zeroMem) rfl hpb
        rfl (by rw [hlZ]; rfl) (by rw [hc0]; rfl)
      have hX' : X = Z := by simpa using hX.symm
      rw [hfold, hX']
    · have hbsl : b1.length = 3 + 1 := by
        have := congrArg List.length hbs1
        simpa using this
      obtain ⟨H, Y, -, hY, hfold, -⟩ := noParamsIota M M.iota_rule hf htyT rfl (krl := r1)
        (by simp) (by rw [hc1]; exact hfS) hrhs1 hbsl
        (by simp only [List.map_take, hbs1]; rfl) (ls := [])
        (fbs := [(natK, { pw := PropWhen.never })]) (Cc := natK)
        (by rw [hlS, htS]; exact inst_self [] _) rfl rfl
        (by simp only [List.map_drop, hbs1]; rfl)
        (hfitG Mot Z S _ hMot hZ hS (hF.succMem x hx)) rfl hpb rfl
        (K := M.cval natSuccName oneLv) (Fs := [x]) (by rw [hc1]; exact (hF.succD _ _).mpr rfl)
        (.cons ((hF.natD _ _).mpr rfl) hx .nil) rfl rfl
      -- the body `succ n (Nat.rec motive zero succ n)`, at the prefix and the field
      have e0 : pushAll ([Mot, Z, S] ++ [x]) ρ 0 = x := by simp [pushAll]
      have e1 : pushAll ([Mot, Z, S] ++ [x]) ρ 1 = S := by simp [pushAll]
      have e2 : pushAll ([Mot, Z, S] ++ [x]) ρ 2 = Z := by simp [pushAll]
      have e3 : pushAll ([Mot, Z, S] ++ [x]) ρ 3 = Mot := by simp [pushAll]
      have hY' : Denotes M.cval env oneLv (pushAll ([Mot, Z, S] ++ [x]) ρ) (natSuccBody p)
          (app (app S x) ([Mot, Z, S, x].foldl app (M.cval natRecKey oneLv))) := by
        have h := Denotes.app (Denotes.app (cval := M.cval) (env := env) (φ := oneLv)
          (ρ := pushAll ([Mot, Z, S] ++ [x]) ρ) (f := .bvar 1) (a := .bvar 0) .bvar .bvar)
          (Denotes.app (Denotes.app (Denotes.app (Denotes.app (hRcD _) (.bvar (i := 3)))
            (.bvar (i := 2))) (.bvar (i := 1))) (.bvar (i := 0)))
        rw [e0, e1, e2, e3] at h
        exact h
      rw [hfold, Denotes_functional hY hY']
    · obtain ⟨T, hT, hm⟩ := mem_key M hf oneLv ρ
      obtain ⟨RR, hRR, hmR⟩ := fits_app_mem (hfitG Mot Z S x hMot hZ hS hx) hT hm
      have hRR' : Denotes M.cval env oneLv (push x (push S (push Z (push Mot ρ))))
          (.app (.bvar 3) (.bvar 0)) (app Mot x) := .app .bvar .bvar
      rwa [Denotes_functional hRR hRR'] at hmR
  have hAppConst : ∀ {A : V → V} {D : V} {x : V}, x ∈ˢ D →
      app (lamR 1 D A) x = A x := fun hx => app_lamR_pos (by decide) hx
  refine ⟨fun x hx heq => ?_, fun x y hx hy heq => ?_⟩
  · -- the motive `fun _ => Prop`, the minors `∅` and `fun _ _ => eqv ∅ ∅`
    let Mot : V := lamR 1 NatS (fun _ => univ 0)
    let B : V := eqv (empty : V) empty
    let S : V := lamR 1 NatS (fun _ => lamR 1 (univ 0) (fun _ => B))
    have hMa : ∀ {n : V}, n ∈ˢ NatS → app Mot n = univ 0 := fun hn => hAppConst hn
    have hMot : Mot ∈ˢ piR 1 NatS (fun _ => univ 1) := lamR_mem fun _ _ => univ_mem_univ 0
    have hZ : (empty : V) ∈ˢ app Mot (M.cval natZeroName oneLv) := by
      rw [hMa hF.zeroMem]; exact empty_mem_univ 0
    have hS : S ∈ˢ piR 1 NatS (fun n => piR 1 (app Mot n)
        (fun _ => app Mot (app (M.cval natSuccName oneLv) n))) := by
      refine lamR_mem fun n hn => ?_
      have e : piR 1 (app Mot n) (fun _ => app Mot (app (M.cval natSuccName oneLv) n)) =
          piR 1 (univ 0) (fun _ => (univ 0 : V)) := by
        rw [hMa hn, hMa (hF.succMem n hn)]
      rw [e]
      exact lamR_mem fun _ _ => eqv_mem_univ _ _
    obtain ⟨hz, hs⟩ := hrules Mot empty S hMot hZ hS
    obtain ⟨hsx, hRx⟩ := hs x hx
    rw [hMa hx] at hRx
    have hv : app (app S x) ([Mot, empty, S, x].foldl app (M.cval natRecKey oneLv)) = B := by
      rw [show app S x = lamR 1 (univ 0) (fun _ => B) from hAppConst hx]
      exact hAppConst hRx
    have hEB : (empty : V) = B := by rw [← hz, heq, hsx, hv]
    have hpt : (pt : V) ∈ˢ B := pt_mem_eqv_self _
    rw [← hEB] at hpt
    exact not_mem_empty _ hpt
  · -- the motive `fun _ => Nat`, the minors `zero` and `fun n _ => n`: the predecessor
    let Mot : V := lamR 1 NatS (fun _ => NatS)
    let S : V := lamR 1 NatS (fun n => lamR 1 NatS (fun _ => n))
    have hMa : ∀ {n : V}, n ∈ˢ NatS → app Mot n = NatS := fun hn => hAppConst hn
    have hMot : Mot ∈ˢ piR 1 NatS (fun _ => univ 1) := lamR_mem fun _ _ => hNatU
    have hZ : M.cval natZeroName oneLv ∈ˢ app Mot (M.cval natZeroName oneLv) := by
      rw [hMa hF.zeroMem]; exact hF.zeroMem
    have hS : S ∈ˢ piR 1 NatS (fun n => piR 1 (app Mot n)
        (fun _ => app Mot (app (M.cval natSuccName oneLv) n))) := by
      refine lamR_mem fun n hn => ?_
      have e : piR 1 (app Mot n) (fun _ => app Mot (app (M.cval natSuccName oneLv) n)) =
          piR 1 NatS (fun _ => NatS) := by
        rw [hMa hn, hMa (hF.succMem n hn)]
      rw [e]
      exact lamR_mem fun _ _ => hn
    obtain ⟨-, hs⟩ := hrules Mot _ S hMot hZ hS
    have hpred : ∀ z, z ∈ˢ NatS →
        [Mot, M.cval natZeroName oneLv, S, app (M.cval natSuccName oneLv) z].foldl app
          (M.cval natRecKey oneLv) = z := by
      intro z hz
      obtain ⟨hsz, hRz⟩ := hs z hz
      rw [hMa hz] at hRz
      rw [hsz, show app S z = lamR 1 NatS (fun _ => z) from hAppConst hz]
      exact hAppConst hRz
    rw [← hpred x hx, ← hpred y hy, heq]

/-- **`litSet` is injective** at `oneLv`, by `natRec_sep`. -/
theorem litSet_inj_rec (M : Model V env) (hN : NatBasis env) (hR : NatRecStored env) :
    ∀ {a b : Nat}, litSet M oneLv a = litSet M oneLv b → a = b := by
  have hF := natFacts M hN oneLv
  obtain ⟨hzs, hinj⟩ := natRec_sep M hN hR
  have hmem : ∀ n, litSet M oneLv n ∈ˢ M.cval natName oneLv := by
    intro n
    induction n with
    | zero => exact hF.zeroMem
    | succ n ih => exact hF.succMem _ ih
  intro a
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ b => exact absurd h (hzs _ (hmem b))
  | succ a ih =>
    intro b h
    cases b with
    | zero => exact absurd h.symm (hzs _ (hmem a))
    | succ b => exact congrArg (· + 1) (ih (hinj _ _ (hmem a) (hmem b) h))

end Sem

/-! ## Numerals, and the answer -/

/-- **What separates numerals by `Nat.rec`**: `Nat` and its constructors, and its recursor. -/
structure NumeralBasisN (env : KEnv) : Prop where
  nat : NatBasis env
  natRec : NatRecStored env

/-- `NumeralBasisN`, decided. -/
def numeralBasisNB (env : KEnv) : Bool := natBasisB env && natRecB env

theorem numeralBasisN_of_check {env : KEnv} (h : numeralBasisNB env = true) :
    NumeralBasisN env := by
  simp only [numeralBasisNB, Bool.and_eq_true] at h
  exact ⟨natBasis_of h.1, natRecStored_of_check h.2⟩

/-- **Two numerals with the same denotation as one term are equal**, by `Nat.rec`. -/
theorem sameDenotation_lit_unique_rec {env : KEnv} (hB : NumeralBasisN env)
    {V : Type u} [Ix.Kernel.SetTheory V] (M : Model V env) {t : KExpr} {a b : Nat}
    (ha : SameDenotation.{u} env t (litE a)) (hb : SameDenotation.{u} env t (litE b)) : a = b := by
  obtain ⟨X, hX, hXa⟩ := ha V M oneLv (fun _ => empty)
  obtain ⟨Y, hY, hYb⟩ := hb V M oneLv (fun _ => empty)
  obtain rfl : X = Y := Denotes_functional hX hY
  have hF := natFacts M hB.nat oneLv
  have h1 : X = litSet M oneLv a := (lit_den M hF (fun _ => empty) a X).mp hXa
  have h2 : X = litSet M oneLv b := (lit_den M hF (fun _ => empty) b X).mp hYb
  exact litSet_inj_rec M hB.nat hB.natRec (h1.symm.trans h2)

/-- **The answer is unique** at a `Nat` result, if a set theory with the kernel's universes exists
and the admitted environment stores `Nat`, its constructors and its recursor
(`numeralBasisNB`): no `Nat.beq`, no `Bool`, no witness theorem. -/
theorem agrees_unique_rec {claim : Claim} {acc : Src.KernelFront.Accepted}
    (hV : ∃ V : Type u, Nonempty (Ix.Kernel.SetTheory V))
    (hB : numeralBasisNB acc.env = true) (hres : claim.abi.result = ResTy.nat)
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
      exact congrArg Answer.nat (sameDenotation_lit_unique_rec (numeralBasisN_of_check hB) M hs1 hs2)

end IxCC.Correct
