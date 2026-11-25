import IxCCCorrect.UniqueNat

/-!
# The answer is unique at an enumeration result (`IxCCCorrect.UniqueEnum`)

At an enumeration result an answer is an index into the claim's constructor list, and its kernel
term is the constructor at that index (`answerTerm`). Two agreeing answers name constructors with
one denotation in every model; this module separates distinct constructors of an enumeration
through the **ι-law of the enumeration's recursor**, as `IxCCCorrect.UniqueIota` does for `Bool`:

```lean
agrees_unique_enum : (∃ V : Type u, Nonempty (SetTheory V)) → claim.abi.result = .enum cs →
  enumUniqueB acc cs D ks kr = true → Agrees claim acc xs a → Agrees claim acc xs b → a = b
```

**The argument** (`enum_ctor_ne`). Apply the stored `D.rec.{1}` to the motive `fun _ => Prop`, the
minors `eqv ∅ ∅` at constructor `j₁` and `∅` at every other, and a major: ι at rule `j`
(`flatIota_noLevels`) makes the application the `j`-th minor. Equal constructors `j₁ ≠ j₂` would
make `eqv ∅ ∅` and `∅` one set.

**What it reads** (`enumUniqueB`, decided; `D`, `ks` and `kr` are found by the caller and only
checked): the claim's addresses have pairwise distinct keys, each among `ks`; at `kr` a recursor of
the enumeration's shape over `ks` in rule order (`enumRecB`: one level parameter, the type
`{motive : D → Sort u} → motive k₀ → … → (t : D) → motive t` with the motive not a proposition at
`u = 1`, rule `j` the constructor `ks[j]` with body its minor); `D` without level parameters; each
constructor without parameters, fields or level parameters, of type `D`.
-/

set_option autoImplicit false

namespace IxCC.Correct

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Grounding

universe u

/-! ## The enumeration's recursor, decided -/

/-- The domain of minor premise `j`, for constructor `k`: `motive k` under `j` binders. -/
def enumMinorDom (j : Nat) (k : KKey) : KExpr := .app (.bvar j) (.const k [])

/-- The minor premises' domains, from binder depth `j` on. -/
def minorDoms : Nat → List KKey → List KExpr
  | _, [] => []
  | j, k :: ks => enumMinorDom j k :: minorDoms (j + 1) ks

theorem minorDoms_length : ∀ (j : Nat) (ks : List KKey), (minorDoms j ks).length = ks.length
  | _, [] => rfl
  | j, _ :: ks => by simp [minorDoms, minorDoms_length (j + 1) ks]

/-- The domains (with binder data) of the first `n` `∀`s, and what is under them. -/
def piDoms : Nat → KExpr → Option (List (KExpr × BinderMeta) × KExpr)
  | 0, e => some ([], e)
  | n + 1, .forallE d b m => (piDoms n b).map fun r => ((d, m) :: r.1, r.2)
  | _ + 1, _ => none

theorem piDoms_sound : ∀ (n : Nat) {e body : KExpr} {bs : List (KExpr × BinderMeta)},
    piDoms n e = some (bs, body) → e = piTele bs body ∧ bs.length = n
  | 0, e, body, bs, h => by
    simp only [piDoms, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, e, body, bs, h => by
    cases e with
    | forallE d b m =>
      cases hr : piDoms n b with
      | none => simp [piDoms, hr] at h
      | some r =>
        obtain ⟨bs', body'⟩ := r
        simp [piDoms, hr] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, hl⟩ := piDoms_sound n hr
        exact ⟨rfl, by simp [hl]⟩
    | _ => simp [piDoms] at h

/-- **The stored enumeration** `D`, its constructors `ks` in rule order, and its recursor `kr`. -/
structure EnumRecStored (env : KEnv) (D : KKey) (ks : List KKey) (kr : KKey) : Prop where
  ind : ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon),
    env.find? D = some (.indInfo cv caps) ∧ cv.levelParams = []
  ctors : ∀ k ∈ ks, ∃ cv : ConstantVal .anon,
    env.find? k = some (.ctorInfo cv 0 0) ∧ cv.levelParams = [] ∧ cv.type = .const D []
  stored : ∃ (cvr : ConstantVal .anon) (rules : List (RecRule .anon)) (p : LevelParam)
      (m0 m1 m4 : BinderMeta) (tbs : List (KExpr × BinderMeta)),
    env.find? kr = some (.recInfo cvr (ks.length + 1) (ks.length + 1) rules) ∧
    cvr.levelParams = [p] ∧
    cvr.type = .forallE (.forallE (.const D []) (.sort (.param p)) m1)
      (piTele tbs (.forallE (.const D []) (.app (.bvar (ks.length + 1)) (.bvar 0)) m4)) m0 ∧
    tbs.map (·.1) = minorDoms 0 ks ∧ m1.pw.holds oneLv = false ∧
    ∀ (j : Nat) (k : KKey), ks[j]? = some k → ∃ rl, rules[j]? = some rl ∧ rl.ctor = k ∧
      ∃ bs : List (KExpr × BinderMeta), rl.rhs = lamTele bs (.bvar (ks.length - 1 - j)) ∧
        bs.map (·.1) = .forallE (.const D []) (.sort (.param p)) m1 :: minorDoms 0 ks

/-- `EnumRecStored`, decided. -/
def enumRecB (env : KEnv) (D : KKey) (ks : List KKey) (kr : KKey) : Bool :=
  (match env.find? D with
    | some (.indInfo cv _) => cv.levelParams.isEmpty
    | _ => false) &&
  ks.all (fun k => match env.find? k with
    | some (.ctorInfo cv 0 0) => cv.levelParams.isEmpty && decide (cv.type = .const D [])
    | _ => false) &&
  match env.find? kr with
  | some (.recInfo cvr mI rP rules) =>
    match cvr.levelParams, cvr.type with
    | [p], .forallE (.forallE e0 e1 m1) rest _ =>
      decide (mI = ks.length + 1) && decide (rP = ks.length + 1) &&
      decide (e0 = .const D []) && decide (e1 = .sort (.param p)) && !(m1.pw.holds oneLv) &&
      (match piDoms ks.length rest with
        | some (tbs, .forallE d b _) =>
          decide (tbs.map (·.1) = minorDoms 0 ks) && decide (d = .const D []) &&
            decide (b = .app (.bvar (ks.length + 1)) (.bvar 0))
        | _ => false) &&
      (List.range ks.length).all fun j =>
        match ks[j]?, rules[j]? with
        | some k, some rl => decide (rl.ctor = k) &&
            decide (lamDoms (ks.length + 1) rl.rhs =
              some (.forallE e0 e1 m1 :: minorDoms 0 ks, .bvar (ks.length - 1 - j)))
        | _, _ => false
    | _, _ => false
  | _ => false

theorem enumRecStored_of_check {env : KEnv} {D : KKey} {ks : List KKey} {kr : KKey}
    (h : enumRecB env D ks kr = true) : EnumRecStored env D ks kr := by
  unfold enumRecB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hD, hC⟩, h⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · split at hD
    · rename_i cv caps hf
      exact ⟨cv, caps, hf, List.isEmpty_iff.mp hD⟩
    · cases hD
  · intro k hk
    have := List.all_eq_true.mp hC k hk
    split at this
    · rename_i cv hf
      simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at this
      exact ⟨cv, hf, this.1, this.2⟩
    · cases this
  · split at h
    · rename_i cvr mI rP rules hf
      split at h
      · rename_i p e0 e1 m1 rest m0 hlp hty
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
        obtain ⟨⟨⟨⟨⟨⟨hmI, hrP⟩, he0⟩, he1⟩, hpw⟩, hT⟩, hR⟩ := h
        subst hmI hrP he0 he1
        split at hT
        · rename_i tbs d b m4 hpd
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hT
          obtain ⟨⟨htbs, hd⟩, hb⟩ := hT
          subst hd hb
          obtain ⟨hrest, -⟩ := piDoms_sound ks.length hpd
          subst hrest
          refine ⟨cvr, rules, p, m0, m1, m4, tbs, hf, hlp, hty, htbs, hpw, ?_⟩
          intro j k hj
          have hjl : j < ks.length := (List.getElem?_eq_some_iff.mp hj).1
          have hr := List.all_eq_true.mp hR j (List.mem_range.mpr hjl)
          cases hrj : rules[j]? with
          | none => simp [hj, hrj] at hr
          | some rl =>
            simp only [hj, hrj, Bool.and_eq_true, decide_eq_true_eq] at hr
            obtain ⟨hc, hl⟩ := hr
            obtain ⟨bs, hbs, hbsm⟩ := lamDoms_sound (ks.length + 1) hl
            exact ⟨rl, rfl, hc, bs, hbs, hbsm⟩
        · cases hT
      · cases h
    · cases h

/-! ## Distinct constructors, by ι -/

section Sem

variable {V : Type u} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- Sets fit the minor premises' telescope: each a proposition, the motive `fun _ => Prop`. -/
theorem fits_minors (M : Model V env) {φ : LevelParam → Nat} {ρ : BVarIdx → V} {D : KKey}
    {Mot : V} (hMot : ∀ k, (∃ cv : ConstantVal .anon, env.find? k = some (.ctorInfo cv 0 0) ∧
      cv.levelParams = [] ∧ cv.type = .const D []) → app Mot (M.cval k φ) = univ 0) :
    ∀ (ks : List KKey) (j : Nat) (tbs : List (KExpr × BinderMeta)) (pre As : List V) (C : KExpr),
      (∀ k ∈ ks, ∃ cv : ConstantVal .anon, env.find? k = some (.ctorInfo cv 0 0) ∧
        cv.levelParams = [] ∧ cv.type = .const D []) →
      tbs.map (·.1) = minorDoms j ks → pre.length = j → As.length = ks.length →
      (∀ A ∈ As, A ∈ˢ (univ 0 : V)) →
      Fits M.cval env φ (pushAll (Mot :: pre) ρ) (piTele tbs C) As
        (pushAll (Mot :: pre ++ As) ρ) C
  | [], j, tbs, pre, As, C, _, htbs, _, hAl, _ => by
    have h1 : tbs = [] := by simpa [minorDoms] using htbs
    have h2 : As = [] := List.eq_nil_of_length_eq_zero hAl
    subst h1 h2
    rw [List.append_nil]; exact .nil
  | k :: ks, j, tbs, pre, As, C, hks, htbs, hpl, hAl, hAs => by
    cases tbs with
    | nil => simp [minorDoms] at htbs
    | cons t tbs =>
      cases As with
      | nil => simp at hAl
      | cons A As =>
        obtain ⟨d, m⟩ := t
        simp only [List.map_cons, minorDoms, List.cons.injEq] at htbs
        obtain ⟨rfl, htbs⟩ := htbs
        have hk := hks k (List.mem_cons_self ..)
        rcases hk with ⟨cv, hfk, hlk, htk⟩
        have hvar : pushAll (Mot :: pre) ρ j = Mot := by
          have := pushAll_rev (Mot :: pre) ρ 0 (by simp)
          simpa [hpl] using this
        have hden : Denotes M.cval env φ (pushAll (Mot :: pre) ρ) (enumMinorDom j k)
            (app Mot (M.cval k φ)) := by
          have h := Denotes.app (cval := M.cval) (env := env) (φ := φ)
            (ρ := pushAll (Mot :: pre) ρ) (f := .bvar j) (a := .const k []) .bvar
            ((den_const0 hfk (by simp [ConstantInfo.toConstantVal, hlk])).mpr rfl)
          rwa [hvar] at h
        have hA : A ∈ˢ app Mot (M.cval k φ) := by
          rw [hMot k ⟨cv, hfk, hlk, htk⟩]; exact hAs A (List.mem_cons_self ..)
        have ih := fits_minors (φ := φ) (ρ := ρ) M hMot ks (j + 1) tbs (pre ++ [A]) As C
          (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) htbs (by simp [hpl])
          (by simpa using hAl) (fun A' hA' => hAs A' (List.mem_cons_of_mem _ hA'))
        have e1 : pushAll (Mot :: (pre ++ [A])) ρ = push A (pushAll (Mot :: pre) ρ) := by
          rw [← List.cons_append, pushAll_snoc]
        have e2 : Mot :: (pre ++ [A]) ++ As = Mot :: pre ++ A :: As := by simp
        rw [e1, e2] at ih
        exact .cons hden hA ih

/-- **Distinct constructors of a stored enumeration denote different sets** in every model (by ι
at its recursor; no stored theorem). -/
theorem enum_ctor_ne (M : Model V env) {D : KKey} {ks : List KKey} {kr : KKey}
    (hE : EnumRecStored env D ks kr) {j1 j2 : Nat} {k1 k2 : KKey} (hne : j1 ≠ j2)
    (h1 : ks[j1]? = some k1) (h2 : ks[j2]? = some k2) (φ : LevelParam → Nat) :
    M.cval k1 φ ≠ M.cval k2 φ := by
  intro heq
  obtain ⟨cvD, capsD, hfD, hlD⟩ := hE.ind
  obtain ⟨cvr, rules, p, m0, m1, m4, tbs, hf, hlp, hty, htbs, hpw, hrules⟩ := hE.stored
  have hcv : CvalParams M := M.cval_params
  have hk1 := hE.ctors k1 (List.mem_of_getElem? h1)
  have hk2 := hE.ctors k2 (List.mem_of_getElem? h2)
  obtain ⟨cv1, hf1, hl1, ht1⟩ := hk1
  obtain ⟨cv2, hf2, hl2, ht2⟩ := hk2
  have heq1 : M.cval k1 oneLv = M.cval k2 oneLv := by
    rw [hcv _ _ hf1 oneLv φ (by simp [ConstantInfo.toConstantVal, hl1]),
      hcv _ _ hf2 oneLv φ (by simp [ConstantInfo.toConstantVal, hl2]), heq]
  have hDl : (ConstantInfo.indInfo cvD capsD).toConstantVal.levelParams = [] := by
    simp [ConstantInfo.toConstantVal, hlD]
  let DS : V := M.cval D oneLv
  have hDD : ∀ ρ : BVarIdx → V, Denotes M.cval env oneLv ρ (.const D []) DS :=
    fun ρ => (den_const0 hfD hDl).mpr rfl
  have hctorMem : ∀ k, (∃ cv : ConstantVal .anon, env.find? k = some (.ctorInfo cv 0 0) ∧
      cv.levelParams = [] ∧ cv.type = .const D []) → M.cval k oneLv ∈ˢ DS := by
    rintro k ⟨cv, hfk, -, htk⟩
    obtain ⟨T, hT, hm⟩ := mem_key M hfk oneLv (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, htk] at hT
    rwa [(den_const0 hfD hDl).mp hT] at hm
  let n := ks.length
  have hn : n = ks.length := rfl
  let Mot : V := lamR 1 DS (fun _ => univ 0)
  let B : V := eqv (empty : V) empty
  let Amin : List V := (List.range n).map fun j => if j = j1 then B else empty
  have hAl : Amin.length = n := by simp [Amin]
  have hreg : regime oneLv m1.pw = 1 := by simp [regime, hpw]
  have hMot : Mot ∈ˢ piR (regime oneLv m1.pw) DS
      (fun _ => univ (Level.eval oneLv (.param p))) := by
    rw [hreg]; exact lamR_mem fun _ _ => univ_mem_univ 0
  have hMotA : ∀ k, (∃ cv : ConstantVal .anon, env.find? k = some (.ctorInfo cv 0 0) ∧
      cv.levelParams = [] ∧ cv.type = .const D []) → app Mot (M.cval k oneLv) = univ 0 :=
    fun k hk => app_lamR_pos (by decide) (hctorMem k hk)
  have hAm : ∀ A ∈ Amin, A ∈ˢ (univ 0 : V) := by
    intro A hA
    simp only [Amin, List.mem_map] at hA
    obtain ⟨j, -, rfl⟩ := hA
    split
    · exact eqv_mem_univ _ _
    · exact empty_mem_univ 0
  let C : KExpr := .forallE (.const D []) (.app (.bvar (n + 1)) (.bvar 0)) m4
  have hfit : ∀ K, K ∈ˢ DS →
      Fits M.cval env oneLv (fun _ => empty) cvr.type (Mot :: Amin ++ [K])
        (push K (pushAll (Mot :: Amin) (fun _ => empty))) (.app (.bvar (n + 1)) (.bvar 0)) := by
    intro K hK
    have hmin := fits_minors (φ := oneLv) (ρ := fun _ => empty) M hMotA ks 0 tbs [] Amin C
      hE.ctors htbs rfl hAl hAm
    have hsnoc := fits_snoc hmin (D := .const D []) (Bk := .app (.bvar (n + 1)) (.bvar 0))
      (m := m4) rfl (hDD _) hK
    have e : pushAll [Mot] (fun _ => (empty : V)) = push Mot (fun _ => empty) := by
      rw [show [Mot] = ([] : List V) ++ [Mot] from rfl, pushAll_snoc, pushAll_nil]
    rw [e] at hsnoc
    rw [hty]
    exact .cons (Denotes.pi (A := DS) (B := fun _ => univ (Level.eval oneLv (.param p)))
      (hDD _) (fun _ _ => .sort) (fun h => absurd h (by rw [hreg]; decide))) hMot hsnoc
  have htyT : cvr.type = piTele ((.forallE (.const D []) (.sort (.param p)) m1, m0) :: tbs) C := by
    rw [hty]; rfl
  have htbl : tbs.length = n := by
    have := congrArg List.length htbs
    simpa [minorDoms_length] using this
  have hpb : piBody (n + 1) cvr.type = C := by
    rw [htyT]
    have := piBody_piTele ((.forallE (.const D []) (.sort (.param p)) m1, m0) :: tbs) C
    simpa [htbl] using this
  -- ι at rule `j`: the application is the `j`-th minor
  have hrule : ∀ (j : Nat) (k : KKey), ks[j]? = some k →
      (Mot :: Amin ++ [M.cval k oneLv]).foldl app (M.cval kr oneLv) =
        if j = j1 then B else empty := by
    intro j k hj
    have hjl : j < n := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨rl, hrl, hc, bs, hbs, hbsm⟩ := hrules j k hj
    have hk := hE.ctors k (List.mem_of_getElem? hj)
    obtain ⟨cv, hfk, hlk, htk⟩ := hk
    have hF := hfit _ (hctorMem k ⟨cv, hfk, hlk, htk⟩)
    obtain ⟨X, hX, hfold⟩ := flatIota_noLevels (ψ := oneLv) M M.iota_rule hcv hf htyT
      (by simp [htbl, hn]) (krl := rl) (List.mem_of_getElem? hrl) (by rw [hc]; exact hfk) hlk
      (by rw [htk]; rfl) hbs (by rw [hbsm, List.map_cons, htbs]) (by omega : n - 1 - j < n + 1)
      hF (by simp [hAl, hn]) hpb rfl (by rw [hlk]; rfl) (by rw [hc]; simp [hAl, hn])
    rw [hfold]
    have hget : ((Mot :: Amin ++ [M.cval k oneLv]).take (n + 1)).reverse[n - 1 - j]? =
        some (if j = j1 then B else empty) := by
      have ht : (Mot :: Amin ++ [M.cval k oneLv]).take (n + 1) = Mot :: Amin := by
        rw [List.take_append_of_le_length (by simp [hAl]), List.take_of_length_le (by simp [hAl])]
      rw [ht, List.reverse_cons, List.getElem?_append_left (by simp [hAl]; omega),
        List.getElem?_reverse (by rw [hAl]; omega), hAl]
      have hidx : n - 1 - (n - 1 - j) = j := by omega
      rw [hidx]
      simp [Amin, hjl]
    rw [hget] at hX
    exact (Option.some.inj hX).symm
  have hT1 := hrule j1 k1 h1
  have hT2 := hrule j2 k2 h2
  rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)] at hT1
  rw [ite_eq_right_iff.mpr (fun h => absurd h (Ne.symm hne))] at hT2
  rw [heq1] at hT1
  have hBE : B = empty := hT1.symm.trans hT2
  have hpt : (pt : V) ∈ˢ B := pt_mem_eqv_self _
  rw [hBE] at hpt
  exact not_mem_empty _ hpt

end Sem

/-! ## The answer -/

/-- **What makes an enumeration answer unique**, decided: the claim's addresses have pairwise
distinct keys, each a constructor of `ks`, and `D`'s recursor over `ks` is stored as `enumRecB`
reads it. -/
def enumUniqueB (acc : Src.KernelFront.Accepted) (cs : List Ixon.Address) (D : KKey)
    (ks : List KKey) (kr : KKey) : Bool :=
  decide ((cs.map (keyOf acc)).Nodup) &&
    cs.all (fun a => match keyOf acc a with
      | some k => decide (k ∈ ks)
      | none => false) &&
    enumRecB acc.env D ks kr

/-- **The answer is unique** at an enumeration result, if a set theory with the kernel's
universes exists and the admitted environment stores the enumeration and its recursor as
`enumUniqueB` decides. -/
theorem agrees_unique_enum {claim : Claim} {acc : Src.KernelFront.Accepted}
    (hV : ∃ V : Type u, Nonempty (Ix.Kernel.SetTheory V)) {cs : List Ixon.Address}
    (hres : claim.abi.result = ResTy.enum cs) {D : KKey} {ks : List KKey} {kr : KKey}
    (hB : enumUniqueB acc cs D ks kr = true)
    {xs : List Nat} {a b : Nat} (ha : Agrees.{u} claim acc xs a) (hb : Agrees.{u} claim acc xs b) :
    a = b := by
  obtain ⟨V, ⟨inst⟩⟩ := hV
  haveI : Ix.Kernel.SetTheory V := inst
  obtain ⟨M⟩ := accepted_has_model V acc
  simp only [enumUniqueB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hB
  obtain ⟨⟨hnd, hin⟩, hrec⟩ := hB
  have hE := enumRecStored_of_check hrec
  unfold Agrees at ha hb
  obtain ⟨t1, o1, hk1, ht1, hs1⟩ := ha
  obtain ⟨t2, o2, hk2, ht2, hs2⟩ := hb
  rw [hk1] at hk2
  cases hk2
  simp only [answerTerm, hres] at ht1 ht2
  -- the answers' constructors
  cases hca : cs[a]? with
  | none => rw [hca] at ht1; cases ht1
  | some ca =>
    cases hcb : cs[b]? with
    | none => rw [hcb] at ht2; cases ht2
    | some cb =>
      rw [hca] at ht1
      rw [hcb] at ht2
      simp only [Option.bind_some] at ht1 ht2
      cases hka : keyOf acc ca with
      | none => rw [hka] at ht1; cases ht1
      | some ka =>
        cases hkb : keyOf acc cb with
        | none => rw [hkb] at ht2; cases ht2
        | some kb =>
          rw [hka] at ht1
          rw [hkb] at ht2
          simp only [Option.map_some, Option.some.injEq] at ht1 ht2
          subst ht1 ht2
          refine Classical.byContradiction fun hab => ?_
          -- distinct answers, distinct keys
          have hkne : ka ≠ kb := by
            intro hkk
            have hla := (List.getElem?_eq_some_iff.mp hca).1
            have hlb := (List.getElem?_eq_some_iff.mp hcb).1
            have hma : (cs.map (keyOf acc))[a]? = some (some ka) := by
              simp [hca, hka]
            have hmb : (cs.map (keyOf acc))[b]? = some (some kb) := by
              simp [hcb, hkb]
            rw [hkk] at hma
            exact hab ((List.Nodup.getElem?_inj (by simpa using hla) hnd).mp (hma.trans hmb.symm))
          -- both are constructors of `ks`, at different positions
          have hia : ka ∈ ks := by
            have := hin ca (List.mem_of_getElem? hca)
            rw [hka] at this
            exact of_decide_eq_true this
          have hib : kb ∈ ks := by
            have := hin cb (List.mem_of_getElem? hcb)
            rw [hkb] at this
            exact of_decide_eq_true this
          obtain ⟨j1, hj1⟩ := List.mem_iff_getElem?.mp hia
          obtain ⟨j2, hj2⟩ := List.mem_iff_getElem?.mp hib
          have hjne : j1 ≠ j2 := by
            intro hjj
            subst hjj
            rw [hj1] at hj2
            exact hkne (Option.some.inj hj2)
          -- the two constructor terms denote one set
          obtain ⟨cva, hfa, hla, -⟩ := hE.ctors ka hia
          obtain ⟨cvb, hfb, hlb, -⟩ := hE.ctors kb hib
          obtain ⟨X, hX, hXa⟩ := hs1 V M oneLv (fun _ => empty)
          obtain ⟨Y, hY, hYb⟩ := hs2 V M oneLv (fun _ => empty)
          obtain rfl : X = Y := Denotes_functional hX hY
          have e1 := (den_const0 hfa (by simp [ConstantInfo.toConstantVal, hla])).mp hXa
          have e2 := (den_const0 hfb (by simp [ConstantInfo.toConstantVal, hlb])).mp hYb
          exact enum_ctor_ne M hE hjne hj1 hj2 oneLv (e1.symm.trans e2)

end IxCC.Correct
