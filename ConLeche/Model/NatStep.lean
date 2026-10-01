module

public import ConLeche.Model.NatWf
import ConLeche.Model.Rules.Inputs

public section

/-!
# The literal tier's two semantic rows (task #161, task #305 R-nat)

`Rules.NatSuccRow` and `Rules.NatOpRow` (`Model/Rules/Inputs.lean`),
discharged: `Bridge/ReduceNat.lean`'s branch analysis at the
validated-annotation currency, standing on the sixteen numeral
transports (`NatSemP.lean`, `NatWfP.lean`) instead of `Red.sound` —
which is what the wall record said the P lane would have to do,
because `Red`'s soundness consumes `EnvSHyp.nat_ops` at the *collapse*
currency and the erasure factoring is refuted at the stored
operations' λ-towers.

The two pieces the seal-II record scoped as owed are in place here:
`EnvModelM.nat_ops` and `EnvModelM.div_mod` (the recurrence laws, from
the run certificates) and the transports.  The third — the whnf IH —
belonged to the RUN side, and the rules tier retired it with the run
rows themselves: `Rules.RulesInputs`' two literal fields
(`Model/Rules/Inputs.lean`) ARE these rows, and `Model/Capstone.lean`'s
`Rules.RulesInputs.ofSem` is where the two theorems below are read into
the bundle.

The reduct's reading, grading and frame conditions are unchanged from
`Steps/Nat.lean`'s leaf analysis, which was always premise-free; what
lands here is the `interp` equality, and with it the wall.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported natOpResult reduceNatFueled)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The pieces the rows read -/

/-- Whatever `rawNatLit?` accepts reads to the numeral spine it
reports — its two shapes are the literal itself and the `Nat.zero`
constant, and `natLit … 0` *is* the `Nat.zero` leaf
(`denote_rawNatLitR`'s mirror). -/
theorem denoteMeta_rawNatLit (m : EnvModel V env)
    (hs : natLitSupported env = true) {a0 : Expr} {n : Nat}
    (h : ConLeche.rawNatLit? a0 = some n) (d : Nat) :
    denoteMeta m.acval env φ d a0 = some (natLit m φ n) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  match a0, h with
  | .lit (.natVal k), h =>
    obtain rfl : k = n := Option.some.inj h
    exact denoteMeta_natLit_spine m hs d k
  | .const c [], h =>
    simp only [ConLeche.rawNatLit?] at h
    split at h
    · next hc =>
      subst hc
      obtain rfl : (0 : Nat) = n := Option.some.inj h
      rw [natLit_zero]
      exact denoteMeta_levelless_const hfZ
        (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
          = [] from hlpZ)
    · exact nomatch h

/-- A stored level-monomorphic head's reading, inverted. -/
theorem denoteMeta_head {m : EnvModel V env} {d : Nat} {c : Name}
    {ci : ConstantInfo} {fa : AnnotTerm}
    (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = [])
    (h : denoteMeta m.acval env φ d (.const c []) = some fa) :
    fa = m.acval c φ :=
  (Option.some.inj ((denoteMeta_levelless_const hf hlp).symm.trans h)).symm

/-! ## The two semantic rows

The literal accelerations' semantic content, at the shapes
`reduceNat` fires on and with the arguments already at literal
readings: `Rules.NatSuccRow` and `Rules.NatOpRow`
(`Model/Rules/Inputs.lean`).  The run inversion that puts a
`reduceNat` run into these shapes — the `whnf`/`rawNatLit?` case
analysis and the whnf IH at the two arguments — is the bridge's
`reduceNat_bridge` (`Verify/Rules/RedBridge.lean`), whose `Red.natSucc`/
`Red.natOp` derivations `Red.natSucc_sound`/`Red.natOp_sound` read
through these rows; the old run rows went with `Model/Steps/*` at the
task #305 closing. -/

/-- **`NatSuccRow`, proved.**  At a literal reading of the argument
the `Nat.succ` application *is* the packed numeral: the head reads to
the `Nat.succ` leaf, the argument to the numeral spine, and
`natLit_succ` is the packing. -/
theorem natSuccRow_of (mp : EnvModelM V μ env) (φ : Name → Nat) :
    Rules.NatSuccRow mp.base2 φ := by
  intro d w n Δa ea hnat hraw hea hg
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hnat
  obtain ⟨fa, wa, hfa, hwa, rfl⟩ := denoteMeta_app_inv hea
  obtain rfl : fa = mp.base2.acval ConLeche.natSuccName φ :=
    denoteMeta_head hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS) hfa
  obtain rfl : wa = natLit mp.base2 φ n :=
    Option.some.inj
      (hwa.symm.trans (denoteMeta_rawNatLit mp.base2 hnat hraw d))
  refine ⟨natLit mp.base2 φ (n + 1),
    denoteMeta_natLit_spine mp.base2 hnat d (n + 1), ?_, ?_⟩
  · rw [natLit_succ]
    exact hg
  · intro ρ _
    rw [natLit_succ]

set_option maxHeartbeats 1600000 in
/-- **`NatOpRow`, proved.**  The fourteen certified binary operations
at two literal readings: the head reads to the stored operation's
leaf, the arguments to the numeral spines, and the operation's own
recurrence law (`EnvModelM.nat_ops` / `EnvModelM.div_mod`, through the
`natOpV_*` transports) computes the interpretation of `natOpResult`. -/
theorem natOpRow_of (mp : EnvModelM V μ env) (φ : Name → Nat) :
    Rules.NatOpRow mp.base2 φ := by
  intro d c wa wb r n₁ n₂ Δa ea hc hstored hrawa hrawb hres hea hg
  have h14 : c = ConLeche.natAddName ∨ c = ConLeche.natSubName ∨
      c = ConLeche.natMulName ∨ c = ConLeche.natPowName ∨
      c = ConLeche.natBeqName ∨ c = ConLeche.natBleName ∨
      c = ConLeche.natDivName ∨ c = ConLeche.natModName ∨
      c = ConLeche.natGcdName ∨ c = ConLeche.natLandName ∨
      c = ConLeche.natLorName ∨ c = ConLeche.natXorName ∨
      c = ConLeche.natShiftLeftName ∨ c = ConLeche.natShiftRightName := by
    simpa [_root_.ConLeche.Rules.natBinOpNames, ConLeche.natDivModNames]
      using hc
  have hmemN : c ∈ ConLeche.natOpNames ∨ c ∈ ConLeche.natDivModNames := by
    rcases h14 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact Or.inl (by decide)
      | exact Or.inr (by decide)
  have hguard := natOpGuardLaw_of mp _ hmemN hstored
  obtain ⟨hnat, hdeps, hbool⟩ := ConLeche.natOpGuard_inv hguard
  have hself : c ∈ ConLeche.natOpDeps c := by
    rcases h14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
      rfl|rfl <;> decide
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps c hself
  obtain ⟨fab, ba, hfab, hba', rfl⟩ := denoteMeta_app_inv hea
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hfab
  obtain rfl : fa = mp.base2.acval c φ :=
    denoteMeta_head hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc) hfa
  obtain rfl : aa = natLit mp.base2 φ n₁ :=
    Option.some.inj
      (haa.symm.trans (denoteMeta_rawNatLit mp.base2 hnat hrawa d))
  obtain rfl : ba = natLit mp.base2 φ n₂ :=
    Option.some.inj
      (hba'.symm.trans (denoteMeta_rawNatLit mp.base2 hnat hrawb d))
  -- the two reduct shapes `natOpResult` can take
  have close : ∀ K : Nat, r = .lit (.natVal K) →
      (∀ ρ : Nat → V, SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval c φ))
        (interp V ρ (natLit mp.base2 φ n₁)))
        (interp V ρ (natLit mp.base2 φ n₂))
        = interp V ρ (natLit mp.base2 φ K)) →
      ∃ ra, denoteMeta mp.base2.acval env φ d r = some ra ∧
        Rules.Graded V Δa ra ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ((.app (.app (mp.base2.acval c φ)
              (natLit mp.base2 φ n₁)) (natLit mp.base2 φ n₂) : AnnotTerm))
            = interp V ρ ra := by
    intro K hr hop
    subst hr
    refine ⟨natLit mp.base2 φ K,
      denoteMeta_natLit_spine mp.base2 hnat d K, fun ρ _ => ?_,
      fun ρ _ => ?_⟩
    · exact (natLit_facts mp.base2 (mp.nat_heads φ) mp.acvalValid hnat
        ρ K).1
    · rw [interp_app, interp_app]
      exact hop ρ
  have closeB : (c = ConLeche.natBeqName ∨ c = ConLeche.natBleName) →
      ∀ bn : Name,
      (bn = ConLeche.boolTrueName ∨ bn = ConLeche.boolFalseName) →
      r = .const bn [] →
      (∀ ρ : Nat → V, SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval c φ))
        (interp V ρ (natLit mp.base2 φ n₁)))
        (interp V ρ (natLit mp.base2 φ n₂))
        = interp V ρ (mp.base2.acval bn φ)) →
      ∃ ra, denoteMeta mp.base2.acval env φ d r = some ra ∧
        Rules.Graded V Δa ra ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ((.app (.app (mp.base2.acval c φ)
              (natLit mp.base2 φ n₁)) (natLit mp.base2 φ n₂) : AnnotTerm))
            = interp V ρ ra := by
    intro hcb bn hbn hr hop
    subst hr
    obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ := hbool
      (by rcases hcb with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl))
    have hread : denoteMeta mp.base2.acval env φ d (.const bn [])
        = some (mp.base2.acval bn φ) := by
      rcases hbn with rfl | rfl
      · exact denoteMeta_levelless_const hfT hlpT
      · exact denoteMeta_levelless_const hfF hlpF
    refine ⟨mp.base2.acval bn φ, hread, fun ρ _ => ?_, fun ρ _ => ?_⟩
    · exact ⟨mp.base2.acval_wellDenoted _ _ ρ, mp.acvalValid _ _ ρ⟩
    · rw [interp_app, interp_app]
      exact hop ρ
  rcases h14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_add mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
        mp.acvalValid hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_sub mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
        mp.acvalValid hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_mul mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
        mp.acvalValid hfc ρ n₁ n₂)
  · -- `pow`: the reduct exists only below the official exponent cap
    exact close _ (by
        have hres' := hres
        simp +decide [natOpResult] at hres'
        exact hres'.2.symm)
      (fun ρ => natOpV_pow mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
        mp.acvalValid hfc ρ n₁ n₂)
  · refine closeB (Or.inl rfl)
      (if n₁ = n₂ then ConLeche.boolTrueName else ConLeche.boolFalseName)
      (by by_cases hh : n₁ = n₂ <;> simp [hh])
      (by simpa +decide [natOpResult] using hres.symm) ?_
    exact fun ρ => natOpV_beq mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
      mp.acvalValid hfc ρ n₁ n₂
  · refine closeB (Or.inr rfl)
      (if n₁ ≤ n₂ then ConLeche.boolTrueName else ConLeche.boolFalseName)
      (by by_cases hh : n₁ ≤ n₂ <;> simp [hh])
      (by simpa +decide [natOpResult] using hres.symm) ?_
    exact fun ρ => natOpV_ble mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
      mp.acvalValid hfc ρ n₁ n₂
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_div (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_mod (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_gcd (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_land (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_lor (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_xor (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_shiftLeft (mp.nat_ops φ) (mp.nat_heads φ)
        mp.acvalValid (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_shiftRight (mp.nat_ops φ) (mp.nat_heads φ)
        mp.acvalValid (mp.div_mod φ) hfc ρ n₁ n₂)

end ConLeche.Model
