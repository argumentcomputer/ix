module

public import ConLeche.Verify.EnvWF
import ConLeche.Kernel.Checker

public section

/-!
# `V`-free readings of the environment's guards

The literal-support guards `natLitSupported` / `strLitSupported` are
`Bool`s the kernel computes from the environment; their inversion
(`_inv`) and their read-set (`_congr`) are facts about `Env.find?`
alone.  `EtaFamilyStored` is the kind- and arity-pinned premise under
which an eta capability is owed, and `EtaFamiliesClosed` its closure
over a block — again statements about what the environment stores.

None of them mentions a valuation, so every consumer takes them from
here: this module and `ConLeche/Verify/EnvPreds.lean` are the single
home of the environment's `V`-free readings.
-/

set_option linter.unusedVariables false
set_option linter.defProp false

namespace ConLeche

/-- The eta family of an eta-capable stored structure is complete: the
capability record's constructor is stored as a constructor, and every
documented projection function is stored as a (degenerate) recursor.
This is the *premise* under which `CapsOk` owes the eta law:
mid-block — the former is installed first, its constructor and
projection functions after it — the premise fails and the law is not
yet owed; the family-completing member's install discharges it.  The
premises are deliberately **kind-pinned**: an installation of a
non-constructor under the constructor's name (or a non-recursor under
a projection name) never completes the family, which is what keeps
the `CapsOk.cons` head obligations dischargeable at every install
site.  The constructor's own parameter and field counts are NOT
pinned to the record's: the law is stated at the record's counts, and
the η certificate works at them too, so the two never have to be
compared at a use. -/
@[expose] def EtaFamilyStored (env : Env) (T : Name) (caps : IndCaps) : Prop :=
  -- name-only conjunct (static in `caps`): a reserved-named capability
  -- constructor never completes a family, which keeps the basis
  -- installs' head obligations vacuous by computation
  reservedBasisNames.contains caps.etaCtor = false ∧
  (∃ cvC cnP cnF, env.find? caps.etaCtor = some (.ctorInfo cvC cnP cnF)) ∧
  ∀ j, j < caps.etaFields → ∃ cv mI rP rules,
    env.find? (projFnName T j) = some (.recInfo cv mI rP rules)

/-- A projection function is never a reserved basis name: `projFnName`
builds a `Name.num` node, and every reserved name is a `Name.str`. -/
theorem projFnName_ne_reserved {T n : Name} {j : Nat}
    (h : reservedBasisNames.contains n = true) : projFnName T j ≠ n := by
  intro hh
  subst hh
  simp only [reservedBasisNames, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, projFnName] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h <;> exact nomatch h

/-- Everything `natLitSupported` checked, as separate facts. -/
theorem natLitSupported_inv {env : Env} (hs : natLitSupported env = true) :
    ∃ cv caps cv0 i0 j0 cv1 i1 j1,
      env.find? natName = some (.indInfo cv caps) ∧
      env.find? natZeroName = some (.ctorInfo cv0 i0 j0) ∧
      env.find? natSuccName = some (.ctorInfo cv1 i1 j1) ∧
      cv.levelParams = [] ∧ cv0.levelParams = [] ∧ cv1.levelParams = [] ∧
      cv.type = .sort (.succ .zero) ∧ cv0.type = .const natName [] ∧
      ∃ mb, cv1.type = .forallE (.const natName []) (.const natName []) mb := by
  unfold natLitSupported at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨hi, hz⟩, hsc⟩ := hs
  unfold natIndOk at hi
  split at hi
  case h_2 => simp at hi
  next cv caps heqN =>
    unfold natZeroOk at hz
    split at hz
    case h_2 => simp at hz
    next cv0 i0 j0 heqZ =>
      unfold natSuccOk at hsc
      split at hsc
      case h_2 => simp at hsc
      next cv1 i1 j1 heqS =>
        simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hi hz hsc
        refine ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, heqN, heqZ, heqS,
          hi.1, hz.1, hsc.1, hi.2, hz.2, ?_⟩
        obtain ⟨-, h6⟩ := hsc
        revert h6
        split
        case h_2 => intro h; simp at h
        next c1 c2 mb heq =>
          intro h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          exact ⟨mb, by rw [heq, h.1, h.2]⟩

/-- The literal guard only reads the three `Nat` slots. -/
theorem natLitSupported_congr {env₁ env₂ : Env}
    (h1 : env₁.find? natName = env₂.find? natName)
    (h2 : env₁.find? natZeroName = env₂.find? natZeroName)
    (h3 : env₁.find? natSuccName = env₂.find? natSuccName) :
    natLitSupported env₁ = natLitSupported env₂ := by
  unfold natLitSupported
  rw [h1, h2, h3]

/-- Everything `strLitSupported` checked beyond `natLitSupported`, as
separate facts (level-parameter lists and exact annotated types of the
seven string-support constants). -/
theorem strLitSupported_inv {env : Env} (hs : strLitSupported env = true) :
    natLitSupported env = true ∧
    ∃ ciS ciO ciL ciN ciC ciH ciF pL pN pC,
      env.find? stringName = some ciS ∧
      env.find? stringOfListName = some ciO ∧
      env.find? listName = some ciL ∧
      env.find? listNilName = some ciN ∧
      env.find? listConsName = some ciC ∧
      env.find? charName = some ciH ∧
      env.find? charOfNatName = some ciF ∧
      ciS.toConstantVal.levelParams = [] ∧
      ciO.toConstantVal.levelParams = [] ∧
      ciL.toConstantVal.levelParams = [pL] ∧
      ciN.toConstantVal.levelParams = [pN] ∧
      ciC.toConstantVal.levelParams = [pC] ∧
      ciH.toConstantVal.levelParams = [] ∧
      ciF.toConstantVal.levelParams = [] ∧
      ciS.toConstantVal.type = .sort (.succ .zero) ∧
      ciH.toConstantVal.type = .sort (.succ .zero) ∧
      (∃ mb, ciO.toConstantVal.type =
        .forallE (.app (.const listName [.zero]) (.const charName []))
          (.const stringName []) mb) ∧
      (∃ mb, ciL.toConstantVal.type =
        .forallE (.sort (.succ (.param pL))) (.sort (.succ (.param pL))) mb) ∧
      (∃ mb, ciN.toConstantVal.type =
        .forallE (.sort (.succ (.param pN)))
          (.app (.const listName [.param pN]) (.bvar 0)) mb) ∧
      (∃ mb1 mb2 mb3, ciC.toConstantVal.type =
        .forallE (.sort (.succ (.param pC)))
          (.forallE (.bvar 0)
            (.forallE (.app (.const listName [.param pC]) (.bvar 1))
              (.app (.const listName [.param pC]) (.bvar 2)) mb3) mb2) mb1) ∧
      (∃ mb, ciF.toConstantVal.type =
        .forallE (.const natName []) (.const charName []) mb) := by
  unfold strLitSupported at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hnat, hS⟩, hO⟩, hL⟩, hN⟩, hC⟩, hH⟩, hF⟩ := hs
  refine ⟨hnat, ?_⟩
  unfold stringTyOk at hS
  unfold stringOfListTyOk at hO
  unfold listTyOk at hL
  unfold listNilTyOk at hN
  unfold listConsTyOk at hC
  unfold charTyOk at hH
  unfold charOfNatTyOk at hF
  split at hS; case h_2 => simp at hS
  next ciS heqS =>
  split at hO; case h_2 => simp at hO
  next ciO heqO =>
  split at hL; case h_2 => simp at hL
  next ciL heqL =>
  split at hN; case h_2 => simp at hN
  next ciN heqN =>
  split at hC; case h_2 => simp at hC
  next ciC heqC =>
  split at hH; case h_2 => simp at hH
  next ciH heqH =>
  split at hF; case h_2 => simp at hF
  next ciF heqF =>
  simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hS hH
  -- List: one level parameter, pinned type
  revert hL
  split; case h_2 => intro h; exact nomatch h
  next pL heqPL =>
  split
  case h_2 => intro h; simp at h
  next nmL u1L u2L mbL heqTL =>
  intro hL
  simp only [Bool.and_eq_true, beq_iff_eq] at hL
  -- List.nil
  revert hN
  split; case h_2 => intro h; exact nomatch h
  next pN heqPN =>
  split
  case h_2 => intro h; simp at h
  next nmN u1N l1N us1N mbN heqTN =>
  intro hN
  simp only [Bool.and_eq_true, beq_iff_eq] at hN
  -- List.cons
  revert hC
  split; case h_2 => intro h; exact nomatch h
  next pC heqPC =>
  split
  case h_2 => intro h; simp at h
  next nmC1 u1C nmC2 nmC3 l1C us1C l2C us2C mb3C mb2C mb1C heqTC =>
  intro hC
  simp only [Bool.and_eq_true, beq_iff_eq] at hC
  -- Char.ofNat
  revert hF
  simp only [Bool.and_eq_true, List.isEmpty_iff]
  rintro ⟨hF1, hF2⟩
  revert hF2
  split
  case h_2 => intro h; simp at h
  next c1F c2F mbF heqTF =>
  intro hF2
  simp only [Bool.and_eq_true, beq_iff_eq] at hF2
  -- String.ofList
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hO
  obtain ⟨hO1, hO2⟩ := hO
  revert hO2
  split
  case h_2 => intro h; simp at h
  next l1O us1O c1O c2O mbO heqTO =>
  intro hO2
  simp only [Bool.and_eq_true, beq_iff_eq] at hO2
  refine ⟨ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC,
    heqS, heqO, heqL, heqN, heqC, heqH, heqF,
    hS.1, hO1, heqPL, heqPN, heqPC, hH.1, hF1, hS.2, hH.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨mbO, by
      rw [heqTO, hO2.1.1.1, hO2.1.1.2, hO2.1.2, hO2.2]⟩
  · exact ⟨mbL, by rw [heqTL, hL.1, hL.2]⟩
  · exact ⟨mbN, by rw [heqTN, hN.1.1, hN.1.2, hN.2]⟩
  · exact ⟨mb1C, mb2C, mb3C, by
      rw [heqTC, hC.1.1.1.1, hC.1.1.1.2, hC.1.1.2, hC.1.2, hC.2]⟩
  · exact ⟨mbF, by rw [heqTF, hF2.1, hF2.2]⟩

/-- Every stored non-reserved eta-capable type former's constructor is
stored, at exactly the capability record's arities.  **Not** an
`EnvModel` clause: inside a block's install derivation the former is
stored before its constructor, so the intermediate models live in the
window where this fails for the freshly installed former.  It holds at
every declaration boundary and is threaded through the consistency
fold *next to* the model; constructor-installing sites consume it to
refute a fresh constructor completing an *older* former's eta family
(the older family's constructor slot is already taken). -/
@[expose] def EtaFamiliesClosed (env : Env) : Prop :=
  ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    reservedBasisNames.contains T = false →
    ∃ cvC, env.find? caps.etaCtor =
      some (.ctorInfo cvC caps.etaParams caps.etaFields)

theorem EtaFamiliesClosed.empty : EtaFamiliesClosed Env.empty := by
  intro T cvT caps h
  simp [Env.find?, Env.empty] at h

/-- Prepending one fresh constant that is not a non-reserved
eta-capable former keeps the stored eta families closed. -/
theorem EtaFamiliesClosed.cons_nonind {env : Env} {c₀ : ConstantInfo}
    (hE1 : EtaFamiliesClosed env)
    (hfresh : env.find? c₀.name = none)
    (hknd : ∀ cv caps, c₀ = .indInfo cv caps → caps.eta = true →
      reservedBasisNames.contains c₀.name = true) :
    EtaFamiliesClosed (⟨c₀ :: env.consts⟩ : Env) := by
  intro T cvT caps hf he hr
  rw [Env.find?_cons] at hf
  split at hf
  · next hh =>
    obtain rfl := Option.some.inj hf
    rw [← hh] at hr
    rw [hknd cvT caps rfl he] at hr
    exact nomatch hr
  · obtain ⟨cvC, hfC⟩ := hE1 T cvT caps hf he hr
    refine ⟨cvC, ?_⟩
    rw [Env.find?_cons_of_isSome hfresh (by rw [hfC]; rfl)]
    exact hfC

/-- **`EtaFamiliesClosed` for every stored family other than `T`**
(task #210 Part A): the shape a block's install carries between its
former's cons and its constructor's, where the block's own η-capable
family (the fixpoint route's structure-like block claims η at the
former's cons) is not yet complete. -/
@[expose] def EtaFamiliesClosedExcept (env : Env) (T : Name) : Prop :=
  ∀ (T' : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T' = some (.indInfo cvT caps) → T' ≠ T → caps.eta = true →
    reservedBasisNames.contains T' = false →
    ∃ cvC, env.find? caps.etaCtor =
      some (.ctorInfo cvC caps.etaParams caps.etaFields)

theorem EtaFamiliesClosed.except {env : Env} (h : EtaFamiliesClosed env) (T : Name) :
    EtaFamiliesClosedExcept env T :=
  fun T' cvT caps hf _ he hr => h T' cvT caps hf he hr

/-- Prepending one fresh constant that is neither a non-reserved
η-capable former nor named other than `T` keeps the other families
closed. -/
theorem EtaFamiliesClosedExcept.cons {env : Env} {T : Name} {c₀ : ConstantInfo}
    (hE1 : EtaFamiliesClosedExcept env T)
    (hfresh : env.find? c₀.name = none)
    (hknd : ∀ cv caps, c₀ = .indInfo cv caps → caps.eta = true →
      reservedBasisNames.contains c₀.name = true ∨ c₀.name = T) :
    EtaFamiliesClosedExcept (⟨c₀ :: env.consts⟩ : Env) T := by
  intro T' cvT caps hf hne he hr
  rw [Env.find?_cons] at hf
  split at hf
  · next hh =>
    obtain rfl := Option.some.inj hf
    rcases hknd cvT caps rfl he with hres | hT
    · rw [← hh] at hr; rw [hres] at hr; exact nomatch hr
    · exact absurd (hh.symm.trans hT) hne
  · obtain ⟨cvC, hfC⟩ := hE1 T' cvT caps hf hne he hr
    refine ⟨cvC, ?_⟩
    rw [Env.find?_cons_of_isSome hfresh (by rw [hfC]; rfl)]
    exact hfC

/-- The families are all closed once `T`'s own is. -/
theorem EtaFamiliesClosedExcept.closed {env : Env} {T : Name}
    (hE : EtaFamiliesClosedExcept env T)
    (hT : ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? T = some (.indInfo cvT caps) → caps.eta = true →
      reservedBasisNames.contains T = false →
      ∃ cvC, env.find? caps.etaCtor = some (.ctorInfo cvC caps.etaParams caps.etaFields)) :
    EtaFamiliesClosed env := by
  intro T' cvT caps hf he hr
  by_cases hne : T' = T
  · subst hne; exact hT cvT caps hf he hr
  · exact hE T' cvT caps hf hne he hr

/-- The extension shape every phase after a block's member fold has:
non-recursor entries survive verbatim (the recursor swap replaces its
own provisional entries), and no new former appears. -/
@[expose] def ExtEta (env env' : Env) : Prop :=
  (∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
    (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
    env'.find? n = some ci) ∧
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env'.find? T = some (.indInfo cvT caps) →
    env.find? T = some (.indInfo cvT caps))

theorem ExtEta.refl (env : Env) : ExtEta env env :=
  ⟨fun _ _ h _ => h, fun _ _ _ h => h⟩

theorem ExtEta.trans {e₁ e₂ e₃ : Env} (h₁ : ExtEta e₁ e₂)
    (h₂ : ExtEta e₂ e₃) : ExtEta e₁ e₃ :=
  ⟨fun n ci hf hnr => h₂.1 n ci (h₁.1 n ci hf hnr) hnr,
   fun T cvT caps hf => h₁.2 T cvT caps (h₂.2 T cvT caps hf)⟩

/-- One fresh install of a non-former. -/
theorem ExtEta.cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none)
    (hnotind : ∀ cv caps, c₀ ≠ .indInfo cv caps) :
    ExtEta env ⟨c₀ :: env.consts⟩ := by
  refine ⟨fun n ci hf _ => Env.find?_cons_of_fresh hfresh hf,
    fun T cvT caps hf => ?_⟩
  rw [Env.find?_cons] at hf
  split at hf
  · exact absurd (Option.some.inj hf) (hnotind cvT caps)
  · exact hf

/-- Closure transfers along `ExtEta`. -/
theorem EtaFamiliesClosed.keep {env env' : Env}
    (hE : EtaFamiliesClosed env) (hx : ExtEta env env') :
    EtaFamiliesClosed env' := by
  intro T cvT caps hf he hr
  obtain ⟨cvC, hfC⟩ := hE T cvT caps (hx.2 T cvT caps hf) he hr
  exact ⟨cvC, hx.1 _ _ hfC (fun _ _ _ _ hh => nomatch hh)⟩

/-! ## The guard, inverted -/

/-- Everything `natOpGuard` checked, as separate facts. -/
theorem natOpGuard_inv {c : Name} (h : natOpGuard env c = true) :
    natLitSupported env = true ∧
    (∀ n ∈ natOpDeps c, ∃ cvn vn hn,
      env.find? n = some (.defnInfo cvn vn hn) ∧ cvn.levelParams = []) ∧
    ((c = natBeqName ∨ c = natBleName ∨ c ∈ natDivModNames) →
      (∃ ciT, env.find? boolTrueName = some ciT ∧
        ciT.toConstantVal.levelParams = []) ∧
      (∃ ciF, env.find? boolFalseName = some ciF ∧
        ciF.toConstantVal.levelParams = [])) := by
  unfold natOpGuard at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hs, hdeps⟩, hbool⟩ := h
  refine ⟨hs, ?_, ?_⟩
  · intro n hn
    have := List.all_eq_true.mp hdeps n hn
    revert this
    split
    · next cvn vn hn heq =>
      intro hlp
      exact ⟨cvn, vn, hn, heq, List.isEmpty_iff.mp (by simpa using hlp)⟩
    · intro hh; exact nomatch hh
  · intro hc
    have hcb : (c = natBeqName || c = natBleName ||
        natDivModNames.contains c) = true := by
      rcases hc with rfl | rfl | hm
      · simp
      · simp
      · rw [List.contains_iff_mem.mpr hm, Bool.or_true]
    rw [if_pos hcb] at hbool
    simp only [Bool.and_eq_true] at hbool
    obtain ⟨hT, hF⟩ := hbool
    constructor
    · revert hT
      split
      · next ciT heq =>
        intro hlp
        exact ⟨ciT, heq, List.isEmpty_iff.mp (by simpa using hlp)⟩
      · intro hh; exact nomatch hh
    · revert hF
      split
      · next ciF heq =>
        intro hlp
        exact ⟨ciF, heq, List.isEmpty_iff.mp (by simpa using hlp)⟩
      · intro hh; exact nomatch hh

/-- Rebuild the guard from the separate facts. -/
theorem natOpGuard_intro {c : Name}
    (hs : natLitSupported env = true)
    (hdeps : ∀ n ∈ natOpDeps c, ∃ cvn vn hn,
      env.find? n = some (.defnInfo cvn vn hn) ∧ cvn.levelParams = [])
    (hbool : (c = natBeqName ∨ c = natBleName ∨ c ∈ natDivModNames) →
      (∃ ciT, env.find? boolTrueName = some ciT ∧
        ciT.toConstantVal.levelParams = []) ∧
      (∃ ciF, env.find? boolFalseName = some ciF ∧
        ciF.toConstantVal.levelParams = [])) :
    natOpGuard env c = true := by
  unfold natOpGuard
  simp only [Bool.and_eq_true]
  refine ⟨⟨hs, ?_⟩, ?_⟩
  · refine List.all_eq_true.mpr ?_
    intro n hn
    obtain ⟨cvn, vn, hn, heq, hlp⟩ := hdeps n hn
    rw [heq]
    simp [hlp]
  · split
    · next hcb =>
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hcb
      have hcb' : c = natBeqName ∨ c = natBleName ∨ c ∈ natDivModNames := by
        rcases hcb with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (List.contains_iff_mem.mp h))
      obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool hcb'
      rw [hT, hF]
      simp [hlpT, hlpF]
    · rfl

/-- The guard survives extension by a fresh constant. -/
theorem natOpGuard_cons {c : Name} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none)
    (h : natOpGuard env c = true) :
    natOpGuard (⟨c₀ :: env.consts⟩ : Env) c = true := by
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv h
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hnn, hzz, hss, -⟩ :=
    natLitSupported_inv hs
  refine natOpGuard_intro ?_ ?_ ?_
  · rw [natLitSupported_congr
      (Env.find?_cons_of_isSome hfresh (by simp [hnn]))
      (Env.find?_cons_of_isSome hfresh (by simp [hzz]))
      (Env.find?_cons_of_isSome hfresh (by simp [hss]))]
    exact hs
  · intro n hn
    obtain ⟨cvn, vn, hn, heq, hlp⟩ := hdeps n hn
    exact ⟨cvn, vn, hn,
      (Env.find?_cons_of_isSome hfresh (by simp [heq])).trans heq, hlp⟩
  · intro hc
    obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool hc
    exact ⟨⟨ciT, (Env.find?_cons_of_isSome hfresh (by simp [hT])).trans hT,
        hlpT⟩,
      ⟨ciF, (Env.find?_cons_of_isSome hfresh (by simp [hF])).trans hF,
        hlpF⟩⟩


/-! ## The `Nat` fast-path guard, unpacked

`natOpGuard` is the certificate that a structural-`Nat` operation may
be accelerated on literals.  Its three consequences below are read by
every clause of both lanes' `reduceNat` bridges — the literal support,
the operation's and its dependencies' storage with no level parameters,
and the two `Bool` constructors for the comparison and div/mod
branches.  All of them are statements about `Env.find?` alone;
relocated here from `ConLeche/TTVerify/NatOpsStep.lean` (task #148, T3)
so that the `ConLeche/SetR/*` bridge consumes them rather than restating
them. -/

/-- The guard's own consequences, in the form every operation clause
reads them: the literal support, and that the operation and each of its
dependencies is stored with no level parameters. -/
theorem natOpGuard_deps {env : Env} {c : Name}
    (hguard : natOpGuard env c = true) :
    natLitSupported env = true ∧
      ∀ n ∈ natOpDeps c, ∃ cv v hh, env.find? n = some (.defnInfo cv v hh) ∧
        cv.levelParams = [] := by
  simp only [natOpGuard, Bool.and_eq_true] at hguard
  refine ⟨hguard.1.1, ?_⟩
  intro n hn
  have hd := hguard.1.2
  rw [List.all_eq_true] at hd
  have h := hd n (by simpa using hn)
  cases hx : env.find? n with
  | none => rw [hx] at h; exact nomatch h
  | some ci =>
    rw [hx] at h
    cases ci with
    | defnInfo cv v hh =>
      exact ⟨cv, v, hh, rfl, by simpa [List.isEmpty_iff] using h⟩
    | _ => simp at h

/-- The `Bool` constructors are pinned by the guard of any operation
whose recurrences mention them. -/
theorem natOpGuard_bools {env : Env} {c : Name}
    (hguard : natOpGuard env c = true)
    (hc : c = natBeqName ∨ c = natBleName ∨ natDivModNames.contains c = true) :
    (∃ ci, env.find? boolTrueName = some ci ∧
        ci.toConstantVal.levelParams = []) ∧
      (∃ ci, env.find? boolFalseName = some ci ∧
        ci.toConstantVal.levelParams = []) := by
  simp only [natOpGuard, Bool.and_eq_true] at hguard
  have hb := hguard.2
  rw [show (decide (c = natBeqName) || decide (c = natBleName) ||
      natDivModNames.contains c) = true from by
    rcases hc with rfl | rfl | h
    · simp
    · simp
    · rw [h]; simp] at hb
  simp only [if_true, Bool.and_eq_true] at hb
  obtain ⟨hT, hF⟩ := hb
  constructor
  · cases hx : env.find? boolTrueName with
    | none => rw [hx] at hT; exact nomatch hT
    | some ci => rw [hx] at hT; exact ⟨ci, rfl,
      by simpa [List.isEmpty_iff] using hT⟩
  · cases hx : env.find? boolFalseName with
    | none => rw [hx] at hF; exact nomatch hF
    | some ci => rw [hx] at hF; exact ⟨ci, rfl,
      by simpa [List.isEmpty_iff] using hF⟩

/-- A guarded operation is stored as a definition. -/
theorem natOp_stored {env : Env} {c : Name} (hg : natOpGuard env c = true)
    (hc : c ∈ natOpDeps c) :
    ∃ cv v hh, env.find? c = some (.defnInfo cv v hh) := by
  obtain ⟨-, hdeps⟩ := natOpGuard_deps hg
  obtain ⟨cv, v, hh, hf, -⟩ := hdeps c hc
  exact ⟨cv, v, hh, hf⟩

/-! ### The reduction-time test (task #161 item B3)

`reduceNat` tests `natOpStored` — one `Env.find?` — where it used to
re-derive `natOpGuard`.  Both directions of the agreement are recorded
here: the *cheap-to-full* direction is the environment invariant's
(`NatOpsV`/`DivModV` and their `P` mirrors take the `defnInfo` lookup
as their hypothesis and hand back the guard), and the *full-to-cheap*
direction is `natOpGuard_stored` below, by computation. -/

/-- Inversion of the reduction-time test: the operation is stored as a
definition.  This is exactly the hypothesis `NatOpsV`/`DivModV` (and
`NatOps`/`DivMod`) take before handing back `natOpGuard`. -/
theorem natOpStored_inv {env : Env} {c : Name}
    (h : natOpStored env c = true) :
    ∃ cv v hh, env.find? c = some (.defnInfo cv v hh) := by
  unfold natOpStored at h
  cases hx : env.find? c with
  | none => rw [hx] at h; exact nomatch h
  | some ci =>
    rw [hx] at h
    cases ci with
    | defnInfo cv v hh => exact ⟨cv, v, hh, rfl⟩
    | _ => exact nomatch h

/-- The guard implies the reduction-time test (`c ∈ natOpDeps c` for
every one of the sixteen guarded names). -/
theorem natOpStored_of_guard {env : Env} {c : Name}
    (hg : natOpGuard env c = true) (hc : c ∈ natOpDeps c) :
    natOpStored env c = true := by
  obtain ⟨cv, v, hh, hf⟩ := natOp_stored hg hc
  unfold natOpStored
  rw [hf]

end ConLeche
