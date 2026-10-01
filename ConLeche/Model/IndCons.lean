module

public import ConLeche.Model.BasisStep

public section

/-!
# The inductive cons, P tier: the mechanical rows at an ind-kind head (task #161, IND TIER)

`declStep_preserves_of_basis_cons` (`Interp/BasisStepP.lean`) collapses seven
of `declStep_preserves_of_cons`'s eleven premises at a *basis* cons.  An
*inductive-block* cons is the other side of the same coin: its name is
never reserved, so the two rows a basis cons could route by *name*
(`caps_ok` through `capsOk_cons_basis`) are unavailable, while every
row a basis cons routes by *kind* survives — and one that a basis cons
had to supply bespoke (`nat_heads` at the `Nat` block) becomes free.

**The name finding, re-checked with an `#eval` before it was spent
(the E/F/G/H practice).**  Every block member enters through
`MemberValR` → `ConstantValR`, whose second conjunct is

> `reservedBasisNames.contains cv.name = false`

and `reservedBasisNames` is the twenty pinned names — `Nat`,
`Nat.zero`, `Nat.succ` and `Eq` among them.  So at every member cons:

* `nat_heads` goes through `natHeads_cons_offNat`: an inductive block
  **cannot** turn the literal-support guard on, because it cannot
  install a constant named `Nat`, `Nat.zero` or `Nat.succ`.  The
  feared obligation — a modeled family that captures the numeral
  heads, whose leaves would then owe the two membership facts — does
  not exist;
* `eq_law` goes through `eqLaw_cons_fresh` for the same reason: no
  block member is named `Eq`, so the pinned spine's law is untouched.

The projection conses (`ProjFnR`'s `recInfo`, `Templates`'s
`projInfo`) carry no reserved check of their own, but their names are
`projFnName T i`, and `projFnName_ne_reserved` supplies the same four
disequalities.

What is left is exactly the tier's bill: `caps_ok` and `rec_rules`,
plus the tower and its type's reading.  Both remaining rows are taken
here in `natHeads_cons_offNat`'s shape — quantified over any carrier
whose base and `acval` are the extension's — so a caller never spells
`declStep_preserves_of_cons`'s anonymous-constructor carrier.

**The `caps_ok` gap is not only at the family's own conses.**
`capsOk_cons_fresh` descends the stored-family predicate past a cons
of a kind no family mentions, and `EtaFamilyStored` mentions three:
`indInfo` (the former), `ctorInfo` (the capability constructor) and
**`recInfo`** (a projection slot).  So the *projection-function*
install — a `recInfo` cons — can complete a family that was not
previously stored, which is why the η law's establishment sits at the
projection install in v1 too (`Install/EtaLawS.lean`, the
`etaLawKeyS` route).  `declStep_preserves_of_ind_cons` therefore keeps
`caps_ok` open at every ind-tier cons and never guesses a route.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- A non-reserved name differs from every reserved one.  The
inductive tier's workhorse: `ConstantValR`'s second conjunct is the
hypothesis, and the four names the mechanical rows read
(`Nat`/`Nat.zero`/`Nat.succ`/`Eq`) are all reserved. -/
theorem ne_of_notReserved {n m : Name}
    (h : ConLeche.reservedBasisNames.contains n = false)
    (hm : ConLeche.reservedBasisNames.contains m = true) : n ≠ m := by
  intro hh
  rw [hh, hm] at h
  exact nomatch h

theorem reserved_natName : ConLeche.reservedBasisNames.contains natName = true := by
  decide

theorem reserved_natZeroName :
    ConLeche.reservedBasisNames.contains natZeroName = true := by decide

theorem reserved_natSuccName :
    ConLeche.reservedBasisNames.contains natSuccName = true := by decide

theorem reserved_eqName : ConLeche.reservedBasisNames.contains eqName = true := by
  decide


/-- **The P step at an inductive-tier cons.**  Six of
`declStep_preserves_of_cons`'s eight collapsible rows are discharged here from
the *name* (non-reserved) and the *kind* (never a value kind, never an
axiom); `caps_ok` and `rec_rules` stay open, because those are the two
rows an inductive block genuinely establishes. -/
theorem declStep_preserves_of_ind_cons (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    -- the name: `ConstantValR`'s second conjunct at a member,
    -- `projFnName_ne_reserved` at a projection slot
    (hnres : ConLeche.reservedBasisNames.contains c₀.name = false)
    -- the kind: an inductive block installs no value kind and no axiom
    (hnotdefn : ∀ cv v hint, c₀ ≠ .defnInfo cv v hint)
    (hnotax : ∀ cv, c₀ ≠ .axiomInfo cv)
    -- the head's own obligations (task #161 S7)
    (hh : ConsHead env c₀ A)
    -- the annotated tower
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValid V ρ (A ψ))
    -- the type's reading, its grading, and the tower's membership
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : AnnotTerm,
        denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta)
    (hmemNew : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta)
    -- the tier's two genuine rows
    (hcaps : ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A → CapsOk m₂)
    (hrec : ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A →
      ∀ φ : Name → Nat, RecRules m₂ φ)
    -- the head is not a projection table (task #175 W4c: those get
    -- their own kit, `DeclStructP`)
    (hntc : ∀ entry, c₀ ≠ .projInfo entry) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  refine declStep_preserves_of_cons mp (c₀ := c₀) (A := A) hfresh hh
    hAclosed hAparams hAok hAvalid htyReads htyOk hmemNew
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `hvalReads`: an inductive cons is never a definition
    intro _ψ cv2 value2 hmem
    obtain ⟨hint2, hdt⟩ := hmem
    exact absurd hdt.symm (hnotdefn cv2 value2 hint2)
  · -- `nat_heads`: the guard's three names are reserved, this one is not
    exact fun φ => natHeads_cons_offNat mp
      (ne_of_notReserved hnres reserved_natName)
      (ne_of_notReserved hnres reserved_natZeroName)
      (ne_of_notReserved hnres reserved_natSuccName) _ rfl φ
  · exact fun φ => natOps_cons_fresh mp (mp.nat_ops φ) hfresh
      (hntc := hh.projTower) (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · exact fun φ => divMod_cons_fresh (mp.div_mod φ) hfresh
      (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · -- `eq_law`: `Eq` is reserved, so it is not this cons
    exact eqLaw_cons_fresh mp.eq_law
      (fun h => ne_of_notReserved hnres reserved_eqName h.symm) _ rfl
  · exact hcaps _ rfl
  · exact fun φ => hrec _ rfl φ
  · exact reduceOps_cons_fresh mp.reduce_ops hfresh
      (Or.inl hnotax) _ rfl
  · -- `tower_ok` (task #175 wiring W5): an ind-tier cons is never a
    -- tower entry (`hh.projTower`)
    exact fun φ => towerOk_cons_fresh mp hfresh hh.projTower hntc _ rfl φ

/-- **The P step at a block *member* cons** — `declStep_preserves_of_ind_cons`
with `rec_rules` discharged too.  A member is an `indInfo` or a
`ctorInfo`, so `recRules_cons_fresh`'s side condition holds
vacuously: the cons is not a recursor at all, and `EnvS.rec_ctors`
carries the rest (ENDGAME D §3a).  `caps_ok` remains the member's one
open row — the block's former *is* a family head. -/
theorem declStep_preserves_of_ind_member_cons (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hnres : ConLeche.reservedBasisNames.contains c₀.name = false)
    (hknd : (∃ cv caps, c₀ = .indInfo cv caps) ∨
      ∃ cv nP nF, c₀ = .ctorInfo cv nP nF)
    (hh : ConsHead env c₀ A)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValid V ρ (A ψ))
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : AnnotTerm,
        denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta)
    (hmemNew : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta)
    (hcaps : ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A → CapsOk m₂) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  refine declStep_preserves_of_ind_cons mp hfresh hnres ?_ ?_ hh
    hAclosed hAparams hAok hAvalid htyReads htyOk hmemNew
    hcaps ?_ ?_
  · rcases hknd with ⟨cv, caps, rfl⟩ | ⟨cv, nP, nF, rfl⟩ <;>
      intro _ _ _ h <;> exact nomatch h
  · rcases hknd with ⟨cv, caps, rfl⟩ | ⟨cv, nP, nF, rfl⟩ <;>
      intro _ h <;> exact nomatch h
  · refine fun m₂ hac φ => recRules_cons_fresh mp hfresh hh.projTower ?_ m₂ hac φ
    rcases hknd with ⟨cv, caps, rfl⟩ | ⟨cv, nP, nF, rfl⟩ <;>
      intro _ _ _ _ h <;> exact nomatch h
  · rcases hknd with ⟨cv, caps, rfl⟩ | ⟨cv, nP, nF, rfl⟩ <;>
      intro _ h <;> exact nomatch h

/-- **The P step at a *recursor* cons** — the block's recursors and the
projection functions, both stored as `recInfo`.  Only `caps_ok` and
`rec_rules` stay open; both are the install's to establish. -/
theorem declStep_preserves_of_ind_rec_cons (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hnres : ConLeche.reservedBasisNames.contains c₀.name = false)
    (hknd : ∃ cv mI rP rules, c₀ = .recInfo cv mI rP rules)
    (hh : ConsHead env c₀ A)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValid V ρ (A ψ))
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : AnnotTerm,
        denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta)
    (hmemNew : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta)
    (hcaps : ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A → CapsOk m₂)
    (hrec : ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A →
      ∀ φ : Name → Nat, RecRules m₂ φ) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  obtain ⟨cv, mI, rP, rules, rfl⟩ := hknd
  exact declStep_preserves_of_ind_cons mp hfresh hnres
    (fun _ _ _ h => nomatch h)
    (fun _ h => nomatch h) hh hAclosed hAparams hAok
    hAvalid htyReads htyOk hmemNew hcaps hrec (fun _ h => nomatch h)

end ConLeche.Model
