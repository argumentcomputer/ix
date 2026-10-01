module

public import ConLeche.Model.BasisEmpty
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

public section

/-!
# The `False` block, P tier (task #181)

`ConLeche/Model/BasisEmpty.lean`'s recipe at the pinned `False` block
(`ConLeche/Kernel/Basis/False.lean`): `False` is `Empty.{0}` in the
built-in currency — the leaf `.const .empty [0]` reads to the empty
set at `Sort 0`, `False.rec`'s leaf is `.const .emptyRec [0, ψ u]` —
so every move below is the `Empty` module's with the level numeral `1`
replaced by `0`.  `BConst.typeAV`/`bval_mem_type`/`WellDenotedV_bconst_type`
are stated at every level list, so nothing new is proved about the
built-ins; the type readings are recomputed at the `False` pins
(`denoteMeta_falseA_type`, `denoteMeta_falseRecA_type`) and `BitAgree`d to
`BConst.typeAV .empty [0]` / `.emptyRec [0, ψ u]`.

The point of the pin is the capstone: `no_constant_of_False`
(`CapstoneP.lean`) reads the leaf's value off `basis_pinnedL` exactly as
`no_constant_of_Empty` does, so `no_proof_of_False_pure` needs no
hypothesis about how a stream declared `False`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  falseA falseRecA falseName uN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## `Empty` -/

/-- The `False` former's type reading: `Sort 0`, which is
`BConst.typeAV .empty [0]` on the nose (no `BitAgree` needed — the
former has no binder, so there is no numeral to disagree about). -/
theorem denoteMeta_falseA_type
    {acval : Name → (Name → Nat) → AnnotTerm} (ψ : Name → Nat) :
    denoteMeta acval ⟨falseA :: env.consts⟩ ψ 0 falseA.toConstantVal.type
      = some (BConst.typeAV .empty [0]) := by
  rw [show falseA.toConstantVal.type = Expr.sort .zero from rfl,
    denoteMeta_sort]
  rfl

/-- **`False`, installed at the P tier.** -/
theorem extendFalse (mp : EnvModelM V μ env)
    (hfresh : env.find? falseName = none)
    (hwf : EnvWF ⟨falseA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨falseA :: env.consts⟩) := by
  refine nonempty_of_exists (declStep_preserves_of_basis_cons mp
    (A := fun _ => AnnotTerm.const .empty [0]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT falseA.name ψ
          = some (Term.const .empty [0]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteMeta_falseA_type ψ⟩) ?_ ?_)
  · intro ψ ta h ρ
    rw [denoteMeta_falseA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedV_bconst_type V .empty [0] ρ
  · intro ψ ta h ρ
    rw [denoteMeta_falseA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .empty [0] ρ

/-! ## `False.rec` — the recipe at `Prop`

Two binders, three stored `PropWhen` pins — the same three as
`Empty.rec`'s (`.ifAllZero [u]`, `.never`, `.ifAllZero [u]`): the
motive's domain `False → Sort u` has sort `imax 0 (u+1) = u+1`, never
`Prop`; the two outer binders' types have sort `imax (u+1) u` and
`imax 0 u = u`, `Prop` exactly at `u = 0`.  The `pwBit` lemmas are
`BasisEmptyP.lean`'s. -/

/-- **`False.rec`'s type reading.**  The four moves of the module
docstring; the leaves are `acval_basis_pinned` at `Empty`. -/
theorem denoteMeta_falseRecA_type {m : EnvModel V env}
    {A : (Name → Nat) → AnnotTerm} (ψ : Name → Nat)
    (hE : env.find? falseName = some falseA) :
    denoteMeta (acvalWith m.acval falseRecA.name A)
        ⟨falseRecA :: env.consts⟩ ψ 0 falseRecA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.pi 0 (pwBit ψ .never) (.const .empty [0]) (.sort (ψ uN)))
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .empty [0])
            (.app (.bvar 1) (.bvar 0)))) := by
  have hpd : ConLeche.Verify.pinnedStructT falseName ψ
      = some (Term.const .empty [0]) := by
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hleaf : acvalWith m.acval falseRecA.name A falseName ψ
      = AnnotTerm.const .empty [0] := by
    rw [acvalWith_ne (by decide)]
    exact acval_basis_pinned hE (by decide) hpd
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval falseRecA.name A)
          ⟨falseRecA :: env.consts⟩ ψ d (.const falseName [])
        = some (AnnotTerm.const .empty [0]) := by
    intro d
    have hf : (⟨falseRecA :: env.consts⟩ : Env).find? falseName
        = some falseA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE
    rw [denoteMeta_levelless_const hf (by rfl), hleaf]
  rw [show falseRecA.toConstantVal.type
      = Expr.forallE
          (Expr.forallE (.const falseName [])
            (.sort (.param uN)) { pw := .never })
          (Expr.forallE (.const falseName [])
            (.app (.bvar 1) (.bvar 0))
            { pw := .ifAllZero [uN] })
          { pw := .ifAllZero [uN] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, hEc, Level.eval]

/-- **The reading agrees with `BConst.typeAV` on every numeral anything
reads.**  Three binders, three `pwBit`s, three `typeAV` slots, and the
iffs are `pwBit_never` and `pwBit_ifAllZero_single` — nothing here is
chosen. -/
theorem bitAgree_falseRecA (ψ : Name → Nat) :
    AnnotTerm.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [uN]))
        (.pi 0 (pwBit ψ .never) (.const .empty [0]) (.sort (ψ uN)))
        (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .empty [0])
          (.app (.bvar 1) (.bvar 0))))
      (BConst.typeAV .emptyRec [0, ψ uN]) := by
  have hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
  refine .pi hz (.pi ?_ (.const _ _) (.sort _))
    (.pi hz (.const _ _) (.app (.bvar 1) (.bvar 0)))
  rw [pwBit_never]
  simp

/-- **`False.rec`, installed at the P tier.** -/
theorem extendFalseRec (mp : EnvModelM V μ env)
    (hE : env.find? falseName = some falseA)
    (hfresh : env.find? falseRecA.name = none)
    (hwf : EnvWF ⟨falseRecA :: env.consts⟩) :
    Nonempty (EnvModelM V μ ⟨falseRecA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteMeta_falseRecA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .emptyRec [0, ψ uN]) ψ hE
  refine nonempty_of_exists (declStep_preserves_of_basis_cons mp
    (A := fun ψ => AnnotTerm.const .emptyRec [0, ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => by injection h with _ _ _ h4; exact h4 ▸ rfl)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT falseRecA.name ψ
          = some (Term.const .emptyRec [0, ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => by injection h with _ _ _ h4
                           intro r hr; rw [← h4] at hr; exact nomatch hr))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_falseRecA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .emptyRec [0, ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_falseRecA ψ) ρ]
    exact bval_mem_type V .emptyRec [0, ψ uN] ρ

/-! ## The block

The dispatch mirrors `declBasisS_emptyK (the `Empty` twin)` link for link, and drives the
two lanes in lockstep: each cons runs the v1 install first (for the
`EnvS` base and its `cval` equation) and then the P install on top of
it.  `BasisInstallRun` is a right-nested `∧` chain, so the walk is an
`obtain` and two steps — there is no fold to invert. -/

/-- **The `False` block, installed at the P tier.**  `BasisStepPB`'s
`falseK` branch. -/
theorem declBasisPB_falseK {env₂ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.falseK.declsA env₂) :
    Nonempty (EnvModelM V μ env₂) := by
  rw [show ConLeche.BasisKind.falseK.declsA = [falseA, falseRecA] from rfl]
    at h
  obtain ⟨h1, h2, hnil⟩ := h
  subst hnil
  have hf1 : env.find? falseA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨falseA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  obtain ⟨mp1⟩ := extendFalse mp hf1 hwf1
  have hE : (⟨falseA :: env.consts⟩ : Env).find? falseName
      = some falseA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hf2 : (⟨falseA :: env.consts⟩ : Env).find? falseRecA.name
      = none := Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨falseRecA :: falseA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq),
      (fun _ _ _ _ heq => by
        injection heq with _ _ _ h4
        subst h4
        intro r hr; exact nomatch hr),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ falseRecA.toConstantVal.type = true
    simp only [show falseRecA.toConstantVal.type
        = Expr.forallE
            (Expr.forallE (.const falseName [])
              (.sort (.param uN)) { pw := .never })
            (Expr.forallE (.const falseName [])
              (.app (.bvar 1) (.bvar 0))
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] } from rfl,
      Expr.constsResolve, Bool.and_eq_true, Option.isSome_iff_exists]
    have hf : (⟨falseRecA :: falseA :: env.consts⟩ : Env).find?
        falseName = some falseA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]
      exact hE
    rw [hf]
    simp
  exact extendFalseRec mp1 hE hf2 hwf2

end ConLeche.Model
