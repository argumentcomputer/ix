module

-- lane S-red's kit is the SHARED one: `DenoteMetaSpine`'s list algebra,
-- `hoist_spine`, `frame_spine`, `denoteMeta_mkAppN(_inv)`, the
-- `PiChain` guard and the tower entry's reading live there
public import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.PropRead
import ConLeche.Model.IOLicense
import ConLeche.Model.Annot.BitClosed
import ConLeche.Verify.InstLevels
import ConLeche.Verify.PinnedShapes
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but
not `@[expose]`d, so the `cases`-then-`rfl` steps of the squash-regime
facts below cannot see the reduct.  `import all` restores that view
HERE only — the transplant of `Model/Steps/IrrelFast.lean`, which
carries the same escape for the same reason. -/
import all ConLeche.Kernel.PropWhen
import ConLeche.Semantics.Hoist
import ConLeche.Model.Annot.BitLevels

public section

/-!
# The definitional-equality soundness kit (task #305, lane S-defeq)

The plumbing the per-rule lemmas of `Model/Rules/DefEqSound.lean`
share: the frame/grading splitters at each node shape, the two `Nat`
constant readings, and `projAV`'s congruence.  Everything here is a
TRANSPLANT of an argument that lived in `Model/Steps/*` until the task
#305 closing deleted that tier (`DefEq.lean`'s `hoist_*` and
`denoteMeta_nat*Const`, `ProjAVKit.lean`'s `projAV` family) — restated
at the rules tier's `Frame`/`Graded` vocabulary, so that no
`Model/Rules` module is stated over runs.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The frame splitters -/

theorem Frame.app_fn {d : Nat} {f x : Expr} (h : Frame d (.app f x)) :
    Frame d f := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.app_arg {d : Nat} {f x : Expr} (h : Frame d (.app f x)) :
    Frame d x := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.2, hb.2, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.proj_arg {d : Nat} {s : Name} {i : Nat} {e : Expr}
    (h : Frame d (.proj s i e)) : Frame d e := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded] at hb
  exact ⟨hw, hb, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

/-- The opened body's frame, at an arbitrary (well-framed) domain —
`binder_congr`'s `hLo₁`/`hLo₂` plus its two scoping arguments. -/
theorem Frame.open_body {d : Nat} {ty' bd : Expr} (hty' : Frame d ty')
    (hwb : Expr.WScoped d bd) (hbb : bd.looseBVarsBounded 1 = true)
    (hLb : Expr.LeavesBounded bd) :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  refine ⟨Expr.WScoped.instantiate1 hty'.1 0 hwb,
    ConLeche.looseBVarsBounded_instantiate1 bd 0 hbb, ?_⟩
  intro l hl
  rcases ConLeche.Expr.fvarLeaves_instantiate1 bd 0 hl with h2 | h2
  · exact hLb l h2
  · rw [ConLeche.Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hty'.2.1
    · exact hty'.2.2 l h3

theorem Frame.forallE_ty {d : Nat} {ty bd : Expr} {mb : ConLeche.BinderMeta}
    (h : Frame d (.forallE ty bd mb)) : Frame d ty := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.forallE_open {d : Nat} {ty bd ty' : Expr}
    {mb : ConLeche.BinderMeta} (h : Frame d (.forallE ty bd mb))
    (hty' : Frame d ty') :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact Frame.open_body hty' hw.2 hb.2
    (fun l hl => hL l (by simp [Expr.fvarLeaves, hl]))

theorem Frame.lam_ty {d : Nat} {ty bd : Expr} {mb : ConLeche.BinderMeta}
    (h : Frame d (.lam ty bd mb)) : Frame d ty := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.lam_open {d : Nat} {ty bd ty' : Expr}
    {mb : ConLeche.BinderMeta} (h : Frame d (.lam ty bd mb))
    (hty' : Frame d ty') :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact Frame.open_body hty' hw.2 hb.2
    (fun l hl => hL l (by simp [Expr.fvarLeaves, hl]))

theorem Frame.of_not_hasFvar {d : Nat} {e : Expr} (hf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) : Frame d e :=
  ⟨Expr.WScoped.of_not_hasFvar hf, hb, Expr.LeavesBounded.of_not_hasFvar hf⟩

/-! ## The grading splitters — `Steps/DefEq.lean`'s `hoist_*`, at
`Graded` -/

theorem Graded.app {Δa : List AnnotTerm} {f a : AnnotTerm}
    (h : Graded V Δa (.app f a)) :
    Graded V Δa f ∧ Graded V Δa a := by
  refine ⟨fun ρ hρ => ⟨((WellDenoted_app V ρ f a) ▸ (h ρ hρ).1).1, ?_⟩,
    fun ρ hρ => ⟨((WellDenoted_app V ρ f a) ▸ (h ρ hρ).1).2.1, ?_⟩⟩
  · exact ((AnnotValid_app V ρ f a) ▸ (h ρ hρ).2).1
  · exact ((AnnotValid_app V ρ f a) ▸ (h ρ hρ).2).2

theorem Graded.fst {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : Graded V Δa (.fst e)) : Graded V Δa e := fun ρ hρ =>
  ⟨((WellDenoted_fst V ρ e) ▸ (h ρ hρ).1).1,
    (AnnotValid_fst V ρ e) ▸ (h ρ hρ).2⟩

theorem Graded.snd {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : Graded V Δa (.snd e)) : Graded V Δa e := fun ρ hρ =>
  ⟨((WellDenoted_snd V ρ e) ▸ (h ρ hρ).1).1,
    (AnnotValid_snd V ρ e) ▸ (h ρ hρ).2⟩

/-- `hoist_pi` (`Steps/DefEq.lean:141`) at `Graded`. -/
theorem Graded.pi {Δa : List AnnotTerm} {u v : Nat} {A B : AnnotTerm}
    (h : Graded V Δa (.pi u v A B)) :
    Graded V Δa A ∧ Graded V (A :: Δa) B := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_pi (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValid_pi V ρ u v A B) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValid_pi V _ u v A B) ▸
      (h _ (Sat_tail hρ)).2).2.1 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

/-- `hoist_lam` (`Steps/DefEq.lean:155`) at `Graded`. -/
theorem Graded.lam {Δa : List AnnotTerm} {v : Nat} {A b : AnnotTerm}
    (h : Graded V Δa (.lam v A b)) :
    Graded V Δa A ∧ Graded V (A :: Δa) b := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_lam (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValid_lam V ρ v A b) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValid_lam V _ v A b) ▸
      (h _ (Sat_tail hρ)).2).2 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

/-- The head transport of a hoisted grading, at `Graded`. -/
theorem Graded.head_congr {Δa : List AnnotTerm} {A B e : AnnotTerm}
    (heq : ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ A = interp V ρ B)
    (h : Graded V (B :: Δa) e) : Graded V (A :: Δa) e :=
  fun ρ hρ => h ρ (Sat.head_congr heq hρ)

theorem denoteMeta_open_rename {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {bd ty ty' : Expr} {ba : AnnotTerm}
    (h : denoteMeta acval env φ (d + 1) (bd.instantiate1 (.fvar d ty))
      = some ba) :
    denoteMeta acval env φ (d + 1) (bd.instantiate1 (.fvar d ty'))
      = some ba := by
  rw [denoteMeta_erasedEq (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl bd)
    (show Expr.ErasedEq (.fvar d ty') (.fvar d ty) from rfl))]
  exact h

/-! ## The constant congruence (`Steps/DefEq.lean:844`) -/

/-- The same constant at level-equivalent instantiations has one
validated reading. -/
theorem acval_const_congr' {m : EnvModel V env} (hap : AcvalParams m)
    {d : Nat} {n : Name} {us us' : List Level} {aa ba : AnnotTerm}
    (hlev : Level.isEquivList us us' = some true)
    (hda : denoteMeta m.acval env φ d (.const n us) = some aa)
    (hdb : denoteMeta m.acval env φ d (.const n us') = some ba) :
    aa = ba := by
  rw [denoteMeta] at hda hdb
  cases hf : env.find? n with
  | none => rw [hf] at hda; exact nomatch hda
  | some ci =>
    rw [hf] at hda hdb
    dsimp only at hda hdb
    split at hda
    · split at hdb
      · rw [← Option.some.inj hda, ← Option.some.inj hdb]
        refine hap n ci hf _ _ ?_
        intro p _
        exact Level.substFn_of_evalEqList _
          (Level.isEquivList_sound hlev φ) p
      · exact nomatch hdb
    · exact nomatch hda

/-- The subject of a graded projection spine is graded (`ProjAV.hoistV`
of `RedSoundKit`, at `Graded`). -/
theorem Graded.projAV {Δa : List AnnotTerm} {i : Nat} {e : AnnotTerm}
    (h : Graded V Δa (ConLeche.Semantics.projAV i e)) : Graded V Δa e :=
  fun ρ hρ => ProjAV.hoistV (h ρ hρ)

/-! ## The stored constant's package (`Steps/IotaRows.lean:200`) -/

/-- A stored declaration's instantiated type: read at every depth,
graded, inhabited, and framed (closed, so the frames are free). -/
theorem constType_pkg {m : EnvModel V env} (hct : ConstType m φ)
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hnt : ci.isTowerEntry = false) {us : List Level}
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    ∃ ta : AnnotTerm,
      (∀ d : Nat, denoteMeta m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V,
        interp V ρ (m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) ∈ˢ interp V ρ ta) ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).hasFvar = false ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
  obtain ⟨ta, hta, hok, hmem⟩ := hct 0 n ci us hf hnt hlen
  have hwf := m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hbd : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwf.2.2.2.1
  exact ⟨ta, denoteMeta_depth_of_closed m.acval_closed hnf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnf hbd hta 1 k)
      hta,
    hok, hmem, hnf, hbd⟩

/-! ## The proof-irrelevance fast arm (`Steps/IrrelFast.lean:67-419`)

The whole squash-regime licence, transplanted: the `V`-level facts,
the type former's `.pi` chain, and `prf_of_isProofFast` itself, with
`ConstType` read as the rules tier's `ConstType`. -/

/-! ## 1. The squash-regime facts, V level -/

/-- Every application of `pt` is `pt` (`app_pt`, folded along a spine). -/
theorem foldl_app_pt' {ρ : Nat → V} : ∀ (as : List AnnotTerm),
    as.foldl (fun r a => app r (interp V ρ a)) (pt : V) = pt
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt' as

/-- A spine on a `pt`-valued head interprets to `pt`. -/
theorem interp_mkAppN_pt {ρ : Nat → V} {f : AnnotTerm}
    (hf : interp V ρ f = pt) (as : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN f as) = pt := by
  rw [interp_mkAppN, hf]
  exact foldl_app_pt' as

/-- The kernel's "definitely `Prop`" test on a datum is the ∀-φ uniform
version of the claims' zero side: the bit is `0` at every valuation
(the dual of `pwBit_ne_zero_of_isNever`). -/
theorem pwBit_eq_zero_of_isProp {pw : PropWhen}
    (h : pw.isProp = true) (φ : Name → Nat) : pwBit φ pw = 0 := by
  rw [eq_of_beq h]
  simp [pwBit]

/-- **Exactness**: `pw.isProp` is *the* datum that is zero at every
valuation — `isNever_iff_forall_pwBit_ne_zero`'s mirror. -/
theorem alwaysZero_iff_forall_pwBit_eq_zero {pw : PropWhen} :
    pw.isProp = true ↔ ∀ φ : Name → Nat, pwBit φ pw = 0 := by
  constructor
  · exact pwBit_eq_zero_of_isProp
  · intro h
    cases pw with
    | never => exact absurd (h (fun _ => 0)) (by simp [pwBit])
    | ifAllZero ps =>
      cases ps with
      | nil => rfl
      | cons n ps =>
        have := h (fun _ => 1)
        simp [pwBit] at this

/-- A level whose zero-ness datum is always-zero evaluates to `0`. -/
theorem eval_eq_zero_of_isProp {u : Level}
    (h : (Level.zeronessOf u).isProp = true) (φ : Name → Nat) :
    Level.eval φ u = 0 := by
  have := pwBit_eq_zero_of_isProp h φ
  rw [pwBit_eq_zero_iff, ConLeche.PropWhen.zeronessOf_sound] at this
  exact beq_iff_eq.mp this

/-- **THE FENCE.**  At a nonzero bit the product reading is a graph set
with two distinct members: a `prf` verdict read off a datum that is
not always-zero would equate them.  So the fast "yes" is exactly the
always-zero datum, model-class-wide. -/
theorem irrel_fast_fence :
    ∃ (A : V) (B : V → V) (f g : V),
      f ∈ˢ piR 1 A B ∧ g ∈ˢ piR 1 A B ∧ f ≠ g := by
  refine ⟨truthVal True, fun _ => univZero,
    lamR 1 (truthVal True) (fun _ => truthVal False),
    lamR 1 (truthVal True) (fun _ => truthVal True), ?_, ?_, ?_⟩
  · exact lamR_mem fun _ _ => truthVal_mem_univZero False
  · exact lamR_mem fun _ _ => truthVal_mem_univZero True
  · intro h
    have h1 : app (lamR 1 (truthVal True) (fun _ => (truthVal False : V))) (pt : V)
        = app (lamR 1 (truthVal True) (fun _ => (truthVal True : V))) (pt : V) :=
      congrArg (fun z => app z (pt : V)) h
    rw [app_lamR_pos (by decide) (pt_mem_truthVal trivial),
      app_lamR_pos (by decide) (pt_mem_truthVal trivial)] at h1
    have : (pt : V) ∈ˢ (truthVal False : V) := h1 ▸ pt_mem_truthVal trivial
    exact (mem_truthVal.mp this).1

/-! ## 2. The type former's telescope: a `.pi` chain at nonzero bits -/

/-- The reading's first `n` heads are `.pi` nodes at nonzero regime
bits, and the residual is `.sort u` — the reading of a type former's
stored type `∀ p⃗, Sort u` whose binders the reader checked to be
`.never`. -/
@[expose] def NeverChain : Nat → Nat → AnnotTerm → Prop
  | 0, u, e => e = .sort u
  | n + 1, u, e =>
    match e with
    | .pi _ v _ B => v ≠ 0 ∧ NeverChain n u B
    | _ => False

theorem neverChain_succ_inv {n u : Nat} {e : AnnotTerm}
    (h : NeverChain (n + 1) u e) :
    ∃ w v A B, e = .pi w v A B ∧ v ≠ 0 ∧ NeverChain n u B := by
  match e with
  | .pi w v A B => exact ⟨w, v, A, B, rfl, h.1, h.2⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .eqE _ _ | .fst _ | .snd _ | .prf => exact nomatch h

/-- Substitution preserves the chain (`inst` maps `.pi` to `.pi` and
`.sort` to itself). -/
theorem NeverChain.inst : ∀ {n u : Nat} {e : AnnotTerm} (a : AnnotTerm) (k : Nat),
    NeverChain n u e → NeverChain n u (e.inst a k) := by
  intro n
  induction n with
  | zero => intro u e a k h; subst h; rfl
  | succ n ih =>
    intro u e a k h
    obtain ⟨w, v, A, B, rfl, hv, hB⟩ := neverChain_succ_inv h
    exact ⟨hv, ih a (k + 1) hB⟩

/-- **A `.never`-peeled telescope reads to a chain**: each binder's bit
is nonzero (`pwBit_ne_zero_of_isNever`), the residual sort evaluates. -/
theorem neverChain_of_peel {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) {d : Nat} {T : Expr} {u : Level} {ta : AnnotTerm},
      T.peelNeverPis n = some (.sort u) →
      denoteMeta acval env φ d T = some ta →
      NeverChain n (Level.eval φ u) ta := by
  intro n
  induction n with
  | zero =>
    intro d T u ta hp hd
    obtain rfl := Expr.peelNeverPis_zero_inv hp
    rw [denoteMeta] at hd
    exact (Option.some.inj hd).symm
  | succ n ih =>
    intro d T u ta hp hd
    obtain ⟨ty, b, m, rfl, hnev, hb⟩ := Expr.peelNeverPis_succ_inv hp
    obtain ⟨tA, tB, -, htB, rfl⟩ := denoteMeta_forallE_inv hd
    exact ⟨pwBit_ne_zero_of_isNever hnev φ,
      ih (Expr.peelNeverPis_instantiate1 n _ 0 hb) htB⟩

/-- **A type former's application lands in its result universe.**  The
walk along the chain: at every slot the bit is nonzero, so the
argument's membership in the domain is `io_domain_transfer` from the
applied spine's own hereditary app slot — no certificate anywhere. -/
theorem spine_mem_univ_of_neverChain {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {Ta f : AnnotTerm} {u : Nat},
      NeverChain vs.length u Ta →
      WellDenotedV V ρ Ta → WellDenotedV V ρ (AnnotTerm.mkAppN f vs) →
      interp V ρ f ∈ˢ interp V ρ Ta →
      interp V ρ (AnnotTerm.mkAppN f vs) ∈ˢ (univ u : V) := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f u hch _ _ hf
    obtain rfl : Ta = .sort u := hch
    exact hf
  | cons a vs ih =>
    intro Ta f u hch hokT hokS hf
    obtain ⟨w, v, A, B, rfl, hv, hB⟩ := neverChain_succ_inv hch
    have hokApp : WellDenotedV V ρ (.app f a) := mkAppN_head vs hokS
    have hoka : WellDenotedV V ρ a :=
      ⟨((WellDenoted_app V ρ f a) ▸ hokApp.1).2.1,
        ((AnnotValid_app V ρ f a) ▸ hokApp.2).2⟩
    have hokB : ∀ y, y ∈ˢ interp V ρ A → WellDenotedV V (cons y ρ) B :=
      fun y hy =>
        ⟨((WellDenoted_pi V ρ w v A B) ▸ hokT.1).2 y hy,
          ((AnnotValid_pi V ρ w v A B) ▸ hokT.2).2.1 y hy⟩
    have hf' : interp V ρ f
        ∈ˢ piR v (interp V ρ A) (fun x => interp V (cons x ρ) B) := hf
    have hmem : interp V ρ a ∈ˢ interp V ρ A := by
      obtain ⟨v', A', B', hslot, ha, -⟩ :=
        ((WellDenoted_app V ρ f a) ▸ hokApp.1).2.2
      exact io_domain_transfer hv hslot ha hf'
    have hokB' : WellDenotedV V ρ (B.inst a) :=
      (WellDenotedV_inst0 hoka).mpr (hokB _ hmem)
    have hfa : interp V ρ (.app f a) ∈ˢ interp V ρ (B.inst a) := by
      rw [interp_app, interp_inst0]
      exact app_mem_piR_pos hv hf' hmem
    exact ih (NeverChain.inst a 0 hB) hokB' hokS hfa

/-- The reading of a type-former application `T = hd b⃗` lands in
`univ 0` once the head's type reads to a chain of `b⃗`'s length ending
in `Sort 0`, the head inhabits it, and both readings are graded. -/
theorem mem_univ_zero_of_spine {m : EnvModel V env}
    {ρ : Nat → V} {d : Nat} {T hd : Expr} {Ta fa taH : AnnotTerm}
    (hfn : T.getAppFn = hd)
    (hTa : denoteMeta m.acval env φ d T = some Ta)
    (hfa : denoteMeta m.acval env φ d hd = some fa)
    (hchain : NeverChain T.getAppArgs.length 0 taH)
    (hokH : WellDenotedV V ρ taH) (hokT : WellDenotedV V ρ Ta)
    (hmem : interp V ρ fa ∈ˢ interp V ρ taH) :
    interp V ρ Ta ∈ˢ (univ 0 : V) := by
  rw [← ConLeche.Expr.mkAppN_getApp T, hfn] at hTa
  obtain ⟨fa', vs, hfa', hsp, rfl⟩ := denoteMeta_mkAppN_inv hTa
  rw [hfa] at hfa'
  obtain rfl := Option.some.inj hfa'
  rw [hsp.length] at hchain
  exact spine_mem_univ_of_neverChain vs hchain hokH hokT hmem

/-- **A constant-headed type former's application** (`I b⃗`, `I` stored
with type `∀ p⃗, Sort u`, every binder `.never`, `u` zero at the use's
levels) lands in `univ 0`: `ConstType` supplies `I`'s membership in
its instantiated stored type and that type's grading; the chain is
read off the stored syntax at the composed valuation. -/
theorem typeFormer_mem_univ_zero {m : EnvModel V env}
    (hct : ConstType m φ) {ρ : Nat → V} {d : Nat} {T : Expr}
    {I : Name} {us : List Level} {ci : ConstantInfo} {u : Level} {Ta : AnnotTerm}
    (hfn : T.getAppFn = .const I us) (hfI : env.find? I = some ci)
    (hnt : ci.isTowerEntry = false)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    (hpeel : ci.toConstantVal.type.peelNeverPis T.getAppArgs.length =
      some (.sort u))
    (hz : Level.eval (Level.substFn φ ci.toConstantVal.levelParams us) u = 0)
    (hTa : denoteMeta m.acval env φ d T = some Ta) (hokT : WellDenotedV V ρ Ta) :
    interp V ρ Ta ∈ˢ (univ 0 : V) := by
  obtain ⟨taI, htaI, hokI, hmemI, -, -⟩ := constType_pkg hct hfI hnt hlen
  have htaI' := htaI d
  rw [denotePInstLevels] at htaI'
  have hchain := neverChain_of_peel (env := env) T.getAppArgs.length hpeel htaI'
  rw [hz] at hchain
  exact mem_univ_zero_of_spine hfn hTa (denoteMeta_const hfI hlen) hchain
    (hokI ρ) hokT (hmemI ρ)

/-! ## 3. The kernel-shaped licence -/

/-- A leaf of a spine's head is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN : ∀ (as : List Expr) (f : Expr)
    (l : Nat × Expr), l ∈ f.fvarLeaves →
    l ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, _, h => h
  | a :: as, f, l, h =>
    mem_fvarLeaves_mkAppN as (.app f a) l (by simp [Expr.fvarLeaves, h])

/-- A leaf of a term's head is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn' {a hd : Expr} {l : Nat × Expr}
    (h : a.getAppFn = hd) (hl : l ∈ hd.fvarLeaves) : l ∈ a.fvarLeaves := by
  rw [← ConLeche.Expr.mkAppN_getApp a, h]
  exact mem_fvarLeaves_mkAppN _ _ _ hl

/-- The leaf of a term's head fvar is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn {a ty : Expr} {idx : Nat}
    (h : a.getAppFn = .fvar idx ty) : (idx, ty) ∈ a.fvarLeaves :=
  mem_fvarLeaves_of_getAppFn' h (by simp [Expr.fvarLeaves])

/-- The leaves of an fvar's type are leaves of the fvar. -/
theorem mem_fvarLeaves_of_ty {ty : Expr} {idx : Nat}
    {l : Nat × Expr} (h : l ∈ ty.fvarLeaves) :
    l ∈ (Expr.fvar idx ty).fvarLeaves := by
  simp [Expr.fvarLeaves, h]

/-- **A term whose validated data say "proof" is `pt`.**  The
head-symbol case split of `isProofFast`, each case closed by the
squash-regime licence (a ∀-typed head, a λ) or the one graph-regime
step (a type-former-typed head). -/
theorem prf_of_isProofFast {m : EnvModel V env} (hct : ConstType m φ)
    {d : Nat} {a : Expr} {Δa : List AnnotTerm} {aa : AnnotTerm}
    (h : isProofFast env.find? a = true)
    (hCa : CtxOk m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) : interp V ρ aa = (pt : V) := by
  obtain ⟨pw, hpw, hprop⟩ := isProofFast_inv env.find? h
  rcases proofPW_some_inv env.find? hpw with
    ⟨ty, bd, mb, rfl, rfl⟩ | ⟨-, hhead⟩
  · -- a λ: its datum is the body's type's sort, at bit `0`
    obtain ⟨ta, ba, -, -, rfl⟩ := denoteMeta_lam_inv hda
    rw [interp_lam, pwBit_eq_zero_of_isProp hprop, lamR_zero]
  -- an application spine: the head decides
  have hspine := hda
  rw [← ConLeche.Expr.mkAppN_getApp a] at hspine
  obtain ⟨fa, vs, hfa, -, rfl⟩ := denoteMeta_mkAppN_inv hspine
  refine interp_mkAppN_pt ?_ vs
  rcases headProofPW_some_inv env.find? hhead with
    ⟨c, us, ci, hfn, hf, hnt, hlen, pw0, hty, rfl⟩ |
    ⟨idx, ty, hfn, hty⟩ | rfl
  · -- a constant head: the stored type decides
    rw [hfn, denoteMeta_const hf hlen] at hfa
    obtain rfl := Option.some.inj hfa
    obtain ⟨ta, hta, hokT, hmem, hnf, -⟩ := constType_pkg hct hf hnt hlen
    rcases typeSortPW_some_inv env.find? hty with
      ⟨A, B, mb, hT, rfl⟩ | rfl |
      ⟨I, us', ciI, u, hfnT, hfI, hntI, hlenI, hpeel, rfl⟩ |
      ⟨idx, ty', u, hfnT, -, -⟩
    · -- ∀-typed: the squash product
      have hta' := hta d
      rw [hT, ConLeche.Expr.instantiateLevelParams] at hta'
      obtain ⟨tA, tB, -, -, rfl⟩ := denoteMeta_forallE_inv hta'
      have hbit : pwBit φ (Level.substPW ci.toConstantVal.levelParams us mb.pw)
          = 0 := pwBit_eq_zero_of_isProp hprop φ
      have hm := hmem ρ
      rw [interp_pi, hbit] at hm
      exact eq_pt_of_mem_piR_zero hm
    · -- `Sort`-typed: never a proof
      exact absurd hprop (by simp)
    · -- a type-former application: the graph-regime step
      have hwf := m.wf _ (ConLeche.Semantics.Env.find?_mem hfI)
      have hdefU : (Level.zeronessOf u).paramsDefined
          ciI.toConstantVal.levelParams = true := by
        obtain ⟨bs, hbs⟩ := Expr.stripPis_of_peelNeverPis _ hpeel
        have := ConLeche.Expr.allLevelParamsDefined_stripPis_body _ hbs hwf.2.1
        exact ConLeche.Level.zeronessOf_paramsDefined
          (by simpa [ConLeche.Expr.allLevelParamsDefined] using this)
      have hcomp := ConLeche.Level.substPW_comp
        (ks := ci.toConstantVal.levelParams) (us := us) hlenI hdefU
      have hz : Level.eval (Level.substFn φ ciI.toConstantVal.levelParams
          (us'.map (Level.subst ci.toConstantVal.levelParams us))) u = 0 := by
        have hb := pwBit_eq_zero_of_isProp hprop φ
        rw [hcomp, pwBit_substPW, pwBit_eq_zero_iff,
          ConLeche.PropWhen.zeronessOf_sound] at hb
        exact beq_iff_eq.mp hb
      have hT : (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us).getAppFn =
          .const I (us'.map (Level.subst ci.toConstantVal.levelParams us)) := by
        rw [ConLeche.Expr.getAppFn_instantiateLevelParams, hfnT]
        rfl
      have hpeel' : ciI.toConstantVal.type.peelNeverPis
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us).getAppArgs.length =
          some (.sort u) := by
        rw [ConLeche.Expr.getAppArgs_instantiateLevelParams, List.length_map]
        exact hpeel
      have huniv := typeFormer_mem_univ_zero hct hT hfI hntI
        (by rw [List.length_map]; exact hlenI) hpeel' hz (hta d) (hokT ρ)
      exact mem_univ_zero huniv (hmem ρ)
    · -- an fvar-headed stored type: stored types are closed
      exact absurd (ConLeche.Expr.hasFvar_of_getAppFn_fvar hfnT)
        (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams] at hnf; simp [hnf])
  · -- an fvar head: the context supplies the membership
    rw [hfn, denoteMeta_fvar] at hfa
    obtain rfl := Option.some.inj hfa
    obtain ⟨-, -, tya, Aa, htya, hAa, heq, hokT⟩ :=
      hCa.2 _ (mem_fvarLeaves_of_getAppFn hfn)
    have hx : interp V ρ (.bvar (d - 1 - idx)) ∈ˢ interp V ρ tya := by
      rw [interp_bvar, heq ρ hρ]
      exact hρ _ _ hAa
    rcases typeSortPW_some_inv env.find? hty with
      ⟨A, B, mb, rfl, rfl⟩ | rfl |
      ⟨I, us', ciI, u, hfnT, hfI, hntI, hlenI, hpeel, rfl⟩ |
      ⟨idy, tyy, u, hfnT, hpeel, rfl⟩
    · -- ∀-typed: the squash product
      obtain ⟨tA, tB, -, -, rfl⟩ := denoteMeta_forallE_inv htya
      rw [interp_pi, pwBit_eq_zero_of_isProp hprop] at hx
      exact eq_pt_of_mem_piR_zero hx
    · exact absurd hprop (by simp)
    · -- a constant-headed type former: the graph-regime step
      have hz : Level.eval (Level.substFn φ ciI.toConstantVal.levelParams us') u
          = 0 := by
        have hb := pwBit_eq_zero_of_isProp hprop φ
        rw [pwBit_substPW, pwBit_eq_zero_iff,
          ConLeche.PropWhen.zeronessOf_sound] at hb
        exact beq_iff_eq.mp hb
      have huniv := typeFormer_mem_univ_zero hct hfnT hfI hntI hlenI hpeel hz
        htya (hokT ρ hρ)
      exact mem_univ_zero huniv hx
    · -- an fvar-headed type former (`h : motive n`): the head's type
      -- is in the context too
      obtain ⟨-, -, tyyA, Ay, htyy, hAy, heqy, hokY⟩ :=
        hCa.2 _ (mem_fvarLeaves_of_getAppFn' hfn
          (mem_fvarLeaves_of_ty (idx := idx)
            (mem_fvarLeaves_of_getAppFn hfnT)))
      have hy : interp V ρ (.bvar (d - 1 - idy)) ∈ˢ interp V ρ tyyA := by
        rw [interp_bvar, heqy ρ hρ]
        exact hρ _ _ hAy
      have hchain := neverChain_of_peel (env := env) (acval := m.acval)
        ty.getAppArgs.length hpeel htyy
      rw [eval_eq_zero_of_isProp hprop φ] at hchain
      have huniv := mem_univ_zero_of_spine hfnT htya (denoteMeta_fvar _ _ _ _)
        hchain (hokY ρ hρ) (hokT ρ hρ) hy
      exact mem_univ_zero huniv hx
  · -- a sort, a ∀, a literal: never a proof
    exact absurd hprop (by simp)



/-! ## The η-projection spelling, unfolded locally

`rw [ConLeche.etaProjs]` would reference the function's EQUATION
LEMMA, generated in whichever module first forces it.  The checker's
definitions are `@[expose]`d, so the clause is available by `rfl`
here, in this tier's own module, and the proof term names nothing
outside it. -/

theorem etaProjs_eq (T : Name) (us : List Level) (targs : List Expr)
    (b : Expr) (nF : Nat) :
    ConLeche.etaProjs env T us targs b nF =
      if ConLeche.towerSlotsAll env T nF then
        (List.range nF).map fun j => Expr.proj T j b
      else
        (List.range nF).map fun j =>
          Expr.mkAppN (.const (projFnName T j) us) (targs ++ [b]) := by
  rfl

/-- The fabricated η spine's values, unfolded here for the same reason
(`etaFabArgsV`/`projSpines` are `EnvModelM`'s; `rfl` beats naming
their equation lemmas here too). -/
theorem etaFabArgsV_eq (val : Name → V) (T : Name) (ts : List V) (b : V)
    (nF : Nat) :
    etaFabArgsV val T ts b nF =
      ts ++ (List.range nF).map
        (fun j => (ts ++ [b]).foldl SetTheory.app (val (projFnName T j))) := by
  rfl

/-! ## The two proof-irrelevance sides (`Steps/Irrel.lean:71`, `:119`)

`prop_side_pt`/`unit_side_pt` at the motives: the run premises become
the rule's `InferSemIO`/`RedSem` derivations, and the inferred type's
frames — which the run lemmas `inferTypeIO_WScoped`/`_looseBVars`/
`_fvarLeaves` supplied there — are now the motives' own conclusions. -/

/-- A term whose type's type reduces to a zero-equivalent sort
interprets to `pt`. -/
theorem prop_side_pt' {m : EnvModel V env} {d : Nat} {a ta tta : Expr}
    {u : Level} {Δa : List AnnotTerm} {aa : AnnotTerm}
    (hta : InferSemIO m φ d a ta) (htta : InferSemIO m φ d ta tta)
    (hu : RedSem m φ d tta (.sort u))
    (hu0 : Level.isEquiv u .zero = some true)
    (hfa : Frame d a) (hCa : CtxOk m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (hokA : Graded V Δa aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) : interp V ρ aa = (pt : V) := by
  obtain ⟨hfta, hsub1, taa, htaa, hoktaa, hmemA⟩ := hta hfa hCa hda hokA
  have hCta : CtxOk m φ d Δa ta := hCa.of_subset hsub1
  obtain ⟨hftta, hsub2, ttaa, httaa, hokttaa, hmemT⟩ :=
    htta hfta hCta htaa hoktaa
  have hCtta : CtxOk m φ d Δa tta := hCta.of_subset hsub2
  obtain ⟨-, -, sa, hsa, -, heq⟩ := hu hftta hCtta httaa hokttaa
  rw [denoteMeta_sort] at hsa
  obtain rfl : sa = AnnotTerm.sort (u.eval φ) := (Option.some.inj hsa).symm
  have h0 : Level.eval φ u = 0 := ConLeche.Level.isEquiv_sound hu0 φ
  have hT := hmemT ρ hρ
  rw [heq ρ hρ, interp_sort, h0] at hT
  exact mem_univ_zero hT (hmemA ρ hρ)

/-- A term whose type reduces to a unit-like type interprets to `pt`:
`isUnitLikeTy` accepts only the pinned `PUnit`, whose `interp` is
`unitSet = {pt}`. -/
theorem unit_side_pt' {m : EnvModel V env} {d : Nat} {a ta wta : Expr}
    {Δa : List AnnotTerm} {aa : AnnotTerm}
    (hta : InferSemIO m φ d a ta) (hwta : RedSem m φ d ta wta)
    (hu : ConLeche.isUnitLikeTy env wta = true)
    (hfa : Frame d a) (hCa : CtxOk m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (hokA : Graded V Δa aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) : interp V ρ aa = (pt : V) := by
  obtain ⟨hfta, hsub1, taa, htaa, hoktaa, hmemA⟩ := hta hfa hCa hda hokA
  have hCta : CtxOk m φ d Δa ta := hCa.of_subset hsub1
  obtain ⟨-, -, wtaa, hwtaa, -, heqW⟩ := hwta hfta hCta htaa hoktaa
  obtain ⟨us, rfl, hfind⟩ :=
    ConLeche.Verify.unitLike_eq_punit m.basis_pinned hu
  rw [denoteMeta, hfind] at hwtaa
  dsimp only at hwtaa
  split at hwtaa
  case isFalse => exact nomatch hwtaa
  case isTrue hlen =>
  obtain rfl : wtaa = m.acval ConLeche.punitName
      (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us) :=
    (Option.some.inj hwtaa).symm
  have hpin : m.cvalE ConLeche.punitName
      (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us)
      = ConLeche.Term.punitT
        (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us
          ConLeche.uN) :=
    (m.basis_pinned ConLeche.punitName _ hfind (by decide)).2 _ _ rfl
  have hleaf : m.acval ConLeche.punitName
      (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us)
      = .const .punit
        [Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us
          ConLeche.uN] :=
    erase_eq_const (by rw [m.acval_erase, hpin]; rfl)
  have hmem := hmemA ρ hρ
  rw [heqW ρ hρ, hleaf, interp_const] at hmem
  exact mem_unitSet hmem

end ConLeche.Model.Rules
