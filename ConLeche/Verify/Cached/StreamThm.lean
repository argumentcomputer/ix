module

public import ConLeche.Cached.Installed
public import ConLeche.SetTheory.Core
import ConLeche.Verify.Cached.MainC
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.BridgeCS4

public section

/-!
# A theorem record of the stream is stored under its own name

The letters of the fold (`ConLeche/Verify/Cached/MainC.lean`) are about
the environment `checkDecls` RETURNS.  This module carries one fact the
other way, from the fold's INPUT: a `thmDecl` record whose declared type
is a bare constant is installed, with that very type, and the constant
survives to the end of the run.

Three ingredients, one per step of the walk:

* **the annotation of a bare constant is the constant.**  Phase A
  annotates a declaration's type before storing it
  (`annotConstantValC`), and the annotation pass is memoized
  (`memoEI (·.annotC)`), so the returned type is the memo's entry on a
  hit and `annotateBodyI`'s on a miss.  The step's own `flushC` empties
  the annotation memo immediately before the call, so the hit branch is
  unreachable and `annotateBodyI`'s `.const` arm — `pure e` — decides:
  `annotate_const`.
* **a theorem record is never dropped.**  `annotStepC`'s `thmDecl` arm
  either throws or pushes `.thmInfo ⟨cv.name, cv.levelParams, jty⟩`
  with the annotated type `jty`: `annotStepC_thm_consts`.
* **pushed constants persist.**  An accepting `InstallRun` only ever
  extends the constants list (`installRun_trace`, `PushChain`), so what
  the theorem's step pushed is still there at the end of phase A —
  and phase B pushes nothing at all.

`checkDecls_thmDecl_const` is the three composed: the returned
environment holds a constant of the record's declared type.  Nothing
here is about `False` in particular; the main corollary
(`no_False_theorem_accepted`, `ConLeche/MainTheorem.lean`) instantiates
it at `falseName`.
-/

namespace ConLeche.Cached

open ConLeche

variable {pins : List NatOpPinSet}

/-! ## The annotation of a bare constant is the constant -/

/-- The annotation pass's `.const` arm: a bare constant annotates to
itself. -/
theorem annotateBodyI_const (r : CoreFnsI) (fe : FEnv) (d : Nat) (n : Name)
    (ls : List Level) :
    annotateBodyI r fe d (.const n ls) = pure (.const n ls) := rfl

/-- With the annotation memo missing the key, the memoized entry point
returns what the body returns: a bare constant annotates to itself. -/
theorem annotate_const_of_miss {mode : CheckMode} {fe : FEnv} {f d : Nat}
    {n : Name} {ls : List Level} {s₀ s' : CState} {j : Expr}
    (hmiss : s₀.annotC[(Expr.const n ls : Expr)]? = none)
    (h : (coreKnotI mode fe (f + 1)).annotate d (.const n ls) s₀ = .ok (j, s')) :
    j = .const n ls := by
  rw [show (coreKnotI mode fe (f + 1)).annotate d (Expr.const n ls) =
      memoEI (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI (coreKnotI mode fe f) fe d e)
        d (Expr.const n ls) from rfl] at h
  simp only [memoEI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind, hmiss, annotateBodyI_const, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, Except.ok.injEq,
    Prod.mk.injEq] at h
  exact h.1.symm

/-- The annotation memo of a flushed state is empty. -/
theorem flushed_annotC_none (s : CState) (e : Expr) :
    (s.flushed).annotC[e]? = none := by
  simp only [CState.flushed]
  simp

/-! ## Phase A's header install keeps a bare declared type -/

/-- Phase A's header install, at a flushed state, returns the header
with the declared type unchanged when that type is a bare constant. -/
theorem annotConstantValC_const {mode : CheckMode} {fe : FEnv}
    {cv cvA : ConstantVal} {jty : Expr} {n : Name} {ls : List Level}
    {s₀ s' : CState} (hty : cv.type = .const n ls)
    (h : annotConstantValC mode fe cv s₀.flushed = .ok ((cvA, jty), s')) :
    cvA = ⟨cv.name, cv.levelParams, .const n ls⟩ := by
  unfold annotConstantValC at h
  by_cases h1 : (fe.find? cv.name).isSome = true
  · rw [if_pos h1] at h; exact absurd h throwC_bind_ok
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h; exact absurd h throwC_bind_ok
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h; exact absurd h throwC_bind_ok
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; exact absurd h throwC_bind_ok
  rw [if_pos h4] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [if_neg h5] at h; exact absurd h throwC_bind_ok
  rw [if_pos h5] at h
  by_cases h6 : Expr.hasFvar cv.type = true
  · rw [if_pos h6] at h; exact absurd h throwC_bind_ok
  rw [if_neg h6] at h
  obtain ⟨jA, s₁, hann, h⟩ := bindC_ok h
  rw [hty] at hann
  obtain rfl : jA = .const n ls :=
    annotate_const_of_miss (f := checkFuel - 1) (flushed_annotC_none s₀ _)
      (by rw [show checkFuel - 1 + 1 = checkFuel from rfl]; exact hann)
  by_cases h7 : Expr.allLevelParamsDefinedC cv.levelParams (Expr.const n ls) = true
  case neg => rw [if_neg h7] at h; exact absurd h throwC_bind_ok
  rw [if_pos h7] at h
  by_cases h8 : constsResolveFC fe (Expr.const n ls) = true
  case neg => rw [if_neg h8] at h; exact absurd h throwC_bind_ok
  rw [if_pos h8] at h
  obtain ⟨hv, _⟩ := pureC_ok h
  obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ hv
  rfl

/-! ## A theorem record is installed, with its declared type -/

/-- Phase A's step at a `thmDecl` record with a bare declared type:
the constant it pushes is a `.thmInfo` of that very type. -/
theorem annotStepC_thm_consts {mode : CheckMode} {i : Nat} {fe : FEnv}
    {pend : Array PendingCheck} {cv : ConstantVal} {value : Expr}
    {n : Name} {ls : List Level} {s₀ s' : CState}
    {fe' : FEnv} {pend' : Array PendingCheck} (hty : cv.type = .const n ls)
    (h : annotStepC mode pins i fe pend (.thmDecl cv value) s₀ = .ok ((fe', pend'), s')) :
    fe'.env.consts =
      ConstantInfo.thmInfo ⟨cv.name, cv.levelParams, .const n ls⟩ value ::
        fe.env.consts := by
  unfold annotStepC at h
  simp only [] at h
  obtain ⟨_, s₁, hfl, h⟩ := bindC_ok h
  rw [show (flushC : CheckCM Unit) s₀ = .ok ((), s₀.flushed) from rfl] at hfl
  have hs₁ : s₀.flushed = s₁ := congrArg Prod.snd (Except.ok.inj hfl)
  subst hs₁
  obtain ⟨p, s₂, hcv, h⟩ := bindC_ok h
  obtain ⟨cvA, jty⟩ := p
  obtain rfl := annotConstantValC_const hty hcv
  obtain ⟨_, s₃, _, h⟩ := bindC_ok h
  obtain ⟨hv, _⟩ := pureC_ok h
  obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ hv
  rfl

/-! ## The constant survives to the end of phase A -/

/-- **A theorem record of the stream is stored**: if phase A accepts a
list of records containing a `thmDecl` whose declared type is a bare
constant, the environment it returns holds a constant of that type. -/
theorem installRun_thmDecl_const {mode : CheckMode} {ds : List Declaration}
    {cv : ConstantVal} {value : Expr} {n : Name} {ls : List Level}
    (hty : cv.type = .const n ls) (hmem : Declaration.thmDecl cv value ∈ ds)
    {p q : Nat × FEnv × Array PendingCheck} {s s' : CState}
    (h : InstallRun mode pins ds p s q s') (hcanon : p.2.1 = mkFEnv p.2.1.env) :
    ∃ c ∈ q.2.1.env.consts, c.toConstantVal.type = .const n ls := by
  induction h with
  | nil p s => exact absurd hmem (List.not_mem_nil)
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    have hchain : PushChain p.2.1.env fe₁ :=
      (annotStepC_push mode p.1 (PushChain.self hcanon) p.2.2 pd s (fe₁, pend₁) s₁
        hstepC).1
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · -- the record is this step's: its constant is pushed here
      have hconsts := annotStepC_thm_consts hty hstepC
      obtain ⟨⟨_, ⟨new, hnew⟩, _⟩, _⟩ :=
        installRun_trace mode rest (PushChain.self hchain.canon)
      refine ⟨ConstantInfo.thmInfo ⟨cv.name, cv.levelParams, .const n ls⟩ value, ?_, rfl⟩
      rw [hnew]
      exact List.mem_append_right _ (hconsts ▸ List.mem_cons_self)
    · exact ih hmem' hchain.canon

/-- **The main corollary's ingredient at the stream**: an accepted stream
that declares a theorem of a bare constant type leaves a constant of
that type in the environment. -/
theorem checkDecls_thmDecl_const {mode : CheckMode} {ds : Array Declaration} {env : Env}
    {cv : ConstantVal} {value : Expr} {n : Name} {ls : List Level}
    (hty : cv.type = .const n ls) (hmem : Declaration.thmDecl cv value ∈ ds)
    (h : checkDecls mode pins ds = .ok env) :
    ∃ c ∈ env.consts, c.toConstantVal.type = .const n ls := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked mode h
  obtain ⟨_, _, run⟩ := fc.1.run
  exact installRun_thmDecl_const hty (Array.mem_toList_iff.mpr hmem) run rfl

end ConLeche.Cached

namespace ConLeche

universe w

/-- **The main corollary, at the stream.**  A stream that declares a
theorem of type `False` is never accepted.  Two steps: the record is
installed under its own name with its declared type and that constant
survives the run (`checkDecls_thmDecl_const`), so an accepted
environment would hold a constant of type `False` — and it cannot,
because in the model of the main theorem that type denotes the empty
set, which the constant would have to be a member of
(`no_proof_of_False_cached`).  The main corollary
(`no_False_declaration`, `ConLeche/MainTheorem.lean`) rests on this. -/
theorem no_False_theorem_accepted (V : Type w) [SetTheory V]
    (ds : Array Declaration) (cv : ConstantVal) (v : Expr)
    (hmem : Declaration.thmDecl cv v ∈ ds) (hty : cv.type = .const falseName []) :
    ∀ env, Cached.checkDecls .verified pins ds ≠ .ok env := by
  intro env accepted
  obtain ⟨c, hc, hcty⟩ := Cached.checkDecls_thmDecl_const hty hmem accepted
  exact Cached.no_proof_of_False_cached V rfl accepted c hc hcty

end ConLeche
