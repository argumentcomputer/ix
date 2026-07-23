import Ix.Tc.Verify.Env
import Ix.Tc.Verify.Monad
import Ix.Tc.Verify.InstUniv

/-!
# The ghost state and the run invariant (M3, F4)

The F4 divergence from upstream, made concrete: lean4lean's environment
is *reader context* (fixed per `M.WF` call), ours is **mutable state**
(lazy ingress inserts constants mid-check). So the `TrEnv`-analog lives
inside a Hoare invariant: a ghost `VState` (the Theory-side environment
plus the ghost name assignment) related to the concrete `TcState` by
`TcStateWF`, under the monotone extension order `VState.LE` — a run
only ever *grows* the ghost state.

`TcInv vs₀ s` — "some ghost state ≥ the baseline `vs₀` describes `s`" —
is the concrete invariant `I` that M1's Hoare combinators (Verify/
Monad.lean, `I`-generic by design) get instantiated with from here on.

`TcStateWF` deliberately constrains only the SEMANTIC core of the
20-field `TcState`: the constant map (via `TrKEnv`) and the intern
table (via `InternTable.WF`). Everything else — fuel, flags, scratch,
statistics — is framed away by `of_env_eq`. Cache-coherence fields
(whnf/infer/defEq entries valid) join the structure with their M5/M6
consumers.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VEnv)

/-- The ghost state: the Theory-side environment plus the ghost name
    assignment for content addresses. Everything else the checker
    mutates is either framed away or (caches) validated against these. -/
structure VState where
  venv : VEnv
  nameOf : Address → Option Lean.Name

/-- Monotone extension: the Theory env grows (`VEnv.LE`) and the name
    assignment never forgets. -/
structure VState.LE (vs vs' : VState) : Prop where
  venv : vs.venv ≤ vs'.venv
  nameOf : ∀ a n, vs.nameOf a = some n → vs'.nameOf a = some n

instance : LE VState := ⟨VState.LE⟩

theorem VState.le_refl (vs : VState) : vs ≤ vs :=
  ⟨⟨id, id⟩, fun _ _ h => h⟩

theorem VState.LE.trans {vs₁ vs₂ vs₃ : VState} (h1 : vs₁ ≤ vs₂)
    (h2 : vs₂ ≤ vs₃) : vs₁ ≤ vs₃ :=
  ⟨h1.venv.trans h2.venv, fun a n h => h2.nameOf a n (h1.nameOf a n h)⟩

variable (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- The concrete state is described by the ghost state: the constant
    map translates (`TrKEnv`) and the intern table is well-formed.
    Extension point for the M5/M6 cache-coherence conditions. -/
structure TcStateWF (s : TcState .anon) (vs : VState) : Prop where
  env : TrKEnv vs.nameOf trProj s.env vs.venv
  intern : s.env.intern.WF

/-- The wide frame: any state operation preserving the constant map and
    the intern table preserves `TcStateWF` — fuel ticks, flag flips,
    depth bumps, statistics, scratch. -/
theorem TcStateWF.of_consts_eq {trProj} {s s' : TcState .anon}
    {vs : VState} (h : TcStateWF trProj s vs)
    (hc : s'.env.consts = s.env.consts)
    (hi : s'.env.intern.WF) :
    TcStateWF trProj s' vs := by
  refine ⟨?_, hi⟩
  obtain ⟨Q, henv⟩ := h.env
  exact ⟨Q, hc ▸ henv⟩

/-- `of_consts_eq` when the whole env is untouched. -/
theorem TcStateWF.of_env_eq {trProj} {s s' : TcState .anon} {vs : VState}
    (h : TcStateWF trProj s vs) (he : s'.env = s.env) :
    TcStateWF trProj s' vs :=
  h.of_consts_eq (by rw [he]) (he ▸ h.intern)

variable (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- The run invariant: some ghost state above the baseline describes the
    current concrete state. This is the `I` for M1's Hoare kernel from
    M3 on — monotonicity in the baseline lets callers thread one
    invariant through sub-calls that grow the environment. -/
def TcInv (vs₀ : VState) (s : TcState .anon) : Prop :=
  ∃ vs, vs₀ ≤ vs ∧ TcStateWF trProj s vs

theorem TcStateWF.tcInv {trProj} {s : TcState .anon} {vs : VState}
    (h : TcStateWF trProj s vs) : TcInv trProj vs s :=
  ⟨vs, VState.le_refl vs, h⟩

/-- Weaken the baseline. -/
theorem TcInv.mono {trProj} {vs₀ vs₀' : VState} {s : TcState .anon}
    (hle : vs₀' ≤ vs₀) (h : TcInv trProj vs₀ s) : TcInv trProj vs₀' s :=
  let ⟨vs, hvs, hwf⟩ := h
  ⟨vs, hle.trans hvs, hwf⟩

/-- Every `TcInv` state has a well-formed Theory environment. -/
theorem TcInv.venv_wf {trProj} {vs₀ : VState} {s : TcState .anon}
    (h : TcInv trProj vs₀ s) : ∃ vs, vs₀ ≤ vs ∧ vs.venv.WF :=
  let ⟨vs, hvs, hwf⟩ := h
  ⟨vs, hvs, hwf.env.wf⟩

/-- Lookups under the invariant translate, at some ghost state above
    the baseline (`TrKEnv.find?` lifted to `TcInv`). -/
theorem TcInv.find? {trProj} {vs₀ : VState} {s : TcState .anon}
    (h : TcInv trProj vs₀ s) {j : KId .anon} {c : KConst .anon}
    (hg : s.env.get? j = some c) :
    ∃ vs, vs₀ ≤ vs ∧ ∃ n ci', vs.nameOf j.addr = some n ∧
      vs.venv.constants n = some ci' ∧
      TrKConstant vs.venv vs.nameOf trProj c ci' :=
  let ⟨vs, hvs, hwf⟩ := h
  ⟨vs, hvs, hwf.env.find? hg⟩

/-! ### Growth: ingress steps as ghost-state transitions

The other half of the monotone design: inserting a translated constant
re-establishes `TcStateWF` at a strictly larger ghost state (the
`TrKEnv'` log steps, viewed as `TcState` transitions — the shape the
ingress-path verification will discharge per constant). The ghost
`nameOf` is total from the start; only `venv` grows. -/

/-- Ingress of an axiom: the `axio` log step as a state transition. -/
theorem TcStateWF.insert_axio {trProj} {s : TcState .anon} {vs : VState}
    {id : KId .anon} {nm : Mode.anon.F Name}
    {lps : Mode.anon.F (Array Name)} {lvls : UInt64} {ty : KExpr .anon}
    {ci' : Lean4Lean.VConstVal} {venv' : VEnv}
    (h : TcStateWF trProj s vs)
    (h1 : TrKConstVal vs.venv vs.nameOf trProj id.addr
      (.axio nm lps false lvls ty) ci')
    (h2 : s.env.consts[id]? = none)
    (h3 : ci'.WF vs.venv)
    (h4 : vs.venv.addConst ci'.name ci'.toVConstant = some venv') :
    TcStateWF trProj
      { s with env := s.env.insert id (.axio nm lps false lvls ty) }
      ⟨venv', vs.nameOf⟩ ∧ vs ≤ ⟨venv', vs.nameOf⟩ := by
  obtain ⟨Q, henv⟩ := h.env
  exact ⟨⟨⟨Q, .axio h1 h2 h3 h4 henv⟩, h.intern⟩,
    ⟨VEnv.addConst_le h4, fun _ _ hn => hn⟩⟩

/-- Ingress of a (safe) definition: the `defn` log step as a state
    transition. -/
theorem TcStateWF.insert_defn {trProj} {s : TcState .anon} {vs : VState}
    {id : KId .anon} {nm : Mode.anon.F Name}
    {lps : Mode.anon.F (Array Name)} {kind : Ix.DefKind}
    {hints : Lean.ReducibilityHints} {lvls : UInt64}
    {ty val : KExpr .anon} {leanAll : Mode.anon.F (Array (KId .anon))}
    {block : KId .anon} {ci' : Lean4Lean.VDefVal} {venv' : VEnv}
    (h : TcStateWF trProj s vs)
    (h1 : TrKDefVal vs.venv vs.nameOf trProj id.addr
      (.defn nm lps kind .safe hints lvls ty val leanAll block) val ci')
    (h2 : s.env.consts[id]? = none)
    (h3 : ci'.WF vs.venv)
    (h4 : vs.venv.addConst ci'.name ci'.toVConstant = some venv') :
    TcStateWF trProj
      { s with env :=
          (s.env.insert id
            (.defn nm lps kind .safe hints lvls ty val leanAll block)) }
      ⟨venv'.addDefEq ci'.toDefEq, vs.nameOf⟩ ∧
    vs ≤ ⟨venv'.addDefEq ci'.toDefEq, vs.nameOf⟩ := by
  obtain ⟨Q, henv⟩ := h.env
  exact ⟨⟨⟨Q, .defn h1 h2 h3 h4 henv⟩, h.intern⟩,
    ⟨(VEnv.addConst_le h4).trans VEnv.addDefEq_le, fun _ _ hn => hn⟩⟩

/-! ### Validation: the M1 helpers under the real invariant -/

/-- `tick` preserves the run invariant (fuel is framed away). -/
theorem TcM.tick.tcInv {trProj} {vs₀ : VState} {s : TcState .anon} :
    TcM.WF (TcInv trProj vs₀) s (TcM.tick (m := .anon))
      (fun _ s' => s'.recFuel = s.recFuel - 1)
      (fun e s' => e = .maxRecFuel ∧ s' = s) :=
  TcM.tick.wf fun _ h =>
    let ⟨vs, hvs, hwf⟩ := h
    ⟨vs, hvs, hwf.of_env_eq rfl⟩

/-- The first M2-walker × M3-invariant composition:
    `instantiateUnivParams` preserves the run invariant — its frame
    moves only `env.intern`, whose well-formedness the M2 triple
    carries through both outcomes. The caller supplies the pre-state
    intern-support condition (`S` covers the table) exactly as in the
    M2 theorem; `TcInv` supplies the intern `WF` half itself. -/
theorem TcM.instantiateUnivParams.tcInv {trProj} {vs₀ : VState}
    {S : KExpr .anon → Prop} {us : Array (KUniv .anon)}
    {e : KExpr .anon} {s : TcState .anon}
    (hcf : KExpr.CollisionFree S)
    (hreach : ∀ x, KExpr.InstUnivReach us e x → S x)
    (hsup : ∀ x, s.env.intern.ExprSupport x → S x) :
    TcM.WF (TcInv trProj vs₀) s (TcM.instantiateUnivParams e us)
      (fun r s' => KExpr.instantiateUnivParamsSpec e us = .ok r ∧
        s' = { s with env := { s.env with intern := s'.env.intern } })
      (fun _ s' =>
        s' = { s with env := { s.env with intern := s'.env.intern } }) := by
  intro hI
  obtain ⟨vs, hvs, hwf⟩ := hI
  have h2 := TcM.instantiateUnivParams_wf hcf hreach
    (s := s) ⟨hwf.intern, hsup⟩
  match hrun : TcM.instantiateUnivParams e us s with
  | .ok r s' =>
    rw [hrun] at h2
    obtain ⟨⟨hwf', _⟩, hspec, hframe⟩ := h2
    have hc : s'.env.consts = s.env.consts :=
      congrArg (fun t => t.env.consts) hframe
    exact ⟨⟨vs, hvs, hwf.of_consts_eq hc hwf'⟩, hspec, hframe⟩
  | .error err s' =>
    rw [hrun] at h2
    obtain ⟨⟨hwf', _⟩, hframe⟩ := h2
    have hc : s'.env.consts = s.env.consts :=
      congrArg (fun t => t.env.consts) hframe
    exact ⟨⟨vs, hvs, hwf.of_consts_eq hc hwf'⟩, hframe⟩

end Ix.Tc
