import Ix.CompileCert.CurrentInputs

/-! Proof-local names for the actual block prefixes and image suffix. Their
production decomposition equations precede all state-invariant arguments. -/
namespace Ix.CompileCert.BlockStates
open Ix (Name Expr ConstantInfo)
open Ix.CompileM Ix.Compile.Pass
open Ix.Compile.ExactKey (ExactName)
open DevelopmentFrames

structure RewritePrefixOut where
  state : RwState
  overlay : Array (Name × ConstantInfo)
  declines : Array (Name × String)

private def rewritePrefix (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo)) (cfg : RwConfig) : Except String RewritePrefixOut := do
  let mut st : RwState := {}
  let mut overlay : Array (Name × ConstantInfo) := #[]
  let mut declines : Array (Name × String) := #[]
  for (n, ci) in members do
    st := { st with declines := #[] }
    let ((ci', changed), st') ← ((rewriteConstM expansion? ci).run cfg).run st
    st := st'
    declines := appendMemberDeclines declines n st.declines
    if changed then overlay := overlay.push (n, ci')
  return ⟨st, overlay, declines⟩

private def project (p : RewritePrefixOut) : BlockRewrite :=
  { overlay := p.overlay, sources := p.state.sources, declines := p.declines,
    canon := p.state.canon, pjForms := p.state.pjForms }

theorem rewriteBlock_eq (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo)) (cfg : RwConfig) :
    rewriteBlock expansion? members cfg = (do let p ← rewritePrefix expansion? members cfg; pure (project p)) := by
  simp only [rewriteBlock, rewritePrefix, project, bind_assoc, pure_bind]

structure ImagePrefixOut where
  views : Std.HashMap ExactName BlockView
  state : RwState
  decls : Array (Name × ConstantInfo)
  exps : Array (Name × (Expansion × Expr))

private def imagePrefix (cenv : CompileEnv) (all : Ix.Set Name) : Except String ImagePrefixOut := do
  let members := all.toArray.qsort fun a b => a.pretty < b.pretty
  for a in members do
    unless cenv.p3Heads.contains a do throw s!"Pass 3: {a.pretty} is not an image-kind head"
  let views ← viewsOf cenv members
  let inp := viewInput cenv
  let mut st : RwState := {}
  let mut decls : Array (Name × ConstantInfo) := #[]
  let mut exps : Array (Name × (Expansion × Expr)) := #[]
  for a in members do
    let some key := cenv.p3Heads.get? a | throw s!"Pass 3: {a.pretty} is not an image-kind head"
    let (x, ty) ← match cenv.p3ImageExps.get? a with
      | some xt => pure xt
      | none => do
        let v ← viewOf cenv views key
        let xt ← v.expansion inp a
        if (cenv.env.get? a matches some (.recInfo _)) && viewMemoable cenv key then
          exps := exps.push (a, xt)
        pure xt
    let st0 := st
    st := {}
    let (dv, st') ← imageDecl cenv views a x ty st0
    st := st'
    if x.needsRewrite && viewMemoable cenv key && readsMemoable cenv st then
      exps := exps.push (a, ({ x with value := dv.value, needsRewrite := false }, ty))
    decls := decls.push (a, imageInfo cenv dv)
  return ⟨views, st, decls, exps⟩

private def imageSuffix (cenv : CompileEnv) (p : ImagePrefixOut) :
    Except String (Array (Name × BlockResult × BlockState) × Published) := do
  let mut pending := p.decls
  let mut known : Std.HashMap ExactName Address := {}
  let mut out : Array (Name × BlockResult × BlockState) := #[]
  let mut lastErr := ""
  for _ in [0:p.decls.size + 1] do
    if pending.isEmpty then break
    let mut rest : Array (Name × ConstantInfo) := #[]
    for (a, ci) in pending do
      match compileImage cenv known ci with
      | .ok (r, bs) =>
        known := known.insert a r.blockAddr
        out := out.push (a, r, bs)
      | .error e =>
        lastErr := e
        rest := rest.push (a, ci)
    pending := rest
  if !pending.isEmpty then throw lastErr
  return (out, { views := newMemoViews cenv p.views, imageExps := p.exps })

theorem compileImageBlock_eq (cenv : CompileEnv) (all : Ix.Set Name) :
    compileImageBlock cenv all = (imagePrefix cenv all >>= imageSuffix cenv) := by
  simp only [compileImageBlock, imagePrefix, imageSuffix, bind_assoc, pure_bind]
  rfl

theorem rewritePrefix_state (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo)) (cfg : RwConfig) {p : RewritePrefixOut}
    (run : rewritePrefix expansion? members cfg = .ok p) : InstFrames p.state.dev := by
  unfold rewritePrefix at run
  obtain ⟨result, walked, returned⟩ := Loop.except_bind_ok.mp run
  cases Except.ok.inj returned
  refine Loop.forIn_inv_array (fun _ (s : RwState × Array (Name × ConstantInfo) × Array (Name × String)) =>
    InstFrames s.1.dev) _ members ?_ DevelopmentFrames.empty walked
  intro pre item post acc result _ held step
  rcases item with ⟨name, ci⟩
  obtain ⟨⟨⟨ci', changed⟩, after⟩, actual, rest⟩ := Loop.except_bind_ok.mp step
  have safe := CurrentInputs.rewriteConstM_state expansion? ci cfg
    { acc.1 with declines := #[] } after (ci', changed) held actual
  dsimp only at rest
  split at rest
  all_goals cases rest; exact ⟨_, rfl, safe⟩

theorem imagePrefix_state (cenv : CompileEnv) (all : Ix.Set Name) {p : ImagePrefixOut}
    (run : imagePrefix cenv all = .ok p) : InstFrames p.state.dev := by
  unfold imagePrefix at run
  simp only [pure_bind] at run
  obtain ⟨_, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨views, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨result, walked, returned⟩ := Loop.except_bind_ok.mp run
  cases Except.ok.inj returned
  refine Loop.forIn_inv_array (fun _ (s : RwState × Array (Name × ConstantInfo) ×
    Array (Name × (Expansion × Expr))) => InstFrames s.1.dev) _ _ ?_ DevelopmentFrames.empty walked
  intro pre name post acc result _ held step
  split at step
  · rename_i key headFound
    split at step
    · obtain ⟨⟨dv, after⟩, actual, rest⟩ := Loop.except_bind_ok.mp step
      -- The callee receives acc.1, captured before the local st:={} release.
      have safe := CurrentInputs.imageDecl_state _ _ _ _ _ acc.1 held actual
      split at rest
      all_goals cases rest; exact ⟨_, rfl, safe⟩
    · obtain ⟨view, _, step⟩ := Loop.except_bind_ok.mp step
      obtain ⟨xt, _, step⟩ := Loop.except_bind_ok.mp step
      by_cases publish : ((cenv.env.get? name matches some (.recInfo _)) && viewMemoable cenv key) = true
      all_goals
        simp only [publish, ↓reduceIte] at step
        obtain ⟨⟨dv, after⟩, actual, rest⟩ := Loop.except_bind_ok.mp step
        have safe := CurrentInputs.imageDecl_state _ _ _ _ _ acc.1 held actual
        split at rest
        all_goals cases rest; exact ⟨_, rfl, safe⟩
  · cases step

/-- The hidden state is the result of the real member loop, not reconstructed
from BlockRewrite's observable fields. -/
theorem rewriteBlock_receipt (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo)) (cfg : RwConfig) {out : BlockRewrite}
    (run : rewriteBlock expansion? members cfg = .ok out) :
    ∃ p, rewritePrefix expansion? members cfg = .ok p ∧ InstFrames p.state.dev ∧ out = project p := by
  rw [rewriteBlock_eq] at run
  obtain ⟨p, ranPrefix, returned⟩ := Loop.except_bind_ok.mp run
  exact ⟨p, ranPrefix, rewritePrefix_state expansion? members cfg ranPrefix, (Except.ok.inj returned).symm⟩

/-- Full success retains both the actual hidden declaration-prefix state and
the actual compilation-suffix success. Neither implies valid output terms. -/
theorem compileImageBlock_receipt (cenv : CompileEnv) (all : Ix.Set Name)
    {out : Array (Name × BlockResult × BlockState)} {pub : Published}
    (run : compileImageBlock cenv all = .ok (out, pub)) :
    ∃ p, imagePrefix cenv all = .ok p ∧ InstFrames p.state.dev ∧ imageSuffix cenv p = .ok (out, pub) := by
  rw [compileImageBlock_eq] at run
  obtain ⟨p, ranPrefix, suffix⟩ := Loop.except_bind_ok.mp run
  exact ⟨p, ranPrefix, imagePrefix_state cenv all ranPrefix, suffix⟩

end Ix.CompileCert.BlockStates
