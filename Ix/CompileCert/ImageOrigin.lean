import Ix.Compile.Pass.ImageView
import Ix.CompileCert.Loop

/-! # Provenance of the actual image generator's result

The prefix witnesses retain the StateT states used by imageOf's telescope,
minor analysis and buildRecApp. The returned value and header fields are
identified through the successful computation-rule loop, without assuming
that the rules are semantically valid or that development is faithful.
-/

namespace Ix.CompileCert.ImageOrigin

open Ix (Name Expr RecursorVal InductiveVal ConstantInfo)
open Ix.Compile.Image
open Ix.Compile.Pass
open Ix.CompileCert.Loop (except_bind_ok)

theorem run'_ok {α : Type} {x : GenM α} {a : α} (h : GenM.run' x = .ok a) :
    ∃ s, x.run {} = .ok (a, s) := by
  unfold GenM.run' at h
  simp only [StateT.run'_eq] at h
  cases hx : x.run {} with
  | error e => simp [hx, Functor.map, Except.map] at h
  | ok p =>
    have eq : p.1 = a := by simpa [hx, Functor.map, Except.map] using h
    exact ⟨p.2, congrArg Except.ok (Prod.ext eq rfl)⟩

theorem bind_ok {α β : Type} {x : GenM α} {f : α → GenM β} {s t : GenState} {b : β}
    (h : (x >>= f).run s = .ok (b, t)) :
    ∃ a u, x.run s = .ok (a, u) ∧ (f a).run u = .ok (b, t) := by
  rw [StateT.run_bind] at h
  obtain ⟨⟨a, u⟩, hx, hf⟩ := except_bind_ok.mp h
  exact ⟨a, u, hx, hf⟩

theorem lift_ok {α : Type} {x : Except String α} {a : α} {s t : GenState}
    (h : (liftExcept x).run s = .ok (a, t)) : x = .ok a ∧ s = t := by
  cases x with
  | error e => cases h
  | ok b =>
    have eq : (b, s) = (a, t) := Except.ok.inj h
    exact ⟨congrArg Except.ok (congrArg Prod.fst eq), congrArg Prod.snd eq⟩

theorem pure_ok {α : Type} {a b : α} {s t : GenState}
    (h : (pure a : GenM α).run s = .ok (b, t)) : a = b ∧ s = t := by
  have eq : (a, s) = (b, t) := Except.ok.inj h
  exact ⟨congrArg Prod.fst eq, congrArg Prod.snd eq⟩

/-- Data obtained from the real generator prefix, before its rule loop. -/
structure Prefix where
  rv : RecursorVal
  xs : Array Local
  body : Expr
  major : Local
  motive : Local
  minors : Array LeanMinor
  first : Name
  ind : InductiveVal
  target : Nat
  value : Expr
  afterTelescope : GenState
  afterMinors : GenState
  afterValue : GenState

def Prefix.params (p : Prefix) := p.xs.extract 0 p.rv.numParams
def Prefix.motives (p : Prefix) := p.xs.extract p.rv.numParams (p.rv.numParams + p.rv.numMotives)
def Prefix.minorLocals (p : Prefix) :=
  p.xs.extract (p.rv.numParams + p.rv.numMotives) (p.rv.numParams + p.rv.numMotives + p.rv.numMinors)
def Prefix.indices (p : Prefix) :=
  p.xs.extract (p.rv.numParams + p.rv.numMotives + p.rv.numMinors) (p.xs.size - 1)

def Prefix.context (p : Prefix) (opts : GenOptions) (const? : Name → Option ConstantInfo)
    (spec : ImageSpec) : LCtx :=
  { const?, spec, opts, ps := p.params, ms := p.motives, mins := p.minorLocals,
    motiveTys := p.motives.map fun m => stripSort m.type, minors := p.minors,
    lu := motiveLevel p.motive.type, indLevels := p.ind.cnst.levelParams.map Ix.Level.mkParam }

/-- Every prefix result is tied to its actual successful operation and state.
Pure lookups keep the state, rather than supplying a new independent one. -/
def Prefix.Ran (p : Prefix) (opts : GenOptions) (const? : Name → Option ConstantInfo)
    (spec : ImageSpec) (r : Name) : Prop :=
  recOf const? r = .ok p.rv ∧
  (telescope (spec.tr p.rv.cnst.type)).run {} = .ok ((p.xs, p.body), p.afterTelescope) ∧
  p.xs.back? = some p.major ∧ p.motives[0]? = some p.motive ∧
  (p.minorLocals.mapM fun m => analyzeLeanMinor p.motives m.type).run p.afterTelescope =
    .ok (p.minors, p.afterMinors) ∧
  p.rv.all[0]? = some p.first ∧ indOf const? p.first = .ok p.ind ∧
  fvarIdx? p.motives (getAppFn p.body) = some p.target ∧
  (buildRecApp (p.rv.numMotives + 1) (p.context opts const? spec) p.target
    (p.indices.map (·.expr)) p.major.expr).run p.afterMinors = .ok (p.value, p.afterValue)

/-- The generated value and immutable image fields, independent of the
subsequent rule-loop contents. This states no source recursor simulation. -/
def Prefix.Result (p : Prefix) (spec : ImageSpec) (r : Name) (img : Image) : Prop :=
  img.leanRec = r ∧ img.name = spec.naming.img r ∧ img.levelParams = p.rv.cnst.levelParams ∧
  img.type = spec.tr p.rv.cnst.type ∧ img.value = mkLambda p.xs p.value ∧
  img.numParams = p.rv.numParams ∧ img.numMotives = p.rv.numMotives ∧
  img.numMinors = p.rv.numMinors ∧ img.numIndices = p.rv.numIndices

theorem imageOf_origin {opts : GenOptions} {const? : Name → Option ConstantInfo}
    {spec : ImageSpec} {r : Name} {img : Image} (h : imageOf opts const? spec r = .ok img) :
    ∃ p : Prefix, p.Ran opts const? spec r ∧ p.Result spec r img := by
  unfold imageOf at h
  obtain ⟨finish, h⟩ := run'_ok h
  obtain ⟨rv, s0, hrvRun, h⟩ := bind_ok h
  obtain ⟨hrv, hs0⟩ := lift_ok hrvRun
  subst s0
  obtain ⟨⟨xs, body⟩, s1, htel, h⟩ := bind_ok h
  dsimp only at h
  cases hmajor : xs.back? with
  | none => rw [hmajor] at h; cases h
  | some major =>
    rw [hmajor] at h
    cases hmotive : (xs.extract rv.numParams (rv.numParams + rv.numMotives))[0]? with
    | none => rw [hmotive] at h; cases h
    | some motive =>
      rw [hmotive] at h
      obtain ⟨minors, s2, hminors, h⟩ := bind_ok h
      cases hfirst : rv.all[0]? with
      | none => rw [hfirst] at h; cases h
      | some first =>
        rw [hfirst] at h
        obtain ⟨ind, s2', hindRun, h⟩ := bind_ok h
        obtain ⟨hind, hs2⟩ := lift_ok hindRun
        subst s2'
        cases htarget : fvarIdx? (xs.extract rv.numParams (rv.numParams + rv.numMotives)) (getAppFn body) with
        | none => rw [htarget] at h; cases h
        | some target =>
          rw [htarget] at h
          obtain ⟨value, s3, hvalue, h⟩ := bind_ok h
          cases hhead : headConst? major.type with
          | none => rw [hhead] at h; cases h
          | some pair =>
            rw [hhead] at h
            obtain ⟨rules, _, _, h⟩ := bind_ok h
            have eq := (pure_ok h).1
            subst img
            refine ⟨⟨rv, xs, body, major, motive, minors, first, ind, target, value, s1, s2, s3⟩,
              ?_, by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
            exact ⟨hrv, htel, hmajor, hmotive, hminors, hfirst, hind, htarget, hvalue⟩

/-- The production view uses default generator options and retains the exact
back-renaming on the returned value, type and rule statements. -/
theorem view_image_origin {inp : ViewInput} {view : BlockView} {r : Name} {img : Image}
    (h : view.image inp r = .ok img) :
    ∃ (raw : Image) (p : Prefix), imageOf {} (view.const? inp) view.spec r = .ok raw ∧
      p.Ran {} (view.const? inp) view.spec r ∧ p.Result view.spec r raw ∧
      img = { raw with
        value := Ix.Compile.Canon.canonicalizeConstNames view.back raw.value
        type := Ix.Compile.Canon.canonicalizeConstNames view.back raw.type
        rules := raw.rules.map fun rule => { rule with
          type := Ix.Compile.Canon.canonicalizeConstNames view.back rule.type
          proof := Ix.Compile.Canon.canonicalizeConstNames view.back rule.proof } } := by
  unfold BlockView.image at h
  obtain ⟨raw, generated, h⟩ := except_bind_ok.mp h
  obtain ⟨p, ran, result⟩ := imageOf_origin generated
  exact ⟨raw, p, generated, ran, result, (Except.ok.inj h).symm⟩

/-- Successful view construction keeps the specification it actually built.
No independently supplied ImageSpec or naming policy is substituted. -/
theorem buildViewWith_spec {inp : ViewInput} {canon : Ix.Compile.Canon.BlockCanon}
    {all : Array Name} {view : BlockView} (h : buildViewWith inp canon all = .ok view) :
    ImageSpec.ofBlock viewNaming inp.const? canon = .ok view.spec ∧ view.canon = canon ∧ view.all = all := by
  unfold buildViewWith at h
  obtain ⟨spec, hspec, h⟩ := except_bind_ok.mp h
  cases first : all[0]? with
  | none => rw [first] at h; cases h
  | some n =>
    rw [first] at h
    obtain ⟨_, _, h⟩ := except_bind_ok.mp h
    obtain ⟨_, _, h⟩ := except_bind_ok.mp h
    have eq := Except.ok.inj h
    subst view
    exact ⟨hspec, rfl, rfl⟩

/-- The full production build retains the successful canonicalizer call as
well as its own successful view/spec construction. -/
theorem buildView_origin {inp : ViewInput} {all : Array Name} {view : BlockView}
    (h : buildView inp all = .ok view) :
    ∃ canon, canonBlockCompiled inp.env (fun n => (inp.addr? n).isSome) all = .ok canon ∧
      buildViewWith inp canon all = .ok view ∧
      ImageSpec.ofBlock viewNaming inp.const? canon = .ok view.spec ∧
      view.canon = canon ∧ view.all = all := by
  unfold buildView at h
  obtain ⟨canon, compiled, built⟩ := except_bind_ok.mp h
  exact ⟨canon, compiled, built, buildViewWith_spec built⟩

end Ix.CompileCert.ImageOrigin
