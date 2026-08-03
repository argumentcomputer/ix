import Ix.Tc.Verify.Whnf.Projection.StringCallback

/-!
# Finite String-constructor expansion plan

StringCallback leaves only the interned String constructor expansion as a projection
premise.  This slice proves that concrete effectful expansion from a pure,
finite plan: every exact intern request is supported, expression-address
collisions are excluded on the run domain, and the final generated term has
a structural Theory translation.
-/

namespace Ix.Tc
namespace RecM

def stringCharConst (p : Primitives .anon) : KExpr .anon :=
  KExpr.mkConst p.charType #[]

def stringCharOfNat (p : Primitives .anon) : KExpr .anon :=
  KExpr.mkConst p.charOfNat #[]

def stringMkConst (p : Primitives .anon) : KExpr .anon :=
  KExpr.mkConst p.stringOfList #[]

def stringListNilZero (p : Primitives .anon) : KExpr .anon :=
  KExpr.mkConst p.listNil #[KUniv.mkZero]

def stringListNil (p : Primitives .anon) : KExpr .anon :=
  KExpr.mkApp (stringListNilZero p) (stringCharConst p)

def stringListConsZero (p : Primitives .anon) : KExpr .anon :=
  KExpr.mkConst p.listCons #[KUniv.mkZero]

def stringListCons (p : Primitives .anon) : KExpr .anon :=
  KExpr.mkApp (stringListConsZero p) (stringCharConst p)

def stringCharNat (c : Char) : KExpr .anon :=
  natExprFromValue c.toNat

def stringCharValue (charOfNat : KExpr .anon) (c : Char) : KExpr .anon :=
  KExpr.mkApp charOfNat (stringCharNat c)

def stringConsPartial (cons charOfNat : KExpr .anon)
    (c : Char) : KExpr .anon :=
  KExpr.mkApp cons (stringCharValue charOfNat c)

def stringConsValue (cons charOfNat list : KExpr .anon)
    (c : Char) : KExpr .anon :=
  KExpr.mkApp (stringConsPartial cons charOfNat c) list

/-- The portion of String expansion determined by an already-read primitive
table.  This is definitionally the body of production's
`strLitToConstructor`; naming it keeps the primitive-table read and the
finite intern transaction as separate proof layers. -/
def strLitToConstructorWithPrimitives (p : Primitives .anon)
    (value : String) : RecM .anon (KExpr .anon) := do
  let charConst ← TcM.intern (stringCharConst p)
  let charOfNat ← TcM.intern (stringCharOfNat p)
  let stringMk ← TcM.intern (stringMkConst p)
  let listNilZero ← TcM.intern (stringListNilZero p)
  let nil ← TcM.intern (KExpr.mkApp listNilZero charConst)
  let listConsZero ← TcM.intern (stringListConsZero p)
  let cons ← TcM.intern (KExpr.mkApp listConsZero charConst)
  let list ← strLitListToConstructor charOfNat cons value.toList.reverse nil
  TcM.intern (KExpr.mkApp stringMk list)

/-- One-layer equation used when verifying the named primitive-table
transaction. -/
theorem strLitToConstructorWithPrimitives_eq
    (p : Primitives .anon) (value : String) :
    strLitToConstructorWithPrimitives p value = (do
      let charConst ← TcM.intern (stringCharConst p)
      let charOfNat ← TcM.intern (stringCharOfNat p)
      let stringMk ← TcM.intern (stringMkConst p)
      let listNilZero ← TcM.intern (stringListNilZero p)
      let nil ← TcM.intern (KExpr.mkApp listNilZero charConst)
      let listConsZero ← TcM.intern (stringListConsZero p)
      let cons ← TcM.intern (KExpr.mkApp listConsZero charConst)
      let list ← strLitListToConstructor charOfNat cons
        value.toList.reverse nil
      TcM.intern (KExpr.mkApp stringMk list)) := by
  rfl

/-- Stable one-layer equation for the production String expander.  Keeping
this equation explicit lets the proof unfold exactly this transaction without
asking the elaborator to reduce `strLitToConstructor` through every later
WHNF contract that mentions it. -/
theorem strLitToConstructor_eq (value : String) :
    strLitToConstructor value = (do
      let p ← prims
      strLitToConstructorWithPrimitives p value) := by
  rfl

attribute [local irreducible] strLitToConstructor
  strLitToConstructorWithPrimitives

/-- Pure finite certificate for the recursive character fold.  The result
index is the exact list term returned after all characters are consumed. -/
inductive StringListPlan (support : RunSupport)
    (charOfNat cons : KExpr .anon) :
    List Char → KExpr .anon → KExpr .anon → Prop
  | nil {list} (hlist : support list) :
      StringListPlan support charOfNat cons [] list list
  | cons {c chars list result}
      (hnat : support (stringCharNat c))
      (hchar : support (stringCharValue charOfNat c))
      (hpartial : support (stringConsPartial cons charOfNat c))
      (hnext : support (stringConsValue cons charOfNat list c))
      (tail : StringListPlan support charOfNat cons chars
        (stringConsValue cons charOfNat list c) result) :
      StringListPlan support charOfNat cons (c :: chars) list result

/-- The actual recursive String-list builder executes any finite pure plan,
returning its exact result and preserving the complete K1 invariant. -/
theorem strLitListToConstructor_plan_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hcollision : support.CollisionFree)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {charOfNat cons list result : KExpr .anon} {chars : List Char}
    (plan : StringListPlan support charOfNat cons chars list result) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (strLitListToConstructor charOfNat cons chars list)
      (fun actual _ => actual = result ∧ support actual) := by
  induction plan generalizing s with
  | nil hlist =>
      rw [strLitListToConstructor]
      exact RecM.WF.pure fun _ => ⟨rfl, hlist⟩
  | cons hnat hchar hpartial hnext tail ih =>
      rw [strLitListToConstructor]
      refine RecM.WF.bind
        (RecM.WF.liftTcM <| TcM.intern_whnf_wf hcollision hnat) ?_
      intro natLit s1 hNat
      rcases hNat with ⟨rfl, _⟩
      refine RecM.WF.bind
        (RecM.WF.liftTcM <| TcM.intern_whnf_wf hcollision hchar) ?_
      intro charValue s2 hChar
      rcases hChar with ⟨rfl, _⟩
      refine RecM.WF.bind
        (RecM.WF.liftTcM <| TcM.intern_whnf_wf hcollision hpartial) ?_
      intro partialApp s3 hPartial
      rcases hPartial with ⟨rfl, _⟩
      refine RecM.WF.bind
        (RecM.WF.liftTcM <| TcM.intern_whnf_wf hcollision hnext) ?_
      intro next s4 hNext
      rcases hNext with ⟨rfl, _⟩
      exact ih (s := s4)

/-- Complete finite plan for one String literal under one primitive table. -/
structure StringExpansionPlan (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (p : Primitives .anon) (value : String) where
  list : KExpr .anon
  charConst : support (stringCharConst p)
  charOfNat : support (stringCharOfNat p)
  stringMk : support (stringMkConst p)
  listNilZero : support (stringListNilZero p)
  nil : support (stringListNil p)
  listConsZero : support (stringListConsZero p)
  cons : support (stringListCons p)
  chars : StringListPlan support (stringCharOfNat p) (stringListCons p)
    value.toList.reverse (stringListNil p) list
  final : support (KExpr.mkApp (stringMkConst p) list)
  translation : ∀ uvars Delta,
    ∃ expandedV,
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (KExpr.mkApp (stringMkConst p) list) expandedV

/-- The already-read primitive-table transaction executes the exact finite
plan, including all seven prefix interns, the recursive character fold, and
the final `String.ofList` application.  This stronger form retains the exact
concrete result so semantic clients can attach a specific translation rather
than merely an existential one. -/
theorem strLitToConstructorWithPrimitives_plan_exact_wf
    {layer : WhnfLayer} {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hcollision : support.CollisionFree)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {p : Primitives .anon} {value : String}
    (plan : StringExpansionPlan trProj world support p value) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (strLitToConstructorWithPrimitives p value)
      (fun expanded _ =>
        expanded = KExpr.mkApp (stringMkConst p) plan.list ∧
          support expanded ∧
          ∃ expandedV,
            TrKExprS world.venv uvars world.nameOf trProj Delta expanded
              expandedV) := by
  intro methods hmethods hI
  obtain ⟨s1, hCharConst, hI1, _⟩ :=
    TcM.intern_whnf_eval hcollision plan.charConst hI
  obtain ⟨s2, hCharOfNat, hI2, _⟩ :=
    TcM.intern_whnf_eval hcollision plan.charOfNat hI1
  obtain ⟨s3, hStringMk, hI3, _⟩ :=
    TcM.intern_whnf_eval hcollision plan.stringMk hI2
  obtain ⟨s4, hListNilZero, hI4, _⟩ :=
    TcM.intern_whnf_eval hcollision plan.listNilZero hI3
  obtain ⟨s5, hNil, hI5, _⟩ :=
    TcM.intern_whnf_eval hcollision plan.nil hI4
  obtain ⟨s6, hListConsZero, hI6, _⟩ :=
    TcM.intern_whnf_eval hcollision plan.listConsZero hI5
  obtain ⟨s7, hCons, hI7, _⟩ :=
    TcM.intern_whnf_eval hcollision plan.cons hI6
  obtain ⟨actualList, s8, hList, _⟩ :=
    strLitListToConstructor_success_frame methods value.toList.reverse
      (stringCharOfNat p) (stringListCons p) (stringListNil p) s7
  have hListPost :=
    strLitListToConstructor_plan_wf hcollision (s := s7) plan.chars
      methods hmethods hI7
  rw [hList] at hListPost
  rcases hListPost with ⟨hI8, hActualList, _⟩
  subst actualList
  obtain ⟨s9, hFinal, hI9, _⟩ :=
    TcM.intern_whnf_eval hcollision plan.final hI8
  have hrun :
      (strLitToConstructorWithPrimitives p value).run methods s =
        .ok (KExpr.mkApp (stringMkConst p) plan.list) s9 := by
    rw [strLitToConstructorWithPrimitives_eq]
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.intern (stringCharConst p)) _ s = _
    unfold EStateM.bind
    rw [hCharConst]
    simp only
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.intern (stringCharOfNat p)) _ s1 = _
    unfold EStateM.bind
    rw [hCharOfNat]
    simp only
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.intern (stringMkConst p)) _ s2 = _
    unfold EStateM.bind
    rw [hStringMk]
    simp only
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.intern (stringListNilZero p)) _ s3 = _
    unfold EStateM.bind
    rw [hListNilZero]
    simp only
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.intern (stringListNil p)) _ s4 = _
    unfold EStateM.bind
    rw [hNil]
    simp only
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.intern (stringListConsZero p)) _ s5 = _
    unfold EStateM.bind
    rw [hListConsZero]
    simp only
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.intern (stringListCons p)) _ s6 = _
    unfold EStateM.bind
    rw [hCons]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run
        (strLitListToConstructor (stringCharOfNat p) (stringListCons p)
          value.toList.reverse (stringListNil p)) methods) _ s7 = _
    unfold EStateM.bind
    rw [hList]
    simp only
    rw [ReaderT.run_monadLift]
    exact hFinal
  rw [hrun]
  exact ⟨hI9, rfl, plan.final, plan.translation uvars Delta⟩

/-- Compatibility form used by K1 callers that need only support and some
structural translation of the generated constructor term. -/
theorem strLitToConstructorWithPrimitives_plan_wf
    {layer : WhnfLayer} {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hcollision : support.CollisionFree)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {p : Primitives .anon} {value : String}
    (plan : StringExpansionPlan trProj world support p value) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (strLitToConstructorWithPrimitives p value)
      (fun expanded _ =>
        support expanded ∧
          ∃ expandedV,
            TrKExprS world.venv uvars world.nameOf trProj Delta expanded
              expandedV) := by
  apply RecM.WF.mono
    (strLitToConstructorWithPrimitives_plan_exact_wf hcollision plan)
  · intro expanded after hpost
    exact ⟨hpost.2.1, hpost.2.2⟩
  · intro _ _ _
    trivial

/-- Exact production String expansion, including the primitive-table read. -/
theorem strLitToConstructor_plan_exact_wf
    {layer : WhnfLayer} {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hcollision : support.CollisionFree)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon} {value : String}
    (plan : StringExpansionPlan trProj world support s.prims value) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (strLitToConstructor value)
      (fun expanded _ =>
        expanded = KExpr.mkApp (stringMkConst s.prims) plan.list ∧
          support expanded ∧
          ∃ expandedV,
            TrKExprS world.venv uvars world.nameOf trProj Delta expanded
              expandedV) := by
  rw [strLitToConstructor_eq]
  apply RecM.WF.bind
    (Q₁ := fun p after => p = s.prims ∧ after = s)
    (prims_wf (s := s))
  intro p after hread
  rcases hread with ⟨rfl, rfl⟩
  exact strLitToConstructorWithPrimitives_plan_exact_wf hcollision plan

/-- Production's full `strLitToConstructor` transaction first reads the
primitive table without changing state and then executes the certified finite
intern transaction above. -/
theorem strLitToConstructor_plan_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hcollision : support.CollisionFree)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon} {value : String}
    (plan : StringExpansionPlan trProj world support s.prims value) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (strLitToConstructor value)
      (fun expanded _ =>
        support expanded ∧
          ∃ expandedV,
            TrKExprS world.venv uvars world.nameOf trProj Delta expanded
              expandedV) := by
  rw [strLitToConstructor_eq]
  refine RecM.WF.bind
    (Q₁ := fun p after => p = s.prims ∧ after = s)
    (prims_wf (s := s)) ?_
  rintro p after ⟨rfl, rfl⟩
  exact strLitToConstructorWithPrimitives_plan_wf hcollision plan

/-- Run-scoped pure inputs for every canonical production primitive table. -/
structure ProjectionStringPlanContext (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) where
  collisionFree : support.CollisionFree
  plan : ∀ p, p.CanonicalAnon → ∀ value,
    StringExpansionPlan trProj world support p value

namespace ProjectionStringExpansion

/-- Pure finite plans construct StringCallback's exact effectful expansion contract. -/
theorem ofPlans
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : ProjectionStringPlanContext trProj world support) :
    ProjectionStringExpansion.WF semantics trProj world support where
  run := by
    intro uvars Delta s value blob info hvalue methods hmethods hI
    have plan := context.plan s.prims hI.noAccel_primitives value
    exact strLitToConstructor_plan_wf context.collisionFree plan methods
      hmethods hI

end ProjectionStringExpansion

namespace ProjectionHelper

/-- Projection-helper closure from pure String generation data plus the
remaining concrete lazy-ingress refinement. -/
theorem noAccelOfStringPlans
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hinputs : WhnfCoreInputSupport support)
    (hfault : ∀ uvars Delta,
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (context : ProjectionStringPlanContext trProj world support) :
    ProjectionHelper.WF .noAccel semantics trProj world support :=
  ProjectionHelper.noAccelOfExpansion hinputs hfault
    (ProjectionStringExpansion.ofPlans context)

end ProjectionHelper

end RecM
end Ix.Tc
