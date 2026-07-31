import Ix.Tc.Verify.InstUniv
import Std.Data.HashMap.Lemmas

/-!
# G3: finite run-scoped collision and arithmetic support

The expression walkers were already proved against an abstract predicate
`S`, with separate hypotheses that their reach relation and the initial
intern-table range lie inside `S`.  This module makes the missing composition
layer explicit:

* `FiniteSupport` gives a small, constructive notion of a finite predicate;
* every currently formalized expression-walker reach is proved finite;
* `WalkerRequest` records the operations whose address observations belong to
  one run, including direct expression and universe interning;
* `RunSupport` packages a finite expression predicate, while
  `CheckConstSupport` proves that it covers the initial intern table and every
  recorded request; and
* `ResourceBounds` records both the walk-execution bounds and the stronger
  bounds needed to keep generated lift/substitution results `Constructed`.

`Verify/Run.lean` connects these finite requests to actual `TcM` computations
with a proof-level execution certificate.  Later soundness slices extend that
certificate through whnf, inference, definitional equality, and cache-key
operations.  Nothing here treats constructor closure as support: that would
be infinite and would make finite collision freedom impossible.
-/

namespace Ix.Tc

/-! ## Constructive finite predicates -/

/-- A predicate is finite when one concrete list contains every witness.
Duplicates are harmless, and no decidable equality or classical choice is
needed. -/
def FiniteSupport {α : Type u} (S : α → Prop) : Prop :=
  ∃ xs : List α, ∀ ⦃x⦄, S x → x ∈ xs

namespace FiniteSupport

theorem empty : FiniteSupport (fun _ : α => False) :=
  ⟨[], fun {_} h => False.elim h⟩

theorem singleton (a : α) : FiniteSupport (fun x => x = a) :=
  ⟨[a], fun {x} h => by subst x; simp⟩

/-- Finiteness is downward closed. -/
theorem mono {S T : α → Prop} (hT : FiniteSupport T)
    (hsub : ∀ x, S x → T x) : FiniteSupport S := by
  obtain ⟨xs, hxs⟩ := hT
  exact ⟨xs, fun {x} h => hxs (hsub x h)⟩

theorem union {S T : α → Prop} (hS : FiniteSupport S)
    (hT : FiniteSupport T) : FiniteSupport (fun x => S x ∨ T x) := by
  obtain ⟨xs, hxs⟩ := hS
  obtain ⟨ys, hys⟩ := hT
  refine ⟨xs ++ ys, fun {_} h => ?_⟩
  exact List.mem_append.mpr <| h.elim (fun hs => .inl (hxs hs))
    (fun ht => .inr (hys ht))

end FiniteSupport

/-! ## Existing walker reaches are genuinely finite -/

private def liftReachList (shift : UInt64) :
    KExpr .anon → UInt64 → List (KExpr .anon)
  | e, cutoff =>
    e :: KExpr.liftSpec e shift cutoff ::
      match e with
      | .app f a _ => liftReachList shift f cutoff ++
          liftReachList shift a cutoff
      | .lam _ _ ty body _ | .all _ _ ty body _ =>
        liftReachList shift ty cutoff ++
          liftReachList shift body (cutoff + 1)
      | .letE _ ty val body _ _ =>
        liftReachList shift ty cutoff ++
          liftReachList shift val cutoff ++
          liftReachList shift body (cutoff + 1)
      | .prj _ _ val _ => liftReachList shift val cutoff
      | _ => []

private theorem mem_liftReachList {shift cutoff : UInt64}
    {e x : KExpr .anon} :
    x ∈ liftReachList shift e cutoff ↔ KExpr.LiftReach shift e cutoff x := by
  induction e generalizing cutoff
  <;> simp_all [KExpr.LiftReach, liftReachList, or_assoc, or_left_comm,
    or_comm]

namespace KExpr.LiftReach

/-- The exact, spec-determined footprint of one lift walk has finite support. -/
theorem finite (shift : UInt64) (e : KExpr .anon) (cutoff : UInt64) :
    FiniteSupport (KExpr.LiftReach shift e cutoff) :=
  ⟨liftReachList shift e cutoff, fun {_} h => mem_liftReachList.mpr h⟩

end KExpr.LiftReach

private def substReachList (arg : KExpr .anon) :
    KExpr .anon → UInt64 → List (KExpr .anon)
  | body, depth =>
    body :: KExpr.substSpec body arg depth ::
      match body with
      | .var _ _ _ => liftReachList depth arg 0
      | .app f a _ => substReachList arg f depth ++
          substReachList arg a depth
      | .lam _ _ ty inner _ | .all _ _ ty inner _ =>
        substReachList arg ty depth ++
          substReachList arg inner (depth + 1)
      | .letE _ ty val inner _ _ =>
        substReachList arg ty depth ++
          substReachList arg val depth ++
          substReachList arg inner (depth + 1)
      | .prj _ _ val _ => substReachList arg val depth
      | _ => []

private theorem mem_substReachList {arg body x : KExpr .anon}
    {depth : UInt64} :
    x ∈ substReachList arg body depth ↔
      KExpr.SubstReach arg body depth x := by
  induction body generalizing depth
  <;> simp_all [KExpr.SubstReach, substReachList, mem_liftReachList,
    or_assoc, or_left_comm, or_comm]

namespace KExpr.SubstReach

/-- The composed substitution footprint, including its nested lift calls, is
finite. -/
theorem finite (arg body : KExpr .anon) (depth : UInt64) :
    FiniteSupport (KExpr.SubstReach arg body depth) :=
  ⟨substReachList arg body depth, fun {_} h => mem_substReachList.mpr h⟩

end KExpr.SubstReach

private def simulSubstReachList (substs : Array (KExpr .anon)) :
    KExpr .anon → UInt64 → List (KExpr .anon)
  | body, depth =>
    body :: KExpr.simulSubstSpec body substs depth ::
      match body with
      | .var i _ _ => liftReachList depth substs[(i - depth).toNat]! 0
      | .app f a _ => simulSubstReachList substs f depth ++
          simulSubstReachList substs a depth
      | .lam _ _ ty inner _ | .all _ _ ty inner _ =>
        simulSubstReachList substs ty depth ++
          simulSubstReachList substs inner (depth + 1)
      | .letE _ ty val inner _ _ =>
        simulSubstReachList substs ty depth ++
          simulSubstReachList substs val depth ++
          simulSubstReachList substs inner (depth + 1)
      | .prj _ _ val _ => simulSubstReachList substs val depth
      | _ => []

private theorem mem_simulSubstReachList
    {substs : Array (KExpr .anon)} {body x : KExpr .anon}
    {depth : UInt64} :
    x ∈ simulSubstReachList substs body depth ↔
      KExpr.SimulSubstReach substs body depth x := by
  induction body generalizing depth
  <;> simp_all [KExpr.SimulSubstReach, simulSubstReachList,
    mem_liftReachList, or_assoc, or_left_comm, or_comm]

namespace KExpr.SimulSubstReach

/-- Simultaneous substitution, including every nested lift footprint, has a
finite spec-determined support. -/
theorem finite (substs : Array (KExpr .anon)) (body : KExpr .anon)
    (depth : UInt64) :
    FiniteSupport (KExpr.SimulSubstReach substs body depth) :=
  ⟨simulSubstReachList substs body depth,
    fun {_} h => mem_simulSubstReachList.mpr h⟩

end KExpr.SimulSubstReach

private def instRevReachList (fvars : Array (KExpr .anon)) :
    KExpr .anon → UInt64 → List (KExpr .anon)
  | body, depth =>
    body :: KExpr.instantiateRevSpec body fvars depth ::
      match body with
      | .app f a _ => instRevReachList fvars f depth ++
          instRevReachList fvars a depth
      | .lam _ _ ty inner _ | .all _ _ ty inner _ =>
        instRevReachList fvars ty depth ++
          instRevReachList fvars inner (depth + 1)
      | .letE _ ty val inner _ _ =>
        instRevReachList fvars ty depth ++
          instRevReachList fvars val depth ++
          instRevReachList fvars inner (depth + 1)
      | .prj _ _ val _ => instRevReachList fvars val depth
      | _ => []

private theorem mem_instRevReachList
    {fvars : Array (KExpr .anon)} {body x : KExpr .anon}
    {depth : UInt64} :
    x ∈ instRevReachList fvars body depth ↔
      KExpr.InstRevReach fvars body depth x := by
  induction body generalizing depth
  <;> simp_all [KExpr.InstRevReach, instRevReachList,
    or_assoc, or_left_comm, or_comm]

namespace KExpr.InstRevReach

/-- Reverse binder instantiation has a finite spec-determined support. -/
theorem finite (fvars : Array (KExpr .anon)) (body : KExpr .anon)
    (depth : UInt64) :
    FiniteSupport (KExpr.InstRevReach fvars body depth) :=
  ⟨instRevReachList fvars body depth,
    fun {_} h => mem_instRevReachList.mpr h⟩

end KExpr.InstRevReach

private def abstractReachList (pos : Std.HashMap FVarId UInt64)
    (n : UInt64) : KExpr .anon → UInt64 → List (KExpr .anon)
  | body, depth =>
    body :: KExpr.abstractFVarsSpec body pos n depth ::
      match body with
      | .app f a _ => abstractReachList pos n f depth ++
          abstractReachList pos n a depth
      | .lam _ _ ty inner _ | .all _ _ ty inner _ =>
        abstractReachList pos n ty depth ++
          abstractReachList pos n inner (depth + 1)
      | .letE _ ty val inner _ _ =>
        abstractReachList pos n ty depth ++
          abstractReachList pos n val depth ++
          abstractReachList pos n inner (depth + 1)
      | .prj _ _ val _ => abstractReachList pos n val depth
      | _ => []

private theorem mem_abstractReachList
    {pos : Std.HashMap FVarId UInt64} {n depth : UInt64}
    {body x : KExpr .anon} :
    x ∈ abstractReachList pos n body depth ↔
      KExpr.AbstractReach pos n body depth x := by
  induction body generalizing depth
  <;> simp_all [KExpr.AbstractReach, abstractReachList,
    or_assoc, or_left_comm, or_comm]

namespace KExpr.AbstractReach

/-- Fvar abstraction against a fixed finite position map has a finite
spec-determined expression support. -/
theorem finite (pos : Std.HashMap FVarId UInt64) (n : UInt64)
    (body : KExpr .anon) (depth : UInt64) :
    FiniteSupport (KExpr.AbstractReach pos n body depth) :=
  ⟨abstractReachList pos n body depth,
    fun {_} h => mem_abstractReachList.mpr h⟩

end KExpr.AbstractReach

private def exceptOkList {ε α : Type} : Except ε α → List α
  | .error _ => []
  | .ok x => [x]

private theorem mem_exceptOkList {ε α : Type} {r : Except ε α} {x : α} :
    x ∈ exceptOkList r ↔ r = .ok x := by
  cases r <;> simp [exceptOkList, eq_comm]

private def instUnivReachList (us : Array (KUniv .anon))
    (e : KExpr .anon) : List (KExpr .anon) :=
  e :: exceptOkList (KExpr.instUnivSpec e us) ++
    match e with
    | .app f a _ => instUnivReachList us f ++ instUnivReachList us a
    | .lam _ _ ty body _ | .all _ _ ty body _ =>
      instUnivReachList us ty ++ instUnivReachList us body
    | .letE _ ty val body _ _ =>
      instUnivReachList us ty ++ instUnivReachList us val ++
        instUnivReachList us body
    | .prj _ _ val _ => instUnivReachList us val
    | _ => []
termination_by structural e

private theorem mem_instUnivReachList {us : Array (KUniv .anon)}
    {e x : KExpr .anon} :
    x ∈ instUnivReachList us e ↔ KExpr.InstUnivReach us e x := by
  induction e
  <;> simp_all [KExpr.InstUnivReach, instUnivReachList, mem_exceptOkList,
    or_assoc, or_left_comm, or_comm]

namespace KExpr.InstUnivReach

/-- Universe instantiation has a finite expression footprint even when its
pure spec throws: the optional successful image contributes at most one node
per visited source node. -/
theorem finite (us : Array (KUniv .anon)) (e : KExpr .anon) :
    FiniteSupport (KExpr.InstUnivReach us e) :=
  ⟨instUnivReachList us e, fun {_} h => mem_instUnivReachList.mpr h⟩

end KExpr.InstUnivReach

/-! ## Finite operation lists -/

/-- The position map built by `abstractFVars`: the last fvar is innermost and
therefore receives position zero.  Naming the pure fold lets the execution
certificate and cached-walker theorem share the exact map. -/
def abstractFVarPositions (fvars : Array FVarId) :
    Std.HashMap FVarId UInt64 := Id.run do
  let n := fvars.size.toUInt64
  let mut pos : Std.HashMap FVarId UInt64 := {}
  let mut i : UInt64 := 0
  for fv in fvars do
    pos := pos.insert fv (n - 1 - i)
    i := i + 1
  return pos

/-- The named position-map helper is definitionally the fold used by the
production API.  This equation is the bridge from an `abstractFVars` request
to the already-proved cached walker. -/
theorem abstractFVars_eq (body : KExpr .anon) (fvars : Array FVarId) :
    abstractFVars body fvars =
      if fvars.isEmpty || (!body.hasFVars && body.lbr == 0) then pure body
      else runWalk (abstractFVarsCached body
        (abstractFVarPositions fvars) fvars.size.toUInt64 0) := by
  rw [abstractFVars]
  rfl

namespace KExpr

/-- Pure result of the production `abstractFVars` API.  A term without fvars
is a no-op only when it also has no loose bvars: otherwise wrapping new
binders must shift those bvars even though none of the target fvars occurs. -/
def abstractFVarsResult (body : KExpr .anon) (fvars : Array FVarId) :
    KExpr .anon :=
  if fvars.isEmpty || (!body.hasFVars && body.lbr == 0) then body
  else abstractFVarsSpec body (abstractFVarPositions fvars)
    fvars.size.toUInt64 0

end KExpr

/-! ## Cheap-beta finite footprint -/

/-- Every base/candidate in the left-associated application chain selected
by one cheap-beta plan. -/
def cheapBetaChainList (base : KExpr .anon) :
    List (KExpr .anon) → List (KExpr .anon)
  | [] => [base]
  | arg :: trailing =>
    base :: cheapBetaChainList (KExpr.mkApp base arg) trailing

/-- Exact finite expression footprint of `cheapBetaReduce`: the unchanged
source plus the selected base and every intermediate application candidate. -/
def KExpr.CheapBetaReach (source x : KExpr .anon) : Prop :=
  x ∈ source :: match cheapBetaPlan? source with
    | none => []
    | some plan => cheapBetaChainList plan.base plan.trailing

namespace KExpr.CheapBetaReach

theorem finite (source : KExpr .anon) :
    FiniteSupport (KExpr.CheapBetaReach source) :=
  ⟨source :: match cheapBetaPlan? source with
      | none => []
      | some plan => cheapBetaChainList plan.base plan.trailing,
    fun {_} h => h⟩

end KExpr.CheapBetaReach

/-- Arithmetic/constructedness contract shared by the simultaneous-
substitution request and cheap beta's consumed prefix. -/
def SimulSubstBounds (body : KExpr .anon)
    (substs : Array (KExpr .anon)) (depth : UInt64) : Prop :=
  KExpr.Constructed body ∧
    (∀ k, k < substs.size → KExpr.Constructed substs[k]!) ∧
    (∀ k, k < substs.size → substs[k]!.size < UInt64.size) ∧
    depth.toNat + body.size + substs.size < UInt64.size ∧
    (∀ k, k < substs.size →
      substs[k]!.lbr.toNat + substs[k]!.size + depth.toNat + body.size <
        UInt64.size)

/-- Resource bounds for the exact lambda prefix selected by cheap beta. -/
def KExpr.CheapBetaBounds (source : KExpr .anon) : Prop :=
  (∀ x, KExpr.CheapBetaReach source x → KExpr.Constructed x) ∧
    ∀ {head : KExpr .anon} {args : Array (KExpr .anon)}
        {body : KExpr .anon} {consumed : Nat},
      source.collectSpine = (head, args) →
      peelLamsN args.size head = (body, consumed) →
      SimulSubstBounds body (args.extract 0 consumed).reverse 0

/-- One interning operation whose address reads, memo keys, and candidates
must be covered by the run support. -/
inductive WalkerRequest where
  | internExpr (e : KExpr .anon)
  | internUniv (u : KUniv .anon)
  | lift (e : KExpr .anon) (shift cutoff : UInt64)
  | subst (body arg : KExpr .anon) (depth : UInt64)
  | simulSubst (body : KExpr .anon) (substs : Array (KExpr .anon))
      (depth : UInt64)
  | instRev (body : KExpr .anon) (fvars : Array (KExpr .anon))
  | abstractFVars (body : KExpr .anon) (fvars : Array FVarId)
  | instUniv (e : KExpr .anon) (us : Array (KUniv .anon))
  | cheapBeta (e : KExpr .anon)

namespace WalkerRequest

def Reach : WalkerRequest → KExpr .anon → Prop
  | .internExpr e => fun x => x = e
  | .internUniv _ => fun _ => False
  | .lift e shift cutoff => KExpr.LiftReach shift e cutoff
  | .subst body arg depth => KExpr.SubstReach arg body depth
  | .simulSubst body substs depth =>
    KExpr.SimulSubstReach substs body depth
  | .instRev body fvars => KExpr.InstRevReach fvars body 0
  | .abstractFVars body fvars =>
    KExpr.AbstractReach (abstractFVarPositions fvars)
      fvars.size.toUInt64 body 0
  | .instUniv e us => KExpr.InstUnivReach us e
  | .cheapBeta e => KExpr.CheapBetaReach e

/-- Universe candidates are tracked separately from expressions: the two
address domains have different erasures and therefore different collision
hypotheses. -/
def UnivReach : WalkerRequest → KUniv .anon → Prop
  | .internUniv u => fun x => x = u
  | _ => fun _ => False

theorem reach_finite (request : WalkerRequest) :
    FiniteSupport request.Reach := by
  cases request with
  | internExpr e => exact FiniteSupport.singleton e
  | internUniv _ => exact FiniteSupport.empty
  | lift e shift cutoff => exact KExpr.LiftReach.finite shift e cutoff
  | subst body arg depth => exact KExpr.SubstReach.finite arg body depth
  | simulSubst body substs depth =>
    exact KExpr.SimulSubstReach.finite substs body depth
  | instRev body fvars => exact KExpr.InstRevReach.finite fvars body 0
  | abstractFVars body fvars =>
    exact KExpr.AbstractReach.finite (abstractFVarPositions fvars)
      fvars.size.toUInt64 body 0
  | instUniv e us => exact KExpr.InstUnivReach.finite us e
  | cheapBeta e => exact KExpr.CheapBetaReach.finite e

theorem univReach_finite (request : WalkerRequest) :
    FiniteSupport request.UnivReach := by
  cases request with
  | internUniv u => exact FiniteSupport.singleton u
  | internExpr | lift | subst | simulSubst | instRev | abstractFVars |
      instUniv | cheapBeta =>
    exact FiniteSupport.empty

/-- Covering one request means covering every expression it can address,
memoize, or offer to the intern table. -/
structure CoveredBy (request : WalkerRequest) (S : KExpr .anon → Prop)
    (U : KUniv .anon → Prop) : Prop where
  expr : ∀ x, request.Reach x → S x
  univ : ∀ u, request.UnivReach u → U u

/-- Arithmetic obligations for existing walkers.  The final conjunct in the
lift and substitution cases is intentionally stronger than the walk's own
descent bound: it proves that the generated spec image remains `Constructed`,
so later walkers receive a valid source term.  Universe instantiation does no
`UInt64` binder/index arithmetic and therefore contributes no bound here. -/
def Bounds : WalkerRequest → Prop
  | .internExpr e => KExpr.Constructed e
  | .internUniv _ => True
  | .lift e shift cutoff =>
    KExpr.Constructed e ∧
    cutoff.toNat + e.size < UInt64.size ∧
    e.lbr.toNat + e.size + shift.toNat < UInt64.size
  | .subst body arg depth =>
    KExpr.Constructed body ∧
    KExpr.Constructed arg ∧
    depth.toNat + body.size < UInt64.size ∧
    arg.size < UInt64.size ∧
    arg.lbr.toNat + arg.size + depth.toNat + body.size < UInt64.size
  | .simulSubst body substs depth =>
    SimulSubstBounds body substs depth
  | .instRev body fvars =>
    KExpr.Constructed body ∧
    (∀ k, k < fvars.size → KExpr.Constructed fvars[k]!) ∧
    body.size + fvars.size < UInt64.size
  | .abstractFVars body fvars =>
    KExpr.Constructed body ∧
    (∀ (id : FVarId) (p : UInt64),
      (abstractFVarPositions fvars)[id]? = some p →
        p.toNat < fvars.size.toUInt64.toNat) ∧
    body.size < UInt64.size ∧
    body.lbr.toNat + body.size + fvars.size.toUInt64.toNat < UInt64.size
  | .instUniv _ _ => True
  | .cheapBeta e => KExpr.CheapBetaBounds e

namespace Bounds

theorem lift_result {e : KExpr .anon} {shift cutoff : UInt64}
    (h : WalkerRequest.Bounds (.lift e shift cutoff)) :
    KExpr.Constructed (KExpr.liftSpec e shift cutoff) :=
  h.1.liftSpec h.2.2

theorem subst_result {body arg : KExpr .anon} {depth : UInt64}
    (h : WalkerRequest.Bounds (.subst body arg depth)) :
    KExpr.Constructed (KExpr.substSpec body arg depth) :=
  h.1.substSpec h.2.1 h.2.2.2.2

theorem simulSubst_result {body : KExpr .anon}
    {substs : Array (KExpr .anon)} {depth : UInt64}
    (h : WalkerRequest.Bounds (.simulSubst body substs depth)) :
    KExpr.Constructed (KExpr.simulSubstSpec body substs depth) := by
  rcases h with ⟨hbody, hsubsts, _, hwalk, hresult⟩
  exact hbody.simulSubstSpec hsubsts hwalk hresult

theorem instRev_result {body : KExpr .anon}
    {fvars : Array (KExpr .anon)}
    (h : WalkerRequest.Bounds (.instRev body fvars)) :
    KExpr.Constructed (KExpr.instantiateRevSpec body fvars 0) := by
  rcases h with ⟨hbody, hfvars, hwalk⟩
  exact hbody.instantiateRevSpec hfvars (by simpa using hwalk)

theorem abstractFVarsCached_result {body : KExpr .anon}
    {fvars : Array FVarId}
    (h : WalkerRequest.Bounds (.abstractFVars body fvars)) :
    KExpr.Constructed (KExpr.abstractFVarsSpec body
      (abstractFVarPositions fvars) fvars.size.toUInt64 0) := by
  rcases h with ⟨hbody, hpos, _, hresult⟩
  exact hbody.abstractFVarsSpec hpos hresult

theorem abstractFVars_result {body : KExpr .anon} {fvars : Array FVarId}
    (h : WalkerRequest.Bounds (.abstractFVars body fvars)) :
    KExpr.Constructed (KExpr.abstractFVarsResult body fvars) := by
  unfold KExpr.abstractFVarsResult
  split
  · exact h.1
  · exact abstractFVarsCached_result h

end Bounds

private theorem listReach_finite (requests : List WalkerRequest) :
    FiniteSupport (fun x => ∃ request ∈ requests, request.Reach x) := by
  induction requests with
  | nil =>
    exact FiniteSupport.empty.mono fun _ h => by
      obtain ⟨_, hmem, _⟩ := h
      simp at hmem
  | cons request requests ih =>
    exact (request.reach_finite.union ih).mono fun x h => by
      obtain ⟨r, hr, hx⟩ := h
      rcases List.mem_cons.mp hr with rfl | hr
      · exact .inl hx
      · exact .inr ⟨r, hr, hx⟩

private theorem listUnivReach_finite (requests : List WalkerRequest) :
    FiniteSupport (fun u => ∃ request ∈ requests, request.UnivReach u) := by
  induction requests with
  | nil =>
    exact FiniteSupport.empty.mono fun _ h => by
      obtain ⟨_, hmem, _⟩ := h
      simp at hmem
  | cons request requests ih =>
    exact (request.univReach_finite.union ih).mono fun u h => by
      obtain ⟨r, hr, hu⟩ := h
      rcases List.mem_cons.mp hr with rfl | hr
      · exact .inl hu
      · exact .inr ⟨r, hr, hu⟩

end WalkerRequest

/-! ## A finite run support and its coverage obligations -/

/-- The finite expression and universe domains on which one checker run
assumes Blake3 address faithfulness.  Cache-key domains can be added beside
these without weakening either collision hypothesis. -/
structure RunSupport where
  expr : KExpr .anon → Prop
  exprFinite : FiniteSupport expr
  univ : KUniv .anon → Prop
  univFinite : FiniteSupport univ

instance : CoeFun RunSupport (fun _ => KExpr .anon → Prop) :=
  ⟨RunSupport.expr⟩

namespace RunSupport

instance : LE RunSupport where
  le before after :=
    (∀ x, before x → after x) ∧
    (∀ u, before.univ u → after.univ u)

theorem le_refl (support : RunSupport) : support ≤ support :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem le_trans {a b c : RunSupport} (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c :=
  ⟨fun x hx => hbc.1 x (hab.1 x hx),
    fun u hu => hbc.2 u (hab.2 u hu)⟩

def empty : RunSupport :=
  ⟨fun _ => False, FiniteSupport.empty,
    fun _ => False, FiniteSupport.empty⟩

def singleton (e : KExpr .anon) : RunSupport :=
  ⟨fun x => x = e, FiniteSupport.singleton e,
    fun _ => False, FiniteSupport.empty⟩

/-- A singleton in each address domain, useful for non-vacuous fixtures. -/
def pair (e : KExpr .anon) (u : KUniv .anon) : RunSupport :=
  ⟨fun x => x = e, FiniteSupport.singleton e,
    fun v => v = u, FiniteSupport.singleton u⟩

/-- The actual collision hypotheses over both finite run domains. -/
structure CollisionFree (support : RunSupport) : Prop where
  expr : KExpr.CollisionFree support
  univ : KUniv.CollisionFree support.univ

/-- Collision freedom weakens from a larger run domain to a smaller one. -/
theorem collisionFree_of_le {small large : RunSupport} (hle : small ≤ large)
    (hcf : large.CollisionFree) : small.CollisionFree :=
  ⟨hcf.expr.mono hle.1, hcf.univ.mono hle.2⟩

theorem singleton_collisionFree (e : KExpr .anon) :
    (singleton e).CollisionFree := by
  constructor
  · intro x hx y hy _
    change x = e at hx
    change y = e at hy
    subst x
    subst y
    rfl
  · intro _ h
    exact False.elim h

theorem pair_collisionFree (e : KExpr .anon) (u : KUniv .anon) :
    (pair e u).CollisionFree := by
  constructor
  · intro x hx y hy _
    change x = e at hx
    change y = e at hy
    subst x
    subst y
    rfl
  · intro x hx y hy _
    change x = u at hx
    change y = u at hy
    subst x
    subst y
    rfl

/-- Both initial intern-table ranges are included in the final run scope. -/
structure CoversIntern (support : RunSupport)
    (initial : InternTable .anon) : Prop where
  expr : ∀ x, initial.ExprSupport x → support x
  univ : ∀ u, initial.UnivSupport u → support.univ u

theorem CoversIntern.mono {small large : RunSupport}
    {initial : InternTable .anon} (h : small.CoversIntern initial)
    (hle : small ≤ large) : large.CoversIntern initial :=
  ⟨fun x hx => hle.1 x (h.expr x hx),
    fun u hu => hle.2 u (h.univ u hu)⟩

end RunSupport

/-- A hash map has a concrete finite value list, so its expression-support
predicate is constructively finite. -/
theorem InternTable.exprSupport_finite (initial : InternTable .anon) :
    FiniteSupport initial.ExprSupport := by
  refine ⟨initial.exprs.toList.map Prod.snd, fun {x} hx => ?_⟩
  obtain ⟨a, ha⟩ := hx
  apply List.mem_map.mpr
  exact ⟨(a, x), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ha, rfl⟩

/-- The universe range of a hash map is constructively finite as well. -/
theorem InternTable.univSupport_finite (initial : InternTable .anon) :
    FiniteSupport initial.UnivSupport := by
  refine ⟨initial.univs.toList.map Prod.snd, fun {u} hu => ?_⟩
  obtain ⟨a, ha⟩ := hu
  apply List.mem_map.mpr
  exact ⟨(a, u), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ha, rfl⟩

/-- Exact finite support generated by the initial intern range and a finite
list of existing walker invocations. -/
def RunSupport.scope (initial : InternTable .anon)
    (requests : List WalkerRequest) : RunSupport where
  expr x := initial.ExprSupport x ∨
    ∃ request ∈ requests, request.Reach x
  exprFinite := (InternTable.exprSupport_finite initial).union
    (WalkerRequest.listReach_finite requests)
  univ u := initial.UnivSupport u ∨
    ∃ request ∈ requests, request.UnivReach u
  univFinite := (InternTable.univSupport_finite initial).union
    (WalkerRequest.listUnivReach_finite requests)

/-- Checker-support composition over one explicit request list.
`ExecutionRequests` in Verify/Run.lean ties that same list to the actual
checker computation. -/
structure CheckConstSupport (initial : InternTable .anon)
    (requests : List WalkerRequest) (support : RunSupport) : Prop where
  initial : support.CoversIntern initial
  requests : ∀ request, request ∈ requests →
    request.CoveredBy support support.univ

namespace CheckConstSupport

theorem initial_support {initial : InternTable .anon}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : CheckConstSupport initial requests support) :
    ∀ x, initial.ExprSupport x → support x :=
  h.initial.expr

theorem initial_univ_support {initial : InternTable .anon}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : CheckConstSupport initial requests support) :
    ∀ u, initial.UnivSupport u → support.univ u :=
  h.initial.univ

theorem internExpr {initial : InternTable .anon}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : CheckConstSupport initial requests support) {e : KExpr .anon}
    (hmem : WalkerRequest.internExpr e ∈ requests) : support e :=
  h.requests _ hmem |>.expr e rfl

theorem internUniv {initial : InternTable .anon}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : CheckConstSupport initial requests support) {u : KUniv .anon}
    (hmem : WalkerRequest.internUniv u ∈ requests) : support.univ u :=
  h.requests _ hmem |>.univ u rfl

/-- Project the exact reach premise expected by `lift_spec`. -/
theorem lift {initial : InternTable .anon} {requests : List WalkerRequest}
    {support : RunSupport} (h : CheckConstSupport initial requests support)
    {e : KExpr .anon} {shift cutoff : UInt64}
    (hmem : WalkerRequest.lift e shift cutoff ∈ requests) :
    ∀ x, KExpr.LiftReach shift e cutoff x → support x :=
  (h.requests _ hmem).expr

/-- Project the exact reach premise expected by `subst_spec`. -/
theorem subst {initial : InternTable .anon} {requests : List WalkerRequest}
    {support : RunSupport} (h : CheckConstSupport initial requests support)
    {body arg : KExpr .anon} {depth : UInt64}
    (hmem : WalkerRequest.subst body arg depth ∈ requests) :
    ∀ x, KExpr.SubstReach arg body depth x → support x :=
  (h.requests _ hmem).expr

theorem simulSubst {initial : InternTable .anon}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : CheckConstSupport initial requests support)
    {body : KExpr .anon} {substs : Array (KExpr .anon)} {depth : UInt64}
    (hmem : WalkerRequest.simulSubst body substs depth ∈ requests) :
    ∀ x, KExpr.SimulSubstReach substs body depth x → support x :=
  (h.requests _ hmem).expr

theorem instRev {initial : InternTable .anon}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : CheckConstSupport initial requests support)
    {body : KExpr .anon} {fvars : Array (KExpr .anon)}
    (hmem : WalkerRequest.instRev body fvars ∈ requests) :
    ∀ x, KExpr.InstRevReach fvars body 0 x → support x :=
  (h.requests _ hmem).expr

theorem abstractFVars {initial : InternTable .anon}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : CheckConstSupport initial requests support)
    {body : KExpr .anon} {fvars : Array FVarId}
    (hmem : WalkerRequest.abstractFVars body fvars ∈ requests) :
    ∀ x, KExpr.AbstractReach (abstractFVarPositions fvars)
      fvars.size.toUInt64 body 0 x → support x :=
  (h.requests _ hmem).expr

/-- Project the exact reach premise expected by
`TcM.instantiateUnivParams_wf`. -/
theorem instUniv {initial : InternTable .anon}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : CheckConstSupport initial requests support)
    {e : KExpr .anon} {us : Array (KUniv .anon)}
    (hmem : WalkerRequest.instUniv e us ∈ requests) :
    ∀ x, KExpr.InstUnivReach us e x → support x :=
  (h.requests _ hmem).expr

theorem mono {initial : InternTable .anon} {requests : List WalkerRequest}
    {small large : RunSupport}
    (h : CheckConstSupport initial requests small) (hle : small ≤ large) :
    CheckConstSupport initial requests large := by
  refine ⟨h.initial.mono hle, fun request hmem => ?_⟩
  constructor
  · exact fun x hx => hle.1 x ((h.requests request hmem).expr x hx)
  · exact fun u hu => hle.2 u ((h.requests request hmem).univ u hu)

/-- The exact initial-range-plus-request footprint always satisfies the
coverage interface and is finite by construction. -/
theorem scope (initial : InternTable .anon) (requests : List WalkerRequest) :
    CheckConstSupport initial requests (RunSupport.scope initial requests) := by
  constructor
  · exact ⟨fun _ hx => .inl hx, fun _ hu => .inl hu⟩
  · intro request hmem
    exact ⟨fun _ hx => .inr ⟨request, hmem, hx⟩,
      fun _ hu => .inr ⟨request, hmem, hu⟩⟩

end CheckConstSupport

/-! ## Run-wide arithmetic bounds -/

/-- Every recorded operation carries its source and generated-term arithmetic
obligations.  This is separate from collision support: collision freedom can
weaken to a smaller domain, whereas bounds are indexed by the actual request
list. -/
structure ResourceBounds (requests : List WalkerRequest) : Prop where
  request : ∀ operation, operation ∈ requests → operation.Bounds

namespace ResourceBounds

theorem empty : ResourceBounds [] :=
  ⟨fun _ h => by simp at h⟩

/-- Dropping operations weakens the resource obligation. -/
theorem mono {before after : List WalkerRequest}
    (h : ResourceBounds after)
    (hsub : ∀ operation, operation ∈ before → operation ∈ after) :
    ResourceBounds before :=
  ⟨fun operation hmem => h.request operation (hsub operation hmem)⟩

end ResourceBounds

end Ix.Tc
