import IxVMRefinement.Guard.RawSignature
import IxC.Kernel.Model.ProjGuardCert
import IxC.Kernel.Model.GuardClassifierErase

/-! # A classifier trace computes the classifier function on erased syntax

The raw traces (`RawHeadTrace`, `RawInferTrace`, `RawSignatureTrace`) record the successful
strategy of the runtime classifier over metadata-carrying raw syntax, relative to abstract
declared-type and definition-value answers. The pure classifier (`GuardClassifier.head`,
`infer`, `sortSignature`) is a function with a depth budget over a lookup.

* `RawHeadTrace.head_erased`, `RawInferTrace.infer_erased`,
  `RawSignatureTrace.sortSignature_erased`: where every answer of a trace is the lookup's
  answer with its metadata erased, the function has the trace's result, with its metadata
  erased, at some depth, on the erased input and context.
* `RawDomainTraces`, `RawFieldTraces`: the relational walk over a constructor telescope (the
  field domains after the parameters, each in the context of the binders before it), and
  `RawFieldTraces.fieldSignatures_erased`: it computes `GuardClassifier.fieldSignatures`.

Nothing here mentions a heap, a run or a store.
-/

namespace Ix.Kernel.GuardClassifier

variable {md : Mode}

/-- A successful head result is the result at every larger depth. -/
theorem head_le (look : Lookup md) {fuel fuel' : Nat} (hle : fuel ≤ fuel') {e r : Expr md}
    (h : head look fuel e = some r) : head look fuel' e = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact head_succ look _ e r ih

/-- A successful structural type is the result at every larger depth. -/
theorem infer_le (look : Lookup md) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ctx : List (Expr md)} {e r : Expr md}
    (h : infer look fuel ctx e = some r) : infer look fuel' ctx e = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact infer_succ look _ ctx e r ih

/-- An application whose function exposes a `λ`: the body is instantiated and exposed. -/
theorem head_app_lam {look : Lookup md} {fuel : Nat} {f a dom body r : Expr md}
    {m : BinderMeta} (hf : head look fuel f = some (.lam dom body m))
    (hb : head look fuel (body.instantiate1Lift a) = some r) :
    head look (fuel + 1) (.app f a) = some r := by
  simp [head, hf, hb]

/-- A `λ`: the body's shape under the binder gives the `∀`. -/
theorem infer_lam {look : Lookup md} {fuel : Nat} {ctx : List (Expr md)}
    {ty body tb : Expr md} {m : BinderMeta}
    (hb : infer look fuel (ty :: ctx) body = some tb) :
    infer look (fuel + 1) ctx (.lam ty body m) = some (.forallE ty tb m) := by
  simp [infer, hb]

end Ix.Kernel.GuardClassifier

namespace IxVM.Refinement.Decl

open IxVM.Refinement.Core
open Ix.Kernel (Expr BinderMeta)
open Ix.Kernel.GuardClassifier

/-- **A head trace computes `head`** on the erased input, where every definition answer is the
lookup's with its metadata erased. -/
theorem RawHeadTrace.head_erased {delta : KKey → List KLevel → KExpr → Prop}
    {look : Lookup .anon}
    (answers : ∀ key parameters value, delta key parameters value →
      look.valueOf key parameters = some value.eraseMeta)
    {input result : KExpr} (trace : RawHeadTrace delta input result) :
    ∃ fuel, head look fuel input.eraseMeta = some result.eraseMeta := by
  induction trace with
  | sort level => exact ⟨1, rfl⟩
  | forallE dom body binderData => exact ⟨1, rfl⟩
  | lam dom body binderData => exact ⟨1, rfl⟩
  | @const key parameters value result loaded child ih =>
    obtain ⟨fuel, computed⟩ := ih
    refine ⟨fuel + 1, ?_⟩
    show (look.valueOf key parameters).bind (head look fuel) = some result.eraseMeta
    rw [answers _ _ _ loaded]
    exact computed
  | @app func arg dom body result binderData functionTrace bodyTrace ihf ihb =>
    obtain ⟨first, functionHead⟩ := ihf
    obtain ⟨second, bodyHead⟩ := ihb
    rw [eraseMeta_instantiate1Lift] at bodyHead
    have functionHead' : head look (max first second) func.eraseMeta =
        some (.lam dom.eraseMeta body.eraseMeta default) :=
      head_le look (Nat.le_max_left first second) functionHead
    have bodyHead' := head_le look (Nat.le_max_right first second) bodyHead
    exact ⟨max first second + 1, head_app_lam functionHead' bodyHead'⟩
  | @letE ty value body result binderData bodyTrace ih =>
    obtain ⟨fuel, computed⟩ := ih
    rw [eraseMeta_instantiate1Lift] at computed
    exact ⟨fuel + 1, computed⟩

/-- **An inference trace computes `infer`** on the erased input in the erased context, where
every declared-type and definition answer is the lookup's with its metadata erased. -/
theorem RawInferTrace.infer_erased {types delta : KKey → List KLevel → KExpr → Prop}
    {look : Lookup .anon}
    (typeAnswers : ∀ key parameters type, types key parameters type →
      look.typeOf key parameters = some type.eraseMeta)
    (deltaAnswers : ∀ key parameters value, delta key parameters value →
      look.valueOf key parameters = some value.eraseMeta)
    {context : List KExpr} {input type : KExpr}
    (trace : RawInferTrace types delta context input type) :
    ∃ fuel, infer look fuel (context.map Expr.eraseMeta) input.eraseMeta =
      some type.eraseMeta := by
  induction trace with
  | @bvar context index type selected =>
    refine ⟨1, ?_⟩
    show ((context.map Expr.eraseMeta)[index]?).map (Expr.liftLooseBVars (index + 1) 0) =
      some (type.liftLooseBVars (index + 1) 0).eraseMeta
    simp only [List.getElem?_map, selected, Option.map_some, eraseMeta_lift]
  | sort context level => exact ⟨1, rfl⟩
  | @const context key parameters type loaded => exact ⟨1, typeAnswers _ _ _ loaded⟩
  | @app context func arg type dom body metadata inferred headed ih =>
    obtain ⟨first, functionType⟩ := ih
    obtain ⟨second, exposed⟩ := headed.head_erased deltaAnswers
    have exposed' : head look second type.eraseMeta =
        some (.forallE dom.eraseMeta body.eraseMeta default) := exposed
    refine ⟨max first second + 1, ?_⟩
    show infer look (max first second + 1) (context.map Expr.eraseMeta)
      (.app func.eraseMeta arg.eraseMeta) = some (body.instantiate1Lift arg).eraseMeta
    rw [eraseMeta_instantiate1Lift]
    exact infer_app (infer_le look (Nat.le_max_left first second) functionType)
      (head_le look (Nat.le_max_right first second) exposed')
  | @forallE context dom body type metadata level inferred headed ih =>
    obtain ⟨first, bodyType⟩ := ih
    obtain ⟨second, exposed⟩ := headed.head_erased deltaAnswers
    have bodyType' : infer look first (dom.eraseMeta :: context.map Expr.eraseMeta)
        body.eraseMeta = some type.eraseMeta := bodyType
    have exposed' : head look second type.eraseMeta = some (.sort level) := exposed
    refine ⟨max first second + 1, ?_⟩
    show infer look (max first second + 1) (context.map Expr.eraseMeta)
      (.forallE dom.eraseMeta body.eraseMeta default) = some (.sort level)
    exact infer_forallE (infer_le look (Nat.le_max_left first second) bodyType')
      (head_le look (Nat.le_max_right first second) exposed')
  | @lam context dom body type metadata inferred ih =>
    obtain ⟨fuel, bodyType⟩ := ih
    have bodyType' : infer look fuel (dom.eraseMeta :: context.map Expr.eraseMeta)
        body.eraseMeta = some type.eraseMeta := bodyType
    refine ⟨fuel + 1, ?_⟩
    show infer look (fuel + 1) (context.map Expr.eraseMeta)
      (.lam dom.eraseMeta body.eraseMeta default) =
        some (.forallE dom.eraseMeta type.eraseMeta default)
    exact infer_lam bodyType'
  | @letE context ty value body type metadata inferred ih =>
    obtain ⟨fuel, computed⟩ := ih
    rw [eraseMeta_instantiate1Lift] at computed
    exact ⟨fuel + 1, computed⟩

/-- **A signature trace computes `sortSignature`.** The signature is a level, so nothing is
erased in the result. -/
theorem RawSignatureTrace.sortSignature_erased
    {types delta : KKey → List KLevel → KExpr → Prop} {look : Lookup .anon}
    (typeAnswers : ∀ key parameters type, types key parameters type →
      look.typeOf key parameters = some type.eraseMeta)
    (deltaAnswers : ∀ key parameters value, delta key parameters value →
      look.valueOf key parameters = some value.eraseMeta)
    {context : List KExpr} {input : KExpr} {signature : KLevel}
    (trace : RawSignatureTrace types delta context input signature) :
    ∃ fuel, sortSignature look fuel (context.map Expr.eraseMeta) input.eraseMeta =
      some signature := by
  obtain ⟨type, level, inferred, headed, rfl⟩ := trace
  obtain ⟨first, typed⟩ := inferred.infer_erased typeAnswers deltaAnswers
  obtain ⟨second, exposed⟩ := headed.head_erased deltaAnswers
  have exposed' : head look second type.eraseMeta = some (.sort level) := exposed
  exact ⟨max first second,
    sortSignature_of (infer_le look (Nat.le_max_left first second) typed)
      (head_le look (Nat.le_max_right first second) exposed')⟩

/-- **The signature traces of the next `count` binder domains** of a raw telescope: each
domain is classified in the context of the binders before it, newest first, and then joins
that context. The relational `GuardClassifier.domainSignatures`. -/
inductive RawDomainTraces (types delta : KKey → List KLevel → KExpr → Prop) :
    Nat → List KExpr → KExpr → List KLevel → Prop where
  | done (context : List KExpr) (rest : KExpr) : RawDomainTraces types delta 0 context rest []
  | step {count : Nat} {context : List KExpr} {dom body : KExpr} {metadata : BinderMeta}
      {signature : KLevel} {signatures : List KLevel} :
      RawSignatureTrace types delta context dom signature →
      RawDomainTraces types delta count (dom :: context) body signatures →
      RawDomainTraces types delta (count + 1) context (.forallE dom body metadata)
        (signature :: signatures)

/-- **The signature traces of the fields of a raw constructor telescope** after its
parameters, whose domains only join the context. The relational
`GuardClassifier.fieldSignatures`. -/
inductive RawFieldTraces (types delta : KKey → List KLevel → KExpr → Prop) :
    Nat → Nat → List KExpr → KExpr → List KLevel → Prop where
  | fields {fieldCount : Nat} {context : List KExpr} {telescope : KExpr}
      {signatures : List KLevel} :
      RawDomainTraces types delta fieldCount context telescope signatures →
      RawFieldTraces types delta 0 fieldCount context telescope signatures
  | parameter {parameterCount fieldCount : Nat} {context : List KExpr} {dom body : KExpr}
      {metadata : BinderMeta} {signatures : List KLevel} :
      RawFieldTraces types delta parameterCount fieldCount (dom :: context) body signatures →
      RawFieldTraces types delta (parameterCount + 1) fieldCount context
        (.forallE dom body metadata) signatures

/-- The domain traces compute `domainSignatures` on the erased telescope. -/
theorem RawDomainTraces.domainSignatures_erased
    {types delta : KKey → List KLevel → KExpr → Prop} {look : Lookup .anon}
    (typeAnswers : ∀ key parameters type, types key parameters type →
      look.typeOf key parameters = some type.eraseMeta)
    (deltaAnswers : ∀ key parameters value, delta key parameters value →
      look.valueOf key parameters = some value.eraseMeta)
    {count : Nat} {context : List KExpr} {telescope : KExpr} {signatures : List KLevel}
    (trace : RawDomainTraces types delta count context telescope signatures) :
    ∃ fuel, domainSignatures look fuel count (context.map Expr.eraseMeta)
      telescope.eraseMeta = some signatures := by
  induction trace with
  | done context rest => exact ⟨0, rfl⟩
  | @step count context dom body metadata signature signatures first rest ih =>
    obtain ⟨fuel₁, classified⟩ := first.sortSignature_erased typeAnswers deltaAnswers
    obtain ⟨fuel₂, walked⟩ := ih
    have walked' : domainSignatures look fuel₂ count
        (dom.eraseMeta :: context.map Expr.eraseMeta) body.eraseMeta = some signatures := walked
    refine ⟨max fuel₁ fuel₂, ?_⟩
    show domainSignatures look (max fuel₁ fuel₂) (count + 1) (context.map Expr.eraseMeta)
      (.forallE dom.eraseMeta body.eraseMeta default) = some (signature :: signatures)
    exact domainSignatures_cons
      (sortSignature_le look (Nat.le_max_left fuel₁ fuel₂) classified)
      (domainSignatures_keeps
        (fun _ _ _ h => sortSignature_le look (Nat.le_max_right fuel₁ fuel₂) h) _ _ _ _ walked')

/-- **The field traces compute `fieldSignatures`** on the erased telescope, in the erased
context, over any lookup whose answers are the traces' with metadata erased. -/
theorem RawFieldTraces.fieldSignatures_erased
    {types delta : KKey → List KLevel → KExpr → Prop} {look : Lookup .anon}
    (typeAnswers : ∀ key parameters type, types key parameters type →
      look.typeOf key parameters = some type.eraseMeta)
    (deltaAnswers : ∀ key parameters value, delta key parameters value →
      look.valueOf key parameters = some value.eraseMeta)
    {parameterCount fieldCount : Nat} {context : List KExpr} {telescope : KExpr}
    {signatures : List KLevel}
    (trace : RawFieldTraces types delta parameterCount fieldCount context telescope signatures) :
    ∃ fuel, fieldSignatures look fuel parameterCount fieldCount
      (context.map Expr.eraseMeta) telescope.eraseMeta = some signatures := by
  induction trace with
  | @fields fieldCount context telescope signatures domains =>
    obtain ⟨fuel, walked⟩ := domains.domainSignatures_erased typeAnswers deltaAnswers
    exact ⟨fuel, walked⟩
  | @parameter parameterCount fieldCount context dom body metadata signatures rest ih =>
    obtain ⟨fuel, walked⟩ := ih
    refine ⟨fuel, ?_⟩
    show fieldSignatures look fuel parameterCount fieldCount
      (dom.eraseMeta :: context.map Expr.eraseMeta) body.eraseMeta = some signatures
    exact walked

/-- The walk yields one signature per field. -/
theorem RawFieldTraces.length {types delta : KKey → List KLevel → KExpr → Prop}
    {parameterCount fieldCount : Nat} {context : List KExpr} {telescope : KExpr}
    {signatures : List KLevel}
    (trace : RawFieldTraces types delta parameterCount fieldCount context telescope signatures) :
    signatures.length = fieldCount := by
  induction trace with
  | @fields fieldCount context telescope signatures domains =>
    induction domains with
    | done context rest => rfl
    | step first rest ih => simp [ih]
  | parameter rest ih => exact ih

end IxVM.Refinement.Decl
