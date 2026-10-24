import Ix.CompileCert.O6Annotation

/-! # Certified beta spines from original full inference

The actual full application run supplies the original head inference and
every argument's real type/domain check. The inferred forall telescope has
the same domains as the checked lambda prefix, proved through the actual
typed openings and bounded re-abstraction. Each beta step uses its original
argument certificate, including Prop; no intermediate reduct is assumed
to have an inference run. The endpoint is one top-level checked reduction,
with the untouched extra arguments. O6 values remain a separate consumer.
-/

namespace Ix.Cert.CheckedBetaSpine

open Ix.Kernel
open Ix.Kernel.Model.Rules (Frame)
open Ix.CompileCert

variable {md : Mode} {env : Ix.Kernel.Env md}

theorem domains_abstract {n : Nat} {e t : Ix.Kernel.Expr md}
    (same : Ix.Kernel.Expr.LamPiDomsEq n e t) (d k : Nat) :
    Ix.Kernel.Expr.LamPiDomsEq n (e.abstract1 d k) (t.abstract1 d k) := by
  induction n generalizing e t k with
  | zero => trivial
  | succ n ih =>
    match e, t, same with
    | .lam dom body mb, .forallE dom' cod mt, same =>
      exact ⟨by rw [same.1], ih same.2 (k + 1)⟩

/-- Every domain in the lambda prefix is the actual inferred forall's
domain. The input frame discharges fresh/bounded open-then-close; the
recursive inference is of the real typed-opened body in the same env. -/
theorem inferred_lam_domains {n F d : Nat} {head type : Ix.Kernel.Expr md}
    (stripped : (head.stripLams n).isSome = true) (frame : Frame d head)
    (run : inferTypeCore .verified env F d head = .ok type) :
    Ix.Kernel.Expr.LamPiDomsEq n head type := by
  induction n generalizing F d head type with
  | zero => trivial
  | succ n ih =>
    cases head with
    | lam dom body mb =>
      have rest : (body.stripLams n).isSome = true := by
        simpa only [Ix.Kernel.Expr.stripLams, Option.isSome_map] using stripped
      cases F with
      | zero => rw [inferTypeCore_zero] at run; exact nomatch run
      | succ F =>
        obtain ⟨_, _, bt, _, _, bodyRun, _, _, rfl⟩ := inferTypeCore_lam_inv run
        refine ⟨rfl, ?_⟩
        have opened := Ix.Kernel.Expr.stripLams_instantiate1_isSome
          (v := .fvar d dom) n 0 rest
        have same := ih opened (frame.lam_open frame.lam_ty) bodyRun
        have closed := domains_abstract same d 0
        have scopeFacts := frame.1
        have bounded := frame.2.1
        simp only [Ix.Kernel.Expr.WScoped] at scopeFacts
        simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
        simpa only [O6Annotation.open_close body d 0 dom scopeFacts.2.fvarsBelow bounded.2] using closed
    | _ => cases stripped

/-- A trace of original full application inference. The indices are its
starting and resulting TYPES; each constructor retains the real recursive
fuel, WHNF, argument inference and domain check. This is a proposition about
existing checker runs, not an alternative inference algorithm. -/
inductive ApplicationTrace (env : Ix.Kernel.Env md) (d : Nat) :
    Ix.Kernel.Expr md → List (Ix.Kernel.Expr md) → Ix.Kernel.Expr md → Prop
  | nil (type) : ApplicationTrace env d type [] type
  | step {type dom cod arg argType result : Ix.Kernel.Expr md}
      {mb : BinderMeta} {fuel : Nat} {rest : List (Ix.Kernel.Expr md)}
      (headWhnf : whnf .verified env fuel d type = .ok (.forallE dom cod mb))
      (argRun : inferTypeCore .verified env fuel d arg = .ok argType)
      (domainRun : isDefEqCore .verified env fuel d argType dom = .ok true)
      (tail : ApplicationTrace env d (cod.instantiate1 arg) rest result) :
      ApplicationTrace env d type (arg :: rest) result

/-- Invert the actual application tree; the types and fuels of successive
prefixes are those of its real recursive calls, so no reduct inference or
caller-supplied telescope/certificate correspondence is used. -/
theorem infer_apps {F d : Nat} (args : List (Ix.Kernel.Expr md))
    {head result : Ix.Kernel.Expr md}
    (run : inferTypeCore .verified env F d (head.mkAppN args) = .ok result) :
    ∃ headFuel headType, inferTypeCore .verified env headFuel d head = .ok headType ∧
      ApplicationTrace env d headType args result := by
  induction args generalizing head with
  | nil => exact ⟨F, result, run, .nil _⟩
  | cons arg args ih =>
    obtain ⟨headFuel, appType, appRun, rest⟩ := ih run
    cases headFuel with
    | zero => rw [inferTypeCore_zero] at appRun; exact nomatch appRun
    | succ fuel =>
      obtain ⟨headType, dom, cod, mb, headRun, headWhnf, rfl, argType, argRun, domainRun⟩ :=
        inferTypeCore_app_inv appRun
      exact ⟨fuel, headType, headRun, .step headWhnf argRun domainRun rest⟩

theorem frame_head {d : Nat} (args : List (Ix.Kernel.Expr md)) {head : Ix.Kernel.Expr md}
    (frame : Frame d (head.mkAppN args)) : Frame d head := by
  induction args generalizing head with
  | nil => exact frame
  | cons arg args ih => exact (ih frame).app_fn

/-- Consume exactly the lambda prefix using the ORIGINAL inference trace.
Domain equality follows through each identical substitution; real full
argument inference gives the real IO certificate, with no marker gate.
The trace is an internal leaf, derived by infer_apps in the public theorem. -/
theorem trace_beta {n : Nat} {head tail type result : Ix.Kernel.Expr md}
    {args : List (Ix.Kernel.Expr md)} {binders : List (Ix.Kernel.Expr md × BinderMeta)}
    (strip : head.stripLams n = some (binders, tail))
    (same : Ix.Kernel.Expr.LamPiDomsEq n head type) (fit : n ≤ args.length)
    (trace : ApplicationTrace env 0 type args result) :
    Ix.Kernel.Rules.Red env 0 (head.mkAppN args)
      ((tail.instantiateList (args.take n).reverse).mkAppN (args.drop n)) := by
  induction n generalizing head tail type args binders with
  | zero =>
    have eq : head = tail := (Prod.mk.inj (Option.some.inj strip)).2
    simp only [List.take_zero, List.reverse_nil, Ix.Kernel.Expr.instantiateList_nil,
      List.drop_zero, eq]
    exact .refl
  | succ n ih =>
    cases head with
    | lam dom body mb =>
      cases type with
      | forallE dom' cod mt =>
        obtain ⟨rfl, domainTail⟩ := same
        cases restStrip : body.stripLams n with
        | none => simp only [Ix.Kernel.Expr.stripLams, restStrip, Option.map_none] at strip; cases strip
        | some pair =>
          simp only [Ix.Kernel.Expr.stripLams, restStrip, Option.map_some] at strip
          have tailEq : pair.2 = tail := (Prod.mk.inj (Option.some.inj strip)).2
          have bodyStrip : body.stripLams n = some (pair.1, tail) := tailEq ▸ restStrip
          cases args with
          | nil => simp at fit
          | cons arg args =>
            have enough : n ≤ args.length := Nat.le_of_succ_le_succ fit
            cases trace with
            | step headWhnf argRun domainRun traceRest =>
              obtain ⟨rfl, rfl, rfl⟩ := Ix.Kernel.Expr.forallE.inj (whnf_forallE_eq headWhnf)
              have step := Ix.Kernel.Rules.Red.beta (body := body) (mb := mb)
                (Ix.Kernel.Rules.inferTypeCoreIO_bridge (inferTypeCoreIO_of_full argRun))
                (Ix.Kernel.Rules.isDefEqCore_bridge domainRun)
              obtain ⟨nextBinders, nextStrip⟩ := O6Annotation.strip_open (v := arg) bodyStrip 0
              simp only [Nat.zero_add] at nextStrip
              have nextDomains := Ix.Kernel.Expr.LamPiDomsEq.instantiate1 (v := arg) n 0 domainTail
              have next := ih nextStrip nextDomains enough traceRest
              have bulk : tail.instantiateList ((arg :: args).take (n + 1)).reverse =
                  (tail.instantiate1 arg n).instantiateList (args.take n).reverse := by
                rw [List.take_succ_cons, List.reverse_cons, Ix.Kernel.Expr.instantiateList_append_one]
                simp only [List.length_reverse, List.length_take, Nat.min_eq_left enough, Nat.zero_add]
              rw [bulk, List.drop_succ_cons]
              exact .trans (O6RecRead.red_spine step args) next
      | _ => cases same
    | _ => cases strip

/-- Full inference of this checked application supplies EVERY beta
certificate, including Prop. Frame and lambda shape are ordinary syntactic
inputs, discharged by the actual annotation in the O6 consumer. The only
inference premise is for the original subject; the intermediate reducts
are related by derived Red, never presumed to have executable inference.

The result consumes n lambdas, makes the exact bulk substitution and keeps
all extra arguments. It introduces no value-model or conversion premise. -/
theorem checked_lambda_spine_red {n F : Nat} {head tail type : Ix.Kernel.Expr md}
    {args : List (Ix.Kernel.Expr md)} {binders : List (Ix.Kernel.Expr md × BinderMeta)}
    (strip : head.stripLams n = some (binders, tail)) (fit : n ≤ args.length)
    (frame : Frame 0 (head.mkAppN args))
    (run : inferTypeCore .verified env F 0 (head.mkAppN args) = .ok type) :
    Ix.Kernel.Rules.Red env 0 (head.mkAppN args)
      ((tail.instantiateList (args.take n).reverse).mkAppN (args.drop n)) := by
  obtain ⟨_, _, headRun, trace⟩ := infer_apps args run
  have same := inferred_lam_domains (by rw [strip]; rfl) (frame_head args frame) headRun
  exact trace_beta strip same fit trace

end Ix.Cert.CheckedBetaSpine
