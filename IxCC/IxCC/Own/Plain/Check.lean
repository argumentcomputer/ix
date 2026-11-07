import IxCC.Own.Plain.Program

/-! Structural checking of the staged canonical plain-RC code. The check
binds the proposed code to a source body, validates lexical ownership scopes,
join/call arities and the restricted contract domain. This is not yet the
semantic refinement theorem; the actual compiler composition must derive the
remaining Fir well-formedness facts from successful Fir.lower. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Fir (Var JoinId FunId Arg Rhs)

mutual
def codeEq : Code → Code → Bool
  | .act a k, .act a' k' => decide (a = a') && codeEq k k'
  | .bind x r k, .bind x' r' k' => decide (x = x') && decide (r = r') && codeEq k k'
  | .jp j ps captured rec b k, .jp j' ps' captured' rec' b' k' =>
    decide (j = j') && decide (ps = ps') && decide (captured = captured') &&
      decide (rec = rec') && codeEq b b' && codeEq k k'
  | .jmp j args, .jmp j' args' => decide (j = j') && decide (args = args')
  | .case x alts dflt, .case x' alts' dflt' =>
    decide (x = x') && altsEq alts alts' && optEq dflt dflt'
  | .ret a, .ret a' => decide (a = a')
  | .tcall f args, .tcall f' args' => decide (f = f') && decide (args = args')
  | .trap, .trap => true
  | _, _ => false

def altsEq : List Alt → List Alt → Bool
  | [], [] => true
  | .mk key body :: alts, .mk key' body' :: alts' =>
    decide (key = key') && codeEq body body' && altsEq alts alts'
  | _, _ => false

def optEq : Option Code → Option Code → Bool
  | none, none => true
  | some c, some c' => codeEq c c'
  | _, _ => false
end

mutual
theorem codeEq_iff (c c' : Code) : codeEq c c' = true ↔ c = c' := by
  cases c <;> cases c' <;>
    simp [codeEq, codeEq_iff, altsEq_iff, optEq_iff, and_assoc]

theorem altsEq_iff (alts alts' : List Alt) : altsEq alts alts' = true ↔ alts = alts' := by
  cases alts with
  | nil => cases alts' <;> simp [altsEq]
  | cons a as =>
    cases alts' with
    | nil => simp [altsEq]
    | cons a' as' =>
      cases a; cases a'
      simp [altsEq, codeEq_iff, altsEq_iff, and_assoc]

theorem optEq_iff (d d' : Option Code) : optEq d d' = true ↔ d = d' := by
  cases d <;> cases d' <;> simp [optEq, codeEq_iff]
end

def argIn (live : List Var) : Arg → Bool
  | .var x => live.contains x
  | _ => true

def fresh (live : List Var) : List Var → Bool
  | [] => true
  | x :: xs => !live.contains x && fresh (live ++ [x]) xs

abbrev Signatures := List (FunId × Nat)
abbrev JoinArities := List (JoinId × Nat)

def rhsIn (functions : Signatures) (live : List Var) : Rhs → Bool
  | .arg a => argIn live a
  | .ctor c args => decide (args.length = c.arity) && args.all (argIn live) &&
      decide (c.nscalar = 0) && decide (c.fieldKinds.length = c.nobj) &&
      c.fieldKinds.all (fun k => decide (k = .shared))
  | .proj x _ _ => live.contains x
  | .prim p args => decide (args.length = p.arity) && args.all (argIn live)
  | .call f args => decide (functions.lookup f = some args.length) && args.all (argIn live)

mutual
def scopeOk (functions : Signatures) (live : List Var) (joins : JoinArities) : Fir.Code → Bool
  | .bind x r k => !live.contains x && rhsIn functions live r &&
      scopeOk functions (live ++ [x]) joins k
  | .jp j ps rec body k =>
    decide (joins.lookup j = none) && fresh live ps &&
      scopeOk functions (live ++ ps) (if rec then (j, ps.length) :: joins else joins) body &&
      scopeOk functions live ((j, ps.length) :: joins) k
  | .jmp j args => decide (joins.lookup j = some args.length) && args.all (argIn live)
  | .case x alts dflt => live.contains x && scopeAlts functions live joins alts &&
      scopeOpt functions live joins dflt
  | .ret a => argIn live a
  | .tcall f args => decide (functions.lookup f = some args.length) && args.all (argIn live)
  | .trap => true

def scopeAlts (functions : Signatures) (live : List Var) (joins : JoinArities) : List Fir.Alt → Bool
  | [] => true
  | .mk _ body :: alts => scopeOk functions live joins body && scopeAlts functions live joins alts

def scopeOpt (functions : Signatures) (live : List Var) (joins : JoinArities) : Option Fir.Code → Bool
  | none => true
  | some c => scopeOk functions live joins c
end

/-- A function entry starts with no join scope. Checking the whole body builds
join arities from its declarations, so lowerCode's unknown-label default is
never admitted by this entry. Captures are supplied only by the producer. -/
def checkBody (functions : Signatures) (params : List Var) (source : Fir.Code) (proposal : Code) : Bool :=
  fresh [] params && scopeOk functions params [] source && codeEq (lowerCode params [] source) proposal

theorem checkBody_iff (functions : Signatures) (params : List Var) (source : Fir.Code) (proposal : Code) :
    checkBody functions params source proposal = true ↔
      fresh [] params = true ∧ scopeOk functions params [] source = true ∧
      lowerCode params [] source = proposal := by
  simp [checkBody, codeEq_iff, and_assoc]

theorem checkBody_erases {functions : Signatures} {params : List Var} {source : Fir.Code} {proposal : Code}
    (h : checkBody functions params source proposal = true) : eraseCode proposal = source := by
  have he := ((checkBody_iff functions params source proposal).mp h).2.2
  rw [← he]
  exact erase_lowerCode ..

/-- Initial intentionally narrow written-contract domain. These are explicit
declines until the RC refinement has rules for the other contract kinds. -/
def funDomain (f : Fir.Fun) : Bool :=
  decide (f.result = Ixon.V3.ValueContract.shared) &&
    f.params.all (fun p => decide (p.2 = .tobj)) &&
    f.contracts.all (fun c => decide (c = Ixon.V3.BinderContract.many)) &&
    f.letContracts.all (fun p => decide (p.2.kind = .value) &&
      decide (p.2.binder = Ixon.V3.BinderContract.many))

def signatures (P : Fir.Program) : Signatures :=
  P.funList.map fun (f, fd) => (f, fd.arity)

/-- Check every numbered function, including unreachable entries. A caller
cannot admit an equal-arity callee outside the supported contract domain.
Missing numbered functions are rejected. This does not establish constructor
table agreement or projection bounds; those remain source-admission facts. -/
def programDomain (P : Fir.Program) : Bool :=
  (List.range P.size).all fun f =>
    match P.fun? f with
    | none => false
    | some fd => funDomain fd && fresh [] (fd.params.map (·.1)) &&
        scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body

/-- Bind a proposal to a function and call signatures in the actual Fir
program, including the explicit written-contract domain. Whole-program Fir
well-formedness remains derived from Fir.lower by the eventual composition. -/
def checkFunction (P : Fir.Program) (f : FunId) (proposal : Code) : Bool :=
  programDomain P && (if f < P.size then
    match P.fun? f with
    | none => false
    | some fd => funDomain fd && checkBody (signatures P) (fd.params.map (·.1)) fd.body proposal
  else false)

theorem checkFunction_domain {P : Fir.Program} {f : FunId} {proposal : Code}
    (h : checkFunction P f proposal = true) : programDomain P = true := by
  simp only [checkFunction, Bool.and_eq_true] at h
  exact h.1

theorem checkFunction_parts {P : Fir.Program} {f : FunId} {proposal : Code}
    (h : checkFunction P f proposal = true) :
    ∃ fd, f < P.size ∧ P.fun? f = some fd ∧ funDomain fd = true ∧
      checkBody (signatures P) (fd.params.map (·.1)) fd.body proposal = true := by
  simp only [checkFunction, Bool.and_eq_true] at h
  have h := h.2
  split at h
  · next hf =>
    cases hp : P.fun? f with
    | none => simp [hp] at h
    | some fd =>
      simp only [hp, Bool.and_eq_true] at h
      exact ⟨fd, hf, rfl, h.1, h.2⟩
  · cases h

/-- Complete proposal coverage: one candidate for each numbered function.
This is a syntactic acceptance check, not yet the heap refinement theorem. -/
def checkProgram (P : Fir.Program) (proposals : List Code) : Bool :=
  decide (proposals.length = P.size) &&
    ((List.range P.size).zip proposals).all (fun (f, proposal) => checkFunction P f proposal)

def BoolPinsOk (F : Fir.Program) : Prop :=
  ∀ (b : Bool) (key : Key.CtorKey) (info : Fir.CtorInfo),
    (if b then F.known.boolTrue else F.known.boolFalse) = some key →
      Fir.CtorInfo.ofKey F.ctors key = some info → info.arity = 0

def boolPinOk (F : Fir.Program) (b : Bool) : Bool :=
  match (if b then F.known.boolTrue else F.known.boolFalse) with
  | none => true
  | some key =>
    match Fir.CtorInfo.ofKey F.ctors key with
    | none => true
    | some info => decide (info.arity = 0)

def checkBoolPins (F : Fir.Program) : Bool := boolPinOk F false && boolPinOk F true

theorem boolPinOk_sound {F : Fir.Program} {b : Bool} (h : boolPinOk F b = true)
    {key : Key.CtorKey} {info : Fir.CtorInfo}
    (hk : (if b then F.known.boolTrue else F.known.boolFalse) = some key)
    (hi : Fir.CtorInfo.ofKey F.ctors key = some info) : info.arity = 0 := by
  simpa only [boolPinOk, hk, hi, decide_eq_true_eq] using h

theorem checkBoolPins_sound {F : Fir.Program} (h : checkBoolPins F = true) : BoolPinsOk F := by
  have hs : boolPinOk F false = true ∧ boolPinOk F true = true := by
    simpa only [checkBoolPins, Bool.and_eq_true] using h
  intro b key info hk hi
  cases b with
  | false => exact boolPinOk_sound hs.1 hk hi
  | true => exact boolPinOk_sound hs.2 hk hi

def checkPlainFunction (F : Fir.Program) (f : Fir.FunId) (proposal : Code) : Bool :=
  checkBoolPins F && checkFunction F f proposal

def bodyMapEq : Src.NatMap Code → Src.NatMap Code → Bool
  | .leaf, .leaf => true
  | .node v z o, .node v' z' o' => optEq v v' && bodyMapEq z z' && bodyMapEq o o'
  | _, _ => false

theorem bodyMapEq_iff (a b : Src.NatMap Code) : bodyMapEq a b = true ↔ a = b := by
  induction a generalizing b with
  | leaf => cases b <;> simp [bodyMapEq]
  | node v z o iz io =>
    cases b <;> simp [bodyMapEq, optEq_iff, iz, io, and_assoc]

def checkPlainMap (F : Fir.Program) (candidate : Src.NatMap Code) : Bool :=
  programDomain F && checkBoolPins F && bodyMapEq (Program.canonical F).bodies candidate

theorem checkPlainMap_parts {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true) :
    programDomain F = true ∧ checkBoolPins F = true ∧
      ({ source := F, bodies := candidate } : Program) = Program.canonical F := by
  have hs : programDomain F = true ∧ checkBoolPins F = true ∧
      (Program.canonical F).bodies = candidate := by
    simpa only [checkPlainMap, Bool.and_eq_true, bodyMapEq_iff, and_assoc] using checked
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [← hs.2.2]
  rfl

end IxCC.Own.Plain
