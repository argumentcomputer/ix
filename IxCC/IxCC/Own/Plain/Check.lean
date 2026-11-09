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

/-- Contract-aware function domain: all parameter representations are `.tobj`.
Admits all frontend `BinderContract` (`0`, `1`, `&`, `*`, `!`, `~`, `let borrow`)
and `ValueContract` annotations without rejecting non-`.many` contracts. -/
def contractFunDomain (f : Fir.Fun) : Bool :=
  f.params.all (fun p => decide (p.2 = .tobj))

theorem funDomain_implies_contractFunDomain {f : Fir.Fun} (h : funDomain f = true) :
    contractFunDomain f = true := by
  simp only [funDomain, Bool.and_eq_true, and_assoc] at h
  exact h.2.1

def contractProgramDomain (P : Fir.Program) : Bool :=
  (List.range P.size).all fun f =>
    match P.fun? f with
    | none => false
    | some fd => contractFunDomain fd && fresh [] (fd.params.map (·.1)) &&
        scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body

theorem programDomain_implies_contractProgramDomain {P : Fir.Program} (h : programDomain P = true) :
    contractProgramDomain P = true := by
  unfold programDomain at h
  unfold contractProgramDomain
  rw [List.all_eq_true] at h ⊢
  intro f hf
  have he := h f hf
  cases hp : P.fun? f with
  | none => simp [hp] at he
  | some fd =>
    simp only [hp, Bool.and_eq_true, and_assoc] at he ⊢
    exact ⟨funDomain_implies_contractFunDomain he.1, he.2.1, he.2.2⟩

def checkContractPlainMap (F : Fir.Program) (candidate : Src.NatMap Code) : Bool :=
  contractProgramDomain F && checkBoolPins F && bodyMapEq (Program.canonical F).bodies candidate

theorem checkContractPlainMap_parts {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractPlainMap F candidate = true) :
    contractProgramDomain F = true ∧ checkBoolPins F = true ∧
      ({ source := F, bodies := candidate } : Program) = Program.canonical F := by
  have hs : contractProgramDomain F = true ∧ checkBoolPins F = true ∧
      (Program.canonical F).bodies = candidate := by
    simpa only [checkContractPlainMap, Bool.and_eq_true, bodyMapEq_iff, and_assoc] using checked
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [← hs.2.2]
  rfl

/-- Ownership / RC compilation policy: `.zeroRc` (no refcount actions needed)
vs `.plainRc` (canonical reference-counted lowering). -/
inductive RcPolicy where
  | zeroRc
  | plainRc
  deriving DecidableEq, Repr, Inhabited

/-- A binder contract permits zero-RC code when its usage is not unrestricted
`.many` (`0` `.erased`, `1` `.linear`, `&` `.affine`), or when its value
contract is `.local` (`~`) or `.unique` (`!`). -/
def zeroRcBinder (c : Ixon.V3.BinderContract) : Bool :=
  decide (c.uses != .many) || decide (c.value.locality = .local) || decide (c.value.owned = .unique)

/-- A binder contract carries an explicit runtime ownership/usage/locality
annotation (`1` `.linear`, `&` `.affine`, `~` `.local`, or `!` `.unique`),
excluding ghost type/proof erasure (`0` `.erased`). -/
def activeZeroRcBinder (c : Ixon.V3.BinderContract) : Bool :=
  decide (c.uses = .linear) || decide (c.uses = .affine) ||
    decide (c.value.locality = .local) || decide (c.value.owned = .unique)

/-- A let contract permits zero-RC code when it is a `let borrow`
(`.borrowShared`) or its binder contract satisfies `zeroRcBinder`. -/
def zeroRcLet (lc : Ixon.V3.LetContract) : Bool :=
  decide (lc.kind = .borrowShared) || zeroRcBinder lc.binder

def activeZeroRcLet (lc : Ixon.V3.LetContract) : Bool :=
  decide (lc.kind = .borrowShared) || activeZeroRcBinder lc.binder

/-- Whether constructor key `c` is one of the pinned scalar constructors
(`Nat.zero`, `Nat.succ`, `Bool.false`, `Bool.true`). -/
def isScalarCtorKey (known : Lam.Known) (c : Key.CtorKey) : Bool :=
  decide (known.natZero = some c) || decide (known.natSucc = some c) ||
    decide (known.boolFalse = some c) || decide (known.boolTrue = some c)

/-- Whether an `Rhs` allocates a non-fieldless heap cell or projects a non-`Nat`
constructor field. Fieldless constructors (`c.fieldless`) and `Nat.succ`
peeling are scalar immediates and do not touch the heap. -/
def rhsAllocsOrProjs (known : Lam.Known) : Rhs → Bool
  | .ctor c _ => !c.fieldless
  | .proj _ c _ => decide (known.natSucc != some c)
  | _ => false

mutual
def codeAllocsOrProjs (known : Lam.Known) : Fir.Code → Bool
  | .bind _ r k => rhsAllocsOrProjs known r || codeAllocsOrProjs known k
  | .jp _ _ _ body k => codeAllocsOrProjs known body || codeAllocsOrProjs known k
  | .case _ alts dflt => altsAllocsOrProjs known alts || optAllocsOrProjs known dflt
  | .jmp .. | .ret _ | .tcall .. | .trap => false

def altsAllocsOrProjs (known : Lam.Known) : List Fir.Alt → Bool
  | [] => false
  | .mk _ body :: alts => codeAllocsOrProjs known body || altsAllocsOrProjs known alts

def optAllocsOrProjs (known : Lam.Known) : Option Fir.Code → Bool
  | none => false
  | some c => codeAllocsOrProjs known c
end

mutual
def codeJoinParams : Fir.Code → List (JoinId × List Var)
  | .bind _ _ k => codeJoinParams k
  | .jp j ps _ body k => (j, ps) :: (codeJoinParams body ++ codeJoinParams k)
  | .case _ alts dflt => altsJoinParams alts ++ optJoinParams dflt
  | .jmp .. | .ret _ | .tcall .. | .trap => []

def altsJoinParams : List Fir.Alt → List (JoinId × List Var)
  | [] => []
  | .mk _ body :: alts => codeJoinParams body ++ altsJoinParams alts

def optJoinParams : Option Fir.Code → List (JoinId × List Var)
  | none => []
  | some c => codeJoinParams c
end

mutual
def codeAliasEdges (jps : List (JoinId × List Var)) : Fir.Code → List (Var × Var)
  | .bind y (.arg (.var x)) k => (x, y) :: codeAliasEdges jps k
  | .bind _ _ k => codeAliasEdges jps k
  | .jp _ _ _ body k => codeAliasEdges jps body ++ codeAliasEdges jps k
  | .jmp j args =>
    let ps := (jps.lookup j).getD []
    (args.zip ps).filterMap fun (a, p) =>
      match a with
      | .var x => some (x, p)
      | _ => none
  | .case _ alts dflt => altsAliasEdges jps alts ++ optAliasEdges jps dflt
  | .ret _ | .tcall .. | .trap => []

def altsAliasEdges (jps : List (JoinId × List Var)) : List Fir.Alt → List (Var × Var)
  | [] => []
  | .mk _ body :: alts => codeAliasEdges jps body ++ altsAliasEdges jps alts

def optAliasEdges (jps : List (JoinId × List Var)) : Option Fir.Code → List (Var × Var)
  | none => []
  | some c => codeAliasEdges jps c
end

def expandAliases : Nat → List (Var × Var) → List Var → List Var
  | 0, _, acc => acc
  | fuel + 1, edges, acc =>
    if !edges.any (fun (u, v) => acc.contains u && !acc.contains v) then acc
    else
      let next := edges.foldl (fun s (u, v) =>
        if s.contains u && !s.contains v then v :: s else s) acc
      if next.length == acc.length then acc
      else expandAliases fuel edges next

def paramAliasesFromEdges (edges : List (Var × Var)) (x : Var) : List Var :=
  expandAliases edges.length edges [x]

/-- Variable `x` together with any local `.arg` or join-point parameter aliases
reachable from `x` in `body`. -/
def paramAliases (x : Var) (body : Fir.Code) : List Var :=
  let jps := codeJoinParams body
  let edges := codeAliasEdges jps body
  paramAliasesFromEdges edges x

def rhsProjsHeap (known : Lam.Known) (vars : List Var) : Rhs → Bool
  | .proj x c _ => vars.contains x && decide (known.natSucc != some c)
  | _ => false

mutual
def varsProjOrCaseHeap (known : Lam.Known) (vars : List Var) : Fir.Code → Bool
  | .bind _ r k => rhsProjsHeap known vars r || varsProjOrCaseHeap known vars k
  | .jp _ _ _ body k => varsProjOrCaseHeap known vars body || varsProjOrCaseHeap known vars k
  | .case x alts dflt =>
    (vars.contains x && alts.any (fun (.mk c _) => !isScalarCtorKey known c)) ||
      altsProjOrCaseHeap known vars alts || optProjOrCaseHeap known vars dflt
  | .jmp .. | .ret _ | .tcall .. | .trap => false

def altsProjOrCaseHeap (known : Lam.Known) (vars : List Var) : List Fir.Alt → Bool
  | [] => false
  | .mk _ body :: alts => varsProjOrCaseHeap known vars body || altsProjOrCaseHeap known vars alts

def optProjOrCaseHeap (known : Lam.Known) (vars : List Var) : Option Fir.Code → Bool
  | none => false
  | some c => varsProjOrCaseHeap known vars c
end

def argInVars (vars : List Var) : Arg → Bool
  | .var x => vars.contains x
  | _ => false

def rhsUsesAsScalar (known : Lam.Known) (vars : List Var) : Rhs → Bool
  | .prim _ args => args.any (argInVars vars)
  | .proj x c _ => vars.contains x && decide (known.natSucc = some c)
  | _ => false

mutual
def varsUsedAsScalar (known : Lam.Known) (vars : List Var) : Fir.Code → Bool
  | .bind _ r k => rhsUsesAsScalar known vars r || varsUsedAsScalar known vars k
  | .jp _ _ _ body k => varsUsedAsScalar known vars body || varsUsedAsScalar known vars k
  | .case x alts dflt =>
    (vars.contains x && !alts.isEmpty && alts.all (fun (.mk c _) => isScalarCtorKey known c)) ||
      altsUsedAsScalar known vars alts || optUsedAsScalar known vars dflt
  | .jmp .. | .ret _ | .tcall .. | .trap => false

def altsUsedAsScalar (known : Lam.Known) (vars : List Var) : List Fir.Alt → Bool
  | [] => false
  | .mk _ body :: alts => varsUsedAsScalar known vars body || altsUsedAsScalar known vars alts

def optUsedAsScalar (known : Lam.Known) (vars : List Var) : Option Fir.Code → Bool
  | none => false
  | some c => varsUsedAsScalar known vars c
end

def argUses (x : Var) : Arg → Nat
  | .var y => if y == x then 1 else 0
  | _ => 0

def argsUses (x : Var) (args : List Arg) : Nat :=
  args.foldl (fun n a => n + argUses x a) 0

def rhsUses (x : Var) : Rhs → Nat
  | .arg a => argUses x a
  | .ctor _ args | .prim _ args | .call _ args => argsUses x args
  | .proj y _ _ => if y == x then 1 else 0

mutual
def varUsesInCode (x : Var) : Fir.Code → Nat
  | .bind _ r k => rhsUses x r + varUsesInCode x k
  | .jp _ ps rec body k =>
    let bodyUses := if rec && !ps.contains x then 2 * varUsesInCode x body else varUsesInCode x body
    bodyUses + varUsesInCode x k
  | .jmp _ args => argsUses x args
  | .case y alts dflt =>
    (if y == x then 1 else 0) + max (altsMaxUses x alts) (optUses x dflt)
  | .ret a => argUses x a
  | .tcall _ args => argsUses x args
  | .trap => 0

def altsMaxUses (x : Var) : List Fir.Alt → Nat
  | [] => 0
  | .mk _ body :: alts => max (varUsesInCode x body) (altsMaxUses x alts)

def optUses (x : Var) : Option Fir.Code → Nat
  | none => 0
  | some c => varUsesInCode x c
end

def varsAffineInCode (vars : List Var) (body : Fir.Code) : Bool :=
  vars.all fun v => decide (varUsesInCode v body ≤ 1)

def rhsValueUses (x : Var) : Rhs → Nat
  | .arg a => argUses x a
  | .ctor _ args | .prim _ args | .call _ args => argsUses x args
  | .proj _ _ _ => 0

mutual
def varValueUsesInCode (x : Var) : Fir.Code → Nat
  | .bind _ r k => rhsValueUses x r + varValueUsesInCode x k
  | .jp _ ps rec body k =>
    let bodyUses := if rec && !ps.contains x then 2 * varValueUsesInCode x body else varValueUsesInCode x body
    bodyUses + varValueUsesInCode x k
  | .jmp _ args => argsUses x args
  | .case _ alts dflt => max (altsMaxValueUses x alts) (optValueUses x dflt)
  | .ret a => argUses x a
  | .tcall _ args => argsUses x args
  | .trap => 0

def altsMaxValueUses (x : Var) : List Fir.Alt → Nat
  | [] => 0
  | .mk _ body :: alts => max (varValueUsesInCode x body) (altsMaxValueUses x alts)

def optValueUses (x : Var) : Option Fir.Code → Nat
  | none => 0
  | some c => varValueUsesInCode x c
end

def rhsProjField (x : Var) : Rhs → Option (Key.CtorKey × Nat)
  | .proj y c i => if y == x then some (c, i) else none
  | _ => none

mutual
def rhsProjsInCode (x : Var) : Fir.Code → Bool
  | .bind _ (.proj y _ _) k => (y == x) || rhsProjsInCode x k
  | .bind _ _ k => rhsProjsInCode x k
  | .jp _ _ _ body k => rhsProjsInCode x body || rhsProjsInCode x k
  | .case _ alts dflt => altsProjsInCode x alts || optProjsInCode x dflt
  | .jmp .. | .ret _ | .tcall .. | .trap => false

def altsProjsInCode (x : Var) : List Fir.Alt → Bool
  | [] => false
  | .mk _ body :: alts => rhsProjsInCode x body || altsProjsInCode x alts

def optProjsInCode (x : Var) : Option Fir.Code → Bool
  | none => false
  | some c => rhsProjsInCode x c
end

mutual
def varProjFieldsAffine (x : Var) (seen : List (Key.CtorKey × Nat)) : Fir.Code → Bool
  | .bind _ r k =>
    match rhsProjField x r with
    | some ci => !seen.contains ci && varProjFieldsAffine x (ci :: seen) k
    | none => varProjFieldsAffine x seen k
  | .jp _ ps rec body k =>
    (if rec && !ps.contains x then !rhsProjsInCode x body
     else varProjFieldsAffine x seen body) &&
      varProjFieldsAffine x seen k
  | .case _ alts dflt =>
    altsProjFieldsAffine x seen alts && optProjFieldsAffine x seen dflt
  | .jmp .. | .ret _ | .tcall .. | .trap => true

def altsProjFieldsAffine (x : Var) (seen : List (Key.CtorKey × Nat)) : List Fir.Alt → Bool
  | [] => true
  | .mk _ body :: alts =>
    varProjFieldsAffine x seen body && altsProjFieldsAffine x seen alts

def optProjFieldsAffine (x : Var) (seen : List (Key.CtorKey × Nat)) : Option Fir.Code → Bool
  | none => true
  | some c => varProjFieldsAffine x seen c
end

/-- Whether parameter `x` (and any local/join aliases of `x`) is safe under
`.zeroRc` in a contract-annotated function `body`: either `c` is an explicit
`zeroRcBinder`, or `x` never projects/cases on a heap constructor and is either
positively used as a scalar (`Nat`/`Bool`) or used affinely (at most once along
every execution path). -/
def zeroRcParam (known : Lam.Known) (body : Fir.Code) (x : Var)
    (c : Ixon.V3.BinderContract) : Bool :=
  zeroRcBinder c ||
    let vars := paramAliases x body
    !varsProjOrCaseHeap known vars body &&
      (varsUsedAsScalar known vars body || varsAffineInCode vars body)

def varDeconstructOrValueAffineWithEdges (known : Lam.Known) (edges : List (Var × Var))
    (x : Var) (body : Fir.Code) : Bool :=
  let vars := paramAliasesFromEdges edges x
  (!varsProjOrCaseHeap known vars body &&
    (varsUsedAsScalar known vars body || varsAffineInCode vars body)) ||
    vars.all fun v =>
      varProjFieldsAffine v [] body &&
        if rhsProjsInCode v body then decide (varValueUsesInCode v body = 0)
        else decide (varValueUsesInCode v body ≤ 1)

/-- Whether variable `x` in a synthesized helper is scalar, used affinely as a
value (`≤ 1` per path), or deconstructed affinely in a pattern match without
retaining `x` as a whole value. -/
def varDeconstructOrValueAffine (known : Lam.Known) (x : Var) (body : Fir.Code) : Bool :=
  let jps := codeJoinParams body
  let edges := codeAliasEdges jps body
  varDeconstructOrValueAffineWithEdges known edges x body

mutual
def codeBindsAffineWithEdges (known : Lam.Known) (jps : List (JoinId × List Var))
    (edges : List (Var × Var)) : Fir.Code → Bool
  | .bind x r k =>
    let kEdges := match r with
      | .arg (.var _) => edges.drop 1
      | _ => edges
    varDeconstructOrValueAffineWithEdges known kEdges x k &&
      codeBindsAffineWithEdges known jps kEdges k
  | .jp _ ps _ body k =>
    let bodyEdges := codeAliasEdges jps body
    let kEdges := codeAliasEdges jps k
    ps.all (fun p => varDeconstructOrValueAffineWithEdges known bodyEdges p body) &&
      codeBindsAffineWithEdges known jps bodyEdges body &&
      codeBindsAffineWithEdges known jps kEdges k
  | .case _ alts dflt =>
    altsBindsAffineWithEdges known jps alts && optBindsAffineWithEdges known jps dflt
  | .jmp .. | .ret _ | .tcall .. | .trap => true

def altsBindsAffineWithEdges (known : Lam.Known) (jps : List (JoinId × List Var)) :
    List Fir.Alt → Bool
  | [] => true
  | .mk _ body :: alts =>
    let bodyEdges := codeAliasEdges jps body
    codeBindsAffineWithEdges known jps bodyEdges body &&
      altsBindsAffineWithEdges known jps alts

def optBindsAffineWithEdges (known : Lam.Known) (jps : List (JoinId × List Var)) :
    Option Fir.Code → Bool
  | none => true
  | some c =>
    let cEdges := codeAliasEdges jps c
    codeBindsAffineWithEdges known jps cEdges c
end

def codeBindsAffine (known : Lam.Known) (body : Fir.Code) : Bool :=
  let jps := codeJoinParams body
  let edges := codeAliasEdges jps body
  codeBindsAffineWithEdges known jps edges body

/-- Whether `key` is a compiler-synthesized helper key (`.spec`, `.worker`,
`.lam`, `.dispatch`, `.recStar`, `.wrapper`) rather than a user-written source
definition (`.const`, `.byName`). -/
def isSynthesizedKey : Key.GKey → Bool
  | .spec .. | .worker .. | .lam .. | .dispatch .. | .recStar .. | .wrapper .. => true
  | .const .. | .byName .. => false

def funHasActiveZeroRcContract (f : Fir.Fun) : Bool :=
  f.contracts.any activeZeroRcBinder || f.letContracts.any (fun p => activeZeroRcLet p.2)

/-- A function qualifies for `.zeroRc` when either:
1. It is purely scalar (`!codeAllocsOrProjs known f.body`),
2. Every parameter and let binder carries a zero-RC contract (`zeroRcBinder` /
   `zeroRcLet`), or
3. It carries at least one explicit runtime zero-RC contract (`1`, `&`, `~`,
   `!`, `let borrow`) and every remaining unannotated parameter is scalar or
   used affinely without heap projection. -/
def zeroRcFun (known : Lam.Known) (f : Fir.Fun) : Bool :=
  !codeAllocsOrProjs known f.body ||
    (f.letContracts.all (fun p => zeroRcLet p.2) &&
      (((!f.params.isEmpty || !f.letContracts.isEmpty) &&
          decide (f.contracts.length = f.params.length) &&
          f.contracts.all zeroRcBinder) ||
        (funHasActiveZeroRcContract f &&
          (f.params.zipIdx).all fun ((x, _), i) =>
            zeroRcParam known f.body x (f.contracts.getD i {}))))

/-- A compiler-synthesized helper function qualifies for `.zeroRc` inside an
annotated program when either `zeroRcFun` holds or all of its parameters and
local bindings are scalar or used affinely. -/
def zeroRcSynthesizedFun (known : Lam.Known) (f : Fir.Fun) : Bool :=
  zeroRcFun known f ||
    (isSynthesizedKey f.key &&
      f.letContracts.all (fun p => zeroRcLet p.2) &&
      (f.params.zipIdx).all (fun ((x, _), i) =>
        let c := f.contracts.getD i {}
        zeroRcBinder c || varDeconstructOrValueAffine known x f.body) &&
      codeBindsAffine known f.body)

def programHasZeroRcContracts (P : Fir.Program) : Bool :=
  (List.range P.size).any fun f =>
    match P.fun? f with
    | none => false
    | some fd =>
      funHasActiveZeroRcContract fd ||
        ((!fd.params.isEmpty || !fd.letContracts.isEmpty) &&
          decide (fd.contracts.length = fd.params.length) &&
          fd.contracts.all zeroRcBinder &&
          fd.letContracts.all (fun p => zeroRcLet p.2))

def zeroRcProgram (P : Fir.Program) : Bool :=
  let hasContracts := programHasZeroRcContracts P
  (List.range P.size).all fun f =>
    match P.fun? f with
    | none => false
    | some fd =>
      zeroRcFun P.known fd || (hasContracts && zeroRcSynthesizedFun P.known fd)

/-- Predictably select `.zeroRc` when the program is scalar or its frontend
usage/ownership/locality annotations discharge all heap bindings, and fall back
to `.plainRc` otherwise. -/
def selectRcPolicy (P : Fir.Program) : RcPolicy :=
  if zeroRcProgram P then .zeroRc else .plainRc

end IxCC.Own.Plain
