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
def collectJoinParams (acc : Src.NatMap (List Var)) : Fir.Code → Src.NatMap (List Var)
  | .bind _ _ k => collectJoinParams acc k
  | .jp j ps _ body k =>
    let acc := acc.insert j ps
    let acc := collectJoinParams acc body
    collectJoinParams acc k
  | .case _ alts dflt => collectOptJoinParams (collectAltsJoinParams acc alts) dflt
  | .jmp .. | .ret _ | .tcall .. | .trap => acc

def collectAltsJoinParams (acc : Src.NatMap (List Var)) : List Fir.Alt → Src.NatMap (List Var)
  | [] => acc
  | .mk _ body :: alts => collectAltsJoinParams (collectJoinParams acc body) alts

def collectOptJoinParams (acc : Src.NatMap (List Var)) : Option Fir.Code → Src.NatMap (List Var)
  | none => acc
  | some c => collectJoinParams acc c
end

def mergeProjs (xs ys : List (Key.CtorKey × Nat)) : List (Key.CtorKey × Nat) :=
  xs.foldl (fun acc ci => if acc.contains ci then acc else ci :: acc) ys

/-- Per-variable usage and projection summary over a `Fir.Code` subterm. -/
structure VarStats where
  projOrCaseHeap : Bool := false
  usedAsScalar : Bool := false
  uses : Nat := 0
  valueUses : Nat := 0
  projs : List (Key.CtorKey × Nat) := []
  projFieldsAffine : Bool := true
  deriving Inhabited

def VarStats.mergeBranch (st1 st2 : VarStats) : VarStats :=
  { projOrCaseHeap := st1.projOrCaseHeap || st2.projOrCaseHeap
    usedAsScalar := st1.usedAsScalar || st2.usedAsScalar
    uses := max st1.uses st2.uses
    valueUses := max st1.valueUses st2.valueUses
    projs := mergeProjs st1.projs st2.projs
    projFieldsAffine := st1.projFieldsAffine && st2.projFieldsAffine }

def VarStats.mergeSeq (st1 st2 : VarStats) : VarStats :=
  { projOrCaseHeap := st1.projOrCaseHeap || st2.projOrCaseHeap
    usedAsScalar := st1.usedAsScalar || st2.usedAsScalar
    uses := st1.uses + st2.uses
    valueUses := st1.valueUses + st2.valueUses
    projs := mergeProjs st1.projs st2.projs
    projFieldsAffine := st1.projFieldsAffine && st2.projFieldsAffine }

def VarStats.onRecBody (st : VarStats) : VarStats :=
  { st with
    uses := 2 * st.uses
    valueUses := 2 * st.valueUses
    projFieldsAffine := st.projs.isEmpty }

def mergeStatsMap (comb : VarStats → VarStats → VarStats) :
    Src.NatMap VarStats → Src.NatMap VarStats → Src.NatMap VarStats
  | .leaf, m2 => m2
  | m1, .leaf => m1
  | .node v1 z1 o1, .node v2 z2 o2 =>
    let v := match v1, v2 with
      | some a, some b => some (comb a b)
      | some a, none => some a
      | none, some b => some b
      | none, none => none
    .node v (mergeStatsMap comb z1 z2) (mergeStatsMap comb o1 o2)

def adjustRecBody : Src.NatSet → Src.NatMap VarStats → Src.NatMap VarStats
  | _, .leaf => .leaf
  | psSet, .node v z o =>
    let (pv, pz, po) := Src.NatMap.parts psSet
    let v' := match v with
      | some st => some (if pv.isSome then st else st.onRecBody)
      | none => none
    .node v' (adjustRecBody pz z) (adjustRecBody po o)

def mergeAdjMap : Src.NatMap (List Var) → Src.NatMap (List Var) → Src.NatMap (List Var)
  | .leaf, m2 => m2
  | m1, .leaf => m1
  | .node v1 z1 o1, .node v2 z2 o2 =>
    let v := match v1, v2 with
      | some a, some b => some (a ++ b)
      | some a, none => some a
      | none, some b => some b
      | none, none => none
    .node v (mergeAdjMap z1 z2) (mergeAdjMap o1 o2)

def addArgUse (a : Arg) (scalar : Bool) (m : Src.NatMap VarStats) : Src.NatMap VarStats :=
  match a with
  | .var x =>
    let st := m.getD x {}
    m.insert x
      { st with
        uses := st.uses + 1
        valueUses := st.valueUses + 1
        usedAsScalar := st.usedAsScalar || scalar }
  | _ => m

def addArgsUses (args : List Arg) (scalar : Bool) (m : Src.NatMap VarStats) : Src.NatMap VarStats :=
  args.foldl (fun acc a => addArgUse a scalar acc) m

def addRhsUses (known : Lam.Known) (r : Rhs) (m : Src.NatMap VarStats) : Src.NatMap VarStats :=
  match r with
  | .arg a => addArgUse a false m
  | .ctor _ args | .call _ args => addArgsUses args false m
  | .prim _ args => addArgsUses args true m
  | .proj y c i =>
    let st := m.getD y {}
    let isNatSucc := decide (known.natSucc = some c)
    let ci := (c, i)
    m.insert y
      { st with
        projOrCaseHeap := st.projOrCaseHeap || !isNatSucc
        usedAsScalar := st.usedAsScalar || isNatSucc
        uses := st.uses + 1
        projFieldsAffine := st.projFieldsAffine && !st.projs.contains ci
        projs := if st.projs.contains ci then st.projs else ci :: st.projs }

/-- Aggregated boolean summary across a variable's reachable alias closure. -/
structure AliasSummary where
  anyProjOrCaseHeap : Bool := false
  anyUsedAsScalar : Bool := false
  allAffine : Bool := true
  allDeconstructOrValueAffine : Bool := true
  deriving Inhabited

def VarStats.toAliasSummary (st : VarStats) : AliasSummary :=
  { anyProjOrCaseHeap := st.projOrCaseHeap
    anyUsedAsScalar := st.usedAsScalar
    allAffine := decide (st.uses ≤ 1)
    allDeconstructOrValueAffine :=
      st.projFieldsAffine &&
        if !st.projs.isEmpty then decide (st.valueUses = 0)
        else decide (st.valueUses ≤ 1) }

def AliasSummary.merge (a b : AliasSummary) : AliasSummary :=
  { anyProjOrCaseHeap := a.anyProjOrCaseHeap || b.anyProjOrCaseHeap
    anyUsedAsScalar := a.anyUsedAsScalar || b.anyUsedAsScalar
    allAffine := a.allAffine && b.allAffine
    allDeconstructOrValueAffine := a.allDeconstructOrValueAffine && b.allDeconstructOrValueAffine }

def AliasSummary.zeroRcParamOk (s : AliasSummary) : Bool :=
  !s.anyProjOrCaseHeap && (s.anyUsedAsScalar || s.allAffine)

def AliasSummary.deconstructOrValueAffineOk (s : AliasSummary) : Bool :=
  s.zeroRcParamOk || s.allDeconstructOrValueAffine

def walkAliases : Nat → Src.NatMap VarStats → Src.NatMap (List Var) →
    Src.NatMap AliasSummary → Src.NatSet → List Var → AliasSummary → AliasSummary
  | 0, _, _, _, _, _, acc => acc
  | _ + 1, _, _, _, _, [], acc => acc
  | fuel + 1, stats, adj, memo, visited, u :: rest, acc =>
    if visited.contains u then
      walkAliases fuel stats adj memo visited rest acc
    else
      let visited' := visited.insert u
      match memo.get? u with
      | some su =>
        walkAliases fuel stats adj memo visited' rest (acc.merge su)
      | none =>
        let su := (stats.getD u {}).toAliasSummary
        let next := adj.getD u []
        walkAliases fuel stats adj memo visited' (next ++ rest) (acc.merge su)

/-- Single-pass bottom-up summary of a `Fir.Code` subterm. -/
structure CodeSummary where
  stats : Src.NatMap VarStats := .leaf
  adj : Src.NatMap (List Var) := .leaf
  memo : Src.NatMap AliasSummary := .leaf
  edgeCount : Nat := 0
  bindsAffine : Bool := true
  deriving Inhabited

def evalAliasSummary (x : Var) (sum : CodeSummary) : AliasSummary × Bool :=
  match sum.memo.get? x with
  | some s => (s, true)
  | none =>
    let base := (sum.stats.getD x {}).toAliasSummary
    let children := sum.adj.getD x []
    if children.all (fun y => sum.memo.contains y) then
      let s := children.foldl (fun acc y => acc.merge (sum.memo.getD y {})) base
      (s, true)
    else
      let visited := Src.NatSet.insert .leaf x
      let s := walkAliases (sum.edgeCount + 2) sum.stats sum.adj sum.memo visited children base
      (s, false)

def argTouchesMemo (memo : Src.NatMap AliasSummary) : Arg → Bool
  | .var x => memo.contains x
  | _ => false

def rhsTouchesMemo (memo : Src.NatMap AliasSummary) : Rhs → Bool
  | .arg a => argTouchesMemo memo a
  | .ctor _ args | .prim _ args | .call _ args => args.any (argTouchesMemo memo)
  | .proj y _ _ => memo.contains y

mutual
def analyzeCode (known : Lam.Known) (jps : Src.NatMap (List Var)) : Fir.Code → CodeSummary
  | .bind x r k =>
    let kSum := analyzeCode known jps k
    let (xAlias, cacheable) := evalAliasSummary x kSum
    let xOk := xAlias.deconstructOrValueAffineOk
    let memo1 := if cacheable then kSum.memo.insert x xAlias else kSum.memo
    let stats' := addRhsUses known r kSum.stats
    let (adj', edgeCount') := match r with
      | .arg (.var y) => (kSum.adj.insert y (x :: kSum.adj.getD y []), kSum.edgeCount + 1)
      | _ => (kSum.adj, kSum.edgeCount)
    let memo' := if rhsTouchesMemo memo1 r then .leaf else memo1
    { stats := stats'
      adj := adj'
      memo := memo'
      edgeCount := edgeCount'
      bindsAffine := xOk && kSum.bindsAffine }
  | .jp _ ps rec body k =>
    let bSum := analyzeCode known jps body
    let kSum := analyzeCode known jps k
    let psOk := ps.all fun p => (evalAliasSummary p bSum).1.deconstructOrValueAffineOk
    let bStats := if rec then adjustRecBody (Src.NatSet.ofList ps) bSum.stats else bSum.stats
    { stats := mergeStatsMap VarStats.mergeSeq bStats kSum.stats
      adj := mergeAdjMap bSum.adj kSum.adj
      memo := .leaf
      edgeCount := bSum.edgeCount + kSum.edgeCount
      bindsAffine := psOk && bSum.bindsAffine && kSum.bindsAffine }
  | .jmp j args =>
    let stats := addArgsUses args false .leaf
    let ps := jps.getD j []
    let (adj, edgeCount) := (args.zip ps).foldl (fun (acc, n) (a, p) =>
      match a with
      | .var x => (acc.insert x (p :: acc.getD x []), n + 1)
      | _ => (acc, n)) (.leaf, 0)
    { stats, adj, edgeCount }
  | .case y alts dflt =>
    let aSum := analyzeAlts known jps alts
    let dSum := analyzeOpt known jps dflt
    let mStats := mergeStatsMap VarStats.mergeBranch aSum.stats dSum.stats
    let st := mStats.getD y {}
    let hasHeapAlt := alts.any (fun (.mk c _) => !isScalarCtorKey known c)
    let allScalarAlts := !alts.isEmpty && alts.all (fun (.mk c _) => isScalarCtorKey known c)
    let stats := mStats.insert y
      { st with
        projOrCaseHeap := st.projOrCaseHeap || hasHeapAlt
        usedAsScalar := st.usedAsScalar || allScalarAlts
        uses := st.uses + 1 }
    { stats
      adj := mergeAdjMap aSum.adj dSum.adj
      memo := .leaf
      edgeCount := aSum.edgeCount + dSum.edgeCount
      bindsAffine := aSum.bindsAffine && dSum.bindsAffine }
  | .ret a => { stats := addArgUse a false .leaf }
  | .tcall _ args => { stats := addArgsUses args false .leaf }
  | .trap => {}

def analyzeAlts (known : Lam.Known) (jps : Src.NatMap (List Var)) : List Fir.Alt → CodeSummary
  | [] => {}
  | .mk _ body :: alts =>
    let bSum := analyzeCode known jps body
    let aSum := analyzeAlts known jps alts
    { stats := mergeStatsMap VarStats.mergeBranch bSum.stats aSum.stats
      adj := mergeAdjMap bSum.adj aSum.adj
      memo := .leaf
      edgeCount := bSum.edgeCount + aSum.edgeCount
      bindsAffine := bSum.bindsAffine && aSum.bindsAffine }

def analyzeOpt (known : Lam.Known) (jps : Src.NatMap (List Var)) : Option Fir.Code → CodeSummary
  | none => {}
  | some c => analyzeCode known jps c
end

def analyzeBody (known : Lam.Known) (body : Fir.Code) : CodeSummary :=
  analyzeCode known (collectJoinParams .leaf body) body

/-- Whether parameter `x` (and any local/join aliases of `x`) is safe under
`.zeroRc` in a contract-annotated function `body`: either `c` is an explicit
`zeroRcBinder`, or `x` never projects/cases on a heap constructor and is either
positively used as a scalar (`Nat`/`Bool`) or used affinely (at most once along
every execution path). -/
def zeroRcParam (known : Lam.Known) (body : Fir.Code) (x : Var)
    (c : Ixon.V3.BinderContract) : Bool :=
  zeroRcBinder c || (evalAliasSummary x (analyzeBody known body)).1.zeroRcParamOk

/-- Whether variable `x` in a synthesized helper is scalar, used affinely as a
value (`≤ 1` per path), or deconstructed affinely in a pattern match without
retaining `x` as a whole value. -/
def varDeconstructOrValueAffine (known : Lam.Known) (x : Var) (body : Fir.Code) : Bool :=
  (evalAliasSummary x (analyzeBody known body)).1.deconstructOrValueAffineOk

def codeBindsAffine (known : Lam.Known) (body : Fir.Code) : Bool :=
  (analyzeBody known body).bindsAffine

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
          let sum := analyzeBody known f.body
          (f.params.zipIdx).all fun ((x, _), i) =>
            let c := f.contracts.getD i {}
            zeroRcBinder c || (evalAliasSummary x sum).1.zeroRcParamOk)))

/-- A compiler-synthesized helper function qualifies for `.zeroRc` inside an
annotated program when either `zeroRcFun` holds or all of its parameters and
local bindings are scalar or used affinely. -/
def zeroRcSynthesizedFun (known : Lam.Known) (f : Fir.Fun) : Bool :=
  zeroRcFun known f ||
    (isSynthesizedKey f.key &&
      f.letContracts.all (fun p => zeroRcLet p.2) &&
      let sum := analyzeBody known f.body
      (f.params.zipIdx).all (fun ((x, _), i) =>
        let c := f.contracts.getD i {}
        zeroRcBinder c || (evalAliasSummary x sum).1.deconstructOrValueAffineOk) &&
      sum.bindsAffine)

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
