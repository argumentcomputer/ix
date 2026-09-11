import Ix.Compiler.IxIR1.EvalRewrite
import Ix.Compiler.IxIR1.Serialize

/-!
# Checked rooted declaration reachability

This pass removes declarations which cannot be reached from top-level main or
an explicitly exported root.  A certificate is checked against an exact graph
digest, root list, canonical retained list, and successor closure.

Dynamic `apply` is deliberately conservative in version 1.  If it occurs in
main or a retained declaration, the checker accepts only the complete
declaration set.  Otherwise every executable declaration lookup is named by a
direct `call` or `papp`, and the exact evaluator proof below transports a run
through the filtered environment.  `callSelf` stays within its already
retained owner; constructor identities and direct oracle calls do not perform
declaration lookup.
-/

namespace Ix.Compiler.IxIR1.Reachability

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR
open Ix.Compiler.IxIR1.Sim

def currentVersion : Nat := 1

/-! ## Executable edge and safety walks -/

namespace Op

/-- Declaration keys which this operation can look up without inspecting a
runtime value. -/
def targets : Ix.Compiler.IxIR1.Op → List Address
  | .call function _ | .papp function _ => [function]
  | _ => []

def hasApply : Ix.Compiler.IxIR1.Op → Bool
  | .apply _ _ => true
  | _ => false

/-- Version-1 safety: dynamic application requires the all-retained fallback;
direct calls and PAP creation must point outside the declaration domain or to
a retained declaration. -/
def safe (keys retained : List Address) : Ix.Compiler.IxIR1.Op → Bool
  | .call function _ | .papp function _ =>
      !keys.contains function || retained.contains function
  | .apply _ _ => false
  | _ => true

end Op

mutual

def Code.targets : Code → List Address
  | .ret _ => []
  | .letOp operation rest => Op.targets operation ++ Code.targets rest
  | .case _ _ alternatives => AltList.targets alternatives.toList

def Alt.targets : Alt → List Address
  | .mk _ _ body => Code.targets body

def AltList.targets : List Alt → List Address
  | [] => []
  | alternative :: rest => Alt.targets alternative ++ AltList.targets rest

end

mutual

def Code.hasApply : Code → Bool
  | .ret _ => false
  | .letOp operation rest => Op.hasApply operation || Code.hasApply rest
  | .case _ _ alternatives => AltList.hasApply alternatives.toList

def Alt.hasApply : Alt → Bool
  | .mk _ _ body => Code.hasApply body

def AltList.hasApply : List Alt → Bool
  | [] => false
  | alternative :: rest =>
      Alt.hasApply alternative || AltList.hasApply rest

end

mutual

def Code.safe (keys retained : List Address) : Code → Bool
  | .ret _ => true
  | .letOp operation rest =>
      Op.safe keys retained operation && Code.safe keys retained rest
  | .case _ _ alternatives =>
      AltList.safe keys retained alternatives.toList

def Alt.safe (keys retained : List Address) : Alt → Bool
  | .mk _ _ body => Code.safe keys retained body

def AltList.safe (keys retained : List Address) : List Alt → Bool
  | [] => true
  | alternative :: rest =>
      Alt.safe keys retained alternative && AltList.safe keys retained rest

end

namespace Decl

def safe (keys retained : List Address) : Decl → Bool
  | .extern _ => true
  | .fn function => Code.safe keys retained function.body

end Decl

/-! ## Certificate and deterministic producer -/

private def entryBytes (entry : Address × Decl) : ByteArray :=
  Encoding.address entry.1 ++ Encoding.blob entry.2.preimage

private def inputDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/reachability-input/1" ++ Encoding.tag 0

/-- Exact digest of the old-keyed declaration rows and main code checked by a
reachability certificate. -/
def inputRoot (entries : List (Address × Decl)) (main : Code) : Address :=
  Address.blake3
    (inputDomain ++ Encoding.list entryBytes entries ++
      Encoding.blob main.bytes)

structure Certificate where
  version : Nat := currentVersion
  inputRoot : Address
  roots : List Address
  retained : List Address
  deriving BEq, Repr

private def keysOf (entries : List (Address × Decl)) : List Address :=
  entries.map (fun entry => entry.1)

private def canonicalRetained (keys retained : List Address) : Bool :=
  retained == keys.filter retained.contains

private def allRetained (keys retained : List Address) : Bool :=
  keys.all retained.contains

private def rootsRetained (keys retained roots : List Address) : Bool :=
  roots.all fun root => keys.contains root && retained.contains root

private def retainedDeclarationsSafe (keys retained : List Address)
    (entries : List (Address × Decl)) : Bool :=
  entries.all fun entry =>
    !retained.contains entry.1 || Decl.safe keys retained entry.2

/-- Executable certificate checker.  A complete retained set is always safe.
Any proper subset must be statically closed and contain no dynamic `apply` in
main or a retained function. -/
def validate (entries : List (Address × Decl)) (main : Code)
    (expectedRoots : List Address) (certificate : Certificate) : Bool :=
  let keys := keysOf entries
  certificate.version == currentVersion &&
    certificate.inputRoot == inputRoot entries main &&
    certificate.roots == expectedRoots &&
    canonicalRetained keys certificate.retained &&
    rootsRetained keys certificate.retained expectedRoots &&
    (allRetained keys certificate.retained ||
      (Code.safe keys certificate.retained main &&
        retainedDeclarationsSafe keys certificate.retained entries))

private def pushNew (known : List Address) (address : Address) : List Address :=
  if known.contains address then known else known ++ [address]

private def addTargets (keys : List Address) (known : List Address)
    (targets : List Address) : List Address :=
  targets.foldl (fun result target =>
    if keys.contains target then pushNew result target else result) known

private def closureStep (keys : List Address)
    (entries : List (Address × Decl)) (known : List Address) : List Address :=
  entries.foldl (fun result entry =>
    if result.contains entry.1 then
      match entry.2 with
      | .extern _ => result
      | .fn function => addTargets keys result (Code.targets function.body)
    else
      result) known

private def close (keys : List Address) (entries : List (Address × Decl)) :
    Nat → List Address → List Address
  | 0, known => known
  | fuel + 1, known => close keys entries fuel (closureStep keys entries known)

private def selectedHasApply (retained : List Address)
    (entries : List (Address × Decl)) : Bool :=
  entries.any fun entry =>
    retained.contains entry.1 &&
      match entry.2 with
      | .extern _ => false
      | .fn function => Code.hasApply function.body

/-- Untrusted deterministic producer.  `run` and external callers always send
its output back through `validate`; this routine need not be trusted for
soundness or completeness. -/
def produce (entries : List (Address × Decl)) (main : Code)
    (roots : List Address) : Certificate :=
  let keys := keysOf entries
  let seeded := addTargets keys roots (Code.targets main)
  let discovered := close keys entries entries.length seeded
  let retained := keys.filter discovered.contains
  let needsOpenWorld := Code.hasApply main || selectedHasApply retained entries
  { inputRoot := inputRoot entries main
    roots
    retained := if needsOpenWorld then keys else retained }

structure Checked where
  certificate : Certificate
  deriving Repr

/-- Public fail-closed checked-artifact API. -/
def check (entries : List (Address × Decl)) (main : Code)
    (roots : List Address) (certificate : Certificate) :
    Except String Checked :=
  if validate entries main roots certificate then
    .ok ⟨certificate⟩
  else
    .error "invalid IxIR1 rooted-reachability certificate"

theorem validate_of_check_eq_ok
    {entries : List (Address × Decl)} {main : Code}
    {roots : List Address} {certificate : Certificate} {checked : Checked}
    (hcheck : check entries main roots certificate = .ok checked) :
    validate entries main roots certificate = true := by
  unfold check at hcheck
  split at hcheck
  · assumption
  · contradiction

def filterEntries (retained : List Address)
    (entries : List (Address × Decl)) : List (Address × Decl) :=
  entries.filter fun entry => retained.contains entry.1

structure Outcome where
  entries : List (Address × Decl)
  certificate : Certificate
  accepted : Bool
  removedDeclarations : Nat

/-- Produce, check, and apply reachability.  An internal producer/checker
disagreement fails soft to the complete input list. -/
def run (roots : List Address) (entries : List (Address × Decl))
    (main : Code) : Outcome :=
  let certificate := produce entries main roots
  if validate entries main roots certificate then
    let filtered := filterEntries certificate.retained entries
    { entries := filtered
      certificate
      accepted := true
      removedDeclarations := entries.length - filtered.length }
  else
    { entries
      certificate
      accepted := false
      removedDeclarations := 0 }

/-! ## Exact evaluator transport through a checked restriction -/

private theorem envOfList_some_mem
    {entries : List (Address × Decl)} {address : Address} {declaration : Decl}
    (hlookup : Env.ofList entries address = some declaration) :
    (address, declaration) ∈ entries := by
  unfold Env.ofList at hlookup
  obtain ⟨entry, hfind, hvalue⟩ := Option.map_eq_some_iff.mp hlookup
  rcases entry with ⟨entryAddress, entryDeclaration⟩
  have hbeq : entryAddress == address :=
    List.find?_some
      (p := fun entry : Address × Decl => entry.1 == address) hfind
  have haddress : entryAddress = address := Address.eq_of_beq hbeq
  have hdeclaration : entryDeclaration = declaration := by
    simpa using hvalue
  subst entryAddress
  subst entryDeclaration
  exact List.mem_of_find?_eq_some hfind

private theorem key_mem_of_envOfList_eq_some
    {entries : List (Address × Decl)} {address : Address} {declaration : Decl}
    (hlookup : Env.ofList entries address = some declaration) :
    address ∈ keysOf entries := by
  exact List.mem_map.mpr ⟨(address, declaration), envOfList_some_mem hlookup,
    rfl⟩

theorem envOfList_filterEntries (retained : List Address)
    (entries : List (Address × Decl)) (address : Address) :
    Env.ofList (filterEntries retained entries) address =
      if retained.contains address then Env.ofList entries address else none := by
  unfold filterEntries Env.ofList
  rw [List.find?_filter]
  by_cases hretained : address ∈ retained
  · have hpred :
        (fun entry : Address × Decl =>
          decide (retained.contains entry.1 = true ∧
            (entry.1 == address) = true)) =
        (fun entry : Address × Decl => entry.1 == address) := by
      funext entry
      by_cases hsame : entry.1 = address
      · simp [hsame, hretained]
      · simp [hsame]
    rw [hpred]
    simp [hretained]
  · have hpred :
        (fun entry : Address × Decl =>
          decide (retained.contains entry.1 = true ∧
            (entry.1 == address) = true)) =
        (fun _ : Address × Decl => false) := by
      funext entry
      by_cases hsame : entry.1 = address
      · simp [hsame, hretained]
      · simp [hsame]
    rw [hpred]
    simp [hretained]

private theorem envOfList_eq_none_of_key_not_mem
    {entries : List (Address × Decl)} {address : Address}
    (hmissing : address ∉ keysOf entries) :
    Env.ofList entries address = none := by
  cases hlookup : Env.ofList entries address with
  | none => rfl
  | some declaration =>
      exact (hmissing (key_mem_of_envOfList_eq_some hlookup)).elim

private theorem envOfList_filterEntries_eq_of_safe
    {entries : List (Address × Decl)} {retained : List Address}
    {address : Address}
    (hsafe : (!(keysOf entries).contains address ||
        retained.contains address) = true) :
    Env.ofList (filterEntries retained entries) address =
      Env.ofList entries address := by
  rw [envOfList_filterEntries]
  cases hretained : retained.contains address with
  | true => simp
  | false =>
      simp only [hretained] at hsafe
      have hmissing : address ∉ keysOf entries := by
        simpa using hsafe
      simp [envOfList_eq_none_of_key_not_mem hmissing]

private def sourceCtx (entries : List (Address × Decl))
    (oracle : Address → List RVal → Option RVal) : Ctx :=
  { decls := Env.ofList entries, oracle }

private def filteredCtx (retained : List Address)
    (entries : List (Address × Decl))
    (oracle : Address → List RVal → Option RVal) : Ctx :=
  { decls := Env.ofList (filterEntries retained entries), oracle }

private theorem AltList.safe_of_mem {keys retained : List Address}
    {alternatives : List Alt} {alternative : Alt}
    (hsafe : AltList.safe keys retained alternatives = true)
    (hmember : alternative ∈ alternatives) :
    Alt.safe keys retained alternative = true := by
  induction alternatives with
  | nil => simp at hmember
  | cons head rest ih =>
      simp only [AltList.safe, Bool.and_eq_true] at hsafe
      cases hmember with
      | head => exact hsafe.1
      | tail _ member => exact ih hsafe.2 member

private theorem function_safe_of_lookup
    {entries : List (Address × Decl)} {retained : List Address}
    {address : Address} {function : FnDef}
    (hentries : retainedDeclarationsSafe (keysOf entries) retained entries =
      true)
    (hlookup : Env.ofList entries address = some (.fn function))
    (hretained : retained.contains address = true) :
    Code.safe (keysOf entries) retained function.body = true := by
  have hmember : (address, .fn function) ∈ entries :=
    envOfList_some_mem hlookup
  have hrow := List.all_eq_true.mp hentries _ hmember
  have hrow' : address ∉ retained ∨
      Code.safe (keysOf entries) retained function.body = true := by
    simpa [Decl.safe] using hrow
  exact hrow'.resolve_left (by simpa using hretained)

private theorem runCode_case_restricted_eq
    {entries : List (Address × Decl)} {retained : List Address}
    {oracle : Address → List RVal → Option RVal} {fuel : Nat}
    (ih : ∀ (current : FnDef),
      Code.safe (keysOf entries) retained current.body = true →
      ∀ (store : Store) (environment : List RVal) (input : Code),
        Code.safe (keysOf entries) retained input = true →
        runCode (filteredCtx retained entries oracle) fuel current store
            environment input =
          runCode (sourceCtx entries oracle) fuel current store environment
            input)
    (current : FnDef)
    (hcurrent : Code.safe (keysOf entries) retained current.body = true)
    (store : Store) (environment : List RVal) (scrutinee : Atom)
    (peelNat : Bool) (alternatives : Array Alt)
    (hsafe : Code.safe (keysOf entries) retained
      (.case scrutinee peelNat alternatives) = true) :
    runCode (filteredCtx retained entries oracle) (fuel + 1) current store
        environment (.case scrutinee peelNat alternatives) =
      runCode (sourceCtx entries oracle) (fuel + 1) current store environment
        (.case scrutinee peelNat alternatives) := by
  simp only [Code.safe] at hsafe
  simp only [runCode]
  cases hscrutinee : resolveAtom environment scrutinee with
  | error error => simp [bind, Except.bind]
  | ok value =>
      simp only [bind, Except.bind]
      cases value with
      | erased => simp
      | lit literal =>
          cases literal with
          | str value => simp
          | nat value =>
              simp only
              cases peelNat with
              | false => simp
              | true =>
                  simp only
                  cases value with
                  | zero =>
                      simp only
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 0) with
                      | none => simp
                      | some alternative =>
                          have hmember : alternative ∈ alternatives :=
                            Array.mem_of_find?_eq_some hfind
                          have haltSafe := AltList.safe_of_mem hsafe
                            (by simpa using hmember)
                          cases alternative with
                          | mk cidx fields body =>
                              simp only [Alt.safe] at haltSafe
                              cases fields with
                              | zero =>
                                  simpa using ih current hcurrent store
                                    environment body haltSafe
                              | succ fields => simp
                  | succ value =>
                      simp only
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 1) with
                      | none => simp
                      | some alternative =>
                          have hmember : alternative ∈ alternatives :=
                            Array.mem_of_find?_eq_some hfind
                          have haltSafe := AltList.safe_of_mem hsafe
                            (by simpa using hmember)
                          cases alternative with
                          | mk cidx fields body =>
                              simp only [Alt.safe] at haltSafe
                              cases fields with
                              | zero => simp
                              | succ fields =>
                                  cases fields with
                                  | zero =>
                                      simpa using ih current hcurrent store
                                        (.lit (.nat value) :: environment)
                                        body haltSafe
                                  | succ fields => simp
      | loc location =>
          simp only
          cases hget : store.get? location with
          | none => simp
          | some box =>
              simp only
              cases hnode : box.node with
              | papN function arity arguments => simp
              | ctorN identity fields =>
                  simp only
                  cases hfind : alternatives.find?
                      (fun alternative =>
                        alternative.cidx == identity.cidx) with
                  | none => simp
                  | some alternative =>
                      have hmember : alternative ∈ alternatives :=
                        Array.mem_of_find?_eq_some hfind
                      have haltSafe := AltList.safe_of_mem hsafe
                        (by simpa using hmember)
                      cases alternative with
                      | mk cidx fieldCount body =>
                          simp only [Alt.safe] at haltSafe
                          by_cases hfields : fields.size = fieldCount
                          · simpa [hfields] using
                              ih current hcurrent store
                                (fields.foldl
                                  (fun result field => field :: result)
                                  environment) body haltSafe
                          · simp [hfields]

private structure RestrictedAt
    (entries : List (Address × Decl)) (retained : List Address)
    (oracle : Address → List RVal → Option RVal)
    (entriesSafe : retainedDeclarationsSafe (keysOf entries) retained entries =
      true) (fuel : Nat) : Prop where
  runCode : ∀ (current : FnDef),
    Code.safe (keysOf entries) retained current.body = true →
    ∀ (store : Store) (environment : List RVal) (input : Code),
      Code.safe (keysOf entries) retained input = true →
      IxIR1.runCode (filteredCtx retained entries oracle) fuel current store
          environment input =
        IxIR1.runCode (sourceCtx entries oracle) fuel current store environment
          input
  runOp : ∀ (current : FnDef),
    Code.safe (keysOf entries) retained current.body = true →
    ∀ (store : Store) (environment : List RVal) (operation : Op),
      Op.safe (keysOf entries) retained operation = true →
      IxIR1.runOp (filteredCtx retained entries oracle) fuel current store
          environment operation =
        IxIR1.runOp (sourceCtx entries oracle) fuel current store environment
          operation
  invoke : ∀ (function : Address),
    (!(keysOf entries).contains function || retained.contains function) =
      true →
    ∀ (arguments : List RVal) (store : Store),
      IxIR1.invoke (filteredCtx retained entries oracle) fuel function
          arguments store =
        IxIR1.invoke (sourceCtx entries oracle) fuel function arguments store

private theorem restrictedAt
    (entries : List (Address × Decl)) (retained : List Address)
    (oracle : Address → List RVal → Option RVal)
    (entriesSafe : retainedDeclarationsSafe (keysOf entries) retained entries =
      true) :
    ∀ fuel, RestrictedAt entries retained oracle entriesSafe fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [runCode, runOp, IxIR1.invoke]
  | succ fuel smaller =>
      refine ⟨?_, ?_, ?_⟩
      · intro current hcurrent store environment input hsafe
        cases input with
        | ret atom => simp [runCode]
        | letOp operation rest =>
            simp only [Code.safe, Bool.and_eq_true] at hsafe
            simp only [runCode]
            rw [smaller.runOp current hcurrent store environment operation
              hsafe.1]
            cases hoperation : runOp (sourceCtx entries oracle) fuel current
                store environment operation with
            | error error => rfl
            | ok output =>
                rcases output with ⟨next, value⟩
                exact smaller.runCode current hcurrent next
                  (value :: environment) rest hsafe.2
        | case scrutinee peelNat alternatives =>
            exact runCode_case_restricted_eq smaller.runCode current hcurrent
              store environment scrutinee peelNat alternatives hsafe
      · intro current hcurrent store environment operation hsafe
        cases operation with
        | pure atom => simp [runOp]
        | alloc world identity arguments => simp [runOp]
        | reuse target identity arguments => simp [runOp]
        | free target => simp [runOp]
        | dup target => simp [runOp]
        | drop target =>
            simp only [runOp]
            cases htarget : resolveAtom environment target with
            | error error => simp [bind, Except.bind]
            | ok value =>
                simp only [bind, Except.bind]
                cases value with
                | lit literal => rfl
                | erased => rfl
                | loc location =>
                    change (do
                        let next ← dropVal
                          (filteredCtx retained entries oracle) fuel store
                          (.loc location)
                        .ok (next, RVal.erased)) =
                      (do
                        let next ← dropVal (sourceCtx entries oracle) fuel
                          store (.loc location)
                        .ok (next, RVal.erased))
                    rw [dropVal_ctx_eq (sourceCtx entries oracle)
                      (filteredCtx retained entries oracle) fuel store
                      (.loc location)]
        | dropU target =>
            simp only [runOp]
            cases htarget : resolveAtom environment target with
            | error error => simp [bind, Except.bind]
            | ok value =>
                simp only [bind, Except.bind]
                cases value with
                | lit literal => rfl
                | erased => rfl
                | loc location =>
                    change (do
                        let next ← dropUVal
                          (filteredCtx retained entries oracle) fuel store
                          (.loc location)
                        .ok (next, RVal.erased)) =
                      (do
                        let next ← dropUVal (sourceCtx entries oracle) fuel
                          store (.loc location)
                        .ok (next, RVal.erased))
                    rw [dropUVal_ctx_eq (sourceCtx entries oracle)
                      (filteredCtx retained entries oracle) fuel store
                      (.loc location)]
        | fetch target field => simp [runOp]
        | call function arguments =>
            simp only [Op.safe] at hsafe
            simp only [runOp]
            cases harguments : resolveAtoms environment arguments with
            | error error => rfl
            | ok values => exact smaller.invoke function hsafe values store
        | callSelf arguments =>
            simp only [runOp]
            cases harguments : resolveAtoms environment arguments with
            | error error => simp [bind, Except.bind]
            | ok values =>
                simp only [bind, Except.bind]
                by_cases harity : values.length = current.arity
                · simp only [harity]
                  rw [smaller.runCode current hcurrent store values.reverse
                    current.body hcurrent]
                · simp [harity]
        | papp function arguments =>
            simp only [Op.safe] at hsafe
            simp only [runOp]
            cases harguments : resolveAtoms environment arguments with
            | error error => rfl
            | ok values =>
                simp only [bind, Except.bind]
                have hlookup :
                    (filteredCtx retained entries oracle).decls function =
                      (sourceCtx entries oracle).decls function :=
                  envOfList_filterEntries_eq_of_safe hsafe
                rw [hlookup]
        | apply function arguments =>
            simp [Op.safe] at hsafe
        | extern function arguments =>
            simp [runOp, callScalarOracle, filteredCtx, sourceCtx]
      · intro function hsafe arguments store
        have hlookup :
            (filteredCtx retained entries oracle).decls function =
              (sourceCtx entries oracle).decls function := by
          exact envOfList_filterEntries_eq_of_safe hsafe
        simp only [IxIR1.invoke]
        rw [hlookup]
        cases hsource : Env.ofList entries function with
        | none => simp [sourceCtx, hsource]
        | some declaration =>
            have hkey : function ∈ keysOf entries :=
              key_mem_of_envOfList_eq_some hsource
            have hkeyBool : (keysOf entries).contains function = true := by
              simpa using hkey
            have hretained : retained.contains function = true := by
              have hsafe' : function ∉ keysOf entries ∨
                  function ∈ retained := by
                simpa using hsafe
              have hmember := hsafe'.resolve_left (fun hmissing =>
                hmissing hkey)
              simpa using hmember
            cases declaration with
            | extern arity =>
                simp [sourceCtx, hsource, filteredCtx, callScalarOracle]
            | fn called =>
                have hcalledSafe := function_safe_of_lookup entriesSafe
                  hsource hretained
                by_cases harity : arguments.length = called.arity
                · have harityBool :
                      (arguments.length != called.arity) = false := by
                    simp [harity]
                  simp only [sourceCtx, hsource, harityBool,
                    Bool.false_eq_true, if_false]
                  have hbody := smaller.runCode called hcalledSafe store
                    arguments.reverse called.body hcalledSafe
                  simpa [sourceCtx] using congrArg
                    (fun output => output >>= checkResultWorld called.result)
                    hbody
                · simp [sourceCtx, hsource, harity]

private theorem filterEntries_eq_self_of_allRetained
    {entries : List (Address × Decl)} {retained : List Address}
    (hall : allRetained (keysOf entries) retained = true) :
    filterEntries retained entries = entries := by
  apply List.filter_eq_self.mpr
  intro entry hmember
  have hkey : entry.1 ∈ keysOf entries := by
    exact List.mem_map.mpr ⟨entry, hmember, rfl⟩
  have hretained := List.all_eq_true.mp hall entry.1 hkey
  simpa using hretained

/-- A valid proper-subset certificate preserves the complete top-level
evaluator result exactly.  The all-retained dynamic-apply fallback is the
degenerate equality case. -/
theorem runMain_filterEntries_eq_of_validate
    {entries : List (Address × Decl)} {main : Code}
    {roots : List Address} {certificate : Certificate}
    (hvalid : validate entries main roots certificate = true)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain
        { decls := Env.ofList
            (filterEntries certificate.retained entries)
          oracle }
        main fuel =
      runMain { decls := Env.ofList entries, oracle } main fuel := by
  simp only [validate, Bool.and_eq_true, Bool.or_eq_true] at hvalid
  have hmode := hvalid.2
  cases hmode with
  | inl hall =>
      have hentries : filterEntries certificate.retained entries = entries :=
        filterEntries_eq_self_of_allRetained hall
      rw [hentries]
  | inr hclosed =>
      let current : FnDef := ⟨0, .shared, false, main⟩
      have heq :=
        (restrictedAt entries certificate.retained oracle hclosed.2 fuel).runCode
          current hclosed.1 {} [] main hclosed.1
      simpa [runMain, current, filteredCtx, sourceCtx] using heq

/-- The produce/check/apply wrapper is fail-soft and exact whether its
internally produced certificate is accepted or rejected. -/
theorem runMain_run_eq (roots : List Address)
    (entries : List (Address × Decl)) (main : Code)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain { decls := Env.ofList (run roots entries main).entries, oracle }
        main fuel =
      runMain { decls := Env.ofList entries, oracle } main fuel := by
  generalize hcertificate : produce entries main roots = certificate
  cases hvalid : validate entries main roots certificate with
  | false => simp [run, hcertificate, hvalid]
  | true =>
      simp only [run, hcertificate, hvalid, if_true]
      exact runMain_filterEntries_eq_of_validate hvalid oracle fuel

end Ix.Compiler.IxIR1.Reachability
