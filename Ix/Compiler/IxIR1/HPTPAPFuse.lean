import Ix.Compiler.IxIR1.EvalRewrite
import Ix.Compiler.IxIR1.HPTSound

/-!
# Checked local PAP/application fusion

The first PAP consumer is deliberately allocation-site local.  It recognizes
two adjacent binders

```text
let p := papp f captured
let y := apply p supplied
rest
```

and replaces them with a larger `papp`, a direct `call`, or a direct `call`
followed by the residual `apply`.  Both binder slots are retained, so no
general de Bruijn substitution is needed.  The checker establishes:

- the target declaration and its arity;
- exact argument order across under-, exact-, and over-saturation;
- that supplied arguments do not refer to the consumed PAP;
- that the old PAP binder is absent from the continuation; and
- that every captured runtime value is scalar according to checked HPT facts.

The scalar restriction is substantive rather than cosmetic.  IxIR₁ function
definitions retain result ownership but no longer carry parameter modes, and
HPT does not infer heap worlds.  A local checker can therefore prove that a
capture needs no retain/release traffic when it is scalar, but cannot certify
an arbitrary heap capture as shared.  A later borrow/ownership artifact can
broaden this same rewrite without changing its syntax contract.
-/

namespace Ix.Compiler.IxIR1.HPT.PAPFuse

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR1.Sim

/-- A fact which admits scalars and no heap value.  Bottom also satisfies the
test; its concrete interpretation is empty, so it cannot authorize a
successful non-scalar capture. -/
def scalarOnly (fact : Fact) : Bool :=
  !fact.unknownHeap && fact.shapes.isEmpty

/-- Lower one operand across removal of the immediately preceding PAP binder.
`none` is exactly a use of that consumed binder. -/
def lowerAtom? : Atom → Option Atom
  | .var 0 => none
  | .var (index + 1) => some (.var index)
  | .lit literal => some (.lit literal)
  | .erased => some .erased

def lowerAtoms? (atoms : Array Atom) : Option (Array Atom) :=
  (atoms.toList.mapM lowerAtom?).map List.toArray

def atomUsesVar (needle : Nat) : Atom → Bool
  | .var index => index == needle
  | .lit _ | .erased => false

def atomsUseVar (needle : Nat) (atoms : Array Atom) : Bool :=
  atoms.any (atomUsesVar needle)

def opUsesVar (needle : Nat) : Op → Bool
  | .pure atom => atomUsesVar needle atom
  | .alloc _ _ atoms | .call _ atoms | .papp _ atoms |
      .extern _ atoms | .callSelf atoms => atomsUseVar needle atoms
  | .reuse target _ atoms =>
      atomUsesVar needle target || atomsUseVar needle atoms
  | .free target | .dup target | .drop target | .dropU target =>
      atomUsesVar needle target
  | .fetch target _ => atomUsesVar needle target
  | .apply function atoms =>
      atomUsesVar needle function || atomsUseVar needle atoms

mutual

private def codeUsesVarFuel : Nat → Code → Nat → Bool
  | 0, _, _ => true
  | _ + 1, .ret atom, needle => atomUsesVar needle atom
  | fuel + 1, .letOp operation rest, needle =>
      opUsesVar needle operation ||
        codeUsesVarFuel fuel rest (needle + 1)
  | fuel + 1, .case scrutinee _ alternatives, needle =>
      atomUsesVar needle scrutinee ||
        alternatives.any
          (fun alternative => altUsesVarFuel fuel alternative needle)

private def altUsesVarFuel : Nat → Alt → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, .mk _ fields body, needle =>
      codeUsesVarFuel fuel body (needle + fields)

end

/-- Capture-aware occurrence check.  `needle` is expressed in the entry
environment; let and case binders shift it on recursive descent.  Fuel is the
syntax size and exhaustion conservatively reports a use. -/
def codeUsesVar (input : Code) (needle : Nat) : Bool :=
  codeUsesVarFuel (input.bytes.size + 1) input needle

/-! The executable occurrence check has a proof-oriented counterpart.  A
false fuel result is enough to construct this evidence: exhaustion returns
`true`, so accepted code necessarily carries evidence down every path. -/

mutual

inductive CodeNoUse : Nat → Code → Prop where
  | ret {needle atom} (hnot : atomUsesVar needle atom = false) :
      CodeNoUse needle (.ret atom)
  | letOp {needle operation rest}
      (hop : opUsesVar needle operation = false)
      (hrest : CodeNoUse (needle + 1) rest) :
      CodeNoUse needle (.letOp operation rest)
  | case {needle scrutinee peelNat alternatives}
      (hscrutinee : atomUsesVar needle scrutinee = false)
      (halternatives : ∀ alternative, alternative ∈ alternatives →
        AltNoUse needle alternative) :
      CodeNoUse needle (.case scrutinee peelNat alternatives)

inductive AltNoUse : Nat → Alt → Prop where
  | mk {needle cidx fields body}
      (hbody : CodeNoUse (needle + fields) body) :
      AltNoUse needle (.mk cidx fields body)

end

mutual

private theorem codeNoUse_of_fuel_false : ∀ fuel input needle,
    codeUsesVarFuel fuel input needle = false → CodeNoUse needle input := by
  intro fuel input needle hcheck
  cases fuel with
  | zero => simp [codeUsesVarFuel] at hcheck
  | succ fuel =>
      cases input with
      | ret atom => exact .ret hcheck
      | letOp operation rest =>
          simp only [codeUsesVarFuel, Bool.or_eq_false_iff] at hcheck
          exact .letOp hcheck.1
            (codeNoUse_of_fuel_false fuel rest (needle + 1) hcheck.2)
      | case scrutinee peelNat alternatives =>
          simp only [codeUsesVarFuel, Bool.or_eq_false_iff] at hcheck
          refine .case hcheck.1 ?_
          intro alternative halternative
          apply altNoUse_of_fuel_false fuel alternative needle
          have hnotTrue :
              ¬ altUsesVarFuel fuel alternative needle = true :=
            (Array.any_eq_false'.mp hcheck.2) alternative halternative
          exact Bool.eq_false_iff.mpr hnotTrue

private theorem altNoUse_of_fuel_false : ∀ fuel alternative needle,
    altUsesVarFuel fuel alternative needle = false →
      AltNoUse needle alternative := by
  intro fuel alternative needle hcheck
  cases fuel with
  | zero => simp [altUsesVarFuel] at hcheck
  | succ fuel =>
      cases alternative with
      | mk cidx fields body =>
          exact .mk
            (codeNoUse_of_fuel_false fuel body (needle + fields) hcheck)

end


theorem codeNoUse_of_codeUsesVar_eq_false {input : Code} {needle : Nat}
    (hcheck : codeUsesVar input needle = false) :
    CodeNoUse needle input :=
  codeNoUse_of_fuel_false (input.bytes.size + 1) input needle hcheck

/-! ## Environment irrelevance

The relation deliberately permits the distinguished slots to contain
arbitrary values.  It is stable when an operation result or constructor
fields are pushed in front of both environments. -/

def EnvsAgreeExcept (needle : Nat) (left right : List RVal) : Prop :=
  ∀ index, index ≠ needle → left[index]? = right[index]?

namespace EnvsAgreeExcept

theorem cons {needle : Nat} {left right : List RVal}
    (h : EnvsAgreeExcept needle left right) (value : RVal) :
    EnvsAgreeExcept (needle + 1) (value :: left) (value :: right) := by
  intro index hindex
  cases index with
  | zero => rfl
  | succ index =>
      simp only [List.getElem?_cons_succ]
      apply h index
      omega

theorem prepend {needle : Nat} {left right : List RVal}
    (h : EnvsAgreeExcept needle left right) (values : List RVal) :
    EnvsAgreeExcept (needle + values.length)
      (values ++ left) (values ++ right) := by
  induction values with
  | nil => simpa using h
  | cons value values ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih.cons value

theorem second (head leftValue rightValue : RVal) (tail : List RVal) :
    EnvsAgreeExcept 1
      (head :: leftValue :: tail) (head :: rightValue :: tail) := by
  intro index hindex
  cases index with
  | zero => rfl
  | succ index =>
      cases index with
      | zero => omega
      | succ index => rfl

end EnvsAgreeExcept

private theorem resolveAtom_env_eq {needle : Nat} {left right : List RVal}
    (henvironment : EnvsAgreeExcept needle left right) {atom : Atom}
    (hnot : atomUsesVar needle atom = false) :
    resolveAtom left atom = resolveAtom right atom := by
  cases atom with
  | var index =>
      have hindex : index ≠ needle := by
        simpa [atomUsesVar] using hnot
      simp only [resolveAtom]
      rw [henvironment index hindex]
  | lit literal => rfl
  | erased => rfl

private theorem List.resolveAtomsFrom_env_eq {needle : Nat}
    {left right : List RVal} (henvironment : EnvsAgreeExcept needle left right) :
    ∀ (atoms : List Atom) (accumulator : List RVal),
      (∀ atom, atom ∈ atoms → atomUsesVar needle atom = false) →
      atoms.foldlM
          (fun accumulated atom => do
            pure (accumulated ++ [← resolveAtom left atom])) accumulator =
        atoms.foldlM
          (fun accumulated atom => do
            pure (accumulated ++ [← resolveAtom right atom])) accumulator := by
  intro atoms
  induction atoms with
  | nil => intro accumulator _; rfl
  | cons atom atoms ih =>
      intro accumulator hnot
      simp only [List.foldlM_cons]
      rw [resolveAtom_env_eq henvironment (hnot atom (by simp))]
      cases resolveAtom right atom with
      | error error => rfl
      | ok value =>
          simp only [bind, Except.bind]
          apply ih
          intro tail htail
          exact hnot tail (by simp [htail])

private theorem resolveAtoms_env_eq {needle : Nat} {left right : List RVal}
    (henvironment : EnvsAgreeExcept needle left right) {atoms : Array Atom}
    (hnot : atomsUseVar needle atoms = false) :
    resolveAtoms left atoms = resolveAtoms right atoms := by
  unfold resolveAtoms
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  apply List.resolveAtomsFrom_env_eq henvironment
  intro atom hatom
  have hnotTrue : ¬ atomUsesVar needle atom = true :=
    (Array.any_eq_false'.mp hnot) atom (by simpa using hatom)
  exact Bool.eq_false_iff.mpr hnotTrue

/-- An operation which does not mention the distinguished slot has exactly
the same behavior in environments which differ only there. -/
theorem runOp_env_eq_of_noUse {ctx : Ctx} {fuel : Nat} {current : FnDef}
    {store : Store} {needle : Nat} {left right : List RVal}
    (henvironment : EnvsAgreeExcept needle left right) {operation : Op}
    (hnot : opUsesVar needle operation = false) :
    runOp ctx fuel current store left operation =
      runOp ctx fuel current store right operation := by
  cases fuel with
  | zero => rw [runOp.eq_def, runOp.eq_def]
  | succ fuel =>
      cases operation with
      | pure atom =>
          simp only [runOp]
          rw [resolveAtom_env_eq henvironment hnot]
      | alloc world cidx atoms =>
          simp only [runOp]
          rw [resolveAtoms_env_eq henvironment hnot]
      | reuse target cidx atoms =>
          simp only [runOp]
          simp only [opUsesVar, Bool.or_eq_false_iff] at hnot
          rw [resolveAtoms_env_eq henvironment hnot.2,
            resolveAtom_env_eq henvironment hnot.1]
      | free target | dup target | drop target | dropU target | fetch target _ =>
          simp only [runOp]
          rw [resolveAtom_env_eq henvironment hnot]
      | call function atoms =>
          simp only [runOp]
          rw [resolveAtoms_env_eq henvironment hnot]
      | callSelf atoms =>
          simp only [runOp]
          rw [resolveAtoms_env_eq henvironment hnot]
      | papp function atoms =>
          simp only [runOp]
          rw [resolveAtoms_env_eq henvironment hnot]
      | extern function atoms =>
          simp only [runOp]
          rw [resolveAtoms_env_eq henvironment hnot]
      | apply function atoms =>
          simp only [runOp]
          simp only [opUsesVar, Bool.or_eq_false_iff] at hnot
          rw [resolveAtom_env_eq henvironment hnot.1,
            resolveAtoms_env_eq henvironment hnot.2]

private theorem List.foldl_cons_eq_reverse_append
    (values environment : List RVal) :
    values.foldl (fun accumulated value => value :: accumulated) environment =
      values.reverse ++ environment := by
  induction values generalizing environment with
  | nil => rfl
  | cons value values ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem Array.foldl_cons_eq_reverse_append
    (values : Array RVal) (environment : List RVal) :
    values.foldl (fun accumulated value => value :: accumulated) environment =
      values.toList.reverse ++ environment := by
  rw [← Array.foldl_toList]
  exact List.foldl_cons_eq_reverse_append values.toList environment

/-- Code certified not to use one slot is completely insensitive to that
slot, including errors and fuel behavior. -/
theorem runCode_env_eq_of_noUse {ctx : Ctx} :
    ∀ fuel current store needle left right input,
      EnvsAgreeExcept needle left right →
      CodeNoUse needle input →
      runCode ctx fuel current store left input =
        runCode ctx fuel current store right input := by
  intro fuel
  induction fuel with
  | zero =>
      intro current store needle left right input henvironment hnot
      rw [runCode.eq_def, runCode.eq_def]
  | succ fuel smaller =>
      intro current store needle left right input henvironment hnot
      cases hnot with
      | ret hatom =>
          simp only [runCode]
          rw [resolveAtom_env_eq henvironment hatom]
      | @letOp _ operation rest hop hrest =>
          simp only [runCode]
          rw [runOp_env_eq_of_noUse henvironment hop]
          cases hoperation : runOp ctx fuel current store right operation with
          | error error => rfl
          | ok output =>
              rcases output with ⟨next, value⟩
              simp only [hoperation, bind, Except.bind]
              exact smaller current next (needle + 1)
                (value :: left) (value :: right) rest
                (henvironment.cons value) hrest
      | @case _ scrutinee peelNat alternatives hscrutinee halternatives =>
          rw [runCode.eq_def, runCode.eq_def]
          dsimp only
          rw [resolveAtom_env_eq henvironment hscrutinee]
          cases hresolve : resolveAtom right scrutinee with
          | error error => rfl
          | ok scrutineeValue =>
              simp only [hresolve, bind, Except.bind]
              cases scrutineeValue with
              | erased => rfl
              | loc location =>
                  cases hbox : store.get? location with
                  | none => simp [hbox]
                  | some box =>
                      simp only [hbox]
                      cases box.node with
                      | papN function arity captured => rfl
                      | ctorN identity fields =>
                          dsimp only
                          cases halt : alternatives.find?
                              (fun alternative =>
                                alternative.cidx == identity.cidx) with
                          | none => simp [halt]
                          | some alternative =>
                              have haltNo := halternatives alternative
                                (Array.mem_of_find?_eq_some halt)
                              cases alternative with
                              | mk cidx fieldCount body =>
                                  cases haltNo with
                                  | mk hbody =>
                                      cases hsize : fields.size != fieldCount
                                      · simp only [halt, hsize,
                                          Bool.false_eq_true, if_false]
                                        rw [
                                          Array.foldl_cons_eq_reverse_append,
                                          Array.foldl_cons_eq_reverse_append]
                                        apply smaller current store
                                          (needle + fieldCount)
                                          (fields.toList.reverse ++ left)
                                          (fields.toList.reverse ++ right)
                                          body
                                        · have hprefix := henvironment.prepend
                                            fields.toList.reverse
                                          have hfieldCount :
                                              fields.size = fieldCount := by
                                            simpa using hsize
                                          simpa [hfieldCount] using hprefix
                                        · exact hbody
                                      · simp [halt, hsize]
              | lit literal =>
                  cases literal with
                  | str string => rfl
                  | nat value =>
                      cases hpeel : peelNat with
                      | false => simp [hpeel]
                      | true =>
                          cases value with
                          | zero =>
                              cases halt : alternatives.find?
                                  (fun alternative =>
                                    alternative.cidx == 0) with
                              | none => simp [hpeel, halt]
                              | some alternative =>
                                  have haltNo := halternatives alternative
                                    (Array.mem_of_find?_eq_some halt)
                                  cases alternative with
                                  | mk cidx fieldCount body =>
                                      cases haltNo with
                                      | mk hbody =>
                                          cases fieldCount with
                                          | zero =>
                                              simp only [hpeel, halt]
                                              exact smaller current store
                                                needle left right body
                                                henvironment (by simpa using hbody)
                                          | succ fieldCount =>
                                              simp [hpeel, halt]
                          | succ value =>
                              cases halt : alternatives.find?
                                  (fun alternative =>
                                    alternative.cidx == 1) with
                              | none => simp [hpeel, halt]
                              | some alternative =>
                                  have haltNo := halternatives alternative
                                    (Array.mem_of_find?_eq_some halt)
                                  cases alternative with
                                  | mk cidx fieldCount body =>
                                      cases haltNo with
                                      | mk hbody =>
                                          cases fieldCount with
                                          | zero => simp [hpeel, halt]
                                          | succ fieldCount =>
                                              cases fieldCount with
                                              | zero =>
                                                  simp only [hpeel, halt]
                                                  exact smaller current store
                                                    (needle + 1)
                                                    (.lit (.nat value) :: left)
                                                    (.lit (.nat value) :: right)
                                                    body
                                                    (henvironment.cons
                                                      (.lit (.nat value)))
                                                    (by simpa using hbody)
                                              | succ fieldCount =>
                                                  simp [hpeel, halt]

private def scalarCaptures (facts : List Fact)
    (captured : Array Atom) : Bool :=
  match resolveAtomFacts facts captured with
  | .error _ => false
  | .ok captureFacts => captureFacts.all scalarOnly

inductive Kind where
  | under
  | exact
  | over
  deriving BEq, Repr

/-- One accepted local replacement, classified for deterministic reporting. -/
structure Fusion where
  code : Code
  kind : Kind

/-- Check and construct one adjacent PAP/application fusion. -/
def fusePair? (declarations : DeclEnv) (facts : List Fact)
    (function : Address) (captured supplied : Array Atom)
    (rest : Code) : Option Fusion := do
  let declaration ← declarations function
  let arity := declArity declaration
  if captured.size >= arity then none
  else if !scalarCaptures facts captured then none
  else if codeUsesVar rest 1 then none
  else
    let loweredSupplied ← lowerAtoms? supplied
    let combined := captured.toList ++ loweredSupplied.toList
    if combined.length < arity then
      some ⟨.letOp (.papp function combined.toArray)
          (.letOp (.pure (.var 0)) rest), .under⟩
    else if combined.length == arity then
      some ⟨.letOp (.call function combined.toArray)
          (.letOp (.pure (.var 0)) rest), .exact⟩
    else
      let consumedSupplied := arity - captured.size
      let first := combined.take arity |>.toArray
      let remaining := supplied.toList.drop consumedSupplied |>.toArray
      some ⟨.letOp (.call function first)
          (.letOp (.apply (.var 0) remaining) rest), .over⟩

/-! A proof-facing view of an accepted executable decision. -/

inductive FuseSpec (declarations : DeclEnv) (facts : List Fact)
    (function : Address) (captured supplied : Array Atom) (rest : Code) :
    Fusion → Prop where
  | under {declaration : Decl} {lowered : Array Atom}
      (hdeclaration : declarations function = some declaration)
      (hcaptureArity : captured.size < declArity declaration)
      (hscalar : scalarCaptures facts captured = true)
      (hrest : codeUsesVar rest 1 = false)
      (hlowered : lowerAtoms? supplied = some lowered)
      (hunder : (captured.toList ++ lowered.toList).length <
        declArity declaration) :
      FuseSpec declarations facts function captured supplied rest
        ⟨.letOp
          (.papp function (captured.toList ++ lowered.toList).toArray)
          (.letOp (.pure (.var 0)) rest), .under⟩
  | exact {declaration : Decl} {lowered : Array Atom}
      (hdeclaration : declarations function = some declaration)
      (hcaptureArity : captured.size < declArity declaration)
      (hscalar : scalarCaptures facts captured = true)
      (hrest : codeUsesVar rest 1 = false)
      (hlowered : lowerAtoms? supplied = some lowered)
      (hexact : (captured.toList ++ lowered.toList).length =
        declArity declaration) :
      FuseSpec declarations facts function captured supplied rest
        ⟨.letOp
          (.call function (captured.toList ++ lowered.toList).toArray)
          (.letOp (.pure (.var 0)) rest), .exact⟩
  | over {declaration : Decl} {lowered : Array Atom}
      (hdeclaration : declarations function = some declaration)
      (hcaptureArity : captured.size < declArity declaration)
      (hscalar : scalarCaptures facts captured = true)
      (hrest : codeUsesVar rest 1 = false)
      (hlowered : lowerAtoms? supplied = some lowered)
      (hover : declArity declaration <
        (captured.toList ++ lowered.toList).length) :
      FuseSpec declarations facts function captured supplied rest
        ⟨.letOp
          (.call function
            ((captured.toList ++ lowered.toList).take
              (declArity declaration)).toArray)
          (.letOp
            (.apply (.var 0)
              (supplied.toList.drop
                (declArity declaration - captured.size)).toArray)
            rest), .over⟩

theorem fuseSpec_of_fusePair?_eq_some
    {declarations : DeclEnv} {facts : List Fact} {function : Address}
    {captured supplied : Array Atom} {rest : Code} {fusion : Fusion}
    (hfusion : fusePair? declarations facts function captured supplied rest =
      some fusion) :
    FuseSpec declarations facts function captured supplied rest fusion := by
  cases hdeclaration : declarations function with
  | none => simp [fusePair?, hdeclaration] at hfusion
  | some declaration =>
      by_cases hcapture : captured.size >= declArity declaration
      · simp [fusePair?, hdeclaration, hcapture] at hfusion
      · have hcapture' : captured.size < declArity declaration := by omega
        by_cases hscalar : scalarCaptures facts captured = true
        · by_cases hrest : codeUsesVar rest 1 = false
          · cases hlowered : lowerAtoms? supplied with
            | none =>
                simp [fusePair?, hdeclaration, hcapture, hscalar, hrest,
                  hlowered] at hfusion
            | some lowered =>
                by_cases hunder :
                    (captured.toList ++ lowered.toList).length <
                      declArity declaration
                · have heq :
                      (⟨.letOp
                          (.papp function
                            (captured.toList ++ lowered.toList).toArray)
                          (.letOp (.pure (.var 0)) rest), .under⟩ : Fusion) =
                        fusion := by
                      have hunderSize :
                          captured.size + lowered.size <
                            declArity declaration := by simpa using hunder
                      simpa [fusePair?, hdeclaration, hcapture, hscalar,
                        hrest, hlowered, hunderSize] using hfusion
                  subst fusion
                  exact .under hdeclaration hcapture' hscalar hrest hlowered
                    hunder
                · by_cases hexact :
                    (captured.toList ++ lowered.toList).length =
                      declArity declaration
                  · have heq :
                        (⟨.letOp
                            (.call function
                              (captured.toList ++ lowered.toList).toArray)
                            (.letOp (.pure (.var 0)) rest), .exact⟩ : Fusion) =
                          fusion := by
                        have hnotUnderSize :
                            ¬ captured.size + lowered.size <
                              declArity declaration := by simpa using hunder
                        have hexactSize : captured.size + lowered.size =
                            declArity declaration := by simpa using hexact
                        simpa [fusePair?, hdeclaration, hcapture, hscalar,
                          hrest, hlowered, hnotUnderSize, hexactSize] using
                            hfusion
                    subst fusion
                    exact .exact hdeclaration hcapture' hscalar hrest hlowered
                      hexact
                  · have hover : declArity declaration <
                        (captured.toList ++ lowered.toList).length := by omega
                    have heq :
                        (⟨.letOp
                            (.call function
                              ((captured.toList ++ lowered.toList).take
                                (declArity declaration)).toArray)
                            (.letOp
                              (.apply (.var 0)
                                (supplied.toList.drop
                                  (declArity declaration - captured.size)).toArray)
                              rest), .over⟩ : Fusion) = fusion := by
                        have hnotUnderSize :
                            ¬ captured.size + lowered.size <
                              declArity declaration := by simpa using hunder
                        have hnotExactSize :
                            captured.size + lowered.size ≠
                              declArity declaration := by simpa using hexact
                        simpa [fusePair?, hdeclaration, hcapture, hscalar,
                          hrest, hlowered, hnotUnderSize, hnotExactSize] using
                            hfusion
                    subst fusion
                    exact .over hdeclaration hcapture' hscalar hrest hlowered
                      hover
          · simp [fusePair?, hdeclaration, hcapture, hscalar, hrest] at hfusion
        · simp [fusePair?, hdeclaration, hcapture, hscalar] at hfusion

structure Changes where
  fusedPaps : Nat := 0
  underSaturated : Nat := 0
  exactlySaturated : Nat := 0
  overSaturated : Nat := 0
  deriving BEq, Repr, Inhabited

def Changes.add (left right : Changes) : Changes :=
  { fusedPaps := left.fusedPaps + right.fusedPaps
    underSaturated := left.underSaturated + right.underSaturated
    exactlySaturated := left.exactlySaturated + right.exactlySaturated
    overSaturated := left.overSaturated + right.overSaturated }

def Changes.ofKind : Kind → Changes
  | .under => { fusedPaps := 1, underSaturated := 1 }
  | .exact => { fusedPaps := 1, exactlySaturated := 1 }
  | .over => { fusedPaps := 1, overSaturated := 1 }

structure Outcome where
  code : Code
  changes : Changes := {}

structure AlternativeOutcome where
  alternative : Alt
  changes : Changes := {}

mutual

/-- Mirror HPT transfer while fusing checked adjacent allocation sites.
Transfer failure is fail-soft for the affected subtree. -/
def runWithFacts (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef) (facts : List Fact) :
    Code → Outcome
  | input@(.ret _) => ⟨input, {}⟩
  | input@(.letOp (.papp function captured)
      (.letOp (.apply (.var 0) supplied) rest)) =>
      let pap := Op.papp function captured
      let apply := Op.apply (.var 0) supplied
      match analyzeOp declarations summaries owner current facts pap with
      | .error _ => ⟨input, {}⟩
      | .ok papFact =>
          let afterPap := papFact :: facts.map Fact.forgetHeap
          match analyzeOp declarations summaries owner current afterPap apply with
          | .error _ => ⟨input, {}⟩
          | .ok resultFact =>
              let afterApply := resultFact :: afterPap.map Fact.forgetHeap
              let nested := runWithFacts declarations summaries owner current
                afterApply rest
              match fusePair? declarations facts function captured supplied
                  nested.code with
              | some fusion =>
                  ⟨fusion.code, nested.changes.add (.ofKind fusion.kind)⟩
              | none =>
                  ⟨.letOp pap (.letOp apply nested.code), nested.changes⟩
  | input@(.letOp operation rest) =>
      match analyzeOp declarations summaries owner current facts operation with
      | .error _ => ⟨input, {}⟩
      | .ok bound =>
          let nested := runWithFacts declarations summaries owner current
            (bound :: facts.map Fact.forgetHeap) rest
          ⟨.letOp operation nested.code, nested.changes⟩
  | input@(.case scrutinee peelNat alternatives) =>
      match resolveAtomFact facts scrutinee with
      | .error _ => ⟨input, {}⟩
      | .ok fact =>
          let nested := alternatives.map
            (runAlternativeWithFacts declarations summaries owner current
              fact peelNat facts)
          ⟨.case scrutinee peelNat
              (nested.map fun result => result.alternative),
            nested.foldl
              (fun total result => total.add result.changes) {}⟩

def runAlternativeWithFacts (declarations : DeclEnv)
    (summaries : SummaryEnv) (owner : Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact) :
    Alt → AlternativeOutcome
  | .mk cidx fields body =>
      let nested := runWithFacts declarations summaries owner current
        (scrutineeFact.caseFields peelNat cidx fields ++ facts) body
      ⟨.mk cidx fields nested.code, nested.changes⟩

end

def runFunction (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef) : Outcome :=
  runWithFacts declarations summaries owner current
    (List.replicate current.arity Fact.top) current.body

def rewriteFunction (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef) : FnDef :=
  { current with body := (runFunction declarations summaries owner current).code }

def rewriteDeclaration (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) : Decl → Decl
  | .fn function => .fn (rewriteFunction declarations summaries owner function)
  | declaration@(.extern _) => declaration

@[simp] private theorem runAlternativeWithFacts_cidx
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact)
    (alternative : Alt) :
    (runAlternativeWithFacts declarations summaries owner current
      scrutineeFact peelNat facts alternative).alternative.cidx =
        alternative.cidx := by
  cases alternative
  simp [runAlternativeWithFacts, Alt.cidx]

private theorem runAlternativeWithFacts_predicate
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact)
    (index : Nat) :
    ((fun alternative : Alt => alternative.cidx == index) ∘
        (fun result : AlternativeOutcome => result.alternative) ∘
        runAlternativeWithFacts declarations summaries owner current
          scrutineeFact peelNat facts) =
      (fun alternative => alternative.cidx == index) := by
  funext alternative
  cases alternative
  simp [Function.comp_def, runAlternativeWithFacts, Alt.cidx]

private theorem find?_runAlternativeWithFacts
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef)
    (scrutineeFact : Fact) (peelNat : Bool) (facts : List Fact)
    (alternatives : Array Alt) (index : Nat) :
    ((alternatives.map
        (runAlternativeWithFacts declarations summaries owner current
          scrutineeFact peelNat facts)).map
        (fun result => result.alternative)).find?
          (fun alternative => alternative.cidx == index) =
      (alternatives.find? (fun alternative => alternative.cidx == index)).map
        (fun alternative =>
          (runAlternativeWithFacts declarations summaries owner current
            scrutineeFact peelNat facts alternative).alternative) := by
  rw [Array.map_map, Array.find?_map,
    runAlternativeWithFacts_predicate declarations summaries owner current
      scrutineeFact peelNat facts index]
  simp [Function.comp_def]

@[simp] theorem declArity_rewriteDeclaration
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (declaration : Decl) :
    declArity (rewriteDeclaration declarations summaries owner declaration) =
      declArity declaration := by
  cases declaration <;> rfl

/-! ## Checker facts used by the semantic layer -/

theorem scalar_of_scalarOnly_holds
    {declarations : DeclEnv} {store : Store} {fact : Fact} {value : RVal}
    (honly : scalarOnly fact = true)
    (hholds : fact.Holds declarations store value) :
    value.isScalar = true := by
  unfold scalarOnly at honly
  simp only [Bool.and_eq_true] at honly
  cases value with
  | lit literal => rfl
  | erased => rfl
  | loc location =>
      simp only [Fact.Holds] at hholds
      rcases hholds with hunknown | ⟨shape, hmember, _⟩
      · have hfalse : fact.unknownHeap = false := by
          simpa using honly.1
        rw [hfalse] at hunknown
        contradiction
      · have hempty : fact.shapes = [] := List.isEmpty_iff.mp honly.2
        rw [hempty] at hmember
        contradiction

private theorem environment_allScalar_of_all_scalarOnly
    {declarations : DeclEnv} {store : Store} :
    ∀ {facts : List Fact} {values : List RVal},
      EnvironmentHolds declarations store facts values →
      facts.all scalarOnly = true → values.all RVal.isScalar = true
  | [], [], .nil, _ => rfl
  | fact :: facts, value :: values, .cons hhead htail, hall => by
      simp only [List.all_cons, Bool.and_eq_true] at hall ⊢
      exact ⟨scalar_of_scalarOnly_holds hall.1 hhead,
        environment_allScalar_of_all_scalarOnly htail hall.2⟩

private theorem allScalar_of_scalarCaptures
    {declarations : DeclEnv} {store : Store} {facts : List Fact}
    {environment : List RVal} {captured : Array Atom}
    {values : List RVal}
    (henvironment : EnvironmentHolds declarations store facts environment)
    (hcheck : scalarCaptures facts captured = true)
    (hresolve : resolveAtoms environment captured = .ok values) :
    values.all RVal.isScalar = true := by
  unfold scalarCaptures at hcheck
  cases habstract : resolveAtomFacts facts captured with
  | error error => simp [habstract] at hcheck
  | ok captureFacts =>
      simp only [habstract] at hcheck
      have hholds := resolveAtomFacts_sound henvironment habstract hresolve
      exact environment_allScalar_of_all_scalarOnly hholds hcheck

private theorem continue_historyIso {ctx : Ctx} {fuel : Nat}
    {current : FnDef} {left right : Store}
    (heap : HeapHistoryIso left right)
    {leftValue rightValue retired alias : RVal}
    {leftEnvironment rightEnvironment : List RVal}
    (hvalue : RValIso heap.locRel leftValue rightValue)
    (henvironment : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    {rest : Code} (hrest : CodeNoUse 1 rest)
    {leftOut : Store × RVal}
    (hrun : runCode ctx fuel current left
      (leftValue :: retired :: leftEnvironment) rest = .ok leftOut) :
    ∃ rightOut,
      runCode ctx fuel current right
          (rightValue :: alias :: rightEnvironment) rest = .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  have hleftAgree := EnvsAgreeExcept.second leftValue retired .erased
    leftEnvironment
  have hleftScrubbed : runCode ctx fuel current left
      (leftValue :: .erased :: leftEnvironment) rest = .ok leftOut := by
    rw [← runCode_env_eq_of_noUse fuel current left 1
      (leftValue :: retired :: leftEnvironment)
      (leftValue :: .erased :: leftEnvironment) rest hleftAgree hrest]
    exact hrun
  have hscrubbedEnvironment : RValsIso heap.locRel
      (leftValue :: .erased :: leftEnvironment)
      (rightValue :: .erased :: rightEnvironment) :=
    .cons hvalue (.cons .erased henvironment)
  obtain ⟨rightOut, hrightScrubbed, hresult⟩ :=
    runCode_historyIso heap hscrubbedEnvironment hleftScrubbed
  have hrightAgree := EnvsAgreeExcept.second rightValue .erased alias
    rightEnvironment
  have hright : runCode ctx fuel current right
      (rightValue :: alias :: rightEnvironment) rest = .ok rightOut := by
    rw [← runCode_env_eq_of_noUse fuel current right 1
      (rightValue :: .erased :: rightEnvironment)
      (rightValue :: alias :: rightEnvironment) rest hrightAgree hrest]
    exact hrightScrubbed
  exact ⟨rightOut, hright, hresult⟩

private theorem lowerAtom?_resolveAtom {head : RVal} {environment : List RVal}
    {source target : Atom} {value : RVal}
    (hlower : lowerAtom? source = some target)
    (hresolve : resolveAtom (head :: environment) source = .ok value) :
    resolveAtom environment target = .ok value := by
  cases source with
  | lit literal =>
      simp only [lowerAtom?, Option.some.injEq] at hlower
      subst target
      simpa [resolveAtom] using hresolve
  | erased =>
      simp only [lowerAtom?, Option.some.injEq] at hlower
      subst target
      simpa [resolveAtom] using hresolve
  | var index =>
      cases index with
      | zero => simp [lowerAtom?] at hlower
      | succ index =>
          simp only [lowerAtom?, Option.some.injEq] at hlower
          subst target
          simp only [resolveAtom] at hresolve ⊢
          cases hget : environment[index]? with
          | none => simp [hget] at hresolve
          | some found => simpa [hget] using hresolve

private theorem List.resolveLoweredFrom_eq (head : RVal)
    (environment : List RVal) :
    ∀ (source target : List Atom) (accumulator output : List RVal),
      source.mapM lowerAtom? = some target →
      source.foldlM
          (fun values atom => do
            pure (values ++ [← resolveAtom (head :: environment) atom]))
          accumulator = .ok output →
        target.foldlM
          (fun values atom => do
            pure (values ++ [← resolveAtom environment atom]))
          accumulator = .ok output := by
  intro source
  induction source with
  | nil =>
      intro target accumulator output hlower hresolve
      change some [] = some target at hlower
      injection hlower with htarget
      subst target
      exact hresolve
  | cons atom source ih =>
      intro target accumulator output hlower hresolve
      simp only [List.mapM_cons] at hlower
      cases hatom : lowerAtom? atom with
      | none => simp [hatom] at hlower
      | some lowered =>
          rw [hatom] at hlower
          simp only [bind, Option.bind] at hlower
          cases htail : source.mapM lowerAtom? with
          | none => simp [htail] at hlower
          | some loweredTail =>
              rw [htail] at hlower
              change some (lowered :: loweredTail) = some target at hlower
              injection hlower with htarget
              subst target
              simp only [List.foldlM_cons] at hresolve ⊢
              cases hsource : resolveAtom (head :: environment) atom with
              | error error =>
                  rw [hsource] at hresolve
                  simp only [bind, Except.bind] at hresolve
                  contradiction
              | ok value =>
                  rw [hsource] at hresolve
                  simp only [bind, Except.bind] at hresolve
                  have htargetResolve := lowerAtom?_resolveAtom hatom hsource
                  rw [htargetResolve]
                  simp only [bind, Except.bind]
                  exact ih loweredTail (accumulator ++ [value]) output htail
                    hresolve

theorem lowerAtoms?_resolveAtoms {head : RVal} {environment : List RVal}
    {source target : Array Atom} {values : List RVal}
    (hlower : lowerAtoms? source = some target)
    (hresolve : resolveAtoms (head :: environment) source = .ok values) :
    resolveAtoms environment target = .ok values := by
  unfold lowerAtoms? at hlower
  cases hmap : source.toList.mapM lowerAtom? with
  | none => simp [hmap] at hlower
  | some lowered =>
      simp only [hmap, Option.map_some, Option.some.injEq] at hlower
      subst target
      unfold resolveAtoms at hresolve ⊢
      rw [← Array.foldlM_toList] at hresolve
      rw [← Array.foldlM_toList]
      simp only
      exact List.resolveLoweredFrom_eq head environment source.toList lowered
        [] values hmap hresolve

private theorem lowerAtom?_notUseZero {source target : Atom}
    (hlower : lowerAtom? source = some target) :
    atomUsesVar 0 source = false := by
  cases source with
  | lit literal => rfl
  | erased => rfl
  | var index =>
      cases index with
      | zero => simp [lowerAtom?] at hlower
      | succ index => simp [atomUsesVar]

private theorem List.all_notUseZero_of_mapM_lower :
    ∀ {source target : List Atom}, source.mapM lowerAtom? = some target →
      source.all (fun atom => !atomUsesVar 0 atom) = true := by
  intro source
  induction source with
  | nil => intro target hlower; rfl
  | cons atom source ih =>
      intro target hlower
      simp only [List.mapM_cons] at hlower
      cases hatom : lowerAtom? atom with
      | none => simp [hatom] at hlower
      | some lowered =>
          rw [hatom] at hlower
          simp only [bind, Option.bind] at hlower
          cases htail : source.mapM lowerAtom? with
          | none => simp [htail] at hlower
          | some loweredTail =>
              have hhead := lowerAtom?_notUseZero hatom
              simp only [List.all_cons, Bool.and_eq_true]
              exact ⟨by simp [hhead], ih htail⟩

theorem lowerAtoms?_notUseZero {source target : Array Atom}
    (hlower : lowerAtoms? source = some target) :
    atomsUseVar 0 source = false := by
  unfold lowerAtoms? at hlower
  cases hmap : source.toList.mapM lowerAtom? with
  | none => simp [hmap] at hlower
  | some lowered =>
      have hall := List.all_notUseZero_of_mapM_lower hmap
      unfold atomsUseVar
      rw [Array.any_eq_false']
      intro atom hatom huses
      have hnot := List.all_eq_true.mp hall atom (by simpa using hatom)
      simp [huses] at hnot

private def resolveStep (environment : List RVal)
    (values : List RVal) (atom : Atom) : Except Err (List RVal) := do
  pure (values ++ [← resolveAtom environment atom])

private inductive AtomsResolve (environment : List RVal) :
    List Atom → List RVal → Prop where
  | nil : AtomsResolve environment [] []
  | cons (hhead : resolveAtom environment atom = .ok value)
      (htail : AtomsResolve environment atoms values) :
      AtomsResolve environment (atom :: atoms) (value :: values)

namespace AtomsResolve

private theorem foldlM {environment : List RVal} :
    ∀ {atoms values}, AtomsResolve environment atoms values →
      ∀ accumulator,
        atoms.foldlM (resolveStep environment) accumulator =
          .ok (accumulator ++ values)
  | [], [], .nil, accumulator => by
      simp only [List.foldlM_nil, pure, Except.pure, List.append_nil]
  | atom :: atoms, value :: values, .cons hhead htail, accumulator => by
      have hstep : resolveStep environment accumulator atom =
          .ok (accumulator ++ [value]) := by
        simp [resolveStep, hhead, bind, Except.bind, pure, Except.pure]
      rw [List.foldlM_cons, hstep]
      simp only [bind, Except.bind]
      rw [htail.foldlM (accumulator ++ [value])]
      simp [List.append_assoc]

private theorem ofFoldlM {environment : List RVal} :
  ∀ atoms accumulator output,
      atoms.foldlM (resolveStep environment) accumulator = .ok output →
      ∃ values, AtomsResolve environment atoms values ∧
        output = accumulator ++ values := by
  intro atoms
  induction atoms with
  | nil =>
      intro accumulator output hrun
      simp only [List.foldlM_nil, pure, Except.pure] at hrun
      injection hrun with houtput
      subst output
      exact ⟨[], .nil, by simp⟩
  | cons atom atoms ih =>
      intro accumulator output hrun
      simp only [List.foldlM_cons] at hrun
      cases hhead : resolveAtom environment atom with
      | error error =>
          have hstep : resolveStep environment accumulator atom =
              .error error := by
            simp [resolveStep, hhead, bind, Except.bind]
          rw [hstep] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok value =>
          have hstep : resolveStep environment accumulator atom =
              .ok (accumulator ++ [value]) := by
            simp [resolveStep, hhead, bind, Except.bind, pure, Except.pure]
          rw [hstep] at hrun
          simp only [bind, Except.bind] at hrun
          obtain ⟨values, hvalues, houtput⟩ :=
            ih (accumulator ++ [value]) output hrun
          refine ⟨value :: values, .cons hhead hvalues, ?_⟩
          rw [houtput]
          simp [List.append_assoc]

theorem length {environment : List RVal} {atoms : List Atom}
    {values : List RVal} (h : AtomsResolve environment atoms values) :
    values.length = atoms.length := by
  induction h <;> simp_all

theorem append {environment : List RVal}
    {leftAtoms rightAtoms : List Atom} {leftValues rightValues : List RVal}
    (left : AtomsResolve environment leftAtoms leftValues)
    (right : AtomsResolve environment rightAtoms rightValues) :
    AtomsResolve environment (leftAtoms ++ rightAtoms)
      (leftValues ++ rightValues) := by
  induction left with
  | nil => exact right
  | cons hhead htail ih => exact .cons hhead ih

theorem take {environment : List RVal} {atoms : List Atom}
    {values : List RVal} (h : AtomsResolve environment atoms values)
    (count : Nat) :
    AtomsResolve environment (atoms.take count) (values.take count) := by
  induction h generalizing count with
  | nil => simpa using (AtomsResolve.nil (environment := environment))
  | cons hhead htail ih =>
      cases count with
      | zero => exact .nil
      | succ count => exact .cons hhead (ih count)

theorem drop {environment : List RVal} {atoms : List Atom}
    {values : List RVal} (h : AtomsResolve environment atoms values)
    (count : Nat) :
    AtomsResolve environment (atoms.drop count) (values.drop count) := by
  induction h generalizing count with
  | nil => simpa using (AtomsResolve.nil (environment := environment))
  | cons hhead htail ih =>
      cases count with
      | zero => exact .cons hhead htail
      | succ count => exact ih count

end AtomsResolve

private theorem atomsResolve_of_resolveAtoms {environment : List RVal}
    {atoms : Array Atom} {values : List RVal}
    (hrun : resolveAtoms environment atoms = .ok values) :
    AtomsResolve environment atoms.toList values := by
  unfold resolveAtoms at hrun
  rw [← Array.foldlM_toList] at hrun
  change atoms.toList.foldlM (resolveStep environment) [] =
    .ok values at hrun
  obtain ⟨found, hfound, hvalues⟩ :=
    AtomsResolve.ofFoldlM atoms.toList [] values hrun
  simp only [List.nil_append] at hvalues
  subst found
  exact hfound

private theorem resolveAtoms_of_atomsResolve {environment : List RVal}
    {atoms : Array Atom} {values : List RVal}
    (h : AtomsResolve environment atoms.toList values) :
    resolveAtoms environment atoms = .ok values := by
  unfold resolveAtoms
  rw [← Array.foldlM_toList]
  change atoms.toList.foldlM (resolveStep environment) [] = .ok values
  simpa using h.foldlM []

private theorem resolveAtoms_length {environment : List RVal}
    {atoms : Array Atom} {values : List RVal}
    (hrun : resolveAtoms environment atoms = .ok values) :
    values.length = atoms.size := by
  simpa using (atomsResolve_of_resolveAtoms hrun).length

private theorem resolveAtoms_take {environment : List RVal}
    {atoms : List Atom} {values : List RVal}
    (hrun : resolveAtoms environment atoms.toArray = .ok values)
    (count : Nat) :
    resolveAtoms environment (atoms.take count).toArray =
      .ok (values.take count) := by
  apply resolveAtoms_of_atomsResolve
  simpa using (atomsResolve_of_resolveAtoms hrun).take count

private theorem resolveAtoms_drop {environment : List RVal}
    {atoms : List Atom} {values : List RVal}
    (hrun : resolveAtoms environment atoms.toArray = .ok values)
    (count : Nat) :
    resolveAtoms environment (atoms.drop count).toArray =
      .ok (values.drop count) := by
  apply resolveAtoms_of_atomsResolve
  simpa using (atomsResolve_of_resolveAtoms hrun).drop count

private theorem resolveAtoms_append {environment : List RVal}
    {left right : List Atom} {leftValues rightValues : List RVal}
    (hleft : resolveAtoms environment left.toArray = .ok leftValues)
    (hright : resolveAtoms environment right.toArray = .ok rightValues) :
    resolveAtoms environment (left ++ right).toArray =
      .ok (leftValues ++ rightValues) := by
  apply resolveAtoms_of_atomsResolve
  simpa using (atomsResolve_of_resolveAtoms hleft).append
    (atomsResolve_of_resolveAtoms hright)

private theorem resolveAtom_selfIso {rel : Nat → Nat → Prop}
    {environment : List RVal} (henvironment : RValsIso rel environment environment)
    {atom : Atom} {value : RVal}
    (hresolve : resolveAtom environment atom = .ok value) :
    RValIso rel value value := by
  cases atom with
  | lit literal =>
      simp only [resolveAtom, Except.ok.injEq] at hresolve
      subst value
      exact .lit
  | erased =>
      simp only [resolveAtom, Except.ok.injEq] at hresolve
      subst value
      exact .erased
  | var index =>
      simp only [resolveAtom] at hresolve
      cases hget : environment[index]? with
      | none => simp [hget] at hresolve
      | some found =>
          simp only [hget, Except.ok.injEq] at hresolve
          subst value
          obtain ⟨other, hother, hiso⟩ := henvironment.get? hget
          have hsame : other = found := Option.some.inj (hother.symm.trans hget)
          subst other
          exact hiso

private theorem AtomsResolve.selfIso {rel : Nat → Nat → Prop}
    {environment : List RVal} (henvironment : RValsIso rel environment environment) :
    ∀ {atoms values}, AtomsResolve environment atoms values →
      RValsIso rel values values
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hhead htail =>
      .cons (resolveAtom_selfIso henvironment hhead)
        (selfIso henvironment htail)

private theorem runHistoryIso_weaken
    {earlierLeft earlierRight left right : Store}
    {earlier : HeapHistoryIso earlierLeft earlierRight}
    {before : HeapHistoryIso left right}
    (hearlier : earlier.Extends before)
    {leftOut rightOut : Store × RVal}
    (hrun : RunHistoryIso before leftOut rightOut) :
    RunHistoryIso earlier leftOut rightOut := by
  obtain ⟨heap, hextends, hvalue⟩ := hrun
  exact ⟨heap, hearlier.trans hextends, hvalue⟩

private structure PairRunAt (ctx : Ctx) (fuel : Nat) (current : FnDef)
    (store : Store) (environment : List RVal) (function : Address)
    (declaration : Decl) (captured supplied : Array Atom) (rest : Code)
    (out : Store × RVal) where
  capturedValues : List RVal
  suppliedValues : List RVal
  resultStore : Store
  resultValue : RVal
  capturedResolve : resolveAtoms environment captured = .ok capturedValues
  suppliedResolve :
    let allocated := store.allocNode .shared
      (.papN function (declArity declaration) capturedValues.toArray)
    resolveAtoms (.loc allocated.2 :: environment) supplied =
      .ok suppliedValues
  applyRun :
    let allocated := store.allocNode .shared
      (.papN function (declArity declaration) capturedValues.toArray)
    applyGo ctx (fuel + 1) allocated.1 (.loc allocated.2) suppliedValues =
      .ok (resultStore, resultValue)
  restRun :
    let allocated := store.allocNode .shared
      (.papN function (declArity declaration) capturedValues.toArray)
    runCode ctx (fuel + 2) current resultStore
      (resultValue :: .loc allocated.2 :: environment) rest = .ok out

private def pairRunAt_of_run
    {ctx : Ctx} {fuel : Nat} {current : FnDef} {store : Store}
    {environment : List RVal} {function : Address}
    {captured supplied : Array Atom} {rest : Code}
    {declaration : Decl} {out : Store × RVal}
    (hdeclaration : ctx.decls function = some declaration)
    (hcapture : captured.size < declArity declaration)
    (hrun : runCode ctx (fuel + 4) current store environment
      (.letOp (.papp function captured)
        (.letOp (.apply (.var 0) supplied) rest)) = .ok out) :
    PairRunAt ctx fuel current store environment function declaration captured
      supplied rest out := by
  rw [runCode.eq_def] at hrun
  dsimp only at hrun
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  cases hcaptured : resolveAtoms environment captured with
  | error error =>
      rw [hcaptured] at hrun
      simp only [bind, Except.bind] at hrun
      contradiction
  | ok capturedValues =>
      rw [hcaptured] at hrun
      simp only [bind, Except.bind] at hrun
      rw [hdeclaration] at hrun
      have hcapturedLength := resolveAtoms_length hcaptured
      have hproper : capturedValues.length < declArity declaration := by
        omega
      simp only [hproper, if_true, bind, Except.bind] at hrun
      rw [runCode.eq_def] at hrun
      dsimp only at hrun
      rw [runOp.eq_def] at hrun
      dsimp only at hrun
      simp only [resolveAtom, List.getElem?_cons_zero, bind, Except.bind] at hrun
      let allocated := store.allocNode .shared
        (.papN function (declArity declaration) capturedValues.toArray)
      cases hsupplied : resolveAtoms (.loc allocated.2 :: environment) supplied with
      | error error =>
          rw [hsupplied] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok suppliedValues =>
          rw [hsupplied] at hrun
          simp only [bind, Except.bind] at hrun
          cases happly : applyGo ctx (fuel + 1) allocated.1
              (.loc allocated.2) suppliedValues with
          | error error =>
              rw [happly] at hrun
              simp only [bind, Except.bind] at hrun
              contradiction
          | ok result =>
              rcases result with ⟨resultStore, resultValue⟩
              rw [happly] at hrun
              simp only [bind, Except.bind] at hrun
              refine
                { capturedValues := capturedValues
                  suppliedValues := suppliedValues
                  resultStore := resultStore
                  resultValue := resultValue
                  capturedResolve := hcaptured
                  suppliedResolve := ?_
                  applyRun := ?_
                  restRun := ?_ }
              · simpa [allocated] using hsupplied
              · simpa [allocated] using happly
              · simpa [allocated] using hrun

private theorem dupVals_eq_of_all_scalar {store : Store} :
    ∀ {values : List RVal}, values.all RVal.isScalar = true →
      dupVals store values = .ok store
  | [], _ => rfl
  | value :: values, hscalar => by
      simp only [List.all_cons, Bool.and_eq_true] at hscalar
      cases value with
      | loc location => simp [RVal.isScalar] at hscalar
      | lit literal =>
          simp only [dupVals, List.foldlM_cons]
          exact dupVals_eq_of_all_scalar hscalar.2
      | erased =>
          simp only [dupVals, List.foldlM_cons]
          exact dupVals_eq_of_all_scalar hscalar.2

private theorem dropMany_eq_of_all_scalar {ctx : Ctx} :
    ∀ fuel store values out,
      values.all RVal.isScalar = true →
      dropMany ctx fuel store values = .ok out → out = store := by
  intro fuel
  induction fuel with
  | zero =>
      intro store values out hscalar hrun
      simp [dropMany] at hrun
  | succ fuel smaller =>
      intro store values out hscalar hrun
      cases values with
      | nil =>
          simp only [dropMany, Except.ok.injEq] at hrun
          exact hrun.symm
      | cons value values =>
          simp only [List.all_cons, Bool.and_eq_true] at hscalar
          cases value with
          | loc location => simp [RVal.isScalar] at hscalar
          | lit literal =>
              cases fuel with
              | zero =>
                  simp only [dropMany, dropVal, bind, Except.bind] at hrun
                  contradiction
              | succ fuel =>
                  simp only [dropMany, dropVal, bind, Except.bind] at hrun
                  exact smaller store values out hscalar.2 hrun
          | erased =>
              cases fuel with
              | zero =>
                  simp only [dropMany, dropVal, bind, Except.bind] at hrun
                  contradiction
              | succ fuel =>
                  simp only [dropMany, dropVal, bind, Except.bind] at hrun
                  exact smaller store values out hscalar.2 hrun

private theorem dropFreshPap_nodes {ctx : Ctx} {fuel : Nat} {store out : Store}
    {function : Address} {arity : Nat} {arguments : List RVal}
    (hscalar : arguments.all RVal.isScalar = true)
    (hrun :
      let allocated := store.allocNode .shared
        (.papN function arity arguments.toArray)
      dropVal ctx fuel allocated.1 (.loc allocated.2) = .ok out) :
    out.nodes =
      (let allocated := store.allocNode .shared
        (.papN function arity arguments.toArray)
       allocated.1.kill allocated.2).nodes := by
  cases fuel with
  | zero => simp [dropVal] at hrun
  | succ fuel =>
      simp only [dropVal] at hrun
      simp [Store.allocNode, Store.get?] at hrun
      have hout := dropMany_eq_of_all_scalar fuel
        ((store.allocNode .shared
          (.papN function arity arguments.toArray)).1.rcTick.kill
            (store.allocNode .shared
              (.papN function arity arguments.toArray)).2)
        arguments out hscalar hrun
      subst out
      rfl

private structure FreshApplyReady (ctx : Ctx) (fuel : Nat)
    (store : Store) (function : Address) (arity : Nat)
    (capturedValues suppliedValues : List RVal)
    (out : Store × RVal) where
  ready : Store
  dropRun :
    let allocated := store.allocNode .shared
      (.papN function arity capturedValues.toArray)
    dropVal ctx fuel allocated.1 (.loc allocated.2) = .ok ready
  readyNodes :
    let allocated := store.allocNode .shared
      (.papN function arity capturedValues.toArray)
    ready.nodes = (allocated.1.kill allocated.2).nodes
  remainderRun :
    (let total := capturedValues ++ suppliedValues
     if total.length < arity then
       let (next, location) := ready.allocNode .shared
         (.papN function arity total.toArray)
       Except.ok (next, .loc location)
     else if total.length == arity then
       match ctx.decls function with
       | none => Except.error (Err.unknownRef function)
       | some declaration =>
         if declPapSafe declaration then
           invoke ctx fuel function total ready
         else Except.error (.stuck "shared pap targets a non-pap-safe declaration")
     else
       match ctx.decls function with
       | none => Except.error (Err.unknownRef function)
       | some declaration =>
         if declPapSafe declaration then do
           let (called, value) ← invoke ctx fuel function (total.take arity) ready
           applyGo ctx fuel called value (total.drop arity)
         else Except.error (.stuck "shared pap targets a non-pap-safe declaration")) =
      Except.ok out

private def freshApplyReady_of_run
    {ctx : Ctx} {fuel : Nat} {store : Store} {function : Address}
    {arity : Nat} {capturedValues suppliedValues : List RVal}
    {out : Store × RVal}
    (hscalar : capturedValues.all RVal.isScalar = true)
    (hrun :
      let allocated := store.allocNode .shared
        (.papN function arity capturedValues.toArray)
      applyGo ctx (fuel + 1) allocated.1 (.loc allocated.2) suppliedValues =
        .ok out) :
    FreshApplyReady ctx fuel store function arity capturedValues suppliedValues
      out := by
  let allocated := store.allocNode .shared
    (.papN function arity capturedValues.toArray)
  change applyGo ctx (fuel + 1) allocated.1 (.loc allocated.2)
    suppliedValues = .ok out at hrun
  rw [applyGo.eq_def] at hrun
  dsimp only at hrun
  have hget : allocated.1.get? allocated.2 =
      some ⟨.shared, 1, .papN function arity capturedValues.toArray⟩ := by
    simp [allocated, Store.allocNode, Store.get?]
  rw [hget] at hrun
  dsimp only at hrun
  rw [dupVals_eq_of_all_scalar hscalar] at hrun
  simp only [bind, Except.bind] at hrun
  cases hdrop : dropVal ctx fuel allocated.1 (.loc allocated.2) with
  | error error =>
      rw [hdrop] at hrun
      simp only [bind, Except.bind] at hrun
      contradiction
  | ok ready =>
      rw [hdrop] at hrun
      simp only [bind, Except.bind] at hrun
      exact
        { ready := ready
          dropRun := by simpa [allocated] using hdrop
          readyNodes := by
            exact dropFreshPap_nodes hscalar (by simpa [allocated] using hdrop)
          remainderRun := hrun }

private theorem List.drop_append_after_prefix :
    ∀ (front suffix : List α) (count : Nat), front.length ≤ count →
      (front ++ suffix).drop count = suffix.drop (count - front.length) := by
  intro front
  induction front with
  | nil => intro suffix count hle; simp
  | cons head tail ih =>
      intro suffix count hle
      cases count with
      | zero => simp at hle
      | succ count =>
          have htail : tail.length ≤ count := by
            simpa using hle
          simp only [List.cons_append, List.drop_succ_cons, List.length_cons,
            Nat.succ_sub_succ_eq_sub]
          exact ih suffix count htail

/-! ## Local semantic refinement

The source and replacement use the same outer fuel.  The source's retired
PAP allocation is omitted from the right-hand heap history; subsequent
allocations and calls are related by the evaluator congruence theorem. -/

private theorem fuseSpec_refinesAt
    {ctx : Ctx} {fuel : Nat} {current : FnDef} {store : Store}
    {environment : List RVal} {declarations : DeclEnv} {facts : List Fact}
    {function : Address} {captured supplied : Array Atom} {rest : Code}
    {fusion : Fusion} {out : Store × RVal}
    (hctx : ctx.decls = declarations)
    (base : HeapHistoryIso store store)
    (henvIso : RValsIso base.locRel environment environment)
    (henvironment : EnvironmentHolds declarations store facts environment)
    (hspec : FuseSpec declarations facts function captured supplied rest
      fusion)
    (hrun : runCode ctx (fuel + 4) current store environment
      (.letOp (.papp function captured)
        (.letOp (.apply (.var 0) supplied) rest)) = .ok out) :
    ∃ targetOut,
      runCode ctx (fuel + 4) current store environment fusion.code =
          .ok targetOut ∧
        RunHistoryIso base out targetOut := by
  cases hspec with
  | @under declaration lowered hdeclaration hcaptureArity hscalar hrest
      hlowered hunder =>
      have hctxDeclaration : ctx.decls function = some declaration := by
        simpa [hctx] using hdeclaration
      obtain ⟨capturedValues, suppliedValues, resultStore, resultValue,
          hcaptured, hsupplied, happly, hrestRun⟩ :=
        pairRunAt_of_run hctxDeclaration hcaptureArity hrun
      have hscalarValues :=
        allScalar_of_scalarCaptures henvironment hscalar hcaptured
      obtain ⟨ready, hdrop, hreadyNodes, hremainder⟩ :=
        freshApplyReady_of_run hscalarValues happly
      let allocated := store.allocNode .shared
        (.papN function (declArity declaration) capturedValues.toArray)
      have hsupplied' : resolveAtoms (.loc allocated.2 :: environment)
          supplied = .ok suppliedValues := by
        simpa [allocated] using hsupplied
      have hloweredResolve : resolveAtoms environment lowered =
          .ok suppliedValues :=
        lowerAtoms?_resolveAtoms hlowered hsupplied'
      have hcombinedResolve :
          resolveAtoms environment
              (captured.toList ++ lowered.toList).toArray =
            .ok (capturedValues ++ suppliedValues) := by
        exact resolveAtoms_append (by simpa using hcaptured)
          (by simpa using hloweredResolve)
      have hcapturedLength : capturedValues.length = captured.size :=
        resolveAtoms_length hcaptured
      have hloweredLength : suppliedValues.length = lowered.size :=
        resolveAtoms_length hloweredResolve
      have htotalUnder :
          (capturedValues ++ suppliedValues).length <
            declArity declaration := by
        simpa [List.length_append, hcapturedLength, hloweredLength] using hunder
      have htotalUnder' : capturedValues.length + suppliedValues.length <
          declArity declaration := by
        simpa using htotalUnder
      let sourceAllocated := ready.allocNode .shared
        (.papN function (declArity declaration)
          (capturedValues ++ suppliedValues).toArray)
      have hremainder' :
          (.ok (sourceAllocated.1, .loc sourceAllocated.2) :
              Except Err (Store × RVal)) =
            .ok (resultStore, resultValue) := by
        simpa [sourceAllocated, htotalUnder'] using hremainder
      have hresultPair :
          (sourceAllocated.1, .loc sourceAllocated.2) =
            (resultStore, resultValue) := Except.ok.inj hremainder'
      have hresultStore : resultStore = sourceAllocated.1 := by
        exact (congrArg Prod.fst hresultPair).symm
      have hresultValue : resultValue = .loc sourceAllocated.2 := by
        exact (congrArg Prod.snd hresultPair).symm
      subst resultStore
      subst resultValue
      let omitted := base.omitDeadAllocLeft .shared
        (.papN function (declArity declaration) capturedValues.toArray)
      let readyHeap : HeapHistoryIso ready store :=
        omitted.nodesEq hreadyNodes rfl
      have henvReady : RValsIso readyHeap.locRel environment environment := by
        change RValsIso base.locRel environment environment
        exact henvIso
      have hcapturedIso : RValsIso readyHeap.locRel
          capturedValues capturedValues := by
        change RValsIso base.locRel capturedValues capturedValues
        exact (atomsResolve_of_resolveAtoms hcaptured).selfIso henvIso
      have hloweredIso : RValsIso readyHeap.locRel
          suppliedValues suppliedValues := by
        change RValsIso base.locRel suppliedValues suppliedValues
        exact (atomsResolve_of_resolveAtoms hloweredResolve).selfIso henvIso
      have htotalIso : RValsIso readyHeap.locRel
          (capturedValues ++ suppliedValues)
          (capturedValues ++ suppliedValues) :=
        hcapturedIso.append hloweredIso
      let targetAllocated := store.allocNode .shared
        (.papN function (declArity declaration)
          (capturedValues ++ suppliedValues).toArray)
      let finalHeap : HeapHistoryIso sourceAllocated.1 targetAllocated.1 :=
        readyHeap.alloc (.pap (by simpa using htotalIso))
      have hvalueIso : RValIso finalHeap.locRel
          (.loc sourceAllocated.2) (.loc targetAllocated.2) := by
        exact .loc (.inl ⟨rfl, rfl⟩)
      have henvFinal : RValsIso finalHeap.locRel
          environment environment :=
        henvReady.mono (fun h => .inr h)
      obtain ⟨targetOut, htargetRest, hrestIso⟩ :=
        continue_historyIso finalHeap hvalueIso henvFinal
          (codeNoUse_of_codeUsesVar_eq_false hrest) hrestRun
      have htargetOuter : runOp ctx (fuel + 3) current store environment
          (.papp function
            (captured.toList ++ lowered.toList).toArray) =
          .ok (targetAllocated.1, .loc targetAllocated.2) := by
        rw [runOp.eq_def]
        dsimp only
        rw [hcombinedResolve]
        simp only [bind, Except.bind]
        rw [hctxDeclaration]
        simp only [htotalUnder, if_true]
        rfl
      have htargetInner : runOp ctx (fuel + 2) current targetAllocated.1
          (.loc targetAllocated.2 :: environment) (.pure (.var 0)) =
          .ok (targetAllocated.1, .loc targetAllocated.2) := by
        rw [runOp.eq_def]
        rfl
      have htargetRun : runCode ctx (fuel + 4) current store environment
          (.letOp
            (.papp function
              (captured.toList ++ lowered.toList).toArray)
            (.letOp (.pure (.var 0)) rest)) = .ok targetOut := by
        rw [runCode.eq_def]
        dsimp only
        rw [htargetOuter]
        simp only [bind, Except.bind]
        rw [runCode.eq_def]
        dsimp only
        rw [htargetInner]
        simp only [bind, Except.bind]
        exact htargetRest
      refine ⟨targetOut, htargetRun, ?_⟩
      change RunHistoryIso base out targetOut
      apply runHistoryIso_weaken (earlier := base) (before := finalHeap)
        (hrun := hrestIso)
      intro left right hrel
      exact .inr hrel
  | @exact declaration lowered hdeclaration hcaptureArity hscalar hrest
      hlowered hexact =>
      have hctxDeclaration : ctx.decls function = some declaration := by
        simpa [hctx] using hdeclaration
      obtain ⟨capturedValues, suppliedValues, resultStore, resultValue,
          hcaptured, hsupplied, happly, hrestRun⟩ :=
        pairRunAt_of_run hctxDeclaration hcaptureArity hrun
      have hscalarValues :=
        allScalar_of_scalarCaptures henvironment hscalar hcaptured
      obtain ⟨ready, hdrop, hreadyNodes, hremainder⟩ :=
        freshApplyReady_of_run hscalarValues happly
      let allocated := store.allocNode .shared
        (.papN function (declArity declaration) capturedValues.toArray)
      have hsupplied' : resolveAtoms (.loc allocated.2 :: environment)
          supplied = .ok suppliedValues := by
        simpa [allocated] using hsupplied
      have hloweredResolve : resolveAtoms environment lowered =
          .ok suppliedValues :=
        lowerAtoms?_resolveAtoms hlowered hsupplied'
      have hcombinedResolve :
          resolveAtoms environment
              (captured.toList ++ lowered.toList).toArray =
            .ok (capturedValues ++ suppliedValues) := by
        exact resolveAtoms_append (by simpa using hcaptured)
          (by simpa using hloweredResolve)
      have hcapturedLength : capturedValues.length = captured.size :=
        resolveAtoms_length hcaptured
      have hloweredLength : suppliedValues.length = lowered.size :=
        resolveAtoms_length hloweredResolve
      have htotalExact :
          (capturedValues ++ suppliedValues).length =
            declArity declaration := by
        simpa [List.length_append, hcapturedLength, hloweredLength] using hexact
      have htotalExact' : capturedValues.length + suppliedValues.length =
          declArity declaration := by
        simpa using htotalExact
      have hpapsafe : declPapSafe declaration = true := by
        cases hpapsafe : declPapSafe declaration with
        | false =>
            simp [htotalExact', hctxDeclaration, hpapsafe] at hremainder
        | true => rfl
      have hremainder' : invoke ctx fuel function
          (capturedValues ++ suppliedValues) ready =
            .ok (resultStore, resultValue) := by
        simpa [htotalExact', hctxDeclaration, hpapsafe] using hremainder
      let omitted := base.omitDeadAllocLeft .shared
        (.papN function (declArity declaration) capturedValues.toArray)
      let readyHeap : HeapHistoryIso ready store :=
        omitted.nodesEq hreadyNodes rfl
      have henvReady : RValsIso readyHeap.locRel environment environment := by
        change RValsIso base.locRel environment environment
        exact henvIso
      have hcapturedIso : RValsIso readyHeap.locRel
          capturedValues capturedValues := by
        change RValsIso base.locRel capturedValues capturedValues
        exact (atomsResolve_of_resolveAtoms hcaptured).selfIso henvIso
      have hloweredIso : RValsIso readyHeap.locRel
          suppliedValues suppliedValues := by
        change RValsIso base.locRel suppliedValues suppliedValues
        exact (atomsResolve_of_resolveAtoms hloweredResolve).selfIso henvIso
      have htotalIso : RValsIso readyHeap.locRel
          (capturedValues ++ suppliedValues)
          (capturedValues ++ suppliedValues) :=
        hcapturedIso.append hloweredIso
      obtain ⟨targetCallOut, htargetInvokeAt, hcallIso⟩ :=
        invoke_historyIso readyHeap htotalIso hremainder'
      rcases targetCallOut with ⟨targetStore, targetValue⟩
      obtain ⟨callHeap, hreadyCall, hvalueIso⟩ := hcallIso
      have htargetInvoke : invoke ctx (fuel + 2) function
          (capturedValues ++ suppliedValues) store =
            .ok (targetStore, targetValue) :=
        invoke_mono (by omega) htargetInvokeAt
      have henvCall : RValsIso callHeap.locRel environment environment :=
        hreadyCall.rvals henvReady
      obtain ⟨targetOut, htargetRest, hrestIso⟩ :=
        continue_historyIso callHeap hvalueIso henvCall
          (codeNoUse_of_codeUsesVar_eq_false hrest) hrestRun
      have htargetOuter : runOp ctx (fuel + 3) current store environment
          (.call function
            (captured.toList ++ lowered.toList).toArray) =
          .ok (targetStore, targetValue) := by
        rw [runOp.eq_def]
        dsimp only
        rw [hcombinedResolve]
        simp only [bind, Except.bind]
        exact htargetInvoke
      have htargetInner : runOp ctx (fuel + 2) current targetStore
          (targetValue :: environment) (.pure (.var 0)) =
          .ok (targetStore, targetValue) := by
        rw [runOp.eq_def]
        rfl
      have htargetRun : runCode ctx (fuel + 4) current store environment
          (.letOp
            (.call function
              (captured.toList ++ lowered.toList).toArray)
            (.letOp (.pure (.var 0)) rest)) = .ok targetOut := by
        rw [runCode.eq_def]
        dsimp only
        rw [htargetOuter]
        simp only [bind, Except.bind]
        rw [runCode.eq_def]
        dsimp only
        rw [htargetInner]
        simp only [bind, Except.bind]
        exact htargetRest
      refine ⟨targetOut, htargetRun, ?_⟩
      change RunHistoryIso base out targetOut
      apply runHistoryIso_weaken (earlier := base) (before := callHeap)
        (hrun := hrestIso)
      exact (fun h => hreadyCall h)
  | @over declaration lowered hdeclaration hcaptureArity hscalar hrest
      hlowered hover =>
      have hctxDeclaration : ctx.decls function = some declaration := by
        simpa [hctx] using hdeclaration
      obtain ⟨capturedValues, suppliedValues, resultStore, resultValue,
          hcaptured, hsupplied, happly, hrestRun⟩ :=
        pairRunAt_of_run hctxDeclaration hcaptureArity hrun
      have hscalarValues :=
        allScalar_of_scalarCaptures henvironment hscalar hcaptured
      obtain ⟨ready, hdrop, hreadyNodes, hremainder⟩ :=
        freshApplyReady_of_run hscalarValues happly
      let allocated := store.allocNode .shared
        (.papN function (declArity declaration) capturedValues.toArray)
      have hsupplied' : resolveAtoms (.loc allocated.2 :: environment)
          supplied = .ok suppliedValues := by
        simpa [allocated] using hsupplied
      have hloweredResolve : resolveAtoms environment lowered =
          .ok suppliedValues :=
        lowerAtoms?_resolveAtoms hlowered hsupplied'
      have hcombinedResolve :
          resolveAtoms environment
              (captured.toList ++ lowered.toList).toArray =
            .ok (capturedValues ++ suppliedValues) := by
        exact resolveAtoms_append (by simpa using hcaptured)
          (by simpa using hloweredResolve)
      have hcapturedLength : capturedValues.length = captured.size :=
        resolveAtoms_length hcaptured
      have hloweredLength : suppliedValues.length = lowered.size :=
        resolveAtoms_length hloweredResolve
      have htotalOver : declArity declaration <
          (capturedValues ++ suppliedValues).length := by
        simpa [List.length_append, hcapturedLength, hloweredLength] using hover
      have htotalOver' : declArity declaration <
          capturedValues.length + suppliedValues.length := by
        simpa using htotalOver
      have hnotUnder : ¬ capturedValues.length + suppliedValues.length <
          declArity declaration := by
        omega
      have hnotExact : capturedValues.length + suppliedValues.length ≠
          declArity declaration := by
        omega
      have hpapsafe : declPapSafe declaration = true := by
        cases hpapsafe : declPapSafe declaration with
        | false =>
            simp [hnotUnder, hnotExact, hctxDeclaration, hpapsafe]
              at hremainder
        | true => rfl
      have hremainder' :
          (do
            let (called, value) ← invoke ctx fuel function
              ((capturedValues ++ suppliedValues).take
                (declArity declaration)) ready
            applyGo ctx fuel called value
              ((capturedValues ++ suppliedValues).drop
                (declArity declaration))) = .ok (resultStore, resultValue) := by
        simpa [hnotUnder, hnotExact, hctxDeclaration, hpapsafe] using hremainder
      let omitted := base.omitDeadAllocLeft .shared
        (.papN function (declArity declaration) capturedValues.toArray)
      let readyHeap : HeapHistoryIso ready store :=
        omitted.nodesEq hreadyNodes rfl
      have henvReady : RValsIso readyHeap.locRel environment environment := by
        change RValsIso base.locRel environment environment
        exact henvIso
      have hcapturedIso : RValsIso readyHeap.locRel
          capturedValues capturedValues := by
        change RValsIso base.locRel capturedValues capturedValues
        exact (atomsResolve_of_resolveAtoms hcaptured).selfIso henvIso
      have hloweredIso : RValsIso readyHeap.locRel
          suppliedValues suppliedValues := by
        change RValsIso base.locRel suppliedValues suppliedValues
        exact (atomsResolve_of_resolveAtoms hloweredResolve).selfIso henvIso
      have htotalIso : RValsIso readyHeap.locRel
          (capturedValues ++ suppliedValues)
          (capturedValues ++ suppliedValues) :=
        hcapturedIso.append hloweredIso
      have hfirstResolve : resolveAtoms environment
          ((captured.toList ++ lowered.toList).take
            (declArity declaration)).toArray =
          .ok ((capturedValues ++ suppliedValues).take
            (declArity declaration)) :=
        resolveAtoms_take hcombinedResolve (declArity declaration)
      have hprefixLe : capturedValues.length ≤ declArity declaration := by
        omega
      have hdropIdentity :
          (capturedValues ++ suppliedValues).drop (declArity declaration) =
            suppliedValues.drop
              (declArity declaration - captured.size) := by
        simpa [hcapturedLength] using
          List.drop_append_after_prefix capturedValues suppliedValues
            (declArity declaration) hprefixLe
      cases hsourceInvoke : invoke ctx fuel function
          ((capturedValues ++ suppliedValues).take
            (declArity declaration)) ready with
      | error error =>
          rw [hsourceInvoke] at hremainder'
          simp only [bind, Except.bind] at hremainder'
          contradiction
      | ok sourceCallOut =>
          rcases sourceCallOut with ⟨sourceCallStore, sourceCallValue⟩
          rw [hsourceInvoke] at hremainder'
          simp only [bind, Except.bind] at hremainder'
          obtain ⟨targetCallOut, htargetInvokeAt, hcallIso⟩ :=
            invoke_historyIso readyHeap
              (htotalIso.take (declArity declaration)) hsourceInvoke
          rcases targetCallOut with ⟨targetCallStore, targetCallValue⟩
          obtain ⟨callHeap, hreadyCall, hcallValueIso⟩ := hcallIso
          have htargetInvoke : invoke ctx (fuel + 2) function
              ((capturedValues ++ suppliedValues).take
                (declArity declaration)) store =
              .ok (targetCallStore, targetCallValue) :=
            invoke_mono (by omega) htargetInvokeAt
          have hheads : EnvsAgreeExcept 0
              (.loc allocated.2 :: environment)
              (targetCallValue :: environment) := by
            intro index hindex
            cases index with
            | zero => exact False.elim (hindex rfl)
            | succ index => rfl
          have hsuppliedTarget :
              resolveAtoms (targetCallValue :: environment) supplied =
                .ok suppliedValues := by
            rw [← resolveAtoms_env_eq hheads
              (lowerAtoms?_notUseZero hlowered)]
            exact hsupplied'
          have hremainingResolve :
              resolveAtoms (targetCallValue :: environment)
                  (supplied.toList.drop
                    (declArity declaration - captured.size)).toArray =
                .ok (suppliedValues.drop
                  (declArity declaration - captured.size)) :=
            resolveAtoms_drop (by simpa using hsuppliedTarget)
              (declArity declaration - captured.size)
          have hresidualIso : RValsIso callHeap.locRel
              ((capturedValues ++ suppliedValues).drop
                (declArity declaration))
              (suppliedValues.drop
                (declArity declaration - captured.size)) := by
            rw [← hdropIdentity]
            exact hreadyCall.rvals
              (htotalIso.drop (declArity declaration))
          obtain ⟨targetApplyOut, htargetApplyAt, happlyIso⟩ :=
            applyGo_historyIso callHeap hcallValueIso hresidualIso hremainder'
          rcases targetApplyOut with ⟨targetStore, targetValue⟩
          obtain ⟨applyHeap, hcallApply, hvalueIso⟩ := happlyIso
          have htargetApply : applyGo ctx (fuel + 1) targetCallStore
              targetCallValue
              (suppliedValues.drop
                (declArity declaration - captured.size)) =
              .ok (targetStore, targetValue) :=
            applyGo_mono (by omega) htargetApplyAt
          have henvApply : RValsIso applyHeap.locRel
              environment environment :=
            hcallApply.rvals (hreadyCall.rvals henvReady)
          obtain ⟨targetOut, htargetRest, hrestIso⟩ :=
            continue_historyIso applyHeap hvalueIso henvApply
              (codeNoUse_of_codeUsesVar_eq_false hrest) hrestRun
          have htargetOuter : runOp ctx (fuel + 3) current store environment
              (.call function
                ((captured.toList ++ lowered.toList).take
                  (declArity declaration)).toArray) =
              .ok (targetCallStore, targetCallValue) := by
            rw [runOp.eq_def]
            dsimp only
            rw [hfirstResolve]
            simp only [bind, Except.bind]
            exact htargetInvoke
          have htargetInner : runOp ctx (fuel + 2) current targetCallStore
              (targetCallValue :: environment)
              (.apply (.var 0)
                (supplied.toList.drop
                  (declArity declaration - captured.size)).toArray) =
              .ok (targetStore, targetValue) := by
            rw [runOp.eq_def]
            dsimp only
            rw [hremainingResolve]
            simp only [bind, Except.bind]
            exact htargetApply
          have htargetRun : runCode ctx (fuel + 4) current store environment
              (.letOp
                (.call function
                  ((captured.toList ++ lowered.toList).take
                    (declArity declaration)).toArray)
                (.letOp
                  (.apply (.var 0)
                    (supplied.toList.drop
                      (declArity declaration - captured.size)).toArray)
                  rest)) = .ok targetOut := by
            rw [runCode.eq_def]
            dsimp only
            rw [htargetOuter]
            simp only [bind, Except.bind]
            rw [runCode.eq_def]
            dsimp only
            rw [htargetInner]
            simp only [bind, Except.bind]
            exact htargetRest
          refine ⟨targetOut, htargetRun, ?_⟩
          change RunHistoryIso base out targetOut
          apply runHistoryIso_weaken (earlier := base) (before := applyHeap)
            (hrun := hrestIso)
          exact fun h => hcallApply (hreadyCall h)

/-! The arbitrary-fuel adapter for an already supplied self-history.  The two
source binders force four units before success is possible. -/
private theorem fusePair?_refines_selfHistory
    {ctx : Ctx} {fuel : Nat} {current : FnDef} {store : Store}
    {environment : List RVal} {declarations : DeclEnv} {facts : List Fact}
    {function : Address} {captured supplied : Array Atom} {rest : Code}
    {fusion : Fusion} {out : Store × RVal}
    (hctx : ctx.decls = declarations)
    (base : HeapHistoryIso store store)
    (henvIso : RValsIso base.locRel environment environment)
    (henvironment : EnvironmentHolds declarations store facts environment)
    (hfusion : fusePair? declarations facts function captured supplied rest =
      some fusion)
    (hrun : runCode ctx fuel current store environment
      (.letOp (.papp function captured)
        (.letOp (.apply (.var 0) supplied) rest)) = .ok out) :
    ∃ targetOut,
      runCode ctx fuel current store environment fusion.code = .ok targetOut ∧
        RunHistoryIso base out targetOut := by
  have hspec := fuseSpec_of_fusePair?_eq_some hfusion
  cases fuel with
  | zero => simp [runCode] at hrun
  | succ fuel =>
      cases fuel with
      | zero =>
          rw [runCode.eq_def] at hrun
          dsimp only at hrun
          rw [runOp.eq_def] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | succ fuel =>
          cases fuel with
          | zero =>
              rw [runCode.eq_def] at hrun
              dsimp only at hrun
              cases houter : runOp ctx 1 current store environment
                  (.papp function captured) with
              | error error =>
                  rw [houter] at hrun
                  simp only [bind, Except.bind] at hrun
                  contradiction
              | ok outerOut =>
                  rcases outerOut with ⟨middle, value⟩
                  rw [houter] at hrun
                  simp only [bind, Except.bind] at hrun
                  rw [runCode.eq_def] at hrun
                  dsimp only at hrun
                  rw [runOp.eq_def] at hrun
                  simp only [bind, Except.bind] at hrun
                  contradiction
          | succ fuel =>
              cases fuel with
              | zero =>
                  rw [runCode.eq_def] at hrun
                  dsimp only at hrun
                  cases houter : runOp ctx 2 current store environment
                      (.papp function captured) with
                  | error error =>
                      rw [houter] at hrun
                      simp only [bind, Except.bind] at hrun
                      contradiction
                  | ok outerOut =>
                      rcases outerOut with ⟨middle, value⟩
                      rw [houter] at hrun
                      simp only [bind, Except.bind] at hrun
                      rw [runCode.eq_def] at hrun
                      dsimp only at hrun
                      rw [runOp.eq_def] at hrun
                      dsimp only at hrun
                      simp only [resolveAtom, List.getElem?_cons_zero, bind,
                        Except.bind] at hrun
                      cases hargs : resolveAtoms (value :: environment)
                          supplied with
                      | error error =>
                          rw [hargs] at hrun
                          simp only [bind, Except.bind] at hrun
                          contradiction
                      | ok arguments =>
                          rw [hargs] at hrun
                          simp only [bind, Except.bind] at hrun
                          rw [applyGo.eq_def] at hrun
                          simp only [bind, Except.bind] at hrun
                          contradiction
              | succ fuel =>
                  exact fuseSpec_refinesAt hctx base henvIso henvironment
                    hspec hrun

/-- Every accepted fusion commutes with an arbitrary incoming allocation
history.  Facts need hold only for the source environment: evaluator
congruence transports the fused execution to the related target heap. -/
theorem fusePair?_refines_historyIso
    {ctx : Ctx} {fuel : Nat} {current : FnDef} {left right : Store}
    {leftEnvironment rightEnvironment : List RVal}
    {declarations : DeclEnv} {facts : List Fact}
    {function : Address} {captured supplied : Array Atom} {rest : Code}
    {fusion : Fusion} {leftOut : Store × RVal}
    (hctx : ctx.decls = declarations)
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (henvironment : EnvironmentHolds declarations left facts leftEnvironment)
    (hfusion : fusePair? declarations facts function captured supplied rest =
      some fusion)
    (hrun : runCode ctx fuel current left leftEnvironment
      (.letOp (.papp function captured)
        (.letOp (.apply (.var 0) supplied) rest)) = .ok leftOut) :
    ∃ rightOut,
      runCode ctx fuel current right rightEnvironment fusion.code =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  let self := heap.trans heap.symm
  have hselfEnvironment : RValsIso self.locRel
      leftEnvironment leftEnvironment := by
    change RValsIso
      (fun leftLoc rightLoc =>
        ∃ middleLoc, heap.locRel leftLoc middleLoc ∧
          heap.locRel rightLoc middleLoc)
      leftEnvironment leftEnvironment
    exact henvironments.trans henvironments.symm
  obtain ⟨middleOut, hmiddleRun, hlocal⟩ :=
    fusePair?_refines_selfHistory hctx self hselfEnvironment henvironment
      hfusion hrun
  obtain ⟨rightOut, hrightRun, htransport⟩ :=
    runCode_historyIso heap henvironments hmiddleRun
  refine ⟨rightOut, hrightRun, ?_⟩
  apply runHistoryIso_weaken (earlier := heap)
    (before := self.trans heap) (hrun := hlocal.trans htransport)
  intro leftLoc rightLoc hrel
  exact ⟨leftLoc, ⟨rightLoc, hrel, hrel⟩, hrel⟩

/-! ## Recursive traversal refinement -/

/-- One unchanged primitive followed by a recursively rewritten
continuation.  Operation congruence produces the history used by both HPT's
forget-heap transfer and the recursive hypothesis. -/
private theorem runCode_letOpWithFacts_refines
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    (hctx : ctx.decls = declarations)
    (howner : AnalysisOwnerCompatible declarations summaries owner current)
    {left right : Store} {facts : List Fact}
    {leftEnvironment rightEnvironment : List RVal}
    {operation : Op} {rest : Code} {bound : Fact}
    {fuel : Nat} {leftOut : Store × RVal}
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (henvironment : EnvironmentHolds declarations left facts leftEnvironment)
    (habstract : analyzeOp declarations summaries owner current facts operation =
      .ok bound)
    (hrun : runCode ctx (fuel + 1) current left leftEnvironment
      (.letOp operation rest) = .ok leftOut)
    (ih : ∀ {left right : Store} {facts : List Fact}
      {leftEnvironment rightEnvironment : List RVal}
      {input : Code} {leftOut : Store × RVal},
      (heap : HeapHistoryIso left right) →
      RValsIso heap.locRel leftEnvironment rightEnvironment →
      EnvironmentHolds declarations left facts leftEnvironment →
      runCode ctx fuel current left leftEnvironment input = .ok leftOut →
      ∃ rightOut,
        runCode ctx fuel current right rightEnvironment
            (runWithFacts declarations summaries owner current facts input).code =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut) :
    ∃ rightOut,
      runCode ctx (fuel + 1) current right rightEnvironment
          (.letOp operation
            (runWithFacts declarations summaries owner current
              (bound :: facts.map Fact.forgetHeap) rest).code) = .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  rw [runCode.eq_def] at hrun ⊢
  dsimp only at hrun ⊢
  cases hleftOperation : runOp ctx fuel current left leftEnvironment operation with
  | error error =>
      rw [hleftOperation] at hrun
      simp only [bind, Except.bind] at hrun
      contradiction
  | ok leftOperationOut =>
      rcases leftOperationOut with ⟨leftNext, leftValue⟩
      rw [hleftOperation] at hrun
      simp only [bind, Except.bind] at hrun
      have hbound := analyzeOp_sound_ownerCompatible hpost hctx howner
        henvironment
        habstract hleftOperation
      have hold := EnvironmentHolds.forgetHeap
        (after := leftNext) henvironment
      obtain ⟨rightOperationOut, hrightOperation, hoperationIso⟩ :=
        runOp_historyIso heap henvironments hleftOperation
      rcases rightOperationOut with ⟨rightNext, rightValue⟩
      obtain ⟨nextHeap, hentryNext, hvalue⟩ := hoperationIso
      rw [hrightOperation]
      simp only [bind, Except.bind]
      obtain ⟨rightOut, hrightRest, hrestIso⟩ :=
        ih nextHeap (.cons hvalue (hentryNext.rvals henvironments))
          (.cons hbound hold) hrun
      exact ⟨rightOut, hrightRest,
        runHistoryIso_weaken hentryNext hrestIso⟩

/-- Package the ordinary `let` equation so the main proof only has to
separate the one adjacent PAP/apply shape handled specially by the pass. -/
private theorem runCode_ordinaryLetWithFacts_refines
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    (hctx : ctx.decls = declarations)
    (howner : AnalysisOwnerCompatible declarations summaries owner current)
    {left right : Store} {facts : List Fact}
    {leftEnvironment rightEnvironment : List RVal}
    {operation : Op} {rest : Code} {fuel : Nat}
    {leftOut : Store × RVal}
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (henvironment : EnvironmentHolds declarations left facts leftEnvironment)
    (hrun : runCode ctx (fuel + 1) current left leftEnvironment
      (.letOp operation rest) = .ok leftOut)
    (ih : ∀ {left right : Store} {facts : List Fact}
      {leftEnvironment rightEnvironment : List RVal}
      {input : Code} {leftOut : Store × RVal},
      (heap : HeapHistoryIso left right) →
      RValsIso heap.locRel leftEnvironment rightEnvironment →
      EnvironmentHolds declarations left facts leftEnvironment →
      runCode ctx fuel current left leftEnvironment input = .ok leftOut →
      ∃ rightOut,
        runCode ctx fuel current right rightEnvironment
            (runWithFacts declarations summaries owner current facts input).code =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut)
    (hordinary :
      (runWithFacts declarations summaries owner current facts
        (.letOp operation rest)).code =
      match analyzeOp declarations summaries owner current facts operation with
      | .error _ => .letOp operation rest
      | .ok bound =>
          .letOp operation
            (runWithFacts declarations summaries owner current
              (bound :: facts.map Fact.forgetHeap) rest).code) :
    ∃ rightOut,
      runCode ctx (fuel + 1) current right rightEnvironment
          (runWithFacts declarations summaries owner current facts
            (.letOp operation rest)).code = .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  cases habstract : analyzeOp declarations summaries owner current facts
      operation with
  | error error =>
      rw [hordinary, habstract]
      exact runCode_historyIso heap henvironments hrun
  | ok bound =>
      rw [hordinary, habstract]
      exact runCode_letOpWithFacts_refines hpost hctx howner heap
        henvironments henvironment habstract hrun ih

/-- The branch-body half of recursive fusion.  The source-side HPT facts are
installed only after the concrete evaluator has selected a matching branch;
the heap-history relation transports the selected fields to the target. -/
private theorem runCode_caseWithFactsBodies_refines
    {declarations : DeclEnv} {summaries : SummaryEnv}
    {owner : Address} {current : FnDef} {ctx : Ctx}
    {left right : Store} {facts : List Fact}
    {leftEnvironment rightEnvironment : List RVal}
    {scrutinee : Atom} {peelNat : Bool} {alternatives : Array Alt}
    {scrutineeFact : Fact} {fuel : Nat} {leftOut : Store × RVal}
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (henvironment : EnvironmentHolds declarations left facts leftEnvironment)
    (habstract : resolveAtomFact facts scrutinee = .ok scrutineeFact)
    (hrun : runCode ctx (fuel + 1) current left leftEnvironment
      (.case scrutinee peelNat alternatives) = .ok leftOut)
    (ih : ∀ {left right : Store} {facts : List Fact}
      {leftEnvironment rightEnvironment : List RVal}
      {input : Code} {leftOut : Store × RVal},
      (heap : HeapHistoryIso left right) →
      RValsIso heap.locRel leftEnvironment rightEnvironment →
      EnvironmentHolds declarations left facts leftEnvironment →
      runCode ctx fuel current left leftEnvironment input = .ok leftOut →
      ∃ rightOut,
        runCode ctx fuel current right rightEnvironment
            (runWithFacts declarations summaries owner current facts input).code =
          .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut) :
    ∃ rightOut,
      runCode ctx (fuel + 1) current right rightEnvironment
          (.case scrutinee peelNat
            ((alternatives.map
              (runAlternativeWithFacts declarations summaries owner current
                scrutineeFact peelNat facts)).map
                  (fun result => result.alternative))) = .ok rightOut ∧
        RunHistoryIso heap leftOut rightOut := by
  obtain ⟨leftValue, hleftResolve⟩ :=
    resolveAtom_complete henvironment habstract
  have hscrutineeHolds :=
    resolveAtom_sound henvironment habstract hleftResolve
  obtain ⟨rightValue, hrightResolve, hvalue⟩ :=
    resolveAtom_historyIso henvironments hleftResolve
  rw [runCode.eq_def] at hrun ⊢
  dsimp only at hrun ⊢
  rw [hleftResolve] at hrun
  rw [hrightResolve]
  simp only [bind, Except.bind] at hrun ⊢
  cases hvalue with
  | erased => simp at hrun
  | @lit literal =>
      cases literal with
      | str value => simp at hrun
      | nat value =>
          cases peelNat with
          | false => simp at hrun
          | true =>
              cases value with
              | zero =>
                  simp only
                  rw [find?_runAlternativeWithFacts]
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == 0) with
                  | none => simp [hfind] at hrun
                  | some alternative =>
                      cases alternative with
                      | mk cidx fields body =>
                          cases fields with
                          | zero =>
                              have hzero :
                                  scrutineeFact.caseFields true cidx 0 = [] := by
                                unfold Fact.caseFields
                                split <;> rfl
                              simp [hfind] at hrun
                              simp only [Option.map_some]
                              obtain ⟨rightOut, hrightRun, hout⟩ :=
                                ih heap henvironments henvironment hrun
                              exact ⟨rightOut, by
                                simpa [runAlternativeWithFacts, hzero]
                                  using hrightRun, hout⟩
                          | succ fields =>
                              simp [hfind, runAlternativeWithFacts] at hrun
              | succ value =>
                  simp only
                  rw [find?_runAlternativeWithFacts]
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == 1) with
                  | none => simp [hfind] at hrun
                  | some alternative =>
                      cases alternative with
                      | mk cidx fields body =>
                          cases fields with
                          | zero =>
                              simp [hfind, runAlternativeWithFacts] at hrun
                          | succ fields =>
                              cases fields with
                              | zero =>
                                  have hcidx : cidx = 1 := by
                                    have hmatch := Array.find?_some
                                      (p := fun alternative : Alt =>
                                        alternative.cidx == 1)
                                      (a := .mk cidx 1 body)
                                      (xs := alternatives) hfind
                                    exact beq_iff_eq.mp hmatch
                                  have hbinders :
                                      EnvironmentHolds declarations left
                                        (scrutineeFact.caseFields true cidx 1)
                                        [.lit (.nat value)] := by
                                    simpa [hcidx] using
                                      (Fact.caseFields_natSucc_holds
                                        hscrutineeHolds)
                                  simp [hfind] at hrun
                                  simp only [Option.map_some]
                                  obtain ⟨rightOut, hrightRun, hout⟩ :=
                                    ih heap (.cons .lit henvironments)
                                      (hbinders.append henvironment) hrun
                                  exact ⟨rightOut, by
                                    simpa [runAlternativeWithFacts]
                                      using hrightRun, hout⟩
                              | succ fields =>
                                  simp [hfind, runAlternativeWithFacts] at hrun
  | @loc leftLoc rightLoc hrel =>
      cases hleft : left.get? leftLoc with
      | none => simp [hleft] at hrun
      | some leftBox =>
          obtain ⟨rightBox, hright, hbox⟩ := heap.boxes hrel hleft
          rcases leftBox with ⟨leftWorld, leftRc, leftNode⟩
          rcases rightBox with ⟨rightWorld, rightRc, rightNode⟩
          rcases hbox with ⟨hworld, hrc, hnode⟩
          change leftWorld = rightWorld at hworld
          change leftRc = rightRc at hrc
          change NodeIso heap.locRel leftNode rightNode at hnode
          subst rightWorld
          subst rightRc
          simp only [hleft] at hrun
          simp only [hright]
          cases hnode with
          | pap harguments => simp at hrun
          | @ctor identity leftFields rightFields hfields =>
              simp only
              rw [find?_runAlternativeWithFacts]
              cases hfind : alternatives.find?
                  (fun alternative => alternative.cidx == identity.cidx) with
              | none => simp [hfind] at hrun
              | some alternative =>
                  cases alternative with
                  | mk cidx fieldCount body =>
                      have hsizes : leftFields.size = rightFields.size := by
                        simpa using hfields.lengths
                      by_cases hcount : leftFields.size = fieldCount
                      · have hrightCount :
                            rightFields.size = fieldCount := by
                          rw [← hsizes]
                          exact hcount
                        have hcidx : identity.cidx = cidx := by
                          have hmatch := Array.find?_some
                            (p := fun alternative : Alt =>
                              alternative.cidx == identity.cidx)
                            (a := .mk cidx fieldCount body)
                            (xs := alternatives) hfind
                          exact (beq_iff_eq.mp hmatch).symm
                        have hbinders := Fact.caseFields_ctor_holds
                          peelNat cidx fieldCount hscrutineeHolds hleft rfl
                          hcidx hcount
                        simp [hfind, hcount] at hrun
                        simp only [Option.map_some]
                        rw [Array.foldl_cons_eq_reverse_append]
                        obtain ⟨rightOut, hrightRun, hout⟩ :=
                          ih heap (hfields.reverse.append henvironments)
                            (hbinders.append henvironment) hrun
                        exact ⟨rightOut, by
                          simpa [hrightCount, runAlternativeWithFacts]
                            using hrightRun, hout⟩
                      · have hrightCount :
                            rightFields.size ≠ fieldCount := by
                          intro heq
                          exact hcount (hsizes.trans heq)
                        simp [hfind, hcount, hrightCount,
                          runAlternativeWithFacts] at hrun

/-- Recursive HPT-guided PAP fusion preserves every successful run modulo
allocation history.  The theorem is deliberately stated over an arbitrary
incoming heap relation, so it can be used beneath calls and inside another
owner-sensitive declaration rewrite. -/
theorem runCode_runWithFacts_refines_ownerCompatible
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    {left right : Store} {facts : List Fact}
    {leftEnvironment rightEnvironment : List RVal}
    {input : Code} {fuel : Nat} {leftOut : Store × RVal}
    (hctx : ctx.decls = declarations)
    (howner : AnalysisOwnerCompatible declarations summaries owner current)
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (henvironment : EnvironmentHolds declarations left facts leftEnvironment)
    (hrun : runCode ctx fuel current left leftEnvironment input = .ok leftOut) :
    ∃ rightOut,
      runCode ctx fuel current right rightEnvironment
          (runWithFacts declarations summaries owner current facts input).code =
        .ok rightOut ∧
      RunHistoryIso heap leftOut rightOut := by
  induction fuel generalizing left right facts leftEnvironment
      rightEnvironment input leftOut with
  | zero => simp [runCode] at hrun
  | succ fuel ih =>
      cases input with
      | ret atom =>
          simpa [runWithFacts] using
            (runCode_historyIso heap henvironments hrun)
      | case scrutinee peelNat alternatives =>
          cases habstract : resolveAtomFact facts scrutinee with
          | error error =>
              simpa [runWithFacts, habstract] using
                (runCode_historyIso heap henvironments hrun)
          | ok scrutineeFact =>
              simpa [runWithFacts, habstract] using
                (runCode_caseWithFactsBodies_refines heap henvironments
                  henvironment habstract hrun
                  (fun nextHeap nextEnvironments nextFacts nextRun =>
                    ih nextHeap nextEnvironments nextFacts nextRun))
      | letOp operation rest =>
          have ordinary {operation : Op} {rest : Code}
              (hordinaryRun : runCode ctx (fuel + 1) current left
                leftEnvironment (.letOp operation rest) = .ok leftOut)
              (hordinary :
                (runWithFacts declarations summaries owner current facts
                  (.letOp operation rest)).code =
                match analyzeOp declarations summaries owner current facts
                    operation with
                | .error _ => .letOp operation rest
                | .ok bound =>
                    .letOp operation
                      (runWithFacts declarations summaries owner current
                        (bound :: facts.map Fact.forgetHeap) rest).code) :=
              runCode_ordinaryLetWithFacts_refines hpost hctx howner heap
                henvironments henvironment hordinaryRun
                (fun nextHeap nextEnvironments nextFacts nextRun =>
                  ih nextHeap nextEnvironments nextFacts nextRun)
                hordinary
          by_cases hpair : ∃ function captured supplied tail,
              operation = .papp function captured ∧
                rest = .letOp (.apply (.var 0) supplied) tail
          · obtain ⟨function, captured, supplied, tail, rfl, rfl⟩ := hpair
            let pap := Op.papp function captured
            let applyOperation := Op.apply (.var 0) supplied
            cases hpap : analyzeOp declarations summaries owner current facts
                pap with
            | error error =>
                simpa [runWithFacts, pap, applyOperation, hpap] using
                  (runCode_historyIso heap henvironments hrun)
            | ok papFact =>
                let afterPap := papFact :: facts.map Fact.forgetHeap
                cases happly : analyzeOp declarations summaries owner current
                    afterPap applyOperation with
                | error error =>
                    simpa [runWithFacts, pap, applyOperation, afterPap, hpap,
                      happly] using
                        (runCode_historyIso heap henvironments hrun)
                | ok resultFact =>
                    let afterApply :=
                      resultFact :: afterPap.map Fact.forgetHeap
                    let nested := runWithFacts declarations summaries owner
                      current afterApply tail
                    have hpapConcrete : analyzeOp declarations summaries owner
                        current facts (.papp function captured) =
                          .ok papFact := by
                      simpa [pap] using hpap
                    have happlyConcrete : analyzeOp declarations summaries
                        owner current (papFact :: facts.map Fact.forgetHeap)
                        (.apply (.var 0) supplied) = .ok resultFact := by
                      simpa [afterPap, applyOperation] using happly
                    cases hfusion : fusePair? declarations facts function
                        captured supplied nested.code with
                    | none =>
                        apply ordinary hrun
                        simp only [runWithFacts, hpapConcrete,
                          happlyConcrete]
                        rw [hfusion]
                    | some fusion =>
                        rw [runCode.eq_def] at hrun
                        dsimp only at hrun
                        cases hleftPap : runOp ctx fuel current left
                            leftEnvironment pap with
                        | error error =>
                            rw [hleftPap] at hrun
                            simp only [bind, Except.bind] at hrun
                            contradiction
                        | ok leftPapOut =>
                            rcases leftPapOut with ⟨leftNext, leftValue⟩
                            rw [hleftPap] at hrun
                            simp only [bind, Except.bind] at hrun
                            have hpapFact := analyzeOp_sound_ownerCompatible
                              hpost hctx howner henvironment hpap hleftPap
                            have hold := EnvironmentHolds.forgetHeap
                              (after := leftNext) henvironment
                            have hafterPap : EnvironmentHolds declarations
                                leftNext afterPap
                                (leftValue :: leftEnvironment) := by
                              exact .cons hpapFact hold
                            obtain ⟨rightPapOut, hrightPap, hpapIso⟩ :=
                              runOp_historyIso heap henvironments hleftPap
                            rcases rightPapOut with ⟨rightNext, rightValue⟩
                            obtain ⟨nextHeap, hentryNext, hvalue⟩ := hpapIso
                            have hnextEnvironments : RValsIso nextHeap.locRel
                                (leftValue :: leftEnvironment)
                                (rightValue :: rightEnvironment) :=
                              .cons hvalue (hentryNext.rvals henvironments)
                            let self := nextHeap.trans nextHeap.symm
                            have hselfEnvironment : RValsIso self.locRel
                                (leftValue :: leftEnvironment)
                                (leftValue :: leftEnvironment) := by
                              change RValsIso
                                (fun leftLoc rightLoc =>
                                  ∃ middleLoc,
                                    nextHeap.locRel leftLoc middleLoc ∧
                                    nextHeap.locRel rightLoc middleLoc)
                                (leftValue :: leftEnvironment)
                                (leftValue :: leftEnvironment)
                              exact hnextEnvironments.trans
                                hnextEnvironments.symm
                            obtain ⟨middleOut, hmiddleRun, hrewrite⟩ :=
                              ih self hselfEnvironment hafterPap hrun
                            have hmiddleRun' : runCode ctx fuel current leftNext
                                (leftValue :: leftEnvironment)
                                (.letOp applyOperation nested.code) =
                                  .ok middleOut := by
                              simpa [runWithFacts, applyOperation, afterPap,
                                afterApply, nested, happly] using hmiddleRun
                            have hsourceNested : runCode ctx (fuel + 1) current
                                left leftEnvironment
                                (.letOp pap
                                  (.letOp applyOperation nested.code)) =
                                    .ok middleOut := by
                              rw [runCode.eq_def]
                              dsimp only
                              rw [hleftPap]
                              simp only [bind, Except.bind]
                              exact hmiddleRun'
                            obtain ⟨rightOut, hrightRun, hfused⟩ :=
                              fusePair?_refines_historyIso hctx heap
                                henvironments henvironment hfusion hsourceNested
                            obtain ⟨rewriteHeap, hselfRewrite,
                              hrewriteValue⟩ := hrewrite
                            obtain ⟨fusedHeap, hheapFused, hfusedValue⟩ :=
                              hfused
                            refine ⟨rightOut, ?_, rewriteHeap.trans fusedHeap,
                              ?_, hrewriteValue.trans hfusedValue⟩
                            · simp only [runWithFacts, hpapConcrete,
                                happlyConcrete]
                              rw [hfusion]
                              exact hrightRun
                            · intro leftLoc rightLoc hrel
                              refine ⟨leftLoc, hselfRewrite ?_,
                                hheapFused hrel⟩
                              exact ⟨rightLoc, hentryNext hrel,
                                hentryNext hrel⟩
          · apply ordinary hrun
            by_cases hpapp : ∃ function captured,
                operation = .papp function captured
            · obtain ⟨function, captured, rfl⟩ := hpapp
              cases rest with
              | ret atom =>
                  simp only [runWithFacts]
                  split <;> rfl
              | case scrutinee peelNat alternatives =>
                  simp only [runWithFacts]
                  split <;> rfl
              | letOp nextOperation tail =>
                  by_cases happlyShape : ∃ applied supplied,
                      nextOperation = .apply applied supplied
                  · obtain ⟨applied, supplied, rfl⟩ := happlyShape
                    by_cases hvarZero : applied = .var 0
                    · subst applied
                      exact False.elim
                        (hpair ⟨function, captured, supplied, tail, rfl, rfl⟩)
                    · cases applied with
                      | var index =>
                          cases index with
                          | zero => exact False.elim (hvarZero rfl)
                          | succ index =>
                              simp only [runWithFacts]
                              split <;> rfl
                      | lit literal =>
                          simp only [runWithFacts]
                          split <;> rfl
                      | erased =>
                          simp only [runWithFacts]
                          split <;> rfl
                  · cases nextOperation <;>
                      try { simp only [runWithFacts]; split <;> rfl }
                    rename_i applied supplied
                    exact False.elim
                      (happlyShape ⟨applied, supplied, rfl⟩)
            · cases operation <;>
                try { simp only [runWithFacts]; split <;> rfl }
              rename_i function captured
              exact False.elim (hpapp ⟨function, captured, rfl⟩)

/-- Exact declaration ownership is the common stored-function specialization
of the owner-compatible recursive refinement theorem. -/
theorem runCode_runWithFacts_refines
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    {left right : Store} {facts : List Fact}
    {leftEnvironment rightEnvironment : List RVal}
    {input : Code} {fuel : Nat} {leftOut : Store × RVal}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current))
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (henvironment : EnvironmentHolds declarations left facts leftEnvironment)
    (hrun : runCode ctx fuel current left leftEnvironment input = .ok leftOut) :
    ∃ rightOut,
      runCode ctx fuel current right rightEnvironment
          (runWithFacts declarations summaries owner current facts input).code =
        .ok rightOut ∧
      RunHistoryIso heap leftOut rightOut :=
  runCode_runWithFacts_refines_ownerCompatible hpost hctx (.inl hcurrent)
    heap henvironments henvironment hrun

/-- The owner-local traversal rewrites a body soundly while retaining the
source current frame.  The generic evaluator fixed-point theorem is
responsible for installing the rewritten frame around recursive self-calls. -/
theorem rewriteFunction_staticBodyRefines
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current)) :
    StaticFunctionBodyRefines ctx current
      (rewriteFunction declarations summaries owner current) := by
  intro fuel store environment sourceOut base hlength henvironment hrun
  have htop : EnvironmentHolds declarations store
      (List.replicate current.arity Fact.top) environment := by
    simpa [hlength] using
      (EnvironmentHolds.top_replicate declarations store environment)
  obtain ⟨targetOut, htargetRun, hiso⟩ :=
    runCode_runWithFacts_refines hpost hctx hcurrent base henvironment htop hrun
  exact ⟨targetOut, by
    simpa [rewriteFunction, runFunction] using htargetRun, hiso⟩

/-- Rewriting the current frame preserves arbitrary surrounding code,
including recursive `callSelf` entries into its rewritten body. -/
theorem runCode_rewriteFunction_refines
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    {left right : Store} {fuel : Nat}
    {leftEnvironment rightEnvironment : List RVal}
    {input : Code} {sourceOut : Store × RVal}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current))
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (hrun : runCode ctx fuel current left leftEnvironment input =
      .ok sourceOut) :
    ∃ targetOut,
      runCode ctx fuel
          (rewriteFunction declarations summaries owner current)
          right rightEnvironment input = .ok targetOut ∧
        RunHistoryIso heap sourceOut targetOut :=
  runCode_currentFrame_refines
    (rewriteFunction_staticBodyRefines hpost hctx hcurrent)
    rfl rfl heap henvironments hrun

/-- The checked owner-local PAP traversal supplies the semantic function-body
obligation consumed by `AbstractEnvironment`. -/
theorem rewriteFunction_bodyRefines
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current)) :
    FunctionBodyRefines ctx current
      (rewriteFunction declarations summaries owner current) :=
  FunctionBodyRefines.ofStatic
    (rewriteFunction_staticBodyRefines hpost hctx hcurrent) rfl rfl

/-! ## Logical declaration environment

The semantic traversal remains keyed by the source addresses.  Artifact
readdressing is a later, separate transport step. -/

/-- Rewrite every stored function under its source owner while retaining the
old lookup keys. -/
def rewriteDeclEnv (declarations : DeclEnv) (summaries : SummaryEnv) :
    DeclEnv :=
  fun owner => (declarations owner).map
    (rewriteDeclaration declarations summaries owner)

/-- Retain the scalar oracle and replace only the declaration environment. -/
def rewriteCtx (declarations : DeclEnv) (summaries : SummaryEnv)
    (ctx : Ctx) : Ctx :=
  { ctx with decls := rewriteDeclEnv declarations summaries }

/-- List form consumed by a subsequent content-address rebuild. -/
def rewriteEntries (declarations : DeclEnv) (summaries : SummaryEnv)
    (entries : List (Address × Decl)) : List (Address × Decl) :=
  entries.map fun entry =>
    (entry.1, rewriteDeclaration declarations summaries entry.1 entry.2)

/-- PAP fusion's owner-local body theorem instantiates the generic declaration
environment interface for every successful source lookup. -/
theorem abstractEnvironment_rewriteCtx
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} (hctx : ctx.decls = declarations) :
    AbstractEnvironment ctx (rewriteCtx declarations summaries ctx) := by
  constructor
  · rfl
  · intro address arity hsource
    have hdeclaration : declarations address = some (.extern arity) := by
      rw [← hctx]
      exact hsource
    simp [rewriteCtx, rewriteDeclEnv, hdeclaration, rewriteDeclaration]
  · intro address source hsource
    have hdeclaration : declarations address = some (.fn source) := by
      rw [← hctx]
      exact hsource
    refine ⟨rewriteFunction declarations summaries address source, ?_,
      rfl, rfl, rfl, ?_⟩
    · simp [rewriteCtx, rewriteDeclEnv, hdeclaration,
        rewriteDeclaration]
    · exact rewriteFunction_bodyRefines hpost hctx hdeclaration

/-- Successful evaluation is preserved after logically replacing every
stored function by its owner-sensitive PAP-fused body. -/
theorem runCode_rewriteCtx_refines
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current : FnDef} {left right : Store} {fuel : Nat}
    {leftEnvironment rightEnvironment : List RVal}
    {input : Code} {sourceOut : Store × RVal}
    (hctx : ctx.decls = declarations)
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (hrun : runCode ctx fuel current left leftEnvironment input =
      .ok sourceOut) :
    ∃ targetOut,
      runCode (rewriteCtx declarations summaries ctx) fuel current right
          rightEnvironment input = .ok targetOut ∧
        RunHistoryIso heap sourceOut targetOut :=
  runCode_abstractEnvironment
    (abstractEnvironment_rewriteCtx hpost hctx) heap henvironments hrun

/-- Closed self-heap specialization of the general history theorem. -/
theorem fusePair?_refines
    {ctx : Ctx} {fuel : Nat} {current : FnDef} {store : Store}
    {environment : List RVal} {declarations : DeclEnv} {facts : List Fact}
    {function : Address} {captured supplied : Array Atom} {rest : Code}
    {fusion : Fusion} {out : Store × RVal}
    (hctx : ctx.decls = declarations)
    (hclosed : StoreClosed store)
    (hbounds : Reclamation.ValuesInBounds store environment)
    (henvironment : EnvironmentHolds declarations store facts environment)
    (hfusion : fusePair? declarations facts function captured supplied rest =
      some fusion)
    (hrun : runCode ctx fuel current store environment
      (.letOp (.papp function captured)
        (.letOp (.apply (.var 0) supplied) rest)) = .ok out) :
    ∃ targetOut,
      runCode ctx fuel current store environment fusion.code = .ok targetOut ∧
        RunHistoryIso (HeapHistoryIso.refl store hclosed) out targetOut := by
  let base := HeapHistoryIso.refl store hclosed
  have henvIso : RValsIso base.locRel environment environment := by
    simpa [base] using RValsIso.refl_of_inBounds hclosed hbounds
  simpa [base] using
    fusePair?_refines_selfHistory hctx base henvIso henvironment hfusion hrun

end Ix.Compiler.IxIR1.HPT.PAPFuse
