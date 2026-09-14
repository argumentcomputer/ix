import Ix.Kernel.Verify.Inductive.RuleApplication

open Ix.Theory (VLevel)

/-!
# Constructive iota-pattern paths

`Pattern.varN` captures application arguments from left to right, but its
dependent `Path` type represents the newest argument as `none` and every
older argument under another `some`.  The definitions and proofs below make
that ordering explicit. Singleton certification uses them to select the certified minor premise
at a constructor's exact rule index; an off-by-one or reversed-spine adapter
cannot satisfy the positional theorem.
-/

namespace Ix.Kernel

open Ix.Theory.Named

/-- The dependent path of the `index`-th (left-to-right) argument captured by
`pattern.varN arity`. -/
def IotaVarPath (pattern : Ix.Theory.Named.Pattern) :
    (arity : Nat) → Fin arity →
      (Ix.Theory.Named.Pattern.varN pattern arity).Path
  | 0, index => Fin.elim0 index
  | arity + 1, index =>
      if h : index.val < arity then
        some (IotaVarPath pattern arity ⟨index.val, h⟩)
      else
        none

/-- Invert a `varN` match to the exact constant-headed argument list and
identify every dependent capture path with its positional list entry. -/
theorem iotaVarMatch_spine
    {name : Lean.Name} {arity : Nat} {source : Ix.Theory.Named.VExpr}
    {levels : List Ix.Theory.VLevel}
    {captures : ((Ix.Theory.Named.Pattern.const name).varN arity).Path →
      Ix.Theory.Named.VExpr}
    (hmatch : Ix.Theory.Named.Pattern.Matches
      ((Ix.Theory.Named.Pattern.const name).varN arity)
      source levels captures) :
    ∃ arguments : List Ix.Theory.Named.VExpr,
      arguments.length = arity ∧
      source = Ix.Theory.Named.VExpr.appN (.const name levels) arguments ∧
      ∀ index : Fin arity,
        arguments[index.val]? = some
          (captures (IotaVarPath (.const name) arity index)) := by
  induction arity generalizing source with
  | zero =>
      change Ix.Theory.Named.Pattern.Matches (.const name)
        source levels captures at hmatch
      cases hmatch
      exact ⟨[], rfl, rfl, fun index => Fin.elim0 index⟩
  | succ arity ih =>
      change Ix.Theory.Named.Pattern.Matches
        (.var ((Ix.Theory.Named.Pattern.const name).varN arity))
        source levels captures at hmatch
      cases hmatch with
      | var hprefix =>
          rename_i fn argument prefixCaptures
          obtain ⟨arguments, hlength, rfl, hcaptures⟩ := ih hprefix
          refine ⟨arguments ++ [argument], by simp [hlength], ?_, ?_⟩
          · rw [Ix.Theory.Named.VExpr.appN_append]
            rfl
          · intro index
            by_cases hlt : index.val < arity
            · rw [List.getElem?_append_left
                (by simpa [hlength] using hlt)]
              simpa [IotaVarPath, hlt] using
                hcaptures ⟨index.val, hlt⟩
            · have heq : index.val = arity := by omega
              have hindex : index = Fin.last arity := Fin.ext heq
              subst index
              rw [List.getElem?_append_right (by simp [hlength])]
              simp [IotaVarPath, hlength]

namespace RecursorIotaPattern

/-- Path of a recursor-prefix argument within the complete iota pattern. -/
def recursorArgumentPath
    (recursorName : Lean.Name) (majorIdx : Nat)
    (constructorName : Lean.Name) (constructorArgs : Nat)
    (index : Fin majorIdx) :
    (RecursorIotaPattern recursorName majorIdx constructorName
      constructorArgs).Path :=
  Sum.inl (IotaVarPath (.const recursorName) majorIdx index)

/-- Pattern RHS selecting one exact recursor-prefix argument. -/
def recursorArgumentRhs
    (recursorName : Lean.Name) (majorIdx : Nat)
    (constructorName : Lean.Name) (constructorArgs : Nat)
    (index : Fin majorIdx) :
    (RecursorIotaPattern recursorName majorIdx constructorName
      constructorArgs).RHS :=
  .var (recursorArgumentPath recursorName majorIdx constructorName
    constructorArgs index)

/-- Path of a constructor argument within the right branch of the complete
iota pattern.  Keeping this distinct from the recursor-prefix path makes the
parameter/field split in generated recursive rules explicit. -/
def constructorArgumentPath
    (recursorName : Lean.Name) (majorIdx : Nat)
    (constructorName : Lean.Name) (constructorArgs : Nat)
    (index : Fin constructorArgs) :
    (RecursorIotaPattern recursorName majorIdx constructorName
      constructorArgs).Path :=
  Sum.inr (IotaVarPath (.const constructorName) constructorArgs index)

/-- Pattern RHS selecting one exact constructor argument. -/
def constructorArgumentRhs
    (recursorName : Lean.Name) (majorIdx : Nat)
    (constructorName : Lean.Name) (constructorArgs : Nat)
    (index : Fin constructorArgs) :
    (RecursorIotaPattern recursorName majorIdx constructorName
      constructorArgs).RHS :=
  .var (constructorArgumentPath recursorName majorIdx constructorName
    constructorArgs index)

@[simp] theorem recursorArgumentRhs_apply
    (recursorName : Lean.Name) (majorIdx : Nat)
    (constructorName : Lean.Name) (constructorArgs : Nat)
    (index : Fin majorIdx) (levels : List Ix.Theory.VLevel)
    (captures : (RecursorIotaPattern recursorName majorIdx constructorName
      constructorArgs).Path → Ix.Theory.Named.VExpr) :
    (recursorArgumentRhs recursorName majorIdx constructorName constructorArgs
      index).apply levels captures =
      captures (recursorArgumentPath recursorName majorIdx constructorName
        constructorArgs index) := rfl

@[simp] theorem constructorArgumentRhs_apply
    (recursorName : Lean.Name) (majorIdx : Nat)
    (constructorName : Lean.Name) (constructorArgs : Nat)
    (index : Fin constructorArgs) (levels : List Ix.Theory.VLevel)
    (captures : (RecursorIotaPattern recursorName majorIdx constructorName
      constructorArgs).Path → Ix.Theory.Named.VExpr) :
    (constructorArgumentRhs recursorName majorIdx constructorName
      constructorArgs index).apply levels captures =
      captures (constructorArgumentPath recursorName majorIdx constructorName
        constructorArgs index) := rfl

/-- A complete iota match exposes both positional application spines.  The
constructor universe list is existential because Ix.Theory.Named's pattern result
retains the recursor levels only. -/
theorem matches_spines
    {recursorName constructorName : Lean.Name}
    {majorIdx constructorArgs : Nat} {source : Ix.Theory.Named.VExpr}
    {levels : List Ix.Theory.VLevel}
    {captures : (RecursorIotaPattern recursorName majorIdx constructorName
      constructorArgs).Path → Ix.Theory.Named.VExpr}
    (hmatch : Ix.Theory.Named.Pattern.Matches
      (RecursorIotaPattern recursorName majorIdx constructorName
        constructorArgs) source levels captures) :
    ∃ recursorArguments constructorLevels constructorArguments,
      recursorArguments.length = majorIdx ∧
      constructorArguments.length = constructorArgs ∧
      source = .app
        (Ix.Theory.Named.VExpr.appN (.const recursorName levels)
          recursorArguments)
        (Ix.Theory.Named.VExpr.appN (.const constructorName constructorLevels)
          constructorArguments) ∧
      (∀ index : Fin majorIdx,
        recursorArguments[index.val]? = some
          (captures (recursorArgumentPath recursorName majorIdx
            constructorName constructorArgs index))) := by
  simp only [RecursorIotaPattern, Ix.Theory.Named.SimplePattern.toPattern] at hmatch
  cases hmatch with
  | app hrecursor hconstructor =>
      obtain ⟨recursorArguments, hrecLength, rfl, hrecCaptures⟩ :=
        iotaVarMatch_spine hrecursor
      obtain ⟨constructorArguments, hctorLength, rfl, _⟩ :=
        iotaVarMatch_spine hconstructor
      refine ⟨recursorArguments, _, constructorArguments, hrecLength,
        hctorLength, rfl, ?_⟩
      intro index
      simpa [recursorArgumentPath] using hrecCaptures index

/-- Strong inversion of a complete iota match, retaining the positional
capture equations for both application spines.  Indexed rules need the
constructor equations as well as the recursor-prefix equations: their
generated RHS and their index-consistency checks mention constructor fields. -/
theorem matches_spines_full
    {recursorName constructorName : Lean.Name}
    {majorIdx constructorArgs : Nat} {source : Ix.Theory.Named.VExpr}
    {levels : List Ix.Theory.VLevel}
    {captures : (RecursorIotaPattern recursorName majorIdx constructorName
      constructorArgs).Path → Ix.Theory.Named.VExpr}
    (hmatch : Ix.Theory.Named.Pattern.Matches
      (RecursorIotaPattern recursorName majorIdx constructorName
        constructorArgs) source levels captures) :
    ∃ recursorArguments constructorLevels constructorArguments,
      recursorArguments.length = majorIdx ∧
      constructorArguments.length = constructorArgs ∧
      source = .app
        (Ix.Theory.Named.VExpr.appN (.const recursorName levels)
          recursorArguments)
        (Ix.Theory.Named.VExpr.appN (.const constructorName constructorLevels)
          constructorArguments) ∧
      (∀ index : Fin majorIdx,
        recursorArguments[index.val]? = some
          (captures (recursorArgumentPath recursorName majorIdx
            constructorName constructorArgs index))) ∧
      (∀ index : Fin constructorArgs,
        constructorArguments[index.val]? = some
          (captures (constructorArgumentPath recursorName majorIdx
            constructorName constructorArgs index))) := by
  simp only [RecursorIotaPattern, Ix.Theory.Named.SimplePattern.toPattern] at hmatch
  cases hmatch with
  | app hrecursor hconstructor =>
      obtain ⟨recursorArguments, hrecLength, rfl, hrecCaptures⟩ :=
        iotaVarMatch_spine hrecursor
      obtain ⟨constructorArguments, hctorLength, rfl, hctorCaptures⟩ :=
        iotaVarMatch_spine hconstructor
      refine ⟨recursorArguments, _, constructorArguments, hrecLength,
        hctorLength, rfl, ?_, ?_⟩
      · intro index
        simpa [recursorArgumentPath] using hrecCaptures index
      · intro index
        simpa [constructorArgumentPath] using hctorCaptures index

end RecursorIotaPattern

end Ix.Kernel
