import IxVMRefinement.Guard.Certificate

/-! # The guard certificate at a propositional structure with a quantified field

    structure P : Prop where
      h : ∀ n : Nat, n = n
      k : True

The constructor's raw telescope is `(h : ∀ n : Nat, @Eq.{1} Nat n n) → (k : True) → P` over
address keys. The sort ordinary inference gives the first field's domain is `imax 1 0`, which is
zero at every assignment without being the literal `0`; the classifier's signature of the same
domain is `0`, computed through the declared type of `Eq` at level `1` (three applications,
each instantiating a `∀` exposed by the head), and the signature of `True` is `0` through the
declared type of `True`. The classifier reads no record of `Nat`: a domain's own universe is
dropped at a `∀`, and arguments are not classified.

* `ctorType_signatures`: the classifier's walk of the two fields, over every lookup that reads
  the two declared types.
* `install_and_use`: **install and one projection use**. IxC's table stage run at the sorts
  `[imax 1 0, 0]` stores a table that has its certificate over the witness store `R`; and over
  every record store `E` for `R` (constrained by `Typing.RecordsFor R E` alone), the use
  observation of field `0` exists and `Rules.FireSem` holds at the entry of field `0`, at every
  level list. No role context and no validation limit occur.

The witness store enters through three readings of its raw dictionary: the constructor's
telescope at the block address, and the declared types of `Eq` and `True`.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Guard.QuantifiedField

open Ix.Kernel (Expr Level ProjTable ConstantVal ProjGuardCert ProjGuardUse)
open Ix.Kernel.GuardClassifier

/-- `Eq.{u} : {α : Sort u} → α → α → Prop` at the level `u`, as the raw dictionary answers. -/
def eqType (u : Level) : Expr .anon :=
  .forallE (.sort u)
    (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero) default) default) default

section

variable (aNat aEq aTrue aP : _root_.Address)

/-- `∀ n : Nat, @Eq.{1} Nat n n`, raw. -/
def quantifiedField : Expr .anon :=
  .forallE (.const (.id aNat) [])
    (.app (.app (.app (.const (.id aEq) [.succ .zero]) (.const (.id aNat) [])) (.bvar 0))
      (.bvar 0))
    default

/-- The constructor's raw telescope: `(h : ∀ n : Nat, n = n) → (k : True) → P`. -/
def ctorType : Expr .anon :=
  .forallE (quantifiedField aNat aEq)
    (.forallE (.const (.id aTrue) []) (.const (.id aP) []) default) default

/-- The sorts ordinary inference gives the two field domains: `imax 1 0` for the quantified
field, `0` for `True`. -/
def sorts : List Level := [.imax (.succ .zero) .zero, .zero]

theorem eval_imax_one_zero (φ : Ix.Kernel.LevelParam → Nat) :
    Level.eval φ (.imax (.succ .zero) .zero) = 0 := rfl

/-- **The classifier's signature of the quantified field is `0`**, in any context, over every
lookup that reads `Eq`'s declared type at level `1`. -/
theorem quantifiedField_signature {look : Lookup .anon}
    (hEq : look.typeOf (.id aEq) [.succ .zero] = some (eqType (.succ .zero)))
    (ctx : List (Expr .anon)) :
    sortSignature look 5 ctx (quantifiedField aNat aEq) = some .zero := by
  have h1 : infer look 1 (.const (.id aNat) [] :: ctx) (.const (.id aEq) [.succ .zero]) =
      some (eqType (.succ .zero)) := (infer_const look 0 _ _ _).trans hEq
  have h2 := infer_app (arg := .const (.id aNat) []) h1 (head_forallE look 0 _ _ _)
  have h3 := infer_app (arg := .bvar 0) h2 (head_forallE look 1 _ _ _)
  have h4 := infer_app (arg := .bvar 0) h3 (head_forallE look 2 _ _ _)
  have h5 := infer_forallE (m := default) h4 (head_sort look 3 _)
  exact sortSignature_of h5 (head_sort look 4 _)

/-- The classifier's walk of the first field, as a use of field `0` makes it. -/
theorem ctorType_signature_first {look : Lookup .anon}
    (hEq : look.typeOf (.id aEq) [.succ .zero] = some (eqType (.succ .zero))) :
    fieldSignatures look 5 0 1 [] (ctorType aNat aEq aTrue aP) = some [.zero] := by
  have s0 := quantifiedField_signature aNat aEq hEq []
  show domainSignatures look 5 1 []
    (.forallE (quantifiedField aNat aEq)
      (.forallE (.const (.id aTrue) []) (.const (.id aP) []) default) default) = some [.zero]
  exact domainSignatures_cons s0 rfl

/-- **The classifier's walk of both fields**, as the install makes it. -/
theorem ctorType_signatures {look : Lookup .anon}
    (hEq : look.typeOf (.id aEq) [.succ .zero] = some (eqType (.succ .zero)))
    (hTrue : look.typeOf (.id aTrue) [] = some (.sort .zero)) :
    fieldSignatures look 5 0 2 [] (ctorType aNat aEq aTrue aP) = some [.zero, .zero] := by
  have s0 := quantifiedField_signature aNat aEq hEq []
  have i1 : infer look 5 [quantifiedField aNat aEq] (.const (.id aTrue) []) =
      some (.sort .zero) := (infer_const look 4 _ _ _).trans hTrue
  have s1 : sortSignature look 5 [quantifiedField aNat aEq] (.const (.id aTrue) []) =
      some .zero := sortSignature_of i1 (head_sort look 4 .zero)
  show domainSignatures look 5 2 []
    (.forallE (quantifiedField aNat aEq)
      (.forallE (.const (.id aTrue) []) (.const (.id aP) []) default) default) =
    some [.zero, .zero]
  exact domainSignatures_cons s0 (domainSignatures_cons s1 rfl)

/-- The inferred sorts have the zero-sets of the signatures: `imax 1 0` and `0` are zero at
every assignment. -/
theorem sorts_zero_iff : ∀ j, j < 2 → ∀ φ : Ix.Kernel.LevelParam → Nat,
    Level.eval φ (sorts.getD j .zero) = 0 ↔
      Level.eval φ (([.zero, .zero] : List Level).getD j .zero) = 0 := by
  intro j hj φ
  rcases j with _ | _ | j
  · exact ⟨fun _ => rfl, fun _ => eval_imax_one_zero φ⟩
  · exact Iff.rfl
  · omega

/-- **What a use of field `0` observes**, over any lookup that reads `Eq`'s declared type: the
sort `imax 1 0` of the field's domain, compared with the signature `0`; no earlier field; the
guard level is that sort. -/
theorem use_first {look : Lookup .anon}
    (hEq : look.typeOf (.id aEq) [.succ .zero] = some (eqType (.succ .zero)))
    (cty : Expr .anon) :
    ProjGuardUse look (ctorType aNat aEq aTrue aP) cty 0 0 (.imax (.succ .zero) .zero) :=
  ⟨[.imax (.succ .zero) .zero], [.zero], 5, fun _ => false,
    ctorType_signature_first aNat aEq aTrue aP hEq,
    fun j hj φ => by
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      exact ⟨fun _ => rfl, fun _ => eval_imax_one_zero φ⟩,
    fun j hj => absurd hj (Nat.not_lt_zero j), rfl⟩

/-- **Install and one use over a binding-style store.**

Install: IxC's table stage for the structure (`checkNativeTable` at a one-constructor block
without indices and without parameters), run at the two inferred sorts, stores a table; that
table has its certificate over the witness store `R`, whose raw dictionary reads the
constructor's telescope at the block address `B` and the declared types of `Eq` and `True`.

Use: for every store `E` with `Typing.RecordsFor R E` and every level list, the entry of field
`0` satisfies `Rules.FireSem`. The stored constructor type `cvC.type` is arbitrary: the
certificate reads the table's guards at it and the raw telescope from the store. -/
theorem install_and_use {p : Ix.Kernel.NativeParts .anon} {cvC : ConstantVal .anon}
    {env env₂ : Ix.Kernel.Env .anon} (hidx : p.nIdx = 0) (hnP : p.nP = 0)
    (htbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p [(cvC, 2)]
      [sorts] env = .ok env₂)
    {R : Ixon.Env} {B : _root_.Address}
    (hraw : ctorRaw R B 0 0 = some (ctorType aNat aEq aTrue aP))
    (hEq : (GuardRaw.ofStore R).typeOf (.id aEq) [.succ .zero] = some (eqType (.succ .zero)))
    (hTrue : (GuardRaw.ofStore R).typeOf (.id aTrue) [] = some (.sort .zero)) :
    ∃ tbl : ProjTable .anon,
      env₂.find? (Ix.Kernel.projTableName p.cvT.name) = some (.projInfo tbl) ∧
      ProjGuardCert (GuardRaw.ofStore R) (ctorType aNat aEq aTrue aP) cvC.type tbl ∧
      ∀ E, Typing.RecordsFor R E → ∀ us : List Level,
        Ix.Kernel.Rules.FireSem (tbl.entry 0) us := by
  have hsig : fieldSignatures (GuardRaw.ofStore R) 5 p.nP 2 []
      (ctorType aNat aEq aTrue aP) = some [.zero, .zero] := by
    rw [hnP]
    exact ctorType_signatures aNat aEq aTrue aP hEq hTrue
  obtain ⟨tbl, -, hfind, hnPt, hnFt, -, -, cert⟩ :=
    projGuardCert_of_checkNativeTable (cA := (cvC, 2)) hidx htbl hsig sorts_zero_iff
  refine ⟨tbl, hfind, cert, fun E hRE us => ?_⟩
  have hEq' := (GuardRaw.ofStore_extends_recordsFor hRE).typeOf _ _ _ hEq
  have hf : 0 < tbl.numFields := by rw [hnFt]; exact Nat.zero_lt_two
  have use : ProjGuardUse (GuardRaw.ofStore E) (ctorType aNat aEq aTrue aP) cvC.type
      tbl.numParams 0 (.imax (.succ .zero) .zero) := by
    rw [hnPt, hnP]
    exact use_first aNat aEq aTrue aP hEq' cvC.type
  refine fireSem_of_cert hRE hraw cert (ctorRaw_recordsFor hRE hraw) use hf (fun φ => ?_)
  rw [Level.eval_subst]
  exact eval_imax_one_zero _

end

end IxVM.Refinement.Guard.QuantifiedField
