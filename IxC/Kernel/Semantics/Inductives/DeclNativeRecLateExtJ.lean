module

public import IxC.Kernel.Semantics.Inductives.DeclNativeRecLateJ
public import IxC.Kernel.Semantics.Inductives.DeclNativeExtJ

@[expose] public section

/-!
# A recursor for a stored native family: the extension and the η-families

Facts about the late recursor's step (`DeclNativeRecLateRunJ`) that read only its freshness
guard and its cons, so they hold at every package:

* what the store holds of the family is lookups only, kept by every extension
  (`NativeFamStored.ext`), and it reads at the recursor's record, whose family projections are
  the family's (`NativeFamStored.atRec`);
* the step extends the environment (`declNativeRecLateRunJ_envExt`): the recursor is fresh and
  passes the front door's shape test, so it is no structure's projection table;
* the step keeps the η-families closed (`declNativeRecLateRunJ_etaClosed`): the head is a
  recursor, not an inductive type.
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Env Expr ConstantVal NativeParts RecRule EnvExt EtaFamiliesClosed
  projTableName)

/-- **What the store holds of a family is kept by every extension**: lookups and facts about
the summary only. -/
theorem NativeFamStored.ext {env env' : Env md} {fam : NativeFam md} (hext : EnvExt env env')
    (h : NativeFamStored env fam) : NativeFamStored env' fam where
  former := hext.find h.former
  ctor j cA hj := ⟨hext.find (h.ctor j cA hj).1, (h.ctor j cA hj).2⟩
  lenA := h.lenA
  lenK := h.lenK

/-- **What the store holds of a family, at a recursor record over it**: every family projection
of `fam.recParts` is the family's, so the lookups and counts read at the record. -/
theorem NativeFamStored.atRec {env : Env md} {fam : NativeFam md} (h : NativeFamStored env fam)
    {pR : NativeParts md} {cvR : ConstantVal md} {elim : LevelParam} {large : Bool}
    {rhs₀ : List (Expr md)} (hpR : pR = fam.recParts cvR elim large rhs₀) :
    env.find? pR.cvT.name = some (.indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p)) ∧
    (∀ (j : Nat) (cA : ConstantVal md × Nat), fam.ctorsA[j]? = some cA →
      env.find? cA.1.name = some (.ctorInfo cA.1 pR.nP cA.2) ∧
      cA.1.levelParams = pR.cvT.levelParams ∧
      ∃ cbs es, cA.1.type.stripPis (pR.nP + cA.2) = some (cbs,
        Expr.mkAppN (.const pR.cvT.name (pR.cvT.levelParams.map .param))
          (Ix.Kernel.structPsAt cA.2 pR.nP ++ es)) ∧
        es.length = pR.nIdx) ∧
    fam.ctorsA.length = pR.ctors.length ∧ fam.ctorsA.length = pR.kinds.length := by
  subst hpR
  exact ⟨h.former, h.ctor, h.lenA, h.lenK⟩

/-- **The late recursor's step extends the environment**, over a package: the recursor is fresh
and passes the front door's shape test, so it is no stored structure's table. -/
theorem declNativeRecLateRunJ_envExt {J : Judgements md} {env env₂ : Env md}
    {fam : NativeFam md} {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (h : DeclNativeRecLateRunJ J env fam cvR mI rP rules env₂) : EnvExt env env₂ := by
  obtain ⟨_, _, _, cvRa, _, -, -, -, -, -, -, -, -, hRec, rfl⟩ := h
  obtain ⟨hnR, -, hfR, hshR⟩ := hRec.recursor
  refine EnvExt.cons ?_ ?_
  · show env.find? cvRa.name = none
    rw [hnR]; exact hfR
  · intro T _ _ _
    show cvRa.name ≠ projTableName T
    rw [hnR]; exact ne_projTableName_of_shape hshR T

/-- **The late recursor's step keeps the η-families closed**, over a package: its one cons is
fresh and is not an inductive type. -/
theorem declNativeRecLateRunJ_etaClosed {J : Judgements md} {env env₂ : Env md}
    {fam : NativeFam md} {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hE : EtaFamiliesClosed env) (h : DeclNativeRecLateRunJ J env fam cvR mI rP rules env₂) :
    EtaFamiliesClosed env₂ := by
  obtain ⟨_, _, _, cvRa, _, -, -, -, -, -, -, -, -, hRec, rfl⟩ := h
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  exact Ix.Kernel.EtaFamiliesClosed.cons_nonind hE
    (show env.find? cvRa.name = none by rw [hnR]; exact hfR) (fun _ _ heq => nomatch heq)

end Ix.Kernel.Semantics
