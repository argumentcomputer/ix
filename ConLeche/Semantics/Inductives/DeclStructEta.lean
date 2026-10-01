module

import ConLeche.Semantics.DeclIndRun
public import ConLeche.Semantics.IndBlockRun
import ConLeche.Semantics.DeclEta
import ConLeche.Verify.Extend.Inversions

import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.StructInv

@[expose] public section

/-!
# The direct-structure declaration keeps the η-families closed (task #175 wiring, W5)

The declaration fold's η half at the `.indDecl` dispatch: the modeled
arm is `declIndEtaClosedRun` (`IndBlockRun`), and the direct arm is
proved here from `DeclStructRun`'s recorded runs — every store the
direct install performs is a **fresh cons** (`checkConstantVal`'s
duplicate guard for the three constants, `checkStructProj`'s own
`isNone` guard for the entries), and the one former it stores carries
`structCaps`, whose `eta` slot is a literal `false`, so
`EtaFamiliesClosed.cons_nonind` applies at every step.

With this the two dispatch lemmas below make the fold's η half
**flag-agnostic**: `declStep_preserves` (`Model/FoldP`) and `declEtaStep` read
the kernel's own `structParts?` dispatch and no longer consult
the former master switch (gone at W4c).
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  StructParts fueledOps checkConstantVal
  checkStructProjTable projTableName EtaFamiliesClosed ProjEntry)

/-! ## The stage shapes, with their freshness guards -/

/-- The table stage's run: the tower table consed at a fresh table
name (task #175 S1). -/
theorem checkStructProjTable_shape {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {guards : List Level} {off : Nat} {cvCa : ConstantVal} {env env' : Env}
    (h : checkStructProjTable (m := ConLeche.CheckM) T C lps nP nF
      resSort guards off cvCa env = .ok env') :
    ∃ tbl : ConLeche.ProjTable, env.find? (projTableName T) = none ∧
      tbl.structName = T ∧ env' = ⟨.projInfo tbl :: env.consts⟩ := by
  obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := ConLeche.checkStructProjTable_inv h
  exact ⟨_, hfresh, rfl, rfl⟩

/-! ## The η half of the direct arm -/

/-- The table stage keeps the η-families closed: a fresh cons of a
table. -/
theorem checkStructProjTable_etaClosed {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {guards : List Level} {off : Nat} {cvCa : ConstantVal} {env env₂ : Env}
    (h : checkStructProjTable (m := ConLeche.CheckM) T C lps nP nF
      resSort guards off cvCa env = .ok env₂)
    (hE : EtaFamiliesClosed env) : EtaFamiliesClosed env₂ := by
  obtain ⟨tbl, hfresh, hsn, rfl⟩ := checkStructProjTable_shape h
  refine EtaFamiliesClosed.cons_nonind hE ?_ (fun _ _ heq => nomatch heq)
  show env.find? (projTableName tbl.structName) = none
  rw [hsn]; exact hfresh

end ConLeche.Semantics
