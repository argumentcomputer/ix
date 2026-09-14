/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer

/-! Syntax that enters all three WHNF cache bodies without transient
literal work. This classification contains no typing or execution resource. -/

namespace Ix.Kernel.Consistency

inductive StructuralWhnfEntry : KExpr .anon → Prop
  | beta {fn arg : KExpr .anon} {appInfo : ExprInfo .anon}
      {name bi domain body info arguments}
      (spine : (KExpr.app fn arg appInfo).collectSpine = (.lam name bi domain body info, arguments)) :
      StructuralWhnfEntry (.app fn arg appInfo)
  | letE (name : Mode.anon.F Name) (domain value body : KExpr .anon)
      (nonDep : Bool) (info : ExprInfo .anon) :
      StructuralWhnfEntry (.letE name domain value body nonDep info)

namespace StructuralWhnfEntry

variable {source : KExpr .anon}

theorem core (entry : StructuralWhnfEntry source) (flags : WhnfFlags) :
    RecM.whnfCoreWithFlags source flags = RecM.whnfCoreWithFlagsNonLeaf source flags := by
  cases entry <;> rfl

theorem noDelta (entry : StructuralWhnfEntry source) (flags : WhnfFlags) (mode : NatSuccMode) :
    RecM.whnfNoDeltaImpl source flags mode = RecM.whnfNoDeltaImplNonLeaf source flags mode := by
  cases entry <;> rfl

theorem full (entry : StructuralWhnfEntry source) (mode : NatSuccMode) :
    RecM.whnfWithNatSuccMode source mode = RecM.whnfWithNatSuccModeNonLeaf source mode := by
  cases entry <;> rfl

theorem sort (entry : StructuralWhnfEntry source) :
    RecM.ensureSortDirect source = RecM.ensureSortWhnf source := by
  cases entry <;> rfl

theorem forallE (entry : StructuralWhnfEntry source) :
    RecM.ensureForallDirect source = RecM.ensureForallWhnf source := by
  cases entry <;> rfl

theorem not_transient (entry : StructuralWhnfEntry source) (methods : Methods .anon) (before : TcState .anon) :
    (RecM.isTransientNatLiteralWork source).run methods before = .ok false before := by
  cases entry with
  | beta spine =>
      simp only [RecM.isTransientNatLiteralWork, RecM.isNatLiteralRecursorApp, spine, pure_bind]
      rfl
  | letE => rfl

end StructuralWhnfEntry

end Ix.Kernel.Consistency
