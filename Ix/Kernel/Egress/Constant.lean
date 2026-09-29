/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Egress.Expr
import Ix.Kernel.Ingress.Constant

namespace Ix.Kernel.Egress

/-- Zip without truncating either input. -/
def zipExact (f : α → β → Option γ) : List α → List β → Option (List γ)
  | [], [] => some []
  | a :: as, b :: bs => return (← f a b) :: (← zipExact f as bs)
  | _, _ => none

theorem zipExact_reading {R : α → β → Prop} {layout : α → γ} {rebuild : γ → β → Option α}
    {sources : List α} {targets : List β} (h : Forall₂ R sources targets)
    (hf : ∀ a b, R a b → rebuild (layout a) b = some a) :
    zipExact rebuild (sources.map layout) targets = some sources := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [zipExact, hf _ _ head, ih]

theorem zipExact_reading_map {R : α → β → Prop} {layout : α → γ} {result : α → δ}
    {rebuild : γ → β → Option δ} {sources : List α} {targets : List β}
    (h : Forall₂ R sources targets)
    (hf : ∀ a b, R a b → rebuild (layout a) b = some (result a)) :
    zipExact rebuild (sources.map layout) targets = some (sources.map result) := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [zipExact, hf _ _ head, ih]

def definitionSafety : Safety → Ix.DefinitionSafety
  | .safe => .safe
  | .unsafe => .unsaf
  | .partial => .part

def unsafeFlag : Safety → Option Bool
  | .safe => some false
  | .unsafe => some true
  | .partial => none

def definitionKind : DefKind → Ix.DefKind
  | .definition => .defn
  | .opaque => .opaq
  | .theorem => .thm

def quotientKind : QuotKind → Ix.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

@[simp] theorem definitionSafety_reading (s : Ix.DefinitionSafety) :
    definitionSafety (Ingress.safety s) = s := by cases s <;> rfl

@[simp] theorem unsafeFlag_reading (s : Bool) : unsafeFlag (Ingress.unsafeFlag s) = some s := by
  cases s <;> rfl

@[simp] theorem definitionKind_reading (k : Ix.DefKind) : definitionKind (Ingress.kind k) = k := by
  cases k <;> rfl

@[simp] theorem quotientKind_reading (k : Ix.QuotKind) : quotientKind (Ingress.quotientKind k) = k := by
  cases k <;> rfl

structure DefinitionLayout where
  type : ExprLayout
  value : ExprLayout

def DefinitionLayout.ofDefinition (source : Ixon.Definition) : DefinitionLayout :=
  ⟨.ofExpr source.typ, .ofExpr source.value⟩

def DefinitionLayout.rebuild (layout : DefinitionLayout) : Const Address → Option Ixon.Definition
  | .defn uvars kind type value safety => return {
      kind := definitionKind kind
      safety := definitionSafety safety
      lvls := ← word uvars
      typ := ← layout.type.rebuild type
      value := ← layout.value.rebuild value }
  | _ => none

theorem DefinitionLayout.rebuild_reading {ctx : Ingress.Context} {source : Ixon.Definition}
    {target : Const Address} (h : Ingress.DefinitionReads ctx source target) :
    (ofDefinition source).rebuild target = some source := by
  cases h with
  | mk type value =>
    simp [ofDefinition, rebuild, ExprLayout.rebuild_reading type, ExprLayout.rebuild_reading value]

def rebuildRule (layout : ExprLayout) (target : RecRule Address) : Option Ixon.RecursorRule :=
  return ⟨← word target.nfields, ← layout.rebuild target.rhs⟩

theorem rebuildRule_reading {ctx : Ingress.Context} {source : Ixon.RecursorRule}
    {target : RecRule Address} (h : Ingress.RuleReads ctx source target) :
    rebuildRule (.ofExpr source.rhs) target = some source := by
  simp [rebuildRule, h.1, ExprLayout.rebuild_reading h.2]

def rebuildConstructor (layout : ExprLayout × Nat) (target : Ctor Address) : Option Ixon.Constructor :=
  return {
    isUnsafe := ← unsafeFlag target.safety
    lvls := ← word target.uvars
    cidx := ← word layout.2
    params := ← word target.nparams
    fields := ← word target.nfields
    typ := ← layout.1.rebuild target.type }

theorem rebuildConstructor_reading {ctx : Ingress.Context} {source : Ixon.Constructor × Nat}
    {target : Ctor Address} (h : Ingress.ConstructorReads ctx source target) :
    rebuildConstructor (.ofExpr source.1.typ, source.2) target = some source.1 := by
  obtain ⟨index, universes, params, fields, safety, type⟩ := h
  simp [rebuildConstructor, ← index, universes, params, fields, safety, ExprLayout.rebuild_reading type]

structure RecursorLayout where
  type : ExprLayout
  rules : List ExprLayout

def RecursorLayout.ofRecursor (source : Ixon.Recursor) : RecursorLayout :=
  ⟨.ofExpr source.typ, source.rules.toList.map fun r => .ofExpr r.rhs⟩

def RecursorLayout.rebuild (layout : RecursorLayout) : Const Address → Option Ixon.Recursor
  | .recursor uvars params indices motives minors type rules k safety => return {
      k
      isUnsafe := ← unsafeFlag safety
      lvls := ← word uvars
      params := ← word params
      indices := ← word indices
      motives := ← word motives
      minors := ← word minors
      typ := ← layout.type.rebuild type
      rules := (← zipExact rebuildRule layout.rules rules).toArray }
  | _ => none

theorem RecursorLayout.rebuild_reading {ctx : Ingress.Context} {source : Ixon.Recursor}
    {target : Const Address} (h : Ingress.RecursorReads ctx source target) :
    (ofRecursor source).rebuild target = some source := by
  cases h with
  | mk type rules =>
    have hr := zipExact_reading rules (fun _ _ h => rebuildRule_reading h)
    simp [ofRecursor, rebuild, ExprLayout.rebuild_reading type, hr]

structure InductiveLayout where
  type : ExprLayout
  constructors : List (ExprLayout × Nat)

def InductiveLayout.ofInductive (source : Ixon.Inductive) : InductiveLayout :=
  ⟨.ofExpr source.typ, source.ctors.toList.zipIdx.map fun (c, i) => (.ofExpr c.typ, i)⟩

def InductiveLayout.rebuild (layout : InductiveLayout) : Const Address → Option Ixon.Inductive
  | .induct uvars params indices type constructors safety => return {
      isUnsafe := ← unsafeFlag safety
      lvls := ← word uvars
      params := ← word params
      indices := ← word indices
      typ := ← layout.type.rebuild type
      ctors := (← zipExact rebuildConstructor layout.constructors constructors).toArray }
  | _ => none

theorem InductiveLayout.rebuild_reading {ctx : Ingress.Context} {source : Ixon.Inductive}
    {target : Const Address} (h : Ingress.InductiveReads ctx source target) :
    (ofInductive source).rebuild target = some source := by
  cases h with
  | mk type constructors =>
    have hc := zipExact_reading_map constructors (fun _ _ h => rebuildConstructor_reading h)
    simp [ofInductive, rebuild, ExprLayout.rebuild_reading type, hc]

inductive MemberLayout where
  | defn (layout : DefinitionLayout)
  | indc (layout : InductiveLayout)
  | recr (layout : RecursorLayout)

def MemberLayout.ofMember : Ixon.MutConst → MemberLayout
  | .defn source => .defn (.ofDefinition source)
  | .indc source => .indc (.ofInductive source)
  | .recr source => .recr (.ofRecursor source)

def MemberLayout.rebuild : MemberLayout → Const Address → Option Ixon.MutConst
  | .defn layout, target => (layout.rebuild target).map .defn
  | .indc layout, target => (layout.rebuild target).map .indc
  | .recr layout, target => (layout.rebuild target).map .recr

theorem MemberLayout.rebuild_reading {ctx : Ingress.Context} {source : Ixon.MutConst}
    {target : Const Address} (h : Ingress.MemberReads ctx source target) :
    (ofMember source).rebuild target = some source := by
  cases h with
  | defn reading => simp [ofMember, rebuild, DefinitionLayout.rebuild_reading reading]
  | indc reading => simp [ofMember, rebuild, InductiveLayout.rebuild_reading reading]
  | recr reading => simp [ofMember, rebuild, RecursorLayout.rebuild_reading reading]

inductive InfoLayout where
  | defn (layout : DefinitionLayout)
  | recr (layout : RecursorLayout)
  | axio (type : ExprLayout)
  | quot (type : ExprLayout)
  | muts (members : List MemberLayout)
  | projection

def InfoLayout.ofInfo : Ixon.ConstantInfo → InfoLayout
  | .defn source => .defn (.ofDefinition source)
  | .recr source => .recr (.ofRecursor source)
  | .axio source => .axio (.ofExpr source.typ)
  | .quot source => .quot (.ofExpr source.typ)
  | .muts members => .muts (members.toList.map .ofMember)
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ => .projection

def InfoLayout.rebuild (layout : InfoLayout) (target : Block Address) : Option Ixon.ConstantInfo :=
  match layout, target.members with
  | .defn layout, [target] => (layout.rebuild target).map .defn
  | .recr layout, [target] => (layout.rebuild target).map .recr
  | .axio layout, [.axiom uvars type safety] => do
    return .axio ⟨← unsafeFlag safety, ← word uvars, ← layout.rebuild type⟩
  | .quot layout, [.quot kind uvars type] => do
    return .quot ⟨quotientKind kind, ← word uvars, ← layout.rebuild type⟩
  | .muts layouts, targets => return .muts (← zipExact MemberLayout.rebuild layouts targets).toArray
  | _, _ => none

theorem InfoLayout.rebuild_reading {ctx : Ingress.Context} {source : Ixon.ConstantInfo}
    {target : Block Address} (h : Ingress.InfoReads ctx source target) :
    (ofInfo source).rebuild target = some source := by
  cases h with
  | defn reading => simp [ofInfo, rebuild, DefinitionLayout.rebuild_reading reading]
  | recr reading => simp [ofInfo, rebuild, RecursorLayout.rebuild_reading reading]
  | axio reading => simp [ofInfo, rebuild, ExprLayout.rebuild_reading reading]
  | quot reading => simp [ofInfo, rebuild, ExprLayout.rebuild_reading reading]
  | muts reading =>
    have hm := zipExact_reading reading (fun _ _ h => MemberLayout.rebuild_reading h)
    simp [ofInfo, rebuild, hm]

/-- Tables retain their original order, including unused entries. They are
layout data, not evidence of typing, canonicality, or address authentication. -/
structure ConstantLayout where
  info : InfoLayout
  sharing : Array Ixon.Expr
  refs : Array Address
  univs : Array Ixon.Univ

def ConstantLayout.ofConstant (source : Ixon.Constant) : ConstantLayout :=
  ⟨.ofInfo source.info, source.sharing, source.refs, source.univs⟩

def ConstantLayout.rebuild (layout : ConstantLayout) (target : Block Address) : Option Ixon.Constant :=
  return ⟨← layout.info.rebuild target, layout.sharing, layout.refs, layout.univs⟩

theorem ConstantLayout.rebuild_reading {ctx : Ingress.Context} {target : Block Address}
    (h : Ingress.BlockReads ctx target) :
    (ofConstant ctx.source).rebuild target = some ctx.source := by
  simp [ofConstant, rebuild, InfoLayout.rebuild_reading h]

/-- Check the reconstructed constant against the complete kernel block. -/
def writeBlockC (ctx : Ingress.Context) (fuel : Nat) (layout : ConstantLayout)
    (target : Block Address) : Search { source : Ixon.Constant //
      Ingress.BlockReads { ctx with source } target } := do
  let some source := layout.rebuild target |
    throw (.malformed "declaration does not fit its Ixon layout or metadata exceeds UInt64")
  let reading ← Ingress.readBlockC { ctx with source } fuel
  if same : reading.val = target then
    return ⟨source, same ▸ reading.property⟩
  else throw (.malformed "Ixon layout resolves to a different kernel declaration")

def writeBlock (ctx : Ingress.Context) (fuel : Nat) (layout : ConstantLayout)
    (target : Block Address) : Search Ixon.Constant :=
  (writeBlockC ctx fuel layout target).map Subtype.val

theorem writeBlock_reading {ctx : Ingress.Context} {fuel : Nat} {layout : ConstantLayout}
    {target : Block Address} {source : Ixon.Constant}
    (h : writeBlock ctx fuel layout target = .ok source) :
    Ingress.BlockReads { ctx with source } target := by
  obtain ⟨result, _, same⟩ := Except.map_eq_ok h
  exact same ▸ result.property

theorem writeBlock_roundtrip {ctx : Ingress.Context} {fuel : Nat} {target : Block Address}
    (h : Ingress.readBlock ctx fuel = .ok target) :
    writeBlock ctx fuel (ConstantLayout.ofConstant ctx.source) target = .ok ctx.source := by
  have rebuilt := ConstantLayout.rebuild_reading (Ingress.readBlock_reading h)
  unfold Ingress.readBlock at h
  obtain ⟨reading, success, same⟩ := Except.map_eq_ok h
  simp [writeBlock, writeBlockC, rebuilt, success, bind, pure, Except.bind, Except.pure, Except.map, same]

end Ix.Kernel.Egress
