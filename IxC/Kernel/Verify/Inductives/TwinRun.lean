module

public import IxC.Kernel.Inductives.TwinInstall
public import IxC.Kernel.Semantics.Inductives.DeclRecTwinJ

public section

/-! # Facts from the executable stored-recursor twin checks -/

namespace Ix.Kernel.NativeTwin

open Ix.Kernel.Semantics

def Part.semantic (part : Part md) : TwinRecPart md := {
  cvW := part.raw
  cvW' := part.annotated
  cvC := part.canonical
  kC := part.canonicalKey
  mI := part.majorIndex
  rP := part.rulePrefix
  rulesW := part.rawRules
  rulesW' := part.checkedRules
  rulesC := part.canonicalRules
  model? := part.model? }

@[simp] theorem semantic_models (parts : List (Part md)) :
    twinModels (parts.map Part.semantic) = models parts := by
  simp only [twinModels, models, List.filterMap_map]
  rfl

@[simp] theorem semantic_provision (parts : List (Part md)) :
    twinProv (parts.map Part.semantic) = provision parts := by
  simp only [twinProv, provision, List.map_map]
  rfl

@[simp] theorem semantic_recursors (parts : List (Part md)) :
    twinRecs (parts.map Part.semantic) = recursors parts := by
  simp only [twinRecs, recursors, List.map_map]
  rfl

theorem majorAgrees_spec {majorIndex : Nat} {canonical annotated : Expr md}
    (h : majorAgrees majorIndex canonical annotated = true)
    {bsW : List (Expr md)} {domW bodyW : Expr md} {bmW : BinderMeta}
    (hW : annotated.stripPis majorIndex = some (bsW, .forallE domW bodyW bmW)) :
    ∃ bsC domC bodyC bmC,
      canonical.stripPis majorIndex = some (bsC, .forallE domC bodyC bmC) ∧
      domW.getAppFn = domC.getAppFn ∧ domW.getAppArgs = domC.getAppArgs := by
  simp only [majorAgrees, hW] at h
  split at h
  next bsC domC bodyC bmC hC =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨bsC, domC, bodyC, bmC, hC, h⟩
  next hC => cases h

theorem ruleShape_plain {env : Env md} {part : Part md} {rule : RecRule md}
    (h : ruleShape env part rule = true) (hfire : rule.fire = .plain)
    {cv : ConstantVal md} {nP nF : Nat} (hfind : env.find? rule.ctor = some (.ctorInfo cv nP nF)) :
    Expr.recRulePlain part.annotated.type part.majorIndex part.rulePrefix rule.ctorParams cv.levelParams = true := by
  simpa only [ruleShape, hfire, hfind] using h

theorem ruleShape_nested {env : Env md} {part : Part md} {rule : RecRule md}
    (h : ruleShape env part rule = true) {levels : List Level} {pins : List (Expr md)}
    (hfire : rule.fire = .nested levels pins) :
    ∃ pre dom body bm D,
      part.annotated.type.stripPis part.majorIndex = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D levels ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (part.majorIndex - part.rulePrefix) 0) ++
          (List.range (part.majorIndex - part.rulePrefix)).map
            (fun i => Expr.bvar (part.majorIndex - part.rulePrefix - 1 - i)) := by
  simp only [ruleShape, hfire] at h
  split at h
  next pre dom body bm hshape =>
    split at h
    next D foundLevels hhead =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hargs⟩ := h
      exact ⟨pre, dom, body, bm, D, hshape, hhead, hargs⟩
    next hhead => cases h
  next hshape => cases h

/-- The executable peer map changes only canonical names of this checked group. -/
theorem peerRename_spec (parts : List (Part md)) (key : Key md) :
    peerRename parts key = key ∨
      ∃ part ∈ parts, key = part.canonicalKey ∧ peerRename parts key = part.raw.name := by
  unfold peerRename
  cases hfind : parts.find? (fun part => part.canonicalKey == key) with
  | none => exact .inl rfl
  | some part =>
    obtain ⟨hmem, hkey⟩ := List.find?_some hfind
    exact .inr ⟨part, hmem, (beq_iff_eq.mp hkey).symm, rfl⟩

/-- A successful finishing check chooses one common rule renaming for the complete group. -/
theorem finish_spec {env output : Env md} {parts : List (Part md)}
    (h : finish (m := CheckM md) env parts = .ok output) :
    ∃ rename : Key md → Key md,
      (∀ key, rename key = key ∨ ∃ part ∈ parts, key = part.canonicalKey ∧ rename key = part.raw.name) ∧
      rulesWrap env rename parts = true ∧
      output = ⟨recursors parts ++ models parts ++ env.consts⟩ := by
  unfold finish at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next hwrap =>
    cases h
    rcases Bool.or_eq_true.mp hwrap with hid | hpeer
    · exact ⟨id, fun _ => .inl rfl, hid, rfl⟩
    · exact ⟨peerRename parts, peerRename_spec parts, hpeer, rfl⟩
  next hwrap => cases h

end Ix.Kernel.NativeTwin
