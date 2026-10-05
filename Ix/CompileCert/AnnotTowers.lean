import Ix.CompileCert.AnnotRecRules

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- Check every semantic component of an actual table entry, not merely a
projection occurrence's eventual offset. The owner supplies the universe
telescope for the body and guard levels. Comparison unavailability remains
`none`, independently of declaration-domain membership. -/
def checkInstalledTowerEntry (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (owner : Kernel.Name) (index : Nat) : Option Bool :=
  match source.findProj? owner index, target.findProj? (names owner) index with
  | some sourceEntry, some targetEntry =>
    bothChecks (some (decide (sourceEntry.numParams = targetEntry.numParams ∧
      sourceEntry.numFields = targetEntry.numFields ∧ sourceEntry.off = targetEntry.off ∧
      names sourceEntry.ctor = targetEntry.ctor)))
      (bothChecks (checkInstalledMemberExpr source target names owner
        (Kernel.projTele (sourceEntry.numParams + 1) sourceEntry.body)
        (Kernel.projTele (targetEntry.numParams + 1) targetEntry.body))
        (bothChecks (checkInstalledMemberExpr source target names owner
          (.sort sourceEntry.structSort) (.sort targetEntry.structSort))
          (checkInstalledMemberExpr source target names owner
            (.sort sourceEntry.fieldSort) (.sort targetEntry.fieldSort))))
  | _, _ => some false

structure InstalledTowerEntryComparison (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (owner : Kernel.Name) (index : Nat) (sourceEntry targetEntry : Kernel.ProjEntry) : Prop where
  sourceLookup : source.findProj? owner index = some sourceEntry
  targetLookup : target.findProj? (names owner) index = some targetEntry
  params : sourceEntry.numParams = targetEntry.numParams
  fields : sourceEntry.numFields = targetEntry.numFields
  offset : sourceEntry.off = targetEntry.off
  constructor : names sourceEntry.ctor = targetEntry.ctor
  body : checkInstalledMemberExpr source target names owner
    (Kernel.projTele (sourceEntry.numParams + 1) sourceEntry.body)
    (Kernel.projTele (targetEntry.numParams + 1) targetEntry.body) = some true
  structSort : checkInstalledMemberExpr source target names owner
    (.sort sourceEntry.structSort) (.sort targetEntry.structSort) = some true
  fieldSort : checkInstalledMemberExpr source target names owner
    (.sort sourceEntry.fieldSort) (.sort targetEntry.fieldSort) = some true

theorem checkInstalledTowerEntry_sound {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    {owner : Kernel.Name} {index : Nat} {sourceEntry : Kernel.ProjEntry}
    (sourceLookup : source.findProj? owner index = some sourceEntry)
    (checked : checkInstalledTowerEntry source target names owner index = some true) :
    ∃ targetEntry, InstalledTowerEntryComparison source target names owner index sourceEntry targetEntry := by
  cases targetLookup : target.findProj? (names owner) index with
  | none => simp [checkInstalledTowerEntry, sourceLookup, targetLookup] at checked
  | some targetEntry =>
    simp only [checkInstalledTowerEntry, sourceLookup, targetLookup] at checked
    obtain ⟨shape, body, structSort, fieldSort⟩ :=
      And.intro (bothChecks_true checked).1
        (And.intro (bothChecks_true (bothChecks_true checked).2).1
          (bothChecks_true (bothChecks_true (bothChecks_true checked).2).2))
    have fields := of_decide_eq_true (Option.some.inj shape)
    exact ⟨targetEntry, sourceLookup, targetLookup, fields.1, fields.2.1,
      fields.2.2.1, fields.2.2.2, body, structSort, fieldSort⟩

/-- Full source table coverage includes entries which are never mentioned by
an expression. Extra admitted target support tables need no source preimage. -/
def checkInstalledTowers (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  source.consts.foldr (fun entry rest => bothChecks
    (match entry with
    | .projInfo table => (List.range table.numFields).foldr (fun index rest =>
        bothChecks (checkInstalledTowerEntry source target names table.structName index) rest) (some true)
    | _ => some true) rest) (some true)

theorem checkInstalledTowers_entry {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledTowers source target names = some true)
    {owner : Kernel.Name} {index : Nat} {entry : Kernel.ProjEntry}
    (lookup : source.findProj? owner index = some entry) :
    checkInstalledTowerEntry source target names owner index = some true := by
  unfold Kernel.Env.findProj? at lookup
  cases tableLookup : source.find? (Kernel.projTableName owner) with
  | none => simp [tableLookup] at lookup
  | some info =>
    cases info <;> simp only [tableLookup] at lookup
    case projInfo table =>
      split at lookup
      next inside =>
        have name := Kernel.Semantics.Env.find?_name tableLookup
        change Kernel.projTableName table.structName = Kernel.projTableName owner at name
        have ownerEq : table.structName = owner := Kernel.projTableName_inj name
        have row := bothChecks_fold_true checked _ (Kernel.Semantics.Env.find?_mem tableLookup)
        have result := bothChecks_fold_true row index (List.mem_range.mpr inside)
        simpa only [ownerEq] using result
      next => contradiction
    all_goals contradiction

end Ix.CompileCert
