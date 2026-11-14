module

public import Ix.Compile.BinderData
public import Ix.CompileM

public section

/-!
# Binder-data sections for records that no compile wrote

The compiler writes each record's binder-data section while it builds the
record: the Ix kernel's annotation pass over the record's declarations, installed
from their sources (`Ix.Compile.KernelAnnotate`). Some records IxVM reads have no
source the compiler installs: the model records `IxVM.Model` generates, the closed
role-evidence theorems `kernel-pin-gen` writes, and hand-built test records. Their
sections come from the same kernel's annotation pass run over the Ixon records
(`IxVM.PwHints.annotateRecord`), typed against the records they reference, spelled
in the canonical form (`Ix.Compile.BinderData.sectionOf`). A datum is the zero-ness
of a binder's codomain sort, which is unique, so both routes write the same data
for the same record.

Nothing here is trusted: IxVM validates every datum it reads.
-/

namespace IxVM.RecordSections

open IxVM.PwHints

/-- Whether a member of `c` is unsafe or partial. Such a record carries the
all-undecided section (`Ix.CompileM.undecidedSection`) whatever its data could be, as
the compiler writes it: one canonical record per constant, and IxVM refuses such
constants anyway. -/
def unsafeOrPartial (c : Ixon.Constant) : Bool :=
  let defn (d : Ixon.Definition) : Bool := match d.safety with
    | .safe => false
    | _ => true
  match c.info with
  | .defn d => defn d
  | .recr r => r.isUnsafe
  | .axio a => a.isUnsafe
  | .muts ms => ms.any fun
    | .defn d => defn d
    | .indc i => i.isUnsafe || i.ctors.any (·.isUnsafe)
    | .recr r => r.isUnsafe
  | _ => false

/-- The sections of `records` (by address; a record without a numbered node gets
the empty one), typed against `support`, records the kernel reads without
annotating them, under the role table and prelude `chosen`; `models` are the generated
model records among them, which the kernel view indexes after the environment's. An unsafe or partial
record gets the all-undecided section. With `taint`, a
binder whose datum IxC's datum function cannot compute is the undecided node, as
the compiler writes it; without, it is `never` (deliberately ill-typed test
records, whose rejection should not move to the sentinel). With the pass's
statistics (`IxVM.PwHints.Stats`). -/
def sectionsOfWithStats (records support : Array (Address × Ixon.Constant))
    (blobs : Std.HashMap Address ByteArray)
    (hints : Std.HashMap Address Lean.ReducibilityHints)
    (chosen : Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) (taint : Bool := true)
    (models : Std.HashSet Address := {}) :
    Except String (Std.HashMap Address (Array Ixon.BinderBlock) × Stats) := do
  let view : View := { records, support, blobs, hints, table := some chosen.1.toBytes, models }
  let k ← KernelEnv.ofView view (prelude? := some chosen)
  let (tables, stats) := annotateKernel k (taint := taint)
  let store : Std.HashMap Address Ixon.Constant :=
    records.foldl (fun m (a, c) => m.insert a c) {}
  let mut out : Std.HashMap Address (Array Ixon.BinderBlock) := {}
  for (a, blocks) in tables do
    let some c := store[a]? | continue
    if unsafeOrPartial c then out := out.insert a (← Ix.Compile.BinderData.stripSection c)
    else out := out.insert a (← Ix.Compile.BinderData.sectionOf c blocks)
  return (out, stats)

/-- `sectionsOfWithStats` without the statistics. -/
def sectionsOf (records support : Array (Address × Ixon.Constant))
    (blobs : Std.HashMap Address ByteArray)
    (hints : Std.HashMap Address Lean.ReducibilityHints)
    (chosen : Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) (taint : Bool := true)
    (models : Std.HashSet Address := {}) :
    Except String (Std.HashMap Address (Array Ixon.BinderBlock)) :=
  (·.1) <$> sectionsOfWithStats records support blobs hints chosen taint models

/-- The role table and prelude of `env`: its binding, the prelude read from its
own records when it holds them, and otherwise the committed prelude. -/
def chosenOf (env : Ixon.Env) :
    Except String (Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) := do
  let store : Std.HashMap Address Ixon.Constant := env.consts.fold (init := {}) fun m a lc =>
    match lc.get? with
    | some c => m.insert a c
    | none => m
  match Ix.Compile.BinderData.preludeOf env store with
  | .ok p => pure p
  | .error _ =>
    let table ← match env.roleBinding with
      | some b =>
        (match Ix.Kernel.RoleTable.ofBytes b.bytes with
          | some t => pure t
          | none => throw "record sections: the role binding does not decode")
      | none => Ix.Kernel.Reader.defaultTable
    return (table, ← Ix.Kernel.Reader.preludeFor (md := .anon) table)

/-- `c` with its section, typed against the records of `env` (which `c` may
reference). The record's address changes with its section. -/
def withSection (env : Ixon.Env) (c : Ixon.Constant) (taint : Bool := false) :
    Except String Ixon.Constant := do
  let stripped ← Ix.Compile.BinderData.stripSection c
  let c := { c with binders := stripped }
  let addr := Address.blake3 (Ixon.ser c)
  let support : Array (Address × Ixon.Constant) := env.consts.fold (init := #[]) fun out a lc =>
    if a == addr then out else match lc.get? with
      | some c' => out.push (a, c')
      | none => out
  let sections ← sectionsOf #[(addr, c)] support env.blobs env.anonHints (← chosenOf env) taint
  return { c with binders := sections.getD addr #[] }

end IxVM.RecordSections

end
