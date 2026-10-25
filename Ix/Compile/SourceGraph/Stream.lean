module
public import Ix.CanonM
public import Ix.Compile.SourceGraph.Literal
public import Ix.Ground

@[expose] public section
namespace Ix.Compile.SourceGraph.Stream

/-! Pure prospective streamed input producers. A record is summarized while
its canonical form is live; CanonState is local to one chunk. Existing
ground-error and reserved-flag collection policies are preserved. No live
CompileDriver caller is changed by this module. -/

structure Item where
  graph : Row
  immediate : Option GroundError
  digest : UInt64
  reserved : Bool

def inspect (thin : Environment) (reserved : Bool) (n : Name) (ci : ConstantInfo) : Item :=
  let refs := (GraphM.run { consts := {} } .init (graphConst ci)).1
  let immediate := match groundConstCheck ci thin with | .ok _ => none | .error e => some e
  ⟨rowUsingShared n ci refs, immediate, hash ci, reserved⟩

def step (thin : Environment) (reserved : Lean.ConstantInfo → Bool)
    (p : Name × Lean.ConstantInfo) : CanonM.CanonM Item := do
  let ci ← CanonM.canonConst p.2
  return inspect thin (reserved p.2) p.1 ci

/-- Summarize each record immediately; never construct an array of complete
canonical theorem/opaque records before summarizing it. -/
def chunk (thin : Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Name × Lean.ConstantInfo)) : Array Item :=
  Id.run ((input.mapM (m := CanonM.CanonM) (step thin reserved)).run' {})

def chunkSize (size workers : Nat) : Nat := max 1 ((size + workers - 1) / workers)

/-- Explicit consecutive slices; the max-1 rule covers workers = 0 too. -/
def partition (input : Array α) (workers : Nat) : Array (Array α) :=
  let size := chunkSize input.size workers
  (Array.range ((input.size + size - 1) / size)).map fun j => input.extract (j * size) ((j + 1) * size)

def tasks (thin : Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Name × Lean.ConstantInfo)) (workers : Nat) : Array (Task (Array Item)) :=
  (partition input workers).map fun part => Task.spawn fun _ => chunk thin reserved part

structure Output where
  facts : Collected := {}
  outRefs : Map Name (Ix.Set Name) := {}
  immediate : Map Name GroundError := {}
  digests : Map Name UInt64 := {}
  reservedMetadata : Array Name := #[]

/-- Graph/code use the coherent winner rule. Immediate errors still insert
only on error, and reserved flags still append, exactly as the live collector. -/
def merge (acc : Output) (item : Item) : Output :=
  let ⟨facts, outRefs, immediate, digests, marked⟩ := acc
  let n := item.graph.name
  let outRefs := outRefs.insert n item.graph.node.direct
  let immediate := match item.immediate with | none => immediate | some e => immediate.insert n e
  let digests := digests.insert n item.digest
  let marked := if item.reserved then marked.push n else marked
  ⟨mergeRow facts item.graph, outRefs, immediate, digests, marked⟩

/-- Join in task-array order, then row order; no flattened runtime copy. -/
def join (pending : Array (Task (Array Item))) : Output :=
  pending.foldl (fun acc task => task.get.foldl merge acc) {}

def runLabelled (thin : Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Name × Lean.ConstantInfo)) (workers : Nat) : Output :=
  join (tasks thin reserved input workers)

/-- The existing per-name conversion, from an empty name memo. The full
leanByIx/thin-map prepass is a separate integration obligation. -/
def label (input : Array (Lean.Name × Lean.ConstantInfo)) : Array (Name × Lean.ConstantInfo) :=
  input.map fun (n, ci) => ((Id.run ((CanonM.canonName n).run {})).1, ci)

def runSource (thin : Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat) : Output :=
  runLabelled thin reserved (label input) workers

end Ix.Compile.SourceGraph.Stream
