import Ix.IxVM.ClaimHarness
import Ix.ClaimContext
import Ix.EnvScope
import Tests.Ix.IxVM.Harness

/-!
# Adversarial mutator over real inductive blocks and recursor records

Draw real compiled `muts` blocks (from `ix compile` of a corpus) that hold an
inductive member or a recursor member, mutate a structural field, project the
mutated member, and submit a `check` claim through IxVM in circuit-verdict mode
(`Tests.Ix.IxVM.Harness`). Two oracles:

- for inductives, Lean's kernel: the mutated field (a constructor's universe
  count, a parameter or index count, a safety flag, a stored constructor index,
  an elimination/universe field) is never varied independently by an honest
  compile, so the mutated record is not one Lean's kernel and compiler produce,
  and it must be rejected;
- for recursors, which Lean's kernel cannot be handed, the recursor Lean
  regenerates from the inductive: the honest compiled record is that canonical
  recursor, so a record that differs from it (every mutation here changes a
  checked field) must be rejected.

A mutation that IxVM accepts is a finding, with its fixture (the mutated block's
Ixon). A class IxVM is known to accept (`knownFindings`) is run for the report
only; every other class is gated, and the gate fails on any acceptance.

Run with a fixed seed (`IX_MUT_SEED`, default 1) and a budget
(`IX_MUT_BUDGET`, default 64 mutations per class). The corpus is
`IX_MUT_MODULES` (default a small set rich in inductives and recursors).
-/

namespace Tests.Ix.IxVM.Mutator

open IxVM.ClaimHarness

/-- A tiny deterministic PRNG, so a run is reproducible from its seed. -/
def nextRand (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13); let s := s ^^^ (s >>> 7); s ^^^ (s <<< 17)

/-- The mutation classes. The name is the finding's identifier. -/
inductive Mut where
  | ctorUniv        -- a constructor's universe count (+1)
  | indParams       -- an inductive's parameter count (+1)
  | indIndices      -- an inductive's index count (+1)
  | ctorFields      -- a constructor's stored field count (+1)
  | ctorIndex       -- a constructor's stored index (swap with a sibling)
  | indSafety       -- flip the safety flag of an inductive with constructors
  | recLvls         -- a recursor's universe count (+1)
  | recMotives      -- move one motive into minors (their sum preserved)
  | recParams       -- a recursor's parameter count (+1)
  | recIndices      -- a recursor's index count (+1)
  | recK            -- flip a recursor's K flag
  | recRuleFields   -- a rule's stored field count (+1)
  deriving Repr, BEq, DecidableEq

def Mut.all : List Mut :=
  [.ctorUniv, .indParams, .indIndices, .ctorFields, .ctorIndex, .indSafety,
   .recLvls, .recMotives, .recParams, .recIndices, .recK, .recRuleFields]

def Mut.name : Mut → String
  | .ctorUniv => "ctor-universe-count" | .indParams => "inductive-param-count"
  | .indIndices => "inductive-index-count" | .ctorFields => "ctor-field-count"
  | .ctorIndex => "ctor-stored-index" | .indSafety => "inductive-safety-flag"
  | .recLvls => "recursor-universe-count" | .recMotives => "recursor-motives-minors-split"
  | .recParams => "recursor-param-count" | .recIndices => "recursor-index-count"
  | .recK => "recursor-k-flag" | .recRuleFields => "recursor-rule-field-count"

/-- Whether an oracle is the kernel (inductive) or the regenerated recursor. -/
def Mut.oracle : Mut → String
  | .recLvls | .recMotives | .recParams | .recIndices | .recK | .recRuleFields =>
    "differs from the recursor Lean regenerates from the inductive"
  | _ => "a record no honest Lean compile produces (Lean's kernel refuses it)"

/-- Classes IxVM is known to accept some instances of, with the review finding
each belongs to. They run for the report only; the other classes are gated. -/
def knownFindings : List (Mut × String) := [(.recLvls, "review finding K1-5(e)")]

/-- Apply a mutation to the `idx`-th member of a `muts` block, returning the
mutated member and a projection of it, or `none` when the class does not apply
to that member. `r` is a random word for the mutations that need a choice. -/
def mutateMember (ms : Array Ixon.MutConst) (idx : Nat) (m : Mut) (r : UInt64) :
    Option (Array Ixon.MutConst × (Address → Ixon.ConstantInfo)) := do
  let member := ms[idx]!
  match m, member with
  | .ctorUniv, .indc ind => do
    guard (!ind.ctors.isEmpty)
    let ci := (r.toNat % ind.ctors.size)
    let ctors := ind.ctors.modify ci fun k => { k with lvls := k.lvls + 1 }
    some (ms.set! idx (.indc { ind with ctors }), fun b => .cPrj ⟨idx.toUInt64, ci.toUInt64, b⟩)
  | .indParams, .indc ind =>
    some (ms.set! idx (.indc { ind with params := ind.params + 1 }), fun b => .iPrj ⟨idx.toUInt64, b⟩)
  | .indIndices, .indc ind =>
    some (ms.set! idx (.indc { ind with indices := ind.indices + 1 }), fun b => .iPrj ⟨idx.toUInt64, b⟩)
  | .ctorFields, .indc ind => do
    guard (!ind.ctors.isEmpty)
    let ci := (r.toNat % ind.ctors.size)
    -- listed field modes stay listed, the new field inherited
    let ctors := ind.ctors.modify ci fun k => { k with
      fields := k.fields + 1
      fieldModes := Ixon.FieldModes.ofArray (k.fieldModes.toArray.push .inherited) }
    some (ms.set! idx (.indc { ind with ctors }), fun b => .cPrj ⟨idx.toUInt64, ci.toUInt64, b⟩)
  | .ctorIndex, .indc ind => do
    guard (ind.ctors.size ≥ 2)
    let ctors := ind.ctors.mapIdx fun i k => { k with cidx := (ind.ctors.size - 1 - i).toUInt64 }
    some (ms.set! idx (.indc { ind with ctors }), fun b => .iPrj ⟨idx.toUInt64, b⟩)
  | .indSafety, .indc ind => do
    -- Only with a constructor: flipping the inductive's flag then leaves it
    -- disagreeing with its constructors' (one `inductDecl` has one safety flag),
    -- a record no honest compile produces. A zero-constructor inductive has no
    -- second flag, so the flip is just a valid `unsafe inductive` Lean accepts.
    guard (!ind.ctors.isEmpty)
    some (ms.set! idx (.indc { ind with isUnsafe := !ind.isUnsafe }), fun b => .iPrj ⟨idx.toUInt64, b⟩)
  | .recLvls, .recr rc =>
    some (ms.set! idx (.recr { rc with lvls := rc.lvls + 1 }), fun b => .rPrj ⟨idx.toUInt64, b⟩)
  | .recMotives, .recr rc => do
    guard (rc.motives ≥ 1)
    some (ms.set! idx (.recr { rc with motives := rc.motives - 1, minors := rc.minors + 1 }),
      fun b => .rPrj ⟨idx.toUInt64, b⟩)
  | .recParams, .recr rc =>
    some (ms.set! idx (.recr { rc with params := rc.params + 1 }), fun b => .rPrj ⟨idx.toUInt64, b⟩)
  | .recIndices, .recr rc =>
    some (ms.set! idx (.recr { rc with indices := rc.indices + 1 }), fun b => .rPrj ⟨idx.toUInt64, b⟩)
  | .recK, .recr rc =>
    some (ms.set! idx (.recr { rc with k := !rc.k }), fun b => .rPrj ⟨idx.toUInt64, b⟩)
  | .recRuleFields, .recr rc => do
    guard (!rc.rules.isEmpty)
    let ri := (r.toNat % rc.rules.size)
    let rules := rc.rules.modify ri fun rule => { rule with fields := rule.fields + 1 }
    some (ms.set! idx (.recr { rc with rules }), fun b => .rPrj ⟨idx.toUInt64, b⟩)
  | _, _ => none

/-- Store the mutated block and every projection wrapper its closure walk needs,
return the projected target of the mutated member. -/
def storeMutated (env : Ixon.Env) (block : Ixon.Constant) (ms : Array Ixon.MutConst)
    (proj : Address → Ixon.ConstantInfo) : Ixon.Env × Address := Id.run do
  let block := { block with info := .muts ms }
  let blockAddr := Address.blake3 (Ixon.ser block)
  let mut env := env.storeConst blockAddr block
  -- store every member's projection wrapper, so the transitive walk resolves
  for i in [:ms.size] do
    let member := ms[i]!
    let info : Ixon.ConstantInfo := match member with
      | .defn _ => .dPrj ⟨i.toUInt64, blockAddr⟩
      | .indc _ => .iPrj ⟨i.toUInt64, blockAddr⟩
      | .recr _ => .rPrj ⟨i.toUInt64, blockAddr⟩
    let wrapper : Ixon.Constant := ⟨info, #[], #[], #[], #[]⟩
    let a := Address.blake3 (Ixon.ser wrapper)
    env := env.storeConst a wrapper
    match member with
    | .indc ind =>
      for ci in [:ind.ctors.size] do
        let cw : Ixon.Constant := ⟨.cPrj ⟨i.toUInt64, ci.toUInt64, blockAddr⟩, #[], #[], #[], #[]⟩
        env := env.storeConst (Address.blake3 (Ixon.ser cw)) cw
    | .defn _ => env := { env with anonHints := env.anonHints.insert a (.regular 0) }
    | _ => pure ()
  let target : Ixon.Constant := ⟨proj blockAddr, #[], #[], #[], #[]⟩
  (env, Address.blake3 (Ixon.ser target))

/-- Real `muts` blocks of `env` that hold an inductive or recursor member,
by address order (deterministic). -/
def targetBlocks (env : Ixon.Env) : Array (Address × Ixon.Constant) := Id.run do
  let mut out : Array (Address × Ixon.Constant) := #[]
  for (a, lc) in env.consts do
    if let some c := lc.get? then
      if let .muts ms := c.info then
        if ms.any (fun m => match m with | .indc _ | .recr _ => true | _ => false) then
          out := out.push (a, c)
  return out.qsort (fun x y => x.1.hash.data < y.1.hash.data)

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let raw := (← IO.getEnv "IX_MUT_MODULES").getD "Init.Data.Nat.Basic,Init.Data.List.Basic,Init.Prelude"
  let budget := ((← IO.getEnv "IX_MUT_BUDGET").bind String.toNat?).getD 64
  let seed := UInt64.ofNat (((← IO.getEnv "IX_MUT_SEED").bind String.toNat?).getD 1)
  let prefixes := (raw.splitOn ",").filterMap fun s =>
    let s := s.trimAscii.toString; if s.isEmpty then none else some s.toName
  let moduleNames := leanEnv.allImportedModuleNames
  let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
    match leanEnv.getModuleIdxFor? n with
    | some idx => if prefixes.any (·.isPrefixOf moduleNames[idx.toNat]!) then some n else none
    | none => none
  let constants := Ix.EnvScope.collectSelectedDeps leanEnv seeds
  let ixon ← loadSharedIxonEnv (constants.map Prod.fst).toArray leanEnv
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv ixon true)
  let blocks := targetBlocks ixon
  IO.println s!"[ixvm-mutator] corpus {prefixes}: {constants.length} constants, \
    {blocks.size} mutable blocks; seed {seed}, budget {budget}/class"
  -- Build mutated cases, class by class, each required to be REJECTED.
  let mut cases : Array (Mut × Address × Address × Ixon.Env) := #[]
  -- The same (block, mutation) can be drawn twice and gives one target address:
  -- keep the first, so every case is distinct (the runner refuses repeated labels).
  let mut seen : Std.HashSet Address := {}
  let mut rng := seed
  for m in Mut.all do
    let mut made := 0
    let mut bi := 0
    while made < budget && bi < blocks.size do
      rng := nextRand rng
      let (ba, block) := blocks[(rng.toNat + bi) % blocks.size]!
      bi := bi + 1
      let .muts ms := block.info | continue
      -- pick a member the class applies to
      let mut placed := false
      for mi in [:ms.size] do
        if placed then continue
        rng := nextRand rng
        if let some (ms', proj) := mutateMember ms mi m rng then
          let (env', target) := storeMutated ixon block ms' proj
          unless seen.contains target do
            seen := seen.insert target
            cases := cases.push (m, ba, target, env')
            made := made + 1
          placed := true
  IO.println s!"[ixvm-mutator] {cases.size} distinct mutations built"
  -- Every mutation must be REJECTED: it is a record Lean's kernel refuses, or a
  -- recursor that differs from the one Lean regenerates. The gate runs the
  -- classes NOT on the known list and fails on any acceptance (a finding). A
  -- known-finding class is run separately and only reported: IxVM accepts some
  -- of its instances (the finding) and may reject others, so neither verdict
  -- fails the gate.
  let known : List Mut := knownFindings.map Prod.fst
  let toBuilder (c : Mut × Address × Address × Ixon.Env) : Builder :=
    let (m, ba, target, env') := c
    fun _ => do
      return { label := s!"mut {m.name} of {ba} → {target}", accept := false
               witness := ← buildClaimWitness env' (.check ctx target none) }
  let gated := cases.filter fun c => !known.contains c.1
  let reported := cases.filter fun c => known.contains c.1
  let code ← Tests.Ix.IxVM.runCases "ixvm-mutator" (circuit := some true) (gated.map toBuilder)
  IO.println s!"[ixvm-mutator] known-finding classes, run for the report only \
    (an instance reported FAILED as accepted is an instance of the known finding):"
  let _ ← Tests.Ix.IxVM.runCases "ixvm-mutator (known findings)" (circuit := some true)
    (reported.map toBuilder)
  for (m, note) in knownFindings do
    let n := reported.countP (·.1 == m)
    IO.println s!"  - {m.name} ({m.oracle}): {n} instances; {note}"
  IO.println s!"[ixvm-mutator] gated {gated.size} mutations of {Mut.all.length - known.length} \
    classes; reported {reported.size} known-finding instances"
  if code != 0 then
    IO.eprintln "[ixvm-mutator] FINDING: a mutation of a class not on the known list was accepted \
      (reported FAILED above as accepted). Its fixture is the mutated block's Ixon in the case's \
      environment."
  return code

end Tests.Ix.IxVM.Mutator
