import IxCCAiur.Compose
import IxCCAiur.World

/-! # An accepted claim, read at the source

`Compose` ends at a Fir value that the Aiur result *represents* on a heap,
under the world hypothesis `Backward.LoweredWorld`. This file removes the
hypothesis and reads the public result:

* the world hypothesis is replaced by the Boolean `World.checkWorld` on the
  prepared source (`entry_source_backward_checked`, `accepted_source_backward`);
* `Accepted prepared i args result` bundles what `Compose`'s circuit theorems
  assume about a claim: certified circuits for the prepared program and rows
  the grouped, activated memo checker accepts for the call of `Prog::main<i>`
  on `args` with public result `result`;
* a public result `Prog::Obj::N(y)` is a `Nat` (`result_nat`), and a nullary
  constructor of the program's table is that constructor (`result_enum`), so
  for those results the statement is about the source alone
  (`accepted_nat_backward`, `accepted_enum_backward`): **the source evaluator
  returns that value on those arguments, or is stuck on them**. The second
  disjunct goes under `Compose.NeverStuck` (`accepted_nat_sound`,
  `accepted_enum_sound`).

What `Accepted` does not contain is the proof system: that the Rust verifier
accepting a proof for the claim gives rows that `checkMemo` accepts for the
circuits `compiled` denotes is the trusted STARK and Rust lowering of every
Aiur claim. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Gadgets IxCC.AiurBackend.Backward
open IxCC.AiurBackend.Compose

/-! ## The entry theorems under the world check -/

section Entry

variable {F : Type} [Field F] [DecidableEq F]

/-- `Compose.entry_source_backward` with the world hypothesis discharged by
`World.checkWorld` on the source the entry is evaluated in. -/
theorem entry_source_backward_checked {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    (fc : FieldCompatible F) {s : Generic.Source F} (hw : World.checkWorld s prog = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn s.world (qualified (entryName i)) args [] r h') :
    ∃ (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      VR f.fir objQName bytesQName h' w r ∧
      (f.Covered c (i, ns) →
        (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
            Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) ∨
          ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .stuck) :=
  entry_source_backward hf fc (World.loweredWorld_of_check fc hlow s hw) hexp ev

/-- `Compose.entry_source_sound` with the world hypothesis discharged by
`World.checkWorld`. -/
theorem entry_source_sound_checked {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    (fc : FieldCompatible F) {s : Generic.Source F} (hw : World.checkWorld s prog = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn s.world (qualified (entryName i)) args [] r h')
    (hp : ∀ ns : List Nat, args = ns.map (fun n => .field (n : F)) →
      NeverStuck ⟨f.src, f.checked⟩ (i, ns)) :
    ∃ (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      VR f.fir objQName bytesQName h' w r ∧
      (f.Covered c (i, ns) →
        ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
          Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) :=
  entry_source_sound hf fc (World.loweredWorld_of_check fc hlow s hw) hexp ev hp

/-! ## Reading a public result -/

omit [DecidableEq F] in
/-- **A `Nat` result.** If the public result that an Aiur value represents is
`Prog::Obj::N(y)`, the Fir value it stands for is a `Nat` literal below
`2^56` whose cast is `y`. -/
theorem result_nat {P : Fir.Program} {heap : Heap F} {w : Fir.Val} {value : SourceValue F}
    {rom : Aiur.ROM F} {y : F}
    (hvr : VR P objQName bytesQName heap w value)
    (hrep : Aiur.Represents rom heap value (.construct objQName "N" [.field y])) :
    ∃ n : Nat, n < natLimit ∧ w = .lit (.nat n) ∧ (n : F) = y := by
  cases hrep with
  | construct items =>
    cases items with
    | cons head tail =>
      cases tail
      obtain ⟨n, hn, rfl, hx⟩ := VR_N_inv hvr
      subst hx
      cases head
      exact ⟨n, hn, rfl, rfl⟩

omit [DecidableEq F] in
/-- **An enumeration result.** If the public result is the nullary
constructor `Prog::Obj::<name of row idx>` of the program's constructor
table, the Fir value it stands for is that constructor without fields. -/
theorem result_enum {P : Fir.Program} (hnd : (objCtorNames P).Nodup)
    {idx : Nat} {entry : Lam.CtorInfo} (hget : P.ctors[idx]? = some entry)
    {heap : Heap F} {w : Fir.Val} {value : SourceValue F} {rom : Aiur.ROM F}
    (hvr : VR P objQName bytesQName heap w value)
    (hrep : Aiur.Represents rom heap value
      (.construct objQName (ctorNameOf idx entry.key) [])) :
    ∃ c, w = Fir.Val.ctor c [] ∧ c.key = entry.key := by
  cases hrep with
  | construct items =>
    cases items
    obtain ⟨c, fs, rfl, hkey, _, hfs⟩ := VR_ctor_inv hnd hget hvr
    cases hfs
    exact ⟨c, rfl, hkey⟩

end Entry

/-- A `Nat` literal's observation. -/
theorem obs_nat (n : Nat) : Fir.obsV (.lit (.nat n)) = some (.nat n) := by
  simp [Fir.obsV]

/-- A nullary source constructor's observation. -/
theorem obs_ctor_nil {c : Fir.CtorInfo} {cid : Src.CId} (hk : c.key = .src cid) :
    Fir.obsV (.ctor c []) = some (.ctor cid []) := by
  simp [Fir.obsV, Fir.obsList, hk]

/-! ## Accepted claims over Goldilocks -/

/-- The field of the proof system. -/
abbrev G := Aiur.Library.U32.Goldilocks.F

/-- A natural number below `2^56` is the value of its cast. -/
theorem val_natCast_lt {n : Nat} (hn : n < natLimit) : ((n : G)).val = n :=
  ZMod.val_cast_of_lt (Nat.lt_of_lt_of_le hn (by decide))

/-- Field arguments that are the casts of naturals below `2^56` have those
naturals as their values. -/
theorem vals_of_fields : ∀ {as : List G} {ns : List Nat}, (∀ n ∈ ns, n < natLimit) →
    as.map (Value.field : G → SourceValue G) = ns.map (fun n => .field (n : G)) →
    as.map ZMod.val = ns
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, n :: ns, hn, h => by
    simp only [List.map_cons, List.cons.injEq, Value.field.injEq] at h
    obtain ⟨rfl, htl⟩ := h
    rw [List.map_cons, val_natCast_lt (hn n List.mem_cons_self),
      vals_of_fields (fun m hm => hn m (List.mem_cons_of_mem _ hm)) htl]

/-- **A claim the checker accepts**: for the prepared program, the call of
the lowered entry `Prog::main<i>` on `args` with public result `result`.

There are circuits compiled from `prepared` by the certified optimizing
compiler (`compiled`), their deduplicated physical system (`physical`) under a
certified depth pass of at most 24 bits (`dcfg`), and a grouping plan with a
well-formed activation (`plan`); the entry selected under some external name
is `Prog::main<i>`; and for a valid ROM there are at most `2^39` weighted rows
that the plan's memo checker accepts for a root message which is the depth
pass's image of the call `⟨entry, wires, output⟩`, whose wires decode to
`args` and whose output decodes to `result`.

These are the hypotheses of `Compose.circuit_source_backward_goldilocks`
(those of `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks`
with the entry named), bundled. -/
def Accepted {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (i : Nat) (args : List (SourceValue G)) (result : Aiur.Value G) : Prop :=
  ∃ (id : String → Except String Nat)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    (dcfg : Aiur.Optimized.Depth.Config)
    (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system dcfg physical.system) id)
    (external : String)
    (entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances)
    (rom : Aiur.WidthROM G)
    (wires : List (Aiur.WireValue G)) (output : Aiur.WireValue G)
    (root : Aiur.Circuit.Message G)
    (rows : List (Aiur.Circuit.WeightedRow G)),
    Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical dcfg ∧
    dcfg.bits ≤ 24 ∧
    plan.WellFormedActivation ∧
    prepared.find? external = some entry ∧
    entry.resolved.name = qualified (entryName i) ∧
    rom.Valid ∧
    Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩ ∧
    Aiur.Optimized.Depth.erase dcfg root =
      Aiur.Circuit.Erasure.message compiled.circuit.system
        ⟨entry.resolved.name, wires, output⟩ ∧
    root.channel ∉ dcfg.names ∧
    rows.length ≤ 2 ^ 39 ∧
    plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok () ∧
    Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args) ∧
    output.decode compiled.specialized.program.enums = some result

/-- **An accepted claim, read at the source (with the stuck-source
disjunct).** `Compose.circuit_source_backward_goldilocks` for a prepared
source that passes the world check: the arguments are `Nat`s below `2^56`,
and the public result is represented (through some ROM) by an Aiur value that
stands for a Fir value `w` which, on a covered input, is the observation of a
value SrcEval returns for root `i`, or SrcEval is stuck on that input. -/
theorem accepted_source_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue G)} {result : Aiur.Value G}
    (acc : Accepted prepared i args result) :
    ∃ (value : SourceValue G) (heap : Heap G) (rom : Aiur.ROM G) (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : G)) ∧
      VR f.fir objQName bytesQName heap w value ∧
      Aiur.Represents rom heap value result ∧
      (f.Covered c (i, ns) →
        (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
            Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) ∨
          ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .stuck) := by
  obtain ⟨id, compiled, physical, dcfg, plan, external, entry, rom, wires, output, root, rows,
    certified, bits, activated, selected, hname, valid, signed, rooted, outside, bound, checked,
    arguments, decoded⟩ := acc
  obtain ⟨value, heap, ns, w, hns, hargs, hvr, hrep, hsrc⟩ :=
    circuit_source_backward_goldilocks hf prepared
      (World.loweredWorld_of_check goldilocks_fieldCompatible hlow _ hw)
      compiled physical certified bits plan activated selected hname hexp valid signed rooted
      outside bound checked arguments decoded
  exact ⟨value, heap, _, ns, w, hns, hargs, hvr, hrep, hsrc⟩

/-- **An accepted `Nat` claim, read at the source (with the stuck-source
disjunct).** If the checker accepts the claim that `Prog::main<i>` on the
field arguments `as` returns `Prog::Obj::N(y)`, then on the `Nat` arguments
`as.map ZMod.val` (a covered input) SrcEval returns, at some clock, a value
whose observation is the `Nat` `y.val`, **or SrcEval is stuck on them**. -/
theorem accepted_nat_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {as : List G} {y : G}
    (acc : Accepted prepared i (as.map Value.field) (.construct objQName "N" [.field y]))
    (hcov : f.Covered c (i, as.map ZMod.val)) :
    (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val)) ∨
      ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .stuck := by
  obtain ⟨value, heap, rom, ns, w, hns, hargs, hvr, hrep, hsrc⟩ :=
    accepted_source_backward hf hlow prepared hw hexp acc
  have hvals : as.map ZMod.val = ns := vals_of_fields hns hargs
  rw [hvals] at hcov ⊢
  obtain ⟨n, hn, rfl, hy⟩ := result_nat hvr hrep
  have hval : y.val = n := by rw [← hy]; exact val_natCast_lt hn
  rcases hsrc hcov with ⟨k, v, hrun, hobs⟩ | ⟨k, hstuck⟩
  · exact Or.inl ⟨k, v, hrun, by rw [hval]; exact Eq.trans hobs (obs_nat n)⟩
  · exact Or.inr ⟨k, hstuck⟩

/-- **An accepted `Nat` claim, read at the source, under source progress on
the input.** As `accepted_nat_backward`, where the source is stuck at no
clock on the input: SrcEval returns a value whose observation is `y.val`. -/
theorem accepted_nat_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {as : List G} {y : G}
    (acc : Accepted prepared i (as.map Value.field) (.construct objQName "N" [.field y]))
    (hcov : f.Covered c (i, as.map ZMod.val))
    (hp : NeverStuck ⟨f.src, f.checked⟩ (i, as.map ZMod.val)) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) := by
  rcases accepted_nat_backward hf hlow prepared hw hexp acc hcov with h | ⟨k, hk⟩
  · exact h
  · exact absurd hk (hp k)

/-- **An accepted enumeration claim, read at the source (with the
stuck-source disjunct).** If the checker accepts the claim that
`Prog::main<i>` on `as` returns the nullary constructor of row `idx` of the
program's constructor table, a source constructor `cid`, then on
`as.map ZMod.val` SrcEval returns a value whose observation is `cid` without
fields, **or SrcEval is stuck**. -/
theorem accepted_enum_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {as : List G} {idx : Nat} {entry : Lam.CtorInfo} {cid : Src.CId}
    (hget : f.fir.ctors[idx]? = some entry) (hkey : entry.key = .src cid)
    (acc : Accepted prepared i (as.map Value.field)
      (.construct objQName (ctorNameOf idx entry.key) []))
    (hcov : f.Covered c (i, as.map ZMod.val)) :
    (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.ctor cid [])) ∨
      ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .stuck := by
  obtain ⟨value, heap, rom, ns, w, hns, hargs, hvr, hrep, hsrc⟩ :=
    accepted_source_backward hf hlow prepared hw hexp acc
  have hvals : as.map ZMod.val = ns := vals_of_fields hns hargs
  rw [hvals] at hcov ⊢
  obtain ⟨ci, rfl, hci⟩ := result_enum (lowerProgram_inv hlow).2.1 hget hvr hrep
  rcases hsrc hcov with ⟨k, v, hrun, hobs⟩ | ⟨k, hstuck⟩
  · exact Or.inl ⟨k, v, hrun, Eq.trans hobs (obs_ctor_nil (hci.trans hkey))⟩
  · exact Or.inr ⟨k, hstuck⟩

/-- **An accepted enumeration claim, read at the source, under source
progress on the input.** -/
theorem accepted_enum_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {as : List G} {idx : Nat} {entry : Lam.CtorInfo} {cid : Src.CId}
    (hget : f.fir.ctors[idx]? = some entry) (hkey : entry.key = .src cid)
    (acc : Accepted prepared i (as.map Value.field)
      (.construct objQName (ctorNameOf idx entry.key) []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    (hp : NeverStuck ⟨f.src, f.checked⟩ (i, as.map ZMod.val)) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.ctor cid []) := by
  rcases accepted_enum_backward hf hlow prepared hw hexp hget hkey acc hcov with h | ⟨k, hk⟩
  · exact h
  · exact absurd hk (hp k)

end IxCC.AiurBackend.Claim
