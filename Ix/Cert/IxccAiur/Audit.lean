import Ix.Cert.IxccAiur.Backward

/-! # Direct `IxCC Fir → Formal Aiur` Certified Compiler Audit Surface

Verifies that every headline theorem in `Ix.Cert.IxccAiur` depends ONLY on
Lean's three standard axioms (`[propext, Classical.choice, Quot.sound]`, or a
subset thereof) — zero `sorry`, zero `native_decide`, zero `bv_decide`, zero
custom axioms — and exercises a concrete end-to-end `Fir.Program` covering
`.src` and `.clo` constructors, `Lit.str` byte lists, non-recursive & recursive
join points (`.jp`/`.jmp`), `Nat` primitives, and `.trap`. -/

namespace Ix.Cert.IxccAiur.Audit

open Ix.Cert.IxccAiur.Fir Ix.Cert.IxccAiur.Lower Ix.Cert.IxccAiur.Gadgets
open Ix.Cert.IxccAiur.Backward

/-! ## 1. Fir Operational Semantics & Monotonicity -/

/--
info: eval_mono : ∀ (P : Program) {k k' : ℕ} {ρ : Env} {J : List JEntry} {c : Code} {v : Val},
  eval P k ρ J c = Result.ok v → k ≤ k' → eval P k' ρ J c = Result.ok v
-/
#guard_msgs (whitespace := lax) in
#check @Fir.eval_mono

/--
info: evalCall_mono : ∀ (P : Program) {k k' : ℕ} {f : FunId} {vs : List Val} {v : Val},
  evalCall P k f vs = Result.ok v → k ≤ k' → evalCall P k' f vs = Result.ok v
-/
#guard_msgs (whitespace := lax) in
#check @Fir.evalCall_mono

/--
info: run_mono : ∀ (P : Program) {k k' : ℕ} {f : FunId} {vs : List Val} {v : Val},
  run P k f vs = Result.ok v → k ≤ k' → run P k' f vs = Result.ok v
-/
#guard_msgs (whitespace := lax) in
#check @Fir.run_mono

/-- info: 'Ix.Cert.IxccAiur.Fir.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fir.eval_mono

/-- info: 'Ix.Cert.IxccAiur.Fir.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fir.run_mono

/-! ## 2. `UInt8` / `UInt64` & Primitive Helper Gadget Contracts -/

/-- info: goldilocks_fieldCompatible : FieldCompatible Aiur.Library.U32.Goldilocks.F -/
#guard_msgs (whitespace := lax) in
#check @Gadgets.goldilocks_fieldCompatible

/--
info: @u8MapSpec_of_source : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] (s : Aiur.Generic.Source F),
  U8TablesMatch s → U8MapSpec s.world
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.u8MapSpec_of_source

/--
info: @U64Contracts.ofLibraryWorld : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Aiur.Generic.SourceSemantics.World F}, U64LibraryWorld world → FieldCompatible F → U64Contracts world
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.U64Contracts.ofLibraryWorld

/--
info: @pAdd_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x y : ℕ},
        x < natLimit →
          y < natLimit →
            ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
              Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_add") [natV objQName x, natV objQName y] h r h' →
                x + y < natLimit ∧ r = natV objQName (x + y) ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pAdd_sound

/--
info: @pSub_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x y : ℕ},
        x < natLimit →
          y < natLimit →
            ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
              Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_sub") [natV objQName x, natV objQName y] h r h' →
                x - y < natLimit ∧ r = natV objQName (x - y) ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pSub_sound

/--
info: @pMul_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x y : ℕ},
        x < natLimit →
          y < natLimit →
            ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
              Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_mul") [natV objQName x, natV objQName y] h r h' →
                x * y < natLimit ∧ r = natV objQName (x * y) ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pMul_sound

/--
info: @divmod_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x y : ℕ},
        x < natLimit →
          y < natLimit →
            y ≠ 0 →
              ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
                Aiur.Generic.SourceSemantics.EvalFn world (qualified "divmod")
                    [Aiur.Value.field ↑x, Aiur.Value.field ↑y] h r h' →
                  x / y < natLimit ∧
                    x % y < natLimit ∧
                      r = Aiur.Value.tuple [Aiur.Value.field ↑(x / y), Aiur.Value.field ↑(x % y)] ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.divmod_sound

/--
info: @pDiv_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x y : ℕ},
        x < natLimit →
          y < natLimit →
            ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
              Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_div") [natV objQName x, natV objQName y] h r h' →
                (if (y == 0) = true then 0 else x / y) < natLimit ∧
                  r = natV objQName (if (y == 0) = true then 0 else x / y) ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pDiv_sound

/--
info: @pMod_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x y : ℕ},
        x < natLimit →
          y < natLimit →
            ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
              Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_mod") [natV objQName x, natV objQName y] h r h' →
                (if (y == 0) = true then x else x % y) < natLimit ∧
                  r = natV objQName (if (y == 0) = true then x else x % y) ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pMod_sound

/--
info: @pPred_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x : ℕ},
        x < natLimit →
          ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
            Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_pred") [natV objQName x] h r h' →
              x - 1 < natLimit ∧ r = natV objQName (x - 1) ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pPred_sound

/--
info: @pLand_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x y : ℕ},
        x < natLimit →
          y < natLimit →
            ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
              Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_land") [natV objQName x, natV objQName y] h r h' →
                x &&& y < natLimit ∧ r = natV objQName (x &&& y) ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pLand_sound

/--
info: @pLor_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x y : ℕ},
        x < natLimit →
          y < natLimit →
            ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
              Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_lor") [natV objQName x, natV objQName y] h r h' →
                x ||| y < natLimit ∧ r = natV objQName (x ||| y) ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pLor_sound

/--
info: @pXor_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {x y : ℕ},
        x < natLimit →
          y < natLimit →
            ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
              Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_xor") [natV objQName x, natV objQName y] h r h' →
                x ^^^ y < natLimit ∧ r = natV objQName (x ^^^ y) ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pXor_sound

/--
info: @pBeq_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {tt ff : String},
        { P := P }.boolNames = some (tt, ff) →
          ∀ {x y : ℕ},
            x < natLimit →
              y < natLimit →
                ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
                  Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_beq") [natV objQName x, natV objQName y] h r
                      h' →
                    r = Aiur.Value.construct objQName (if (x == y) = true then tt else ff) [] ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pBeq_sound

/--
info: @pBle_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {tt ff : String},
        { P := P }.boolNames = some (tt, ff) →
          ∀ {x y : ℕ},
            x < natLimit →
              y < natLimit →
                ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
                  Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_ble") [natV objQName x, natV objQName y] h r
                      h' →
                    r = Aiur.Value.construct objQName (if decide (x ≤ y) = true then tt else ff) [] ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pBle_sound

/--
info: @pBlt_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    PrimHelpersWorld P world →
      ∀ {tt ff : String},
        { P := P }.boolNames = some (tt, ff) →
          ∀ {x y : ℕ},
            x < natLimit →
              y < natLimit →
                ∀ {r : Aiur.SourceValue F} {h h' : Aiur.Heap F},
                  Aiur.Generic.SourceSemantics.EvalFn world (qualified "p_blt") [natV objQName x, natV objQName y] h r
                      h' →
                    r = Aiur.Value.construct objQName (if decide (x < y) = true then tt else ff) [] ∧ h' = h
-/
#guard_msgs (whitespace := lax) in
#check @Gadgets.pBlt_sound

/-- info: 'Ix.Cert.IxccAiur.Gadgets.goldilocks_fieldCompatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.goldilocks_fieldCompatible

/-- info: 'Ix.Cert.IxccAiur.Gadgets.U64Contracts.ofLibraryWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.U64Contracts.ofLibraryWorld

/-- info: 'Ix.Cert.IxccAiur.Gadgets.pAdd_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pAdd_sound

/-- info: 'Ix.Cert.IxccAiur.Gadgets.pMul_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pMul_sound

/-- info: 'Ix.Cert.IxccAiur.Gadgets.pDiv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pDiv_sound

/-- info: 'Ix.Cert.IxccAiur.Gadgets.pMod_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pMod_sound

/-- info: 'Ix.Cert.IxccAiur.Gadgets.pXor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pXor_sound

/-- info: 'Ix.Cert.IxccAiur.Gadgets.pBlt_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pBlt_sound

/-! ## 3. Full Backward Simulation & End-to-End Certified Circuit Soundness -/

/--
info: @VR.extend : ∀ {F : Type} [inst : Field F] {P : Program} {e be : String} {h h' : Aiur.Heap F},
  h.Extends h' → ∀ {v : Val} {w : Aiur.SourceValue F}, VR P e be h v w → VR P e be h' v w
-/
#guard_msgs (whitespace := lax) in
#check @Backward.VR.extend

/--
info: @trap_no_derivation : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Aiur.Generic.SourceSemantics.World F} {types : Aiur.Generic.SourceSemantics.Types}
  {locals : Aiur.Environment F ℕ} {msg : String} {h h' : Aiur.Heap F} {r : Aiur.SourceValue F},
  Aiur.Generic.SourceSemantics.EvalExpr world types locals (qualifyExprF F (trapE msg)) h r h' → False
-/
#guard_msgs (whitespace := lax) in
#check @Backward.trap_no_derivation

/--
info: @LoweredWorld.ofSource : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {prog : Aiur.Generic.Program ℕ},
  lowerProgram P = Except.ok prog →
    ∀ (s : Aiur.Generic.Source F),
      U64Contracts s.world →
        (∀ g ∈ prog.functions,
            ∃ f,
              s.program.findFunction? (qualified g.name) = some f ∧
                f.typeParams = [] ∧
                  List.map Prod.fst f.params = List.map Prod.fst g.params ∧ f.body = qualifyExprF F g.body) →
          LoweredWorld P prog s.world
-/
#guard_msgs (whitespace := lax) in
#check @Backward.LoweredWorld.ofSource

/--
info: @eval_codeE_sound_N : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {prog : Aiur.Generic.Program ℕ} {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F → LoweredWorld P prog world → ∀ (d : ℕ), CodeSoundAt P world d
-/
#guard_msgs (whitespace := lax) in
#check @Backward.eval_codeE_sound_N

/--
info: @backward_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program} {prog : Aiur.Generic.Program ℕ}
  {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    LoweredWorld P prog world →
      ∀ {f : FunId} {fd : Fun},
        P.fun? f = some fd →
          f < P.size →
            ∀ {vs : List Val} {ws : List (Aiur.SourceValue F)} {h h' : Aiur.Heap F} {r : Aiur.SourceValue F},
              List.Forall₂ (VR P objQName bytesQName h) vs ws →
                Aiur.Generic.SourceSemantics.EvalFn world (qualified (funName f)) ws h r h' →
                  ∃ k v, run P k f vs = Result.ok v ∧ VR P objQName bytesQName h' v r
-/
#guard_msgs (whitespace := lax) in
#check @Backward.backward_sound

/--
info: @entry_backward_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {prog : Aiur.Generic.Program ℕ} {world : Aiur.Generic.SourceSemantics.World F},
  FieldCompatible F →
    LoweredWorld P prog world →
      ∀ {i : ℕ} {f : FunId},
        P.exports[i]? = some f →
          ∀ {args : List (Aiur.SourceValue F)} {h' : Aiur.Heap F} {r : Aiur.SourceValue F},
            Aiur.Generic.SourceSemantics.EvalFn world (qualified (entryName i)) args [] r h' →
              ∃ ns k v,
                (∀ n ∈ ns, n < natLimit) ∧
                  args = List.map (fun n => Aiur.Value.field ↑n) ns ∧
                    run P k f (List.map (fun n => Val.lit (Lit.nat n)) ns) = Result.ok v ∧
                      VR P objQName bytesQName h' v r
-/
#guard_msgs (whitespace := lax) in
#check @Backward.entry_backward_sound

/--
info: @lowered_circuit_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {P : Program}
  {prog : Aiur.Generic.Program ℕ} {moduleProg : Aiur.Modules.Program F} {id : String → Except String ℕ},
  FieldCompatible F →
    ∀ (prepared : Aiur.Modules.Prepared moduleProg),
      LoweredWorld P prog prepared.environment.source.world →
        ∀ (compiled : Aiur.Optimized.ModulesArtifact prepared)
          (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact) {cfg : Aiur.Optimized.Depth.Config},
          Aiur.Optimized.Depth.Certified cfg physical.system →
            ∀ (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id),
              plan.WellFormedActivation →
                ∀ {external : String}
                  {entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances},
                  prepared.find? external = some entry →
                    ∀ {i : ℕ} {f : FunId},
                      entry.resolved.name = qualified (entryName i) →
                        P.exports[i]? = some f →
                          ∀ {rom : Aiur.WidthROM F},
                            rom.Valid →
                              ∀ {args : List (Aiur.SourceValue F)} {result : Aiur.Value F}
                                {wires : List (Aiur.WireValue F)} {output : Aiur.WireValue F},
                                Aiur.Circuit.Erasure.Signed compiled.circuit.system
                                    { channel := entry.resolved.name, args := wires, result := output } →
                                  ∀ {root : Aiur.Circuit.Message F},
                                    Aiur.Optimized.Depth.erase cfg root =
                                        Aiur.Circuit.Erasure.message compiled.circuit.system
                                          { channel := entry.resolved.name, args := wires, result := output } →
                                      root.channel ∉ cfg.names →
                                        ∀ {rows : List (Aiur.Circuit.WeightedRow F)},
                                          rows.length ≤ 2 ^ 39 →
                                            (∀ (n : ℕ), 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → ↑n ≠ 0) →
                                              plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows =
                                                  Except.ok () →
                                                Aiur.DecodesValues compiled.specialized.program.enums wires
                                                    (Aiur.entryValues args) →
                                                  Aiur.WireValue.decode compiled.specialized.program.enums output =
                                                      some result →
                                                    ∃ value heap ns k v,
                                                      (∀ n ∈ ns, n < natLimit) ∧
                                                        args = List.map (fun n => Aiur.Value.field ↑n) ns ∧
                                                          run P k f (List.map (fun n => Val.lit (Lit.nat n)) ns) =
                                                              Result.ok v ∧
                                                            VR P objQName bytesQName heap v value ∧
                                                              Aiur.Represents
                                                                (Aiur.WireROM.decode compiled.specialized.program.enums
                                                                  (Aiur.Circuit.Erasure.typedROM compiled.circuit.system
                                                                    rom))
                                                                heap value result
-/
#guard_msgs (whitespace := lax) in
#check @Backward.lowered_circuit_sound

/--
info: @lowered_circuit_sound_goldilocks : ∀ {P : Program} {prog : Aiur.Generic.Program ℕ}
  {moduleProg : Aiur.Modules.Program Aiur.Library.U32.Goldilocks.F} {id : String → Except String ℕ}
  (prepared : Aiur.Modules.Prepared moduleProg),
  LoweredWorld P prog prepared.environment.source.world →
    ∀ (compiled : Aiur.Optimized.ModulesArtifact prepared)
      (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact) {cfg : Aiur.Optimized.Depth.Config},
      Aiur.Optimized.Depth.Certified cfg physical.system →
        cfg.bits ≤ 24 →
          ∀ (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id),
            plan.WellFormedActivation →
              ∀ {external : String} {entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances},
                prepared.find? external = some entry →
                  ∀ {i : ℕ} {f : FunId},
                    entry.resolved.name = qualified (entryName i) →
                      P.exports[i]? = some f →
                        ∀ {rom : Aiur.WidthROM Aiur.Library.U32.Goldilocks.F},
                          rom.Valid →
                            ∀ {args : List (Aiur.SourceValue Aiur.Library.U32.Goldilocks.F)}
                              {result : Aiur.Value Aiur.Library.U32.Goldilocks.F}
                              {wires : List (Aiur.WireValue Aiur.Library.U32.Goldilocks.F)}
                              {output : Aiur.WireValue Aiur.Library.U32.Goldilocks.F},
                              Aiur.Circuit.Erasure.Signed compiled.circuit.system
                                  { channel := entry.resolved.name, args := wires, result := output } →
                                ∀ {root : Aiur.Circuit.Message Aiur.Library.U32.Goldilocks.F},
                                  Aiur.Optimized.Depth.erase cfg root =
                                      Aiur.Circuit.Erasure.message compiled.circuit.system
                                        { channel := entry.resolved.name, args := wires, result := output } →
                                    root.channel ∉ cfg.names →
                                      ∀ {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.U32.Goldilocks.F)},
                                        rows.length ≤ 2 ^ 39 →
                                          plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = Except.ok () →
                                            Aiur.DecodesValues compiled.specialized.program.enums wires
                                                (Aiur.entryValues args) →
                                              Aiur.WireValue.decode compiled.specialized.program.enums output =
                                                  some result →
                                                ∃ value heap ns k v,
                                                  (∀ n ∈ ns, n < natLimit) ∧
                                                    args = List.map (fun n => Aiur.Value.field ↑n) ns ∧
                                                      run P k f (List.map (fun n => Val.lit (Lit.nat n)) ns) =
                                                          Result.ok v ∧
                                                        VR P objQName bytesQName heap v value ∧
                                                          Aiur.Represents
                                                            (Aiur.WireROM.decode compiled.specialized.program.enums
                                                              (Aiur.Circuit.Erasure.typedROM compiled.circuit.system
                                                                rom))
                                                            heap value result
-/
#guard_msgs (whitespace := lax) in
#check @Backward.lowered_circuit_sound_goldilocks

/-- info: 'Ix.Cert.IxccAiur.Backward.VR.extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.VR.extend

/-- info: 'Ix.Cert.IxccAiur.Backward.trap_no_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.trap_no_derivation

/-- info: 'Ix.Cert.IxccAiur.Backward.backward_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.backward_sound

/-- info: 'Ix.Cert.IxccAiur.Backward.entry_backward_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.entry_backward_sound

/-- info: 'Ix.Cert.IxccAiur.Backward.lowered_circuit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.lowered_circuit_sound

/-- info: 'Ix.Cert.IxccAiur.Backward.lowered_circuit_sound_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.lowered_circuit_sound_goldilocks

/-! ## 4. Concrete End-to-End Lowering & Execution Fixture -/

private def kNatZero : CtorKey := .src 0
private def kNatSucc : CtorKey := .src 1
private def kBoolFalse : CtorKey := .src 2
private def kBoolTrue : CtorKey := .src 3
private def kCloBox : CtorKey := .clo (.const 42 []) 2

private def cloBoxInfo : CtorInfo :=
  { key := kCloBox, tag := 0, nobj := 2, fieldKinds := [.shared, .shared] }

private def demoFun0 : Fir.Fun := {
  key := .const 0 []
  params := [(0, .obj)]
  body :=
    -- Construct a closure holding `(x0, "ix")`, extract field 0 via `.proj`,
    -- enter non-recursive join point `j1`, then run recursive join point `j0`.
    .bind 1 (.ctor cloBoxInfo [.var 0, .lit (.str "ix")]) <|
    .case 1
      [ .mk kCloBox <|
          .bind 2 (.proj 1 kCloBox 0) <|
          .jp 1 [3] false
            (.jp 0 [4, 5] true
              (.bind 6 (.prim .natBeq [.var 4, .lit (.nat 0)]) <|
               .case 6
                 [ .mk kBoolTrue (.ret (.var 5)),
                   .mk kBoolFalse
                     (.bind 7 (.prim .natAdd [.var 5, .var 4]) <|
                      .bind 8 (.prim .natPred [.var 4]) <|
                      .jmp 0 [.var 8, .var 7]) ]
                 (some .trap))
              (.jmp 0 [.var 3, .lit (.nat 0)]))
            (.jmp 1 [.var 2]) ]
      (some .trap)
  vars := 9
  joins := 2
}

/-- Fixture `Fir.Program` exercising:
- `.src` constructors (`Nat.zero`, `Nat.succ`, `Bool.false`, `Bool.true`)
- `.clo` closure constructor (`kCloBox` holding a `Nat` payload and a `Lit.str` tag)
- `Lit.str` literal (`"ix"`)
- non-recursive join point (`j1`) wrapping closure construction + projection
- recursive join point (`j0`) accumulating `sum(n) = 1 + 2 + ... + n` via `natAdd`,
  `natBeq`, `natPred`, and `.case` on `Bool`
- `.trap` on unreachable branch. -/
def demoProgram : Fir.Program :=
  {
    funs := NatMap.empty.insert 0 demoFun0
    size := 1
    exports := [0]
    ctors := [
      { key := kNatZero, tag := 0, arity := 0 },
      { key := kNatSucc, tag := 1, arity := 1 },
      { key := kBoolFalse, tag := 0, arity := 0 },
      { key := kBoolTrue, tag := 1, arity := 0 },
      { key := kCloBox, tag := 0, arity := 2 }
    ]
    known := {
      natZero := some kNatZero
      natSucc := some kNatSucc
      boolFalse := some kBoolFalse
      boolTrue := some kBoolTrue
    }
  }

private theorem natDigits_lt10 {n : Nat} (h : n < 10) : Lower.natDigits n = [Nat.digitChar n] := by
  unfold Lower.natDigits
  simp [h]

/-- `demoProgram` lowers cleanly via `Lower.lowerModule` (kernel-verified, zero `native_decide`). -/
theorem demoProgram_lowers : (Lower.lowerModule demoProgram).isOk = true := by
  have h1 : Lower.allDistinct (demoProgram.ctors.map (·.key)) = true := by decide
  have h2 : Lower.allDistinct (Lower.objCtorNames demoProgram) = true := by
    simp [Lower.objCtorNames, demoProgram, Lower.allDistinct, Lower.ctorNameOf, natDigits_lt10,
      Nat.digitChar, kNatZero, kNatSucc, kBoolFalse, kBoolTrue, kCloBox]
  have hfunList : demoProgram.funList = [(0, demoFun0)] := rfl
  have hfun0 : demoProgram.fun? 0 = some demoFun0 := rfl
  have hexports : demoProgram.exports = [0] := rfl
  have hclo : (Lower.Cx.mk demoProgram).ctorEntry? kCloBox =
      some (4, { key := kCloBox, tag := 0, arity := 2 }) := rfl
  have hbools : (Lower.Cx.mk demoProgram).boolNames.isNone = false := rfl
  have h0lt : 0 < Lower.natLimit := by decide
  have hfunE : ∃ fns, Lower.funE ⟨demoProgram⟩ 0 demoFun0 = .ok fns := by
    refine ⟨?_, ?_⟩
    swap
    simp only [Lower.funE, demoFun0, Lower.freshLocals, Lower.freshLocal, Lower.freshJp,
      Lower.emitLifted, Lower.liftExcept, Lower.bindVm, Lower.codeE, Lower.altsE, Lower.optE,
      Lower.rhsE, Lower.argsE, Lower.argE, Lower.primFun, Lower.isBoolPrim,
      hclo, hbools, h0lt, cloBoxInfo,
      List.mapM, List.mapM.loop, List.lookup, List.find?, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, beq_self_eq_true, Bool.and_self, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, StateT.run, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]
    rfl
  have hentry : ∃ efn, Lower.entryE demoProgram 0 0 = .ok efn := by
    refine ⟨?_, ?_⟩
    swap
    simp only [Lower.entryE, hfun0]
    rfl
  rcases hfunE with ⟨fns, hfns⟩
  rcases hentry with ⟨efn, hefn⟩
  unfold Lower.lowerModule Lower.lowerProgram
  rw [h1, h2, hfunList, hexports]
  simp [hfns, hefn, List.mapM, List.mapM.loop,
    bind, pure, Except.bind, Except.pure, Except.isOk, Except.toBool]

/-- `demoProgram` evaluates `sum(4) = 10` under `Fir.run` (kernel-verified, zero `native_decide`). -/
theorem demoProgram_runs :
    Fir.run demoProgram 20 0 [.lit (.nat 4)] = .ok (.lit (.nat 10)) := by
  have hcloAr : cloBoxInfo.arity = 2 := rfl
  have hbf : Fir.boolVal demoProgram false = some (.ctor ⟨kBoolFalse, 0, 0, 0, []⟩ []) := rfl
  have hbt : Fir.boolVal demoProgram true = some (.ctor ⟨kBoolTrue, 1, 0, 0, []⟩ []) := rfl
  rw [Fir.run_eq, Fir.evalCall_of demoProgram 20 (f := 0) (by rfl)]
  simp only [demoFun0, Fir.callFun, Fir.later, Fir.bindAll, List.length_cons, List.length_nil,
    ↓reduceIte, List.map_cons, List.map_nil]
  -- Bind closure `(4, "ix")`, match `kCloBox`, project field 0, enter `j1` and recursive `j0`
  rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
  simp only [Fir.evalRhs, Fir.evalArgs, Fir.Arg.eval, NatMap.get?_insert_self, hcloAr,
    List.length_cons, List.length_nil, ↓reduceIte, Fir.Result.bind_ok]
  rw [Fir.eval_case]
  simp only [NatMap.get?_insert_self, Fir.Result.ofOption, Fir.Result.bind_ok, Fir.Val.asCtor,
    cloBoxInfo, Fir.evalAlts_cons, ↓reduceIte]
  rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
  simp only [Fir.evalRhs, NatMap.get?_insert_self, Fir.projVal, Fir.Val.asCtor, ↓reduceIte,
    List.getElem?_cons_zero, Fir.Result.ofOption, Fir.Result.bind_ok]
  rw [Fir.eval_jp, Fir.eval_jmp]
  simp only [Fir.lookupJ, ↓reduceIte, Fir.evalArgs, Fir.Arg.eval, NatMap.get?_insert_self,
    Fir.Result.ofOption, Fir.Result.bind_ok, Fir.jumpTo, List.length_cons, List.length_nil,
    Bool.false_eq_true, Fir.JEntry.after, Fir.bindAll]
  rw [Fir.eval_jp, Fir.eval_jmp]
  simp only [Fir.lookupJ, ↓reduceIte, Fir.evalArgs, Fir.Arg.eval, NatMap.get?_insert_self,
    Fir.Result.ofOption, Fir.Result.bind_ok, Fir.jumpTo, List.length_cons, List.length_nil,
    Bool.false_eq_true, Fir.JEntry.after, Fir.bindAll]
  -- 4 recursive iterations of `j0`: (4,0) → (3,4) → (2,7) → (1,9) → (0,10)
  let baseEnv : Fir.Env :=
    NatMap.insert (NatMap.insert (NatMap.insert (NatMap.insert .leaf 0 (.lit (.nat 4)))
      1 (.ctor cloBoxInfo [.lit (.nat 4), .lit (.str "ix")])) 2 (.lit (.nat 4))) 3 (.lit (.nat 4))
  let loopBody : Fir.Code :=
    .bind 6 (.prim .natBeq [.var 4, .lit (.nat 0)]) <|
    .case 6
      [ .mk kBoolTrue (.ret (.var 5)),
        .mk kBoolFalse
          (.bind 7 (.prim .natAdd [.var 5, .var 4]) <|
           .bind 8 (.prim .natPred [.var 4]) <|
           .jmp 0 [.var 8, .var 7]) ]
      (some .trap)
  let loopJ : List Fir.JEntry :=
    [{ id := 0, charged := true, env := baseEnv, params := [4, 5], body := loopBody, isRec := true }]
  have step : ∀ (k a acc : Nat), a ≠ 0 →
      Fir.eval demoProgram (k + 1) ((baseEnv.insert 4 (.lit (.nat a))).insert 5 (.lit (.nat acc)))
        loopJ loopBody =
      Fir.eval demoProgram k ((baseEnv.insert 4 (.lit (.nat (a - 1)))).insert 5 (.lit (.nat (acc + a))))
        loopJ loopBody := by
    intro k a acc ha
    have hbeq : (a == 0) = false := beq_false_of_ne ha
    have hneTF : kBoolTrue ≠ kBoolFalse := by decide
    dsimp only [loopBody]
    rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
    simp only [Fir.evalRhs, Fir.evalArgs, Fir.Arg.eval,
      NatMap.get?_insert_ne _ _ (by decide : 5 ≠ 4), NatMap.get?_insert_self,
      Fir.primResult, Fir.natArgs, Option.map_some, Fir.Prim.sem, hbeq, hbf,
      Fir.Result.ofOption, Fir.Result.bind_ok]
    rw [Fir.eval_case]
    simp only [NatMap.get?_insert_self, Fir.Result.ofOption, Fir.Result.bind_ok, Fir.Val.asCtor,
      Fir.evalAlts_cons, hneTF, ↓reduceIte]
    rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
    simp only [Fir.evalRhs, Fir.evalArgs, Fir.Arg.eval,
      NatMap.get?_insert_ne _ _ (by decide : 6 ≠ 5),
      NatMap.get?_insert_ne _ _ (by decide : 6 ≠ 4),
      NatMap.get?_insert_ne _ _ (by decide : 5 ≠ 4),
      NatMap.get?_insert_self, Fir.primResult, Fir.natArgs, Option.map_some, Fir.Prim.sem,
      Fir.Result.bind_ok]
    rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
    simp only [Fir.evalRhs, Fir.evalArgs, Fir.Arg.eval,
      NatMap.get?_insert_ne _ _ (by decide : 7 ≠ 4),
      NatMap.get?_insert_ne _ _ (by decide : 6 ≠ 4),
      NatMap.get?_insert_ne _ _ (by decide : 5 ≠ 4),
      NatMap.get?_insert_self, Fir.primResult, Fir.natArgs, Option.map_some, Fir.Prim.sem,
      Fir.Result.bind_ok]
    rw [Fir.eval_jmp]
    simp only [loopJ, Fir.lookupJ, ↓reduceIte, Fir.evalArgs, Fir.Arg.eval,
      NatMap.get?_insert_self, NatMap.get?_insert_ne _ _ (by decide : 8 ≠ 7),
      Fir.Result.ofOption, Fir.Result.bind_ok, Fir.jumpTo, List.length_cons, List.length_nil,
      Fir.later, Fir.JEntry.after, Fir.bindAll]
    rfl
  change Fir.eval demoProgram 19 ((baseEnv.insert 4 (.lit (.nat 4))).insert 5 (.lit (.nat 0)))
    loopJ loopBody = .ok (.lit (.nat 10))
  rw [step 18 4 0 (by decide)]
  rw [step 17 3 4 (by decide)]
  rw [step 16 2 7 (by decide)]
  rw [step 15 1 9 (by decide)]
  -- Base case `(0, 10)` returns `10`
  dsimp only [loopBody]
  rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
  simp only [Fir.evalRhs, Fir.evalArgs, Fir.Arg.eval,
    NatMap.get?_insert_ne _ _ (by decide : 5 ≠ 4), NatMap.get?_insert_self,
    Fir.primResult, Fir.natArgs, Option.map_some, Fir.Prim.sem, beq_self_eq_true, hbt,
    Fir.Result.ofOption, Fir.Result.bind_ok]
  rw [Fir.eval_case]
  simp only [NatMap.get?_insert_self, Fir.Result.ofOption, Fir.Result.bind_ok, Fir.Val.asCtor,
    Fir.evalAlts_cons, ↓reduceIte]
  rw [Fir.eval_ret]
  simp [Fir.Arg.eval, NatMap.get?_insert_ne _ _ (by decide : 6 ≠ 5), NatMap.get?_insert_self,
    Fir.Result.ofOption]

/-- info: 'Ix.Cert.IxccAiur.Audit.demoProgram_lowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demoProgram_lowers

/-- info: 'Ix.Cert.IxccAiur.Audit.demoProgram_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demoProgram_runs

end Ix.Cert.IxccAiur.Audit
