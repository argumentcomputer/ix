import IxCCAiur.Backward
import IxCCAiur.Compose
import IxCCAiur.Fib
import IxCCAiur.Gcd
import IxCCAiur.Roots

/-! # Direct `IxCC Fir → Formal Aiur` Certified Compiler Audit Surface

Verifies that every headline theorem of the package `IxCCAiur` (namespace
`IxCC.AiurBackend`) depends ONLY on Lean's three standard axioms
(`[propext, Classical.choice, Quot.sound]`, or a subset thereof) — zero `sorry`,
zero `native_decide`, zero `bv_decide`, zero custom axioms — and exercises a
concrete `IxCC.Fir.Program` covering `.src` and `.clo` constructors, `Lit.str`
byte lists, non-recursive & recursive join points (`.jp`/`.jmp`), `Nat`
primitives, and `.trap`. The Fir program, its evaluator and its values are the
compiler's own (`IxCC.Fir`); section 5 pins the composition with the compiler's
front half (`IxCCAiur.Compose`), and section 6 the world check
(`IxCCAiur.World`), the public result (`IxCCAiur.Claim`) and the `fib` instance
(`IxCCAiur.Fib`).

The fixture of section 4 is lowered and run in Fir only; the lowered `fib`
closure is prepared and world-checked by the driver (`IxCCAiur.Driver`,
`ixcc-aiur`) and proved and verified by the Rust host, outside this file. -/

namespace IxCC.AiurBackend.Audit

open IxCC.Fir IxCC.Key IxCC.AiurBackend.Lower IxCC.AiurBackend.Gadgets
open IxCC.Lam (Lit Prim)
open IxCC.AiurBackend.Backward

/-! ## 1. Fir Operational Semantics & Monotonicity -/

/--
info: FirFacts.eval_mono : ∀ (P : Program) {k k' : ℕ} {ρ : Env} {J : List JEntry} {c : Code} {v : Val},
  eval P k ρ J c = Sem.Result.ok v → k ≤ k' → eval P k' ρ J c = Sem.Result.ok v
-/
#guard_msgs (whitespace := lax) in
#check @FirFacts.eval_mono

/--
info: FirFacts.evalCall_mono : ∀ (P : Program) {k k' : ℕ} {f : FunId} {vs : List Val} {v : Val},
  evalCall P k f vs = Sem.Result.ok v → k ≤ k' → evalCall P k' f vs = Sem.Result.ok v
-/
#guard_msgs (whitespace := lax) in
#check @FirFacts.evalCall_mono

/--
info: FirFacts.run_mono : ∀ (P : Program) {k k' : ℕ} {f : FunId} {vs : List Val} {v : Val},
  run P k f vs = Sem.Result.ok v → k ≤ k' → run P k' f vs = Sem.Result.ok v
-/
#guard_msgs (whitespace := lax) in
#check @FirFacts.run_mono

/-- info: 'IxCC.AiurBackend.FirFacts.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FirFacts.eval_mono

/-- info: 'IxCC.AiurBackend.FirFacts.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FirFacts.run_mono

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

/-- info: 'IxCC.AiurBackend.Gadgets.goldilocks_fieldCompatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.goldilocks_fieldCompatible

/-- info: 'IxCC.AiurBackend.Gadgets.U64Contracts.ofLibraryWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.U64Contracts.ofLibraryWorld

/-- info: 'IxCC.AiurBackend.Gadgets.pAdd_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pAdd_sound

/-- info: 'IxCC.AiurBackend.Gadgets.pMul_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pMul_sound

/-- info: 'IxCC.AiurBackend.Gadgets.pDiv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pDiv_sound

/-- info: 'IxCC.AiurBackend.Gadgets.pMod_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pMod_sound

/-- info: 'IxCC.AiurBackend.Gadgets.pXor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gadgets.pXor_sound

/-- info: 'IxCC.AiurBackend.Gadgets.pBlt_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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
                  ∃ k v, run P k f vs = Sem.Result.ok v ∧ VR P objQName bytesQName h' v r
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
                    run P k f (List.map (fun n => Val.lit (Lit.nat n)) ns) = Sem.Result.ok v ∧
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
          Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg →
            cfg.bits ≤ 24 →
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
                                            (∀ (n : ℕ), 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → ↑n ≠ 0) →
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
                                                              Sem.Result.ok v ∧
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
      Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg →
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
                                                          Sem.Result.ok v ∧
                                                        VR P objQName bytesQName heap v value ∧
                                                          Aiur.Represents
                                                            (Aiur.WireROM.decode compiled.specialized.program.enums
                                                              (Aiur.Circuit.Erasure.typedROM compiled.circuit.system
                                                                rom))
                                                            heap value result
-/
#guard_msgs (whitespace := lax) in
#check @Backward.lowered_circuit_sound_goldilocks

/-- info: 'IxCC.AiurBackend.Backward.VR.extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.VR.extend

/-- info: 'IxCC.AiurBackend.Backward.trap_no_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.trap_no_derivation

/-- info: 'IxCC.AiurBackend.Backward.backward_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.backward_sound

/-- info: 'IxCC.AiurBackend.Backward.entry_backward_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.entry_backward_sound

/-- info: 'IxCC.AiurBackend.Backward.lowered_circuit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backward.lowered_circuit_sound

/-- info: 'IxCC.AiurBackend.Backward.lowered_circuit_sound_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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
    funs := Src.NatMap.empty.insert 0 demoFun0
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
  simp only [demoFun0, Fir.callFun, Sem.later, Fir.bindAll, List.length_cons, List.length_nil,
    ↓reduceIte, List.map_cons, List.map_nil]
  -- Bind closure `(4, "ix")`, match `kCloBox`, project field 0, enter `j1` and recursive `j0`
  rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
  simp only [Fir.evalRhs, Fir.evalArgs, Fir.Arg.eval, Src.NatMap.get?_insert_self, hcloAr,
    List.length_cons, List.length_nil, ↓reduceIte, Sem.Result.bind_ok]
  rw [Fir.eval_case]
  simp only [Src.NatMap.get?_insert_self, Sem.Result.ofOption, Sem.Result.bind_ok, Fir.Val.asCtor,
    cloBoxInfo, Fir.evalAlts_cons, ↓reduceIte]
  rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
  simp only [Fir.evalRhs, Src.NatMap.get?_insert_self, Fir.Val.asCtor, ↓reduceIte,
    List.getElem?_cons_zero, Sem.Result.ofOption, Sem.Result.bind_ok]
  rw [Fir.eval_jp, Fir.eval_jmp]
  simp only [Fir.lookupJ, ↓reduceIte, Fir.evalArgs, Fir.Arg.eval, Src.NatMap.get?_insert_self,
    Sem.Result.ofOption, Sem.Result.bind_ok, Fir.jumpTo, List.length_cons, List.length_nil,
    Bool.false_eq_true, Fir.JEntry.after, Fir.bindAll]
  rw [Fir.eval_jp, Fir.eval_jmp]
  simp only [Fir.lookupJ, ↓reduceIte, Fir.evalArgs, Fir.Arg.eval, Src.NatMap.get?_insert_self,
    Sem.Result.ofOption, Sem.Result.bind_ok, Fir.jumpTo, List.length_cons, List.length_nil,
    Bool.false_eq_true, Fir.JEntry.after, Fir.bindAll]
  -- 4 recursive iterations of `j0`: (4,0) → (3,4) → (2,7) → (1,9) → (0,10)
  let baseEnv : Fir.Env :=
    Src.NatMap.insert (Src.NatMap.insert (Src.NatMap.insert (Src.NatMap.insert .leaf 0 (.lit (.nat 4)))
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
      FirFacts.get?_insert_ne _ _ (by decide : 5 ≠ 4), Src.NatMap.get?_insert_self,
      Fir.primResult, Fir.natArgs, Option.map_some, FirFacts.sem_natBeq, hbeq, hbf,
      Sem.Result.ofOption, Sem.Result.bind_ok]
    rw [Fir.eval_case]
    simp only [Src.NatMap.get?_insert_self, Sem.Result.ofOption, Sem.Result.bind_ok, Fir.Val.asCtor,
      Fir.evalAlts_cons, hneTF, ↓reduceIte]
    rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
    simp only [Fir.evalRhs, Fir.evalArgs, Fir.Arg.eval,
      FirFacts.get?_insert_ne _ _ (by decide : 6 ≠ 5),
      FirFacts.get?_insert_ne _ _ (by decide : 6 ≠ 4),
      FirFacts.get?_insert_ne _ _ (by decide : 5 ≠ 4),
      Src.NatMap.get?_insert_self, Fir.primResult, Fir.natArgs, Option.map_some, FirFacts.sem_natAdd,
      Sem.Result.bind_ok]
    rw [Fir.eval_bindRhs (hr := by intro _ _ h; cases h)]
    simp only [Fir.evalRhs, Fir.evalArgs, Fir.Arg.eval,
      FirFacts.get?_insert_ne _ _ (by decide : 7 ≠ 4),
      FirFacts.get?_insert_ne _ _ (by decide : 6 ≠ 4),
      FirFacts.get?_insert_ne _ _ (by decide : 5 ≠ 4),
      Src.NatMap.get?_insert_self, Fir.primResult, Fir.natArgs, Option.map_some, FirFacts.sem_natPred,
      Sem.Result.bind_ok]
    rw [Fir.eval_jmp]
    simp only [loopJ, Fir.lookupJ, ↓reduceIte, Fir.evalArgs, Fir.Arg.eval,
      Src.NatMap.get?_insert_self, FirFacts.get?_insert_ne _ _ (by decide : 8 ≠ 7),
      Sem.Result.ofOption, Sem.Result.bind_ok, Fir.jumpTo, List.length_cons, List.length_nil,
      Sem.later, Fir.JEntry.after, Fir.bindAll]
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
    FirFacts.get?_insert_ne _ _ (by decide : 5 ≠ 4), Src.NatMap.get?_insert_self,
    Fir.primResult, Fir.natArgs, Option.map_some, FirFacts.sem_natBeq, beq_self_eq_true, hbt,
    Sem.Result.ofOption, Sem.Result.bind_ok]
  rw [Fir.eval_case]
  simp only [Src.NatMap.get?_insert_self, Sem.Result.ofOption, Sem.Result.bind_ok, Fir.Val.asCtor,
    Fir.evalAlts_cons, ↓reduceIte]
  rw [Fir.eval_ret]
  simp [Fir.Arg.eval, FirFacts.get?_insert_ne _ _ (by decide : 6 ≠ 5), Src.NatMap.get?_insert_self,
    Sem.Result.ofOption]

/-- info: 'IxCC.AiurBackend.Audit.demoProgram_lowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demoProgram_lowers

/-- info: 'IxCC.AiurBackend.Audit.demoProgram_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demoProgram_runs

/-! ## 5. Composition with the Compiler's Front Half (`IxCCAiur.Compose`)

The lowered program is the Fir program `Recheck.runFir` makes. `Recheck.front_fir`
is the front half's refinement down to Fir; `Compose.entry_source_backward` and
`Compose.circuit_source_backward_goldilocks` read an accepted run at the source
evaluator **with the stuck-source disjunct**; the `…_sound` forms take source
progress on the input (`Compose.NeverStuck`) as a hypothesis. -/

/--
info: @Recheck.front_fir : ∀ {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {f : Recheck.FrontFir},
  Recheck.runFir cfg P c = Except.ok f → Sem.RefinesOn (f.Covered c) { p := f.src, ch := f.checked } f.fir
-/
#guard_msgs (whitespace := lax) in
#check @Recheck.front_fir

/--
info: @Recheck.runLir_runFir : ∀ {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {f : Recheck.Front},
  Recheck.runLir cfg P c = Except.ok f →
    Recheck.runFir cfg P c = Except.ok { src := f.src, checked := f.checked, lam := f.lam, anf := f.anf, fir := f.fir }
-/
#guard_msgs (whitespace := lax) in
#check @Recheck.runLir_runFir

/--
info: @Compose.source_of_fir_run : ∀ {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {f : Recheck.FrontFir},
  Recheck.runFir cfg P c = Except.ok f →
    ∀ {i : ℕ} {g : FunId},
      f.fir.exports[i]? = some g →
        ∀ {ns : List ℕ} {k : ℕ} {w : Val},
          run f.fir k g (List.map (fun n => Val.lit (Lit.nat n)) ns) = Sem.Result.ok w →
            f.Covered c (i, ns) →
              (∃ k' v, Sem.Lang.run { p := f.src, ch := f.checked } (i, ns) k' = Sem.Result.ok v ∧ Sem.Lang.ObsEq v w) ∨
                ∃ k', Sem.Lang.run { p := f.src, ch := f.checked } (i, ns) k' = Sem.Result.stuck
-/
#guard_msgs (whitespace := lax) in
#check @Compose.source_of_fir_run

/--
info: @Compose.entry_source_backward : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {cfg : Recheck.Config}
  {P : Src.Program} {c : Recheck.Cert} {f : Recheck.FrontFir},
  Recheck.runFir cfg P c = Except.ok f →
    ∀ {prog : Aiur.Generic.Program ℕ} {world : Aiur.Generic.SourceSemantics.World F},
      FieldCompatible F →
        LoweredWorld f.fir prog world →
          ∀ {i : ℕ} {g : FunId},
            f.fir.exports[i]? = some g →
              ∀ {args : List (Aiur.SourceValue F)} {h' : Aiur.Heap F} {r : Aiur.SourceValue F},
                Aiur.Generic.SourceSemantics.EvalFn world (qualified (entryName i)) args [] r h' →
                  ∃ ns w,
                    (∀ n ∈ ns, n < natLimit) ∧
                      args = List.map (fun n => Aiur.Value.field ↑n) ns ∧
                        VR f.fir objQName bytesQName h' w r ∧
                          (f.Covered c (i, ns) →
                            (∃ k v,
                                Sem.Lang.run { p := f.src, ch := f.checked } (i, ns) k = Sem.Result.ok v ∧
                                  Sem.Lang.ObsEq v w) ∨
                              ∃ k, Sem.Lang.run { p := f.src, ch := f.checked } (i, ns) k = Sem.Result.stuck)
-/
#guard_msgs (whitespace := lax) in
#check @Compose.entry_source_backward

/--
info: @Compose.entry_source_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {cfg : Recheck.Config}
  {P : Src.Program} {c : Recheck.Cert} {f : Recheck.FrontFir},
  Recheck.runFir cfg P c = Except.ok f →
    ∀ {prog : Aiur.Generic.Program ℕ} {world : Aiur.Generic.SourceSemantics.World F},
      FieldCompatible F →
        LoweredWorld f.fir prog world →
          ∀ {i : ℕ} {g : FunId},
            f.fir.exports[i]? = some g →
              ∀ {args : List (Aiur.SourceValue F)} {h' : Aiur.Heap F} {r : Aiur.SourceValue F},
                Aiur.Generic.SourceSemantics.EvalFn world (qualified (entryName i)) args [] r h' →
                  (∀ (ns : List ℕ),
                      args = List.map (fun n => Aiur.Value.field ↑n) ns →
                        Compose.NeverStuck { p := f.src, ch := f.checked } (i, ns)) →
                    ∃ ns w,
                      (∀ n ∈ ns, n < natLimit) ∧
                        args = List.map (fun n => Aiur.Value.field ↑n) ns ∧
                          VR f.fir objQName bytesQName h' w r ∧
                            (f.Covered c (i, ns) →
                              ∃ k v,
                                Sem.Lang.run { p := f.src, ch := f.checked } (i, ns) k = Sem.Result.ok v ∧
                                  Sem.Lang.ObsEq v w)
-/
#guard_msgs (whitespace := lax) in
#check @Compose.entry_source_sound

/--
info: @Compose.circuit_source_backward_goldilocks : ∀ {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
  {f : Recheck.FrontFir},
  Recheck.runFir cfg P c = Except.ok f →
    ∀ {prog : Aiur.Generic.Program ℕ} {moduleProg : Aiur.Modules.Program Aiur.Library.U32.Goldilocks.F}
      {id : String → Except String ℕ} (prepared : Aiur.Modules.Prepared moduleProg),
      LoweredWorld f.fir prog prepared.environment.source.world →
        ∀ (compiled : Aiur.Optimized.ModulesArtifact prepared)
          (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact) {dcfg : Aiur.Optimized.Depth.Config},
          Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical dcfg →
            dcfg.bits ≤ 24 →
              ∀ (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system dcfg physical.system) id),
                plan.WellFormedActivation →
                  ∀ {external : String}
                    {entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances},
                    prepared.find? external = some entry →
                      ∀ {i : ℕ} {g : FunId},
                        entry.resolved.name = qualified (entryName i) →
                          f.fir.exports[i]? = some g →
                            ∀ {rom : Aiur.WidthROM Aiur.Library.U32.Goldilocks.F},
                              rom.Valid →
                                ∀ {args : List (Aiur.SourceValue Aiur.Library.U32.Goldilocks.F)}
                                  {result : Aiur.Value Aiur.Library.U32.Goldilocks.F}
                                  {wires : List (Aiur.WireValue Aiur.Library.U32.Goldilocks.F)}
                                  {output : Aiur.WireValue Aiur.Library.U32.Goldilocks.F},
                                  Aiur.Circuit.Erasure.Signed compiled.circuit.system
                                      { channel := entry.resolved.name, args := wires, result := output } →
                                    ∀ {root : Aiur.Circuit.Message Aiur.Library.U32.Goldilocks.F},
                                      Aiur.Optimized.Depth.erase dcfg root =
                                          Aiur.Circuit.Erasure.message compiled.circuit.system
                                            { channel := entry.resolved.name, args := wires, result := output } →
                                        root.channel ∉ dcfg.names →
                                          ∀ {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.U32.Goldilocks.F)},
                                            rows.length ≤ 2 ^ 39 →
                                              plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows =
                                                  Except.ok () →
                                                Aiur.DecodesValues compiled.specialized.program.enums wires
                                                    (Aiur.entryValues args) →
                                                  Aiur.WireValue.decode compiled.specialized.program.enums output =
                                                      some result →
                                                    ∃ value heap ns w,
                                                      (∀ n ∈ ns, n < natLimit) ∧
                                                        args = List.map (fun n => Aiur.Value.field ↑n) ns ∧
                                                          VR f.fir objQName bytesQName heap w value ∧
                                                            Aiur.Represents
                                                                (Aiur.WireROM.decode compiled.specialized.program.enums
                                                                  (Aiur.Circuit.Erasure.typedROM compiled.circuit.system
                                                                    rom))
                                                                heap value result ∧
                                                              (f.Covered c (i, ns) →
                                                                (∃ k v,
                                                                    Sem.Lang.run { p := f.src, ch := f.checked } (i, ns)
                                                                        k =
                                                                      Sem.Result.ok v ∧
                                                                    Sem.Lang.ObsEq v w) ∨
                                                                  ∃ k,
                                                                    Sem.Lang.run { p := f.src, ch := f.checked } (i, ns)
                                                                        k =
                                                                      Sem.Result.stuck)
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Compose.circuit_source_backward_goldilocks

/-- info: 'IxCC.Recheck.front_fir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Recheck.front_fir

/-- info: 'IxCC.Recheck.runLir_runFir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Recheck.runLir_runFir

/-- info: 'IxCC.AiurBackend.Compose.lang_run_of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Compose.lang_run_of_run

/-- info: 'IxCC.AiurBackend.Compose.source_of_fir_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Compose.source_of_fir_run

/-- info: 'IxCC.AiurBackend.Compose.entry_source_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Compose.entry_source_backward

/-- info: 'IxCC.AiurBackend.Compose.entry_source_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Compose.entry_source_sound

/-- info: 'IxCC.AiurBackend.Compose.circuit_source_backward_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Compose.circuit_source_backward_goldilocks

/-- info: 'IxCC.AiurBackend.Compose.circuit_source_sound_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Compose.circuit_source_sound_goldilocks

/-! ## 6. The World Check, the Public Result and the `fib` Instance

`World.loweredWorld_of_check` replaces the world hypothesis by a Boolean on
the prepared source; it rests on `==` being equality on `Aiur.Generic.Expr`
(`Aiur.Generic.Expr.eq_of_beq`, in the `aiur` package). `Claim.Accepted` is the
bundle of what the circuit theorems assume about a claim, printed in full
below. `Claim.accepted_nat_backward` reads a `Prog::Obj::N(y)` result at the
source, and `Fib.accepted_backward` and `Fib.accepted_sound` are its instance
for the K1 `fib` closure, on which the kernel evaluates the front half
(`Fib.summary_fib`, by `decide +kernel`: no axiom beyond the three). -/

/--
info: @Aiur.Generic.Expr.eq_of_beq : ∀ {α : Type} [inst : BEq α] [LawfulBEq α] (a b : Aiur.Generic.Expr α),
  a.beq b = true → a = b
-/
#guard_msgs (whitespace := lax) in
#check @Aiur.Generic.Expr.eq_of_beq

/--
info: @World.loweredWorld_of_check : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F],
  FieldCompatible F →
    ∀ {P : Program} {prog : Aiur.Generic.Program ℕ},
      lowerProgram P = Except.ok prog →
        ∀ (s : Aiur.Generic.Source F), World.checkWorld s prog = true → LoweredWorld P prog s.world
-/
#guard_msgs (whitespace := lax) in
#check @World.loweredWorld_of_check

/--
info: def IxCC.AiurBackend.Claim.Accepted : {moduleProg : Aiur.Modules.Program Claim.G} →
  Aiur.Modules.Prepared moduleProg → ℕ → List (Aiur.SourceValue Claim.G) → Aiur.Value Claim.G → Prop :=
fun {moduleProg} prepared i args result =>
  ∃ id compiled physical dcfg plan external entry rom wires output root rows,
    Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical dcfg ∧
      dcfg.bits ≤ 24 ∧
        plan.WellFormedActivation ∧
          prepared.find? external = some entry ∧
            entry.resolved.name = qualified (entryName i) ∧
              rom.Valid ∧
                Aiur.Circuit.Erasure.Signed compiled.circuit.system
                    { channel := entry.resolved.name, args := wires, result := output } ∧
                  Aiur.Optimized.Depth.erase dcfg root =
                      Aiur.Circuit.Erasure.message compiled.circuit.system
                        { channel := entry.resolved.name, args := wires, result := output } ∧
                    root.channel ∉ dcfg.names ∧
                      rows.length ≤ 2 ^ 39 ∧
                        plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = Except.ok () ∧
                          Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args) ∧
                            Aiur.WireValue.decode compiled.specialized.program.enums output = some result
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#print Claim.Accepted

/--
info: @Claim.accepted_nat_backward : ∀ {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {f : Recheck.FrontFir},
  Recheck.runFir cfg P c = Except.ok f →
    ∀ {prog : Aiur.Generic.Program ℕ},
      lowerProgram f.fir = Except.ok prog →
        ∀ {moduleProg : Aiur.Modules.Program Claim.G} (prepared : Aiur.Modules.Prepared moduleProg),
          World.checkWorld prepared.environment.source prog = true →
            ∀ {i : ℕ} {g : FunId},
              f.fir.exports[i]? = some g →
                ∀ {as : List Claim.G} {y : Claim.G},
                  Claim.Accepted prepared i (List.map Aiur.Value.field as)
                      (Aiur.Value.construct Claim.G objQName "N" [Aiur.Value.field Claim.G y]) →
                    f.Covered c (i, List.map ZMod.val as) →
                      (∃ k v,
                          Sem.Lang.run { p := f.src, ch := f.checked } (i, List.map ZMod.val as) k = Sem.Result.ok v ∧
                            Sem.Lang.obs v = some (Sem.Obs.nat (ZMod.val y))) ∨
                        ∃ k, Sem.Lang.run { p := f.src, ch := f.checked } (i, List.map ZMod.val as) k = Sem.Result.stuck
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Claim.accepted_nat_backward

/--
info: Fib.summary_fib : Fib.summary
    (Recheck.runFir IxCCTests.Recheck.Artifacts.Fib.cfg IxCCTests.Recheck.Artifacts.Fib.program
      IxCCTests.Recheck.Artifacts.Fib.cert) =
  some (some 1, 1)
-/
#guard_msgs (whitespace := lax) in
#check @Fib.summary_fib

/--
info: @Fib.accepted_backward : ∀ {f : Recheck.FrontFir},
  Recheck.runFir IxCCTests.Recheck.Artifacts.Fib.cfg IxCCTests.Recheck.Artifacts.Fib.program
        IxCCTests.Recheck.Artifacts.Fib.cert =
      Except.ok f →
    ∀ {prog : Aiur.Generic.Program ℕ},
      lowerProgram f.fir = Except.ok prog →
        ∀ {moduleProg : Aiur.Modules.Program Claim.G} (prepared : Aiur.Modules.Prepared moduleProg),
          World.checkWorld prepared.environment.source prog = true →
            ∀ {x y : Claim.G},
              Claim.Accepted prepared 0 [Aiur.Value.field x]
                  (Aiur.Value.construct Claim.G objQName "N" [Aiur.Value.field Claim.G y]) →
                (∃ k v,
                    Sem.Lang.run { p := f.src, ch := f.checked } (0, [ZMod.val x]) k = Sem.Result.ok v ∧
                      Sem.Lang.obs v = some (Sem.Obs.nat (ZMod.val y))) ∨
                  ∃ k, Sem.Lang.run { p := f.src, ch := f.checked } (0, [ZMod.val x]) k = Sem.Result.stuck
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Fib.accepted_backward

/--
info: @Fib.accepted_sound : ∀ {f : Recheck.FrontFir},
  Recheck.runFir IxCCTests.Recheck.Artifacts.Fib.cfg IxCCTests.Recheck.Artifacts.Fib.program
        IxCCTests.Recheck.Artifacts.Fib.cert =
      Except.ok f →
    ∀ {prog : Aiur.Generic.Program ℕ},
      lowerProgram f.fir = Except.ok prog →
        ∀ {moduleProg : Aiur.Modules.Program Claim.G} (prepared : Aiur.Modules.Prepared moduleProg),
          World.checkWorld prepared.environment.source prog = true →
            ∀ {x y : Claim.G},
              Claim.Accepted prepared 0 [Aiur.Value.field x]
                  (Aiur.Value.construct Claim.G objQName "N" [Aiur.Value.field Claim.G y]) →
                Compose.NeverStuck { p := f.src, ch := f.checked } (0, [ZMod.val x]) →
                  ∃ k v,
                    Sem.Lang.run { p := f.src, ch := f.checked } (0, [ZMod.val x]) k = Sem.Result.ok v ∧
                      Sem.Lang.obs v = some (Sem.Obs.nat (ZMod.val y))
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Fib.accepted_sound

/--
info: 'Aiur.Generic.Pattern.eq_of_beq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Aiur.Generic.Pattern.eq_of_beq

/--
info: 'Aiur.Generic.Expr.eq_of_beq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Aiur.Generic.Expr.eq_of_beq

/--
info: 'IxCC.AiurBackend.World.loweredWorld_of_check' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms World.loweredWorld_of_check

/--
info: 'IxCC.AiurBackend.Claim.entry_source_backward_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Claim.entry_source_backward_checked

/--
info: 'IxCC.AiurBackend.Claim.accepted_source_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Claim.accepted_source_backward

/--
info: 'IxCC.AiurBackend.Claim.accepted_nat_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Claim.accepted_nat_backward

/--
info: 'IxCC.AiurBackend.Claim.accepted_nat_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Claim.accepted_nat_sound

/--
info: 'IxCC.AiurBackend.Claim.accepted_enum_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Claim.accepted_enum_backward

/--
info: 'IxCC.AiurBackend.Claim.accepted_enum_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Claim.accepted_enum_sound

/--
info: 'IxCC.AiurBackend.Fib.summary_fib' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Fib.summary_fib

/--
info: 'IxCC.AiurBackend.Fib.accepted_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Fib.accepted_backward

/--
info: 'IxCC.AiurBackend.Fib.accepted_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Fib.accepted_sound

/-! ## 7. Without the Escape: Source Progress from the Shape Decision

`Progress.checkShape` is the source-progress lane's shape decision
(`Shape2.certOk` and the root's instance) as a Boolean on the checked source,
and `Progress.neverStuck_of_checkShape` its soundness for
`Compose.NeverStuck`, by the lane's `Shape2.neverStuck_checked`
(`IxCCCorrect.ShapeHook`). `Instance.decision` is one Boolean per closure on the
front half's result, and `Fib.accepted`, `Gcd.accepted` and the three of
`IxCCAiur.Roots` are the statements **with no disjunct and no progress
hypothesis**: the kernel evaluates the decision (`decide +kernel`). -/

/--
info: @Progress.neverStuck_of_checkShape : ∀ {src : Src.Program} {ch : Src.Relevance.Checked} {cert : Correct.Shape2.Cert}
  {r : ℕ} {ns : List ℕ},
  Progress.checkShape src cert r ns.length = true → Compose.NeverStuck { p := src, ch := ch } (r, ns)
-/
#guard_msgs (whitespace := lax) in
#check @Progress.neverStuck_of_checkShape

/--
info: def IxCC.AiurBackend.Progress.checkShape : Src.Program → Correct.Shape2.Cert → ℕ → ℕ → Bool :=
fun src cert r n =>
  Correct.Shape2.certOk src cert &&
    match src.roots[r]? with
    | some (fst, c) =>
      cert.insts.any fun e => decide (e.1 = c) && decide (e.2.1 = []) && (Progress.resultAfter n e.2.2).isSome
    | none => false
-/
#guard_msgs (whitespace := lax) in
#print Progress.checkShape

/--
info: def IxCC.AiurBackend.Instance.decision : ℕ → Except Recheck.Err Recheck.FrontFir → Bool :=
fun n x =>
  match x with
  | Except.ok f =>
    f.fir.exports[0]?.isSome &&
      match f.src.roots[0]? with
      | some (fst, c) =>
        decide (Recheck.declaredParams f.src c = some n) &&
          Progress.checkShape f.src (Correct.Shape2.Produce.produce f.src c) 0 n
      | none => false
  | Except.error a => false
-/
#guard_msgs (whitespace := lax) in
#print Instance.decision

/--
info: @Instance.accepted_nat : ∀ {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {n : ℕ} {f : Recheck.FrontFir},
  Recheck.runFir cfg P c = Except.ok f →
    Instance.decision n (Recheck.runFir cfg P c) = true →
      ∀ {prog : Aiur.Generic.Program ℕ},
        lowerProgram f.fir = Except.ok prog →
          ∀ {moduleProg : Aiur.Modules.Program Claim.G} (prepared : Aiur.Modules.Prepared moduleProg),
            World.checkWorld prepared.environment.source prog = true →
              ∀ {as : List Claim.G},
                as.length = n →
                  ∀ {y : Claim.G},
                    Claim.Accepted prepared 0 (List.map Aiur.Value.field as)
                        (Aiur.Value.construct Claim.G objQName "N" [Aiur.Value.field Claim.G y]) →
                      ∃ k v,
                        Sem.Lang.run { p := f.src, ch := f.checked } (0, List.map ZMod.val as) k = Sem.Result.ok v ∧
                          Sem.Lang.obs v = some (Sem.Obs.nat (ZMod.val y))
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Instance.accepted_nat

/--
info: Fib.decision_fib : Instance.decision 1
    (Recheck.runFir IxCCTests.Recheck.Artifacts.Fib.cfg IxCCTests.Recheck.Artifacts.Fib.program
      IxCCTests.Recheck.Artifacts.Fib.cert) =
  true
-/
#guard_msgs (whitespace := lax) in
#check @Fib.decision_fib

/--
info: @Fib.accepted : ∀ {f : Recheck.FrontFir},
  Recheck.runFir IxCCTests.Recheck.Artifacts.Fib.cfg IxCCTests.Recheck.Artifacts.Fib.program
        IxCCTests.Recheck.Artifacts.Fib.cert =
      Except.ok f →
    ∀ {prog : Aiur.Generic.Program ℕ},
      lowerProgram f.fir = Except.ok prog →
        ∀ {moduleProg : Aiur.Modules.Program Claim.G} (prepared : Aiur.Modules.Prepared moduleProg),
          World.checkWorld prepared.environment.source prog = true →
            ∀ {x y : Claim.G},
              Claim.Accepted prepared 0 [Aiur.Value.field x]
                  (Aiur.Value.construct Claim.G objQName "N" [Aiur.Value.field Claim.G y]) →
                ∃ k v,
                  Sem.Lang.run { p := f.src, ch := f.checked } (0, [ZMod.val x]) k = Sem.Result.ok v ∧
                    Sem.Lang.obs v = some (Sem.Obs.nat (ZMod.val y))
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Fib.accepted

/--
info: @Gcd.accepted : ∀ {f : Recheck.FrontFir},
  Recheck.runFir IxCCTests.Recheck.Artifacts.Gcd.cfg IxCCTests.Recheck.Artifacts.Gcd.program
        IxCCTests.Recheck.Artifacts.Gcd.cert =
      Except.ok f →
    ∀ {prog : Aiur.Generic.Program ℕ},
      lowerProgram f.fir = Except.ok prog →
        ∀ {moduleProg : Aiur.Modules.Program Claim.G} (prepared : Aiur.Modules.Prepared moduleProg),
          World.checkWorld prepared.environment.source prog = true →
            ∀ {a b y : Claim.G},
              Claim.Accepted prepared 0 [Aiur.Value.field a, Aiur.Value.field b]
                  (Aiur.Value.construct Claim.G objQName "N" [Aiur.Value.field Claim.G y]) →
                ∃ k v,
                  Sem.Lang.run { p := f.src, ch := f.checked } (0, [ZMod.val a, ZMod.val b]) k = Sem.Result.ok v ∧
                    Sem.Lang.obs v = some (Sem.Obs.nat (ZMod.val y))
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Gcd.accepted

/--
info: 'IxCC.AiurBackend.Progress.neverStuck_of_checkShape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Progress.neverStuck_of_checkShape

/--
info: 'IxCC.AiurBackend.Progress.accepted_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Progress.accepted_nat

/--
info: 'IxCC.AiurBackend.Progress.accepted_enum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Progress.accepted_enum

/--
info: 'IxCC.AiurBackend.Instance.accepted_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Instance.accepted_nat

/--
info: 'IxCC.AiurBackend.Fib.decision_fib' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Fib.decision_fib

/--
info: 'IxCC.AiurBackend.Fib.accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Fib.accepted

/--
info: 'IxCC.AiurBackend.Gcd.accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gcd.accepted

/--
info: 'IxCC.AiurBackend.EvenOdd.accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms EvenOdd.accepted

/--
info: 'IxCC.AiurBackend.Sfib.accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Sfib.accepted

/--
info: 'IxCC.AiurBackend.Tak.accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Tak.accepted

end IxCC.AiurBackend.Audit
