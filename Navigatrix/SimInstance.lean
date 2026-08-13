import Navigatrix.Sim

/-!
# The first theorem, applied

`erasure_sim` instantiated on a real program: `add 2̂ 3̂` over the
hand-written Nat store (the same shapes as the reference-evaluator
and differential suites). This file closes the loop between the
theorem and the executable pass:

- the **erased environment is pinned to the executable eraser** — a
  `#guard` checks `Erase.eraseProgram` produces exactly the
  hand-written `erasedList` the proofs run against (the CompCert
  split: validate the executable, prove against the spec-shaped
  data; the guard makes drift impossible);
- `Covered` / `RecMember` / `RulesRel` derivations are built
  concretely for every address the program touches — including the
  recursor member with both rule bodies (the successor rule exercises
  `recurS`, the guarded ghost application, and the rule mask);
- the source run is an executable fact (`rfl` through the reference
  evaluator), and `erasure_sim_closed` concludes: the erased program
  terminates with a value related to the source's `5̂`.

If any relation clause failed to cover what the eraser actually
emits, this file would not elaborate.
-/

namespace Navigatrix.SimInstance

open Navigatrix.Ixon (Uses Recursor RecursorRule MutConst Constant
  ConstantInfo)
open Navigatrix.Sim

private def addrOf (n : UInt8) : Ixon.Address :=
  ⟨ByteArray.mk (Array.mk (List.replicate 32 n))⟩

private def aNatBlock := addrOf 0x10
private def aNat := addrOf 0x11
private def aZero := addrOf 0x12
private def aSucc := addrOf 0x13
private def aNatRec := addrOf 0x14
private def aAdd := addrOf 0x15

/-! ## The source store (the reference-evaluator suite's shapes) -/

private def natInd : Navigatrix.Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0
    typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0
        typ := .recur 0 #[] },
      { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
        typ := .all .many .shared (.recur 0 #[]) (.recur 0 #[]) }] }

private def natRec : Recursor :=
  { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0
    motives := 1, minors := 2, typ := .sort 0
    rules := #[
      { fields := 0
        rhs := .lam .many (.sort 0) (.lam .many (.sort 0)
          (.lam .many (.sort 0) (.var 1))) },
      { fields := 1
        rhs := .lam .many (.sort 0) (.lam .many (.sort 0)
          (.lam .many (.sort 0) (.lam .many (.recur 0 #[])
            (.app (.app (.var 1) (.var 0))
              (.app (.app (.app (.app (.recur 1 #[0]) (.var 3)) (.var 2))
                (.var 1)) (.var 0)))))) }] }

private def cNatBlock : Constant :=
  { info := .muts #[.indc natInd, .recr natRec]
    sharing := #[], refs := #[], univs := #[.var 0] }

private def prjConst (info : ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def cNat := prjConst (.iPrj { idx := 0, block := aNatBlock })
private def cZero :=
  prjConst (.cPrj { idx := 0, cidx := 0, block := aNatBlock })
private def cSucc :=
  prjConst (.cPrj { idx := 0, cidx := 1, block := aNatBlock })
private def cNatRec := prjConst (.rPrj { idx := 1, block := aNatBlock })

/-- `fun m n => Nat.rec.{1} (fun _ => Nat) m (fun k ih => succ ih) n` —
refs: 0 = Nat, 1 = zero, 2 = succ, 3 = Nat.rec. -/
private def cAdd : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .many .shared (.ref 0 #[])
          (.all .many .shared (.ref 0 #[]) (.ref 0 #[]))
        value := .lam .many (.ref 0 #[]) (.lam .many (.ref 0 #[])
          (.app (.app (.app (.app (.ref 3 #[0])
            (.lam .many (.ref 0 #[]) (.ref 0 #[])))
            (.var 1))
            (.lam .many (.ref 0 #[]) (.lam .many (.ref 0 #[])
              (.app (.ref 2 #[]) (.var 0)))))
            (.var 0))) }
    sharing := #[], refs := #[aNat, aZero, aSucc, aNatRec]
    univs := #[.succ .zero] }

private def storeL : List (Ixon.Address × Constant) :=
  [(aNatBlock, cNatBlock), (aNat, cNat), (aZero, cZero), (aSucc, cSucc),
   (aNatRec, cNatRec), (aAdd, cAdd)]

private def resolver : Ixon.Address → Option Constant := fun a =>
  (storeL.find? (fun p => p.1 == a)).map (·.2)

private def ectxI : Ixon.Eval.EvalCtx :=
  { resolve := resolver, natBlock := some aNatBlock }

private def ectxE : Erase.EraseCtx :=
  { resolve := resolver, natBlock := some aNatBlock }

/-! ## The erased environment, pinned to the executable pass -/

/-- Expected erasure of the successor rule's body. -/
private def succRuleBody' : IxIR0.Expr :=
  .app (.app (.var 1) (.var 0))
    (.app (.app (.app (.app (.var 4) .erased) (.var 2)) (.var 1))
      (.var 0))

/-- Expected erasure of `add`'s body: motive ghosted to `◻`, the
recursor referenced by address, the minor's lambdas kept. -/
private def addBody' : IxIR0.Expr :=
  .lam .many (.lam .many
    (.app
      (.app (.app (.app (.ref aNatRec) .erased) (.var 1))
        (.lam .many (.lam .many (.app (.ref aSucc) (.var 0)))))
      (.var 0)))

private def maNat := Erase.memberAddr aNatBlock 0
private def maNatRec := Erase.memberAddr aNatBlock 1

private def erasedList : List (Ixon.Address × IxIR0.Decl) :=
  [(maNat, .defn .erased),
   (maNatRec, .recursor 3 true #[
     { fields := 0, rhs := .var 1 },
     { fields := 1, rhs := succRuleBody' }]),
   (aNat, .defn .erased),
   (aZero, .ctor 0 0),
   (aSucc, .ctor 1 1),
   (aNatRec, .defn (.ref maNatRec)),
   (aAdd, .defn addBody')]

-- The hand-written erased environment IS the executable eraser's
-- output — the proofs below cannot drift from the pass.
#guard (match Erase.eraseProgram ectxE storeL with
  | .ok l => l == erasedList
  | .error _ => false)

private def ienv : IxIR0.Env := IxIR0.Env.ofList erasedList

private def ictxI : IxIR0.Ctx := { env := ienv }

/-! ## The program -/

/-- Evaluation frame: refs 0 = add, 1 = zero, 2 = succ. -/
private def testFI : Ixon.Eval.Frame :=
  { refs := #[aAdd, aZero, aSucc] }

private def natE : Nat → Ixon.Expr
  | 0 => .ref 1 #[]
  | n + 1 => .app (.ref 2 #[]) (natE n)

private def natE' : Nat → IxIR0.Expr
  | 0 => .ref aZero
  | n + 1 => .app (.ref aSucc) (natE' n)

private def addE : Ixon.Expr :=
  .app (.app (.ref 0 #[]) (natE 2)) (natE 3)

private def addE' : IxIR0.Expr :=
  .app (.app (.ref aAdd) (natE' 2)) (natE' 3)

/-! ## Coverage derivations -/

private theorem covZero : Covered ectxI ictxI aZero :=
  .ctor rfl rfl ⟨cNatBlock, natInd, natInd.ctors[0]!, rfl, rfl, rfl,
    rfl, rfl⟩ rfl

private theorem covSucc : Covered ectxI ictxI aSucc :=
  .ctor rfl rfl ⟨cNatBlock, natInd, natInd.ctors[1]!, rfl, rfl, rfl,
    rfl, rfl⟩ rfl

/-- The zero rule's body relation: `z` under the rule mask. -/
private theorem zeroRuleDer : PErase ectxI ictxI (some (aNatBlock, 1))
    cNatBlock.refs (Ixon.Eval.selfMutsOf cNatBlock.info) (some aNatBlock)
    (ruleMask 1 2 0) (.var 1) (.var 1) :=
  .var rfl

/-- The successor rule's body relation: the ghost motive argument goes
through the guarded `appG`, the self-reference through `recurS`. -/
private theorem succRuleDer : PErase ectxI ictxI (some (aNatBlock, 1))
    cNatBlock.refs (Ixon.Eval.selfMutsOf cNatBlock.info) (some aNatBlock)
    (ruleMask 1 2 1)
    (.app (.app (.var 1) (.var 0))
      (.app (.app (.app (.app (.recur 1 #[0]) (.var 3)) (.var 2))
        (.var 1)) (.var 0)))
    succRuleBody' :=
  .app (.app (.var rfl) (.var rfl))
    (.app (.app (.app (.appG (.head (.recurH rfl rfl rfl rfl))
      (by decide) (.recurS rfl)) (.var rfl)) (.var rfl)) (.var rfl))

private theorem recMem : RecMember ectxI ictxI aNatBlock 1 natRec :=
  .mk rfl rfl rfl rfl
    (.cons rfl rfl zeroRuleDer (.cons rfl rfl succRuleDer .nil))

private theorem covNatRec : Covered ectxI ictxI aNatRec :=
  .recrP rfl rfl rfl rfl recMem

/-- The source body of `add`, as stored in `cAdd`. -/
private def addSrcBody : Ixon.Expr :=
  .lam .many (.ref 0 #[]) (.lam .many (.ref 0 #[])
    (.app (.app (.app (.app (.ref 3 #[0])
      (.lam .many (.ref 0 #[]) (.ref 0 #[])))
      (.var 1))
      (.lam .many (.ref 0 #[]) (.lam .many (.ref 0 #[])
        (.app (.ref 2 #[]) (.var 0)))))
      (.var 0)))

/-- `add`'s erased body relates to its source under the definition's
tables — the ghost motive at the call site goes through `appG` with
the `refH` spine guard. -/
private theorem addBodyDer : PErase ectxI ictxI none cAdd.refs
    (Ixon.Eval.selfMutsOf cAdd.info) none [] addSrcBody addBody' :=
  .lamK rfl (.lamK rfl
    (.app
      (.app
        (.app
          (.appG (.head (.refH rfl rfl rfl rfl rfl rfl)) (by decide)
            (.ref rfl covNatRec))
          (.var rfl))
        (.lamK rfl (.lamK rfl (.app (.ref rfl covSucc) (.var rfl)))))
      (.var rfl)))

private theorem covAdd : Covered ectxI ictxI aAdd :=
  .defn rfl rfl rfl rfl addBodyDer

/-! ## The instance -/

private theorem natEDer : ∀ (n : Nat), PErase ectxI ictxI none
    testFI.refs testFI.selfMuts testFI.selfAddr [] (natE n) (natE' n) := by
  intro n
  induction n with
  | zero => exact .ref rfl covZero
  | succ k ih => exact .app (.ref rfl covSucc) ih

private theorem addEDer : PErase ectxI ictxI none testFI.refs
    testFI.selfMuts testFI.selfAddr [] addE addE' :=
  .app (.app (.ref rfl covAdd) (natEDer 2)) (natEDer 3)

/-- **The first theorem, applied**: whenever the source `add 2̂ 3̂`
terminates (it does — the `#guard` below witnesses the hypothesis
executably; the fueled interpreters are well-founded definitions, so
runs are compiler facts, not kernel `rfl`s), its erasure terminates
under the IxIR₀ semantics with a related value. The content is the
coverage derivation `addEDer`: it elaborates only because the
relation covers exactly what the executable eraser emits. -/
theorem addSim {fuel : Nat} {v : Ixon.Eval.Value}
    (hev : Ixon.Eval.eval ectxI fuel testFI [] addE = .ok v) :
    ∃ fuel' v', IxIR0.eval ictxI fuel' [] addE' = .ok v' ∧
      ValRel ectxI ictxI v v' :=
  erasure_sim_closed hev addEDer

-- The hypothesis is inhabited: the source run computes `5̂`…
private def srcNatOf? : Nat → Ixon.Eval.Value → Option Nat
  | 0, _ => none
  | _, .ctorV _ _ 0 [] => some 0
  | f + 1, .ctorV _ _ 1 [v] => (srcNatOf? f v).map (· + 1)
  | _, _ => none

#guard (match Ixon.Eval.eval ectxI 1000 testFI [] addE with
  | .ok v => srcNatOf? 100 v == some 5
  | .error _ => false)

-- …and the erased run computes `5̂` on the target evaluator.
#guard (match IxIR0.eval ictxI 1000 [] addE' with
  | .ok (.ctor _ 1 [.ctor _ 1 [.ctor _ 1 [.ctor _ 1 [.ctor _ 1
      [.ctor _ 0 []]]]]]) => true
  | _ => false)

end Navigatrix.SimInstance
