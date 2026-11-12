import Ix.Cli.FormalAiur
import Ix.IxVM.ClaimHarness
import Ix.AiurInvocation

/-! Real claim fixtures, plus independently specified evaluation inputs.
Run through the Rust host. -/
open Lean IxVM.ClaimHarness

private def claimCase (label : String) (w : ClaimWitness) (accept : Bool := true) :
    Ix.AiurInvocation.Case :=
  { label := label, accept := accept,
    invocation := Ix.Cli.FormalAiur.invocation w.input w.inputIOBuffer }

private def evalCases : Except String (Array Ix.AiurInvocation.Case) := do
  let ty : Ixon.Expr := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
  let value : Ixon.Expr := .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))
  let beta : Ixon.Expr := .app (.leanLam ty (.var 0)) value
  let constant v : Ixon.Constant := ⟨.defn ⟨.defn, .safe, {}, 0, ty, v⟩, #[], #[], #[.zero], #[]⟩
  let input := constant beta
  let output := constant value
  let ia := Address.blake3 (Ixon.ser input)
  let oa := Address.blake3 (Ixon.ser output)
  let env := ({} : Ixon.Env).storeConst ia input |>.storeConst oa output
  let env := { env with anonHints := env.anonHints.insert ia (.regular 0) |>.insert oa (.regular 0) }
  let ctx ← Ix.ClaimContext.ofDefaultTable
  let good ← buildClaimWitness env (.eval ctx ia oa none)
  let unreduced ← buildClaimWitness env (.eval ctx ia ia none)
  return #[claimCase "Eval beta normal form" good,
    claimCase "Eval rejects an unreduced claimed result" unreduced false]

/-- Small, dependency-bearing environment for the orchestration gate. This
exercises real IxVM checking and cross-record calls without importing Init. -/
private def controllerEnv : Ixon.Env := Id.run do
  let ty : Ixon.Expr := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
  let value : Ixon.Expr := .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))
  let mut env : Ixon.Env := {}
  let mut prior : Option Address := none
  for i in [:3] do
    let body := if i == 0 then value else if i == 1 then .ref 0 #[]
      else .app (.leanLam ty (.var 0)) (.ref 0 #[])
    let c : Ixon.Constant := ⟨.defn ⟨.defn, .safe, {}, 0, ty, body⟩,
      #[], prior.toArray, #[.zero], #[]⟩
    let addr := Address.blake3 (Ixon.ser c)
    env := env.storeConst addr c
    env := { env with anonHints := env.anonHints.insert addr (.regular 0) }
    prior := some addr
  let emptyTable : Ix.Kernel.RoleTable := { version := Ix.Kernel.specVersion, bound := #[], evidence := #[] }
  let bytes := emptyTable.toBytes
  return { env with roleBinding := some { address := Address.blake3 bytes, bytes } }

private def findConstWithOrThrow (ixonEnv : Ixon.Env) (label : String)
    (pred : Ixon.ConstantInfo → Bool) : IO (Address × Ixon.ConstantInfo) := do
  for (addr, lc) in ixonEnv.consts do
    if let some c := lc.get? then
      if pred c.info then return (addr, c.info)
  throw <| IO.userError s!"no {label} const found in shared smoke env"

private def singletonTrees (tree : Ix.AssumptionTree) :
    Std.HashMap Address Ix.AssumptionTree :=
  ({} : Std.HashMap _ _).insert tree.root tree

/-- No claim assumes its own subject, and a `CheckEnv` claim owns at least one
constant. Each case pairs the ill-typed `Prop : Prop` with an assumption tree
that would let the circuit skip checking it; the control shows the circuit
rejects it when it is checked. -/
private def assumptionCases : Except String (Array Ix.AiurInvocation.Case) := do
  let prop : Ixon.Expr := .sort 0
  let bad : Ixon.Constant := ⟨.defn ⟨.defn, .safe, {}, 0, prop, prop⟩, #[], #[], #[.zero], #[]⟩
  let ba := Address.blake3 (Ixon.ser bad)
  let env := ({} : Ixon.Env).storeConst ba bad
  let env := { env with anonHints := env.anonHints.insert ba (.regular 0) }
  let ctx ← Ix.ClaimContext.ofDefaultTable
  let some self := Ix.AssumptionTree.canonical #[ba]
    | .error "assumptionCases: no tree for the ill-typed constant"
  let empty : Ix.AssumptionTree := .node .padding .padding
  let control ← buildClaimWitness env (.check ctx ba none)
  let selfCheck ← buildClaimWitness env (.check ctx ba (some self.root)) (singletonTrees self)
  let selfEnv ← buildClaimWitness env (.checkEnv ctx self.root (some self.root))
    (singletonTrees self)
  let emptyEnv ← buildClaimWitness env (.checkEnv ctx empty.root none) (singletonTrees empty)
  return #[claimCase "Check rejects the ill-typed constant (control)" control false,
    claimCase "Check rejects a target in its own assumption set" selfCheck false,
    claimCase "CheckEnv rejects an owned subject in its own assumption set" selfEnv false,
    claimCase "CheckEnv rejects an owned tree with no leaves" emptyEnv false]

private def claimCheckWithAsm (ixonEnv : Ixon.Env) : IO (String × ClaimWitness) := do
  let target ← lookupAddr ixonEnv ``Nat.zero
  let closure := closureFrom ixonEnv target
  let depLeaves : Array Address :=
    closure.fold (init := #[]) fun acc a =>
      if a == target then acc else acc.push a
  let some tree := Ix.AssumptionTree.canonical depLeaves
    | throw <| IO.userError "deps unexpectedly empty for Nat.zero"
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.check (← IO.ofExcept (Ix.ClaimContext.ofEnv ixonEnv)) target (some tree.root))
    (singletonTrees tree)
  pure ("Claim Check with-asm (Nat.zero)", witness)

private def claimCheckEnvFull (ixonEnv : Ixon.Env) : IO (String × ClaimWitness) := do
  let some tree := envCanonicalTree ixonEnv
    | throw <| IO.userError "envCanonicalTree empty"
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.checkEnv (← IO.ofExcept (Ix.ClaimContext.ofEnv ixonEnv)) tree.root none)
    (singletonTrees tree)
  pure ("CheckEnv self-contained (shared smoke env)", witness)

private def claimCheckEnvFrontier (ixonEnv : Ixon.Env) : IO (String × ClaimWitness) := do
  let target ← lookupAddr ixonEnv ``Nat.add_comm
  let some c := ixonEnv.getConst? target
    | throw <| IO.userError "Nat.add_comm constant missing"
  let some ownedTree := Ix.AssumptionTree.canonical #[target]
    | throw <| IO.userError "owned tree build failed"
  let some asmTree := Ix.AssumptionTree.canonical c.refs
    | throw <| IO.userError "asm (frontier) tree build failed"
  let trees := (singletonTrees ownedTree).insert asmTree.root asmTree
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.checkEnv (← IO.ofExcept (Ix.ClaimContext.ofEnv ixonEnv)) ownedTree.root
      (some asmTree.root)) trees
  pure ("CheckEnv frontier-asm (Nat.add_comm)", witness)

private def claimRevealDefnFields (ixonEnv : Ixon.Env) : IO (String × ClaimWitness) := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "Defn"
    fun ci => match ci with | .defn _ => true | _ => false
  let .defn d := info
    | throw <| IO.userError "findConstWith returned non-Defn"
  let revealInfo : Ix.RevealConstantInfo :=
    .defn (some d.kind) (some d.safety) none none none
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.reveal comm revealInfo) {}
  pure ("Claim Reveal Defn (kind+safety)", witness)

private def claimRevealDefnExpr (ixonEnv : Ixon.Env) : IO (String × ClaimWitness) := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "Defn"
    fun ci => match ci with | .defn _ => true | _ => false
  let .defn d := info
    | throw <| IO.userError "findConstWith returned non-Defn"
  let typAddr := Address.blake3 (Ixon.runPut (Ixon.putExpr d.typ))
  let revealInfo : Ix.RevealConstantInfo :=
    .defn none none none (some typAddr) none
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.reveal comm revealInfo) {}
  pure ("Claim Reveal Defn (typ Expr addr)", witness)

private def claimRevealBinderModes : IO (String × ClaimWitness) := do
  let typ : Ixon.Expr := .all (.sort 0) (.lam (.sort 0) (.all (.sort 0) (.var 0)))
  -- the binders' modes, in the record's section
  let modes : Array Ixon.AllMode := #[⟨.unique, .unique⟩, ⟨.once, .shared⟩, ⟨.erased, .borrowed⟩]
  let c : Ixon.Constant :=
    ⟨.axio ⟨false, 0, typ⟩, #[], #[], #[.zero], #[⟨false, 0, 0, modes.map Ixon.BinderNode.never⟩]⟩
  let addr := Address.blake3 (Ixon.ser c)
  let ixonEnv := ({} : Ixon.Env).storeConst addr c
  let typAddr := Address.blake3 (Ixon.runPut (Ixon.putExpr typ))
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.reveal addr (.axio none none (some typAddr))) {}
  pure ("Claim Reveal Expr (binder modes in the section)", witness)

private def claimRevealCPrj (ixonEnv : Ixon.Env) : IO (String × ClaimWitness) := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "CPrj"
    fun ci => match ci with | .cPrj _ => true | _ => false
  let .cPrj p := info
    | throw <| IO.userError "findConstWith returned non-CPrj"
  let revealInfo : Ix.RevealConstantInfo :=
    .cPrj (some p.idx) (some p.cidx) (some p.block)
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.reveal comm revealInfo) {}
  pure ("Claim Reveal CPrj (all fields)", witness)

private def claimContains : IO (String × ClaimWitness) := do
  let a : Address := ⟨⟨Array.replicate 32 0x11⟩⟩
  let b : Address := ⟨⟨Array.replicate 32 0x22⟩⟩
  let c : Address := ⟨⟨Array.replicate 32 0x33⟩⟩
  let some tree := Ix.AssumptionTree.canonical #[a, b, c]
    | throw <| IO.userError "Contains tree build failed"
  let witness ← IO.ofExcept <| buildClaimWitness ({} : Ixon.Env)
    (Ix.Claim.contains tree.root b) (singletonTrees tree)
  pure ("Claim Contains (synthetic 3-leaf)", witness)

def main (args : List String) : IO Unit := do
  -- Without an argument, write into a fresh temporary directory, not a fixed
  -- /tmp path that concurrent runs would share.
  let path ← match args.head? with
    | some path => pure path
    | none => do
      let dir ← IO.FS.createTempDir
      pure (dir / "claims.ixt").toString
  IO.eprintln s!"[formal-aiur-tests] writing {path}"
  let env ← get_env!
  let fixture ← loadIxonEnv ``Nat.add_comm env
  IO.FS.writeBinFile (path ++ ".ixe") (← IO.ofExcept (Ixon.serEnv fixture))
  IO.FS.writeBinFile (path ++ ".controller.ixe") (← IO.ofExcept (Ixon.serEnv controllerEnv))
  let mut cases := (← IO.ofExcept evalCases) ++ (← IO.ofExcept assumptionCases)
  for build in [claimCheckWithAsm,
      claimCheckEnvFull, claimCheckEnvFrontier,
      claimRevealDefnFields, claimRevealDefnExpr,
      claimRevealCPrj] do
    let (label, witness) ← build fixture
    cases := cases.push (claimCase label witness)
  for (label, witness) in [← claimContains, ← claimRevealBinderModes] do
    cases := cases.push (claimCase label witness)
  IO.FS.writeBinFile path (Ix.AiurInvocation.encodeCases cases)
  IO.println s!"Wrote {cases.size} production claim cases and .ixe fixture to {path}"
