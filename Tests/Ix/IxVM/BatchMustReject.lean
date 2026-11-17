import Ix.Meta
import Ix.Compile.BinderData
import Ix.IxVM.Model
import Ix.IxVM.ClaimHarness
import Ix.ClaimContext
import Ix.AssumptionTree
import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.BatchMustRejectDefs

/-!
# The declaration checker's must-reject cases

Hand-built inputs the IxVM program must refuse, each with a control it must accept. Run by
`ixvm-batch-must-reject` (manual). A case whose target is a recursor of a mutual or nested
family, or whose closure holds one, is refused at that recursor while the program refuses
such recursors (`modeledRecursorsRefused`); the case then names the type as well, where the
family check still runs.

* user axioms under a table that leaves `sorryAx` unbound, with a theorem of `False`
  by `sorryAx`; the kernel admits no such table under user axioms;
* a user axiom that restates `propext`'s or `sorryAx`'s specification (the role's own
  record with its type moved into the sharing table: another address); the kernel
  declines such an axiom;
* a recursor whose type mentions itself (a `let` of its own application, which
  reduction erases); the kernel refuses the type before the recursor is installed;
* a nested block's recursor family with an auxiliary motive its constructors do not
  require: `T1`'s family (motives `T1`, `List T1`, `Option T1`) on the block `T2`, whose
  constructor has `K (Option Bool) Unit` where `T1`'s has `K (Option T1) Unit`. Lean's kernel derives no
  `Option` motive for `T2`.
-/

namespace Tests.Ix.IxVM.BatchMustReject

open IxVM.ClaimHarness
open Tests.Ix.IxVM

abbrev E := Ixon.Expr

def st (env : Ixon.Env) (c : Ixon.Constant) : Ixon.Env × Address :=
  let a := Address.blake3 (Ixon.ser c)
  let env := env.storeConst a c
  let env := match c.info with
    | .defn _ | .dPrj _ => { env with anonHints := env.anonHints.insert a (.regular 0) }
    | _ => env
  (env, a)

def annot (env : Ixon.Env) (c : Ixon.Constant) : IO Ixon.Constant := do
  let sup ← IO.ofExcept (Ix.Compile.BinderData.recordsOf env)
  let (env0, a0) := st env c
  let view : IxVM.PwHints.View := {
    records := #[(a0, c)], support := sup, blobs := env0.blobs, hints := env0.anonHints,
    table := env0.roleBinding.map (·.bytes) }
  let k ← IO.ofExcept (IxVM.PwHints.KernelEnv.ofView view)
  let (tables, _) := IxVM.PwHints.annotateKernel k (taint := false)
  let blocks := (tables.find? (·.1 == a0)).map (·.2) |>.getD #[]
  let sec ← IO.ofExcept (Ix.Compile.BinderData.sectionOf c blocks)
  pure { c with binders := sec }

def stAnnot (env : Ixon.Env) (c : Ixon.Constant) : IO (Ixon.Env × Address) := do
  pure (st env (← annot env c))

def withoutModels (env : Ixon.Env) : Ixon.Env :=
  { env with models := {}, modelRecords := {}, modelHints := {}, modelBlobs := {},
             modelDeps := {}, modelsAttached := false }

def boundAddr (t : Ix.Kernel.RoleTable) (r : Ix.Kernel.Role) : Except String Address :=
  match t.bound.find? (·.1 == r) with
  | some (_, a) => pure a
  | none => throw s!"the default table does not bind {repr r}"

/-- A definition `d : True := True.intro`, a target unrelated to any axiom. -/
def trivialDef (env : Ixon.Env) (trueA introA : Address) : Ixon.Env × Address :=
  st env ⟨.defn ⟨.defn, .safe, {}, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[trueA, introA], #[], #[]⟩

/-- `c` with its axiom type moved into the sharing table: the same constant, another
record and address. -/
def reshare (c : Ixon.Constant) : Except String Ixon.Constant := do
  let .axio ax := c.info | throw "not an axiom record"
  pure { c with info := .axio { ax with typ := .share c.sharing.size.toUInt64 },
                sharing := c.sharing.push ax.typ, binders := #[] }

/-- A check claim on `target` with the axioms tree of `leaves`. -/
def withAxioms (label : String) (env : Ixon.Env) (target : Address) (leaves : Array Address)
    (accept : Bool) (rejectsWith : Option String) : Builder := fun _ => do
  let some tree := Ix.AssumptionTree.canonical leaves | throw "no tree"
  let ctx ← Ix.ClaimContext.ofEnv env
  Case.ofClaim label env (.check { ctx with axioms := some tree.root } target none)
    (({} : Std.HashMap _ _).insert tree.root tree) accept rejectsWith

/-- The user-axiom cases. -/
def axiomCases (lenv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv #[``True, ``True.intro, ``False, ``Bool.false, ``propext, ``sorryAx] lenv
  let table ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let propextA ← IO.ofExcept (boundAddr table .propext)
  let sorryA ← IO.ofExcept (boundAddr table .sorryAx)
  let trueA ← lookupAddr env ``True
  let introA ← lookupAddr env ``True.intro
  let falseA ← lookupAddr env ``False
  let bfA ← lookupAddr env ``Bool.false
  let (env, dA) := trivialDef env trueA introA
  -- a genuine user axiom `ax : Prop`
  let (env, axA) := st env ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero], #[]⟩
  -- restatements of propext and sorryAx
  let some propC := env.getConst? propextA | throw (IO.userError "propext's record is missing")
  let some sorryC := env.getConst? sorryA | throw (IO.userError "sorryAx's record is missing")
  let (env, prop2A) ← stAnnot env (← IO.ofExcept (reshare propC))
  let (env, sorry2A) ← stAnnot env (← IO.ofExcept (reshare sorryC))
  -- `bad : False := sorryAx False false`, under a table that leaves sorryAx unbound
  let (env, badA) := st env ⟨.defn ⟨.defn, .safe, {}, 0, .ref 0 #[],
    .app (.app (.ref 1 #[0]) (.ref 0 #[])) (.ref 2 #[])⟩, #[], #[falseA, sorryA, bfA], #[.zero], #[]⟩
  let partialT : Ix.Kernel.RoleTable := { table with bound := table.bound.filter (·.1 != .sorryAx) }
  let bytes := partialT.toBytes
  let partialEnv := { env with roleBinding := some ⟨Address.blake3 bytes, bytes⟩ }
  return #[
    withAxioms "control-user-axiom" env dA #[axA] true none,
    withAxioms "user-axiom-restates-propext" env dA #[prop2A] false
      (some "restates an axiom role's specification"),
    withAxioms "user-axiom-restates-sorryAx" env dA #[sorry2A] false
      (some "restates an axiom role's specification"),
    withAxioms "sorryAx-unbound-false-by-sorry" partialEnv badA #[sorryA] false
      (some "user axioms need propext, Classical.choice and sorryAx bound")]

/-- `Two.rec`'s record with its type's conclusion `motive t` replaced by
`let _ : motive t := Two.rec motive ma mb t; motive t` (the recursor's own record by
`recur 0`). -/
def wrapConclusion (uIdx : UInt64) : Nat → E → Except String E
  | 0, body => do
    unless body == .app (.var 3) (.var 0) do throw "Two.rec's conclusion is not `motive t`"
    let self : E := .app (.app (.app (.app (.recur 0 #[uIdx]) (.var 3)) (.var 2)) (.var 1)) (.var 0)
    pure (.leanLet false body self (.app (.var 4) (.var 1)))
  | n + 1, .all ty b => do pure (.all ty (← wrapConclusion uIdx n b))
  | _, _ => throw "Two.rec's type is not a four-binder telescope"

def selfRefRec (c : Ixon.Constant) : Except String Ixon.Constant := do
  let .recr r := c.info | throw "Two.rec is not a single recursor record"
  let uIdx ← match c.univs.findIdx? (· == .var 0) with
    | some i => pure i
    | none => throw "Two.rec's universe table has no parameter 0"
  pure { c with info := .recr { r with typ := ← wrapConclusion uIdx.toUInt64 4 r.typ } }

/-- The recursor-type case. -/
def recursorCases (fenv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv #[`BatchMR.Two, `BatchMR.Two.rec] fenv
  let recA ← lookupAddr env `BatchMR.Two.rec
  let some recC := env.getConst? recA | throw (IO.userError "Two.rec's record is missing")
  let (env, badA) := st env (← IO.ofExcept (selfRefRec recC))
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  return #[
    fun _ => Case.ofClaim "control-two-rec" env (.check ctx recA none) {} true,
    fun _ => Case.ofClaim "recursor-type-mentions-itself" env (.check ctx badA none) {} false]

/-- The auxiliary-motive case. -/
def auxCases (fenv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv #[`BatchMR.T1, `BatchMR.T1.rec, `BatchMR.T2, `BatchMR.T2.rec] fenv
  let t1A ← lookupAddr env `BatchMR.T1
  let n1A ← lookupAddr env `BatchMR.T1.node
  let t2A ← lookupAddr env `BatchMR.T2
  let n2A ← lookupAddr env `BatchMR.T2.node
  let r1A ← lookupAddr env `BatchMR.T1.rec
  let r2A ← lookupAddr env `BatchMR.T2.rec
  let some r1C := env.getConst? r1A | throw (IO.userError "T1.rec is missing")
  let some r2C := env.getConst? r2A | throw (IO.userError "T2.rec is missing")
  let .rPrj p1 := r1C.info | throw (IO.userError "T1.rec is not a recursor projection")
  let .rPrj p2 := r2C.info | throw (IO.userError "T2.rec is not a recursor projection")
  let some fam1 := env.getConst? p1.block | throw (IO.userError "T1's family is missing")
  let some fam2 := env.getConst? p2.block | throw (IO.userError "T2's family is missing")
  let .muts ms1 := fam1.info | throw (IO.userError "T1's family is not a mutual record")
  let .muts ms2 := fam2.info | throw (IO.userError "T2's family is not a mutual record")
  IO.println s!"[ixvm-batch-must-reject] T1's family has {ms1.size} recursors, T2's {ms2.size}"
  -- T1's family on T2: every reference to T1 or T1.node is to T2 or T2.node
  let remap (a : Address) : Address := if a == t1A then t2A else if a == n1A then n2A else a
  let (env', famA) := st env { fam1 with refs := fam1.refs.map remap }
  let mut env' := env'
  let mut prjs : Array Address := #[]
  for i in [0:ms1.size] do
    let (e, a) := st env' ⟨.rPrj ⟨i.toUInt64, famA⟩, #[], #[], #[], #[]⟩
    env' := e
    prjs := prjs.push a
  -- T2's own family is removed, so the crafted one is T2's only family
  let mut consts := env'.consts.erase p2.block
  for i in [0:ms2.size] do
    consts := consts.erase (Address.blake3 (Ixon.ser (⟨.rPrj ⟨i.toUInt64, p2.block⟩, #[], #[], #[], #[]⟩ : Ixon.Constant)))
  let crafted := ({ env' with consts } : Ixon.Env).registerNameAddr (Ix.Name.fromLeanName `BatchMR.T2.rec) (prjs.getD p1.idx.toNat default)
  let (crafted, rep) ← IO.ofExcept (IxVM.Model.generateReport (withoutModels crafted))
  for (b, r) in rep.blocks do
    match r with
    | .error e => IO.println s!"[ixvm-batch-must-reject] block {b} has no model: {e}"
    | .ok (n, outside) => IO.println s!"[ixvm-batch-must-reject] block {b}: {n} advice records, {outside.size} outside references"
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  let ctxC ← IO.ofExcept (Ix.ClaimContext.ofEnv crafted true)
  let craftedRec := prjs.getD p1.idx.toNat default
  -- claimed at a recursor, each family is refused at the recursor while the program refuses the
  -- recursors of such families; claimed at the type, the family check runs
  let atRecursor (label : String) (e : Ixon.Env) (c : Ix.ClaimContext) (a : Address)
      (accept : Bool) (why : Option String := none) : Builder := fun _ => do
    let case ← Case.ofClaim label e (.check c a none) {} accept why
    return case.throughModeledRecursor
  return #[
    atRecursor "control-T1-erased-option-occurrence" env ctx r1A true,
    atRecursor "control-T2" env ctx r2A true,
    atRecursor "extra-auxiliary-motive" crafted ctxC craftedRec false
      (some "auxiliary members are not the constructors' nested occurrences"),
    fun _ => Case.ofClaim "control-T1-erased-option-occurrence, at the type" env
      (.check ctx t1A none) {} true,
    fun _ => Case.ofClaim "control-T2, at the type" env (.check ctx t2A none) {} true,
    fun _ => Case.ofClaim "extra-auxiliary-motive, at the type" crafted
      (.check ctxC t2A none) {} false]

/-- Blocks the reader's modeller declines (a rule at a constructor outside the block; a block
constructor whose type ends in a family outside the block), with prover-chosen records:
* `X₁.rec : ∀ (motive : Sort u) (minor : motive) (major : Two), motive` with one rule at `Two.a`,
  `λ motive minor, minor` (its family's major is outside any modeled block, so the circuit takes
  the native route of `Two`, whose canonical recursor it is not);
* a two-type block whose first type's constructor is `C : Two`. -/
def knCases (fenv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv #[`BatchMR.Two, `BatchMR.Two.a, `BatchMR.Two.b] fenv
  let twoA ← lookupAddr env `BatchMR.Two
  -- X₁.rec, a single recursor record
  let recTy : E := .leanAll (.sort 0) (.leanAll (.var 0) (.leanAll (.ref 0 #[]) (.var 2)))
  let rule : Ixon.RecursorRule := { fields := 0, rhs := .leanLam (.sort 0) (.leanLam (.var 0) (.var 0)) }
  let r : Ixon.Recursor :=
    { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0,
      motives := 1, minors := 1, typ := recTy, rules := #[rule] }
  let (env1, recA) ← stAnnot env ⟨.recr r, #[], #[twoA], #[.var 0], #[]⟩
  -- the same, well shaped: `∀ (motive : Two → Sort u) (minor : motive Two.a) (t : Two), motive t`,
  -- one rule `λ motive minor, minor` (Two has two constructors)
  let twoAA ← lookupAddr env `BatchMR.Two.a
  let motiveDom : E := .leanAll (.ref 0 #[]) (.sort 0)
  let minorDom : E := .app (.var 0) (.ref 1 #[])
  let recTy3 : E := .leanAll motiveDom (.leanAll minorDom (.leanAll (.ref 0 #[]) (.app (.var 2) (.var 0))))
  let rule3 : Ixon.RecursorRule := { fields := 0, rhs := .leanLam motiveDom (.leanLam minorDom (.var 0)) }
  let r3 : Ixon.Recursor :=
    { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0,
      motives := 1, minors := 1, typ := recTy3, rules := #[rule3] }
  let (env3, rec3A) ← stAnnot env ⟨.recr r3, #[], #[twoA, twoAA], #[.var 0], #[]⟩
  -- the control: both rules, `Two.rec` up to binder data
  let twoAB ← lookupAddr env `BatchMR.Two.b
  let minorBDom : E := .app (.var 1) (.ref 2 #[])
  let recTyC : E := .leanAll motiveDom (.leanAll minorDom (.leanAll minorBDom
    (.leanAll (.ref 0 #[]) (.app (.var 3) (.var 0)))))
  let ruleC (i : UInt64) : Ixon.RecursorRule :=
    { fields := 0, rhs := .leanLam motiveDom (.leanLam minorDom (.leanLam minorBDom (.var i))) }
  let rC : Ixon.Recursor :=
    { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0,
      motives := 1, minors := 2, typ := recTyC, rules := #[ruleC 1, ruleC 0] }
  let (envC, recCA) ← stAnnot env ⟨.recr rC, #[], #[twoA, twoAA, twoAB], #[.var 0], #[]⟩
  -- the same with the first minor's domain written as a β-redex, in the type and in the rules'
  -- λ-prefix: convertible with the generated domain, not related to it by consumed wrappers
  let minorDomBeta : E := .app (.leanLam (.ref 0 #[]) (.app (.var 1) (.var 0))) (.ref 1 #[])
  let recTyB : E := .leanAll motiveDom (.leanAll minorDomBeta (.leanAll minorBDom
    (.leanAll (.ref 0 #[]) (.app (.var 3) (.var 0)))))
  let ruleB (i : UInt64) : Ixon.RecursorRule :=
    { fields := 0, rhs := .leanLam motiveDom (.leanLam minorDomBeta (.leanLam minorBDom (.var i))) }
  let rB : Ixon.Recursor := { rC with typ := recTyB, rules := #[ruleB 1, ruleB 0] }
  let (envB, recBA) ← stAnnot env ⟨.recr rB, #[], #[twoA, twoAA, twoAB], #[.var 0], #[]⟩
  let ctxB ← IO.ofExcept (Ix.ClaimContext.ofEnv envB true)
  -- the block X₁ X₂ : Type, X₁'s constructor C : Two
  let blk : Ixon.Constant := ⟨.muts #[
    .indc ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .inherited, .ref 0 #[]⟩]⟩,
    .indc ⟨false, 0, 0, 0, .sort 0, #[]⟩], #[], #[twoA], #[.succ .zero], #[]⟩
  let (env2, bA) ← stAnnot env blk
  let (env2, x1A) := st env2 ⟨.iPrj ⟨0, bA⟩, #[], #[], #[], #[]⟩
  let (env2, _) := st env2 ⟨.iPrj ⟨1, bA⟩, #[], #[], #[], #[]⟩
  let (env2, _) := st env2 ⟨.cPrj ⟨0, 0, bA⟩, #[], #[], #[], #[]⟩
  let ctx1 ← IO.ofExcept (Ix.ClaimContext.ofEnv env1 true)
  let ctx2 ← IO.ofExcept (Ix.ClaimContext.ofEnv env2 true)
  let ctx3 ← IO.ofExcept (Ix.ClaimContext.ofEnv env3 true)
  let ctxC ← IO.ofExcept (Ix.ClaimContext.ofEnv envC true)
  return #[
    fun _ => Case.ofClaim "control-two-rule-recursor" envC (.check ctxC recCA none) {} true,
    fun _ => Case.ofClaim "convertible-but-unrelated-recursor" envB (.check ctxB recBA none) {} false
      (some "not the generated one up to consumed wrappers"),
    fun _ => Case.ofClaim "rule-at-a-constructor-outside-the-block" env1 (.check ctx1 recA none) {} false,
    fun _ => Case.ofClaim "one-rule-recursor-of-a-two-constructor-family" env3 (.check ctx3 rec3A none) {} false,
    fun _ => Case.ofClaim "block-constructor-ending-outside-the-block" env2 (.check ctx2 x1A none) {} false
      (some "ctor return head belongs to a different block")]

/-- Constructors of an indexed family `W (α : Type) : Two → Type` whose declared residual is
headed by a `let`, on the native route (a one-type block) and the modeled route (a two-type
block), with their plain controls:
* `mk : ∀ α, (let x := W α; x) Two.a` (the `let` hides the parameter);
* `mk : ∀ α, (let f := λ a i, W a Two.a; f) α Two.b` (the visible index is not the
  constructor's: its type is `W α Two.a`). -/
def letResidualCases (fenv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv #[`BatchMR.Two, `BatchMR.Two.a, `BatchMR.Two.b] fenv
  let twoA ← lookupAddr env `BatchMR.Two
  let twoAA ← lookupAddr env `BatchMR.Two.a
  let twoAB ← lookupAddr env `BatchMR.Two.b
  let wTy : E := .leanAll (.sort 0) (.leanAll (.ref 0 #[]) (.sort 0))
  let plain (k : UInt64) : E := .leanAll (.sort 0) (.app (.app (.recur k #[]) (.var 0)) (.ref 1 #[]))
  let hidden (k : UInt64) : E := .leanAll (.sort 0)
    (.app (.leanLet false (.leanAll (.ref 0 #[]) (.sort 0)) (.app (.recur k #[]) (.var 0)) (.var 0)) (.ref 1 #[]))
  let reorder (k : UInt64) : E := .leanAll (.sort 0)
    (.app (.app (.leanLet false wTy
      (.leanLam (.sort 0) (.leanLam (.ref 0 #[]) (.app (.app (.recur k #[]) (.var 1)) (.ref 1 #[]))))
      (.var 0)) (.var 0)) (.ref 2 #[]))
  let ind (cty : E) : Ixon.MutConst := .indc ⟨false, 0, 1, 1, wTy, #[⟨false, 0, 0, 1, 0, .inherited, cty⟩]⟩
  let store (env : Ixon.Env) (ms : Array Ixon.MutConst) : IO (Ixon.Env × Address) := do
    let (env, b) ← stAnnot env ⟨.muts ms, #[], #[twoA, twoAA, twoAB], #[.succ .zero], #[]⟩
    let mut env := env
    let mut first : Address := default
    for i in [0:ms.size] do
      let (e, a) := st env ⟨.iPrj ⟨i.toUInt64, b⟩, #[], #[], #[], #[]⟩
      let (e, _) := st e ⟨.cPrj ⟨i.toUInt64, 0, b⟩, #[], #[], #[], #[]⟩
      env := e
      if i == 0 then first := a
    return (env, first)
  let (env, nPlain) ← store env #[ind (plain 0)]
  let (env, nHidden) ← store env #[ind (hidden 0)]
  let (env, nReorder) ← store env #[ind (reorder 0)]
  let (env, mPlain) ← store env #[ind (plain 0), ind (plain 1)]
  let (env, mHidden) ← store env #[ind (hidden 0), ind (plain 1)]
  let (env, mReorder) ← store env #[ind (reorder 0), ind (plain 1)]
  let (env, rep) ← IO.ofExcept (IxVM.Model.generateReport (withoutModels env))
  for (b, r) in rep.blocks do
    match r with
    | .error e => IO.println s!"[ixvm-batch-must-reject] let residual: block {b} has no model: {e}"
    | .ok (n, _) => IO.println s!"[ixvm-batch-must-reject] let residual: block {b}: {n} advice records"
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  let claim (label : String) (a : Address) (accept : Bool) : Builder :=
    fun _ => Case.ofClaim label env (.check ctx a none) {} accept
  return #[
    claim "let-residual-control-native-plain-residual" nPlain true,
    claim "let-residual-native-residual-hides-the-parameter" nHidden false,
    claim "let-residual-native-residual-shows-another-index" nReorder false,
    claim "let-residual-control-modeled-plain-residual" mPlain true,
    claim "let-residual-modeled-residual-hides-the-parameter" mHidden false,
    claim "let-residual-modeled-residual-shows-another-index" mReorder false]

/-- `PUnit.rec` on a variable at a never-zero level (`PUnit.{1}`, `PUnit.{u+1}`): the circuit's
η route of ι fabricates `PUnit.unit` and fires, as the reference kernel's 0-field rescue does. -/
def punitCases (fenv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv #[`BatchMR.punitRecStuck, `BatchMR.punitRecStuckU] fenv
  let a1 ← lookupAddr env `BatchMR.punitRecStuck
  let a2 ← lookupAddr env `BatchMR.punitRecStuckU
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  return #[
    fun _ => Case.ofClaim "punit-rec-stuck-at-level-one" env (.check ctx a1 none) {} true,
    fun _ => Case.ofClaim "punit-rec-stuck-at-a-successor-level" env (.check ctx a2 none) {} true]

/-- The second batch's cases: a definition whose level-parameter count is 2^32; the witness of
an existential projected out of it (field 0 of `Exists`, a proposition, whose stored guard is
the witness's sort); and, as control, the first component of a conjunction. -/
def secondBatchCases (fenv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv #[``True, ``True.intro, `BatchMR.exWitness, `BatchMR.andFst, `BatchMR.FI,
    `BatchMR.FI.rec, `BatchMR.F0, `BatchMR.F0.rec] fenv
  let fiRecA ← lookupAddr env `BatchMR.FI.rec
  let f0A ← lookupAddr env `BatchMR.F0
  let trueA ← lookupAddr env ``True
  let introA ← lookupAddr env ``True.intro
  let (env, wideA) := st env ⟨.defn ⟨.defn, .safe, {}, 4294967296, .ref 0 #[], .ref 1 #[]⟩, #[],
    #[trueA, introA], #[], #[]⟩
  let exA ← lookupAddr env `BatchMR.exWitness
  let existsA ← lookupAddr env ``Exists
  let some exC := env.getConst? exA | throw (IO.userError "exWitness's record is missing")
  let .defn d := exC.info | throw (IO.userError "exWitness is not a definition record")
  let some eIdx := exC.refs.findIdx? (· == existsA)
    | throw (IO.userError "exWitness's record does not reference Exists")
  let .lam ty _ := d.value | throw (IO.userError "exWitness's value is not a λ")
  let (env, projA) := st env
    { exC with info := .defn { d with value := .lam ty (.prj eIdx.toUInt64 0 (.var 0)) } }
  let andA ← lookupAddr env `BatchMR.andFst
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  return #[
    fun _ => Case.ofClaim "level-count-at-2^32" env (.check ctx wideA none) {} false
      (some "a level-parameter count is 2^32 or more"),
    fun _ => Case.ofClaim "projection-of-an-existential-witness" env (.check ctx projA none) {} false,
    fun _ => Case.ofClaim "control-and-first-component" env (.check ctx andA none) {} true,
    fun _ => Case.ofClaim "control-indexed-family-declared-at-a-definition" env
      (.check ctx fiRecA none) {} true,
    fun _ => Case.ofClaim "index-free-family-declared-at-a-definition" env
      (.check ctx f0A none) {} false (some "has no index")]

def run (lenv : Lean.Environment) : IO UInt32 := do
  -- the fixtures of `BatchMustRejectDefs` are in the test binary's environment
  let fenv := lenv
  let cases := (← axiomCases lenv) ++ (← recursorCases fenv) ++ (← auxCases fenv)
  runCases "ixvm-batch-must-reject"
    (cases ++ (← knCases fenv) ++ (← letResidualCases fenv) ++ (← punitCases fenv) ++
      (← secondBatchCases fenv))

end Tests.Ix.IxVM.BatchMustReject
