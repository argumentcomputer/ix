module

public import Ix.IxVM.ClaimHarness
public import Tests.Ix.IxVM.Harness

/-! # User axioms in a typing claim's context

A typing claim (`check`, `checkEnv`, `eval`) may name an axioms tree beside its
role binding: the axioms beyond Lean's three standard ones that the claim holds
under. IxVM refuses a leaf that is not a stored safe axiom record, or that the
role table binds (`KernelRoles::validate_user_axioms`). It also type-checks every
leaf with its closure, whether or not the claim's subjects use it, under the
claim's assumptions (`KernelClaim::check_axiom_leaves`). So every leaf is
installed as a user axiom.

The cases pair a well-typed axiom, `axiom good : (fun (p : Type) => p) Prop`,
with an ill-typed one, `axiom bad : (fun (p : Prop) => p) Prop`, whose argument
`Prop : Type` is not a `Prop`. No subject uses either. The claims cover `check`,
`checkEnv` and `eval`, with and without assumptions. Beside them:

- an axiom the subject uses is accepted;
- an ill-typed axiom that is itself assumed is not checked. The claim is then
  conditional on it, as on any assumption. A shard's assumptions can hold a
  user axiom that another shard owns.
-/

public section

namespace Tests.Ix.IxVM.UserAxioms

open IxVM.ClaimHarness

/-- `∀ (α : Prop), α → α`, its identity, and a redex for it. -/
private def idType : Ixon.Expr := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
private def idValue : Ixon.Expr := .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))
private def beta : Ixon.Expr := .app (.leanLam idType (.var 0)) idValue

private def definition (ty value : Ixon.Expr) (refs : Array Address := #[])
    (univs : Array Ixon.Univ := #[.zero]) : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 0, ty, value⟩, #[], refs, univs⟩

/-- A safe axiom of type `ty`. -/
private def axiomOf (ty : Ixon.Expr) (univs : Array Ixon.Univ) : Ixon.Constant :=
  ⟨.axio ⟨false, 0, ty⟩, #[], #[], univs⟩

/-- `axiom good : (fun (p : Type) => p) Prop`. -/
private def good : Ixon.Constant :=
  axiomOf (.app (.leanLam (.sort 1) (.var 0)) (.sort 0)) #[.zero, .succ .zero]

/-- `axiom bad : (fun (p : Prop) => p) Prop`: ill-typed. -/
private def bad : Ixon.Constant :=
  axiomOf (.app (.leanLam (.sort 0) (.var 0)) (.sort 0)) #[.zero]

private def store (env : Ixon.Env) (c : Ixon.Constant) (hint : Bool := true) :
    Ixon.Env × Address :=
  let addr := Address.blake3 (Ixon.ser c)
  let env := env.storeConst addr c
  if hint then ({ env with anonHints := env.anonHints.insert addr (.regular 0) }, addr)
  else (env, addr)

private def tree (leaves : Array Address) : Except String Ix.AssumptionTree :=
  match Ix.AssumptionTree.canonical leaves with
  | some t => pure t
  | none => throw "no tree for the leaves"

/-- The message IxVM refuses `bad` with. -/
def badMessage : String := "inferred type is not def-eq to the expected type"

/-- The cases. -/
def cases : Except String (Array Builder) := do
  let base ← Ix.ClaimContext.ofDefaultTable
  let (env, dep) := store {} (definition idType beta)
  let (env, target) := store env (definition idType (.ref 0 #[]) #[dep])
  let (env, output) := store env (definition idType idValue)
  let depTree ← tree #[dep]
  let targetTree ← tree #[target]
  let mut out : Array Builder := #[]
  for (name, ax, accept) in [("good", good, true), ("bad", bad, false)] do
    let (env, a) := store env ax (hint := false)
    let axioms ← tree #[a]
    let ctx := { base with axioms := some axioms.root }
    let trees : Std.HashMap Address Ix.AssumptionTree :=
      (({} : Std.HashMap _ _).insert axioms.root axioms).insert depTree.root depTree
        |>.insert targetTree.root targetTree
    let rejectsWith := if accept then none else some badMessage
    let verdict := if accept then "accepts" else "rejects"
    for (label, claim) in [
        ("check", Ix.Claim.check ctx target none),
        ("check with assumptions", .check ctx target (some depTree.root)),
        ("check-env", .checkEnv ctx targetTree.root none),
        ("check-env with assumptions", .checkEnv ctx targetTree.root (some depTree.root)),
        ("eval", .eval ctx target output none),
        ("eval with assumptions", .eval ctx target output (some depTree.root))] do
      out := out.push fun _ => Tests.Ix.IxVM.Case.ofClaim
        s!"user axioms: {label} {verdict} an unused {name} axiom" env claim trees accept rejectsWith
  -- A used axiom: `def useGood : Prop := good`.
  let (env, a) := store env good (hint := false)
  let axioms ← tree #[a]
  let (env, user) := store env (definition (.sort 0) (.ref 0 #[]) #[a])
  let trees : Std.HashMap Address Ix.AssumptionTree := ({} : Std.HashMap _ _).insert axioms.root axioms
  let ctx := { base with axioms := some axioms.root }
  out := out.push fun _ => Tests.Ix.IxVM.Case.ofClaim
    "user axioms: check accepts a used good axiom" env (.check ctx user none) trees
  -- An assumed ill-typed axiom is not checked: the claim is conditional on it.
  let (env, b) := store env bad (hint := false)
  let axioms ← tree #[b]
  let assumed ← tree #[dep, b]
  let trees : Std.HashMap Address Ix.AssumptionTree :=
    (({} : Std.HashMap _ _).insert axioms.root axioms).insert assumed.root assumed
  let ctx := { base with axioms := some axioms.root }
  out := out.push fun _ => Tests.Ix.IxVM.Case.ofClaim
    "user axioms: check accepts an assumed bad axiom" env (.check ctx target (some assumed.root)) trees
  return out

def run : IO UInt32 := do
  Tests.Ix.IxVM.runCases "ixvm-user-axioms" (← IO.ofExcept cases)

end Tests.Ix.IxVM.UserAxioms

end
