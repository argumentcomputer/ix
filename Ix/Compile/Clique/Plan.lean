/-
  Ix.Compile.Clique.Plan: the plan of a changed definition clique (what the
  Pass 3 clique hook, `Ix.Compile.Pass.Cliques`, does with it), as data.

  The types live here, below `Ix.CompileM`, so that the compile environment
  can carry the per-clique plan table (`CompileEnv.p3CliquePlans`): a
  clique's plan is computed by the first block of its unit that needs it and
  read back by the later ones (design document §5.4, "the plan is computed
  once"). `planClique` itself stays in `Ix.Compile.Pass.Cliques`.
-/
module
public import Ix.Compile.Clique.Basic
public section

namespace Ix.Compile.Clique

open Ix (Name)

inductive Encoding where
  | wellFounded
  | structural
  | partialFixpoint
  deriving BEq, Repr, Inhabited

def Encoding.tag : Encoding → String
  | .wellFounded => "well-founded"
  | .structural => "structural"
  | .partialFixpoint => "partial_fixpoint"

/-- Where a clique's canonical order came from. -/
inductive OrderSource where
  /-- Pass 1's classes over (type, normalised specification) -/
  | specification
  /-- the specification could not be recovered; the statements decide (Q6,
  first source) -/
  | statements (why : String)
  deriving Inhabited

def OrderSource.tag : OrderSource → String
  | .specification => "specification"
  | .statements why => s!"statements ({why})"

/-- Exact equality of two declarations: name, universe parameters, kind,
and type and value by content hash (`Ix.Expr`'s `BEq`, which covers binder
names and `mdata`, as the compiled bytes and metadata do). -/
def Decl.same (a b : Decl) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.isThm == b.isThm &&
    a.type == b.type && a.value == b.value

end Ix.Compile.Clique

namespace Ix.Compile.Pass

open Ix (Name)
open Ix.Compile.Clique (Decl Encoding Cause OrderSource)

/-- A changed clique's transport, ready for the members' blocks. -/
structure CliquePlan where
  /-- Lean's order (`all`) -/
  all : Array Name
  encoding : Encoding
  sigma : Array Nat
  classes : Array (Array Name)
  source : OrderSource
  /-- the transported members, by Lean name -/
  members : Std.HashMap Name Decl
  /-- the canonical constants, each with the Lean constant it transports -/
  canon : Array (Decl × Name)
  /-- the canonical functional(s): the side-car record goes on these -/
  functionals : Array Name
  causes : Array (Name × Cause × String)
  /-- O17: a member ↦ the representative of its class, whose constant it is -/
  aliases : Array (Name × Name) := #[]
  deriving Inhabited

/-- What the hook does with a clique. -/
inductive CliqueOutcome where
  /-- not an encoded clique (compiled as today) -/
  | notEncoded (why : String)
  /-- the canonical order is Lean's (compiled as today) -/
  | unchanged (enc : Encoding) (source : OrderSource)
  /-- the order is undetermined (`NOSPEC`) or the transport kept Lean's form
  (`SHAPE`): compiled as today -/
  | baseline (enc : Encoding) (cause : String) (why : String)
  | transported (plan : CliquePlan)
  deriving Inhabited

/-- The side-car record of a plan. -/
def CliquePlan.record (p : CliquePlan) : String :=
  let causes := p.causes.map fun (n, c, why) => s!"{n.pretty} {c.tag}: {why}"
  s!"{p.encoding.tag}; lean order {p.all.map (·.pretty)}; sigma {p.sigma}; \
    order by {p.source.tag}; classes {p.classes.map (·.map (·.pretty))}; \
    aliases (O17) {p.aliases.map fun (m, r) => s!"{m.pretty} = {r.pretty}"}; causes {causes}"

/-- Exact equality of two plans (the plan-cache check, `IX_PASS3_CHECK_PLANS`):
every field, declarations by `Decl.same`, the member map by key. -/
def CliquePlan.same (a b : CliquePlan) : Bool :=
  a.all == b.all && a.encoding == b.encoding && a.sigma == b.sigma && a.classes == b.classes &&
    a.source.tag == b.source.tag && a.functionals == b.functionals && a.aliases == b.aliases &&
    a.causes.size == b.causes.size &&
    (a.causes.zip b.causes).all (fun ((n, c, w), (n', c', w')) => n == n' && c == c' && w == w') &&
    a.canon.size == b.canon.size &&
    (a.canon.zip b.canon).all (fun ((d, s), (d', s')) => d.same d' && s == s') &&
    a.members.size == b.members.size &&
    a.members.toList.all fun (n, d) => match b.members.get? n with
      | some d' => d.same d'
      | none => false

/-- Exact equality of two outcomes (the plan-cache check). -/
def CliqueOutcome.same : CliqueOutcome → CliqueOutcome → Bool
  | .notEncoded w, .notEncoded w' => w == w'
  | .unchanged e s, .unchanged e' s' => e == e' && s.tag == s'.tag
  | .baseline e c w, .baseline e' c' w' => e == e' && c == c' && w == w'
  | .transported p, .transported p' => p.same p'
  | _, _ => false

/-- A short description of an outcome, for the check's error. -/
def CliqueOutcome.tag : CliqueOutcome → String
  | .notEncoded w => s!"not encoded ({w})"
  | .unchanged e s => s!"unchanged ({e.tag}, {s.tag})"
  | .baseline e c w => s!"baseline {c} ({e.tag}: {w})"
  | .transported p => s!"transported ({p.record})"

end Ix.Compile.Pass

end
