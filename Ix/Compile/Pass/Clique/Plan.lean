/-
  Ix.Compile.Pass.Clique.Plan: the plan of a changed definition clique, as
  data, and the side-car record it puts in the canonical functional.

  The types are separate from the planner so that the compile environment can
  carry the per-clique plan table: a clique's plan is computed once, by the
  first block of its unit that needs it, and read back by the later ones.

  The side-car record (`CliquePlan.record`) holds typed data only: names,
  numbers and enumeration tags. The free-form reasons (why the specification
  could not be recovered, why a constant kept Lean's form) stay in the plan
  for diagnostics and are never part of the record.
-/
module
public import Ix.Compile.Pass.Clique.Basic
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name)

/-- The encoding of a definition clique. -/
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
  /-- the specification could not be recovered (`why`, for diagnostics); the
  statements decide -/
  | statements (why : String)
  deriving BEq, Repr, Inhabited

/-- The source's tag, as the side-car record carries it: `specification` or
`statements` (never the recovery error). -/
def OrderSource.tag : OrderSource → String
  | .specification => "specification"
  | .statements _ => "statements"

/-- The source for display: the tag, with the recovery error of
`statements`. -/
def OrderSource.describe : OrderSource → String
  | .specification => "specification"
  | .statements why => s!"statements ({why})"

/-- Exact equality of two declarations: name, universe parameters, kind,
and type and value by content hash (`Ix.Expr`'s `BEq`, which covers binder
names and `mdata`, as the compiled bytes and metadata do). -/
def Decl.same (a b : Decl) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.isThm == b.isThm &&
    a.type == b.type && a.value == b.value

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
  /-- the transport's causes: the constant, the cause, and the reason (for
  diagnostics; the record carries the first two only) -/
  causes : Array (Name × Cause × String)
  /-- a member ↦ the representative of its class, whose constant it is (the
  aliases of equal members) -/
  aliases : Array (Name × Name) := #[]
  deriving Inhabited

/-- What the hook does with a clique. -/
inductive CliqueOutcome where
  /-- not an encoded clique (compiled as today) -/
  | notEncoded (why : String)
  /-- the canonical order is Lean's (compiled as today) -/
  | unchanged (enc : Encoding) (source : OrderSource)
  /-- the order is undetermined (`noSpec`) or the transport kept Lean's form
  (`shape`): compiled as today; `why` is for diagnostics -/
  | baseline (enc : Encoding) (cause : Cause) (why : String)
  | transported (plan : CliquePlan)
  deriving Inhabited

/-- The side-car record of a plan (`_ix.clique`), typed data only:

```
record  ::= enc "; lean order " names "; sigma " nats "; order by " source
            "; classes " classes "; aliases " aliases "; causes " causes
enc     ::= "well-founded" | "structural" | "partial_fixpoint"   -- Encoding.tag
source  ::= "specification" | "statements"                       -- OrderSource.tag
cause   ::= "SHAPE" | "GUESSLEX" | "NOSPEC"                      -- Cause.tag
names   ::= array(name)          -- Lean's order, `all`
nats    ::= array(nat)           -- σ, decimal
classes ::= array(names)
aliases ::= array(name " = " name)       -- member = representative
causes  ::= array(name " " cause)        -- constant, cause
array(x) ::= "#[" (x (", " x)*)? "]"
```

`name` is `Ix.Name.pretty` (components joined by `.`, no escaping). Example:
`well-founded; lean order #[f, g]; sigma #[1, 0]; order by specification;
classes #[#[g], #[f]]; aliases #[]; causes #[g._ix._mutual._proof_1 SHAPE]`
(on one line). -/
def CliquePlan.record (p : CliquePlan) : String :=
  let causes := p.causes.map fun (n, c, _) => s!"{n.pretty} {c.tag}"
  s!"{p.encoding.tag}; lean order {p.all.map (·.pretty)}; sigma {p.sigma}; \
    order by {p.source.tag}; classes {p.classes.map (·.map (·.pretty))}; \
    aliases {p.aliases.map fun (m, r) => s!"{m.pretty} = {r.pretty}"}; causes {causes}"

/-- Exact equality of two plans (the plan-cache check): every field,
declarations by `Decl.same`, the member map by key, the reasons included. -/
def CliquePlan.same (a b : CliquePlan) : Bool :=
  a.all == b.all && a.encoding == b.encoding && a.sigma == b.sigma && a.classes == b.classes &&
    a.source == b.source && a.functionals == b.functionals && a.aliases == b.aliases &&
    a.causes.size == b.causes.size &&
    (a.causes.zip b.causes).all (fun ((n, c, w), (n', c', w')) => n == n' && c == c' && w == w') &&
    a.canon.size == b.canon.size &&
    (a.canon.zip b.canon).all (fun ((d, s), (d', s')) => d.same d' && s == s') &&
    a.members.size == b.members.size &&
    a.members.toList.all fun (n, d) => match b.members.get? n with
      | some d' => d.same d'
      | none => false

/-- Exact equality of two outcomes (the plan-cache check), the reasons
included. -/
def CliqueOutcome.same : CliqueOutcome → CliqueOutcome → Bool
  | .notEncoded w, .notEncoded w' => w == w'
  | .unchanged e s, .unchanged e' s' => e == e' && s == s'
  | .baseline e c w, .baseline e' c' w' => e == e' && c == c' && w == w'
  | .transported p, .transported p' => p.same p'
  | _, _ => false

/-- A short description of an outcome, for the check's error (with the
reasons). -/
def CliqueOutcome.tag : CliqueOutcome → String
  | .notEncoded w => s!"not encoded ({w})"
  | .unchanged e s => s!"unchanged ({e.tag}, {s.describe})"
  | .baseline e c w => s!"baseline {c.tag} ({e.tag}: {w})"
  | .transported p => s!"transported ({p.record})"

end Ix.Compile.Pass.Clique

end
