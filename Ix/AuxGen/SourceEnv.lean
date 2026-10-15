/-
  Ix.AuxGen.SourceEnv: the checked half of the Source service environment
  (AuxGen on IxC, M1; AUXGEN-IXC §3.2–§3.3).

  What AuxGen's kernel questions run against in Source mode, and what they
  need besides the environment's construction: the verified fold's state
  (`Fold`), its evidence, and the class map σ of the canonical flat blocks
  and generated constants installed so far. A `module`, over the shared term
  half of the Source ingress (`Ix.LeanIngress.Expr`), so the compiler's
  modules (the `AuxKernel` interface's IxC arm, AuxGen M2) can hold one.
  Building it from a Lean environment (lowering declaration groups through
  the Ixon reader's back half) is `Ix.AuxGen.SourceService`'s, which is not a
  module yet because the reader is not.

  * **The fold.** `Fold.step` is one declaration through both phases of the
    verified fold (`Cached.annotDeclStep`, then `Cached.checkPendingList` on
    the records the step left pending, against the environment after it), as
    the per-record step drivers run it; `Fold.steps` a group's declarations,
    the first failure the group's. A failure leaves the caller's fold as it
    was: folds are values.
  * **Terms in** (`ingress`, `key`): a Lean term renamed by σ
    (`Flat.renameExpr`), then the ingress's term conversion (`ingressExprs`)
    under the constant's numbering. σ fits `Key.map` (`Flat.ClassMap.misfit` is
    refused at every install), so this equals the ingress followed by
    `Key.map` of σ on Source keys.
  * **Installs.** `install` folds a block's lowered declarations and joins
    its σ, both or neither; `admitDefinition` checks a generated definition
    under its fresh name through σ and then maps its name there (the
    `AuxKernel` contract's clause 9: "IxC will use a fresh key and σ").

  Nothing here is trusted: every declaration goes through the verified
  fold, and what it cannot install is refused, with the fold's reason.
-/
module
public import Ix.LeanIngress.Expr
public import IxC.Kernel.Cached.Installed
public import Ix.AuxGen.FlatBlock
public section

namespace Ix.AuxGen.Source

open Ix.LeanIngress (ingressKey ingressExprs Numbering ExprError)
open Ix.AuxGen.Flat (ClassMap FlatError)

abbrev Decl := Ix.Kernel.Declaration .source

/-! ## The fold -/

/-- The fold's state: the indexed environment, the memo state, the fold
position. -/
structure Fold where
  fe : Ix.Kernel.FEnv .source := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  cs : Ix.Kernel.Cached.CState .source := {}
  pos : Nat := 0

instance : Inhabited Fold := ⟨{}⟩

/-- One declaration through both phases of the verified fold. -/
def Fold.step (ev : Ix.Kernel.Evidences .source) (f : Fold) (d : Decl) :
    Except (Ix.Kernel.CheckError .source) Fold :=
  match Ix.Kernel.Cached.annotDeclStep .verified ev (f.pos, f.fe, #[]) d f.cs with
  | .error (e, _) => .error e
  | .ok ((pos, fe, pend), cs) =>
    match Ix.Kernel.Cached.checkPendingList .verified fe pend.toList with
    | .ok () => .ok { fe, cs, pos }
    | .error (e, _) => .error e

/-- A group's declarations in order; the first failure is the group's. -/
def Fold.steps (ev : Ix.Kernel.Evidences .source) (f : Fold) (ds : Array Decl) :
    Except (Ix.Kernel.CheckError .source) Fold :=
  ds.foldlM (·.step ev) f

/-- A failure as text: the verdict and the message, keys spelled as their
Lean names. -/
def renderCheck (e : Ix.Kernel.CheckError .source) : String := e.render toString

/-- Whether Source mode's role binding fixes a Lean name: its key is a role
key. σ never moves such a name (`Key.map` fixes `.role` keys). -/
def roleBound (n : Name) : Bool := ingressKey n matches .role _

/-! ## The checked environment -/

/-- **The checked half of the service**: the fold, its evidence, and the
class map σ of everything installed under fresh names. -/
structure SourceEnv where
  fold : Fold := {}
  ev : Ix.Kernel.Evidences .source := []
  sigma : ClassMap := {}

instance : Inhabited SourceEnv := ⟨{}⟩

namespace SourceEnv

/-- **A Lean term as a Source term, through σ**: constants renamed by σ, then
the Source ingress's conversion under the numbering of `lps` (`large` for a
large eliminator's own terms). -/
def ingress (s : SourceEnv) (lps : Array Name) (es : List Expr) (large : Bool := false) :
    Except ExprError (List (Ix.Kernel.Expr .source)) :=
  let renamed := (es.mapM (Flat.renameExpr s.sigma)).run' {}
  ingressExprs (Numbering.mk lps large).pos renamed

/-- A Lean name's Source key, through σ. -/
def key (s : SourceEnv) (n : Name) : Ix.Kernel.Key .source := ingressKey (s.sigma.apply n)

/-- **Install a block** (a canonical flat block's lowered declarations) with
its σ: the declarations folded and σ joined, or neither, with the reason. A
σ that moves or produces a role-bound name is refused before any fold. -/
def install (s : SourceEnv) (ds : Array Decl) (σ : ClassMap) : Except String SourceEnv := do
  if let some n := σ.misfit roleBound then throw (FlatError.roleBound n).render
  let f ← (s.fold.steps s.ev ds).mapError renderCheck
  let σ' ← (s.sigma.union σ).mapError (·.render)
  pure { s with fold := f, sigma := σ' }

/-- **Admit a generated definition** (or theorem, `thm`) named `name`, with
level parameters `lps`, type and value: checked under its fresh name
(`Flat.fresh name`), its terms read through σ; on acceptance σ maps `name` to
the fresh name, so later queries and installs see the generated declaration.
The constants it references must be installed already. -/
def admitDefinition (s : SourceEnv) (name : Name) (lps : Array Name) (type value : Expr)
    (thm : Bool) (hint : Ix.Kernel.ReducibilityHint := .abbrev) : Except String SourceEnv := do
  if roleBound name then throw (FlatError.roleBound name).render
  let fresh := Flat.fresh name
  match s.ingress lps [type, value] with
  | .error e => throw s!"ingress: {e}"
  | .ok [t, v] =>
    let cv : Ix.Kernel.ConstantVal .source := ⟨ingressKey fresh, (Numbering.mk lps false).params, t⟩
    let d : Decl := if thm then .thmDecl cv v else .defnDecl cv v hint
    let f ← (s.fold.step s.ev d).mapError renderCheck
    let σ ← (s.sigma.insert name fresh).mapError (·.render)
    pure { s with fold := f, sigma := σ }
  | .ok _ => throw "ingress: arity"

end SourceEnv

end Ix.AuxGen.Source

end
