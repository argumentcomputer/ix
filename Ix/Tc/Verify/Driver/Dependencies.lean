import Ix.Tc.Verify.Driver.Model

/-!
# Semantic dependencies of Ixon constants

`Ixon.Constant.refs` is an intern table, not itself a dependency list.  Nat
and String nodes index blobs through the same table, and malformed/unused
table entries must not become declaration assumptions.  E1 therefore follows
the expression constructors which ingress turns into kernel constants:

* `.ref i` contributes `refs[i]`;
* `.prj i ...` contributes its type declaration `refs[i]`;
* structural children and reachable `.share` expansions are traversed;
* `.recur` remains internal to the current collapsed block; and
* `.nat`/`.str` are data dependencies, not Theory declaration dependencies.
-/

namespace Ix.Tc

namespace IxonExpr

/-- A finite derivation that expression ingress can expose `target` as a
kernel declaration reference.  Sharing is followed through its exact table
lookup, so an unused sharing entry contributes nothing. -/
inductive DeclReference (sharing : Array Ixon.Expr)
    (refs : Array Address) : Ixon.Expr → Address → Prop
  | ref {index : UInt64} {univs : Array UInt64} {target : Address} :
      refs[index.toNat]? = some target →
      DeclReference sharing refs (.ref index univs) target
  | prjType {index field : UInt64} {value : Ixon.Expr} {target : Address} :
      refs[index.toNat]? = some target →
      DeclReference sharing refs (.prj index field value) target
  | prjValue {index field : UInt64} {value : Ixon.Expr} {target : Address} :
      DeclReference sharing refs value target →
      DeclReference sharing refs (.prj index field value) target
  | appFn {fn arg : Ixon.Expr} {target : Address} :
      DeclReference sharing refs fn target →
      DeclReference sharing refs (.app fn arg) target
  | appArg {fn arg : Ixon.Expr} {target : Address} :
      DeclReference sharing refs arg target →
      DeclReference sharing refs (.app fn arg) target
  | lamType {uses : Ixon.Uses} {type body : Ixon.Expr} {target : Address} :
      DeclReference sharing refs type target →
      DeclReference sharing refs (.lam uses type body) target
  | lamBody {uses : Ixon.Uses} {type body : Ixon.Expr} {target : Address} :
      DeclReference sharing refs body target →
      DeclReference sharing refs (.lam uses type body) target
  | allType {uses : Ixon.Uses} {owned : Ixon.Owned}
      {type body : Ixon.Expr} {target : Address} :
      DeclReference sharing refs type target →
      DeclReference sharing refs (.all uses owned type body) target
  | allBody {uses : Ixon.Uses} {owned : Ixon.Owned}
      {type body : Ixon.Expr} {target : Address} :
      DeclReference sharing refs body target →
      DeclReference sharing refs (.all uses owned type body) target
  | letType {nondep : Bool} {type value body : Ixon.Expr}
      {target : Address} :
      DeclReference sharing refs type target →
      DeclReference sharing refs (.letE nondep type value body) target
  | letValue {nondep : Bool} {type value body : Ixon.Expr}
      {target : Address} :
      DeclReference sharing refs value target →
      DeclReference sharing refs (.letE nondep type value body) target
  | letBody {nondep : Bool} {type value body : Ixon.Expr}
      {target : Address} :
      DeclReference sharing refs body target →
      DeclReference sharing refs (.letE nondep type value body) target
  | share {index : UInt64} {expansion : Ixon.Expr} {target : Address} :
      sharing[index.toNat]? = some expansion →
      DeclReference sharing refs expansion target →
      DeclReference sharing refs (.share index) target

/-- Every semantic declaration reference selects an address from the
constant's reference table.  Following a sharing-table expansion can expose
more syntax, but cannot introduce an address outside `refs`. -/
theorem DeclReference.target_mem_refs {sharing : Array Ixon.Expr}
    {refs : Array Address} {root : Ixon.Expr} {target : Address}
    (h : DeclReference sharing refs root target) : target ∈ refs := by
  induction h with
  | ref hlookup | prjType hlookup =>
      obtain ⟨hbound, hget⟩ := Array.getElem?_eq_some_iff.mp hlookup
      exact Array.mem_iff_getElem.mpr ⟨_, hbound, hget⟩
  | prjValue _ ih => exact ih
  | appFn _ ih => exact ih
  | appArg _ ih => exact ih
  | lamType _ ih => exact ih
  | lamBody _ ih => exact ih
  | allType _ ih => exact ih
  | allBody _ ih => exact ih
  | letType _ ih => exact ih
  | letValue _ ih => exact ih
  | letBody _ ih => exact ih
  | share _ _ ih => exact ih

end IxonExpr

namespace IxonMutConst

/-- Root expressions which contribute to one member of a Muts block. -/
inductive RootExpr : Ixon.MutConst → Ixon.Expr → Prop
  | defnType {defn : Ixon.Definition} : RootExpr (.defn defn) defn.typ
  | defnValue {defn : Ixon.Definition} : RootExpr (.defn defn) defn.value
  | inductiveType {ind : Ixon.Inductive} : RootExpr (.indc ind) ind.typ
  | constructorType {ind : Ixon.Inductive} {ctor : Ixon.Constructor} :
      ctor ∈ ind.ctors → RootExpr (.indc ind) ctor.typ
  | recursorType {recr : Ixon.Recursor} : RootExpr (.recr recr) recr.typ
  | recursorRule {recr : Ixon.Recursor} {rule : Ixon.RecursorRule} :
      rule ∈ recr.rules → RootExpr (.recr recr) rule.rhs

end IxonMutConst

namespace IxonConstantInfo

/-- Every expression root which is semantically part of a constant.  Pure
projection records have no expression roots. -/
inductive RootExpr : Ixon.ConstantInfo → Ixon.Expr → Prop
  | defnType {defn : Ixon.Definition} : RootExpr (.defn defn) defn.typ
  | defnValue {defn : Ixon.Definition} : RootExpr (.defn defn) defn.value
  | recursorType {recr : Ixon.Recursor} : RootExpr (.recr recr) recr.typ
  | recursorRule {recr : Ixon.Recursor} {rule : Ixon.RecursorRule} :
      rule ∈ recr.rules → RootExpr (.recr recr) rule.rhs
  | axiomType {ax : Ixon.Axiom} : RootExpr (.axio ax) ax.typ
  | quotientType {quotient : Ixon.Quotient} :
      RootExpr (.quot quotient) quotient.typ
  | mutualMember {members : Array Ixon.MutConst} {member : Ixon.MutConst}
      {expr : Ixon.Expr} :
      member ∈ members → IxonMutConst.RootExpr member expr →
      RootExpr (.muts members) expr

end IxonConstantInfo

namespace IxonConstant

/-- Exact declaration dependency of a serialized constant. -/
def SemanticDependency (constant : Ixon.Constant)
    (target : Address) : Prop :=
  ∃ root,
    IxonConstantInfo.RootExpr constant.info root ∧
      IxonExpr.DeclReference constant.sharing constant.refs root target

theorem SemanticDependency.target_mem_refs {constant : Ixon.Constant}
    {target : Address} (h : SemanticDependency constant target) :
    target ∈ constant.refs := by
  obtain ⟨_, _, href⟩ := h
  exact href.target_mem_refs

end IxonConstant

namespace IxonEnv

/-- Structural condition needed to use production `blockOfAddr` as a
collapsed-node map.  Well-formed compiled environments satisfy it; malformed
projection chains must state the failure rather than being normalized
silently. -/
def BlockOfIdempotent (env : Ixon.Env) : Prop :=
  ∀ addr, blockOfAddr env (blockOfAddr env addr) = blockOfAddr env addr

/-- Production Ixon dependency catalog.  Dependencies are read from the
constant stored at the already-collapsed node. -/
def dependencyCatalog (env : Ixon.Env) (hblock : BlockOfIdempotent env) :
    DependencyCatalog where
  blockOf := blockOfAddr env
  dependsOn := fun source target =>
    ∃ constant, env.getConst? source = some constant ∧
      IxonConstant.SemanticDependency constant target
  blockOf_idem := hblock

@[simp] theorem dependencyCatalog_blockOf (env : Ixon.Env)
    (hblock : BlockOfIdempotent env) (addr : Address) :
    (dependencyCatalog env hblock).blockOf addr = blockOfAddr env addr :=
  rfl

theorem dependencyCatalog_dependsOn_iff (env : Ixon.Env)
    (hblock : BlockOfIdempotent env) {source target : Address} :
    (dependencyCatalog env hblock).dependsOn source target ↔
      ∃ constant, env.getConst? source = some constant ∧
        IxonConstant.SemanticDependency constant target :=
  Iff.rfl

end IxonEnv

end Ix.Tc
