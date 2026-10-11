module
public import Ix.Compile.Canon.NameTable
public import Std.Data.HashMap.Lemmas
import all Ix.Environment
import all IxC.Address.Core
public section

namespace Ix.Compile.Canon

open Ix (Name Expr ConstantInfo)

/-- Every typed name in a universe, independently of its cached digest. -/
def sourceLevelNames : Ix.Level → List Lean.Name
  | .zero _ => []
  | .succ u _ => sourceLevelNames u
  | .max u v _ | .imax u v _ => sourceLevelNames u ++ sourceLevelNames v
  | .param n _ | .mvar n _ => [keyName n]

def sourcePreresolvedNames : Ix.SyntaxPreresolved → List Lean.Name
  | .namespace n | .decl n _ => [keyName n]

def sourceSyntaxNames (s : Ix.Syntax) : List Lean.Name :=
  match s with
  | .missing | .atom .. => []
  | .node _ kind args => keyName kind ::
      args.attach.toList.flatMap (fun a => sourceSyntaxNames a.1)
  | .ident _ _ value pres => keyName value :: pres.toList.flatMap sourcePreresolvedNames
termination_by sizeOf s
decreasing_by
  simp_wf
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem a.property) (by omega)

def sourceDataNames : Ix.DataValue → List Lean.Name
  | .ofName n => [keyName n]
  | .ofSyntax s => sourceSyntaxNames s
  | _ => []

/-- All name fields, including binders, universe parameters and syntax
metadata. These are forbidden spellings, not declaration dependencies. -/
def sourceExprNames : Expr → List Lean.Name
  | .bvar .. | .lit .. => []
  | .fvar n _ | .mvar n _ => [keyName n]
  | .sort u _ => sourceLevelNames u
  | .const n us _ => keyName n :: us.toList.flatMap sourceLevelNames
  | .app f a _ => sourceExprNames f ++ sourceExprNames a
  | .lam n t b _ _ | .forallE n t b _ _ =>
      keyName n :: (sourceExprNames t ++ sourceExprNames b)
  | .letE n t v b _ _ =>
      keyName n :: (sourceExprNames t ++ sourceExprNames v ++ sourceExprNames b)
  | .proj n _ e _ => keyName n :: sourceExprNames e
  | .mdata md e _ =>
      md.toList.flatMap (fun (n, v) => keyName n :: sourceDataNames v) ++ sourceExprNames e

/-- Declaration references only: constants and projection heads.
Metadata names are protected separately and never dereferenced. -/
def sourceExprRefs : Expr → List Name
  | .const n _ _ => [n]
  | .app f a _ => sourceExprRefs f ++ sourceExprRefs a
  | .lam _ t b _ _ | .forallE _ t b _ _ => sourceExprRefs t ++ sourceExprRefs b
  | .letE _ t v b _ _ => sourceExprRefs t ++ sourceExprRefs v ++ sourceExprRefs b
  | .proj n _ e _ => n :: sourceExprRefs e
  | .mdata _ e _ => sourceExprRefs e
  | _ => []

def sourceConstNames (ci : ConstantInfo) : List Lean.Name :=
  let c := ci.getCnst
  keyName c.name :: (c.levelParams.toList.map keyName ++ sourceExprNames c.type ++
    match ci with
    | .defnInfo v => v.all.toList.map keyName ++ sourceExprNames v.value
    | .thmInfo v => v.all.toList.map keyName ++ sourceExprNames v.value
    | .opaqueInfo v => v.all.toList.map keyName ++ sourceExprNames v.value
    | .inductInfo v => (v.all.toList ++ v.ctors.toList).map keyName
    | .ctorInfo v => [keyName v.induct]
    | .recInfo v => v.all.toList.map keyName ++
        v.rules.toList.flatMap (fun r => keyName r.ctor :: sourceExprNames r.rhs)
    | _ => [])

/-- Reference closure also follows a declaration's recorded mutual
members. A nested external group reads those members and their ctors,
even when one sibling is not mentioned directly by the first member. -/
def sourceConstRefs (ci : ConstantInfo) : List Name :=
  sourceExprRefs ci.getCnst.type ++
    match ci with
    | .defnInfo v => v.all.toList ++ sourceExprRefs v.value
    | .thmInfo v => v.all.toList ++ sourceExprRefs v.value
    | .opaqueInfo v => v.all.toList ++ sourceExprRefs v.value
    | .inductInfo v => v.all.toList ++ v.ctors.toList
    | .ctorInfo v => [v.induct]
    | .recInfo v => v.all.toList ++
        v.rules.toList.flatMap (fun r => r.ctor :: sourceExprRefs r.rhs)
    | _ => []


private theorem address_beq_iff {a b : Address} : (a == b) = true ↔ a = b := by
  obtain ⟨⟨x⟩⟩ := a
  obtain ⟨⟨y⟩⟩ := b
  show (ByteArray.beq ⟨x⟩ ⟨y⟩) = true ↔ _
  simp [ByteArray.beq]

private instance : LawfulBEq Address where
  rfl := address_beq_iff.2 rfl
  eq_of_beq := address_beq_iff.1

private instance : EquivBEq Name where
  rfl := by intro n; change (n.getHash == n.getHash) = true; exact BEq.rfl
  symm := by
    intro a b h
    change (a.getHash == b.getHash) = true at h
    change (b.getHash == a.getHash) = true
    exact BEq.symm h
  trans := by
    intro a b c h k
    change (a.getHash == b.getHash) = true at h
    change (b.getHash == c.getHash) = true at k
    change (a.getHash == c.getHash) = true
    exact BEq.trans h k

private instance : LawfulHashable Name where
  hash_eq a b h := by
    change (a.getHash == b.getHash) = true at h
    have e : a.getHash = b.getHash := by simpa using h
    change hash a.getHash = hash b.getHash
    rw [e]

/-- Actual lookup-key support, used only in the termination proof. It
does not evaluate lazy records or select any forbidden source names.
The original source maps compare a query's complete cached address, so
this is their exact lookup identity, not a generated-name equality. -/
def sourceSupport (source : Ix.Environment) : List Address :=
  source.overlay.toList.map (fun p => p.1.getHash) ++
    source.consts.toList.map (fun p => p.1.getHash) ++
    (source.fallback?.map (fun f => f.index.toList.map (fun p => p.1.getHash))).getD []

theorem map_key_mem {α : Type} {m : Std.HashMap Name α} {n : Name} {value : α}
    (h : m[n]? = some value) : n.getHash ∈ m.toList.map (fun p => p.1.getHash) := by
  obtain ⟨k, heq, hk⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp h
  have same : k.getHash = n.getHash := by
    change (n.getHash == k.getHash) = true at heq
    exact (address_beq_iff.1 heq).symm
  exact List.mem_map.mpr ⟨(k, value), hk, same⟩

theorem sourceGet_mem {source : Ix.Environment} {n : Name} {ci : ConstantInfo}
    (h : source.get? n = some ci) : n.getHash ∈ sourceSupport source := by
  unfold Ix.Environment.get? at h
  cases ho : source.overlay[n]? with
  | some a =>
    exact List.mem_append_left _ (List.mem_append_left _ (map_key_mem ho))
  | none =>
    cases hc : source.consts[n]? with
    | some a =>
      exact List.mem_append_left _ (List.mem_append_right _ (map_key_mem hc))
    | none =>
      cases hf : source.fallback? with
      | none => simp [ho, hc, hf] at h
      | some f =>
        cases hk : f.index[n]? with
        | none => simp [ho, hc, hf, Ix.LazyConstants.get?, hk] at h
        | some entry =>
          have member := map_key_mem hk
          simp only [sourceSupport, hf, Option.map_some, Option.getD_some]
          exact List.mem_append_right _ member

theorem filter_unseen_decreases {α : Type} [BEq α] [LawfulBEq α]
    (support seen : List α) (label : α)
    (mem : label ∈ support) (fresh : label ∉ seen) :
    (support.filter (fun n => !((label :: seen).contains n))).length <
      (support.filter (fun n => !seen.contains n)).length := by
  have rewrite : support.filter (fun n => !((label :: seen).contains n)) =
      (support.filter (fun n => !seen.contains n)).filter (· != label) := by
    simp only [List.filter_filter]
    apply List.filter_congr
    intro n _
    simp [bne_eq]
  rw [rewrite]
  have member : label ∈ support.filter (fun n => !seen.contains n) := by simp [mem, fresh]
  have le := List.length_filter_le (· != label) (support.filter (fun n => !seen.contains n))
  have ne : ((support.filter (fun n => !seen.contains n)).filter (· != label)).length ≠
      (support.filter (fun n => !seen.contains n)).length := by
    intro eq
    have impossible := (List.length_filter_eq_length_iff.mp eq) label member
    simp at impossible
  omega

structure SourceContext where
  declarations : Std.HashMap Name ConstantInfo := {}
  protectedNames : List Lean.Name := []
  visitedKeys : List Address := []

/-- `refs` are the actual declaration/reference edges, `names` all typed
Name fields (including binder, universe and syntax metadata). Metadata
names are protected but are not followed as constant references. -/
def collectSource (source : Ix.Environment) (refs : ConstantInfo → List Name)
    (names : ConstantInfo → List Lean.Name) (pending : List Name) (out : SourceContext := {})
    (groups : Std.HashMap Name (Array (Array Name)) := {}) : SourceContext :=
  match pending with
  | [] => out
  | n :: rest =>
    let out' := { out with protectedNames := keyName n :: out.protectedNames }
    match _h : source.get? n with
    | none => collectSource source refs names rest out' groups
    | some ci =>
      let out' := { out' with declarations := out'.declarations.insert n ci }
      if _known : n.getHash ∈ out.visitedKeys then
        collectSource source refs names rest out' groups
      else
        let groupRefs := match ci with
          | .inductInfo _ => ((groups.get? n).getD #[]).toList.flatMap (·.toList)
          | _ => []
        collectSource source refs names (refs ci ++ groupRefs ++ rest)
          { out' with
            protectedNames := names ci ++ out'.protectedNames
            visitedKeys := n.getHash :: out.visitedKeys } groups
termination_by
  (((sourceSupport source).filter (fun n => !out.visitedKeys.contains n)).length,
    pending.length)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.right _ (Nat.lt_succ_self _)
    | apply Prod.Lex.left
      simpa using filter_unseen_decreases (sourceSupport source) out.visitedKeys n.getHash
        (sourceGet_mem _h) _known

/-- The actual source data owned or referenced by this block. Only
declaration edges are traversed; typed metadata names are protected. -/
def sourceContext (source : Ix.Environment) (members : Array Name)
    (groups : Std.HashMap Name (Array (Array Name)) := {}) : SourceContext :=
  collectSource source sourceConstRefs sourceConstNames members.toList {} groups

end Ix.Compile.Canon
