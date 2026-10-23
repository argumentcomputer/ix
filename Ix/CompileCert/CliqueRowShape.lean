import Ix.Compile.Pass.Clique.Row
import Ix.CompileCert.Loop

/-! # The equation shape produced by an actual clique-row run

Successful construction supplies the exact source/member/value/sort lookups,
proof-generator run and outside-reference guard. The common type is the
original source header's type; the right endpoint names the argument f at
that header's level parameters. No publication or equality of ci.name and f
is inferred. The left endpoint and proof are the producer's actual renaming
outputs, not assumed faithful translations.

These are producer identities. Recipe validity, source-copy meaning, required
row existence, publication, reading/annotation and semantic universe/type
domains remain separate obligations.
-/

namespace Ix.CompileCert.CliqueRowShape

open Ix (Name Expr Level ConstantInfo)
open Ix.Compile.Pass.Clique
open Ix.Compile.Canon (mkAppN)
open Ix.Compile.LibraryNames (nEq)
open Ix.CompileCert.Loop (except_bind_ok)

/-- Names the producer's inline lookup of source encoding declarations. -/
def sourceDecls (const? : Name → Option ConstantInfo) (enc : Std.HashSet Name)
    (p : Name) : Option Decl :=
  if enc.contains p then (const? p).bind Decl.ofConstantInfo? else none

/-- Names the producer's inline lookup of canonical declarations. -/
def targetDecls (plan : CliquePlan) (p : Name) : Option Decl :=
  (plan.canon.find? (·.1.name == p)).map (·.1)

def outside (plan : CliquePlan) (enc : Std.HashSet Name) (n : Name) : Bool :=
  isEncodingName plan.all n && !enc.contains n

/-- The full proof run starts at the same empty TM state as rowOfWith. -/
theorem proof_run {x : TM Expr} {proof : Expr} (h : TM.run' x = .ok proof) :
    ∃ finish, x.run {} = .ok (proof, finish) := by
  unfold TM.run' at h
  simp only [StateT.run'_eq] at h
  cases hx : x.run {} with
  | error e => simp [hx, Functor.map, Except.map] at h
  | ok p =>
    have eq : p.1 = proof := by simpa [hx, Functor.map, Except.map] using h
    exact ⟨p.2, congrArg Except.ok (Prod.ext eq rfl)⟩

/-- Exact successful construction witnesses. sortOf? gives the actual
chosen universe, not a semantic typing fact. The guard uses the SAME original
proof and value subsequently renamed into the returned theorem. -/
def RowShape (const? : Name → Option ConstantInfo) (plan : CliquePlan)
    (enc : Std.HashSet Name) (f : Name) (row : ConstantInfo) : Prop :=
  ∃ (index : Nat) (md : Decl) (ci : ConstantInfo) (leanValue : Expr) (proof : Expr)
    (u : Level) (finish : TState),
    plan.all.idxOf? f = some index ∧ plan.aliases.any (·.1 == f) = false ∧
    plan.members.get? f = some md ∧ const? f = some ci ∧ valueOf? ci = some leanValue ∧
    sortOf? const? #[] ci.getCnst.type = some u ∧
    (rowProof const? (sourceDecls const? enc) (targetDecls plan) plan.all.size plan.sigma
      index ci.getCnst.type leanValue md.value
      (Expr.mkConst f (ci.getCnst.levelParams.map Level.mkParam))).run {} = .ok (proof, finish) ∧
    (constOccurrences (outside plan enc) leanValue ++ constOccurrences (outside plan enc) proof)[0]? = none ∧
    row = .thmInfo {
      cnst := ⟨rowName f, ci.getCnst.levelParams, mkAppN (Expr.mkConst nEq #[u])
        #[ci.getCnst.type, rowLhs enc leanValue, Expr.mkConst f (ci.getCnst.levelParams.map Level.mkParam)]⟩
      value := renameConsts (srcRename enc) proof
      all := #[rowName f] }

/-- The Eq endpoints and universe follow from the actual producer's success;
they are not inputs to the lemma. No raw input hash is trusted as equality. -/
theorem rowOfWith_shape {const? : Name → Option ConstantInfo} {plan : CliquePlan}
    {enc : Std.HashSet Name} {f : Name} {row : ConstantInfo}
    (produced : rowOfWith const? plan enc f = .ok row) : RowShape const? plan enc f row := by
  unfold rowOfWith at produced
  cases hindex : plan.all.idxOf? f with
  | none => simp only [hindex] at produced; cases produced
  | some index =>
    simp only [hindex] at produced
    split at produced
    · cases produced
    · rename_i noAlias
      have aliases : plan.aliases.any (·.1 == f) = false := by simpa using noAlias
      cases hmember : plan.members.get? f with
      | none => simp only [hmember] at produced; cases produced
      | some md =>
        simp only [hmember] at produced
        cases hsource : const? f with
        | none => simp only [hsource] at produced; cases produced
        | some ci =>
          simp only [hsource] at produced
          cases hvalue : valueOf? ci with
          | none => simp only [hvalue] at produced; cases produced
          | some leanValue =>
            simp only [hvalue] at produced
            cases hsort : sortOf? const? #[] ci.getCnst.type with
            | none => simp only [hsort] at produced; cases produced
            | some u =>
              simp only [hsort] at produced
              obtain ⟨proof, hproof, produced⟩ := except_bind_ok.mp produced
              obtain ⟨finish, run⟩ := proof_run hproof
              cases houtside : (constOccurrences (fun c => isEncodingName plan.all c && !enc.contains c) leanValue ++
                  constOccurrences (fun c => isEncodingName plan.all c && !enc.contains c) proof)[0]? with
              | some n =>
                simp only [houtside] at produced
                cases produced
              | none =>
                simp only [houtside] at produced
                exact ⟨index, md, ci, leanValue, proof, u, finish,
                  hindex, aliases, hmember, hsource, hvalue, hsort, run, houtside,
                  (Except.ok.inj produced).symm⟩

/-- The optional wrapper obtains the encoding set from the actual WF branch.
No row is asserted for a retained or unsupported encoding. -/
theorem rowOf_shape {const? : Name → Option ConstantInfo} {plan : CliquePlan}
    {f : Name} {row : ConstantInfo} (produced : rowOf const? plan f = .ok (some row)) :
    ∃ enc, plan.encoding = .wellFounded ∧ encodingSet const? plan = .ok enc ∧
      rowOfWith const? plan enc f = .ok row ∧ RowShape const? plan enc f row := by
  unfold rowOf at produced
  cases encoding : plan.encoding <;> simp only [encoding] at produced
  all_goals first
    | cases produced
    | (obtain ⟨enc, henc, produced⟩ := except_bind_ok.mp produced
       obtain ⟨row', hrow, produced⟩ := except_bind_ok.mp produced
       have eq : row' = row := Option.some.inj (Except.ok.inj produced)
       subst row'
       exact ⟨enc, rfl, henc, hrow, rowOfWith_shape hrow⟩)

/-- The actual copied header. In particular its universe parameters survive
unchanged; its renamed type is not confused with rowOfWith's common type. -/
theorem srcCopy_header (enc : Std.HashSet Name) (ci : ConstantInfo) :
    (srcCopy enc ci).getCnst = ⟨srcName ci.getCnst.name, ci.getCnst.levelParams,
      renameConsts (srcRename enc) ci.getCnst.type⟩ := by
  cases ci <;> rfl

/-- The copy and row-left producer use the same value renaming operation.
This is syntactic equality of producer outputs, not semantic faithfulness. -/
theorem srcCopy_value {enc : Std.HashSet Name} {ci : ConstantInfo} {value : Expr}
    (source : valueOf? ci = some value) : valueOf? (srcCopy enc ci) = some (rowLhs enc value) := by
  cases ci with
  | defnInfo v => cases Option.some.inj source; rfl
  | thmInfo v => cases Option.some.inj source; rfl
  | _ => cases source

/-- Compact header consumer, still derived solely from actual row production.
The original common type, renamed left, and f's own level arguments are exact. -/
theorem rowOfWith_header {const? : Name → Option ConstantInfo} {plan : CliquePlan}
    {enc : Std.HashSet Name} {f : Name} {row : ConstantInfo}
    (produced : rowOfWith const? plan enc f = .ok row) :
    ∃ ci value u, const? f = some ci ∧ valueOf? ci = some value ∧
      sortOf? const? #[] ci.getCnst.type = some u ∧
      row.getCnst = ⟨rowName f, ci.getCnst.levelParams, mkAppN (Expr.mkConst nEq #[u])
        #[ci.getCnst.type, rowLhs enc value, Expr.mkConst f (ci.getCnst.levelParams.map Level.mkParam)]⟩ := by
  obtain ⟨_, _, ci, value, _, u, _, _, _, _, hs, hv, hu, _, _, rfl⟩ := rowOfWith_shape produced
  exact ⟨ci, value, u, hs, hv, hu, rfl⟩

end Ix.CompileCert.CliqueRowShape
