import Ix.Cert.CtxAgreeHints

/-! # Projection rewrite lookups and definition lowering under renaming

`ProjectionAgree` describes the two reader tables outside the modeller's
`StateAgree`: projection owners, with their scope, and projection levels.
At states satisfying this internal relation, `projRewrite_mapKeys` preserves
both success and failure and gives a good rewritten value;
`lowerDefinition_mapKeys` transports the actual lowering, its hint and its
rewrite flag. The hint itself is the same on both sides; the compiler's
projection-hint bridge supplies that equality under its stated conditions.

`ownersOf` and `lowerInductive_owners` expose exactly the owners returned by
a successful inductive lowering. Their scoped renaming is proved separately
in `CtxAgreeOwners` (`ownersOf_mapKeys`), including the structPartsCore? gate.
The actual stream must still discharge `ProjectionAgree`; these intermediate
lemmas add no final compiler-correctness premise and do not claim the stream
composition is complete.
-/

namespace Ix.Cert.CtxAgree

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Frontend Ix.Kernel.Frontend.InModel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}

/-- The two extra reader tables used by the projection rewrite. This is a
local state relation whose stream provenance must be proved by the caller. -/
structure ProjectionAgree (f : md.Id → md'.Id) (P : KeyScope md)
    (source : State md) (target : State md') : Prop where
  owners : ∀ k : Key md, k.Good P →
    target.projOwners[k.map f]? = (source.projOwners[k]?).map (ProjRecOwner.mapKeys f)
  ownersGood : ∀ k : Key md, k.Good P → ∀ o, source.projOwners[k]? = some o → o.Good P
  levels : ∀ k : Key md, k.Good P → target.projLevels[k.map f]? = source.projLevels[k]?

theorem lamBody_mapKeys (value : CExpr md) :
    lamBody (value.mapKeys f) = (lamBody value).mapKeys f := by
  induction value with
  | lam t b m _ ih => simpa only [lamBody, Expr.mapKeys] using ih
  | _ => rfl

theorem lamBody_good {value : CExpr md} (good : value.Good P) : (lamBody value).Good P := by
  induction value with
  | lam t b m _ ih => exact ih good.2
  | _ => exact good

theorem projRewrite_rel (hP : P.Pre) (hf : InjOn f P) {source : State md} {target : State md'}
    (agree : ProjectionAgree f P source target) {cv : CVal md} {value : CExpr md}
    (typeGood : cv.type.Good P) (valueGood : value.Good P) :
    ORel (fun v v' => v' = v.mapKeys f ∧ v.Good P)
      (projRewrite source cv value) (projRewrite target (cv.mapKeys f) (value.mapKeys f)) := by
  have bodyGood := lamBody_good valueGood
  unfold projRewrite
  rw [lamBody_mapKeys]
  generalize hb : lamBody value = body at bodyGood ⊢
  cases body <;> simp only [Expr.mapKeys] <;> try trivial
  case proj T i arg =>
    cases arg <;> simp only [Expr.mapKeys] <;> try trivial
    case bvar n =>
      cases n with
      | succ => trivial
      | zero =>
        have ownerRel : ORel (fun o o' => o' = o.mapKeys f ∧ o.Good P)
            source.projOwners[T]? target.projOwners[T.map f]? :=
          ORel.of_eq (agree.owners T bodyGood.1) (agree.ownersGood T bodyGood.1)
        refine ORel.bind ownerRel fun o o' ho => ?_
        obtain ⟨rfl, goodOwner⟩ := ho
        refine ORel.bind (ORel.guard Iff.rfl) fun _ _ _ => ?_
        have keyGood : (projIotaName T i).Good P := bodyGood.1
        have levels : target.projLevels[projIotaName (T.map f) i]? = source.projLevels[projIotaName T i]? :=
          agree.levels _ keyGood
        rw [levels]
        cases hl : source.projLevels[projIotaName T i]? with
        | none => trivial
        | some level => exact projRecValue_mapKeys hP hf goodOwner level typeGood valueGood i

theorem projRewrite_mapKeys (hP : P.Pre) (hf : InjOn f P) {source : State md} {target : State md'}
    (agree : ProjectionAgree f P source target) {cv : CVal md} {value : CExpr md}
    (typeGood : cv.type.Good P) (valueGood : value.Good P) :
    projRewrite target (cv.mapKeys f) (value.mapKeys f) =
      (projRewrite source cv value).map (Expr.mapKeys f) ∧
      ∀ v, projRewrite source cv value = some v → v.Good P := by
  have related := projRewrite_rel hP hf agree typeGood valueGood
  cases hs : projRewrite source cv value with
  | none =>
    cases ht : projRewrite target (cv.mapKeys f) (value.mapKeys f) with
    | none => exact ⟨rfl, by intros; contradiction⟩
    | some v => rw [hs, ht] at related; exact related.elim
  | some v =>
    cases ht : projRewrite target (cv.mapKeys f) (value.mapKeys f) with
    | none => rw [hs, ht] at related; exact related.elim
    | some v' =>
      rw [hs, ht] at related
      obtain ⟨rfl, good⟩ := related
      exact ⟨rfl, by intro v equal; cases equal; exact good⟩

theorem lowerDefinition_mapKeys (hP : P.Pre) (hf : InjOn f P) {source : State md} {target : State md'}
    (agree : ProjectionAgree f P source target) {heights : CName md → Nat} {heights' : CName md' → Nat}
    (heightAgree : ∀ k : Key md, k.Good P → heights' (k.map f) = heights k)
    {cv : CVal md} {value : CExpr md} (typeGood : cv.type.Good P) (valueGood : value.Good P)
    (hint : Option Ix.Kernel.ReducibilityHint) (kind : Ix.DefKind) (safety : Ix.DefinitionSafety) :
    lowerDefinition hint target heights' (cv.mapKeys f) (value.mapKeys f) kind safety =
      (lowerDefinition hint source heights cv value kind safety).map fun (decl, rewrote) =>
        (decl.mapKeys f, rewrote) := by
  obtain ⟨rewritten, good⟩ := projRewrite_mapKeys hP hf agree typeGood valueGood
  have valueEq : ((projRewrite source cv value).map (Expr.mapKeys f)).getD (value.mapKeys f) =
      ((projRewrite source cv value).getD value).mapKeys f := by
    cases projRewrite source cv value <;> rfl
  have rewrittenGood : ((projRewrite source cv value).getD value).Good P := by
    cases h : projRewrite source cv value with
    | none => exact valueGood
    | some v => exact good v h
  unfold lowerDefinition
  simp only [rewritten, valueEq]
  cases safetyDeclineOf kind safety with
  | some why => rfl
  | none =>
    cases kind <;> simp only [hintFor_mapKeys heightAgree rewrittenGood, Option.isSome_map,
      pure, Except.pure, Except.map, Declaration.mapKeys]

/-- The projection-owner array constructed by `lowerInductive`, separated
from its checks and generation. Its scoped renaming is proved by
`ownersOf_mapKeys` in CtxAgreeOwners, including the structPartsCore? gate. -/
def ownersOf (rb : BlockRead md) : List (ProjRecOwner md) :=
  let block := rb.types.toList.map (fun (cv, _, _) => .indInfo cv {}) ++
    rb.ctors.toList.map (fun (cv, nP, nF) => .ctorInfo cv nP nF) ++
    rb.recs.toList.map fun (cv, r, rules) =>
      .recInfo cv (r.params + r.motives + r.minors + r.indices) (r.params + r.motives + r.minors) rules
  let types := rb.types.toList.zip rb.ctorNames.toList |>.map fun ((cv, nP, nIdx), cs) =>
    (cv.name, cv.levelParams, cv.type, nP, nIdx, cs, isRecOf rb)
  let ctors := rb.ctors.toList.map fun (cv, _, nF) => (cv.name, nF, cv.type)
  let recs := rb.recs.toList.map fun (cv, r, _) =>
    (cv.name, cv.levelParams, cv.type, r.motives, r.minors)
  projRecOwners block types ctors recs

/-- A successful lowering returns exactly these owners, independently of
which declarations the modeller generates. -/
theorem lowerInductive_owners {st : State md} {rb : BlockRead md} {r : Read md}
    (h : lowerInductive st rb = .ok r) : r.owners = ownersOf rb := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  replace h := LowerDistinct.lowerInductiveDecls_of_ok h
  unfold lowerInductiveDecls at h
  simp only [ite_not, bne_iff_ne, ne_eq] at h
  all_goals
    rcases ite_ok' h with ⟨-, h⟩ | ⟨-, h⟩
    all_goals first
      | (obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h)
      | skip
    all_goals
      rcases ite_ok' h with ⟨-, h⟩ | ⟨-, h⟩
      · split at h
        · simp [declined, throw, throwThe, MonadExceptOf.throw] at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          rfl
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rfl

end Ix.Cert.CtxAgree
