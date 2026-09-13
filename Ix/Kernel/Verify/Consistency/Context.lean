/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ScopedExpr
import Ix.Kernel.Verify.Consistency.Atomic
import Std.Data.HashMap.Lemmas

/-!
# Production locals and model contexts

`LocalContextReading` identifies the actual declaration returned by each
active free-variable lookup and reads its type in the full model context.
It contains structural agreement only. The model variable rule supplies
typing for every valuation satisfying that context.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

private local instance : LawfulBEq FVarId where
  eq_of_beq := by
    intro left right equal
    cases left
    cases right
    congr 1
    exact eq_of_beq equal
  rfl {a} := by
    cases a with
    | mk x => show (x == x) = true; exact beq_self_eq_true x

theorem localContext_find?_push_same {m : Mode} (context : LocalContext m)
    (id : FVarId) (decl : LocalDecl m) :
    (context.push id decl).find? id = some decl := by
  simp [LocalContext.find?, LocalContext.push, Array.getElem?_push]

theorem localContext_find?_push_ne {m : Mode} {context : LocalContext m}
    {id fresh : FVarId} {decl added : LocalDecl m}
    (different : id ≠ fresh) (found : context.find? id = some decl) :
    (context.push fresh added).find? id = some decl := by
  cases index : context.index[id]? with
  | none => simp [LocalContext.find?, index] at found
  | some position =>
      cases value : context.decls[position]? with
      | none => simp [LocalContext.find?, index, value] at found
      | some pair =>
          have bound := (Array.getElem?_eq_some_iff.mp value).1
          simp [LocalContext.find?, index, value] at found
          simp [LocalContext.find?, LocalContext.push, Std.HashMap.getElem?_insert,
            Ne.symm different, index, Array.getElem?_push, Nat.ne_of_lt bound, value, found]

/-- Every registered id corresponds to the exact type returned by production
lookup. All types are expressed in the full current model context. -/
structure LocalContextReading {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (concrete : LocalContext .anon) (context : Model.Context β) : Prop where
  distinct : locals.Nodup
  length : context.length = locals.length
  lookup : ∀ id index, localIndex? locals id = some index →
    ∃ decl type, concrete.find? id = some decl ∧ context[index]? = some type ∧
      readScopedExpr? resolve locals decl.ty = some type.erase

theorem LocalContextReading.empty {β : Type u}
    (resolve : Address → Option (ConstRef β)) (concrete : LocalContext .anon) :
    LocalContextReading resolve [] concrete [] := by
  refine ⟨List.nodup_nil, rfl, ?_⟩
  intro id index found
  contradiction

/-- Pushing a fresh production declaration implements the model's lifted
context extension, including the types of older dependent locals. -/
theorem LocalContextReading.push {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {concrete : LocalContext .anon} {context : Model.Context β}
    {fresh : FVarId} {decl : LocalDecl .anon} {type : AExpr β}
    (agreement : LocalContextReading resolve locals concrete context)
    (absent : fresh ∉ locals)
    (reading : readScopedExpr? resolve locals decl.ty = some type.erase) :
    LocalContextReading resolve (fresh :: locals) (concrete.push fresh decl)
      (context.push type) := by
  refine ⟨List.nodup_cons.mpr ⟨absent, agreement.distinct⟩, ?_, ?_⟩
  · simp [Model.Context.push, agreement.length]
  · intro id index found
    by_cases equal : id = fresh
    · subst id
      simp only [localIndex?, if_true, Option.some.injEq] at found
      subst index
      refine ⟨decl, type.liftN 1, localContext_find?_push_same _ _ _, rfl, ?_⟩
      simpa only [AExpr.erase_liftN] using readScopedExpr?_push absent reading
    · simp only [localIndex?, equal, if_false] at found
      obtain ⟨previous, hit, rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨oldDecl, oldType, oldFound, oldIndex, oldReads⟩ := agreement.lookup id previous hit
      refine ⟨oldDecl, oldType.liftN 1, localContext_find?_push_ne equal oldFound, ?_, ?_⟩
      · simp [Model.Context.push, oldIndex]
      · simpa only [AExpr.erase_liftN] using readScopedExpr?_push absent oldReads

/-- Semantic typing tied to the exact opened expression and returned type. -/
def ScopedModelTyping {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (locals : List FVarId) (context : Model.Context β)
    (term type : KExpr .anon) : Prop :=
  ∃ e A : AExpr β,
    readScopedExpr? resolve locals term = some e.erase ∧
    readScopedExpr? resolve locals type = some A.erase ∧
    TypingClaim.{u,v} entries context e A

theorem ScopedModelTyping.closed {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {term type : KExpr .anon}
    (typed : ScopedModelTyping.{u,v} resolve entries [] [] term type) :
    ModelTyping.{u,v} resolve entries [] term type := by
  obtain ⟨e, A, he, hA, typed⟩ := typed
  exact ⟨e, A, readScopedExpr?_closed he, readScopedExpr?_closed hA, typed⟩

/-- Computing an inference key changes only its memo table, preserving the
actual free-variable context in every fast, hit, and miss branch. -/
theorem inferKey_lctx {term : KExpr .anon} {before after : TcState .anon}
    {key : Address × Address}
    (run : TcM.inferKey term before = .ok key after) : after.lctx = before.lctx := by
  unfold TcM.inferKey at run
  change EStateM.bind (TcM.ctxAddrForLbr term.lbr) _ before = _ at run
  unfold TcM.ctxAddrForLbr at run
  change EStateM.bind (fun state => EStateM.bind (get : TcM .anon (TcState .anon))
    _ state) _ before = _ at run
  simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
    .ok before before from rfl] at run
  by_cases fast : (term.lbr == 0 || before.ctx.isEmpty) = true
  · rw [if_pos fast] at run
    cases run; rfl
  · rw [if_neg fast] at run
    cases cached : before.ctxAddrCache[(before.ctxId, term.lbr)]? with
    | none => rw [cached] at run; cases run; rfl
    | some address => rw [cached] at run; cases run; rfl

theorem UncachedInference.localContext {term : KExpr .anon} {before : TcState .anon}
    (miss : UncachedInference before term) : miss.keyed.lctx = before.lctx :=
  inferKey_lctx miss.keyRun

/-- The actual free-variable inference branch reads its type from the local
context; model typing follows from that same context entry. -/
theorem inferUncached_fvar_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {id : FVarId} {index : Nat}
    {info : ExprInfo .anon} {name : Mode.anon.F Name}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {inferOnly : Bool}
    {methods : Methods .anon} {before after : TcState .anon} {type : KExpr .anon}
    (agreement : LocalContextReading resolve locals before.lctx context)
    (registered : localIndex? locals id = some index)
    (accepted : RecM.inferUncached inferRec inferOnly (.fvar id name info)
      methods before = .ok type after) :
    ∃ A : AExpr β, context[index]? = some A ∧
      readScopedExpr? resolve locals type = some A.erase ∧
      TypingClaim.{u,v} entries context (.bvar index) A := by
  obtain ⟨decl, A, found, atIndex, reading⟩ := agreement.lookup id index registered
  change (RecM.inferUncached inferRec inferOnly (.fvar id name info)).run
    methods before = .ok type after at accepted
  unfold RecM.inferUncached at accepted
  simp only [ReaderT.run_bind] at accepted
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _ at accepted
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
    .ok before before from rfl] at accepted
  simp only [found] at accepted
  cases accepted
  exact ⟨A, atIndex, reading, TypingClaim.bvar atIndex⟩

/-- Free-variable inference through both cache lookups and the final cache
write, under the same explicit miss boundary as constant inference. -/
theorem infer_fvar_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {id : FVarId} {index : Nat}
    {info : ExprInfo .anon} {name : Mode.anon.F Name}
    {methods : Methods .anon} {before after : TcState .anon} {type : KExpr .anon}
    (miss : UncachedInference before (.fvar id name info))
    (agreement : LocalContextReading resolve locals miss.keyed.lctx context)
    (registered : localIndex? locals id = some index)
    (accepted : RecM.infer (.fvar id name info) methods before = .ok type after) :
    ScopedModelTyping.{u,v} resolve entries locals context (.fvar id name info) type := by
  obtain ⟨state, run⟩ := infer_uncached_success miss accepted
  obtain ⟨A, _, reading, typed⟩ := inferUncached_fvar_sound agreement registered run
  exact ⟨.bvar index, A, by simp [readScopedExpr?, registered, AExpr.erase], reading, typed⟩

/-- A free-variable cache entry must be the exact type returned by its
current production declaration. This is a check on concrete data at one key;
it does not assert semantic typing of a cached answer. -/
structure FVarInferenceSupport (before : TcState .anon) (id : FVarId)
    (name : Mode.anon.F Name) (info : ExprInfo .anon) where
  key : Address × Address
  keyed : TcState .anon
  keyRun : TcM.inferKey (.fvar id name info) before = .ok key keyed
  fullMatches : ∀ cached decl, keyed.env.inferCache[key]? = some cached →
    keyed.lctx.find? id = some decl → cached = decl.ty
  onlyMatches : before.inferOnly = true →
    ∀ cached decl, keyed.env.inferOnlyCache[key]? = some cached →
    keyed.lctx.find? id = some decl → cached = decl.ty

def FVarInferenceSupport.ofMiss {before : TcState .anon} {id : FVarId}
    {name : Mode.anon.F Name} {info : ExprInfo .anon}
    (miss : UncachedInference before (.fvar id name info)) :
    FVarInferenceSupport before id name info := {
  key := miss.key, keyed := miss.keyed, keyRun := miss.keyRun
  fullMatches := by intros; simp_all [miss.fullMiss]
  onlyMatches := by intros; simp_all [miss.onlyMiss]
}

/-- Local inference returns the actual declaration type through either cache
partition or the uncached lookup, including the final cache insertion. -/
theorem FVarInferenceSupport.output {before after : TcState .anon} {id : FVarId}
    {name : Mode.anon.F Name} {info : ExprInfo .anon} {decl : LocalDecl .anon}
    {methods : Methods .anon} {type : KExpr .anon}
    (support : FVarInferenceSupport before id name info)
    (found : support.keyed.lctx.find? id = some decl)
    (accepted : RecM.infer (.fvar id name info) methods before = .ok type after) :
    type = decl.ty := by
  change (RecM.infer (.fvar id name info)).run methods before = .ok type after at accepted
  unfold RecM.infer RecM.inferWith at accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.inferKey (.fvar id name info)) _ before = _ at accepted
  rw [EStateM.bind, support.keyRun] at accepted
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ support.keyed = _ at accepted
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) support.keyed =
    .ok support.keyed support.keyed from rfl] at accepted
  cases full : support.keyed.env.inferCache[support.key]? with
  | some cached =>
      simp only [full] at accepted
      cases accepted
      exact support.fullMatches _ _ full found
  | none =>
      simp only [full] at accepted
      cases policy : before.inferOnly with
      | false =>
          simp only [policy, Bool.false_eq_true, if_false] at accepted
          have lookup : RecM.inferUncached RecM.inferCall false (.fvar id name info)
              methods support.keyed = .ok decl.ty support.keyed := by
            change (RecM.inferUncached RecM.inferCall false (.fvar id name info)).run
              methods support.keyed = _
            unfold RecM.inferUncached
            simp only [ReaderT.run_bind]
            change EStateM.bind (get : TcM .anon (TcState .anon)) _ support.keyed = _
            rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) support.keyed =
              .ok support.keyed support.keyed from rfl]
            simp only [found]
            rfl
          change EStateM.bind (RecM.inferUncached RecM.inferCall false (.fvar id name info) methods)
            _ support.keyed = _ at accepted
          rw [EStateM.bind, lookup] at accepted
          cases accepted
          rfl
      | true =>
          simp only [policy, if_true, ReaderT.run_bind] at accepted
          change EStateM.bind (get : TcM .anon (TcState .anon)) _ support.keyed = _ at accepted
          rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) support.keyed =
            .ok support.keyed support.keyed from rfl] at accepted
          cases only : support.keyed.env.inferOnlyCache[support.key]? with
          | some cached =>
              simp only [only] at accepted
              cases accepted
              exact support.onlyMatches policy _ _ only found
          | none =>
              simp only [only] at accepted
              have lookup : RecM.inferUncached RecM.inferCall true (.fvar id name info)
                  methods support.keyed = .ok decl.ty support.keyed := by
                change (RecM.inferUncached RecM.inferCall true (.fvar id name info)).run
                  methods support.keyed = _
                unfold RecM.inferUncached
                simp only [ReaderT.run_bind]
                change EStateM.bind (get : TcM .anon (TcState .anon)) _ support.keyed = _
                rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) support.keyed =
                  .ok support.keyed support.keyed from rfl]
                simp only [found]
                rfl
              change EStateM.bind (RecM.inferUncached RecM.inferCall true
                (.fvar id name info) methods) _ support.keyed = _ at accepted
              rw [EStateM.bind, lookup] at accepted
              cases accepted
              rfl

theorem FVarInferenceSupport.sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {before after : TcState .anon}
    {id : FVarId} {name : Mode.anon.F Name} {info : ExprInfo .anon}
    {index : Nat} {A : AExpr β} {methods : Methods .anon} {type : KExpr .anon}
    (support : FVarInferenceSupport before id name info)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (registered : localIndex? locals id = some index)
    (atIndex : context[index]? = some A)
    (accepted : RecM.infer (.fvar id name info) methods before = .ok type after) :
    readScopedExpr? resolve locals type = some A.erase ∧
      TypingClaim.{u,v} entries context (.bvar index) A := by
  have keyedAgreement := (inferKey_lctx support.keyRun).symm ▸ agreement
  obtain ⟨decl, B, found, position, reading⟩ := keyedAgreement.lookup id index registered
  have equal := Option.some.inj (position.symm.trans atIndex)
  subst B
  rw [support.output found accepted]
  exact ⟨reading, TypingClaim.bvar atIndex⟩

end Ix.Kernel.Consistency
