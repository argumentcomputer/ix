/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.ContextTransport
import Ix.Kernel.Verify.LocalContext
import Ix.Kernel.Verify.Consistency.BinderOpening

/-!
# Reading production locals by their values

Regular binders map to model variables. Let-bound locals map to the already
checked value stored by the production declaration. This extends the scoped
reader and makes local zeta reduction preserve the reading itself. A regular
binder extends the model context and lifts older readings; a let leaves the
model context unchanged. Both operations preserve lookup completeness and
the exact types and stored values returned by the production local context.

The typing premise of a let push is the recursive inference obligation for
its value. General inference and cache preservation must still discharge it;
these local rules do not assume a general checker-soundness theorem.
-/

namespace Ix.Kernel.Consistency
open Theory Theory.Model
universe u v
variable {β : Type u} {m : Mode}

abbrev LocalValues (β : Type u) := FVarId → Option (AExpr β)

def readLocalExpr? (resolve : Address → Option (ConstRef β)) (values : LocalValues β) :
    KExpr m → (depth : Nat := 0) → Option (VExpr β)
  | .var index _ _, depth =>
      if index.toNat < depth then some (.bvar index.toNat) else none
  | .fvar id _ _, depth => (values id).map (fun value => value.erase.liftN depth)
  | .sort level _, _ => some (.sort (readLevel level))
  | .const id levels _, _ => do
      return .const (← resolve id.addr) (levels.toList.map readLevel)
  | .app fn arg _, depth => do
      return .app (← readLocalExpr? resolve values fn depth)
        (← readLocalExpr? resolve values arg depth)
  | .lam _ _ domain body _, depth => do
      return .lam (← readLocalExpr? resolve values domain depth)
        (← readLocalExpr? resolve values body (depth + 1))
  | .all _ _ domain body _, depth => do
      return .forallE (← readLocalExpr? resolve values domain depth)
        (← readLocalExpr? resolve values body (depth + 1))
  | .prj id index value _, depth => do
      return .proj (← resolve id.addr) index.toNat
        (← readLocalExpr? resolve values value depth)
  | .nat value _ _, _ => some (.natLit value)
  | .letE _ domain value body _ _, depth => do
      let _ ← readLocalExpr? resolve values domain depth
      let value ← readLocalExpr? resolve values value depth
      let body ← readLocalExpr? resolve values body (depth + 1)
      return body.inst value
  | .str value _ _, _ => readString? resolve value

@[simp] theorem readLocalExpr?_mkFVar (resolve : Address → Option (ConstRef β))
    (values : LocalValues β) (id : FVarId) (name : m.F Name) (depth : Nat) :
    readLocalExpr? resolve values (KExpr.mkFVar id name) depth =
      (values id).map (fun value => value.erase.liftN depth) := rfl

@[simp] theorem readLocalExpr?_mkApp (resolve : Address → Option (ConstRef β))
    (values : LocalValues β) (fn arg : KExpr m) (depth : Nat) :
    readLocalExpr? resolve values (KExpr.mkApp fn arg) depth = do
      return .app (← readLocalExpr? resolve values fn depth)
        (← readLocalExpr? resolve values arg depth) := rfl

@[simp] theorem readLocalExpr?_mkLam (resolve : Address → Option (ConstRef β))
    (values : LocalValues β) (name : m.F Name) (bi : m.F Lean.BinderInfo)
    (domain body : KExpr m) (depth : Nat) :
    readLocalExpr? resolve values (KExpr.mkLam name bi domain body) depth = do
      return .lam (← readLocalExpr? resolve values domain depth)
        (← readLocalExpr? resolve values body (depth + 1)) := rfl

@[simp] theorem readLocalExpr?_mkAll (resolve : Address → Option (ConstRef β))
    (values : LocalValues β) (name : m.F Name) (bi : m.F Lean.BinderInfo)
    (domain body : KExpr m) (depth : Nat) :
    readLocalExpr? resolve values (KExpr.mkAll name bi domain body) depth = do
      return .forallE (← readLocalExpr? resolve values domain depth)
        (← readLocalExpr? resolve values body (depth + 1)) := rfl

@[simp] theorem readLocalExpr?_mkPrj (resolve : Address → Option (ConstRef β))
    (values : LocalValues β) (id : KId m) (index : UInt64) (value : KExpr m) (depth : Nat) :
    readLocalExpr? resolve values (KExpr.mkPrj id index value) depth = do
      return .proj (← resolve id.addr) index.toNat
        (← readLocalExpr? resolve values value depth) := rfl

@[simp] theorem readLocalExpr?_mkLet (resolve : Address → Option (ConstRef β))
    (values : LocalValues β) (name : m.F Name) (domain value body : KExpr m)
    (nonDep : Bool) (depth : Nat) :
    readLocalExpr? resolve values (KExpr.mkLet name domain value body nonDep) depth = do
      let _ ← readLocalExpr? resolve values domain depth
      let value ← readLocalExpr? resolve values value depth
      let body ← readLocalExpr? resolve values body (depth + 1)
      return body.inst value := rfl

theorem readLocalExpr?_scoped (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (term : KExpr m) (depth : Nat) :
    readLocalExpr? resolve (fun id => (localIndex? locals id).map AExpr.bvar) term depth =
      readScopedExpr? resolve locals term depth := by
  induction term generalizing depth with
  | fvar id name info =>
      cases found : localIndex? locals id <;>
        simp [readLocalExpr?, readScopedExpr?, found, AExpr.erase, VExpr.liftN, liftVar]
  | _ => simp_all [readLocalExpr?, readScopedExpr?]

@[simp] theorem readLocalExpr?_eraseMeta
    (resolve : Address → Option (ConstRef β)) (values : LocalValues β)
    (term : KExpr m) (depth : Nat) :
    readLocalExpr? resolve values term.eraseMeta depth =
      readLocalExpr? resolve values term depth := by
  induction term generalizing depth <;>
    simp_all [readLocalExpr?, KExpr.eraseMeta, KId.eraseMeta,
      Array.toList_map, List.map_map, Function.comp_def]

theorem internExpr_readLocalExpr? {resolve : Address → Option (ConstRef β)}
    {values : LocalValues β} {table : InternTable m} {term : KExpr m} {depth : Nat}
    (coherent : table.WF)
    (faithful : KExpr.KeyCollisionFree fun value => table.ExprSupport value ∨ value = term) :
    readLocalExpr? resolve values (table.internExpr term).1 depth =
      readLocalExpr? resolve values term depth := by
  simpa only [readLocalExpr?_eraseMeta] using
    congrArg (fun term => readLocalExpr? resolve values term depth)
      (table.internExpr_eraseMeta coherent faithful)

private theorem option_bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ value, action = some value ∧ next value = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

theorem readLocalExpr?_extend {resolve : Address → Option (ConstRef β)}
    {values more : LocalValues β} {term : KExpr m} {depth : Nat} {source : VExpr β}
    (extension : ∀ id value, values id = some value → more id = some value)
    (reading : readLocalExpr? resolve values term depth = some source) :
    readLocalExpr? resolve more term depth = some source := by
  induction term generalizing source depth with
  | fvar id name info =>
      obtain ⟨value, found, rfl⟩ := Option.map_eq_some_iff.mp reading
      simp [readLocalExpr?, extension _ _ found]
  | var _ _ _ | sort _ _ | const _ _ _ | nat _ _ _ | str _ _ _ => exact reading
  | app fn arg info hf ha | lam _ _ fn arg info hf ha | all _ _ fn arg info hf ha =>
      rw [readLocalExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := option_bind_success reading
      obtain ⟨a, aReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readLocalExpr?, hf fReads, ha aReads]
  | prj id index value info ih =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := option_bind_success reading
      obtain ⟨value, valueReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readLocalExpr?, resolved, ih valueReads]
  | letE name domain value body nonDep info hA hv hb =>
      rw [readLocalExpr?] at reading
      obtain ⟨A, aReads, reading⟩ := option_bind_success reading
      obtain ⟨v, vReads, reading⟩ := option_bind_success reading
      obtain ⟨b, bReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readLocalExpr?, hA aReads, hv vReads, hb bReads]

theorem readLocalExpr?_lift {resolve : Address → Option (ConstRef β)}
    {values more : LocalValues β} {term : KExpr m} {depth : Nat} {source : VExpr β}
    (extension : ∀ id value, values id = some value → more id = some (value.liftN 1))
    (reading : readLocalExpr? resolve values term depth = some source) :
    readLocalExpr? resolve more term depth = some (source.liftN 1 depth) := by
  induction term generalizing source depth with
  | var index name info =>
      simp only [readLocalExpr?] at reading ⊢
      split at reading
      next bound =>
        cases reading
        simp [bound, VExpr.liftN, liftVar]
      · contradiction
  | fvar id name info =>
      obtain ⟨value, found, rfl⟩ := Option.map_eq_some_iff.mp reading
      simp only [readLocalExpr?, extension _ _ found, Option.map_some, AExpr.erase_liftN]
      congr 1
      rw [VExpr.liftN_combine (Nat.zero_le 0) (Nat.zero_le 1),
        VExpr.liftN_combine (Nat.zero_le depth) (by omega), Nat.add_comm]
  | str value _ _ =>
      rw [readString?_liftN reading]
      exact reading
  | sort _ _ | nat _ _ _ => cases reading; rfl
  | const id levels info =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := option_bind_success reading
      cases reading
      simp [readLocalExpr?, resolved, VExpr.liftN]
  | app fn arg info hf ha | lam _ _ fn arg info hf ha | all _ _ fn arg info hf ha =>
      rw [readLocalExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := option_bind_success reading
      obtain ⟨a, aReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readLocalExpr?, hf fReads, ha aReads, VExpr.liftN]
  | prj id index value info ih =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := option_bind_success reading
      obtain ⟨value, valueReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readLocalExpr?, resolved, ih valueReads, VExpr.liftN]
  | letE name domain value body nonDep info hA hv hb =>
      rw [readLocalExpr?] at reading
      obtain ⟨A, aReads, reading⟩ := option_bind_success reading
      obtain ⟨v, vReads, reading⟩ := option_bind_success reading
      obtain ⟨b, bReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readLocalExpr?, hA aReads, hv vReads, hb bReads, VExpr.liftN_inst_hi]

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

theorem localContext_find?_push_ne_eq {context : LocalContext m} {id fresh : FVarId}
    {decl : LocalDecl m} (coherent : context.WF) (different : id ≠ fresh) :
    (context.push fresh decl).find? id = context.find? id := by
  cases index : context.index[id]? with
  | none =>
      simp [LocalContext.find?, LocalContext.push, Std.HashMap.getElem?_insert,
        Ne.symm different, index]
  | some position =>
      have bound := coherent.index_lt index
      simp [LocalContext.find?, LocalContext.push, Std.HashMap.getElem?_insert,
        Ne.symm different, index, Array.getElem?_push, Nat.ne_of_lt bound]

def LocalValues.pushLet (values : LocalValues β) (fresh : FVarId) (value : AExpr β) :
    LocalValues β := fun id => if id = fresh then some value else values id

def LocalValues.pushBinder (values : LocalValues β) (fresh : FVarId) : LocalValues β :=
  fun id => if id = fresh then some (.bvar 0) else (values id).map (·.liftN 1)

/-- The live readings use only identifiers already allocated by the
production counter. Successful allocation checks that its increment fits. -/
def LocalValues.Below (values : LocalValues β) (next : UInt64) : Prop :=
  ∀ id value, values id = some value → id.id.toNat < next.toNat

theorem LocalValues.Below.empty (next : UInt64) :
    LocalValues.Below (β := β) (fun _ => none) next := by
  intro id value found
  contradiction

theorem LocalValues.Below.absent {values : LocalValues β} {next : UInt64}
    (below : values.Below next) : values ⟨next⟩ = none := by
  cases found : values ⟨next⟩ with
  | none => rfl
  | some value => exact False.elim (Nat.lt_irrefl _ (below _ _ found))

theorem LocalValues.Below.pushLet {values : LocalValues β} {next : UInt64}
    (below : values.Below next) (value : AExpr β)
    (room : next.toNat + 1 < UInt64.size) :
    (values.pushLet ⟨next⟩ value).Below (next + 1) := by
  have advance : (next + 1).toNat = next.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt room]
  intro id e found
  rw [advance]
  by_cases equal : id = ⟨next⟩
  · subst id; exact Nat.lt_succ_self _
  · simp only [LocalValues.pushLet, equal, if_false] at found
    exact Nat.lt_trans (below _ _ found) (Nat.lt_succ_self _)

theorem LocalValues.Below.pushBinder {values : LocalValues β} {next : UInt64}
    (below : values.Below next) (room : next.toNat + 1 < UInt64.size) :
    (values.pushBinder ⟨next⟩).Below (next + 1) := by
  have advance : (next + 1).toNat = next.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt room]
  intro id e found
  rw [advance]
  by_cases equal : id = ⟨next⟩
  · subst id; exact Nat.lt_succ_self _
  · simp only [LocalValues.pushBinder, equal, if_false] at found
    obtain ⟨previous, hit, _⟩ := Option.map_eq_some_iff.mp found
    exact Nat.lt_trans (below _ _ hit) (Nat.lt_succ_self _)

theorem LocalValues.pushLet_extends {values : LocalValues β} {fresh : FVarId}
    (absent : values fresh = none) (added : AExpr β) :
    ∀ id value, values id = some value → values.pushLet fresh added id = some value := by
  intro id value found
  have different : id ≠ fresh := by intro equal; subst id; simp [absent] at found
  simp [pushLet, different, found]

theorem LocalValues.pushBinder_lifts {values : LocalValues β} {fresh : FVarId}
    (absent : values fresh = none) :
    ∀ id value, values id = some value → values.pushBinder fresh id = some (value.liftN 1) := by
  intro id value found
  have different : id ≠ fresh := by intro equal; subst id; simp [absent] at found
  simp [pushBinder, different, found]

structure LocalContextValues (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (values : LocalValues β)
    (concrete : LocalContext .anon) (context : Model.Context β) : Prop where
  coherent : concrete.WF
  complete : ∀ id decl, concrete.find? id = some decl → ∃ value, values id = some value
  lookup : ∀ id value, values id = some value →
    ∃ decl type, concrete.find? id = some decl ∧
      readLocalExpr? resolve values decl.ty = some type.erase ∧
      TypingClaim.{u,v} entries context value type ∧
      ∀ stored, decl.val? = some stored → readLocalExpr? resolve values stored = some value.erase

theorem LocalContextValues.empty (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) :
    LocalContextValues.{u,v} resolve entries (fun _ => none) .empty [] := by
  refine ⟨.empty, ?_, ?_⟩
  · intro id decl found
    simp [LocalContext.find?, LocalContext.empty] at found
  · intro id value found
    contradiction

theorem LocalContextValues.index_none {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β}
    {concrete : LocalContext .anon} {context : Model.Context β} {id : FVarId}
    (agreement : LocalContextValues.{u,v} resolve entries values concrete context)
    (absent : values id = none) : concrete.index[id]? = none := by
  cases index : concrete.index[id]? with
  | none => rfl
  | some position =>
      obtain ⟨decl, atIndex⟩ := agreement.coherent.sound index
      have found : concrete.find? id = some decl := by simp [LocalContext.find?, index, atIndex]
      obtain ⟨value, read⟩ := agreement.complete _ _ found
      simp [absent] at read

theorem LocalContextValues.pushLet {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β}
    {concrete : LocalContext .anon} {context : Model.Context β}
    {fresh : FVarId} {name : Mode.anon.F Name} {type value : KExpr .anon}
    {A e : AExpr β}
    (agreement : LocalContextValues.{u,v} resolve entries values concrete context)
    (absent : values fresh = none)
    (typeReads : readLocalExpr? resolve values type = some A.erase)
    (valueReads : readLocalExpr? resolve values value = some e.erase)
    (typed : TypingClaim.{u,v} entries context e A) :
    LocalContextValues.{u,v} resolve entries (values.pushLet fresh e)
      (concrete.push fresh (.ldecl name type value)) context := by
  have extended := LocalValues.pushLet_extends absent e
  refine ⟨agreement.coherent.push (agreement.index_none absent), ?_, ?_⟩
  · intro id decl found
    by_cases equal : id = fresh
    · subst id; exact ⟨e, by simp [LocalValues.pushLet]⟩
    · rw [localContext_find?_push_ne_eq agreement.coherent equal] at found
      obtain ⟨v, hit⟩ := agreement.complete _ _ found
      exact ⟨v, extended _ _ hit⟩
  · intro id v hit
    by_cases equal : id = fresh
    · subst id
      simp only [LocalValues.pushLet, if_true, Option.some.injEq] at hit
      subst v
      refine ⟨.ldecl name type value, A, localContext_find?_push_same _ _ _,
        readLocalExpr?_extend extended typeReads, typed, ?_⟩
      intro stored found
      cases found
      exact readLocalExpr?_extend extended valueReads
    · simp only [LocalValues.pushLet, equal, if_false] at hit
      obtain ⟨decl, B, found, reading, vTyped, valueReading⟩ := agreement.lookup _ _ hit
      exact ⟨decl, B, localContext_find?_push_ne equal found,
        readLocalExpr?_extend extended reading, vTyped,
        fun stored found => readLocalExpr?_extend extended (valueReading stored found)⟩

theorem LocalContextValues.pushBinder {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β}
    {concrete : LocalContext .anon} {context : Model.Context β}
    {fresh : FVarId} {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {type : KExpr .anon} {A : AExpr β}
    (agreement : LocalContextValues.{u,v} resolve entries values concrete context)
    (absent : values fresh = none)
    (typeReads : readLocalExpr? resolve values type = some A.erase) :
    LocalContextValues.{u,v} resolve entries (values.pushBinder fresh)
      (concrete.push fresh (.cdecl name bi type)) (context.push A) := by
  have extended := LocalValues.pushBinder_lifts absent
  refine ⟨agreement.coherent.push (agreement.index_none absent), ?_, ?_⟩
  · intro id decl found
    by_cases equal : id = fresh
    · subst id; exact ⟨.bvar 0, by simp [LocalValues.pushBinder]⟩
    · rw [localContext_find?_push_ne_eq agreement.coherent equal] at found
      obtain ⟨v, hit⟩ := agreement.complete _ _ found
      exact ⟨v.liftN 1, extended _ _ hit⟩
  · intro id v hit
    by_cases equal : id = fresh
    · subst id
      simp only [LocalValues.pushBinder, if_true, Option.some.injEq] at hit
      subst v
      refine ⟨.cdecl name bi type, A.liftN 1, localContext_find?_push_same _ _ _,
        ?_, TypingClaim.bvar rfl, ?_⟩
      · simpa only [AExpr.erase_liftN, LocalDecl.ty] using readLocalExpr?_lift extended typeReads
      · intro stored found; contradiction
    · simp only [LocalValues.pushBinder, equal, if_false] at hit
      obtain ⟨previous, previousHit, rfl⟩ := Option.map_eq_some_iff.mp hit
      obtain ⟨decl, B, found, reading, vTyped, valueReading⟩ := agreement.lookup _ _ previousHit
      refine ⟨decl, B.liftN 1, localContext_find?_push_ne equal found, ?_,
        vTyped.weaken A, ?_⟩
      · simpa only [AExpr.erase_liftN] using readLocalExpr?_lift extended reading
      · intro stored found
        simpa only [AExpr.erase_liftN] using readLocalExpr?_lift extended (valueReading stored found)

def LocalModelTyping (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (values : LocalValues β) (context : Model.Context β)
    (term type : KExpr .anon) : Prop :=
  ∃ e A : AExpr β, readLocalExpr? resolve values term = some e.erase ∧
    readLocalExpr? resolve values type = some A.erase ∧
    TypingClaim.{u,v} entries context e A

theorem LocalModelTyping.closed {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {term type : KExpr .anon}
    (typed : LocalModelTyping.{u,v} resolve entries (fun _ => none) [] term type) :
    ModelTyping.{u,v} resolve entries [] term type := by
  obtain ⟨e, A, termReads, typeReads, typed⟩ := typed
  have asScoped (t : KExpr .anon) : readLocalExpr? resolve (fun _ => none) t =
      readScopedExpr? resolve [] t := readLocalExpr?_scoped resolve [] t 0
  rw [asScoped] at termReads typeReads
  exact ⟨e, A, readScopedExpr?_closed termReads, readScopedExpr?_closed typeReads, typed⟩

theorem inferUncached_fvar_local_sound {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β} {context : Model.Context β}
    {id : FVarId} {name : Mode.anon.F Name} {info : ExprInfo .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {inferOnly : Bool}
    {methods : Methods .anon} {before after : TcState .anon} {type : KExpr .anon}
    (agreement : LocalContextValues.{u,v} resolve entries values before.lctx context)
    (accepted : RecM.inferUncached inferRec inferOnly (.fvar id name info)
      methods before = .ok type after) :
    LocalModelTyping.{u,v} resolve entries values context (.fvar id name info) type := by
  change (RecM.inferUncached inferRec inferOnly (.fvar id name info)).run
    methods before = .ok type after at accepted
  unfold RecM.inferUncached at accepted
  simp only [ReaderT.run_bind] at accepted
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _ at accepted
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
    .ok before before from rfl] at accepted
  cases found : before.lctx.find? id with
  | none => simp only [found] at accepted; contradiction
  | some decl =>
      simp only [found] at accepted
      cases accepted
      obtain ⟨value, hit⟩ := agreement.complete _ _ found
      obtain ⟨decl', A, found', reading, typed, _⟩ := agreement.lookup _ _ hit
      have equal : decl' = decl := Option.some.inj (found'.symm.trans found)
      subst decl'
      exact ⟨value, A, by simp [readLocalExpr?, hit], reading, typed⟩

theorem whnfCoreWithFlagsStep_fvar_local_sound
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {values : LocalValues β} {context : Model.Context β}
    {id : FVarId} {name : Mode.anon.F Name} {info : ExprInfo .anon}
    {methods : Methods .anon} {before after : TcState .anon}
    {flags : WhnfFlags} {result : KExpr .anon}
    (agreement : LocalContextValues.{u,v} resolve entries values before.lctx context)
    (accepted : RecM.whnfCoreWithFlagsStep (.fvar id name info) flags
      methods before = .ok (.next result) after) :
    after = before ∧ ∃ e A : AExpr β,
      readLocalExpr? resolve values (.fvar id name info) = some e.erase ∧
      readLocalExpr? resolve values result = some e.erase ∧
      TypingClaim.{u,v} entries context e A := by
  change (RecM.whnfCoreWithFlagsStep (.fvar id name info) flags).run
    methods before = .ok (.next result) after at accepted
  unfold RecM.whnfCoreWithFlagsStep at accepted
  simp only [ReaderT.run_bind] at accepted
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _ at accepted
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
    .ok before before from rfl] at accepted
  cases found : before.lctx.find? id with
  | none => simp only [found] at accepted; cases accepted
  | some decl =>
      cases decl with
      | cdecl n bi ty => simp only [found] at accepted; cases accepted
      | ldecl n ty value =>
          simp only [found] at accepted
          cases accepted
          obtain ⟨value, hit⟩ := agreement.complete _ _ found
          obtain ⟨decl, A, found', _, typed, reading⟩ := agreement.lookup _ _ hit
          have equal : decl = .ldecl n ty result := Option.some.inj (found'.symm.trans found)
          subst decl
          exact ⟨rfl, value, A, by simp [readLocalExpr?, hit], reading result rfl, typed⟩

theorem openLet_eq (name : Mode.anon.F Name) (type value body : KExpr .anon)
    (before : TcState .anon) :
    TcM.openLet name type value body before =
      if before.env.nextFVarId.toNat + 1 < UInt64.size then
        let fresh : FVarId := ⟨before.env.nextFVarId⟩
        let internedLocal := before.env.intern.internExpr (KExpr.mkFVar fresh name)
        let opened := instantiateRev body #[internedLocal.1] internedLocal.2
        .ok (opened.1, fresh) {before with
          env := {before.env with
            nextFVarId := before.env.nextFVarId + 1
            intern := opened.2}
          lctx := before.lctx.push fresh (.ldecl name type value)}
      else .error (.other "free-variable id space exhausted") before := by
  unfold TcM.openLet
  change EStateM.bind TcM.freshFVarId _ before = _
  rw [EStateM.bind, TcM.freshFVarId]
  by_cases room : before.env.nextFVarId.toNat + 1 < UInt64.size
  · simp only [room, if_true]
    rfl
  · simp only [room, if_false]

theorem LocalContextValues.openLet {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β}
    {context : Model.Context β} {before after : TcState .anon}
    {fresh : FVarId} {name : Mode.anon.F Name} {type value body opened : KExpr .anon}
    {A e : AExpr β}
    (agreement : LocalContextValues.{u,v} resolve entries values before.lctx context)
    (absent : values ⟨before.env.nextFVarId⟩ = none)
    (typeReads : readLocalExpr? resolve values type = some A.erase)
    (valueReads : readLocalExpr? resolve values value = some e.erase)
    (typed : TypingClaim.{u,v} entries context e A)
    (accepted : TcM.openLet name type value body before = .ok (opened, fresh) after) :
    fresh = ⟨before.env.nextFVarId⟩ ∧
      LocalContextValues.{u,v} resolve entries (values.pushLet fresh e) after.lctx context := by
  rw [openLet_eq] at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, agreement.pushLet absent typeReads valueReads typed⟩
  · contradiction

theorem LocalContextValues.openBinder {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β}
    {context : Model.Context β} {before after : TcState .anon}
    {fresh : FVarId} {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {type body opened : KExpr .anon} {A : AExpr β}
    (agreement : LocalContextValues.{u,v} resolve entries values before.lctx context)
    (absent : values ⟨before.env.nextFVarId⟩ = none)
    (typeReads : readLocalExpr? resolve values type = some A.erase)
    (accepted : TcM.openBinder name bi type body before = .ok (opened, fresh) after) :
    fresh = ⟨before.env.nextFVarId⟩ ∧
      LocalContextValues.{u,v} resolve entries (values.pushBinder fresh)
        after.lctx (context.push A) := by
  rw [openBinder_eq] at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, agreement.pushBinder absent typeReads⟩
  · contradiction

end Ix.Kernel.Consistency
