import Ix.Cert.DefinitionBlockReads

/-! # A compiled definition block references its members' mentioned names' bindings

The compile of a definition block reads, through the emission reading theorems, in any context
that reads the compile environment's bindings as `names` relates them. Read it in a context
whose keys are the addresses themselves (`addrCtx`: a store that resolves every address as a
singleton record and no roles, so `keyAt a = .id a`), the block's members as fresh keys
(`DefinitionOrder.tagSelf`), and every other name as its binding's address (`addrNames`). Then a
name a member's terms mention, other than a member, reads as its binding's address, and a
reading mentions an address only through a reference of the record (`refs_read`): the record's
reference table holds the binding of every non-member name its members mention
(`mentioned_binding_ref`). -/

namespace Ix.Cert.BlockRefs

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.DefinitionDeps (ConstOcc)

/-! ## A context keyed by addresses -/

/-- A singleton record every address of `addrCtx`'s store holds. -/
def anyRecord : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[]⟩

/-- **A context whose keys are the addresses**, with the compile's blobs. -/
def addrCtx (blob : Address → Option ByteArray) : Ctx .anon :=
  { store := fun _ => some anyRecord, blob, roles := {}, index := default }

theorem addrCtx_keyAt (blob : Address → Option ByteArray) (a : Address) :
    (addrCtx blob).keyAt a = .ok (.id a) := by
  simp [Ctx.keyAt, addrCtx, resolve, resolveSource, anyRecord, Mode.addressId?, pure, Except.pure]

/-! ## A reading mentions an address only through a reference -/

section Refs

variable {cx : Ctx .anon} {c : Ixon.Constant} {univs : Array CLevel} {N : Nat} {K : Nat → CName .anon}

/-- The reading table's entries mention an address only through a reference of the record. -/
def TblRefs (c : Ixon.Constant) (tbl : Array (ReadM (CExpr .anon))) : Prop :=
  ∀ (i : Nat) (t : CExpr .anon), tbl[i]? = some (.ok t) → ∀ a, Frontend.occursConst (.id a) t = true → a ∈ c.refs

theorem expr_refs (keys : ∀ a k, cx.keyAt a = .ok k → k = .id a) (aux : ∀ j a, K j ≠ .id a)
    {tbl : Array (ReadM (CExpr .anon))} (htbl : TblRefs c tbl) :
    ∀ (e : Ixon.Expr) (t : CExpr .anon), convExpr ⟨cx, c, univs, DefinitionOrder.tagSelf N K⟩ tbl e = .ok t →
      ∀ a, Frontend.occursConst (.id a) t = true → a ∈ c.refs := by
  intro e
  induction e with
  | var i =>
    intro t h a ho
    simp only [convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [Ix.Kernel.Expr.mkBvar_eq, Frontend.occursConst] at ho
  | sort i =>
    intro t h a ho
    simp only [convExpr] at h
    obtain ⟨l, -, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [Frontend.occursConst] at ho
  | ref i us =>
    intro t h a ho
    simp only [convExpr] at h
    obtain ⟨k, hk, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨ls, -, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    unfold ECx.keyAt at hk
    cases ha : c.refs[i.toNat]? with
    | none => simp only [ha] at hk; cases hk
    | some a' =>
      simp only [ha] at hk
      have := keys a' k hk
      subst this
      simp only [Frontend.occursConst, beq_iff_eq, Key.id.injEq] at ho
      subst ho
      exact Array.mem_of_getElem? ha
  | recur i us =>
    intro t h a ho
    simp only [convExpr] at h
    unfold DefinitionOrder.tagSelf at h
    by_cases hi : i.toNat < N
    · simp only [hi, ↓reduceIte] at h
      obtain ⟨k, hk, h⟩ := RecordTransfer.bind_ok h
      obtain ⟨ls, -, h⟩ := RecordTransfer.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h hk
      subst h hk
      simp only [Frontend.occursConst, beq_iff_eq] at ho
      exact absurd ho (aux _ _)
    · simp only [hi, ↓reduceIte] at h
      cases h
  | prj i field v ih =>
    intro t h a ho
    simp only [convExpr] at h
    obtain ⟨k, -, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨v', hv, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ih v' hv a ho
  | str i =>
    intro t h a ho
    simp only [convExpr] at h
    obtain ⟨b, -, h⟩ := RecordTransfer.bind_ok h
    cases hs : String.fromUTF8? b with
    | none => rw [hs] at h; cases h
    | some s =>
      rw [hs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [Frontend.occursConst] at ho
  | nat i =>
    intro t h a ho
    simp only [convExpr] at h
    obtain ⟨b, -, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [Frontend.occursConst] at ho
  | app f x ihf ihx =>
    intro t h a ho
    simp only [convExpr] at h
    obtain ⟨f', hf, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨x', hx, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Frontend.occursConst, Bool.or_eq_true] at ho
    exact ho.elim (ihf f' hf a) (ihx x' hx a)
  | lam bc ty b iht ihb =>
    intro t h a ho
    simp only [convExpr] at h
    obtain ⟨ty', hty, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨b', hb, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Frontend.occursConst, Bool.or_eq_true] at ho
    exact ho.elim (iht ty' hty a) (ihb b' hb a)
  | all bc vc ty b iht ihb =>
    intro t h a ho
    simp only [convExpr] at h
    obtain ⟨ty', hty, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨b', hb, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Frontend.occursConst, Bool.or_eq_true] at ho
    exact ho.elim (iht ty' hty a) (ihb b' hb a)
  | letE lc ty v b iht ihv ihb =>
    intro t h a ho
    simp only [convExpr] at h
    obtain ⟨ty', hty, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨v', hv, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨b', hb, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Frontend.occursConst, Bool.or_eq_true] at ho
    exact ho.elim (fun h => h.elim (iht ty' hty a) (ihv v' hv a)) (ihb b' hb a)
  | share i =>
    intro t h a ho
    simp only [convExpr] at h
    cases hr : tbl[i.toNat]? with
    | none => simp only [hr] at h; cases h
    | some r =>
      simp only [hr] at h
      subst h
      exact htbl i.toNat t hr a ho

theorem tblFold_refs (keys : ∀ a k, cx.keyAt a = .ok k → k = .id a) (aux : ∀ j a, K j ≠ .id a) :
    ∀ (l : List Ixon.Expr) {tbl : Array (ReadM (CExpr .anon))}, TblRefs c tbl →
      TblRefs c (RecordTransfer.tblFold ⟨cx, c, univs, DefinitionOrder.tagSelf N K⟩ l tbl)
  | [], _, h => h
  | e :: l, tbl, h => by
    simp only [RecordTransfer.tblFold, List.foldl_cons]
    refine tblFold_refs keys aux l (fun i t hi a ho => ?_)
    rw [Array.getElem?_push] at hi
    split at hi
    · simp only [Option.some.injEq] at hi
      exact expr_refs keys aux h e t hi a ho
    · exact h i t hi a ho

end Refs

/-- **A reading mentions an address only through a reference of the record**: the member
reader reading references by their addresses and members by keys that are no address. -/
theorem refs_read {cx : Ctx .anon} {c : Ixon.Constant} {param : Nat → LevelParam} {N : Nat}
    {K : Nat → CName .anon} (keys : ∀ a k, cx.keyAt a = .ok k → k = .id a) (aux : ∀ j a, K j ≠ .id a)
    {x : Ixon.Expr} {t : CExpr .anon}
    (h : (MemberReader.mk' cx c param (DefinitionOrder.tagSelf N K)).read x = .ok t)
    (a : Address) (ho : Frontend.occursConst (.id a) t = true) : a ∈ c.refs := by
  rw [RecordTransfer.mk'_eq] at h
  exact expr_refs keys aux (tblFold_refs keys aux c.sharing.toList (fun i t hi => by simp at hi)) x t h a ho

/-! ## A mentioned name has a key -/

/-- **A related reading mentions a key of every name its Lean term mentions.** -/
theorem related_occ {names : Ix.Name → CName .anon → Prop} {levels : Ix.Level → Kernel.Level → Prop}
    {e : Ix.Expr} {t : CExpr .anon} (rel : Related names levels e t) {n : Ix.Name} (hn : ConstOcc n e) :
    ∃ k, names n k ∧ Frontend.occursConst k t = true := by
  induction rel with
  | bvar => cases hn
  | sort => cases hn
  | const hash sources targets mapped universes =>
    cases hn
    exact ⟨_, mapped, by simp [Frontend.occursConst]⟩
  | app hash _ _ fnIH argIH =>
    cases hn with
    | appF h => obtain ⟨k, hk, ho⟩ := fnIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
    | appA h => obtain ⟨k, hk, ho⟩ := argIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
  | lam name info hash _ _ typeIH bodyIH =>
    cases hn with
    | lamT h => obtain ⟨k, hk, ho⟩ := typeIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
    | lamB h => obtain ⟨k, hk, ho⟩ := bodyIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
  | all name info hash _ _ typeIH bodyIH =>
    cases hn with
    | allT h => obtain ⟨k, hk, ho⟩ := typeIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
    | allB h => obtain ⟨k, hk, ho⟩ := bodyIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
  | letE name nonDep hash _ _ _ typeIH valueIH bodyIH =>
    cases hn with
    | letT h => obtain ⟨k, hk, ho⟩ := typeIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
    | letV h => obtain ⟨k, hk, ho⟩ := valueIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
    | letB h => obtain ⟨k, hk, ho⟩ := bodyIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
  | nat => cases hn
  | str => cases hn
  | proj field hash mapped _ valueIH =>
    cases hn with
    | proj h => obtain ⟨k, hk, ho⟩ := valueIH h; exact ⟨k, hk, by simp [Frontend.occursConst, ho]⟩
  | mdata data hash plain _ bodyIH =>
    cases hn with
    | mdata h => exact bodyIH h
  | contract data hash c frame read _ lowered bodyIH =>
    cases hn with
    | mdata h =>
      obtain ⟨k, hk, ho⟩ := bodyIH h
      exact ⟨k, hk, by rw [DefinitionDeps.withContract_occurs lowered]; exact ho⟩

/--
info: 'Ix.Cert.BlockRefs.refs_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refs_read

/--
info: 'Ix.Cert.BlockRefs.related_occ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms related_occ


/-! ## The block's references -/

open Ix.Cert.DefinitionBlockReads (ctx_defs_val ctx_defs_member)

/-- The names a definition block is read at in `addrCtx`: a member as a fresh key, any other name
as its binding's address. -/
def addrNames (defs : List Ix.Def) (env : CompileEnv) (bindings : Bindings) (K : Nat → CName .anon)
    (n : Ix.Name) (k : CName .anon) : Prop :=
  match (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[n]? with
  | some j => k = K j
  | none => ∃ a, lookupBinding env bindings n = some a ∧ k = .id a

/-- **A definition block's reference table holds the binding of every non-member name its
members mention**, for a block compiled from a clean state in which no member is bound. -/
theorem mentioned_binding_ref (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    {bindings : Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before) {defs : List Ix.Def} (two : 2 ≤ defs.length)
    (distinct : Canon.KeysDistinct (defs.map MutConst.defn))
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before =
      (.ok output, after))
    (unresolved : ∀ d ∈ defs, bindings.1.get? d.name = none ∧ context.1.nameToAddr.get? d.name = none)
    (unaliased : ∀ d ∈ defs, bindings.2.get? d.name = none ∧ context.1.auxNameToAddr.get? d.name = none)
    {i : Nat} (hi : i < defs.length) {n : Ix.Name} (hn : ConstOcc n defs[i].type ∨ ConstOcc n defs[i].value)
    (notMember : (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[n]? = none) :
    ∃ a, lookupBinding context.1 bindings n = some a ∧ a ∈ output.block.refs := by
  let cx := addrCtx (fun a => context.1.blobs.get? a)
  let K : Nat → CName .anon := DefinitionOrder.freshKey cx
  have aux : ∀ j a, K j ≠ .id a := fun j a h => by cases h
  have external : BindingsCorrect context.1 bindings cx (addrNames defs context.1 bindings K) := by
    intro m a hb
    have hnone : (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[m]? = none := by
      cases hc : (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[m]? with
      | none => rfl
      | some j =>
        exfalso
        obtain ⟨hj, hname⟩ := ctx_defs_val distinct hc
        have hd := List.getElem_mem hj
        rw [← hname] at hb
        simp only [lookupBinding, (unresolved _ hd).1, (unresolved _ hd).2, (unaliased _ hd).1,
          (unaliased _ hd).2, Option.orElse] at hb
        cases hb
    exact ⟨.id a, addrCtx_keyAt _ a, by simp only [addrNames, hnone]; exact ⟨a, hb, rfl⟩⟩
  have scopes : ∀ m ∈ defs.map MutConst.defn, ∀ e ∈ BlockEmission.memberSources m,
      ConstsSatisfy (SelfName (BlockEmission.mutContext ((defs.map MutConst.defn).map ([·])) context).2
        (DefinitionOrder.tagSelf defs.length K) (addrNames defs context.1 bindings K)) e := by
    intro _ _ e _
    refine constsSatisfy_of_forall (fun m index found => ?_) e
    change (MutConst.ctx ((defs.map MutConst.defn).map ([·]))).get? m = some index at found
    rw [Std.TreeMap.get?_eq_getElem?] at found
    obtain ⟨hj, -⟩ := ctx_defs_val distinct found
    exact ⟨_, by simp only [DefinitionOrder.tagSelf, hj, ↓reduceIte]; rfl,
      by simp only [addrNames, found]⟩
  obtain ⟨ts, hinfo, each⟩ := DefinitionEmission.defsBlock_each cx id (DefinitionOrder.tagSelf defs.length K)
    (addrNames defs context.1 bindings K) bindings (fun m => (Ix.LeanIngress.Numbering.mk m.levelParams false).pos)
    context free (fun _ => rfl) external defs two scopes clean ran
  obtain ⟨-, -, ⟨tT, hTread, hTrel⟩, ⟨tV, hVread, hVrel⟩⟩ :=
    DefinitionBlocks.forall₂_getElem each i hi (by have := DefinitionBlocks.forall₂_length each; omega)
  have keys : ∀ a k, (ExpressionRead.withBlockBlobs cx after).keyAt a = .ok k → k = .id a := by
    intro a k h
    have h' : cx.keyAt a = .ok k := h
    rw [addrCtx_keyAt] at h'
    exact (Except.ok.inj h').symm
  have found : ∀ (t : CExpr .anon) (x : Ixon.Expr),
      (EmissionBlocks.recordReader cx id (DefinitionOrder.tagSelf defs.length K) after output.block).read x = .ok t →
      ∀ k, addrNames defs context.1 bindings K n k → Frontend.occursConst k t = true →
        ∃ a, lookupBinding context.1 bindings n = some a ∧ a ∈ output.block.refs := by
    intro t x hread k hk ho
    simp only [addrNames, notMember] at hk
    obtain ⟨a, hb, rfl⟩ := hk
    exact ⟨a, hb, refs_read keys aux hread a ho⟩
  rcases hn with hn | hn
  · obtain ⟨k, hk, ho⟩ := related_occ hTrel hn
    exact found tT _ hTread k hk ho
  · obtain ⟨k, hk, ho⟩ := related_occ hVrel hn
    exact found tV _ hVread k hk ho

/--
info: 'Ix.Cert.BlockRefs.mentioned_binding_ref' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mentioned_binding_ref
end Ix.Cert.BlockRefs
