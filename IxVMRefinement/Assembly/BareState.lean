import IxVMRefinement.Assembly.InductiveRead
import IxC.Kernel.Verify.Frontend.InModelMemo

/-! # Definition reading after removing generated declarations

Raw expression reading introduces no free variables. Its reducibility heights therefore
depend only on the actual constant keys it reads. A successful definition lowering that did
not rewrite a projection can be replayed with empty projection levels and those same heights.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (RolesKeyed)

theorem convExpr_noFvar {md : Mode} {ecx : ECx md}
    {tbl : Array (ReadM (CExpr md))}
    (htbl : ∀ m ∈ tbl.toList, ∀ e, m = .ok e → e.hasFvar = false) :
    ∀ (ie : Ixon.Expr) {e : CExpr md}, convExpr ecx tbl ie = .ok e → e.hasFvar = false
  | .var i, e, h => by
    simp only [convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst e
    rw [Expr.mkBvar_eq]
    rfl
  | .sort i, e, h => by
    simp only [convExpr] at h
    obtain ⟨l, _, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst e
    rfl
  | .ref i us, e, h => by
    simp only [convExpr] at h
    obtain ⟨k, _, h⟩ := except_bind_ok.mp h
    obtain ⟨ls, _, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst e
    rfl
  | .recur i us, e, h => by
    simp only [convExpr] at h
    cases hs : ecx.self i.toNat with
    | none => simp [hs, malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some m =>
      simp only [hs] at h
      obtain ⟨k, _, h⟩ := except_bind_ok.mp h
      obtain ⟨ls, _, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst e
      rfl
  | .prj i field v, e, h => by
    simp only [convExpr] at h
    obtain ⟨k, _, h⟩ := except_bind_ok.mp h
    obtain ⟨ev, hv, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst e
    change ev.hasFvar = false
    exact convExpr_noFvar htbl v hv
  | .str i, e, h => by
    simp only [convExpr] at h
    obtain ⟨bytes, _, h⟩ := except_bind_ok.mp h
    cases hs : String.fromUTF8? bytes with
    | none => simp [hs, malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some s =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      subst e
      rfl
  | .nat i, e, h => by
    simp only [convExpr] at h
    obtain ⟨n, _, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst e
    rfl
  | .app f a, e, h => by
    simp only [convExpr] at h
    obtain ⟨ef, hf, h⟩ := except_bind_ok.mp h
    obtain ⟨ea, ha, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst e
    simp only [Expr.hasFvar, convExpr_noFvar htbl f hf, convExpr_noFvar htbl a ha,
      Bool.or_self]
  | .lam t b, e, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst e
    simp only [Expr.hasFvar, convExpr_noFvar htbl t ht, convExpr_noFvar htbl b hb,
      Bool.or_self]
  | .all t b, e, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst e
    simp only [Expr.hasFvar, convExpr_noFvar htbl t ht, convExpr_noFvar htbl b hb,
      Bool.or_self]
  | .letE nonDep kind t v b, e, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨ev, hv, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst e
    simp only [Expr.hasFvar, convExpr_noFvar htbl t ht, convExpr_noFvar htbl v hv,
      convExpr_noFvar htbl b hb, Bool.or_self]
  | .share i, e, h => by
    simp only [convExpr] at h
    cases hget : tbl[i.toNat]? with
    | none => simp [hget, malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some r =>
      simp only [hget] at h
      exact htbl r (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget)) e h

theorem memberReader_read_noFvar {md : Mode} {cx : Ctx md}
    {src : Ixon.Constant} {param : Nat → LevelParam}
    {self : Nat → Option (ReadM (CName md))} {ie : Ixon.Expr} {e : CExpr md}
    (h : (MemberReader.mk' cx src param self).read ie = .ok e) : e.hasFvar = false := by
  let ecx : ECx md := ⟨cx, src, src.univs.map (convUniv param), self⟩
  have htbl_fold :
      ∀ (entries : List Ixon.Expr) (tbl : Array (ReadM (CExpr md))),
        (∀ m ∈ tbl.toList, ∀ e', m = .ok e' → e'.hasFvar = false) →
        ∀ m ∈ (entries.foldl (fun acc entry => acc.push (convExpr ecx acc entry)) tbl).toList,
          ∀ e', m = .ok e' → e'.hasFvar = false := by
    intro entries
    induction entries with
    | nil => intro tbl hI; exact hI
    | cons entry rest ih =>
      intro tbl hI
      refine ih (tbl.push (convExpr ecx tbl entry)) fun m hm e' he' => ?_
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hI m hm e' he'
      · exact convExpr_noFvar hI entry he'
  have hmk :
      (MemberReader.mk' cx src param self).ecx = ecx ∧
      (MemberReader.mk' cx src param self).tbl =
        src.sharing.toList.foldl (fun acc entry => acc.push (convExpr ecx acc entry)) #[] := by
    simp [MemberReader.mk', ecx, Array.forIn_pure_yield_eq_foldl, Array.mkEmpty,
      ← Array.foldl_toList]
  unfold MemberReader.read at h
  rw [hmk.1, hmk.2] at h
  exact convExpr_noFvar (htbl_fold src.sharing.toList #[] (fun _ hm => nomatch hm)) ie h

theorem maxHeight_eq_of_refs {md : Mode} {K : Key md → Prop}
    {heights heights' : Key md → Nat} (hh : ∀ k, K k → heights' k = heights k)
    {e : Expr md} (hrefs : e.RefsIn K) (hfree : e.hasFvar = false) :
    Frontend.InModel.maxHeight heights' e = Frontend.InModel.maxHeight heights e := by
  rw [Frontend.InModel.maxHeight_eq, Frontend.InModel.maxHeight_eq]
  induction e with
  | const k us => exact hh k hrefs
  | _ => simp_all [Expr.RefsIn, Expr.hasFvar, Frontend.InModel.maxHeightP]

theorem memberReader_hintFor_eq {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {src : Ixon.Constant} {param : Nat → LevelParam}
    {self : Nat → Option (ReadM (CName md))}
    (hself : ∀ i m k, self i = some m → m = .ok k → NonAuxKey k)
    {heights heights' : Key md → Nat}
    (hh : ∀ k, NonAuxKey k → heights' k = heights k)
    {ie : Ixon.Expr} {e : CExpr md}
    (h : (MemberReader.mk' cx src param self).read ie = .ok e) :
    Frontend.InModel.hintFor heights' e = Frontend.InModel.hintFor heights e := by
  unfold Frontend.InModel.hintFor
  rw [maxHeight_eq_of_refs hh (memberReader_read_refsIn_nonAux hrk hself h)
    (memberReader_read_noFvar h)]

/-- With no observed projection rewrite, definition lowering only reads the original
value and its reducibility height. Empty projection levels preserve that actual output. -/
theorem lowerDefinition_without_rewrite {md : Mode}
    {hint : Option ReducibilityHint} {source target : State md}
    {heights heights' : CName md → Nat} {cv : CVal md} {value : CExpr md}
    {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {decl : CDecl md}
    (h : lowerDefinition hint source heights cv value kind safety = .ok (decl, false))
    (hempty : ∀ k : CName md, target.projLevels[k]? = none)
    (hheight : Frontend.InModel.hintFor heights' value = Frontend.InModel.hintFor heights value) :
    lowerDefinition hint target heights' cv value kind safety = .ok (decl, false) := by
  unfold lowerDefinition at h ⊢
  rw [projRewrite_eq_none hempty cv value]
  cases hsafety : safetyDeclineOf kind safety with
  | some why => simp [hsafety, declined, throw, throwThe, MonadExceptOf.throw] at h
  | none =>
    simp only [hsafety] at h ⊢
    cases kind <;> cases hrewrite : projRewrite source cv value <;>
      simp_all [pure, Except.pure]
    all_goals
      have hbad : (true : Bool) = false := h.2
      cases hbad

theorem readDefinition_without_rewrite {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {source target : State md} {heights heights' : CName md → Nat}
    {ref : ConstRef _root_.Address} {lps : List LevelParam}
    {src : Ixon.Constant} {param : Nat → LevelParam}
    {self : Nat → Option (ReadM (CName md))}
    (hself : ∀ i m k, self i = some m → m = .ok k → NonAuxKey k)
    (hh : ∀ k, NonAuxKey k → heights' k = heights k)
    (hempty : ∀ k : CName md, target.projLevels[k]? = none)
    {d : Ixon.Definition} {decl : CDecl md}
    (h : readDefinition cx source heights ref lps (MemberReader.mk' cx src param self) d =
      .ok (decl, false)) :
    readDefinition cx target heights' ref lps (MemberReader.mk' cx src param self) d =
      .ok (decl, false) := by
  unfold readDefinition at h ⊢
  obtain ⟨name, hname, h⟩ := except_bind_ok.mp h
  obtain ⟨ty, hty, h⟩ := except_bind_ok.mp h
  obtain ⟨val, hval, h⟩ := except_bind_ok.mp h
  rw [hname]
  dsimp only [bind, Except.bind]
  rw [hty]
  dsimp only [bind, Except.bind]
  rw [hval]
  dsimp only [bind, Except.bind]
  exact lowerDefinition_without_rewrite h hempty (memberReader_hintFor_eq hrk hself hh hval)

private theorem fold_insert_agrees_at {md : Mode} {α β : Type}
    (g : α → Option (Key md × β)) (k : Key md) :
    ∀ (xs : List α) (left right : Std.HashMap (Key md) β),
      left[k]? = right[k]? →
      (xs.foldl (Ix.Cert.CtxAgree.insOpt g) left)[k]? =
        (xs.foldl (Ix.Cert.CtxAgree.insOpt g) right)[k]?
  | [], _, _, h => h
  | x :: xs, left, right, h => by
    simp only [List.foldl_cons]
    apply fold_insert_agrees_at g k xs
    unfold Ix.Cert.CtxAgree.insOpt
    cases g x with
    | none => exact h
    | some pair => simp only [Std.HashMap.getElem?_insert, h]

private theorem fold_insert_unchanged_at {md : Mode} {α β : Type}
    (g : α → Option (Key md × β)) (k : Key md) :
    ∀ (xs : List α) (table : Std.HashMap (Key md) β),
      (∀ x ∈ xs, ∀ pair, g x = some pair → pair.1 ≠ k) →
      (xs.foldl (Ix.Cert.CtxAgree.insOpt g) table)[k]? = table[k]?
  | [], _, _ => rfl
  | x :: xs, table, h => by
    rw [List.foldl_cons, fold_insert_unchanged_at g k xs _
      (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    unfold Ix.Cert.CtxAgree.insOpt
    cases hx : g x with
    | none => rfl
    | some pair => simp [Std.HashMap.getElem?_insert, h x List.mem_cons_self pair hx]

private theorem generated_noteEntry_aux {md : Mode} {d : CDecl md}
    (hg : d.isGenerated = true) {e : Ix.Cert.CtxAgree.Entry md}
    (he : e ∈ Ix.Cert.CtxAgree.noteEntries d) : e.1.isAux = true := by
  have hname : e.1 ∈ d.names := by
    cases d with
    | basisDecl kind => simp [Declaration.isGenerated, Declaration.names] at hg
    | indDecl block nP =>
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp he
      exact List.mem_map.mpr ⟨ci, hci, rfl⟩
    | _ =>
      simp only [Ix.Cert.CtxAgree.noteEntries, List.mem_singleton] at he
      subst e
      exact List.mem_cons_self
  simp only [Declaration.isGenerated, Bool.and_eq_true] at hg
  exact List.all_eq_true.mp hg.2 e.1 hname

/-- Removing a generated declaration prefix preserves every public constant's height
after committing the common bare suffix. No reader-state equality is assumed. -/
theorem commit_heights_after_generated_prefix {md : Mode}
    {source target : State md} {full bare : Read md} {generated : List (CDecl md)}
    (hdecls : full.decls.toList = generated ++ bare.decls.toList)
    (hgenerated : ∀ d ∈ generated, d.isGenerated = true)
    (hheight : ∀ (k : CName md), NonAuxKey k → target.heights[k]? = source.heights[k]?) :
    ∀ (k : CName md), NonAuxKey k → (target.commit bare).heights[k]? = (source.commit full).heights[k]? := by
  intro k hk
  rw [Ix.Cert.CtxAgree.commit_heights, Ix.Cert.CtxAgree.commit_heights, hdecls,
    List.flatMap_append, List.foldl_append]
  apply fold_insert_agrees_at Ix.Cert.CtxAgree.htOf k
  rw [fold_insert_unchanged_at Ix.Cert.CtxAgree.htOf k _ _ ?_]
  · exact hheight k hk
  · intro e he pair hp heq
    obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
    have heaux := generated_noteEntry_aux (hgenerated d hd) he
    unfold Ix.Cert.CtxAgree.htOf at hp
    cases hh : e.2.2.2 with
    | none => simp [hh] at hp
    | some n =>
      simp only [hh, Option.map_some, Option.some.injEq] at hp
      subst pair
      dsimp only at heq
      rw [heq, (isAux_eq_false_iff.mpr hk)] at heaux
      cases heaux

/-- A singleton definition whose successful full read did not rewrite a projection has
the same concrete bare output after generated prefixes have been removed from the state. -/
theorem readRecord_defn_without_rewrite {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {source target : State md} {owner : _root_.Address} {c : Ixon.Constant}
    {defn : Ixon.Definition} {full : Read md}
    (hinfo : c.info = .defn defn)
    (h : readRecord cx source owner c = .ok full) (hzero : full.projRewrites = 0)
    (hh : ∀ (k : CName md), NonAuxKey k → target.heights[k]? = source.heights[k]?)
    (hempty : ∀ (k : CName md), target.projLevels[k]? = none) :
    readRecordBare cx target owner c = .ok full := by
  unfold readRecord at h
  simp only [hinfo] at h
  obtain ⟨⟨decl, rewrote⟩, hdef, h⟩ := except_bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst full
  cases rewrote with
  | true => simp at hzero
  | false =>
    have hdef' := readDefinition_without_rewrite
      (target := target) (heights' := fun k => target.heights.getD k 0) hrk
      (by
        intro i m k hs hm
        split at hs
        · injection hs with hs
          rw [← hs] at hm
          exact memberKey_nonAux hrk hm
        · cases hs)
      (by
        intro k hk
        simp only [Std.HashMap.getD_eq_getD_getElem?, hh k hk]) hempty hdef
    simp only [readRecordBare, hinfo, readRecord, hdef', bind, Except.bind,
      pure, Except.pure]

end IxVM.Refinement.Assembly
