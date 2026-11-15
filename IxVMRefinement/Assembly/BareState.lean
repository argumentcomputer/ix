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
  simp only [bind, Except.bind]
  rw [hty]
  simp only [bind, Except.bind]
  rw [hval]
  simp only [bind, Except.bind]
  exact lowerDefinition_without_rewrite h hempty (memberReader_hintFor_eq hrk hself hh hval)

end IxVM.Refinement.Assembly
