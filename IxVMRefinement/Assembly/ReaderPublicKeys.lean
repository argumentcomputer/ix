import IxVMRefinement.Assembly.ReadBare

/-! # Public keys in decoded expressions

Successful expression conversion uses only role or identifier keys, including projection
targets and the support of literals. This strengthens ordinary reference traversal without
changing that traversal's treatment of projection targets.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel (ConstRef Mode)
open Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (throw_ok RolesKeyed)

theorem convExpr_publicKeys {md : Mode} {ecx : ECx md}
    (hrk : RolesKeyed ecx.cx)
    (hself : ∀ i m k, ecx.self i = some m → m = .ok k → NonAuxKey k)
    {tbl : Array (ReadM (CExpr md))}
    (htbl : ∀ m ∈ tbl.toList, ∀ e, m = .ok e → e.constsResolveBy (fun key => !key.isAux) = true) :
    ∀ (ie : Ixon.Expr) {e : CExpr md},
      convExpr ecx tbl ie = .ok e → e.constsResolveBy (fun key => !key.isAux) = true
  | .var i, e, h => by
    simp only [convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [Ix.Kernel.Expr.mkBvar_eq]
    rfl
  | .sort i, e, h => by
    simp only [convExpr] at h
    obtain ⟨l, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | .ref i us, e, h => by
    simp only [convExpr] at h
    obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
    obtain ⟨ls, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    unfold ECx.keyAt at hk
    split at hk
    · simp only [Ix.Kernel.Expr.constsResolveBy,
        isAux_eq_false_iff.mpr (keyAt_nonAux hrk hk), Bool.not_false]
    · exact (throw_ok hk).elim
  | .recur i us, e, h => by
    simp only [convExpr] at h
    cases hs : ecx.self i.toNat with
    | none => simp [hs, malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some m =>
      simp only [hs] at h
      obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
      obtain ⟨ls, -, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Ix.Kernel.Expr.constsResolveBy,
        isAux_eq_false_iff.mpr (hself i.toNat m k hs hk), Bool.not_false]
  | .prj i field v, e, h => by
    simp only [convExpr] at h
    obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
    obtain ⟨ev, hv, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have publicKey : k.isAux = false := by
      unfold ECx.keyAt at hk
      split at hk
      · exact isAux_eq_false_iff.mpr (keyAt_nonAux hrk hk)
      · exact (throw_ok hk).elim
    simp only [Ix.Kernel.Expr.constsResolveBy, publicKey, Bool.not_false, Bool.true_and]
    exact convExpr_publicKeys hrk hself htbl v hv
  | .str i, e, h => by
    simp only [convExpr] at h
    obtain ⟨bytes, -, h⟩ := except_bind_ok.mp h
    cases hs : String.fromUTF8? bytes with
    | none => simp [hs, malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some s =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      subst h
      rfl
  | .nat i, e, h => by
    simp only [convExpr] at h
    obtain ⟨n, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | .app f a, e, h => by
    simp only [convExpr] at h
    obtain ⟨ef, hf, h⟩ := except_bind_ok.mp h
    obtain ⟨ea, ha, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true]
    exact ⟨convExpr_publicKeys hrk hself htbl f hf,
      convExpr_publicKeys hrk hself htbl a ha⟩
  | .lam t b, e, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true]
    exact ⟨convExpr_publicKeys hrk hself htbl t ht,
      convExpr_publicKeys hrk hself htbl b hb⟩
  | .all t b, e, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true]
    exact ⟨convExpr_publicKeys hrk hself htbl t ht,
      convExpr_publicKeys hrk hself htbl b hb⟩
  | .letE nonDep _ t v b, e, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨ev, hv, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true]
    exact ⟨⟨convExpr_publicKeys hrk hself htbl t ht,
      convExpr_publicKeys hrk hself htbl v hv⟩,
      convExpr_publicKeys hrk hself htbl b hb⟩
  | .share i, e, h => by
    simp only [convExpr] at h
    cases hget : tbl[i.toNat]? with
    | none => simp [hget, malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some r =>
      simp only [hget] at h
      exact htbl r (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget)) e h

theorem memberReader_read_publicKeys {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (ReadM (CName md))}
    (hself : ∀ i m k, self i = some m → m = .ok k → NonAuxKey k)
    {ie : Ixon.Expr} {e : CExpr md}
    (h : (MemberReader.mk' cx src param self).read ie = .ok e) :
    e.constsResolveBy (fun key => !key.isAux) = true := by
  let ecx : ECx md := ⟨cx, src, src.univs.map (convUniv param), self⟩
  have htbl_fold :
      ∀ (entries : List Ixon.Expr) (tbl : Array (ReadM (CExpr md))),
        (∀ m ∈ tbl.toList, ∀ e', m = .ok e' → e'.constsResolveBy (fun key => !key.isAux) = true) →
        ∀ m ∈ (entries.foldl (fun acc entry => acc.push (convExpr ecx acc entry)) tbl).toList,
          ∀ e', m = .ok e' → e'.constsResolveBy (fun key => !key.isAux) = true := by
    intro entries
    induction entries with
    | nil => intro tbl hI; exact hI
    | cons entry rest ih =>
      intro tbl hI
      refine ih (tbl.push (convExpr ecx tbl entry)) fun m hm e' he' => ?_
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hI m hm e' he'
      · exact convExpr_publicKeys hrk hself hI entry he'
  have hmk :
      (MemberReader.mk' cx src param self).ecx = ecx ∧
      (MemberReader.mk' cx src param self).tbl =
        src.sharing.toList.foldl (fun acc entry => acc.push (convExpr ecx acc entry)) #[] := by
    simp [MemberReader.mk', ecx, Array.forIn_pure_yield_eq_foldl, Array.mkEmpty,
      ← Array.foldl_toList]
  unfold MemberReader.read at h
  rw [hmk.1, hmk.2] at h
  exact convExpr_publicKeys hrk hself
    (htbl_fold src.sharing.toList #[] (fun _ hm => nomatch hm)) ie h

/-- The raw type of a value declaration contains only public keys. -/
def ValueTypePublic {md : Mode} : CDecl md → Prop
  | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ =>
    cv.type.constsResolveBy (fun key => !key.isAux) = true
  | _ => True

/-- Definition lowering preserves its exact header, even when it rewrites the value. -/
theorem lowerDefinition_publicType {md : Mode}
    {hint : Option Ix.Kernel.ReducibilityHint} {st : State md} {heights : CName md → Nat}
    {cv : CVal md} {value : CExpr md} {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
    {decl : CDecl md} {rewritten : Bool}
    (publicType : cv.type.constsResolveBy (fun key => !key.isAux) = true)
    (read : lowerDefinition hint st heights cv value kind safety = .ok (decl, rewritten)) :
    ValueTypePublic decl := by
  unfold lowerDefinition at read
  dsimp only at read
  split at read
  · exact (Ix.Cert.ReaderUnits.fail_bind read).elim
  · cases kind <;>
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at read <;>
      obtain ⟨rfl, _⟩ := read <;> exact publicType

/-- Actual member conversion supplies the strong support of a definition's raw type. -/
theorem readDefinition_publicType {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {st : State md} {heights : CName md → Nat} {ref : ConstRef _root_.Address}
    {lps : List Ix.Kernel.LevelParam} {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (ReadM (CName md))}
    (hself : ∀ i m k, self i = some m → m = .ok k → NonAuxKey k)
    {d : Ixon.Definition} {decl : CDecl md} {rewritten : Bool}
    (read : readDefinition cx st heights ref lps (MemberReader.mk' cx src param self) d =
      .ok (decl, rewritten)) :
    ValueTypePublic decl := by
  unfold readDefinition at read
  obtain ⟨name, _, read⟩ := except_bind_ok.mp read
  obtain ⟨type, converted, read⟩ := except_bind_ok.mp read
  obtain ⟨value, _, read⟩ := except_bind_ok.mp read
  exact lowerDefinition_publicType (memberReader_read_publicKeys hrk hself converted) read

end IxVM.Refinement.Assembly
