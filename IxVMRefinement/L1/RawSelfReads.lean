import IxVMRefinement.L1.ConvertExpr
import Ix.CompileCert.Loop

/-! # Self callbacks reached by an actual raw expression

Only a recursive-reference leaf reached from the root expression or one of its sharing
entries can affect the reader's result. Unused block members and unused sharing entries
therefore require no self-callback agreement for this conversion.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open Ix.Kernel.Reader

/-- A recursive-reference index reached by this expression, following its actual sharing table. -/
inductive RecurUsed (sharing : List Ixon.Expr) : Nat → Ixon.Expr → Prop where
  | recur {index : UInt64} {levels : Array UInt64} : RecurUsed sharing index.toNat (.recur index levels)
  | prj {index field inner i} : RecurUsed sharing i inner → RecurUsed sharing i (.prj index field inner)
  | appFn {fnPart arg i} : RecurUsed sharing i fnPart → RecurUsed sharing i (.app fnPart arg)
  | appArg {fnPart arg i} : RecurUsed sharing i arg → RecurUsed sharing i (.app fnPart arg)
  | lamType {domain body i} : RecurUsed sharing i domain → RecurUsed sharing i (.lam domain body)
  | lamBody {domain body i} : RecurUsed sharing i body → RecurUsed sharing i (.lam domain body)
  | allType {domain body i} : RecurUsed sharing i domain → RecurUsed sharing i (.all domain body)
  | allBody {domain body i} : RecurUsed sharing i body → RecurUsed sharing i (.all domain body)
  | letType {nondep mode domain value body i} :
      RecurUsed sharing i domain → RecurUsed sharing i (.letE nondep mode domain value body)
  | letValue {nondep mode domain value body i} :
      RecurUsed sharing i value → RecurUsed sharing i (.letE nondep mode domain value body)
  | letBody {nondep mode domain value body i} :
      RecurUsed sharing i body → RecurUsed sharing i (.letE nondep mode domain value body)
  | share {index : UInt64} {source : Ixon.Expr} {i : Nat} : sharing[index.toNat]? = some source →
      RecurUsed sharing i source → RecurUsed sharing i (.share index)

/-- Each reached recursive reference has its actual conversion address. -/
theorem RawConvExpr.recur_used_address {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {heap : Heap F} {bound : Nat} {expression : Ixon.Expr} {pointer : SourceValue F}
    (raw : RawConvExpr refs recurAddrs univs sharing blobs heap bound expression pointer) :
    ∀ {index}, RecurUsed sharing index expression → ∃ address, recurAddrs[index]? = some address := by
  induction raw with
  | var _ _ | sort _ _ _ _ | ref _ _ _ _ _ _ _ | str _ _ _ _ _ _ | nat _ _ _ _ _ _ _ _ => intro index used; cases used
  | recur _ found _ _ _ _ _ => intro index used; cases used; exact ⟨_, found⟩
  | prj _ _ _ _ _ _ _ ih => intro index used; cases used with | prj used => exact ih used
  | app _ _ _ fnPart arg =>
    intro index used
    cases used with
    | appFn used => exact fnPart used
    | appArg used => exact arg used
  | lam _ _ _ _ domain body =>
    intro index used
    cases used with
    | lamType used => exact domain used
    | lamBody used => exact body used
  | all _ _ _ _ domain body =>
    intro index used
    cases used with
    | allType used => exact domain used
    | allBody used => exact body used
  | letE _ _ _ _ domain value body =>
    intro index used
    cases used with
    | letType used => exact domain used
    | letValue used => exact value used
    | letBody used => exact body used
  | share _ found _ ih =>
    intro index used
    cases used with
    | share actual used =>
      have same := Option.some.inj (actual.symm.trans found)
      cases same
      exact ih used

/-- Successful reader self callbacks need agree only at reached recursive-reference leaves.
The raw sharing derivation supplies the decreasing indices used to replay cached entries. -/
theorem RawConvExpr.memberReader_self_mono
    {cx : Ctx .anon} {source : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {self₁ self₂ : Nat → Option (ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {heap : Heap F} {expression : Ixon.Expr} {pointer : SourceValue F} {readExpr : Core.KExpr}
    (raw : RawConvExpr source.refs.toList recurAddrs source.univs.toList source.sharing.toList blobs
      heap 4294967295 expression pointer)
    (agreement : ∀ index, RecurUsed source.sharing.toList index expression →
      ∀ key, self₁ index = some (.ok key) → self₂ index = some (.ok key))
    (read : (MemberReader.mk' cx source param self₁).read expression = .ok readExpr) :
    (MemberReader.mk' cx source param self₂).read expression = .ok readExpr := by
  obtain ⟨context₁, table₁⟩ := memberReader_mk'_eq cx source param self₁
  obtain ⟨context₂, table₂⟩ := memberReader_mk'_eq cx source param self₂
  unfold MemberReader.read at read ⊢
  rw [context₁, table₁, ← List.take_length (l := source.sharing.toList)] at read
  rw [context₂, table₂, ← List.take_length (l := source.sharing.toList)]
  let ecx₁ : ECx .anon := ⟨cx, source, source.univs.map (convUniv param), self₁⟩
  let ecx₂ : ECx .anon := ⟨cx, source, source.univs.map (convUniv param), self₂⟩
  have go : ∀ {bound : Nat} {expression : Ixon.Expr} {pointer : SourceValue F},
      RawConvExpr source.refs.toList recurAddrs source.univs.toList source.sharing.toList blobs
        heap bound expression pointer →
      (∀ index, RecurUsed source.sharing.toList index expression →
        ∀ key, self₁ index = some (.ok key) → self₂ index = some (.ok key)) →
      ∀ {n : Nat} {result : Core.KExpr}, n ≤ source.sharing.toList.length →
        (bound ≤ n ∨ n = source.sharing.toList.length) →
        convExpr ecx₁ (buildShareTbl ecx₁ (source.sharing.toList.take n)) expression = .ok result →
        convExpr ecx₂ (buildShareTbl ecx₂ (source.sharing.toList.take n)) expression = .ok result := by
    intro bound expression pointer converted
    induction converted with
    | var _ _ | sort _ _ _ _ | ref _ _ _ _ _ _ _ | str _ _ _ _ _ _ | nat _ _ _ _ _ _ _ _ => intro _ _ _ _ _ success; exact success
    | @recur _ _ index levels _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro agrees n result _ _ success
      simp only [convExpr] at success ⊢
      cases selfRead : ecx₁.self index.toNat with
      | none => simp [selfRead, malformed, throw] at success
      | some computation =>
        simp only [selfRead] at success
        obtain ⟨key, computed, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
        have original : self₁ index.toNat = some (.ok key) := by
          change self₁ index.toNat = some computation at selfRead
          rwa [computed] at selfRead
        have transferred : ecx₂.self index.toNat = some (.ok key) := agrees _ .recur key original
        rw [transferred]
        exact success
    | prj _ _ _ _ _ _ _ ih =>
      intro agrees n result within enough success
      simp only [convExpr] at success ⊢
      obtain ⟨key, keyRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      obtain ⟨inner, innerRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      have transferred := ih (fun index used => agrees index (.prj used)) within enough innerRead
      rw [show ecx₂.keyAt _ = .ok key from keyRead, transferred]
      exact success
    | app _ _ _ fnPart arg =>
      intro agrees n result within enough success
      simp only [convExpr] at success ⊢
      obtain ⟨fnExpr, fnRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      obtain ⟨argExpr, argRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      rw [fnPart (fun index used => agrees index (.appFn used)) within enough fnRead,
        arg (fun index used => agrees index (.appArg used)) within enough argRead]
      exact success
    | lam _ _ _ _ domain body =>
      intro agrees n result within enough success
      simp only [convExpr] at success ⊢
      obtain ⟨typeExpr, typeRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      obtain ⟨bodyExpr, bodyRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      rw [domain (fun index used => agrees index (.lamType used)) within enough typeRead,
        body (fun index used => agrees index (.lamBody used)) within enough bodyRead]
      exact success
    | all _ _ _ _ domain body =>
      intro agrees n result within enough success
      simp only [convExpr] at success ⊢
      obtain ⟨typeExpr, typeRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      obtain ⟨bodyExpr, bodyRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      rw [domain (fun index used => agrees index (.allType used)) within enough typeRead,
        body (fun index used => agrees index (.allBody used)) within enough bodyRead]
      exact success
    | letE _ _ _ _ domain value body =>
      intro agrees n result within enough success
      simp only [convExpr] at success ⊢
      obtain ⟨typeExpr, typeRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      obtain ⟨valueExpr, valueRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      obtain ⟨bodyExpr, bodyRead, success⟩ := Ix.CompileCert.Loop.except_bind_ok.mp success
      rw [domain (fun index used => agrees index (.letType used)) within enough typeRead,
        value (fun index used => agrees index (.letValue used)) within enough valueRead,
        body (fun index used => agrees index (.letBody used)) within enough bodyRead]
      exact success
    | @share bound index entry _ indexBound found _ ih =>
      intro agrees n result within enough success
      have inside : index.toNat < source.sharing.toList.length :=
        (List.getElem?_eq_some_iff.mp found).1
      have before : index.toNat < n := by rcases enough with enough | rfl <;> omega
      simp only [convExpr] at success ⊢
      rw [buildShareTbl_take_getElem? ecx₁ source.sharing.toList before found] at success
      rw [buildShareTbl_take_getElem? ecx₂ source.sharing.toList before found]
      exact ih (fun i used => agrees i (.share found used)) (Nat.le_of_lt inside)
        (.inl (Nat.le_refl _)) success
  exact go raw agreement (Nat.le_refl _) (.inr rfl) read

/-- Exact conversion needs self-name agreement only for recursive references actually
reached by this root and its sharing entries. -/
theorem RawConvExpr.toTmCExact_of_selfReads {κ : _root_.Address → Core.KKey}
    {ps : List Ix.Kernel.LevelParam}
    (permutation : ps.Perm (List.range ps.length)) (paramsBound : ps.length < 4294967296)
    {cx : Ctx .anon} {source : Ixon.Constant}
    {self : Nat → Option (ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (keyAt : ∀ address key, cx.keyAt address = .ok key → key = κ address)
    {heap : Heap F} {expression : Ixon.Expr} {pointer : SourceValue F} {readExpr : Core.KExpr}
    (raw : RawConvExpr source.refs.toList recurAddrs source.univs.toList source.sharing.toList blobs
      heap 4294967295 expression pointer)
    (selfReads : ∀ index address computation key,
      RecurUsed source.sharing.toList index expression → recurAddrs[index]? = some address →
      self index = some computation → computation = .ok key → key = κ address)
    (blob : BlobReadAgreement cx.blob blobs)
    (read : (MemberReader.mk' cx source (recParam ps) self).read expression = .ok readExpr)
    (varsBounded : readExpr.looseBVarsBounded 0 = true)
    (levels : readExpr.allLevelParamsDefined ps = true) :
    ∃ annotated : Core.KExpr, IxVM.Consistency.Annotates annotated readExpr ∧
      Decl.TmCExact κ heap (Core.posOf ps annotated) pointer := by
  let canonicalSelf : Nat → Option (ReadM Core.KKey) :=
    fun index => recurAddrs[index]?.map fun address => .ok (κ address)
  have canonicalRead : (MemberReader.mk' cx source (recParam ps) canonicalSelf).read expression = .ok readExpr := by
    apply raw.memberReader_self_mono _ read
    intro index used key succeeded
    obtain ⟨address, found⟩ := raw.recur_used_address used
    have named := selfReads index address (.ok key) key used found succeeded rfl
    simp only [canonicalSelf, found, Option.map_some, named]
  apply raw.toTmCExact_of_blobAgreement permutation paramsBound keyAt (self := canonicalSelf) _ blob
    canonicalRead varsBounded levels
  intro index address computation key found selected succeeded
  have same : computation = .ok (κ address) := by
    simpa only [canonicalSelf, found, Option.map_some, Option.some.injEq] using selected.symm
  exact Except.ok.inj (succeeded.symm.trans same)


/-- A reached recursive reference retains its serialized UInt64 index bound. -/
theorem RecurUsed.index_lt {sharing : List Ixon.Expr} {index : Nat} {expression : Ixon.Expr}
    (used : RecurUsed sharing index expression) : index < UInt64.size := by
  induction used with
  | @recur index _ => exact index.toNat_lt
  | prj _ ih => exact ih
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

end IxVM.Refinement.L1
