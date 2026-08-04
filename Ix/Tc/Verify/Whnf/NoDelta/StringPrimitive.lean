import Ix.Tc.Verify.Whnf.NoDelta.ProjectionApplication

/-!
# String primitive no-delta field

`tryReduceString` has three successful forms: an interned UTF-8 byte count,
the canonical empty byte array, or an interned `Char.ofNat` application for
`String.back`.  The helper has no recursive method-table edge and no lazy
environment lookup.

This slice proves its complete state behavior from finite support for those
exact generated nodes.  Theory computation remains a deliberately narrow
reflection boundary indexed by an observed successful production run.
-/

namespace Ix.Tc

/-- Finite generated-node support for the String reducer.

Every premise is scoped to a supported source and the exact production
classifier equations.  Thus the obligation remains finite even though
String and Nat are infinite datatypes. -/
structure StringReductionSupport (support : RunSupport) : Prop where
  utf8 : ∀ {source head : KExpr .anon} {args : Array (KExpr .anon)}
      {id : KId .anon} {us : Array (KUniv .anon)}
      {headInfo : ExprInfo .anon} {value : String} {blob : Address}
      {stringInfo : ExprInfo .anon} {prims : Primitives .anon},
    support source →
    source.collectSpine = (head, args) →
    head = .const id us headInfo →
    (args.size != 1) = false →
    args[0]! = .str value blob stringInfo →
    prims.CanonicalAnon →
    (id.addr == prims.stringUtf8ByteSize.addr) = true →
    support (RecM.natExprFromValue value.utf8ByteSize)
  emptyByteArray : ∀ {source head : KExpr .anon}
      {args : Array (KExpr .anon)} {id : KId .anon}
      {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
      {value : String} {blob : Address} {stringInfo : ExprInfo .anon}
      {prims : Primitives .anon},
    support source →
    source.collectSpine = (head, args) →
    head = .const id us headInfo →
    (args.size != 1) = false →
    args[0]! = .str value blob stringInfo →
    prims.CanonicalAnon →
    (id.addr == prims.stringToByteArray.addr) = true →
    value.isEmpty = true →
    support (KExpr.mkConst prims.byteArrayEmpty #[])
  back : ∀ {source head : KExpr .anon} {args : Array (KExpr .anon)}
      {id : KId .anon} {us : Array (KUniv .anon)}
      {headInfo : ExprInfo .anon} {value : String} {blob : Address}
      {stringInfo : ExprInfo .anon} {prims : Primitives .anon},
    support source →
    source.collectSpine = (head, args) →
    head = .const id us headInfo →
    (args.size != 1) = false →
    args[0]! = .str value blob stringInfo →
    prims.CanonicalAnon →
    (id.addr == prims.stringBack.addr ||
      id.addr == prims.stringLegacyBack.addr) = true →
    (id.addr == prims.stringUtf8ByteSize.addr) = false →
    (id.addr == prims.stringToByteArray.addr) = false →
    let codepoint := (value.toList.getLast?.map (·.toNat)).getD 65
    let charHead := KExpr.mkConst prims.charOfNat #[]
    let natLit := RecM.natExprFromValue codepoint
    support charHead ∧ support natLit ∧
      support (KExpr.mkApp charHead natLit)

/-- Semantic authority for an observed successful String primitive
reduction.  It contributes no state claim; StringPrimitive proves state preservation
for hits, misses, and all intermediate intern operations directly. -/
structure StringReductionReflection (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  success : ∀ {uvars : Nat} {Delta : KVLCtx}
      {methods : Methods .anon} {source result : KExpr .anon}
      {sourceV : Lean4Lean.VExpr} {s sf : TcState .anon},
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
    (RecM.tryReduceString source).run methods s =
      .ok (some result) sf →
    WhnfMeaning trProj world uvars Delta source result

namespace RecM

set_option maxHeartbeats 800000

/-- State and generated-result closure of the production String helper. -/
theorem tryReduceString_inv_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (collision : support.CollisionFree)
    (generated : StringReductionSupport support)
    {uvars : Nat} {Delta : KVLCtx} {source : KExpr .anon}
    {s : TcState .anon}
    (hsourceSupport : support source) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceString source)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced) := by
  unfold tryReduceString
  generalize hspine : source.collectSpine = spine
  rcases spine with ⟨head, args⟩
  cases hsize : args.size != 1 with
  | true =>
      simp only [hsize, if_true]
      exact RecM.WF.pure fun _ => trivial
  | false =>
      simp only [hsize, Bool.false_eq_true, if_false]
      cases head with
      | const id us headInfo =>
          simp only [pure_bind]
          apply RecM.WF.bind (RecM.WF.withInv (prims_wf (s := s)))
          intro prims afterRead hread
          rcases hread with ⟨hIRead, hprims, hafterRead⟩
          subst afterRead
          have hcanonical : prims.CanonicalAnon := by
            rw [hprims]
            exact hIRead.noAccel_primitives
          cases hguard :
              (!(id.addr == prims.stringBack.addr ||
                  id.addr == prims.stringLegacyBack.addr) &&
                !(id.addr == prims.stringUtf8ByteSize.addr) &&
                !(id.addr == prims.stringToByteArray.addr)) with
          | true =>
              simp only [if_true]
              exact RecM.WF.pure fun _ => trivial
          | false =>
              simp only [Bool.false_eq_true, if_false]
              cases harg : args[0]! with
              | str value blob stringInfo =>
                  unfold tryReduceStringLiteral
                  simp only
                  cases hutf8 :
                      (id.addr == prims.stringUtf8ByteSize.addr) with
                  | true =>
                      simp only [if_true]
                      let requested : KExpr .anon :=
                        natExprFromValue value.utf8ByteSize
                      have hrequested : support requested := by
                        apply generated.utf8 hsourceSupport hspine rfl hsize
                          harg
                        · exact hcanonical
                        · exact hutf8
                      apply RecM.WF.bind <| RecM.WF.liftTcM <|
                        TcM.intern_whnf_wf collision hrequested
                      intro interned afterIntern hintern
                      have hinterned : interned = requested := hintern.1
                      subst interned
                      exact RecM.WF.pure fun _ => hrequested
                  | false =>
                      simp only [Bool.false_eq_true, if_false]
                      cases hbytes :
                          (id.addr == prims.stringToByteArray.addr) with
                      | true =>
                          simp only [if_true]
                          cases hempty : value.isEmpty with
                          | true =>
                              simp only [if_true, pure_bind]
                              let requested : KExpr .anon :=
                                KExpr.mkConst prims.byteArrayEmpty #[]
                              have hrequested : support requested := by
                                apply generated.emptyByteArray hsourceSupport
                                  hspine rfl hsize harg
                                · exact hcanonical
                                · exact hbytes
                                · exact hempty
                              apply RecM.WF.bind <| RecM.WF.liftTcM <|
                                TcM.intern_whnf_wf collision hrequested
                              intro interned afterIntern hintern
                              have hinterned : interned = requested :=
                                hintern.1
                              subst interned
                              exact RecM.WF.pure fun _ => hrequested
                          | false =>
                              simp only [Bool.false_eq_true, if_false]
                              exact RecM.WF.pure fun _ => trivial
                      | false =>
                          simp only [Bool.false_eq_true, if_false, pure_bind]
                          have hback :
                              (id.addr == prims.stringBack.addr ||
                                id.addr ==
                                  prims.stringLegacyBack.addr) = true := by
                            cases hb :
                                (id.addr == prims.stringBack.addr ||
                                  id.addr ==
                                    prims.stringLegacyBack.addr) with
                            | false =>
                                simp [hb, hutf8, hbytes] at hguard
                            | true => rfl
                          let codepoint :=
                            (value.toList.getLast?.map (·.toNat)).getD 65
                          let charHead : KExpr .anon :=
                            KExpr.mkConst prims.charOfNat #[]
                          let natLit : KExpr .anon :=
                            natExprFromValue codepoint
                          let result : KExpr .anon :=
                            KExpr.mkApp charHead natLit
                          have hgenerated :=
                            generated.back hsourceSupport hspine rfl hsize
                              harg hcanonical
                              hback hutf8 hbytes
                          have hcharHead : support charHead := by
                            simpa [codepoint, charHead, natLit, result] using
                              hgenerated.1
                          have hnatLit : support natLit := by
                            simpa [codepoint, charHead, natLit, result] using
                              hgenerated.2.1
                          have hresult : support result := by
                            simpa [codepoint, charHead, natLit, result] using
                              hgenerated.2.2
                          unfold charOfNatExpr
                          apply RecM.WF.bind (prims_wf (s := s))
                          intro innerPrims afterInnerRead hinnerRead
                          rcases hinnerRead with
                            ⟨hinnerPrims, hafterInnerRead⟩
                          subst afterInnerRead
                          have hinnerEq : innerPrims = prims :=
                            hinnerPrims.trans hprims.symm
                          subst innerPrims
                          rw [hinnerEq]
                          apply RecM.WF.bind <| RecM.WF.liftTcM <|
                            TcM.intern_whnf_wf collision hcharHead
                          intro actualHead afterHead hactualHead
                          have hactualHeadEq : actualHead = charHead :=
                            hactualHead.1
                          subst actualHead
                          apply RecM.WF.bind <| RecM.WF.liftTcM <|
                            TcM.intern_whnf_wf collision hnatLit
                          intro actualNat afterNat hactualNat
                          have hactualNatEq : actualNat = natLit :=
                            hactualNat.1
                          subst actualNat
                          apply RecM.WF.bind <| RecM.WF.liftTcM <|
                            TcM.intern_whnf_wf collision hresult
                          intro actualResult afterResult hactualResult
                          have hactualResultEq : actualResult = result :=
                            hactualResult.1
                          subst actualResult
                          exact RecM.WF.pure fun _ => hresult
              | var | fvar | sort | const | app | lam | all | letE | prj |
                    nat =>
                  simp only
                  exact RecM.WF.pure fun _ => trivial
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          simp only [pure_bind]
          exact RecM.WF.pure fun _ => trivial

/-- Complete optional-reducer field: operational closure comes from the
finite generated-node support, while only a successful hit consults the
String Theory reflection boundary. -/
theorem tryReduceString_optional_wf_of_reflection
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (collision : support.CollisionFree)
    (generated : StringReductionSupport support)
    (reflection : StringReductionReflection semantics trProj world support) :
    OptionalReduction.WF .noAccel semantics trProj world support
      tryReduceString := by
  intro uvars Delta source sourceV s hsourceSupport hsource
  have hstate :=
    tryReduceString_inv_wf (semantics := semantics) (trProj := trProj)
      (world := world) collision generated
      (uvars := uvars) (Delta := Delta) (s := s) hsourceSupport
  intro methods hmethods hI
  have hpost := hstate methods hmethods hI
  match hrun : (tryReduceString source).run methods s with
  | .error err sf =>
      rw [hrun] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok none sf =>
      rw [hrun] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok (some result) sf =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2,
        reflection.success hmethods hsourceSupport hsource hI hrun⟩

end RecM
end Ix.Tc
