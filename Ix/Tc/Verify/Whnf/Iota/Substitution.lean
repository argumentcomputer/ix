import Ix.Tc.Verify.Whnf.Iota.RuleSuffixTransport
import Ix.Tc.Verify.Totalization

/-!
# Transient iota substitution agrees with the verified spec

Production's Nat-literal iota path sets `transient = true` and beta-reduces
lambda intermediates with `substNoIntern`.  The existing semantic beta theorem
is phrased over `KExpr.substSpec`, because that is also the specification of
the ordinary memoized substitution walker.  The two implementations have the
same rebuilding arms, but `substNoIntern` adds `lbr` fast paths and uses its own
non-interning lift helper.

This slice proves those optimizations exact for constructed anonymous terms
under the same UInt64 bounds already required by the walker proofs.  It then
uses the equality to expose the production `applyIotaArg` transient-lambda
branch as the verified substitution spec and as a semantic beta reduction.
-/

namespace Ix.Tc

namespace KExpr

/-- The local non-interning lift used by `substNoIntern` computes the same
anonymous term as `liftSpec`.  `Constructed` makes the stored `lbr` metadata
coherent, and the cutoff/size premise prevents binder-depth wraparound in the
fast-path justification. -/
theorem Constructed.liftNoIntern_eq_liftSpec
    {e : KExpr .anon} {shift cutoff : UInt64}
    (hcon : Constructed e)
    (hcut : cutoff.toNat + e.size < UInt64.size) :
    substNoIntern.liftNoIntern e shift cutoff =
      KExpr.liftSpec e shift cutoff := by
  induction hcon generalizing cutoff with
  | @var idx name md hidx =>
    rw [mkVar_shape]
    rw [substNoIntern.liftNoIntern]
    split
    · rename_i hfast
      rcases Bool.or_eq_true_iff.mp hfast with hzero | hlbr
      · rw [eq_of_beq hzero]
        exact (liftSpec_zero (.var hidx) cutoff).symm
      · exact (liftSpec_id (.var hidx) hcut
          (of_decide_eq_true hlbr)).symm
    · rw [KExpr.liftSpec]
  | @fvar id name md =>
    rw [mkFVar_shape]
    simp only [substNoIntern.liftNoIntern, KExpr.liftSpec, KExpr.lbr,
      ite_self]
  | @sort u md =>
    rw [mkSort_shape]
    simp only [substNoIntern.liftNoIntern, KExpr.liftSpec, KExpr.lbr,
      ite_self]
  | @const id us md =>
    rw [mkConst_shape]
    simp only [substNoIntern.liftNoIntern, KExpr.liftSpec, KExpr.lbr,
      ite_self]
  | @app f a md hf ha ihf iha =>
    rw [mkApp_shape, size] at hcut
    rw [mkApp_shape]
    rw [substNoIntern.liftNoIntern]
    split
    · rename_i hfast
      rcases Bool.or_eq_true_iff.mp hfast with hzero | hlbr
      · rw [eq_of_beq hzero]
        exact (liftSpec_zero (.app hf ha) cutoff).symm
      · exact (liftSpec_id (.app hf ha) hcut
          (of_decide_eq_true hlbr)).symm
    · rw [KExpr.liftSpec,
        ihf (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut),
        iha (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut)]
  | @lam n bi ty body md hty hbody ihty ihbody =>
    rw [mkLam_shape, size] at hcut
    have hc1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLam_shape]
    rw [substNoIntern.liftNoIntern]
    split
    · rename_i hfast
      rcases Bool.or_eq_true_iff.mp hfast with hzero | hlbr
      · rw [eq_of_beq hzero]
        exact (liftSpec_zero (.lam hty hbody) cutoff).symm
      · exact (liftSpec_id (.lam hty hbody) hcut
          (of_decide_eq_true hlbr)).symm
    · rw [KExpr.liftSpec,
        ihty (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut),
        ihbody (cutoff := cutoff + 1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut)]
  | @all n bi ty body md hty hbody ihty ihbody =>
    rw [mkAll_shape, size] at hcut
    have hc1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkAll_shape]
    rw [substNoIntern.liftNoIntern]
    split
    · rename_i hfast
      rcases Bool.or_eq_true_iff.mp hfast with hzero | hlbr
      · rw [eq_of_beq hzero]
        exact (liftSpec_zero (.all hty hbody) cutoff).symm
      · exact (liftSpec_id (.all hty hbody) hcut
          (of_decide_eq_true hlbr)).symm
    · rw [KExpr.liftSpec,
        ihty (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut),
        ihbody (cutoff := cutoff + 1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut)]
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    rw [mkLet_shape, size] at hcut
    have hc1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLet_shape]
    rw [substNoIntern.liftNoIntern]
    split
    · rename_i hfast
      rcases Bool.or_eq_true_iff.mp hfast with hzero | hlbr
      · rw [eq_of_beq hzero]
        exact (liftSpec_zero (.letE hty hval hbody) cutoff).symm
      · exact (liftSpec_id (.letE hty hval hbody) hcut
          (of_decide_eq_true hlbr)).symm
    · rw [KExpr.liftSpec,
        ihty (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut),
        ihval (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut),
        ihbody (cutoff := cutoff + 1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut)]
  | @prj id field val md hval ihval =>
    rw [mkPrj_shape, size] at hcut
    rw [mkPrj_shape]
    rw [substNoIntern.liftNoIntern]
    split
    · rename_i hfast
      rcases Bool.or_eq_true_iff.mp hfast with hzero | hlbr
      · rw [eq_of_beq hzero]
        exact (liftSpec_zero (.prj hval) cutoff).symm
      · exact (liftSpec_id (.prj hval) hcut
          (of_decide_eq_true hlbr)).symm
    · rw [KExpr.liftSpec,
        ihval (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut)]
  | @nat v blob md =>
    rw [mkNat_shape]
    simp only [substNoIntern.liftNoIntern, KExpr.liftSpec, KExpr.lbr,
      ite_self]
  | @str v blob md =>
    rw [mkStr_shape]
    simp only [substNoIntern.liftNoIntern, KExpr.liftSpec, KExpr.lbr,
      ite_self]

/-- The complete non-interning substitution computes `substSpec`.  Its body
bound is the memoized walker's `depth + size` premise; its argument bound is
the same premise needed when a variable hit invokes the local lift above. -/
theorem Constructed.substNoIntern_eq_substSpec
    {body arg : KExpr .anon}
    (hbody : Constructed body) (harg : Constructed arg)
    {depth : UInt64}
    (hcut : depth.toNat + body.size < UInt64.size)
    (hargsz : arg.size < UInt64.size) :
    substNoIntern body arg depth =
      KExpr.substSpec body arg depth := by
  induction hbody generalizing depth with
  | @var idx name md hidx =>
    rw [mkVar_shape]
    rw [substNoIntern]
    split
    · rename_i hfast
      exact (substSpec_id (.var hidx) hcut hfast).symm
    · rw [KExpr.substSpec,
        harg.liftNoIntern_eq_liftSpec (shift := depth) (cutoff := 0)
          (by simpa using hargsz)]
  | @fvar id name md =>
    rw [mkFVar_shape]
    simp only [substNoIntern, KExpr.substSpec, KExpr.lbr, ite_self]
  | @sort u md =>
    rw [mkSort_shape]
    simp only [substNoIntern, KExpr.substSpec, KExpr.lbr, ite_self]
  | @const id us md =>
    rw [mkConst_shape]
    simp only [substNoIntern, KExpr.substSpec, KExpr.lbr, ite_self]
  | @app f a md hf ha ihf iha =>
    rw [mkApp_shape, size] at hcut
    rw [mkApp_shape]
    rw [substNoIntern]
    split
    · rename_i hfast
      exact (substSpec_id (.app hf ha) hcut hfast).symm
    · rw [KExpr.substSpec,
        ihf (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut),
        iha (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut)]
  | @lam n bi ty inner md hty hinner ihty ihinner =>
    rw [mkLam_shape, size] at hcut
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLam_shape]
    rw [substNoIntern]
    split
    · rename_i hfast
      exact (substSpec_id (.lam hty hinner) hcut hfast).symm
    · rw [KExpr.substSpec,
        ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut),
        ihinner (depth := depth + 1)
          (by rw [hd1]; exact Nat.lt_of_le_of_lt (by omega) hcut)]
  | @all n bi ty inner md hty hinner ihty ihinner =>
    rw [mkAll_shape, size] at hcut
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkAll_shape]
    rw [substNoIntern]
    split
    · rename_i hfast
      exact (substSpec_id (.all hty hinner) hcut hfast).symm
    · rw [KExpr.substSpec,
        ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut),
        ihinner (depth := depth + 1)
          (by rw [hd1]; exact Nat.lt_of_le_of_lt (by omega) hcut)]
  | @letE n ty val inner nd md hty hval hinner ihty ihval ihinner =>
    rw [mkLet_shape, size] at hcut
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLet_shape]
    rw [substNoIntern]
    split
    · rename_i hfast
      exact (substSpec_id (.letE hty hval hinner) hcut hfast).symm
    · rw [KExpr.substSpec,
        ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut),
        ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut),
        ihinner (depth := depth + 1)
          (by rw [hd1]; exact Nat.lt_of_le_of_lt (by omega) hcut)]
  | @prj id field val md hval ihval =>
    rw [mkPrj_shape, size] at hcut
    rw [mkPrj_shape]
    rw [substNoIntern]
    split
    · rename_i hfast
      exact (substSpec_id (.prj hval) hcut hfast).symm
    · rw [KExpr.substSpec,
        ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut)]
  | @nat v blob md =>
    rw [mkNat_shape]
    simp only [substNoIntern, KExpr.substSpec, KExpr.lbr, ite_self]
  | @str v blob md =>
    rw [mkStr_shape]
    simp only [substNoIntern, KExpr.substSpec, KExpr.lbr, ite_self]

end KExpr

namespace RecM

/-- Exact production equation for the transient lambda branch, normalized to
the already verified pure substitution specification. -/
theorem applyIotaArg_true_lam_spec
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (dom body arg : KExpr .anon) (info : ExprInfo .anon)
    (hbody : KExpr.Constructed body) (harg : KExpr.Constructed arg)
    (hbig : body.size + arg.size < UInt64.size) :
    RecM.applyIotaArg (.lam name bi dom body info) arg true =
      pure (KExpr.substSpec body arg 0) := by
  rw [Ix.Tc.RecM.applyIotaArg_true_lam,
    hbody.substNoIntern_eq_substSpec harg
      (depth := 0)
      (by rw [show (0 : UInt64).toNat = 0 from rfl]; omega) (by omega)]

/-- Executable form of `applyIotaArg_true_lam_spec`: transient beta neither
reads nor changes the typechecker state. -/
theorem applyIotaArg_true_lam_run
    (methods : Methods .anon) (s : TcState .anon)
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (dom body arg : KExpr .anon) (info : ExprInfo .anon)
    (hbody : KExpr.Constructed body) (harg : KExpr.Constructed arg)
    (hbig : body.size + arg.size < UInt64.size) :
    (RecM.applyIotaArg (.lam name bi dom body info) arg true).run methods s =
      .ok (KExpr.substSpec body arg 0) s := by
  rw [applyIotaArg_true_lam_spec name bi dom body arg info hbody harg hbig]
  rfl

end RecM

namespace WhnfMeaning

/-- Semantic beta theorem for the exact non-interning term returned by
production's transient iota branch.  The equality above is the only new
bridge; the typing and Theory beta argument remain those of `beta`. -/
theorem betaNoIntern
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (projections : TrProjOK world.venv uvars trProj)
    {Delta : KVLCtx} {nm : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg : KExpr .anon} {lamMd appMd : ExprInfo .anon}
    {A bodyV argV B : Lean4Lean.VExpr} {u : Lean4Lean.VLevel}
    (hty : TrKExprS world.venv uvars world.nameOf trProj Delta ty A)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam A) :: Delta) body bodyV)
    (harg : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV)
    (hA : world.venv.HasType uvars Delta.toCtx A (.sort u))
    (hbodyTy : world.venv.HasType uvars (A :: Delta.toCtx) bodyV B)
    (hargTy : world.venv.HasType uvars Delta.toCtx argV A)
    (hbodyCon : KExpr.Constructed body)
    (hargCon : KExpr.Constructed arg)
    (hbig : Delta.bvars + body.size + arg.size < UInt64.size) :
    WhnfMeaning trProj world uvars Delta
      (.app (.lam nm bi ty body lamMd) arg appMd)
      (substNoIntern body arg 0) := by
  rw [hbodyCon.substNoIntern_eq_substSpec hargCon
    (depth := 0)
    (by rw [show (0 : UInt64).toNat = 0 from rfl]; omega) (by omega)]
  exact WhnfMeaning.beta projections hty hbody harg hA hbodyTy hargTy hbig

end WhnfMeaning

end Ix.Tc
