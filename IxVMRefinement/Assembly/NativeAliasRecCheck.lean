import IxVMRefinement.Decl.LateNatRecCheckTele
import IxVMRefinement.Assembly.NativeAliasOpenTrace

/-! # The native recursor comparison at the registered telescope

A recursor run loads the stored former's type, renames its level parameters to positions
(instantiating them when the recursor eliminates into every sort), and rebuilds the telescope
with `KernelCheck::nat_former_tele`. For a family declared at a type that only head-reduces to
a telescope, the rebuilt telescope is not the loaded term.

`NatFormerTeleTraced` is the statement that the builder follows the head traces of the term its
input represents: its output represents a term the walk `OpenBinderTrace` builds. It holds for
a syntactic telescope with empty traces (`NatFormerTeleTraced.of_strip`); for a term that
needs head steps it is the specification of `KernelGuard::head` at the term seam, which this
file takes as a premise and does not prove.

Given that premise and the traced binders a registered family records
(`Decl.TracedBinders`), the builder's output represents, at positions, one telescope with the
registered binder prefix (`NatFormerTeleReads.of_traced`): the walk commutes with the renaming
of level parameters and is a function of its input. `late_nat_rec_check_spec_registered` is
then the comparison for the recursor generated from the registered telescope. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration)
open Ix.Kernel.HeadDeltaBeta (DefnLevelsClosed)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The telescope builder follows the head traces of its input**: every observed run of
`KernelCheck::nat_former_tele` for `n` binders, at depth zero and with good calls, on a pointer
that represents `A`, returns a pointer that represents a term the walk builds from `A`. -/
def NatFormerTeleTraced (c : ScopedCtx) (n : Nat) (A : KExpr) : Prop :=
  ∀ {x_rc x_ty x_types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    RCRep c.t c.lim h x_rc → TypesRep c.κ (fun _ => default) h 0 x_types → CoreGood c cs →
    Tm c.κ 0 (fun _ => default) h 0 A x_ty →
    ObsFn W "KernelCheck::nat_former_tele" [x_rc, x_ty, .field (n : F), x_types] h r h' cs →
    ∃ Y, OpenBinderTrace c.env 0 n A Y ∧ Tm c.κ 0 (fun _ => default) h' 0 Y r

/-- On a term whose first `n` nodes are `∀`s the builder follows the empty traces. -/
theorem NatFormerTeleTraced.of_strip {c : ScopedCtx} (hc : ScopedCoreFacts c) {n : Nat}
    {A : KExpr} (hn : n < 18446744069414584321) (hs : (A.stripPis n).isSome = true) :
    NatFormerTeleTraced c n A := by
  intro x_rc x_ty x_types r h h' cs hrc htypes hgood hA ev
  exact ⟨A, OpenBinderTrace.of_strip c.env n hs (tm_fvarIdxLt hA) hA.looseBVarsBounded,
    (scoped_nat_former_tele_bounded hc n hn hs hrc htypes (ghostScoped_zero _) hgood hA ev).2⟩

/-- **The builder's output at the registered telescope.** If `A` carries the traced binders of
`S` and the builder follows the traces of an instance of `S`, then the builder's output on that
instance represents the instance of one telescope `X` with `n` leading `∀`s and the binder
prefix of `A`. -/
theorem NatFormerTeleReads.of_traced {c : ScopedCtx} {n : Nat} {S A : KExpr}
    (ks : List LevelParam) (ws : List Level)
    (hdef : DefnLevelsClosed c.env) (hreg : TracedBinders c.env n S A)
    (hfollow : NatFormerTeleTraced c n (S.instantiateLevelParams ks ws)) :
    ∃ X, (X.stripPis n).isSome = true ∧ PrefixEq n X A ∧
      NatFormerTeleReads c n (S.instantiateLevelParams ks ws)
        (X.instantiateLevelParams ks ws) := by
  obtain ⟨X, hsX, hpre, huniq⟩ := hreg.instantiated hdef ks ws
  refine ⟨X, hsX, hpre, ?_⟩
  intro x_rc x_ty x_types r h h' cs hrc htypes hgood hS ev
  obtain ⟨Y, hY, hYr⟩ := hfollow hrc htypes hgood hS ev
  have hYX := huniq hY
  subst hYX
  exact hYr

/-- **The native recursor comparison of a late recursor, at the registered telescope.**
`pty₀` is the loaded stored former's type and `ttyReg` a telescope with the traced binders of
`pty₀` (`hreg`: what a registered family records about its telescope constant). Given that the
builder follows the head traces of `pty₀` at positions (`hfollow`), the generated recursor type
and rules are those of `ttyReg`. -/
theorem late_nat_rec_check_spec_registered {c : ScopedCtx} (hc : ScopedCoreFacts c)
    (hall : ∀ cl, c.allowed cl)
    {κ₂ : _root_.Address → KKey} {find₂ : KKey → Option (ConstantInfo .anon)}
    (hkeep : ∀ x, c.κ x ≠ unresolvedKey → κ₂ x = c.κ x)
    (hwl₂ : WrapLoads c.toCtx κ₂ find₂)
    {cst : Ixon.Constant} {rc' : Ixon.Recursor}
    {T recC : KKey} {b₀ bT bRec bRB : Bytes.Address} {idx k nP nIdx : Nat} {large : Bool}
    {pty₀ ttyReg rec_ty₀ : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {rls : List (RecRule .anon)}
    {x_rc x_nlvls x_ty x_n_mot x_n_min x_rules w_k w_u x_rec_blk w_ridx : SourceValue F}
    {x_pty w_p1 w_p2 w_pu x_block : SourceValue F}
    {x_addr x_parent_addr r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    [Resolved (κ₂ (ixAddr bRec))]
    (hT_ind : ∃ cv caps, c.env.find? T = some (.indInfo cv caps))
    (hrecblk : Ix.Cert.recordAt c.E (ixAddr bRB) = some cst)
    (hcst : cst.info = .recr rc')
    (hT : c.κ (ixAddr bT) = T)
    (hκ₂_inj : ∀ a : Bytes.Address, κ₂ (ixAddr a) = T → a = bT)
    (hRec : κ₂ (ixAddr bRec) = recC)
    (hidx : idx < 72057594037927936)
    (hCres : ∀ i, i < ctors_info.length → c.κ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey)
    (hk_lt : k + (if large then 1 else 0) < 4294967296)
    (hnP_lt : nP < 72057594037927936)
    (hnIdx_lt : nIdx < 72057594037927936)
    (hnCtors_lt : ctors_info.length < 72057594037927936)
    (hlps_pty : pty₀.allLevelParamsDefined (List.range k) = true)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWfT T k large nP nIdx ctors_info.length info)
    (hrls_len : rls.length = ctors_info.length)
    (hload : NatCtorLoadT c.κ b₀ idx k ctors_info x_block cs)
    (hhead : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs)
    (hgood : CoreGood c cs)
    (hrc : RCRep c.t c.lim h x_rc)
    (hb₀_blk : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbRB : Bytes.RepAddressRef addrTy h bRB x_rec_blk)
    (hbT : Bytes.RepAddressRef addrTy h bT x_parent_addr)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_addr)
    (hpty : Tm c.κ 0 (fun _ => default) h 0 pty₀ x_pty)
    (hdef : DefnLevelsClosed c.env)
    (hreg : TracedBinders c.env (nP + nIdx) pty₀ ttyReg)
    (hfollow : NatFormerTeleTraced c (nP + nIdx)
      (posOf (if large then k :: List.range k else List.range k) pty₀))
    (hrec_ty : Tm c.κ 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) rec_ty₀) x_ty)
    (hrules : RulesRep κ₂ h
      (if large then k :: List.range k else List.range k) 0 x_rules rls)
    (ev : ObsFn W "KernelCheck::nat_rec_check"
      [x_rc,
        .construct kciEnum "Rec"
          [x_nlvls, x_ty, .field (nP : F), .field (nIdx : F), x_n_mot, x_n_min,
            x_rules, w_k, w_u, x_rec_blk, w_ridx],
        x_addr,
        .construct kciEnum "Induct"
          [.field (k : F), x_pty, w_p1, w_p2, .field (ctors_info.length : F),
            w_pu, x_block, .field (idx : F)],
        x_parent_addr,
        .field ((if large then 1 else 0 : Nat) : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    let elim := if large then k else 0
    let ctors₀ := ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2))
    x_nlvls = .field (rlps.length : F) ∧
    x_n_mot = .field 1 ∧
    x_n_min = .field (ctors_info.length : F) ∧
    (∃ recTy,
      Ix.Kernel.structRecTyR T (List.range k) elim large nP nIdx ttyReg ctors₀ = some recTy ∧
      WrapRelSem c.env.find? recTy rec_ty₀) ∧
    (∀ a_d ls_d,
      ForallRightHeadLvls h a_d ls_d (nP + 1 + ctors_info.length + nIdx) x_ty →
      ls_d = (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) ∧
    ∀ j (hlt : j < rls.length) (hj : j < ctors_info.length),
      (rls[j]'hlt).nfields = (ctors_info[j]'hj).2.1 ∧
      ∃ rhsG,
        Ix.Kernel.structRecRhsR T (List.range k) elim large nP nIdx ttyReg ctors₀
          recC (rlps.map .param) j = some rhsG ∧
        WrapRelSem find₂ rhsG (rls[j]'hlt).rhs := by
  intro rlps elim ctors₀
  dsimp only [rlps, elim, ctors₀]
  obtain ⟨X, hsX, hpre, hreads⟩ := NatFormerTeleReads.of_traced
    (if large then k :: List.range k else List.range k)
    (posLevels (if large then k :: List.range k else List.range k)) hdef hreg hfollow
  obtain ⟨⟨tbs₀, tsort₀⟩, hsT₀⟩ := Option.isSome_iff_exists.mp hsX
  have hmain := late_nat_rec_check_spec_of_tele hc hall hkeep hwl₂ (tty₀ := X)
    (hT_ind := hT_ind) (hrecblk := hrecblk) (hcst := hcst) (hT := hT) (hκ₂_inj := hκ₂_inj)
    (hRec := hRec) (hidx := hidx) (hCres := hCres) (hk_lt := hk_lt) (hnP_lt := hnP_lt)
    (hnIdx_lt := hnIdx_lt) (hnCtors_lt := hnCtors_lt)
    (hlps_pty := hlps_pty) (hsT₀ := hsT₀) (hwf_all := hwf_all) (hrls_len := hrls_len)
    (hload := hload) (hhead := hhead) (hgood := hgood) (hrc := hrc) (hb₀_blk := hb₀_blk)
    (hbRB := hbRB) (hbT := hbT) (hbRec := hbRec) (hpty := hpty) (htele := hreads)
    (hrec_ty := hrec_ty) (hrules := hrules) (ev := ev)
  dsimp only at hmain
  obtain ⟨h1, h2, h3, ⟨recTy, hrecTy, hwrap⟩, h5, h6⟩ := hmain
  refine ⟨h1, h2, h3, ⟨recTy, ?_, hwrap⟩, h5, ?_⟩
  · rw [← hpre.structRecTyR]
    exact hrecTy
  · intro j hlt hj
    obtain ⟨hnf, rhsG, hrhs, hw⟩ := h6 j hlt hj
    refine ⟨hnf, rhsG, ?_, hw⟩
    rw [← hpre.structRecRhsR]
    exact hrhs

end IxVM.Refinement.Decl
