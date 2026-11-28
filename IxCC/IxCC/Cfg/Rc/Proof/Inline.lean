import IxCC.Cfg.Rc.Proof.InlineReuseSites
import IxCC.Lir.Proof.Relabel
import IxCC.Lir.Proof.Split

/-! # Semantic preservation of inline RC fast paths (`Cfg.Rc.Inline`)

Proves `inlineProgram_sim`: for any raw Lir program whose runtime wrappers and
procedures match `RuntimeFuncs l raw`, `inlineProgram l raw` simulates `raw`
with exact result equality (`Eq`) and clock map
`fun k => k + 3 * Lir.fuelFor (inlineProgram l raw) k`.

No heap invariant is needed: `step_match` aligns every source, runtime, and
inlined RC / reuse / fused reset+reuse site step via `MatchedStep`, from which
both `forward_run` and `backward_run` follow in ~25 lines each. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Inline

open IxCC.Cfg.Rc.Native

/-! ## Stack and state relation between `raw` and `inlineProgram l raw` -/

/-- Frame-level correspondence for normal frames. -/
inductive FrameRel (l : Layout) (raw : Lir.Program) : Lir.Frame → Lir.Frame → Prop
  | runtime {fr : Lir.Frame} (hge : l.sourceCount ≤ fr.fn) :
      FrameRel l raw fr fr
  | emptySource {F : Lir.Func} {fr : Lir.Frame}
      (hlt : fr.fn < l.sourceCount)
      (hF : raw.funcs[fr.fn]? = some F)
      (hnone : F.blocks[fr.label]? = none) :
      FrameRel l raw fr fr
  | source {F : Lir.Func} {B : Lir.Block} {fr₁ fr₂ : Lir.Frame}
      (hlt : fr₁.fn < l.sourceCount)
      (hfn : fr₂.fn = fr₁.fn)
      (hF : raw.funcs[fr₁.fn]? = some F)
      (hcp : ChunkPos l F fr₁.label B fr₁.pos fr₂.label fr₂.pos)
      (hagree : AgreeBelow (freshBase F) fr₁.env fr₂.env)
      (hdsts : fr₂.dsts = fr₁.dsts) :
      FrameRel l raw fr₁ fr₂

/-- How an inlined `reset` (jump to join block) or `resetU` (in-place assign) finishes
after its dead-field `decProc` calls complete. -/
inductive ResetFinish (l : Layout) (F : Lir.Func) (b : Lir.Label) (B : Lir.Block)
    (rawPos : Nat) (dst x : Lir.VReg) (inBlk : Lir.Block) (inLbl : Lir.Label) (decEndPos : Nat) : Prop
  | jump (joinLbl : Lir.Label)
      (hltLbl : inLbl < joinLbl)
      (hlen : decEndPos = inBlk.body.size)
      (hterm : inBlk.term = .jump ⟨joinLbl, [.v x]⟩)
      (hjoin : ∃ jb, (inlineFunc l F).blocks[joinLbl]? = some jb ∧ jb.params = [dst])
      (hcp : ChunkPos l F b B rawPos joinLbl 0) :
      ResetFinish l F b B rawPos dst x inBlk inLbl decEndPos
  | assign
      (hpos : decEndPos < inBlk.body.size)
      (hstmt : inBlk.body[decEndPos]? = some (.assign dst (.arg (.v x))))
      (hcp : ChunkPos l F b B rawPos inLbl (decEndPos + 1)) :
      ResetFinish l F b B rawPos dst x inBlk inLbl decEndPos

/-- How an inlined shared-path `decProc` call (`mkSharedDecBlocks`) finishes after `decProc`
returns `[]` (`reset` jumps to `joinLbl([.imm 1])`, `fusedResetReuse` jumps to `allocLbl`). -/
inductive SharedDecFinish (l : Layout) (F : Lir.Func) (b : Lir.Label) (B : Lir.Block)
    (rawPos : Nat) (slot : Lir.VReg) (decLbl : Lir.Label) (x : Lir.VReg) : Prop
  | reset (joinLbl : Lir.Label)
      (hltLbl : decLbl + 2 < joinLbl)
      (hdecBlk : (inlineFunc l F).blocks[decLbl + 2]? =
        some { body := #[.call [] l.decProc [.v x]], term := .jump ⟨joinLbl, [.imm 1]⟩, cold := true })
      (hjoin : ∃ jb, (inlineFunc l F).blocks[joinLbl]? = some jb ∧ jb.params = [slot])
      (hcp : ChunkPos l F b B rawPos joinLbl 0) :
      SharedDecFinish l F b B rawPos slot decLbl x
  | fused (dst : Lir.VReg) (idx2 : Nat) (c2 : Lam.CtorInfo) (lay2 : Rt.Rc.CellLayout) (cls : Nat)
      (args : List Lir.Arg) (allocLbl pubLbl : Lir.Label) (aBase : Nat)
      (pubBlk : Lir.Block) (postJ : List Lir.Stmt)
      (hB : F.blocks[b]? = some B)
      (hpos₂ : rawPos < B.body.size)
      (hc2 : l.ctors[idx2]? = some c2)
      (hlay2 : lay2 = Rt.Rc.CellLayout.ofFields c2.arity c2.tag)
      (hcls2 : lay2.cls? = some cls) (hok2 : lay2.ok = true) (hlen2 : args.length = c2.arity)
      (hstmt₂ : B.body[rawPos] = .call [dst] (l.reuseWrapper idx2) (.v slot :: args))
      (hargsLt : argsMax args 0 < freshBase F)
      (hds : dst ≠ slot) (hnd : argsContainVReg dst args = false) (hns : argsContainVReg slot args = false)
      (haGe : freshBase F ≤ aBase)
      (hltAlloc : decLbl + 2 < allocLbl)
      (hdecBlk : (inlineFunc l F).blocks[decLbl + 2]? =
        some { body := #[.call [] l.decProc [.v x]], term := .jump ⟨allocLbl, []⟩, cold := true })
      (halloc : InlineAllocShape (inlineFunc l F) allocLbl pubLbl aBase slot dst (.imm 1) lay2 cls args pubBlk postJ)
      (hcp : ChunkPos l F b B (rawPos + 1) pubLbl (1 + args.length)) :
      SharedDecFinish l F b B rawPos slot decLbl x

/-- Stack-level correspondence: either matching frames, or a suspended RC / reuse
fast-path/slow-path site frame pair. -/
inductive StackRel (l : Layout) (raw : Lir.Program) : List Lir.Frame → List Lir.Frame → Prop
  | nil : StackRel l raw [] []
  | cons {fr₁ fr₂ : Lir.Frame} {rest₁ rest₂ : List Lir.Frame}
      (hfr : FrameRel l raw fr₁ fr₂)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (fr₁ :: rest₁) (fr₂ :: rest₂)
  | consDecSlow {F : Lir.Func} {B : Lir.Block} {wrapFr caller₁ caller₂ : Lir.Frame}
      {rest₁ rest₂ : List Lir.Frame} {dst x : Lir.VReg} {inLbl : Lir.Label}
      (hwrap : wrapFr.fn = l.decWrapper ∧ wrapFr.label = 0 ∧ wrapFr.pos = 1 ∧ wrapFr.dsts = [])
      (hlt : caller₁.fn < l.sourceCount)
      (hfn : caller₂.fn = caller₁.fn)
      (hF : raw.funcs[caller₁.fn]? = some F)
      (hdsts₁ : caller₁.dsts = [dst])
      (hdsts₂ : caller₂.dsts = [])
      (hfree : caller₂.label = inLbl + 2 ∧ caller₂.pos = 1)
      (hfreeBlk : (inlineFunc l F).blocks[inLbl + 2]? =
        some { body := #[.call [] l.decProc [.v x]], term := .jump ⟨inLbl + 5, []⟩, cold := B.cold })
      (hjoinBlk : ∃ jb, (inlineFunc l F).blocks[inLbl + 5]? = some jb ∧
        jb.params = [] ∧ 0 < jb.body.size ∧ jb.body[0]? = some (.assign dst (.arg (.imm 1))))
      (hcpNext : ChunkPos l F caller₁.label B caller₁.pos (inLbl + 5) 1)
      (hagree : AgreeBelow (freshBase F) caller₁.env caller₂.env)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (wrapFr :: caller₁ :: rest₁) (caller₂ :: rest₂)
  /-- Cold redirect for `.reuse` or `.reset`: both sides called the same runtime wrapper;
  on return `[v]`, `inl` jumps from `coldLbl` (`pos = 1`) to `joinLbl([.v tmpReg])` binding `dst`. -/
  | consColdRedirect {F : Lir.Func} {B : Lir.Block} {caller₁ caller₂ : Lir.Frame}
      {rest₁ rest₂ : List Lir.Frame} {dst tmpReg : Lir.VReg} {coldLbl joinLbl : Lir.Label}
      {coldBlk : Lir.Block}
      (hlt : caller₁.fn < l.sourceCount)
      (hfn : caller₂.fn = caller₁.fn)
      (hF : raw.funcs[caller₁.fn]? = some F)
      (hdsts₁ : caller₁.dsts = [dst])
      (hdsts₂ : caller₂.dsts = [tmpReg])
      (htmpGe : freshBase F ≤ tmpReg)
      (hcoldPos : caller₂.label = coldLbl ∧ caller₂.pos = 1)
      (hltLbl : coldLbl < joinLbl)
      (hcoldBlk : (inlineFunc l F).blocks[coldLbl]? = some coldBlk)
      (hcoldSz : coldBlk.body.size = 1)
      (hcoldTerm : coldBlk.term = .jump ⟨joinLbl, [.v tmpReg]⟩)
      (hjoinBlk : ∃ jb, (inlineFunc l F).blocks[joinLbl]? = some jb ∧ jb.params = [dst])
      (hcpNext : ChunkPos l F caller₁.label B caller₁.pos joinLbl 0)
      (hagree : AgreeBelow (freshBase F) caller₁.env caller₂.env)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (caller₁ :: rest₁) (caller₂ :: rest₂)
  /-- Active `dec`-loop alignment for `.reset` hot path and `.resetU` (ready at block `base + 2 * k`). -/
  | consResetDec {F W : Lir.Func} {B inBlk : Lir.Block} {wFr caller₁ caller₂ : Lir.Frame}
      {rest₁ rest₂ : List Lir.Frame} {dst x deadBase : Lir.VReg}
      {n base oldBase k i decBasePos : Nat} {xVal mask : Lir.Word} {inLbl : Lir.Label}
      (hW : raw.funcs[wFr.fn]? = some W)
      (hshape : DecLoopShape l.decProc n base oldBase W)
      (hwPos : wFr.label = base + 2 * k ∧ wFr.pos = 0 ∧ wFr.dsts = [])
      (hkLe : k ≤ n)
      (hw0 : wFr.env[0]? = some xVal)
      (hw1 : wFr.env[1]? = some mask)
      (hwvals : ∀ j < n, ∃ v, wFr.env[oldBase + j]? = some v)
      (hlt : caller₁.fn < l.sourceCount)
      (hfn : caller₂.fn = caller₁.fn)
      (hF : raw.funcs[caller₁.fn]? = some F)
      (hdsts₁ : caller₁.dsts = [dst])
      (hdsts₂ : caller₂.dsts = [])
      (hinPos : caller₂.label = inLbl ∧ caller₂.pos = decBasePos + i)
      (hinBlk : (inlineFunc l F).blocks[inLbl]? = some inBlk)
      (hdrop : (deadFields n mask).drop i = deadFrom n mask k)
      (hiLe : i ≤ (deadFields n mask).length)
      (hdecs : ∀ idx < (deadFields n mask).length,
        inBlk.body[decBasePos + idx]? = some (.call [] l.decProc [.v (deadBase + idx)]))
      (hvals : ∀ idx, (hi : idx < (deadFields n mask).length) →
        caller₂.env[deadBase + idx]? = wFr.env[oldBase + (deadFields n mask)[idx]]?)
      (hx : caller₂.env[x]? = some xVal)
      (hfin : ResetFinish l F caller₁.label B caller₁.pos dst x inBlk inLbl (decBasePos + (deadFields n mask).length))
      (hagree : AgreeBelow (freshBase F) caller₁.env caller₂.env)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (wFr :: caller₁ :: rest₁) (caller₂ :: rest₂)
  /-- Suspended `dec`-loop frame inside `call [] decProc` (at `base + 2 * j + 1, pos = 1`). -/
  | consResetDecCall {F W : Lir.Func} {B inBlk : Lir.Block} {wFr caller₁ caller₂ : Lir.Frame}
      {rest₁ rest₂ : List Lir.Frame} {dst x deadBase : Lir.VReg}
      {n base oldBase j i decBasePos : Nat} {xVal mask : Lir.Word} {inLbl : Lir.Label}
      (hW : raw.funcs[wFr.fn]? = some W)
      (hshape : DecLoopShape l.decProc n base oldBase W)
      (hwPos : wFr.label = base + 2 * j + 1 ∧ wFr.pos = 1 ∧ wFr.dsts = [])
      (hjLt : j < n)
      (hw0 : wFr.env[0]? = some xVal)
      (hw1 : wFr.env[1]? = some mask)
      (hwvals : ∀ q < n, ∃ v, wFr.env[oldBase + q]? = some v)
      (hlt : caller₁.fn < l.sourceCount)
      (hfn : caller₂.fn = caller₁.fn)
      (hF : raw.funcs[caller₁.fn]? = some F)
      (hdsts₁ : caller₁.dsts = [dst])
      (hdsts₂ : caller₂.dsts = [])
      (hinPos : caller₂.label = inLbl ∧ caller₂.pos = decBasePos + i)
      (hinBlk : (inlineFunc l F).blocks[inLbl]? = some inBlk)
      (hdrop : (deadFields n mask).drop i = deadFrom n mask (j + 1))
      (hiLe : i ≤ (deadFields n mask).length)
      (hdecs : ∀ idx < (deadFields n mask).length,
        inBlk.body[decBasePos + idx]? = some (.call [] l.decProc [.v (deadBase + idx)]))
      (hvals : ∀ idx, (hi : idx < (deadFields n mask).length) →
        caller₂.env[deadBase + idx]? = wFr.env[oldBase + (deadFields n mask)[idx]]?)
      (hx : caller₂.env[x]? = some xVal)
      (hfin : ResetFinish l F caller₁.label B caller₁.pos dst x inBlk inLbl (decBasePos + (deadFields n mask).length))
      (hagree : AgreeBelow (freshBase F) caller₁.env caller₂.env)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (wFr :: caller₁ :: rest₁) (caller₂ :: rest₂)
  /-- Suspended shared-path `decProc` call inside inlined `.reset` / `.fusedResetReuse` (`live.length ≤ maxInlineResetLive`). -/
  | consResetSharedDec {F : Lir.Func} {B : Lir.Block} {wFr caller₁ caller₂ : Lir.Frame}
      {rest₁ rest₂ : List Lir.Frame} {slot x : Lir.VReg} {idx1 : Nat} {c1 : Lam.CtorInfo}
      {lay1 : Rt.Rc.CellLayout} {cls1 : Nat} {decLbl : Lir.Label}
      (hc1 : l.ctors[idx1]? = some c1)
      (hlay1 : lay1 = Rt.Rc.CellLayout.ofFields c1.arity c1.tag)
      (hcls1 : lay1.cls? = some cls1)
      (hwPos : wFr.fn = l.resetWrapper idx1 ∧ wFr.label = (3 + 2 * lay1.nobj) + 2 * lay1.nobj ∧ wFr.pos = 1 ∧ wFr.dsts = [])
      (hlt : caller₁.fn < l.sourceCount)
      (hfn : caller₂.fn = caller₁.fn)
      (hF : raw.funcs[caller₁.fn]? = some F)
      (hdsts₁ : caller₁.dsts = [slot])
      (hdsts₂ : caller₂.dsts = [])
      (hinPos : caller₂.label = decLbl + 2 ∧ caller₂.pos = 1)
      (hfin : SharedDecFinish l F caller₁.label B caller₁.pos slot decLbl x)
      (hagree : AgreeBelow (freshBase F) caller₁.env caller₂.env)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (wFr :: caller₁ :: rest₁) (caller₂ :: rest₂)
  /-- Fused `reset`+`reuse` fallback (`live.length > maxInlineResetLive`) — stage 1 (under `resetWrapper idx1`). -/
  | consFusedCold1 {F : Lir.Func} {B pubBlk : Lir.Block} {caller₁ caller₂ : Lir.Frame}
      {rest₁ rest₂ : List Lir.Frame} {slot x dst : Lir.VReg} {idx1 idx2 tmp : Nat}
      {c2 : Lam.CtorInfo} {lay2 : Rt.Rc.CellLayout} {cls : Nat} {mask : UInt64}
      {args : List Lir.Arg} {postJ : List Lir.Stmt} {inLbl : Lir.Label}
      (hlt : caller₁.fn < l.sourceCount)
      (hfn : caller₂.fn = caller₁.fn)
      (hF : raw.funcs[caller₁.fn]? = some F)
      (hB : F.blocks[caller₁.label]? = some B)
      (hpos₂ : caller₁.pos < B.body.size)
      (hc2 : l.ctors[idx2]? = some c2)
      (hlay2 : lay2 = Rt.Rc.CellLayout.ofFields c2.arity c2.tag)
      (hcls2 : lay2.cls? = some cls) (hok2 : lay2.ok = true) (hlen2 : args.length = c2.arity)
      (hstmt₂ : B.body[caller₁.pos] = .call [dst] (l.reuseWrapper idx2) (.v slot :: args))
      (hargsLt : argsMax args 0 < freshBase F)
      (hds : dst ≠ slot) (hnd : argsContainVReg dst args = false) (hns : argsContainVReg slot args = false)
      (hdsts₁ : caller₁.dsts = [slot])
      (hdsts₂ : caller₂.dsts = [tmp + 1])
      (htmpGe : freshBase F ≤ tmp)
      (hcoldPos : caller₂.label = inLbl + 2 ∧ caller₂.pos = 1)
      (hcoldBlk : (inlineFunc l F).blocks[inLbl + 2]? =
        some { body := #[.call [tmp + 1] (l.resetWrapper idx1) [.v x, .imm mask]],
               term := .br .tnz .w64 (.v (tmp + 1)) (.imm 1) ⟨inLbl + 3, []⟩ ⟨inLbl + 9, [.v (tmp + 1), .v (tmp + 1)]⟩,
               cold := true })
      (halloc : InlineAllocShape (inlineFunc l F) (inLbl + 3) (inLbl + 9) (tmp + 2) slot dst (.v (tmp + 1)) lay2 cls args pubBlk postJ)
      (hcpNext : ChunkPos l F caller₁.label B (caller₁.pos + 1) (inLbl + 9) (1 + args.length))
      (hagree : AgreeBelow (freshBase F) caller₁.env caller₂.env)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (caller₁ :: rest₁) (caller₂ :: rest₂)
  /-- Fused `reset`+`reuse` fallback (`live.length > maxInlineResetLive`) — stage 2 (after `resetWrapper` returns `slotVal`). -/
  | consFusedColdMid {F : Lir.Func} {B pubBlk : Lir.Block} {caller₁ caller₂ : Lir.Frame}
      {rest₁ rest₂ : List Lir.Frame} {slot x dst : Lir.VReg} {idx1 idx2 tmp : Nat}
      {c2 : Lam.CtorInfo} {lay2 : Rt.Rc.CellLayout} {cls : Nat} {mask : UInt64}
      {args : List Lir.Arg} {postJ : List Lir.Stmt} {inLbl : Lir.Label} {slotVal : Lir.Word}
      (hlt : caller₁.fn < l.sourceCount)
      (hfn : caller₂.fn = caller₁.fn)
      (hF : raw.funcs[caller₁.fn]? = some F)
      (hB : F.blocks[caller₁.label]? = some B)
      (hpos₂ : caller₁.pos < B.body.size)
      (hc2 : l.ctors[idx2]? = some c2)
      (hlay2 : lay2 = Rt.Rc.CellLayout.ofFields c2.arity c2.tag)
      (hcls2 : lay2.cls? = some cls) (hok2 : lay2.ok = true) (hlen2 : args.length = c2.arity)
      (hstmt₂ : B.body[caller₁.pos] = .call [dst] (l.reuseWrapper idx2) (.v slot :: args))
      (hargsLt : argsMax args 0 < freshBase F)
      (hds : dst ≠ slot) (hnd : argsContainVReg dst args = false) (hns : argsContainVReg slot args = false)
      (hdsts₁ : caller₁.dsts = [])
      (hdsts₂ : caller₂.dsts = [])
      (htmpGe : freshBase F ≤ tmp)
      (hslot₁ : caller₁.env[slot]? = some slotVal)
      (hslot₂ : caller₂.env[tmp + 1]? = some slotVal)
      (hcoldPos : caller₂.label = inLbl + 2 ∧ caller₂.pos = 1)
      (hcoldBlk : (inlineFunc l F).blocks[inLbl + 2]? =
        some { body := #[.call [tmp + 1] (l.resetWrapper idx1) [.v x, .imm mask]],
               term := .br .tnz .w64 (.v (tmp + 1)) (.imm 1) ⟨inLbl + 3, []⟩ ⟨inLbl + 9, [.v (tmp + 1), .v (tmp + 1)]⟩,
               cold := true })
      (halloc : InlineAllocShape (inlineFunc l F) (inLbl + 3) (inLbl + 9) (tmp + 2) slot dst (.v (tmp + 1)) lay2 cls args pubBlk postJ)
      (hcpNext : ChunkPos l F caller₁.label B (caller₁.pos + 1) (inLbl + 9) (1 + args.length))
      (hagreeNe : ∀ r < freshBase F, r ≠ slot → caller₁.env[r]? = caller₂.env[r]?)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (caller₁ :: rest₁) (caller₂ :: rest₂)
  /-- Suspended cold pointer `decProc` call inside fused 1-dead-field `resetU`+`reuseU`. -/
  | consFusedResetU1Dec {F : Lir.Func} {B joinBlk : Lir.Block} {wFr caller₁ caller₂ : Lir.Frame}
      {rest₁ rest₂ : List Lir.Frame} {slot x dst : Lir.VReg} {idx1 idx2 deadIdx tmp : Nat}
      {c1 c2 : Lam.CtorInfo} {lay1 lay2 : Rt.Rc.CellLayout} {cls : Nat} {mask xVal : Lir.Word}
      {args : List Lir.Arg} {postJ : List Lir.Stmt} {inLbl : Lir.Label}
      (hc1 : l.ctors[idx1]? = some c1)
      (hlay1 : lay1 = Rt.Rc.CellLayout.ofFields c1.arity c1.tag)
      (hcls1 : lay1.cls? = some cls)
      (hc2 : l.ctors[idx2]? = some c2)
      (hlay2 : lay2 = Rt.Rc.CellLayout.ofFields c2.arity c2.tag)
      (hcls2 : lay2.cls? = some cls) (hlen2 : args.length = c2.arity)
      (hdead : deadFields lay1.nobj mask = [deadIdx])
      (hwPos : wFr.fn = l.resetUWrapper idx1 ∧ wFr.label = 1 + 2 * deadIdx + 1 ∧ wFr.pos = 1 ∧ wFr.dsts = [])
      (hw0 : wFr.env[0]? = some xVal)
      (hw1 : wFr.env[1]? = some mask)
      (hwvals : ∀ j < lay1.nobj, ∃ v, wFr.env[2 + j]? = some v)
      (hlt : caller₁.fn < l.sourceCount)
      (hfn : caller₂.fn = caller₁.fn)
      (hF : raw.funcs[caller₁.fn]? = some F)
      (hB : F.blocks[caller₁.label]? = some B)
      (hpos₂ : caller₁.pos < B.body.size)
      (hstmt₂ : B.body[caller₁.pos] = .call [dst] (l.reuseUWrapper idx2) (.v slot :: args))
      (hsx : slot ≠ x) (hns : argsContainVReg slot args = false)
      (hxLt : (x : Nat) < freshBase F) (hargsLt : argsMax args 0 < freshBase F)
      (hx : caller₁.env[x]? = some xVal)
      (hdsts₁ : caller₁.dsts = [slot])
      (hdsts₂ : caller₂.dsts = [])
      (hinPos : caller₂.label = inLbl + 1 ∧ caller₂.pos = (1 + lay1.nobj) + 1)
      (hb1 : (inlineFunc l F).blocks[inLbl + 1]? =
        some { body := (mkShellStores x (Rt.Rc.dynamicHeader lay1.nobj cls lay1.tag 1) lay1.nobj ++
                 [Lir.Stmt.call [] l.decProc [.v tmp]]).toArray,
               term := .jump ⟨inLbl + 2, []⟩, cold := true })
      (hjb : (inlineFunc l F).blocks[inLbl + 2]? = some joinBlk)
      (hjbP : joinBlk.params = [])
      (hjbBody : joinBlk.body.toList =
        (.store .w64 (cellAddr x 0) (.imm (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1)) ::
          mkFieldStores x 0 args) ++ [.assign slot (.arg (.v x)), .assign dst (.arg (.v x))] ++ postJ)
      (hcpNext : ChunkPos l F caller₁.label B (caller₁.pos + 1) (inLbl + 2) (3 + args.length))
      (hagree : AgreeBelow (freshBase F) caller₁.env caller₂.env)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (wFr :: caller₁ :: rest₁) (caller₂ :: rest₂)

/-- Whole-state correspondence: identical memory and context, related stacks,
and the running top frame always has empty `dsts`. -/
structure StateRel (l : Layout) (raw : Lir.Program) (s₁ s₂ : Lir.State) : Prop where
  mem : s₂.mem = s₁.mem
  ctx : s₂.ctx = s₁.ctx
  stack : StackRel l raw s₁.stack s₂.stack
  topDsts : ∀ fr rest, s₁.stack = fr :: rest → fr.dsts = []

/-! ## Generic `Sem.runClocked` / `Sem.Star` / `Sem.Reaches` helpers -/

theorem runClocked_step_free {σ α : Type} {st : σ → Sem.Step σ α} {fuel k : Nat} {s s' : σ}
    (hs : st s = .next s' false) :
    Sem.runClocked st (fuel + 1) k s = Sem.runClocked st fuel k s' := by
  simp [Sem.runClocked, hs]

theorem runClocked_step_charge {σ α : Type} {st : σ → Sem.Step σ α} {fuel k : Nat} {s s' : σ}
    (hs : st s = .next s' true) :
    Sem.runClocked st (fuel + 1) (k + 1) s = Sem.runClocked st fuel k s' := by
  simp [Sem.runClocked, hs]

theorem runClocked_step_charge_zero {σ α : Type} {st : σ → Sem.Step σ α} {fuel : Nat} {s s' : σ}
    (hs : st s = .next s' true) :
    Sem.runClocked st (fuel + 1) 0 s = .timeout := by
  simp [Sem.runClocked, hs]

theorem runClocked_star_inv {σ α : Type} {st : σ → Sem.Step σ α} :
    ∀ {s s' : σ} {c : Nat}, Sem.Star st s c s' →
    ∀ {fuel k : Nat} {r : Sem.Result α},
      Sem.runClocked st fuel k s = r → r ≠ .timeout →
      ∃ fuel' k', fuel' ≤ fuel ∧ k = c + k' ∧ Sem.runClocked st fuel' k' s' = r
  | _, _, 0, .refl _, fuel, k, _, hrun, _ => ⟨fuel, k, Nat.le_refl _, (Nat.zero_add k).symm, hrun⟩
  | _, _, _, .free hs hstar, fuel, k, _, hrun, hne => by
    cases fuel with
    | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hne
    | succ fuel =>
      rw [runClocked_step_free hs] at hrun
      obtain ⟨f', k', hf', hk', hrun'⟩ := runClocked_star_inv hstar hrun hne
      exact ⟨f', k', by omega, hk', hrun'⟩
  | _, _, _ + 1, .charge hs hstar, fuel, k, _, hrun, hne => by
    cases fuel with
    | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hne
    | succ fuel =>
      cases k with
      | zero => rw [runClocked_step_charge_zero hs] at hrun; exact absurd hrun.symm hne
      | succ k =>
        rw [runClocked_step_charge hs] at hrun
        obtain ⟨f', k', hf', hk', hrun'⟩ := runClocked_star_inv hstar hrun hne
        exact ⟨f', k', by omega, by omega, hrun'⟩

theorem runClocked_star_inv_lt {σ α : Type} {st : σ → Sem.Step σ α} {s s₁ s₂ : σ}
    {b : Bool} {c : Nat} (h1 : st s = .next s₁ b) (hstar : Sem.Star st s₁ c s₂)
    {fuel k : Nat} {r : Sem.Result α}
    (hrun : Sem.runClocked st fuel k s = r) (hne : r ≠ .timeout) :
    ∃ fuel' k', fuel' < fuel ∧ k = b.toNat + c + k' ∧ Sem.runClocked st fuel' k' s₂ = r := by
  cases fuel with
  | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hne
  | succ fuel =>
    cases b with
    | false =>
      rw [runClocked_step_free h1] at hrun
      obtain ⟨f', k', hf', hk', hrun'⟩ := runClocked_star_inv hstar hrun hne
      exact ⟨f', k', by omega, by simpa using hk', hrun'⟩
    | true =>
      cases k with
      | zero => rw [runClocked_step_charge_zero h1] at hrun; exact absurd hrun.symm hne
      | succ k =>
        rw [runClocked_step_charge h1] at hrun
        obtain ⟨f', k', hf', hk', hrun'⟩ := runClocked_star_inv hstar hrun hne
        exact ⟨f', k', by omega, by simp; omega, hrun'⟩

theorem reaches_of_star_reaches {σ α : Type} {st : σ → Sem.Step σ α} {s s' : σ} {c k : Nat}
    {r : Sem.Result α} (hstar : Sem.Star st s c s') (hr : Sem.Reaches st s' k r) :
    Sem.Reaches st s (c + k) r := by
  induction hstar with
  | refl => simpa using hr
  | free hs _ ih => exact .free hs (ih hr)
  | charge hs _ ih =>
    have := Sem.Reaches.charge hs (ih hr)
    rwa [Nat.add_right_comm] at this

/-! ## Function entry, return, and edge correspondence -/

theorem enter_rel (l : Layout) (raw : Lir.Program) {g : Lir.FunId} {vs : List Lir.Word} :
    (∀ callee₁, Lir.enter raw g vs = some callee₁ →
      ∃ callee₂, Lir.enter (inlineProgram l raw) g vs = some callee₂ ∧
        FrameRel l raw callee₁ callee₂ ∧ callee₁.dsts = []) ∧
    (∀ callee₂, Lir.enter (inlineProgram l raw) g vs = some callee₂ →
      ∃ callee₁, Lir.enter raw g vs = some callee₁ ∧
        FrameRel l raw callee₁ callee₂ ∧ callee₁.dsts = []) ∧
    (Lir.enter raw g vs = none ↔ Lir.enter (inlineProgram l raw) g vs = none) := by
  by_cases hlt : g < l.sourceCount
  · have hget := inlineProgram_get_lt l raw hlt
    cases hF : raw.funcs[g]? with
    | none => simp [Lir.enter, hF, hget]
    | some F =>
      have hF' : (inlineProgram l raw).funcs[g]? = some (inlineFunc l F) := by rw [hget, hF]; rfl
      have hparams : (inlineFunc l F).params = F.params := rfl
      simp only [Lir.enter, hF, hF', hparams, Option.bind_eq_bind, Option.bind_some]
      cases hbp : Lir.bindParams {} F.params vs with
      | none => simp
      | some ρ =>
        cases hB0 : F.blocks[0]? with
        | none =>
          exact ⟨fun _ h1 => by cases h1; exact ⟨_, rfl, .emptySource hlt hF hB0, rfl⟩,
            fun _ h2 => by cases h2; exact ⟨_, rfl, .emptySource hlt hF hB0, rfl⟩, by simp⟩
        | some B0 =>
          have hcp : ChunkPos l F 0 B0 0 0 0 := ChunkPos.entry l F hB0
          exact ⟨fun _ h1 => by cases h1; exact ⟨_, rfl, .source hlt rfl hF hcp AgreeBelow.refl rfl, rfl⟩,
            fun _ h2 => by cases h2; exact ⟨_, rfl, .source hlt rfl hF hcp AgreeBelow.refl rfl, rfl⟩, by simp⟩
  · have hge : l.sourceCount ≤ g := Nat.le_of_not_lt hlt
    have hget := inlineProgram_get_ge l raw hge
    simp only [Lir.enter, hget]
    cases raw.funcs[g]? with
    | none => simp
    | some F =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases Lir.bindParams {} F.params vs with
      | none => simp
      | some ρ =>
        exact ⟨fun _ h1 => by cases h1; exact ⟨_, rfl, .runtime hge, rfl⟩,
          fun _ h2 => by cases h2; exact ⟨_, rfl, .runtime hge, rfl⟩, by simp⟩

/-- Unified single-step or single-site matching relation between `raw` and `inlineProgram l raw`. -/
inductive MatchedStep (l : Layout) (raw : Lir.Program) (s₁ s₂ : Lir.State) : Prop
  | rawStuck : Lir.step raw s₁ = .stuck → MatchedStep l raw s₁ s₂
  | rawStuckWithin {c₁ : Nat} : c₁ ≤ 12 →
      Sem.Reaches (Lir.semStep raw) s₁ c₁ .stuck →
      MatchedStep l raw s₁ s₂
  | sameFinal {r : Sem.Result (List Lir.Word × X86.Memory)} :
      Sem.Final (Lir.semStep raw s₁) r → Sem.Final (Lir.semStep (inlineProgram l raw) s₂) r →
      MatchedStep l raw s₁ s₂
  | sameOom {c₁ : Nat} : c₁ ≤ 12 →
      Sem.Reaches (Lir.semStep raw) s₁ c₁ (.resource .heap) →
      Sem.Reaches (Lir.semStep (inlineProgram l raw)) s₂ 0 (.resource .heap) →
      MatchedStep l raw s₁ s₂
  | sync {s₁' s₂' s₁'' s₂'' : Lir.State} {b₁ b₂ : Bool} {c₁ c₂ : Nat} :
      Lir.semStep raw s₁ = .next s₁' b₁ → Sem.Star (Lir.semStep raw) s₁' c₁ s₁'' →
      Lir.semStep (inlineProgram l raw) s₂ = .next s₂' b₂ → Sem.Star (Lir.semStep (inlineProgram l raw)) s₂' c₂ s₂'' →
      b₁.toNat + c₁ ≤ b₂.toNat + c₂ + 12 →
      StateRel l raw s₁'' s₂'' →
      MatchedStep l raw s₁ s₂

private theorem mkDeadDecs_getElem? (decProc : Nat) :
    ∀ (baseTmp : Lir.VReg) (xs : List Nat) (idx : Nat), idx < xs.length →
      (mkDeadDecs decProc baseTmp xs)[idx]? = some (.call [] decProc [.v (baseTmp + idx)])
  | _, [], _, hi => by simp at hi
  | baseTmp, _ :: _, 0, _ => by simp [mkDeadDecs]
  | baseTmp, _ :: xs, idx + 1, hi => by
    simp only [mkDeadDecs, List.getElem?_cons_succ]
    have ih := mkDeadDecs_getElem? decProc (baseTmp + 1) xs idx (by simp at hi; omega)
    have hidx : baseTmp + 1 + idx = baseTmp + (idx + 1) := by dsimp only [Lir.VReg]; omega
    simpa [hidx] using ih

private theorem argsMax_mono_local (xs : List Lir.Arg) {a b : Nat} (h : a ≤ b) :
    argsMax xs a ≤ argsMax xs b := by
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    unfold argsMax; rw [List.foldl_cons, List.foldl_cons]
    apply ih; cases x <;> simp [argMax] <;> omega

private theorem evalArgs_eq_of_agree_ne {bound : Nat} {slot : Lir.VReg} {e₁ e₂ : Lir.Env}
    (hag : ∀ r < bound, r ≠ slot → e₁[r]? = e₂[r]?) :
    ∀ {args : List Lir.Arg}, argsMax args 0 < bound → argsContainVReg slot args = false →
      Lir.evalArgs e₁ args = Lir.evalArgs e₂ args
  | [], _, _ => rfl
  | a :: as, hlt, hns => by
    have haLt : argMax a 0 < bound :=
      Nat.lt_of_le_of_lt (le_argsMax as (argMax a 0)) hlt
    have hasLt : argsMax as 0 < bound :=
      Nat.lt_of_le_of_lt (argsMax_mono_local as (Nat.zero_le (argMax a 0))) hlt
    have ⟨haEq, hns'⟩ : a.eval e₁ = a.eval e₂ ∧ argsContainVReg slot as = false := by
      cases a with
      | imm _ => exact ⟨rfl, hns⟩
      | v r =>
        simp only [argsContainVReg, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hns
        have hrLt : r < bound := by simp [argMax] at haLt; dsimp only [Lir.VReg] at haLt ⊢; omega
        exact ⟨hag r hrLt hns.1, hns.2⟩
    have ih := evalArgs_eq_of_agree_ne hag hasLt hns'
    simp only [Lir.evalArgs, List.mapM_cons, haEq]
    rw [show List.mapM (Lir.Arg.eval e₁) as = List.mapM (Lir.Arg.eval e₂) as from ih]

private theorem raw_reset_stuck {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst x : Lir.VReg} {idx : Nat} {c : Lam.CtorInfo}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask xVal : Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size) (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag) (hcls : lay.cls? = some cls)
    (hstmt : B.body[fr.pos] = .call [dst] (l.resetWrapper idx) [.v x, .imm mask])
    (hx : fr.env[x]? = some xVal) (hstk : evalUniqueCheck xVal mem = .stuck) :
    Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 2 .stuck := by
  have hwrapF : raw.funcs[l.resetWrapper idx]? =
      some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls) := by
    rw [hlay]; exact hr.resetWrap idx c cls hc (by rwa [← hlay])
  let e0 : Lir.Env := (({} : Lir.Env).insert 0 xVal).insert 1 mask
  have he0_0 : e0[0]? = some xVal := by rw [Lir.env_insert_ne _ _ (by decide)]; simp
  let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
  let wFr0 : Lir.Frame := { fn := l.resetWrapper idx, label := 0, pos := 0, env := e0 }
  let wFr0' : Lir.Frame := { fn := l.resetWrapper idx, label := 0, pos := 1, env := e0, dsts := [2] }
  let uFr : Lir.Frame := { fn := l.isUniqueProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
  have sCallWrap : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (vs := [xVal, mask]) hF hB hpos hstmt
      (by simp [Lir.evalArgs, Lir.Arg.eval, hx])
      (by simp [Lir.enter, hwrapF, mkResetWrapper, Lir.bindParams, e0, wFr0])
  have sCallU : Lir.semStep raw { mem, ctx, stack := wFr0 :: caller' :: rest } =
      .next { mem, ctx, stack := uFr :: wFr0' :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (fr := wFr0) (g := l.isUniqueProc) (as := [.v 0]) (vs := [xVal])
      hwrapF rfl (by simp [wFr0, mkResetWrapper]) (by simp [wFr0, mkResetWrapper])
      (by simp [wFr0, Lir.evalArgs, Lir.Arg.eval, he0_0])
      (by simp [Lir.enter, hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.bindParams, uFr])
  have hU := exec_isUniqueProc hr (xVal := xVal) (ctx := ctx) (mem := mem)
    (caller := wFr0') (rest := caller' :: rest) (dst := 2) rfl
  rw [hstk] at hU
  exact .charge sCallWrap (.charge sCallU hU)

/-- Step a synchronized `reset`/`resetU` `dec`-loop state (`consResetDec`), returning the
synchronized post-state pair (so `consResetDecCall` can prepend `raw_decLoop_after_call`). -/
private theorem step_resetDec_sync {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F W : Lir.Func} {B inBlk : Lir.Block} {wFr caller₁ caller₂ : Lir.Frame}
    {rest₁ rest₂ : List Lir.Frame} {dst x deadBase : Lir.VReg}
    {n base oldBase k i decBasePos : Nat} {xVal mask ctx : Lir.Word} {inLbl : Lir.Label}
    {mem : X86.Memory}
    (hW : raw.funcs[wFr.fn]? = some W)
    (hshape : DecLoopShape l.decProc n base oldBase W)
    (hwPos : wFr.label = base + 2 * k ∧ wFr.pos = 0 ∧ wFr.dsts = [])
    (hkLe : k ≤ n)
    (hw0 : wFr.env[0]? = some xVal)
    (hw1 : wFr.env[1]? = some mask)
    (hwvals : ∀ j < n, ∃ v, wFr.env[oldBase + j]? = some v)
    (hlt : caller₁.fn < l.sourceCount)
    (hfn : caller₂.fn = caller₁.fn)
    (hF : raw.funcs[caller₁.fn]? = some F)
    (hdsts₁ : caller₁.dsts = [dst])
    (hdsts₂ : caller₂.dsts = [])
    (hinPos : caller₂.label = inLbl ∧ caller₂.pos = decBasePos + i)
    (hinBlk : (inlineFunc l F).blocks[inLbl]? = some inBlk)
    (hdrop : (deadFields n mask).drop i = deadFrom n mask k)
    (hiLe : i ≤ (deadFields n mask).length)
    (hdecs : ∀ idx < (deadFields n mask).length,
      inBlk.body[decBasePos + idx]? = some (.call [] l.decProc [.v (deadBase + idx)]))
    (hvals : ∀ idx, (hi : idx < (deadFields n mask).length) →
      caller₂.env[deadBase + idx]? = wFr.env[oldBase + (deadFields n mask)[idx]]?)
    (hx : caller₂.env[x]? = some xVal)
    (hfin : ResetFinish l F caller₁.label B caller₁.pos dst x inBlk inLbl (decBasePos + (deadFields n mask).length))
    (hagree : AgreeBelow (freshBase F) caller₁.env caller₂.env)
    (hrest : StackRel l raw rest₁ rest₂) :
    ∃ s₁' s₂' s₁'' s₂'' b₁ b₂ c₁ c₂,
      Lir.semStep raw { mem, ctx, stack := wFr :: caller₁ :: rest₁ } = .next s₁' b₁ ∧
      Sem.Star (Lir.semStep raw) s₁' c₁ s₁'' ∧
      Lir.semStep (inlineProgram l raw) { mem, ctx, stack := caller₂ :: rest₂ } = .next s₂' b₂ ∧
      Sem.Star (Lir.semStep (inlineProgram l raw)) s₂' c₂ s₂'' ∧
      b₁.toNat + c₁ ≤ b₂.toNat + c₂ + 12 ∧
      StateRel l raw s₁'' s₂'' := by
  have hF' : (inlineProgram l raw).funcs[caller₂.fn]? = some (inlineFunc l F) := by
    rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
  have hwEq : ({ fn := wFr.fn, label := base + 2 * k, pos := 0, env := wFr.env, dsts := [] } : Lir.Frame) = wFr := by
    cases wFr; dsimp only at hwPos; obtain ⟨rfl, rfl, rfl⟩ := hwPos; rfl
  have hloop := raw_decLoop_step hr hW hshape hw0 hw1 hdsts₁ hwvals k hkLe (mem := mem) (ctx := ctx) (rest := rest₁)
  cases hdf : deadFrom n mask k with
  | nil =>
    rw [hdf] at hloop hdrop
    have hiEq : i = (deadFields n mask).length := by
      have hlen := congrArg List.length hdrop
      simp only [List.length_drop, List.length_nil] at hlen; omega
    have hstar₁ : Sem.Star (Lir.semStep raw) { mem, ctx, stack := wFr :: caller₁ :: rest₁ } 0
        { mem, ctx, stack := { caller₁ with env := caller₁.env.insert dst xVal, dsts := [] } :: rest₁ } := by
      rwa [hwEq] at hloop
    obtain ⟨s₁', hs₁, htail₁⟩ := star_zero_split hstar₁ (fun heq => by
      have hlen := congrArg (fun s => s.stack.length) heq
      simp at hlen)
    cases hfin with
    | jump joinLbl hltLbl hlen hterm hjoin hcp =>
      obtain ⟨jb, hbJ, hjp⟩ := hjoin
      have hs₂ : Lir.semStep (inlineProgram l raw) { mem, ctx, stack := caller₂ :: rest₂ } =
          .next { mem, ctx, stack := { caller₂ with label := joinLbl, pos := 0, env := caller₂.env.insert dst xVal, dsts := [] } :: rest₂ } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := caller₂) hF' (by rw [hinPos.1]; exact hinBlk) (by rw [hinPos.2, hiEq, hlen])]
        have hfwd : ¬ (joinLbl ≤ caller₂.label) := by rw [hinPos.1]; dsimp only [Lir.Label] at hltLbl ⊢; omega
        simp [hterm, Lir.takeEdge, Lir.evalArgs, Lir.Arg.eval, hx, hbJ, hjp, Lir.bindParams, hfwd, hdsts₂]
      refine ⟨s₁', _, _, _, false, false, 0, 0, hs₁, htail₁, hs₂, .refl _, by omega, ?_⟩
      exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcp (hagree.insert_same dst xVal) rfl) hrest,
        fun _ _ h => by cases h; rfl⟩
    | assign hpos hstmt hcp =>
      have hget : inBlk.body[caller₂.pos]'(by rw [hinPos.2, hiEq]; exact hpos) = .assign dst (.arg (.v x)) := by
        have h1 : inBlk.body[caller₂.pos]? = some (.assign dst (.arg (.v x))) := by rw [hinPos.2, hiEq]; exact hstmt
        rw [Array.getElem?_eq_getElem (by rw [hinPos.2, hiEq]; exact hpos), Option.some.injEq] at h1; exact h1
      have hs₂ : Lir.semStep (inlineProgram l raw) { mem, ctx, stack := caller₂ :: rest₂ } =
          .next { mem, ctx, stack := { caller₂ with label := inLbl, pos := decBasePos + (deadFields n mask).length + 1, env := caller₂.env.insert dst xVal, dsts := [] } :: rest₂ } false := by
        apply Lir.semStep_next.mpr
        have h1 := Lir.step_stmt (fr := caller₂) (mem := mem) (ctx := ctx) (rest := rest₂)
          (ρ' := caller₂.env.insert dst xVal) (mem' := mem)
          hF' (by rw [hinPos.1]; exact hinBlk) (by rw [hinPos.2, hiEq]; exact hpos) hget rfl
          (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, hx])
        cases caller₂; dsimp only at hinPos hdsts₂; obtain ⟨rfl, rfl⟩ := hinPos; subst hdsts₂; subst hiEq; exact h1
      refine ⟨s₁', _, _, _, false, false, 0, 0, hs₁, htail₁, hs₂, .refl _, by omega, ?_⟩
      exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcp (hagree.insert_same dst xVal) rfl) hrest,
        fun _ _ h => by cases h; rfl⟩
  | cons j rem =>
    rw [hdf] at hloop hdrop
    obtain ⟨hjLt, val, hval, hrem, hstar₁⟩ := hloop
    have hiLt : i < (deadFields n mask).length := by
      by_cases hlt' : i < (deadFields n mask).length
      · exact hlt'
      · have : (deadFields n mask).drop i = [] := List.drop_eq_nil_of_le (by omega)
        rw [this] at hdrop; cases hdrop
    have hdj : (deadFields n mask)[i] = j := by
      have h1 : ((deadFields n mask).drop i)[0]? = some j := by rw [hdrop]; rfl
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hiLt, Option.some.injEq] at h1
      exact h1
    have hdropNext : (deadFields n mask).drop (i + 1) = deadFrom n mask (j + 1) := by
      have h1 : (deadFields n mask).drop (i + 1) = ((deadFields n mask).drop i).tail := by
        rw [List.drop_eq_getElem_cons hiLt]; simp
      rw [h1, hdrop, hrem]; rfl
    have hval₂ : caller₂.env[deadBase + i]? = some val := by
      have h1 := hvals i hiLt
      rw [hdj, hval] at h1; exact h1
    have hstmt₂ := hdecs i hiLt
    have hpos₂ : caller₂.pos < inBlk.body.size := by
      rw [hinPos.2]
      by_cases hlt' : decBasePos + i < inBlk.body.size
      · exact hlt'
      · rw [Array.getElem?_eq_none (by omega)] at hstmt₂; cases hstmt₂
    have hget₂ : inBlk.body[caller₂.pos]'hpos₂ = .call [] l.decProc [.v (deadBase + i)] := by
      have h1 : inBlk.body[caller₂.pos]? = some (.call [] l.decProc [.v (deadBase + i)]) := by
        rw [hinPos.2]; exact hstmt₂
      rw [Array.getElem?_eq_getElem hpos₂, Option.some.injEq] at h1; exact h1
    have hdecInl : (inlineProgram l raw).funcs[l.decProc]? = some Rt.Rc.Gen.dec := by
      rw [inlineProgram_get_ge l raw (by simp [Layout.decProc, Layout.incProc]; omega)]
      exact hr.decProc
    have hs₂ : Lir.semStep (inlineProgram l raw) { mem, ctx, stack := caller₂ :: rest₂ } =
        .next { mem, ctx, stack :=
          { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 val } ::
          { caller₂ with pos := decBasePos + (i + 1), dsts := [] } :: rest₂ } true := by
      apply Lir.semStep_next.mpr
      have h1 := Lir.step_call (mem := mem) (ctx := ctx) (rest := rest₂) (fr := caller₂) (vs := [val])
        (callee := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 val })
        hF' (by rw [hinPos.1]; exact hinBlk)
        hpos₂ hget₂ (by simp [Lir.evalArgs, Lir.Arg.eval, hval₂])
        (by simp [Lir.enter, hdecInl, Rt.Rc.Gen.dec, Lir.bindParams])
      have hidx : caller₂.pos + 1 = decBasePos + (i + 1) := by rw [hinPos.2]; omega
      simpa [hidx] using h1
    have hstar₁' : Sem.Star (Lir.semStep raw) { mem, ctx, stack := wFr :: caller₁ :: rest₁ } 1
        { mem, ctx, stack :=
          { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 val } ::
          { fn := wFr.fn, label := base + 2 * j + 1, pos := 1, env := wFr.env, dsts := [] } :: caller₁ :: rest₁ } := by
      rwa [hwEq] at hstar₁
    have hdecGe : l.sourceCount ≤ l.decProc := by simp [Layout.decProc, Layout.incProc]; omega
    -- Split off the first step of `hstar₁'` (which has 1 charged step, hence ≥ 1 step)
    cases hstar₁' with
    | free hs₁ htail₁ =>
      refine ⟨_, _, _, _, false, true, 1, 0, hs₁, htail₁, hs₂, .refl _, by simp, ?_⟩
      exact ⟨rfl, rfl, .cons (.runtime hdecGe)
        (.consResetDecCall hW hshape ⟨rfl, rfl, rfl⟩ hjLt hw0 hw1 hwvals hlt hfn hF hdsts₁ rfl
          ⟨hinPos.1, rfl⟩ hinBlk hdropNext (by omega) hdecs hvals hx hfin hagree hrest),
        fun _ _ h => by cases h; rfl⟩
    | charge hs₁ htail₁ =>
      refine ⟨_, _, _, _, true, true, 0, 0, hs₁, htail₁, hs₂, .refl _, by simp, ?_⟩
      exact ⟨rfl, rfl, .cons (.runtime hdecGe)
        (.consResetDecCall hW hshape ⟨rfl, rfl, rfl⟩ hjLt hw0 hw1 hwvals hlt hfn hF hdsts₁ rfl
          ⟨hinPos.1, rfl⟩ hinBlk hdropNext (by omega) hdecs hvals hx hfin hagree hrest),
        fun _ _ h => by cases h; rfl⟩

private theorem matched_of_ret {l : Layout} {raw : Lir.Program} {mem : X86.Memory} {ctx : Lir.Word}
    {fr₁ fr₂ : Lir.Frame} {rest₁ rest₂ : List Lir.Frame} {vals : List Lir.Word}
    (hstep₁ : Lir.step raw { mem, ctx, stack := fr₁ :: rest₁ } =
      match rest₁ with
      | [] => .done vals mem
      | caller :: rest =>
        match Lir.bindParams caller.env caller.dsts vals with
        | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest } false
        | none => .stuck)
    (hstep₂ : Lir.step (inlineProgram l raw) { mem, ctx, stack := fr₂ :: rest₂ } =
      match rest₂ with
      | [] => .done vals mem
      | caller :: rest =>
        match Lir.bindParams caller.env caller.dsts vals with
        | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest } false
        | none => .stuck)
    (hrest : StackRel l raw rest₁ rest₂) :
    MatchedStep l raw { mem, ctx, stack := fr₁ :: rest₁ } { mem, ctx, stack := fr₂ :: rest₂ } := by
  cases hrest with
  | nil =>
    apply MatchedStep.sameFinal (r := .ok (vals, mem))
    · rw [Lir.semStep, hstep₁]; exact .done
    · rw [Lir.semStep, hstep₂]; exact .done
  | @cons caller₁ caller₂ rest₁' rest₂' hfr hrest' =>
    cases hfr with
    | runtime hge =>
      cases hbp : Lir.bindParams caller₁.env caller₁.dsts vals with
      | none =>
        apply MatchedStep.rawStuck
        simpa [hbp] using hstep₁
      | some ρ =>
        refine .sync (Lir.semStep_next.mpr (by simpa [hbp] using hstep₁)) (.refl _)
          (Lir.semStep_next.mpr (by simpa [hbp] using hstep₂)) (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.runtime hge) hrest', fun _ _ h => by cases h; rfl⟩
    | emptySource hlt hF hnone =>
      cases hbp : Lir.bindParams caller₁.env caller₁.dsts vals with
      | none =>
        apply MatchedStep.rawStuck
        simpa [hbp] using hstep₁
      | some ρ =>
        refine .sync (Lir.semStep_next.mpr (by simpa [hbp] using hstep₁)) (.refl _)
          (Lir.semStep_next.mpr (by simpa [hbp] using hstep₂)) (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.emptySource hlt hF hnone) hrest', fun _ _ h => by cases h; rfl⟩
    | source hlt hfn hF hcp hagree hdsts =>
      obtain ⟨hfwd, _, _⟩ := hagree.bindParams_agree caller₁.dsts vals
      cases hbp : Lir.bindParams caller₁.env caller₁.dsts vals with
      | none =>
        apply MatchedStep.rawStuck
        simpa [hbp] using hstep₁
      | some ρ₁ =>
        obtain ⟨ρ₂, hbp₂, hagree'⟩ := hfwd ρ₁ hbp
        refine .sync (Lir.semStep_next.mpr (by simpa [hbp] using hstep₁)) (.refl _)
          (Lir.semStep_next.mpr (by simpa [hdsts, hbp₂] using hstep₂)) (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcp hagree' rfl) hrest', fun _ _ h => by cases h; rfl⟩
  | consDecSlow hwrap hlt hfn hF hdsts₁ hdsts₂ hfree hfreeBlk hjoinBlk hcpNext hagree hrest' =>
    cases vals with
    | nil =>
      refine .sync (Lir.semStep_next.mpr (by simpa [hwrap.2.2.2, Lir.bindParams] using hstep₁)) (.refl _)
        (Lir.semStep_next.mpr (by simpa [hdsts₂, Lir.bindParams] using hstep₂)) (.refl _) (by omega) ?_
      exact ⟨rfl, rfl, .consDecSlow ⟨hwrap.1, hwrap.2.1, hwrap.2.2.1, rfl⟩ hlt hfn hF hdsts₁ rfl
        hfree hfreeBlk hjoinBlk hcpNext hagree hrest', fun _ _ h => by cases h; rfl⟩
    | cons _ _ =>
      apply MatchedStep.rawStuck
      simpa [hwrap.2.2.2, Lir.bindParams] using hstep₁
  | @consColdRedirect F B caller₁ caller₂ rest₁' rest₂' dst tmpReg coldLbl joinLbl coldBlk
      hlt hfn hF hdsts₁ hdsts₂ htmpGe hcoldPos hltLbl hcoldBlk hcoldSz hcoldTerm hjoinBlk hcpNext hagree hrest' =>
    cases vals with
    | nil => exact .rawStuck (by simpa [hdsts₁, Lir.bindParams] using hstep₁)
    | cons v vs =>
      cases vs with
      | cons _ _ => exact .rawStuck (by simpa [hdsts₁, Lir.bindParams] using hstep₁)
      | nil =>
        obtain ⟨jb, hbJ, hjp⟩ := hjoinBlk
        have hF' : (inlineProgram l raw).funcs[caller₂.fn]? = some (inlineFunc l F) := by
          rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
        have hs₁ : Lir.semStep raw { mem, ctx, stack := fr₁ :: caller₁ :: rest₁' } =
            .next { mem, ctx, stack := { caller₁ with env := caller₁.env.insert dst v, dsts := [] } :: rest₁' } false :=
          Lir.semStep_next.mpr (by simpa [hdsts₁, Lir.bindParams] using hstep₁)
        have hs₂_1 : Lir.semStep (inlineProgram l raw) { mem, ctx, stack := fr₂ :: caller₂ :: rest₂' } =
            .next { mem, ctx, stack := { caller₂ with env := caller₂.env.insert tmpReg v, dsts := [] } :: rest₂' } false :=
          Lir.semStep_next.mpr (by simpa [hdsts₂, Lir.bindParams] using hstep₂)
        have hs₂_2 : Lir.semStep (inlineProgram l raw)
            { mem, ctx, stack := { caller₂ with env := caller₂.env.insert tmpReg v, dsts := [] } :: rest₂' } =
            .next { mem, ctx, stack := { caller₂ with label := joinLbl, pos := 0, env := (caller₂.env.insert tmpReg v).insert dst v, dsts := [] } :: rest₂' } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { caller₂ with env := caller₂.env.insert tmpReg v, dsts := [] })
            hF' (by rw [hcoldPos.1]; exact hcoldBlk) (by rw [hcoldPos.2, hcoldSz])]
          have hfwd : ¬ (joinLbl ≤ caller₂.label) := by rw [hcoldPos.1]; dsimp only [Lir.Label] at hltLbl ⊢; omega
          simp [hcoldTerm, Lir.takeEdge, Lir.evalArgs, Lir.Arg.eval, hbJ, hjp, Lir.bindParams, hfwd]
        refine .sync hs₁ (.refl _) hs₂_1 (.free hs₂_2 (.refl _)) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext ((hagree.insert_ge htmpGe v).insert_same dst v) rfl) hrest',
          fun _ _ h => by cases h; rfl⟩
  | consResetDec hW hshape hwPos hkLe hw0 hw1 hwvals hlt hfn hF hdsts₁ hdsts₂ hinPos hinBlk
      hdrop hiLe hdecs hvals hx hfin hagree hrest' =>
    cases vals with
    | nil =>
      refine .sync (Lir.semStep_next.mpr (by simpa [hwPos.2.2, Lir.bindParams] using hstep₁)) (.refl _)
        (Lir.semStep_next.mpr (by simpa [hdsts₂, Lir.bindParams] using hstep₂)) (.refl _) (by omega) ?_
      exact ⟨rfl, rfl, .consResetDec hW hshape ⟨hwPos.1, hwPos.2.1, rfl⟩ hkLe hw0 hw1 hwvals hlt hfn hF hdsts₁ rfl
        hinPos hinBlk hdrop hiLe hdecs hvals hx hfin hagree hrest', fun _ _ h => by cases h; rfl⟩
    | cons _ _ => exact .rawStuck (by simpa [hwPos.2.2, Lir.bindParams] using hstep₁)
  | consResetDecCall hW hshape hwPos hjLt hw0 hw1 hwvals hlt hfn hF hdsts₁ hdsts₂ hinPos hinBlk
      hdrop hiLe hdecs hvals hx hfin hagree hrest' =>
    cases vals with
    | nil =>
      refine .sync (Lir.semStep_next.mpr (by simpa [hwPos.2.2, Lir.bindParams] using hstep₁)) (.refl _)
        (Lir.semStep_next.mpr (by simpa [hdsts₂, Lir.bindParams] using hstep₂)) (.refl _) (by omega) ?_
      exact ⟨rfl, rfl, .consResetDecCall hW hshape ⟨hwPos.1, hwPos.2.1, rfl⟩ hjLt hw0 hw1 hwvals hlt hfn hF hdsts₁ rfl
        hinPos hinBlk hdrop hiLe hdecs hvals hx hfin hagree hrest', fun _ _ h => by cases h; rfl⟩
    | cons _ _ => exact .rawStuck (by simpa [hwPos.2.2, Lir.bindParams] using hstep₁)
  | consResetSharedDec hc1 hlay1 hcls1 hwPos hlt hfn hF hdsts₁ hdsts₂ hinPos hfin hagree hrest' =>
    cases vals with
    | nil =>
      refine .sync (Lir.semStep_next.mpr (by simpa [hwPos.2.2.2, Lir.bindParams] using hstep₁)) (.refl _)
        (Lir.semStep_next.mpr (by simpa [hdsts₂, Lir.bindParams] using hstep₂)) (.refl _) (by omega) ?_
      exact ⟨rfl, rfl, .consResetSharedDec hc1 hlay1 hcls1 ⟨hwPos.1, hwPos.2.1, hwPos.2.2.1, rfl⟩
        hlt hfn hF hdsts₁ rfl hinPos hfin hagree hrest', fun _ _ h => by cases h; rfl⟩
    | cons _ _ => exact .rawStuck (by simpa [hwPos.2.2.2, Lir.bindParams] using hstep₁)
  | @consFusedCold1 F B pubBlk caller₁ caller₂ rest₁' rest₂' slot x dst idx1 idx2 tmp c2 lay2 cls mask args postJ inLbl
      hlt hfn hF hB hpos₂ hc2 hlay2 hcls2 hok2 hlen2 hstmt₂ hargsLt hds hnd hns hdsts₁ hdsts₂ htmpGe
      hcoldPos hcoldBlk halloc hcpNext hagree hrest' =>
    cases vals with
    | nil => exact .rawStuck (by simpa [hdsts₁, Lir.bindParams] using hstep₁)
    | cons slotVal vs =>
      cases vs with
      | cons _ _ => exact .rawStuck (by simpa [hdsts₁, Lir.bindParams] using hstep₁)
      | nil =>
        have hs₁ := Lir.semStep_next.mpr (by simpa [hdsts₁, Lir.bindParams] using hstep₁)
        have hs₂ := Lir.semStep_next.mpr (by simpa [hdsts₂, Lir.bindParams] using hstep₂)
        refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
        refine ⟨rfl, rfl, .consFusedColdMid (slotVal := slotVal) hlt hfn hF hB hpos₂ hc2 hlay2 hcls2 hok2 hlen2
          hstmt₂ hargsLt hds hnd hns rfl rfl htmpGe (by simp) (by simp) hcoldPos hcoldBlk halloc hcpNext ?_ hrest',
          fun _ _ h => by cases h; rfl⟩
        intro r hr hne
        rw [Lir.env_insert_ne _ _ (Ne.symm hne), Lir.env_insert_ne _ _ (by omega)]
        exact hagree r hr
  | consFusedColdMid hlt hfn hF hB hpos₂ hc2 hlay2 hcls2 hok2 hlen2 hstmt₂ hargsLt hds hnd hns
      hdsts₁ hdsts₂ htmpGe hslot₁ hslot₂ hcoldPos hcoldBlk halloc hcpNext hagreeNe hrest' =>
    cases vals with
    | nil =>
      refine .sync (Lir.semStep_next.mpr (by simpa [hdsts₁, Lir.bindParams] using hstep₁)) (.refl _)
        (Lir.semStep_next.mpr (by simpa [hdsts₂, Lir.bindParams] using hstep₂)) (.refl _) (by omega) ?_
      exact ⟨rfl, rfl, .consFusedColdMid hlt hfn hF hB hpos₂ hc2 hlay2 hcls2 hok2 hlen2 hstmt₂ hargsLt hds hnd hns
        rfl rfl htmpGe hslot₁ hslot₂ hcoldPos hcoldBlk halloc hcpNext hagreeNe hrest',
        fun _ _ h => by cases h; rfl⟩
    | cons _ _ => exact .rawStuck (by simpa [hdsts₁, Lir.bindParams] using hstep₁)
  | consFusedResetU1Dec hc1 hlay1 hcls1 hc2 hlay2 hcls2 hlen2 hdead hwPos hw0 hw1 hwvals
      hlt hfn hF hB hpos₂ hstmt₂ hsx hns hxLt hargsLt hx hdsts₁ hdsts₂ hinPos hb1 hjb hjbP hjbBody
      hcpNext hagree hrest' =>
    cases vals with
    | nil =>
      refine .sync (Lir.semStep_next.mpr (by simpa [hwPos.2.2.2, Lir.bindParams] using hstep₁)) (.refl _)
        (Lir.semStep_next.mpr (by simpa [hdsts₂, Lir.bindParams] using hstep₂)) (.refl _) (by omega) ?_
      exact ⟨rfl, rfl, .consFusedResetU1Dec hc1 hlay1 hcls1 hc2 hlay2 hcls2 hlen2 hdead
        ⟨hwPos.1, hwPos.2.1, hwPos.2.2.1, rfl⟩ hw0 hw1 hwvals
        hlt hfn hF hB hpos₂ hstmt₂ hsx hns hxLt hargsLt hx hdsts₁ rfl hinPos hb1 hjb hjbP hjbBody
        hcpNext hagree hrest', fun _ _ h => by cases h; rfl⟩
    | cons _ _ => exact .rawStuck (by simpa [hwPos.2.2.2, Lir.bindParams] using hstep₁)

private theorem matched_of_runtime_edge {l : Layout} {raw : Lir.Program} {F : Lir.Func}
    {mem : X86.Memory} {ctx : Lir.Word} {fr₁ : Lir.Frame} {rest₁ rest₂ : List Lir.Frame}
    {ρ0 : Lir.Env} {e : Lir.Edge}
    (hge : l.sourceCount ≤ fr₁.fn) (htop : fr₁.dsts = [])
    (hrest : StackRel l raw rest₁ rest₂)
    (hstep₁ : Lir.step raw { mem, ctx, stack := fr₁ :: rest₁ } =
      Lir.takeEdge F { mem, ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ0 e)
    (hstep₂ : Lir.step (inlineProgram l raw) { mem, ctx, stack := fr₁ :: rest₂ } =
      Lir.takeEdge F { mem, ctx, stack := fr₁ :: rest₂ } fr₁ rest₂ ρ0 e) :
    MatchedStep l raw { mem, ctx, stack := fr₁ :: rest₁ } { mem, ctx, stack := fr₁ :: rest₂ } := by
  cases ha : Lir.evalArgs ρ0 e.args with
  | none => exact .rawStuck (by simp [hstep₁, Lir.takeEdge, ha])
  | some vals =>
    cases htb : F.blocks[e.target]? with
    | none => exact .rawStuck (by simp [hstep₁, Lir.takeEdge, ha, htb])
    | some TB =>
      cases hbp : Lir.bindParams ρ0 TB.params vals with
      | none => exact .rawStuck (by simp [hstep₁, Lir.takeEdge, ha, htb, hbp])
      | some ρ' =>
        have hs₁ := Lir.semStep_next.mpr (hstep₁.trans (Lir.takeEdge_ok ha htb hbp))
        have hs₂ := Lir.semStep_next.mpr (hstep₂.trans (Lir.takeEdge_ok ha htb hbp))
        refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.runtime hge) hrest, fun _ _ h => by cases h; exact htop⟩

private theorem matched_of_edge {l : Layout} {raw : Lir.Program} {F : Lir.Func} {B : Lir.Block}
    {mem : X86.Memory} {ctx : Lir.Word} {fr₁ fr₂ : Lir.Frame} {rest₁ rest₂ : List Lir.Frame}
    {ρ₁ ρ₂ : Lir.Env} {e : Lir.Edge}
    (hlt : fr₁.fn < l.sourceCount) (hfn : fr₂.fn = fr₁.fn)
    (hF : raw.funcs[fr₁.fn]? = some F) (hB : F.blocks[fr₁.label]? = some B)
    (hdsts₁ : fr₁.dsts = []) (hdsts₂ : fr₂.dsts = [])
    (hlbl₂ : fr₂.label = newLabel l F fr₁.label + blockExtra l B)
    (hagree : AgreeBelow (freshBase F) ρ₁ ρ₂)
    (heLt : argsMax e.args 0 < freshBase F)
    (hrest : StackRel l raw rest₁ rest₂)
    (hstep₁ : Lir.step raw { mem, ctx, stack := fr₁ :: rest₁ } =
      Lir.takeEdge F { mem, ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ₁ e)
    (hstep₂ : Lir.step (inlineProgram l raw) { mem, ctx, stack := fr₂ :: rest₂ } =
      Lir.takeEdge (inlineFunc l F) { mem, ctx, stack := fr₂ :: rest₂ } fr₂ rest₂ ρ₂ (relabelEdge (newLabel l F) e)) :
    MatchedStep l raw { mem, ctx, stack := fr₁ :: rest₁ } { mem, ctx, stack := fr₂ :: rest₂ } := by
  have hargsEq : Lir.evalArgs ρ₁ e.args = Lir.evalArgs ρ₂ e.args := hagree.evalArgs_eq heLt
  cases hargs : Lir.evalArgs ρ₁ e.args with
  | none =>
    apply MatchedStep.rawStuck
    simp [hstep₁, Lir.takeEdge, hargs]
  | some vals =>
    have hargs₂ : Lir.evalArgs ρ₂ (relabelEdge (newLabel l F) e).args = some vals := by
      simpa [relabelEdge, hargsEq] using hargs
    cases hTB : F.blocks[e.target]? with
    | none =>
      apply MatchedStep.rawStuck
      simp [hstep₁, Lir.takeEdge, hargs, hTB]
    | some TB =>
      obtain ⟨TB', hTB', hparams⟩ := ChunkPos.entry_params l F hTB
      have hcp' := ChunkPos.entry l F hTB
      obtain ⟨hfwd, _, _⟩ := hagree.bindParams_agree TB.params vals
      cases hbp : Lir.bindParams ρ₁ TB.params vals with
      | none =>
        apply MatchedStep.rawStuck
        simp [hstep₁, Lir.takeEdge, hargs, hTB, hbp]
      | some ρ₁' =>
        obtain ⟨ρ₂', hbp₂, hagree'⟩ := hfwd ρ₁' hbp
        have hcharge : decide (newLabel l F e.target ≤ fr₂.label) = decide (e.target ≤ fr₁.label) := by
          rw [hlbl₂]
          by_cases hle : e.target ≤ fr₁.label
          · have h1 : newLabel l F e.target ≤ newLabel l F fr₁.label + blockExtra l B :=
              (newLabel_end_le_iff l F hB).mpr hle
            simp only [decide_eq_true hle, decide_eq_true h1]
          · have h1 : ¬ newLabel l F e.target ≤ newLabel l F fr₁.label + blockExtra l B := by
              intro hle'; exact hle ((newLabel_end_le_iff l F hB).mp hle')
            simp only [decide_eq_false hle, decide_eq_false h1]
        have hs₁ : Lir.semStep raw { mem, ctx, stack := fr₁ :: rest₁ } =
            .next { mem, ctx, stack := { fr₁ with label := e.target, pos := 0, env := ρ₁' } :: rest₁ }
              (decide (e.target ≤ fr₁.label)) := by
          apply Lir.semStep_next.mpr
          rw [hstep₁]
          exact Lir.takeEdge_ok hargs hTB hbp
        have hs₂ : Lir.semStep (inlineProgram l raw) { mem, ctx, stack := fr₂ :: rest₂ } =
            .next { mem, ctx, stack := { fr₂ with label := newLabel l F e.target, pos := 0, env := ρ₂' } :: rest₂ }
              (decide (e.target ≤ fr₁.label)) := by
          apply Lir.semStep_next.mpr
          rw [hstep₂, ← hcharge]
          exact Lir.takeEdge_ok hargs₂ (by simpa [relabelEdge] using hTB') (by simpa [hparams] using hbp₂)
        refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcp' hagree' (by simp [hdsts₁, hdsts₂])) hrest,
          fun _ _ h => by cases h; exact hdsts₁⟩

/-- Shared continuation matcher for inlined `.fusedResetReuse` (`live.length ≤ maxInlineResetLive`):
given synchronized prefixes reaching `s2 = reuseWrapper idx2 (.v slot :: args)` with `slot = 1`
in `raw` and `allocLbl` in `inl`, matches `raw_reuse_cold_exec` against `exec_inlineAlloc_blocks`. -/
private theorem match_fused_shared_alloc {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B pubBlk : Lir.Block} {caller₁ caller₂ : Lir.Frame}
    {rest₁ rest₂ : List Lir.Frame} {slot dst : Lir.VReg} {idx2 : Nat} {c2 : Lam.CtorInfo}
    {lay2 : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg} {postJ : List Lir.Stmt}
    {allocLbl pubLbl : Lir.Label} {aBase : Nat} {envD : Lir.Env}
    {s₁_0 s₁' s₂_0 s₂' : Lir.State} {b₁ : Bool} {c₁ : Nat} {mem_dec : X86.Memory} {ctx₁ : Lir.Word}
    (hlt : caller₁.fn < l.sourceCount) (hfn : caller₂.fn = caller₁.fn)
    (hF : raw.funcs[caller₁.fn]? = some F) (hB : F.blocks[caller₁.label]? = some B)
    (hpos₂ : caller₁.pos < B.body.size)
    (hc2 : l.ctors[idx2]? = some c2)
    (hlay2 : lay2 = Rt.Rc.CellLayout.ofFields c2.arity c2.tag)
    (hcls2 : lay2.cls? = some cls) (hok2 : lay2.ok = true) (hlen2 : args.length = c2.arity)
    (hstmt₂ : B.body[caller₁.pos] = .call [dst] (l.reuseWrapper idx2) (.v slot :: args))
    (hargsLt : argsMax args 0 < freshBase F)
    (hds : dst ≠ slot) (hnd : argsContainVReg dst args = false) (hns : argsContainVReg slot args = false)
    (haGe : freshBase F ≤ aBase)
    (halloc : InlineAllocShape (inlineFunc l F) allocLbl pubLbl aBase slot dst (.imm 1) lay2 cls args pubBlk postJ)
    (hcpNext : ChunkPos l F caller₁.label B (caller₁.pos + 1) pubLbl (1 + args.length))
    (hagreeD : AgreeBelow (freshBase F) caller₁.env envD)
    (hrest : StackRel l raw rest₁ rest₂)
    (hcBound : b₁.toNat + c₁ + 2 ≤ 12)
    (hs₁ : Lir.semStep raw s₁_0 = .next s₁' b₁)
    (hpref₁ : Sem.Star (Lir.semStep raw) s₁' c₁
      { mem := mem_dec, ctx := ctx₁, stack := { caller₁ with env := caller₁.env.insert slot 1, dsts := [] } :: rest₁ })
    (hs₂ : Lir.semStep (inlineProgram l raw) s₂_0 = .next s₂' false)
    (hpref₂ : Sem.Star (Lir.semStep (inlineProgram l raw)) s₂' 0
      { mem := mem_dec, ctx := ctx₁, stack := { fn := caller₂.fn, label := allocLbl, pos := 0, env := envD } :: rest₂ }) :
    MatchedStep l raw s₁_0 s₂_0 := by
  have hF' : (inlineProgram l raw).funcs[caller₂.fn]? = some (inlineFunc l F) := by
    rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
  have hargsIns : Lir.evalArgs (caller₁.env.insert slot 1) args = Lir.evalArgs caller₁.env args :=
    evalArgs_eq_of_agree_ne (bound := freshBase F) (slot := slot)
      (fun r _ hne => Lir.env_insert_ne _ _ (Ne.symm hne)) hargsLt hns
  have hargsEq : Lir.evalArgs caller₁.env args = Lir.evalArgs envD args :=
    hagreeD.evalArgs_eq hargsLt
  cases hargs : Lir.evalArgs caller₁.env args with
  | none =>
    have hargs' : List.mapM (Lir.Arg.eval (caller₁.env.insert slot 1)) args = none := hargsIns.trans hargs
    have hstk : Lir.step raw
        { mem := mem_dec, ctx := ctx₁, stack := { caller₁ with env := caller₁.env.insert slot 1, dsts := [] } :: rest₁ } = .stuck := by
      unfold Lir.step
      simp [hF, hB, hpos₂, hstmt₂, Lir.evalArgs, Lir.Arg.eval, hargs']
    have hr := reaches_of_star_reaches (Sem.Star.head hs₁ hpref₁) (.final (k := 0) (by rw [Lir.semStep, hstk]; exact .stuck))
    exact .rawStuckWithin (by cases b₁ <;> simp at hcBound ⊢ <;> omega) hr
  | some vals =>
    have h1tnz : Lir.Cond.holds .tnz .w64 1 1 = true := by decide
    have hraw2 := raw_reuse_cold_exec hr
      (fr := { caller₁ with env := caller₁.env.insert slot 1, dsts := [] })
      hF hB hpos₂ hc2 hlay2 hcls2 hok2 hlen2 hstmt₂ (by simp) (by rw [hargsIns, hargs]) h1tnz
      (rest := rest₁) (mem := mem_dec) (ctx := ctx₁)
    have hinl2 := exec_inlineAlloc_blocks (p := inlineProgram l raw) (F' := inlineFunc l F)
      (pubBlk := pubBlk) (fn := caller₂.fn) (base := allocLbl) (pubLbl := pubLbl)
      (aBase := aBase) (bound := freshBase F) (dst := dst) (lay := lay2) (cls := cls)
      (args := args) (vals := vals) (postJ := postJ) (pre := some (slot, .imm 1, 1))
      (env0 := envD) (mem := mem_dec) (ctx := ctx₁) (rest := rest₂)
      hF' halloc.pubGt haGe hargsLt hnd
      (fun sl a w h => by cases h; exact ⟨hds, hns, fun _ _ => rfl⟩)
      (by rw [← hargsEq, hargs]) halloc.pubParams halloc.pubBody
      halloc.b0 halloc.b1 halloc.b2 halloc.b3 halloc.b4 halloc.b5 halloc.pubLookup
    cases hres : evalAllocReserve lay2 cls mem_dec ctx₁ with
    | stuck =>
      rw [hres] at hraw2
      have hr := reaches_of_star_reaches (Sem.Star.head hs₁ hpref₁) hraw2
      exact .rawStuckWithin (by cases b₁ <;> simp at hcBound ⊢ <;> omega) hr
    | oom =>
      rw [hres] at hraw2 hinl2
      have hr₁ := reaches_of_star_reaches (Sem.Star.head hs₁ hpref₁) hraw2
      have hr₂ := reaches_of_star_reaches (Sem.Star.head hs₂ hpref₂) hinl2
      exact .sameOom (by cases b₁ <;> simp at hcBound ⊢ <;> omega) hr₁ (by simpa using hr₂)
    | ok addr mem₂ =>
      rw [hres] at hraw2 hinl2
      dsimp only at hraw2 hinl2
      cases hwf : writeFieldsMem mem₂ addr 0 vals with
      | none =>
        rw [hwf] at hraw2
        have hr := reaches_of_star_reaches (Sem.Star.head hs₁ hpref₁) hraw2
        exact .rawStuckWithin (by cases b₁ <;> simp at hcBound ⊢ <;> omega) hr
      | some mem' =>
        rw [hwf] at hraw2 hinl2
        obtain ⟨s₁'', hs₁₂, hstar₁₂⟩ := hraw2
        obtain ⟨env', hstar₂₂, hag'⟩ := hinl2
        have hagree' : AgreeBelow (freshBase F) ((caller₁.env.insert slot 1).insert dst addr) env' :=
          fun r hr' => (((hagreeD.insert_same slot 1).insert_same dst addr) r hr').trans (hag' r hr')
        refine .sync hs₁ (hpref₁.trans (.charge hs₁₂ hstar₁₂)) hs₂ (hpref₂.trans hstar₂₂)
          (by cases b₁ <;> simp at hcBound ⊢ <;> omega) ?_
        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
          fun _ _ h => by cases h; rfl⟩

/-! ## Master single-step / single-site simulation theorem -/

theorem step_match {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {s₁ s₂ : Lir.State} (hrel : StateRel l raw s₁ s₂) :
    MatchedStep l raw s₁ s₂ := by
  rcases s₁ with ⟨mem₁, ctx₁, stack₁⟩
  rcases s₂ with ⟨mem₂, ctx₂, stack₂⟩
  rcases hrel with ⟨hmem, hctx, hstack, htopDsts⟩
  dsimp only at hmem hctx hstack htopDsts
  subst mem₂; subst ctx₂
  cases hstack with
  | nil =>
    exact .rawStuck rfl
  | @consDecSlow F B wrapFr caller₁ caller₂ rest₁ rest₂ dst x inLbl
      hwrap hlt hfn hF hdsts₁ hdsts₂ hfree hfreeBlk hjoinBlk hcpNext hagree hrest =>
    obtain ⟨jb, hb5, hjp, hjbPos, hjbStmt⟩ := hjoinBlk
    have hF' : (inlineProgram l raw).funcs[caller₂.fn]? = some (inlineFunc l F) := by
      rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
    have hs₁ : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := wrapFr :: caller₁ :: rest₁ } =
        .next { mem := mem₁, ctx := ctx₁, stack := { caller₁ with env := caller₁.env.insert dst 1, dsts := [] } :: rest₁ } false := by
      apply Lir.semStep_next.mpr
      have hterm := Lir.step_term (p := raw) (F := decrementWrapper l.decProc)
        (B := (decrementWrapper l.decProc).blocks[0]!) (fr := wrapFr) (rest := caller₁ :: rest₁)
        (mem := mem₁) (ctx := ctx₁) (by rw [hwrap.1]; exact hr.decWrap)
        (by rw [hwrap.2.1]; rfl) (by rw [hwrap.2.2.1]; rfl)
      rw [hterm]
      simp [decrementWrapper, Lir.evalArgs, Lir.Arg.eval, hdsts₁, Lir.bindParams]
    have hs₂_1 : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := caller₂ :: rest₂ } =
        .next { mem := mem₁, ctx := ctx₁, stack := { caller₂ with label := inLbl + 5, pos := 0 } :: rest₂ } false := by
      apply Lir.semStep_next.mpr
      have hterm := Lir.step_term (p := inlineProgram l raw) (F := inlineFunc l F)
        (B := { body := #[.call [] l.decProc [.v x]], term := .jump ⟨inLbl + 5, []⟩, cold := B.cold })
        (fr := caller₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
        hF' (by rw [hfree.1]; exact hfreeBlk) (by rw [hfree.2]; rfl)
      rw [hterm]
      have hfwd : ¬ (inLbl + 5 ≤ caller₂.label) := by
        rw [hfree.1]; dsimp only [Lir.Label]; omega
      simp [Lir.takeEdge, Lir.evalArgs, hb5, hjp, Lir.bindParams, hfwd]
    have hjbGet : jb.body[0] = .assign dst (.arg (.imm 1)) := by
      rw [Array.getElem?_eq_getElem hjbPos, Option.some.injEq] at hjbStmt; exact hjbStmt
    have hs₂_2 : Lir.semStep (inlineProgram l raw)
        { mem := mem₁, ctx := ctx₁, stack := { caller₂ with label := inLbl + 5, pos := 0 } :: rest₂ } =
        .next { mem := mem₁, ctx := ctx₁, stack := { caller₂ with label := inLbl + 5, pos := 1, env := caller₂.env.insert dst 1, dsts := [] } :: rest₂ } false := by
      apply Lir.semStep_next.mpr
      have h1 := Lir.step_stmt (p := inlineProgram l raw) (F := inlineFunc l F) (B := jb)
        (fr := { caller₂ with label := inLbl + 5, pos := 0 }) (rest := rest₂)
        (mem := mem₁) (ctx := ctx₁) (ρ' := caller₂.env.insert dst 1) (mem' := mem₁)
        hF' hb5 hjbPos hjbGet rfl (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval])
      simpa [hdsts₂] using h1
    refine .sync hs₁ (.refl _) hs₂_1 (.free hs₂_2 (.refl _)) (by omega) ?_
    exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext (hagree.insert_same dst 1) rfl) hrest,
      fun _ _ h => by cases h; rfl⟩
  | consColdRedirect _ _ _ hdsts₁ _ _ _ _ _ _ _ _ _ _ _ =>
    have h0 := htopDsts _ _ rfl; rw [hdsts₁] at h0; cases h0
  | consFusedCold1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdsts₁ _ _ _ _ _ _ _ _ =>
    have h0 := htopDsts _ _ rfl; rw [hdsts₁] at h0; cases h0
  | @consResetDec F W B inBlk wFr caller₁ caller₂ rest₁ rest₂ dst x deadBase n base oldBase k i decBasePos
      xVal mask inLbl hW hshape hwPos hkLe hw0 hw1 hwvals hlt hfn hF hdsts₁ hdsts₂ hinPos hinBlk
      hdrop hiLe hdecs hvals hx hfin hagree hrest =>
    obtain ⟨s₁', s₂', s₁'', s₂'', b₁, b₂, c₁, c₂, hs₁, hst₁, hs₂, hst₂, hchg, hrel'⟩ :=
      step_resetDec_sync hr hW hshape hwPos hkLe hw0 hw1 hwvals hlt hfn hF hdsts₁ hdsts₂ hinPos hinBlk
        hdrop hiLe hdecs hvals hx hfin hagree hrest (mem := mem₁) (ctx := ctx₁)
    exact .sync hs₁ hst₁ hs₂ hst₂ hchg hrel'
  | @consResetDecCall F W B inBlk wFr caller₁ caller₂ rest₁ rest₂ dst x deadBase n base oldBase j i decBasePos
      xVal mask inLbl hW hshape hwPos hjLt hw0 hw1 hwvals hlt hfn hF hdsts₁ hdsts₂ hinPos hinBlk
      hdrop hiLe hdecs hvals hx hfin hagree hrest =>
    have hwEq : ({ fn := wFr.fn, label := base + 2 * j + 1, pos := 1, env := wFr.env, dsts := [] } : Lir.Frame) = wFr := by
      cases wFr; dsimp only at hwPos; obtain ⟨rfl, rfl, rfl⟩ := hwPos; rfl
    have sAfter : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := wFr :: caller₁ :: rest₁ } =
        .next { mem := mem₁, ctx := ctx₁, stack :=
          { fn := wFr.fn, label := base + 2 * (j + 1), pos := 0, env := wFr.env, dsts := [] } :: caller₁ :: rest₁ } false := by
      rw [← hwEq]
      exact raw_decLoop_after_call hW hshape hjLt
    obtain ⟨s₁', s₂', s₁'', s₂'', b₁, b₂, c₁, c₂, hs₁, hst₁, hs₂, hst₂, hchg, hrel'⟩ :=
      step_resetDec_sync hr (wFr := { fn := wFr.fn, label := base + 2 * (j + 1), pos := 0, env := wFr.env, dsts := [] })
        hW hshape (k := j + 1) ⟨rfl, rfl, rfl⟩ (by omega) hw0 hw1 hwvals hlt hfn hF
        hdsts₁ hdsts₂ hinPos hinBlk hdrop hiLe hdecs hvals hx hfin hagree hrest (mem := mem₁) (ctx := ctx₁)
    exact .sync sAfter (Sem.Star.head hs₁ hst₁) hs₂ hst₂ (by cases b₁ <;> simp at hchg ⊢ <;> omega) hrel'
  | @consResetSharedDec F B wFr caller₁ caller₂ rest₁ rest₂ slot x idx1 c1 lay1 cls1 decLbl
      hc1 hlay1 hcls1 hwPos hlt hfn hF hdsts₁ hdsts₂ hinPos hfin hagree hrest =>
    have hF' : (inlineProgram l raw).funcs[caller₂.fn]? = some (inlineFunc l F) := by
      rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
    have hwrapF : raw.funcs[wFr.fn]? = some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay1 cls1) := by
      rw [hwPos.1, hlay1]; exact hr.resetWrap idx1 c1 cls1 hc1 (by rwa [← hlay1])
    have hretBlk := mkResetWrapper_shared_ret_block l.isUniqueProc l.incProc l.decProc lay1 cls1
    have hs₁ : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := wFr :: caller₁ :: rest₁ } =
        .next { mem := mem₁, ctx := ctx₁, stack := { caller₁ with env := caller₁.env.insert slot 1, dsts := [] } :: rest₁ } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := wFr) hwrapF (by rw [hwPos.2.1]; exact hretBlk) (by rw [hwPos.2.2.1]; rfl)]
      simp [Lir.evalArgs, Lir.Arg.eval, hdsts₁, Lir.bindParams]
    cases hfin with
    | reset joinLbl hltLbl hdecBlk hjoin hcpNext =>
      obtain ⟨jb, hbJ, hjp⟩ := hjoin
      have hs₂ : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := caller₂ :: rest₂ } =
          .next { mem := mem₁, ctx := ctx₁, stack := { caller₂ with label := joinLbl, pos := 0, env := caller₂.env.insert slot 1, dsts := [] } :: rest₂ } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := caller₂) hF' (by rw [hinPos.1]; exact hdecBlk) (by rw [hinPos.2]; rfl)]
        have hfwd : ¬ (joinLbl ≤ caller₂.label) := by rw [hinPos.1]; dsimp only [Lir.Label] at hltLbl ⊢; omega
        simp [Lir.takeEdge, Lir.evalArgs, Lir.Arg.eval, hbJ, hjp, Lir.bindParams, hfwd, hdsts₂]
      refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
      exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext (hagree.insert_same slot 1) rfl) hrest,
        fun _ _ h => by cases h; rfl⟩
    | fused dst idx2 c2 lay2 cls args allocLbl pubLbl aBase pubBlk postJ
        hB hpos₂ hc2 hlay2 hcls2 hok2 hlen2 hstmt₂ hargsLt hds hnd hns haGe hltAlloc hdecBlk halloc hcpNext =>
      have hs₂ : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := caller₂ :: rest₂ } =
          .next { mem := mem₁, ctx := ctx₁, stack := { fn := caller₂.fn, label := allocLbl, pos := 0, env := caller₂.env } :: rest₂ } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := caller₂) hF' (by rw [hinPos.1]; exact hdecBlk) (by rw [hinPos.2]; rfl)]
        have hfwd : ¬ (allocLbl ≤ caller₂.label) := by rw [hinPos.1]; dsimp only [Lir.Label] at hltAlloc ⊢; omega
        have hfrA : ({ caller₂ with label := allocLbl, pos := 0 } : Lir.Frame) =
            { fn := caller₂.fn, label := allocLbl, pos := 0, env := caller₂.env } := by
          cases caller₂; dsimp only at hdsts₂; subst hdsts₂; rfl
        rw [← hfrA]
        simp [Lir.takeEdge, Lir.evalArgs, halloc.b0, Lir.bindParams, hfwd]
      exact match_fused_shared_alloc hr hlt hfn hF hB hpos₂ hc2 hlay2 hcls2 hok2 hlen2 hstmt₂
        hargsLt hds hnd hns haGe halloc hcpNext hagree hrest (by simp) hs₁ (.refl _) hs₂ (.refl _)
  | @consFusedColdMid F B pubBlk caller₁ caller₂ rest₁ rest₂ slot x dst idx1 idx2 tmp c2 lay2 cls mask
      args postJ inLbl slotVal hlt hfn hF hB hpos₂ hc2 hlay2 hcls2 hok2 hlen2 hstmt₂ hargsLt hds hnd hns
      hdsts₁ hdsts₂ htmpGe hslot₁ hslot₂ hcoldPos hcoldBlk halloc hcpNext hagreeNe hrest =>
    have hF' : (inlineProgram l raw).funcs[caller₂.fn]? = some (inlineFunc l F) := by
      rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
    have hargsEq : Lir.evalArgs caller₁.env args = Lir.evalArgs caller₂.env args :=
      evalArgs_eq_of_agree_ne hagreeNe hargsLt hns
    cases hargs : Lir.evalArgs caller₁.env args with
    | none =>
      have hargs' : List.mapM (Lir.Arg.eval caller₁.env) args = none := hargs
      exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₂, hstmt₂, Lir.evalArgs, Lir.Arg.eval, hslot₁, hargs'])
    | some vals =>
      by_cases htag : Lir.Cond.holds .tnz .w64 slotVal 1 = true
      · have hraw := raw_reuse_cold_exec hr hF hB hpos₂ hc2 hlay2 hcls2 hok2 hlen2 hstmt₂ hslot₁ hargs htag
          (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
        have sBr : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := caller₂ :: rest₂ } =
            .next { mem := mem₁, ctx := ctx₁, stack := { fn := caller₂.fn, label := inLbl + 3, pos := 0, env := caller₂.env } :: rest₂ } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := caller₂) hF' (by rw [hcoldPos.1]; exact hcoldBlk) (by rw [hcoldPos.2]; rfl)]
          have hfwd : ¬ (inLbl + 3 ≤ caller₂.label) := by rw [hcoldPos.1]; dsimp only [Lir.Label]; omega
          have hfr3 : ({ caller₂ with label := inLbl + 3, pos := 0 } : Lir.Frame) =
              { fn := caller₂.fn, label := inLbl + 3, pos := 0, env := caller₂.env } := by
            cases caller₂; dsimp only at hdsts₂; subst hdsts₂; rfl
          rw [← hfr3]
          simp [Lir.Arg.eval, hslot₂, htag, Lir.takeEdge, Lir.evalArgs, halloc.b0, Lir.bindParams, hfwd]
        have hinl := exec_inlineAlloc_blocks (p := inlineProgram l raw) (F' := inlineFunc l F)
          (pubBlk := pubBlk) (fn := caller₂.fn) (base := inLbl + 3) (pubLbl := inLbl + 9)
          (aBase := tmp + 2) (bound := freshBase F) (dst := dst) (lay := lay2) (cls := cls)
          (args := args) (vals := vals) (postJ := postJ) (pre := some (slot, .v (tmp + 1), slotVal))
          (env0 := caller₂.env) (mem := mem₁) (ctx := ctx₁) (rest := rest₂)
          hF' halloc.pubGt (by omega) hargsLt hnd
          (fun sl a w h => by
            cases h; exact ⟨hds, hns, fun env' hagA => by
              simp only [Lir.Arg.eval]; rw [← hagA (tmp + 1) (by omega), hslot₂]⟩)
          (by rw [← hargsEq, hargs]) halloc.pubParams halloc.pubBody
          halloc.b0 halloc.b1 halloc.b2 halloc.b3 halloc.b4 halloc.b5 halloc.pubLookup
        cases hres : evalAllocReserve lay2 cls mem₁ ctx₁ with
        | stuck => rw [hres] at hraw; exact .rawStuckWithin (by omega) hraw
        | oom =>
          rw [hres] at hraw hinl
          exact .sameOom (by omega) hraw (.free sBr hinl)
        | ok addr mem₂ =>
          rw [hres] at hraw hinl
          dsimp only at hraw hinl
          cases hwf : writeFieldsMem mem₂ addr 0 vals with
          | none => rw [hwf] at hraw; exact .rawStuckWithin (by omega) hraw
          | some mem' =>
            rw [hwf] at hraw hinl
            obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
            obtain ⟨env', hstar₂, hag'⟩ := hinl
            have hagree' : AgreeBelow (freshBase F) (caller₁.env.insert dst addr) env' := fun r hr' => by
              rw [← hag' r hr']
              by_cases hrd : r = dst
              · subst hrd; simp
              · rw [Lir.env_insert_ne _ _ (Ne.symm hrd), Lir.env_insert_ne _ _ (Ne.symm hrd)]
                by_cases hrs : r = slot
                · subst hrs; simp [hslot₁]
                · rw [Lir.env_insert_ne _ _ (Ne.symm hrs)]; exact hagreeNe r hr' hrs
            refine .sync hs₁ hstar₁ sBr hstar₂ (by simp) ?_
            exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
              fun _ _ h => by cases h; rfl⟩
      · have hcell : Lir.Cond.holds .tnz .w64 slotVal 1 = false := by simpa using htag
        have hraw := raw_reuse_hot_exec hr hF hB hpos₂ hc2 hlay2 hcls2 hlen2 hstmt₂ hslot₁ hargs hcell
          (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
        dsimp only at hraw
        let envPub := (caller₂.env.insert slot slotVal).insert dst slotVal
        have sBr : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := caller₂ :: rest₂ } =
            .next { mem := mem₁, ctx := ctx₁, stack := { fn := caller₂.fn, label := inLbl + 9, pos := 0, env := envPub } :: rest₂ } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := caller₂) hF' (by rw [hcoldPos.1]; exact hcoldBlk) (by rw [hcoldPos.2]; rfl)]
          have hfwd : ¬ (inLbl + 9 ≤ caller₂.label) := by rw [hcoldPos.1]; dsimp only [Lir.Label]; omega
          have hfrP : ({ caller₂ with label := inLbl + 9, pos := 0, env := envPub } : Lir.Frame) =
              { fn := caller₂.fn, label := inLbl + 9, pos := 0, env := envPub } := by
            cases caller₂; dsimp only at hdsts₂; subst hdsts₂; rfl
          rw [← hfrP]
          simp [Lir.Arg.eval, hslot₂, hcell, Lir.takeEdge, Lir.evalArgs, halloc.pubLookup, halloc.pubParams, Lir.bindParams, hfwd, envPub]
        have hargsPub : Lir.evalArgs envPub args = some vals := by
          simp only [envPub]
          rw [evalArgs_insert_not_mem (argsContainVReg_false hnd),
            evalArgs_insert_not_mem (argsContainVReg_false hns), ← hargsEq, hargs]
        have hpubBody' : pubBlk.body.toList =
            [] ++ (.store .w64 (cellAddr dst 0) (.imm (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1)) :: mkFieldStores dst 0 args) ++ postJ := by
          simpa [cellAddr] using halloc.pubBody
        have hwr := exec_writeReuse (p := inlineProgram l raw) (F := inlineFunc l F) (B := pubBlk)
          (fn := caller₂.fn) (lbl := inLbl + 9) (base := dst) (addr := slotVal)
          (hdr := Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1)
          (ctx := ctx₁) (rest := rest₂) (env := envPub)
          hF' halloc.pubLookup (by simp [envPub]) hpubBody' hargsPub (mem := mem₁)
        cases hwm : writeReuseMem mem₁ slotVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals with
        | none => rw [hwm] at hraw; exact .rawStuckWithin (by omega) hraw
        | some mem' =>
          rw [hwm] at hraw hwr
          obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
          have hagree' : AgreeBelow (freshBase F) (caller₁.env.insert dst slotVal) envPub := fun r hr' => by
            simp only [envPub]
            by_cases hrd : r = dst
            · subst hrd; simp
            · rw [Lir.env_insert_ne _ _ (Ne.symm hrd), Lir.env_insert_ne _ _ (Ne.symm hrd)]
              by_cases hrs : r = slot
              · subst hrs; simp [hslot₁]
              · rw [Lir.env_insert_ne _ _ (Ne.symm hrs)]; exact hagreeNe r hr' hrs
          refine .sync hs₁ hstar₁ sBr (by simpa using hwr) (by simp) ?_
          exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
            fun _ _ h => by cases h; rfl⟩
  | @consFusedResetU1Dec F B joinBlk wFr caller₁ caller₂ rest₁ rest₂ slot x dst idx1 idx2 deadIdx tmp
      c1 c2 lay1 lay2 cls mask xVal args postJ inLbl
      hc1 hlay1 hcls1 hc2 hlay2 hcls2 hlen2 hdead hwPos hw0 hw1 hwvals
      hlt hfn hF hB hpos₂ hstmt₂ hsx hns hxLt hargsLt hx hdsts₁ hdsts₂ hinPos hb1 hjb hjbP hjbBody
      hcpNext hagree hrest =>
    have hF' : (inlineProgram l raw).funcs[caller₂.fn]? = some (inlineFunc l F) := by
      rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
    have hwF : raw.funcs[wFr.fn]? = some (mkResetUWrapper l.decProc lay1 cls) := by
      rw [hwPos.1, hlay1]; exact hr.resetUWrap idx1 c1 cls hc1 (by rwa [← hlay1])
    have hshape := mkResetUWrapper_decLoopShape l.decProc lay1 cls
    obtain ⟨hdeadLt, _, hdeadNext⟩ := deadFields_singleton_split hdead
    have hwEq : ({ fn := wFr.fn, label := 1 + 2 * deadIdx + 1, pos := 1, env := wFr.env, dsts := [] } : Lir.Frame) = wFr := by
      cases wFr; dsimp only at hwPos; obtain ⟨_, rfl, rfl, rfl⟩ := hwPos; rfl
    have sAfter : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := wFr :: caller₁ :: rest₁ } =
        .next { mem := mem₁, ctx := ctx₁, stack :=
          { fn := wFr.fn, label := 1 + 2 * (deadIdx + 1), pos := 0, env := wFr.env, dsts := [] } :: caller₁ :: rest₁ } false := by
      rw [← hwEq]; exact raw_decLoop_after_call hwF hshape hdeadLt
    have hloop := raw_decLoop_step hr hwF hshape hw0 hw1 hdsts₁ hwvals (deadIdx + 1) (by omega)
      (mem := mem₁) (ctx := ctx₁) (rest := rest₁)
    rw [hdeadNext] at hloop; dsimp only at hloop
    have hargsIns : Lir.evalArgs (caller₁.env.insert slot xVal) args = Lir.evalArgs caller₁.env args :=
      evalArgs_eq_of_agree_ne (bound := freshBase F) (slot := slot)
        (fun r _ hne => Lir.env_insert_ne _ _ (Ne.symm hne)) hargsLt hns
    have hargsEq : Lir.evalArgs caller₁.env args = Lir.evalArgs caller₂.env args :=
      hagree.evalArgs_eq hargsLt
    cases hargs : Lir.evalArgs caller₁.env args with
    | none =>
      have hargs' : List.mapM (Lir.Arg.eval (caller₁.env.insert slot xVal)) args = none := hargsIns.trans hargs
      have hstk : Lir.step raw
          { mem := mem₁, ctx := ctx₁, stack := { caller₁ with env := caller₁.env.insert slot xVal, dsts := [] } :: rest₁ } = .stuck := by
        unfold Lir.step
        simp [hF, hB, hpos₂, hstmt₂, Lir.evalArgs, Lir.Arg.eval, hargs']
      exact .rawStuckWithin (by omega)
        (.free sAfter (reaches_of_star_reaches hloop (.final (k := 0) (by rw [Lir.semStep, hstk]; exact .stuck))))
    | some vals =>
      have hraw2 := raw_reuseU_exec hr (slotVal := xVal)
        (fr := { caller₁ with env := caller₁.env.insert slot xVal, dsts := [] })
        hF hB hpos₂ hc2 hlay2 hcls2 hlen2 hstmt₂ (by simp) (by rw [hargsIns, hargs])
        (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
      dsimp only at hraw2
      cases hwm : writeReuseMem mem₁ xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals with
      | none =>
        rw [hwm] at hraw2
        exact .rawStuckWithin (by omega) (.free sAfter (reaches_of_star_reaches hloop hraw2))
      | some mem' =>
        rw [hwm] at hraw2
        obtain ⟨s₁'', hs₁₂, hstar₂⟩ := hraw2
        have hx₂ : caller₂.env[x]? = some xVal := by rw [← hagree x hxLt, hx]
        have sJmp : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := caller₂ :: rest₂ } =
            .next { mem := mem₁, ctx := ctx₁, stack := { fn := caller₂.fn, label := inLbl + 2, pos := 0, env := caller₂.env, dsts := [] } :: rest₂ } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := caller₂) hF' (by rw [hinPos.1]; exact hb1)
            (by rw [hinPos.2]; simp [mkShellStores_length])]
          have hfwd : ¬ (inLbl + 2 ≤ caller₂.label) := by rw [hinPos.1]; dsimp only [Lir.Label]; omega
          have hfrJ : ({ caller₂ with label := inLbl + 2, pos := 0 } : Lir.Frame) =
              { fn := caller₂.fn, label := inLbl + 2, pos := 0, env := caller₂.env, dsts := [] } := by
            cases caller₂; dsimp only at hdsts₂; subst hdsts₂; rfl
          rw [← hfrJ]
          simp [Lir.takeEdge, Lir.evalArgs, hjb, hjbP, Lir.bindParams, hfwd]
        have hjoin := exec_fusedResetU1_join (p := inlineProgram l raw) (F' := inlineFunc l F) (joinBlk := joinBlk)
          (fn := caller₂.fn) (joinLbl := inLbl + 2) (slot := slot) (x := x) (dst := dst)
          (lay2 := lay2) (cls := cls) (args := args) (postJ := postJ)
          (xVal := xVal) (ctx := ctx₁) (vals := vals) (env := caller₂.env) (mem := mem₁) (mem' := mem') (rest := rest₂)
          hF' hjb hsx hx₂ (by rw [← hargsEq, hargs]) hjbBody hwm
        refine .sync sAfter (hloop.trans (.charge hs₁₂ hstar₂)) sJmp hjoin (by simp) ?_
        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext ((hagree.insert_same slot xVal).insert_same dst xVal) rfl) hrest,
          fun _ _ h => by cases h; rfl⟩
  | @cons fr₁ fr₂ rest₁ rest₂ hfr hrest =>
    have htop : fr₁.dsts = [] := htopDsts fr₁ rest₁ rfl
    cases hfr with
    | emptySource _ hF hnone =>
      exact .rawStuck (by unfold Lir.step; simp [hF, hnone])
    | runtime hge =>
      have hfunEq : (inlineProgram l raw).funcs[fr₁.fn]? = raw.funcs[fr₁.fn]? :=
        inlineProgram_get_ge l raw hge
      cases hF : raw.funcs[fr₁.fn]? with
      | none => exact .rawStuck (by unfold Lir.step; simp [hF])
      | some F =>
        have hF' : (inlineProgram l raw).funcs[fr₁.fn]? = some F := by rw [hfunEq, hF]
        cases hB : F.blocks[fr₁.label]? with
        | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB])
        | some B =>
          by_cases hpos : fr₁.pos < B.body.size
          · cases hs : B.body[fr₁.pos] with
            | call rs g as =>
              cases hargs : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hargs])
              | some vs =>
                obtain ⟨heFwd, _, _⟩ := enter_rel l raw (g := g) (vs := vs)
                cases hent : Lir.enter raw g vs with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hargs, hent])
                | some callee₁ =>
                  obtain ⟨callee₂, hent₂, hfrCallee, hdstCallee⟩ := heFwd callee₁ hent
                  have hs₁ := Lir.semStep_next.mpr (Lir.step_call (p := raw) (mem := mem₁) (ctx := ctx₁) (rest := rest₁) hF hB hpos hs hargs hent)
                  have hs₂ := Lir.semStep_next.mpr (Lir.step_call (p := inlineProgram l raw) (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hF' hB hpos hs hargs hent₂)
                  refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                  exact ⟨rfl, rfl, .cons hfrCallee (.cons (.runtime hge) hrest),
                    fun _ _ h => by cases h; exact hdstCallee⟩
            | assign x r =>
              cases hx : (Lir.Stmt.assign x r).exec fr₁.env mem₁ ctx₁ with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hx])
              | some p =>
                rcases p with ⟨ρ', mem'⟩
                have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hs rfl hx)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hB hpos hs rfl hx)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons (.runtime hge) hrest, fun _ _ h => by cases h; exact htop⟩
            | limb r1 r2 op =>
              cases hx : (Lir.Stmt.limb r1 r2 op).exec fr₁.env mem₁ ctx₁ with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hx])
              | some p =>
                rcases p with ⟨ρ', mem'⟩
                have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hs rfl hx)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hB hpos hs rfl hx)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons (.runtime hge) hrest, fun _ _ h => by cases h; exact htop⟩
            | store w m a =>
              cases hx : (Lir.Stmt.store w m a).exec fr₁.env mem₁ ctx₁ with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hx])
              | some p =>
                rcases p with ⟨ρ', mem'⟩
                have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hs rfl hx)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hB hpos hs rfl hx)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons (.runtime hge) hrest, fun _ _ h => by cases h; exact htop⟩
          · have hposGe : ¬ fr₁.pos < B.body.size := hpos
            cases ht : B.term with
            | jump e =>
              exact matched_of_runtime_edge (F := F) (ρ0 := fr₁.env) (e := e) hge htop hrest
                (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht])
                (by unfold Lir.step; simp only [hF', hB, hposGe, ↓reduceDIte, ht])
            | br c w a b' t f =>
              cases ha : a.eval fr₁.env with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha])
              | some va =>
                cases hb : b'.eval fr₁.env with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha, hb])
                | some vb =>
                  exact matched_of_runtime_edge (F := F) (ρ0 := fr₁.env) (e := if c.holds w va vb then t else f)
                    hge htop hrest
                    (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb])
                    (by unfold Lir.step; simp only [hF', hB, hposGe, ↓reduceDIte, ht, ha, hb])
            | brOvf o x a b' ok ovf =>
              cases ha : a.eval fr₁.env with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha])
              | some va =>
                cases hb : b'.eval fr₁.env with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha, hb])
                | some vb =>
                  exact matched_of_runtime_edge (F := F) (ρ0 := fr₁.env.insert x (o.eval va vb).1)
                    (e := if (o.eval va vb).2 then ovf else ok) hge htop hrest
                    (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb])
                    (by unfold Lir.step; simp only [hF', hB, hposGe, ↓reduceDIte, ht, ha, hb])
            | ret as =>
              cases hargs : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs])
              | some vals =>
                exact matched_of_ret (vals := vals)
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, hargs]; rfl)
                  (by unfold Lir.step; simp only [hF', hB, hposGe, ↓reduceDIte, ht, hargs]; rfl) hrest
            | tail g as =>
              cases hargs : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs])
              | some vs =>
                obtain ⟨heFwd, _, _⟩ := enter_rel l raw (g := g) (vs := vs)
                cases hent : Lir.enter raw g vs with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs, hent])
                | some callee₁ =>
                  obtain ⟨callee₂, hent₂, hfrCallee, hdstCallee⟩ := heFwd callee₁ hent
                  have hs₁ : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } =
                      .next { mem := mem₁, ctx := ctx₁, stack := callee₁ :: rest₁ } true := by
                    apply Lir.semStep_next.mpr; unfold Lir.step; simp [hF, hB, hposGe, ht, hargs, hent]
                  have hs₂ : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } =
                      .next { mem := mem₁, ctx := ctx₁, stack := callee₂ :: rest₂ } true := by
                    apply Lir.semStep_next.mpr; unfold Lir.step; simp [hF', hB, hposGe, ht, hargs, hent₂]
                  refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
                  exact ⟨rfl, rfl, .cons hfrCallee hrest, fun _ _ h => by cases h; exact hdstCallee⟩
            | fail r =>
              refine .sameFinal (r := .resource r) ?_ ?_
              · rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hposGe, ht]; exact .fail
              · rw [Lir.semStep]; unfold Lir.step; simp [hF', hB, hposGe, ht]; exact .fail
            | trap =>
              refine .sameFinal (r := .trap) ?_ ?_
              · rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hposGe, ht]; exact .trap
              · rw [Lir.semStep]; unfold Lir.step; simp [hF', hB, hposGe, ht]; exact .trap
    | @source F B _ _ hlt hfn hF hcp0 hagree hdsts =>
      have hdsts₂ : fr₂.dsts = [] := hdsts.trans htop
      have hF' : (inlineProgram l raw).funcs[fr₂.fn]? = some (inlineFunc l F) := by
        rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
      obtain ⟨tmp, params, acc, rest0, hcp⟩ := hcp0
      have hB : F.blocks[fr₁.label]? = some B := hcp.bLookup
      by_cases hpos : fr₁.pos < B.body.size
      · obtain ⟨restStmts, hrest0⟩ := ChunkPos.rest_cons hcp hpos
        let s := B.body[fr₁.pos]
        have hsMem : s ∈ B.body.toList := by
          have : B.body.toList[fr₁.pos]? = some s := by
            rw [Array.getElem?_toList, Array.getElem?_eq_getElem hpos]
          exact List.mem_of_getElem? this
        have hsMax : stmtMax s 0 < freshBase F := by
          have := stmt_le_maxVReg hB hsMem; unfold freshBase; omega
        by_cases hpair : ∃ s2 rest2 fp, restStmts = s2 :: rest2 ∧ classifyPair l s s2 = some fp
        · obtain ⟨s2, rest2, fp, hrest2, hp⟩ := hpair
          have hrestPair : rest0 = s :: s2 :: rest2 := by rw [hrest0, hrest2]
          obtain ⟨hpos2, hget2?⟩ := ChunkPos.rest_cons2 hcp hrestPair
          have hget2 : B.body[fr₁.pos + 1] = s2 := by
            rw [Array.getElem?_eq_getElem hpos2, Option.some.injEq] at hget2?; exact hget2?
          have hs2Mem : s2 ∈ B.body.toList := by
            have : B.body.toList[fr₁.pos + 1]? = some s2 := by
              rw [Array.getElem?_toList, Array.getElem?_eq_getElem hpos2, hget2]
            exact List.mem_of_getElem? this
          cases fp with
          | fusedResetReuse slot x dst idx1 lay1 mask idx2 lay2 cls args =>
            obtain ⟨hc1, hc2, hle, hdead, hdx, hsx, hds, hnd, hns⟩ := classifyPair_eq_fusedResetReuse hp
            obtain ⟨c1, hc1', hs1Eq0, hlay1, hcls1, _, _⟩ := classify_eq_reset hc1
            obtain ⟨c2, hc2', hs2Eq0, hlay2, hcls2, hlen2, hok2, _, _⟩ := classify_eq_reuse hc2
            have hs1Eq : B.body[fr₁.pos] = .call [slot] (l.resetWrapper idx1) [.v x, .imm mask] := hs1Eq0
            have hs2Eq : B.body[fr₁.pos + 1] = .call [dst] (l.reuseWrapper idx2) (.v slot :: args) := hget2.trans hs2Eq0
            have hxLt : (x : Nat) < freshBase F := by
              have h1 := call_args_lt_freshBase hB (by rw [← hs1Eq]; exact hsMem)
              have h2 : x ≤ argsMax [.v x, .imm mask] 0 := mem_le_argsMax (by simp)
              dsimp only [Lir.VReg] at h2 ⊢; omega
            have hargsLt : argsMax args 0 < freshBase F := by
              have h1 := call_args_lt_freshBase hB (by rw [← hs2Eq, hget2]; exact hs2Mem)
              have h2 : argsMax args 0 ≤ argsMax (.v slot :: args) 0 := by
                unfold argsMax; rw [List.foldl_cons]; exact argsMax_mono_local args (Nat.zero_le _)
              omega
            have hxEq : fr₁.env[x]? = fr₂.env[x]? := hagree x hxLt
            cases hx : fr₁.env[x]? with
            | none =>
              exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs1Eq, Lir.evalArgs, Lir.Arg.eval, hx])
            | some xVal =>
              cases hu : evalUniqueCheck xVal mem₁ with
              | stuck =>
                exact .rawStuckWithin (by omega)
                  (raw_reset_stuck hr hF hB hpos hc1' hlay1 hcls1 hs1Eq hx hu)
              | shared =>
                by_cases hliveLe : (liveFields lay1.nobj mask).length ≤ maxInlineResetLive
                · obtain ⟨hcpNext, ⟨pubBlk, postJ, halloc⟩, hdec2, _, hinlShared⟩ :=
                    inl_fusedResetReuse_inline_exec hr (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp hrestPair hp
                      hpos rfl hpos2 hget2 (by rw [← hxEq, hx]) hxLt hargsLt hliveLe
                      (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                  have hrawS := raw_reset_shared_exec hr hF hB hpos hc1' hlay1 hcls1 hs1Eq hx hu
                    (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                  dsimp only at hrawS
                  have hinlS := hinlShared hu
                  have hmaxL : (liveFields lay1.nobj mask).length ≤ 6 := hliveLe
                  cases hincEv : evalSharedIncList xVal (liveFields lay1.nobj mask) mem₁ with
                  | oom =>
                    rw [hincEv] at hrawS hinlS
                    exact .sameOom (by omega) hrawS hinlS
                  | stuck =>
                    rw [hincEv] at hrawS
                    exact .rawStuckWithin (by omega) hrawS
                  | ok mem_inc =>
                    rw [hincEv] at hrawS hinlS
                    dsimp only at hrawS hinlS
                    cases hdecEv : evalDecSite xVal mem_inc with
                    | stuck =>
                      rw [hdecEv] at hrawS
                      exact .rawStuckWithin (by omega) hrawS
                    | free =>
                      rw [hdecEv] at hrawS hinlS
                      obtain ⟨wEnv', s₁', hs₁, hstar₁⟩ := hrawS
                      obtain ⟨env1, s₂', hs₂, hstar₂, hag1⟩ := hinlS
                      have hagree' : AgreeBelow (freshBase F) fr₁.env env1 := fun r hr' => (hagree r hr').trans (hag1 r hr')
                      have hdecGe : l.sourceCount ≤ l.decProc := by simp [Layout.decProc, Layout.incProc]; omega
                      have hposEq : fr₁.pos + 1 + 1 = fr₁.pos + 2 := by omega
                      refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp; omega) ?_
                      refine ⟨rfl, rfl, .cons (.runtime hdecGe)
                        (.consResetSharedDec hc1' hlay1 hcls1 ⟨rfl, rfl, rfl, rfl⟩ hlt hfn hF rfl rfl ⟨rfl, rfl⟩
                          (.fused dst idx2 c2 lay2 cls args _ _ _ pubBlk postJ hB hpos2 hc2' hlay2 hcls2 hok2 hlen2
                            hs2Eq hargsLt hds hnd hns (by have := hcp.tmpGe; omega)
                            (by dsimp only [Lir.Label]; omega) hdec2 halloc (by simpa [hposEq] using hcpNext))
                          hagree' hrest),
                        fun _ _ h => by cases h; rfl⟩
                    | ok mem_dec =>
                      rw [hdecEv] at hrawS hinlS
                      obtain ⟨s₁', hs₁, hstar₁⟩ := hrawS
                      obtain ⟨envD, s₂', hs₂, hstar₂, hagD⟩ := hinlS
                      have hagreeD : AgreeBelow (freshBase F) fr₁.env envD := fun r hr' => (hagree r hr').trans (hagD r hr')
                      have hposEq : fr₁.pos + 1 + 1 = fr₁.pos + 2 := by omega
                      exact match_fused_shared_alloc hr (caller₁ := { fr₁ with pos := fr₁.pos + 1 })
                        (caller₂ := fr₂) hlt hfn hF hB hpos2 hc2' hlay2 hcls2 hok2 hlen2 hs2Eq
                        hargsLt hds hnd hns (by have := hcp.tmpGe; omega) halloc
                        (by simpa [hposEq] using hcpNext) hagreeD hrest (by simp; omega)
                        hs₁ hstar₁ hs₂ hstar₂
                · obtain ⟨hcpNext, ⟨pubBlk, postJ, halloc⟩, hcoldBlk, _, hinlCold⟩ :=
                    inl_fusedResetReuse_fallback_exec hr (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp hrestPair hp
                      hpos rfl hpos2 hget2 (by rw [← hxEq, hx]) hxLt hargsLt hliveLe
                      (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                  obtain ⟨callee, env', s₂', hentRaw, hag', hs₂, hstar₂⟩ := hinlCold hu
                  have hs₁ : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } =
                      .next { mem := mem₁, ctx := ctx₁, stack := callee :: { fr₁ with pos := fr₁.pos + 1, dsts := [slot] } :: rest₁ } true := by
                    apply Lir.semStep_next.mpr
                    exact Lir.step_call hF hB hpos hs1Eq (by simp [Lir.evalArgs, Lir.Arg.eval, hx]) hentRaw
                  have hwrapGe : l.sourceCount ≤ l.resetWrapper idx1 := by
                    simp [Layout.resetWrapper, Layout.init, Layout.incProc]; omega
                  have hcalleeFn : callee.fn = l.resetWrapper idx1 ∧ callee.dsts = [] := by
                    simp only [Lir.enter] at hentRaw
                    cases hrf : raw.funcs[l.resetWrapper idx1]? with
                    | none => simp [hrf] at hentRaw
                    | some wf =>
                      simp only [hrf, Option.bind_eq_bind, Option.bind_some] at hentRaw
                      cases hbp : Lir.bindParams {} wf.params [xVal, mask] with
                      | none => simp [hbp] at hentRaw
                      | some ρ => simp only [hbp, Option.bind_some, Option.some.injEq] at hentRaw; subst hentRaw; exact ⟨rfl, rfl⟩
                  have hagree' : AgreeBelow (freshBase F) fr₁.env env' := fun r hr' => (hagree r hr').trans (hag' r hr')
                  have hposEq : fr₁.pos + 1 + 1 = fr₁.pos + 2 := by omega
                  refine .sync hs₁ (.refl _) hs₂ hstar₂ (by simp) ?_
                  exact ⟨rfl, rfl, .cons (.runtime (by rw [hcalleeFn.1]; exact hwrapGe))
                    (.consFusedCold1 hlt hfn hF hB hpos2 hc2' hlay2 hcls2 hok2 hlen2 hs2Eq hargsLt hds hnd hns
                      rfl rfl hcp.tmpGe ⟨rfl, rfl⟩ hcoldBlk halloc (by simpa [hposEq] using hcpNext) hagree' hrest),
                    fun _ _ h => by cases h; exact hcalleeFn.2⟩
              | unique =>
                have hraw1 := raw_reset_hot_prefix hr hF hB hpos hc1' hlay1 hcls1 hs1Eq hx hu
                  (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                cases hlf : loadFieldsMem mem₁ xVal (List.range lay1.nobj) with
                | none =>
                  rw [hlf] at hraw1; exact .rawStuckWithin (by omega) hraw1
                | some allVals =>
                  rw [hlf] at hraw1; dsimp only at hraw1
                  cases hws : writeShellMem mem₁ xVal (Rt.Rc.dynamicHeader lay1.nobj cls lay1.tag 1) lay1.nobj with
                  | none =>
                    rw [hws] at hraw1; exact .rawStuckWithin (by omega) hraw1
                  | some mem_sh =>
                    rw [hws] at hraw1
                    obtain ⟨wEnv, s₁', hw0, hw1, hwvals, hs₁, hstar1⟩ := hraw1
                    have hwF : raw.funcs[l.resetWrapper idx1]? =
                        some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay1 cls) := by
                      rw [hlay1]; exact hr.resetWrap idx1 c1 cls hc1' (by rwa [← hlay1])
                    have hshape := mkResetWrapper_decLoopShape l.isUniqueProc l.incProc l.decProc lay1 cls
                    have hwvals' : ∀ j < lay1.nobj, ∃ v, wEnv[3 + j]? = some v := fun j hj => by
                      have hlen : allVals.length = lay1.nobj := by have := loadFieldsMem_length hlf; simpa using this
                      exact ⟨allVals[j]'(by omega), by rw [hwvals j hj, List.getElem?_eq_getElem (by omega)]⟩
                    have hloop := raw_decLoop_step hr hwF hshape hw0 hw1 (caller := { fr₁ with pos := fr₁.pos + 1, dsts := [slot] })
                      rfl hwvals' 0 (Nat.zero_le _) (mem := mem_sh) (ctx := ctx₁) (rest := rest₁)
                    have hdeadNil : deadFrom lay1.nobj mask 0 = [] := by
                      rw [deadFrom_zero]; cases hd : deadFields lay1.nobj mask with
                      | nil => rfl
                      | cons _ _ => simp [hd] at hdead
                    rw [hdeadNil] at hloop; dsimp only at hloop
                    have hstar1' : Sem.Star (Lir.semStep raw) s₁' 1
                        { mem := mem_sh, ctx := ctx₁,
                          stack := { fr₁ with pos := fr₁.pos + 1, env := fr₁.env.insert slot xVal, dsts := [] } :: rest₁ } :=
                      hstar1.trans hloop
                    have hargsIns : Lir.evalArgs (fr₁.env.insert slot xVal) args = Lir.evalArgs fr₁.env args :=
                      evalArgs_eq_of_agree_ne (bound := freshBase F) (slot := slot)
                        (fun r _ hne => Lir.env_insert_ne _ _ (Ne.symm hne)) hargsLt hns
                    have hargsEq : Lir.evalArgs fr₁.env args = Lir.evalArgs fr₂.env args :=
                      hagree.evalArgs_eq hargsLt
                    cases hargs : Lir.evalArgs fr₁.env args with
                    | none =>
                      have hargs' : List.mapM (Lir.Arg.eval (fr₁.env.insert slot xVal)) args = none := hargsIns.trans hargs
                      have hstk2 : Lir.step raw
                          { mem := mem_sh, ctx := ctx₁,
                            stack := { fr₁ with pos := fr₁.pos + 1, env := fr₁.env.insert slot xVal, dsts := [] } :: rest₁ } = .stuck := by
                        unfold Lir.step
                        simp [hF, hB, hpos2, hs2Eq, Lir.evalArgs, Lir.Arg.eval, hargs']
                      exact .rawStuckWithin (c₁ := 2) (by omega)
                        (.charge hs₁ (reaches_of_star_reaches hstar1' (.final (k := 0) (by rw [Lir.semStep, hstk2]; exact .stuck))))
                    | some vals =>
                      have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by
                        unfold evalUniqueCheck at hu
                        cases ht : Lir.Cond.holds .tnz .w64 xVal 1
                        · rfl
                        · simp [ht] at hu
                      have hraw2 := raw_reuse_hot_exec hr
                        (fr := { fr₁ with pos := fr₁.pos + 1, env := fr₁.env.insert slot xVal, dsts := [] })
                        hF hB hpos2 hc2' hlay2 hcls2 hlen2 hs2Eq (by simp) (by rw [hargsIns, hargs]) htagF
                        (rest := rest₁) (mem := mem_sh) (ctx := ctx₁)
                      dsimp only at hraw2
                      have hvlen : vals.length = lay2.nobj := by
                        have := evalArgs_length hargs; rw [hlay2]; dsimp [Rt.Rc.CellLayout.ofFields]; omega
                      have hover : writeReuseMem mem_sh xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals =
                          writeReuseMem mem₁ xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals :=
                        writeReuseMem_after_writeShellMem (by omega) hws
                      rw [hover] at hraw2
                      cases hwm : writeReuseMem mem₁ xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals with
                      | none =>
                        rw [hwm] at hraw2
                        exact .rawStuckWithin (by omega)
                          (.charge hs₁ (reaches_of_star_reaches hstar1' hraw2))
                      | some mem' =>
                        rw [hwm] at hraw2
                        obtain ⟨s₁'', hs₁₂, hstar2⟩ := hraw2
                        have hposEq : fr₁.pos + 1 + 1 = fr₁.pos + 2 := by omega
                        have htot₁ : Sem.Star (Lir.semStep raw) s₁' 2
                            { mem := mem', ctx := ctx₁,
                              stack := { fr₁ with pos := fr₁.pos + 2, env := (fr₁.env.insert slot xVal).insert dst xVal, dsts := [] } :: rest₁ } := by
                          simpa [hposEq] using hstar1'.trans (.charge hs₁₂ hstar2)
                        by_cases hliveLe : (liveFields lay1.nobj mask).length ≤ maxInlineResetLive
                        · obtain ⟨hcpNext, _, _, hinlHot, _⟩ :=
                            inl_fusedResetReuse_inline_exec hr (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp hrestPair hp
                              hpos rfl hpos2 hget2 (by rw [← hxEq, hx]) hxLt hargsLt hliveLe
                              (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                          obtain ⟨env2, s₂', hag2, hs₂, hstar₂⟩ := hinlHot hu (by rw [← hargsEq, hargs]) hwm
                          have hagree' : AgreeBelow (freshBase F) ((fr₁.env.insert slot xVal).insert dst xVal) env2 :=
                            fun r hr' => ((hagree.insert_same slot xVal).insert_same dst xVal r hr').trans (hag2 r hr')
                          refine .sync hs₁ htot₁ hs₂ hstar₂ (by simp) ?_
                          exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                            fun _ _ h => by cases h; rfl⟩
                        · obtain ⟨hcpNext, _, _, hinlHot, _⟩ :=
                            inl_fusedResetReuse_fallback_exec hr (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp hrestPair hp
                              hpos rfl hpos2 hget2 (by rw [← hxEq, hx]) hxLt hargsLt hliveLe
                              (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                          obtain ⟨env2, s₂', hag2, hs₂, hstar₂⟩ := hinlHot hu (by rw [← hargsEq, hargs]) hwm
                          have hagree' : AgreeBelow (freshBase F) ((fr₁.env.insert slot xVal).insert dst xVal) env2 :=
                            fun r hr' => ((hagree.insert_same slot xVal).insert_same dst xVal r hr').trans (hag2 r hr')
                          refine .sync hs₁ htot₁ hs₂ hstar₂ (by simp) ?_
                          exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                            fun _ _ h => by cases h; rfl⟩
          | fusedResetUReuseU slot x dst lay2 cls args =>
            obtain ⟨idx1, lay1, mask, idx2, hc1, hc2, hle, hdead, hdx, hsx, hds, hnd, hns⟩ :=
              classifyPair_eq_fusedResetUReuseU hp
            obtain ⟨c1, hc1', hs1Eq0, hlay1, hcls1, _, _⟩ := classify_eq_resetU hc1
            obtain ⟨c2, hc2', hs2Eq0, hlay2, hcls2, hlen2, _, _, _⟩ := classify_eq_reuseU hc2
            have hs1Eq : B.body[fr₁.pos] = .call [slot] (l.resetUWrapper idx1) [.v x, .imm mask] := hs1Eq0
            have hs2Eq : B.body[fr₁.pos + 1] = .call [dst] (l.reuseUWrapper idx2) (.v slot :: args) := hget2.trans hs2Eq0
            have hxLt : (x : Nat) < freshBase F := by
              have h1 := call_args_lt_freshBase hB (by rw [← hs1Eq]; exact hsMem)
              have h2 : x ≤ argsMax [.v x, .imm mask] 0 := mem_le_argsMax (by simp)
              dsimp only [Lir.VReg] at h2 ⊢; omega
            have hargsLt : argsMax args 0 < freshBase F := by
              have h1 := call_args_lt_freshBase hB (by rw [← hs2Eq, hget2]; exact hs2Mem)
              have h2 : argsMax args 0 ≤ argsMax (.v slot :: args) 0 := by
                unfold argsMax; rw [List.foldl_cons]; exact argsMax_mono_local args (Nat.zero_le _)
              omega
            have hxEq : fr₁.env[x]? = fr₂.env[x]? := hagree x hxLt
            cases hx : fr₁.env[x]? with
            | none =>
              exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs1Eq, Lir.evalArgs, Lir.Arg.eval, hx])
            | some xVal =>
              have hraw1 := raw_resetU_prefix hr hF hB hpos hc1' hlay1 hcls1 hs1Eq hx
                (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
              cases hlf : loadFieldsMem mem₁ xVal (List.range lay1.nobj) with
              | none =>
                rw [hlf] at hraw1; exact .rawStuckWithin (by omega) hraw1
              | some allVals =>
                rw [hlf] at hraw1; dsimp only at hraw1
                cases hws : writeShellMem mem₁ xVal (Rt.Rc.dynamicHeader lay1.nobj cls lay1.tag 1) lay1.nobj with
                | none =>
                  rw [hws] at hraw1; exact .rawStuckWithin (by omega) hraw1
                | some mem_sh =>
                  rw [hws] at hraw1
                  obtain ⟨wEnv, s₁', hw0, hw1, hwvals, hs₁, hstar1⟩ := hraw1
                  have hwF : raw.funcs[l.resetUWrapper idx1]? =
                      some (mkResetUWrapper l.decProc lay1 cls) := by
                    rw [hlay1]; exact hr.resetUWrap idx1 c1 cls hc1' (by rwa [← hlay1])
                  have hshape := mkResetUWrapper_decLoopShape l.decProc lay1 cls
                  have hwvals' : ∀ j < lay1.nobj, ∃ v, wEnv[2 + j]? = some v := fun j hj => by
                    have hlen : allVals.length = lay1.nobj := by have := loadFieldsMem_length hlf; simpa using this
                    exact ⟨allVals[j]'(by omega), by rw [hwvals j hj, List.getElem?_eq_getElem (by omega)]⟩
                  have hloop := raw_decLoop_step hr hwF hshape hw0 hw1 (caller := { fr₁ with pos := fr₁.pos + 1, dsts := [slot] })
                    rfl hwvals' 0 (Nat.zero_le _) (mem := mem_sh) (ctx := ctx₁) (rest := rest₁)
                  have hdeadNil : deadFrom lay1.nobj mask 0 = [] := by
                    rw [deadFrom_zero]; cases hd : deadFields lay1.nobj mask with
                    | nil => rfl
                    | cons _ _ => simp [hd] at hdead
                  rw [hdeadNil] at hloop; dsimp only at hloop
                  have hstar1' : Sem.Star (Lir.semStep raw) s₁' 0
                      { mem := mem_sh, ctx := ctx₁,
                        stack := { fr₁ with pos := fr₁.pos + 1, env := fr₁.env.insert slot xVal, dsts := [] } :: rest₁ } :=
                    hstar1.trans hloop
                  have hargsIns : Lir.evalArgs (fr₁.env.insert slot xVal) args = Lir.evalArgs fr₁.env args :=
                    evalArgs_eq_of_agree_ne (bound := freshBase F) (slot := slot)
                      (fun r _ hne => Lir.env_insert_ne _ _ (Ne.symm hne)) hargsLt hns
                  have hargsEq : Lir.evalArgs fr₁.env args = Lir.evalArgs fr₂.env args :=
                    hagree.evalArgs_eq hargsLt
                  cases hargs : Lir.evalArgs fr₁.env args with
                  | none =>
                    have hargs' : List.mapM (Lir.Arg.eval (fr₁.env.insert slot xVal)) args = none := hargsIns.trans hargs
                    have hstk2 : Lir.step raw
                        { mem := mem_sh, ctx := ctx₁,
                          stack := { fr₁ with pos := fr₁.pos + 1, env := fr₁.env.insert slot xVal, dsts := [] } :: rest₁ } = .stuck := by
                      unfold Lir.step
                      simp [hF, hB, hpos2, hs2Eq, Lir.evalArgs, Lir.Arg.eval, hargs']
                    exact .rawStuckWithin (c₁ := 1) (by omega)
                      (.charge hs₁ (reaches_of_star_reaches hstar1' (.final (k := 0) (by rw [Lir.semStep, hstk2]; exact .stuck))))
                  | some vals =>
                    have hraw2 := raw_reuseU_exec hr (slotVal := xVal)
                      (fr := { fr₁ with pos := fr₁.pos + 1, env := fr₁.env.insert slot xVal, dsts := [] })
                      hF hB hpos2 hc2' hlay2 hcls2 hlen2 hs2Eq (by simp) (by rw [hargsIns, hargs])
                      (rest := rest₁) (mem := mem_sh) (ctx := ctx₁)
                    dsimp only at hraw2
                    have hvlen : vals.length = lay2.nobj := by
                      have := evalArgs_length hargs; rw [hlay2]; dsimp [Rt.Rc.CellLayout.ofFields]; omega
                    have hover : writeReuseMem mem_sh xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals =
                        writeReuseMem mem₁ xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals :=
                      writeReuseMem_after_writeShellMem (by omega) hws
                    rw [hover] at hraw2
                    cases hwm : writeReuseMem mem₁ xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals with
                    | none =>
                      rw [hwm] at hraw2
                      exact .rawStuckWithin (by omega)
                        (.charge hs₁ (reaches_of_star_reaches hstar1' hraw2))
                    | some mem' =>
                      rw [hwm] at hraw2
                      obtain ⟨s₁'', hs₁₂, hstar2⟩ := hraw2
                      obtain ⟨hcpNext, s₂', hs₂, hstar₂⟩ :=
                        inl_fusedResetUReuseU_exec (raw := raw) (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp hrestPair hp
                          hpos rfl hpos2 hget2 (by rw [← hxEq, hx]) (by rw [← hargsEq, hargs]) hwm
                          (rest := rest₂) (ctx := ctx₁)
                      have hposEq : fr₁.pos + 1 + 1 = fr₁.pos + 2 := by omega
                      have htot₁ : Sem.Star (Lir.semStep raw) s₁' 1
                          { mem := mem', ctx := ctx₁,
                            stack := { fr₁ with pos := fr₁.pos + 2, env := (fr₁.env.insert slot xVal).insert dst xVal, dsts := [] } :: rest₁ } := by
                        simpa [hposEq] using hstar1'.trans (.charge hs₁₂ hstar2)
                      refine .sync hs₁ htot₁ hs₂ hstar₂ (by simp) ?_
                      exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext ((hagree.insert_same slot xVal).insert_same dst xVal) rfl) hrest,
                        fun _ _ h => by cases h; rfl⟩
          | fusedResetUReuseU1 slot x dst lay1 mask deadIdx lay2 cls args =>
            obtain ⟨idx1, idx2, hc1, hc2, hle, hdead, hdx, hsx, hds, hnd, hns⟩ :=
              classifyPair_eq_fusedResetUReuseU1 hp
            obtain ⟨c1, hc1', hs1Eq0, hlay1, hcls1, _, _⟩ := classify_eq_resetU hc1
            obtain ⟨c2, hc2', hs2Eq0, hlay2, hcls2, hlen2, _, _, _⟩ := classify_eq_reuseU hc2
            have hs1Eq : B.body[fr₁.pos] = .call [slot] (l.resetUWrapper idx1) [.v x, .imm mask] := hs1Eq0
            have hs2Eq : B.body[fr₁.pos + 1] = .call [dst] (l.reuseUWrapper idx2) (.v slot :: args) := hget2.trans hs2Eq0
            have hxLt : (x : Nat) < freshBase F := by
              have h1 := call_args_lt_freshBase hB (by rw [← hs1Eq]; exact hsMem)
              have h2 : x ≤ argsMax [.v x, .imm mask] 0 := mem_le_argsMax (by simp)
              dsimp only [Lir.VReg] at h2 ⊢; omega
            have hargsLt : argsMax args 0 < freshBase F := by
              have h1 := call_args_lt_freshBase hB (by rw [← hs2Eq, hget2]; exact hs2Mem)
              have h2 : argsMax args 0 ≤ argsMax (.v slot :: args) 0 := by
                unfold argsMax; rw [List.foldl_cons]; exact argsMax_mono_local args (Nat.zero_le _)
              omega
            have hxEq : fr₁.env[x]? = fr₂.env[x]? := hagree x hxLt
            cases hx : fr₁.env[x]? with
            | none =>
              exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs1Eq, Lir.evalArgs, Lir.Arg.eval, hx])
            | some xVal =>
              have hraw1 := raw_resetU_prefix hr hF hB hpos hc1' hlay1 hcls1 hs1Eq hx
                (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
              cases hlf : loadFieldsMem mem₁ xVal (List.range lay1.nobj) with
              | none =>
                rw [hlf] at hraw1; exact .rawStuckWithin (by omega) hraw1
              | some allVals =>
                rw [hlf] at hraw1; dsimp only at hraw1
                cases hws : writeShellMem mem₁ xVal (Rt.Rc.dynamicHeader lay1.nobj cls lay1.tag 1) lay1.nobj with
                | none =>
                  rw [hws] at hraw1; exact .rawStuckWithin (by omega) hraw1
                | some mem_sh =>
                  rw [hws] at hraw1
                  obtain ⟨wEnv, s₁', hw0, hw1, hwvals, hs₁, hstar1⟩ := hraw1
                  obtain ⟨hdeadLt, hdead0, hdeadNext⟩ := deadFields_singleton_split hdead
                  have hallLen : allVals.length = lay1.nobj := by have := loadFieldsMem_length hlf; simpa using this
                  let deadVal := allVals[deadIdx]'(by omega)
                  have hloadDead : Lir.loadWord mem₁ .w64 .zero (xVal + Lir.dispWord (Int.ofNat (8 * (deadIdx + 1)))) = some deadVal := by
                    have h1 := loadFieldsMem_get hlf deadIdx (by simp [hdeadLt])
                    simpa [deadVal] using h1
                  have hwF : raw.funcs[l.resetUWrapper idx1]? = some (mkResetUWrapper l.decProc lay1 cls) := by
                    rw [hlay1]; exact hr.resetUWrap idx1 c1 cls hc1' (by rwa [← hlay1])
                  have hshape := mkResetUWrapper_decLoopShape l.decProc lay1 cls
                  have hwvals' : ∀ j < lay1.nobj, ∃ v, wEnv[2 + j]? = some v := fun j hj =>
                    ⟨allVals[j]'(by omega), by rw [hwvals j hj, List.getElem?_eq_getElem (by omega)]⟩
                  have hloop0 := raw_decLoop_step hr hwF hshape hw0 hw1
                    (caller := { fr₁ with pos := fr₁.pos + 1, dsts := [slot] }) rfl hwvals' 0 (Nat.zero_le _)
                    (mem := mem_sh) (ctx := ctx₁) (rest := rest₁)
                  rw [hdead0] at hloop0; dsimp only at hloop0
                  obtain ⟨_, deadVal', hdeadEnv, _, hloopStar0⟩ := hloop0
                  have hdeadEq : deadVal' = deadVal := by
                    have h1 := hwvals deadIdx hdeadLt
                    rw [hdeadEnv, List.getElem?_eq_getElem (by omega), Option.some.injEq] at h1
                    exact h1
                  subst hdeadEq
                  obtain ⟨hcpNext, hb1, ⟨joinBlk, postJ, hjb, hjbP, hjbBody⟩, hinlHot, hinlCold⟩ :=
                    inl_fusedResetUReuseU1_exec hr (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp hrestPair hp
                      hpos rfl hpos2 hget2 (by rw [← hxEq, hx]) hxLt hargsLt hloadDead
                      (rest := rest₂) (ctx := ctx₁)
                  by_cases htag : Lir.Cond.holds .tnz .w64 deadVal 1 = true
                  · have hdecImm := raw_decProc_imm hr
                      (caller := { fn := l.resetUWrapper idx1, label := 1 + 2 * deadIdx + 1, pos := 1, env := wEnv, dsts := [] })
                      (rest := { fr₁ with pos := fr₁.pos + 1, dsts := [slot] } :: rest₁)
                      (ctx := ctx₁) (mem := mem_sh) rfl htag
                    have sAfter := raw_decLoop_after_call (wEnv := wEnv) (ctx := ctx₁) (mem := mem_sh)
                      (caller := { fr₁ with pos := fr₁.pos + 1, dsts := [slot] }) (rest := rest₁) hwF hshape hdeadLt
                    have hloop1 := raw_decLoop_step hr hwF hshape hw0 hw1
                      (caller := { fr₁ with pos := fr₁.pos + 1, dsts := [slot] }) rfl hwvals' (deadIdx + 1) (by omega)
                      (mem := mem_sh) (ctx := ctx₁) (rest := rest₁)
                    rw [hdeadNext] at hloop1; dsimp only at hloop1
                    have hstar1' : Sem.Star (Lir.semStep raw) s₁' 1
                        { mem := mem_sh, ctx := ctx₁,
                          stack := { fr₁ with pos := fr₁.pos + 1, env := fr₁.env.insert slot xVal, dsts := [] } :: rest₁ } :=
                      hstar1.trans (hloopStar0.trans (hdecImm.trans (.free sAfter hloop1)))
                    have hargsIns : Lir.evalArgs (fr₁.env.insert slot xVal) args = Lir.evalArgs fr₁.env args :=
                      evalArgs_eq_of_agree_ne (bound := freshBase F) (slot := slot)
                        (fun r _ hne => Lir.env_insert_ne _ _ (Ne.symm hne)) hargsLt hns
                    have hargsEq : Lir.evalArgs fr₁.env args = Lir.evalArgs fr₂.env args := hagree.evalArgs_eq hargsLt
                    cases hargs : Lir.evalArgs fr₁.env args with
                    | none =>
                      have hargs' : List.mapM (Lir.Arg.eval (fr₁.env.insert slot xVal)) args = none := hargsIns.trans hargs
                      have hstk2 : Lir.step raw
                          { mem := mem_sh, ctx := ctx₁,
                            stack := { fr₁ with pos := fr₁.pos + 1, env := fr₁.env.insert slot xVal, dsts := [] } :: rest₁ } = .stuck := by
                        unfold Lir.step; simp [hF, hB, hpos2, hs2Eq, Lir.evalArgs, Lir.Arg.eval, hargs']
                      exact .rawStuckWithin (by omega)
                        (.charge hs₁ (reaches_of_star_reaches hstar1' (.final (k := 0) (by rw [Lir.semStep, hstk2]; exact .stuck))))
                    | some vals =>
                      have hraw2 := raw_reuseU_exec hr (slotVal := xVal)
                        (fr := { fr₁ with pos := fr₁.pos + 1, env := fr₁.env.insert slot xVal, dsts := [] })
                        hF hB hpos2 hc2' hlay2 hcls2 hlen2 hs2Eq (by simp) (by rw [hargsIns, hargs])
                        (rest := rest₁) (mem := mem_sh) (ctx := ctx₁)
                      dsimp only at hraw2
                      have hvlen : vals.length = lay2.nobj := by
                        have := evalArgs_length hargs; rw [hlay2]; dsimp [Rt.Rc.CellLayout.ofFields]; omega
                      have hover : writeReuseMem mem_sh xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals =
                          writeReuseMem mem₁ xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals :=
                        writeReuseMem_after_writeShellMem (by omega) hws
                      rw [hover] at hraw2
                      cases hwm : writeReuseMem mem₁ xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals with
                      | none =>
                        rw [hwm] at hraw2
                        exact .rawStuckWithin (by omega) (.charge hs₁ (reaches_of_star_reaches hstar1' hraw2))
                      | some mem' =>
                        rw [hwm] at hraw2
                        obtain ⟨s₁'', hs₁₂, hstar2⟩ := hraw2
                        obtain ⟨env2, s₂', hag2, hs₂, hstar₂⟩ := hinlHot htag (by rw [← hargsEq, hargs]) hwm
                        have hagree' : AgreeBelow (freshBase F) ((fr₁.env.insert slot xVal).insert dst xVal) env2 :=
                          fun r hr' => ((hagree.insert_same slot xVal).insert_same dst xVal r hr').trans (hag2 r hr')
                        have hposEq : fr₁.pos + 1 + 1 = fr₁.pos + 2 := by omega
                        have htot₁ : Sem.Star (Lir.semStep raw) s₁' 2
                            { mem := mem', ctx := ctx₁,
                              stack := { fr₁ with pos := fr₁.pos + 2, env := (fr₁.env.insert slot xVal).insert dst xVal, dsts := [] } :: rest₁ } := by
                          simpa [hposEq] using hstar1'.trans (.charge hs₁₂ hstar2)
                        refine .sync hs₁ htot₁ hs₂ hstar₂ (by simp) ?_
                        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                          fun _ _ h => by cases h; rfl⟩
                  · have htagF : Lir.Cond.holds .tnz .w64 deadVal 1 = false := by simpa using htag
                    obtain ⟨env1, s₂', hag1, hs₂, hstar₂⟩ := hinlCold htagF hws
                    have hagree' : AgreeBelow (freshBase F) fr₁.env env1 := fun r hr' => (hagree r hr').trans (hag1 r hr')
                    have hdecGe : l.sourceCount ≤ l.decProc := by simp [Layout.decProc, Layout.incProc]; omega
                    have hposEq : fr₁.pos + 1 + 1 = fr₁.pos + 2 := by omega
                    refine .sync hs₁ (hstar1.trans hloopStar0) hs₂ hstar₂ (by simp) ?_
                    exact ⟨rfl, rfl, .cons (.runtime hdecGe)
                      (.consFusedResetU1Dec hc1' hlay1 hcls1 hc2' hlay2 hcls2 hlen2 hdead
                        ⟨rfl, rfl, rfl, rfl⟩ hw0 hw1 hwvals' hlt hfn hF hB hpos2 hs2Eq
                        hsx hns hxLt hargsLt hx rfl rfl ⟨rfl, rfl⟩ hb1 hjb hjbP hjbBody
                        (by simpa [hposEq] using hcpNext) hagree' hrest),
                      fun _ _ h => by cases h; rfl⟩
        · have hnp : ∀ s2 rest2, restStmts = s2 :: rest2 → classifyPair l s s2 = none := by
            intro s2 rest2 h2
            cases hcp' : classifyPair l s s2 with
            | none => rfl
            | some fp => exact absurd ⟨s2, rest2, fp, h2, hcp'⟩ hpair
          cases hcls : classify l s with
          | none =>
            obtain ⟨⟨blk, hblk, hinPosLt, hblkStmt⟩, hcpNext⟩ :=
              ChunkPos.step_normal hcp hrest0 hcls hpos rfl
            have hblkGet : blk.body[fr₂.pos] = s := by
              rw [Array.getElem?_eq_getElem hinPosLt, Option.some.injEq] at hblkStmt; exact hblkStmt
            cases hsEq : B.body[fr₁.pos] with
            | call rs g as =>
              have hargsLt : argsMax as 0 < freshBase F := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
              have hargsEq := hagree.evalArgs_eq hargsLt
              cases hargs : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hargs])
              | some vs =>
                obtain ⟨heFwd, _, _⟩ := enter_rel l raw (g := g) (vs := vs)
                cases hent : Lir.enter raw g vs with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hargs, hent])
                | some callee₁ =>
                  obtain ⟨callee₂, hent₂, hfrCallee, hdstCallee⟩ := heFwd callee₁ hent
                  have hs₁ := Lir.semStep_next.mpr (Lir.step_call (p := raw) (mem := mem₁) (ctx := ctx₁) (rest := rest₁) hF hB hpos hsEq hargs hent)
                  have hs₂ := Lir.semStep_next.mpr (Lir.step_call (p := inlineProgram l raw) (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hF' hblk hinPosLt
                    (hblkGet.trans hsEq) (by rw [← hargsEq, hargs]) hent₂)
                  refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                  exact ⟨rfl, rfl, .cons hfrCallee (.cons (.source hlt hfn hF hcpNext hagree rfl) hrest),
                    fun _ _ h => by cases h; exact hdstCallee⟩
            | assign x r =>
              obtain ⟨hfwd, _, _⟩ := hagree.stmt_exec (s := .assign x r) (by simpa [s, hsEq] using hsMax) mem₁ ctx₁
              cases hx : (Lir.Stmt.assign x r).exec fr₁.env mem₁ ctx₁ with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hx])
              | some p =>
                rcases p with ⟨ρ₁', mem'⟩
                obtain ⟨ρ₂', hx₂, hagree'⟩ := hfwd ρ₁' mem' hx
                have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hsEq rfl hx)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hblk hinPosLt
                  (hblkGet.trans hsEq) rfl hx₂)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' hdsts) hrest,
                  fun _ _ h => by cases h; exact htop⟩
            | limb r1 r2 op =>
              obtain ⟨hfwd, _, _⟩ := hagree.stmt_exec (s := .limb r1 r2 op) (by simpa [s, hsEq] using hsMax) mem₁ ctx₁
              cases hx : (Lir.Stmt.limb r1 r2 op).exec fr₁.env mem₁ ctx₁ with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hx])
              | some p =>
                rcases p with ⟨ρ₁', mem'⟩
                obtain ⟨ρ₂', hx₂, hagree'⟩ := hfwd ρ₁' mem' hx
                have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hsEq rfl hx)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hblk hinPosLt
                  (hblkGet.trans hsEq) rfl hx₂)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' hdsts) hrest,
                  fun _ _ h => by cases h; exact htop⟩
            | store w m a =>
              obtain ⟨hfwd, _, _⟩ := hagree.stmt_exec (s := .store w m a) (by simpa [s, hsEq] using hsMax) mem₁ ctx₁
              cases hx : (Lir.Stmt.store w m a).exec fr₁.env mem₁ ctx₁ with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hx])
              | some p =>
                rcases p with ⟨ρ₁', mem'⟩
                obtain ⟨ρ₂', hx₂, hagree'⟩ := hfwd ρ₁' mem' hx
                have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hsEq rfl hx)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hblk hinPosLt
                  (hblkGet.trans hsEq) rfl hx₂)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' hdsts) hrest,
                  fun _ _ h => by cases h; exact htop⟩
          | some site =>
            cases site with
            | inc dst x =>
              obtain ⟨wLit, hsEq0⟩ := classify_eq_inc hcls
              have hsEq : B.body[fr₁.pos] = .call [dst] l.incWrapper [.v x, .imm wLit] := hsEq0
              have hxLt : x < freshBase F := by
                have h1 := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
                have h2 : x ≤ argsMax [.v x, .imm wLit] 0 := mem_le_argsMax (by simp)
                dsimp only [Lir.VReg] at h2 ⊢; omega
              have hxEq : fr₁.env[x]? = fr₂.env[x]? := hagree x hxLt
              cases hx : fr₁.env[x]? with
              | none =>
                exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hx])
              | some xVal =>
                have hraw := raw_inc_exec hr hF hB hpos hsEq hx (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                obtain ⟨hcpNext, hinl⟩ := inl_inc_exec (raw := raw) (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                  (by rwa [← hsEq]) hpos hsEq (by rw [← hxEq, hx]) hxLt (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                cases hout : evalIncSite xVal mem₁ with
                | stuck =>
                  rw [hout] at hraw
                  exact .rawStuckWithin (by omega) hraw
                | oom =>
                  rw [hout] at hraw hinl
                  exact .sameOom (by omega) hraw hinl
                | ok mem' =>
                  rw [hout] at hraw hinl
                  obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                  obtain ⟨env', s₂', hs₂, hstar₂, hag'⟩ := hinl
                  have hagree' : AgreeBelow (freshBase F) (fr₁.env.insert dst 1) env' := fun r hr' => by
                    rw [← hag' r hr', Lir.env_insert_get, Lir.env_insert_get]
                    split
                    · rfl
                    · exact hagree r hr'
                  refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                  exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                    fun _ _ h => by cases h; rfl⟩
            | dec dst x =>
              have hsEq : B.body[fr₁.pos] = .call [dst] l.decWrapper [.v x] := classify_eq_dec hcls
              have hxLt : x < freshBase F := by
                have h1 := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
                have h2 : x ≤ argsMax [.v x] 0 := mem_le_argsMax (by simp)
                dsimp only [Lir.VReg] at h2 ⊢; omega
              have hxEq : fr₁.env[x]? = fr₂.env[x]? := hagree x hxLt
              cases hx : fr₁.env[x]? with
              | none =>
                exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hx])
              | some xVal =>
                have hraw := raw_dec_exec hr hF hB hpos hsEq hx (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                obtain ⟨hcpNext, hfreeBlk, hjoinBlk, hinl⟩ := inl_dec_exec hr (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                  (by rwa [← hsEq]) hpos hsEq (by rw [← hxEq, hx]) hxLt (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                cases hout : evalDecSite xVal mem₁ with
                | stuck =>
                  rw [hout] at hraw
                  exact .rawStuckWithin (by omega) hraw
                | ok mem' =>
                  rw [hout] at hraw hinl
                  obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                  obtain ⟨env', s₂', hs₂, hstar₂, hag'⟩ := hinl
                  have hagree' : AgreeBelow (freshBase F) (fr₁.env.insert dst 1) env' := fun r hr' => by
                    rw [← hag' r hr', Lir.env_insert_get, Lir.env_insert_get]
                    split
                    · rfl
                    · exact hagree r hr'
                  refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                  exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                    fun _ _ h => by cases h; rfl⟩
                | free =>
                  rw [hout] at hraw hinl
                  obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                  obtain ⟨env', s₂', hs₂, hstar₂, hag'⟩ := hinl
                  have hagree' : AgreeBelow (freshBase F) fr₁.env env' := fun r hr' =>
                    (hagree r hr').trans (hag' r hr')
                  have hdecGe : l.sourceCount ≤ l.decProc := by
                    simp [Layout.decProc, Layout.incProc]; omega
                  refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                  exact ⟨rfl, rfl, .cons (.runtime hdecGe)
                    (.consDecSlow ⟨rfl, rfl, rfl, rfl⟩ hlt hfn hF rfl rfl ⟨rfl, rfl⟩ hfreeBlk hjoinBlk hcpNext hagree' hrest),
                    fun _ _ h => by cases h; rfl⟩
            | alloc dst idx lay cls args =>
              obtain ⟨c, hc, hsEq0, hlay, hclsOk, hlen, hok, _⟩ := classify_eq_alloc hcls
              have hsEq : B.body[fr₁.pos] = .call [dst] (l.allocWrapper idx) args := hsEq0
              have hargsLt : argsMax args 0 < freshBase F := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
              have hargsEq : Lir.evalArgs fr₁.env args = Lir.evalArgs fr₂.env args := hagree.evalArgs_eq hargsLt
              cases hargs : Lir.evalArgs fr₁.env args with
              | none =>
                exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hargs])
              | some vals =>
                have hraw := raw_alloc_exec hr hF hB hpos hc hlay hclsOk hok hlen hsEq hargs
                  (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                obtain ⟨hcpNext, hinl⟩ := inl_alloc_exec (raw := raw) (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                  (by rwa [← hsEq]) (by rwa [← hsEq]) hpos hsEq (by rw [← hargsEq, hargs]) hargsLt
                  (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                cases hres : evalAllocReserve lay cls mem₁ ctx₁ with
                | stuck =>
                  rw [hres] at hraw
                  exact .rawStuckWithin (by omega) hraw
                | oom =>
                  rw [hres] at hraw hinl
                  exact .sameOom (by omega) hraw hinl
                | ok addr mem₂ =>
                  rw [hres] at hraw hinl
                  dsimp only at hraw hinl
                  cases hwf : writeFieldsMem mem₂ addr 0 vals with
                  | none =>
                    rw [hwf] at hraw
                    exact .rawStuckWithin (by omega) hraw
                  | some mem' =>
                    rw [hwf] at hraw hinl
                    obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                    obtain ⟨env', s₂', hs₂, hstar₂, hag'⟩ := hinl
                    have hagree' : AgreeBelow (freshBase F) (fr₁.env.insert dst addr) env' := fun r hr' => by
                      rw [← hag' r hr', Lir.env_insert_get, Lir.env_insert_get]
                      split
                      · rfl
                      · exact hagree r hr'
                    refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                    exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                      fun _ _ h => by cases h; rfl⟩
            | reset dst x idx lay cls mask =>
              obtain ⟨c, hc, hsEq0, hlay, hclsOk, _, _⟩ := classify_eq_reset hcls
              have hsEq : B.body[fr₁.pos] = .call [dst] (l.resetWrapper idx) [.v x, .imm mask] := hsEq0
              have hxLt : (x : Nat) < freshBase F := by
                have h1 := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
                have h2 : x ≤ argsMax [.v x, .imm mask] 0 := mem_le_argsMax (by simp)
                dsimp only [Lir.VReg] at h2 ⊢; omega
              have hxEq : fr₁.env[x]? = fr₂.env[x]? := hagree x hxLt
              cases hx : fr₁.env[x]? with
              | none =>
                exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hx])
              | some xVal =>
                cases hu : evalUniqueCheck xVal mem₁ with
                | stuck =>
                  exact .rawStuckWithin (by omega)
                    (raw_reset_stuck hr hF hB hpos hc hlay hclsOk hsEq hx hu)
                | shared =>
                  by_cases hliveLe : (liveFields lay.nobj mask).length ≤ maxInlineResetLive
                  · have hrawS := raw_reset_shared_exec hr hF hB hpos hc hlay hclsOk hsEq hx hu
                      (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                    dsimp only at hrawS
                    obtain ⟨hcpNext, hjoinBlk, hdec2, hinlS⟩ :=
                      inl_reset_shared_exec hr (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                        (by rwa [← hsEq]) (by rwa [← hsEq]) (by rwa [← hsEq]) hpos hsEq
                        (by rw [← hxEq, hx]) hxLt hu hliveLe (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                    have hmaxL : (liveFields lay.nobj mask).length ≤ 6 := hliveLe
                    cases hincEv : evalSharedIncList xVal (liveFields lay.nobj mask) mem₁ with
                    | oom =>
                      rw [hincEv] at hrawS hinlS
                      exact .sameOom (by omega) hrawS hinlS
                    | stuck =>
                      rw [hincEv] at hrawS
                      exact .rawStuckWithin (by omega) hrawS
                    | ok mem_inc =>
                      rw [hincEv] at hrawS hinlS
                      dsimp only at hrawS hinlS
                      cases hdecEv : evalDecSite xVal mem_inc with
                      | stuck =>
                        rw [hdecEv] at hrawS
                        exact .rawStuckWithin (by omega) hrawS
                      | ok mem' =>
                        rw [hdecEv] at hrawS hinlS
                        obtain ⟨s₁', hs₁, hstar₁⟩ := hrawS
                        obtain ⟨envD, s₂', hs₂, hstar₂, hagD⟩ := hinlS
                        have hagree' : AgreeBelow (freshBase F) (fr₁.env.insert dst 1) envD :=
                          fun r hr' => ((hagree.insert_same dst 1) r hr').trans (hagD r hr')
                        refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp; omega) ?_
                        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                          fun _ _ h => by cases h; rfl⟩
                      | free =>
                        rw [hdecEv] at hrawS hinlS
                        obtain ⟨wEnv', s₁', hs₁, hstar₁⟩ := hrawS
                        obtain ⟨env1, s₂', hs₂, hstar₂, hag1⟩ := hinlS
                        have hagree' : AgreeBelow (freshBase F) fr₁.env env1 := fun r hr' => (hagree r hr').trans (hag1 r hr')
                        have hdecGe : l.sourceCount ≤ l.decProc := by simp [Layout.decProc, Layout.incProc]; omega
                        refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp; omega) ?_
                        exact ⟨rfl, rfl, .cons (.runtime hdecGe)
                          (.consResetSharedDec hc hlay hclsOk ⟨rfl, rfl, rfl, rfl⟩ hlt hfn hF rfl rfl ⟨rfl, rfl⟩
                            (.reset _ (by dsimp only [Lir.Label]; omega) hdec2 hjoinBlk hcpNext) hagree' hrest),
                          fun _ _ h => by cases h; rfl⟩
                  · obtain ⟨hcpNext, hjoinBlk, hcoldBlk, callee, env', s₂', hentRaw, hag', hs₂, hstar₂⟩ :=
                      inl_reset_cold_exec hr (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                        (by rwa [← hsEq]) (by rwa [← hsEq]) (by rwa [← hsEq]) hpos hsEq
                        (by rw [← hxEq, hx]) hxLt hu hliveLe (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                    have hs₁ : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } =
                        .next { mem := mem₁, ctx := ctx₁, stack := callee :: { fr₁ with pos := fr₁.pos + 1, dsts := [dst] } :: rest₁ } true := by
                      apply Lir.semStep_next.mpr
                      exact Lir.step_call hF hB hpos hsEq (by simp [Lir.evalArgs, Lir.Arg.eval, hx]) hentRaw
                    have hwrapGe : l.sourceCount ≤ l.resetWrapper idx := by
                      simp [Layout.resetWrapper, Layout.init, Layout.incProc]; omega
                    have hcalleeFn : callee.fn = l.resetWrapper idx ∧ callee.dsts = [] := by
                      simp only [Lir.enter] at hentRaw
                      cases hrf : raw.funcs[l.resetWrapper idx]? with
                      | none => simp [hrf] at hentRaw
                      | some wf =>
                        simp only [hrf, Option.bind_eq_bind, Option.bind_some] at hentRaw
                        cases hbp : Lir.bindParams {} wf.params [xVal, mask] with
                        | none => simp [hbp] at hentRaw
                        | some ρ => simp only [hbp, Option.bind_some, Option.some.injEq] at hentRaw; subst hentRaw; exact ⟨rfl, rfl⟩
                    have hagree' : AgreeBelow (freshBase F) fr₁.env env' := fun r hr' => (hagree r hr').trans (hag' r hr')
                    refine .sync hs₁ (.refl _) hs₂ hstar₂ (by simp) ?_
                    exact ⟨rfl, rfl, .cons (.runtime (by rw [hcalleeFn.1]; exact hwrapGe))
                      (.consColdRedirect hlt hfn hF rfl rfl (by have := hcp.tmpGe; dsimp only [Lir.VReg]; omega)
                        ⟨rfl, rfl⟩ (by dsimp only [Lir.Label]; omega) hcoldBlk rfl rfl hjoinBlk hcpNext hagree' hrest),
                      fun _ _ h => by cases h; exact hcalleeFn.2⟩
                | unique =>
                  have hraw := raw_reset_hot_prefix hr hF hB hpos hc hlay hclsOk hsEq hx hu
                    (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                  cases hlf : loadFieldsMem mem₁ xVal (List.range lay.nobj) with
                  | none =>
                    rw [hlf] at hraw; exact .rawStuckWithin (by omega) hraw
                  | some allVals =>
                    rw [hlf] at hraw; dsimp only at hraw
                    cases hws : writeShellMem mem₁ xVal (Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1) lay.nobj with
                    | none =>
                      rw [hws] at hraw; exact .rawStuckWithin (by omega) hraw
                    | some mem_sh =>
                      rw [hws] at hraw
                      obtain ⟨wEnv, s₁', hw0, hw1, hwvals, hs₁, hstar₁⟩ := hraw
                      obtain ⟨hcpNext, hb2, hjoinBlk, env', s₂', hs₂, hstar₂, hag', hx', hdeadVals⟩ :=
                        inl_reset_hot_prefix (raw := raw) (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                          (by rwa [← hsEq]) (by rwa [← hsEq]) (by rwa [← hsEq]) hpos hsEq
                          (by rw [← hxEq, hx]) hxLt hu hlf hws (rest := rest₂) (ctx := ctx₁)
                      have hwF : raw.funcs[l.resetWrapper idx]? =
                          some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls) := by
                        rw [hlay]; exact hr.resetWrap idx c cls hc (by rwa [← hlay])
                      have hshape := mkResetWrapper_decLoopShape l.isUniqueProc l.incProc l.decProc lay cls
                      have hwvals' : ∀ j < lay.nobj, ∃ v, wEnv[3 + j]? = some v := fun j hj => by
                        have hlen : allVals.length = lay.nobj := by have := loadFieldsMem_length hlf; simpa using this
                        exact ⟨allVals[j]'(by omega), by rw [hwvals j hj, List.getElem?_eq_getElem (by omega)]⟩
                      have hagree' : AgreeBelow (freshBase F) fr₁.env env' := fun r hr' => (hagree r hr').trans (hag' r hr')
                      let dead := deadFields lay.nobj mask
                      let live := liveFields lay.nobj mask
                      let joinLbl := if live.length ≤ maxInlineResetLive then fr₂.label + 8 + 5 * live.length else fr₂.label + 4
                      let deadBase := if live.length ≤ maxInlineResetLive then tmp + 1 else tmp + 2
                      let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
                      let hotBody : List Lir.Stmt :=
                        mkDeadLoads x deadBase dead ++ mkShellStores x hdr lay.nobj ++ mkDeadDecs l.decProc deadBase dead
                      let inBlk : Lir.Block := { body := hotBody.toArray, term := .jump ⟨joinLbl, [.v x]⟩, cold := B.cold }
                      have hdecs : ∀ q < dead.length,
                          inBlk.body[(dead.length + (1 + lay.nobj)) + q]? = some (.call [] l.decProc [.v (deadBase + q)]) := by
                        intro q hq
                        simp only [inBlk, hotBody, List.getElem?_toArray]
                        have hpre : (mkDeadLoads x deadBase dead ++ mkShellStores x hdr lay.nobj).length = dead.length + (1 + lay.nobj) := by
                          simp [mkDeadLoads_length, mkShellStores_length]
                        rw [List.getElem?_append_right (by omega), hpre, Nat.add_sub_cancel_left]
                        exact mkDeadDecs_getElem? l.decProc deadBase dead q hq
                      have hfin : ResetFinish l F fr₁.label B (fr₁.pos + 1) dst x inBlk (fr₂.label + 2)
                          ((dead.length + (1 + lay.nobj)) + dead.length) :=
                        .jump joinLbl (by dsimp only [joinLbl, Lir.Label]; split <;> omega)
                          (by simp [inBlk, hotBody, mkDeadLoads_length, mkShellStores_length, mkDeadDecs_length]; omega)
                          rfl hjoinBlk hcpNext
                      refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                      refine ⟨rfl, rfl, .consResetDec (W := mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls)
                        (B := B) (inBlk := inBlk) (n := lay.nobj) (base := 2) (oldBase := 3) (k := 0) (i := 0)
                        (decBasePos := dead.length + (1 + lay.nobj)) (deadBase := deadBase)
                        hwF hshape ⟨rfl, rfl, rfl⟩ (Nat.zero_le _) hw0 hw1 hwvals' hlt hfn hF rfl rfl
                        ⟨rfl, by simp [dead]⟩ hb2 (by simp [deadFrom_zero]) (Nat.zero_le _) hdecs ?_ hx' hfin hagree' hrest,
                        fun _ _ h => by cases h; rfl⟩
                      intro q hq
                      have hltN := deadFields_lt lay.nobj mask (List.getElem_mem hq)
                      have hlen : allVals.length = lay.nobj := by have := loadFieldsMem_length hlf; simpa using this
                      rw [hdeadVals q hq, hwvals _ hltN, List.getElem?_eq_getElem (by omega)]
            | resetU dst x idx lay cls mask =>
              obtain ⟨c, hc, hsEq0, hlay, hclsOk, _, _⟩ := classify_eq_resetU hcls
              have hsEq : B.body[fr₁.pos] = .call [dst] (l.resetUWrapper idx) [.v x, .imm mask] := hsEq0
              have hxLt : (x : Nat) < freshBase F := by
                have h1 := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
                have h2 : x ≤ argsMax [.v x, .imm mask] 0 := mem_le_argsMax (by simp)
                dsimp only [Lir.VReg] at h2 ⊢; omega
              have hxEq : fr₁.env[x]? = fr₂.env[x]? := hagree x hxLt
              cases hx : fr₁.env[x]? with
              | none =>
                exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hx])
              | some xVal =>
                have hraw := raw_resetU_prefix hr hF hB hpos hc hlay hclsOk hsEq hx
                  (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                cases hlf : loadFieldsMem mem₁ xVal (List.range lay.nobj) with
                | none =>
                  rw [hlf] at hraw; exact .rawStuckWithin (by omega) hraw
                | some allVals =>
                  rw [hlf] at hraw; dsimp only at hraw
                  cases hws : writeShellMem mem₁ xVal (Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1) lay.nobj with
                  | none =>
                    rw [hws] at hraw; exact .rawStuckWithin (by omega) hraw
                  | some mem_sh =>
                    rw [hws] at hraw
                    obtain ⟨wEnv, s₁', hw0, hw1, hwvals, hs₁, hstar₁⟩ := hraw
                    obtain ⟨hcpNext, inBlk, post, env', s₂', hinBlk, hfull, hs₂, hstar₂, hag', hx', hdeadVals⟩ :=
                      inl_resetU_prefix (raw := raw) (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                        (by rwa [← hsEq]) (by rwa [← hsEq]) (by rwa [← hsEq]) hpos hsEq
                        (by rw [← hxEq, hx]) hxLt hlf hws (rest := rest₂) (ctx := ctx₁)
                    have hwF : raw.funcs[l.resetUWrapper idx]? =
                        some (mkResetUWrapper l.decProc lay cls) := by
                      rw [hlay]; exact hr.resetUWrap idx c cls hc (by rwa [← hlay])
                    have hshape := mkResetUWrapper_decLoopShape l.decProc lay cls
                    have hwvals' : ∀ j < lay.nobj, ∃ v, wEnv[2 + j]? = some v := fun j hj => by
                      have hlen : allVals.length = lay.nobj := by have := loadFieldsMem_length hlf; simpa using this
                      exact ⟨allVals[j]'(by omega), by rw [hwvals j hj, List.getElem?_eq_getElem (by omega)]⟩
                    have hagree' : AgreeBelow (freshBase F) fr₁.env env' := fun r hr' => (hagree r hr').trans (hag' r hr')
                    let dead := deadFields lay.nobj mask
                    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
                    let decBasePos := fr₂.pos + (dead.length + (1 + lay.nobj))
                    have hpreLen : (acc.reverse ++ mkDeadLoads x tmp dead ++ mkShellStores x hdr lay.nobj).length = decBasePos := by
                      simp [decBasePos, hcp.inPosEq, mkDeadLoads_length, mkShellStores_length]
                    have hdecs : ∀ q < dead.length,
                        inBlk.body[decBasePos + q]? = some (.call [] l.decProc [.v (tmp + q)]) := by
                      intro q hq
                      rw [← Array.getElem?_toList, hfull]
                      have hsplit : acc.reverse ++ mkDeadLoads x tmp dead ++ mkShellStores x hdr lay.nobj ++
                          mkDeadDecs l.decProc tmp dead ++ [.assign dst (.arg (.v x))] ++ post =
                          (acc.reverse ++ mkDeadLoads x tmp dead ++ mkShellStores x hdr lay.nobj) ++
                            (mkDeadDecs l.decProc tmp dead ++ ([.assign dst (.arg (.v x))] ++ post)) := by
                        simp [List.append_assoc]
                      rw [hsplit, List.getElem?_append_right (by omega), hpreLen, Nat.add_sub_cancel_left,
                        List.getElem?_append_left (by rw [mkDeadDecs_length]; exact hq)]
                      exact mkDeadDecs_getElem? l.decProc tmp dead q hq
                    have hposEnd : decBasePos + dead.length < inBlk.body.size := by
                      have := congrArg List.length hfull
                      simp only [Array.length_toList, List.length_append, List.length_cons,
                        List.length_reverse, mkDeadLoads_length, mkShellStores_length, mkDeadDecs_length] at this
                      have := hcp.inPosEq
                      dsimp only [decBasePos, dead] at this ⊢; omega
                    have hstmtEnd : inBlk.body[decBasePos + dead.length]? = some (.assign dst (.arg (.v x))) := by
                      rw [← Array.getElem?_toList, hfull]
                      have hsplit : acc.reverse ++ mkDeadLoads x tmp dead ++ mkShellStores x hdr lay.nobj ++
                          mkDeadDecs l.decProc tmp dead ++ [.assign dst (.arg (.v x))] ++ post =
                          (acc.reverse ++ mkDeadLoads x tmp dead ++ mkShellStores x hdr lay.nobj ++ mkDeadDecs l.decProc tmp dead) ++
                            ([.assign dst (.arg (.v x))] ++ post) := by
                        simp [List.append_assoc]
                      have hpre2 : (acc.reverse ++ mkDeadLoads x tmp dead ++ mkShellStores x hdr lay.nobj ++
                          mkDeadDecs l.decProc tmp dead).length = decBasePos + dead.length := by
                        rw [List.length_append, hpreLen, mkDeadDecs_length]
                      rw [hsplit, List.getElem?_append_right (by omega), hpre2, Nat.sub_self]; rfl
                    have hcpEnd : ChunkPos l F fr₁.label B (fr₁.pos + 1) fr₂.label (decBasePos + dead.length + 1) := by
                      have hidx : fr₂.pos + ((deadFields lay.nobj mask).length + (1 + lay.nobj) + (deadFields lay.nobj mask).length + 1) = decBasePos + dead.length + 1 := by
                        dsimp only [decBasePos, dead]; omega
                      simpa [hidx] using hcpNext
                    have hfin : ResetFinish l F fr₁.label B (fr₁.pos + 1) dst x inBlk fr₂.label (decBasePos + dead.length) :=
                      .assign hposEnd hstmtEnd hcpEnd
                    refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                    refine ⟨rfl, rfl, .consResetDec (W := mkResetUWrapper l.decProc lay cls)
                      (B := B) (inBlk := inBlk) (n := lay.nobj) (base := 1) (oldBase := 2) (k := 0) (i := 0)
                      (decBasePos := decBasePos) (deadBase := tmp)
                      hwF hshape ⟨rfl, rfl, rfl⟩ (Nat.zero_le _) hw0 hw1 hwvals' hlt hfn hF rfl rfl
                      ⟨rfl, by simp [decBasePos, dead]⟩ hinBlk (by simp [deadFrom_zero]) (Nat.zero_le _) hdecs ?_ hx' hfin hagree' hrest,
                      fun _ _ h => by cases h; rfl⟩
                    intro q hq
                    have hltN := deadFields_lt lay.nobj mask (List.getElem_mem hq)
                    have hlen : allVals.length = lay.nobj := by have := loadFieldsMem_length hlf; simpa using this
                    rw [hdeadVals q hq, hwvals _ hltN, List.getElem?_eq_getElem (by omega)]
            | reuse dst slot idx lay cls args =>
              obtain ⟨c, hc, hsEq0, hlay, hclsOk, hlen, hok, _, _⟩ := classify_eq_reuse hcls
              have hsEq : B.body[fr₁.pos] = .call [dst] (l.reuseWrapper idx) (.v slot :: args) := hsEq0
              have hfullLt : argsMax (.v slot :: args) 0 < freshBase F :=
                call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
              have hslotLt : (slot : Nat) < freshBase F := by
                have h2 : slot ≤ argsMax (.v slot :: args) 0 := mem_le_argsMax (by simp)
                dsimp only [Lir.VReg] at h2 ⊢; omega
              have hargsLt : argsMax args 0 < freshBase F := by
                have h2 : argsMax args 0 ≤ argsMax (.v slot :: args) 0 := by
                  unfold argsMax; rw [List.foldl_cons]; exact argsMax_mono_local args (Nat.zero_le _)
                omega
              have hslotEq : fr₁.env[slot]? = fr₂.env[slot]? := hagree slot hslotLt
              have hargsEq : Lir.evalArgs fr₁.env args = Lir.evalArgs fr₂.env args := hagree.evalArgs_eq hargsLt
              cases hslot : fr₁.env[slot]? with
              | none =>
                exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hslot])
              | some slotVal =>
                cases hargs : Lir.evalArgs fr₁.env args with
                | none =>
                  have hargs' : List.mapM (Lir.Arg.eval fr₁.env) args = none := hargs
                  exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hslot, hargs'])
                | some vals =>
                  obtain ⟨hcpNext, hinlHot, hinlCold⟩ :=
                    inl_reuse_exec (raw := raw) (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                      (by rwa [← hsEq]) (by rwa [← hsEq]) hpos hsEq
                      (by rw [← hslotEq, hslot]) (by rw [← hargsEq, hargs]) hargsLt
                      (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                  by_cases htag : Lir.Cond.holds .tnz .w64 slotVal 1 = true
                  · have hraw := raw_reuse_cold_exec hr hF hB hpos hc hlay hclsOk hok hlen hsEq hslot hargs htag
                      (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                    have hinl := hinlCold htag
                    cases hres : evalAllocReserve lay cls mem₁ ctx₁ with
                    | stuck => rw [hres] at hraw; exact .rawStuckWithin (by omega) hraw
                    | oom => rw [hres] at hraw hinl; exact .sameOom (by omega) hraw hinl
                    | ok addr mem₂ =>
                      rw [hres] at hraw hinl
                      dsimp only at hraw hinl
                      cases hwf : writeFieldsMem mem₂ addr 0 vals with
                      | none => rw [hwf] at hraw; exact .rawStuckWithin (by omega) hraw
                      | some mem' =>
                        rw [hwf] at hraw hinl
                        obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                        obtain ⟨env', s₂', hs₂, hstar₂, hag'⟩ := hinl
                        have hagree' : AgreeBelow (freshBase F) (fr₁.env.insert dst addr) env' :=
                          fun r hr' => ((hagree.insert_same dst addr) r hr').trans (hag' r hr')
                        refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                          fun _ _ h => by cases h; rfl⟩
                  · have hcell : Lir.Cond.holds .tnz .w64 slotVal 1 = false := by simpa using htag
                    have hraw := raw_reuse_hot_exec hr hF hB hpos hc hlay hclsOk hlen hsEq hslot hargs hcell
                      (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                    dsimp only at hraw
                    have hinl := hinlHot hcell
                    cases hwm : writeReuseMem mem₁ slotVal (Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1) vals with
                    | none =>
                      rw [hwm] at hraw; exact .rawStuckWithin (by omega) hraw
                    | some mem' =>
                      rw [hwm] at hraw hinl
                      obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                      obtain ⟨s₂', hs₂, hstar₂⟩ := hinl
                      refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                      exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext (hagree.insert_same dst slotVal) rfl) hrest,
                        fun _ _ h => by cases h; rfl⟩
            | reuseU dst slot idx lay cls args =>
              obtain ⟨c, hc, hsEq0, hlay, hclsOk, hlen, _, _, _⟩ := classify_eq_reuseU hcls
              have hsEq : B.body[fr₁.pos] = .call [dst] (l.reuseUWrapper idx) (.v slot :: args) := hsEq0
              have hfullLt : argsMax (.v slot :: args) 0 < freshBase F :=
                call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
              have hslotLt : (slot : Nat) < freshBase F := by
                have h2 : slot ≤ argsMax (.v slot :: args) 0 := mem_le_argsMax (by simp)
                dsimp only [Lir.VReg] at h2 ⊢; omega
              have hargsLt : argsMax args 0 < freshBase F := by
                have h2 : argsMax args 0 ≤ argsMax (.v slot :: args) 0 := by
                  unfold argsMax; rw [List.foldl_cons]; exact argsMax_mono_local args (Nat.zero_le _)
                omega
              have hslotEq : fr₁.env[slot]? = fr₂.env[slot]? := hagree slot hslotLt
              have hargsEq : Lir.evalArgs fr₁.env args = Lir.evalArgs fr₂.env args := hagree.evalArgs_eq hargsLt
              cases hslot : fr₁.env[slot]? with
              | none =>
                exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hslot])
              | some slotVal =>
                cases hargs : Lir.evalArgs fr₁.env args with
                | none =>
                  have hargs' : List.mapM (Lir.Arg.eval fr₁.env) args = none := hargs
                  exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hslot, hargs'])
                | some vals =>
                  have hraw := raw_reuseU_exec hr hF hB hpos hc hlay hclsOk hlen hsEq hslot hargs
                    (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
                  dsimp only at hraw
                  obtain ⟨hcpNext, hinl⟩ := inl_reuseU_exec (raw := raw) (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                    (by rwa [← hsEq]) (by rwa [← hsEq]) hpos hsEq
                    (by rw [← hslotEq, hslot]) (by rw [← hargsEq, hargs])
                    (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                  cases hwm : writeReuseMem mem₁ slotVal (Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1) vals with
                  | none =>
                    rw [hwm] at hraw; exact .rawStuckWithin (by omega) hraw
                  | some mem' =>
                    rw [hwm] at hraw hinl
                    obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                    obtain ⟨s₂', hs₂, hstar₂⟩ := hinl
                    refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                    exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext (hagree.insert_same dst slotVal) rfl) hrest,
                      fun _ _ h => by cases h; rfl⟩
      · have hposEq : fr₁.pos = B.body.size := by have := hcp.posLe; omega
        obtain ⟨blk, hblk, hinPosEq, htermEq, hlbl₂⟩ := ChunkPos.at_term ⟨tmp, params, acc, rest0, hcp⟩ hposEq
        have hposGe : ¬ fr₁.pos < B.body.size := hpos
        have hinPosGe : ¬ fr₂.pos < blk.body.size := by omega
        have htMax : termMax B.term 0 < freshBase F := by
          have := term_le_maxVReg hB; unfold freshBase; omega
        cases ht : B.term with
        | jump e =>
          have heLt : argsMax e.args 0 < freshBase F := by simpa [ht, termMax, edgeMax] using htMax
          exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree heLt hrest
            (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht])
            (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm])
        | br c w a b' t f =>
          simp only [ht, termMax] at htMax
          obtain ⟨hfLt, h1⟩ := AgreeBelow.edge_lt_of_chain htMax
          obtain ⟨htLt, h2⟩ := AgreeBelow.edge_lt_of_chain h1
          obtain ⟨hbLt, haLt⟩ := AgreeBelow.arg_lt_of_chain h2
          have haEq := hagree.arg_eval haLt
          have hbEq := hagree.arg_eval hbLt
          cases ha : a.eval fr₁.env with
          | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha])
          | some va =>
            cases hb : b'.eval fr₁.env with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha, hb])
            | some vb =>
              by_cases hcond : c.holds w va vb = true
              · exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree htLt hrest
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb, hcond, ↓reduceIte])
                  (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← haEq, ha, ← hbEq, hb, hcond, ↓reduceIte])
              · have hcondF : c.holds w va vb = false := by simpa using hcond
                exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree hfLt hrest
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb, hcondF, Bool.false_eq_true, ↓reduceIte])
                  (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← haEq, ha, ← hbEq, hb, hcondF, Bool.false_eq_true, ↓reduceIte])
        | brOvf o x a b' ok ovf =>
          simp only [ht, termMax] at htMax
          obtain ⟨hovfLt, h1⟩ := AgreeBelow.edge_lt_of_chain htMax
          obtain ⟨hokLt, h2⟩ := AgreeBelow.edge_lt_of_chain h1
          obtain ⟨hbLt, h3⟩ := AgreeBelow.arg_lt_of_chain h2
          obtain ⟨haLt, _⟩ := AgreeBelow.arg_lt_of_chain h3
          have haEq := hagree.arg_eval haLt
          have hbEq := hagree.arg_eval hbLt
          cases ha : a.eval fr₁.env with
          | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha])
          | some va =>
            cases hb : b'.eval fr₁.env with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha, hb])
            | some vb =>
              let res := o.eval va vb
              have hagree' := hagree.insert_same x res.1
              cases hov : res.2 with
              | true =>
                exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree' hovfLt hrest
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb, res, hov, ↓reduceIte])
                  (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← haEq, ha, ← hbEq, hb, res, hov, ↓reduceIte])
              | false =>
                exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree' hokLt hrest
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb, res, hov, Bool.false_eq_true, ↓reduceIte])
                  (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← haEq, ha, ← hbEq, hb, res, hov, Bool.false_eq_true, ↓reduceIte])
        | ret as =>
          have hargsLt : argsMax as 0 < freshBase F := by simpa [ht, termMax] using htMax
          have hargsEq := hagree.evalArgs_eq hargsLt
          cases hargs : Lir.evalArgs fr₁.env as with
          | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs])
          | some vals =>
            exact matched_of_ret (vals := vals)
              (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, hargs]; rfl)
              (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← hargsEq, hargs]; rfl) hrest
        | tail g as =>
          have hargsLt : argsMax as 0 < freshBase F := by simpa [ht, termMax] using htMax
          have hargsEq := hagree.evalArgs_eq hargsLt
          cases hargs : Lir.evalArgs fr₁.env as with
          | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs])
          | some vs =>
            obtain ⟨heFwd, _, _⟩ := enter_rel l raw (g := g) (vs := vs)
            cases hent : Lir.enter raw g vs with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs, hent])
            | some callee₁ =>
              obtain ⟨callee₂, hent₂, hfrCallee, hdstCallee⟩ := heFwd callee₁ hent
              have hs₁ : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } =
                  .next { mem := mem₁, ctx := ctx₁, stack := callee₁ :: rest₁ } true := by
                apply Lir.semStep_next.mpr; unfold Lir.step; simp [hF, hB, hposGe, ht, hargs, hent]
              have hs₂ : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } =
                  .next { mem := mem₁, ctx := ctx₁, stack := callee₂ :: rest₂ } true := by
                apply Lir.semStep_next.mpr; unfold Lir.step
                simp [hF', hblk, hinPosGe, htermEq, ht, relabelTerm, ← hargsEq, hargs, hent₂]
              refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
              exact ⟨rfl, rfl, .cons hfrCallee hrest, fun _ _ h => by cases h; exact hdstCallee⟩
        | fail r =>
          refine .sameFinal (r := .resource r) ?_ ?_
          · rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hposGe, ht]; exact .fail
          · rw [Lir.semStep]; unfold Lir.step; simp [hF', hblk, hinPosGe, htermEq, ht, relabelTerm]; exact .fail
        | trap =>
          refine .sameFinal (r := .trap) ?_ ?_
          · rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hposGe, ht]; exact .trap
          · rw [Lir.semStep]; unfold Lir.step; simp [hF', hblk, hinPosGe, htermEq, ht, relabelTerm]; exact .trap

/-! ## Forward and backward clocked runs -/

theorem forward_run {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw) :
    ∀ fuel k s₁ s₂ r, StateRel l raw s₁ s₂ →
      Sem.runClocked (Lir.semStep raw) fuel k s₁ = r →
      r ≠ .timeout → r ≠ .stuck →
      ∃ k' r₂, Sem.Reaches (Lir.semStep (inlineProgram l raw)) s₂ k' r₂ ∧ Sem.Result.Refines Eq r r₂ := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro k s₁ s₂ r hrel hrun hnt hns
    have hr1 : Sem.Reaches (Lir.semStep raw) s₁ k r := Sem.runClocked_sound hrun hnt
    cases step_match hr hrel with
    | rawStuck hst =>
      have h2 : Sem.Reaches (Lir.semStep raw) s₁ k .stuck := .final (by rw [Lir.semStep, hst]; exact .stuck)
      exact absurd (hr1.det h2) hns
    | @rawStuckWithin c₁ hc hst =>
      have h2 : Sem.Reaches (Lir.semStep raw) s₁ (max k c₁) .stuck := hst.mono (by simp) (Nat.le_max_right k c₁)
      have h1 : Sem.Reaches (Lir.semStep raw) s₁ (max k c₁) r := hr1.mono hnt (Nat.le_max_left k c₁)
      exact absurd (h1.det h2) hns
    | sameFinal hf₁ hf₂ =>
      have heq : r = _ := hr1.det (.final hf₁)
      subst heq
      exact ⟨0, _, .final hf₂, Sem.Result.Refines.refl (fun _ => rfl)⟩
    | @sameOom c₁ hc hoom₁ hoom₂ =>
      have h2 : Sem.Reaches (Lir.semStep raw) s₁ (max k c₁) (.resource .heap) := hoom₁.mono (by simp) (Nat.le_max_right k c₁)
      have h1 : Sem.Reaches (Lir.semStep raw) s₁ (max k c₁) r := hr1.mono hnt (Nat.le_max_left k c₁)
      have heq := h1.det h2
      subst heq
      exact ⟨0, .resource .heap, hoom₂, .resource .heap⟩
    | sync hs₁ hstar₁ hs₂ hstar₂ _ hrel' =>
      obtain ⟨fuel', k', hflt, _, hrun'⟩ := runClocked_star_inv_lt hs₁ hstar₁ hrun hnt
      obtain ⟨k₂, r₂, hreach₂, href⟩ := ih fuel' hflt k' _ _ r hrel' hrun' hnt hns
      exact ⟨_, r₂, reaches_of_star_reaches (Sem.Star.head hs₂ hstar₂) hreach₂, href⟩

theorem backward_run {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw) :
    ∀ fuel k s₁ s₂ r, StateRel l raw s₁ s₂ →
      Sem.runClocked (Lir.semStep (inlineProgram l raw)) fuel k s₂ = r →
      r ≠ .timeout → (∀ fail, r ≠ .resource fail) →
      ∃ r₁, r₁ ≠ .timeout ∧ Sem.Reaches (Lir.semStep raw) s₁ (k + 12 * fuel) r₁ := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro k s₁ s₂ r hrel hrun hnt hnr
    have hfuelPos : 1 ≤ fuel := by
      cases fuel with
      | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hnt
      | succ _ => omega
    have hr2 : Sem.Reaches (Lir.semStep (inlineProgram l raw)) s₂ k r := Sem.runClocked_sound hrun hnt
    cases step_match hr hrel with
    | rawStuck hst =>
      exact ⟨.stuck, by simp, .final (by rw [Lir.semStep, hst]; exact .stuck)⟩
    | rawStuckWithin hc hst =>
      exact ⟨.stuck, by simp, hst.mono (by simp) (by omega)⟩
    | sameFinal hf₁ hf₂ =>
      have heq : r = _ := hr2.det (.final hf₂)
      subst heq
      exact ⟨r, hnt, .final hf₁⟩
    | sameOom hc hoom₁ hoom₂ =>
      have h2 := hoom₂.mono (by simp) (Nat.zero_le k)
      exact absurd (hr2.det h2) (hnr .heap)
    | @sync s₁' s₂' s₁'' s₂'' b₁ b₂ c₁ c₂ hs₁ hstar₁ hs₂ hstar₂ hchg hrel' =>
      obtain ⟨fuel', k', hflt, hkEq, hrun'⟩ := runClocked_star_inv_lt hs₂ hstar₂ hrun hnt
      obtain ⟨r₁, hr₁nt, hreach₁⟩ := ih fuel' hflt k' s₁'' s₂'' r hrel' hrun' hnt hnr
      have htotal := reaches_of_star_reaches (Sem.Star.head hs₁ hstar₁) hreach₁
      exact ⟨r₁, hr₁nt, htotal.mono hr₁nt (by omega)⟩

/-! ## Top-level simulation theorem (`inlineProgram_sim`) -/

/-- **`inlineProgram l raw` simulates `raw` with exact value equality.** -/
theorem inlineProgram_sim {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word) :
    Sem.Sim Eq (fun k => k + 12 * Lir.fuelFor (inlineProgram l raw) k)
      (fun k => Lir.eval raw k args mem ctx)
      (fun k => Lir.eval (inlineProgram l raw) k args mem ctx) := by
  let inl := inlineProgram l raw
  have hmain : inl.main = raw.main := rfl
  obtain ⟨heFwd, _, heNone⟩ := enter_rel l raw (g := raw.main) (vs := args)
  cases hent : Lir.enter raw raw.main args with
  | none =>
    have hent₂ : Lir.enter inl inl.main args = none := by rw [hmain]; exact heNone.mp hent
    have he1 : ∀ k, Lir.eval raw k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hent]
    have he2 : ∀ k, Lir.eval inl k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hent₂]
    exact {
      forward := fun k _ => ⟨k, by rw [he1, he2]; exact .stuck⟩
      timeout := fun k hk => by rw [he1] at hk; cases hk }
  | some fr₁ =>
    obtain ⟨fr₂, hent₂, hfr, hdst₁⟩ := heFwd fr₁ hent
    let s₁ : Lir.State := { mem, ctx, stack := [fr₁] }
    let s₂ : Lir.State := { mem, ctx, stack := [fr₂] }
    have hinit₁ : Lir.State.initial raw args mem ctx = some s₁ := by
      simp [Lir.State.initial, hent, s₁]
    have hinit₂ : Lir.State.initial inl args mem ctx = some s₂ := by
      simp [Lir.State.initial, hmain, inl, hent₂, s₂]
    have hruns₁ := Lir.runs_eval hinit₁
    have hruns₂ := Lir.runs_eval hinit₂
    have hrel : StateRel l raw s₁ s₂ :=
      ⟨rfl, rfl, .cons hfr .nil, fun _ _ h => by cases h; exact hdst₁⟩
    exact {
      forward := fun k hk => by
        by_cases hst : Lir.eval raw k args mem ctx = .stuck
        · exact ⟨0, hst ▸ .stuck⟩
        · have hrun : Sem.runClocked (Lir.semStep raw) (Lir.fuelFor raw k) k s₁ =
              Lir.eval raw k args mem ctx := by
            rw [Lir.eval_eq, hinit₁]
          obtain ⟨k', r₂, hreach₂, href⟩ := forward_run hr (Lir.fuelFor raw k) k s₁ s₂ _ hrel hrun hk hst
          exact ⟨k', hruns₂.eq hreach₂ ▸ href⟩
      timeout := fun k hk => by
        by_cases hto : Lir.eval inl k args mem ctx = .timeout
        · exact .inl hto
        · by_cases hres : ∃ fail, Lir.eval inl k args mem ctx = .resource fail
          · exact .inr hres
          · have hres' : ∀ fail, Lir.eval inl k args mem ctx ≠ .resource fail :=
              fun fail h => hres ⟨fail, h⟩
            have hrun₂ : Sem.runClocked (Lir.semStep inl) (Lir.fuelFor inl k) k s₂ =
                Lir.eval inl k args mem ctx := by
              rw [Lir.eval_eq, hinit₂]
            obtain ⟨r₁, hr₁nt, hreach₁⟩ := backward_run hr (Lir.fuelFor inl k) k s₁ s₂ _ hrel hrun₂ hto hres'
            have hto₁ : Sem.Reaches (Lir.semStep raw) s₁ (k + 12 * Lir.fuelFor inl k) .timeout :=
              hk ▸ hruns₁ (k + 12 * Lir.fuelFor inl k)
            exact absurd (hreach₁.det hto₁) hr₁nt }

/-! ## Lifting `inlineProgram_sim` across `splitCriticalEdges` and clock maps -/

private theorem foldl_add_eq_sum {α : Type} (f : α → Nat) :
    ∀ (xs : List α) (acc : Nat), xs.foldl (fun n x => n + f x) acc = acc + (xs.map f).sum
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_eq_sum f xs]
    omega

theorem func_size_eq_sum (F : Lir.Func) :
    F.size = (F.blocks.toList.map Lir.Block.size).sum := by
  unfold Lir.Func.size
  rw [← Array.foldl_toList, foldl_add_eq_sum, Nat.zero_add]

theorem program_size_eq_sum (p : Lir.Program) :
    p.size = (p.funcs.toList.map Lir.Func.size).sum := by
  unfold Lir.Program.size
  rw [← Array.foldl_toList, foldl_add_eq_sum, Nat.zero_add]

private theorem emit_size_ge (blocks : List Lir.Block) (critical : Lir.Block → Lir.Edge → Bool)
    (relabel : Lir.Label → Lir.Label) :
    ∀ (bs : List Lir.Block) (ls : List Lir.Label), bs.length = ls.length →
      (bs.map Lir.Block.size).sum ≤
        ((Lir.Func.splitCriticalEdges.emit blocks critical relabel bs ls).map Lir.Block.size).sum
  | [], [], _ => Nat.le_refl _
  | b :: bs, l :: ls, hlen => by
    simp only [Lir.Func.splitCriticalEdges.emit, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, Lir.Block.size]
    have ih := emit_size_ge blocks critical relabel bs ls (by simpa using hlen)
    omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem func_size_le_split (F : Lir.Func) : F.size ≤ F.splitCriticalEdges.size := by
  rw [func_size_eq_sum, func_size_eq_sum]
  unfold Lir.Func.splitCriticalEdges
  dsimp only
  split
  · exact Nat.le_refl _
  · rw [List.toList_toArray]
    apply emit_size_ge
    rw [Lir.newLabels_length]
    simp

private theorem list_sum_map_le {α : Type} (f g : α → Nat) (h : ∀ x, f x ≤ g x) :
    ∀ (xs : List α), (xs.map f).sum ≤ (xs.map g).sum
  | [] => Nat.le_refl _
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons]
    have hx := h x
    have ih := list_sum_map_le f g h xs
    omega

theorem program_size_le_split (p : Lir.Program) : p.size ≤ p.splitCriticalEdges.size := by
  rw [program_size_eq_sum, program_size_eq_sum]
  simp only [Lir.Program.splitCriticalEdges_eq, Array.toList_map, List.map_map]
  exact list_sum_map_le Lir.Func.size (Lir.Func.size ∘ Lir.Func.splitCriticalEdges)
    func_size_le_split p.funcs.toList

theorem fuelFor_le_split (p : Lir.Program) (k : Nat) :
    Lir.fuelFor p k ≤ Lir.fuelFor p.splitCriticalEdges k := by
  unfold Lir.fuelFor
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (program_size_le_split p) 1)

theorem fuelFor_main (p : Lir.Program) (m k : Nat) :
    Lir.fuelFor { p with main := m } k = Lir.fuelFor p k := rfl

/-- Single-pass target-indexed clock map (`k + 3072 * fuelFor p k`, absorbing the ≤256×
size reduction of `pruneDeadRuntime`). -/
def inlineStepClock (p : Lir.Program) (k : Nat) : Nat := k + 3072 * Lir.fuelFor p k

/-- Target-indexed clock map for `inlineProgram`, `InlineWrappers`, `FastDec`, `pruneDeadRuntime`, and `splitCriticalEdges`. -/
def inlineClock (p : Lir.Program) (k : Nat) : Nat :=
  inlineStepClock p (inlineStepClock p (inlineStepClock p k))

/-- Entry-level clock map composing `Nat.succ` with `inlineClock`. -/
def inlineEntryClock (p : Lir.Program) (k : Nat) : Nat := Nat.succ (inlineClock p k)

theorem inlineProgram_sim_clock {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word)
    {f : Nat → Nat} (hf : ∀ k, k + 12 * Lir.fuelFor (inlineProgram l raw) k ≤ f k) :
    Sem.Sim Eq f
      (fun k => Lir.eval raw k args mem ctx)
      (fun k => Lir.eval (inlineProgram l raw) k args mem ctx) :=
  let hsim := inlineProgram_sim hr args mem ctx
  { forward := hsim.forward
    timeout := fun k hk => by
      apply hsim.timeout k
      by_cases h0 : Lir.eval raw (k + 12 * Lir.fuelFor (inlineProgram l raw) k) args mem ctx = .timeout
      · exact h0
      · have heq := Lir.eval_mono raw args mem ctx (hf k) h0
        dsimp only at heq
        rw [hk] at heq
        exact absurd heq.symm h0 }

end IxCC.Cfg.Rc.Inline
