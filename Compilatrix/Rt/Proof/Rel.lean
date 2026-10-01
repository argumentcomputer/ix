import Compilatrix.Rt.Proof.LayoutFun
import Compilatrix.Cfg.Semantics

/-!
# The state relation of `Rt.lower_correct`

Between a Cfg state (over the immortal heap) and a Lir state of the lowered
program (before pruning and edge splitting):

* the heap invariant (`HeapInv`) for some placement `Pw` of Cfg's cells;
* a running frame (`RunAt`): Lir is where the code for the rest of the
  frame's block starts (`PosAt`: the function's layout, and a state of its
  block's lowering that the lowering's rest runs from to the chunk's final
  state), its registers hold related words for Cfg's live variables (all
  but fused comparisons, which Lir never computes), and in a fused block
  past its comparison Cfg's comparison is known (`FusedDone`);
* each suspended caller (`SuspAt`) is positioned after its call, waiting
  for the result in the call's variable;
* a Cfg call (`.call`) is a Lir state whose next step enters the callee on
  related words with the related callers (a call statement or a tail
  call);
* a Cfg return (`.ret`) is a Lir frame at a `ret` of a related word.

`Res` relates final values: one related word, under the heap invariant.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

/-- The lowered (unpruned) program has each Cfg function's lowering and the
runtime procedures. -/
structure Target (P : Cfg.Program) (lp : Lir.Program) : Prop where
  fn : ∀ {f : Nat} {fd : Cfg.Fun}, P.fun? f = some fd →
    ∃ F starts, lp.funcs[f]? = some F ∧ Lowered (tables P) f fd F starts
  pow : lp.funcs[(tables P).natPow]? = some Procs.natPow
  gcd : lp.funcs[(tables P).natGcd]? = some Procs.natGcd

/-- Where the code for the rest of Cfg frame `fr` (block `b` of function
`fd`) starts in Lir frame `lfr`, with the lowering's state there. -/
def PosAt (P : Cfg.Program) (lp : Lir.Program) (fr : Cfg.Frame) (lfr : Lir.Frame) (fd : Cfg.Fun) (b : Cfg.Block) :
    Prop :=
  ∃ (F : Lir.Func) (starts : NatMap Nat) (off : Nat) (C : List PBlock) (st stF : St),
    P.fun? fr.fn = some fd ∧ fd.blocks[fr.blk]? = some b ∧ lp.funcs[fr.fn]? = some F ∧
    Lowered (tables P) fr.fn fd F starts ∧ starts.get? fr.blk = some off ∧ Holds fr.fn F off starts C ∧
    (restAct fr.fn (tables P) (useCounts fd) fr.blk b fr.rest).run st = .ok ((), stF) ∧ Ext C stF ∧
    Labels st ∧ Open st ∧ supOf fd ≤ st.fresh ∧ (∃ pre, pre ++ fr.rest = b.body) ∧
    lfr.fn = fr.fn ∧ lfr.label = off + st.cur ∧ lfr.pos = st.acc.length

/-- In a fused block past its comparison: Cfg's comparison of the operands
is the scrutinee's value. -/
def FusedDone (T : Tables) (fd : Cfg.Fun) (b : Cfg.Block) (fr : Cfg.Frame) : Prop :=
  ∀ init c a a', fusable T (useCounts fd) b = some (init, c, a, a') → fr.rest = [] →
    ∃ x op va vb v, b.body = init ++ [.bind x (.fir (.prim op [a, a']))] ∧
      Own.evalArgs fr.env [a, a'] = some [va, vb] ∧ Own.primResult (ownTables T) op [va, vb] = .ok v ∧
      fr.env.get? x = some v

/-- A running frame. -/
def RunAt (P : Cfg.Program) (lp : Lir.Program) (Pw : List Word) (fr : Cfg.Frame) (lfr : Lir.Frame) : Prop :=
  lfr.dsts = [] ∧ ∃ fd b, PosAt P lp fr lfr fd b ∧
    EnvRel (tables P) Pw (Fused (tables P) fd) (supOf fd) fr.env lfr.env ∧ FusedDone (tables P) fd b fr

/-- A suspended caller, waiting for its call's variable. -/
def SuspAt (P : Cfg.Program) (lp : Lir.Program) (Pw : List Word) (p : Cfg.Frame × Nat) (lfr : Lir.Frame) : Prop :=
  lfr.dsts = [p.2] ∧ ∃ fd b, PosAt P lp p.1 lfr fd b ∧
    EnvRel (tables P) Pw (Fused (tables P) fd) (supOf fd) p.1.env lfr.env ∧ p.2 < supOf fd ∧
    ((fusable (tables P) (useCounts fd) b).isNone = true ∨ p.1.rest ≠ [])

/-- A Lir frame at a `ret` of `w`. -/
def RetAt (lp : Lir.Program) (lfr : Lir.Frame) (w : Word) : Prop :=
  lfr.dsts = [] ∧ ∃ (F : Lir.Func) (lb : Lir.Block) (la : Lir.Arg), lp.funcs[lfr.fn]? = some F ∧
    F.blocks[lfr.label]? = some lb ∧ lfr.pos = lb.body.size ∧ lb.term = .ret [la] ∧ la.eval lfr.env = some w

/-- A Cfg state's heap. -/
def heapOf : Cfg.State → Own.Heap
  | .call _ _ _ H | .run _ _ H | .ret _ _ H => H

/-- **The state relation.** -/
def Rel (P : Cfg.Program) (lp : Lir.Program) (ctx : Word) (s₁ : Cfg.State) (s₂ : Lir.State) : Prop :=
  s₂.ctx = ctx ∧ ∃ Pw, HeapInv (tables P) Pw (heapOf s₁) ctx s₂.mem ∧
    match s₁ with
    | .run fr stk _ => ∃ lfr lrest, s₂.stack = lfr :: lrest ∧ RunAt P lp Pw fr lfr ∧
        ListRel (SuspAt P lp Pw) stk lrest
    | .call g vs stk _ => ∃ ws lrest, ListRel (ValRel (tables P) Pw) vs ws ∧ ListRel (SuspAt P lp Pw) stk lrest ∧
        ∀ callee, Lir.enter lp g ws = some callee → Lir.step lp s₂ = .next { s₂ with stack := callee :: lrest } true
    | .ret v stk _ => ∃ lfr lrest w, s₂.stack = lfr :: lrest ∧ ValRel (tables P) Pw v w ∧ RetAt lp lfr w ∧
        ListRel (SuspAt P lp Pw) stk lrest

/-- **Related final values**: one related word, under the heap invariant. -/
def Res (P : Cfg.Program) (ctx : Word) (r₁ : Own.RVal × Own.Heap) (r₂ : List Word × X86.Memory) : Prop :=
  ∃ Pw w, r₂.1 = [w] ∧ ValRel (tables P) Pw r₁.1 w ∧ HeapInv (tables P) Pw r₁.2 ctx r₂.2

theorem SuspAt.mono {P : Cfg.Program} {lp : Lir.Program} {Pw Pw' : List Word} (hP : Pw <+: Pw')
    {p : Cfg.Frame × Nat} {lfr : Lir.Frame} (h : SuspAt P lp Pw p lfr) : SuspAt P lp Pw' p lfr := by
  obtain ⟨hd, fd, b, hpos, hρ, hx, hf⟩ := h
  exact ⟨hd, fd, b, hpos, hρ.mono hP, hx, hf⟩

theorem stack_mono {P : Cfg.Program} {lp : Lir.Program} {Pw Pw' : List Word} (hP : Pw <+: Pw')
    {stk : List (Cfg.Frame × Nat)} {lrest : List Lir.Frame} (h : ListRel (SuspAt P lp Pw) stk lrest) :
    ListRel (SuspAt P lp Pw') stk lrest :=
  h.mono fun _ _ hs => hs.mono hP

/-- `fun?` names a function at most once. -/
theorem fun_unique {P : Cfg.Program} {f : Nat} {fd fd' : Cfg.Fun} (h : P.fun? f = some fd) (h' : P.fun? f = some fd') :
    fd' = fd := by
  rw [h] at h'
  exact (Option.some.inj h').symm

end Compilatrix.Rt.Proof
