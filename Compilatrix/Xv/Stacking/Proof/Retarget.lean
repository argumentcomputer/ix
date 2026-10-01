import Compilatrix.Xv.Stacking.Proof.Ends

/-!
# Stacking from any export's wrapper

`Stacking.run` emits one wrapper per SysV export and starts the program at
`main`'s. Nothing else in the stacked program depends on which function is
`main`: the same run for `{ p with main := g }` gives the same program
started at `g`'s wrapper, with the same shape and exports
(`run_withMain`). So the stacking theorem for `main` (`stacked_ends`,
`wrapper_overflow`) holds for every export: `stacked_ends_at` and
`wrapper_overflow_at` run the stacked program from the wrapper of `g`
against `g`'s clocked Xl run.

- `export_at`: every export's wrapper is placed at its first block, its
  function is a SysV export of its symbol and passes its arguments as
  `exportReps` says;
- `run_exports`: the exports `run` reports are its wrappers';
- `wrapper_of_export`: a SysV export function has a wrapper.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream
open Compilatrix.Lir (FunId)
open Compilatrix.Xv.Stacking

/-- A well-formed program started at another of its blocks is well formed
(the kernel-style check). -/
theorem wellFormedK_withEntry {p : X86.Program} (h : p.wellFormedK = true) {b : X86.BlockId}
    (hb : b.toNat < p.blocks.size) : ({ p with entry := b } : X86.Program).wellFormedK = true := by
  simp only [X86.Program.wellFormedK, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨⟨⟨h.1.1.1, h.1.1.2⟩, by simpa using hb⟩, h.2⟩

/-- **Every export's wrapper**: its function is a SysV export of its
symbol, its argument passing is `exportReps`'s, and its blocks sit at its
placement. -/
theorem export_at {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} {env : Xl.Env}
    {st : Stacked} (h : run p layouts reps env = .ok st) {w : PlacedExport} (hw : w ∈ runWrappers p layouts reps) :
    ∃ (f : Func Loc) (blks : List X86.Block),
      p.funcs[w.fn]? = some f ∧ f.conv = .sysvExport w.symbol ∧ w.reps = exportReps reps w.fn f ∧
      wrapperOf (entriesOf (runPlaced p layouts reps)) w f = .ok blks ∧
      ∀ j, j < blks.length → st.program.blocks[w.start + j]? = blks[j]? := by
  obtain ⟨hlen, -, -, -, -, wrapperCode, funcCode, main, hwc, hfc, hmain, hprog, -⟩ := run_ok h
  obtain ⟨i, hi, hmi⟩ := List.getElem_of_mem hw
  have hwi : (runWrappers p layouts reps)[i]? = some w := by rw [List.getElem?_eq_getElem hi, hmi]
  have hilen : i < (exportsOf reps (withLayouts p layouts)).length := by
    rw [runWrappers, placeExports_eq] at hi
    simpa [placeList_length] using hi
  obtain ⟨e, he⟩ : ∃ e, (exportsOf reps (withLayouts p layouts))[i]? = some e :=
    ⟨_, List.getElem?_eq_getElem hilen⟩
  have hwe := placeList_get (fun (e : FunId × String × List ArgRep × Func Loc) n =>
      ({ fn := e.1, symbol := e.2.1, reps := e.2.2.1, start := n } : PlacedExport))
    (fun e => wrapperBlocks e.2.2.1) _ exitBlocks i e he
  have hwi' := hwi
  rw [runWrappers, placeExports_eq] at hwi'
  rw [hwi', Option.some.injEq] at hwe
  obtain ⟨fn, s, rs, f⟩ := e
  have hem := List.mem_of_getElem? he
  simp only [exportsOf, List.mem_filterMap] at hem
  obtain ⟨x, hx, hxe⟩ := hem
  obtain ⟨hxf, -, -⟩ := withLayouts_mem hx
  split at hxe
  · rename_i s' hconv
    simp only [Option.some.injEq, Prod.mk.injEq] at hxe
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hxe
    obtain ⟨-, hget⟩ := mapM_ok hwc
    have hz : ((runWrappers p layouts reps).zip (exportsOf reps (withLayouts p layouts)))[i]? =
        some (w, (x.2.1, s', exportReps reps x.2.1 x.1, x.1)) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hwi, he⟩
    obtain ⟨blks, hblks, hwo⟩ := hget i _ hz
    subst hwe
    refine ⟨x.1, blks, hxf, hconv, rfl, hwo, fun j hj => ?_⟩
    rw [hprog]
    simp only [List.getElem?_toArray, List.append_assoc]
    have hwl : wrapperCode.map List.length =
        (exportsOf reps (withLayouts p layouts)).map fun e => wrapperBlocks e.2.2.1 := by
      have := mapM_lengths (sz := fun (x : PlacedExport × (FunId × String × List ArgRep × Func Loc)) =>
          wrapperBlocks x.1.reps)
        (fun x ys hx => by
          obtain ⟨w, fn, s, rs, f⟩ := x
          have hx' : wrapperOf (entriesOf (runPlaced p layouts reps)) w f = .ok ys := hx
          obtain ⟨-, -, _, _, -, hw⟩ := wrapperOf_ok hx'
          exact wrapper_length hw) hwc
      rw [this, runWrappers, placeExports_eq]
      apply List.ext_getElem
      · simp [List.length_zip, placeList_length]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_zip]
        have hi : i < (exportsOf reps (withLayouts p layouts)).length := by
          simp [List.length_zip, placeList_length] at h1; omega
        have := placeList_get (fun (e : FunId × String × List ArgRep × Func Loc) n =>
            ({ fn := e.1, symbol := e.2.1, reps := e.2.2.1, start := n } : PlacedExport))
          (fun e => wrapperBlocks e.2.2.1) _ exitBlocks i _ (List.getElem?_eq_getElem hi)
        rw [List.getElem?_eq_getElem (by rwa [placeList_length])] at this
        simp only [Option.some.injEq] at this
        rw [this]
    have hlen5 : (exitGroup 0).length = exitBlocks := by simp [exitGroup, exitBlocks]
    rw [← hlen5, Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      ← take_sum_eq hwl i]
    have hidx := flatten_getElem? wrapperCode i j blks hblks hj
    have hlt : ((wrapperCode.take i).map List.length).sum + j < wrapperCode.flatten.length :=
      (List.getElem?_eq_some_iff.1 (hidx.trans (List.getElem?_eq_getElem hj))).1
    rw [List.getElem?_append_left hlt]
    exact hidx
  · simp at hxe

/-- An export's wrapper starts at a block of the program. -/
theorem export_start {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} {env : Xl.Env}
    {st : Stacked} (h : run p layouts reps env = .ok st) {w : PlacedExport} (hw : w ∈ runWrappers p layouts reps) :
    w.start < st.program.blocks.size := by
  obtain ⟨f, blks, -, -, -, hwo, hat⟩ := export_at h hw
  obtain ⟨-, -, _, _, -, hwr⟩ := wrapperOf_ok hwo
  have hl := wrapper_length hwr
  have hpos : 0 < blks.length := by
    rw [hl]; unfold wrapperBlocks; split <;> omega
  have h0 := hat 0 hpos
  rw [Nat.add_zero, List.getElem?_eq_getElem hpos] at h0
  exact (Array.getElem?_eq_some_iff.1 h0).1

/-- The exports `run` reports, and its layout shape's roots, are its wrappers'. -/
theorem run_exports {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} {env : Xl.Env}
    {st : Stacked} (h : run p layouts reps env = .ok st) :
    st.exports = (runWrappers p layouts reps).map (fun w => { fn := w.fn, symbol := w.symbol, block := w.start }) ∧
      st.shape.roots = (runWrappers p layouts reps).map (·.start) := by
  unfold run at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · split at h
                  · simp only [Except.ok.injEq] at h
                    subst h
                    exact ⟨rfl, rfl⟩
                  · cases h
                · cases h
          · cases h
  · cases h

/-- **The same run started at another export**: for the program whose
`main` is `g`, `run` makes the same stacked program started at `g`'s
wrapper (the first wrapper of `g`), with the same shape and exports. -/
theorem run_withMain {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} {env : Xl.Env}
    {st : Stacked} (h : run p layouts reps env = .ok st) {g : FunId} {w : PlacedExport}
    (hw : (runWrappers p layouts reps).find? (·.fn == g) = some w) :
    run { p with main := g } layouts reps env =
      .ok { st with program := { st.program with entry := UInt32.ofNat w.start } } := by
  have hb := export_start h (List.mem_of_find?_eq_some hw)
  unfold runWrappers at hw
  unfold run at h ⊢
  simp only [bind, Except.bind, pure, Except.pure] at h ⊢
  split at h
  · rename_i c1
    split
    case isFalse hne => exact absurd c1 hne
    split at h
    · cases h
    · rename_i c2
      split
      case h_1 heq => exact absurd (heq.symm.trans c2) (by simp)
      split at h
      · cases h
      · rename_i c3
        split
        case h_1 heq => exact absurd (heq.symm.trans c3) (by simp)
        split at h
        · cases h
        · rename_i c4
          split
          case h_1 heq => exact absurd (heq.symm.trans c4) (by simp)
          split at h
          · rename_i c5
            split
            case isFalse hne => exact absurd c5 hne
            split at h
            · cases h
            · rename_i wrapperCode c6
              split
              case h_1 heq => exact absurd (heq.symm.trans c6) (by simp)
              rename_i wc' c6'
              obtain rfl : wc' = wrapperCode := Except.ok.inj (c6'.symm.trans c6)
              split at h
              · cases h
              · rename_i funcCode c7
                split
                case h_1 heq => exact absurd (heq.symm.trans c7) (by simp)
                rename_i fc' c7'
                obtain rfl : fc' = funcCode := Except.ok.inj (c7'.symm.trans c7)
                split at h
                · rename_i main c8
                  split at h
                  · rename_i c9
                    split
                    case h_1 =>
                      rename_i main' c8'
                      obtain rfl : main' = w := Option.some.inj (c8'.symm.trans hw)
                      cases h
                      have hsz : (exitGroup 0 ++ wc'.flatten ++ fc'.flatten).toArray.size < 2 ^ 32 := by
                        have := c9
                        simp only [X86.Program.wellFormedK, Bool.and_eq_true, decide_eq_true_eq] at this
                        simpa using this.1.1.2
                      have hb' : main'.start < (exitGroup 0 ++ wc'.flatten ++ fc'.flatten).toArray.size := hb
                      have hwf' : ({ blocks := (exitGroup 0 ++ wc'.flatten ++ fc'.flatten).toArray, entry := UInt32.ofNat main'.start } : X86.Program).wellFormedK = true := by
                        refine wellFormedK_withEntry c9 ?_
                        show (UInt32.ofNat main'.start).toNat < _
                        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
                        exact hb'
                      rw [ite_eq_left_iff.mpr (fun h => absurd hwf' h)]
                      rfl
                    case h_2 hne => exact (hne w hw).elim
                  · cases h
                · cases h
          · cases h
  · cases h

/-- A SysV export function has a wrapper. -/
theorem wrapper_of_export {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)}
    {env : Xl.Env} {st : Stacked} (h : run p layouts reps env = .ok st) {g : FunId} {f : Func Loc} {s : String}
    (hf : p.funcs[g]? = some f) (hconv : f.conv = .sysvExport s) :
    ∃ w, (runWrappers p layouts reps).find? (·.fn == g) = some w := by
  obtain ⟨hlen, -⟩ := run_ok h
  have hg : g < p.funcs.size := (Array.getElem?_eq_some_iff.1 hf).1
  have hgl : g < layouts.length := by rw [hlen]; exact hg
  obtain ⟨l, hl⟩ : ∃ l, layouts[g]? = some l := ⟨layouts[g], List.getElem?_eq_getElem hgl⟩
  have hx := List.mem_of_getElem? (withLayouts_get hf hl)
  have he : (g, s, exportReps reps g f, f) ∈ exportsOf reps (withLayouts p layouts) := by
    simp only [exportsOf, List.mem_filterMap]
    exact ⟨_, hx, by simp [hconv]⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
  have hwe := placeList_get (fun (e : FunId × String × List ArgRep × Func Loc) n =>
      ({ fn := e.1, symbol := e.2.1, reps := e.2.2.1, start := n } : PlacedExport))
    (fun e => wrapperBlocks e.2.2.1) _ exitBlocks i _ hi
  have hmem := List.mem_of_getElem? hwe
  have hsome : ((runWrappers p layouts reps).find? (·.fn == g)).isSome := by
    rw [List.find?_isSome]
    have hw0 : (placeExports (exportsOf reps (withLayouts p layouts))).1 = runWrappers p layouts reps := rfl
    rw [placeExports_eq] at hw0
    dsimp only at hw0
    rw [hw0] at hmem
    exact ⟨_, hmem, by simp⟩
  exact Option.isSome_iff_exists.1 hsome

/-- The stacking problem for `S`'s program started at `g`'s wrapper. -/
def Stk.withMain (S : Stk) (g : FunId) (w : PlacedExport)
    (hw : (runWrappers S.p S.layouts S.reps).find? (·.fn == g) = some w) : Stk :=
  ⟨{ S.p with main := g }, S.layouts, S.reps, S.env,
    { S.st with program := { S.st.program with entry := UInt32.ofNat w.start } }, run_withMain S.ok hw⟩

theorem Stk.withMain_cs (S : Stk) {g : FunId} {w : PlacedExport}
    (hw : (runWrappers S.p S.layouts S.reps).find? (·.fn == g) = some w) {cs : Checked}
    (hcs : cs.program = { S.st.program with entry := UInt32.ofNat w.start }) :
    (S.withMain g w hw).cs = cs := by
  obtain ⟨prog, valid⟩ := cs
  simp only at hcs
  subst hcs
  rfl

/-- **Stacking and the wrapper simulate Xl from any export** (05 §6.2's
conclusion at the stacked level): the stacked program started at `g`'s
wrapper, under the entry invariant for `g`, ends as `g`'s clocked Xl run
does. -/
theorem stacked_ends_at (S : Stk) {g : FunId} {w : PlacedExport}
    (hw : (runWrappers S.p S.layouts S.reps).find? (·.fn == g) = some w) {cs : Checked}
    (hcs : cs.program = { S.st.program with entry := UInt32.ofNat w.start })
    {core₀ : Core} {retAddr ctx : Word} {args : List Word} {mem : Memory}
    (inv : EntryInv { S.p with main := g } S.reps core₀ retAddr args mem ctx) (k : Nat)
    (hk : Xl.eval { S.p with main := g } S.env k args mem ctx ≠ .stuck) :
    ∃ n holes after, SafeSteps Runtime.rejecting cs n (fun _ => False) (Machine.initial cs core₀) holes after ∧
      Outcome core₀ retAddr k n holes after (Xl.eval { S.p with main := g } S.env k args mem ctx) := by
  have := stacked_ends (S.withMain g w hw) inv k hk
  rwa [Stk.withMain_cs S hw hcs] at this

/-- From any export: a `Nat` argument of 2^63 or more exits with status 3. -/
theorem wrapper_overflow_at (S : Stk) {g : FunId} {w : PlacedExport}
    (hw : (runWrappers S.p S.layouts S.reps).find? (·.fn == g) = some w) {cs : Checked}
    (hcs : cs.program = { S.st.program with entry := UInt32.ofNat w.start })
    {core₀ : Core} {retAddr ctx : Word} {mem : Memory}
    (base : EntryBase core₀ retAddr mem ctx) (hbig : ¬ArgsFit (mainReps { S.p with main := g } S.reps) core₀) :
    ∃ n holes after, SafeSteps Runtime.rejecting cs n (fun _ => False) (Machine.initial cs core₀) holes after ∧
      Exit core₀ retAddr 3 0 after ∧ ReadableData holes (after.core.readReg .rsp) 8 := by
  have := wrapper_overflow (S := S.withMain g w hw) base hbig
  rwa [Stk.withMain_cs S hw hcs] at this

end Compilatrix.Xv.Stacking.Proof
