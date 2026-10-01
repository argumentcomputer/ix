import Compilatrix.Backend.Proof.Ends
import Compilatrix.Backend.Proof.Retarget
import Compilatrix.Xv.Stacking.Proof.Retarget
import Compilatrix.X86.Layout.Proof.Retarget
import Compilatrix.X86.ObjectCallSafe

/-!
# Every export of an emitted object

`compile_sim_main` runs `main`'s export. The object `Backend.emit` writes
exports every SysV export function's wrapper under its symbol (`main`'s as
the ELF entry symbol, the others in the symbol table). This module runs any
of them by its symbol (`ObjectEval.call`, the linker's lookup), against the
Lir program started at that function (`{ p with main := g }`):

- `emit_exports`: an emitted object's further exports are the stacked
  exports other than the entry symbol, at their laid-out blocks;
- `emitted_call_ends`: for an export function `g` of symbol `sym`, when the
  stacked exports' symbols are distinct, the laid-out program started at
  `g`'s wrapper is encoded in the object (`Stream.Valid`), the object's
  text is it, `sym` names its first block, and its runs end as `g`'s clocked
  Xl runs do (05 §6.2, under the entry invariant for `g`) or, for a `Nat`
  argument of 2^63 or more, exit with status 3;
- `call_sim_export`: Lir started at `g` to the object's call of `sym`, with
  the clock map `k ↦ (B + 1)(k + 1)`;
- `call_overflow_export`: a `Nat` argument of 2^63 or more fails with
  `natOverflow`.

Distinct symbols are needed: `Backend.finish` lists the further exports
without the entry symbol, so an export sharing `main`'s symbol would be
dropped and its symbol would run `main`.
-/

namespace Compilatrix.Backend

open Compilatrix.Xv
open Compilatrix.Lir (Word)
open Compilatrix.X86.ObjectEval (Ends Lifted call call_mono)
open Compilatrix.X86.Stream (SafeSteps)

/-- An emitted object's further exports are the stacked exports other
than the entry symbol, at their laid-out blocks. -/
theorem emit_exports {l : LProgram} {cfg : Config} {art : Artifact} (h : emit l cfg = .ok art) :
    ∃ input pos, Emitted l cfg art input ∧
      X86.Layout.run (X86.Layout.tunnel art.stacked.program) art.stacked.shape
        (cfg.order.getD (X86.Layout.Order.produce (X86.Layout.tunnel art.stacked.program) art.stacked.shape)) =
          .ok (art.program, pos) ∧
      input.exports = (art.stacked.exports.map fun e => (e.symbol, UInt32.ofNat ((pos.get? e.block).getD e.block))).filter
        (·.1 != art.exportName) := by
  unfold emit lay finish at h
  simp only [bind, Except.bind, Except.mapError] at h
  cases hs : Stacking.run l (cfg.layouts.getD (Stacking.produce l)) cfg.reps cfg.env with
  | error e => simp [hs] at h
  | ok stacked =>
    simp only [hs] at h
    cases hl : X86.Layout.run (X86.Layout.tunnel stacked.program) stacked.shape
        (cfg.order.getD (X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape)) with
    | error e => simp [hl] at h
    | ok pp =>
      obtain ⟨program, pos⟩ := pp
      simp only [hl, pure, Except.pure] at h
      cases hc : program.checkK with
      | error e => simp [hc] at h
      | ok checked =>
        simp only [hc] at h
        cases he : X86.Stream.encodeK checked with
        | error e => simp [he] at h
        | ok stream =>
          simp only [he] at h
          cases hf : stacked.exports.find? (·.fn == l.main) with
          | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
          | some entry =>
            simp only [hf] at h
            split at h
            · cases h
            · rename_i object hw
              cases h
              have hprog : checked.program = program := by
                unfold X86.Program.checkK at hc
                split at hc
                · cases hc; rfl
                · split at hc <;> cases hc
              have hmain := List.find?_some hf
              have hmem := List.mem_of_find?_eq_some hf
              split at hw
              · cases hw
              · rename_i object hcert
                cases hw
                exact ⟨_, pos, ⟨hs, ⟨pos, hl⟩, hprog, stream.valid, object.valid, by simp [hprog], rfl, rfl,
                  ⟨entry, hmem, by simpa using hmain, rfl⟩⟩, hl, rfl⟩

/-- Distinct images identify members. -/
theorem nodup_map_inj {α β : Type} {h : α → β} :
    ∀ {xs : List α}, (xs.map h).Nodup → ∀ {a b : α}, a ∈ xs → b ∈ xs → h a = h b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, hn, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha, hb]
    · subst ha; exact absurd (by rw [hab]; exact List.mem_map_of_mem hb) hn.1
    · subst hb; exact absurd (by rw [← hab]; exact List.mem_map_of_mem ha) hn.1
    · exact nodup_map_inj hn.2 ha hb hab

/-- The stacked exports' symbols are distinct: what the further exports'
lookup needs (`Backend.finish` drops a further export named like the entry
symbol). -/
def SymbolsApart (art : Artifact) : Prop := (art.stacked.exports.map (·.symbol)).Nodup

/-- **An emitted object's export of `g`**, as a checked typed program: the
laid-out program started at `g`'s wrapper, encoded in the object, with
`sym` at its first block; its runs end as `g`'s clocked Xl runs do under
the entry invariant for `g`, and exit with status 3 for a `Nat` argument
of 2^63 or more. -/
theorem emitted_call_ends {l : LProgram} {cfg : Config} {art : Artifact} (he : emit l cfg = .ok art)
    (hapart : SymbolsApart art) {g : Lir.FunId} {f : Func Loc} {sym : String} (hf : l.funcs[g]? = some f)
    (hconv : f.conv = .sysvExport sym) :
    ∃ cq : X86.Checked, X86.Stream.Valid cq.program art.encoded ∧
      X86.ELFRead.text? art.object = some art.encoded.text ∧
      X86.ELF.symbol? art.object sym = art.encoded.blockOffsets[cq.program.entry.toNat]? ∧
      (∀ (core₀ : X86.Core) (retAddr ctx : Word) (args : List Word) (mem : X86.Memory),
        Stacking.Proof.EntryInv { l with main := g } cfg.reps core₀ retAddr args mem ctx →
        ∀ k, Xl.eval { l with main := g } cfg.env k args mem ctx ≠ .stuck →
          Ends cq core₀ retAddr StackFinal (k / (art.stacked.program.blocks.size + 1))
            (Xl.eval { l with main := g } cfg.env k args mem ctx)) ∧
      (∀ (core₀ : X86.Core) (retAddr ctx : Word) (mem : X86.Memory),
        Stacking.Proof.EntryBase core₀ retAddr mem ctx →
        ¬Stacking.Proof.ArgsFit (Stacking.Proof.mainReps { l with main := g } cfg.reps) core₀ →
        ∃ n holes after, SafeSteps X86.Runtime.rejecting cq n (fun _ => False) (X86.Machine.initial cq core₀) holes after ∧
          X86.Exit core₀ retAddr 3 0 after) := by
  obtain ⟨input, pos, em, hlay, hexp⟩ := emit_exports he
  let S : Stacking.Proof.Stk :=
    ⟨l, cfg.layouts.getD (Stacking.produce l), cfg.reps, cfg.env, art.stacked, em.stacked⟩
  obtain ⟨w, hw⟩ := Stacking.Proof.wrapper_of_export em.stacked hf hconv
  have hwmem := List.mem_of_find?_eq_some hw
  have hwg : w.fn = g := by simpa using List.find?_some hw
  obtain ⟨f', -, hf', hconv', -, -, -⟩ := Stacking.Proof.export_at em.stacked hwmem
  rw [hwg, hf] at hf'
  cases hf'
  have hsym : w.symbol = sym := by rw [hconv] at hconv'; cases hconv'; rfl
  have hb := Stacking.Proof.export_start em.stacked hwmem
  obtain ⟨hexports, hroots⟩ := Stacking.Proof.run_exports em.stacked
  have hroot : w.start ∈ art.stacked.shape.roots := by
    rw [hroots]; exact List.mem_map_of_mem hwmem
  -- the layout's setup, for the new number of `g`'s wrapper
  obtain ⟨setup, sound⟩ := X86.Layout.Proof.setup_of_run (X86.Layout.Proof.tunnelChecked S.cs).valid hlay
    (em.checked ▸ art.checked.valid)
  have hplaced := X86.Layout.Proof.root_placed sound hroot
  have hsmall : (X86.Layout.tunnel art.stacked.program).blocks.size < 2 ^ 32 :=
    ((X86.Layout.Proof.wellFormed_iff _).1 (X86.Layout.Proof.tunnelChecked S.cs).valid).2.1
  have hbsz : w.start < (X86.Layout.tunnel art.stacked.program).blocks.size := sound.inRange _ hplaced
  have hbn : (UInt32.ofNat w.start).toNat = w.start := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  let order := (cfg.order.getD (X86.Layout.Order.produce (X86.Layout.tunnel art.stacked.program) art.stacked.shape))
  let b' := X86.Layout.Proof.renum order.flatten (UInt32.ofNat w.start)
  have hb' : b'.toNat < art.checked.program.blocks.size := by
    have := setup.hasBlock (t := UInt32.ofNat w.start) (by rw [hbn]; exact hplaced)
    rw [em.checked]
    exact X86.Layout.Proof.hasBlock_iff.1 this
  let cq := art.checked.withEntry b' hb'
  have hbs : (UInt32.ofNat w.start).toNat < S.cs.program.blocks.size := by
    rw [hbn]; exact hb
  let cs' := S.cs.withEntry (UInt32.ofNat w.start) hbs
  refine ⟨cq, em.encoded ▸ em.stream.withEntry b', em.encoded ▸ em.object.text, ?_, ?_, ?_⟩
  · -- the symbol names `g`'s wrapper
    rw [← em.encoded]
    by_cases hname : sym = art.exportName
    · -- the entry symbol: `g` is `main`
      obtain ⟨e, he, hemain, hesym⟩ := em.main
      have hwe : (⟨w.fn, w.symbol, w.start⟩ : Stacking.Export) ∈ art.stacked.exports := by
        rw [hexports]; exact List.mem_map_of_mem hwmem
      have heq : e = ⟨w.fn, w.symbol, w.start⟩ :=
        nodup_map_inj hapart he hwe (by rw [hesym, hsym, hname])
      have hgm : g = l.main := by rw [← hwg, ← hemain, heq]
      obtain ⟨-, -, -, -, -, wc, fc, main, -, -, hmain, hprog, -⟩ := Stacking.Proof.run_ok em.stacked
      have hmw : main = w := by
        rw [hgm] at hw
        exact Option.some.inj (hmain.symm.trans hw)
      have hentry : cq.program.entry = art.checked.program.entry := by
        show b' = _
        rw [em.checked, (X86.Layout.Proof.run_eq hlay).2]
        show _ = X86.Layout.Proof.renum order.flatten (X86.Layout.tunnel art.stacked.program).entry
        rw [show (X86.Layout.tunnel art.stacked.program).entry = art.stacked.program.entry from rfl, hprog, hmw]
      rw [hentry, ← em.entry, hname, ← em.name]
      exact em.object.symbol_entry
    · -- a further export
      have hmem : (sym, b') ∈ input.exports := by
        rw [hexp, List.mem_filter]
        refine ⟨?_, by simpa using hname⟩
        rw [hexports, List.map_map, List.mem_map]
        refine ⟨w, hwmem, ?_⟩
        simp only [Function.comp, hsym, Prod.mk.injEq, true_and]
        have hpos : pos = X86.Layout.Proof.posOf order.flatten := by
          have := hlay
          unfold X86.Layout.run at this
          split at this
          · simp only [pure, Except.pure, Except.ok.injEq, X86.Layout.Proof.linearize_eq, Prod.mk.injEq] at this
            exact this.2.symm
          · cases this
        show _ = UInt32.ofNat (((X86.Layout.Proof.posOf order.flatten).get? (UInt32.ofNat w.start).toNat).getD
          (UInt32.ofNat w.start).toNat)
        rw [hbn, hpos]
      exact em.object.exported hmem
  · -- runs end as Xl's
    intro core₀ retAddr ctx args mem inv k hk
    obtain ⟨n, holes, after, steps, out⟩ :=
      Stacking.Proof.stacked_ends_at S hw (cs := cs') rfl inv k hk
    obtain ⟨n', mt, m₁, stepsQ, -, hnle, ⟨kk, relT⟩, relL⟩ :=
      X86.Layout.Proof.transport_at (cs := S.cs) (cq := art.checked) hlay em.checked hroot
        (cs' := cs') (cq' := cq) rfl (by show { art.checked.program with entry := b' } = _; rw [em.checked]) steps
    obtain ⟨hrun, -, hexit, -⟩ := X86.Layout.Proof.transport_end relT relL
    have hB : S.cs.program.blocks.size = art.stacked.program.blocks.size := rfl
    rw [hB] at hnle
    refine ⟨n', holes, m₁, stepsQ, ?_⟩
    rcases out with ⟨val, ex, hd⟩ | out
    · exact .inl ⟨val, hexit ex hd⟩
    · right
      revert out
      cases Xl.eval { l with main := g } cfg.env k args mem ctx with
      | ok v =>
        rintro ⟨val, ex, hfin, hd⟩
        refine ⟨val, hexit ex hd, after.core.memory, hfin, ?_⟩
        have hm := relL.memory fun fl h => by rw [relT.status, ex.halted] at h; cases h
        rwa [relT.core] at hm
      | timeout =>
        rintro ⟨hkn, hr⟩
        exact ⟨Nat.div_le_of_le_mul (by omega), hrun hr⟩
      | resource failure =>
        rintro ⟨val, ex, hd⟩
        exact ⟨val, by rw [← statusOf_code]; exact hexit ex hd⟩
      | trap =>
        rintro ⟨val, ex, hd⟩
        exact ⟨val, hexit ex hd⟩
      | stuck => intro; trivial
  · -- a `Nat` argument out of range
    intro core₀ retAddr ctx mem base hbig
    obtain ⟨n, holes, after, steps, ex, hd⟩ := Stacking.Proof.wrapper_overflow_at S hw (cs := cs') rfl base hbig
    obtain ⟨n', mt, m₁, stepsQ, -, -, ⟨kk, relT⟩, relL⟩ :=
      X86.Layout.Proof.transport_at (cs := S.cs) (cq := art.checked) hlay em.checked hroot
        (cs' := cs') (cq' := cq) rfl (by show { art.checked.program with entry := b' } = _; rw [em.checked]) steps
    obtain ⟨-, -, hexit, -⟩ := X86.Layout.Proof.transport_end relT relL
    exact ⟨n', holes, m₁, stepsQ, hexit ex hd⟩

variable {p : Lir.Program} {q : VProgram} {outs : List Alloc.Output} {l : LProgram} {cfg : Config}
  {art : Artifact} {g : Lir.FunId} {f : Func Loc} {sym : String}

/-- **Lir to the object for any export**: on the recheck path's selection
and the validated allocation, the object's call of the symbol of `g`
simulates the Lir program started at `g`, from any entry the invariant for
`g` describes, with the clock map `k ↦ (B + 1)(k + 1)`. -/
theorem call_sim_export (hs : Select.select p = .ok q) (hv : Validate.run cfg.env q outs = .ok l)
    (he : emit l cfg = .ok art) (hapart : SymbolsApart art) (hf : l.funcs[g]? = some f)
    (hconv : f.conv = .sysvExport sym) (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core)
    (base retAddr : Word) (flags : X86.ByteEval.Flags)
    (inv : Stacking.Proof.EntryInv { l with main := g } cfg.reps core₀ retAddr args mem ctx)
    (hout : art.encoded.text.size ≤ (retAddr - base).toNat) :
    Sem.Sim (Lifted StackFinal) (fun k => (art.stacked.program.blocks.size + 1) * (k + 1))
      (fun k => Lir.eval { p with main := g } k args mem ctx) (call art.object sym base core₀ flags) := by
  obtain ⟨cq, stream, htext, hsym, hends, -⟩ := emitted_call_ends he hapart hf hconv
  have hcall := X86.ObjectEval.call_sim_of_ends stream htext hsym (flags := flags) inv.slot hout
    (b := (· / (art.stacked.program.blocks.size + 1)))
    (fun k => by rw [Nat.mul_div_cancel_left _ (by omega)]; exact Nat.le_refl _) (hends core₀ retAddr ctx args mem inv)
  have hc := (xl_sim_select (select_withMain hs g) (validate_withMain hv g) args mem ctx).comp
    (call_mono art.object sym base core₀ flags) hcall
  exact hc.mono fun _ _ h => by obtain ⟨_, h₁, h₂⟩ := h; exact h₁ ▸ h₂

/-- **A `Nat` argument out of range**: the object's call of the symbol of
`g` fails with `natOverflow` (the wrapper's status 3). -/
theorem call_overflow_export (he : emit l cfg = .ok art) (hapart : SymbolsApart art) (hf : l.funcs[g]? = some f)
    (hconv : f.conv = .sysvExport sym) {core₀ : X86.Core} {retAddr ctx : Word} {mem : X86.Memory} {base : Word}
    (flags : X86.ByteEval.Flags) (hbase : Stacking.Proof.EntryBase core₀ retAddr mem ctx)
    (hbig : ¬Stacking.Proof.ArgsFit (Stacking.Proof.mainReps { l with main := g } cfg.reps) core₀)
    (hout : art.encoded.text.size ≤ (retAddr - base).toNat) :
    ∃ k, call art.object sym base core₀ flags k = .resource .natOverflow := by
  obtain ⟨cq, stream, htext, hsym, -, hover⟩ := emitted_call_ends he hapart hf hconv
  obtain ⟨n, holes, after, steps, ex⟩ := hover core₀ retAddr ctx mem hbase hbig
  obtain ⟨k, m, hk, -⟩ := X86.ObjectEval.call_exit stream htext hsym (flags := flags) hbase.slot hout steps ex
  exact ⟨k, by rw [hk]; rfl⟩

end Compilatrix.Backend
