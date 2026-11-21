import Ix.Cert.MultiStark.LogUpSoundness
import Aiur.Optimized.Depth.Grouped
import Aiur.MultiStarkSpec

/-! # Extracted Trace Rows → `Aiur.Optimized.Grouping.Plan.checkMemo` Bridge (Gap 5)

Connects the algebraic output of Multi-STARK soundness (per-row AIR polynomial
satisfaction + Goldilocks field-level LogUp balance + sharded `MEMSEG = 16`
interval uniqueness) directly to `Aiur.Optimized.Grouping.Plan.checkMemo` and
`Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks`.

Key insight: in Multi-STARK, each active row carries a field-element multiplicity
`m_i ∈ Fp` (from the prover's witness), whereas `Aiur.Optimized.Grouping.Plan.checkMemo`
requires *exact integer* balance in `Aiur.Circuit.Balance.accumulator`. Rather than
requiring the prover's raw field multiplicities to be small positive integers, we
exploit `Aiur.Circuit.Balance.weigh_balanced`:
1. Whenever a dynamic claim `c` is demanded `d > 0` times (`d < p`), field-level
   LogUp balance `∑_{r providing c} w(r) = (d : Fp)` implies via
   `exists_provider_of_field_balance` that at least one active row in the trace
   provides `c`.
2. We reweight the extracted rows via `attachWeights` (assigning `0` to padding rows
   and the `Balance.weigh` integer weights to active rows), preserving exact row
   count `wrows.length = rows.length`.
3. `Balance.weigh_balanced` immediately proves `plan.checkMemo rom root wrows = .ok ()`!
4. Combined with `memseg_balance_implies_unique` + `widthROM_valid_of_count_le_one`,
   this delivers both `rom.Valid` and `plan.checkMemo (Erasure.rawROM rom) root wrows = .ok ()`
   directly to `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks`.

Zero `sorry`, standard axioms only.
-/

namespace Ix.Cert.MultiStark

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Optimized.Grouping

section AttachWeights

variable {F : Type} [Field F] [DecidableEq F]

/-- Pair each physical row with an integer weight matching the output of `Balance.weigh`:
padding rows (`none`) receive weight `0`; active rows (`some _`) consume the next weight
from `weighted`. -/
def attachWeights :
    List (Row F) →
    List (Option (RuleClaims (Message F))) →
    List (RuleClaims (Message F) × Int) →
    List (WeightedRow F)
  | [], _, _ => []
  | r :: rs, none :: os, ws => ⟨r, 0⟩ :: attachWeights rs os ws
  | r :: rs, some _ :: os, w :: ws => ⟨r, w.2⟩ :: attachWeights rs os ws
  | r :: rs, _, _ => ⟨r, 0⟩ :: attachWeights rs [] []

omit [Field F] [DecidableEq F] in
/-- Reweighting preserves the exact number of physical rows (preserving `rows.length ≤ 2^39`). -/
theorem attachWeights_length :
    ∀ (rows : List (Row F)) (os : List (Option (RuleClaims (Message F))))
      (ws : List (RuleClaims (Message F) × Int)),
      (attachWeights rows os ws).length = rows.length
  | [], _, _ => rfl
  | _ :: rs, [], _ => by simp [attachWeights, attachWeights_length]
  | _ :: rs, none :: os, ws => by simp [attachWeights, attachWeights_length]
  | _ :: rs, some _ :: os, [] => by simp [attachWeights, attachWeights_length]
  | _ :: rs, some _ :: os, _ :: ws => by simp [attachWeights, attachWeights_length]

/-- Reweighted rows pass `plan.weigh rom` and produce weighted `Option` entries whose
`activeRules` equal the exact weighted rules `ws` (provided `ws.map Prod.fst = activeRules os`). -/
theorem mapM_weigh_attachWeights {source : System F} {id : String → Except String ℕ}
    (plan : Plan source id) (rom : WireROM F) :
    ∀ (rows : List (Row F)) (os : List (Option (RuleClaims (Message F))))
      (ws : List (RuleClaims (Message F) × Int)),
      rows.mapM (plan.inspectRow rom) = .ok os →
      ws.map Prod.fst = activeRules os →
      ∃ out : List (Option (RuleClaims (Message F) × Int)),
        (attachWeights rows os ws).mapM (plan.weigh rom) = .ok out ∧
        activeRules out = ws
  | [], os, ws, hmap, hws => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmap
    subst hmap
    cases ws with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons _ _ => simp [activeRules] at hws
  | r :: rs, os, ws, hmap, hws => by
    rw [List.mapM_cons] at hmap
    cases hinsp : plan.inspectRow rom r with
    | error e => simp [hinsp, bind, Except.bind] at hmap
    | ok opt =>
      simp only [hinsp, bind, Except.bind] at hmap
      cases hrest : rs.mapM (plan.inspectRow rom) with
      | error e => simp [hrest] at hmap
      | ok os' =>
        simp only [hrest, pure, Except.pure, Except.ok.injEq] at hmap
        subst hmap
        cases opt with
        | none =>
          simp only [activeRules_none] at hws
          obtain ⟨out', hout', hact'⟩ := mapM_weigh_attachWeights plan rom rs os' ws hrest hws
          refine ⟨none :: out', ?_, by simp [hact']⟩
          simp only [attachWeights, List.mapM_cons, Plan.weigh, hinsp, ↓reduceIte,
            bind, Except.bind, hout', pure, Except.pure]
        | some claims =>
          simp only [activeRules_some] at hws
          cases ws with
          | nil => simp at hws
          | cons w ws' =>
            simp only [List.map_cons, List.cons.injEq] at hws
            obtain ⟨hw1, hws'⟩ := hws
            obtain ⟨out', hout', hact'⟩ := mapM_weigh_attachWeights plan rom rs os' ws' hrest hws'
            refine ⟨some (claims, w.2) :: out', ?_, ?_⟩
            · simp only [attachWeights, List.mapM_cons, Plan.weigh, hinsp,
                bind, Except.bind, hout', pure, Except.pure]
            · simp only [activeRules_some, hact', List.cons.injEq, and_true]
              cases w with
              | mk fst snd =>
                dsimp only at hw1
                rw [hw1]

end AttachWeights

section PlanCheckMemo

/-- **Core Plan Bridge (`Plan.checkMemo` from per-row AIR + field-level LogUp balance):**

Given extracted physical rows `rows : List (Aiur.Circuit.Row Fp)` over a grouping plan
`plan : Plan source id`:
1. `source.checkContext rom root = .ok ()` (the root claim's context/arguments are well-formed),
2. Every row satisfies `plan.inspectRow rom` (`rows.mapM (plan.inspectRow rom) = .ok inspected`),
3. Every dynamic claim `c ∈ Balance.required (fun m => decide (source.MapClaim m)) root rules`
   balances in Goldilocks `Fp` against some witness weight assignment `provWeight` on active rows,
   with total demand `demands.length < Goldilocks.order` (automatically satisfied when
   `rows.length ≤ 2^39` and max lookups per row `< 2^20`).

Then there exist integer-weighted rows `wrows` of the exact same length `rows.length`
such that `plan.checkMemo rom root wrows = .ok ()`! -/
theorem plan_checkMemo_of_field_balance {source : System Fp} {id : String → Except String ℕ}
    (plan : Plan source id) (rom : WireROM Fp) (root : Message Fp)
    (rows : List (Row Fp)) (inspected : List (Option (RuleClaims (Message Fp))))
    (hctx : source.checkContext rom root = .ok ())
    (hinsp : rows.mapM (plan.inspectRow rom) = .ok inspected)
    (hdem_lt : (Balance.required (fun c => decide (source.MapClaim c)) root
      (activeRules inspected)).length < CertiFri.P3.Goldilocks.order)
    (provWeight : RuleClaims (Message Fp) → Fp)
    (hbal : ∀ claim ∈ Balance.required (fun c => decide (source.MapClaim c)) root
        (activeRules inspected),
      (((activeRules inspected).filter fun r => decide (r.1 = claim)).map provWeight).sum =
        ((((Balance.required (fun c => decide (source.MapClaim c)) root
          (activeRules inspected)).countP fun x => decide (x = claim)) : ℕ) : Fp)) :
    ∃ wrows : List (WeightedRow Fp),
      wrows.length = rows.length ∧
      plan.checkMemo rom root wrows = .ok () := by
  set rules := activeRules inspected
  set demands := Balance.required (fun c => decide (source.MapClaim c)) root rules
  set ws := Balance.weigh demands rules
  -- Step 1: Field-level balance implies every demanded claim has an active provider row
  have hcov : ∀ claim ∈ demands, ∃ rule ∈ rules, rule.1 = claim := by
    intro claim hmem
    have hd_pos : 0 < demands.countP (fun x => decide (x = claim)) :=
      List.countP_pos_iff.mpr ⟨claim, hmem, decide_eq_true rfl⟩
    have hd_le : demands.countP (fun x => decide (x = claim)) ≤ demands.length :=
      List.countP_le_length
    have hne := exists_provider_of_field_balance
      (rules.filter fun r => decide (r.1 = claim)) provWeight hd_pos
      (lt_of_le_of_lt hd_le hdem_lt) (hbal claim hmem)
    obtain ⟨rule, hrmem⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨hr_in, hr_eq⟩ := List.mem_filter.mp hrmem
    exact ⟨rule, hr_in, of_decide_eq_true hr_eq⟩
  -- Step 2: Attach integer weights preserving `rows.length` and passing `plan.weigh`
  obtain ⟨out, hout, hact⟩ :=
    mapM_weigh_attachWeights plan rom rows inspected ws hinsp (Balance.weigh_rules demands rules)
  refine ⟨attachWeights rows inspected ws, attachWeights_length rows inspected ws, ?_⟩
  -- Step 3: `Balance.weigh_balanced` discharges `Plan.checkMemo`
  unfold Plan.checkMemo
  simp only [hctx, hout, hact]
  rw [Balance.weigh_balanced hcov]
  rfl

/-- **Full Extracted-Trace → Prepared Aiur Evaluation Bridge (Goldilocks):**

Combines:
- Sharded `MEMSEG = 16` interval uniqueness (`memseg_balance_implies_unique` → `rom.Valid`),
- Field-level LogUp balance → integer `Plan.checkMemo` (`plan_checkMemo_of_field_balance`), and
- `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks`!

Any extracted trace `(rom, rows)` whose sharded `MEMSEG` channel balances against sorted
disjoint preamble intervals and whose active rows satisfy `plan.inspectRow` and field-level
LogUp balance for `root` (with `rows.length ≤ 2^39`) directly yields a sound evaluation
`prepared.EvalFn external args value heap` with heap representation `Represents`. -/
theorem prepared_eval_of_extracted_trace
    {program : Aiur.Modules.Program Fp}
    (prepared : Aiur.Modules.Prepared program)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Depth.Certified cfg physical.system) (bits : cfg.bits ≤ 24)
    {id : String → Except String ℕ}
    (plan : Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : Aiur.WidthROM Fp}
    (ivlsOf : ℕ → List (ℕ × ℕ))
    (hdisj : ∀ w, DisjointIntervals (ivlsOf w))
    (hrom_lt : ∀ w,
      (∑ x : Fp, (rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length) + 1 <
        CertiFri.P3.Goldilocks.order)
    (hmemseg : ∀ (w : ℕ) (x : Fp),
      (((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length : Fp) -
        ((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x - 1)).length : Fp)) +
        memsegBoundary (ivlsOf w) x = 0)
    {args : List (Aiur.SourceValue Fp)} {result : Aiur.Value Fp}
    {wires : List (Aiur.WireValue Fp)} {output : Aiur.WireValue Fp}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Message Fp}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (rows : List (Row Fp)) (hrows_len : rows.length ≤ 2 ^ 39)
    (inspected : List (Option (RuleClaims (Message Fp))))
    (hctx : (Aiur.Optimized.Depth.system cfg physical.system).checkContext
      (Erasure.rawROM rom) root = .ok ())
    (hinsp : rows.mapM (plan.inspectRow (Erasure.rawROM rom)) = .ok inspected)
    (hdem_lt : (Balance.required
        (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
        root (activeRules inspected)).length < CertiFri.P3.Goldilocks.order)
    (provWeight : RuleClaims (Message Fp) → Fp)
    (hbal : ∀ claim ∈ Balance.required
          (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
          root (activeRules inspected),
        (((activeRules inspected).filter fun r => decide (r.1 = claim)).map provWeight).sum =
          ((((Balance.required
            (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
            root (activeRules inspected)).countP fun x => decide (x = claim)) : ℕ) : Fp))
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Aiur.Represents ((Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result := by
  have hvalid : rom.Valid := widthROM_valid_of_count_le_one rom fun w x =>
    (memseg_balance_implies_unique (hdisj w) (hrom_lt w) (hmemseg w) x).2
  obtain ⟨wrows, hlen, hchecked⟩ := plan_checkMemo_of_field_balance plan (Erasure.rawROM rom) root
    rows inspected hctx hinsp hdem_lt provWeight hbal
  exact prepared.depth_grouped_activated_heap_sound_goldilocks compiled physical certified bits plan
    activated selected hvalid signed rooted outside (hlen ▸ hrows_len) hchecked arguments decoded

end PlanCheckMemo

section VectorizedRomBridge

open Aiur.MultiStarkSpec

/-- Every extracted entry from a `K`-lane vectorized `<ROM:w>` trace has payload length `w`. -/
theorem vecTraceEntries_payload_length {F : Type} [Field F] [DecidableEq F]
    (w K : ℕ) (rows : List (ℕ → F)) {e : F × List F}
    (he : e ∈ vecTraceEntries w K rows) : e.2.length = w := by
  unfold vecTraceEntries at he
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp he
  unfold vecRowEntries at hr
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hr
  simp [vecPayload]

/-- **Vectorized `K`-lane ROM → scalar `hmemseg` bridge (`C6`):**
if the width-`w` entries of `rom : Aiur.WidthROM Fp` are extracted from valid
`K`-lane vectorized ROM rows (`1 < K`) whose `MEMSEG` row deltas balance against
sorted disjoint intervals `ivls`, then the exact scalar `hmemseg` balance required by
`memseg_balance_implies_unique` and `prepared_eval_of_extracted_trace` holds. -/
theorem vectorized_rom_hmemseg_of_valid
    (rom : Aiur.WidthROM Fp) (w K : ℕ) (hK : 1 < K)
    (rows : List (ℕ → Fp)) (hrows : ∀ r ∈ rows, KLaneRomRowValid w K r)
    (hslice : rom.entries.filter (fun e => decide (e.2.length = w)) = vecTraceEntries w K rows)
    (ivls : List (ℕ × ℕ))
    (hbal : ∀ x : Fp, (rows.map fun r => vecRowMemsegDelta w K r x).sum +
        memsegBoundary ivls x = 0) :
    ∀ x : Fp,
      (((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length : Fp) -
        ((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x - 1)).length : Fp)) +
        memsegBoundary ivls x = 0 := by
  intro x
  have hfilt : ∀ y : Fp,
      (rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = y)) =
        (vecTraceEntries w K rows).filter (fun e => decide (e.1 = y)) := by
    intro y
    rw [← hslice, List.filter_filter]
    congr 1
    funext e
    by_cases hw : e.2.length = w <;> by_cases ha : e.1 = y <;> simp [hw, ha]
  rw [hfilt x, hfilt (x - 1), ← vecTrace_memseg_delta_eq_scalar hK hrows x]
  exact hbal x

/-- **Vectorized `K`-lane ROM `WidthROM.Valid` bridge (`C6`):**
any `WidthROM Fp` whose every width bucket either balances as a scalar ROM or is
extracted from valid `K`-lane vectorized ROM rows (`1 < K`) balancing against sorted
disjoint `MEMSEG` intervals is guaranteed `rom.Valid` (uniquely addressed per width). -/
theorem vectorized_rom_widthROM_valid
    (rom : Aiur.WidthROM Fp)
    (ivlsOf : ℕ → List (ℕ × ℕ))
    (hdisj : ∀ w, DisjointIntervals (ivlsOf w))
    (hrom_lt : ∀ w,
      (∑ x : Fp, (rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length) + 1 <
        CertiFri.P3.Goldilocks.order)
    (hvec : ∀ w,
      (∀ x : Fp,
        (((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length : Fp) -
          ((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x - 1)).length : Fp)) +
          memsegBoundary (ivlsOf w) x = 0) ∨
      ∃ (K : ℕ) (rows : List (ℕ → Fp)),
        1 < K ∧
        (∀ r ∈ rows, KLaneRomRowValid w K r) ∧
        rom.entries.filter (fun e => decide (e.2.length = w)) = vecTraceEntries w K rows ∧
        ∀ x : Fp, (rows.map fun r => vecRowMemsegDelta w K r x).sum +
          memsegBoundary (ivlsOf w) x = 0) :
    rom.Valid := by
  apply widthROM_valid_of_count_le_one rom
  intro w x
  have hmemseg : ∀ y : Fp,
      (((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = y)).length : Fp) -
        ((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = y - 1)).length : Fp)) +
        memsegBoundary (ivlsOf w) y = 0 := by
    rcases hvec w with hscalar | ⟨K, rows, hK, hrows, hslice, hbal⟩
    · exact hscalar
    · exact vectorized_rom_hmemseg_of_valid rom w K hK rows hrows hslice (ivlsOf w) hbal
  exact (memseg_balance_implies_unique (hdisj w) (hrom_lt w) hmemseg x).2

end VectorizedRomBridge

end Ix.Cert.MultiStark
