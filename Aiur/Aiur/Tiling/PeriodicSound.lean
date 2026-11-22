import Aiur.Tiling.PeriodicMessages

/-!
# Soundness of a sharded v2 layout

`Sharded.sound`: shard traces that satisfy their shard circuits, with each
layout's fixed matrix, and whose lookups balance under multi-stark's
fingerprint against an external ledger of message shapes, give wide rows of
the logical system that satisfy their circuits and whose lookups balance
against the external parts' wide tuples. It is `System.keyed_core` for the
logical system read through `mainV`; the shard traces provide its two inputs:
the relations (`Sharded.logical`) and the message ledger
(`Sharded.msgLedger_total`).
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

theorem sum_range_blocks {M : Type} [AddCommMonoid M] : ∀ (lens : List Nat) (G : Nat → M),
    ((List.range lens.sum).map G).sum =
      ((List.range lens.length).map fun k => ((List.range (lens.getD k 0)).map fun f' =>
        G ((lens.take k).sum + f')).sum).sum
  | [], _ => by simp
  | n :: ns, G => by
      have ih := sum_range_blocks ns (fun f => G (n + f))
      rw [List.sum_cons, List.range_add, List.map_append, List.sum_append, List.map_map,
        show (G ∘ fun x => n + x) = (fun f => G (n + f)) from rfl, ih, List.length_cons,
        List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      simp only [List.getD_cons_zero, List.take_zero, List.sum_nil, Nat.zero_add, Function.comp_def,
        List.getD_cons_succ, List.take_succ_cons, List.sum_cons, Nat.add_assoc]

namespace Sharded

variable {S : Sharded F}

section Instance

variable (lens : S.Lengths) (rowsOk : S.RowsOk) (virt : S.VirtualOk) (valid : S.system.Valid) {H : Nat → Nat}
  {main : Nat → Nat → Nat → F} (trace : S.ShardTrace H main) {k f' i : Nat} (hk : k < S.shards.length)
  {T2 : Template2 F} (hT2 : (S.layout k).templates[f']? = some T2)
  (cap : i < ((S.layout k).shadow S.width).cap f')

include lens rowsOk virt valid trace hk hT2 cap in
/-- The rows of an instance carry its logical messages, each once. -/
theorem instance_total {bound : Nat} (sep : S.Separated bound) (logical : S.system.Logical (S.mainV main)) :
    ((List.range T2.rows.length).map fun r =>
        Finsupp.mapDomain S.proj2 (S.rowMsgs k (main k) (((S.layout k).shadow S.width).row f' i r))).sum =
      (T2.messages.map (System.msgEntry (S.system.slotValue (S.mainV main) (S.base k + f') i))).sum := by
  set val := S.system.slotValue (S.mainV main) (S.base k + f') i
  rw [sum_range_getElem T2.rows _ (fun row => (row.refs.map (entryOf T2 val)).sum)
    (fun r hr => row_total lens rowsOk virt valid trace hk hT2 cap sep logical hr)]
  rw [← System.sum_map_flatMap]
  obtain ⟨_, phys⟩ := rowsOk k hk T2 (List.mem_of_getElem? hT2)
  simp only [Template2.checkPhysical, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at phys
  obtain ⟨⟨⟨_, nodup⟩, len⟩, lt⟩ := phys
  have perm : T2.refs.Perm (List.range T2.messages.length) :=
    (List.subperm_of_subset nodup (fun x hx => List.mem_range.mpr (by simpa using lt x hx))).perm_of_length_le
      (by simp [len])
  change ((T2.refs).map (entryOf T2 val)).sum = _
  rw [(perm.map _).sum_eq]
  apply sum_range_getElem
  intro m hm
  simp [entryOf, List.getElem?_eq_getElem hm]

end Instance

theorem assign_unplaced {k p : Nat} {main : Nat → Nat → F}
    (h : ((S.layout k).shadow S.width).places[p]? = none) (c : Nat) :
    S.assign k main p (S.width + c) = 0 := by
  simp [assign, S.fixedAt_unplaced h]

theorem rowMsgs_unplaced {k p : Nat} {main : Nat → Nat → F}
    (h : ((S.layout k).shadow S.width).places[p]? = none) : S.rowMsgs k main p = 0 := by
  unfold rowMsgs
  rw [rowMessage_entry]
  simp only [assign_unplaced h, zero_mul, add_zero, Finsupp.single_zero, zero_add]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
  rw [laneMessage_entry]
  simp [assign_unplaced h]

/-- A shard's messages are its instances' logical messages. -/
theorem shard_total (lens : S.Lengths) (rowsOk : S.RowsOk) (virt : S.VirtualOk) (valid : S.system.Valid) {H : Nat → Nat}
    {main : Nat → Nat → Nat → F} (trace : S.ShardTrace H main) {k : Nat} (hk : k < S.shards.length)
    {bound : Nat} (sep : S.Separated bound) (logical : S.system.Logical (S.mainV main)) :
    Finsupp.mapDomain S.proj2 (S.msgLedger k (H k) (main k)) =
      ((List.range (S.layout k).templates.length).map fun f' =>
        ((List.range (((S.layout k).shadow S.width).cap f')).map fun i =>
          (((S.layout k).templates[f']?).map fun T2 =>
            (T2.messages.map (System.msgEntry (S.system.slotValue (S.mainV main) (S.base k + f') i))).sum).getD
              0).sum).sum := by
  let sh := (S.layout k).shadow S.width
  let G : Nat → Ledger F := fun p => Finsupp.mapDomain S.proj2 (S.rowMsgs k (main k) p)
  have step1 : Finsupp.mapDomain S.proj2 (S.msgLedger k (H k) (main k)) = ∑ p ∈ Finset.range (H k), G p := by
    simp only [msgLedger, Finsupp.mapDomain_finsetSum, G, rowMsgs]
  have step2 : ∑ p ∈ Finset.range (H k), G p = ∑ p ∈ Finset.range sh.places.length, G p := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr (trace.tall k hk))
    intro p _ out
    simp only [G, rowMsgs_unplaced (sh.places_getElem?_none (by simpa using out)), Finsupp.mapDomain_zero]
  have step3 : ∑ p ∈ Finset.range sh.places.length, G p =
      (sh.places.map fun x => G (sh.row x.1 x.2.1 x.2.2)).sum := by
    rw [System.finset_sum_range_list]
    apply sum_range_getElem
    intro p lt
    rw [sh.row_places lt]
  rw [step1, step2, step3]
  simp only [sh, System.places, System.enumerate, System.sum_map_flatMap, List.map_map]
  have lenT : ((S.layout k).shadow S.width).templates.length = (S.layout k).templates.length := by
    simp [Layout.shadow]
  rw [lenT]
  apply congrArg List.sum
  apply List.map_congr_left
  intro f' hf'
  have hf' := List.mem_range.mp hf'
  have hT2 := List.getElem?_eq_getElem hf'
  try simp only [System.sum_map_flatMap, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  have count : ((S.layout k).shadow S.width).rowCount f' = ((S.layout k).templates[f']).rows.length := by
    simp [System.rowCount, Layout.shadow, hT2, Template2.shadow]
  simp only [Function.comp_def, hT2, Option.map_some, Option.getD_some, count]
  exact instance_total lens rowsOk virt valid trace hk hT2 hi sep logical

/-- **The message ledger.** All shards' messages, decoded and cut to arities,
are the logical system's message rows read through `mainV`. -/
theorem msgLedger_total (lens : S.Lengths) (rowsOk : S.RowsOk) (virt : S.VirtualOk) (valid : S.system.Valid) {H : Nat → Nat}
    {main : Nat → Nat → Nat → F} (trace : S.ShardTrace H main)
    {bound : Nat} (sep : S.Separated bound) (logical : S.system.Logical (S.mainV main)) :
    Finsupp.mapDomain S.proj2 (∑ k ∈ Finset.range S.shards.length, S.msgLedger k (H k) (main k)) =
      S.system.msgSum (S.mainV main) := by
  rw [Finsupp.mapDomain_finsetSum, System.finset_sum_range_list]
  unfold System.msgSum
  rw [length_system_templates, sum_range_blocks]
  have lenL : S.lens.length = S.shards.length := List.length_map _
  rw [lenL]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  have hk := List.mem_range.mp hk
  rw [shard_total lens rowsOk virt valid trace hk sep logical]
  have getD : S.lens.getD k 0 = (S.layout k).templates.length := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [lenL]; exact hk), Option.getD_some]
    exact lens_getElem _
  rw [getD]
  apply congrArg List.sum
  apply List.map_congr_left
  intro f' hf'
  have hf' := List.mem_range.mp hf'
  rw [← base_eq, system_cap lens k hk hf', system_template k hk hf']
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  cases (S.layout k).templates[f']? with
  | none => rfl
  | some T2 => simp [logical_messages]


theorem check_parts (ok : S.check = true) :
    S.system.checkKeyed = true ∧ S.Lengths ∧ S.RowsOk ∧ (S.buses.map (·.2.1)).Nodup ∧
      ∀ e ∈ S.buses, e.2.1 % 4 = 1 ∨ e.2.1 % 4 = 2 := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨keyed, layouts⟩, _⟩, codes⟩, mods⟩, _⟩ := ok
  refine ⟨keyed, fun L hL => ⟨(layouts L hL).1.1, (layouts L hL).1.2⟩, fun k hk T hT => ?_, codes,
    fun e he => mods e he⟩
  rw [layout_eq hk] at hT
  exact (layouts _ (List.getElem_mem hk)).2 T hT

theorem check_virtual (ok : S.check = true) : S.VirtualOk := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at ok
  intro k hk T hT
  rw [layout_eq hk] at hT
  exact (ok.2 _ (List.getElem_mem hk) T hT).1

theorem check_bool (ok : S.check = true) : S.BoolOk := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at ok
  intro k hk T hT
  rw [layout_eq hk] at hT
  exact (ok.2 _ (List.getElem_mem hk) T hT).2

theorem copyLedger_zero {k H : Nat} {main : Nat → Nat → F} (valid : ((S.layout k).shadow S.width).CellsValid)
    (bal : ∀ n, n ≤ (S.shadow k).keys.length → ∀ v,
      S.copyLedger k H main [((copyKey (n + S.labelOffset k) : Nat) : F), v] = 0) :
    S.copyLedger k H main = 0 := by
  ext t
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_cases h : ∃ n v, n ≤ (S.shadow k).keys.length ∧ t = [((copyKey (n + S.labelOffset k) : Nat) : F), v]
  · obtain ⟨n, v, hn, rfl⟩ := h
    exact bal n hn v
  · rw [copyLedger_apply]
    apply Finset.sum_eq_zero; intro p _
    apply Finset.sum_eq_zero; intro j _
    rw [if_neg]
    intro e
    exact h ⟨_, _, labelNat_le valid p j, e.symm⟩

/-- **Soundness of a sharded v2 layout.** Shard traces that satisfy their
shard circuits with their layouts' fixed matrices, and whose lookups balance
under multi-stark's fingerprint against an external ledger of message shapes
that is the narrow encoding of external parts `X`, give wide rows of the
logical system that satisfy their circuits and whose lookups balance against
the wide tuples of `X`. Chunked external receivers must use channels without
in-system receivers and have distinct keys per channel. -/
theorem sound (ok : S.check = true) {bound : Nat} (small : SmallCast F bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (ids : S.system.instances ≤ bound)
    (X : List (Part F)) (count : (S.system.enumerate S.system.lookupCount).length + X.length < bound)
    {H : Nat → Nat} {main : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (rows : ∀ k < S.shards.length, ∀ p < H k, Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    {ext : Ledger F} (extShape : ∀ t, ext t ≠ 0 → S.MsgShape t)
    (extParts : Finsupp.mapDomain S.proj2 ext = (X.map Part.narrow).sum)
    (extFormed : ∀ x ∈ X, x.Formed S.system.width ∧ x.RowsIn S.system.roleOf S.system.arityAt)
    (extRecv : ∀ x ∈ X, x.recv = true → x.chunks ≠ [] → (x.tag, x.sub) ∉ S.system.receivers)
    (extUnique : ∀ j (hj : j < X.length) j' (hj' : j' < X.length), X[j].recv = true →
      X[j'].recv = true → X[j].chunks ≠ [] → X[j'].chunks ≠ [] → X[j].tag = X[j'].tag →
      X[j].sub = X[j'].sub → X[j].key = X[j'].key → j = j')
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + ext) = 0) :
    (∀ f (hf : f < S.system.circuits.length), ∀ i < S.system.cap f,
        S.system.circuits[f].Holds (S.system.wideRow (S.mainV main) f i)) ∧
      S.system.wideLedger (S.system.wideRow (S.mainV main)) + (X.map Part.wide).sum = 0 := by
  obtain ⟨keyed, lens, rowsOk, nodup, mods⟩ := check_parts ok
  have valid := S.system.valid_of_checkKeyed keyed
  have sep : S.Separated bound :=
    ⟨small, by simpa [system] using valid.width.1, fun e he => ⟨codesBound e he, mods e he⟩, nodup, labels⟩
  have exact := exact_of_trimmed sep rowsOk (fun t h => Or.inl (extShape t h)) balanced
  have extLen : ∀ t, ext t ≠ 0 → t.length ≠ 2 := by
    intro t h len
    obtain ⟨e, _, _, lt⟩ := extShape t h
    rw [len] at lt
    have := sep.width
    split at lt <;> omega
  have copyBal := fun k (hk : k < S.shards.length) n hn v => copy_balanced sep rowsOk extLen exact hk (n := n) hn v
  have keysLt : ∀ k < S.shards.length,
      copyKey (((S.layout k).shadow S.width).keys.length + S.labelOffset k) < bound := by
    intro k hk
    have := S.labelOffset_mono hk
    rw [shadow_eq] at this
    simp only [copyKey, labelTotal] at labels ⊢
    omega
  have trace : S.ShardTrace H main := ⟨tall, rows, fun k hk f i r place T hT j hj s cell =>
    S.consistent small (rowsOk.cells hk) (small.mono (shadowBound k hk)) (keysLt k hk) (tall k hk)
      (fun n hn v => copyBal k hk n hn v) place hT hj cell⟩
  have logical := S.logical lens rowsOk (check_virtual ok) (check_bool ok) valid trace
  refine System.keyed_core keyed small ids X count logical ?_ extFormed extRecv extUnique
  have copies : ∀ k ∈ Finset.range S.shards.length, S.copyLedger k (H k) (main k) = 0 := fun k hk =>
    copyLedger_zero (rowsOk.cells (Finset.mem_range.mp hk))
      (fun n hn v => copyBal k (Finset.mem_range.mp hk) n hn v)
  rw [ledger_split, Finset.sum_add_distrib, Finset.sum_eq_zero copies, add_zero] at exact
  rw [← msgLedger_total lens rowsOk (check_virtual ok) valid trace sep logical, ← extParts, ← Finsupp.mapDomain_add, exact,
    Finsupp.mapDomain_zero]

end Sharded

end Aiur.Tiling.Periodic
