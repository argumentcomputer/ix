import Aiur.Tiling.PeriodicLogical

/-!
# The message ledger of a sharded layout

A shard's message tuple `[code, x1, …]` decodes through the bus table to
`[tag, sub, x1, …]` (`unpack`); cut to the channel's arity (`proj2`) it is the
logical system's message entry of the placed message (`lane_entry`,
`row_entry`). On a key row the second coordinate `x1 + rkey + idOffset` is
the logical invocation id, because `x1 = 0` (`Placed.key_cell`).
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

/-- The channel of a bus code. -/
def decode (buses : Buses F) (c : F) : Option (F × F) :=
  (buses.find? fun e => ((e.2.1 : Nat) : F) == c).map (·.1)

/-- `[code, rest…] ↦ [tag, sub, rest…]`. -/
def unpack (buses : Buses F) : List F → List F
  | c :: rest =>
      match decode buses c with
      | some (tag, sub) => tag :: sub :: rest
      | none => c :: rest
  | [] => []

theorem logical_messages (T : Template2 F) : T.logical.messages = T.messages := by
  simp only [Template.messages, Template2.logical, List.filterMap_append]
  rw [List.filterMap_eq_nil_iff.mpr ?g1, List.filterMap_eq_nil_iff.mpr ?g2,
    List.filterMap_eq_nil_iff.mpr ?g3, List.filterMap_eq_nil_iff.mpr ?g4, List.nil_append, List.nil_append,
    List.nil_append, List.nil_append]
  · simp only [Template2.messageRows, List.filterMap_map]
    conv_rhs => rw [← List.filterMap_some (l := T.messages)]
    apply List.filterMap_congr
    intro x _
    rfl
  case g1 =>
    intro row hrow
    obtain ⟨r2, _, hr⟩ := List.mem_flatMap.mp hrow
    cases r2 with
    | gate ls spans =>
        simp only [Row2.logical, List.mem_map] at hr
        obtain ⟨sp, _, rfl⟩ := hr
        rfl
    | message => simp [Row2.logical] at hr
  case g2 =>
    intro row hrow
    simp only [Template2.pins, List.mem_filterMap] at hrow
    obtain ⟨⟨d, s⟩, _, hrow⟩ := hrow
    split at hrow
    · simp only [Option.some.injEq] at hrow; subst hrow; rfl
    · simp at hrow
  case g3 =>
    intro row hrow
    simp only [Template2.virtualRows, List.mem_map] at hrow
    obtain ⟨_, _, rfl⟩ := hrow
    rfl
  case g4 =>
    intro row hrow
    simp only [Template2.boolRows, List.mem_map] at hrow
    obtain ⟨_, _, rfl⟩ := hrow
    rfl

namespace Sharded

variable {S : Sharded F}

variable (S) in
/-- A v2 message tuple, decoded and cut to its channel's arity. -/
def proj2 (t : List F) : List F := S.system.proj (unpack S.buses t)

theorem decode_code {bound : Nat} (sep : S.Separated bound) {e : (F × F) × Nat × Bool} (he : e ∈ S.buses) :
    decode S.buses ((e.2.1 : Nat) : F) = some e.1 := by
  unfold decode
  cases h : S.buses.find? (fun e' => ((e'.2.1 : Nat) : F) == ((e.2.1 : Nat) : F)) with
  | none =>
      have := List.find?_eq_none.mp h e he
      simp at this
  | some e' =>
      have mem := List.mem_of_find?_eq_some h
      have eq := List.find?_some h
      simp only [beq_iff_eq] at eq
      have := sep.small.inj (sep.codes e' mem).1 (sep.codes e he).1 eq
      rw [List.inj_on_of_nodup_map sep.nodup mem he this]
      rfl

theorem unpack_code {bound : Nat} (sep : S.Separated bound) {tag sub : F} {code : Nat} {lane : Bool}
    (he : ((tag, sub), code, lane) ∈ S.buses) (rest : List F) :
    unpack S.buses ((code : F) :: rest) = tag :: sub :: rest := by
  simp [unpack, decode_code sep he]

section Instance

variable (lens : S.Lengths) (rowsOk : S.RowsOk) (virt : S.VirtualOk) (valid : S.system.Valid) {H : Nat → Nat}
  {main : Nat → Nat → Nat → F} (trace : S.ShardTrace H main) {k f' i : Nat} (hk : k < S.shards.length)
  {T2 : Template2 F} (hT2 : (S.layout k).templates[f']? = some T2)
  (cap : i < ((S.layout k).shadow S.width).cap f')

include lens rowsOk virt trace hk hT2 cap in
/-- A physical cell of a placed row holds `valV` of its slot. -/
theorem cell_value {r j s : Nat} (hr : r < T2.rows.length) (hj : j < S.width)
    (hc : (T2.rowCells T2.rows[r])[j]? = some (some s)) :
    main k (((S.layout k).shadow S.width).row f' i r) j = S.valV main (S.base k + f') i s := by
  have hf' : f' < (S.layout k).templates.length := (List.getElem?_eq_some_iff.mp hT2).1
  obtain ⟨_, phys⟩ := rowsOk k hk T2 (List.mem_of_getElem? hT2)
  simp only [Template2.checkPhysical, Bool.and_eq_true, List.all_eq_true] at phys
  have facts := phys.1.1.1.1 _ (List.getElem_mem hr) _ (List.mem_of_getElem? hc)
  simp only [Option.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at facts
  obtain ⟨_, ns⟩ := facts s rfl
  have place : (f', i, r) ∈ ((S.layout k).shadow S.width).places :=
    ((S.layout k).shadow S.width).mem_places.mpr ⟨by simpa [Layout.shadow] using hf', cap,
      by simp [System.rowCount, Layout.shadow, hT2, Template2.shadow, hr]⟩
  have hsh : ((S.layout k).shadow S.width).templates[f']? = some T2.shadow := by
    simp [Layout.shadow, hT2]
  have shCell : T2.shadow.cell r j = some s := by
    rw [Template.cell_of (show T2.shadow.rows[r]? = some (.message 0 0 0 (T2.rowCells T2.rows[r])) by
      simp [Template2.shadow, hr])]
    simp only [Row.cells, hc, Option.getD_some]
  have nv := VirtualOk.cell virt hk (List.mem_of_getElem? hT2) (List.getElem_mem hr) (List.mem_of_getElem? hc)
  rw [trace.consistent k hk f' i r place T2.shadow hsh j hj s shCell, valV_physical hk hf' hT2 ns nv i]

include lens valid hk hT2 cap in
/-- A slot in a cell of a logical message row reads `valV`. -/
theorem message_value {m : Nat} {msg : Message F} (hm : T2.messages[m]? = some msg) {j s : Nat}
    (hc : msg.2.2.2[j]? = some (some s)) :
    S.system.slotValue (S.mainV main) (S.base k + f') i s = S.valV main (S.base k + f') i s := by
  have hf' : f' < (S.layout k).templates.length := (List.getElem?_eq_some_iff.mp hT2).1
  have hT := system_template k hk hf'
  rw [hT2, Option.map_some] at hT
  have hf : S.base k + f' < S.system.templates.length := (List.getElem?_eq_some_iff.mp hT).1
  have hi : i < S.system.cap (S.base k + f') := by rw [system_cap lens k hk hf']; exact cap
  have hc' : S.base k + f' < S.system.circuits.length := by rw [valid.lengths.1]; exact hf
  obtain ⟨_, checked⟩ := valid.templates _ hf hc'
  rw [show S.system.templates[S.base k + f'] = T2.logical from
    Option.some.inj ((List.getElem?_eq_getElem hf).symm.trans hT)] at checked
  obtain ⟨sel, tag, sub, cells⟩ := msg
  have hrow : Row.message sel tag sub cells ∈ T2.logical.rows := by
    simp only [Template2.logical, List.mem_append, Template2.messageRows, List.mem_map]
    exact Or.inr ⟨_, List.mem_of_getElem? hm, rfl⟩
  have wf := checked.rows _ hrow
  simp only [Row.wellFormed, beq_iff_eq] at wf
  have hj : j < T2.logical.width := by rw [← wf]; exact (List.getElem?_eq_some_iff.mp hc).1
  have hs := checked.cells _ hrow _ (List.mem_of_getElem? hc) s rfl
  obtain ⟨r, hr, cell⟩ := cell_of_mem hrow (j := j) (s := s) (by simpa [Row.cells] using hc)
  exact slotValue_mainV hf hi hT hr hj cell hs

include lens virt valid hk hT2 cap in
/-- The physical multiplicity `mk + mc·x`, with `x` the value of the physical
cell 0, is the logical multiplicity `sel·mult`. -/
theorem mult_value {m : Nat} {sel tag sub : F} {mult : Nat} {rest : List (Option Nat)}
    (hm : T2.messages[m]? = some (sel, tag, sub, some mult :: rest)) (x : F)
    (hx : ∀ s, (T2.physMult m).2.2 = some s → x = S.valV main (S.base k + f') i s) :
    (T2.physMult m).1 + (T2.physMult m).2.1 * x =
      sel * S.system.slotValue (S.mainV main) (S.base k + f') i mult := by
  have hf' : f' < (S.layout k).templates.length := (List.getElem?_eq_some_iff.mp hT2).1
  rw [message_value lens valid hk hT2 cap hm (j := 0) (s := mult) rfl]
  have memT := List.mem_of_getElem? hT2
  by_cases hv : mult ∈ T2.virtual
  · have sel1 := VirtualOk.sel virt hk memT (List.mem_of_getElem? hm) hv
    rcases VirtualOk.def virt hk memT hv with ⟨c, x', k', hdef, _, nsx, nvx⟩ | ⟨k', hdef⟩
    · have pm : T2.physMult m = (k', c, some x') := by simp [Template2.physMult, hm, hv, hdef]
      rw [pm] at hx ⊢
      rw [valV_virtual hk hf' hT2 (by rw [hdef]; simp) hv i, sel1, one_mul, hx x' rfl,
        valV_physical hk hf' hT2 nsx nvx i]
      simp [Template2.virtualValue, hdef]
    · have pm : T2.physMult m = (k', 0, none) := by simp [Template2.physMult, hm, hv, hdef]
      rw [pm, valV_virtual hk hf' hT2 (by rw [hdef]; simp) hv i, sel1, one_mul]
      simp [Template2.virtualValue, hdef]
  · have pm : T2.physMult m = (0, sel, some mult) := by simp [Template2.physMult, hm, hv]
    rw [pm] at hx ⊢
    rw [hx mult rfl]; ring

include lens rowsOk virt valid trace hk hT2 cap in
/-- A lane message, decoded and cut to its arity, is its logical message entry. -/
theorem lane_entry {bound : Nat} (sep : S.Separated bound) (logical : S.system.Logical (S.mainV main))
    {r : Nat} {ls : List (LaneUse F)} {spans : List Span} (hr : T2.rows[r]? = some (.gate ls spans))
    {l m : Nat} (hl : l < lanes S.width) (hu : ls[l]? = some (.message m)) {msg : Message F}
    (hm : T2.messages[m]? = some msg) :
    Finsupp.mapDomain S.proj2 ((laneMessage S.width l).entry
        (S.assign k (main k) (((S.layout k).shadow S.width).row f' i r))) =
      System.msgEntry (S.system.slotValue (S.mainV main) (S.base k + f') i) msg := by
  have hf' : f' < (S.layout k).templates.length := (List.getElem?_eq_some_iff.mp hT2).1
  have hrlt : r < T2.rows.length := (List.getElem?_eq_some_iff.mp hr).1
  have hrow : T2.rows[r] = .gate ls spans := Option.some.inj ((List.getElem?_eq_getElem hrlt).symm.trans hr)
  have place : (f', i, r) ∈ ((S.layout k).shadow S.width).places :=
    ((S.layout k).shadow S.width).mem_places.mpr ⟨by simpa [Layout.shadow] using hf', cap,
      by simp [System.rowCount, Layout.shadow, hT2, Template2.shadow, hrlt]⟩
  set p := ((S.layout k).shadow S.width).row f' i r
  have placed : Placed S k p f' i r T2 (.gate ls spans) :=
    ⟨by rw [List.getElem?_eq_getElem (((S.layout k).shadow S.width).row_lt place),
        ((S.layout k).shadow S.width).places_row place], hT2, hr⟩
  obtain ⟨sel, tag, sub, cells⟩ := msg
  obtain ⟨w2, phys⟩ := rowsOk k hk T2 (List.mem_of_getElem? hT2)
  have rowOk := rowsOk.row hk placed
  obtain ⟨lenLs, _, _, _⟩ := checkRow_gate rowOk
  have mOk : T2.laneMessageOk S.buses m = true := by
    simp only [Template2.checkRow, Bool.and_eq_true, List.all_eq_true] at rowOk
    exact rowOk.1.1.2 _ (List.mem_of_getElem? hu)
  simp only [Template2.laneMessageOk, hm, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at mOk
  obtain ⟨tail, lk⟩ := mOk
  obtain ⟨code, lane, hlk⟩ : ∃ code lane, S.buses.lookup (tag, sub) = some (code, lane) := by
    cases h : S.buses.lookup (tag, sub) with
    | none => rw [h] at lk; simp at lk
    | some e => exact ⟨e.1, e.2, rfl⟩
  obtain ⟨codeEq, mem⟩ := codeOf_mem hlk
  have hT := system_template k hk hf'
  rw [hT2, Option.map_some] at hT
  have hf : S.base k + f' < S.system.templates.length := (List.getElem?_eq_some_iff.mp hT).1
  have hc' : S.base k + f' < S.system.circuits.length := by rw [valid.lengths.1]; exact hf
  have hi : i < S.system.cap (S.base k + f') := by rw [system_cap lens k hk hf']; exact cap
  obtain ⟨wT, checked⟩ := valid.templates _ hf hc'
  have eqT : S.system.templates[S.base k + f'] = T2.logical :=
    Option.some.inj ((List.getElem?_eq_getElem hf).symm.trans hT)
  rw [eqT] at checked wT
  have memMsg : (sel, tag, sub, cells) ∈ T2.logical.messages := by
    rw [logical_messages]; exact List.mem_of_getElem? hm
  obtain ⟨mult, ps, cellsEq, psW⟩ :=
    checked.rowShaped (logical.relations _ hf i hi _ hT) _ memMsg
  simp only at cellsEq
  rw [show T2.logical.width = S.width from w2] at cellsEq
  have psLen : ps.length ≤ 3 := by
    by_contra h
    have h4 := System.messageCells_succ S.width mult ps (j := 3) (by omega)
    rw [← cellsEq] at h4
    have := tail _ (List.mem_of_getElem? (show (cells.drop 4)[0]? = some (some ps[3]) by
      rw [List.getElem?_drop]; exact h4))
    simp at this
  have hl' : l < ls.length := by rw [lenLs, w2]; exact hl
  have hls : ls[l] = .message m := (List.getElem?_eq_some_iff.mp hu).2
  have val_eq : ∀ j s, j < 4 → 0 < j → cells[j]? = some (some s) →
      main k p (4 * l + j) = S.system.slotValue (S.mainV main) (S.base k + f') i s := by
    intro j s hj j0 hc
    have physCell : (T2.rowCells T2.rows[r])[4 * l + j]? = some (some s) := by
      rw [hrow]
      simp only [Template2.rowCells]
      rw [flatMap_laneCells_getElem? T2 ls hl' hj, hls]
      simp [Template2.laneCells, Template2.msgCells, hm, hc, hj, Nat.pos_iff_ne_zero.mp j0]
    rw [cell_value lens rowsOk virt trace hk hT2 cap hrlt (by simp only [lanes] at hl; omega) physCell]
    exact (message_value lens valid hk hT2 cap hm hc).symm
  have arity : S.system.arityOf (tag :: sub :: [main k p (4 * l + 1), main k p (4 * l + 2),
      main k p (4 * l + 3)]) = ps.length := by
    have entry : ((tag, sub), ((cells.drop 1).filterMap id).length) ∈ S.system.arities := by
      simp only [System.arities, List.mem_flatMap, List.mem_map]
      exact ⟨T2.logical, List.mem_of_getElem? hT, _, memMsg, rfl⟩
    have := valid.arities _ entry
    rw [cellsEq, System.messageCells_drop] at this
    simp only [System.arityOf, this, Option.getD_some]
  have a0 := placed.laneMsg (main := main k) (c := 0) hl (by norm_num)
  have a1 := placed.laneMsg (main := main k) (c := 1) hl (by norm_num)
  have a2 := placed.laneMsg (main := main k) (c := 2) hl (by norm_num)
  simp only [Row2.laneMsg, hu, hm, codeEq] at a0 a1 a2
  have m0 : S.assign k (main k) p (4 * l) = main k p (4 * l + 0) :=
    Sharded.assign_main (by simp only [lanes] at hl; omega)
  have m1 : S.assign k (main k) p (4 * l + 1) = main k p (4 * l + 1) :=
    Sharded.assign_main (by simp only [lanes] at hl; omega)
  have m2 : S.assign k (main k) p (4 * l + 2) = main k p (4 * l + 2) :=
    Sharded.assign_main (by simp only [lanes] at hl; omega)
  have m3 : S.assign k (main k) p (4 * l + 3) = main k p (4 * l + 3) :=
    Sharded.assign_main (by simp only [lanes] at hl; omega)
  rw [laneMessage_entry, Finsupp.mapDomain_single, a0, a1, a2, m0, m1, m2, m3]
  simp only [List.getD_cons_zero, List.getD_cons_succ, zero_add]
  simp only [System.msgEntry, cellsEq, System.messageCells_drop, proj2, unpack_code sep mem,
    System.proj, arity]
  congr 1
  · simp only [List.take_succ_cons, show 2 + ps.length = ps.length + 1 + 1 by omega]
    congr 2
    apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.getElem_map]
    have hj : j < ps.length := by simpa using h2
    rw [List.getElem_take]
    have := val_eq (j + 1) ps[j] (by omega) (by omega) (by rw [cellsEq]; exact System.messageCells_succ _ _ _ hj)
    rcases j with _ | _ | _ | j
    · simpa using this
    · simpa using this
    · simpa using this
    · omega
  · have hm' : T2.messages[m]? = some (sel, tag, sub, some mult :: (cells.drop 1)) := by
      rw [hm, cellsEq]; rfl
    have v0 := mult_value lens virt valid hk hT2 cap hm' (main k p (4 * l + 0)) (fun s hs => by
      have physCell : (T2.rowCells T2.rows[r])[4 * l + 0]? = some (some s) := by
        rw [hrow]
        simp only [Template2.rowCells]
        rw [flatMap_laneCells_getElem? T2 ls hl' (by norm_num), hls]
        simp [Template2.laneCells, hs]
      exact cell_value lens rowsOk virt trace hk hT2 cap hrlt (by simp only [lanes] at hl; omega) physCell)
    rw [v0]
    simp [messageCells]

include lens rowsOk virt valid trace hk hT2 cap in
/-- A row message, decoded and cut to its arity, is its logical message entry;
on a key row the key coordinate is the logical invocation id. -/
theorem row_entry {bound : Nat} (sep : S.Separated bound) (logical : S.system.Logical (S.mainV main))
    {r m : Nat} {key : Bool} (hr : T2.rows[r]? = some (.message m key)) {msg : Message F}
    (hm : T2.messages[m]? = some msg) :
    Finsupp.mapDomain S.proj2 ((rowMessage S.width (S.idOffset k)).entry
        (S.assign k (main k) (((S.layout k).shadow S.width).row f' i r))) =
      System.msgEntry (S.system.slotValue (S.mainV main) (S.base k + f') i) msg := by
  have hf' : f' < (S.layout k).templates.length := (List.getElem?_eq_some_iff.mp hT2).1
  have hrlt : r < T2.rows.length := (List.getElem?_eq_some_iff.mp hr).1
  have hrow : T2.rows[r] = .message m key := Option.some.inj ((List.getElem?_eq_getElem hrlt).symm.trans hr)
  have place : (f', i, r) ∈ ((S.layout k).shadow S.width).places :=
    ((S.layout k).shadow S.width).mem_places.mpr ⟨by simpa [Layout.shadow] using hf', cap,
      by simp [System.rowCount, Layout.shadow, hT2, Template2.shadow, hrlt]⟩
  set p := ((S.layout k).shadow S.width).row f' i r
  have placed : Placed S k p f' i r T2 (.message m key) :=
    ⟨by rw [List.getElem?_eq_getElem (((S.layout k).shadow S.width).row_lt place),
        ((S.layout k).shadow S.width).places_row place], hT2, hr⟩
  have pH : p < H k := Nat.lt_of_lt_of_le (((S.layout k).shadow S.width).row_lt place) (trace.tall k hk)
  obtain ⟨sel, tag, sub, cells⟩ := msg
  obtain ⟨w2, _⟩ := rowsOk k hk T2 (List.mem_of_getElem? hT2)
  have rowOk := rowsOk.row hk placed
  simp only [Template2.checkRow, Template2.rowMessageOk, hm, Bool.and_eq_true] at rowOk
  obtain ⟨lk, keyOk⟩ := rowOk
  obtain ⟨code, lane, hlk⟩ : ∃ code lane, S.buses.lookup (tag, sub) = some (code, lane) := by
    cases h : S.buses.lookup (tag, sub) with
    | none => rw [h] at lk; simp at lk
    | some e => exact ⟨e.1, e.2, rfl⟩
  obtain ⟨codeEq, mem⟩ := codeOf_mem hlk
  have hT := system_template k hk hf'
  rw [hT2, Option.map_some] at hT
  have hf : S.base k + f' < S.system.templates.length := (List.getElem?_eq_some_iff.mp hT).1
  have hc' : S.base k + f' < S.system.circuits.length := by rw [valid.lengths.1]; exact hf
  have hi : i < S.system.cap (S.base k + f') := by rw [system_cap lens k hk hf']; exact cap
  obtain ⟨wT, checked⟩ := valid.templates _ hf hc'
  have eqT : S.system.templates[S.base k + f'] = T2.logical :=
    Option.some.inj ((List.getElem?_eq_getElem hf).symm.trans hT)
  rw [eqT] at checked wT
  have memMsg : (sel, tag, sub, cells) ∈ T2.logical.messages := by
    rw [logical_messages]; exact List.mem_of_getElem? hm
  obtain ⟨mult, ps, cellsEq, psW⟩ :=
    checked.rowShaped (logical.relations _ hf i hi _ hT) _ memMsg
  simp only at cellsEq psW
  rw [show T2.logical.width = S.width from w2] at cellsEq psW
  have w4 : 4 ≤ S.width := by have := checked.width.1; rw [show T2.logical.width = S.width from w2] at this; exact this
  set val := S.system.slotValue (S.mainV main) (S.base k + f') i
  have val_eq : ∀ j s, j < S.width → ¬ (key = true ∧ j = 1) → j ≠ 0 → cells[j]? = some (some s) →
      main k p j = val s := by
    intro j s hj nk j0 hc
    have physCell : (T2.rowCells T2.rows[r])[j]? = some (some s) := by
      rw [hrow]
      simp only [Template2.rowCells, List.getElem?_map, List.getElem?_range, w2, hj, if_true,
        Option.map_some, Template2.msgCells, hm, Option.map_some, Option.getD_some, hc,
        Option.some.injEq]
      rw [if_neg nk, if_neg j0]
    rw [cell_value lens rowsOk virt trace hk hT2 cap hrlt hj physCell]
    exact (message_value lens valid hk hT2 cap hm hc).symm
  have arity : ∀ rest : List F, S.system.arityOf (tag :: sub :: rest) = ps.length := by
    intro rest
    have entry : ((tag, sub), ((cells.drop 1).filterMap id).length) ∈ S.system.arities := by
      simp only [System.arities, List.mem_flatMap, List.mem_map]
      exact ⟨T2.logical, List.mem_of_getElem? hT, _, memMsg, rfl⟩
    have := valid.arities _ entry
    rw [cellsEq, System.messageCells_drop] at this
    simp only [System.arityOf, this, Option.getD_some]
  have r0 := placed.rowMsg (main := main k) (c := 0) (by norm_num)
  have r1 := placed.rowMsg (main := main k) (c := 1) (by norm_num)
  have r2 := placed.rowMsg (main := main k) (c := 2) (by norm_num)
  have r3 := placed.rowMsg (main := main k) (c := 3) (by norm_num)
  have r4 := placed.rowMsg (main := main k) (c := 4) (by norm_num)
  simp only [Row2.rowMsg, hm, codeEq, List.getD_cons_succ, List.getD_cons_zero] at r0 r1 r2 r3 r4
  have keyCoord : S.assign k (main k) p 1 +
      (if key = true then (((S.layout k).shadow S.width).instId f' i : F) else 0) +
      (if key = true then (1 : F) else 0) * ((S.idOffset k : Nat) : F) =
      (if ps = [] then main k p 1 else val ps[0]!) := by
    rw [Sharded.assign_main (by omega)]
    cases key with
    | true =>
        have x1 := placed.key_cell w4 (trace.rows k hk p pH)
        simp only [Bool.true_eq_false, Bool.not_true, Bool.false_or] at keyOk
        obtain ⟨ks, hks, inv⟩ : ∃ ks, (T2.msgCells m)[1]? = some (some ks) ∧ T2.slots[ks]? = some .invocation := by
          split at keyOk
          · rename_i ks h; exact ⟨ks, h, by simpa using keyOk⟩
          · simp at keyOk
        have c1 : cells[1]? = some (some ks) := by simpa [Template2.msgCells, hm] using hks
        have ps0 : ps ≠ [] := by
          intro e; rw [cellsEq, e] at c1
          simp [messageCells, List.getElem?_replicate] at c1
        have hp0 : ps[0]! = ks := by
          have := System.messageCells_succ S.width mult ps (j := 0) (List.length_pos_iff.mpr ps0)
          rw [← cellsEq, c1] at this
          simp only [Option.some.injEq] at this
          rw [getElem!_pos ps 0 (List.length_pos_iff.mpr ps0)]
          exact this.symm
        rw [if_neg ps0, hp0, x1]
        have vk : val ks = S.valV main (S.base k + f') i ks := message_value lens valid hk hT2 cap hm c1
        rw [vk]
        simp only [valV, hT, Option.bind_some, Template2.logical, inv, if_true]
        rw [system_instId lens k hk hf' i]
        push_cast; ring
    | false =>
        simp only [Bool.false_eq_true, if_false, add_zero, Nat.cast_zero, zero_mul, Nat.cast_ofNat]
        split
        · rfl
        · rename_i ps0
          apply val_eq 1 _ (by omega) (by simp) (by omega) _
          have := System.messageCells_succ S.width mult ps (j := 0) (List.length_pos_iff.mpr ps0)
          rw [← cellsEq] at this
          rw [this, getElem!_pos ps 0 (List.length_pos_iff.mpr ps0)]
  have a0 : S.assign k (main k) p 0 = main k p 0 := Sharded.assign_main (by omega)
  rw [rowMessage_entry, Finsupp.mapDomain_single, r0, r1, r2, r3, r4, keyCoord, a0]
  simp only [System.msgEntry, cellsEq, System.messageCells_drop, proj2, unpack_code sep mem,
    System.proj, arity, zero_add]
  have hm' : T2.messages[m]? = some (sel, tag, sub, some mult :: (cells.drop 1)) := by
    rw [hm, cellsEq]; rfl
  have v0 := mult_value lens virt valid hk hT2 cap hm' (main k p 0) (fun s hs => by
    have physCell : (T2.rowCells T2.rows[r])[0]? = some (some s) := by
      rw [hrow]
      simp [Template2.rowCells, hs, show 0 < T2.width by omega]
    exact cell_value lens rowsOk virt trace hk hT2 cap hrlt (by omega) physCell)
  congr 1
  · rw [show 2 + ps.length = ps.length + 1 + 1 by omega, List.take_succ_cons, List.take_succ_cons]
    congr 2
    have rest : ∀ j (hj : j + 1 < ps.length), S.assign k (main k) p (j + 2) = val ps[j + 1] := by
      intro j hj
      rw [Sharded.assign_main (by omega)]
      exact val_eq (j + 2) _ (by omega) (by omega) (by omega)
        (by rw [cellsEq]; exact System.messageCells_succ _ _ _ hj)
    rcases ps with _ | ⟨p0, ps'⟩
    · simp
    · simp only [List.length_cons, List.take_succ_cons, List.map_cons, reduceCtorEq, if_false,
        getElem!_pos (p0 :: ps') 0 (by simp), List.getElem_cons_zero]
      congr 1
      apply List.ext_getElem (by simp at psW ⊢; omega)
      intro j h1 h2
      simp only [List.getElem_take, List.getElem_map, List.getElem_range]
      have := rest j (by simpa using h2)
      rw [List.getElem_cons_succ] at this
      simpa using this

/-- The row and lane messages of physical row `p` of shard `k`. -/
noncomputable def rowMsgs (S : Sharded F) (k : Nat) (main : Nat → Nat → F) (p : Nat) : Ledger F :=
  (rowMessage S.width (S.idOffset k)).entry (S.assign k main p) +
    ((List.range (lanes S.width)).map fun l => (laneMessage S.width l).entry (S.assign k main p)).sum

/-- The logical entry of message `m`, zero past the last message. -/
noncomputable def entryOf (T : Template2 F) (val : Nat → F) (m : Nat) : Ledger F :=
  ((T.messages[m]?).map (System.msgEntry val)).getD 0

theorem mapDomain_list_sum (g : List F → List F) (l : List (Ledger F)) :
    Finsupp.mapDomain g l.sum = (l.map (Finsupp.mapDomain g)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [Finsupp.mapDomain_add, ih]

theorem sum_lanes_refs {M : Type} [AddCommMonoid M] (ls : List (LaneUse F)) (h : Nat → M) :
    (ls.map fun u => match u with
      | .message m => h m
      | _ => 0).sum = ((Row2.gate ls ([] : List Span)).refs.map h).sum := by
  simp only [Row2.refs]
  induction ls with
  | nil => simp
  | cons u ls ih => cases u <;> simp [ih]

include lens rowsOk virt valid trace hk hT2 cap in
/-- A placed row's messages are its placed logical messages. -/
theorem row_total {bound : Nat} (sep : S.Separated bound) (logical : S.system.Logical (S.mainV main))
    {r : Nat} (hr : r < T2.rows.length) :
    Finsupp.mapDomain S.proj2 (S.rowMsgs k (main k) (((S.layout k).shadow S.width).row f' i r)) =
      ((T2.rows[r].refs).map (entryOf T2 (S.system.slotValue (S.mainV main) (S.base k + f') i))).sum := by
  have hf' : f' < (S.layout k).templates.length := (List.getElem?_eq_some_iff.mp hT2).1
  have place : (f', i, r) ∈ ((S.layout k).shadow S.width).places :=
    ((S.layout k).shadow S.width).mem_places.mpr ⟨by simpa [Layout.shadow] using hf', cap,
      by simp [System.rowCount, Layout.shadow, hT2, Template2.shadow, hr]⟩
  have placedAt : ∀ row, T2.rows[r]? = some row →
      Placed S k (((S.layout k).shadow S.width).row f' i r) f' i r T2 row := fun row h =>
    ⟨by rw [List.getElem?_eq_getElem (((S.layout k).shadow S.width).row_lt place),
        ((S.layout k).shadow S.width).places_row place], hT2, h⟩
  have hget := List.getElem?_eq_getElem hr
  unfold rowMsgs
  rw [Finsupp.mapDomain_add, mapDomain_list_sum, List.map_map]
  cases hrow : T2.rows[r] with
  | gate ls spans =>
      rw [hrow] at hget
      have placed := placedAt _ hget
      have rowZero : (rowMessage S.width (S.idOffset k)).entry
          (S.assign k (main k) (((S.layout k).shadow S.width).row f' i r)) = 0 := by
        rw [rowMessage_entry, placed.rowMsg (c := 1) (by norm_num), placed.rowMsg (c := 2) (by norm_num)]
        simp [Row2.rowMsg]
      rw [rowZero, Finsupp.mapDomain_zero, zero_add]
      obtain ⟨lenLs, _, _, _⟩ := checkRow_gate (rowsOk.row hk placed)
      obtain ⟨w2, _⟩ := rowsOk k hk T2 (List.mem_of_getElem? hT2)
      have refsEq : (Row2.gate ls spans).refs = (Row2.gate ls ([] : List Span)).refs := rfl
      rw [refsEq, ← sum_lanes_refs, show lanes S.width = ls.length by rw [lenLs, w2]]
      apply sum_range_getElem
      intro l hl
      have hu := List.getElem?_eq_getElem hl
      simp only [Function.comp]
      cases hlu : ls[l] with
      | message m =>
          rw [hlu] at hu
          have mOk : T2.laneMessageOk S.buses m = true := by
            have := rowsOk.row hk placed
            simp only [Template2.checkRow, Bool.and_eq_true, List.all_eq_true] at this
            exact this.1.1.2 _ (List.mem_of_getElem? hu)
          cases hm : T2.messages[m]? with
          | none => simp [Template2.laneMessageOk, hm] at mOk
          | some msg =>
              simp only [entryOf, hm, Option.map_some, Option.getD_some]
              exact lane_entry lens rowsOk virt valid trace hk hT2 cap sep logical hget
                (by rw [lenLs, w2] at hl; exact hl) hu hm
      | gate lane =>
          rw [hlu] at hu
          rw [laneMessage_entry, placed.laneMsg (c := 1) (by rw [lenLs, w2] at hl; exact hl) (by norm_num),
            placed.laneMsg (c := 2) (by rw [lenLs, w2] at hl; exact hl) (by norm_num)]
          simp [Row2.laneMsg, hu]
      | empty =>
          rw [hlu] at hu
          rw [laneMessage_entry, placed.laneMsg (c := 1) (by rw [lenLs, w2] at hl; exact hl) (by norm_num),
            placed.laneMsg (c := 2) (by rw [lenLs, w2] at hl; exact hl) (by norm_num)]
          simp [Row2.laneMsg, hu]
  | message m key =>
      rw [hrow] at hget
      have placed := placedAt _ hget
      have lanesZero : ∀ l ∈ List.range (lanes S.width), Finsupp.mapDomain S.proj2
          ((laneMessage S.width l).entry (S.assign k (main k) (((S.layout k).shadow S.width).row f' i r))) = 0 := by
        intro l hl
        have hl := List.mem_range.mp hl
        rw [laneMessage_entry, placed.laneMsg (c := 1) hl (by norm_num), placed.laneMsg (c := 2) hl (by norm_num)]
        simp [Row2.laneMsg]
      rw [List.sum_eq_zero (fun x hx => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
        exact lanesZero l hl), add_zero]
      have mOk := rowsOk.row hk placed
      simp only [Template2.checkRow, Template2.rowMessageOk, Bool.and_eq_true] at mOk
      cases hm : T2.messages[m]? with
      | none => simp [hm] at mOk
      | some msg =>
          simp only [Row2.refs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, entryOf,
            hm, Option.map_some, Option.getD_some]
          exact row_entry lens rowsOk virt valid trace hk hT2 cap sep logical hget hm

end Instance

end Sharded

end Aiur.Tiling.Periodic
