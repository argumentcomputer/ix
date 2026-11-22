import Aiur.Tiling.Assemble

/-!
# The lookup half for keyed layouts

Every lookup `l` of instance `i` of circuit `f` of a system accepted by
`System.checkKeyed` travels on the narrow bus as one `Part`
(`System.partAt`): its message group, read at the instance's slot values.
The projected narrow message ledger is the sum of the parts' narrow
encodings, and the wide ledger of the reconstructed rows is the sum of their
wide tuples. With `Part.balance` this gives `System.keyed_sound`: a balanced
narrow trace of a keyed layout yields wide rows whose lookups balance
against the external parts, provided the external ledger is given as parts
whose chunked receivers use channels without in-system receivers.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

def zeroPart : Part F := ⟨0, 0, [], 0, false, 0, [], []⟩

/-- The part a message group carries, given slot values `val` and the wide row `a`. -/
def groupPart (val : Nat → F) (a : Var → F) (recv : Bool) (g : List (F × F × F × List (Option Nat)))
    (L : Lookup F) : Part F :=
  match g with
  | [m] => ⟨m.2.1, m.2.2.1, (L.tuple a).drop 2, L.multiplicity.denote a, recv, 0, [], []⟩
  | m :: m' :: rest => ⟨m.2.1, m.2.2.1 - chunkSub (Template.messageRom m) 0 0, (L.tuple a).drop 2,
      L.multiplicity.denote a, recv, val ((m.2.2.2[1]?).join.getD 0),
      (m :: m' :: rest).map fun r => (Template.chunkCells r).map val, []⟩
  | [] => zeroPart

theorem chunkSub_zero_sub (rom : Bool) (sub : F) : chunkSub rom sub 0 - chunkSub rom 0 0 = sub := by
  simp [chunkSub]

theorem chunkCells_keyed (sel tag s : F) (W mult key : Nat) (ch : List Nat) :
    Template.chunkCells (sel, tag, s, keyedCells W mult key ch) = ch := by
  simp [Template.chunkCells, keyedCells, List.filterMap_append, List.filterMap_map]

theorem msgEntry_keyed (val : Nat → F) (sel tag s : F) (W mult key : Nat) (ch : List Nat) :
    System.msgEntry val (sel, tag, s, keyedCells W mult key ch) =
      Finsupp.single (tag :: s :: val key :: ch.map val) (sel * val mult) := by
  rw [keyedCells_eq]
  simp only [System.msgEntry, System.messageCells_drop]
  simp [messageCells]

theorem map_zipIdx_fst {α β : Type} (g : α → β) : ∀ (l : List α) (n : Nat),
    (l.zipIdx n).map (fun x => g x.1) = l.map g
  | [], _ => rfl
  | x :: l, n => by simp [List.zipIdx_cons, map_zipIdx_fst g l (n + 1)]

/-- The rows' table entries a group must have for its part to be `RowsIn`. -/
structure GroupTables (role : F × F → Option (RowRole F)) (arity : F × F → Option Nat)
    (g : List (F × F × F × List (Option Nat))) : Prop where
  roles : ∀ e ∈ groupRoles g, role e.1 = some e.2
  arities : ∀ m ∈ g, arity (m.2.1, m.2.2.1) = some ((m.2.2.2.drop 1).filterMap id).length

theorem mem_groupRoles {g : List (F × F × F × List (Option Nat))} (two : 2 ≤ g.length) {c : Nat}
    (hc : c < g.length) :
    ((g[c].2.1, g[c].2.2.1), (g[0].2.2.1 - chunkSub (Template.messageRom g[0]) 0 0,
      some (c, g.length, Template.messageRom g[0]))) ∈ groupRoles g := by
  match g, two with
  | m :: m' :: rest, _ =>
      simp only [groupRoles]
      exact List.mem_map.mpr ⟨(_, c), List.mk_mem_zipIdx_iff_getElem?.mpr
        (by simp [List.getElem?_eq_getElem hc]), rfl⟩

theorem groupPart_chunks {val : Nat → F} {a : Var → F} {recv : Bool} {L : Lookup F} {W : Nat}
    {sel tag sub : F} {mult key : Nat} {rom : Bool} {chunks : List (List Nat)}
    (two : 2 ≤ chunks.length) (romEq : rom = (tag == 2))
    (tupleEq : L.tuple a = tag :: sub :: ((if rom then [val key] else []) ++ chunks.flatten.map val))
    (multEq : L.multiplicity.denote a = sel * val mult) :
    groupPart val a recv (chunks.zipIdx.map
        (fun x => (sel, tag, chunkSub rom sub x.2, keyedCells W mult key x.1))) L =
      ⟨tag, sub, (if rom then [val key] else []) ++ chunks.flatten.map val, sel * val mult, recv,
        val key, chunks.map (List.map val), []⟩ := by
  match chunks, two with
  | c0 :: c1 :: rest, _ =>
      have keyCell : ((keyedCells W mult key c0)[1]?).join.getD 0 = key := by simp [keyedCells]
      simp only [List.zipIdx_cons, List.map_cons, groupPart, Template.messageRom, ← romEq,
        chunkSub_zero_sub, tupleEq, multEq, List.drop_succ_cons, List.drop_zero, keyCell,
        chunkCells_keyed, List.map_map, Function.comp_def]
      rw [map_zipIdx_fst (fun x => List.map val x) rest]

/-- What the part of a sound group satisfies. -/
theorem GroupSound.part {W : Nat} {val : Nat → F} {a : Var → F} {recv : Bool} {idv : Nat}
    {g : List (F × F × F × List (Option Nat))} {L : Lookup F} (h : GroupSound W val a recv idv g L)
    (long : 2 ≤ g.length → W ≤ L.args.length - 2) {role : F × F → Option (RowRole F)}
    {arity : F × F → Option Nat} (tables : GroupTables role arity g) :
    (g.map (System.msgEntry val)).sum = (groupPart val a recv g L).narrow ∧
      L.entry a = (groupPart val a recv g L).wide ∧
      (groupPart val a recv g L).Formed W ∧
      (groupPart val a recv g L).RowsIn role arity ∧
      (groupPart val a recv g L).recv = recv ∧
      ((groupPart val a recv g L).chunks ≠ [] → recv = true → 2 ≤ g.length ∧
        ((groupPart val a recv g L).rom = false → (groupPart val a recv g L).key = val idv) ∧
        ((groupPart val a recv g L).rom = true →
          L.args[2]? = some (.const (groupPart val a recv g L).key))) := by
  rcases h with ⟨m, rfl, sound⟩ | ⟨sel, tag, sub, mult, key, rom, chunks, rfl, two, lens, multEq,
    tupleEq, recvK, recvR, sendB, romEq⟩
  · obtain ⟨mult, payload, cells, len, multEq, tupleEq⟩ := sound
    have entry := System.msgEntry_lookup ⟨mult, payload, cells, len, multEq, tupleEq⟩
    have wideEq : L.entry a = (groupPart val a recv [m] L).wide := by
      simp only [Lookup.entry, groupPart, Part.wide, Part.tuple, tupleEq, multEq, List.drop_succ_cons,
        List.drop_zero]
    refine ⟨by simp [entry, wideEq, Part.narrow, groupPart], wideEq,
      Or.inl ⟨rfl, by simp [groupPart, tupleEq]; omega⟩, ⟨?_, fun h => absurd rfl h⟩, rfl,
      fun h => absurd rfl h⟩
    intro _ r hr
    have := tables.roles ((m.2.1, m.2.2.1), (m.2.2.1, none)) (by simp [groupRoles])
    change role (m.2.1, m.2.2.1) = some r at hr
    rw [this] at hr
    cases hr
    rfl
  · set g := chunks.zipIdx.map (fun x => (sel, tag, chunkSub rom sub x.2, keyedCells W mult key x.1))
      with hg
    have glen : g.length = chunks.length := by simp [hg]
    have gat : ∀ c (hc : c < g.length), g[c] = (sel, tag, chunkSub rom sub c,
        keyedCells W mult key (chunks[c]'(by rw [glen] at hc; exact hc))) := by
      intro c hc; simp [hg]
    rw [groupPart_chunks two romEq tupleEq multEq]
    have nonempty : chunks.map (List.map val) ≠ [] := by
      intro h; rw [List.map_eq_nil_iff] at h; simp [h] at two
    refine ⟨?_, by simp only [Lookup.entry, tupleEq, multEq]; rfl, ?_, ?_, rfl, ?_⟩
    · unfold Part.narrow
      rw [if_neg nonempty, System.finset_sum_range_list]
      simp only [List.length_map]
      symm
      apply congrArg List.sum
      apply List.ext_getElem (by simp [glen])
      intro c h1 h2
      simp only [List.getElem_map, List.getElem_range, gat, msgEntry_keyed, Part.chunkTuple, Part.rom,
        ← romEq, Part.cweight, List.getD_nil]
      congr 3
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1), Option.getD_some, List.getElem_map]
    · refine Or.inr ⟨by simpa using two, ?_, ?_, ?_⟩
      · have := long (by rw [glen]; exact two)
        have len := congrArg List.length tupleEq
        simp only [Lookup.tuple, List.length_map, List.length_cons, List.length_append] at len ⊢
        omega
      · simp only [Part.rom, ← romEq, List.map_flatten]
      · exact ⟨sendB, Or.inl rfl⟩
    · refine ⟨fun h => absurd h nonempty, fun _ c hc => ?_⟩
      simp only [List.length_map] at hc
      have hcg : c < g.length := by rw [glen]; exact hc
      have row := tables.roles _ (mem_groupRoles (by rw [glen]; exact two) hcg)
      have ar := tables.arities _ (List.getElem_mem hcg)
      have g0 := gat 0 (by rw [glen]; omega)
      simp only [gat, g0, Template.messageRom, ← romEq, chunkSub_zero_sub, glen] at row ar
      simp only [Part.rom, ← romEq, List.length_map]
      refine ⟨row, ?_⟩
      rw [ar]
      simp [keyedCells, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    · intro _ hr
      refine ⟨by rw [glen]; exact two, fun r => recvK hr (by simpa [Part.rom, ← romEq] using r),
        fun r => ?_⟩
      have r : rom = true := by simpa [Part.rom, ← romEq] using r
      obtain ⟨k, hk⟩ := recvR hr r
      have at2 := congrArg (·[2]?) tupleEq
      simp only [Lookup.tuple, List.getElem?_map, hk, r, ↓reduceIte] at at2
      simp only [hk]
      simpa [Scalar.Circuit.ArithExpr.denote] using at2

theorem splitGroups_getElem_length (W : Nat) :
    ∀ (ms : List (F × F × F × List (Option Nat))) (ls : List (Lookup F)) (l : Nat) (hl : l < ls.length),
      ∃ rom, ((Template.splitGroups W ms ls)[l]'(by rw [splitGroups_length]; exact hl)).length ≤
        groupSize W (ls[l].args.length - 2) rom
  | ms, L :: ls, 0, _ => ⟨_, by simp only [Template.splitGroups, List.getElem_cons_zero]; exact List.length_take_le _ _⟩
  | ms, L :: ls, l + 1, hl => by
      simpa [Template.splitGroups] using splitGroups_getElem_length W _ ls l (by simpa using hl)

theorem wide_of_groupSize {W n k : Nat} {rom : Bool} (two : 2 ≤ k) (le : k ≤ groupSize W n rom) :
    W ≤ n := by
  unfold groupSize at le
  split_ifs at le <;> omega

theorem sum_range_mono (g : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    ((List.range a).map g).sum ≤ ((List.range b).map g).sum := by
  induction b, h using Nat.le_induction with
  | base => exact le_refl _
  | succ b _ ih => rw [List.range_succ, List.map_append, List.sum_append]; omega

namespace System

variable (sys : System F)

def roleOf (k : F × F) : Option (RowRole F) := List.lookup k sys.roles

def arityAt (k : F × F) : Option Nat := List.lookup k sys.arities

/-- Lookups of circuit `f`. -/
def lookupCount (f : Nat) : Nat := (sys.circuits[f]?.map (·.lookups.length)).getD 0

/-- Instances of all circuits. -/
def instances : Nat := ((List.range sys.templates.length).map sys.cap).sum

/-- Channels `(tag, sub)` whose chunked receive is lookup 0 of some template. -/
def receivers : List (F × F) :=
  (sys.templates.zip sys.circuits).filterMap fun (T, C) =>
    match groups T C with
    | (m :: _ :: _) :: _ => some (m.2.1, m.2.2.1 - chunkSub (Template.messageRom m) 0 0)
    | _ => none

/-- The part carried by lookup `l` of instance `i` of circuit `f`. -/
def partAt (main : Nat → Nat → F) (x : Nat × Nat × Nat) : Part F :=
  match sys.templates[x.1]?, sys.circuits[x.1]? with
  | some T, some C =>
      match (groups T C)[x.2.2]?, C.lookups[x.2.2]? with
      | some g, some L =>
          groupPart (sys.slotValue main x.1 x.2.1) (sys.wideRow main x.1 x.2.1) (x.2.2 == 0) g L
      | _, _ => zeroPart
  | _, _ => zeroPart

/-- What the part of lookup `x.2.2` of instance `x.2.1` of circuit `x.1` satisfies. -/
def PartFacts (main : Nat → Nat → F) (x : Nat × Nat × Nat) : Prop :=
  (sys.partAt main x).Formed sys.width ∧
    (sys.partAt main x).RowsIn sys.roleOf sys.arityAt ∧
    (sys.partAt main x).recv = (x.2.2 == 0) ∧
    ((sys.partAt main x).chunks ≠ [] → x.2.2 = 0 →
      ((sys.partAt main x).tag, (sys.partAt main x).sub) ∈ sys.receivers ∧
      ((sys.partAt main x).rom = false → (sys.partAt main x).key = (sys.instId x.1 x.2.1 : F)) ∧
      ((sys.partAt main x).rom = true →
        (x.1, ((sys.partAt main x).tag, (sys.partAt main x).sub), (sys.partAt main x).key) ∈
          sys.romReceivers))

theorem checkKeyed_parts {sys : System F} (ok : sys.checkKeyed = true) :
    (∀ T C, (T, C) ∈ sys.templates.zip sys.circuits → T.checkGroups C = true) ∧
      (∀ e ∈ sys.roles, sys.roles.lookup e.1 = some e.2) ∧
      (sys.romReceivers.map (·.2)).Nodup ∧ ∀ x ∈ sys.romReceivers, sys.cap x.1 ≤ 1 := by
  simp only [System.checkKeyed, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, temps⟩, _⟩, _⟩, rl⟩, nd⟩, caps⟩ := ok
  refine ⟨fun T C mem => ?_, fun e he => by simpa using rl e he, nd, caps⟩
  have := temps _ mem
  simp only [Bool.and_eq_true] at this
  exact this.2

omit [DecidableEq F] in
theorem instId_lt {f i : Nat} (hf : f < sys.templates.length) (hi : i < sys.cap f) :
    sys.instId f i < sys.instances := by
  have le : ((List.range (f + 1)).map sys.cap).sum ≤ sys.instances := by
    unfold instances
    exact sum_range_mono _ (by omega)
  rw [List.range_succ, List.map_append, List.sum_append] at le
  simp only [instId, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at le ⊢
  omega

omit [DecidableEq F] in
theorem instId_inj {f i f' i' : Nat} (hi : i < sys.cap f) (hi' : i' < sys.cap f')
    (h : sys.instId f i = sys.instId f' i') : f = f' ∧ i = i' := by
  have mono : ∀ a b, a < b → sys.instId a (sys.cap a) ≤ ((List.range b).map sys.cap).sum := by
    intro a b ab
    have : ((List.range (a + 1)).map sys.cap).sum ≤ ((List.range b).map sys.cap).sum := by
      exact sum_range_mono _ (by omega)
    rw [List.range_succ, List.map_append, List.sum_append] at this
    simpa [instId] using this
  rcases Nat.lt_trichotomy f f' with lt | rfl | gt
  · have := mono f f' lt; simp only [instId] at h this; omega
  · simp only [instId] at h; exact ⟨rfl, by omega⟩
  · have := mono f' f gt; simp only [instId] at h this; omega

omit [DecidableEq F] in
theorem mem_zip {f : Nat} (hf : f < sys.templates.length) {T : Template F} {C : Circuit F}
    (hT : sys.templates[f]? = some T) (hC : sys.circuits[f]? = some C) :
    (T, C) ∈ sys.templates.zip sys.circuits := by
  have hc : f < sys.circuits.length := (List.getElem?_eq_some_iff.mp hC).1
  have eT : sys.templates[f] = T := Option.some.inj ((List.getElem?_eq_getElem hf).symm.trans hT)
  have eC : sys.circuits[f] = C := Option.some.inj ((List.getElem?_eq_getElem hc).symm.trans hC)
  rw [← eT, ← eC, List.mem_iff_getElem]
  exact ⟨f, by simp [hf, hc], by simp⟩

theorem receiver_mem {T : Template F} {C : Circuit F} (mem : (T, C) ∈ sys.templates.zip sys.circuits)
    {g : List (F × F × F × List (Option Nat))} (h0 : (groups T C)[0]? = some g) (two : 2 ≤ g.length)
    (val : Nat → F) (a : Var → F) (recv : Bool) (L : Lookup F) :
    ((groupPart val a recv g L).tag, (groupPart val a recv g L).sub) ∈ sys.receivers := by
  obtain ⟨m, m', r, rfl⟩ : ∃ m m' r, g = m :: m' :: r := by
    match g, two with
    | m :: m' :: r, _ => exact ⟨m, m', r, rfl⟩
  obtain ⟨rest, hgs⟩ : ∃ rest, groups T C = (m :: m' :: r) :: rest := by
    cases h : groups T C with
    | nil => simp [h] at h0
    | cons g' rest => simp only [h, List.getElem?_cons_zero, Option.some.injEq] at h0; exact ⟨rest, by rw [h0]⟩
  simp only [System.receivers, List.mem_filterMap]
  exact ⟨(T, C), mem, by simp only [hgs]; rfl⟩

theorem romReceiver_mem {f : Nat} {T : Template F} {C : Circuit F}
    (hT : sys.templates[f]? = some T) (hC : sys.circuits[f]? = some C)
    {g : List (F × F × F × List (Option Nat))} (h0 : (groups T C)[0]? = some g) (two : 2 ≤ g.length)
    (val : Nat → F) (a : Var → F) (recv : Bool) {L : Lookup F} (hL : C.lookups[0]? = some L)
    (rom : (groupPart val a recv g L).rom = true)
    (addr : L.args[2]? = some (.const (groupPart val a recv g L).key)) :
    (f, ((groupPart val a recv g L).tag, (groupPart val a recv g L).sub),
      (groupPart val a recv g L).key) ∈ sys.romReceivers := by
  obtain ⟨m, m', r, rfl⟩ : ∃ m m' r, g = m :: m' :: r := by
    match g, two with
    | m :: m' :: r, _ => exact ⟨m, m', r, rfl⟩
  obtain ⟨rest, hgs⟩ : ∃ rest, groups T C = (m :: m' :: r) :: rest := by
    cases h : groups T C with
    | nil => simp [h] at h0
    | cons g' rest => simp only [h, List.getElem?_cons_zero, Option.some.injEq] at h0; exact ⟨rest, by rw [h0]⟩
  obtain ⟨ls, hls⟩ : ∃ ls, C.lookups = L :: ls := by
    cases h : C.lookups with
    | nil => simp [h] at hL
    | cons L' ls => simp only [h, List.getElem?_cons_zero, Option.some.injEq] at hL; exact ⟨ls, by rw [hL]⟩
  set key := (groupPart val a recv (m :: m' :: r) L).key
  have romM : Template.messageRom m = true := by simpa [groupPart, Part.rom, Template.messageRom] using rom
  have romAddr : romAddress C = some key := by
    obtain ⟨multiplicity, args⟩ := L
    simp only [romAddress, hls]
    match args, addr with
    | _ :: _ :: .const _ :: _, h => simp at h; rw [h]
  simp only [System.romReceivers, List.mem_filterMap]
  refine ⟨((T, C), f), List.mk_mem_zipIdx_iff_getElem?.mpr ?_, ?_⟩
  · have hf : f < sys.templates.length := (List.getElem?_eq_some_iff.mp hT).1
    have hc : f < sys.circuits.length := (List.getElem?_eq_some_iff.mp hC).1
    rw [List.getElem?_eq_getElem (by simp [hf, hc])]
    simp only [List.getElem_zip, Option.some.injEq, Prod.mk.injEq]
    exact ⟨Option.some.inj ((List.getElem?_eq_getElem hf).symm.trans hT),
      Option.some.inj ((List.getElem?_eq_getElem hc).symm.trans hC)⟩
  · simp only [hgs, romAddr, romM, ↓reduceIte]
    simp [groupPart, romM]

variable {sys} {main : Nat → Nat → F} (logical : sys.Logical main)
include logical

theorem Logical.partAt_spec (keyed : ∀ T C, (T, C) ∈ sys.templates.zip sys.circuits → T.checkGroups C = true)
    (rolesOk : ∀ e ∈ sys.roles, sys.roles.lookup e.1 = some e.2) {f i l : Nat}
    (hf : f < sys.templates.length) (hi : i < sys.cap f) {T : Template F} {C : Circuit F}
    (hT : sys.templates[f]? = some T) (hC : sys.circuits[f]? = some C) (hl : l < C.lookups.length) :
    (((groups T C)[l]'(by rw [groups, splitGroups_length]; exact hl)).map
        (msgEntry (sys.slotValue main f i))).sum = (sys.partAt main (f, i, l)).narrow ∧
      C.lookups[l].entry (sys.wideRow main f i) = (sys.partAt main (f, i, l)).wide ∧
      sys.PartFacts main (f, i, l) := by
  obtain ⟨C', hC', width, checked⟩ := logical.template hf hT
  rw [hC] at hC'
  cases hC'
  have hc : f < sys.circuits.length := (List.getElem?_eq_some_iff.mp hC).1
  have mem : (T, C) ∈ sys.templates.zip sys.circuits := by
    have eT : sys.templates[f] = T := Option.some.inj ((List.getElem?_eq_getElem hf).symm.trans hT)
    have eC : sys.circuits[f] = C := Option.some.inj ((List.getElem?_eq_getElem hc).symm.trans hC)
    rw [← eT, ← eC, List.mem_iff_getElem]
    exact ⟨f, by simp [hf, hc], by simp⟩
  have glen : (groups T C).length = C.lookups.length := by simp [groups, splitGroups_length]
  obtain ⟨flat, sound⟩ := checked.grouped (logical.relations f hf i hi T hT) (keyed T C mem)
  have hg : l < (groups T C).length := by rw [glen]; exact hl
  set g := (groups T C)[l] with hgdef
  have partEq : sys.partAt main (f, i, l) =
      groupPart (sys.slotValue main f i) (sys.wideRow main f i) (l == 0) g C.lookups[l] := by
    simp [partAt, hT, hC, List.getElem?_eq_getElem hg, List.getElem?_eq_getElem hl, hgdef]
  have gs := sound l hl
  have long : 2 ≤ g.length → T.width ≤ C.lookups[l].args.length - 2 := by
    intro two
    obtain ⟨rom, le⟩ := splitGroups_getElem_length T.width T.messages C.lookups l hl
    exact wide_of_groupSize two le
  have tables : GroupTables sys.roleOf sys.arityAt g := by
    constructor
    · intro e he
      apply rolesOk e
      simp only [System.roles, List.mem_flatMap]
      exact ⟨(T, C), mem, g, List.getElem_mem hg, he⟩
    · intro m hm
      apply logical.valid.arities ((m.2.1, m.2.2.1), ((m.2.2.2.drop 1).filterMap id).length)
      simp only [System.arities, List.mem_flatMap, List.mem_map]
      refine ⟨T, List.mem_of_getElem? hT, m, ?_, rfl⟩
      rw [← flat]
      exact List.mem_flatten.mpr ⟨g, List.getElem_mem hg, hm⟩
  have wideEq : sys.wideRow main f i = T.wide (sys.slotValue main f i) := by simp [wideRow, hT]
  rw [← wideEq] at gs
  obtain ⟨n, w, fm, rw', rc, ky⟩ := gs.part long tables
  unfold System.PartFacts
  dsimp only
  rw [partEq]
  refine ⟨n, w, by rw [← width]; exact fm, rw', rc, fun ch l0 => ?_⟩
  subst l0
  obtain ⟨two, key, addr⟩ := ky ch rfl
  have h0 : (groups T C)[0]? = some g := by simp [groups, hgdef, List.getElem?_eq_getElem hg]
  refine ⟨sys.receiver_mem mem h0 two _ _ _ _, fun r => (key r).trans (by simp [slotValue, hT]),
    fun r => sys.romReceiver_mem hT hC h0 two _ _ _ (List.getElem?_eq_getElem hl) r (addr r)⟩

theorem Logical.sums (keyed : ∀ T C, (T, C) ∈ sys.templates.zip sys.circuits → T.checkGroups C = true)
    (rolesOk : ∀ e ∈ sys.roles, sys.roles.lookup e.1 = some e.2) :
    ∑ x ∈ (sys.enumerate sys.lookupCount).toFinset, (sys.partAt main x).narrow = sys.msgSum main ∧
      ∑ x ∈ (sys.enumerate sys.lookupCount).toFinset, (sys.partAt main x).wide =
        sys.wideLedger (sys.wideRow main) := by
  rw [List.sum_toFinset _ (sys.enumerate_nodup _), List.sum_toFinset _ (sys.enumerate_nodup _)]
  unfold System.wideLedger System.msgSum
  rw [logical.valid.lengths.1]
  simp only [System.enumerate, sum_map_flatMap, List.map_map]
  constructor
  all_goals
    apply congrArg List.sum
    apply List.map_congr_left
    intro f hf
    have hf := List.mem_range.mp hf
    try simp only [sum_map_flatMap, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    obtain ⟨T, hT, _, _⟩ := sys.templates_getElem? hf
    obtain ⟨C, hC, _, checked⟩ := logical.template hf hT
    have glen : (groups T C).length = C.lookups.length := by simp [groups, splitGroups_length]
    have lc : sys.lookupCount f = C.lookups.length := by simp [lookupCount, hC]
    have flat : (groups T C).flatten = T.messages := by
      have := keyed T C (sys.mem_zip hf hT hC)
      simp only [Template.checkGroups, Bool.and_eq_true, beq_iff_eq] at this
      exact this.1
    have spec := fun l (hl : l < C.lookups.length) => logical.partAt_spec keyed rolesOk hf hi hT hC hl
    simp only [Function.comp_def, hT, hC, Option.map_some, Option.getD_some, lc]
  · rw [← flat, ← List.flatMap_id, sum_map_flatMap, ← glen]
    exact sum_range_getElem (groups T C) _ _ fun l hl => (spec l (by rw [← glen]; exact hl)).1.symm
  · simp only [Circuit.rowLedger]
    exact sum_range_getElem C.lookups _ _ fun l hl => (spec l hl).2.1.symm

end System

/-- **The ledger argument of a keyed layout.** Slot values under which every
instance's relations hold, and whose message rows balance against the narrow
encodings of external parts `X`, give wide rows that satisfy their circuits
and whose lookups balance against the wide tuples of `X`. Chunked external
receivers must use channels without in-system receivers and have distinct
keys per channel. -/
theorem System.keyed_core {sys : System F} (ok : sys.checkKeyed = true) {bound : Nat}
    (small : SmallCast F bound) (ids : sys.instances ≤ bound)
    (X : List (Part F)) (count : (sys.enumerate sys.lookupCount).length + X.length < bound)
    {main : Nat → Nat → F} (logical : sys.Logical main)
    (msgBal : sys.msgSum main + (X.map Part.narrow).sum = 0)
    (extFormed : ∀ x ∈ X, x.Formed sys.width ∧ x.RowsIn sys.roleOf sys.arityAt)
    (extRecv : ∀ x ∈ X, x.recv = true → x.chunks ≠ [] → (x.tag, x.sub) ∉ sys.receivers)
    (extUnique : ∀ j (hj : j < X.length) j' (hj' : j' < X.length), X[j].recv = true →
      X[j'].recv = true → X[j].chunks ≠ [] → X[j'].chunks ≠ [] → X[j].tag = X[j'].tag →
      X[j].sub = X[j'].sub → X[j].key = X[j'].key → j = j') :
    (∀ f (hf : f < sys.circuits.length), ∀ i < sys.cap f,
        sys.circuits[f].Holds (sys.wideRow main f i)) ∧
      sys.wideLedger (sys.wideRow main) + (X.map Part.wide).sum = 0 := by
  obtain ⟨keyed, rolesOk, romNodup, romCap⟩ := System.checkKeyed_parts ok
  obtain ⟨narrowSum, wideSum⟩ := System.Logical.sums logical keyed rolesOk
  refine ⟨fun f hf i hi => logical.wide_holds hf hi, ?_⟩
  set Isys := (sys.enumerate sys.lookupCount).toFinset with hIsys
  let part : (Nat × Nat × Nat) ⊕ Nat → Part F := fun x => match x with
    | .inl y => sys.partAt main y
    | .inr j => X.getD j zeroPart
  have getD : ∀ j (hj : j < X.length), X.getD j zeroPart = X[j] := fun j hj => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have total : ∀ G : Part F → Ledger F, ∑ x ∈ Isys.disjSum (Finset.range X.length), G (part x) =
      ∑ y ∈ Isys, G (sys.partAt main y) + (X.map G).sum := by
    intro G
    rw [Finset.sum_disjSum, System.finset_sum_range_list]
    congr 1
    exact sum_range_getElem X _ G fun r hr => by simp only [part, getD r hr]
  have zero : ∑ x ∈ Isys.disjSum (Finset.range X.length), (part x).narrow = 0 := by
    rw [total Part.narrow, narrowSum, msgBal]
  have spec : ∀ y ∈ Isys, sys.PartFacts main y := fun y hy => by
    obtain ⟨f, i, l⟩ := y
    obtain ⟨hf, hi, hl⟩ := sys.mem_enumerate.mp (List.mem_toFinset.mp hy)
    obtain ⟨T, hT, _, _⟩ := sys.templates_getElem? hf
    obtain ⟨C, hC, _, _⟩ := logical.template hf hT
    have lc : sys.lookupCount f = C.lookups.length := by simp [System.lookupCount, hC]
    exact (logical.partAt_spec keyed rolesOk hf hi hT hC (by rw [← lc]; exact hl)).2.2
  have formed : ∀ x ∈ Isys.disjSum (Finset.range X.length), (part x).Formed sys.width ∧
      (part x).RowsIn sys.roleOf sys.arityAt := by
    rintro (y | j) hx
    · obtain ⟨fm, rw', _⟩ := spec y (Finset.inl_mem_disjSum.mp hx)
      exact ⟨fm, rw'⟩
    · have hj := Finset.mem_range.mp (Finset.inr_mem_disjSum.mp hx)
      simp only [part, getD j hj]
      exact extFormed _ (List.getElem_mem hj)
  have recvSys : ∀ y ∈ Isys, (sys.partAt main y).recv = true → (sys.partAt main y).chunks ≠ [] →
      ((sys.partAt main y).tag, (sys.partAt main y).sub) ∈ sys.receivers ∧
        ((sys.partAt main y).rom = false → (sys.partAt main y).key = (sys.instId y.1 y.2.1 : F)) ∧
        ((sys.partAt main y).rom = true →
          (y.1, ((sys.partAt main y).tag, (sys.partAt main y).sub), (sys.partAt main y).key) ∈
            sys.romReceivers) ∧
        y.2.2 = 0 ∧ y.1 < sys.templates.length ∧ y.2.1 < sys.cap y.1 := by
    intro y hy r ch
    obtain ⟨_, _, rc, ky⟩ := spec y hy
    have l0 : y.2.2 = 0 := by rw [rc] at r; simpa using r
    obtain ⟨hf, hi, _⟩ := sys.mem_enumerate.mp (List.mem_toFinset.mp hy)
    obtain ⟨m, k, kr⟩ := ky ch l0
    exact ⟨m, k, kr, l0, hf, hi⟩
  have bal := Part.balance (I := Isys.disjSum (Finset.range X.length)) (part := part)
    (role := sys.roleOf) (arity := sys.arityAt)
    (fun x hx => (formed x hx).1) (fun x hx => (formed x hx).2) ?unique small ?short zero
  · rw [total Part.wide, wideSum] at bal
    exact bal
  case short =>
    rw [Finset.card_disjSum, Finset.card_range, hIsys, List.toFinset_card_of_nodup (sys.enumerate_nodup _)]
    exact count
  case unique =>
    rintro (y | j) hx (y' | j') hx' r r' ch ch' tg sb ky
    · have hy := Finset.inl_mem_disjSum.mp hx
      have hy' := Finset.inl_mem_disjSum.mp hx'
      obtain ⟨_, k, kr, l0, hf, hi⟩ := recvSys y hy r ch
      obtain ⟨_, k', kr', l0', hf', hi'⟩ := recvSys y' hy' r' ch'
      simp only [part] at ky tg sb
      have romEq : (sys.partAt main y).rom = (sys.partAt main y').rom := by simp [Part.rom, tg]
      cases hrom : (sys.partAt main y).rom
      · rw [k hrom, k' (romEq ▸ hrom)] at ky
        have lt := sys.instId_lt hf hi
        have lt' := sys.instId_lt hf' hi'
        have := small.inj (by omega) (by omega) ky
        obtain ⟨e1, e2⟩ := sys.instId_inj hi hi' this
        obtain ⟨f, i, l⟩ := y
        obtain ⟨f', i', l'⟩ := y'
        simp only at e1 e2 l0 l0'
        subst e1 e2 l0 l0'
        rfl
      · have m := kr hrom
        have m' := kr' (romEq ▸ hrom)
        rw [tg, sb, ky] at m
        have e := List.inj_on_of_nodup_map romNodup m m' rfl
        simp only [Prod.mk.injEq] at e
        have c1 := romCap _ m
        have c2 := romCap _ m'
        obtain ⟨f, i, l⟩ := y
        obtain ⟨f', i', l'⟩ := y'
        simp only at e c1 c2 hi hi' l0 l0'
        subst l0 l0'
        rw [e.1]
        congr <;> omega
    · have hy := Finset.inl_mem_disjSum.mp hx
      have hj' := Finset.mem_range.mp (Finset.inr_mem_disjSum.mp hx')
      obtain ⟨mem, _⟩ := recvSys y hy r ch
      simp only [part, getD j' hj'] at r' ch' tg sb
      exact absurd (by rw [tg, sb] at mem; exact mem) (extRecv _ (List.getElem_mem hj') r' ch')
    · have hj := Finset.mem_range.mp (Finset.inr_mem_disjSum.mp hx)
      have hy' := Finset.inl_mem_disjSum.mp hx'
      obtain ⟨mem, _⟩ := recvSys y' hy' r' ch'
      simp only [part, getD j hj] at r ch tg sb
      exact absurd (by rw [← tg, ← sb] at mem; exact mem) (extRecv _ (List.getElem_mem hj) r ch)
    · have hj := Finset.mem_range.mp (Finset.inr_mem_disjSum.mp hx)
      have hj' := Finset.mem_range.mp (Finset.inr_mem_disjSum.mp hx')
      simp only [part, getD j hj, getD j' hj'] at r r' ch ch' tg sb ky
      rw [extUnique j hj j' hj' r r' ch ch' tg sb ky]

/-- **Refinement of a keyed layout.** A narrow trace of a system accepted by
`checkKeyed`, whose lookups balance against an external ledger that is the
narrow encoding of external parts `X`, reconstructs wide rows that satisfy
their circuits and whose lookups balance against the wide tuples of `X`.
Chunked external receivers must use channels without in-system receivers and
have distinct keys per channel. -/
theorem System.keyed_sound {sys : System F} (ok : sys.checkKeyed = true) {bound : Nat}
    (small : SmallCast F bound) (sysBound : sys.bound ≤ bound) (ids : sys.instances ≤ bound)
    (X : List (Part F)) (count : (sys.enumerate sys.lookupCount).length + X.length < bound)
    {N : Nat} (tall : sys.places.length ≤ N) {main : Nat → Nat → F}
    (rows : ∀ p < N, Satisfies (narrowCircuit (F := F) sys.width).constraints (sys.assign main p))
    {ext : Ledger F} (extCopy : ∀ L v, ext [(COPY : F), L, v] = 0)
    (balanced : sys.narrowLedger N main + ext = 0)
    (extParts : Finsupp.mapDomain sys.proj ext = (X.map Part.narrow).sum)
    (extFormed : ∀ x ∈ X, x.Formed sys.width ∧ x.RowsIn sys.roleOf sys.arityAt)
    (extRecv : ∀ x ∈ X, x.recv = true → x.chunks ≠ [] → (x.tag, x.sub) ∉ sys.receivers)
    (extUnique : ∀ j (hj : j < X.length) j' (hj' : j' < X.length), X[j].recv = true →
      X[j'].recv = true → X[j].chunks ≠ [] → X[j'].chunks ≠ [] → X[j].tag = X[j'].tag →
      X[j].sub = X[j'].sub → X[j].key = X[j'].key → j = j') :
    (∀ f (hf : f < sys.circuits.length), ∀ i < sys.cap f,
        sys.circuits[f].Holds (sys.wideRow main f i)) ∧
      sys.wideLedger (sys.wideRow main) + (X.map Part.wide).sum = 0 := by
  have valid := sys.valid_of_checkKeyed ok
  obtain ⟨_, msgBal, copies⟩ := System.copy_balance valid valid.width.1 extCopy balanced
  have trace : sys.Trace N main := ⟨valid, small.mono sysBound, tall, rows, copies⟩
  refine System.keyed_core ok small ids X count trace.logical ?_ extFormed extRecv extUnique
  rw [← trace.message_rows, ← extParts, ← Finsupp.mapDomain_add, msgBal, Finsupp.mapDomain_zero]

end Aiur.Tiling
