import Ix.Cert.ClosureSegments
import Ix.Cert.ScheduleOrder
import Ix.Cert.SourceStoredNames
import Ix.Cert.Order

/-! # The compiled closure's segments in quotient Source's order

`ClosureSegments` reads a closure order cut into one segment per read of quotient Source's
trace. This module cuts the compiled closure that way and proves that the cut is a closure
order (`closureOrder_segments`).

**The cut.** Each lowered group of the trace has the records of its names: each name's
published record and that record's block (`groupRecords`). The compile's records have an
order in which none precedes a record it references (`Order.recordsOrdered`, from
`compileReport`'s acyclicity check); a group's segment is that order restricted to the group's
records that no earlier group has (`segmentsOf`). Records within a segment therefore keep the
compile's order; the segments follow the trace.

**Why it is a closure order.**
* *Each record once*: the segments are disjoint pieces of one list without repeats.
* *Every record of the compiled closure*: quotient Source's trace gives every name of the
  closure, aliases and collapsed duplicates included, the quotient key of a name of a lowered
  group at or before its own (`trace_lowered`), and two names with one quotient key have one
  published address (`ReadingKeys.keyAddress_quotientKey`). The edges the fold follows lead
  from a group's records to records of names of the closure (`Layout`).
* *No record before one it references*: a group's records reference names of the group or of
  the groups it references (`Layout.refs`), and the schedule lets a group through only after
  every group it references (`ScheduleOrder.hard_before`); within a group the compile's order
  decides.

`Layout` is the compile's side: where each name's records lie and what they reference. It is
stated against quotient Source's groups, as the fold's provenance gives it per block. -/

namespace Ix.Cert.ClosureLayout

open Ix.LeanIngress
open Ix.Kernel.Reader (State Read)
open Ix.Cert.SourcePrelude (Trace Scheduled)

/-! ## Segments cut from an order -/

/-- **The segments of an order by candidate lists**: the `i`-th lists, in `L`'s order, the
addresses of the `i`-th candidate list that neither `seen` nor an earlier list holds. -/
def segmentsOf (L : List Address) : List (List Address) → List Address → List (List Address)
  | [], _ => []
  | C :: Cs, seen => L.filter (fun a => decide (a ∈ C ∧ a ∉ seen)) :: segmentsOf L Cs (seen ++ C)

theorem segmentsOf_length (L : List Address) :
    ∀ (Cs : List (List Address)) (seen : List Address), (segmentsOf L Cs seen).length = Cs.length
  | [], _ => rfl
  | _ :: Cs, seen => by simp [segmentsOf, segmentsOf_length L Cs]

theorem mem_segmentsOf (L : List Address) :
    ∀ (Cs : List (List Address)) (seen : List Address) (a : Address),
      a ∈ (segmentsOf L Cs seen).flatten ↔ a ∈ L ∧ a ∉ seen ∧ ∃ C ∈ Cs, a ∈ C
  | [], _, a => by simp [segmentsOf]
  | C :: Cs, seen, a => by
    rw [segmentsOf, List.flatten_cons, List.mem_append, List.mem_filter, mem_segmentsOf L Cs]
    simp only [decide_eq_true_eq, List.mem_append, not_or, List.mem_cons, exists_eq_or_imp]
    by_cases hC : a ∈ C
    · simp only [hC, true_and, not_true_eq_false, and_false, false_and, or_false, true_or, and_true]
    · simp only [hC, false_and, and_false, false_or, not_false_eq_true, and_true]

theorem segmentsOf_nodup {L : List Address} (h : L.Nodup) :
    ∀ (Cs : List (List Address)) (seen : List Address), (segmentsOf L Cs seen).flatten.Nodup
  | [], _ => List.nodup_nil
  | C :: Cs, seen => by
    rw [segmentsOf, List.flatten_cons]
    refine List.nodup_append.mpr ⟨h.filter _, segmentsOf_nodup h Cs _, fun a ha b hb e => ?_⟩
    subst e
    have ha' := List.mem_filter.mp ha
    simp only [decide_eq_true_eq] at ha'
    exact ((mem_segmentsOf L Cs _ a).mp hb).2.1 (List.mem_append_right _ ha'.2.1)

/-- **The segments respect a relation the order respects**, when every candidate the relation
leads from leads to a candidate of the same or an earlier list. -/
theorem segmentsOf_pairwise {R : Address → Address → Prop} {L : List Address}
    (hL : L.Pairwise fun a b => ¬ R a b) :
    ∀ (Cs : List (List Address)) (seen : List Address),
      (∀ i (hi : i < Cs.length), ∀ a ∈ Cs[i], ∀ b, R a b →
        b ∈ seen ∨ ∃ j ≤ i, ∃ hj : j < Cs.length, b ∈ Cs[j]) →
      (segmentsOf L Cs seen).flatten.Pairwise fun a b => ¬ R a b
  | [], _, _ => List.Pairwise.nil
  | C :: Cs, seen, back => by
    rw [segmentsOf, List.flatten_cons]
    refine List.pairwise_append.mpr ⟨hL.filter _, segmentsOf_pairwise hL Cs _ ?_, fun a ha b hb hab => ?_⟩
    · intro i hi a ha b hab
      rcases back (i + 1) (by simp; omega) a (by simpa using ha) b hab with h | ⟨j, hj, hjn, hb⟩
      · exact .inl (List.mem_append_left _ h)
      · cases j with
        | zero => exact .inl (List.mem_append_right _ (by simpa using hb))
        | succ j => exact .inr ⟨j, by omega, by simp at hjn; omega, by simpa using hb⟩
    · have ha' := List.mem_filter.mp ha
      simp only [decide_eq_true_eq] at ha'
      have hb' := (mem_segmentsOf L Cs _ b).mp hb
      rcases back 0 (by simp) a (by simpa using ha'.2.1) b hab with h | ⟨j, hj, hjn, hbj⟩
      · exact hb'.2.1 (List.mem_append_left _ h)
      · have : j = 0 := by omega
        subst this
        exact hb'.2.1 (List.mem_append_right _ (by simpa using hbj))

/-! ## The lowered groups of quotient Source's trace -/

/-- A name's quotient key under `ρ`. -/
abbrev qkey (ρ : FiberMap) (n : Ix.Name) : Ix.Kernel.Reader.CName .source := Key.subst ρ (ingressKey n)

/-- The names of the group a scheduled item lowers. -/
abbrev namesAt (g : Graph) (x : Scheduled) : Array Ix.Name := g.groups[x.1.1]!.names

/-- **The lowered items of a trace and what they cover**: they are among the trace's items;
every name of every item has the quotient key of a name of a lowered item at or before it;
every name of a kept block is a lowered item's name's quotient key. -/
structure Lowered (g : Graph) (ρ : FiberMap) (xs ls : List Scheduled) (kb : KeptBlocks) : Prop where
  sub : ls.Sublist xs
  covers : ∀ x ∈ xs, ∀ n ∈ namesAt g x, ∃ y ∈ ls, y.2 ≤ x.2 ∧ ∃ n₀ ∈ namesAt g y, qkey ρ n = qkey ρ n₀
  kept : ∀ k, (kb.blockOf[k]?).isSome = true → ∃ y ∈ ls, ∃ n₀ ∈ namesAt g y, k = qkey ρ n₀

/-- **The lowered items' steps**, one per read: each item's conversion, lowering at the state
the reads before it leave, collapse and step. -/
abbrev Steps (g : Graph) (start : State .source) (ls : List Scheduled) (rs : List (Read .source)) : Prop :=
  ls.length = rs.length ∧ ∀ ℓ y r, ls[ℓ]? = some y → rs[ℓ]? = some r →
    ∃ conv raw s s' kb kb' dropped, y.1.2 = .ok conv ∧
      lower ((rs.take ℓ).foldl State.commit start) conv = .ok raw ∧
      collapseRead s g.groups[y.1.1]!.name raw = (s', .ok (r, dropped)) ∧
      collapseGroup ((rs.take ℓ).foldl State.commit start) s kb g.groups[y.1.1]!.name y.2 y.1.2 =
        .lowered s' kb' r dropped

/-- The keys a quotient renaming gives a converted group are its keys renamed. -/
theorem convKeys_quotient_inv {ρ : FiberMap} {c : Converted} {k : Ix.Kernel.Reader.CName .source}
    (hk : k ∈ SourceDeclares.convKeys (c.quotient ρ)) :
    ∃ k' ∈ SourceDeclares.convKeys c, k = Key.subst ρ k' := by
  cases c with
  | «inductive» rb =>
    change k ∈ BlockRead.names (BlockRead.canon (BlockRead.substKeys ρ rb)) at hk
    unfold BlockRead.names at hk
    rcases List.mem_append.mp hk with hk | hk
    · rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
        obtain ⟨e1, he1, rfl⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp he)
        obtain ⟨⟨c, p, i⟩, he0, rfl⟩ := Array.mem_map.mp he1
        exact ⟨c.name, List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr
          ⟨(c, p, i), Array.mem_toList_iff.mpr he0, rfl⟩)), rfl⟩
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
        obtain ⟨e1, he1, rfl⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp he)
        obtain ⟨⟨c, p, f⟩, he0, rfl⟩ := Array.mem_map.mp he1
        exact ⟨c.name, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
          ⟨(c, p, f), Array.mem_toList_iff.mpr he0, rfl⟩)), rfl⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
      obtain ⟨e1, he1, rfl⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp he)
      obtain ⟨⟨c, rc, rules⟩, he0, rfl⟩ := Array.mem_map.mp he1
      exact ⟨c.name, List.mem_append_right _ (List.mem_map.mpr
        ⟨(c, rc, rules), Array.mem_toList_iff.mpr he0, rfl⟩),
        SourceDeclares.canonRec_name _ rc _⟩
  | definitions ms =>
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hk
    obtain ⟨m1, hm1, rfl⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp hm)
    obtain ⟨m0, hm0, rfl⟩ := Array.mem_map.mp hm1
    exact ⟨m0.cv.name, List.mem_map.mpr ⟨m0, Array.mem_toList_iff.mpr hm0, rfl⟩, rfl⟩
  | «axiom» cv =>
    rw [List.mem_singleton.mp hk]
    exact ⟨cv.name, List.mem_singleton.mpr rfl, rfl⟩
  | quot q cv =>
    rw [List.mem_singleton.mp hk]
    exact ⟨cv.name, List.mem_singleton.mpr rfl, rfl⟩

/-- Every key of a converted group whose entries carry `K`-keys is a `K`-key. -/
theorem convertedKeys_mem {K : Ix.Kernel.Reader.CName .source → Prop} {c : Converted}
    (h : ReaderUnits.ConvertedKeys K c) : ∀ k ∈ SourceDeclares.convKeys c, K k := by
  cases c with
  | «inductive» rb =>
    obtain ⟨tk, ck, rk⟩ := h
    intro k hk
    change k ∈ BlockRead.names rb at hk
    unfold BlockRead.names at hk
    rcases List.mem_append.mp hk with hk | hk
    · rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
        exact tk e (Array.mem_toList_iff.mp he)
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
        exact ck e (Array.mem_toList_iff.mp he)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
      exact rk e (Array.mem_toList_iff.mp he)
  | definitions ms =>
    intro k hk
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hk
    exact h m (Array.mem_toList_iff.mp hm)
  | «axiom» cv =>
    intro k hk
    rw [List.mem_singleton.mp hk]
    exact h
  | quot q cv =>
    intro k hk
    rw [List.mem_singleton.mp hk]
    exact h

theorem getElem!_of_getElem? {xs : Array Group} {i : Nat} {v : Group} (h : xs[i]? = some v) : xs[i]! = v := by
  simp [getElem!_def, h]

/-- A scheduled item's conversion that succeeds is its group's, renamed. -/
theorem scheduled_conversion {ρ : FiberMap} {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {x : Scheduled} {conv : Converted}
    (hx : x ∈ (scheduleOf (graphCollapsed ρ hints env blocks)).zipIdx.toList) (hc : x.1.2 = .ok conv) :
    ∃ gr c, (graphCollapsed ρ hints env blocks).groups[x.1.1]? = some gr ∧ convert gr = .ok c ∧
      conv = (c.withHints hints).quotient ρ := by
  have hx1 : x.1 ∈ (scheduleOf (graphCollapsed ρ hints env blocks)).toList :=
    List.fst_mem_of_mem_zipIdx (by simpa only [Array.toList_zipIdx] using hx)
  exact SourceTrace.graph_conversion (ReaderUnits.scheduleOf_ok hx1 hc)

/-- **Quotient Source's trace covers every name by a lowered item at or before it.** -/
theorem trace_lowered {ρ : FiberMap} {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {start st : State .source}
    {xs : List Scheduled} {rs : List (Read .source)} {s : CollapseState} {kb : KeptBlocks}
    (h : Trace (graphCollapsed ρ hints env blocks) start xs rs st s kb) :
    (∀ x ∈ xs, x ∈ (scheduleOf (graphCollapsed ρ hints env blocks)).zipIdx.toList) →
    xs.map (·.2) = List.range xs.length →
    ∃ ls, Lowered (graphCollapsed ρ hints env blocks) ρ xs ls kb ∧
      Steps (graphCollapsed ρ hints env blocks) start ls rs := by
  induction h with
  | nil =>
    intro _ _
    exact ⟨[], ⟨List.Sublist.slnil, (fun x hx => nomatch hx), fun k hk => by simp at hk⟩,
      rfl, fun ℓ y r hy => by simp at hy⟩
  | @«alias» xs rs st s kb x i ht hcol ih =>
    intro inside hidx
    rw [List.map_append, List.length_append, List.length_singleton, List.range_succ] at hidx
    obtain ⟨hpre, hlast⟩ := List.append_inj hidx (by simp)
    obtain ⟨ls, low, steps⟩ := ih (fun y hy => inside y (List.mem_append_left _ hy)) hpre
    refine ⟨ls, ⟨low.sub.trans (List.sublist_append_left _ _), fun y hy n hn => ?_, low.kept⟩, steps⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact low.covers y hy n hn
    · rw [List.mem_singleton] at hy
      subst hy
      obtain ⟨rb, hc, ha⟩ := SourceDeclares.collapseGroup_alias_inv hcol
      obtain ⟨gr, c, hgr, hconv, heq⟩ := scheduled_conversion (inside y (List.mem_append_right _
        List.mem_cons_self)) hc
      have hnames : namesAt (graphCollapsed ρ hints env blocks) y = gr.names := by
        unfold namesAt
        rw [getElem!_of_getElem? hgr]
      rw [hnames] at hn
      have hk : qkey ρ n ∈ SourceDeclares.convKeys (.inductive rb) := by
        rw [heq]
        exact SourceDeclares.convKeys_quotient (by
          rw [SourceDeclares.convKeys_withHints hints]
          exact SourceDeclares.convert_declares hconv n hn)
      have hkept := SourceDeclares.alias_names ha _ hk
      obtain ⟨y', hy', n₀, hn₀, hkey⟩ := low.kept _ (by rw [hkept]; rfl)
      have hlt : y'.2 < xs.length := by
        have : y'.2 ∈ xs.map (·.2) := List.mem_map_of_mem (low.sub.subset hy')
        rw [hpre] at this
        exact List.mem_range.mp this
      have hyx : y.2 = xs.length := by simpa using hlast
      exact ⟨y', hy', by omega, n₀, hn₀, hkey⟩
  | @lowered xs rs st s kb x s' kb' conv raw r dropped ht hc hl hr hcol ih =>
    intro inside hidx
    rw [List.map_append, List.length_append, List.length_singleton, List.range_succ] at hidx
    obtain ⟨hpre, -⟩ := List.append_inj hidx (by simp)
    obtain ⟨ls, low, hlen, steps⟩ := ih (fun y hy => inside y (List.mem_append_left _ hy)) hpre
    have hxin := inside x (List.mem_append_right _ List.mem_cons_self)
    obtain ⟨gr, c, hgr, hconv, heq⟩ := scheduled_conversion hxin hc
    have hnames : namesAt (graphCollapsed ρ hints env blocks) x = gr.names := by
      unfold namesAt
      rw [getElem!_of_getElem? hgr]
    refine ⟨ls ++ [x], ⟨low.sub.append (List.Sublist.refl _), fun y hy n hn => ?_, fun k hk => ?_⟩,
      by simp [hlen], fun ℓ y r' hy hr' => ?_⟩
    · rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨y', hy', hle, n₀, hn₀, hkey⟩ := low.covers y hy n hn
        exact ⟨y', List.mem_append_left _ hy', hle, n₀, hn₀, hkey⟩
      · rw [List.mem_singleton] at hy
        subst hy
        exact ⟨y, List.mem_append_right _ List.mem_cons_self, Nat.le_refl _, n, hn, rfl⟩
    · obtain ⟨conv', hc', hkb⟩ := SourceDeclares.collapseGroup_lowered_kb hcol
      rw [hc] at hc'
      cases hc'
      have old : (kb.blockOf[k]?).isSome = true → ∃ y ∈ ls ++ [x], ∃ n₀ ∈ namesAt _ y, k = qkey ρ n₀ :=
        fun h => by
          obtain ⟨y, hy, n₀, hn₀, hkey⟩ := low.kept k h
          exact ⟨y, List.mem_append_left _ hy, n₀, hn₀, hkey⟩
      subst hkb
      cases hcv : conv with
      | «inductive» rb =>
        rw [hcv] at hk
        rcases SourceDeclares.push_blockOf hk with hk | hk
        · have hk' : k ∈ SourceDeclares.convKeys ((c.withHints hints).quotient ρ) := by
            rw [← heq, hcv]
            exact hk
          obtain ⟨k', hkc, rfl⟩ := convKeys_quotient_inv hk'
          rw [SourceDeclares.convKeys_withHints hints] at hkc
          obtain ⟨n, hn, rfl⟩ := convertedKeys_mem (ReaderUnits.convert_keys hconv) k' hkc
          exact ⟨x, List.mem_append_right _ List.mem_cons_self, n, by rw [hnames]; exact hn, rfl⟩
        · exact old hk
      | definitions ms => rw [hcv] at hk; exact old hk
      | «axiom» cv => rw [hcv] at hk; exact old hk
      | quot q cv => rw [hcv] at hk; exact old hk
    · by_cases hℓ : ℓ < ls.length
      · rw [List.getElem?_append_left hℓ] at hy
        rw [List.getElem?_append_left (hlen ▸ hℓ)] at hr'
        have htake : (rs ++ [r]).take ℓ = rs.take ℓ := List.take_append_of_le_length (by omega)
        rw [htake]
        exact steps ℓ y r' hy hr'
      · have hℓ' : ℓ = ls.length := by
          have := (List.getElem?_eq_some_iff.mp hy).1
          simp at this
          omega
        subst hℓ'
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hy
        rw [hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hr'
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy hr'
        subst hy hr'
        have htake : (rs ++ [r]).take ls.length = rs := by rw [hlen]; simp
        rw [htake, ← ht.fold]
        exact ⟨conv, raw, s, s', kb, kb', dropped, hc, hl, hr, hcol⟩

/-! ## The compiled closure's records -/

/-- The address the artifact publishes a name at. -/
def addrOf (ixe : Ixon.Env) (n : Ix.Name) : Option Address := (ixe.named.get? n).map (·.addr)

/-- The block a record resolves to: a projection's block, otherwise the record itself. -/
def blockAt (ixe : Ixon.Env) (a : Address) : Address :=
  match recordAt ixe a with
  | some c => ownerOf a c
  | none => a

/-- **A name's records**: its published record and that record's block. -/
def nameRecords (ixe : Ixon.Env) (n : Ix.Name) : List Address :=
  match addrOf ixe n with
  | some a => [a, blockAt ixe a]
  | none => []

/-- A group's records: its names' records. -/
def groupRecords (ixe : Ixon.Env) (names : Array Ix.Name) : List Address :=
  names.toList.flatMap (nameRecords ixe)

/-- **The compile's layout of the closure against quotient Source's groups**, as the fold
gives it block by block. For every name `n` of a group `gr` at index `i` of the graph `g`:
* `block`: the block of `n`'s published record is stored and is its own block;
* `refs`: every stored reference of one of `n`'s records is the published address of a name of
  `gr` or of a group that `gr` references (`Graph.hard`);
* `extra`: the edges the fold follows without a reference (a `Nat` operation's ground, a
  literal's support, an inductive block's recursors) lead to records of names of groups. -/
structure Layout (ixe : Ixon.Env) (g : Graph) : Prop where
  block : ∀ (i : Nat) (gr : Group), g.groups[i]? = some gr → ∀ n ∈ gr.names, ∀ a, addrOf ixe n = some a →
    ∃ c, recordAt ixe (blockAt ixe a) = some c ∧ ownerOf (blockAt ixe a) c = blockAt ixe a
  refs : ∀ (i : Nat) (gr : Group), g.groups[i]? = some gr → ∀ n ∈ gr.names, ∀ a ∈ nameRecords ixe n, ∀ c,
    recordAt ixe a = some c → ∀ r ∈ c.refs, ixe.consts.contains r = true →
      ∃ m, addrOf ixe m = some r ∧
        (m ∈ gr.names ∨ ∃ j ∈ g.hard[i]!, ∃ gr' : Group, g.groups[j]? = some gr' ∧ m ∈ gr'.names)
  extra : ∀ (i : Nat) (gr : Group), g.groups[i]? = some gr → ∀ n ∈ gr.names, ∀ a ∈ nameRecords ixe n, ∀ b,
    (GroundEdge ixe a b ∨ RecursorEdge ixe a b) →
      ∃ (j : Nat) (gr' : Group), g.groups[j]? = some gr' ∧ ∃ m ∈ gr'.names, b ∈ nameRecords ixe m

/-- Quotient Source's graph of a closure at a compiled artifact. -/
abbrev quotientGraph (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint) (sub : Ix.Environment) :
    Graph :=
  graphCollapsed (fiberAliasAt ixe (roleAtMap t)) hints sub (blocksOf sub)

theorem recordAt_contains {ixe : Ixon.Env} {a : Address} {c : Ixon.Constant} (h : recordAt ixe a = some c) :
    ixe.consts.contains a = true := by
  unfold recordAt at h
  cases hg : ixe.consts.get? a with
  | none => rw [hg] at h; cases h
  | some lc => rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hg]; rfl

theorem contains_of_get {ixe : Ixon.Env} {a : Address} {lc : Ixon.LazyConstant} (h : ixe.consts.get? a = some lc) :
    ixe.consts.contains a = true := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, h]; rfl

/-- **The compiled closure in quotient Source's order is a closure order.** For quotient
Source's trace of an accepted closure and the compile's layout of it, the lowered items of the
trace (`Steps`: one per read) cut the compile's record order into segments, one per read,
that list the compiled closure once each, with no record before one it references. -/
theorem closureOrder_segments {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {start fin : State .source} {rs : List (Read .source)} {s : CollapseState} {kb : KeptBlocks}
    (htrace : Trace (quotientGraph ixe t hints sub) start
      (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList rs fin s kb)
    (layout : Layout ixe (quotientGraph ixe t hints sub)) :
    ∃ (ls : List Scheduled) (L : List Address),
      Steps (quotientGraph ixe t hints sub) start ls rs ∧
      L.Nodup ∧ (∀ a, a ∈ L ↔ ixe.consts.contains a = true) ∧ L.Pairwise (fun a b => ¬ RecordRef ixe a b) ∧
      ClosureOrder ixe (Seed ixe sub)
        (segmentsOf L (ls.map fun y => groupRecords ixe (namesAt (quotientGraph ixe t hints sub) y)) []).flatten := by
  have hcomp : compile env = .ok ixe := by unfold compile; rw [P.compiled]; rfl
  obtain ⟨L, hnd, hmem, hpw⟩ := Order.recordsOrdered hcomp
  have hxs : ((scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList).map (·.2) =
      List.range (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList.length := by
    rw [Array.toList_zipIdx, List.zipIdx_map_snd, List.length_zipIdx, List.range_eq_range']
  obtain ⟨ls, low, steps⟩ := trace_lowered htrace (fun _ h => h) hxs
  obtain ⟨-, declared⟩ := SourceDeclares.trace_declares htrace
  -- the trace's items are groups that convert
  have groupOf : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ gr c,
      (quotientGraph ixe t hints sub).groups[x.1.1]? = some gr ∧ convert gr = .ok c ∧
        namesAt (quotientGraph ixe t hints sub) x = gr.names := by
    intro x hx
    obtain ⟨conv, hc, -⟩ := declared x hx
    obtain ⟨gr, c, hgr, hconv, -⟩ := scheduled_conversion hx hc
    exact ⟨gr, c, hgr, hconv, by unfold namesAt; rw [getElem!_of_getElem? hgr]⟩
  -- a converted group's names are constants of the closure, stored under those names
  have stored : ∀ (i : Nat) (gr : Group) (c : Converted), (quotientGraph ixe t hints sub).groups[i]? = some gr → convert gr = .ok c →
      ∀ n ∈ gr.names, ∃ ci, (n, ci) ∈ sub.consts.toList := by
    intro i gr c hgr hc n hn
    have hmemg : gr ∈ groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
    obtain ⟨k, ci, hk, hown⟩ := SourceStoredNames.groupsOf_stored sub _ gr hmemg c hc n hn
    have hname := inputsNamed P.compiled k ci (SourceStoredNames.stored_input P hk)
    rw [hown] at hname
    subst hname
    exact ⟨ci, hk⟩
  -- two such names with one quotient key have one published address
  have addrEq : ∀ (i : Nat) (gr : Group) (c : Converted), (quotientGraph ixe t hints sub).groups[i]? = some gr → convert gr = .ok c →
      ∀ n ∈ gr.names, ∀ (i' : Nat) (gr' : Group) (c' : Converted), (quotientGraph ixe t hints sub).groups[i']? = some gr' →
      convert gr' = .ok c' → ∀ n' ∈ gr'.names,
      qkey (fiberAliasAt ixe (roleAtMap t)) n = qkey (fiberAliasAt ixe (roleAtMap t)) n' →
      addrOf ixe n = addrOf ixe n' := by
    intro i gr c hgr hc n hn i' gr' c' hgr' hc' n' hn' hkey
    obtain ⟨ci, hci⟩ := stored i gr c hgr hc n hn
    obtain ⟨ci', hci'⟩ := stored i' gr' c' hgr' hc' n' hn'
    obtain ⟨named, hm, hget⟩ := SourceStoredNames.stored_published P hci
    obtain ⟨named', hm', hget'⟩ := SourceStoredNames.stored_published P hci'
    have e1 : keyAddress ixe t (qkey (fiberAliasAt ixe (roleAtMap t)) n) = some named.addr :=
      ReadingKeys.keyAddress_quotientKey (defaultTable_check P.table) P.bound P.agree hm
    have e2 : keyAddress ixe t (qkey (fiberAliasAt ixe (roleAtMap t)) n') = some named'.addr :=
      ReadingKeys.keyAddress_quotientKey (defaultTable_check P.table) P.bound P.agree hm'
    rw [hkey, e2] at e1
    unfold addrOf
    rw [hget, hget', Option.map_some, Option.map_some, e1]
  -- every name of a trace item has the records of a name of a lowered item at or before it
  have covered : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∀ m ∈ namesAt (quotientGraph ixe t hints sub) x, ∃ y ∈ ls, y.2 ≤ x.2 ∧
        ∃ n₀ ∈ namesAt (quotientGraph ixe t hints sub) y, nameRecords ixe m = nameRecords ixe n₀ := by
    intro x hx m hm
    obtain ⟨y, hy, hle, n₀, hn₀, hkey⟩ := low.covers x hx m hm
    obtain ⟨gr, c, hgr, hc, hnm⟩ := groupOf x hx
    obtain ⟨gr', c', hgr', hc', hnm'⟩ := groupOf y (low.sub.subset hy)
    refine ⟨y, hy, hle, n₀, hn₀, ?_⟩
    unfold nameRecords
    rw [addrEq _ gr c hgr hc m (hnm ▸ hm) _ gr' c' hgr' hc' n₀ (hnm' ▸ hn₀) hkey]
  -- every group is scheduled
  have scheduled : ∀ (j : Nat) (gr : Group), (quotientGraph ixe t hints sub).groups[j]? = some gr →
      ∃ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, x.1.1 = j := by
    intro j gr hgr
    obtain ⟨c, hcmem⟩ := scheduleOf_complete _ (Array.getElem?_eq_some_iff.mp hgr).1
    obtain ⟨q, hq, hqeq⟩ := Array.getElem_of_mem hcmem
    exact ⟨((j, c), q), Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr (by simp [hq, hqeq])), rfl⟩
  -- the order lists groups only
  have inRange : ∀ i ∈ orderOf (quotientGraph ixe t hints sub),
      i < (quotientGraph ixe t hints sub).groups.size := by
    intro i hi
    obtain ⟨p, hp, hpe⟩ := Array.getElem_of_mem hi
    have hs : (scheduleOf (quotientGraph ixe t hints sub))[p]? =
        some (i, ScheduleOrder.admit (quotientGraph ixe t hints sub)
          (ScheduleOrder.positions (quotientGraph ixe t hints sub)) i) := by
      rw [ScheduleOrder.scheduleOf_eq, Array.getElem?_map, Array.getElem?_eq_getElem hp, hpe]
      rfl
    obtain ⟨gr, -, hgr, -, -⟩ := groupOf ((i, _), p)
      (Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr hs))
    exact (Array.getElem?_eq_some_iff.mp hgr).1
  -- the lowered items in order
  have lsInc : ls.Pairwise (fun a b => a.2 < b.2) := by
    have hrange := List.pairwise_lt_range (n := (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList.length)
    rw [← hxs] at hrange
    exact List.Pairwise.sublist low.sub (List.pairwise_map.mp hrange)
  -- the records of a trace item's names are in the compiled closure
  have seedOf : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∀ n ∈ namesAt (quotientGraph ixe t hints sub) x, ∀ a, addrOf ixe n = some a →
        Seed ixe sub a ∧ ixe.consts.contains a = true := by
    intro x hx n hn a ha
    obtain ⟨gr, c, hgr, hc, hnm⟩ := groupOf x hx
    obtain ⟨ci, hci⟩ := stored _ gr c hgr hc n (hnm ▸ hn)
    obtain ⟨named, hm, hget⟩ := SourceStoredNames.stored_published P hci
    have haddr : named.addr = a := by
      unfold addrOf at ha
      rw [hget, Option.map_some] at ha
      exact Option.some.inj ha
    refine ⟨⟨n, ci, named, SourceStoredNames.stored_get hci, hget, haddr⟩, ?_⟩
    have henv := SourceStoredNames.stored_get (SourceStoredNames.stored_input P hci)
    obtain ⟨lc, hlc, -⟩ := publishedReadable P.compiled n named hm (by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, henv]; rfl)
    rw [← haddr]
    exact contains_of_get hlc
  have reachOf : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∀ n ∈ namesAt (quotientGraph ixe t hints sub) x, ∀ a ∈ nameRecords ixe n,
        CompiledReach ixe (Seed ixe sub) a := by
    intro x hx n hn a ha
    unfold nameRecords at ha
    cases hn' : addrOf ixe n with
    | none => rw [hn'] at ha; cases ha
    | some p =>
      rw [hn'] at ha
      obtain ⟨seed, hcont⟩ := seedOf x hx n hn p hn'
      have hp : CompiledReach ixe (Seed ixe sub) p := .seed seed hcont
      rcases List.mem_cons.mp ha with hap | ha
      · rw [hap]; exact hp
      · rw [List.mem_singleton] at ha
        rw [ha]
        unfold blockAt
        cases hr : recordAt ixe p with
        | none => exact hp
        | some c =>
          show CompiledReach ixe (Seed ixe sub) (ownerOf p c)
          by_cases he : ownerOf p c = p
          · rw [he]; exact hp
          · exact .step hp ⟨c, hr, .inl ⟨rfl, he⟩⟩
  -- a record of the compiled closure is stored and is a record of a lowered item's name
  have reached : ∀ a, CompiledReach ixe (Seed ixe sub) a → ixe.consts.contains a = true ∧
      ∃ y ∈ ls, ∃ n ∈ namesAt (quotientGraph ixe t hints sub) y, a ∈ nameRecords ixe n := by
    -- a record of a name of any group
    have ofGroup : ∀ (j : Nat) (gr : Group), (quotientGraph ixe t hints sub).groups[j]? = some gr → ∀ m ∈ gr.names,
        ∀ b ∈ nameRecords ixe m, ∃ y ∈ ls, ∃ n ∈ namesAt (quotientGraph ixe t hints sub) y,
          b ∈ nameRecords ixe n := by
      intro j gr hgr m hm b hb
      obtain ⟨x, hx, hxj⟩ := scheduled j gr hgr
      have hnames : namesAt (quotientGraph ixe t hints sub) x = gr.names := by
        unfold namesAt; rw [hxj, getElem!_of_getElem? hgr]
      obtain ⟨y, hy, -, n₀, hn₀, hrecs⟩ := covered x hx m (hnames ▸ hm)
      exact ⟨y, hy, n₀, hn₀, hrecs ▸ hb⟩
    intro a h
    induction h with
    | @seed a hs hc =>
      obtain ⟨n, ci, named, hget, hnamed, rfl⟩ := hs
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hget
      obtain ⟨k, hnk, hk⟩ := hget
      obtain ⟨gr, hgr, hkn⟩ := SourceDeclares.stored_grouped sub (blocksOf sub) hk
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hgr
      have hgi : (quotientGraph ixe t hints sub).groups[i]? = some (groupsOf sub (blocksOf sub))[i] :=
        Array.getElem?_eq_getElem hi
      have hka : addrOf ixe k = some named.addr := by
        unfold addrOf
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr (BEq.symm hnk),
          ← Std.HashMap.get?_eq_getElem?, hnamed, Option.map_some]
      exact ⟨hc, ofGroup i _ hgi k hkn named.addr (by unfold nameRecords; rw [hka]; exact List.mem_cons_self)⟩
    | @step a b ha hedge ih =>
      obtain ⟨-, y, hy, n, hn, hrec⟩ := ih
      obtain ⟨gr, c', hgr, -, hnm⟩ := groupOf y (low.sub.subset hy)
      rw [hnm] at hn
      obtain ⟨c, hc, hedge⟩ := hedge
      rcases hedge with ⟨hown, hne⟩ | ⟨hrefs, hcb⟩
      · unfold nameRecords at hrec
        cases hp : addrOf ixe n with
        | none => rw [hp] at hrec; cases hrec
        | some p =>
          rw [hp] at hrec
          obtain ⟨cb, hcb, hself⟩ := layout.block _ gr hgr n hn p hp
          rcases List.mem_cons.mp hrec with hap | hrec
          · rw [hap] at hc hown
            have hb : b = blockAt ixe p := by unfold blockAt; rw [hc]; exact hown.symm
            refine ⟨hb ▸ recordAt_contains hcb, y, hy, n, hnm ▸ hn, ?_⟩
            unfold nameRecords
            rw [hp, hb]
            exact List.mem_cons_of_mem _ List.mem_cons_self
          · rw [List.mem_singleton] at hrec
            rw [hrec, hcb] at hc
            cases hc
            rw [hrec] at hown hne
            exact absurd (hown.symm.trans hself) hne
      · obtain ⟨m, hm, hwhere⟩ := layout.refs _ gr hgr n hn a hrec c hc b
          (Array.mem_of_contains_eq_true hrefs) hcb
        refine ⟨hcb, ?_⟩
        have hbm : b ∈ nameRecords ixe m := by
          unfold nameRecords; rw [hm]; exact List.mem_cons_self
        rcases hwhere with hm' | ⟨j, -, gr', hgr', hm'⟩
        · exact ofGroup _ gr hgr m hm' b hbm
        · exact ofGroup j gr' hgr' m hm' b hbm
    | @ground a b ha hedge ih =>
      obtain ⟨-, y, hy, n, hn, hrec⟩ := ih
      obtain ⟨gr, c', hgr, -, hnm⟩ := groupOf y (low.sub.subset hy)
      obtain ⟨j, gr', hgr', m, hm, hb⟩ := layout.extra _ gr hgr n (hnm ▸ hn) a hrec b (.inl hedge)
      exact ⟨hedge.1, ofGroup j gr' hgr' m hm b hb⟩
    | @recursor a b ha hedge ih =>
      obtain ⟨-, y, hy, n, hn, hrec⟩ := ih
      obtain ⟨gr, c', hgr, -, hnm⟩ := groupOf y (low.sub.subset hy)
      obtain ⟨j, gr', hgr', m, hm, hb⟩ := layout.extra _ gr hgr n (hnm ▸ hn) a hrec b (.inr hedge)
      exact ⟨hedge.1, ofGroup j gr' hgr' m hm b hb⟩
  refine ⟨ls, L, steps, hnd, hmem, hpw, segmentsOf_nodup hnd _ _, fun a => ?_, ?_⟩
  · rw [mem_segmentsOf]
    constructor
    · rintro ⟨-, -, C, hC, ha⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hC
      obtain ⟨n, hn, ha⟩ := List.mem_flatMap.mp ha
      exact reachOf y (low.sub.subset hy) n (Array.mem_toList_iff.mp hn) a ha
    · intro h
      obtain ⟨hc, y, hy, n, hn, ha⟩ := reached a h
      exact ⟨(hmem a).mpr hc, List.not_mem_nil, _, List.mem_map_of_mem hy,
        List.mem_flatMap.mpr ⟨n, Array.mem_toList_iff.mpr hn, ha⟩⟩
  · refine segmentsOf_pairwise hpw _ _ fun i hi a ha b hab => .inr ?_
    rw [List.length_map] at hi
    rw [List.getElem_map] at ha
    obtain ⟨n, hn, hrec⟩ := List.mem_flatMap.mp ha
    have hyx : ls[i] ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList :=
      low.sub.subset (List.getElem_mem hi)
    obtain ⟨gr, c', hgr, -, hnm⟩ := groupOf _ hyx
    obtain ⟨c, hc, r, hr, cr, hcr, hown, -⟩ := hab
    obtain ⟨m, hm, hwhere⟩ := layout.refs _ gr hgr n (hnm ▸ Array.mem_toList_iff.mp hn) a hrec c hc r hr
      (recordAt_contains hcr)
    have hbm : b ∈ nameRecords ixe m := by
      unfold nameRecords
      rw [hm]
      refine List.mem_cons_of_mem _ (List.mem_singleton.mpr ?_)
      unfold blockAt
      rw [hcr]
      exact hown.symm
    rcases hwhere with hm' | ⟨j, hj, gr', hgr', hm'⟩
    · refine ⟨i, Nat.le_refl _, by simpa using hi, ?_⟩
      rw [List.getElem_map]
      exact List.mem_flatMap.mpr ⟨m, Array.mem_toList_iff.mpr (hnm ▸ hm'), hbm⟩
    · obtain ⟨conv, hconvy, -⟩ := declared _ hyx
      have hsched : (scheduleOf (quotientGraph ixe t hints sub))[ls[i].2]? = some ls[i].1 :=
        Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp hyx)
      obtain ⟨q, hq, z, hz, hzj⟩ := ScheduleOrder.hard_before inRange hsched hconvy hj
        (Array.getElem?_eq_some_iff.mp hgr').1
      have hx' : (z, q) ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList :=
        Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr hz)
      have hnames : namesAt (quotientGraph ixe t hints sub) (z, q) = gr'.names := by
        unfold namesAt; dsimp only; rw [hzj, getElem!_of_getElem? hgr']
      obtain ⟨y', hy', hle, n₀, hn₀, hrecs⟩ := covered (z, q) hx' m (hnames ▸ hm')
      obtain ⟨j', hj', rfl⟩ := List.mem_iff_getElem.mp hy'
      have hj'i : j' ≤ i := by
        refine Nat.le_of_not_lt fun hgt => ?_
        have := List.pairwise_iff_getElem.mp lsInc i j' hi hj' hgt
        simp only at hle
        omega
      refine ⟨j', hj'i, by simpa using hj', ?_⟩
      rw [List.getElem_map]
      exact List.mem_flatMap.mpr ⟨n₀, Array.mem_toList_iff.mpr hn₀, hrecs ▸ hbm⟩

/--
info: 'Ix.Cert.ClosureLayout.closureOrder_segments' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closureOrder_segments

/-- **The reader's units from the layout**: for an accepted closure whose compiled records lie as
`Layout` says, quotient Source's trace has the reader's units once the segments that
`closureOrder_segments` cuts hold stored canonical records and read as the trace's reads
(`ClosureSegments.SegmentsRead`). -/
theorem unitsRead_of_layout {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {preA : Ix.Kernel.Reader.Prelude .anon} {b : Ix.RoleEvidence.Bundle} {pre : Ix.Kernel.Reader.Prelude .source}
    {rs : List (Read .source)} {fin : State .source} {s : CollapseState} {kb : KeptBlocks}
    (htrace : Trace (quotientGraph ixe t hints sub) pre.state
      (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList rs fin s kb)
    (layout : Layout ixe (quotientGraph ixe t hints sub))
    (reads : ∀ (ls : List Scheduled) (L : List Address), Steps (quotientGraph ixe t hints sub) pre.state ls rs →
      L.Nodup → (∀ a, a ∈ L ↔ ixe.consts.contains a = true) → L.Pairwise (fun a b => ¬ RecordRef ixe a b) →
      Stream.StoredCanonical ixe
          (segmentsOf L (ls.map fun y => groupRecords ixe (namesAt (quotientGraph ixe t hints sub) y)) []).flatten ∧
        ClosureSegments.SegmentsRead (evAddr ixe b) (Ix.Kernel.KeyScope.ofId (QRepAt ixe (roleAtMap t)))
          (closureContext ixe t preA
            (segmentsOf L (ls.map fun y => groupRecords ixe (namesAt (quotientGraph ixe t hints sub) y)) []).flatten)
          ixe pre.state rs
          (segmentsOf L (ls.map fun y => groupRecords ixe (namesAt (quotientGraph ixe t hints sub) y)) [])) :
    ReaderStreamsUnits.UnitsRead ixe sub t preA b pre rs := by
  obtain ⟨ls, L, steps, hnd, hmem, hpw, order⟩ := closureOrder_segments P htrace layout
  obtain ⟨canonical, segs⟩ := reads ls L steps hnd hmem hpw
  exact ClosureSegments.unitsRead_of_segments [] _ order canonical (fun _ h => nomatch h) segs

/--
info: 'Ix.Cert.ClosureLayout.unitsRead_of_layout' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms unitsRead_of_layout

end Ix.Cert.ClosureLayout
