/-
  The area search computes the specification's search, part 4: the component
  cost. `phiA` equals `phiEL2` (hence `SCtx.phiE`) at every search node
  (`phiA_eq`).
-/
module

public import Ix.Sharing.Exact.AreaTruncRows
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearchLocal
import all Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.AreaRowsRel
import all Ix.Sharing.Exact.AreaClosureRows
import all Ix.Sharing.Exact.AreaTruncRows

public section

namespace Ix.Sharing.Exact.AreaProof

open Ix.Sharing.Exact
open Ix.Sharing.Exact.LocalSearch (ESize)

/-! ## An entry's cost with its own Share hidden -/

section Hidden

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
  (hS : ∀ t, t < p.dag.size → SpineRow p.dag p.family (fun _ => true) p.spineLen p.tail t)

include h hfam hS in
/-- The inline cost of `x` with its own Share hidden is the inline cost of its
dictionary row. -/
theorem hidden_eq {wd : Nat → Option Nat} {dC dS : Nat → Nat} {dB : Nat → Option Nat}
    (hD : ∀ t, t < p.dag.size → DRow p wd dC dS dB t) {x : Nat} (hx : x < p.dag.size) :
    evalHiddenG p.dag p.family p.spineLen p.tail wd true true dC dS dB x =
      dInl p wd dC dS dB x := by
  unfold evalHiddenG dInl
  simp only [ite_true]
  by_cases hf : p.family[x]! = .none
  · have hb : (p.family[x]! == Family.none) = true := by simp [hf]
    rw [ite_eq_left hb, ite_eq_left hf]
  · have hb : (p.family[x]! == Family.none) = false := by simpa using hf
    simp only [hb, Bool.false_eq_true, ite_false, hf]
    have hn := nx_lt h hfam hx hf
    have hnx : (p.dag.node x).spineNext ≠ x := by
      show nx p x ≠ x; omega
    simp only [hnx, ite_false, beq_iff_eq]
    -- the two scans visit only terms on the spine below `x`
    have hside : (p.dag.node x).sideExtra + dC (p.dag.node x).sideChild +
        (if p.family[(p.dag.node x).spineNext]! = p.family[x]! then dS (p.dag.node x).spineNext
          else 0) = dSide p dC dS x := rfl
    have hbl : (if p.family[(p.dag.node x).spineNext]! = p.family[x]! then
        (if (wd (p.dag.node x).spineNext).isSome = true then some (p.dag.node x).spineNext
          else dB (p.dag.node x).spineNext) else none) = dBl p wd dB x := rfl
    rw [hside, hbl]
    refine scan_congr _ _ _ _ _ _ _ _ _ (fun u => DSp p x u ∧ (wd u).isSome = true) ?_ ?_ _ _ _ _ ?_
    · intro u v hu huv
      have hux : u ≠ x := by have := (DSp.props h hfam hS hx hu.1).1; omega
      rw [ite_eq_right hux] at huv
      have hun : u < p.dag.size := by have := (DSp.props h hfam hS hx hu.1).1; omega
      have hfu : p.family[u]! ≠ .none := by
        rw [(DSp.props h hfam hS hx hu.1).2.1]; exact hf
      obtain ⟨a, b⟩ := dLink h hfam hD u hun hfu v huv
      exact ⟨hu.1.trans a, b⟩
    · intro u hu
      have hux : u ≠ x := by have := (DSp.props h hfam hS hx hu.1).1; omega
      simp [hux]
    · intro v hv
      unfold dBl at hv
      split at hv
      · rename_i hs
        split at hv
        · rename_i hw; cases hv; exact ⟨.one hf hs, hw⟩
        · have hfn : p.family[nx p x]! ≠ .none := by rw [hs]; exact hf
          obtain ⟨a, b⟩ := dLink h hfam hD _ (by omega) hfn v hv
          exact ⟨.step hf hs a, b⟩
      · cases hv

end Hidden

/-! ## Sums -/

theorem foldl_add_list (f : Nat → Nat) (l : List Nat) (a : Nat) :
    l.foldl (fun acc x => acc + f x) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; omega

theorem foldl_add_arr (f : Nat → Nat) (arr : Array Nat) (a : Nat) :
    arr.foldl (fun acc x => acc + f x) a = a + (arr.toList.map f).sum := by
  rw [← Array.foldl_toList, foldl_add_list]

theorem sum_filter_split (f : Nat → Nat) (P : Nat → Bool) (l : List Nat) :
    (l.map f).sum = ((l.filter P).map f).sum + ((l.filter (fun x => !P x)).map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    cases hp : P x
    · simp only [Bool.false_eq_true, ite_false, Bool.not_false, ite_true, List.map_cons,
        List.sum_cons]
      rw [ih]; omega
    · simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false, List.map_cons,
        List.sum_cons]
      rw [ih]; omega

theorem sum_congr_mem {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

theorem sum_perm {f : Nat → Nat} {l l' : List Nat} (h : l.Perm l') :
    (l.map f).sum = (l'.map f).sum :=
  (h.map f).sum_nat

/-! ## The closure -/

theorem evalFrom_esize (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (init : DictEval) (width : Array (Option Nat)) (aff : Array Bool) :
    (evalFrom dag family spineLen tail init width aff).cost.size = init.cost.size ∧
      (evalFrom dag family spineLen tail init width aff).sides.size = init.sides.size ∧
      (evalFrom dag family spineLen tail init width aff).below.size = init.below.size := by
  unfold evalFrom
  have : ∀ m (st : DictEval),
      (foldRange (evalStep dag family spineLen tail width aff) 0 m st).cost.size = st.cost.size ∧
      (foldRange (evalStep dag family spineLen tail width aff) 0 m st).sides.size = st.sides.size ∧
      (foldRange (evalStep dag family spineLen tail width aff) 0 m st).below.size =
        st.below.size := by
    intro m
    induction m with
    | zero => intro st; exact ⟨rfl, rfl, rfl⟩
    | succ m ih =>
      intro st
      rw [Ix.Sharing.Exact.LocalSearch.foldRange_succ, Nat.zero_add]
      obtain ⟨a, b, c⟩ := ih st
      obtain ⟨a', b', c'⟩ := evalStep_sizes dag family spineLen tail width aff
        (foldRange (evalStep dag family spineLen tail width aff) 0 m st) m
      exact ⟨a'.trans a, b'.trans b, c'.trans c⟩
  exact this dag.size _

/-- The closure of a set of members is closed upward along descendants. -/
theorem upClosure_up {dag : Dag} (h : DagOK dag) (isMember : Nat → Bool) {t u : Nat}
    (ht : t < dag.size) (hd : Desc dag t u)
    (hu : u ∈ (upClosure dag isMember).toList) : t ∈ (upClosure dag isMember).toList := by
  rw [Ix.Sharing.Exact.LocalSearch.mem_upClosure h.cp] at hu ⊢
  induction hd with
  | child hc => exact .par ht hc hu
  | @trans u' c hd' hc ih =>
    have hu' : u' < dag.size := Nat.lt_trans (hd'.lt h ht) ht
    exact ih (.par hu' hc hu)

theorem inA_iff_mem {area : Array Nat} {u : Nat} : InA area u ↔ u ∈ area.toList := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact Ix.Sharing.Exact.LocalSearch.mem_of_getElem! hj
  · intro hm
    rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hm
    obtain ⟨j, hj, hx⟩ := hm
    exact ⟨j, hj, by rw [getElem!_pos area j hj]; exact hx⟩

theorem strictInc_pairwise {a : Array Nat} (h : strictInc a = true) :
    a.toList.Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := Ix.Sharing.Exact.LocalSearch.strictInc_lt h i j hij (by simpa using hj)
  rw [getElem!_pos a i (by simpa using hi), getElem!_pos a j (by simpa using hj)] at this
  simpa using this

/-- The widths of `SCtx.phiE` are `w` exactly at the opaque terms and the
available members (read through the member flags by area position). -/
theorem width_eq {cx : SCtx} {posA posC : Array Nat}
    (hr : Ix.Sharing.Exact.LocalSearch.Ready cx posA posC)
    (hm : Ix.Sharing.Exact.LocalSearch.MembersIn cx posA)
    (hwcs : ∀ u, widthOf cx.widthCs u = if cx.up.opaq[u]! then some cx.up.w else none)
    (avail : Nat → Bool) (u : Nat) :
    widthOf (cx.members.foldl (fun acc t => if avail t then acc.set! t (some cx.up.w) else acc)
      cx.widthCs) u =
      if cx.up.opaq[u]! = true ∨ avA posA (memberFlags cx posA avail) u = true then
        some cx.up.w else none := by
  rw [Ix.Sharing.Exact.LocalSearch.phiWidth_eq,
    ← Ix.Sharing.Exact.LocalSearch.flagWidth_eq hr hm]
  unfold flagWidth avA
  cases hp : posOf posA u with
  | none =>
    have h0 : posA[u]! = 0 := by
      cases hz : posA[u]! with
      | zero => rfl
      | succ k => rw [(Ix.Sharing.Exact.LocalSearch.posOf_some posA u k).mpr hz] at hp; cases hp
    simp only [h0, hwcs]
    cases cx.up.opaq[u]! <;> simp
  | some j =>
    have hk := (Ix.Sharing.Exact.LocalSearch.posOf_some posA u j).mp hp
    simp only [hk, hwcs]
    cases hfj : (memberFlags cx posA avail)[j]! <;> cases hou : cx.up.opaq[u]! <;> simp [hfj]

section Guard

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
  {opaq : Array Bool} {tLn tTl : Array Nat}
  (hT : ∀ t, t < p.dag.size → SpineRow p.dag p.family (fun u => !opaq[u]!) tLn tTl t)

include h hfam hT in
/-- The opacity test of an opaque term outside the area reads the same as on
the base tables. -/
theorem guard_out {area posA : Array Nat} {w : Nat} {X : Nat → Bool} (tb : TBase)
    (hpos : Ix.Sharing.Exact.LocalSearch.PosFn area.size (area[·]!) (posOf posA))
    (hclose : ∀ y q, InA area y → opaq[y]! = false → q < p.dag.size →
      y ∈ (p.dag.node q).children → InA area q) (C I S B : Array Nat)
    (hTr : ∀ t, t < p.dag.size → TRow p opaq tLn tTl w X (rdA posA C tb.cost)
      (rdA posA I tb.inl) (rdA posA S tb.sides) (rdA posA B tb.below) t)
    (htb : ∀ t, t < p.dag.size → TRow p opaq tLn tTl w (fun _ => false)
      (tb.cost[·]!) (tb.inl[·]!) (tb.sides[·]!) (tb.below[·]!) t)
    {c : Nat} (hc : c < p.dag.size) (hout : ¬ InA area c)
    (hg : tGuard p tTl w (tb.cost[·]!) (tb.inl[·]!) (tb.sides[·]!) c = true) :
    tGuard p tTl w (rdA posA C tb.cost) (rdA posA I tb.inl) (rdA posA S tb.sides) c = true := by
  simp only [tGuard] at hg ⊢
  rw [rdA_out hpos _ _ hout, rdA_out hpos _ _ hout]
  by_cases hf : p.family[c]! = .none
  · have hb : (p.family[c]! == Family.none) = true := by simp [hf]
    simp only [hb, Bool.true_or, Bool.and_true] at hg ⊢
    exact hg
  · have htl := ttail_lt h hfam hT c hc hf
    have e : rdA posA C tb.cost tTl[c]! = tb.cost[tTl[c]!]! := by
      by_cases hin : InA area tTl[c]!
      · by_cases ho : opaq[tTl[c]!]! = true
        · have h1 := (hTr tTl[c]! (by omega)).parts.1
          have h2 := (htb tTl[c]! (by omega)).parts.1
          unfold tCost at h1 h2
          simp only [ho, ite_true] at h1 h2
          rw [h1, h2]
        · exfalso
          have ho' : opaq[tTl[c]!]! = false := by simpa using ho
          rcases ttail_parent h hfam hT c hc hf with hch | ⟨y, hy, hch⟩
          · exact hout (hclose _ c hin ho' hc hch)
          · have hyt := (TSp.lt_fam h hfam hc hy).1
            exact hout (TSp_area h hfam hclose hc hy (hclose _ y hin ho' (by omega) hch))
      · exact rdA_out hpos _ _ hin
    rw [e]; exact hg

end Guard

/-- The facts of `Prep.ofDag` the rows need. -/
theorem ofDag_facts {dag : Dag} (h : DagOK dag) :
    DagOK (Prep.ofDag dag).dag ∧
      (∀ t, t < (Prep.ofDag dag).dag.size →
        (Prep.ofDag dag).family[t]! = ((Prep.ofDag dag).dag.node t).head.family) ∧
      (∀ t, t < (Prep.ofDag dag).dag.size → SpineRow (Prep.ofDag dag).dag (Prep.ofDag dag).family
        (fun _ => true) (Prep.ofDag dag).spineLen (Prep.ofDag dag).tail t) := by
  have hfam : ∀ t, t < (Prep.ofDag dag).dag.size →
      (Prep.ofDag dag).family[t]! = ((Prep.ofDag dag).dag.node t).head.family :=
    fun t ht => ofDag_family ht
  refine ⟨h, hfam, fun t ht => ?_⟩
  have := spineTables_rows h hfam t ht
  exact this

theorem ofDag_empty_size (dag : Dag) : ESize dag.size (Prep.ofDag dag).empty := by
  unfold Prep.ofDag
  obtain ⟨a, b, c⟩ := evalFrom_esize dag (dag.nodes.map (·.head.family))
    (spineTables dag (dag.nodes.map (·.head.family))).1
    (spineTables dag (dag.nodes.map (·.head.family))).2
    { cost := Array.replicate dag.size 0, sides := Array.replicate dag.size 0,
      below := Array.replicate dag.size none } (Array.replicate dag.size none)
    (Array.replicate dag.size true)
  exact ⟨by simpa using a, by simpa using b, by simpa using c⟩

theorem tStageOK_spec {p : Prep} {w : Nat} {opaq : Array Bool} {tb : TBase}
    (h : tStageOK p w opaq tb = true) :
    tb.cost.size = p.dag.size ∧ tb.inl.size = p.dag.size ∧
      ∀ c, c < p.dag.size → opaq[c]! = true →
        tGuard p tb.tTail w (tb.cost[·]!) (tb.inl[·]!) (tb.sides[·]!) c = true := by
  unfold tStageOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩, h8⟩ := h
  refine ⟨h3, h4, fun c hc ho => ?_⟩
  have := h8 c hc
  simp only [ho, Bool.not_true, Bool.false_or] at this
  exact this

/-! ## The component cost -/

/-- **The component cost from the area.** Under the stage's facts and the
checks of the component, `phiA` is `phiEL2` at every node. -/
theorem phiA_eq (ex : Expanded) (cx cxL : SCtx) (posA posC : Array Nat) (tb : TBase)
    (aux : AAux) (fb : Unit → SCtx × Array Nat)
    (hdag : DagOK ex.dag) (hp : cx.up.prep = Prep.ofDag ex.dag)
    (hclo : cx.closure = upClosure ex.dag ((markTable ex.dag.size cx.members)[·]!))
    (hrootsC : cx.rootsC = ex.roots.filter ((markTable ex.dag.size cx.closure)[·]!))
    (hstoredC : cx.storedInC = cx.closure.filter (cx.up.opaq[·]!))
    (hwcs : ∀ u, widthOf cx.widthCs u = if cx.up.opaq[u]! then some cx.up.w else none)
    (hall : cx.allTrue = Array.replicate ex.dag.size true)
    (hbase : cx.baseEv = cx.up.prep.eval cx.widthCs cx.allTrue)
    (htb : tb = TBase.ofPrep cx.up.prep cx.up.w cx.up.opaq)
    (hstage : tStageOK cx.up.prep cx.up.w cx.up.opaq tb = true)
    (hr : Ix.Sharing.Exact.LocalSearch.Ready cx posA posC)
    (hmem : ∀ m, cx.members.contains m = true → InA cx.area m ∧ cx.up.opaq[m]! = false)
    (hclose : ∀ y q, InA cx.area y → cx.up.opaq[y]! = false → q < ex.dag.size →
      y ∈ (ex.dag.node q).children → InA cx.area q)
    (hAinC : ∀ y, InA cx.area y → y ∈ cx.closure.toList)
    (hcs : aux.csize = cx.closure.size)
    (hK : aux.K =
      ((ex.roots.toList.filter (fun r => (markTable ex.dag.size cx.closure)[r]! && posA[r]! == 0)).map
        (tb.cost[·]!)).sum +
      ((cx.closure.toList.filter (fun c => cx.up.opaq[c]! && posA[c]! == 0)).map
        (tb.inl[·]!)).sum)
    (hrA : aux.rootsA = ex.roots.filter (fun r => posA[r]! != 0))
    (hsA : aux.storedA = cx.area.filter (cx.up.opaq[·]!))
    (hcxL : cxL = { cx with closure := #[], rootsC := #[], storedInC := #[] })
    (hfb : fb () = (cx, posC)) (avail : Nat → Bool) (stored : Array Nat) :
    phiA cxL posA tb aux fb avail stored = phiEL2 cx posA posC avail stored := by
  subst hcxL
  obtain ⟨_, _, _, _, hev, _, _, hopsz, hareaLt, _⟩ :=
    Ix.Sharing.Exact.LocalSearch.localSearchOK_spec hr.ok
  have hinc := (Ix.Sharing.Exact.LocalSearch.localSearchOK_inc hr.ok).1
  have hpd : cx.up.prep.dag = ex.dag := by rw [hp]; rfl
  obtain ⟨hdagP, hfamP, hSP⟩ := ofDag_facts hdag
  rw [← hp] at hdagP hfamP hSP
  -- area membership by position
  have hInA : ∀ u, InA cx.area u ↔ posA[u]! ≠ 0 := by
    intro u
    constructor
    · rintro ⟨j, hj, hju⟩
      have := (hr.area u j).mpr ⟨hj, hju⟩
      rw [Ix.Sharing.Exact.LocalSearch.posOf_some] at this
      omega
    · intro hne
      obtain ⟨k, hk⟩ : ∃ k, posA[u]! = k + 1 := ⟨posA[u]! - 1, by omega⟩
      have := (hr.area u k).mp ((Ix.Sharing.Exact.LocalSearch.posOf_some posA u k).mpr hk)
      exact ⟨k, this.1, this.2⟩
  have hm : Ix.Sharing.Exact.LocalSearch.MembersIn cx posA := by
    intro m hc
    obtain ⟨⟨j, hj, hjm⟩, _⟩ := hmem m hc
    rw [(hr.area m j).mpr ⟨hj, hjm⟩]; rfl
  -- the light context reads as `cx`
  have hfl : memberFlags { cx with closure := #[], rootsC := #[], storedInC := #[] } posA avail =
      memberFlags cx posA avail := rfl
  unfold phiA
  simp only [hfl]
  generalize hF : areaFold cx.up.prep cx.up.opaq tb cx.up.w cx.area posA
    (memberFlags cx posA avail) = F
  obtain ⟨C, I, S, B⟩ := F
  simp only
  split
  · rename_i hguard
    -- the truncated rows
    have hn : cx.up.prep.dag.size = ex.dag.size := by rw [hpd]
    obtain ⟨hTL, hTT, htbr⟩ := tbase_rows hdagP hfamP cx.up.opaq cx.up.w
    rw [← htb] at hTL hTT htbr
    have hT : ∀ t, t < cx.up.prep.dag.size → SpineRow cx.up.prep.dag cx.up.prep.family
        (fun u => !cx.up.opaq[u]!) tb.tLen tb.tTail t := by
      intro t ht; rw [hTL, hTT]; exact tSpineTables_rows hdagP hfamP cx.up.opaq t ht
    have hclose' : ∀ y q, InA cx.area y → cx.up.opaq[y]! = false → q < cx.up.prep.dag.size →
        y ∈ (cx.up.prep.dag.node q).children → InA cx.area q := by
      rw [hpd]; exact hclose
    have hTr := area_rows hdagP hfamP hT tb rfl rfl htbr cx.area posA (memberFlags cx posA avail)
      hinc hr.area hclose'
    simp only [hF] at hTr
    obtain ⟨hcsz, hisz, hstg⟩ := tStageOK_spec hstage
    -- the opacity test at every opaque term
    have hguard' : ∀ x ∈ aux.storedA, tGuard cx.up.prep tb.tTail cx.up.w (rdA posA C tb.cost)
        (rdA posA I tb.inl) (rdA posA S tb.sides) x = true := Array.all_eq_true'.mp hguard
    have hG : ∀ c, c < cx.up.prep.dag.size → cx.up.opaq[c]! = true →
        tGuard cx.up.prep tb.tTail cx.up.w (rdA posA C tb.cost) (rdA posA I tb.inl)
          (rdA posA S tb.sides) c = true := by
      intro c hc ho
      by_cases hin : InA cx.area c
      · apply hguard'
        rw [hsA, Array.mem_filter]
        exact ⟨Array.mem_toList_iff.mp (inA_iff_mem.mp hin), ho⟩
      · exact guard_out hdagP hfamP hT tb hr.area hclose' C I S B hTr htbr hc hin (hstg c hc ho)
    -- the dictionary rows over the closure
    have hwd := width_eq hr hm hwcs avail
    have haff : ∀ t, t < cx.up.prep.dag.size → cx.allTrue[t]! = true := by
      intro t ht
      rw [hall, getElem!_pos _ t (by simpa [hn] using ht)]
      simp
    have hbeq : cx.baseEv = evalFrom cx.up.prep.dag cx.up.prep.family cx.up.prep.spineLen
        cx.up.prep.tail cx.up.prep.empty cx.widthCs cx.allTrue := hbase
    have hempty : ESize cx.up.prep.dag.size cx.up.prep.empty := by
      rw [hp]; exact ofDag_empty_size ex.dag
    obtain ⟨_, hbrows⟩ := eval_rows hdagP hfamP hSP cx.widthCs cx.allTrue haff
      cx.up.prep.empty hempty
    rw [← hbeq] at hbrows
    have hCmem := Ix.Sharing.Exact.LocalSearch.mem_upClosure hdag.cp
      ((markTable ex.dag.size cx.members)[·]!)
    have hCsorted : cx.closure.toList.Pairwise (· < ·) := by
      rw [hclo]; exact Ix.Sharing.Exact.LocalSearch.upClosure_sorted _ _
    have hClt : ∀ x ∈ cx.closure.toList, x < cx.up.prep.dag.size := by
      intro x hx
      rw [hclo, hCmem] at hx
      rw [hpd]; exact hx.lt
    have hCup : ∀ t u, t < cx.up.prep.dag.size → Desc cx.up.prep.dag t u →
        u ∈ cx.closure.toList → t ∈ cx.closure.toList := by
      rw [hpd, hclo]
      intro t u ht hd hu
      exact upClosure_up hdag _ ht hd hu
    have hW : ∀ u, u < cx.up.prep.dag.size → u ∉ cx.closure.toList →
        widthOf (cx.members.foldl (fun acc t => if avail t then acc.set! t (some cx.up.w) else acc)
          cx.widthCs) u = widthOf cx.widthCs u := by
      intro u hu hnot
      rw [Ix.Sharing.Exact.LocalSearch.phiWidth_eq]
      unfold phiWidth
      have hc : cx.members.contains u = false := by
        cases hc : cx.members.contains u
        · rfl
        · exfalso
          apply hnot
          rw [hclo, hCmem]
          refine .mem (by rw [← hpd]; exact hu) ?_
          show (markTable ex.dag.size cx.members)[u]! = true
          rw [Ix.Sharing.Exact.LocalSearch.markTable_read, hc]
          simp [show u < ex.dag.size by rw [← hpd]; exact hu]
      simp only [hc, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false]
    obtain ⟨hEsz, hD⟩ := closure_rows hdagP hfamP hSP cx.widthCs
      (cx.members.foldl (fun acc t => if avail t then acc.set! t (some cx.up.w) else acc)
        cx.widthCs) cx.allTrue haff cx.baseEv hev hbrows cx.closure.toList hCsorted hClt hCup hW
    rw [Array.foldl_toList] at hEsz hD
    -- the two evaluations agree
    have hRel := rows_rel hdagP hfamP hSP hT (fun u _ => hwd u) hD hTr hG
    -- the specification's component cost
    rw [← Ix.Sharing.Exact.LocalSearch.phiE_eq_L2 hr hm avail stored]
    unfold SCtx.phiE
    simp only []
    generalize cx.members.foldl (fun acc t => if avail t then acc.set! t (some cx.up.w) else acc)
      cx.widthCs = W at hD hEsz hRel hwd ⊢
    generalize cx.closure.foldl (evalStep cx.up.prep.dag cx.up.prep.family cx.up.prep.spineLen
      cx.up.prep.tail W cx.allTrue) cx.baseEv = E at hD hEsz hRel ⊢
    have hcostE : ∀ r, r < cx.up.prep.dag.size → E.cost[r]! = rdA posA C tb.cost r :=
      fun r hr' => (hRel r hr').1
    have hinlE : ∀ x, (evalStep cx.up.prep.dag cx.up.prep.family cx.up.prep.spineLen
        cx.up.prep.tail (W.set! x none) cx.allTrue E x).cost[x]! = rdA posA I tb.inl x := by
      intro x
      rw [evalHidden_eq, Ix.Sharing.Exact.LocalSearch.evalHidden_eq_G _ _ _ _ _ _ _ _
        (hEsz.2.1.trans hEsz.1.symm) (hEsz.2.2.trans hEsz.1.symm)]
      by_cases hx : x < cx.up.prep.dag.size
      · rw [haff x hx, show decide (x < E.cost.size) = true by simp [hEsz.1, hx]]
        rw [hidden_eq hdagP hfamP hSP hD hx]
        exact (hRel x hx).2.1
      · have hxa : ¬ InA cx.area x := fun ⟨j, hj, hjx⟩ => hx (hjx ▸ hareaLt j hj)
        rw [rdA_out hr.area _ _ hxa]
        have h1 : cx.allTrue[x]! = false := by
          rw [hall, getElem!_neg _ x (by simpa [hn] using hx)]; rfl
        rw [h1]
        unfold evalHiddenG
        simp only [Bool.false_eq_true, ite_false]
        rw [getElem!_neg _ x (by rw [hEsz.1]; exact hx), getElem!_neg _ x (by rw [hisz]; exact hx)]
    have hinC : ∀ r, (markTable ex.dag.size cx.closure)[r]! = true ↔ r ∈ cx.closure.toList := by
      intro r
      rw [Ix.Sharing.Exact.LocalSearch.markTable_read]
      constructor
      · intro h1
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        exact Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp h1.2)
      · intro h1
        have hlt := hClt r h1
        rw [hn] at hlt
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hlt, Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp h1)⟩
    have hR : ((ex.roots.toList.filter (fun r => (markTable ex.dag.size cx.closure)[r]!)).map
          (fun r => E.cost[r]!)).sum =
        ((ex.roots.toList.filter (fun r => posA[r]! != 0)).map (rdA posA C tb.cost)).sum +
        ((ex.roots.toList.filter (fun r => (markTable ex.dag.size cx.closure)[r]! &&
          posA[r]! == 0)).map (tb.cost[·]!)).sum := by
      rw [sum_congr_mem (g := rdA posA C tb.cost) (fun r hr' => by
        rw [List.mem_filter] at hr'
        exact hcostE r (hClt r ((hinC r).mp hr'.2)))]
      rw [sum_filter_split _ (fun r => posA[r]! != 0), List.filter_filter, List.filter_filter]
      congr 1
      · rw [List.filter_congr (q := fun r => posA[r]! != 0) (fun r _ => ?_)]
        cases hP : (posA[r]! != 0)
        · rfl
        · have hin : InA cx.area r := (hInA r).mpr (by simpa using hP)
          simp only [Bool.true_and]
          exact (hinC r).mpr (hAinC r hin)
      · rw [sum_congr_mem (g := (tb.cost[·]!)) ?_]
        · rw [List.filter_congr (fun r _ => ?_)]
          simp only [bne, Bool.not_not, Bool.and_comm]
        · intro r hr'
          rw [List.mem_filter] at hr'
          apply rdA_out hr.area
          rw [hInA]
          exact fun hne => hne (by simpa using hr'.2 : posA[r]! = 0 ∧ _).1
    have hB : ((cx.closure.toList.filter (fun c => cx.up.opaq[c]!)).map
          (rdA posA I tb.inl)).sum =
        ((cx.area.toList.filter (fun c => cx.up.opaq[c]!)).map (rdA posA I tb.inl)).sum +
        ((cx.closure.toList.filter (fun c => cx.up.opaq[c]! && posA[c]! == 0)).map
          (tb.inl[·]!)).sum := by
      rw [sum_filter_split _ (fun c => posA[c]! != 0), List.filter_filter, List.filter_filter]
      congr 1
      · apply sum_perm
        rw [List.perm_ext_iff_of_nodup ((hCsorted.filter _).imp Nat.ne_of_lt)
          (((strictInc_pairwise hinc).filter _).imp Nat.ne_of_lt)]
        intro x
        simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq]
        constructor
        · rintro ⟨_, hx1, hx2⟩
          exact ⟨inA_iff_mem.mp ((hInA x).mpr hx1), hx2⟩
        · rintro ⟨hxa, hx⟩
          have hia := inA_iff_mem.mpr hxa
          exact ⟨hAinC x hia, (hInA x).mp hia, hx⟩
      · rw [sum_congr_mem (g := (tb.inl[·]!)) ?_]
        · rw [List.filter_congr (fun c _ => ?_)]
          simp only [bne, Bool.not_not, Bool.and_comm]
        · intro c hc
          rw [List.mem_filter] at hc
          apply rdA_out hr.area
          rw [hInA]
          exact fun hne => hne (by simpa using hc.2 : posA[c]! = 0 ∧ _).1
    simp only [hinlE, foldl_add_arr, Nat.zero_add]
    rw [hrootsC, hstoredC, hrA, hsA, hK, hcs]
    simp only [Array.toList_filter]
    rw [hR, hB]
    refine Prod.ext ?_ rfl
    simp only
    omega
  · rw [hfb]

end Ix.Sharing.Exact.AreaProof

end
