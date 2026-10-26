import Ix.Cert.Statement
import Ix.Compile.ConeCheck

/-! # The changed-cone check's closure orders

The runtime check (`Ix.Compile.ConeCheck`) reads the artifact with its own copies
of the statement's readers; they are the statement's (`recordAt_eq`, …, by
`rfl`). Its decider of closure orders is sound (`closureOrderCheck_sound`): an
order it passes lists, each once, exactly the addresses the seeds reach over the
check's edges (`edge`: a projection's block, a stored reference, a stored target
of an extra edge), with no record before one it references. Over no extra edges
that is the statement's `ClosureOrder` (`closureOrderCheck_closureOrder`). -/

namespace Ix.Cert.ConeOrder

open Ix.Compile.ConeCheck

/-! ## The readers are the statement's -/

theorem recordAt_eq (ixe : Ixon.Env) (a : Address) :
    Ix.Compile.ConeCheck.recordAt ixe a = Ix.Cert.recordAt ixe a := rfl

theorem ownerOf_eq (a : Address) (c : Ixon.Constant) :
    Ix.Compile.ConeCheck.ownerOf a c = Ix.Cert.ownerOf a c := rfl

theorem recordsOf_eq (ixe : Ixon.Env) (order : List Address) :
    Ix.Compile.ConeCheck.recordsOf ixe order = Ix.Cert.recordsOf ixe order := rfl

theorem blobsOf_eq (ixe : Ixon.Env) (order : List Address) :
    Ix.Compile.ConeCheck.blobsOf ixe order = Ix.Cert.blobsOf ixe order := rfl

theorem hintsOf_eq (ixe : Ixon.Env) :
    Ix.Compile.ConeCheck.hintsOf ixe = Ix.Cert.hintsOf ixe := rfl

/-- The hints read through the projection map computed once are the statement's. -/
theorem hintsWith_projAtOf (ixe : Ixon.Env) :
    hintsWith (projAtOf ixe) ixe.anonHints = Ix.Cert.hintsOf ixe := rfl

/-! ## Reach over an edge relation -/

/-- `a` is reached from the stored seeds `S` over the edges `R`. -/
inductive ReachBy (ixe : Ixon.Env) (R : Address → Address → Prop) (S : Address → Prop) :
    Address → Prop
  | seed {a : Address} : S a → ixe.consts.contains a = true → ReachBy ixe R S a
  | step {a b : Address} : ReachBy ixe R S a → R a b → ReachBy ixe R S b

/-- `order` lists the addresses `S` reaches over `R`, each once, and no record
before one it references. -/
structure OrderBy (ixe : Ixon.Env) (R : Address → Address → Prop) (S : Address → Prop)
    (order : List Address) : Prop where
  nodup : order.Nodup
  complete : ∀ a, a ∈ order ↔ ReachBy ixe R S a
  ordered : order.Pairwise fun a b => ¬ RecordRef ixe a b

/-- Over the statement's edges, reach is the statement's. -/
theorem reachBy_recordEdge_iff {ixe : Ixon.Env} {S : Address → Prop} {a : Address} :
    ReachBy ixe (RecordEdge ixe) S a ↔ CompiledReach ixe S a := by
  constructor
  · intro h
    induction h with
    | seed hs hc => exact .seed hs hc
    | step _ he ih => exact .step ih he
  · intro h
    induction h with
    | seed hs hc => exact .seed hs hc
    | step _ he ih => exact .step ih he

/-- An order over the statement's edges is a `ClosureOrder`. -/
theorem OrderBy.closureOrder {ixe : Ixon.Env} {S : Address → Prop} {order : List Address}
    (h : OrderBy ixe (RecordEdge ixe) S order) : ClosureOrder ixe S order :=
  ⟨h.nodup, fun a => (h.complete a).trans reachBy_recordEdge_iff, h.ordered⟩

/-! ## Reading the decider -/

/-- The check's edge: a projection's block, a stored reference, or a stored target
of an extra edge. -/
def CheckEdge (ixe : Ixon.Env) (extra : Extra) (a b : Address) : Prop :=
  RecordEdge ixe a b ∨ ((extra.getD a #[]).contains b = true ∧ ixe.consts.contains b = true)

theorem edge_iff {ixe : Ixon.Env} {extra : Extra} {a b : Address} :
    edge ixe extra a b = true ↔ CheckEdge ixe extra a b := by
  unfold edge CheckEdge RecordEdge
  change ((match Ix.Cert.recordAt ixe a with
    | some c => (Ix.Cert.ownerOf a c == b && b != a) || (c.refs.contains b && ixe.consts.contains b)
    | none => false) || ((extra.getD a #[]).contains b && ixe.consts.contains b)) = true ↔ _
  rw [Bool.or_eq_true, Bool.and_eq_true]
  apply or_congr_left
  cases Ix.Cert.recordAt ixe a with
  | none => simp
  | some c =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    constructor
    · intro h
      exact ⟨c, rfl, h⟩
    · rintro ⟨c', hc, h⟩
      cases hc
      exact h

/-- With no extra edge, the check's edge is the statement's. -/
theorem checkEdge_empty {ixe : Ixon.Env} : CheckEdge ixe {} = RecordEdge ixe := by
  funext a b
  apply propext
  unfold CheckEdge
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h
    · simp at h
  · exact .inl

theorem getD_of_lt {order : Array Address} {j : Nat} (h : j < order.size) (d : Address) :
    order.getD j d = order[j] := by
  simp [Array.getD, h]

theorem mem_sound {order : Array Address} {positions : Std.HashMap Address Nat} {y : Address}
    (h : mem order positions y = true) : ∃ j, ∃ hj : j < order.size, order[j] = y := by
  unfold mem at h
  split at h
  · rename_i j _
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hj, he⟩ := h
    exact ⟨j, hj, by rw [← getD_of_lt hj default]; exact he⟩
  · cases h

theorem memBefore_sound {order : Array Address} {positions : Std.HashMap Address Nat} {i : Nat}
    {y : Address} (hi : i ≤ order.size) (h : memBefore order positions i y = true) :
    ∃ j, j < i ∧ ∃ hj : j < order.size, order[j] = y := by
  unfold memBefore at h
  split at h
  · rename_i j _
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hj, he⟩ := h
    have hj' : j < order.size := Nat.lt_of_lt_of_le hj hi
    exact ⟨j, hj, hj', by rw [← getD_of_lt hj' default]; exact he⟩
  · cases h

theorem mem_toList {order : Array Address} {j : Nat} (hj : j < order.size) :
    order[j] ∈ order.toList :=
  Array.mem_toList_iff.mpr (Array.getElem_mem hj)

theorem listed {order : Array Address} {positions : Std.HashMap Address Nat} {y : Address}
    (h : mem order positions y = true) : y ∈ order.toList := by
  obtain ⟨j, hj, he⟩ := mem_sound h
  have := mem_toList hj
  rw [he] at this
  exact this

/-- What the check at one position says. -/
structure PositionFacts (ixe : Ixon.Env) (extra : Extra) (isSeed : Address → Bool)
    (order : Array Address) (positions : Std.HashMap Address Nat) (depth : Array Nat)
    (i : Nat) (hi : i < order.size) : Prop where
  position : positions.get? order[i] = some i
  reached : (isSeed order[i] = true ∧ ixe.consts.contains order[i] = true) ∨
    ∃ p, ∃ hp : p < order.size, depth.getD p 0 < depth.getD i 0 ∧ CheckEdge ixe extra order[p] order[i]
  closed : ∀ c, Ix.Cert.recordAt ixe order[i] = some c →
    (Ix.Cert.ownerOf order[i] c ≠ order[i] → Ix.Cert.ownerOf order[i] c ∈ order.toList) ∧
    (∀ r ∈ c.refs, ixe.consts.contains r = true → r ∈ order.toList)
  extraClosed : ∀ r ∈ extra.getD order[i] #[], ixe.consts.contains r = true → r ∈ order.toList
  before : ∀ c, Ix.Cert.recordAt ixe order[i] = some c → ∀ r ∈ c.refs, ∀ cr,
    Ix.Cert.recordAt ixe r = some cr → Ix.Cert.ownerOf r cr ≠ order[i] →
    ∃ j, j < i ∧ ∃ hj : j < order.size, order[j] = Ix.Cert.ownerOf r cr

theorem positionFacts {ixe : Ixon.Env} {extra : Extra} {isSeed : Address → Bool}
    {order : Array Address} {positions : Std.HashMap Address Nat} {parent : Array (Option Nat)}
    {depth : Array Nat} {i : Nat} (hi : i < order.size)
    (h : positionCheck ixe extra isSeed order positions parent depth i = true) :
    PositionFacts ixe extra isSeed order positions depth i hi := by
  unfold positionCheck at h
  simp only [getD_of_lt hi] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hpos, hreach⟩, hrec⟩, hextra⟩ := h
  refine ⟨by simpa using hpos, ?_, ?_, ?_, ?_⟩
  · split at hreach
    · simp only [Bool.and_eq_true] at hreach
      exact .inl hreach
    · rename_i p _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hreach
      obtain ⟨⟨hp, hd⟩, he⟩ := hreach
      rw [getD_of_lt hp] at he
      exact .inr ⟨p, hp, hd, edge_iff.mp he⟩
  · intro c hc
    change (match Ix.Cert.recordAt ixe order[i] with
      | some c => _ | none => true) = true at hrec
    rw [hc] at hrec
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Array.all_eq_true] at hrec
    obtain ⟨⟨howner, hrefs⟩, -⟩ := hrec
    refine ⟨fun hne => ?_, fun r hr hs => ?_⟩
    · rcases howner with heq | hm
      · exact absurd heq hne
      · exact listed hm
    · obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hr
      have := hrefs k hk
      simp only [hs, Bool.not_true, Bool.false_eq_true, false_or] at this
      exact listed this
  · intro r hr hs
    simp only [Array.all_eq_true] at hextra
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hr
    have := hextra k hk
    simp only [hs, Bool.not_true, Bool.false_or] at this
    exact listed this
  · intro c hc r hr cr hcr hne
    change (match Ix.Cert.recordAt ixe order[i] with
      | some c => _ | none => true) = true at hrec
    rw [hc] at hrec
    simp only [Bool.and_eq_true, Array.all_eq_true] at hrec
    obtain ⟨-, hord⟩ := hrec
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hr
    have := hord k hk
    change (match Ix.Cert.recordAt ixe c.refs[k] with
      | some cr => _ | none => true) = true at this
    rw [hcr] at this
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with heq | hb
    · exact absurd heq hne
    · exact memBefore_sound (Nat.le_of_lt hi) hb

/-! ## The decider is sound -/

theorem nodup_of_positions {order : Array Address} {positions : Std.HashMap Address Nat}
    (h : ∀ i (hi : i < order.size), positions.get? order[i] = some i) : order.toList.Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro i j hi hj he
  simp only [Array.length_toList] at hi hj
  simp only [Array.getElem_toList] at he
  have h1 := h i hi
  have h2 := h j hj
  rw [he] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- **The decider is sound**: an order it passes lists, each once, exactly what the
seeds it was given (`isSeed`, all among `seeds`) reach over the check's edges, and
no record before one it references. -/
theorem closureOrderCheck_sound {ixe : Ixon.Env} {extra : Extra} {seeds : Array Address}
    {isSeed : Address → Bool} {order : Array Address} {positions : Std.HashMap Address Nat}
    {parent : Array (Option Nat)} {depth : Array Nat}
    (h : closureOrderCheck ixe extra seeds isSeed order positions parent depth = true)
    (hs : ∀ a, isSeed a = true → a ∈ seeds) :
    OrderBy ixe (CheckEdge ixe extra) (fun a => isSeed a = true) order.toList := by
  unfold closureOrderCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Array.all_eq_true]
    at h
  obtain ⟨⟨⟨_, _⟩, hpos⟩, hseeds⟩ := h
  have facts : ∀ i (hi : i < order.size), PositionFacts ixe extra isSeed order positions depth i hi :=
    fun i hi => positionFacts hi (hpos i hi)
  have nodup := nodup_of_positions fun i hi => (facts i hi).position
  refine ⟨nodup, fun a => ⟨fun ha => ?_, fun hr => ?_⟩, ?_⟩
  · -- every listed address is reached, by induction on its distance
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    simp only [Array.length_toList] at hi
    simp only [Array.getElem_toList]
    have reached : ∀ d i (hi : i < order.size), depth.getD i 0 = d →
        ReachBy ixe (CheckEdge ixe extra) (fun a => isSeed a = true) order[i] := by
      intro d
      induction d using Nat.strongRecOn with
      | ind d ih =>
        intro i hi hd
        rcases (facts i hi).reached with ⟨hseed, hstored⟩ | ⟨p, hp, hlt, hedge⟩
        · exact .seed hseed hstored
        · exact .step (ih _ (hd ▸ hlt) p hp rfl) hedge
    exact reached _ i hi rfl
  · -- every reached address is listed
    induction hr with
    | @seed a hseed hstored =>
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp (hs a hseed)
      have := hseeds k hk
      simp only [hstored, Bool.not_true] at this
      exact listed this
    | @step a b _ hedge ih =>
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ih
      simp only [Array.length_toList] at hi
      simp only [Array.getElem_toList] at hedge ⊢
      rcases hedge with ⟨c, hc, hown | hrefs⟩ | ⟨hx, hstored⟩
      · obtain ⟨rfl, hne⟩ := hown
        exact ((facts i hi).closed c hc).1 hne
      · exact ((facts i hi).closed c hc).2 b (by simpa using hrefs.1) hrefs.2
      · exact (facts i hi).extraClosed b (by simpa using hx) hstored
  · -- no record before one it references
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij hrr
    simp only [Array.length_toList] at hi hj
    simp only [Array.getElem_toList] at hrr
    obtain ⟨c, hc, r, hr, cr, hcr, howner, hne⟩ := hrr
    obtain ⟨k, hk, hk', he⟩ := (facts i hi).before c hc r hr cr hcr (howner ▸ hne)
    rw [howner] at he
    have : k = j :=
      (List.nodup_iff_eq_of_getElem_eq.mp nodup) k j (by simpa using hk') (by simpa using hj)
        (by simpa using he)
    omega

/-- Over no extra edge, an order the decider passes is a `ClosureOrder`. -/
theorem closureOrderCheck_closureOrder {ixe : Ixon.Env} {seeds : Array Address}
    {isSeed : Address → Bool} {order : Array Address} {positions : Std.HashMap Address Nat}
    {parent : Array (Option Nat)} {depth : Array Nat}
    (h : closureOrderCheck ixe {} seeds isSeed order positions parent depth = true)
    (hs : ∀ a, isSeed a = true → a ∈ seeds) :
    ClosureOrder ixe (fun a => isSeed a = true) order.toList :=
  OrderBy.closureOrder (checkEdge_empty ▸ closureOrderCheck_sound h hs)

/-! ## The runs -/

/-- A run over an order the decider passed is the certified entry's acceptance of
that order's records, which list what the seeds reach over the check's edges. -/
theorem runOrdered_accepts {s : Setting} {ixe : Ixon.Env} {seeds : Array Address}
    {isSeed : Address → Bool} {order : Array Address} {cert : Array (Option Nat) × Array Nat}
    {c : Checked} (hints : s.hints = Ix.Cert.hintsOf ixe) (hs : ∀ a, isSeed a = true → a ∈ seeds)
    (h : runOrdered s ixe seeds isSeed order cert = .ok c) :
    OrderBy ixe (CheckEdge ixe s.extra) (fun a => isSeed a = true) c.order.toList ∧
      Ixon.Authenticated.checkBytes s.binding s.limits (Ix.Cert.recordsOf ixe c.order.toList)
        (Ix.Cert.blobsOf ixe c.order.toList) (Ix.Cert.hintsOf ixe) = .ok c.env := by
  unfold runOrdered at h
  split at h
  · rename_i hcheck
    split at h
    · rename_i env hrun
      cases h
      exact ⟨closureOrderCheck_sound hcheck hs, hints ▸ hrun⟩
    · cases h
  · cases h

/-- **A passed run of the certified entry on the closure of seeds**: the run's
order lists what the seeds reach over the check's edges, and the entry accepted
its records. -/
theorem checkSeeds_accepts {s : Setting} {ixe : Ixon.Env} {seeds : Array Address}
    {isSeed : Address → Bool} {c : Checked} (hints : s.hints = Ix.Cert.hintsOf ixe)
    (hs : ∀ a, isSeed a = true → a ∈ seeds) (h : checkSeeds s ixe seeds isSeed = .ok c) :
    OrderBy ixe (CheckEdge ixe s.extra) (fun a => isSeed a = true) c.order.toList ∧
      Ixon.Authenticated.checkBytes s.binding s.limits (Ix.Cert.recordsOf ixe c.order.toList)
        (Ix.Cert.blobsOf ixe c.order.toList) (Ix.Cert.hintsOf ixe) = .ok c.env := by
  unfold checkSeeds at h
  split at h
  · cases h
  · exact runOrdered_accepts hints hs h

end Ix.Cert.ConeOrder
