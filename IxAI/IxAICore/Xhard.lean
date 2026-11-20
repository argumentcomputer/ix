import IxAICore.Typed

/-!
# Tseitin parity formulas: a family past failed-literal reasoning

`prop-xhard` draws CNFs built from a Tseitin formula: a connected 3-regular graph on `verts`
vertices whose edge `i` is atom `i`, and for every vertex `v` the constraint "the parity of `v`'s
edges is `charge v`", written as one 3-clause per pattern of the wrong parity. Summing the
constraints counts every edge twice, so the formula is unsatisfiable whenever the charges have odd
parity (`Tseitin.not_sat`). Refuting it needs resolution proofs of size exponential in the
graph's expansion, and assigning one atom never produces a unit clause, so unit propagation and
failed-literal probing find nothing to learn: the bounded refutation search of `certify` does not
refute these formulas within its budget, while the complete `Dpll.dpll` still labels them.

Each instance starts from a drawn assignment `σ*` with charges equal to `σ*`'s parities, then:

* unsatisfiable: one vertex's charge flipped (odd parity), every Tseitin clause kept;
* satisfiable, trap: the same flip, but the one clause `σ*` falsifies removed, so `σ*` is a model
  and every model takes `σ*`'s values at that vertex, which DPLL has to find by search;
* satisfiable, even: no flip (`σ*` is a model; DPLL finds one without backtracking).

Up to `extras` random 3-clauses true under `σ*` are added in every class (one more for traps, so
the clause count does not reveal the class), clauses and literals are shuffled, and the outer form
is a CNF or its De Morgan dual, as in `sampleLogic`. The sampler records what it built (`XInst`);
`XInst.check` verifies it by evaluation and `XInst.check_sound` proves that a passing instance's
claimed status is its `status`. Labels used for training and scoring are still `fastStatus`.
-/

namespace IxAICore
namespace Typed

/-! ## Parity -/

/-- Parity of a list of truth values. -/
def parity : List Bool → Bool
  | [] => false
  | b :: l => b ^^ parity l

theorem parity_append : ∀ l₁ l₂ : List Bool, parity (l₁ ++ l₂) = (parity l₁ ^^ parity l₂)
  | [], _ => by simp [parity]
  | b :: l₁, l₂ => by simp [parity, parity_append l₁ l₂]

theorem parity_map_xor {α : Type} (f g : α → Bool) : ∀ l : List α,
    parity (l.map fun x => f x ^^ g x) = (parity (l.map f) ^^ parity (l.map g))
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, parity, parity_map_xor f g l]
    generalize parity (l.map f) = P
    generalize parity (l.map g) = Q
    cases f a <;> cases g a <;> cases P <;> cases Q <;> rfl

theorem parity_map_and {α : Type} (c : Bool) (f : α → Bool) : ∀ l : List α,
    parity (l.map fun x => c && f x) = (c && parity (l.map f))
  | [] => by cases c <;> rfl
  | a :: l => by
    simp only [List.map_cons, parity, parity_map_and c f l]
    cases c <;> simp

theorem parity_map_false {α : Type} : ∀ l : List α, parity (l.map fun _ => false) = false
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, parity, parity_map_false l, Bool.xor_false]

/-- Exactly one vertex below `V` equals `a` when `a < V`. -/
theorem parity_range_beq (a : Nat) : ∀ V : Nat,
    parity ((List.range V).map fun v => a == v) = decide (a < V)
  | 0 => by simp [parity]
  | V + 1 => by
    rw [List.range_succ, List.map_append, parity_append, parity_range_beq a V]
    simp only [List.map_cons, List.map_nil, parity, Bool.xor_false]
    rcases Nat.lt_trichotomy a V with h | h | h
    · have h1 : (a == V) = false := by simp; omega
      have h2 : a < V + 1 := by omega
      simp [h, h1, h2]
    · subst h
      simp
    · have h1 : (a == V) = false := by simp; omega
      have h2 : ¬ a < V + 1 := by omega
      have h3 : ¬ a < V := by omega
      simp [h1, h2, h3]

/-- An edge `(a, b)` with distinct endpoints below `V` meets an even number of those vertices. -/
theorem parity_incident {a b V : Nat} (hab : a ≠ b) (ha : a < V) (hb : b < V) :
    parity ((List.range V).map fun v => (a == v || b == v)) = false := by
  have hx : (fun v => (a == v || b == v)) = fun v => ((a == v) ^^ (b == v)) := by
    funext v
    cases h1 : a == v <;> cases h2 : b == v <;> simp_all
  rw [hx, parity_map_xor, parity_range_beq, parity_range_beq]
  simp [ha, hb]

/-! ## Tseitin formulas -/

/-- A graph on vertices `0 … verts − 1`, edge `i` being atom `i`, with a charge per vertex
(`false` past the end of the list). -/
structure Tseitin where
  verts : Nat
  edges : List (Nat × Nat)
  charge : List Bool
  deriving Repr, DecidableEq

/-- Indices `k, k + 1, …` of the edges of `es` that meet vertex `v`. -/
def incFrom (v : Nat) : List (Nat × Nat) → Nat → List Nat
  | [], _ => []
  | e :: es, k => if (e.1 == v || e.2 == v) then k :: incFrom v es (k + 1) else incFrom v es (k + 1)

/-- The atoms of the edges at `v`. -/
def Tseitin.inc (t : Tseitin) (v : Nat) : List Nat := incFrom v t.edges 0

/-- The clause false exactly when the atoms `es` take the values `p`. -/
def patClause : List Nat → List Bool → Dpll.Clause
  | e :: es, b :: bs => (e, !b) :: patClause es bs
  | _, _ => []

/-- Vertex `v`'s constraint, one clause for each pattern of its edges with the wrong parity. -/
def Tseitin.vertexClauses (t : Tseitin) (v : Nat) : Dpll.CNF :=
  ((assignments (t.inc v).length).filter fun p => parity p != t.charge.getD v false).map
    (patClause (t.inc v))

def Tseitin.cnf (t : Tseitin) : Dpll.CNF := (List.range t.verts).flatMap t.vertexClauses

/-- Every edge has two distinct endpoints among the vertices. -/
def Tseitin.wf (t : Tseitin) : Bool :=
  t.edges.all fun e => e.1 != e.2 && decide (e.1 < t.verts) && decide (e.2 < t.verts)

def Tseitin.odd (t : Tseitin) : Bool := parity ((List.range t.verts).map fun v => t.charge.getD v false)

theorem patClause_map (σ : Nat → Bool) : ∀ es : List Nat,
    Dpll.clauseEval σ (patClause es (es.map σ)) = false
  | [] => rfl
  | e :: es => by
    have ih := patClause_map σ es
    simp only [Dpll.clauseEval] at ih ⊢
    simp only [List.map_cons, patClause, List.any_cons, ih, Bool.or_false, Dpll.litEval]
    cases σ e <;> rfl

/-- A model of the Tseitin clauses gives every vertex its charge. -/
theorem Tseitin.vertex_parity (t : Tseitin) (σ : Nat → Bool)
    (h : ∀ c ∈ t.cnf, Dpll.clauseEval σ c = true) {v : Nat} (hv : v < t.verts) :
    t.charge.getD v false = parity ((t.inc v).map σ) := by
  apply Eq.symm
  cases hq : (parity ((t.inc v).map σ) != t.charge.getD v false)
  · simpa using hq
  · have hp : (t.inc v).map σ ∈ assignments (t.inc v).length := mem_assignments.mpr (by simp)
    have hc : patClause (t.inc v) ((t.inc v).map σ) ∈ t.cnf :=
      List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv,
        List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hp, hq⟩, rfl⟩⟩
    have := h _ hc
    rw [patClause_map] at this
    cases this

/-- Summing the vertex parities counts every edge twice. -/
theorem parity_incFrom (σ : Nat → Bool) (V : Nat) : ∀ (es : List (Nat × Nat)) (k : Nat),
    (∀ e ∈ es, e.1 ≠ e.2 ∧ e.1 < V ∧ e.2 < V) →
    parity ((List.range V).map fun v => parity ((incFrom v es k).map σ)) = false
  | [], _, _ => by
    simp only [incFrom, List.map_nil, parity]
    exact parity_map_false _
  | e :: es, k, h => by
    have step : ∀ v, parity ((incFrom v (e :: es) k).map σ) =
        ((σ k && (e.1 == v || e.2 == v)) ^^ parity ((incFrom v es (k + 1)).map σ)) := by
      intro v
      simp only [incFrom]
      split
      · rename_i hc
        rw [hc]
        simp [parity]
      · rename_i hc
        rw [Bool.not_eq_true] at hc
        rw [hc]
        simp
    simp only [step]
    obtain ⟨hab, ha, hb⟩ := h e List.mem_cons_self
    rw [parity_map_xor, parity_map_and, parity_incident hab ha hb,
      parity_incFrom σ V es (k + 1) fun e he => h e (List.mem_cons_of_mem _ he)]
    simp

/-- Some clause of `F` has all its literals in `c`, so every model of `F` satisfies `c`. Literal
order and repetition do not matter. -/
def subsumes (F : Dpll.CNF) (c : Dpll.Clause) : Bool := F.any fun d => d.all fun l => decide (l ∈ c)

theorem subsumes_eval {σ : Nat → Bool} {F : Dpll.CNF} {c : Dpll.Clause}
    (h : subsumes F c = true) (hF : Dpll.cnfEval σ F = true) : Dpll.clauseEval σ c = true := by
  obtain ⟨d, hd, hdc⟩ := List.any_eq_true.mp h
  have hσd : Dpll.clauseEval σ d = true := List.all_eq_true.mp hF d hd
  obtain ⟨l, hl, hle⟩ := List.any_eq_true.mp hσd
  have hlc : l ∈ c := by simpa using List.all_eq_true.mp hdc l hl
  exact List.any_eq_true.mpr ⟨l, hlc, hle⟩

/-- Tseitin clauses with odd total charge have no model, and neither does any CNF subsuming each
of them. -/
theorem Tseitin.not_sat (t : Tseitin) (hw : t.wf = true) (ho : t.odd = true) {F : Dpll.CNF}
    (hF : ∀ c ∈ t.cnf, subsumes F c = true) : ¬ Dpll.Sat F := by
  rintro ⟨σ, hσ⟩
  have hall : ∀ c ∈ t.cnf, Dpll.clauseEval σ c = true := fun c hc => subsumes_eval (hF c hc) hσ
  have hwf : ∀ e ∈ t.edges, e.1 ≠ e.2 ∧ e.1 < t.verts ∧ e.2 < t.verts := by
    intro e he
    have := List.all_eq_true.mp hw e he
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hv : ∀ v ∈ List.range t.verts, t.charge.getD v false = parity ((t.inc v).map σ) :=
    fun v hv => t.vertex_parity σ hall (List.mem_range.mp hv)
  unfold Tseitin.odd at ho
  rw [List.map_congr_left hv] at ho
  simp only [Tseitin.inc] at ho
  rw [parity_incFrom σ t.verts t.edges 0 hwf] at ho
  cases ho

/-! ## Instances and their claimed status -/

def PForm.ofLit (m : Dpll.Lit) : PForm := if m.2 then .atom m.1 else .neg (.atom m.1)

/-- A clause as a left-nested disjunction, as `clause` draws them. -/
def PForm.ofClause : Dpll.Clause → PForm
  | [] => .and (.atom 0) (.neg (.atom 0))
  | m :: ms => ms.foldl (fun (f : PForm) l => PForm.or f (PForm.ofLit l)) (PForm.ofLit m)

/-- Clauses as a right-nested conjunction, as `cnf` draws them. -/
def PForm.ofCNF : Dpll.CNF → PForm
  | [] => .or (.atom 0) (.neg (.atom 0))
  | [c] => PForm.ofClause c
  | c :: cs => .and (PForm.ofClause c) (PForm.ofCNF cs)

/-- How an instance was built: the graph and charges, the clauses (the CNF core), the drawn
assignment, the status the construction claims, and the formula shown. -/
structure XInst where
  graph : Tseitin
  cls : Dpll.CNF
  witness : List Bool
  claim : Status
  form : PForm
  deriving Repr

/-- What the construction guarantees, checked by evaluation: for a contradiction (tautology) the
formula (its dual) reads as `cls`, which subsumes every clause of an odd, well-formed Tseitin
formula; for a contingent formula, it or its dual reads as `cls`, the witness of length `n`
satisfies `cls`, and some clause of `cls` can be falsified. -/
def XInst.check (n : Nat) (x : XInst) : Bool :=
  let tseitin := x.graph.wf && x.graph.odd && x.graph.cnf.all (subsumes x.cls)
  match x.claim with
  | .contradiction => decide (x.form.cnf? = some x.cls) && tseitin
  | .tautology => decide (x.form.dual.cnf? = some x.cls) && tseitin
  | .contingent =>
    (decide (x.form.cnf? = some x.cls) || decide (x.form.dual.cnf? = some x.cls)) &&
      x.witness.length == n && Dpll.cnfEval (Dpll.ofList x.witness) x.cls && falsifiable n x.cls

/-- A checked instance's claimed status is its status. -/
theorem XInst.check_sound (n : Nat) (x : XInst) (h : x.check n = true) : status n x.form = x.claim := by
  unfold XInst.check at h
  have tse : (x.graph.wf && x.graph.odd && x.graph.cnf.all (subsumes x.cls)) = true →
      ∀ σ, Dpll.cnfEval σ x.cls = false := by
    intro ht σ
    simp only [Bool.and_eq_true] at ht
    have hns := Tseitin.not_sat x.graph ht.1.1 ht.1.2 (F := x.cls) fun c hc =>
      List.all_eq_true.mp ht.2 c hc
    cases he : Dpll.cnfEval σ x.cls
    · rfl
    · exact absurd ⟨σ, he⟩ hns
  cases hc : x.claim with
  | contradiction =>
    rw [hc] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine (status_contradiction_iff n x.form).mpr fun l _ => ?_
    rw [PForm.cnf?_eval h.1]
    exact tse (by simp only [Bool.and_eq_true]; exact h.2) _
  | tautology =>
    rw [hc] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine (status_tautology_iff n x.form).mpr fun l _ => ?_
    have hd := PForm.eval_dual l x.form
    rw [PForm.cnf?_eval h.1, tse (by simp only [Bool.and_eq_true]; exact h.2)] at hd
    cases he : x.form.eval l
    · simp [he] at hd
    · rfl
  | contingent =>
    rw [hc] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hf, hlen⟩, hsat⟩, hfal⟩ := h
    obtain ⟨l₀, hl₀, he₀⟩ := falsifiable_sound hfal
    refine (status_contingent_iff n x.form).mpr ?_
    rcases hf with hf | hf
    · exact ⟨⟨x.witness, hlen, by rw [PForm.cnf?_eval hf]; exact hsat⟩,
        ⟨l₀, hl₀, by rw [PForm.cnf?_eval hf]; exact he₀⟩⟩
    · have hd := fun l => PForm.eval_dual l x.form
      refine ⟨⟨l₀, hl₀, ?_⟩, ⟨x.witness, hlen, ?_⟩⟩
      · have := hd l₀
        rw [PForm.cnf?_eval hf, he₀] at this
        cases he : x.form.eval l₀
        · simp [he] at this
        · rfl
      · have := hd x.witness
        rw [PForm.cnf?_eval hf, hsat] at this
        cases he : x.form.eval x.witness
        · rfl
        · simp [he] at this

/-! ## Sampling -/

/-- Generation parameters: vertices of the 3-regular graph (even), at most `extras` extra
clauses, and graph draws before falling back to a fixed graph. -/
structure XGen where
  verts : Nat
  extras : Nat
  fuel : Nat
  deriving Repr

/-- 16 vertices: 24 atoms and 64–67 clauses. DPLL refutes an unsatisfiable draw in a few thousand
nodes; the 16-node refutation search refutes none. -/
def XGen.default : XGen := { verts := 16, extras := 3, fuel := 200 }

def XGen.atoms (g : XGen) : Nat := 3 * g.verts / 2

/-- Edges pairing consecutive entries. -/
def pairUp : List Nat → List (Nat × Nat)
  | a :: b :: l => (a, b) :: pairUp l
  | _ => []

/-- No loops and no repeated edges. -/
def simpleEdges (es : List (Nat × Nat)) : Bool :=
  es.all (fun e => e.1 != e.2) &&
  es.zipIdx.all fun (e, i) => (es.drop (i + 1)).all fun f => !(f == e || f == (e.2, e.1))

/-- Every vertex below `V` is reachable from vertex 0. -/
def connected (V : Nat) (es : List (Nat × Nat)) : Bool :=
  let step := fun (seen : List Bool) => es.foldl (fun s e =>
    if s.getD e.1 false || s.getD e.2 false then setAt (setAt s e.1 true) e.2 true else s) seen
  (Nat.repeat step V ((List.range V).map (· == 0))).all id

/-- The Möbius ladder on `V` vertices, a connected 3-regular graph. -/
def ladder (V : Nat) : List (Nat × Nat) :=
  (List.range V).map (fun i => (i, (i + 1) % V)) ++ (List.range (V / 2)).map fun i => (i, i + V / 2)

/-- A uniform pairing of three copies of each vertex, redrawn until the graph is simple and
connected. -/
def drawGraph (V : Nat) : Nat → Rng → List (Nat × Nat) × Rng
  | 0, r => (ladder V, r)
  | fuel + 1, r =>
    let (pts, r) := shuffle ((List.range V).flatMap fun v => [v, v, v]) r
    let es := pairUp pts
    if simpleEdges es && connected V es then (es, r) else drawGraph V fuel r

/-- A random 3-clause over `n` atoms made true by `σ`: if all three literals are false, the first
is negated. -/
def plantedClause (n : Nat) (σ : Nat → Bool) (r : Rng) : Dpll.Clause × Rng :=
  let lit := fun (r : Rng) =>
    let (i, r) := r.below n
    let (s, r) := r.below 2
    ((i, s == 1), r)
  let (a, r) := lit r
  let (b, r) := lit r
  let (c, r) := lit r
  let cl := [a, b, c]
  (if Dpll.clauseEval σ cl then cl else (a.1, !a.2) :: [b, c], r)

def plantedClauses (n : Nat) (σ : Nat → Bool) : Nat → Rng → Dpll.CNF × Rng
  | 0, r => ([], r)
  | k + 1, r =>
    let (c, r) := plantedClause n σ r
    let (cs, r) := plantedClauses n σ k r
    (c :: cs, r)

def shuffleEach : Dpll.CNF → Rng → Dpll.CNF × Rng
  | [], r => ([], r)
  | c :: cs, r =>
    let (c, r) := shuffle c r
    let (cs, r) := shuffleEach cs r
    (c :: cs, r)

/-- One instance: a target status uniformly, then (for contingent) a trap with probability 3/4,
else an even instance; a CNF, or its dual for tautologies and half the contingent ones. -/
def sampleXInst (g : XGen) (r : Rng) : XInst × Rng :=
  let (c, r) := r.below 3
  let (form, r) := r.below 2
  let (kind, r) := r.below 4
  let V := g.verts
  let (es, r) := drawGraph V g.fuel r
  let (es, r) := shuffle es r
  let n := es.length
  let (bits, r) := r.draws 2 n
  let witness := bits.map (· == 1)
  let σ := Dpll.ofList witness
  let t0 : Tseitin := { verts := V, edges := es, charge := [] }
  let base := (List.range V).map fun v => parity ((t0.inc v).map σ)
  let (v0, r) := r.below V
  let even := c == 1 && kind == 0
  let trap := c == 1 && kind != 0
  let charge := if even then base else setAt base v0 (!base.getD v0 false)
  let t : Tseitin := { t0 with charge }
  let tcls := if trap then t.cnf.erase (patClause (t.inc v0) ((t.inc v0).map σ)) else t.cnf
  let (m, r) := r.below (g.extras + 1)
  let (ex, r) := plantedClauses n σ (if trap then m + 1 else m) r
  let (cls, r) := shuffle (tcls ++ ex) r
  let (cls, r) := shuffleEach cls r
  let f := PForm.ofCNF cls
  let claim : Status := if c == 1 then .contingent else if c == 0 then .contradiction else .tautology
  ({ graph := t, cls, witness, claim, form := if c == 2 || (c == 1 && form == 1) then f.dual else f }, r)

def sampleXhard (g : XGen) (r : Rng) : PForm × Rng :=
  let (x, r) := sampleXInst g r
  (x.form, r)

/-- Without certificates: the 26 features of `prop-hard`. -/
def xhardSpec (g : XGen) : Spec PForm :=
  { name := "prop-xhard"
    features := PForm.hardFeatures g.atoms
    numFeatures := 26
    slots := [(statusQ g.atoms).slot]
    sample := sampleXhard g }

/-- With the refutation feature; certified items are answered by `certify`. -/
def xhardCertSpec (g : XGen) (c : RefuteCfg) : Spec PForm :=
  { name := "prop-xhard-cert"
    features := PForm.certFeatures g.atoms c
    numFeatures := 27
    slots := [(statusQ g.atoms).slot]
    sample := sampleXhard g }

/-- The `prop-hard` config; the training seed is the best of 2614–2618 on validation
(`ixai bench typed-xhard-sweep`: 89.5%). Two of those five seeds end near majority accuracy, the
ReLUs dead after training. -/
def logicXhardConfig : Config :=
  { seed := 2614, hidden := 16, lrRaw := 1, epochs := 10, batch := 50, trainSize := 2000, testSize := 200 }

/-- The model behind the certificates, its seed chosen the same way (the first of three tied at
91.8% for certificate + model on validation; seed 2614 gives 58.3%). -/
def logicXhardCertConfig : Config := { logicXhardConfig with seed := 2615 }

example : (Tseitin.mk 2 [(0, 1)] [true, false]).odd = true := by decide

/-- A triangle with one charged vertex: three clauses-per-vertex over two edges each. -/
example : Dpll.solve (Tseitin.mk 3 [(0, 1), (1, 2), (2, 0)] [true, false, false]).cnf = false := by decide

-- Drawn instances pass `check`, and their claimed status is the DPLL label.
#guard ((List.range 12).foldl (fun (acc : List XInst × Rng) _ =>
    let (x, r) := sampleXInst { XGen.default with verts := 8 } acc.2
    (x :: acc.1, r)) ([], Rng.seeded 7)).1.all fun x =>
  x.check 12 && x.claim == fastStatus 12 x.form

end Typed
end IxAICore
