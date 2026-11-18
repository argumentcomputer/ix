import Aiur.Plonk.MsgSound

/-!
# A row's running sum, and uniform rows

The running-sum gates of a row form a chain: lookup `k`'s `s` reference is
the previous gated lookup's `s'`, the first is `sumIn`, the last is the row's
final sum. `chainOk` checks every lookup's certificate and this chain;
`chain_sound` sums the per-lookup facts `q · fp = m`, `s' = s + q` along it.
With every fingerprint nonzero, `q = m / fp`, so the row's final sum minus
`sumIn` is `logupEval γ β` of the row's ledger (`msgChain_sound`):
`logupEval γ β L = Σ_t L(t) / fp γ β t`.

`rowCheck a r P poolIdx` lowers row `r` against the pool `P` and checks its
constraints (`rowOkG`) and its messages and chain (`msgChainOk`) against the
row's gates followed by `P`'s gates. `rowCheck_sound` turns a wire assignment
satisfying those gates into `a.circuit.Holds` at row `r` and the row's
LogUp equation.

`uniformB a`: no constraint, multiplicity or argument reads a fixed column.
Then `rowCheck a r P poolIdx = rowCheck a 0 P poolIdx` (`rowCheck_uniform`),
so a unit table is checked once.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Template SlotDef Ledger)
open Aiur.Tiling.WideStage (Air)
open Aiur.Scalar.Circuit (ArithExpr)
open Lower (Fr LGate Ref)

/-- `Σ_t L(t) / fp γ β t`. -/
noncomputable def logupEval (γ β : Fr) : Ledger Fr →+ Fr :=
  Finsupp.liftAddHom fun t => AddMonoidHom.mulRight (fp γ β t)⁻¹

theorem logupEval_single (γ β : Fr) (t : List Fr) (m : Fr) :
    logupEval γ β (Finsupp.single t m) = m * (fp γ β t)⁻¹ := by
  simp [logupEval]

theorem map_range_getD {α β : Type} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun k => f (l.getD k d)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

namespace AirIn

theorem logupEval_rowLedger (a : Air Fr) (x : Nat → Fr) (γ β : Fr) :
    logupEval γ β (a.circuit.rowLedger x) =
      ((List.range a.circuit.lookups.length).map fun k =>
        (lookupAt a k).multiplicity.denote x * (fp γ β ((lookupAt a k).tuple x))⁻¹).sum := by
  simp only [Tiling.Circuit.rowLedger, map_list_sum, List.map_map, lookupAt]
  rw [map_range_getD a.circuit.lookups ⟨.const 0, []⟩
    (fun l => l.multiplicity.denote x * (fp γ β (l.tuple x))⁻¹)]
  congr 1
  apply List.map_congr_left
  intro l _
  simp [Tiling.Lookup.entry, logupEval_single]

/-! ## The chain -/

/-- Every lookup of `ks` is checked, and the running sums chain from `cur`
to `fin`; `cert k` is lookup `k`'s certificate. -/
def chainOk (a : Air Fr) (r : Nat) (G : Nat → Option LGate) (cert : Nat → Except String (Option MsgCert)) :
    List Nat → Ref → Ref → Bool
  | [], cur, fin => cur == fin
  | k :: ks, cur, fin =>
      match cert k with
      | .ok none => certNoneOk a r k && chainOk a r G cert ks cur fin
      | .ok (some c) => certSomeOk a r k G c && c.sIn == cur && chainOk a r G cert ks c.sOut fin
      | .error _ => false

theorem chain_sound {a : Air Fr} {r : Nat} {G : Nat → Option LGate} {cert : Nat → Except String (Option MsgCert)}
    (wireOf : Ref → Nat) (cellWire : Nat → Nat) (hcell : ∀ x, x % 4 = 0 → wireOf x = cellWire (x / 8))
    (w : Nat → Fr) (hold : ∀ i g, G i = some g → (g.inst wireOf).Holds w)
    (main : Nat → Nat → Fr) (hmain : ∀ v, main r v = w (cellWire v)) :
    ∀ (ks : List Nat) (cur fin : Ref), chainOk a r G cert ks cur fin = true →
      (∀ k ∈ ks, fp (w (wireOf Lower.gammaRef)) (w (wireOf Lower.betaRef))
        ((lookupAt a k).tuple (a.assign main r)) ≠ 0) →
      w (wireOf fin) - w (wireOf cur) =
        (ks.map fun k => (lookupAt a k).multiplicity.denote (a.assign main r) *
          (fp (w (wireOf Lower.gammaRef)) (w (wireOf Lower.betaRef)) ((lookupAt a k).tuple (a.assign main r)))⁻¹).sum
  | [], cur, fin, ok, _ => by
      simp only [chainOk, beq_iff_eq] at ok
      simp [ok]
  | k :: ks, cur, fin, ok, hfp => by
      simp only [chainOk] at ok
      split at ok
      · simp only [Bool.and_eq_true] at ok
        have ih := chain_sound wireOf cellWire hcell w hold main hmain ks cur fin ok.2
          (fun k' hk' => hfp k' (List.mem_cons_of_mem _ hk'))
        rw [List.map_cons, List.sum_cons, mult_zero_of_certNoneOk ok.1 main, zero_mul, zero_add, ih]
      · rename_i c _
        simp only [Bool.and_eq_true, beq_iff_eq] at ok
        obtain ⟨⟨hc, hin⟩, hrest⟩ := ok
        have ih := chain_sound wireOf cellWire hcell w hold main hmain ks c.sOut fin hrest
          (fun k' hk' => hfp k' (List.mem_cons_of_mem _ hk'))
        obtain ⟨hq, hs⟩ := message_of_certSomeOk hc wireOf cellWire hcell w hold main hmain
        have hf := hfp k List.mem_cons_self
        rw [List.map_cons, List.sum_cons, ← ih, ← hq, hs, hin, mul_assoc, mul_inv_cancel₀ hf]
        ring
      · exact absurd ok (by simp)

/-! ## A row's messages -/

/-- A row's gates followed by the gates of the pool `P`. -/
def rowPool (gs P : Array LGate) (i : Nat) : Option LGate :=
  if i < gs.size then gs[i]? else P[i - gs.size]?

theorem rowPool_mem {gs P : Array LGate} {i : Nat} {g : LGate} (h : rowPool gs P i = some g) :
    g ∈ gs ∨ g ∈ P := by
  unfold rowPool at h
  split at h
  · exact .inl (Array.mem_of_getElem? h)
  · exact .inr (Array.mem_of_getElem? h)

/-- The defining gate of each row-local wire and each lookup's gates
(untrusted index). -/
def msgIndex (gs : Array LGate) : Std.HashMap Ref Nat × Std.HashMap Nat (Array Nat) := Id.run do
  let mut localDef : Std.HashMap Ref Nat := {}
  let mut byMsg : Std.HashMap Nat (Array Nat) := {}
  for h : i in [0:gs.size] do
    let g := gs[i]
    match g.msg with
    | some k => byMsg := byMsg.insert k ((byMsg.getD k #[]).push i)
    | none => if g.root.isNone then localDef := localDef.insert g.c i
  return (localDef, byMsg)

/-- Every lookup of row `r` is checked against `rowPool gs P`, and the
running sums chain from `sumIn` to `fin`. `poolIdx` (untrusted) names the
index in `P` of each pool wire's defining gate. -/
def msgChainOk (a : Air Fr) (r : Nat) (gs P : Array LGate) (poolIdx : Ref → Option Nat) (fin : Ref) : Bool :=
  let (localDef, byMsg) := msgIndex gs
  let n := gs.size
  let defOf (x : Ref) : Option Nat := if x % 4 == 2 then (poolIdx x).map (· + n) else localDef[x]?
  chainOk a r (rowPool gs P) (fun k => msgCert a (rowPool gs P) defOf (byMsg.getD k #[]))
    (List.range a.circuit.lookups.length) Lower.sumIn fin

theorem msgChain_sound {a : Air Fr} {r : Nat} {gs P : Array LGate} {poolIdx : Ref → Option Nat} {fin : Ref}
    (ok : msgChainOk a r gs P poolIdx fin = true)
    (wireOf : Ref → Nat) (cellWire : Nat → Nat) (hcell : ∀ x, x % 4 = 0 → wireOf x = cellWire (x / 8))
    (w : Nat → Fr) (hrow : ∀ g ∈ gs, (g.inst wireOf).Holds w) (hpool : ∀ g ∈ P, (g.inst wireOf).Holds w)
    (main : Nat → Nat → Fr) (hmain : ∀ v, main r v = w (cellWire v))
    (hfp : ∀ l ∈ a.circuit.lookups,
      fp (w (wireOf Lower.gammaRef)) (w (wireOf Lower.betaRef)) (l.tuple (a.assign main r)) ≠ 0) :
    w (wireOf fin) - w (wireOf Lower.sumIn) =
      logupEval (w (wireOf Lower.gammaRef)) (w (wireOf Lower.betaRef)) (a.circuit.rowLedger (a.assign main r)) := by
  rw [logupEval_rowLedger]
  refine chain_sound wireOf cellWire hcell w ?_ main hmain _ _ _ ok ?_
  · intro i g hg
    rcases rowPool_mem hg with h | h
    · exact hrow g h
    · exact hpool g h
  · intro k hk
    have hk' := List.mem_range.mp hk
    exact hfp _ (by simp [lookupAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', List.getElem_mem])

/-! ## A row's constraints -/

/-- Every constraint of row `r` is checked on its cone in `gs`. -/
def rowOkG (gs : Array LGate) (a : Air Fr) (r : Nat) : Bool :=
  (List.range a.circuit.constraints.length).all (coneOkR gs a.circuit.width (rowConstraint a r))

theorem constraints_of_gatesG {gs : Array LGate} {a : Air Fr} {r : Nat} (ok : rowOkG gs a r = true)
    (wireOf : Ref → Nat) (cellWire : Nat → Nat) (hcell : ∀ x, x % 4 = 0 → wireOf x = cellWire (x / 8))
    (w : Nat → Fr) (hold : ∀ g ∈ gs, (g.inst wireOf).Holds w)
    (main : Nat → Nat → Fr) (hmain : ∀ v, main r v = w (cellWire v)) :
    a.circuit.Holds (a.assign main r) := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨T, sr, hcheck, hcover, hreal, hcols⟩ :=
    coneOkR_spec (List.all_eq_true.mp ok j (List.mem_range.mpr hj))
  have hold' : ∀ g ∈ gs.toList.map (Lower.LGate.inst wireOf), g.Holds w := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact hold g' (Array.mem_toList_iff.mp hg')
  have holds := relationsHold_of_realised (realised_of_realisedB hreal wireOf) hold'
  refine constraint_of_cone hcheck hcover holds ?_ hj
  intro v _ s hs
  have hslot := colSlot_column hs
  have hc' := List.all_eq_true.mp hcols (SlotDef.column v, s)
    (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hslot))
  simp only [Bool.and_eq_true, beq_iff_eq] at hc'
  simp [Function.comp, hcell _ hc'.1, hc'.2, hmain]

/-! ## A row -/

def rowCheck (a : Air Fr) (r : Nat) (P : Lower.Pool) (poolIdx : Ref → Option Nat) : Bool :=
  let s := lowerRowState a r P
  rowOkG (s.gates.filter (·.tag == .constraint)) a r && msgChainOk a r s.gates P.gates poolIdx s.sum

theorem rowCheck_sound {a : Air Fr} {r : Nat} {P : Lower.Pool} {poolIdx : Ref → Option Nat}
    (ok : rowCheck a r P poolIdx = true)
    (wireOf : Ref → Nat) (cellWire : Nat → Nat) (hcell : ∀ x, x % 4 = 0 → wireOf x = cellWire (x / 8))
    (w : Nat → Fr) (hrow : ∀ g ∈ (lowerRowState a r P).gates, (g.inst wireOf).Holds w)
    (hpool : ∀ g ∈ P.gates, (g.inst wireOf).Holds w)
    (main : Nat → Nat → Fr) (hmain : ∀ v, main r v = w (cellWire v)) :
    a.circuit.Holds (a.assign main r) ∧
      ((∀ l ∈ a.circuit.lookups,
          fp (w (wireOf Lower.gammaRef)) (w (wireOf Lower.betaRef)) (l.tuple (a.assign main r)) ≠ 0) →
        w (wireOf (lowerRowState a r P).sum) - w (wireOf Lower.sumIn) =
          logupEval (w (wireOf Lower.gammaRef)) (w (wireOf Lower.betaRef))
            (a.circuit.rowLedger (a.assign main r))) := by
  unfold rowCheck at ok
  simp only [Bool.and_eq_true] at ok
  refine ⟨constraints_of_gatesG ok.1 wireOf cellWire hcell w ?_ main hmain, fun hfp =>
    msgChain_sound ok.2 wireOf cellWire hcell w hrow hpool main hmain hfp⟩
  intro g hg
  exact hrow g (Array.mem_of_mem_filter hg)

/-! ## Uniform rows -/

def uniformB (a : Air Fr) : Bool :=
  readsMainOnly a && a.circuit.lookups.all fun l =>
    l.multiplicity.inBounds a.circuit.width && l.args.all (·.inBounds a.circuit.width)

theorem lookupAt_inBounds {a : Air Fr} (h : uniformB a = true) (k : Nat) :
    (lookupAt a k).multiplicity.inBounds a.circuit.width = true ∧
      ∀ e ∈ (lookupAt a k).args, e.inBounds a.circuit.width = true := by
  simp only [uniformB, Bool.and_eq_true, List.all_eq_true] at h
  unfold lookupAt
  cases hk : a.circuit.lookups[k]? with
  | none => simp [List.getD_eq_getElem?_getD, hk, ArithExpr.inBounds]
  | some l =>
      have hl := h.2 l (List.mem_of_getElem? hk)
      simpa [List.getD_eq_getElem?_getD, hk] using hl

theorem multExpr_uniform {a : Air Fr} (h : uniformB a = true) (r : Nat) : multExpr a r = multExpr a 0 := by
  funext k
  simp [multExpr, fixRow_of_inBounds a _ _ (lookupAt_inBounds h k).1]

theorem argExprs_uniform {a : Air Fr} (h : uniformB a = true) (r : Nat) : argExprs a r = argExprs a 0 := by
  funext k
  unfold argExprs
  apply List.map_congr_left
  intro e he
  rw [fixRow_of_inBounds a _ _ ((lookupAt_inBounds h k).2 e he),
    fixRow_of_inBounds a _ _ ((lookupAt_inBounds h k).2 e he)]

theorem msgCircuit_uniform {a : Air Fr} (h : uniformB a = true) (r : Nat) : msgCircuit a r = msgCircuit a 0 := by
  funext k count
  simp only [msgCircuit, qConstraint, countConstraint, multExpr_uniform h r, argExprs_uniform h r]

theorem rowConstraint_uniformB {a : Air Fr} (h : uniformB a = true) (r : Nat) :
    rowConstraint a r = rowConstraint a 0 := by
  funext j
  simp only [uniformB, Bool.and_eq_true] at h
  exact rowConstraint_uniform a h.1 r j

theorem table_uniform {a : Air Fr} (h : uniformB a = true) (r : Nat) : table a r = table a 0 := by
  have hc : ∀ r, a.circuit.constraints.map (fixRow a r) = a.circuit.constraints := by
    intro r
    simp only [uniformB, readsMainOnly, Bool.and_eq_true, List.all_eq_true] at h
    conv => rhs; rw [← List.map_id a.circuit.constraints]
    exact List.map_congr_left fun e he => fixRow_of_inBounds a r e (h.1 e he)
  have hl : ∀ r, a.circuit.lookups.map (fun l => (⟨fixRow a r l.multiplicity, l.args.map (fixRow a r)⟩ :
      Tiling.Lookup Fr)) = a.circuit.lookups := by
    intro r
    simp only [uniformB, Bool.and_eq_true, List.all_eq_true] at h
    conv => rhs; rw [← List.map_id a.circuit.lookups]
    refine List.map_congr_left fun l hl => ?_
    have hl' := h.2 l hl
    rw [fixRow_of_inBounds a r _ hl'.1]
    have : l.args.map (fixRow a r) = l.args := by
      conv => rhs; rw [← List.map_id l.args]
      exact List.map_congr_left fun e he => fixRow_of_inBounds a r e (hl'.2 e he)
    simp [this]
  unfold table
  simp only [hc, hl]

theorem certNoneOk_uniform {a : Air Fr} (h : uniformB a = true) (r k : Nat) :
    certNoneOk a r k = certNoneOk a 0 k := by
  simp only [certNoneOk, multExpr_uniform h r]

theorem certSomeOk_uniform {a : Air Fr} (h : uniformB a = true) (r k : Nat) (G : Nat → Option LGate)
    (c : MsgCert) : certSomeOk a r k G c = certSomeOk a 0 k G c := by
  simp only [certSomeOk, msgCircuit_uniform h r]

theorem chainOk_uniform {a : Air Fr} (h : uniformB a = true) (r : Nat) (G : Nat → Option LGate)
    (cert : Nat → Except String (Option MsgCert)) :
    ∀ ks cur fin, chainOk a r G cert ks cur fin = chainOk a 0 G cert ks cur fin
  | [], _, _ => rfl
  | k :: ks, cur, fin => by
      simp only [chainOk, certNoneOk_uniform h r k, certSomeOk_uniform h r k,
        chainOk_uniform h r G cert ks]

theorem rowCheck_uniform {a : Air Fr} (h : uniformB a = true) (r : Nat) (P : Lower.Pool)
    (poolIdx : Ref → Option Nat) : rowCheck a r P poolIdx = rowCheck a 0 P poolIdx := by
  simp only [rowCheck, lowerRowState, table_uniform h r, rowOkG, rowConstraint_uniformB h r, msgChainOk,
    chainOk_uniform h r]

theorem lowerRowState_uniform {a : Air Fr} (h : uniformB a = true) (r : Nat) (P : Lower.Pool) :
    lowerRowState a r P = lowerRowState a 0 P := by
  simp only [lowerRowState, table_uniform h r]

end AirIn

end Aiur.Plonk
