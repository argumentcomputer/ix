import Aiur.Plonk.RowSound

/-!
# A row's lookup messages from its emitted gates

The gates a message cone reaches live in the row's gates and in the global
pool. `G` is the row's gates followed by the pool gates created so far, and
every cone gate is named by its index in `G`, so realisation is checked in
constant time per template row (`realisedIdx`, `realised_of_realisedIdx`).

`msgCertOk` runs the message template of lookup `k` through
`Template.check`, `coversVars`, `realisedIdx` and `msgColsB` (each column
slot reads the reference its column stands for: the cell of main column
`c`, or the `γ`, `β`, `q`, `s`, `s'` references).
`message_of_gates`: a wire assignment satisfying `G`'s gates gives
`q · fp γ β tuple = multiplicity` and `s' = s + q` for lookup `k` at row `r`,
with `γ, β, q, s, s'` the values of the wires of those references.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Template SlotDef Row Term)
open Aiur.Tiling.WideStage (Air)
open Lower (LGate Ref)

section Generic

variable {F : Type} [Field F] [DecidableEq F]

def realisedIdx (T : Template F) (sr : Nat → Ref) (idx : Array Nat) (G : Nat → Option (LGate F)) : Bool :=
  T.rows.zipIdx.all fun (row, i) =>
    match row with
    | .gate [lane] false _ =>
        match G (idx.getD i 0) with
        | some g => laneMatches sr lane g
        | none => false
    | _ => false

omit [Field F] [DecidableEq F] in
/-- The gates `G` names, instantiated. -/
def instOf (G : Nat → Option (LGate F)) (wireOf : Ref → Nat) (h : Gate F) : Prop :=
  ∃ i g, G i = some g ∧ g.inst wireOf = h

theorem realised_of_realisedIdx {T : Template F} {sr : Nat → Ref} {idx : Array Nat} {G : Nat → Option (LGate F)}
    (h : realisedIdx T sr idx G = true) (wireOf : Ref → Nat) :
    Realised T (wireOf ∘ sr) (instOf G wireOf) := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  have hm := List.all_eq_true.mp h (T.rows[i], i) (List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hi]))
  simp only at hm
  split at hm
  · rename_i lane roles hrow'
    split at hm
    · rename_i g hg
      refine ⟨g.inst wireOf, ?_, ⟨_, g, hg, rfl⟩⟩
      rw [hrow']; exact rowGate_of_matches hm wireOf roles
    · exact absurd hm (by simp)
  · exact absurd hm (by simp)

namespace AirIn

omit [Field F] [DecidableEq F] in
/-- The column a reference stands for in lookup `k`'s message circuit. -/
def msgCol (a : Air F) (qRef sIn sOut : Ref) (x : Ref) : Option Nat :=
  if x % 4 == 0 then some (x / 8)
  else if x == Lower.gammaRef then some (gammaCol a)
  else if x == Lower.betaRef then some (betaCol a)
  else if x == qRef then some (qCol a)
  else if x == sIn then some (sInCol a)
  else if x == sOut then some (sOutCol a)
  else if x == Lower.sumIn then some (spareCol a)
  else none

omit [Field F] [DecidableEq F] in
/-- Each column slot reads the reference its column stands for. -/
def msgColsB (a : Air F) (T : Template F) (sr : Nat → Ref) (qRef sIn sOut : Ref) : Bool :=
  T.slots.zipIdx.all fun (d, s) =>
    match d with
    | .column c =>
        if c < a.circuit.width then sr s % 4 == 0 && sr s / 8 == c
        else if c == gammaCol a then sr s == Lower.gammaRef
        else if c == betaCol a then sr s == Lower.betaRef
        else if c == qCol a then sr s == qRef
        else if c == sInCol a then sr s == sIn
        else if c == sOutCol a then sr s == sOut
        else c == spareCol a && sr s == Lower.sumIn
    | _ => true

omit [DecidableEq F] in
/-- The cone of `roots` (indices into `G`) through `defOf` (indices into
`G`), pool wires first, each group in creation order. -/
def coneIdxOf (G : Nat → Option (LGate F)) (defOf : Ref → Option Nat) (roots : Array Nat) : Array Nat := Id.run do
  let mut need : Std.HashMap Ref Nat := {}
  let mut stack : List Ref := roots.toList.flatMap fun i =>
    let g := (G i).getD Lower.LGate.empty; [g.a, g.b, g.c]
  while !stack.isEmpty do
    let r := stack.head!
    stack := stack.tail!
    if need.contains r then continue
    if let some i := defOf r then
      need := need.insert r i
      let g := (G i).getD Lower.LGate.empty
      stack := g.a :: g.b :: stack
  let refs := need.toArray.map (·.1)
  let group (r : Ref) : Nat := if r % 4 == 2 then 0 else 1
  let sorted := refs.qsort fun x y => group x < group y || (group x == group y && x < y)
  return sorted.filterMap (need[·]?)

omit [Field F] [DecidableEq F] in
/-- The slot references `toTemplateG defs roots col` assigns: columns in
order of first use, then each defining gate's output. -/
def slotRefsG (defs roots : Array (LGate F)) (col : Ref → Option Nat) : Array Ref := Id.run do
  let mut seen : Std.HashMap Ref Unit := {}
  let mut out : Array Ref := #[]
  for g in defs ++ roots do
    for r in [g.a, g.b, g.c] do
      if (col r).isSome && !seen.contains r then
        seen := seen.insert r ()
        out := out.push r
  for g in defs do out := out.push g.c
  return out

structure MsgCert (F : Type) where
  T : Template F
  sr : Array Ref
  idx : Array Nat
  count : Bool
  qRef : Ref
  sIn : Ref
  sOut : Ref

/-- The certificate of lookup `k` whose gates are `gk` (indices into `G`). -/
def msgCert (a : Air F) (G : Nat → Option (LGate F)) (defOf : Ref → Option Nat) (gk : Array Nat) :
    Except String (Option (MsgCert F)) := do
  if gk.isEmpty then return none
  let counts := gk.filter fun i => ((G i).getD Lower.LGate.empty).tag == .count
  let logups := gk.filter fun i => ((G i).getD Lower.LGate.empty).tag == .logup
  unless logups.size == 2 && counts.size ≤ 1 do throw "malformed message gates"
  let qg := (G logups[0]!).getD Lower.LGate.empty
  let sg := (G logups[1]!).getD Lower.LGate.empty
  let col := msgCol a qg.a sg.a sg.c
  let rootsI := #[logups[0]!, logups[1]!] ++ counts
  let defsI := coneIdxOf G defOf rootsI
  let defs := defsI.map fun i => (G i).getD Lower.LGate.empty
  let roots := rootsI.map fun i => (G i).getD Lower.LGate.empty
  let T ← Lower.toTemplateG defs roots col
  return some ⟨T, slotRefsG defs roots col, defsI ++ rootsI, !counts.isEmpty, qg.a, sg.a, sg.c⟩

/-- The checks of a message certificate: its template passes
`Template.check` against `msgCircuit`, covers its variables, is realised by
the gates `G` names, and its column slots read their references. -/
def certSomeOk (a : Air F) (r k : Nat) (G : Nat → Option (LGate F)) (c : MsgCert F) : Bool :=
  let sr (s : Nat) : Ref := c.sr.getD s 0
  c.T.check (msgCircuit a r k c.count) && coversVars c.T (a.circuit.width + 6) (msgCircuit a r k c.count) &&
    realisedIdx c.T sr c.idx G && msgColsB a c.T sr c.qRef c.sIn c.sOut

/-- A lookup without gates is checked when its multiplicity normalises to 0. -/
def certNoneOk (a : Air F) (r k : Nat) : Bool :=
  (Tiling.Poly.norm (Tiling.Poly.ofExpr (multExpr a r k))).isEmpty

def msgCertOk (a : Air F) (r k : Nat) (G : Nat → Option (LGate F)) (defOf : Ref → Option Nat)
    (gk : Array Nat) : Bool :=
  match msgCert a G defOf gk with
  | .ok none => certNoneOk a r k
  | .ok (some c) => certSomeOk a r k G c
  | .error _ => false

theorem mult_zero_of_certNoneOk {a : Air F} {r k : Nat} (ok : certNoneOk a r k = true)
    (main : Nat → Nat → F) : (lookupAt a k).multiplicity.denote (a.assign main r) = 0 := by
  have h0 := Tiling.Poly.denote_eq_zero_of_norm _ ok (a.assign main r)
  rw [Tiling.Poly.denote_ofExpr] at h0
  simpa [multExpr, fixRow_denote] using h0

theorem message_of_certSomeOk {a : Air F} {r k : Nat} {G : Nat → Option (LGate F)} {c : MsgCert F}
    (ok : certSomeOk a r k G c = true)
    (wireOf : Ref → Nat) (cellWire : Nat → Nat) (hcell : ∀ x, x % 4 = 0 → wireOf x = cellWire (x / 8))
    (w : Nat → F) (hold : ∀ i g, G i = some g → (g.inst wireOf).Holds w)
    (main : Nat → Nat → F) (hmain : ∀ v, main r v = w (cellWire v)) :
    w (wireOf c.qRef) * fp (w (wireOf Lower.gammaRef)) (w (wireOf Lower.betaRef))
        ((lookupAt a k).tuple (a.assign main r)) = (lookupAt a k).multiplicity.denote (a.assign main r) ∧
      w (wireOf c.sOut) = w (wireOf c.sIn) + w (wireOf c.qRef) := by
  unfold certSomeOk at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨⟨⟨hcheck, hcover⟩, hreal⟩, hcols⟩ := ok
  have holds := relationsHold_of_realised (realised_of_realisedIdx hreal wireOf)
    (fun _ ⟨i, g, hg, he⟩ => he ▸ hold i g hg)
  refine message_of_cone (z := w (wireOf Lower.sumIn)) hcheck hcover holds ?_
  intro v hv s hs
  have hslot := colSlot_column hs
  have hc' := List.all_eq_true.mp hcols (SlotDef.column v, s)
    (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hslot))
  simp only at hc'
  simp only [Function.comp, msgView]
  by_cases h1 : v < a.circuit.width
  · simp only [h1, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hc' ⊢
    rw [hcell _ hc'.1, hc'.2, hmain]
  · obtain ⟨d, rfl⟩ : ∃ d, v = a.circuit.width + d := ⟨v - a.circuit.width, by omega⟩
    have hd : d < 6 := by omega
    interval_cases d <;>
      simp [gammaCol, betaCol, qCol, sInCol, sOutCol, spareCol] at hc' ⊢ <;> simp [hc']

theorem message_of_gates {a : Air F} {r k : Nat} {G : Nat → Option (LGate F)} {defOf : Ref → Option Nat}
    {gk : Array Nat} (ok : msgCertOk a r k G defOf gk = true)
    (wireOf : Ref → Nat) (cellWire : Nat → Nat) (hcell : ∀ x, x % 4 = 0 → wireOf x = cellWire (x / 8))
    (w : Nat → F) (hold : ∀ i g, G i = some g → (g.inst wireOf).Holds w)
    (main : Nat → Nat → F) (hmain : ∀ v, main r v = w (cellWire v)) :
    (lookupAt a k).multiplicity.denote (a.assign main r) = 0 ∨
      ∃ c : MsgCert F, msgCert a G defOf gk = .ok (some c) ∧
        w (wireOf c.qRef) * fp (w (wireOf Lower.gammaRef)) (w (wireOf Lower.betaRef))
            ((lookupAt a k).tuple (a.assign main r)) = (lookupAt a k).multiplicity.denote (a.assign main r) ∧
          w (wireOf c.sOut) = w (wireOf c.sIn) + w (wireOf c.qRef) := by
  unfold msgCertOk at ok
  split at ok
  · exact .inl (mult_zero_of_certNoneOk ok main)
  · rename_i c hc
    exact .inr ⟨c, hc, message_of_certSomeOk ok wireOf cellWire hcell w hold main hmain⟩
  · exact absurd ok (by simp)

omit [Field F] [DecidableEq F] in
/-- A row's gates followed by the pool's. -/
def rowPoolGates (s : Lower.St F) (i : Nat) : Option (LGate F) :=
  if i < s.gates.size then s.gates[i]? else s.pool.gates[i - s.gates.size]?

/-- Check every lookup of row `r` by `msgCertOk`; `poolIdx` gives the index
in `s.pool.gates` of each pool wire's defining gate. -/
def checkMessagesR (name : String) (a : Air F) (r : Nat) (s : Lower.St F)
    (poolIdx : Ref → Option Nat) : Except String Unit := do
  let mut localDef : Std.HashMap Ref Nat := {}
  let mut byMsg : Std.HashMap Nat (Array Nat) := {}
  for h : i in [0:s.gates.size] do
    let g := s.gates[i]
    match g.msg with
    | some k => byMsg := byMsg.insert k ((byMsg.getD k #[]).push i)
    | none => if g.root.isNone then localDef := localDef.insert g.c i
  let n := s.gates.size
  let defOf (x : Ref) : Option Nat :=
    if x % 4 == 2 then (poolIdx x).map (· + n) else localDef[x]?
  for k in [0:a.circuit.lookups.length] do
    unless msgCertOk a r k (rowPoolGates s) defOf (byMsg.getD k #[]) do
      throw s!"{name}: lookup {k} is not realised by its gates"

end AirIn

end Generic

end Aiur.Plonk
