import IxCC.Fir.Proof.Sim
import IxCC.Anf.Proof.Lang
import IxCC.Sem.TracedSim

/-! # `Fir.convert_correct`

The Anf → Fir lowering is correct for the first-order fragment it accepts
(design note 03 §2.2, 06 S31): for every program `A` that `Fir.lower`
lowers to `F` (it declines closures with `fir.closures`, so every program it
accepts is first order), every global `g` below the size and related
argument lists of its arity,

`Sem.Sim (VR A) (fun k => N · (k + 1)) (Anf.run A · g xs) (Fir.run F · g ws)`

with `N = Fir.tickBound A`:

* **forward at the same clock:** an Anf value at clock `k` is a related Fir
  value at `k`, a trap a trap (Fir charges a subset of Anf's events);
* **timeout with the tick bound:** Anf timing out at `N · (k + 1)` means Fir
  times out at `k` (between two Fir charges, Anf makes fewer than `N`
  charges Fir does not: ticks, non-recursive jumps, the jump entering a
  recursive join point).

A stuck Anf run imposes nothing (Fir is less stuck: arms project only the
fields they use, and `proj` peels `Nat` literals). Related values have the
same program-independent observation (`vr_obs`, with `Fir.obsV`, the
observation Anf's `Lang` instance uses), so the simulation gives behaviour
refinement (`Sem.Sim.refines`). The traced form (decision D-1) follows by
`TSim.ofPure`. -/

set_option autoImplicit false

namespace IxCC.Fir

open IxCC.Sem (Obs)

mutual

/-- A program-independent observation of a Fir value, as Anf's `obsV`:
literals, and constructor trees tagged by the source constructor. -/
def obsV : Val → Option Obs
  | .lit (.nat n) => some (.nat n)
  | .lit (.str s) => some (.bytes s.toUTF8.toList)
  | .ctor c fs =>
    match c.key with
    | .src cid => (obsList fs).map (.ctor cid)
    | .clo .. => none
  | .erased => none

def obsList : List Val → Option (List Obs)
  | [] => some []
  | v :: vs =>
    match obsV v, obsList vs with
    | some o, some os => some (o :: os)
    | _, _ => none

end

end IxCC.Fir

namespace IxCC.Fir.Proof

open IxCC.Sem (Result later ClockMono Sim)
open IxCC.Fir.Lower

variable {A : Anf.Program}

mutual

/-- Related values observe the same. -/
theorem vr_obs : ∀ {v : Anf.Val} {w : Val}, VR A v w → Anf.obsV v = obsV w
  | _, _, .lit (.nat n) => rfl
  | _, _, .lit (.str s) => rfl
  | _, _, .box => rfl
  | .con c vs, .ctor info ws, .con hi hvs _ => by
    have hk := ofKey_key hi
    cases c with
    | src cid =>
      simp only [Anf.obsV, obsV, hk, vrs_obs hvs]
    | clo f n =>
      simp only [Anf.obsV, obsV, hk]

theorem vrs_obs : ∀ {vs : List Anf.Val} {ws : List Val}, VRs A vs ws → Anf.obsList vs = obsList ws
  | _, _, .nil => rfl
  | _, _, .cons hvw hvs => by
    rw [Anf.obsList, obsList, vr_obs hvw, vrs_obs hvs]
    cases obsV _ <;> cases obsList _ <;> rfl

end

/-! ## Runs -/

/-- An Anf run of a global on as many arguments as it has parameters enters
it (a function global's closure applied once, or a CAF's value). -/
theorem anf_run_eq {k : Nat} {g : Anf.GlobalId} {gd : Anf.GDef} (hg : A.global? g = some gd)
    {xs : List Anf.Val} (hl : xs.length = gd.ps.length) :
    Anf.run A k g xs = Anf.callVal A k gd xs := by
  rw [Anf.run_eq, Anf.evalBind_glob, hg]
  simp only [Result.ofOption, Result.bind_ok]
  unfold Anf.globVal Anf.callVal
  simp only [hl, ↓reduceIte]
  cases hps : gd.ps with
  | nil =>
    rw [hps] at hl
    have : xs = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    simp only [Anf.applyN_nil', Result.bind_pure, List.reverse_nil]
  | cons p ps =>
    simp only [Result.bind_ok]
    rw [hps] at hl
    cases xs with
    | nil => simp at hl
    | cons v rest =>
      rw [Anf.applyN_clos]
      congr 1
      funext k'
      have hlen : rest.length = ps.length := by simpa using hl
      have htake : List.take (ps.length + 1) (v :: rest) = v :: rest := List.take_of_length_le (by simp; omega)
      have hdrop : List.drop (ps.length + 1) (v :: rest) = [] := List.drop_of_length_le (by simp; omega)
      simp only [List.length_nil, List.length_cons, Nat.zero_add, hlen, Nat.lt_irrefl, ↓reduceIte,
        Nat.zero_lt_succ, Anf.enter, List.nil_append, List.append_nil, htake, hdrop, Anf.applyN_nil']
      exact Result.bind_pure _

/-- Every global below the size of a lowered program is present. -/
theorem lower_global {F : Program} (h : lower A = .ok F) {g : Anf.GlobalId} (hs : g < A.size) :
    ∃ gd, A.global? g = some gd := by
  obtain ⟨_, _, _, fs, hfs, _⟩ := lower_ok h
  obtain ⟨hm, hall⟩ := functions_ok hfs
  have hmem : g ∈ fs.map (·.1) := by rw [hm]; exact List.mem_range.2 hs
  obtain ⟨⟨g', fd⟩, hfd, rfl⟩ := List.mem_map.1 hmem
  obtain ⟨gd, hgd, _⟩ := hall g' fd hfd
  exact ⟨gd, hgd⟩

/-- **The simulation from one global**, for related arguments of its arity. -/
theorem run_sim {F : Program} (h : lower A = .ok F) {g : Anf.GlobalId} (hs : g < A.size)
    {gd : Anf.GDef} (hg : A.global? g = some gd) {xs : List Anf.Val} {ws : List Val} (hvs : VRs A xs ws)
    (hl : xs.length = gd.ps.length) :
    Sim (VR A) (fun k => tickBound A * (k + 1)) (fun k => Anf.run A k g xs) (fun k => run F k g ws) := by
  have S := setting_of h
  obtain ⟨fd, hfd, hfun⟩ := S.funs hg hs
  have hc : ∀ a, Corr A (tickBound A) a 0 (Anf.run A a g xs) (fun k => run F k g ws) := by
    intro a
    have := call_corr S (fun a' _ => stmt S a') hg hs hfun hvs hl (a := a)
    rw [anf_run_eq hg hl]
    exact this.congr fun k => by rw [run_eq, evalCall_of F k hfd ws]
  refine ⟨fun k hk => ⟨k, ?_⟩, fun k hk => .inl ((hc _).tmo hk k (by
    rw [Nat.mul_succ]; omega))⟩
  cases hr : Anf.run A k g xs with
  | ok v =>
    obtain ⟨w, hw, hvw⟩ := (hc k).ok v hr
    rw [hw]; exact .ok hvw
  | timeout => exact absurd hr hk
  | resource f => rw [(hc k).res f hr]; exact .resource f
  | trap => rw [(hc k).trap hr]; exact .trap
  | stuck => exact .stuck

end IxCC.Fir.Proof

namespace IxCC.Fir

open IxCC.Sem (Sim TSim)
open IxCC.Fir.Proof

/-- **`Fir.convert_correct`** (design note 03 §2.2, 06 S31; M2.4): for an
Anf program `Fir.lower` accepts (the first-order fragment), related values
observe the same, every root is a global below the size, and from every
global, on related arguments of its arity, Fir simulates Anf with the tick
bound's clock map `k ↦ N · (k + 1)`, `N = Fir.tickBound A`: forward at the
same clock, and Anf timing out at `N · (k + 1)` gives Fir timing out at
`k`. -/
theorem convert_correct {A : Anf.Program} {F : Program} (h : lower A = .ok F) :
    (∀ v w, VR A v w → Anf.obsV v = obsV w) ∧ F.exports = A.roots ∧ (∀ r ∈ A.roots, r < A.size) ∧
      ∀ g gd, g < A.size → A.global? g = some gd → ∀ xs ws, VRs A xs ws → xs.length = gd.ps.length →
        Sim (VR A) (fun k => tickBound A * (k + 1)) (fun k => Anf.run A k g xs) (fun k => run F k g ws) :=
  ⟨fun _ _ hvw => vr_obs hvw, (lower_fields h).2.1, (lower_ok h).2.2.1,
    fun _ _ hs hg _ _ hvs hl => run_sim h hs hg hvs hl⟩

/-- `Fir.convert_correct` in the traced shape (decision D-1), for every
environment and event type. -/
theorem convert_correct_traced {Env E : Type} {A : Anf.Program} {F : Program} (h : lower A = .ok F)
    {g : Anf.GlobalId} {gd : Anf.GDef} (hs : g < A.size) (hg : A.global? g = some gd) {xs : List Anf.Val}
    {ws : List Val} (hvs : VRs A xs ws) (hl : xs.length = gd.ps.length) :
    TSim (Env := Env) (E := E) (VR A) (fun k => tickBound A * (k + 1))
      (fun _ k => Sem.Traced.lift (Anf.run A k g xs)) (fun _ k => Sem.Traced.lift (run F k g ws)) :=
  TSim.ofPure (run_sim h hs hg hvs hl)

end IxCC.Fir
