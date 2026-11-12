import IxCC.Own.Plain.Proof.Owned.Simulation
import IxCC.Own.Plain.Proof.EvalShape
import IxCC.Own.Rc.Proof.LeakFreedom

/-! # Accepted body maps refine the source and reclaim

`checkContractOwned_refines` and `checkOwned_refines` have exactly the conclusions of the landed
`checked_contract_program_refines` and `checked_program_refines`; their premise is the ownership
checker instead of equality with the canonical producer's map. Reclamation follows from refinement
and the producer-independent heap-shape theorem (`call_heap_shape`), as it does today. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

mutual
theorem erases_sound : ∀ (c : Code) (s : Fir.Code), erases c s = true → eraseCode c = s
  | .act _ k, s, h => by
    rw [erases] at h
    rw [eraseCode]
    exact erases_sound k s h
  | .bind x r k, s, h => by
    cases s with
    | bind x' r' k' =>
      simp only [erases, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hk⟩ := h
      rw [eraseCode, erases_sound k k' hk]
    | _ => simp [erases] at h
  | .jp j ps cs rec b k, s, h => by
    cases s with
    | jp j' ps' rec' b' k' =>
      simp only [erases, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hb⟩, hk⟩ := h
      rw [eraseCode, erases_sound b b' hb, erases_sound k k' hk]
    | _ => simp [erases] at h
  | .jmp j args, s, h => by
    cases s with
    | jmp j' args' =>
      simp only [erases, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | _ => simp [erases] at h
  | .case x alts d, s, h => by
    cases s with
    | case x' alts' d' =>
      simp only [erases, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, ha⟩, hd⟩ := h
      rw [eraseCode, erasesAlts_sound alts alts' ha, erasesOpt_sound d d' hd]
    | _ => simp [erases] at h
  | .ret a, s, h => by
    cases s with
    | ret a' =>
      simp only [erases, decide_eq_true_eq] at h
      subst h; rfl
    | _ => simp [erases] at h
  | .tcall f args, s, h => by
    cases s with
    | tcall f' args' =>
      simp only [erases, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | _ => simp [erases] at h
  | .trap, s, h => by
    cases s with
    | trap => rfl
    | _ => simp [erases] at h
theorem erasesAlts_sound : ∀ (alts : List Alt) (alts' : List Fir.Alt),
    erasesAlts alts alts' = true → eraseAlts alts = alts'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [erasesAlts] at h
  | _ :: _, [], h => by simp [erasesAlts] at h
  | .mk key b :: rest, .mk key' b' :: rest', h => by
    simp only [erasesAlts, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hb⟩, hr⟩ := h
    rw [eraseAlts, erases_sound b b' hb, erasesAlts_sound rest rest' hr]
theorem erasesOpt_sound : ∀ (d : Option Code) (d' : Option Fir.Code),
    erasesOpt d d' = true → eraseOpt d = d'
  | none, none, _ => rfl
  | none, some _, h => by simp [erasesOpt] at h
  | some _, none, h => by simp [erasesOpt] at h
  | some c, some s, h => by
    simp only [erasesOpt] at h
    rw [eraseOpt, erases_sound c s h]
end

theorem checkBodyE_ok {fd : Fir.Fun} {body : Code} (h : checkBodyE fd body = .ok ()) :
    eraseCode body = fd.body ∧ checkCode .leaf (Ctx.entry (fd.params.map (·.1))) body = .ok () := by
  unfold checkBodyE at h
  cases he : erases body fd.body
  · simp only [he, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  · simp only [he, ↓reduceIte, pure_bind] at h
    exact ⟨erases_sound _ _ he, h⟩

theorem checkFuns_ok {F : Fir.Program} {candidate : Src.NatMap Code} :
    ∀ {fs : List Fir.FunId}, checkFuns F candidate fs = .ok () →
      ∀ f, f ∈ fs → ∀ fd, F.fun? f = some fd → ∃ body, candidate.get? f = some body ∧
        eraseCode body = fd.body ∧ checkCode .leaf (Ctx.entry (fd.params.map (·.1))) body = .ok ()
  | [], _, _, hf, _, _ => by simp at hf
  | g :: gs, h, f, hf, fd, hfd => by
    unfold checkFuns at h
    cases hg : F.fun? g with
    | none => rw [hg] at h; cases h
    | some gd =>
      cases hb : candidate.get? g with
      | none => rw [hg, hb] at h; cases h
      | some body =>
        simp only [hg, hb] at h
        cases hc : checkBodyE gd body with
        | error e => simp only [hc] at h; cases h
        | ok u =>
          simp only [hc] at h
          rcases List.mem_cons.mp hf with rfl | hf
          · have : gd = fd := Option.some.inj (hg.symm.trans hfd)
            subst this
            exact ⟨body, hb, checkBodyE_ok hc⟩
          · exact checkFuns_ok h f hf fd hfd

theorem checkMapE_ok {F : Fir.Program} {candidate : Src.NatMap Code}
    (h : checkMapE F candidate = .ok ()) : BodiesChecked F candidate := by
  unfold checkMapE at h
  cases hs : sameShape F.funs candidate
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  · simp only [hs, ↓reduceIte, pure_bind] at h
    intro f fd hf hfd
    exact checkFuns_ok h f (List.mem_range.mpr hf) fd hfd

theorem except_isOk {e : Except String Unit} (h : e.isOk = true) : e = .ok () := by
  cases e with
  | error _ => cases h
  | ok u => rfl

theorem checkOwned_contract {F : Fir.Program} {candidate : Src.NatMap Code}
    (h : checkOwned F candidate = true) : checkContractOwned F candidate = true := by
  simp only [checkOwned, checkContractOwned, Bool.and_eq_true] at h ⊢
  exact ⟨⟨programDomain_implies_contractProgramDomain h.1.1, h.1.2⟩, h.2⟩

/-- What the checker established: the contract domain, the Boolean pins, and for every numbered
function a candidate body that erases to its Fir body and checks from its parameters. -/
theorem checkContractOwned_parts {F : Fir.Program} {candidate : Src.NatMap Code}
    (h : checkContractOwned F candidate = true) :
    contractProgramDomain F = true ∧ checkBoolPins F = true ∧
      ∀ f fd, f < F.size → F.fun? f = some fd → ∃ body, candidate.get? f = some body ∧
        eraseCode body = fd.body ∧
        checkCode .leaf (Ctx.entry (fd.params.map (·.1))) body = .ok () := by
  simp only [checkContractOwned, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, checkMapE_ok (except_isOk h.2)⟩

/-- **The milestone-1 induction**, for an accepted map. -/
theorem owned_refines {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractOwned F candidate = true) : ∀ k, AtClockOwned F candidate k := by
  obtain ⟨domain, pins, bodies⟩ := checkContractOwned_parts checked
  exact owned_refines_of domain (checkBoolPins_sound pins) bodies

/-- **An accepted map refines Fir's `evalCall`** (generalises `checked_contract_program_refines`:
same conclusion, the premise the ownership checker). The checker lets a path that ends in `trap`
keep tokens it holds: sound here because a trap ends the whole run (`ResultRel.trap` has no heap
clause, and the process model has no recoverable trap). An embedding with recoverable traps would
need `trap` to require `total = 0`. -/
theorem checkContractOwned_refines {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractOwned F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) := by
  obtain ⟨domain, _, bodies⟩ := checkContractOwned_parts checked
  exact owned_call_of_smaller domain bodies (fun j _ => owned_refines checked j) hf hd hb

/-- **An accepted map refines Fir's `evalCall`** (generalises `checked_program_refines`). -/
theorem checkOwned_refines {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkOwned F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) :=
  checkContractOwned_refines (checkOwned_contract checked) k hf hd hb

theorem checkContractOwned_shape {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractOwned F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) (hh : HeapOk H) {w : Fir.Val}
    (source : Fir.evalCall F k f ws = .ok w) :
    ∃ v after,
      evalCall { source := F, bodies := candidate } k f vs H = .ok (v, after) ∧
      Proof.Den after v w ∧ Balance after external [v] ∧ HeapOk after ∧
      H.size ≤ after.size ∧ ExternalPreserved H after external := by
  have related := checkContractOwned_refines checked k hf hd hb
  rw [source] at related
  obtain ⟨v, after, success, den, balance, preserved⟩ := related.success
  have shape := call_heap_shape { source := F, bodies := candidate } k f H vs hh (dens_bounded hd)
  obtain ⟨heapShape, size, _⟩ := shape v after success
  exact ⟨v, after, success, den, balance, heapShape, size, preserved⟩

/-- **Reclamation for accepted maps** (generalises `checked_program_reclaims`, contract domain):
with no external owner and an ordered heap, releasing the result frees every cell. -/
theorem checkContractOwned_reclaims {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractOwned F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {vs : List RVal} {ws : List Fir.Val}
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hb : Balance H (fun _ => 0) vs)
    (hh : HeapOk H) {w : Fir.Val} (source : Fir.evalCall F k f ws = .ok w) :
    ∃ v after released,
      evalCall { source := F, bodies := candidate } k f vs H = .ok (v, after) ∧
      Proof.Den after v w ∧ dropAll after [v] = some released ∧
      ∀ l, l < released.size → released.cell? l = some .dead := by
  obtain ⟨v, after, success, den, balance, shape, _, _⟩ :=
    checkContractOwned_shape checked k hf hd hb hh source
  obtain ⟨released, dropped, dead⟩ := dropAll_reclaims shape balance
  exact ⟨v, after, released, success, den, dropped, dead⟩

theorem checkOwned_shape {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkOwned F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) (hh : HeapOk H) {w : Fir.Val}
    (source : Fir.evalCall F k f ws = .ok w) :
    ∃ v after,
      evalCall { source := F, bodies := candidate } k f vs H = .ok (v, after) ∧
      Proof.Den after v w ∧ Balance after external [v] ∧ HeapOk after ∧
      H.size ≤ after.size ∧ ExternalPreserved H after external :=
  checkContractOwned_shape (checkOwned_contract checked) k hf hd hb hh source

/-- **Reclamation for accepted maps** (generalises `checked_program_reclaims`). -/
theorem checkOwned_reclaims {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkOwned F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {vs : List RVal} {ws : List Fir.Val}
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hb : Balance H (fun _ => 0) vs)
    (hh : HeapOk H) {w : Fir.Val} (source : Fir.evalCall F k f ws = .ok w) :
    ∃ v after released,
      evalCall { source := F, bodies := candidate } k f vs H = .ok (v, after) ∧
      Proof.Den after v w ∧ dropAll after [v] = some released ∧
      ∀ l, l < released.size → released.cell? l = some .dead :=
  checkContractOwned_reclaims (checkOwned_contract checked) k hf hd hb hh source

end IxCC.Own.Plain
