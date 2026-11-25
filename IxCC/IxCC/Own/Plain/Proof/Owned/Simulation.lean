import IxCC.Own.Plain.Proof.Owned.Reset
import IxCC.Own.Plain.Proof.Owned.Actions
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.ResultCompose
import IxCC.Own.Plain.Proof.Admission
import IxCC.Fir.Proof.Unfold

/-! # The Own-level induction over an accepted body

`owned_eval` inducts on the **Own** code (`inc`, `dec`, `reset`, and `dropSlot` stutter at the
source clock, while `reuse` refines `bind x (.ctor ..)`), with the source code its erasure, under
the lexicographic clock / code-and-join-stack measure of `Own.Plain.eval`. Calls and charged jumps
use the hypothesis at smaller clocks (`AtClockOwned`), threading caller-backed `@borrowed`
reachability, `@unique` parameter/return uniqueness, live reset slots, and caller-frame `priv`
isolation. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg)

theorem own_jump_measure {j : Fir.JoinId} {J : List JEntry} {e : JEntry} {rest : List JEntry}
    (h : lookupJ j J = some (e, rest)) (hc : e.charged = false) (args : List Arg) :
    e.body.size + jweight (e.after rest) < (Code.jmp j args).size + jweight J := by
  have hw := lookupJ_weight j h
  rw [JEntry.jweight_after]
  simp only [JEntry.weight, hc, Bool.false_eq_true, ↓reduceIte] at hw
  simp only [Code.size]
  omega

private theorem envRoots_bindAll_entryOwned {ρ : Own.Env} :
    ∀ (ps : List Fir.Var) (vs : List RVal) (bs : List Bool),
      vs.length = ps.length → ps.Nodup →
      EnvRoots (Own.bindAll ρ ps vs) (Ctx.entryOwned ps bs) (selectOwnedVals bs vs)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | p :: ps, v :: vs, [], hl, hn => by
    have hnd := List.nodup_cons.mp hn
    have htail := envRoots_bindAll_entryOwned (ρ := ρ.insert p v) ps vs [] (by simpa using hl) hnd.2
    have hp : (Own.bindAll (ρ.insert p v) ps vs).get? p = some v := by
      rw [get_bindAll_untouched _ _ _ _ hnd.1, Src.NatMap.get?_insert_self]
    rw [Ctx.entryOwned_all_false _ [] rfl, selectOwnedVals_nil_left] at htail
    exact EnvRoots.cons hp htail
  | p :: ps, v :: vs, false :: bs, hl, hn => by
    have hnd := List.nodup_cons.mp hn
    have htail := envRoots_bindAll_entryOwned (ρ := ρ.insert p v) ps vs bs (by simpa using hl) hnd.2
    have hp : (Own.bindAll (ρ.insert p v) ps vs).get? p = some v := by
      rw [get_bindAll_untouched _ _ _ _ hnd.1, Src.NatMap.get?_insert_self]
    exact EnvRoots.cons hp htail
  | p :: ps, v :: vs, true :: bs, hl, hn => by
    have hnd := List.nodup_cons.mp hn
    exact envRoots_bindAll_entryOwned (ρ := ρ.insert p v) ps vs bs (by simpa using hl) hnd.2

private theorem bindAll_entryBorrowed_mem {ρ : Own.Env} :
    ∀ (ps : List Fir.Var) (vs : List RVal) (bs : List Bool),
      vs.length = ps.length → ps.Nodup →
      ∀ y, y ∈ Ctx.entryBorrowed ps bs →
        ∃ v, (Own.bindAll ρ ps vs).get? y = some v ∧ v ∈ selectBorrowedVals bs vs
  | [], [], _, _, _, _, hy => by cases hy
  | [], _ :: _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _, _ => by simp at hl
  | _, _, [], _, _, _, hy => by rw [Ctx.entryBorrowed_all_false _ [] rfl] at hy; cases hy
  | p :: ps, v :: vs, false :: bs, hl, hn, y, hy => by
    have hnd := List.nodup_cons.mp hn
    exact bindAll_entryBorrowed_mem (ρ := ρ.insert p v) ps vs bs (by simpa using hl) hnd.2 y hy
  | p :: ps, v :: vs, true :: bs, hl, hn, y, hy => by
    have hnd := List.nodup_cons.mp hn
    simp only [Ctx.entryBorrowed, List.mem_cons] at hy
    rcases hy with rfl | hy
    · refine ⟨v, ?_, List.mem_cons_self⟩
      simp only [Own.bindAll]
      rw [get_bindAll_untouched _ _ _ _ hnd.1, Src.NatMap.get?_insert_self]
    · obtain ⟨u, hu, hm⟩ :=
        bindAll_entryBorrowed_mem (ρ := ρ.insert p v) ps vs bs (by simpa using hl) hnd.2 y hy
      exact ⟨u, hu, List.mem_cons_of_mem _ hm⟩

private theorem bindAll_entryUnique_mem {ρ : Own.Env} :
    ∀ (ps : List Fir.Var) (vs : List RVal) (bs us : List Bool),
      vs.length = ps.length → ps.Nodup →
      ∀ y, y ∈ Ctx.entryUnique ps bs us →
        ∃ v, (Own.bindAll ρ ps vs).get? y = some v ∧ v ∈ selectUniqueVals bs us vs
  | [], [], _, _, _, _, _, hy => by cases hy
  | [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | p :: ps, v :: vs, true :: bs, _ :: us, hl, hn, y, hy => by
    have hnd := List.nodup_cons.mp hn
    exact bindAll_entryUnique_mem (ρ := ρ.insert p v) ps vs bs us (by simpa using hl) hnd.2 y hy
  | p :: ps, v :: vs, true :: bs, [], hl, hn, y, hy => by
    have hnd := List.nodup_cons.mp hn
    exact bindAll_entryUnique_mem (ρ := ρ.insert p v) ps vs bs [] (by simpa using hl) hnd.2 y hy
  | p :: ps, v :: vs, false :: bs, true :: us, hl, hn, y, hy => by
    have hnd := List.nodup_cons.mp hn
    simp only [Ctx.entryUnique, List.mem_cons] at hy
    rcases hy with rfl | hy
    · refine ⟨v, ?_, List.mem_cons_self⟩
      simp only [Own.bindAll]
      rw [get_bindAll_untouched _ _ _ _ hnd.1, Src.NatMap.get?_insert_self]
    · obtain ⟨u, hu, hm⟩ :=
        bindAll_entryUnique_mem (ρ := ρ.insert p v) ps vs bs us (by simpa using hl) hnd.2 y hy
      exact ⟨u, hu, List.mem_cons_of_mem _ hm⟩
  | p :: ps, v :: vs, false :: bs, false :: us, hl, hn, y, hy => by
    have hnd := List.nodup_cons.mp hn
    exact bindAll_entryUnique_mem (ρ := ρ.insert p v) ps vs bs us (by simpa using hl) hnd.2 y hy
  | p :: ps, v :: vs, false :: bs, [], hl, hn, y, hy => by
    have hnd := List.nodup_cons.mp hn
    exact bindAll_entryUnique_mem (ρ := ρ.insert p v) ps vs bs [] (by simpa using hl) hnd.2 y hy
  | p :: ps, v :: vs, [], true :: us, hl, hn, y, hy => by
    have hnd := List.nodup_cons.mp hn
    simp only [Ctx.entryUnique, List.mem_cons] at hy
    rcases hy with rfl | hy
    · refine ⟨v, ?_, List.mem_cons_self⟩
      simp only [Own.bindAll]
      rw [get_bindAll_untouched _ _ _ _ hnd.1, Src.NatMap.get?_insert_self]
    · obtain ⟨u, hu, hm⟩ :=
        bindAll_entryUnique_mem (ρ := ρ.insert p v) ps vs [] us (by simpa using hl) hnd.2 y hy
      exact ⟨u, hu, List.mem_cons_of_mem _ hm⟩
  | p :: ps, v :: vs, [], false :: us, hl, hn, y, hy => by
    have hnd := List.nodup_cons.mp hn
    exact bindAll_entryUnique_mem (ρ := ρ.insert p v) ps vs [] us (by simpa using hl) hnd.2 y hy
  | p :: ps, v :: vs, [], [], _, _, _, hy => by cases hy

private theorem entryUnique_not_borrowed :
    ∀ (ps : List Fir.Var) (bs us : List Bool),
      ps.Nodup → ∀ y, y ∈ Ctx.entryUnique ps bs us → y ∉ Ctx.entryBorrowed ps bs
  | [], _, _, _, _, hy, _ => by cases hy
  | p :: ps, true :: bs, _ :: us, hn, y, hy, hb => by
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hnd.1 ((Ctx.entryUnique_sublist ps bs us).subset hy)
    · exact entryUnique_not_borrowed ps bs us hnd.2 y hy hb
  | p :: ps, true :: bs, [], hn, y, hy, hb => by
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hnd.1 ((Ctx.entryUnique_sublist ps bs []).subset hy)
    · exact entryUnique_not_borrowed ps bs [] hnd.2 y hy hb
  | p :: ps, false :: bs, true :: us, hn, y, hy, hb => by
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hnd.1 ((Ctx.entryBorrowed_sublist ps bs).subset hb)
    · exact entryUnique_not_borrowed ps bs us hnd.2 y hy hb
  | p :: ps, false :: bs, false :: us, hn, y, hy, hb =>
    entryUnique_not_borrowed ps bs us (List.nodup_cons.mp hn).2 y hy hb
  | p :: ps, false :: bs, [], hn, y, hy, hb =>
    entryUnique_not_borrowed ps bs [] (List.nodup_cons.mp hn).2 y hy hb
  | _ :: _, [], _ :: _, _, _, _, hb => by cases hb
  | _ :: _, [], [], _, _, hy, _ => by cases hy

private theorem bindAll_leaf_mem :
    ∀ (ρ : Own.Env) (ps : List Fir.Var) (vs : List RVal),
      vs.length = ps.length →
      ∀ y v, y ∈ ps → (Own.bindAll ρ ps vs).get? y = some v → v ∈ vs
  | _, [], _, _, _, _, hy, _ => by cases hy
  | ρ, p :: ps, v :: vs, hl, y, u, hy, hu => by
    by_cases htail : y ∈ ps
    · exact List.mem_cons_of_mem _ (bindAll_leaf_mem (ρ.insert p v) ps vs (by simpa using hl) y u htail hu)
    · rcases List.mem_cons.mp hy with rfl | hy'
      · simp only [Own.bindAll] at hu
        rw [get_bindAll_untouched _ _ _ _ htail, Src.NatMap.get?_insert_self] at hu
        cases hu; exact List.mem_cons_self
      · exact absurd hy' htail
  | _, _ :: _, [], hl, _, _, _, _ => by simp at hl

/-- Function entry with full `@borrowed`, `@unique`, and `priv` isolation invariants. -/
theorem ownedState_entryFull_exact (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (params : List Fir.Var) (bs us : List Bool) (vs : List RVal) (ws : List Fir.Val)
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hl : vs.length = params.length)
    (hf : fresh [] params = true) (hb : Balance H external (selectOwnedVals bs vs))
    (hbrw : ∀ v, v ∈ selectBorrowedVals bs vs → ReachableFrom H external v)
    (borrows : BorrowSigs := .leaf) (uniqs : UniqSigs := .leaf) (retUniq : Bool := false)
    (ctors : List Lam.CtorInfo := []) (K : Lam.Known := {})
    (priv : Nat → Prop := fun _ => False)
    (huniq : ∀ v, v ∈ selectUniqueVals bs us vs → UniqVal ctors H external (selectOwnedVals bs vs) v)
    (hprivB : ∀ l, priv l → l < H.size)
    (hprivE : ∀ l, priv l → edgeCount H l = 0)
    (hprivArgs : ∀ l, priv l → ∀ v, v ∈ vs → v ≠ .loc l) :
    OwnedState functions H external params (Ctx.entryWith params bs us)
      (Fir.bindAll .leaf params ws) (Own.bindAll .leaf params vs) (selectOwnedVals bs vs)
      [] .leaf [] [] borrows uniqs retUniq ctors K priv .leaf [] := by
  have hn : params.Nodup := by simpa using fresh_nodup_append List.nodup_nil hf
  have htok := Ctx.Tokens.entryWith params bs us hn
  have hroots := envRoots_bindAll_entryOwned (ρ := .leaf) params vs bs hl hn
  have hden0 : EnvDen H [] (.leaf : Fir.Env) (.leaf : Own.Env) := by intro x hx; simp at hx
  have hden : EnvDen H params (Fir.bindAll .leaf params ws) (Own.bindAll .leaf params vs) := by
    simpa using hden0.bindAll params hd hl
  have himm : ∀ y, (Ctx.entryWith params bs us).isImm y = false := fun _ => rfl
  have hbrw0 : ∀ y, (Ctx.entryWith params bs us).brw.get? y = none := fun _ => rfl
  have hownSub := Ctx.entryOwned_sublist params bs
  have hbrwSub := Ctx.entryBorrowed_sublist params bs
  have hownNodup : (Ctx.entryOwned params bs).Nodup := hn.sublist hownSub
  have hbal : Balance H external (selectOwnedVals bs vs ++ []) := by simpa using hb
  refine ⟨fun y hy => ?_, ⟨_, htok, hroots⟩, ⟨[], Ctx.SlotKeys.empty rfl, rfl⟩, hbal,
    fun y hy => ?_, hn,
    fun y hy => absurd hy (by simp [himm y]), fun y hy => ?_, fun y hy => ?_, fun y e hy => ?_,
    fun _ _ hc => by simp [Ctx.entryWith, Src.NatMap.get?] at hc,
    fun _ _ _ _ hp => by simp [Ctx.entryWith, Src.NatMap.get?] at hp,
    fun _ _ _ hc => by simp [Ctx.entryWith, Src.NatMap.get?] at hc,
    fun _ _ _ _ _ _ hp => by simp [Ctx.entryWith, Src.NatMap.get?] at hp,
    fun y hy => ?_,
    fun _ _ _ hrs => by simp [Ctx.entryWith, Src.NatMap.get?] at hrs,
    hprivB, hprivE, fun l hl' y hy hEq => ?_,
    fun _ _ _ hs => by simp [Ctx.entryWith, Src.NatMap.contains, Src.NatMap.get?] at hs,
    .nil _ _ _ _, .nil _⟩
  · simp only [Ctx.avail_eq, himm, Ctx.borrowed_eq, hbrw0, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq] at hy
    rcases hy with (hp | hb') | hpb
    · exact hden y (hownSub.subset (htok.mem hp))
    · simp at hb'
    · rw [Ctx.pbrw_entryWith us hn] at hpb
      exact hden y (hbrwSub.subset (of_decide_eq_true hpb))
  · simp only [Ctx.known_eq, himm, hbrw0, Option.isSome_none, Bool.or_false, Bool.false_or,
      Bool.or_eq_true] at hy
    rcases hy with ho | hpb
    · exact hownSub.subset (Ctx.ownHas_ofList hownNodup ho)
    · rw [Ctx.pbrw_entryWith us hn] at hpb
      exact hbrwSub.subset (of_decide_eq_true hpb)
  · simp [Ctx.borrowed_eq, hbrw0] at hy
  · rw [Ctx.pbrw_entryWith us hn] at hy
    obtain ⟨v, hv, hm⟩ := bindAll_entryBorrowed_mem (ρ := .leaf) params vs bs hl hn y
      (of_decide_eq_true hy)
    exact ⟨v, hv, hbrw v hm⟩
  · simp [hbrw0] at hy
  · rw [Ctx.uniq_entryWith hn] at hy
    have hmemU : y ∈ Ctx.entryUnique params bs us := of_decide_eq_true hy
    have hmemO : y ∈ Ctx.entryOwned params bs := (Ctx.entryUnique_sublist_owned params bs us).subset hmemU
    have htok1 : (Ctx.entryWith params bs us).tokens y = 1 := by
      rw [← htok.count y, Ctx.count_nodup hownNodup]; simp [hmemO]
    have hnb : (Ctx.entryWith params bs us).isPbrw y = false := by
      rw [Ctx.pbrw_entryWith us hn]
      simp [entryUnique_not_borrowed params bs us hn y hmemU]
    obtain ⟨v, hv, hmv⟩ := bindAll_entryUnique_mem (ρ := .leaf) params vs bs us hl hn y hmemU
    exact ⟨fun _ => ⟨htok1, hnb⟩, v, hv, (huniq v hmv).sameRefs (fun k => by simp)⟩
  · have hmemP : y ∈ params := by
      simp only [Ctx.avail_eq, himm, Ctx.borrowed_eq, hbrw0, Bool.false_or, Bool.or_eq_true,
        decide_eq_true_eq] at hy
      rcases hy with (hp | hb') | hpb
      · exact hownSub.subset (htok.mem hp)
      · simp at hb'
      · rw [Ctx.pbrw_entryWith us hn] at hpb
        exact hbrwSub.subset (of_decide_eq_true hpb)
    exact hprivArgs l hl' (.loc l) (bindAll_leaf_mem .leaf params vs hl y (.loc l) hmemP hEq) rfl

/-- Function entry with arbitrary borrow mask `bs`: owned parameters hold one token each,
borrowed parameters are backed by `external`. -/
theorem ownedState_entryWith_exact (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (params : List Fir.Var) (bs : List Bool) (vs : List RVal) (ws : List Fir.Val)
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hl : vs.length = params.length)
    (hf : fresh [] params = true) (hb : Balance H external (selectOwnedVals bs vs))
    (hbrw : ∀ v, v ∈ selectBorrowedVals bs vs → ReachableFrom H external v)
    (borrows : BorrowSigs := .leaf) :
    OwnedState functions H external params (Ctx.entryWith params bs)
      (Fir.bindAll .leaf params ws) (Own.bindAll .leaf params vs) (selectOwnedVals bs vs)
      [] .leaf [] [] borrows :=
  ownedState_entryFull_exact functions H external params bs [] vs ws hd hl hf hb hbrw borrows
    (huniq := fun _ hm => by simp [selectUniqueVals_all_false _ [] _ rfl] at hm)
    (hprivB := fun _ h => False.elim h) (hprivE := fun _ h => False.elim h)
    (hprivArgs := fun _ h => False.elim h)

/-- Function entry: parameters own one token each, and the tokens are the arguments' values. -/
theorem ownedState_entry_exact (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (params : List Fir.Var) (vs : List RVal) (ws : List Fir.Val)
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hl : vs.length = params.length)
    (hf : fresh [] params = true) (hb : Balance H external vs) :
    OwnedState functions H external params (Ctx.entry params)
      (Fir.bindAll .leaf params ws) (Own.bindAll .leaf params vs) vs [] .leaf [] [] := by
  have h := ownedState_entryWith_exact functions H external params [] vs ws hd hl hf
    (by simpa [selectOwnedVals_nil_left] using hb)
    (fun _ hm => by simp [selectBorrowedVals_nil_left] at hm)
  simpa [selectOwnedVals_nil_left, Ctx.entryWith_all_false params [] rfl] using h

/-- Function entry: parameters own one token each. -/
theorem ownedState_entry (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (params : List Fir.Var) (vs : List RVal) (ws : List Fir.Val)
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hl : vs.length = params.length)
    (hf : fresh [] params = true) (hb : Balance H external vs) :
    ∃ owned, OwnedState functions H external params (Ctx.entry params)
      (Fir.bindAll .leaf params ws) (Own.bindAll .leaf params vs) owned [] .leaf [] [] ∧
      Balance H external owned :=
  ⟨vs, ownedState_entry_exact functions H external params vs ws hd hl hf hb, hb⟩

/-- The accepted bodies, for the call step. -/
def BodiesChecked (F : Fir.Program) (candidate : Src.NatMap Code)
    (borrows : BorrowSigs := .leaf) (uniqs : UniqSigs := .leaf) : Prop :=
  ∀ f fd, f < F.size → F.fun? f = some fd → ∃ body, candidate.get? f = some body ∧
    eraseCode body = fd.body ∧
    checkCode .leaf
      (Ctx.entryWith (fd.params.map (·.1)) (borrows.getD f []) (uniqs.getD f ([], false)).1)
      body borrows uniqs (uniqs.getD f ([], false)).2 F.ctors F.known = .ok ()

theorem owned_call_of_smaller_full {F : Fir.Program} {candidate : Src.NatMap Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {k : Nat}
    (domain : contractProgramDomain F = true) (bodies : BodiesChecked F candidate borrows uniqs)
    (ih : ∀ j, j < k → AtClockOwned F candidate j borrows uniqs)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat} {priv : Nat → Prop}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external (selectOwnedVals (borrows.getD f []) vs))
    (hbrw : ∀ v, v ∈ selectBorrowedVals (borrows.getD f []) vs → ReachableFrom H external v)
    (huniq : ∀ v, v ∈ selectUniqueVals (borrows.getD f []) (uniqs.getD f ([], false)).1 vs →
      UniqVal F.ctors H external (selectOwnedVals (borrows.getD f []) vs) v)
    (hprivB : ∀ l, priv l → l < H.size)
    (hprivE : ∀ l, priv l → edgeCount H l = 0)
    (hprivArgs : ∀ l, priv l → ∀ v, v ∈ vs → v ≠ .loc l) :
    ResultRelFull H external priv F.ctors (uniqs.getD f ([], false)).2
      (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate, borrows, uniqs } k f vs H) := by
  cases hfd : F.fun? f with
  | none =>
    rw [Fir.evalCall_eq, hfd]
    exact .stuck
  | some fd =>
    obtain ⟨body, hbody, herase, htyped⟩ := bodies f fd hf hfd
    rw [Fir.evalCall_eq, hfd, evalCall_of _ _ _ hfd hbody]
    simp only [Result.ofOption, Result.bind_ok, Fir.callFun, callFun]
    obtain ⟨_, freshParams, scopeBody⟩ := contractProgramDomain_function domain hf hfd
    by_cases hl : ws.length = fd.params.length
    · have hl' : vs.length = fd.params.length := hd.length.trans hl
      simp only [hl, hl', ↓reduceIte]
      refine ResultRelFull.later fun j hj => ?_
      have st := ownedState_entryFull_exact (signatures F) H external (fd.params.map (·.1))
        (borrows.getD f []) (uniqs.getD f ([], false)).1 vs ws hd (by simpa using hl')
        freshParams hb hbrw borrows uniqs (uniqs.getD f ([], false)).2 F.ctors F.known priv
        huniq hprivB hprivE hprivArgs
      have := ih j hj body st (by rw [herase]; exact scopeBody) htyped
      rwa [herase] at this
    · have hl' : ¬vs.length = fd.params.length := by rw [hd.length]; exact hl
      simp only [hl, hl', ↓reduceIte]
      exact .stuck

theorem owned_call_of_smaller_with {F : Fir.Program} {candidate : Src.NatMap Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {k : Nat}
    (domain : contractProgramDomain F = true) (bodies : BodiesChecked F candidate borrows uniqs)
    (ih : ∀ j, j < k → AtClockOwned F candidate j borrows uniqs)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external (selectOwnedVals (borrows.getD f []) vs))
    (hbrw : ∀ v, v ∈ selectBorrowedVals (borrows.getD f []) vs → ReachableFrom H external v)
    (huniq : ∀ v, v ∈ selectUniqueVals (borrows.getD f []) (uniqs.getD f ([], false)).1 vs →
      UniqVal F.ctors H external (selectOwnedVals (borrows.getD f []) vs) v) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate, borrows, uniqs } k f vs H) :=
  (owned_call_of_smaller_full domain bodies ih hf hd hb hbrw huniq
    (priv := fun _ => False) (fun _ h => False.elim h) (fun _ h => False.elim h)
    (fun _ h => False.elim h)).toResultRel

theorem owned_call_of_smaller {F : Fir.Program} {candidate : Src.NatMap Code} {k : Nat}
    (domain : contractProgramDomain F = true) (bodies : BodiesChecked F candidate)
    (ih : ∀ j, j < k → AtClockOwned F candidate j)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) :=
  owned_call_of_smaller_with domain bodies ih hf hd
    (by simpa [Src.NatMap.getD, Src.NatMap.get?, selectOwnedVals_nil_left] using hb)
    (fun _ hm => by simp [Src.NatMap.getD, Src.NatMap.get?, selectBorrowedVals_nil_left] at hm)
    (fun _ hm => by simp [Src.NatMap.getD, Src.NatMap.get?, selectUniqueVals_all_false _ [] _ rfl] at hm)

private theorem evalArgs_mem_arg {ρo : Own.Env} :
    ∀ {args : List Arg} {vs : List RVal}, Own.evalArgs ρo args = some vs →
      ∀ v, v ∈ vs → (∃ a, a ∈ args ∧ Own.evalArg ρo a = some v)
  | [], _, hev, _, hm => by simp [Own.evalArgs] at hev; subst hev; cases hm
  | a :: as, vs, hev, v, hm => by
    cases ha : Own.evalArg ρo a with
    | none => simp [Own.evalArgs, ha] at hev
    | some v0 =>
      cases has : Own.evalArgs ρo as with
      | none => simp [Own.evalArgs, ha, has] at hev
      | some vs' =>
        have : v0 :: vs' = vs := by simpa [Own.evalArgs, ha, has] using hev
        subst this
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨a', hm'', ha'⟩ := evalArgs_mem_arg has v hm'
          exact ⟨a', List.mem_cons_of_mem _ hm'', ha'⟩

private theorem evalArgs_mem_split {ρo : Own.Env} :
    ∀ (bs : List Bool) (args : List Arg) (vs : List RVal),
      Own.evalArgs ρo args = some vs →
      ∀ v, v ∈ vs →
        v ∈ selectOwnedVals bs vs ∨
        ∃ a, a ∈ (bs.zip args).filterMap (fun p => if p.1 then some p.2 else none) ∧
          Own.evalArg ρo a = some v
  | _, [], _, hev, _, hm => by simp [Own.evalArgs] at hev; subst hev; cases hm
  | [], a :: as, _, hev, v, hm => by
    left; rw [selectOwnedVals_nil_left]; exact hm
  | b :: bs, a :: as, vs, hev, v, hm => by
    cases ha : Own.evalArg ρo a with
    | none => simp [Own.evalArgs, ha] at hev
    | some v0 =>
      cases has : Own.evalArgs ρo as with
      | none => simp [Own.evalArgs, ha, has] at hev
      | some vs' =>
        have : v0 :: vs' = vs := by simpa [Own.evalArgs, ha, has] using hev
        subst this
        cases b with
        | false =>
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact Or.inl List.mem_cons_self
          · rcases evalArgs_mem_split bs as vs' has v hm' with h1 | ⟨a', h2, h3⟩
            · exact Or.inl (List.mem_cons_of_mem _ h1)
            · exact Or.inr ⟨a', by simp [List.zip_cons_cons, h2], h3⟩
        | true =>
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact Or.inr ⟨a, by simp [List.zip_cons_cons], ha⟩
          · rcases evalArgs_mem_split bs as vs' has v hm' with h1 | ⟨a', h2, h3⟩
            · exact Or.inl h1
            · exact Or.inr ⟨a', by simp [List.zip_cons_cons, h2], h3⟩

private theorem checkCallBorrowed_zip {Γ : Ctx} :
    ∀ {bs : List Bool} {args : List Arg},
      Γ.checkCallBorrowed bs args = .ok () →
      ∀ x, Arg.var x ∈ (bs.zip args).filterMap (fun p => if p.1 then some p.2 else none) →
        Γ.borrowable x = true
  | [], _, _, _, hm => by simp at hm
  | _ :: _, [], _, _, hm => by simp at hm
  | false :: bs, _ :: as, h, x, hm => by
    simp only [Ctx.checkCallBorrowed] at h
    simp only [List.zip_cons_cons, List.filterMap_cons, Bool.false_eq_true, ↓reduceIte] at hm
    exact checkCallBorrowed_zip h x hm
  | true :: bs, a :: as, h, x, hm => by
    simp only [List.zip_cons_cons, List.filterMap_cons, ↓reduceIte, List.mem_cons] at hm
    cases a with
    | var y =>
      simp only [Ctx.checkCallBorrowed] at h
      cases hb : Γ.borrowable y with
      | false => simp [hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      | true =>
        simp only [hb, ↓reduceIte] at h
        rcases hm with hEq | hm'
        · cases hEq; exact hb
        · exact checkCallBorrowed_zip h x hm'
    | lit _ | erased =>
      simp only [Ctx.checkCallBorrowed] at h
      rcases hm with hEq | hm'
      · cases hEq
      · exact checkCallBorrowed_zip h x hm'

private theorem ResultRelFull.weakenRetUniq {H : Heap} {external : Nat → Nat} {priv : Nat → Prop}
    {ctors : List Lam.CtorInfo} {r₁ r₂ : Bool} {s : Result Fir.Val} {t : Result (RVal × Heap)}
    (himp : r₂ = true → r₁ = true) (h : ResultRelFull H external priv ctors r₁ s t) :
    ResultRelFull H external priv ctors r₂ s t := by
  cases h with
  | ok hd hb hp hr hpriv hret hru => exact .ok hd hb hp hr hpriv hret (fun h2 => hru (himp h2))
  | timeout => exact .timeout
  | trap => exact .trap
  | resource r => exact .resource r
  | stuck => exact .stuck

section
variable {F : Fir.Program} {candidate : Src.NatMap Code} {borrows : BorrowSigs} {uniqs : UniqSigs}
  (domain : contractProgramDomain F = true) (pins : BoolPinsOk F)
  (bodies : BodiesChecked F candidate borrows uniqs)
variable {k : Nat} (smaller : ∀ j, j < k → AtClockOwned F candidate j borrows uniqs)
include domain pins bodies smaller

mutual
theorem owned_eval {H : Heap} {external : Nat → Nat} {priv : Nat → Prop} {retUniq : Bool}
    {live : List Var} {Γ : Ctx} {Δ : JCtx}
    {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {slots : Src.NatMap RVal} {slotVals : List RVal}
    {lex : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry} (c : Code)
    (st : OwnedState (signatures F) H external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq F.ctors F.known priv slots slotVals)
    (scope : scopeOk (signatures F) live (stackArities Jf) (eraseCode c) = true)
    (typed : checkCode Δ Γ c borrows uniqs retUniq F.ctors F.known = .ok ()) :
    ResultRelFull H external priv F.ctors retUniq (Fir.eval F k ρf Jf (eraseCode c))
      (eval { source := F, bodies := candidate, borrows, uniqs } k ρo Jo H c slots) := by
  match c with
  | .act (.inc x n) c' =>
    obtain ⟨Γ', hc, typed'⟩ := checkCode_inc typed
    obtain ⟨H', owned', hact, st', hreach, hpriv⟩ := inc_step st hc
    rw [eval_act, hact, Result.bind_ok]
    exact (owned_eval c' st' scope typed').preheap hreach hpriv
  | .act (.dec x) c' =>
    obtain ⟨Γ', hc, typed'⟩ := checkCode_dec typed
    obtain ⟨H', owned', hact, st', hreach, hpriv⟩ := dec_step st hc
    rw [eval_act, hact, Result.bind_ok]
    exact (owned_eval c' st' scope typed').preheap hreach hpriv
  | .reset s x ctor fields uniq c' =>
    obtain ⟨Γ', hreset, typed'⟩ := checkCode_reset typed
    obtain ⟨sv, H', owned', slotVals', hev, st', hreach, hpriv⟩ := reset_step st hreset
    rw [eval_reset, hev, Result.bind_ok]
    exact (owned_eval c' st' scope typed').preheap hreach hpriv
  | .reuse x s ctor args uniq c' =>
    have parts : x ∉ live ∧ rhsIn (signatures F) live (.ctor ctor args) = true ∧
        scopeOk (signatures F) (live ++ [x]) (stackArities Jf) (eraseCode c') = true := by
      simpa [eraseCode, scopeOk, Bool.and_eq_true, and_assoc] using scope
    obtain ⟨hx, _, hc'⟩ := parts
    obtain ⟨Γ', hreuse, typed'⟩ := checkCode_reuse typed
    show ResultRelFull H external priv F.ctors retUniq
      (Fir.eval F k ρf Jf (.bind x (.ctor ctor args) (eraseCode c'))) _
    rw [Fir.eval_bindRhs F k ρf Jf x (.ctor ctor args) (eraseCode c') (fun _ _ h => by cases h)]
    rcases fir_rhs_pure F ρf (.ctor ctor args) with hstuck | ⟨w, hw⟩
    · rw [hstuck]; exact .stuck
    · obtain ⟨sv, v, H', owned', slotVals', hsv, hev, st', hreach, hpriv⟩ :=
        reuse_step st hx hreuse hw
      rw [hw, Result.bind_ok, eval_reuse, hsv, Result.ofOption, Result.bind_ok, hev, Result.bind_ok]
      exact (owned_eval c' st' hc' typed').preheap hreach hpriv
  | .dropSlot s c' =>
    obtain ⟨Γ', hdrop, typed'⟩ := checkCode_dropSlot typed
    obtain ⟨sv, H', slotVals', hsv, hev, st', hreach, hpriv⟩ := dropSlot_step st hdrop
    rw [eval_dropSlot, hsv, Result.ofOption, Result.bind_ok, hev, Result.bind_ok]
    exact (owned_eval c' st' scope typed').preheap hreach hpriv
  | .bind x r c' =>
    have parts : x ∉ live ∧ rhsIn (signatures F) live r = true ∧
        scopeOk (signatures F) (live ++ [x]) (stackArities Jf) (eraseCode c') = true := by
      simpa [eraseCode, scopeOk, Bool.and_eq_true, and_assoc] using scope
    obtain ⟨hx, hr, hc'⟩ := parts
    obtain ⟨Γ', hbs, typed'⟩ := checkCode_bindStep typed
    by_cases call : ∃ f args, r = .call f args
    · obtain ⟨f, args, rfl⟩ := call
      have hs : (signatures F).lookup f = some args.length ∧ args.all (argIn live) = true := by
        simpa [rhsIn, Bool.and_eq_true] using hr
      obtain ⟨fd, hf, _, _⟩ := signatures_lookup hs.1
      have hbc : bindCtx Γ x (.call f args) borrows uniqs F.ctors = .ok Γ' := hbs
      simp only [bindCtx] at hbc
      obtain ⟨Γ₁, ht, hbc'⟩ := except_bind_ok hbc
      obtain ⟨⟨⟩, hchk, hΓ⟩ := except_bind_ok hbc'
      have hΓ := except_pure_ok hΓ
      subst hΓ
      let bs := borrows.getD f []
      let us := (uniqs.getD f ([], false)).1
      let retU := (uniqs.getD f ([], false)).2
      obtain ⟨vs, ws, owned₁, hvs, hws, hds, inv₁, hs₁, hw₁, hbrw, huniq, havArgs⟩ :=
        takeOwnedUniqueArgs_call_sem st ht hchk
      have hle₁ : ∀ k, refsIn k owned₁ ≤ refsIn k owned := fun k => by
        have := hs₁ k; rw [refsIn_append] at this; omega
      have hwkClr := Ctx.clearBorrowedUniq_weaker Γ₁ bs args
      have hownClr := Ctx.clearBorrowedUniq_own Γ₁ bs args
      obtain ⟨toks₁, htok₁, hroots₁⟩ := inv₁.roots
      have hrootsClr : ∃ toks, Ctx.Tokens (Γ₁.clearBorrowedUniq bs args) toks ∧ EnvRoots ρo toks owned₁ :=
        ⟨toks₁, htok₁.same hownClr.1 hownClr.2, hroots₁⟩
      have pre₁ := st.pre.weaker (hwkClr.trans hw₁) hrootsClr hle₁
      have pre₂ := pre₁.release
      have hbal_call : Balance H (holdRoots external (owned₁ ++ slotVals)) (selectOwnedVals bs vs) := by
        apply balance_hold.mp
        refine SameRefs.balance ?_ st.counts
        intro k; simp only [refsIn_append, hs₁ k]; dsimp only [bs]; omega
      -- Every argument value `v ∈ vs` avoids `pre₂.localPriv`.
      have hprivArgs : ∀ l, pre₂.localPriv l → ∀ v, v ∈ vs → v ≠ .loc l := by
        intro l hl v hv hEq; subst hEq
        rcases hl with hp | ⟨s, cls, u, hrs, hsl⟩ | ⟨z, huz, hiz, hvz⟩
        · obtain ⟨a, hma, ha⟩ := evalArgs_mem_arg hvs (.loc l) hv
          cases a with
          | lit _ | erased => simp [Own.evalArg] at ha
          | var y => exact st.privNoVar l hp y (havArgs y hma) ha
        · rcases evalArgs_mem_split bs args vs hvs (.loc l) hv with hownV | ⟨a, hma, ha⟩
          · obtain ⟨skeys, hsk, hsroots⟩ := st.slotRoots
            have hrs0 : Γ.rset.get? s = some (cls, u) := by
              rw [← (hwkClr.trans hw₁).rset]; exact hrs
            obtain ⟨sv, hsv, hcase⟩ := st.rsetOk s cls u hrs0
            have : sv = .loc l := Option.some.inj (hsv.symm.trans hsl); subst this
            rcases hcase with ⟨hc0, _⟩ | ⟨_, _, hEq', _, _, _, _, _, hrefsL⟩
            · cases hc0
            · cases hEq'
              have hmS : RVal.loc l ∈ slotVals :=
                hsroots.member ((hsk.mem s).mpr (by simp [Src.NatMap.contains, hrs0])) hsv
              have hp1 := refsIn_pos hmS
              have hp2 := refsIn_pos hownV
              rw [refsIn_append, hs₁ l, refsIn_append] at hrefsL; dsimp only [bs] at hp2; omega
          · cases a with
            | lit _ | erased => simp [Own.evalArg] at ha
            | var y =>
              have hbrwY := checkCallBorrowed_zip hchk y hma
              obtain ⟨skeys, hsk, hsroots⟩ := st.slotRoots
              have hrs0 : Γ.rset.get? s = some (cls, u) := by
                rw [← (hwkClr.trans hw₁).rset]; exact hrs
              obtain ⟨sv, hsv, hcase⟩ := st.rsetOk s cls u hrs0
              have : sv = .loc l := Option.some.inj (hsv.symm.trans hsl); subst this
              rcases hcase with ⟨hc0, _⟩ | ⟨_, _, hEq', _, _, _, hextL, hedgeL, hrefsL⟩
              · cases hc0
              · cases hEq'
                have hmS : RVal.loc l ∈ slotVals :=
                  hsroots.member ((hsk.mem s).mpr (by simp [Src.NatMap.contains, hrs0])) hsv
                have hpS := refsIn_pos hmS
                simp only [Ctx.borrowable_eq, Bool.or_eq_true, decide_eq_true_eq] at hbrwY
                rcases hbrwY with (hi | hpb) | htk
                · obtain ⟨u', hu', himm⟩ := st.immOk y (by rw [← hw₁.isImm y]; exact hi)
                  have : u' = .loc l := Option.some.inj (hu'.symm.trans ha); subst this
                  exact himm l rfl
                · obtain ⟨u', hu', hreach⟩ := st.pbrwOk y (by rw [← hw₁.isPbrw y]; exact hpb)
                  have : u' = .loc l := Option.some.inj (hu'.symm.trans ha); subst this
                  exact ReachableFrom.not_of_zero hextL hedgeL hreach
                · have hpO := refsIn_pos (hroots₁.member (htok₁.mem htk) ha)
                  rw [refsIn_append, hs₁ l, refsIn_append] at hrefsL; omega
        · rcases evalArgs_mem_split bs args vs hvs (.loc l) hv with hownV | ⟨a, hma, ha⟩
          · obtain ⟨hmeta, v', hv', hvu⟩ := pre₂.uniqOk z huz
            have : v' = .loc l := Option.some.inj (hv'.symm.trans hvz); subst this
            obtain ⟨_, _, _, _, hrefsL⟩ := hvu
            have hrefs0 : refsIn l (owned ++ slotVals) = 1 := by
              obtain ⟨_, v0, hv0, hvu0⟩ := st.uniqOk z ((hwkClr.trans hw₁).isUniq z huz)
              have : v0 = .loc l := Option.some.inj (hv0.symm.trans hvz); subst this
              obtain ⟨_, _, _, _, hr0⟩ := hvu0; exact hr0
            have hp1 := refsIn_pos hownV
            rw [refsIn_append, hs₁ l, refsIn_append] at hrefs0
            rw [refsIn_append] at hrefsL; dsimp only [bs] at hp1; omega
          · cases a with
            | lit _ | erased => simp [Own.evalArg] at ha
            | var y =>
              have hneYZ : y ≠ z := fun hEq => by
                subst hEq
                exact Ctx.clearBorrowedUniq_avoids Γ₁ bs args huz hiz (.var y) hma rfl
              have hbrwY := checkCallBorrowed_zip hchk y hma
              obtain ⟨hmeta, v', hv', hvu⟩ := pre₂.uniqOk z huz
              have : v' = .loc l := Option.some.inj (hv'.symm.trans hvz); subst this
              obtain ⟨_, _, hextL, hedgeL, hrefsL⟩ := hvu
              simp only [Ctx.borrowable_eq, Bool.or_eq_true, decide_eq_true_eq] at hbrwY
              rcases hbrwY with (hi | hpb) | htk
              · obtain ⟨u', hu', himm⟩ := st.immOk y (by rw [← hw₁.isImm y]; exact hi)
                have : u' = .loc l := Option.some.inj (hu'.symm.trans ha); subst this
                exact himm l rfl
              · obtain ⟨u', hu', hreach⟩ := st.pbrwOk y (by rw [← hw₁.isPbrw y]; exact hpb)
                have : u' = .loc l := Option.some.inj (hu'.symm.trans ha); subst this
                exact ReachableFrom.not_of_zero hextL hedgeL hreach
              · have hyMem : y ∈ toks₁ := htok₁.mem htk
                have hzTok : Γ₁.tokens z = 1 := by
                  have h1 := (hmeta hiz).1
                  change (Γ₁.clearBorrowedUniq bs args).tokens z = 1 at h1
                  rw [Ctx.tokens_eq, hownClr.1] at h1; exact h1
                have hzMem : z ∈ toks₁ := htok₁.mem (by omega)
                have h2 := envRoots_distinct_ne hroots₁ hneYZ hyMem hzMem ha hvz
                rw [refsIn_append] at hrefsL; omega
      have hcall := owned_call_of_smaller_full domain bodies smaller hf hds hbal_call hbrw huniq
        (priv := pre₂.localPriv)
        (fun l hl => (pre₂.localPriv_facts hl).1)
        (fun l hl => (pre₂.localPriv_facts hl).2)
        hprivArgs
      show ResultRelFull H external priv F.ctors retUniq
        (Fir.eval F k ρf Jf (.bind x (.call f args) (eraseCode c'))) _
      rw [Fir.eval_bindCall, hws, eval_bindCall, hvs]
      simp only [Result.ofOption, Result.bind_ok]
      apply ResultRelFull.bind_frame_full hcall
      intro w v H' hd' hb' _ hreach' hpriv' hretNoPriv' hretU'
      have pre₃ := pre₂.call (release_borrowed pre₁.epochs) hreach' hpriv'
      have hbal_after : Balance H' external ((v :: owned₁) ++ slotVals) := by
        have hr' := balance_resume hb'
        refine SameRefs.balance ?_ hr'
        intro k; simp only [List.cons_append, refsIn_append, refsIn]; omega
      cases hru : (uniqs.getD f ([], false)).2 with
      | true =>
        simp only [hru, ↓reduceIte] at typed'
        have hvU : UniqVal F.ctors H' external ((v :: owned₁) ++ slotVals) v := by
          have hvU0 := hretU' hru
          cases v with
          | lit _ | erased => trivial
          | ctor0 c => exact hvU0
          | loc l =>
            obtain ⟨b, hc, hextH, hedge, _⟩ := hvU0
            simp only [holdRoots, refsIn_append] at hextH
            exact ⟨b, hc, by omega, hedge, by simp only [List.cons_append, refsIn_append, refsIn, ↓reduceIte]; omega⟩
        have st' := pre₃.bindUniqOwned hx hd' hbal_after hvU hretNoPriv'
        exact (owned_eval c' st' hc' typed').preheap hreach'.of_holdRoots
          (hpriv'.mono (fun _ h => Or.inl h))
      | false =>
        simp only [hru, Bool.false_eq_true, ↓reduceIte] at typed'
        have st' := pre₃.bindOwned hx hd' hbal_after hretNoPriv'
        exact (owned_eval c' st' hc' typed').preheap hreach'.of_holdRoots
          (hpriv'.mono (fun _ h => Or.inl h))
    · have hn : ∀ f args, r ≠ .call f args := fun f args h => call ⟨f, args, h⟩
      show ResultRelFull H external priv F.ctors retUniq
        (Fir.eval F k ρf Jf (.bind x r (eraseCode c'))) _
      rw [Fir.eval_bindRhs F k ρf Jf x r (eraseCode c') hn,
        eval_bindRhs _ k ρo Jo H x r c' hn]
      rcases fir_rhs_pure F ρf r with hstuck | ⟨w, hw⟩
      · rw [hstuck]; exact .stuck
      · obtain ⟨v, H', owned', hev, st', hreach, hpriv⟩ := rhs_step pins st hx hn hbs hw
        rw [hw, Result.bind_ok]
        change ResultRelFull H external priv F.ctors retUniq _
          ((evalRhs { ctors := F.ctors, known := F.known } ρo H r).bind _)
        rw [hev, Result.bind_ok]
        exact (owned_eval c' st' hc' typed').preheap hreach hpriv
  | .jp j ps captured rec body c' =>
    obtain ⟨hnd, hneed, htb, htk⟩ := checkCode_jp typed
    have parts : (stackArities Jf).lookup j = none ∧ fresh live ps = true ∧
        scopeOk (signatures F) (live ++ ps)
          (if rec then (j, ps.length) :: stackArities Jf else stackArities Jf) (eraseCode body) = true ∧
        scopeOk (signatures F) live ((j, ps.length) :: stackArities Jf) (eraseCode c') = true := by
      simpa [eraseCode, scopeOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using scope
    obtain ⟨hnone, hf, hb, hc'⟩ := parts
    have st' := st.declare hnd hneed htb hnone hf hb
    show ResultRelFull H external priv F.ctors retUniq
      (Fir.eval F k ρf Jf (.jp j ps rec (eraseCode body) (eraseCode c'))) _
    rw [Fir.eval_jp, eval_jp]
    exact owned_eval c' st' (by simpa [stackArities] using hc') htk
  | .jmp j args =>
    obtain ⟨captured, Γ₁, Γ₂, hΔ, h1, h2, h3⟩ := checkCode_jmp typed
    have hs : (stackArities Jf).lookup j = some args.length := by
      have : decide ((stackArities Jf).lookup j = some args.length) = true ∧
          args.all (argIn live) = true := by
        simpa only [eraseCode, scopeOk, Bool.and_eq_true] using scope
      simpa using this.1
    obtain ⟨ef, restf, hl, _⟩ := Fir.lookupJ_of_arity hs
    obtain ⟨vs, ws, eo, resto, hvs, hws, hlen', hlo, hpar, hch, hbody⟩ :=
      jump_body st hΔ h1 h2 h3 hl
    show ResultRelFull H external priv F.ctors retUniq (Fir.eval F k ρf Jf (.jmp j args)) _
    rw [Fir.eval_jmp_of F k ρf Jf hl hws, eval_jmp, hlo, hvs]
    simp only [Result.ofOption, Result.bind_ok]
    unfold Fir.jumpTo jumpTo
    by_cases hlen : ws.length = ef.params.length
    · have hlo' : vs.length = eo.params.length := by rw [hpar, hlen', hlen]
      simp only [hlen, hlo', ↓reduceIte, hch]
      obtain ⟨Δb, Γb, lexd, lexb, owned', st', typed', herase, scope'⟩ := hbody hlen
      cases hc : ef.charged with
      | true =>
        simp only [↓reduceIte]
        refine ResultRelFull.later fun j' hj' => ?_
        have := smaller j' hj' eo.body st' (by rw [herase]; exact scope') typed'
        rwa [herase] at this
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hco : eo.charged = false := by rw [hch]; exact hc
        have := own_jump_measure hlo hco args
        have := owned_eval eo.body st' (by rw [herase]; exact scope') typed'
        rwa [herase] at this
    · simp only [hlen, ↓reduceIte]
      exact .stuck
  | .case x alts d =>
    obtain ⟨hneed, halts, hopt⟩ := checkCode_case typed
    have parts : x ∈ live ∧ scopeAlts (signatures F) live (stackArities Jf) (eraseAlts alts) = true ∧
        scopeOpt (signatures F) live (stackArities Jf) (eraseOpt d) = true := by
      simpa [eraseCode, scopeOk, Bool.and_eq_true, and_assoc] using scope
    obtain ⟨v, w, hv, hw, hd⟩ := st.den x (Ctx.need_avail hneed)
    show ResultRelFull H external priv F.ctors retUniq
      (Fir.eval F k ρf Jf (.case x (eraseAlts alts) (eraseOpt d))) _
    rw [Fir.eval_case, hw, eval_case, hv]
    simp only [Result.ofOption, Result.bind_ok]
    cases hk : w.asCtor F.known with
    | none => exact .stuck
    | some p =>
      obtain ⟨key, fs⟩ := p
      obtain ⟨fields, hfields, _⟩ := (Values.asCtor_den F.known hd).1 key fs hk
      simp only [hfields]
      exact owned_evalAlts x v fields key alts d st parts.1 hv hfields parts.2.1 parts.2.2 halts hopt
  | .ret a =>
    obtain ⟨hretU, Γ', ht, hcl⟩ := checkCode_ret typed
    obtain ⟨v, w, owned₁, hev, hfa, hd, inv₁, hs, hwk⟩ := takeArg_sem st.takeInv ht
    obtain ⟨toks₁, htok₁, hr₁⟩ := inv₁.roots
    have hnil := closed_nil htok₁ hcl
    subst hnil
    have ho := EnvRoots.nil_inv hr₁
    subst ho
    obtain ⟨skeys, hsk, hsr⟩ := st.slotRoots
    have hsnil := (hsk.same hwk.rset).closed_nil (closed_rset hcl)
    subst hsnil
    have hsv := EnvRoots.nil_inv hsr
    subst hsv
    show ResultRelFull H external priv F.ctors retUniq (Fir.eval F k ρf Jf (.ret a)) _
    rw [Fir.eval_ret, hfa, eval_ret, hev]
    simp only [Result.ofOption, Result.bind_ok]
    refine .ok hd (hs.balance (by simpa using st.counts))
      (fun _ _ _ h => h) (ReachablePreserved.refl H external)
      (PrivPreserved.refl st.privNoEdge) ?_ ?_
    · intro l hl hEq; subst hEq
      cases a with
      | lit _ | erased => simp [Own.evalArg] at hev
      | var y =>
        have havy : Γ.avail y = true := by
          rcases Ctx.take_ok ht with ⟨hi, _⟩ | ⟨_, n, hn, _⟩
          · simp [Ctx.avail_eq, hi]
          · simp [Ctx.avail_eq, Ctx.tokens_eq, hn]
        exact st.privNoVar l hl y havy hev
    · intro hru
      cases a with
      | lit _ | erased => simp [Own.evalArg] at hev; subst hev; trivial
      | var y =>
        obtain ⟨_, u', hu', hvu⟩ := st.uniqOk y (hretU hru y rfl)
        have : u' = v := Option.some.inj (hu'.symm.trans hev); subst this
        exact hvu.sameRefs (fun k => by simpa using hs k)
  | .tcall f args =>
    obtain ⟨hretU, Γ', ht, hchk, hcl⟩ := checkCode_tcall typed
    have hs : (signatures F).lookup f = some args.length := by
      have : decide ((signatures F).lookup f = some args.length) = true ∧
          args.all (argIn live) = true := by
        simpa only [eraseCode, scopeOk, Bool.and_eq_true] using scope
      simpa using this.1
    obtain ⟨fd, hf, _, _⟩ := signatures_lookup hs
    obtain ⟨vs, ws, owned₁, hvs, hws, hds, inv₁, hs₁, hw₁, hbrw, huniq, havArgs⟩ :=
      takeOwnedUniqueArgs_tail_sem st ht hchk hcl
    obtain ⟨toks₁, htok₁, hr₁⟩ := inv₁.roots
    have hnil := closed_nil htok₁ hcl
    subst hnil
    have ho := EnvRoots.nil_inv hr₁
    subst ho
    obtain ⟨skeys, hsk, hsr⟩ := st.slotRoots
    have hsnil := (hsk.same hw₁.rset).closed_nil (closed_rset hcl)
    subst hsnil
    have hsv := EnvRoots.nil_inv hsr
    subst hsv
    have hprivArgs : ∀ l, priv l → ∀ v, v ∈ vs → v ≠ .loc l := by
      intro l hl v hv hEq; subst hEq
      obtain ⟨a, hma, ha⟩ := evalArgs_mem_arg hvs (.loc l) hv
      cases a with
      | lit _ | erased => simp [Own.evalArg] at ha
      | var y => exact st.privNoVar l hl y (havArgs y hma) ha
    show ResultRelFull H external priv F.ctors retUniq (Fir.eval F k ρf Jf (.tcall f args)) _
    rw [Fir.eval_tcall, hws, eval_tcall, hvs]
    simp only [Result.ofOption, Result.bind_ok]
    exact (owned_call_of_smaller_full domain bodies smaller hf hds
      ((by simpa using hs₁ : SameRefs owned (selectOwnedVals (borrows.getD f []) vs)).balance
        (by simpa using st.counts))
      hbrw huniq st.privBound st.privNoEdge hprivArgs).weakenRetUniq hretU
  | .trap =>
    show ResultRelFull H external priv F.ctors retUniq (Fir.eval F k ρf Jf .trap) _
    rw [Fir.eval_trap, eval_trap]
    exact .trap
termination_by c.size + jweight Jo
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Code.size]; omega)
    | (simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | omega

theorem owned_evalAlts {H : Heap} {external : Nat → Nat} {priv : Nat → Prop} {retUniq : Bool}
    {live : List Var} {Γ : Ctx} {Δ : JCtx}
    {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {slots : Src.NatMap RVal} {slotVals : List RVal}
    {lex : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (x : Var) (vx : RVal) (fields : List RVal) (key : Key.CtorKey)
    (alts : List Alt) (d : Option Code)
    (st : OwnedState (signatures F) H external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq F.ctors F.known priv slots slotVals)
    (hx : x ∈ live) (hvx : ρo.get? x = some vx) (hac : vx.asCtor F.known H = some (key, fields))
    (ha : scopeAlts (signatures F) live (stackArities Jf) (eraseAlts alts) = true)
    (hd : scopeOpt (signatures F) live (stackArities Jf) (eraseOpt d) = true)
    (typedAlts : checkAlts Δ Γ x alts borrows uniqs retUniq F.ctors F.known = .ok ())
    (typedOpt : checkOpt Δ Γ d borrows uniqs retUniq F.ctors F.known = .ok ()) :
    ResultRelFull H external priv F.ctors retUniq
      (Fir.evalAlts F k ρf Jf key (eraseAlts alts) (eraseOpt d))
      (evalAlts { source := F, bodies := candidate, borrows, uniqs } k ρo Jo H key alts d slots) := by
  match alts, d with
  | [], some c =>
    simp only [eraseAlts, eraseOpt]
    rw [Fir.evalAlts_nil, evalAlts_nil]
    exact owned_eval c st (by simpa [eraseOpt, scopeOpt] using hd)
      (by simpa [checkOpt] using typedOpt)
  | [], none =>
    simp only [eraseAlts, eraseOpt]
    rw [Fir.evalAlts_nil]
    exact .stuck
  | .mk key' body :: rest, d =>
    obtain ⟨tb, tr⟩ := checkAlts_cons typedAlts
    have hs : scopeOk (signatures F) live (stackArities Jf) (eraseCode body) = true ∧
        scopeAlts (signatures F) live (stackArities Jf) (eraseAlts rest) = true := by
      simpa only [eraseAlts, scopeAlts, Bool.and_eq_true] using ha
    simp only [eraseAlts]
    rw [Fir.evalAlts_cons, evalAlts_cons]
    split
    · next hkey =>
      subst hkey
      exact owned_eval body (st.setCtor hx hvx hac) hs.1 tb
    · exact owned_evalAlts x vx fields key rest d st hx hvx hac hs.2 hd tr typedOpt
termination_by Code.altsSize alts + Code.optSize d + jweight Jo + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)
end

end

/-- **The milestone-1 induction** (generalised to arbitrary `@borrowed` and `@unique` signatures). -/
theorem owned_refines_of {F : Fir.Program} {candidate : Src.NatMap Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs}
    (domain : contractProgramDomain F = true) (pins : BoolPinsOk F)
    (bodies : BodiesChecked F candidate borrows uniqs) :
    ∀ k, AtClockOwned F candidate k borrows uniqs := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro H external priv retUniq live Γ Δ ρf ρo owned slots slotVals lex Jf Jo c st scope typed
    exact owned_eval domain pins bodies ih c st scope typed

end IxCC.Own.Plain
