import IxCC.Cfg.Rc.Proof.Native.Pipeline
import IxCC.Cfg.Rc.Proof.Markers

/-! Recover every source instruction from the actual successful RC consuming
pass. In particular, reserved decrement/increment markers survive unchanged;
allocation is the only newly introduced call path. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

theorem consume_decrement (P : Program) (l : Layout) (slot x : Nat) :
    consume P l (marker P.base.size slot (.dec x)) =
      .ok (marker P.base.size slot (.dec x)) := by
  simp [consume, reserved_marker, decode_marker, pure, Except.pure]

theorem consume_increment (P : Program) (l : Layout) (slot x : Nat) :
    consume P l (marker P.base.size slot (.inc x 1)) =
      .ok (marker P.base.size slot (.inc x 1)) := by
  simp [consume, reserved_marker, decode_marker, pure, Except.pure]

theorem consumeFunction_parts {P : Program} {l : Layout} {fd lowered : Cfg.Fun}
    (accepted : consumeFunction P l fd = .ok lowered) :
    lowered.key = fd.key ∧ lowered.sig = fd.sig ∧ lowered.vars = fd.vars ∧
      lowered.regionFrame = fd.regionFrame ∧ lowered.blocks.length = fd.blocks.length ∧
      ∀ {b : Nat} {block : Cfg.Block}, fd.blocks[b]? = some block →
        ∃ body, block.body.mapM (consume P l) = .ok body ∧
          lowered.blocks[b]? = some { block with body } := by
  unfold consumeFunction at accepted
  cases hb : fd.blocks.mapM (fun b => do
      let body ← b.body.mapM (consume P l)
      pure { b with body }) with
  | error e => rw [hb] at accepted; cases accepted
  | ok blocks =>
    rw [hb] at accepted
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
    subst lowered
    obtain ⟨hlen, each⟩ := Rt.Proof.except_mapM hb
    refine ⟨rfl, rfl, rfl, rfl, hlen, ?_⟩
    intro b block hblock
    obtain ⟨result, hr, hi⟩ := each hblock
    cases hm : block.body.mapM (consume P l) with
    | error e => rw [hm] at hr; cases hr
    | ok body =>
      simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hr
      subst result
      exact ⟨body, rfl, hi⟩

theorem consumeFunction_instr {P : Program} {l : Layout} {fd lowered : Cfg.Fun}
    (accepted : consumeFunction P l fd = .ok lowered)
    {b : Nat} {block : Cfg.Block} (hblock : fd.blocks[b]? = some block)
    {i : Nat} {instruction : Cfg.Instr} (hi : block.body[i]? = some instruction) :
    ∃ body result, lowered.blocks[b]? = some { block with body } ∧
      body.length = block.body.length ∧ body[i]? = some result ∧
      consume P l instruction = .ok result := by
  obtain ⟨body, hb, hbody⟩ := (consumeFunction_parts accepted).2.2.2.2.2 hblock
  obtain ⟨hlen, each⟩ := Rt.Proof.except_mapM hb
  obtain ⟨result, hr, hi'⟩ := each hi
  exact ⟨body, result, hbody, hlen, hi', hr⟩

theorem consumeAll_length {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (accepted : consumeAll P = .ok pairs) : pairs.length = P.base.size := by
  simpa [consumeAll] using (Rt.Proof.except_mapM accepted).1

theorem consumeAll_entry {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (accepted : consumeAll P = .ok pairs) {f : Nat} (hf : f < P.base.size) :
    ∃ fd lowered, P.base.fun? f = some fd ∧
      consumeFunction P (layoutOf P) fd = .ok lowered ∧ pairs[f]? = some (f, lowered) := by
  obtain ⟨pair, hp, hi⟩ := (Rt.Proof.except_mapM accepted).2 (j := f) (x := f) (by simp [hf])
  cases hfd : P.base.fun? f with
  | none => rw [hfd] at hp; cases hp
  | some fd =>
    simp only [hfd] at hp
    cases hl : consumeFunction P (layoutOf P) fd with
    | error e => rw [hl] at hp; cases hp
    | ok lowered =>
      simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hp
      subst pair
      exact ⟨fd, lowered, rfl, hl, hi⟩

theorem consumeAll_keys {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (accepted : consumeAll P = .ok pairs) : pairs.map Prod.fst = List.range P.base.size := by
  have hlen := consumeAll_length accepted
  apply List.ext_getElem?
  intro i
  by_cases hi : i < P.base.size
  · obtain ⟨fd, lowered, _, _, hget⟩ := consumeAll_entry accepted hi
    simp [List.getElem?_map, hget, hi]
  · have hp : pairs[i]? = none := List.getElem?_eq_none (by omega)
    simp [List.getElem?_map, hp, hi]

theorem consumed_entry {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (accepted : consumeAll P = .ok pairs) {f : Nat} (hf : f < P.base.size) :
    ∃ fd lowered, P.base.fun? f = some fd ∧
      consumeFunction P (layoutOf P) fd = .ok lowered ∧ (consumed P pairs).fun? f = some lowered := by
  obtain ⟨fd, lowered, hs, hc, hp⟩ := consumeAll_entry accepted hf
  refine ⟨fd, lowered, hs, hc, ?_⟩
  exact Src.NatMap.get?_ofList (by rw [consumeAll_keys accepted]; exact List.nodup_range)
    (List.mem_of_getElem? hp)









end IxCC.Cfg.Rc.Native.Spec
