import IxVMRefinement.Assembly.BareState

/-! # Replaying mutual definition blocks without projection rewrites -/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (RolesKeyed)

abbrev DefinitionBlockState (md : Mode) :=
  Std.HashMap (CName md) Nat × Array (CDecl md) × Nat

def definitionBlockStep (cx : Ctx md) (st : State md) (owner : _root_.Address)
    (c : Ixon.Constant) (ms : Array Ixon.MutConst) (defs : Array Ixon.Definition)
    (i : Nat) (s : DefinitionBlockState md) : ReadM (ForInStep (DefinitionBlockState md)) := do
  let (decl, rewrote) ← readDefinition cx st (fun k => s.1.getD k (st.heights.getD k 0))
    (.member owner i) (List.range defs[i]!.lvls.toNat)
    (MemberReader.mk' cx c id
      (fun j => if j < ms.size then some (cx.memberKey (.member owner j)) else none)) defs[i]!
  match decl with
  | .defnDecl cv _ hint =>
    if rewrote then
      pure (.yield (s.1.insert cv.name (Frontend.InModel.hintHeight hint), s.2.1.push decl, s.2.2 + 1))
    else
      pure (.yield (s.1.insert cv.name (Frontend.InModel.hintHeight hint), s.2.1.push decl, s.2.2))
  | _ =>
    if rewrote then pure (.yield (s.1, s.2.1.push decl, s.2.2 + 1))
    else pure (.yield (s.1, s.2.1.push decl, s.2.2))

def readDefinitionBlock (cx : Ctx md) (st : State md) (owner : _root_.Address)
    (c : Ixon.Constant) (ms : Array Ixon.MutConst) (defs : Array Ixon.Definition)
    (order : Array Nat) : ReadM (Read md) := do
  let result ← forIn order ({}, #[], 0) (definitionBlockStep cx st owner c ms defs)
  pure { decls := result.2.1, projRewrites := result.2.2 }

/-- The actual definition-only branch of the record reader is this block loop. -/
theorem readRecord_mutDefns_eq (cx : Ctx md) (st : State md) (owner : _root_.Address)
    (c : Ixon.Constant) (ms : Array Ixon.MutConst) (defs : Array Ixon.Definition)
    (order : Array Nat) (hinfo : c.info = .muts ms)
    (hinds : ms.any (fun | .indc _ => true | _ => false) = false)
    (hrecs : ms.all (fun | .recr _ => true | _ => false) = false)
    (hdefsAll : ms.all (fun | .defn _ => true | _ => false) = true)
    (hdefs : ms.filterMap (fun | .defn d => some d | _ => none) = defs)
    (hsafe : defs.findSome? safetyDecline = none)
    (horder : defOrder (defs.map (recurDeps c)) = some order) :
    readRecord cx st owner c = readDefinitionBlock cx st owner c ms defs order := by
  have anyInd : ∀ p : Ixon.MutConst → Bool,
      (∀ x, p x = match x with | .indc _ => true | _ => false) → ms.any p = false := by
    intro p hp
    rw [funext hp]
    exact hinds
  have allRec : ∀ p : Ixon.MutConst → Bool,
      (∀ x, p x = match x with | .recr _ => true | _ => false) → ms.all p = false := by
    intro p hp
    rw [funext hp]
    exact hrecs
  have allDef : ∀ p : Ixon.MutConst → Bool,
      (∀ x, p x = match x with | .defn _ => true | _ => false) → ms.all p = true := by
    intro p hp
    rw [funext hp]
    exact hdefsAll
  have defValues : ∀ p : Ixon.MutConst → Option Ixon.Definition,
      (∀ x, p x = match x with | .defn d => some d | _ => none) → ms.filterMap p = defs := by
    intro p hp
    rw [funext hp]
    exact hdefs
  unfold readRecord
  rw [hinfo]
  dsimp only
  rw [anyInd _ (fun x => by cases x <;> rfl), allRec _ (fun x => by cases x <;> rfl),
    allDef _ (fun x => by cases x <;> rfl), defValues _ (fun x => by cases x <;> rfl),
    hsafe, horder]
  rfl

private theorem forIn_replay_zero {α σ : Type} (counter : σ → Nat)
    (source target : α → σ → ReadM (ForInStep σ))
    (hstep : ∀ i s q, source i s = .ok q →
      ∃ next, q = .yield next ∧ counter s ≤ counter next ∧
        (counter next = 0 → target i s = .ok q)) :
    ∀ (items : List α) (start result : σ), forIn items start source = .ok result →
      counter result = 0 → counter start = 0 ∧ forIn items start target = .ok result
  | [], start, result, h, hzero => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst result
    exact ⟨hzero, rfl⟩
  | i :: rest, start, result, h, hzero => by
    rw [List.forIn_cons] at h
    obtain ⟨q, hq, hrest⟩ := except_bind_ok.mp h
    obtain ⟨next, rfl, hmono, hreplay⟩ := hstep i start q hq
    obtain ⟨hnext, htail⟩ := forIn_replay_zero counter source target hstep rest next result hrest hzero
    refine ⟨by omega, ?_⟩
    rw [List.forIn_cons, hreplay hnext]
    exact htail

theorem definitionBlockStep_without_rewrite {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {source target : State md} {owner : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {defs : Array Ixon.Definition}
    (hh : ∀ (k : CName md), NonAuxKey k → target.heights[k]? = source.heights[k]?)
    (hempty : ∀ (k : CName md), target.projLevels[k]? = none)
    (i : Nat) (s : DefinitionBlockState md) {q : ForInStep (DefinitionBlockState md)}
    (h : definitionBlockStep cx source owner c ms defs i s = .ok q) :
    ∃ next, q = .yield next ∧ s.2.2 ≤ next.2.2 ∧
      (next.2.2 = 0 → definitionBlockStep cx target owner c ms defs i s = .ok q) := by
  unfold definitionBlockStep at h
  obtain ⟨⟨decl, rewrote⟩, hdef, h⟩ := except_bind_ok.mp h
  cases rewrote with
  | true =>
    cases decl <;> simp [pure, Except.pure] at h <;> subst q <;>
      exact ⟨_, rfl, Nat.le_succ _, fun hz => (Nat.succ_ne_zero _ hz).elim⟩
  | false =>
    have hdef' := readDefinition_without_rewrite
      (target := target) (heights' := fun k => s.1.getD k (target.heights.getD k 0)) hrk
      (by
        intro j m k hs hm
        split at hs
        · injection hs with hs
          rw [← hs] at hm
          exact memberKey_nonAux hrk hm
        · cases hs)
      (by
        intro k hk
        simp only [Std.HashMap.getD_eq_getD_getElem?, hh k hk]) hempty hdef
    cases decl <;> simp [pure, Except.pure] at h <;> subst q <;>
      refine ⟨_, rfl, Nat.le_refl _, fun _ => ?_⟩ <;>
      simp only [definitionBlockStep, hdef', bind, Except.bind, pure, Except.pure,
        Bool.false_eq_true, ↓reduceIte]

theorem readDefinitionBlock_without_rewrite {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {source target : State md} {owner : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {defs : Array Ixon.Definition} {order : Array Nat}
    {full : Read md} (h : readDefinitionBlock cx source owner c ms defs order = .ok full)
    (hzero : full.projRewrites = 0)
    (hh : ∀ (k : CName md), NonAuxKey k → target.heights[k]? = source.heights[k]?)
    (hempty : ∀ (k : CName md), target.projLevels[k]? = none) :
    readDefinitionBlock cx target owner c ms defs order = .ok full := by
  unfold readDefinitionBlock at h ⊢
  obtain ⟨result, hloop, h⟩ := except_bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst full
  rw [← Array.forIn_toList] at hloop ⊢
  obtain ⟨_, htarget⟩ := forIn_replay_zero (fun s : DefinitionBlockState md => s.2.2)
    (definitionBlockStep cx source owner c ms defs)
    (definitionBlockStep cx target owner c ms defs)
    (fun i s _ hq => definitionBlockStep_without_rewrite hrk hh hempty i s hq)
    order.toList ({}, #[], 0) result hloop hzero
  rw [htarget]
  rfl

end IxVM.Refinement.Assembly
