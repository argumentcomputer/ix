import Ix.Cert.CtxAgree
import Ix.Cert.Quotient

/-! # Both sides run the hint the artifact ships at a name's address (CtxAgree, point (2))

A definition's height is its hint's (`Reader.State.note`), so the per-key
relation's heights (`Ix.Cert.CtxAgree.ReadsAgreeAt`) need the two sides to run
one hint per definition. Quotient Source overrides each definition's hint by its
input name's (`Ix.LeanIngress.fiberHintsMap ixe`: the hint the artifact ships,
`Ixon.Env.anonHints`, at the address it publishes the name at), and the Ixon
reader reads a definition at the hint the artifact ships at the record it reads
the member through (`Ix.Cert.hintsOf ixe`: a block member's projection record, a
singleton's own record). So the two are one when the name is published at that
record (`hints_agree`):

* `fiberHintsMap_named`: Source's hint at a published name's key is the one at
  its address, when every two published names with one ingress name have one
  address (`PublishedAgree`'s property);
* `hintsOf_projection`: the reader's hint at a block member is the one at its
  projection record, when that is the member's one projection record;
* `hintsOf_block`: at a member no projection record projects (a singleton), the
  one at its block's record. -/

namespace Ix.Cert.CtxAgree

open Ix.LeanIngress (fiberHintsMap hintOfLean ingressKey ingressName)
open Ix.Kernel (ConstRef)

theorem hintOfLean_eq_hintOf : hintOfLean = Ix.Cert.hintOf := by
  funext h; cases h <;> rfl

/-- **`Key.ofName` is injective.** -/
theorem ofName_inj {x y : Ix.Kernel.Name} (h : Ix.Kernel.Key.ofName x = Ix.Kernel.Key.ofName y) : x = y := by
  have role : ∀ (z : Ix.Kernel.Name) (r : Ix.Kernel.Role), Ix.Kernel.Key.ofName z = .role r → z = r.leanName :=
    fun z r hz => Ix.Cert.roleOf_leanName (by unfold Ix.LeanIngress.roleOf; rw [hz])
  have ident : ∀ (z i : Ix.Kernel.Name), Ix.Kernel.Key.ofName z = .id i → z = i := by
    intro z i hz
    unfold Ix.Kernel.Key.ofName at hz
    split at hz <;> cases hz
    rfl
  cases hx : Ix.Kernel.Key.ofName x with
  | role r => exact (role x r hx).trans (role y r (h.symm.trans hx)).symm
  | id i => exact (ident x i hx).trans (ident y i (h.symm.trans hx)).symm
  | aux k d =>
    unfold Ix.Kernel.Key.ofName at hx
    split at hx <;> cases hx

/-- A fold at pointwise-equal steps. -/
theorem foldl_step {δ β : Type} {F G : δ → β → δ} (h : ∀ m x, F m x = G m x) (l : List β) (init : δ) :
    l.foldl F init = l.foldl G init := by
  rw [show F = G from funext fun m => funext fun x => h m x]

/-- **Quotient Source's hint at a published name's key** is the hint the artifact
ships at the name's address. -/
theorem fiberHintsMap_named {ixe : Ixon.Env}
    (agree : ∀ m d, (m, d) ∈ ixe.named.toList → (Ix.LeanIngress.sourceAddrs ixe)[ingressName m]? = some d.addr)
    {n : Ix.Name} {d : Ixon.Named} (hn : (n, d) ∈ ixe.named.toList) :
    (fiberHintsMap ixe)[ingressKey n]? = hintOfLean <$> ixe.anonHints.get? d.addr := by
  let g : Ix.Name × Ixon.Named → Option (Ix.Kernel.Key .source × Ix.Kernel.ReducibilityHint) := fun b =>
    (ixe.anonHints.get? b.2.addr).map fun h => (ingressKey b.1, hintOfLean h)
  have hfold : fiberHintsMap ixe = ixe.named.toList.foldl (insOpt g) {} := by
    unfold fiberHintsMap
    rw [Std.HashMap.fold_eq_foldl_toList]
    refine foldl_step (fun m b => ?_) _ _
    simp only [insOpt, g]
    cases ixe.anonHints.get? b.2.addr <;> rfl
  -- every entry at the key is at `d`'s address
  have same : ∀ e ∈ ixe.named.toList, ingressKey e.1 = ingressKey n → e.2.addr = d.addr := by
    intro e he hk
    have h1 := agree e.1 e.2 he
    have h2 := agree n d hn
    rw [ofName_inj hk, h2] at h1
    exact (Option.some.inj h1).symm
  rw [hfold]
  cases hh : ixe.anonHints.get? d.addr with
  | none =>
    refine (foldl_insOpt_none g _ _).mpr ⟨fun e he w hw => ?_, by simp⟩
    simp only [g, Option.map_eq_some_iff, Prod.mk.injEq] at hw
    obtain ⟨h0, hh0, hk, -⟩ := hw
    rw [same e he hk, hh] at hh0
    cases hh0
  | some h0 =>
    refine foldl_insOpt_eq g _ _ (fun e he w hw => ?_) (fun w hw => by simp at hw) (.inl ⟨(n, d), hn, ?_⟩)
    · simp only [g, Option.map_eq_some_iff, Prod.mk.injEq] at hw
      obtain ⟨h1, hh1, hk, rfl⟩ := hw
      rw [same e he hk, hh] at hh1
      cases hh1
      rfl
    · have hh' : ixe.anonHints[d.addr]? = some h0 := by rw [← Std.HashMap.get?_eq_getElem?]; exact hh
      simp [g, hh']

/-- A record that is a definition block member's projection: the member it
projects and its address. -/
def projEntry (e : Address × Ixon.LazyConstant) : Option (ConstRef Address × Address) :=
  match e.2.get? with
  | some c =>
    match c.info with
    | .dPrj p => some (.member p.block p.idx.toNat, e.1)
    | _ => none
  | none => none

/-- `hintsOf` through the projection records, as a fold of inserts. -/
theorem hintsOf_eq (ixe : Ixon.Env) (r : ConstRef Address) :
    Ix.Cert.hintsOf ixe r =
      Ix.Cert.hintOf <$> ixe.anonHints.get? ((ixe.consts.toList.foldl (insOpt projEntry) {})[r]?.getD r.block) := by
  unfold Ix.Cert.hintsOf
  rw [Std.HashMap.fold_eq_foldl_toList, foldl_step (G := insOpt projEntry) ?step]
  · simp only [Std.HashMap.get?_eq_getElem?]
  · intro m e
    obtain ⟨a, lc⟩ := e
    simp only [insOpt, projEntry]
    split <;> (try split) <;> simp_all

/-- **The reader's hint at a block member** is the hint at its projection record,
when that is the one projection record of the member. -/
theorem hintsOf_projection {ixe : Ixon.Env} {r : ConstRef Address} {a : Address} {lc : Ixon.LazyConstant}
    (ha : (a, lc) ∈ ixe.consts.toList) (hp : projEntry (a, lc) = some (r, a))
    (one : ∀ e ∈ ixe.consts.toList, ∀ a', projEntry e = some (r, a') → a' = a) :
    Ix.Cert.hintsOf ixe r = Ix.Cert.hintOf <$> ixe.anonHints.get? a := by
  rw [hintsOf_eq, foldl_insOpt_eq projEntry _ _ (fun e he w hw => one e he w hw) (fun w hw => by simp at hw)
    (.inl ⟨(a, lc), ha, hp⟩)]
  rfl

/-- **The reader's hint at a member no projection record projects** is the hint
at its block's record (a singleton's own). -/
theorem hintsOf_block {ixe : Ixon.Env} {r : ConstRef Address}
    (none : ∀ e ∈ ixe.consts.toList, ∀ a', projEntry e ≠ some (r, a')) :
    Ix.Cert.hintsOf ixe r = Ix.Cert.hintOf <$> ixe.anonHints.get? r.block := by
  rw [hintsOf_eq, (foldl_insOpt_none projEntry _ _).mpr ⟨none, by simp⟩]
  rfl

/-- **One hint per published definition**: Source's hint at a published name's
key is the reader's at a member whose record is the name's address. -/
theorem hints_agree {ixe : Ixon.Env}
    (agree : ∀ m d, (m, d) ∈ ixe.named.toList → (Ix.LeanIngress.sourceAddrs ixe)[ingressName m]? = some d.addr)
    {n : Ix.Name} {d : Ixon.Named} (hn : (n, d) ∈ ixe.named.toList) {r : ConstRef Address}
    (hr : Ix.Cert.hintsOf ixe r = Ix.Cert.hintOf <$> ixe.anonHints.get? d.addr) :
    (fiberHintsMap ixe)[ingressKey n]? = Ix.Cert.hintsOf ixe r := by
  rw [fiberHintsMap_named agree hn, hr, hintOfLean_eq_hintOf]

end Ix.Cert.CtxAgree
