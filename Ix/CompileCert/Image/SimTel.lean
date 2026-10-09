import Ix.CompileCert.Image.Fv

/-!
# M7 L2a-syn: the generator's telescopes from shifted counters

`telescope` opens binders with fresh names; from a counter shifted by `d` it opens the same
binders under the shifted names (`sim_telescope`).
-/

namespace Ix.CompileCert.Img

open Ix (Name Level Expr)
open Ix.Compile.Image (GenM GenState freshName Local telescope)

section
variable (s0 d B : Nat)

/-- Expressions of the two runs: renamed by the shift, and the first's free variables fresh
names below the bound. -/
def RE (a b : Expr) : Prop := Ren (shift s0 d) a b ∧ FvAll (FreshBelow B) a

/-- Locals of the two runs. -/
def RL (l l' : Local) : Prop :=
  LocRen (shift s0 d) l l' ∧ FreshBelow B l.fvar ∧ FvAll (FreshBelow B) l.type

/-- Arrays of locals of the two runs. -/
def RLs (xs ys : Array Local) : Prop :=
  xs.size = ys.size ∧ ∀ i (h : i < xs.size) (h' : i < ys.size), RL s0 d B xs[i] ys[i]

end

section
variable {s0 d B : Nat}

theorem RLs.empty : RLs s0 d B #[] #[] := ⟨rfl, fun i h => by simp at h⟩

theorem RLs.push {xs ys : Array Local} (h : RLs s0 d B xs ys) {l l' : Local} (hl : RL s0 d B l l') :
    RLs s0 d B (xs.push l) (ys.push l') := by
  have hsz := h.1
  refine ⟨by simp [h.1], fun i hi hi' => ?_⟩
  simp only [Array.size_push] at hi hi'
  by_cases hlt : i < xs.size
  · rw [Array.getElem_push_lt hlt, Array.getElem_push_lt (by omega)]; exact h.2 i hlt (by omega)
  · have e1 : i = xs.size := by omega
    have e2 : i = ys.size := by omega
    subst e1
    rw [Array.getElem_push_eq]; simp only [e2, Array.getElem_push_eq]; exact hl

theorem RLs.exprs {xs ys : Array Local} (h : RLs s0 d B xs ys) :
    ARen (shift s0 d) (xs.map (·.expr)) (ys.map (·.expr)) ∧ LFv (FreshBelow B) (xs.map (·.expr)).toList := by
  refine ⟨?_, ?_⟩
  · unfold ARen
    apply (LRel.of_getElem (R := Ren (shift s0 d)) _ _ (by simp [h.1]) fun i h1 h2 => ?_).rec
      (motive := fun l l' _ => LRen (shift s0 d) l l') .nil (fun hab _ ih => .cons hab ih)
    simp only [Array.getElem_toList, Array.getElem_map, Ix.Compile.Image.Local.expr]
    simp only [Array.length_toList, Array.size_map] at h1 h2
    rw [(h.2 i h1 h2).1.1]
    exact Ren.mkFVar' _
  · intro x hx
    simp only [Array.toList_map, List.mem_map, Array.mem_toList_iff] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hl
    exact (h.2 i hi (by rw [← h.1]; exact hi)).2.1

theorem RLs.fv {xs ys : Array Local} (h : RLs s0 d B xs ys) :
    ∀ l ∈ xs, FreshBelow B l.fvar ∧ FvAll (FreshBelow B) l.type := by
  intro l hl
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hl
  exact (h.2 i hi (by rw [← h.1]; exact hi)).2

theorem RLs.lsRen {xs ys : Array Local} (h : RLs s0 d B xs ys) : LsRen (shift s0 d) xs ys :=
  ⟨h.1, fun i h1 h2 => (h.2 i h1 h2).1⟩

theorem RLs.extract {xs ys : Array Local} (h : RLs s0 d B xs ys) (a b : Nat) :
    RLs s0 d B (xs.extract a b) (ys.extract a b) := by
  refine ⟨by simp [h.1], fun i h1 h2 => ?_⟩
  simp only [Array.getElem_extract]
  simp only [Array.size_extract] at h1 h2
  exact h.2 _ (by omega) (by omega)

theorem mono_telescope (e : Expr) (n : Nat) : Mono (Ix.Compile.Image.telescope e n) := by
  unfold Ix.Compile.Image.telescope
  generalize Ix.Compile.Canon.peelForalls n e #[] = p
  obtain ⟨bs, body⟩ := p
  simp only
  refine Mono.bind (Mono.forIn_array (fun x r => ?_) _ _) fun _ => Mono.pure _
  obtain ⟨nm, t, bi⟩ := x
  exact Mono.bind Mono.freshName fun _ => Mono.pure _

/-- **Telescopes from shifted counters**: the same binders opened under the shifted names. -/
theorem sim_telescope (hok : InjOn (shift s0 d) (FreshBelow B)) {e e' : Expr} (he : RE s0 d B e e') (n : Nat) :
    Sim s0 d B (fun p q => RLs s0 d B p.1 q.1 ∧ RE s0 d B p.2 q.2) (telescope e n) (telescope e' n) := by
  have hi := hok
  unfold Ix.Compile.Image.telescope
  have hp := peelForalls_ren n he.1 (xs := #[]) (ys := #[]) ⟨rfl, fun i h => by simp at h⟩
  have hpf := peelForalls_fv n he.2 (acc := #[]) (by simp)
  generalize Ix.Compile.Canon.peelForalls n e #[] = p at hp hpf
  generalize Ix.Compile.Canon.peelForalls n e' #[] = q at hp hpf
  obtain ⟨bs, body⟩ := p
  obtain ⟨bs', body'⟩ := q
  obtain ⟨⟨hbs, hbr⟩, hbody⟩ := hp
  obtain ⟨hbsf, hbodyf⟩ := hpf
  simp only at hbs hbr hbody hbsf hbodyf ⊢
  refine Sim.bind (R := RLs s0 d B) ?_ (fun ls ls' hls => Sim.pure ⟨hls, ?_⟩)
    (fun _ => Mono.pure _)
  · refine Sim.forIn_array (Ra := fun x y => BRen (shift s0 d) x y ∧ FvAll (FreshBelow B) x.2.1)
      (fun x y r r' hxy hr => ?_) (fun x r => ?_) ?_ RLs.empty
    · obtain ⟨nm, t, bi⟩ := x
      obtain ⟨nm', t', bi'⟩ := y
      obtain ⟨⟨hnm, ht, hbi⟩, htf⟩ := hxy
      simp only at hnm ht hbi htf ⊢
      subst hnm hbi
      have hexp := hr.exprs
      refine Sim.bind Sim.freshName (fun f f' hf => Sim.pure ?_) (fun _ => Mono.pure _)
      exact hr.push ⟨⟨hf.1, rfl, instLocals_ren hexp.1 ht, rfl⟩, hf.2, instLocals_fv hexp.2 htf⟩
    · obtain ⟨nm, t, bi⟩ := x
      exact Mono.bind Mono.freshName fun _ => Mono.pure _
    · apply LRel.of_getElem _ _ (by simp [hbs])
      intro i h1 h2
      simp only [Array.getElem_toList]
      simp only [Array.length_toList] at h1 h2
      exact ⟨hbr i h1 h2, hbsf _ (Array.getElem_mem _)⟩
  · have hexp := hls.exprs
    exact ⟨instLocals_ren hexp.1 hbody, instLocals_fv hexp.2 hbodyf⟩

/-- `telescope` at its default arity. -/
theorem sim_telescope' (hok : InjOn (shift s0 d) (FreshBelow B)) {e e' : Expr} (he : RE s0 d B e e') :
    Sim s0 d B (fun p q => RLs s0 d B p.1 q.1 ∧ RE s0 d B p.2 q.2) (telescope e) (telescope e') := by
  rw [forallArity_ren he.1]; exact sim_telescope hok he _

end

end Ix.CompileCert.Img
