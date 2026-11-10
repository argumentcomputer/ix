import IxCC.Anf.Proof.Convert.App
import IxCC.Src.Proof.NatMap
import IxCC.Lam.Proof.Program

/-! # ANF conversion: the converted program

What a successful `convert L = .ok Q` gives the P1 simulation:
`L` is `ModesOk` (so every global's telescope has its kinds and its body is
well moded, `Lam.modesOk_sound`), and every global `g` of `L` has a global of
`Q` under the same id whose parameters are `g`'s leading telescope and whose
body is the telescope body's conversion; roots, constructor table and pinned
keys are unchanged. -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo later)
open IxCC.Lam (Kind Mode)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName InfoSpec KindsSpec sigsOf)
open IxCC.Ixon

theorem natMap_ofList_mem {α : Type} {xs : List (Nat × α)} (hn : (xs.map (·.1)).Nodup) {k : Nat}
    {x : α} (h : (Src.NatMap.ofList xs).get? k = some x) : (k, x) ∈ xs := by
  have hparts := Src.NatMap.get?_foldl_insert (f := fun m (p : Nat × α) => m.insert p.1 p.2)
    (fun _ _ => rfl) xs .leaf hn
  by_cases hk : k ∈ xs.map (·.1)
  · obtain ⟨⟨k', x'⟩, hmem, rfl⟩ := List.mem_map.1 hk
    have := hparts.2 _ _ hmem
    unfold Src.NatMap.ofList at h
    rw [this] at h
    cases h
    exact hmem
  · have := hparts.1 k hk
    unfold Src.NatMap.ofList at h
    rw [this] at h
    cases h

/-- Lam's telescope is conversion's, without the contracts. -/
theorem lam_telescope_eq : ∀ t : Lam.Term,
    Lam.Term.telescope t = ((telescope t).1.map (·.1), (telescope t).2)
  | .lam m c b => by simp only [Lam.Term.telescope, telescope, lam_telescope_eq b, List.map_cons]
  | .var _ | .glob _ | .app .. | .letE .. | .con .. | .case .. | .proj .. | .lit _ | .prim .. | .tick _
  | .box | .trap => rfl

theorem arities_get {L : Lam.Program} {g : GlobalId} {n : Nat} (h : (arities L).get? g = some n) :
    ∃ gl, L.global? g = some gl ∧ g < L.size ∧ n = (telescope gl.body).1.length := by
  unfold arities at h
  have hn : ((L.globalList.map fun (p : GlobalId × Lam.Global) =>
      (p.1, (telescope p.2.body).1.length)).map (·.1)).Nodup := by
    rw [List.map_map]
    exact Lam.Program.globalList_keys_nodup L
  have hmem := natMap_ofList_mem hn h
  obtain ⟨⟨g', gl⟩, hgl, e⟩ := List.mem_map.1 hmem
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨hlt, hg⟩ := Lam.Program.mem_globalList.1 hgl
  exact ⟨gl, hg, hlt, rfl⟩

theorem arities_of {L : Lam.Program} {g : GlobalId} {gl : Lam.Global} (hg : L.global? g = some gl)
    (hlt : g < L.size) : (arities L).get? g = some (telescope gl.body).1.length := by
  unfold arities
  refine Src.NatMap.get?_ofList ?_ (List.mem_map.2 ⟨(g, gl), Lam.Program.mem_globalList.2 ⟨hlt, hg⟩, rfl⟩)
  rw [List.map_map]
  exact Lam.Program.globalList_keys_nodup L

/-- What a successful conversion gives. -/
theorem convert_spec {L : Lam.Program} {Q : Program} (h : convert L = .ok Q) :
    Lam.modesOk L = true ∧ Q.size = L.size ∧ Q.roots = L.roots ∧ Q.ctors = L.ctors ∧
      Q.known = L.known ∧ L.roots.all (rootStrict L) = true ∧
      ∀ g gl, L.global? g = some gl → g < L.size →
        ∃ gd, Q.global? g = some gd ∧ Convert.global (arities L) gl = .ok gd := by
  unfold convert at h
  cases hm : Lam.modesOk L with
  | false =>
    simp only [hm] at h
    obtain ⟨_, he, _⟩ := Lam.ModesOk.bind_ok h
    cases he
  | true => ?_
  simp only [hm, ↓reduceIte] at h
  cases hr : L.roots.all (rootStrict L) with
  | false =>
    simp only [hr] at h
    obtain ⟨_, he, _⟩ := Lam.ModesOk.bind_ok h
    cases he
  | true => ?_
  simp only [hr, ↓reduceIte] at h
  cases hdn : (List.range L.size).all (fun g => (L.global? g).isSome) with
  | false =>
    simp only [hdn] at h
    obtain ⟨_, he, _⟩ := Lam.ModesOk.bind_ok h
    cases he
  | true => ?_
  simp only [hdn, ↓reduceIte] at h
  obtain ⟨gs, hgs, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun g gl hg hlt => ?_⟩
  obtain ⟨hlen, hall⟩ := Lam.ModesOk.mapM_ok hgs
  have hmem : (g, gl) ∈ L.globalList := Lam.Program.mem_globalList.2 ⟨hlt, hg⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
  obtain ⟨y, hy, hf⟩ := hall i _ hi
  obtain ⟨gd, hgd, hret⟩ := Lam.ModesOk.bind_ok hf
  have hgd' : Convert.global (arities L) gl = .ok gd := Lam.ModesOk.mapError_ok hgd
  cases hret
  refine ⟨gd, ?_, hgd'⟩
  show (Src.NatMap.ofList gs).get? g = some gd
  refine Src.NatMap.get?_ofList ?_ (List.mem_iff_getElem?.2 ⟨i, hy⟩)
  -- the keys of `gs` are the keys of the global list
  have hkeys : gs.map (·.1) = L.globalList.map (·.1) := by
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_map]
    cases hj : L.globalList[j]? with
    | none =>
      have : gs[j]? = none := by
        rw [List.getElem?_eq_none_iff] at hj ⊢; omega
      simp [this]
    | some p =>
      obtain ⟨y', hy', hf'⟩ := hall j p hj
      obtain ⟨gd', _, hret'⟩ := Lam.ModesOk.bind_ok hf'
      cases hret'
      simp [hy']
  rw [hkeys]
  exact Lam.Program.globalList_keys_nodup L

/-- A converted global: its parameters are the telescope, its body the
telescope body's conversion. -/
theorem global_spec {A : Arities} {gl : Lam.Global} {gd : GDef} (h : Convert.global A gl = .ok gd) :
    gd.ps.length = (telescope gl.body).1.length ∧
      conv A (fuelFor gl.body)
        { vars := pushParams [] 0 ((telescope gl.body).1.map (·.1 == .name)),
          d := (telescope gl.body).1.length, dj := 0 } (telescope gl.body).2 .ret = .ok gd.body := by
  unfold Convert.global at h
  obtain ⟨b, hb, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  exact ⟨by simp, hb⟩

/-- Kinds that a `KindsSpec` gives agree with the binders' modes. -/
theorem modesAgree_of_kindsSpec {ps : List (Mode × V3.BinderContract)} {d : Nat} {body : Lam.Term}
    {kinds : List Kind} (h : KindsSpec (ps.map (·.1)) d body kinds) : ModesAgree ps kinds := by
  obtain ⟨hl, hk⟩ := h
  refine ⟨by simpa using hl.symm, fun i p q hp hq => ?_⟩
  have hm : (ps.map (·.1))[i]? = some p.1 := by simp [hp]
  obtain ⟨hs, hn⟩ := hk i p.1 hm
  cases hpm : p.1 with
  | strict => rw [hs hpm] at hq; cases hq; rfl
  | name =>
    obtain ⟨sig, hsig, _⟩ := hn hpm
    rw [hsig] at hq; cases hq; rfl

/-- The P1 setting: a Lam program, its conversion, and the table of global
telescopes `ModesOk` gives. -/
structure Setting where
  L : Lam.Program
  Q : Program
  G : Src.NatMap GInfo
  hconv : convert L = .ok Q
  modes : ∀ g gl, L.global? g = some gl → g < L.size → ∃ gi kinds, G.get? g = some gi ∧
    InfoSpec gl.body gi kinds ∧ TermOk G kinds.reverse gl.body.telescope.2

theorem Setting.exists {L : Lam.Program} {Q : Program} (h : convert L = .ok Q) :
    ∃ S : Setting, S.L = L ∧ S.Q = Q := by
  obtain ⟨G, hG⟩ := Lam.modesOk_sound (convert_spec h).1
  exact ⟨⟨L, Q, G, h, fun g gl hg hlt => by
    obtain ⟨gi, kinds, h1, h2, -, h4⟩ := hG g gl hg hlt
    exact ⟨gi, kinds, h1, h2, h4⟩⟩, rfl, rfl⟩

namespace Setting

variable (S : Setting)

abbrev A : Arities := arities S.L

theorem known : S.Q.known = S.L.known := (convert_spec S.hconv).2.2.2.2.1

theorem rootsStrict : S.L.roots.all (rootStrict S.L) = true := (convert_spec S.hconv).2.2.2.2.2.1

theorem roots : S.Q.roots = S.L.roots := (convert_spec S.hconv).2.2.1

/-- Everything the simulation needs about a global with an arity. -/
theorem glob {g : GlobalId} {n : Nat} (h : S.A.get? g = some n) :
    ∃ gl gd gi kinds, S.L.global? g = some gl ∧ S.Q.global? g = some gd ∧ S.G.get? g = some gi ∧
      n = (telescope gl.body).1.length ∧ gd.ps.length = n ∧
      conv S.A (fuelFor gl.body)
        { vars := pushParams [] 0 (kinds.map Kind.isName), d := n, dj := 0 }
        (telescope gl.body).2 .ret = .ok gd.body ∧
      gi.tele = (telescope gl.body).1.map (·.1) ∧ gi.sigs = sigsOf kinds ∧
      ModesAgree (telescope gl.body).1 kinds ∧ TermOk S.G kinds.reverse (telescope gl.body).2 := by
  obtain ⟨gl, hg, hlt, rfl⟩ := arities_get h
  obtain ⟨gd, hgd, hconv⟩ := (convert_spec S.hconv).2.2.2.2.2.2 g gl hg hlt
  obtain ⟨gi, kinds, hgi, ⟨htele, hks, hsigs⟩, htm⟩ := S.modes g gl hg hlt
  rw [lam_telescope_eq] at htele htm hks
  have hma := modesAgree_of_kindsSpec (by rw [htele] at hks; exact hks)
  obtain ⟨hps, hbody⟩ := global_spec hconv
  rw [modesAgree_thunks hma] at hbody
  exact ⟨gl, gd, gi, kinds, hg, hgd, hgi, rfl, hps, hbody, htele, hsigs, hma, htm⟩

end Setting

end IxCC.Anf.Convert.Proof
