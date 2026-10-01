import Compilatrix.Rt.Proof.Program
import Compilatrix.Rt.Proof.LayoutFun
import Compilatrix.Rt.Proof.Publish

/-!
# The lowered roots' functions

`Rt.lower` exports each root's function under the root's symbol: a root
`(fn, sym)` of the lowered program (`fn` a Cfg function) is a SysV export of
`sym` taking the Cfg function's parameters (`lower_root_func`). A function
exported twice keeps its first symbol, which every root of it carries
(`lookup_dedup`).
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Rt.Lower

theorem lookup_map {α β : Type} [BEq α] [LawfulBEq α] (G : α → β → β) (a : α) :
    ∀ l : List (α × β), (l.map fun p => (p.1, G p.1 p.2)).lookup a = (l.lookup a).map (G a)
  | [] => rfl
  | (k, b) :: es => by
    simp only [List.map_cons, List.lookup_cons]
    cases hk : a == k
    · exact lookup_map G a es
    · have := beq_iff_eq.1 hk
      subst this
      rfl

theorem lookup_isSome {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, (a, b) ∈ l → ∃ b', l.lookup a = some b'
  | [], h => absurd h List.not_mem_nil
  | (k, c) :: es, h => by
    simp only [List.lookup_cons]
    cases hk : a == k
    · rcases List.mem_cons.1 h with h | h
      · cases h; simp at hk
      · exact lookup_isSome h
    · exact ⟨c, rfl⟩

/-- A list keyed by its first occurrences: every entry's value is its key's
first value, which `lookup` finds. -/
theorem lookup_dedup {α β : Type} [BEq α] [LawfulBEq α] (named : List (α × β)) {x : α × β}
    (hx : x ∈ named.map fun p => (p.1, (named.lookup p.1).getD p.2)) :
    (named.map fun p => (p.1, (named.lookup p.1).getD p.2)).lookup x.1 = some x.2 := by
  rw [lookup_map (fun f s => (named.lookup f).getD s) x.1 named]
  obtain ⟨⟨f, s⟩, hmem, rfl⟩ := List.mem_map.1 hx
  obtain ⟨b', hb'⟩ := lookup_isSome hmem
  simp [hb']

/-- `Rt.lower`'s roots keep each function's first symbol. -/
theorem lower_roots {cfg : Config} {P : Cfg.Program} {L : Compilatrix.Rt.Lowered} (h : lower cfg P = .ok L) :
    ∃ named : List (Nat × String), L.roots = named.map fun p => (p.1, (named.lookup p.1).getD p.2) := by
  unfold lower at h
  cases hm : P.exports.head? with
  | none => simp [hm, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | some main =>
    simp only [hm, bind, Except.bind] at h
    cases hr : P.funs.toList.find? (P.size ≤ ·.1) with
    | some p => simp [hr, throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    | none =>
      simp only [hr] at h
      split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨_, rfl⟩

/-- A root's convention is its symbol's export. -/
theorem lower_root_conv {cfg : Config} {P : Cfg.Program} {L : Compilatrix.Rt.Lowered} (h : lower cfg P = .ok L)
    {r fn : Nat} {sym : String} (hr : L.roots[r]? = some (fn, sym)) : convOf L.roots fn = .sysvExport sym := by
  obtain ⟨named, hn⟩ := lower_roots h
  have hmem := List.mem_of_getElem? hr
  rw [hn] at hmem
  have := lookup_dedup named hmem
  rw [← hn] at this
  simp [convOf, this]

/-- Edge splitting keeps a function's parameters and convention. -/
theorem split_params_conv (F : Lir.Func) :
    F.splitCriticalEdges.params = F.params ∧ F.splitCriticalEdges.conv = F.conv := by
  unfold Lir.Func.splitCriticalEdges
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- A lowered function takes its Cfg function's parameters and carries the
convention it was given. -/
theorem function_params {T : Tables} {f : Nat} {fd : Cfg.Fun} {conv : Lir.Conv} {F : Lir.Func}
    (h : function T f fd conv = .ok F) : F.params.length = fd.params.length ∧ F.conv = conv := by
  obtain ⟨params, raw, hraw, -, rfl⟩ := function_spec h
  obtain ⟨hp, hc⟩ := split_params_conv
    { name := s!"f{f}", params, results := 1, blocks := (pruneWith (reachable raw) raw).toArray, conv }
  rw [hp, hc]
  refine ⟨?_, rfl⟩
  obtain ⟨starts, low⟩ := functionRaw_lowered hraw "" conv
  cases hb : fd.blocks with
  | nil =>
    unfold functionRaw at hraw
    simp [hb, throw, throwThe, MonadExceptOf.throw, Except.bind] at hraw
  | cons b0 bs =>
    have hb0 : fd.blocks[0]? = some b0 := by rw [hb]; rfl
    obtain ⟨o0, -, hent⟩ := low.entry hb0
    have hfp : fd.params.length = b0.params.length := by
      simp [Cfg.Fun.params, hb]
    rw [hfp]
    rcases hent with ⟨-, -, hpar⟩ | ⟨-, -, -, -, -, hlen⟩
    · have := congrArg List.length hpar
      simpa using this
    · exact hlen

/-- **A root's function**: a lowered root `(fn, sym)` whose function is a Cfg
function is a SysV export of `sym` taking that function's parameters. -/
theorem lower_root_func {cfg : Config} {P : Cfg.Program} {L : Compilatrix.Rt.Lowered} (h : lower cfg P = .ok L)
    {r fn : Nat} {sym : String} (hr : L.roots[r]? = some (fn, sym)) (hlt : fn < P.size) :
    ∃ fd F, P.fun? fn = some fd ∧ L.program.funcs[fn]? = some F ∧ F.conv = .sysvExport sym ∧
      F.params.length = fd.params.length := by
  obtain ⟨funcs, hfs, hprog, -⟩ := lower_spec h
  obtain ⟨hlen, hget⟩ := functions_spec hfs
  obtain ⟨fd, F, hfd, hF, hfF⟩ := hget (i := fn) (f := fn) (by simp [hlt])
  obtain ⟨hpar, hconv⟩ := function_params hF
  refine ⟨fd, F, hfd, ?_, by rw [hconv, lower_root_conv h hr], hpar⟩
  rw [hprog, List.getElem?_toArray, List.getElem?_append_left (by simp at hlen; omega)]
  exact hfF

end Compilatrix.Rt.Proof
