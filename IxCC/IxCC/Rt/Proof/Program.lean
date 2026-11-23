import IxCC.Rt.Proof.StrHoist
import IxCC.Rt.Proof.Prune
import IxCC.Lir.Proof.Split
import IxCC.Cfg.Proof.Fuel

/-!
# The lowered program, stage by stage

`Rt.lower` lowers each Cfg function (`functionRaw`), prunes it, splits its
critical edges, and appends the runtime procedures. `rawProg` and
`prunedProg` are the program before pruning and before splitting (each
with `main` set to the function run). `lower_spec` reads `Rt.lower`'s
result off; `target_raw` gives the unpruned program's `Target`;
`raw_pruned` and `pruned_split` the two relabellings; `lower_ordered`
the order Cfg's clock needs.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word Label)
open IxCC.Rt.Lower
open IxCC.Src (NatMap NatSet)

/-! ## Reading `Rt.lower` off -/

/-- A root's calling convention. -/
def convOf (roots : List (Nat × String)) (f : Nat) : Lir.Conv :=
  match roots.lookup f with
  | some s => .sysvExport s
  | none => .internal

theorem function_spec {T : Tables} {f : Nat} {fd : Cfg.Fun} {conv : Lir.Conv} {F : Lir.Func}
    (h : function T f fd conv = .ok F) :
    ∃ params raw, functionRaw T f fd = .ok (params, raw) ∧ reachClosed raw (reachable raw) = true ∧
      F = Lir.Func.splitCriticalEdges
        { name := s!"f{f}", params, results := 1, blocks := (pruneWith (reachable raw) raw).toArray, conv } := by
  unfold function at h
  cases hr : functionRaw T f fd with
  | error e => simp [hr, bind, Except.bind] at h
  | ok p =>
    obtain ⟨params, raw⟩ := p
    simp only [hr, bind, Except.bind] at h
    by_cases hc : reachClosed raw (reachable raw) = true
    · simp only [hc, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨params, raw, rfl, hc, h.symm⟩
    · simp [hc, throw, throwThe, MonadExceptOf.throw] at h

theorem functions_spec {T : Tables} {P : Cfg.Program} {roots : List (Nat × String)} :
    ∀ {fs : List Nat} {funcs : List Lir.Func}, functions T P roots fs = .ok funcs →
      funcs.length = fs.length ∧ ∀ {i f : Nat}, fs[i]? = some f →
        ∃ fd F, P.fun? f = some fd ∧ function T f fd (convOf roots f) = .ok F ∧ funcs[i]? = some F
  | [], funcs, h => by
    simp only [functions, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun h => by simp at h⟩
  | f :: fs, funcs, h => by
    simp only [functions, bind, Except.bind] at h
    cases hfd : P.fun? f with
    | none => simp [hfd, throw, throwThe, MonadExceptOf.throw] at h
    | some fd =>
      simp only [hfd] at h
      split at h
      · cases h
      · rename_i F hF
        split at h
        · cases h
        · rename_i rest hr
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨hlen, hrest⟩ := functions_spec hr
          refine ⟨by simp [hlen], fun {i g} hi => ?_⟩
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            exact ⟨fd, F, hfd, hF, rfl⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hi ⊢
            exact hrest hi

/-- **What `Rt.lower` returns.** -/
theorem lower_spec {cfg : Config} {P : Cfg.Program} {L : IxCC.Rt.Lowered} (h : lower cfg P = .ok L) :
    ∃ funcs, functions (tables (lowerCfg P)) (lowerCfg P) L.roots (List.range P.size) = .ok funcs ∧
      L.program.funcs = (funcs ++ [Procs.cxInit, Procs.natPow, Procs.natGcd] ++ lowerStrProcs P).toArray ∧
      ∀ {f : Nat} {fd : Cfg.Fun}, P.fun? f = some fd → f < P.size := by
  unfold lower at h
  cases hm : P.exports.head? with
  | none => simp [hm, throw, throwThe, MonadExceptOf.throw] at h
  | some main =>
    simp only [hm, bind, Except.bind] at h
    cases hr : P.funs.toList.find? (P.size ≤ ·.1) with
    | some p => simp [hr, throw, throwThe, MonadExceptOf.throw] at h
    | none =>
      simp only [hr] at h
      unfold lowerCore at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i res hres
        split at hres
        · cases hres
        · rename_i funcs hfs
          cases hemp : (lowerStrs P).isEmpty with
          | true =>
            simp only [hemp, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hres
            subst hres
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have hnil : lowerStrs P = [] := List.isEmpty_iff.1 hemp
            have hsp : lowerStrProcs P = [] := by simp [lowerStrProcs, hnil]
            refine ⟨funcs, hfs, by simp [hsp], fun {f fd} hf => ?_⟩
            have hmem := NatMap.mem_toList hf
            have := List.find?_eq_none.1 hr (f, fd) hmem
            simpa using this
          | false =>
            simp only [hemp, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hres
            subst hres
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            refine ⟨funcs, hfs, rfl, fun {f fd} hf => ?_⟩
            have hmem := NatMap.mem_toList hf
            have := List.find?_eq_none.1 hr (f, fd) hmem
            simpa using this


/-! ## The stages -/

/-- A Cfg function's lowering before pruning (a filler where it declines). -/
def rawOf (P : Cfg.Program) (roots : List (Nat × String)) (f : Nat) : Lir.Func :=
  match P.fun? f with
  | some fd =>
    match functionRaw (tables P) f fd with
    | .ok (params, raw) => { name := s!"f{f}", params, results := 1, blocks := raw.toArray, conv := convOf roots f }
    | .error _ => default
  | none => default

/-- A Cfg function's lowering after pruning. -/
def prunedOf (P : Cfg.Program) (roots : List (Nat × String)) (f : Nat) : Lir.Func :=
  match P.fun? f with
  | some fd =>
    match functionRaw (tables P) f fd with
    | .ok (params, raw) =>
      { name := s!"f{f}", params, results := 1, blocks := (pruneWith (reachable raw) raw).toArray,
        conv := convOf roots f }
    | .error _ => default
  | none => default

/-- The program of a stage's functions, the runtime procedures, and extra trailing procedures,
run from `g`. -/
def stageProgWith (P : Cfg.Program) (extra : List Lir.Func) (fs : Nat → Lir.Func) (g : Nat) : Lir.Program :=
  { funcs := ((List.range P.size).map fs ++ [Procs.cxInit, Procs.natPow, Procs.natGcd] ++ extra).toArray, main := g }

/-- The program of a stage's functions and the runtime procedures, run
from `g`. -/
def stageProg (P : Cfg.Program) (fs : Nat → Lir.Func) (g : Nat) : Lir.Program :=
  { funcs := ((List.range P.size).map fs ++ [Procs.cxInit, Procs.natPow, Procs.natGcd]).toArray, main := g }

/-- The program of a stage's functions for `lowerCfg P`, the runtime procedures, and `lowerStrProcs P`,
run from `g`. -/
def stageProgStr (P : Cfg.Program) (fs : Nat → Lir.Func) (g : Nat) : Lir.Program :=
  stageProgWith (lowerCfg P) (lowerStrProcs P) fs g

theorem stageProgWith_get (P : Cfg.Program) (extra : List Lir.Func) (fs : Nat → Lir.Func) (g f : Nat) :
    (stageProgWith P extra fs g).funcs[f]? =
      if f < P.size then some (fs f)
      else ([Procs.cxInit, Procs.natPow, Procs.natGcd] ++ extra)[f - P.size]? := by
  simp only [stageProgWith, List.append_assoc, List.getElem?_toArray]
  split
  · rename_i hf
    rw [List.getElem?_append_left (by simpa using hf)]
    simp [hf]
  · rename_i hf
    rw [List.getElem?_append_right (by simp; omega)]
    simp

theorem stageProg_get (P : Cfg.Program) (fs : Nat → Lir.Func) (g f : Nat) :
    (stageProg P fs g).funcs[f]? =
      if f < P.size then some (fs f) else [Procs.cxInit, Procs.natPow, Procs.natGcd][f - P.size]? := by
  simp only [stageProg, List.getElem?_toArray]
  split
  · rename_i hf
    rw [List.getElem?_append_left (by simpa using hf)]
    simp [hf]
  · rename_i hf
    rw [List.getElem?_append_right (by simp; omega)]
    simp

theorem stageProgStr_get (P : Cfg.Program) (fs : Nat → Lir.Func) (g f : Nat) :
    (stageProgStr P fs g).funcs[f]? =
      if f < P.size then some (fs f)
      else ([Procs.cxInit, Procs.natPow, Procs.natGcd] ++ lowerStrProcs P)[f - P.size]? := by
  unfold stageProgStr
  rw [stageProgWith_get, lowerCfg_size]

/-- The kept labels of each function. -/
def pruneRel (P : Cfg.Program) (f : Nat) : Label → Label → Prop :=
  match P.fun? f with
  | some fd =>
    match functionRaw (tables P) f fd with
    | .ok (_, raw) => Kept raw (reachable raw)
    | .error _ => Eq
  | none => Eq

/-- The split labels of each function. -/
def splitRelOf (P : Cfg.Program) (roots : List (Nat × String)) (f : Nat) : Label → Label → Prop :=
  if f < P.size then Lir.splitRel (prunedOf P roots f) else Eq

/-- What `Rt.lower`'s success says of every function. -/
structure Lowers (P : Cfg.Program) (roots : List (Nat × String)) : Prop where
  dense : ∀ {f : Nat} {fd : Cfg.Fun}, P.fun? f = some fd → f < P.size
  fn : ∀ {f : Nat}, f < P.size → ∃ fd params raw, P.fun? f = some fd ∧
    functionRaw (tables P) f fd = .ok (params, raw) ∧ reachClosed raw (reachable raw) = true

theorem lower_lowers {cfg : Config} {P : Cfg.Program} {L : IxCC.Rt.Lowered} (h : lower cfg P = .ok L) :
    Lowers (lowerCfg P) L.roots ∧
      ∀ {f : Nat}, f < P.size → L.program.funcs[f]? = some (prunedOf (lowerCfg P) L.roots f).splitCriticalEdges := by
  obtain ⟨funcs, hfs, hprog, hdense⟩ := lower_spec h
  obtain ⟨hlen, hget⟩ := functions_spec hfs
  have hdense' : ∀ {f : Nat} {fd : Cfg.Fun}, (lowerCfg P).fun? f = some fd → f < (lowerCfg P).size := by
    intro f fd hf
    rw [lowerCfg_size]
    unfold lowerCfg at hf
    split at hf
    · exact hdense hf
    · exact hoistStrings_dense (lowerStrFns P) hdense hf
  have hone : ∀ {f : Nat}, f < P.size → ∃ fd params raw F, (lowerCfg P).fun? f = some fd ∧
      functionRaw (tables (lowerCfg P)) f fd = .ok (params, raw) ∧ reachClosed raw (reachable raw) = true ∧
      funcs[f]? = some F ∧ F = (prunedOf (lowerCfg P) L.roots f).splitCriticalEdges := by
    intro f hf
    obtain ⟨fd, F, hfd, hF, hfF⟩ := hget (i := f) (f := f) (by simp [hf])
    obtain ⟨params, raw, hraw, hc, rfl⟩ := function_spec hF
    refine ⟨fd, params, raw, _, hfd, hraw, hc, hfF, ?_⟩
    simp [prunedOf, hfd, hraw]
  refine ⟨⟨hdense', fun {f} hf => ?_⟩, fun {f} hf => ?_⟩
  · rw [lowerCfg_size] at hf
    obtain ⟨fd, params, raw, F, h1, h2, h3, -⟩ := hone hf
    exact ⟨fd, params, raw, h1, h2, h3⟩
  · obtain ⟨fd, params, raw, F, -, -, -, hF, rfl⟩ := hone hf
    rw [hprog, List.append_assoc, List.getElem?_toArray, List.getElem?_append_left (by rw [hlen]; simpa using hf)]
    exact hF

/-- The unpruned program's functions are laid out as `Lowered` says. -/
theorem target_raw {P : Cfg.Program} {roots : List (Nat × String)} (hl : Lowers P roots) (g : Nat) :
    Target P (stageProg P (rawOf P roots) g) where
  fn := by
    intro f fd hfd
    have hf := hl.dense hfd
    obtain ⟨fd', params, raw, hfd', hraw, -⟩ := hl.fn hf
    rw [hfd] at hfd'
    cases hfd'
    obtain ⟨starts, hL⟩ := functionRaw_lowered hraw s!"f{f}" (convOf roots f)
    refine ⟨_, starts, ?_, hL⟩
    rw [stageProg_get, ite_eq_left hf]
    simp [rawOf, hfd, hraw]
  pow := by
    rw [stageProg_get, ite_eq_right (by simp [tables])]
    simp [tables]
  gcd := by
    rw [stageProg_get, ite_eq_right (by simp [tables])]
    simp [tables]

/-- The unpruned string-hoisted program's functions and string procs are laid out as `TargetStr` says. -/
theorem targetStr_raw {P : Cfg.Program} {roots : List (Nat × String)}
    (hl : Lowers (lowerCfg P) roots) (g : Nat) :
    TargetStr P (lowerCfg P) (stageProgStr P (rawOf (lowerCfg P) roots) g) where
  base := {
    fn := by
      intro f fd hfd
      have hf := hl.dense hfd
      obtain ⟨fd', params, raw, hfd', hraw, -⟩ := hl.fn hf
      rw [hfd] at hfd'
      cases hfd'
      obtain ⟨starts, hL⟩ := functionRaw_lowered hraw s!"f{f}" (convOf roots f)
      refine ⟨_, starts, ?_, hL⟩
      rw [stageProgStr_get, ite_eq_left (by simpa [lowerCfg_size] using hf)]
      simp [rawOf, hfd, hraw]
    pow := by
      rw [stageProgStr_get, ite_eq_right (by simp [tables, lowerCfg_size])]
      simp [tables, lowerCfg_size]
    gcd := by
      rw [stageProgStr_get, ite_eq_right (by simp [tables, lowerCfg_size])]
      simp [tables, lowerCfg_size]
  }
  strs := by
    intro i s hs
    rw [stageProgStr_get, ite_eq_right (by omega)]
    have hsub : P.size + 3 + i - P.size = 3 + i := by omega
    rw [hsub, List.getElem?_append_right (by simp)]
    simp [lowerStrProcs, hs]

/-- A lowered function has blocks. -/
theorem raw_ne_nil {P : Cfg.Program} {f : Nat} {fd : Cfg.Fun} {params : List Nat} {raw : List Lir.Block}
    (_hfd : P.fun? f = some fd) (hraw : functionRaw (tables P) f fd = .ok (params, raw)) : raw ≠ [] := by
  obtain ⟨starts, hL⟩ := functionRaw_lowered hraw "" .internal
  have hb0 : ∃ b0, fd.blocks[0]? = some b0 := by
    unfold functionRaw at hraw
    cases hb : fd.blocks.head? with
    | none => simp [hb, throw, throwThe, MonadExceptOf.throw] at hraw
    | some b0 =>
      refine ⟨b0, ?_⟩
      cases hbl : fd.blocks with
      | nil => simp [hbl] at hb
      | cons c l => simp only [hbl, List.head?_cons, Option.some.injEq] at hb; simp [hb]
  obtain ⟨b0, hb0⟩ := hb0
  obtain ⟨o0, ho0, -⟩ := hL.entry hb0
  obtain ⟨tb, htb, -⟩ := hL.head hb0 ho0
  intro hnil
  subst hnil
  simp at htb

/-- **Pruning, program-wide.** -/
theorem raw_pruned {P : Cfg.Program} {roots : List (Nat × String)} (hl : Lowers P roots) (g : Nat) :
    Lir.ProgSim (stageProg P (rawOf P roots) g) (stageProg P (prunedOf P roots) g) (pruneRel P) where
  main := rfl
  funcs := by
    intro f F hF
    rw [stageProg_get] at hF
    split at hF
    · rename_i hf
      simp only [Option.some.injEq] at hF
      subst hF
      obtain ⟨fd, params, raw, hfd, hraw, hc⟩ := hl.fn hf
      refine ⟨prunedOf P roots f, by rw [stageProg_get, ite_eq_left hf], ?_⟩
      have h1 : (rawOf P roots f).blocks = raw.toArray := by simp [rawOf, hfd, hraw]
      have h2 : prunedOf P roots f = { rawOf P roots f with blocks := (pruneWith (reachable raw) raw).toArray } := by
        simp [prunedOf, rawOf, hfd, hraw]
      have h3 : pruneRel P f = Kept raw (reachable raw) := by simp [pruneRel, hfd, hraw]
      rw [h2, h3]
      exact prune_sim h1 hc (reachable_zero raw) (raw_ne_nil hfd hraw)
    · rename_i hf
      refine ⟨F, by rw [stageProg_get, ite_eq_right hf]; exact hF, ?_⟩
      have h3 : pruneRel P f = Eq := by
        unfold pruneRel
        cases hfd : P.fun? f with
        | none => rfl
        | some fd => exact absurd (hl.dense hfd) hf
      rw [h3]
      exact Lir.funcSim_refl F

/-- **Pruning, program-wide (with appended string procedures).** -/
theorem raw_pruned_str {P : Cfg.Program} {roots : List (Nat × String)}
    (hl : Lowers (lowerCfg P) roots) (g : Nat) :
    Lir.ProgSim (stageProgStr P (rawOf (lowerCfg P) roots) g)
      (stageProgStr P (prunedOf (lowerCfg P) roots) g) (pruneRel (lowerCfg P)) where
  main := rfl
  funcs := by
    intro f F hF
    rw [stageProgStr_get] at hF
    split at hF
    · rename_i hf
      simp only [Option.some.injEq] at hF
      subst hF
      obtain ⟨fd, params, raw, hfd, hraw, hc⟩ := hl.fn (by simpa [lowerCfg_size] using hf)
      refine ⟨prunedOf (lowerCfg P) roots f, by rw [stageProgStr_get, ite_eq_left hf], ?_⟩
      have h1 : (rawOf (lowerCfg P) roots f).blocks = raw.toArray := by simp [rawOf, hfd, hraw]
      have h2 : prunedOf (lowerCfg P) roots f =
          { rawOf (lowerCfg P) roots f with blocks := (pruneWith (reachable raw) raw).toArray } := by
        simp [prunedOf, rawOf, hfd, hraw]
      have h3 : pruneRel (lowerCfg P) f = Kept raw (reachable raw) := by simp [pruneRel, hfd, hraw]
      rw [h2, h3]
      exact prune_sim h1 hc (reachable_zero raw) (raw_ne_nil hfd hraw)
    · rename_i hf
      refine ⟨F, by rw [stageProgStr_get, ite_eq_right hf]; exact hF, ?_⟩
      have h3 : pruneRel (lowerCfg P) f = Eq := by
        unfold pruneRel
        cases hfd : (lowerCfg P).fun? f with
        | none => rfl
        | some fd => exact absurd (by simpa [lowerCfg_size] using hl.dense hfd) hf
      rw [h3]
      exact Lir.funcSim_refl F

/-- **Edge splitting, program-wide.** -/
theorem pruned_split {cfg : Config} {P : Cfg.Program} {L : IxCC.Rt.Lowered} (h : lower cfg P = .ok L) (g : Nat) :
    Lir.ProgSim (stageProgStr P (prunedOf (lowerCfg P) L.roots) g)
      { L.program with main := g } (splitRelOf (lowerCfg P) L.roots) where
  main := rfl
  funcs := by
    obtain ⟨-, hget⟩ := lower_lowers h
    obtain ⟨funcs, hfs, hprog, -⟩ := lower_spec h
    obtain ⟨hlen, -⟩ := functions_spec hfs
    intro f F hF
    rw [stageProgStr_get] at hF
    split at hF
    · rename_i hf
      simp only [Option.some.injEq] at hF
      subst hF
      refine ⟨_, hget hf, ?_⟩
      have : splitRelOf (lowerCfg P) L.roots f = Lir.splitRel (prunedOf (lowerCfg P) L.roots f) := by
        simp [splitRelOf, lowerCfg_size, hf]
      rw [this]
      exact Lir.split_sim _
    · rename_i hf
      refine ⟨F, ?_, ?_⟩
      · show L.program.funcs[f]? = some F
        rw [hprog, List.append_assoc, List.getElem?_toArray,
          List.getElem?_append_right (by rw [hlen]; simp; omega), hlen]
        simpa using hF
      · have : splitRelOf (lowerCfg P) L.roots f = Eq := by simp [splitRelOf, lowerCfg_size, hf]
        rw [this]
        exact Lir.funcSim_refl F

end IxCC.Rt.Proof
