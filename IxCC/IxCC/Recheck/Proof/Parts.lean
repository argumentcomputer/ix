import IxCC.Recheck.Proof.Front
import IxCC.Recheck.Linked
import IxCC.Backend.Proof.Exports
import IxCC.Backend.Proof.Funcs
import IxCC.Rt.Proof.Roots

/-!
# What `Recheck.run` made, part by part

`run_parts`: an artifact `Recheck.run` returns is its front half
(`runLir`, as `Artifact.front`), selection on the lowered program
(`Select.select`), the allocation certificate validated and applied
(`Validate.run`), the backend's emission of the Xl program with the
certificate's frame layouts and block order (`Backend.emit`, whose
`lay` and `finish` `run` performs), with every export its own symbol
(`checkSymbols`).

`run_root` and `run_init`: every lowered root is a SysV export of its symbol
in the Xl program, taking its Cfg function's parameters, and is not
`cx_init`; `cx_init` is the SysV export `cx_init` with two parameters.
-/

set_option autoImplicit false

namespace IxCC.Recheck

theorem sharedSymbol?_nodup : ∀ {es : List Xv.Stacking.Export}, sharedSymbol? es = none → (es.map (·.symbol)).Nodup
  | [], _ => List.nodup_nil
  | e :: rest, h => by
    simp only [sharedSymbol?, Backend.sharedSymbol?] at h
    split at h
    · cases h
    · rename_i hany
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => hany ?_, sharedSymbol?_nodup h⟩
      obtain ⟨e', he', hs⟩ := List.mem_map.1 hm
      exact List.any_eq_true.2 ⟨e', he', by simp [hs]⟩

theorem checkSymbols_ok {es : List Xv.Stacking.Export} {u : Unit} (h : checkSymbols es = .ok u) :
    (es.map (·.symbol)).Nodup := by
  unfold checkSymbols at h
  split at h
  · exact sharedSymbol?_nodup (by assumption)
  · cases h

theorem backTyped_parts {cfg : Config} {l : Rt.Lowered} {root : Ixon.Address} {c : Cert} {xv : Xv.VProgram}
    {xl : Xv.LProgram} {stacked : Xv.Stacking.Stacked} {program : X86.Program} {exports : List (String × X86.BlockId)}
    (h : backTyped cfg l root c = .ok (xv, xl, stacked, program, exports)) :
    Xv.Select.select l.program = .ok xv ∧ Xv.Validate.run cfg.env xv c.alloc = .ok xl ∧
      Backend.lay xl (backendConfig cfg l root c) = .ok (stacked, program, exports) := by
  unfold backTyped at h
  simp only [bind, Except.bind, Except.mapError] at h
  cases hs : Xv.Select.select l.program with
  | error e => simp [hs] at h
  | ok xv' =>
    simp only [hs] at h
    cases hv : Xv.Validate.program cfg.env xv' c.alloc with
    | error e => simp [hv] at h
    | ok u =>
      simp only [hv] at h
      cases ha : Xv.Alloc.applyProgram xv' c.alloc with
      | error e => simp [ha] at h
      | ok xl' =>
        simp only [ha] at h
        cases hl : Backend.lay xl' (backendConfig cfg l root c) with
        | error e => simp [hl] at h
        | ok r =>
          obtain ⟨st, pr, ex⟩ := r
          simp only [hl, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          refine ⟨rfl, ?_, hl⟩
          unfold Xv.Validate.run
          rw [hv]
          exact ha

theorem finish_stacked {main : Lir.FunId} {stacked : Xv.Stacking.Stacked} {program : X86.Program}
    {exports : List (String × X86.BlockId)} {prov : X86.ELF.Provenance} {b : Backend.Artifact}
    (h : Backend.finish main stacked program exports prov = .ok b) : b.stacked = stacked := by
  unfold Backend.finish at h
  simp only [bind, Except.bind, Except.mapError] at h
  cases hc : program.checkK with
  | error e => simp [hc] at h
  | ok checked =>
    simp only [hc] at h
    cases he : X86.Stream.encodeK checked with
    | error e => simp [he] at h
    | ok stream =>
      simp only [he] at h
      cases hf : stacked.exports.find? (·.fn == main) with
      | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
      | some entry =>
        simp only [hf] at h
        split at h
        · cases h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          rw [← h]

/-- **`Recheck.run`, part by part.** -/
theorem run_parts {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact} (h : run cfg P c = .ok a) :
    runLir cfg P c = .ok a.front ∧ ∃ xv : Xv.VProgram,
      Xv.Select.select a.lowered.program = .ok xv ∧ Xv.Validate.run cfg.env xv c.alloc = .ok a.xl ∧
      Backend.emit a.xl (backendConfig cfg a.lowered ((a.src.roots.head?.map (·.1)).getD default) c) = .ok a.backend ∧
      Backend.SymbolsApart a.backend := by
  unfold run at h
  cases ht : runTyped cfg P c with
  | error e => rw [ht] at h; cases h
  | ok t =>
    rw [ht] at h
    simp only [bind, Except.bind] at h
    cases hc : checkSymbols t.stacked.exports with
    | error e => rw [hc] at h; cases h
    | ok u =>
      rw [hc] at h
      simp only at h
      cases hb : Backend.finish t.xl.main t.stacked t.program t.exports t.provenance with
      | error e => rw [hb] at h; cases h
      | ok b =>
        simp only [hb, Except.mapError, pure, Except.pure, Except.ok.injEq] at h
        subst h
        unfold runTyped at ht
        cases hf : runLir cfg P c with
        | error e => rw [hf] at ht; cases ht
        | ok f =>
          rw [hf] at ht
          simp only [bind, Except.bind] at ht
          split at ht
          · cases ht
          · rename_i r hbt
            obtain ⟨xv, xl, stacked, program, exports⟩ := r
            simp only [pure, Except.pure, Except.ok.injEq] at ht
            subst ht
            obtain ⟨hs, hv, hl⟩ := backTyped_parts hbt
            refine ⟨rfl, xv, hs, hv, ?_, ?_⟩
            · have hsym : Backend.checkSymbols stacked.exports = .ok () := by
                unfold checkSymbols at hc
                unfold Backend.checkSymbols
                split at hc
                · rename_i hs
                  simp only [sharedSymbol?] at hs
                  rw [hs]
                  rfl
                · cases hc
              unfold Backend.emit
              simp only [bind, Except.bind]
              rw [hl]
              simp only [hsym]
              exact hb
            · have := checkSymbols_ok hc
              have hst : b.stacked = stacked := finish_stacked hb
              show (b.stacked.exports.map (·.symbol)).Nodup
              rw [hst]
              exact this

/-- Fir's exports are its functions. -/
theorem fir_exports_lt {A : Anf.Program} {F : Fir.Program} (h : Fir.lower A = .ok F) :
    ∀ r ∈ F.exports, r < F.size := by
  unfold Fir.lower at h
  by_cases h1 : (Fir.Lower.residual A).isEmpty = true
  · by_cases h2 : Fir.Lower.pinsOk A = true
    · cases hfind : A.roots.find? (A.size ≤ ·) with
      | some r => simp [h1, h2, hfind, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      | none =>
        cases hfs : Fir.Lower.functions A (List.range A.size) with
        | error e => simp [h1, h2, hfind, hfs, bind, Except.bind] at h
        | ok fs =>
          simp [h1, h2, hfind, hfs, bind, Except.bind, pure, Except.pure] at h
          subst h
          intro r hm
          have := List.find?_eq_none.1 hfind r hm
          simpa using this
    · simp [h1, h2, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · simp [h1, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- The front half's exports are its Cfg functions. -/
theorem runLir_exports_lt {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f) :
    ∀ r ∈ f.cfg.exports, r < f.cfg.size := by
  obtain ⟨-, -, -, hfir, hown, hcfg, -, -⟩ := runLir_spec h
  rw [hcfg, hown]
  exact fir_exports_lt hfir

/-- **Every lowered root is an Xl SysV export of its symbol**, taking its
Cfg function's parameters, and is not `cx_init`. -/
theorem run_root {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact} (h : run cfg P c = .ok a)
    {xv : Xv.VProgram} (hs : Xv.Select.select a.lowered.program = .ok xv) (hv : Xv.Validate.run cfg.env xv c.alloc = .ok a.xl)
    {r fn : Nat} {sym : String} (hr : a.lowered.roots[r]? = some (fn, sym)) :
    ∃ xf, a.xl.funcs[fn]? = some xf ∧ xf.conv = .sysvExport sym ∧ xf.params.length = cfgParams a.cfg fn ∧
      fn ≠ a.lowered.init := by
  obtain ⟨hf, -⟩ := run_parts h
  obtain ⟨-, -, -, -, -, -, -, hlow⟩ := runLir_spec hf
  have hshape := Rt.lower_shape hlow
  have hex : fn ∈ a.cfg.exports := by
    show fn ∈ a.front.cfg.exports
    rw [← hshape.2]
    exact List.mem_map.2 ⟨_, List.mem_of_getElem? hr, rfl⟩
  have hlt := runLir_exports_lt hf fn hex
  obtain ⟨fd, F, hfd, hF, hconv, hpar⟩ := Rt.Proof.lower_root_func hlow hr hlt
  obtain ⟨xf, hxf, hc, hp⟩ := Backend.xl_func hs hv hF
  refine ⟨xf, hxf, hc.trans hconv, ?_, ?_⟩
  · rw [hp, hpar]
    show fd.params.length = ((a.cfg.fun? fn).map (·.params.length)).getD 0
    rw [show a.cfg = a.front.cfg from rfl, hfd]
    rfl
  · rw [show a.lowered.init = a.front.lowered.init from rfl, hshape.1]
    exact Nat.ne_of_lt hlt

/-- **`cx_init` is the Xl SysV export `cx_init`**, with two parameters. -/
theorem run_init {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact} (h : run cfg P c = .ok a)
    {xv : Xv.VProgram} (hs : Xv.Select.select a.lowered.program = .ok xv) (hv : Xv.Validate.run cfg.env xv c.alloc = .ok a.xl) :
    ∃ xf, a.xl.funcs[a.lowered.init]? = some xf ∧ xf.conv = .sysvExport Rt.Procs.initSymbol ∧ xf.params.length = 2 := by
  obtain ⟨hf, -⟩ := run_parts h
  obtain ⟨-, -, -, -, -, -, -, hlow⟩ := runLir_spec hf
  have hinit := Rt.lower_cxInit hlow
  rw [← (Rt.lower_shape hlow).1] at hinit
  obtain ⟨xf, hxf, hc, hp⟩ := Backend.xl_func hs hv hinit
  exact ⟨xf, hxf, hc, hp⟩

end IxCC.Recheck
