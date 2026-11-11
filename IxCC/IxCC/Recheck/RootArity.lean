import IxCC.Recheck.Run

/-! # A compiled root takes exactly its declared parameters

A root is called with exactly its declared number of parameters
(`docs/closures-design.md`, "Proof obligation", the decisions of 2026-11-13
and 2026-11-14): `ExactDeclared`, the end-to-end statement's input premise.
The declared count (`declaredParams`) is the number of leading binders of
the root's declared type as written (`Src.Term.pis` unfolds no definition),
the quantity `CompileClaim.rootParamsAllNat` compares, read from the source
program. The compiled count (`cfgParams`) is read off the compiled function:
the leading λs of the body the unfolding table gives the root (its kernel
value, an equation's body or a `csimp` target), which the middle end keeps.
The table is certificate data, so the compiled count is the certificate's
choice.

`checkRootArities` is the interim guard: it refuses a program where the two
counts differ for any root (`rt.arity`), and then an input of the declared
count is one of the compiled root's arity (`exactDeclared_cfg`), whatever the
certificate chose. The planned entry at the declared arity makes it
redundant once the steps after the entry are shown to keep its parameters.
`Recheck.run` does not call it.

Kernel-evaluable (D17): lists, structural recursion. -/

namespace IxCC.Recheck

/-- A source root's declared parameter count. -/
def declaredParams (src : Src.Program) (c : Src.CId) : Option Nat :=
  (src.decl? c).map fun d => d.type.pis.1.length

/-- Inputs of exactly their source root's declared parameter count. -/
def ExactDeclared (src : Src.Program) (i : Nat × List Nat) : Prop :=
  ∀ addr c, src.roots[i.1]? = some (addr, c) → ∀ n, declaredParams src c = some n → i.2.length = n

/-- One root and its compiled function (`rootsOf` pairs them by position). -/
def rootArityOk (src : Src.Program) (C : Cfg.Program) (p : (Ixon.Address × Src.CId) × Fir.FunId) : Bool :=
  declaredParams src p.1.2 == some (cfgParams C p.2)

/-- Every compiled root takes exactly its source root's declared parameter
count. -/
def rootAritiesOk (src : Src.Program) (C : Cfg.Program) : Bool :=
  src.roots.length == C.exports.length && (src.roots.zip C.exports).all (rootArityOk src C)

/-- The refusing check: `rootAritiesOk`, with a diagnostic naming the first
root whose counts differ. -/
def checkRootArities (cfg : Config) (src : Src.Program) (C : Cfg.Program) : Except Err Unit :=
  if rootAritiesOk src C then pure ()
  else
    let bad := (src.roots.zip C.exports).zipIdx.find? fun (p, _) => !rootArityOk src C p
    let message := match bad with
      | some (((_, c), f), i) =>
        let declared := match declaredParams src c with
          | some n => s!"its declared type shows {n}"
          | none => "it has no declaration"
        s!"root {(cfg.names[i]?).getD s!"root{i}"} takes {cfgParams C f} parameters, {declared}; \
          state the type with explicit arrows and give the root an equation with all its parameters"
      | none => s!"{src.roots.length} roots, {C.exports.length} compiled functions"
    .error { stage := .rt, code := "rt.arity", message }

theorem checkRootArities_ok {cfg : Config} {src : Src.Program} {C : Cfg.Program} {u : Unit}
    (h : checkRootArities cfg src C = .ok u) : rootAritiesOk src C = true := by
  unfold checkRootArities at h
  by_cases hr : rootAritiesOk src C = true
  · exact hr
  · rw [ite_eq_right hr] at h
    cases h

theorem rootAritiesOk_spec {src : Src.Program} {C : Cfg.Program} (h : rootAritiesOk src C = true)
    {i : Nat} {addr : Ixon.Address} {c : Src.CId} {f : Fir.FunId}
    (hr : src.roots[i]? = some (addr, c)) (hf : C.exports[i]? = some f) :
    declaredParams src c = some (cfgParams C f) := by
  unfold rootAritiesOk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hz : ((addr, c), f) ∈ src.roots.zip C.exports :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hr, hf⟩)
  have := h.2 _ hz
  simpa [rootArityOk] using this

/-- Every root has a compiled function. -/
theorem rootAritiesOk_length {src : Src.Program} {C : Cfg.Program} (h : rootAritiesOk src C = true) :
    src.roots.length = C.exports.length := by
  unfold rootAritiesOk at h
  rw [Bool.and_eq_true] at h
  exact beq_iff_eq.1 h.1

/-- **An input of the declared count is one of the compiled arity.** -/
theorem exactDeclared_cfg {src : Src.Program} {C : Cfg.Program} (h : rootAritiesOk src C = true)
    {i : Nat × List Nat} (hi : ExactDeclared src i) {addr : Ixon.Address} {c : Src.CId} {f : Fir.FunId}
    (hr : src.roots[i.1]? = some (addr, c)) (hf : C.exports[i.1]? = some f) :
    i.2.length = cfgParams C f :=
  hi addr c hr _ (rootAritiesOk_spec h hr hf)

end IxCC.Recheck
