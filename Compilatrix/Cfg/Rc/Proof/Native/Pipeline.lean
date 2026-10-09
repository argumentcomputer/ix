import Compilatrix.Cfg.Rc.Native
import Compilatrix.Cfg.Rc.Proof.PublicApi
import Compilatrix.Rt.Proof.Program

/-! Read actual native admission off without changing its execution. Runtime
procedure proofs apply to the concrete program before the final edge split;
the split is explicit here and must be composed using Lir's relabelling proof. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec

def layoutOf (P : Program) : Layout :=
  ⟨P.base.size, P.base.ctors.filter (fun c => c.arity > 0)⟩

def consumeAll (P : Program) : Except String (List (Nat × Cfg.Fun)) :=
  (List.range P.base.size).mapM fun f => do
    let some fd := P.base.fun? f | throw "missing admitted source function"
    let lowered ← consumeFunction P (layoutOf P) fd
    pure (f, lowered)

def consumed (P : Program) (pairs : List (Nat × Cfg.Fun)) : Cfg.Program :=
  { P.base with funs := Src.NatMap.ofList pairs }

def rootsOf (config : Rt.Config) (P : Program) : List (Nat × String) :=
  let named := P.base.exports.zipIdx.map fun (f, i) =>
    (f, Rt.Lower.symbolOf ((config.names[i]?).getD s!"root{i}"))
  named.map fun (f, symbol) => (f, (named.lookup f).getD symbol)

def tablesOf (P : Program) (pairs : List (Nat × Cfg.Fun)) : Rt.Lower.Tables :=
  { Rt.Lower.tables (consumed P pairs) with
    natPow := (layoutOf P).init + 1, natGcd := (layoutOf P).init + 2 }

def wrappers (l : Layout) : List Lir.Func :=
  [incrementWrapper l.incProc, decrementWrapper l.decProc] ++
    l.ctors.zipIdx.map (fun (c, i) => allocationWrapper (l.allocProc i) c.arity)

def procedures (l : Layout) : List Lir.Func :=
  [Rt.Rc.Procs.inc, Rt.Rc.Procs.dec] ++
    l.ctors.map (fun c => Rt.Rc.Procs.alloc c.arity c.tag)

def rawProgram (l : Layout) (funcs : List Lir.Func) (main : Nat) : Lir.Program :=
  { funcs := (funcs ++ wrappers l ++ procedures l ++
      [Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd]).toArray
    main }

theorem lower_parts {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Rt.Lowered}
    (accepted : Native.lower config F bodies P = .ok lowered) :
    ∃ main pairs funcs,
      checkProgram F bodies P = true ∧
      Rt.checkSwitches P.base = .ok () ∧
      P.base.exports.head? = some main ∧
      (layoutOf P).ctors.all (fun c => decide (c.arity ≤ 31 ∧ c.tag ≤ Rt.maxTag)) = true ∧
      consumeAll P = .ok pairs ∧
      Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
        (List.range P.base.size) = .ok funcs ∧
      funcs.length = P.base.size ∧
      lowered.program = (rawProgram (layoutOf P) funcs main).splitCriticalEdges ∧
      lowered.init = (layoutOf P).init ∧
      lowered.natPow = (layoutOf P).init + 1 ∧
      lowered.natGcd = (layoutOf P).init + 2 ∧
      lowered.roots = rootsOf config P ∧ lowered.program.check = .ok () := by
  change ((do
    unless checkProgram F bodies P do throw "unchecked RC Cfg candidate"
    (Rt.checkSwitches P.base).mapError Rt.SwitchError.render
    let some main := P.base.exports.head? | throw "no exports"
    unless (layoutOf P).ctors.all (fun c => decide (c.arity ≤ 31 ∧ c.tag ≤ Rt.maxTag)) do
      throw "constructor table exceeds first RC layout fragment"
    let pairs ← consumeAll P
    let funcs ← (Rt.Lower.functions (tablesOf P pairs) (consumed P pairs)
      (rootsOf config P) (List.range P.base.size)).mapError Rt.Error.render
    let program := (rawProgram (layoutOf P) funcs main).splitCriticalEdges
    program.check
    return {
      program, init := (layoutOf P).init, natPow := (layoutOf P).init + 1
      natGcd := (layoutOf P).init + 2, roots := rootsOf config P }) : Except String Rt.Lowered) = .ok lowered at accepted
  cases hc : checkProgram F bodies P with
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind] at accepted
    cases accepted
  | true =>
    simp only [hc, Bool.true_eq_false, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
    cases hs : Rt.checkSwitches P.base with
    | error e => rw [hs] at accepted; cases accepted
    | ok u =>
      cases u
      simp only [hs, Except.mapError, bind, Except.bind] at accepted
      cases hm : P.base.exports.head? with
      | none => rw [hm] at accepted; cases accepted
      | some main =>
        simp only [hm] at accepted
        cases hl : (layoutOf P).ctors.all (fun c => decide (c.arity ≤ 31 ∧ c.tag ≤ Rt.maxTag)) with
        | false =>
          simp only [hl, Bool.false_eq_true, ↓reduceIte, throw, throwThe,
            MonadExceptOf.throw, bind, Except.bind] at accepted
          cases accepted
        | true =>
          simp only [hl, Bool.true_eq_false, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
          cases hp : consumeAll P with
          | error e => rw [hp] at accepted; cases accepted
          | ok pairs =>
            simp only [hp, bind, Except.bind] at accepted
            cases hf : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs)
                (rootsOf config P) (List.range P.base.size) with
            | error e => rw [hf] at accepted; cases accepted
            | ok funcs =>
              simp only [hf, Except.mapError, bind, Except.bind] at accepted
              cases hcheck : (rawProgram (layoutOf P) funcs main).splitCriticalEdges.check with
              | error e => rw [hcheck] at accepted; cases accepted
              | ok u =>
                cases u
                simp only [hcheck, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
                subst lowered
                exact ⟨main, pairs, funcs, rfl, rfl, rfl, rfl, rfl, hf,
                  by simpa using (Rt.Proof.functions_spec hf).1, rfl, rfl, rfl, rfl, rfl, hcheck⟩


end Compilatrix.Cfg.Rc.Native.Spec
