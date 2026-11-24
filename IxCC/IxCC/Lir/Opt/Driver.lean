import IxCC.Lir.Opt.Check
import IxCC.Lir.Opt.Gvn
import IxCC.Lir.Opt.Licm
import IxCC.Lir.WellFormed

/-!
# Validated Lir SSA optimizer driver (`Lir.Opt.run` & `Lir.Opt.validateCert`)

Combines the untrusted optimization passes (`gvnFunc → licmFunc → gvnFunc`) with
the formally verified translation validator (`Lir.Opt.check`) and well-formedness
checks (`Lir.Program.wellFormed`):

- `optimizeFunc` / `optimize`: untrusted optimizer pipeline.
- `run`: per-function validated optimizer with global `check p cand` gate,
  guaranteeing both semantic refinement (`run_sim`, `run_refines`) and
  preservation of `Lir.WellFormed` (`run_wellFormed`).
- `validateCert`: validates an externally supplied optimized `Lir.Program`
  certificate against `p`.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (Func Program)

/-- Untrusted optimization pipeline on a single function:
1. GVN/CSE + algebraic simplification + div strength reduction + branch/brOvf fold +
   forwarding/load CSE + DSE + DCE + prune unreachable.
2. Natural-loop LICM + invariant block parameter substitution + invariant `.fail` guard hoisting.
3. Second GVN + DSE + DCE + prune pass to clean up hoisted code and newly folded checks. -/
def optimizeFunc (F : Func) : Func :=
  let F1 := gvnFunc F
  let F2 := licmFunc F1
  gvnFunc F2

/-- Untrusted optimization pipeline on a whole program. -/
def optimize (p : Program) : Program :=
  { p with funcs := p.funcs.map optimizeFunc }

/-- Validated per-function optimization: optimizes each function independently,
keeping the optimized function only if it passes `checkFuncWithPlan` and well-formedness,
and gates the final program with `check p cand` (plus `cand.wellFormed` whenever `p` is
well-formed). -/
def run (p : Program) : Program :=
  let candFuncs := (List.range p.funcs.size).toArray.map fun fi =>
    match p.funcs[fi]? with
    | none => default
    | some F =>
        let G := optimizeFunc F
        if checkFuncWithPlan F G (inferFuncPlan F G) &&
           (G.checkShape p fi).toBool && (G.checkSsa fi).toBool then G
        else F
  let cand : Program := { p with funcs := candFuncs }
  if check p cand && (!p.wellFormed || cand.wellFormed) then cand else p

/-- Validate an externally supplied optimized `Lir.Program` certificate `cert`
against source program `p`, requiring both semantic equivalence (`check p cert`)
and `cert.wellFormed`. -/
def validateCert (p cert : Program) : Except String Program :=
  if !check p cert then
    .error "lir.opt: translation validator rejected optimized program"
  else
    match cert.check with
    | .error msg => .error s!"lir.opt: optimized program not well-formed: {msg}"
    | .ok () => .ok cert

end IxCC.Lir.Opt
