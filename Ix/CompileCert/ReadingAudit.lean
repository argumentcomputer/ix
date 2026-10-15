import Ix.CompileCert.UniverseAudit
import Ix.CompileCert.CacheSound

/-! # Audit of the reading-chain proofs

Every theorem of the reading chain's shared layers that a later proof uses
is a root here: the run layer (`Ix.CompileCert.RawRun`, beyond the universe
proofs' part, which `Ix.CompileCert.UniverseAudit` audits) and the memo
invariant (`Ix.CompileCert.CacheSound`). Each root must exist, occur once,
and depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`
(`Ix.CompileCert.UniverseAudit.checkRoots`, through the certified kernel's
traversal `Ix.Kernel.Audit.collectCached`, so `sorryAx` fails it). -/

namespace Ix.CompileCert.ReadingAudit

/-- The run equations, bind inversions, frame combinators and success-only
triples. -/
def runRoots : Array Lean.Name :=
  #[`rawRun_throw, `rawRun_modifyGet, `rawRun_withBlockEnv, `rawRun_applyBlockState,
    `run_eq_rawRun, `run_success, `bind_ok, `bind_success,
    `Preserves.readCompile, `Preserves.modifyGet, `Preserves.map, `Preserves.withBlockEnv,
    `Preserves.mapM_list, `Preserves.mapM_array, `Preserves.forIn'_list, `Preserves.forIn'_array,
    `Preserves.forIn_list, `Preserves.forIn_array, `Preserves.of_ok,
    `Triple.pure, `Triple.throw, `Triple.bind, `Triple.consequence, `Triple.map, `Triple.get,
    `Triple.readBlock, `Triple.readCompile, `Triple.modify, `Triple.modifyGet,
    `Triple.withBlockEnv, `Triple.forIn_list, `Triple.forIn_array].map (`Ix.CompileCert ++ ·)

/-- The memo invariant. -/
def cacheRoots : Array Lean.Name :=
  #[`CacheSound.empty, `CacheSound.mono, `CacheSound.insert_of_respects,
    `CacheSound.insert].map (`Ix.CompileCert ++ ·)

end Ix.CompileCert.ReadingAudit

open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd checkRoots (tag := "reading-audit") "run layer" Ix.CompileCert.ReadingAudit.runRoots
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd checkRoots (tag := "reading-audit") "memo invariant" Ix.CompileCert.ReadingAudit.cacheRoots
