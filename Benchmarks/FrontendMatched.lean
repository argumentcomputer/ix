import Benchmarks.FrontendMatchedData

/-! Matched workload: authenticate source bytes, run the unchanged upstream
parser/elaborator with prelude seeding, and compare EVERY resulting constant
against an alpha-canonical expected payload. Raw Aiur implements this same
output contract for the representative language subset. Neither path invokes
the separate addressed kernel/resource checker. Elaboration checks source
terms; the complete output comparison additionally covers all generated types,
bodies, declaration flags and recursor reduction rules.
-/
namespace FrontendMatched

def checkOutput (src : String) : Bool :=
  match FrontendRepresentative.elaborate src with
  | .error _ => false
  | .ok env => FrontendWire.ofEnv env == FrontendMatchedData.expected

def check (src : String) (digest : Address) : Bool :=
  Address.admissionHash src.toUTF8 == digest && checkOutput src

-- The expected digest is a literal, generated from the fixture, rather than a
-- second invocation of the hash computation inside the benchmark statement.
def input : Bool := check FrontendRepresentative.sourceText FrontendMatchedData.sourceDigest

end FrontendMatched
