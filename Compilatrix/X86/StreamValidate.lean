import Compilatrix.X86.StreamIndexed

namespace Compilatrix.X86.Stream

/-- The compiler returns a stream only with a checked concrete certificate.
The ordinary encoder remains available for isolated encoding tests. -/
def encode (checked : Checked) : Except Error (Certified checked) := do
  let output ← (Encode.encode checked).mapError Error.encoder
  if accepted : checkIndexed checked.program output = true then
    return ⟨output, checkIndexed_sound accepted⟩
  else throw .invalidStream

end Compilatrix.X86.Stream
