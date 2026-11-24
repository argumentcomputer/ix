import Aiur.Generic.Refinement.Mirror
import IxVM.Lookup

/-! The mirrors of the TagN decoders and their callees, with their lemmas
(`Aiur.Generic.Derive.Mirrors`), derived from `IxVM.source`. This is the first mirror
module: it also declares the world `W` and the simp set of the mirror lemmas. -/

namespace IxVM.Refinement.Mirrors

/-- The TagN decoders. -/
def tagNRoots : List String :=
  ["IxonDeserialize::get_tagn0", "IxonDeserialize::get_tagn2", "IxonDeserialize::get_tagn4"]

end IxVM.Refinement.Mirrors

#ixvm_mirrors IxVM.Refinement.Mirrors.tagNRoots
