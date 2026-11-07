import IxCC.Recheck.Rc.Replay

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay


def Artifact.bytes (artifact : Artifact) : List UInt8 := artifact.backend.object.data.toList

end IxCC.Recheck.RcReplay
