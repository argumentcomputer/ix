import Compilatrix.Recheck.Rc.Replay

set_option autoImplicit false
namespace Compilatrix.Recheck.RcReplay


def Artifact.bytes (artifact : Artifact) : List UInt8 := artifact.backend.object.data.toList

end Compilatrix.Recheck.RcReplay
