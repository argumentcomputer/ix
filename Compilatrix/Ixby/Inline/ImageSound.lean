import Compilatrix.Ixby.Inline.Image
import Compilatrix.Ixby.Inline.Sound

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

theorem ImageOutcome.execute_forward {source protectedPrefix}
    (result : ImageOutcome source protectedPrefix)
    {input : Array Value} {fuel : Nat} {output : Value}
    (accepted : execute source.state.limits source.program input fuel = .ok output) :
    execute result.image.state.limits result.image.program input fuel = .ok output :=
  result.selected.execute_forward accepted

theorem ImageOutcome.execute_reflect {source protectedPrefix}
    (result : ImageOutcome source protectedPrefix)
    {input : Array Value} {fuel : Nat} {output : Value}
    (accepted : execute result.image.state.limits result.image.program input fuel = .ok output) :
    execute (extraStack source.state.limits) source.program input (4 * fuel) = .ok output :=
  result.selected.execute_reflect accepted

end Compilatrix.Ixby.Inline
