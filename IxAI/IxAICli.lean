import IxAICli.Trajectory
import IxAICli.Formats
import IxAICli.RL
import IxAICli.Codegen
import IxAICli.Mines
import IxAICli.Reward
import IxAICli.Package
import IxAICli.Bench

/-!
# The commands of `ixai`

One module per concern; `Ixai.lean` only dispatches. Flag parsing, route printing and the
trajectory check are shared with `ixai-verify` (`IxAIVerify.Cli`).
-/
