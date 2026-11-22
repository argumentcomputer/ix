module

/-! The committed pins of the certified formal Aiur programs,
`tools/formal-aiur.keys`, embedded when this module is built. The module is
the only one of the `FormalAiurKeys` library, whose `needs` names the pin
file, so Lake rebuilds it, and everything importing it, whenever the file
changes. `Ix.Cli.FormalKeys` parses and checks the pins. -/

public section
namespace Ix.FormalAiurKeys

/-- The text of `tools/formal-aiur.keys`. -/
def text : String := include_str "tools/formal-aiur.keys"

end Ix.FormalAiurKeys
