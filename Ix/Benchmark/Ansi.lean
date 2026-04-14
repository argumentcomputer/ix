module

public section

/-!
# ANSI terminal styling for benchmark output

Provides colored/bold/faint text and ephemeral (overwritable) progress lines,
matching criterion.rs's `CliReport` output style. ANSI colors are always
enabled (Lake handles terminal capability detection). Ephemeral overwriting
is disabled in verbose mode so all output is permanent.
-/

namespace Ansi

def esc := "\x1B"
def reset := s!"{esc}[0m"

def bold (s : String) : String := s!"{esc}[1m{s}{reset}"
/-- Dim text via a neutral gray from the 256-color grayscale ramp (index 240). -/
def faint (s : String) : String := s!"{esc}[38;5;240m{s}{reset}"

/-- DarkGreen foreground (ANSI 256-color index 2) -/
def green (s : String) : String := s!"{esc}[38;5;2m{s}{reset}"
/-- DarkRed foreground (ANSI 256-color index 1) -/
def red (s : String) : String := s!"{esc}[38;5;1m{s}{reset}"
/-- DarkYellow foreground (ANSI 256-color index 3) -/
def yellow (s : String) : String := s!"{esc}[38;5;3m{s}{reset}"

/-- Carriage-return + clear-entire-line, used to erase ephemeral progress. -/
def clearLine := s!"\r{esc}[2K"

end Ansi

/-- Controls ephemeral progress line overwriting. ANSI colors are always on. -/
structure CliStyle where
  overwriteEnabled : Bool

namespace CliStyle

/-- Erase the current ephemeral line on stderr. No-op if overwrite is disabled. -/
def overwrite (s : CliStyle) : IO Unit := do
  if s.overwriteEnabled then
    IO.eprint Ansi.clearLine

/-- Print an ephemeral progress message to stderr. If overwrite is enabled,
    the line has no trailing newline and can be overwritten by the next call.
    Otherwise falls back to a normal `eprintln`. -/
def printEphemeral (s : CliStyle) (msg : String) : IO Unit := do
  if s.overwriteEnabled then
    IO.eprint s!"\r{Ansi.clearLine}{msg}"
    (← IO.getStderr).flush
  else
    IO.eprintln msg

end CliStyle

end
