import Benchmarks.Compiler.Schedule

namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def optionalFile (path : FilePath) : IO String := do
  try return (← IO.FS.readFile path).trimAscii.toString
  catch _ => return "unavailable"

def firstCore : IO Nat := do
  let status ← IO.FS.readFile "/proc/self/status"
  let some line := (status.splitOn "\n").find? (·.startsWith "Cpus_allowed_list:") |
    throw (IO.userError "Linux CPU affinity list unavailable")
  let list := (line.drop "Cpus_allowed_list:".length).toString.trimAscii.toString
  present (((list.splitOn ",").head!).splitOn "-").head!.toNat? "invalid Linux CPU affinity list"

def environment (core : Nat) : IO Json := do
  let cpu := s!"/sys/devices/system/cpu/cpu{core}"
  let mut stable := #[]
  for path in ["/proc/sys/kernel/random/boot_id", "/sys/devices/system/cpu/online",
      "/sys/devices/system/cpu/smt/active", "/sys/devices/system/cpu/cpufreq/boost",
      "/sys/devices/system/cpu/intel_pstate/no_turbo", "/sys/devices/system/clocksource/clocksource0/current_clocksource",
      s!"{cpu}/topology/thread_siblings_list", s!"{cpu}/topology/core_id", s!"{cpu}/topology/physical_package_id",
      s!"{cpu}/cpufreq/scaling_governor", s!"{cpu}/cpufreq/scaling_driver",
      s!"{cpu}/cpufreq/cpuinfo_min_freq", s!"{cpu}/cpufreq/cpuinfo_max_freq", s!"{cpu}/microcode/version"] do
    stable := stable.push (path, toJson (← optionalFile path))
  let kernel ← run "uname" #["-srvmo"]
  stable := stable.push ("kernel", toJson kernel.trimAscii.toString)
  let cpuinfo ← IO.FS.readFile "/proc/cpuinfo"
  let first := (cpuinfo.splitOn "\n\n").head!
  let identity := (first.splitOn "\n").filter fun line =>
    ["vendor_id", "cpu family", "model\t", "model name", "stepping", "microcode", "flags"].any (fun startText => line.startsWith startText)
  stable := stable.push ("cpu_identity", toJson identity)
  let topology ← run "lscpu" #["--json"]
  let placement ← IO.Process.output { cmd := "taskset", args := #["--cpu-list", toString core, "sh", "-c", "cat /proc/self/status"] }
  need (placement.exitCode == 0) "requested benchmark core is unavailable"
  let affinity := (placement.stdout.splitOn "\n").filter fun line =>
    ["Cpus_allowed_list:", "Mems_allowed_list:"].any (fun startText => line.startsWith startText)
  stable := stable.push ("placed_affinity_and_numa_nodes", toJson affinity)
  let controller ← IO.FS.readFile "/proc/self/status"
  stable := stable.push ("controller_affinity_and_numa_nodes", toJson ((controller.splitOn "\n").filter fun line =>
    ["Cpus_allowed_list:", "Mems_allowed_list:"].any (fun startText => line.startsWith startText)))
  let stableFields := Json.mkObj stable.toList
  let mut dynamic := #[]
  for path in ["/proc/loadavg", "/proc/meminfo", "/proc/pressure/cpu", "/proc/pressure/memory",
      s!"{cpu}/cpufreq/scaling_cur_freq", "/proc/sys/kernel/perf_event_paranoid", "/proc/sys/kernel/nmi_watchdog",
      "/proc/1/cgroup", "/etc/os-release"] do
    dynamic := dynamic.push (path, toJson (← optionalFile path))
  let mut variables := #[]
  for name in ["CML_HEAP_SIZE", "CML_STACK_SIZE", "MALLOC_ARENA_MAX", "MALLOC_PERTURB_", "LD_PRELOAD", "LD_LIBRARY_PATH",
      "LEAN_NUM_THREADS", "OMP_NUM_THREADS", "NIX_CFLAGS_COMPILE", "NIX_LDFLAGS"] do
    variables := variables.push (name, toJson (← IO.getEnv name))
  return Json.mkObj [
    ("format", toJson "compilatrix/benchmark-environment/1"), ("utc", toJson (← run "date" #["-u", "+%Y-%m-%dT%H:%M:%SZ"]).trimAscii.toString),
    ("core", toJson core), ("stable", stableFields), ("stable_blake3", toJson (digest stableFields.compress.toUTF8)),
    ("lscpu", ← checked (Json.parse topology)), ("observations", Json.mkObj dynamic.toList),
    ("environment_variables", Json.mkObj variables.toList), ("runtime_overrides", toJson runtimeEnv),
    ("limitations", toJson (["shared host; other tenants and SMT sibling are not controlled",
      "worker affinity is pinned; NUMA follows Linux first-touch placement on the pinned worker",
      "turbo, governor, system services, thermal state, and ambient load are observed, not administratively changed",
      "this run is not a dedicated performance-regression baseline"] : List String))]

def stableEnvironment (before after : Json) : IO Bool := do
  pure ((← field before "stable") == (← field after "stable") &&
    (← field before "environment_variables") == (← field after "environment_variables"))

def environmentRegressions (original : Json) : IO Unit := do
  let changed ← replaceAt original ["stable", "kernel"] (toJson "different kernel")
  need (!(← stableEnvironment original changed)) "environment drift was not detected"

end Benchmarks.Compiler
