import CompilatrixTests.Runtime

/-! Compatibility entry point for the complete compiled regression suite. -/

def main : IO UInt32 := CompilatrixTests.runAll
