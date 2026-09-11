import Init

/- The consuming argument is deliberately not borrowed. The C driver owns
each list exactly once, clears its input slot before this call, and checks
exclusivity and cell reuse in a separate diagnostic run. -/
@[noinline]
def benchReverseOnto : List Nat → List Nat → List Nat
  | [], accumulator => accumulator
  | value :: rest, accumulator => benchReverseOnto rest (value :: accumulator)

@[noinline, export bench_lean_reverse]
def benchReverse (input : List Nat) : List Nat := benchReverseOnto input []
