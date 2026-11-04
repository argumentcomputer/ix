import Ix.KernelDisplay.Render

/-! # The display-only read (IxC step 6b): the one `unsafe` of the step

A display annotation (a binder's or a let's Lean name, a failure's terms and
binders) is held in a `Squash`, so that it is a subsingleton: every statement,
equation and decision of the checker is blind to it, and no proof moves. The
same property makes it unreadable by safe code. Printing a name needs its
value, so this module reads it with `unsafeCast` (a `Squash` is represented by
its value at run time).

**Trust surface.** This is the one `unsafe` entry 6b adds, allowlisted in the
trust-surface fence (`Tests/Ix/Kernel/TrustSurface.lean`) with this reason:
*display only; outside the certified closure; `.meta` never decides.*

* It is outside `IxC.Kernel` and outside every certified closure: the kernel,
  the reader and the certified entries never import it, and the runtime
  closures of their roots (`IxC/Kernel/Audit/Roots.lean`, `Ix.Cert`'s runtime
  audit) do not reach it.
* A verdict never depends on it: the `.meta` checker reaches `.anon`'s
  verdicts (the erasure test), the CLI's verdict is the `.anon` run's, and a
  read value goes only into a printed message.
* Its callers are `unsafe` too, as Lean requires (no `implemented_by`): the
  entry points that print with names (`kernel-check-ixe --meta`, the
  `kernel-meta-names` oracle). The renderer itself (`Ix.KernelDisplay.Render`)
  is safe code that takes the read as a parameter (`Peek`), and this module
  holds nothing else. `Tests.Ix.Kernel.DisplayRead` checks that the runtime
  closures of the certified roots do not reach `peekSquash`. -/

namespace Ix.KernelDisplay

/-- **Read a display annotation's value** (display only; see the module
docstring). -/
@[noinline] unsafe def peekSquash {α : Type} (s : Squash α) : α := unsafeCast s

/-- The display reads, for the renderer. -/
unsafe def peekAll : Peek where
  binder := peekSquash
  letName := peekSquash
  failure := peekSquash

end Ix.KernelDisplay
