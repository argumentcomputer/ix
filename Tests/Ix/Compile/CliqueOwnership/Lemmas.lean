/-
  Structural definition cliques whose equation lemmas are realised (each
  namespace's `unfold_used` uses the members' `eq_def`s), for the carried-lemma
  units of `clique-ownership` (D-M5-1, `docs/compiler-passes.md` §5.3).

  Lean's `eq_def` of a structural member unfolds it through the recursion's
  encoding: `brecOn.go`, `brecOn.eq`, the packed functional and tuple, and the
  `below` dictionary unfolded in the splitter's motive. The transport carries
  such a lemma only when no type former's group is repacked:

  * `SC1`: `od`/`ev` over `Nat` (one group of two), Lean's order not the
    canonical one: the group is repacked, the clique keeps Lean's form (`SHAPE`);
  * `SC0`: the same clique in the canonical order (unchanged);
  * `MA`: one function per type former of a mutual inductive (groups of one),
    order not canonical: transported with its `eq_def`s;
  * `MB`: as `MA`, with fixed parameters in different orders (the fixed
    parameters are reordered, nothing is repacked): transported;
  * `MC`: two functions on `TA` in a non-canonical order and one on `TB`: the
    `TA` group is repacked, Lean's form (`SHAPE`);
  * `MD`: as `MC` with the `TA` group in the canonical order but the clique's
    order not (`σ` moves `h` only): transported.
-/

namespace Tests.Ix.Compile.CliqueOwnership.Lem

namespace SC1
mutual
def od : Nat → Bool
  | 0 => false
  | n + 1 => ev n
def ev : Nat → Bool
  | 0 => true
  | n + 1 => od n
end
theorem unfold_used (n : Nat) : ev n = ev n ∧ od n = od n :=
  ⟨(ev.eq_def n).trans (ev.eq_def n).symm, (od.eq_def n).trans (od.eq_def n).symm⟩
end SC1

namespace SC0
mutual
def ev : Nat → Bool
  | 0 => true
  | n + 1 => od n
def od : Nat → Bool
  | 0 => false
  | n + 1 => ev n
end
theorem unfold_used (n : Nat) : ev n = ev n ∧ od n = od n :=
  ⟨(ev.eq_def n).trans (ev.eq_def n).symm, (od.eq_def n).trans (od.eq_def n).symm⟩
end SC0

namespace MA
mutual
inductive TA where
  | leaf : TA
  | node : TB → TA
inductive TB where
  | nil : TB
  | cons : TA → TB → TB
end
mutual
def sa : TA → Nat
  | .leaf => 1
  | .node b => sb b + 1
def sb : TB → Nat
  | .nil => 0
  | .cons a b => sa a + sb b
end
theorem unfold_used (a : TA) (b : TB) : sa a = sa a ∧ sb b = sb b :=
  ⟨(sa.eq_def a).trans (sa.eq_def a).symm, (sb.eq_def b).trans (sb.eq_def b).symm⟩
end MA

namespace MB
mutual
inductive TA where
  | leaf : TA
  | node : TB → TA
inductive TB where
  | nil : TB
  | cons : TA → TB → TB
end
mutual
def sb (y : Bool) (x : Nat) : TB → Nat
  | .nil => if y then x else 0
  | .cons a b => sa x y a + sb y x b
def sa (x : Nat) (y : Bool) : TA → Nat
  | .leaf => x + 1
  | .node b => sb y x b + 1
end
theorem unfold_used (a : TA) (b : TB) : sa 1 true a = sa 1 true a ∧ sb false 2 b = sb false 2 b :=
  ⟨(sa.eq_def 1 true a).trans (sa.eq_def 1 true a).symm,
   (sb.eq_def false 2 b).trans (sb.eq_def false 2 b).symm⟩
end MB

namespace MC
mutual
inductive TA where
  | leaf : TA
  | node : TB → TA
inductive TB where
  | nil : TB
  | cons : TA → TB → TB
end
mutual
def h : TB → Nat
  | .nil => 0
  | .cons a b => f a + g a + h b
def f : TA → Nat
  | .leaf => 1
  | .node b => h b + 1
def g : TA → Nat
  | .leaf => 2
  | .node b => h b + 2
end
theorem unfold_used (a : TA) (b : TB) : f a = f a ∧ g a = g a ∧ h b = h b :=
  ⟨(f.eq_def a).trans (f.eq_def a).symm, (g.eq_def a).trans (g.eq_def a).symm,
   (h.eq_def b).trans (h.eq_def b).symm⟩
end MC

namespace MD
mutual
inductive TA where
  | leaf : TA
  | node : TB → TA
inductive TB where
  | nil : TB
  | cons : TA → TB → TB
end
mutual
def f : TA → Nat
  | .leaf => 1
  | .node b => h b + 1
def g : TA → Nat
  | .leaf => 2
  | .node b => h b + 2
def h : TB → Nat
  | .nil => 0
  | .cons a b => f a + g a + h b
end
theorem unfold_used (a : TA) (b : TB) : f a = f a ∧ g a = g a ∧ h b = h b :=
  ⟨(f.eq_def a).trans (f.eq_def a).symm, (g.eq_def a).trans (g.eq_def a).symm,
   (h.eq_def b).trans (h.eq_def b).symm⟩
end MD

/-! `HC`: two functions with different result types (`Bool`, `Nat`), so the
group's packed motive `fun _ => PProd Bool Nat` changes when the group is
repacked: the structural memo's ownership-mode check of `clique-ownership`
(`memoByMode`). -/
namespace HC
mutual
def hb : Nat → Bool
  | 0 => false
  | n + 1 => hn n == 0
def hn : Nat → Nat
  | 0 => 1
  | n + 1 => if hb n then 1 else 2
end
end HC

end Tests.Ix.Compile.CliqueOwnership.Lem
