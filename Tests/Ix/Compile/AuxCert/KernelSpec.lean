/-! Kernel-spec probes (Rust kernel vs Lean's C++ kernel).
H4: elimination size of a Prop inductive with a nested auxiliary (C++ counts
the nested-expanded block: Prop-only).
H6: nested occurrence under a non-inductive head (`Id (List T)`); Lean's
SizeOf generation fails on it, so it is declared with `genSizeOf` off. -/
namespace KernelSpec
inductive P : Prop
  | mk : And P P → P


set_option genSizeOf false in
inductive T
  | leaf
  | mk : Id (List T) → T
end KernelSpec
