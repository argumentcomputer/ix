import Ix.CompileCert.Opt.ShapeWF

/-!
# Telescope and argument ranges of a closed image

`stripLams_er` identifies the erased lambda telescope. `stripLams_arg_range` derives the loose
variable bound on each body argument from the original image's closedness. The shape reader
does not check that bound for every recorded minor term; its eventual image specification
must supply closedness from image construction. No such construction theorem is assumed here
without being an explicit premise of the corresponding range lemma.
-/

namespace Ix.CompileCert.Opt

open Ix (Expr)
open Ix.CompileCert.Conv
open Ix.Compile.Pass.Opt

/-- Stripping a successful lambda telescope exposes exactly that telescope after erasure. -/
theorem stripLams_er {n : Nat} {value body : Expr} (h : stripLams n value = some body) :
    ∃ ts, ts.length = n ∧ er value = lamN ts (er body) := by
  induction n generalizing value with
  | zero =>
    simp only [stripLams, Option.some.injEq] at h
    cases h
    exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    cases value <;> try (cases h)
    rename_i _name dom rest _bi _hash
    obtain ⟨ts, hlen, her⟩ := ih h
    exact ⟨er dom :: ts, by simp only [List.length_cons, hlen], by simp only [er, lamN, her]⟩

/-- The body's loose-variable range is bounded by that of the enclosing lambda telescope plus
its length. This uses no typing or hash assumption. -/
theorem lamN_body_range (ts : List Tm) (body : Tm) :
    body.range ≤ (lamN ts body).range + ts.length := by
  induction ts with
  | nil => simp only [lamN, List.length_nil, Nat.add_zero, Nat.le_refl]
  | cons t ts ih =>
    simp only [lamN, Tm.range, List.length_cons]
    have h := Nat.le_max_right t.range ((lamN ts body).range - 1)
    omega

theorem appN_head_range (f : Tm) (args : List Tm) :
    f.range ≤ (Tm.appN f args).range := by
  induction args generalizing f with
  | nil => exact Nat.le_refl _
  | cons a args ih =>
    exact Nat.le_trans (Nat.le_max_left f.range a.range) (ih (.app f a))

theorem appN_arg_range {f a : Tm} {args : List Tm} (ha : a ∈ args) :
    a.range ≤ (Tm.appN f args).range := by
  induction args generalizing f with
  | nil => cases ha
  | cons b args ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Nat.le_trans (Nat.le_max_right f.range a.range) (appN_head_range (.app f a) args)
    · exact ih ha

/-- Closedness of the original image supplies the bound that a shape-reader minor slot does
not check on its own. -/
theorem stripLams_arg_range {n : Nat} {value body a : Expr}
    (h : stripLams n value = some body) (hc : (er value).range = 0)
    (ha : a ∈ (Ix.Compile.Canon.getAppFnArgs body).2.toList) : (er a).range ≤ n := by
  obtain ⟨ts, hlen, her⟩ := stripLams_er h
  have hb := lamN_body_range ts (er body)
  rw [← her, hc, Nat.zero_add, hlen] at hb
  have ha' : er a ∈ (Ix.Compile.Canon.getAppFnArgs body).2.toList.map er :=
    List.mem_map_of_mem ha
  have hr := appN_arg_range (f := er (Ix.Compile.Canon.getAppFnArgs body).1) ha'
  rw [← er_getAppFnArgs] at hr
  exact Nat.le_trans hr hb

end Ix.CompileCert.Opt
