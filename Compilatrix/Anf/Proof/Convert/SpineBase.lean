import Compilatrix.Anf.Proof.Convert.Groups

/-! # ANF conversion: facts for spines

Lam spines rebuilt from their head and arguments, `covered` and the kinds a
global's telescope expects, grouped argument order under a bind, and Lam's
value of a global (P1, M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Convert.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Lam (Kind Mode argSlot applyArgs)
open Compilatrix.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec sigsOf)
open Compilatrix.Ixon

theorem spine_go_apps : ∀ (t : Lam.Term) (acc : List (Lam.Term × Mode)),
    Lam.Term.apps (Lam.Term.spine.go t acc).1 (Lam.Term.spine.go t acc).2 = Lam.Term.apps t acc
  | .app f a m, acc => by
    rw [Lam.Term.spine.go, spine_go_apps f]
    rfl
  | .var _, _ | .glob _, _ | .lam .., _ | .letE .., _ | .con .., _ | .case .., _ | .proj .., _
  | .lit _, _ | .prim .., _ | .tick _, _ | .box, _ | .trap, _ => rfl

theorem spine_apps (t : Lam.Term) : Lam.Term.apps t.spine.1 t.spine.2 = t :=
  spine_go_apps t []

theorem spine_go_ne : ∀ (t : Lam.Term) (acc : List (Lam.Term × Mode)), acc ≠ [] →
    (Lam.Term.spine.go t acc).2 ≠ []
  | .app f a m, acc, _ => by
    rw [Lam.Term.spine.go]; exact spine_go_ne f _ (List.cons_ne_nil _ _)
  | .var _, _, h | .glob _, _, h | .lam .., _, h | .letE .., _, h | .con .., _, h | .case .., _, h
  | .proj .., _, h | .lit _, _, h | .prim .., _, h | .tick _, _, h | .box, _, h | .trap, _, h => h

theorem spine_app_ne (f a : Lam.Term) (m : Mode) : (Lam.Term.app f a m).spine.2 ≠ [] := by
  unfold Lam.Term.spine
  rw [Lam.Term.spine.go]
  exact spine_go_ne f _ (List.cons_ne_nil _ _)

/-- `covered`: every `name` position is among the arguments. -/
theorem covered_spec {ms : List Mode} {n : Nat} (h : covered ms n = true) :
    ∀ p, ms.getD p .strict = .name → p < n := by
  intro p hp
  unfold covered at h
  rw [List.all_eq_true] at h
  rcases Nat.lt_or_ge p ms.length with hl | hl
  · have hm : ms[p] = .name := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at hp; exact hp
    have := h (ms[p], p) (by
      rw [List.mem_iff_getElem?]
      exact ⟨p, by simp [List.getElem?_zipIdx, hl]⟩)
    simp [hm] at this
    exact this
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at hp; cases hp

/-- A global's telescope kinds are exactly the kinds its spines expect. -/
theorem compat_glob {ps : List (Mode × V3.BinderContract)} {kinds : List Kind}
    (hma : ModesAgree ps kinds) : Compat (ps.map (·.1)) (sigsOf kinds) kinds := by
  intro p
  left
  unfold expKind
  rcases Nat.lt_or_ge p ps.length with hp | hp
  · have hk : p < kinds.length := by rw [← hma.1]; exact hp
    have hagree := hma.2 p ps[p] kinds[p] (List.getElem?_eq_getElem hp) (List.getElem?_eq_getElem hk)
    rw [List.getD_eq_getElem?_getD (l := ps.map (·.1)), List.getElem?_map, List.getElem?_eq_getElem hp,
      Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD (l := kinds),
      List.getElem?_eq_getElem hk, Option.getD_some]
    cases hm : ps[p].1 with
    | strict =>
      rw [hm] at hagree
      cases hq : kinds[p] with
      | strict => rfl
      | name s => rw [hq] at hagree; cases hagree
    | name =>
      rw [hm] at hagree
      simp only [if_true]
      cases hq : kinds[p] with
      | strict => rw [hq] at hagree; cases hagree
      | name s =>
        simp [sigsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk, hq]
  · have hk : kinds.length ≤ p := by rw [← hma.1]; exact hp
    rw [List.getD_eq_getElem?_getD (l := ps.map (·.1)), List.getElem?_eq_none (by simpa using hp),
      List.getD_eq_getElem?_getD (l := kinds), List.getElem?_eq_none hk]
    rfl

theorem lamArgs_bind (L : Lam.Program) (k : Nat) (ρ : Lam.Env) (F : Lam.Val → Result Lam.Val) :
    ∀ (args : List (Lam.Term × Mode)) (C : List Lam.Slot → Nat → Result Lam.Val),
      (lamArgs L k ρ args C).bind F = lamArgs L k ρ args fun ss k => (C ss k).bind F
  | [], C => rfl
  | a :: rest, C => by
    rw [lamArgs_cons, lamArgs_cons, Result.bind_assoc]
    exact Result.bind_congr _ fun s => lamArgs_bind L k ρ F rest _

theorem lamArgs_congr_len (L : Lam.Program) (k : Nat) (ρ : Lam.Env) :
    ∀ (args : List (Lam.Term × Mode)) {C C' : List Lam.Slot → Nat → Result Lam.Val},
      (∀ ss, ss.length = args.length → C ss k = C' ss k) →
      lamArgs L k ρ args C = lamArgs L k ρ args C'
  | [], _, _, h => h [] rfl
  | _ :: rest, _, _, h => Result.bind_congr _ fun s =>
      lamArgs_congr_len L k ρ rest fun ss hs => h (s :: ss) (by simp [hs])

theorem later_congr {α : Type} (k : Nat) {f g : Nat → Result α} (h : ∀ j, f j = g j) :
    later k f = later k g := by
  rw [funext h]

/-- A function global's Lam value: one charge, then its closure. -/
theorem lam_eval_glob_fun (L : Lam.Program) {g : Lam.GlobalId} {gl : Lam.Global}
    (hg : L.global? g = some gl) {p : Mode × V3.BinderContract} {ps : List (Mode × V3.BinderContract)}
    {body : Lam.Term} (hb : gl.body = lamsWith (p :: ps) body) (k : Nat) (ρ : Lam.Env) :
    Lam.eval L k ρ (.glob g) = later k fun _ => .ok (.clos [] (lamsWith ps body)) := by
  rw [Lam.eval_glob, hg]
  cases k with
  | zero => rfl
  | succ k => simp only [later_succ]; rw [hb]; exact eval_lamsWith_cons L k [] p ps body

theorem lam_eval_glob (L : Lam.Program) {g : Lam.GlobalId} {gl : Lam.Global}
    (hg : L.global? g = some gl) (k : Nat) (ρ : Lam.Env) :
    Lam.eval L k ρ (.glob g) = later k fun k => Lam.eval L k [] gl.body := by
  rw [Lam.eval_glob, hg]; cases k <;> rfl

end Compilatrix.Anf.Convert.Proof
