import Compilatrix.Anf.Proof.Walk.App

/-! # The rewriting walk: the simulation at every bound

The walk's simulation (`WalkAt`) at every fuel, by induction on the fuel
inside a strong induction on the clock bound: one fuel level from the one
below and the bound below (`walkAt_succ`); with it, the fundamental lemma
and the program interface at every bound (`levels`), and refinement of a
program by one whose globals are walks of its globals (`refines`) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable {P Q : Program} {Valid : Cfg → List Val → List Val → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg} {n : Nat}

theorem walkBind_step {fuel : Nat} (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg}
    {env : Walk.Env} {here : Here} {c : Ixon.V3.LetContract} {b : Bind} {body : Exp} {k : Kont} {out : Exp}
    {s s' : Fires} (h : (Walk.walkBind C (fuel + 1) env here c b body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.bind c b body) := by
  cases b with
  | atom a => exact walkBind_atom hctx hW h
  | con cc as => exact walkBind_con hctx hW h
  | proj cc i x => exact walkBind_proj hctx hW h
  | prim p as => exact walkBind_prim hctx hW h
  | glob g => exact walkBind_glob hctx hW h
  | call g as => exact walkBind_call hctx hW h
  | app f as => exact walkBind_app hctx hW h
  | fn ps fb => exact walkBind_fn hctx hW h

theorem walkAt_zero : WalkAt P Q Valid Xc n 0 where
  walk _ _ _ _ _ _ _ _ h := by rw [Walk.walk] at h; exact absurd h (fun h => Walk.run_throw_ok h)
  after _ _ _ _ _ _ _ h := by rw [Walk.after] at h; exact absurd h (fun h => Walk.run_throw_ok h)
  walkBind _ _ _ _ _ _ _ _ _ _ h := by rw [Walk.walkBind] at h; exact absurd h (fun h => Walk.run_throw_ok h)
  walkJoin _ _ _ _ _ _ _ _ _ _ _ h := by rw [Walk.walkJoin] at h; exact absurd h (fun h => Walk.run_throw_ok h)
  walkJump _ _ _ _ _ _ _ _ _ h := by rw [Walk.walkJump] at h; exact absurd h (fun h => Walk.run_throw_ok h)
  walkCase _ _ _ _ _ _ _ _ _ _ h := by rw [Walk.walkCase] at h; exact absurd h (fun h => Walk.run_throw_ok h)
  walkAlts _ _ _ _ _ _ _ _ _ h := by
    rw [Walk.walkAlts.eq_1] at h; exact absurd h (fun h => Walk.run_throw_ok h)

theorem walkAt_succ {fuel : Nat} (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel)
    (hlow : ∀ m < n, WalkAt P Q Valid Xc m fuel) : WalkAt P Q Valid Xc n (fuel + 1) where
  walk _ _ _ _ _ _ _ _ h := walk_step hW h
  after _ _ _ _ _ _ _ h := after_step hctx hW h
  walkBind _ _ _ _ _ _ _ _ _ _ h := walkBind_step hctx hW h
  walkJoin _ _ _ _ _ _ _ _ _ _ _ h := walkJoin_step hctx hW hlow h
  walkJump _ _ _ _ _ _ _ _ _ h := walkJump_step hctx hW h
  walkCase _ _ _ _ _ _ _ _ _ _ h := walkCase_step hctx hW h
  walkAlts _ _ _ _ _ _ _ _ _ h := walkAlts_step hctx hW h

theorem walkAt_all (hctx : Ctx P Q Valid Xc n) (hlow : ∀ m < n, ∀ fuel, WalkAt P Q Valid Xc m fuel) :
    ∀ fuel, WalkAt P Q Valid Xc n fuel
  | 0 => walkAt_zero
  | fuel + 1 => walkAt_succ hctx (walkAt_all hctx hlow fuel) fun m hm => hlow m hm fuel

variable (P Q Valid Xc) in
/-- The walk's simulation, the fundamental lemma and the entry of `Xc`
closures below `n`. -/
def Low (n : Nat) : Prop :=
  ∀ m < n, (∀ fuel, WalkAt P Q Valid Xc m fuel) ∧ Rel.FundAt P Q (WV Q Valid Xc) m ∧ XcEnter P Q Valid Xc m

variable (P Q Valid Xc) in
/-- What the walk's simulation assumes of a pass: the programs agree on
constructors and arities, valid configurations read them as the source
does (and inline only the source's globals), and calls, global values,
redirected calls and the entry of `Xc` closures simulate at each bound
given the walk's simulation, the fundamental lemma and `Xc` entry below
it (and, for `Xc` entry, the program interface at the bound). -/
structure Hyp : Prop where
  known : Q.known = P.known
  arity : ∀ g gd, P.global? g = some gd → ∃ gd', Q.global? g = some gd' ∧ gd'.ps.length = gd.ps.length
  suffix : ∀ C ρ ρ' ρ₂ ρ'₂, Valid C ρ ρ' → ρ <:+ ρ₂ → ρ' <:+ ρ'₂ → Valid C ρ₂ ρ'₂
  cknown : ∀ C ρ ρ', Valid C ρ ρ' → C.prog.known = P.known
  cglob : ∀ C ρ ρ', Valid C ρ ρ' → ∀ g,
    (C.prog.global? g).map (·.ps.length) = (P.global? g).map (·.ps.length)
  cbody : ∀ C ρ ρ', Valid C ρ ρ' → ∀ g, C.inline.contains g = true → C.prog.global? g = P.global? g
  inl : ∀ C ρ ρ' ρ₂, Valid C ρ ρ' → Valid { C with inline := [], redirect := none } ρ₂ ρ'
  call : ∀ n, Low P Q Valid Xc n → Rel.CallSim P Q (WV Q Valid Xc) n
  glob : ∀ n, Low P Q Valid Xc n → Rel.GlobSim P Q (WV Q Valid Xc) n
  red : ∀ n, Low P Q Valid Xc n →
    ∀ C ρ ρ' r, Valid C ρ ρ' → C.redirect = some r →
      RedSim (P := P) (Q := Q) (Valid := Valid) (Xc := Xc) n r ρ ρ'
  xenter : ∀ n, Low P Q Valid Xc n → Rel.AppSim P Q (WV Q Valid Xc) n → Rel.CallSim P Q (WV Q Valid Xc) n →
    Rel.GlobSim P Q (WV Q Valid Xc) n → XcEnter P Q Valid Xc n

/-- The walk's simulation, the fundamental lemma, `Xc` entry and the program
interface, at every bound. -/
theorem levels (H : Hyp P Q Valid Xc) : ∀ n, ((∀ fuel, WalkAt P Q Valid Xc n fuel) ∧
    Rel.FundAt P Q (WV Q Valid Xc) n ∧ XcEnter P Q Valid Xc n) ∧ Rel.AppSim P Q (WV Q Valid Xc) n ∧
    Rel.CallSim P Q (WV Q Valid Xc) n ∧ Rel.GlobSim P Q (WV Q Valid Xc) n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hlow : Low P Q Valid Xc n := fun m hm => (ih m hm).1
  have happ := app_at (fun m hm => (hlow m hm).1) (fun m hm => (hlow m hm).2.1) (fun m hm => (hlow m hm).2.2)
    H.suffix
  have hcall := H.call n hlow
  have hglob := H.glob n hlow
  have hctx : Ctx P Q Valid Xc n :=
    { known := H.known, arity := H.arity, suffix := H.suffix, cknown := H.cknown, cglob := H.cglob
      cbody := H.cbody, inl := H.inl, app := happ, call := hcall, glob := hglob
      red := H.red n hlow }
  exact ⟨⟨walkAt_all hctx (fun m hm => (hlow m hm).1),
    Rel.fund_step structural H.known (fun m hm => (hlow m hm).2.1) happ hcall hglob,
    H.xenter n hlow happ hcall hglob⟩, happ, hcall, hglob⟩

/-- **Adequacy** for the walk: a pass satisfying `Hyp` with the same roots
refines its input. -/
theorem refines (H : Hyp P Q Valid Xc) (hroots : Q.roots = P.roots) : Sem.Refines P Q :=
  Rel.refines_of structural hroots (fun _ _ h => obs h) (fun n => (levels H n).2.2.2)
    (fun n => (levels H n).2.1)

end Compilatrix.Anf.WalkProof
