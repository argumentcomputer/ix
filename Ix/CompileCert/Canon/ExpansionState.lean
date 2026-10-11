import Ix.CompileCert.Canon.ExpansionScope
import Ix.CompileCert.Canon.ExpansionLoops

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- Unconditional frame of an actual expansion step. This retains every prior
structural queue identity and allocation-history entry and the exact source
protection list. It is an internal transition property, not an input premise. -/
def ExpansionFrame (cx : XCtx) (before after : XSt) : Prop :=
  (∀ name, before.typeNames.contains name = true → after.typeNames.contains name = true) ∧
  after.sourceNames cx = before.sourceNames cx ∧
  (∀ name ∈ before.allocatedNames, name ∈ after.allocatedNames) ∧
  (∀ name ∈ before.allocatedCtorRoots, name ∈ after.allocatedCtorRoots)

theorem ExpansionFrame.refl (cx : XCtx) (st : XSt) : ExpansionFrame cx st st :=
  ⟨fun _ h => h,rfl,fun _ h => h,fun _ h => h⟩

theorem ExpansionFrame.trans {cx : XCtx} {a b c : XSt}
    (left : ExpansionFrame cx a b) (right : ExpansionFrame cx b c) :
    ExpansionFrame cx a c :=
  ⟨fun name h => right.1 name (left.1 name h),right.2.1.trans left.2.1,
    fun name h => right.2.2.1 name (left.2.2.1 name h),
    fun name h => right.2.2.2 name (left.2.2.2 name h)⟩

theorem ExpansionFrame.push (cx : XCtx) (st : XSt) (member : XMember) :
    ExpansionFrame cx st (st.push member) :=
  ⟨fun name h => NameTable.contains_insert_mono st.typeNames member.name name () h,
    rfl,fun _ h => h,fun _ h => h⟩

theorem ExpansionFrame.reserve (cx : XCtx) (st : XSt) (aux : Name) :
    ExpansionFrame cx st { st with
      sourceNames? := some (st.sourceNames cx)
      allocatedNames := keyName aux :: st.allocatedNames } :=
  ⟨fun _ h => h,rfl,fun _ h => List.mem_cons_of_mem _ h,fun _ h => h⟩

theorem ExpansionFrame.constructor (cx : XCtx) (st : XSt) (ctor : Name) :
    ExpansionFrame cx st { st with
      allocatedNames := keyName ctor :: st.allocatedNames
      allocatedCtorRoots := keyName ctor :: st.allocatedCtorRoots } :=
  ⟨fun _ h => h,rfl,fun _ h => List.mem_cons_of_mem _ h,
    fun _ h => List.mem_cons_of_mem _ h⟩

/-- The actual query/group/constructor transition retains the frame. No
assumption about lookup success, cached digests, or source naming is used. -/
theorem replaceIfNested_frame (cx : XCtx) (np : Nat) (owner : Name)
    (e : Expr) (depth : Nat) (st : XSt) :
    ExpansionFrame cx st (replaceIfNested cx np owner e depth st).2 := by
  unfold replaceIfNested
  dsimp only [Id.run]
  repeat' (first | exact ExpansionFrame.refl cx st | split)
  all_goals
    show ExpansionFrame cx st
      (forIn (m := Id) (β := XSt × Option Expr) (_ : Array (Array Name)) _ _).1
    refine forIn_id_inv_array (fun r : XSt × Option Expr => ExpansionFrame cx st r.1)
      _ ?_ _ _ (ExpansionFrame.refl cx st)
    intro cls r hr
    try dsimp only
    split
    · split
      · simp only [id_bind_eq]
        repeat' split
        all_goals
          apply hr.trans
          refine ExpansionFrame.trans ?_ (ExpansionFrame.push cx _ _)
          refine forIn_id_inv_array (fun q : XSt × Array XCtor => ExpansionFrame cx r.1 q.1)
            _ ?_ _ _ ?_
          · intro x q hq
            obtain ⟨cn,ct,nf⟩ := x
            exact hq.trans (ExpansionFrame.constructor cx q.1 _)
          · first
            | exact ExpansionFrame.reserve cx r.1 _
            | (refine array_foldl_inv (fun q : XSt => ExpansionFrame cx r.1 q)
                _ ?_ _ _ (ExpansionFrame.reserve cx r.1 _)
               intro q k hq
               try dsimp only
               repeat' (first | exact hq | split))
      · exact hr
    · exact hr

theorem replaceAll_frame (cx : XCtx) (np : Nat) (owner : Name) :
    ∀ (e : Expr) (d : Nat) (st : XSt), ExpansionFrame cx st (replaceAll cx np owner e d st).2 := by
  intro e
  induction e with
  | app f a h ihf iha =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.app f a h) d st
    revert hR
    cases replaceIfNested cx np owner (.app f a h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihf d st1
        revert h1
        cases replaceAll cx np owner f d st1 with
        | mk f' st2 =>
          intro h1
          have h2 := iha d st2
          revert h2
          cases replaceAll cx np owner a d st2 with
          | mk a' st3 => intro h2; exact hR.trans (h1.trans h2)
  | lam n t b bi h iht ihb =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.lam n t b bi h) d st
    revert hR
    cases replaceIfNested cx np owner (.lam n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1
        revert h1
        cases replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2
          revert h2
          cases replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact hR.trans (h1.trans h2)
  | forallE n t b bi h iht ihb =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.forallE n t b bi h) d st
    revert hR
    cases replaceIfNested cx np owner (.forallE n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1
        revert h1
        cases replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2
          revert h2
          cases replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact hR.trans (h1.trans h2)
  | letE n t v b nd h iht ihv ihb =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.letE n t v b nd h) d st
    revert hR
    cases replaceIfNested cx np owner (.letE n t v b nd h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1
        revert h1
        cases replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihv d st2
          revert h2
          cases replaceAll cx np owner v d st2 with
          | mk v' st3 =>
            intro h2
            have h3 := ihb (d + 1) st3
            revert h3
            cases replaceAll cx np owner b (d + 1) st3 with
            | mk b' st4 => intro h3; exact hR.trans (h1.trans (h2.trans h3))
  | proj n i s h ihs =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.proj n i s h) d st
    revert hR
    cases replaceIfNested cx np owner (.proj n i s h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihs d st1
        revert h1
        cases replaceAll cx np owner s d st1 with
        | mk s' st2 => intro h1; exact hR.trans h1
  | mdata md x h ihx =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.mdata md x h) d st
    revert hR
    cases replaceIfNested cx np owner (.mdata md x h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihx d st1
        revert h1
        cases replaceAll cx np owner x d st1 with
        | mk x' st2 => intro h1; exact hR.trans h1
  | bvar i h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.bvar i h) d st
    revert hR
    cases replaceIfNested cx np owner (.bvar i h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | fvar n h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.fvar n h) d st
    revert hR
    cases replaceIfNested cx np owner (.fvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | mvar n h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.mvar n h) d st
    revert hR
    cases replaceIfNested cx np owner (.mvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | sort u h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.sort u h) d st
    revert hR
    cases replaceIfNested cx np owner (.sort u h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | const n us h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.const n us h) d st
    revert hR
    cases replaceIfNested cx np owner (.const n us h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | lit l h =>
    intro d st
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_frame cx np owner (.lit l h) d st
    revert hR
    cases replaceIfNested cx np owner (.lit l h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR

/-- Rewriting one queued constructor preserves the actual state frame. -/
theorem walkCtor_frame (cx : XCtx) (qi ci : Nat) (st : XSt) :
    ExpansionFrame cx st (walkCtor cx qi ci st) := by
  unfold walkCtor
  split
  · exact ExpansionFrame.refl cx st
  · rename_i member found
    split
    · exact ExpansionFrame.refl cx st
    · rename_i ctor foundCtor
      exact replaceAll_frame cx (peelForalls cx.nParams ctor.typ #[]).1.size
        member.sourceOwner (peelForalls cx.nParams ctor.typ #[]).2 0 st

/-- A successful actual queue execution preserves the state frame. Errors
are not projected to partial successful outputs. -/
theorem walkQueue_frame (cx : XCtx) : ∀ (fuel qi : Nat) (st fin : XSt),
    walkQueue cx fuel qi st = .ok fin → ExpansionFrame cx st fin
  | 0,qi,st,fin,run => by
    rw [walkQueue.eq_1] at run
    split at run
    · cases run
    · split at run
      · cases run
      · cases except_pure_ok run
        exact ExpansionFrame.refl cx st
  | fuel+1,qi,st,fin,run => by
    rw [walkQueue.eq_2] at run
    split at run
    · cases run
    · split at run
      · cases except_pure_ok run
        exact ExpansionFrame.refl cx st
      · rename_i member found
        have step : ExpansionFrame cx st
            ((List.range member.ctors.size).foldl (fun s ci => walkCtor cx qi ci s) st) := by
          refine list_foldl_inv (fun s => ExpansionFrame cx st s) _ ?_ _ _
            (ExpansionFrame.refl cx st)
          intro s ci current
          exact current.trans (walkCtor_frame cx qi ci s)
        exact step.trans (walkQueue_frame cx fuel (qi+1) _ fin run)

theorem RunKnown.frame {cx : XCtx} {before after : XSt}
    (transition : ExpansionFrame cx before after) {name : Name}
    (known : RunKnown cx before name) : RunKnown cx after name := by
  rcases known with reached | queued
  · exact Or.inl reached
  · exact Or.inr (transition.1 name queued)

end Ix.CompileCert.Canon
