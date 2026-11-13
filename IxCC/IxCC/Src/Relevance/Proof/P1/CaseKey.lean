import IxCC.Src.Relevance.Proof.P1.Ctor
import IxCC.Src.Relevance.Proof.P1.Delta

/-! # P1, relevance preservation: a `case` key fired (F5)

The case of the core at a `case` key (`CaseCases`, `IxCC.Src.Relevance.Proof.P1.Cases`). F5 forces
the major (an ordinary kind) and the chosen minor, and applies the minor to the fields one by one.
The major's and the minor's `force` have their precondition from `FireOk` (a marker or a `Live`
slot); the minor is read at the key's instance (`Canonical.minorsRead`), so it forces to a `Live`,
`Whole` value. The fields fit it one by one (`allFit_chain`): a field that is no marker is `Live`
(the major's `Live.con`, or an index argument of the key); a marker field not written erased meets
a value that ignores it by `SortCoherent` (c); a marker field written erased meets the minor's
λ-telescope at an irrelevant binder (`MinorsIgnore`, the constructor's record from the major's
`Live.con` at an ordinary kind, from `Canonical.subRecords` at a subsingleton one), which the
values along the application keep (`IgnoresAt`); an index slot written erased in the key's type
cannot be, since the key reads every position from `np + 1` on (`Canonical.reads`). -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical
open IxCC.Lam.Erase.Proof (Agree)

variable {p : Program} {ann : Ann} {ch : Checked}

/-! ## Values that ignore an argument after some applications -/

/-- `f`, after `n` applications at clock `k` that return, ignores the next argument. -/
def IgnoresAt (p : Program) (ann : Ann) (k : Nat) : Value → Nat → Prop
  | f, 0 => IgnoresNext ann f
  | f, n + 1 => ∀ s v, apply p k f s = .ok v → IgnoresAt p ann k v n

/-- The closure of a λ-telescope whose binder `n` is irrelevant at its levels. -/
theorem ignoresAt_clo {k : Nat} : ∀ (n : Nat) (b : Binder) (d body : Term) (ρ : Env) (ls : Levels)
    (r : Rel), (lamRels (.lam b d body))[n]? = some r → r.irrAt ls = true →
    IgnoresAt p ann k (.clo b d body ρ ls) n
  | 0, b, d, body, ρ, ls, r, hr, hirr => by
    simp only [lamRels, List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr
    exact hirr
  | n + 1, b, d, body, ρ, ls, r, hr, hirr => by
    intro s v hv
    simp only [lamRels, List.getElem?_cons_succ] at hr
    cases body with
    | lam b2 d2 body2 =>
      rw [apply_clo] at hv
      split at hv
      · cases k with
        | zero => cases hv
        | succ k' =>
          simp only [Sem.later_succ, eval_lam, Sem.Result.ok.injEq] at hv
          subst hv
          exact ignoresAt_clo n b2 d2 body2 _ ls r hr hirr
      · cases hv
    | _ => simp [lamRels] at hr

/-- A value that is neither a closure nor a partial application ignores every argument (applying
it is stuck). -/
theorem ignoresAt_stuck {k : Nat} {v : Value} (h1 : ∀ b d body ρ' ls', v ≠ .clo b d body ρ' ls')
    (h2 : ∀ h ls' args, v ≠ .pap h ls' args) : ∀ n, IgnoresAt p ann k v n
  | 0 => by
    cases v with
    | clo b d body ρ' ls' => exact absurd rfl (h1 b d body ρ' ls')
    | pap h ls' args => exact absurd rfl (h2 h ls' args)
    | _ => trivial
  | n + 1 => by
    intro s w hw
    rw [apply_other p k v s h1 h2] at hw
    cases hw

/-- The value a minor slot forces to ignores argument `n` after `n` applications when the slot
ignores argument `n` (`IgnoresSlot`). -/
theorem ignoresAt_of_slot {k k' : Nat} {s : Slot} {v : Value} {n : Nat} (hig : IgnoresSlot s n)
    (hv : force p k s = .ok v) : IgnoresAt p ann k' v n := by
  cases s with
  | val w =>
    rw [force_val] at hv
    cases hv
    cases v with
    | clo b d body ρ' ls' =>
      obtain ⟨r, hr, hirr⟩ := hig
      exact ignoresAt_clo n b d body ρ' ls' r hr hirr
    | pap _ _ _ => exact hig.elim
    | lit _ => exact ignoresAt_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) n
    | str _ => exact ignoresAt_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) n
    | con _ _ _ _ => exact ignoresAt_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) n
    | irr _ _ _ => exact ignoresAt_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) n
  | name t ρ' ls' =>
    rw [force_name] at hv
    cases k with
    | zero => cases hv
    | succ k0 =>
      simp only [Sem.later_succ] at hv
      obtain ⟨r, hr, hirr⟩ := hig
      cases t with
      | lam b d body =>
        rw [eval_lam] at hv
        cases hv
        exact ignoresAt_clo n b d body ρ' ls' r hr hirr
      | _ => simp [lamRels] at hr

/-! ## Slots that fit a value -/

/-- A marker fits a `Whole` value that ignores its next argument. -/
theorem slotFits_of_ignores (hf : Facts p ann ch) {f : Value} {s : Slot} (hw : Whole p f)
    (hig : IgnoresNext ann f) (hms : MarkerSlot s) : SlotFits p ann ch f s := by
  cases f with
  | clo b d body ρ ls =>
    intro hrel
    simp only [IgnoresNext] at hig
    rw [hig] at hrel
    cases hrel
  | pap h ls args => exact ⟨fun hn => (hn ⟨hig, hms⟩).elim, minorsIgnore_of_whole hf hw⟩
  | lit _ => trivial
  | str _ => trivial
  | con _ _ _ _ => trivial
  | irr _ _ _ => trivial

/-- A `LiveSlot` fits a `Whole` value. -/
theorem slotFits_of_live (hf : Facts p ann ch) {f : Value} {s : Slot} (hw : Whole p f)
    (hs : LiveSlot p ann ch s) : SlotFits p ann ch f s := by
  cases f with
  | clo _ _ _ _ _ => exact fun _ => hs
  | pap h ls args => exact ⟨fun _ => hs, minorsIgnore_of_whole hf hw⟩
  | lit _ => trivial
  | str _ => trivial
  | con _ _ _ _ => trivial
  | irr _ _ _ => trivial

/-- Slots fit a `Live`, `Whole` value one by one (`AllFit`), along the applications a call `c0`
makes: a slot that is no marker is `LiveSlot`; a marker meets a value that ignores it, by
`MarkersIgnored` where the position is not exempt and by `IgnoresAt` where it is. Each application
is a call `c0` makes, whose `Post` the induction hypothesis gives. -/
theorem allFit_chain (hf : Facts p ann ch) {c0 : Call} (ih : Below p ann ch c0) {k : Nat}
    (exempt : Nat → Prop) : ∀ (fs : List Slot) (i : Nat) (f : Value),
      Relation.TransGen (Step p) c0 (.applyAll k f fs) → Live p ann ch f → Whole p f →
      MarkersIgnored p ann k exempt i f fs →
      (∀ m s, fs[m]? = some s → MarkerSlot s → exempt (i + m) → IgnoresAt p ann k f m) →
      (∀ s ∈ fs, ¬ MarkerSlot s → LiveSlot p ann ch s) →
      AllFit p ann ch k f fs
  | [], _, _, _, _, _, _, _, _ => trivial
  | s :: ss, i, f, hpath, hl, hw, hmi, hex, hls => by
    have hfit : SlotFits p ann ch f s := by
      by_cases hms : MarkerSlot s
      · have hig : IgnoresNext ann f := by
          by_cases he : exempt i
          · exact hex 0 s rfl hms (by simpa using he)
          · exact hmi.1 hms he
        exact slotFits_of_ignores hf hw hig hms
      · exact slotFits_of_live hf hw (hls s (List.mem_cons_self ..) hms)
    refine ⟨hfit, fun v hv => ?_⟩
    have hpa : Relation.TransGen (Step p) c0 (.apply k f s) := .tail hpath .allHead
    obtain ⟨hlv, hwv⟩ := (ih _ hpa ⟨hl, hfit⟩).1 v hv
    refine allFit_chain hf ih exempt ss (i + 1) v (.tail hpath (.allRest hv)) hlv (hwv hw)
      (hmi.2 v hv) (fun m s' hs' hms' he => ?_) (fun s' hs' => hls s' (List.mem_cons_of_mem _ hs'))
    have he' : exempt (i + (m + 1)) := by
      have : i + (m + 1) = i + 1 + m := by omega
      rw [this]
      exact he
    exact hex (m + 1) s' (by simpa using hs') hms' he' s v hv

/-! ## The `case` key -/

/-- A `case` key's special head comes from its `case` entry. -/
theorem resolve_of_cases {c : CId} (hsp : specialHead? p c = some (.cases c)) :
    ∃ r, p.table.resolveOf c = some (.case r) := by
  unfold specialHead? at hsp
  cases hr : p.table.resolveOf c with
  | none =>
    rw [hr] at hsp
    simp only at hsp
    split at hsp <;> simp at hsp
  | some e =>
    rw [hr] at hsp
    cases e with
    | case r => exact ⟨r, rfl⟩
    | _ => simp at hsp

/-- A reached `case` key reads every position from `np + 1` on, so its type writes none of them
erased (`Canonical.reads`). -/
theorem cases_not_erased (hf : Facts p ann ch) {c r : CId} (hr : c ∈ ch.reached)
    (hsp : specialHead? p c = some (.cases c)) (hres : p.table.resolveOf c = some (.case r))
    {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty))
    {d : Decl} (hdc : p.decl? c = some d) {i : Nat} (hi : np + 1 ≤ i) : i ∉ erasedParams d.type := by
  intro hmem
  have h := hf.canon.reads c hr (.cases c) d hsp hdc i hmem
  simp [readsAt, headReadsWith, hres, hd, hi] at h

theorem headArity_cases {c r : CId} {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Rule} {ty : Term} (hres : p.table.resolveOf c = some (.case r))
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty)) :
    p.headArity (.cases c) = np + 1 + ni + 1 + nmin := by
  simp [Program.headArity, hres, hd]

theorem elimShape_cases {c r : CId} {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Rule} {ty : Term} (hres : p.table.resolveOf c = some (.case r))
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty)) :
    elimShape? p c = some { recr := r, minors := (List.range nmin).map fun j => (np + 1 + ni + 1 + j, j, j)
                            major := np + 1 + ni, arity := np + 1 + ni + 1 + nmin } := by
  simp [elimShape?, hres, hd]

/-- The result of a `case` key fired at `k + 1`: its chosen minor applied to the fields. -/
theorem fire_cases_ok {k : Nat} {c r : CId} {ls : Levels} {args : List Slot} {sf kk : Bool}
    {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term} {kind : RecKind} {v : Value}
    (hres : p.table.resolveOf c = some (.case r))
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty))
    (hk : (p.table.recKindOf r).map (·.atLevels ls) = some kind)
    (h : fire p (k + 1) (.cases c) ls args = .ok v) :
    ∃ j fields mv, caseChosen p k ls np ni ind kind args = .ok (j, fields) ∧
      force p k (args.getD (np + 1 + ni + 1 + j) default) = .ok mv ∧
      applyAll p k mv fields = .ok v := by
  have e : fire p (k + 1) (.cases c) ls args =
      (match caseChosen p k ls np ni ind kind args with
       | .ok (j, fields) =>
         match force p k (args.getD (np + 1 + ni + 1 + j) default) with
         | .ok minor => applyAll p k minor fields
         | .timeout => .timeout
         | .resource r => .resource r
         | .trap => .trap
         | .stuck => .stuck
       | .timeout => .timeout
       | .resource r => .resource r
       | .trap => .trap
       | .stuck => .stuck) := by
    rw [fire]
    simp only [hres, hd, hk]
    rfl
  rw [e] at h
  cases hc : caseChosen p k ls np ni ind kind args with
  | ok jf =>
    obtain ⟨j, fields⟩ := jf
    rw [hc] at h
    simp only at h
    cases hm : force p k (args.getD (np + 1 + ni + 1 + j) default) with
    | ok mv =>
      rw [hm] at h
      exact ⟨j, fields, mv, by first | rfl | exact hc, by first | rfl | exact hm, h⟩
    | _ => rw [hm] at h; cases h
  | _ => rw [hc] at h; cases h

/-- A `case` key that fires to a value has a recursor declaration and a kind at the levels. -/
theorem fire_cases_decl {k : Nat} {c r : CId} {ls : Levels} {args : List Slot} {v : Value}
    (hres : p.table.resolveOf c = some (.case r)) (h : fire p (k + 1) (.cases c) ls args = .ok v) :
    ∃ sf kk lv np nmot nmin ni ind rules ty kind,
      p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) ∧
      (p.table.recKindOf r).map (·.atLevels ls) = some kind := by
  cases hd : p.decl? r with
  | none => rw [fire] at h; simp [hres, hd] at h
  | some d =>
    cases d with
    | recr sf kk lv np nmot nmin ni ind rules ty =>
      cases hk : (p.table.recKindOf r).map (·.atLevels ls) with
      | none => rw [fire] at h; simp [hres, hd, hk] at h
      | some kind => exact ⟨sf, kk, lv, np, nmot, nmin, ni, ind, rules, ty, kind, rfl, rfl⟩
    | _ => rw [fire] at h; simp [hres, hd] at h

/-- Any argument of a fired special head, forced, has its precondition: a marker or `LiveSlot`
(`FireOk.live`); past the arguments, the default slot is a literal. -/
theorem pre_force_getD {h : Head} {ls : Levels} {args : List Slot} (hfire : FireOk p ann ch h ls args)
    (k i : Nat) : Pre p ann ch (.force k (args.getD i default)) := by
  cases hi : args[i]? with
  | none =>
    rw [List.getD_eq_getElem?_getD, hi]
    exact Or.inl (.val (.lit 0) whole_lit)
  | some s =>
    rw [List.getD_eq_getElem?_getD, hi]
    by_cases hms : MarkerSlot s
    · exact Or.inr hms
    · exact Or.inl (hfire.live i s hi (fun h => hms h.2))

/-- The fields F5 applies the chosen minor to, at a reached `case` key with its recursor's
declaration and kind: each that is no marker is `LiveSlot`, and at each marker the
`CaseFieldErased` exemption excuses, the minor's value ignores it after as many applications. -/
theorem fields_F5 (hf : Facts p ann ch) (hs : ShapeOk p) {k : Nat} {c r : CId} {ls : Levels}
    {args : List Slot} (hfire : FireOk p ann ch (.cases c) ls args) (hreached : c ∈ ch.reached)
    (hsp : specialHead? p c = some (.cases c)) (hres : p.table.resolveOf c = some (.case r))
    {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty)) {kind : RecKind}
    (hk : (p.table.recKindOf r).map (·.atLevels ls) = some kind) {j : Nat} {fields : List Slot}
    (hch : caseChosen p k ls np ni ind kind args = .ok (j, fields))
    (hmajor : kind = .ordinary → Post p ann ch (.force k (args.getD (np + 1 + ni) default))) {mv : Value}
    (hmv : force p k (args.getD (np + 1 + ni + 1 + j) default) = .ok mv) :
    (∀ s ∈ fields, ¬ MarkerSlot s → LiveSlot p ann ch s) ∧
    (∀ m s, fields[m]? = some s → MarkerSlot s → CaseFieldErased p c np rules kind j m →
      IgnoresAt p ann k mv m) := by
  have harity : args.length = np + 1 + ni + 1 + nmin := by
    rw [hfire.arity]; exact headArity_cases hres hd
  have hshape := elimShape_cases hres hd
  -- the minor slot ignores a field written erased of the chosen rule's constructor, given its record
  have hminor : ∀ rule kr m, rules[j]? = some rule → ann.ctorRel? rule.ctor = some kr →
      m < kr.fields.length → fieldWrittenErased p rule.ctor m = true → IgnoresAt p ann k mv m := by
    intro rule kr m hrule hkr hm hwe
    cases hsm : args[np + 1 + ni + 1 + j]? with
    | none =>
      rw [List.getD_eq_getElem?_getD, hsm] at hmv
      simp only [Option.getD_none] at hmv
      have : mv = .lit 0 := by
        have h0 : force p k (default : Slot) = .ok (.lit 0) := force_val p k _
        rw [h0] at hmv
        exact (Sem.Result.ok.inj hmv).symm
      subst this
      exact ignoresAt_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) m
    | some sm =>
      rw [List.getD_eq_getElem?_getD, hsm] at hmv
      simp only [Option.getD_some] at hmv
      have hjlt : j < nmin := by
        have := (List.getElem?_eq_some_iff.1 hsm).1
        omega
      have hig : IgnoresSlot sm m := by
        refine hfire.minors c _ rfl hshape (np + 1 + ni + 1 + j) j j ?_ sm hsm rule.ctor kr.fields ?_ m hm hwe
        · show (np + 1 + ni + 1 + j, j, j) ∈ (List.range nmin).map fun j => (np + 1 + ni + 1 + j, j, j)
          simp only [List.mem_map, List.mem_range]
          exact ⟨j, hjlt, rfl⟩
        · simp [ruleCtorFields, hd, hrule, hkr]
      exact ignoresAt_of_slot hig hmv
  cases kind with
  | empty => simp [caseChosen] at hch
  | ordinary =>
    simp only [caseChosen] at hch
    cases hfm : force p k (args.getD (np + 1 + ni) default) with
    | ok major =>
      rw [hfm] at hch
      simp only [Sem.Result.ofOption] at hch
      cases hsel : p.selectRule ind np major with
      | none => rw [hsel] at hch; cases hch
      | some jf =>
        rw [hsel] at hch
        simp only [Sem.Result.ok.injEq] at hch
        subst hch
        cases major with
        | lit n =>
          -- a literal major's fields are literals
          have hlits : ∀ s ∈ fields, ∃ n', s = .val (.lit n') := by
            intro s hs
            simp only [Program.selectRule] at hsel
            split at hsel
            · split at hsel
              · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                rw [← hsel.2] at hs
                cases hs
              · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                rw [← hsel.2, List.mem_singleton] at hs
                exact ⟨_, hs⟩
            · cases hsel
          refine ⟨fun s hs _ => ?_, fun m s hs hms _ => ?_⟩
          · obtain ⟨n', rfl⟩ := hlits s hs
            exact .val (.lit n') whole_lit
          · obtain ⟨n', rfl⟩ := hlits s (List.mem_iff_getElem?.2 ⟨m, hs⟩)
            obtain ⟨_, _, _, h⟩ := hms
            cases h
        | con c' lsv ps fs =>
          have hlive : Live p ann ch (.con c' lsv ps fs) := (hmajor rfl _ hfm).1 rfl
          obtain ⟨sf', lv', np', nf', ty', hdc, rfl⟩ : ∃ sf' lv' np' nf' ty',
              p.decl? c' = some (.ctor sf' lv' ind j np' nf' ty') ∧ fields = fs.map .val := by
            simp only [Program.selectRule] at hsel
            cases hdc : p.decl? c' with
            | none => rw [hdc] at hsel; cases hsel
            | some d =>
              rw [hdc] at hsel
              cases d with
              | ctor sf' lv' ind' cidx np' nf' ty' =>
                simp only at hsel
                split at hsel
                · rename_i hcond
                  simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                  obtain ⟨rfl, rfl⟩ := hsel
                  obtain ⟨rfl, -⟩ := hcond
                  exact ⟨sf', lv', np', nf', ty', rfl, rfl⟩
                · cases hsel
              | _ => simp at hsel
          cases hlive with
          | con hread hwhole hplaced =>
            refine ⟨fun s hs hms => ?_, fun m s hs hms hex => ?_⟩
            · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hs
              obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
              have hvi : v.isIrr = false := by
                cases v with
                | irr t ρ' l' => exact (hms ⟨t, ρ', l', rfl⟩).elim
                | _ => rfl
              exact .val (hread i v hi (Or.inr hvi)) (hwhole i v hi)
            · rw [List.getElem?_map] at hs
              cases hv : fs[m]? with
              | none => rw [hv] at hs; cases hs
              | some v =>
                rw [hv] at hs
                simp only [Option.map_some, Option.some.injEq] at hs
                subst hs
                have hvi : v.isIrr = true := by
                  obtain ⟨_, _, _, h⟩ := hms
                  cases h
                  rfl
                rcases hex with hwe' | ⟨w, srcs, i', d, hkd, -, -, -⟩
                · cases hrule : rules[j]? with
                  | none => rw [hrule] at hwe'; cases hwe'
                  | some rule =>
                    rw [hrule] at hwe'
                    simp only [Option.map_some, Option.getD_some] at hwe'
                    -- the rule's constructor is the value's
                    obtain ⟨sf2, lv2, np2, ty2, hdr⟩ :=
                      (hf.canon.rules c hreached _ hshape) sf kk lv np nmot nmin ni ind rules ty hd j rule hrule
                    have hcc : c' = rule.ctor := hs.ctorUnique _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdc hdr
                    subst hcc
                    have hcount := hplaced.count m v hv hvi hwe' _ _ _ _ _ _ _ hdc
                    have hrd : ReadsField p ann ch rule.ctor lsv m = false := by
                      cases hrf : ReadsField p ann ch rule.ctor lsv m
                      · rfl
                      · have := live_not_irr (hread m v hv (Or.inl hrf))
                        rw [hvi] at this; cases this
                    obtain ⟨kr, hkr⟩ : ∃ kr, ann.ctorRel? rule.ctor = some kr := by
                      simp only [ReadsField, hdc, Checked.keeps, Checked.keepsP] at hrd
                      cases hck : ch.ctorRel? rule.ctor with
                      | none => rw [hck] at hrd; cases hrd
                      | some kr =>
                        refine ⟨kr, ?_⟩
                        simp only [Checked.ctorRel?, hf.wa.ctors] at hck
                        exact hck
                    obtain ⟨sf3, lv3, ind3, cidx3, np3, nf3, ty3, hdr3, hkrlen, -⟩ :=
                      hf.canon.ctors rule.ctor kr hkr
                    rw [hdc] at hdr3
                    simp only [Option.some.injEq, Decl.ctor.injEq] at hdr3
                    obtain ⟨-, -, -, -, -, rfl, -⟩ := hdr3
                    have hmlt : m < kr.fields.length := by
                      have := (List.getElem?_eq_some_iff.1 hv).1
                      omega
                    exact hminor rule kr m hrule hkr hmlt hwe'
                · cases hkd
        | _ => simp [Program.selectRule] at hsel
    | _ => rw [hfm] at hch; cases hch
  | subsingleton w srcs =>
    simp only [caseChosen, Sem.Result.ok.injEq, Prod.mk.injEq] at hch
    obtain ⟨rfl, hfields⟩ := hch
    -- the raw kind
    have hraw : p.table.recKindOf r = some (.subsingleton w srcs) := by
      cases hr : p.table.recKindOf r with
      | none => rw [hr] at hk; cases hk
      | some k0 =>
        rw [hr] at hk
        simp only [Option.map_some, Option.some.injEq] at hk
        cases k0 with
        | subsingleton w0 srcs0 =>
          simp only [RecKind.atLevels] at hk
          split at hk
          · exact hk ▸ rfl
          · cases hk
        | _ => simp [RecKind.atLevels] at hk
    -- a field slot: an index argument of the key, or the marker
    have hflen : fields.length = srcs.length := by rw [← hfields, List.length_map]
    have hslot : ∀ (m : Nat) (s : Slot), fields[m]? = some s → ¬ MarkerSlot s →
        ∃ i', srcs[m]? = some (FieldSrc.index i') ∧ args[np + 1 + i']? = some s := by
      intro m s hs hms
      rw [← hfields, List.getElem?_map] at hs
      cases hsrc : srcs[m]? with
      | none => rw [hsrc] at hs; cases hs
      | some src =>
        rw [hsrc] at hs
        simp only [Option.map_some, Option.some.injEq] at hs
        cases src with
        | proof => exact (hms (by rw [← hs]; exact ⟨_, _, _, rfl⟩)).elim
        | index i' =>
          simp only at hs
          rw [List.getD_eq_getElem?_getD] at hs
          cases hai : args[np + 1 + i']? with
          | none => rw [hai] at hs; exact (hms (by rw [← hs]; exact ⟨_, _, _, rfl⟩)).elim
          | some s' =>
            rw [hai] at hs
            simp only [Option.getD_some] at hs
            exact ⟨i', rfl, by rw [hai, hs]⟩
    refine ⟨fun s hs hms => ?_, fun m s hs hms hex => ?_⟩
    · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hs
      obtain ⟨i', -, hai⟩ := hslot m s hm hms
      exact hfire.live _ s hai (fun h => hms h.2)
    · rcases hex with hwe' | ⟨w', srcs', i', d, hkd, hsrc, hdc, hmem⟩
      · cases hrule : rules[0]? with
        | none => rw [hrule] at hwe'; cases hwe'
        | some rule =>
          rw [hrule] at hwe'
          simp only [Option.map_some, Option.getD_some] at hwe'
          have hrec := hf.canon.subRecords c hreached _ hshape w srcs sf kk lv np nmot nmin ni ind rules ty
            rule hraw hd hrule
          obtain ⟨kr, hkr⟩ := Option.isSome_iff_exists.1 hrec
          obtain ⟨sf3, lv3, ind3, cidx3, np3, nf3, ty3, hdr3, hkrlen, -⟩ := hf.canon.ctors rule.ctor kr hkr
          have hsl := hf.canon.subsingletonFields c hreached _ hshape sf kk lv np nmot nmin ni ind rules ty
            w srcs rule hd hraw hrule
          have hcf : ctorFields p rule = nf3 := by simp [ctorFields, hdr3]
          have hmlt : m < kr.fields.length := by
            have := (List.getElem?_eq_some_iff.1 hs).1
            omega
          exact hminor rule kr m hrule hkr hmlt hwe'
      · simp only [RecKind.subsingleton.injEq] at hkd
        obtain ⟨rfl, rfl⟩ := hkd
        exact (cases_not_erased hf hreached hsp hres hd hdc (by omega) hmem).elim

/-- F5. -/
theorem case_cases : CaseCases p ann ch := by
  intro k c ls args hf hs hpre hcoh ih
  have hfire : FireOk p ann ch (.cases c) ls args := hpre
  obtain ⟨hsp, q, hag, hinst⟩ := hfire.inst.1 c rfl
  have hreached : c ∈ ch.reached := hf.reached (c, q) hinst
  obtain ⟨r, hres⟩ := resolve_of_cases hsp
  cases k with
  | zero =>
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · simp [fire] at hv
    · cases hst
  | succ k =>
    -- the chosen minor forces to a `Live`, `Whole` value
    have hminorPre : ∀ sf kk lv np nmot nmin ni ind rules ty j,
        p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        LiveSlot p ann ch (args.getD (np + 1 + ni + 1 + j) default) := by
      intro sf kk lv np nmot nmin ni ind rules ty j hd
      have harity : args.length = np + 1 + ni + 1 + nmin := by
        rw [hfire.arity]; exact headArity_cases hres hd
      cases hsm : args[np + 1 + ni + 1 + j]? with
      | none =>
        rw [List.getD_eq_getElem?_getD, hsm]
        exact .val (.lit 0) whole_lit
      | some sm =>
        rw [List.getD_eq_getElem?_getD, hsm]
        refine hfire.live _ sm hsm ?_
        rintro ⟨⟨c0, cr, r0, hc0, hcr, hpr, hirr⟩, -⟩
        simp only [headConst?, Option.some.injEq] at hc0
        rw [← hc0] at hcr
        have happ : appliedAt p c (np + 1 + ni + 1 + j) = true := by
          have := (List.getElem?_eq_some_iff.1 hsm).1
          simp [appliedAt, hsp, hres, hd]
          omega
        have h1 := hf.canon.minorsRead (c, q) hinst cr hcr _ r0 happ hpr
        rw [hag.irr] at h1
        rw [h1] at hirr
        cases hirr
    have hpreApply : ∀ sf kk lv np nmot nmin ni ind rules ty kind j fields mv,
        p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        (p.table.recKindOf r).map (·.atLevels ls) = some kind →
        caseChosen p k ls np ni ind kind args = .ok (j, fields) →
        force p k (args.getD (np + 1 + ni + 1 + j) default) = .ok mv →
        Pre p ann ch (.applyAll k mv fields) ∧ Whole p mv := by
      intro sf kk lv np nmot nmin ni ind rules ty kind j fields mv hd hk hch hmv
      have hmajor : kind = .ordinary → Post p ann ch (.force k (args.getD (np + 1 + ni) default)) := by
        intro hko
        subst hko
        exact (ih _ (.single (Step.caseMajor hres hd hk)) (pre_force_getD hfire k _)).1
      have hmstep : Relation.TransGen (Step p) (.fire (k + 1) (.cases c) ls args)
          (.force k (args.getD (np + 1 + ni + 1 + j) default)) :=
        .single (Step.caseMinor hres hd hk hch)
      have hml := hminorPre sf kk lv np nmot nmin ni ind rules ty j hd
      have hlmv : Live p ann ch mv := force_live ih hmstep hml hmv
      have hwmv : Whole p mv := ((ih _ hmstep (Or.inl hml)).1 mv hmv).2
      obtain ⟨hlive, hex⟩ := fields_F5 hf hs hfire hreached hsp hres hd hk hch hmajor hmv
      have hmi : MarkersIgnored p ann k (CaseFieldErased p c np rules kind j) 0 mv fields :=
        hcoh r sf kk lv np nmot nmin ni ind rules ty kind j fields mv hres hd hk hch hmv
      refine ⟨⟨hlmv, ?_⟩, hwmv⟩
      exact allFit_chain hf ih (CaseFieldErased p c np rules kind j) fields 0 mv
        (.single (Step.caseApply hres hd hk hch hmv)) hlmv hwmv hmi
        (fun m s hs hms he => hex m s hs hms (by simpa using he)) hlive
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · obtain ⟨sf, kk, lv, np, nmot, nmin, ni, ind, rules, ty, kind, hd, hk⟩ := fire_cases_decl hres hv
      obtain ⟨j, fields, mv, hch, hmv, happ⟩ := fire_cases_ok hres hd hk hv
      obtain ⟨hpa, hwmv⟩ := hpreApply sf kk lv np nmot nmin ni ind rules ty kind j fields mv hd hk hch hmv
      have hpost := (ih _ (.single (Step.caseApply hres hd hk hch hmv)) hpa).1 v happ
      exact ⟨hpost.1, hpost.2 hwmv⟩
    · cases hst with
      | caseMajor _ _ _ => exact pre_force_getD hfire k _
      | caseMinor _ _ _ _ => exact pre_force_getD hfire k _
      | caseApply hres' hd' hk' hch' hmv' =>
        rw [hres] at hres'
        simp only [Option.some.injEq, Resolve.case.injEq] at hres'
        subst hres'
        exact (hpreApply _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd' hk' hch' hmv').1

end IxCC.Src.Relevance.Proof.P1
