import IxCC.Xv.Validate.Proof.Row

/-!
# The row simulation

`execBound_sim` (see `Proof.Row`): under the validator's checks of an
instruction's paired operands (`RowFacts`), a successful Xv run of its rows
is matched by the Xl run over its locations.
-/

namespace IxCC.Xv

open IxCC.Lir (VReg Word Env)
open X86 (GPR)
open IxCC.Xv.Validate (Wide)
open IxCC.Xv.Xl (placeL xlLocs xlNamed xlCells xlFree xlTable WriteOk)

/-- The validator's checks of one instruction's rows, bound over operands
paired with their locations, in the form the soundness proof uses
(`Proof.Inst` derives them from `Validate.stepOperands`). -/
structure RowFacts (parts : List (X86.Op × List (Bound (VReg × Loc)))) (zf : Bool) (fr : Xl.Frame) :
    Prop where
  shape : ∀ q ∈ parts, ∃ defs args, bindRow q.1 defs args = some q.2
  stack : ∀ q ∈ parts, (X86.desc q.1).stack = .none
  wide : ∀ q ∈ parts, ∀ i ∈ (X86.desc q.1).implicit, i.role.reads = true ∨ Wide i.width
  narrow : ∀ q ∈ parts, ∀ b ∈ q.2, b.narrowOutput = true → zf = true ∧ parts.getLast? = some q
  onlyLast : ∀ q ∈ parts.dropLast, q.2.flatMap Bound.defs = []
  placeable : ∀ b ∈ parts.flatMap Prod.snd, Xl.Bound.placeable (b.map Prod.snd) = true
  addr : ∀ b ∈ parts.flatMap Prod.snd, ∀ u ∈ b.addrRegs, u.2.isCell = false
  useReg : ∀ u ∈ (parts.flatMap Prod.snd).flatMap Bound.uses, ∀ r, u.2 = .reg r → Xl.reserved r = false
  defOk : ∀ d ∈ (parts.flatMap Prod.snd).flatMap Bound.defs, WriteOk fr d.2
  defLocs : (((parts.flatMap Prod.snd).flatMap Bound.defs).map (·.2)).Nodup
  defRegs : (((parts.flatMap Prod.snd).flatMap Bound.defs).map (·.1)).Nodup
  early : ∀ b ∈ parts.flatMap Prod.snd, b.narrowOutput = true → ∀ d ∈ b.defs,
    ∀ u ∈ (parts.flatMap Prod.snd).flatMap Bound.uses, u.2 ≠ d.2
  cells : (xlCells ((parts.flatMap Prod.snd).map (Bound.map Prod.snd))).length ≤
    (xlFree ((parts.flatMap Prod.snd).map (Bound.map Prod.snd))).length

/-! ## Helpers -/

theorem mapM_isSome {β γ : Type} {f : β → Option γ} :
    ∀ {l : List β}, (∀ x ∈ l, (f x).isSome = true) → ∃ ys, l.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
      obtain ⟨ys, hys⟩ := mapM_isSome (l := l) fun z hz => h z (List.mem_cons_of_mem _ hz)
      exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

theorem mapM_map_congr {β γ δ : Type} {f : γ → Option δ} {g : β → γ} {h : β → Option δ} :
    ∀ {l : List β}, (∀ x ∈ l, f (g x) = h x) → (l.map g).mapM f = l.mapM h
  | [], _ => rfl
  | x :: l, e => by
      simp only [List.map_cons, List.mapM_cons]
      rw [e x List.mem_cons_self, mapM_map_congr fun y hy => e y (List.mem_cons_of_mem _ hy)]

theorem Bound.machine_isSome {b : Bound GPR} (hs : b.isSlot = true)
    (ha : ∀ r ∈ b.addrRegs, r ≠ .rsp) : (b.machine some some).isSome = true := by
  have am : ∀ (m : Amode GPR), (∀ r ∈ m.regs, r ≠ .rsp) → (m.toMem some).isSome = true := by
    intro m hm
    rcases m with ⟨base, index, disp⟩
    rcases index with _ | ⟨r, s⟩
    · rcases base with _ | (_ | _) <;> simp [Amode.toMem]
    · have hr : r ≠ .rsp := hm r (by rcases base with _ | (_ | _) <;> simp [Amode.regs])
      cases hi : indexReg r with
      | none => cases r <;> simp_all [indexReg]
      | some i => rcases base with _ | (_ | _) <;> simp [Amode.toMem, hi]
  cases b with
  | input s a =>
    cases a with
    | m m => simpa [Bound.machine] using am m ha
    | _ => simp [Bound.machine]
  | memory s m => simpa [Bound.machine] using am m ha
  | _ => simp_all [Bound.machine, Bound.isSlot]

theorem slotArgs_isSome {bs : List (Bound GPR)} (ha : ∀ b ∈ bs, ∀ r ∈ b.addrRegs, r ≠ .rsp) :
    ∃ as, slotArgs some some bs = some as :=
  mapM_isSome fun b hb => by
    rw [List.mem_filter] at hb
    exact Bound.machine_isSome hb.2 (ha b hb.1)

theorem uses_map_flat {α β : Type} (f : α → β) (bs : List (Bound α)) :
    (bs.map (Bound.map f)).flatMap Bound.uses = (bs.flatMap Bound.uses).map f := by
  rw [List.flatMap_map, List.map_flatMap]
  simp

theorem defs_map_flat {α β : Type} (f : α → β) (bs : List (Bound α)) :
    (bs.map (Bound.map f)).flatMap Bound.defs = (bs.flatMap Bound.defs).map f := by
  rw [List.flatMap_map, List.map_flatMap]
  simp

/-- A location of the Xl bounds is a use's or a definition's. -/
theorem mem_xlLocs {bs : List (Bound (VReg × Loc))} {l : Loc}
    (h : l ∈ xlLocs (bs.map (Bound.map Prod.snd))) :
    (∃ u ∈ bs.flatMap Bound.uses, u.2 = l) ∨ (∃ d ∈ bs.flatMap Bound.defs, d.2 = l) := by
  unfold xlLocs at h
  obtain ⟨b, hb, hl⟩ := List.mem_flatMap.1 h
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  rw [Xl.Bound.mem_locs, Bound.uses_map, Bound.defs_map, ← List.map_append] at hl
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hl
  rcases List.mem_append.1 hq with hq | hq
  · exact .inl ⟨q, List.mem_flatMap.2 ⟨b', hb', hq⟩, rfl⟩
  · exact .inr ⟨q, List.mem_flatMap.2 ⟨b', hb', hq⟩, rfl⟩

theorem use_mem_xlLocs {bs : List (Bound (VReg × Loc))} {u : VReg × Loc}
    (h : u ∈ bs.flatMap Bound.uses) : u.2 ∈ xlLocs (bs.map (Bound.map Prod.snd)) := by
  obtain ⟨b, hb, hu⟩ := List.mem_flatMap.1 h
  unfold xlLocs
  refine List.mem_flatMap.2 ⟨b.map Prod.snd, List.mem_map_of_mem hb, ?_⟩
  rw [Xl.Bound.mem_locs, Bound.uses_map, Bound.defs_map]
  exact List.mem_append_left _ (List.mem_map_of_mem hu)

theorem def_mem_xlLocs {bs : List (Bound (VReg × Loc))} {d : VReg × Loc}
    (h : d ∈ bs.flatMap Bound.defs) : d.2 ∈ xlLocs (bs.map (Bound.map Prod.snd)) := by
  obtain ⟨b, hb, hd⟩ := List.mem_flatMap.1 h
  unfold xlLocs
  refine List.mem_flatMap.2 ⟨b.map Prod.snd, List.mem_map_of_mem hb, ?_⟩
  rw [Xl.Bound.mem_locs, Bound.uses_map, Bound.defs_map]
  exact List.mem_append_right _ (List.mem_map_of_mem hd)

theorem Bound.narrowOutput_defs {α : Type} {b : Bound α} (h : b.narrowOutput = true) :
    b.defs = b.outputs := by
  cases b <;> simp_all [Bound.narrowOutput, Bound.defs, Bound.outputs]

/-- A narrow output's location is a register. -/
theorem narrow_loc_reg {b : Bound (VReg × Loc)} (hp : Xl.Bound.placeable (b.map Prod.snd) = true)
    (hn : b.narrowOutput = true) {d : VReg × Loc} (hd : d ∈ b.defs) : ∃ r, d.2 = .reg r := by
  cases b with
  | output s x =>
    simp only [Bound.defs, List.mem_singleton] at hd
    subst hd
    simp only [Bound.narrowOutput, Bool.or_eq_true, beq_iff_eq] at hn
    simp only [Bound.map, Xl.Bound.placeable, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      beq_iff_eq] at hp
    rcases hp with hp | ⟨-, hw⟩
    · cases h : d.2 with
      | reg r => exact ⟨r, rfl⟩
      | _ => simp [h, Loc.isCell] at hp
    · rcases hn with hn | hn <;> rw [hn] at hw <;> cases hw
  | _ => simp [Bound.narrowOutput] at hn

/-- A fixed use sits in its register's location. -/
theorem fixed_use_loc {b : Bound ((VReg × Loc) × GPR)} (ha : b.Assigned)
    (hp : Xl.Bound.placeable ((b.map Prod.fst).map Prod.snd) = true) {q : (VReg × Loc) × GPR}
    (hq : q ∈ b.uses) (hf : q ∉ b.freeUses) : q.1.2 = .reg q.2 := by
  cases b with
  | fixedUse i a =>
    simp only [Bound.uses, List.mem_singleton] at hq
    subst hq
    simp only [Bound.Assigned] at ha
    simp only [Bound.map, Xl.Bound.placeable, beq_iff_eq] at hp
    rw [hp, ha]
  | fixedTied i a x =>
    simp only [Bound.uses, List.mem_singleton] at hq
    subst hq
    simp only [Bound.Assigned] at ha
    simp only [Bound.map, Xl.Bound.placeable, Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.1, ha.1]
  | _ => simp_all [Bound.uses, Bound.freeUses]

/-- The Xl registers of an assigned bound are its locations' registers. -/
theorem reassign_assigned {LB : List (Bound Loc)} {b : Bound ((VReg × Loc) × GPR)}
    (hp : Xl.Bound.placeable ((b.map Prod.fst).map Prod.snd) = true) :
    (b.reassign fun p => placeL LB p.2).Assigned := by
  cases b with
  | tied s a x =>
    simp only [Bound.map, Xl.Bound.placeable, Bool.and_eq_true, beq_iff_eq] at hp
    simp [Bound.reassign, Bound.map, Bound.Assigned, hp.1]
  | fixedUse i a =>
    simp only [Bound.map, Xl.Bound.placeable, beq_iff_eq] at hp
    simp [Bound.reassign, Bound.map, Bound.Assigned, hp, Xl.placeL_reg]
  | fixedDef i x =>
    simp only [Bound.map, Xl.Bound.placeable, beq_iff_eq] at hp
    simp [Bound.reassign, Bound.map, Bound.Assigned, hp, Xl.placeL_reg]
  | fixedTied i a x =>
    simp only [Bound.map, Xl.Bound.placeable, Bool.and_eq_true, beq_iff_eq] at hp
    simp [Bound.reassign, Bound.map, Bound.Assigned, hp.1, hp.2, Xl.placeL_reg]
  | _ => trivial

theorem PartShape.of_map {ap : APart (VReg × Loc)} {o : X86.Op} (ho : ap.1 = o)
    {defs : List (VReg × Loc)} {args : List (XArg (VReg × Loc))}
    (h : bindRow o defs args = some (ap.2.map (Bound.map Prod.fst))) : PartShape ap := by
  obtain ⟨bs₁, bs₂, he, hs, hi, hr⟩ := bindRow_shape h
  obtain ⟨cs₁, cs₂, hcs, rfl, rfl⟩ := List.map_eq_append_iff.1 he
  subst ho
  refine ⟨⟨cs₁, cs₂, hcs, ?_, ?_⟩, ?_⟩
  · simpa [List.map_map, Function.comp_def] using hs
  · simpa [List.map_map, Function.comp_def] using hi
  · intro b hb
    have := hr (b.map Prod.fst) (List.mem_map_of_mem hb)
    simpa using this

/-! ## The simulation -/

theorem nodup_map_on {β γ : Type} {f : β → γ} :
    ∀ {l : List β}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => by simp
  | x :: l, h, hn => by
      rw [List.nodup_cons] at hn
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nodup_map_on (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)) hn.2⟩
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      exact hn.1 ((h x List.mem_cons_self y (List.mem_cons_of_mem _ hy) e.symm) ▸ hy)

theorem optGuard_eq {p : Prop} [Decidable p] (h : p) : optGuard p = some () := by
  simp [optGuard, guard, h]

theorem partArgs_eq (place : Loc → Option GPR) (part : X86.Op × List (Bound Loc)) :
    Xl.partArgs place part = (part.1, ·) <$> slotArgs place Xl.Loc.reg? part.2 := by
  unfold Xl.partArgs
  cases slotArgs place Xl.Loc.reg? part.2 <;> simp

theorem execBound_sim {parts : List (X86.Op × List (Bound (VReg × Loc)))} {zf : Bool}
    {ρ ρ' : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem mem' : X86.Memory} {ctx : Word}
    {flags : X86.ByteEval.Flags}
    (hf : RowFacts parts zf fr) (hsize : regs.size = 16)
    (hagree : ∀ u ∈ (parts.flatMap Prod.snd).flatMap Bound.uses,
      ∃ w, ρ[u.1]? = some w ∧ Xl.read regs fr u.2 = some w)
    (hxv : execBound (parts.map fun q => (q.1, q.2.map (Bound.map Prod.fst))) ρ mem ctx =
      some (ρ', mem', flags)) :
    ∃ regs' fr', Xl.execBound (parts.map fun q => (q.1, q.2.map (Bound.map Prod.snd))) regs fr mem ctx zf =
        some (regs', fr', mem', flags) ∧ regs'.size = 16 ∧ Xl.Frame.SameCtl fr fr' ∧
      (∀ d ∈ (parts.flatMap Prod.snd).flatMap Bound.defs,
        ∃ w, ρ'[d.1]? = some w ∧ Xl.read regs' fr' d.2 = some w) ∧
      (∀ x, x ∉ ((parts.flatMap Prod.snd).flatMap Bound.defs).map (·.1) → ρ'[x]? = ρ[x]?) ∧
      (∀ l, l ∉ ((parts.flatMap Prod.snd).flatMap Bound.defs).map (·.2) →
        Xl.read regs' fr' l = Xl.read regs fr l) := by
  obtain ⟨aps, margs₁, core₁, core₁', hmap, hass, hargs₁, hrun₁, hcm, hmem', hctx₁, htk, htkS, huse₁,
    hout₁, hρ'⟩ := execBound_spec (f := Prod.fst) hxv
  obtain ⟨hshape, hstack, hwide, hnarrow, honly, hplace, haddr, huseR, hdefOk, hdefLocs, hdefRegs,
    hearly, hcells⟩ := hf
  -- The paired bounds and their assignment
  obtain ⟨AB, hAB⟩ : ∃ AB, aps.flatMap (fun q => q.2) = AB := ⟨_, rfl⟩
  rw [hAB] at htk htkS huse₁ hout₁ hρ'
  have hPB : parts.flatMap Prod.snd = AB.map (Bound.map Prod.fst) := by
    rw [← hAB, ← hmap, List.flatMap_map, List.map_flatMap]
  rw [hPB] at hplace haddr huseR hdefOk hdefLocs hdefRegs hearly hcells hagree ⊢
  rw [uses_map_flat] at huseR hearly hagree
  rw [defs_map_flat] at hdefOk hdefLocs hdefRegs ⊢
  simp only [List.map_map] at hdefLocs hdefRegs ⊢
  -- Xl's view
  obtain ⟨LB, hLBdef⟩ : ∃ LB, (AB.map (Bound.map Prod.fst)).map (Bound.map Prod.snd) = LB := ⟨_, rfl⟩
  rw [hLBdef] at hcells
  have hLB : (parts.map fun q => (q.1, q.2.map (Bound.map Prod.snd))).flatMap Prod.snd = LB := by
    rw [← hLBdef, ← hPB, List.flatMap_map, List.map_flatMap]
  let g : VReg × Loc → GPR := fun p => placeL LB p.2
  let val : VReg × Loc → Word := fun p => (ρ[p.1]?).getD 0
  have hmemAB : ∀ b ∈ AB, b.map Prod.fst ∈ AB.map (Bound.map Prod.fst) := fun b hb =>
    List.mem_map_of_mem hb
  have hplace' : ∀ b ∈ AB, Xl.Bound.placeable ((b.map Prod.fst).map Prod.snd) = true := fun b hb =>
    hplace _ (hmemAB b hb)
  have huseLoc : ∀ q ∈ AB.flatMap Bound.uses, q.1.2 ∈ xlLocs LB := fun q hq => by
    rw [← hLBdef]
    exact use_mem_xlLocs (by rw [uses_map_flat]; exact List.mem_map_of_mem hq)
  have hdefLoc : ∀ q ∈ AB.flatMap Bound.defs, q.1.2 ∈ xlLocs LB := fun q hq => by
    rw [← hLBdef]
    exact def_mem_xlLocs (by rw [defs_map_flat]; exact List.mem_map_of_mem hq)
  -- Locations of the Xl bounds
  have hlocs : ∀ l ∈ xlLocs LB, (∃ q ∈ AB.flatMap Bound.uses, q.1.2 = l) ∨
      (∃ q ∈ AB.flatMap Bound.defs, q.1.2 = l) := by
    intro l hl
    rw [← hLBdef] at hl
    rcases mem_xlLocs hl with ⟨u, hu, rfl⟩ | ⟨d, hd, rfl⟩
    · rw [uses_map_flat] at hu
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hu
      exact .inl ⟨q, hq, rfl⟩
    · rw [defs_map_flat] at hd
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hd
      exact .inr ⟨q, hq, rfl⟩
  have hreserved : ∀ l ∈ xlLocs LB, ∀ r, l = .reg r → Xl.reserved r = false := by
    intro l hl r hr
    rcases hlocs l hl with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact huseR q.1 (List.mem_map_of_mem hq) r hr
    · have := hdefOk q.1 (List.mem_map_of_mem hq)
      rw [hr] at this
      exact this
  -- Zeroed registers
  obtain ⟨zeroed, hzdef⟩ : ∃ z, Xl.zeroedRegs (parts.map fun q => (q.1, q.2.map (Bound.map Prod.snd))) zf = z :=
    ⟨_, rfl⟩
  have hzeroed : ∀ r ∈ zeroed, ∃ b ∈ AB, b.narrowOutput = true ∧ ∃ q ∈ b.defs, q.1.2 = .reg r := by
    intro r hr
    rw [← hzdef] at hr
    unfold Xl.zeroedRegs at hr
    split at hr
    · simp only [List.mem_filterMap, List.mem_flatMap, List.mem_filter] at hr
      obtain ⟨l, ⟨b, ⟨hb, hn⟩, hl⟩, hlr⟩ := hr
      cases hlast : (parts.map fun q => (q.1, q.2.map (Bound.map Prod.snd))).getLast? with
      | none => simp [hlast] at hb
      | some lp =>
        rw [hlast] at hb
        simp only [Option.map_some, Option.getD_some] at hb
        have hlp : lp ∈ parts.map fun q => (q.1, q.2.map (Bound.map Prod.snd)) :=
          List.mem_of_getLast? hlast
        have hb' : b ∈ LB := by
          rw [← hLB]; exact List.mem_flatMap.2 ⟨lp, hlp, hb⟩
        rw [← hLBdef] at hb'
        obtain ⟨b₁, hb₁, rfl⟩ := List.mem_map.1 hb'
        obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb₁
        rw [Bound.defs_map, Bound.defs_map] at hl
        obtain ⟨q₁, hq₁, rfl⟩ := List.mem_map.1 hl
        obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.1 hq₁
        refine ⟨b₀, hb₀, by simpa using hn, q₀, hq₀, ?_⟩
        cases h : q₀.1.2 <;> simp [h, Xl.Loc.reg?] at hlr
        rw [hlr]
    · simp at hr
  have hzNamed : ∀ r ∈ zeroed, r ∈ xlNamed LB := by
    intro r hr
    obtain ⟨b, hb, -, q, hq, hqr⟩ := hzeroed r hr
    exact Xl.mem_xlNamed.2 (hqr ▸ hdefLoc q (List.mem_flatMap.2 ⟨b, hb, hq⟩))
  have hzUse : ∀ r ∈ zeroed, ∀ q ∈ AB.flatMap Bound.uses, q.1.2 ≠ .reg r := by
    intro r hr q hq e
    obtain ⟨b, hb, hn, d, hd, hdr⟩ := hzeroed r hr
    refine hearly (b.map Prod.fst) (hmemAB b hb) (by simpa using hn) d.1 ?_ q.1 (List.mem_map_of_mem hq)
      (e.trans hdr.symm)
    rw [Bound.defs_map]; exact List.mem_map_of_mem hd
  -- Guards
  have hG1 : LB.all Xl.Bound.placeable = true := by
    rw [List.all_eq_true]
    intro b hb
    rw [← hLBdef] at hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    exact hplace b' hb'
  have hG2 : (xlNamed LB).all (!Xl.reserved ·) = true := by
    rw [List.all_eq_true]
    intro r hr
    simp [hreserved _ (Xl.mem_xlNamed.1 hr) r rfl]
  have hG4 : ∃ vs, Xl.readAll regs fr (LB.flatMap Bound.uses) = some vs := by
    unfold Xl.readAll
    refine mapM_isSome fun l hl => ?_
    rw [← hLBdef, uses_map_flat, uses_map_flat] at hl
    simp only [List.map_map, List.mem_map] at hl
    obtain ⟨q, hq, rfl⟩ := hl
    obtain ⟨w, -, hw⟩ := hagree q.1 (List.mem_map_of_mem hq)
    simp [hw]
  have hG5 : (zeroed.all fun r => !(LB.flatMap Bound.uses).contains (.reg r)) = true := by
    rw [List.all_eq_true]
    intro r hr
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
    cases hc : (LB.flatMap Bound.uses).contains (.reg r)
    · rfl
    · have hm := List.contains_iff_mem.1 hc
      rw [← hLBdef, uses_map_flat, uses_map_flat] at hm
      simp only [List.map_map, List.mem_map] at hm
      obtain ⟨q, hq, e⟩ := hm
      exact absurd e (hzUse r hr q hq)
  -- The Xl placement of each operand
  have hplaceIn : ∀ l ∈ xlLocs LB, Xl.placeIn (xlTable LB) l = some (placeL LB l) :=
    fun l hl => Xl.placeIn_locs hcells hl
  -- Machine arguments
  have hmargs : (parts.map fun q => (q.1, q.2.map (Bound.map Prod.snd))).mapM
      (Xl.partArgs (Xl.placeIn (xlTable LB))) = (aps.map (APart.reassign g)).mapM APart.args := by
    rw [← hmap, List.map_map]
    refine (mapM_map_congr (h := fun ap => (ap.reassign g).args) fun ap hap => ?_).trans
      (mapM_map_congr fun _ _ => rfl).symm
    rw [partArgs_eq, APart.reassign_args]
    simp only [Function.comp_apply]
    congr 1
    have hsub : ∀ b ∈ ap.2, b ∈ AB := fun b hb => hAB ▸ List.mem_flatMap.2 ⟨ap, hap, hb⟩
    rw [Xl.slotArgs_rename (h := placeL LB)]
    · congr 1
      simp only [List.map_map]
      refine List.map_congr_left fun b _ => ?_
      simp only [Function.comp_apply, Bound.map_map]
      rfl
    · intro b hb x hx
      obtain ⟨b₁, hb₁, rfl⟩ := List.mem_map.1 hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb₁
      rw [Xl.Bound.placed_map, Xl.Bound.placed_map] at hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      apply hplaceIn
      rcases List.mem_append.1 (Xl.Bound.placed_sub hq) with hq' | hq'
      · exact huseLoc q (List.mem_flatMap.2 ⟨b', hsub b' hb', hq'⟩)
      · exact hdefLoc q (List.mem_flatMap.2 ⟨b', hsub b' hb', hq'⟩)
    · intro b hb x hx
      obtain ⟨b₁, hb₁, rfl⟩ := List.mem_map.1 hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb₁
      rw [Xl.Bound.addrRegs_map, Xl.Bound.addrRegs_map] at hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      have hcell := haddr (b'.map Prod.fst) (hmemAB b' (hsub b' hb')) q.1 (by
        rw [Xl.Bound.addrRegs_map]; exact List.mem_map_of_mem hq)
      cases h : q.1.2 <;> simp [h, Loc.isCell] at hcell
      simp [Xl.Loc.reg?, Xl.placeL_reg]
  obtain ⟨margs₂, hmargs₂⟩ : ∃ margs₂, (aps.map (APart.reassign g)).mapM APart.args = some margs₂ := by
    refine mapM_isSome fun ap hap => ?_
    obtain ⟨ap₀, hap₀, rfl⟩ := List.mem_map.1 hap
    have hsub : ∀ b ∈ ap₀.2, b ∈ AB := fun b hb => hAB ▸ List.mem_flatMap.2 ⟨ap₀, hap₀, hb⟩
    rw [APart.reassign_args]
    obtain ⟨as, has⟩ := slotArgs_isSome (bs := ap₀.2.map (Bound.map fun q => g q.1)) (by
      intro b hb r hr
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      rw [Xl.Bound.addrRegs_map] at hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      have hcell := haddr (b'.map Prod.fst) (hmemAB b' (hsub b' hb')) q.1 (by
        rw [Xl.Bound.addrRegs_map]; exact List.mem_map_of_mem hq)
      cases h : q.1.2 with
      | reg r' =>
        have := hreserved _ (huseLoc q (List.mem_flatMap.2 ⟨b', hsub b' hb',
          Xl.Bound.addrRegs_sub hq⟩)) r' h
        simp only [g, h, Xl.placeL_reg]
        intro e; subst e; simp [Xl.reserved] at this
      | _ => simp [h, Loc.isCell] at hcell)
    simp [has]
  -- Each part, as a part of `parts`
  have hpart : ∀ ap ∈ aps, (ap.1, ap.2.map (Bound.map Prod.fst)) ∈ parts := fun ap hap => by
    rw [← hmap]; exact List.mem_map_of_mem (f := fun q => (q.1, q.2.map (Bound.map Prod.fst))) hap
  have hinAB : ∀ b ∈ AB, ∃ ap ∈ aps, b ∈ ap.2 := fun b hb => by
    rw [← hAB] at hb; exact List.mem_flatMap.1 hb
  -- Registers of uses are never the context register
  have hne15 : ∀ q ∈ AB.flatMap Bound.uses, q.2 ≠ .r15 := by
    intro q hq
    obtain ⟨b, hb, hqb⟩ := List.mem_flatMap.1 hq
    by_cases hfu : q ∈ b.freeUses
    · have hk : q.2 ∈ b.taken := by
        rw [Bound.taken_eq]; exact List.mem_map_of_mem (List.mem_append_left _ hfu)
      intro e
      exact Xl.r15_not_scratch (e ▸ (htkS b hb q.2 hk).1)
    · obtain ⟨ap, hap, hbap⟩ := hinAB b hb
      have hloc := fixed_use_loc (hass ap hap b hbap) (hplace' b hb) hqb hfu
      have := huseR q.1 (List.mem_map_of_mem hq) q.2 hloc
      intro e; rw [e] at this; simp [Xl.reserved] at this
  -- The rows
  have hsh : ∀ ap ∈ aps, PartShape ap ∧ (X86.desc ap.1).stack = .none ∧
      ∀ i ∈ (X86.desc ap.1).implicit, i.role.reads = true ∨ Wide i.width := by
    intro ap hap
    obtain ⟨defs, args, hb⟩ := hshape _ (hpart ap hap)
    exact ⟨PartShape.of_map rfl hb, hstack _ (hpart ap hap), hwide _ (hpart ap hap)⟩
  have hasg : ∀ ap ∈ aps, ∀ b ∈ ap.2, b.Assigned ∧ (b.reassign g).Assigned := fun ap hap b hb =>
    ⟨hass ap hap b hb, reassign_assigned (hplace' b (hAB ▸ List.mem_flatMap.2 ⟨ap, hap, hb⟩))⟩
  have hlast : ∀ ap ∈ aps.dropLast, ap.2.flatMap Bound.defs = [] := by
    intro ap hap
    have hm : (ap.1, ap.2.map (Bound.map Prod.fst)) ∈ parts.dropLast := by
      rw [← hmap, ← List.map_dropLast]; exact List.mem_map_of_mem (f := fun q => (q.1, q.2.map (Bound.map Prod.fst))) hap
    have := honly _ hm
    simp only at this
    rw [defs_map_flat, List.map_eq_nil_iff] at this
    exact this
  have hn₂ : ((AB.flatMap Bound.defs).map fun q => g q.1).Nodup := by
    have : ((AB.flatMap Bound.defs).map fun q => g q.1) =
        ((AB.flatMap Bound.defs).map fun q => q.1.2).map (placeL LB) := by
      rw [List.map_map]; rfl
    rw [this]
    refine nodup_map_on (fun x hx y hy e => Xl.placeL_inj hcells ?_ ?_ e) ?_
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx; exact hdefLoc q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy; exact hdefLoc q hq
    · simpa [Function.comp_def] using hdefLocs
  have hn₁ : ((AB.flatMap Bound.defs).map (·.2)).Nodup :=
    defRegs_nodup (g := g) (fun b hb => by
        obtain ⟨ap, hap, hbap⟩ := hinAB b hb; exact hass ap hap b hbap)
      (fun b hb => reassign_assigned (hplace' b hb)) htk
      (fun b hb r hr b' hb' i hi => (htkS b hb r hr).2 b' hb' i hi) hn₂
  have hzero₂ : ∀ b ∈ AB, b.narrowOutput = true → ∀ q ∈ b.defs,
      Xl.rowRegisters regs fr ctx (xlTable LB) zeroed (g q.1) = 0 := by
    intro b hb hn q hq
    obtain ⟨ap, hap, hbap⟩ := hinAB b hb
    have hq' : q.1 ∈ (b.map Prod.fst).defs := by rw [Bound.defs_map]; exact List.mem_map_of_mem hq
    obtain ⟨r, hr⟩ := narrow_loc_reg (hplace' b hb) (by simpa using hn) hq'
    obtain ⟨hzf, hlastp⟩ := hnarrow _ (hpart ap hap) (b.map Prod.fst)
      (List.mem_map_of_mem hbap) (by simpa using hn)
    have hrz : r ∈ zeroed := by
      rw [← hzdef]
      unfold Xl.zeroedRegs
      simp only [hzf, ↓reduceIte, List.getLast?_map, hlastp, Option.map_some, Option.getD_some]
      simp only [List.mem_filterMap, List.mem_flatMap, List.mem_filter]
      refine ⟨.reg r, ⟨(b.map Prod.fst).map Prod.snd, ⟨List.mem_map_of_mem (List.mem_map_of_mem hbap),
        by simpa using hn⟩, ?_⟩, rfl⟩
      rw [Bound.defs_map, ← hr]; exact List.mem_map_of_mem hq'
    have hres := hdefOk q.1 (List.mem_map_of_mem (List.mem_flatMap.2 ⟨b, hb, hq⟩))
    rw [hr] at hres
    have hr15 : r ≠ .r15 := by intro e; subst e; simp [WriteOk, Xl.reserved] at hres
    show Xl.rowRegisters regs fr ctx (xlTable LB) zeroed (placeL LB q.1.2) = 0
    rw [hr, Xl.placeL_reg]
    exact Xl.rowRegisters_zeroed hr15 hrz
  rw [execRows_eq] at hrun₁
  obtain ⟨core₂', hrun₂, hmemc, hdefc⟩ := rows_corr (val := val) (g := g)
    (c₂ := ⟨Xl.rowRegisters regs fr ctx (xlTable LB) zeroed, mem⟩) hargs₁ hmargs₂ hsh hasg hlast
    hcm (by rw [hctx₁]; exact (Xl.rowRegisters_r15 regs fr ctx (xlTable LB) zeroed).symm)
    (by
      rw [hAB]
      intro q hq
      obtain ⟨w, hw, hc⟩ := huse₁ q hq (hne15 q hq)
      rw [hc]; simp [val, hw])
    (by
      rw [hAB]
      intro q hq
      obtain ⟨w, hw, hread⟩ := hagree q.1 (List.mem_map_of_mem hq)
      show Xl.rowRegisters regs fr ctx (xlTable LB) zeroed (placeL LB q.1.2) = val q.1
      rw [Xl.rowRegisters_use hcells hzNamed (huseLoc q hq)
        (fun r hr => huseR q.1 (List.mem_map_of_mem hq) r hr)
        (fun r hr hrz => hzUse r hrz q hq hr), hread]
      simp [val, hw])
    (by
      rw [hAB]
      intro b hb hn q hq
      rw [Bound.narrowOutput_defs hn] at hq
      exact hout₁ b hb q hq)
    (by rw [hAB]; exact hzero₂)
    (by rw [hAB]; exact hn₁) (by rw [hAB]; exact hn₂) hrun₁
  rw [hAB] at hdefc
  -- Writing back
  have hrb := readback_eq (place := Xl.placeIn (xlTable LB)) (h := placeL LB) (bs := AB.map (Bound.map Prod.fst))
    hplace (fun b hb d hd => by
      apply hplaceIn
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      rw [Bound.defs_map] at hd
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hd
      exact hdefLoc q (List.mem_flatMap.2 ⟨b', hb', hq⟩)) (fun r => Xl.placeL_reg LB r)
  rw [hLBdef, defs_map_flat] at hrb
  obtain ⟨regs', fr', hwb, hs', hctl, hread, hother⟩ := writeBacks_spec (core := core₂')
    (L := (AB.flatMap Bound.defs).map fun q => (q.1.2, placeL LB q.1.2)) hsize
    (by simpa [List.map_map, Function.comp_def] using hdefLocs)
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hdefOk q.1 (List.mem_map_of_mem hq))
  refine ⟨regs', fr', ?_, hs', hctl, ?_, ?_, ?_⟩
  · obtain ⟨vs, hvs⟩ := hG4
    rw [Xl.execBound_eq, hLB, hzdef, optGuard_eq hG1, Option.bind_some, optGuard_eq hG2,
      Option.bind_some, optGuard_eq hcells, Option.bind_some, hvs, Option.bind_some, optGuard_eq hG5,
      Option.bind_some, hmargs, hmargs₂, Option.bind_some, execRows_eq, hrun₂, Option.bind_some]
    simp only [hrb, List.map_map, Function.comp_def] at hwb ⊢
    rw [hwb, Option.bind_some, hmem', hmemc]
  · intro d hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hd
    refine ⟨core₁'.readReg q.2, ?_, ?_⟩
    · rw [hρ']
      apply readBack_mem (by simpa [List.map_map, Function.comp_def] using hdefRegs)
        (q.1.1, q.2) (List.mem_map.2 ⟨q, hq, rfl⟩)
    · rw [hread (q.1.2, placeL LB q.1.2) (List.mem_map.2 ⟨q, hq, rfl⟩), hdefc q hq]
  · intro x hx
    rw [hρ']
    exact readBack_other (by simpa [List.map_map, Function.comp_def] using hx)
  · intro l hl
    exact hother l (by simpa [List.map_map, Function.comp_def] using hl)

end IxCC.Xv
