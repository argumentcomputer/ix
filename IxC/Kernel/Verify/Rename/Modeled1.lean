module

public import IxC.Kernel.Verify.Rename.Native4
public import IxC.Kernel.Inductives.Modeled

@[expose] public section

/-!
# The renaming walk through the modeled route: the iota theorems (step 7.3, chunk (iii))

The modeled install compares a block against its `_model` artifacts under a
block-local renaming `ρ` (a member's name to its model's). An input renaming
commutes with `ρ` on good keys (`ρ' (k.map f) = (ρ k).map f`), so the renamed
run compares the renamed artifacts under the renamed `ρ'`. Here: the lookups
(`Env.findCV?`), `renameConsts` at a renaming that commutes on good keys, the
equality-head tests, and the canonical rule's `iota_j` check (`checkIotaThm`).
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

/-! ## Lookups and small tests -/

theorem EnvRel.findCV? {env : Env md} {env' : Env md'} (h : EnvRel P f env env') {k : Key md}
    (hk : k.Good P) : env'.findCV? (k.map f) = (env.findCV? k).map (ConstantVal.mapKeys f) := by
  simp only [Env.findCV?, h.find k hk]
  cases env.find? k <;> simp

theorem EnvRel.findCV?_good {env : Env md} {env' : Env md'} (h : EnvRel P f env env') {k : Key md}
    (hk : k.Good P) {cv : ConstantVal md} (hcv : env.findCV? k = some cv) : cv.Good P := by
  simp only [Env.findCV?, Option.map_eq_some_iff] at hcv
  obtain ⟨c, hc, rfl⟩ := hcv
  exact (h.good k c hk hc).toConstantVal

theorem getD_mapKeys_bvar (l : List (Expr md)) (i k : Nat) :
    (l.map (Expr.mapKeys f)).getD i (.bvar k) = (l.getD i (.bvar k)).mapKeys f := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem getLastD_mapKeys_bvar (l : List (Expr md)) (k : Nat) :
    (l.map (Expr.mapKeys f)).getLastD (.bvar k) = (l.getLastD (.bvar k)).mapKeys f := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs => simpa [List.getLastD] using ih

theorem Expr.GoodList.getLastD {l : List (Expr md)} (h : Expr.GoodList P l) (k : Nat) :
    (l.getLastD (.bvar k)).Good P := by
  rw [List.getLastD_eq_getLast?]
  cases hl : l.getLast? with
  | none => trivial
  | some e => exact h e (List.mem_of_getLast? hl)

@[simp] theorem isEqHead_mapKeys (e : Expr md) : isEqHead (e.mapKeys f) = isEqHead e := by
  rcases e with _ | _ | _ | ⟨c, _ | ⟨_, _ | _⟩⟩ | _ | _ | _ | _ | _ | _ <;>
    simp [isEqHead, Expr.mapKeys, eqName]

@[simp] theorem eqHeadLevel_mapKeys (e : Expr md) : eqHeadLevel (e.mapKeys f) = eqHeadLevel e := by
  rcases e with _ | _ | _ | ⟨c, _ | ⟨_, _ | _⟩⟩ | _ | _ | _ | _ | _ | _ <;>
    simp [eqHeadLevel, Expr.mapKeys]

/-! ## `renameConsts` at a renaming that commutes on good keys -/

theorem mapKeys_renameConsts_good {ρ : Key md → Key md} {ρ' : Key md' → Key md'}
    (hρ : ∀ k : Key md, k.Good P → (ρ k).map f = ρ' (k.map f)) :
    ∀ {e : Expr md}, e.Good P → (e.renameConsts ρ).mapKeys f = (e.mapKeys f).renameConsts ρ' := by
  intro e he
  induction e with
  | const n us =>
    simp only [Expr.renameConsts, Expr.mapKeys, hρ n he]
  | proj s i x ih =>
    simp only [Expr.Good] at he
    simp only [Expr.renameConsts, Expr.mapKeys, ih he.2]
  | _ => simp_all [Expr.renameConsts, Expr.mapKeys, Expr.Good]

theorem Expr.Good.renameConsts {ρ : Key md → Key md} (hρ : ∀ k : Key md, k.Good P → (ρ k).Good P) :
    ∀ {e : Expr md}, e.Good P → (e.renameConsts ρ).Good P := by
  intro e he
  induction e with
  | const n us => exact hρ n he
  | proj s i x ih =>
    simp only [Expr.Good] at he
    exact ⟨he.1, ih he.2⟩
  | _ => simp_all [Ix.Kernel.Expr.renameConsts, Expr.Good]

/-- **The block-local renaming** of the modeled install: a member's name to
its model's. -/
abbrev modelRen (blockNames : List (Key md)) : Key md → Key md := fun n =>
  if blockNames.contains n then auxKey n .model else n

theorem modelRen_map (hf : InjOn f P) {blockNames : List (Key md)}
    (hb : ∀ k ∈ blockNames, k.Good P) :
    ∀ k : Key md, k.Good P →
      (modelRen blockNames k).map f = modelRen (blockNames.map (Key.map f)) (k.map f) := by
  intro k hk
  simp only [modelRen, contains_map_ren hf hb hk]
  split <;> rfl

theorem modelRen_good {blockNames : List (Key md)} :
    ∀ k : Key md, k.Good P → (modelRen blockNames k).Good P := by
  intro k hk
  simp only [modelRen]
  split
  · exact hk
  · exact hk

/-! ## The iota theorems -/

theorem checkIotaSidesTy_sim (mode : CheckMode) (hops : OpsSim P f ops ops') {envS : Env md}
    {envS' : Env md'} (hE : EnvRel P f envS envS') (depth : Nat) {alphaS lhsS rhsS : Expr md}
    (ha : alphaS.Good P) (hl : lhsS.Good P) (hr : rhsS.Good P) (ℓA : Level) (cvName : Key md) :
    SimV (checkIotaSidesTy mode ops envS depth alphaS lhsS rhsS ℓA cvName)
      (checkIotaSidesTy mode ops' envS' depth (alphaS.mapKeys f) (lhsS.mapKeys f) (rhsS.mapKeys f) ℓA
        (cvName.map f)) := by
  unfold checkIotaSidesTy
  refine SimE.bind (hops.inferType hE depth lhsS hl) (fun tl htl => ?_)
  refine SimE.bind (hops.isDefEq hE depth tl alphaS htl ha) (fun c _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.bind (hops.inferType hE depth rhsS hr) (fun tr htr => ?_)
  refine SimE.bind (hops.isDefEq hE depth tr alphaS htr ha) (fun c _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT ())
  refine SimE.bind (hops.inferType hE depth alphaS ha) (fun tα htα => ?_)
  have hs : (Expr.sort ℓA : Expr md').mapKeys (fun i => i) = Expr.sort ℓA := rfl
  refine SimE.bind (hops.isDefEq hE depth tα (.sort ℓA) htα trivial) (fun c _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT ()) (fun _ => SimE.throw')

end Ix.Kernel
