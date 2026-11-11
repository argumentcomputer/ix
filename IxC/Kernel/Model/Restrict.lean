module

public import IxC.Kernel.Denotes

@[expose] public section

/-!
# Restricting a model to a sub-environment

`Denotes` reads an environment at two places only: a constant's entry
(`find?`, for its level parameters) and a structure's projection table
(`findProj?`). So a model of `env` is a model of any sub-environment `env'` that
agrees with it there, on the keys the stored types and the definitions' values
mention: `Model.restrict`.

The keys a term mentions are `Expr.RefsIn`'s; a literal is read through its
constructor form, whose keys are `LitKeys`. The consistency statement uses this
for the claimed sub-environment (`IxVM.Consistency.claimedEnv`,
`Ix/IxVM/Consistency/Restrict.lean`).
-/

namespace Ix.Kernel

universe w

/-- **Every constant key `e` mentions satisfies `K`.** A literal mentions none
here; `Denotes` reads it through its constructor form (`LitKeys`). -/
def Expr.RefsIn (K : Key md → Prop) : Expr md → Prop
  | .bvar _ => True
  | .fvar _ _ => True
  | .sort _ => True
  | .const n _ => K n
  | .app f a => f.RefsIn K ∧ a.RefsIn K
  | .lam ty b _ => ty.RefsIn K ∧ b.RefsIn K
  | .forallE ty b _ => ty.RefsIn K ∧ b.RefsIn K
  | .letE ty v b _ => ty.RefsIn K ∧ v.RefsIn K ∧ b.RefsIn K
  | .lit _ => True
  | .proj _ _ e => e.RefsIn K

/-- The keys the literals' constructor forms mention satisfy `K`. -/
def LitKeys (K : Key md → Prop) : Prop :=
  K natZeroName ∧ K natSuccName ∧ K stringOfListName ∧ K listNilName ∧
    K listConsName ∧ K charName ∧ K charOfNatName

theorem refsIn_natLit {K : Key md → Prop} (hl : LitKeys K) :
    ∀ n : Nat, (natLitToConstructor n : Expr md).RefsIn K
  | 0 => hl.1
  | _ + 1 => And.intro hl.2.1 trivial

theorem refsIn_strLit {K : Key md → Prop} (hl : LitKeys K) (s : String) :
    (strLitToConstructor s : Expr md).RefsIn K := by
  obtain ⟨-, -, hso, hnil, hcons, hchar, hofNat⟩ := hl
  unfold strLitToConstructor
  simp only [Expr.RefsIn]
  refine And.intro hso ?_
  generalize s.toList = l
  induction l with
  | nil => simp only [List.foldr, Expr.RefsIn]; exact And.intro hnil hchar
  | cons c cs ih =>
    simp only [List.foldr, Expr.RefsIn] at ih ⊢
    exact ⟨⟨⟨hcons, hchar⟩, by first | exact ⟨hofNat, trivial⟩ | exact hofNat⟩, ih⟩

variable {V : Type w} [SetTheory V]

/-- **Denotation transports to an environment that agrees on the keys a term
mentions and on projection tables.** -/
theorem Denotes.mono_env {cval : Key md → (LevelParam → Nat) → V} {env env' : Env md}
    {φ : LevelParam → Nat} {K : Key md → Prop}
    (hfind : ∀ n, K n → env'.find? n = env.find? n)
    (hproj : ∀ T i, env'.findProj? T i = env.findProj? T i)
    (hlit : LitKeys K) :
    ∀ {ρ : BVarIdx → V} {e : Expr md} {v : V},
      Denotes cval env φ ρ e v → e.RefsIn K → Denotes cval env' φ ρ e v := by
  intro ρ e v h
  induction h with
  | bvar => exact fun _ => .bvar
  | sort => exact fun _ => .sort
  | const hf hlen =>
    intro hK
    exact .const (by rw [hfind _ hK]; exact hf) hlen
  | app _ _ ihf iha =>
    intro hK
    simp only [Expr.RefsIn] at hK
    exact .app (ihf hK.1) (iha hK.2)
  | lam _ _ hP ihA ihF =>
    intro hK
    simp only [Expr.RefsIn] at hK
    exact .lam (ihA hK.1) (fun x hx => ihF x hx hK.2) hP
  | pi _ _ hP ihA ihB =>
    intro hK
    simp only [Expr.RefsIn] at hK
    exact .pi (ihA hK.1) (fun x hx => ihB x hx hK.2) hP
  | proj_table ht _ ih =>
    intro hK
    simp only [Expr.RefsIn] at hK
    exact .proj_table (by rw [hproj]; exact ht) (ih hK)
  | proj_fst ht _ ih =>
    intro hK
    simp only [Expr.RefsIn] at hK
    exact .proj_fst (by rw [hproj]; exact ht) (ih hK)
  | proj_snd ht _ ih =>
    intro hK
    simp only [Expr.RefsIn] at hK
    exact .proj_snd (by rw [hproj]; exact ht) (ih hK)
  | natLit _ ih => exact fun _ => .natLit (ih (refsIn_natLit hlit _))
  | strLit _ ih => exact fun _ => .strLit (ih (refsIn_strLit hlit _))

/-- A constant's denotation in the sub-environment is its denotation in the
environment, at a key where they agree. -/
theorem Denotes.const_back {cval : Key md → (LevelParam → Nat) → V} {env env' : Env md}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {n : Key md} {us : List Level} {F : V}
    (hfind : env'.find? n = env.find? n)
    (h : Denotes cval env' φ ρ (.const n us) F) : Denotes cval env φ ρ (.const n us) F := by
  cases h with
  | const hf hlen => exact .const (by rw [← hfind]; exact hf) hlen

/-- **A model restricts** to a sub-environment that agrees with the environment
on the keys its stored types and definitions' values mention (and on `False`
and `Eq`) and on projection tables. -/
def Model.restrict {env env' : Env md} (M : Model V env) {K : Key md → Prop}
    (hfind : ∀ n, K n → env'.find? n = env.find? n)
    (hproj : ∀ T i, env'.findProj? T i = env.findProj? T i)
    (hlit : LitKeys K)
    (hsub : ∀ c ∈ env'.consts, c ∈ env.consts)
    (htype : ∀ c ∈ env'.consts, c.toConstantVal.type.RefsIn K)
    (hvalue : ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ env'.consts →
      value.RefsIn K)
    (hF : K falseName) (hE : K eqName) : Model V env' where
  cval := M.cval
  mem := fun c hc φ ρ =>
    let ⟨T, hT, hm⟩ := M.mem c (hsub c hc) φ ρ
    ⟨T, Denotes.mono_env hfind hproj hlit hT (htype c hc), hm⟩
  false_empty := fun φ ρ F h => M.false_empty φ ρ F (Denotes.const_back (hfind _ hF) h)
  eq_equality := fun u φ ρ E A a b h =>
    M.eq_equality u φ ρ E A a b (Denotes.const_back (hfind _ hE) h)
  defn_value := fun cv value hint hc φ ρ =>
    Denotes.mono_env hfind hproj hlit (M.defn_value cv value hint (hsub _ hc) φ ρ)
      (hvalue cv value hint hc)

end Ix.Kernel
