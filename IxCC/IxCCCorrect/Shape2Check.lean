import IxCCCorrect.Shape2

/-!
# The decision for milestone M2 (`IxCCCorrect.Shape2Check`)

`IxCCCorrect.Shape2`'s judgments, decided from an untrusted certificate
(`Cert`): the instances `(constant, levels, shape)` the program uses, the
constructor list of each enumeration, and the table of data entries. Beyond
`IxCCCorrect.Shape1Check`: `projRes` in `synth` (E6), `dataCtorOk` (a constructor of a
data entry), `casesOk` with the inductive's parameters, and `ctorsOk`/`structOk` on
each entry of the table.

* `synth`: the shapes a term can have in a context, as a list (a constant may have
  several instances); a λ needs the expected shape. `synth_sound`: each is a
  derivation.
* `entryOk`: one instance resolves in the program as its shape says, by kind of
  constant (primitive, equation hint, `csimp`, `case` entry, definition, constructor,
  recursor). `entryOk_sound`: `ConstOk`.
* `certOk`: every instance and every enumeration. `sigOk_of_cert`: `SigOk`.
* `neverWrong_of_cert_nat`, `neverWrong_of_cert_enum`: `NeverWrong` from the
  decision, at a root that returns a `Nat` or a value of an enumeration.

The checks read a shape apart with total, unproved helpers (`argAt`, `resAfter`,
`unarrowD`) and then compare the shape with the one the rule builds (`decide`), so
soundness rests on the comparison only.
-/

set_option autoImplicit false

namespace IxCC.Correct.Shape2

open IxCC.Src
open IxCC.Sem (Result Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-- The certificate: the instances, and each enumeration's constructors in index
order. -/
structure Cert where
  insts : List (CId × Levels × Shape)
  enums : List (CId × List CId)
  datas : List DataDecl

/-- The constructors a certificate lists for an enumeration: its first entry's. -/
def lookupEnum : List (CId × List CId) → CId → Option (List CId)
  | [], _ => none
  | (I', cs) :: l, I => if I = I' then some cs else lookupEnum l I

theorem mem_of_lookupEnum : ∀ (l : List (CId × List CId)) (I : CId) (cs : List CId),
    lookupEnum l I = some cs → (I, cs) ∈ l
  | [], I, cs, h => by simp [lookupEnum] at h
  | (I', cs') :: l, I, cs, h => by
    simp only [lookupEnum] at h
    split at h
    · rename_i hI
      simp only [Option.some.injEq] at h
      subst hI
      subst h
      exact List.mem_cons.2 (.inl rfl)
    · exact List.mem_cons.2 (.inr (mem_of_lookupEnum l I cs h))

/-- The signature a certificate states. -/
def Cert.sig (cert : Cert) : Sig where
  inst c ls σ := (c, ls, σ) ∈ cert.insts
  enums := lookupEnum cert.enums
  datas d := cert.datas[d]?

/-- The shapes the certificate lists for a constant at given levels. -/
def instsOf : List (CId × Levels × Shape) → CId → Levels → List Shape
  | [], _, _ => []
  | (c', ls', σ) :: l, c, ls =>
    if c' = c ∧ ls' = ls then σ :: instsOf l c ls else instsOf l c ls

theorem mem_instsOf : ∀ (l : List (CId × Levels × Shape)) (c : CId) (ls : Levels) (σ : Shape),
    σ ∈ instsOf l c ls → (c, ls, σ) ∈ l
  | [], _, _, _, h => by simp [instsOf] at h
  | (c', ls', σ') :: l, c, ls, σ, h => by
    simp only [instsOf] at h
    split at h
    · rename_i hcond
      obtain ⟨h1, h2⟩ := hcond
      subst h1
      subst h2
      rcases List.mem_cons.1 h with h' | h'
      · subst h'
        exact List.mem_cons.2 (.inl rfl)
      · exact List.mem_cons.2 (.inr (mem_instsOf l _ _ σ h'))
    · exact List.mem_cons.2 (.inr (mem_instsOf l c ls σ h))

/-! ## Shape synthesis -/

/-- What an application returns, per shape of the function: at an irrelevant argument
the domain must be `irr`; at a relevant one the argument must check against it. -/
def appRes (irrArg : Bool) (argOk : Shape → Bool) : Shape → List Shape
  | .fn σ τ => if irrArg then (if σ = .irr then [τ] else []) else (if argOk σ then [τ] else [])
  | _ => []

theorem mem_appRes {irrArg : Bool} {argOk : Shape → Bool} {s τ : Shape}
    (h : τ ∈ appRes irrArg argOk s) :
    ∃ σ, s = .fn σ τ ∧ ((irrArg = true ∧ σ = .irr) ∨ (irrArg = false ∧ argOk σ = true)) := by
  cases s with
  | fn σ τ' =>
    cases irrArg with
    | true =>
      by_cases hσ : σ = .irr
      · simp [appRes, hσ] at h
        exact ⟨σ, by rw [h], .inl ⟨rfl, hσ⟩⟩
      · simp [appRes, hσ] at h
    | false =>
      by_cases ha : argOk σ = true
      · simp [appRes, ha] at h
        exact ⟨σ, by rw [h], .inr ⟨rfl, ha⟩⟩
      · simp [appRes, ha] at h
  | nat => simp [appRes] at h
  | enum _ => simp [appRes] at h
  | data _ => simp [appRes] at h
  | irr => simp [appRes] at h

/-- What a projection returns, per shape of its subject: field `i` of a structure's
entry of the projected inductive. -/
def projRes (datas : List DataDecl) (s : CId) (i : Nat) : Shape → List Shape
  | .data d =>
    match datas[d]? with
    | some D =>
      if D.struct = true ∧ D.ind = s then
        match D.ctors with
        | [e] => (e.2[i]?).toList
        | _ => []
      else []
    | none => []
  | _ => []

theorem mem_projRes {datas : List DataDecl} {s : CId} {i : Nat} {σ τ : Shape}
    (h : τ ∈ projRes datas s i σ) :
    ∃ (d : Nat) (D : DataDecl) (c : CId) (fl : List Shape), σ = .data d ∧ datas[d]? = some D ∧
      D.struct = true ∧ D.ind = s ∧ D.ctors = [(c, fl)] ∧ fl[i]? = some τ := by
  cases σ with
  | data d =>
    simp only [projRes] at h
    cases hD : datas[d]? with
    | none => simp [hD] at h
    | some D =>
      simp only [hD] at h
      split at h
      · rename_i hc
        cases hct : D.ctors with
        | nil => simp [hct] at h
        | cons e rest =>
          cases rest with
          | cons _ _ => simp [hct] at h
          | nil =>
            obtain ⟨c, fl⟩ := e
            simp [hct] at h
            exact ⟨d, D, c, fl, rfl, by first | exact hD | rfl, hc.1, hc.2, by first | exact hct | rfl, h⟩
      · simp at h
  | nat => simp [projRes] at h
  | enum _ => simp [projRes] at h
  | irr => simp [projRes] at h
  | fn _ _ => simp [projRes] at h

/-- What is known of the shape of a term being synthesized: nothing, all of it, or
(for a λ in function position) its domain. -/
inductive Exp where
  | none
  | full (σ : Shape)
  | dom (σ : Shape)

/-- **Shape synthesis at levels `ls`**: the shapes of a term in a context. Only a λ
reads what is expected: the whole shape (a λ passed as an argument, a body checked
against an instance), or the domain (a λ applied on the spot: the domain is the
argument's shape). -/
def synth (insts : List (CId × Levels × Shape)) (datas : List DataDecl) (ls : Levels) :
    List Shape → Term → Exp → List Shape
  | Γ, .var i, _ => (Γ[i]?).toList
  | _, .natLit _, _ => [.nat]
  | _, .sort _, _ => [.irr]
  | _, .pi _ _ _, _ => [.irr]
  | _, .const c us, _ => instsOf insts c (us.map (evalUniv ls))
  | Γ, .app f a _ r, _ =>
    (match f with
      | .lam _ _ _ =>
        (if r.irrAt ls then [Shape.irr] else synth insts datas ls Γ a .none).flatMap fun σ =>
          synth insts datas ls Γ f (.dom σ)
      | _ => synth insts datas ls Γ f .none).flatMap fun s =>
      appRes (r.irrAt ls) (fun σ => decide (σ ∈ synth insts datas ls Γ a (.full σ))) s
  | Γ, .lam b _ body, e =>
    match e with
    | .full (.fn σ τ) =>
      if b.propWhen.allowsBeta ls then
        if τ ∈ synth insts datas ls (σ :: Γ) body (.full τ) then [.fn σ τ] else []
      else []
    | .dom σ =>
      if b.propWhen.allowsBeta ls then
        (synth insts datas ls (σ :: Γ) body .none).map fun τ => .fn σ τ
      else []
    | _ => []
  | Γ, .letE _ _ r _ v body, e =>
    if r.irrAt ls then synth insts datas ls (.irr :: Γ) body e
    else (synth insts datas ls Γ v .none).flatMap fun σ => synth insts datas ls (σ :: Γ) body e
  | Γ, .proj s i e', _ => (synth insts datas ls Γ e' .none).flatMap fun σ => projRes datas s i σ
  | _, _, _ => []

/-- A synthesized shape is a derivation. -/
theorem synth_sound (cert : Cert) (ls : Levels) : ∀ (t : Term) (Γ : List Shape)
    (e : Exp) (σ : Shape), σ ∈ synth cert.insts cert.datas ls Γ t e → HasShape cert.sig ls Γ t σ := by
  intro t
  induction t with
  | var i =>
    intro Γ e σ h
    simp [synth] at h
    exact .var h
  | sort u =>
    intro Γ e σ h
    simp [synth] at h
    subst h
    exact .sort
  | const c us =>
    intro Γ e σ h
    simp only [synth] at h
    exact .const (mem_instsOf _ _ _ _ h)
  | app f a m r ihf iha =>
    intro Γ e σ h
    simp only [synth] at h
    obtain ⟨s, hs, hτ⟩ := List.mem_flatMap.1 h
    have hf : HasShape cert.sig ls Γ f s := by
      cases f with
      | lam b d body =>
        obtain ⟨σ₀, -, hs'⟩ := List.mem_flatMap.1 hs
        exact ihf _ _ _ hs'
      | var _ => exact ihf _ _ _ hs
      | sort _ => exact ihf _ _ _ hs
      | const _ _ => exact ihf _ _ _ hs
      | app _ _ _ _ => exact ihf _ _ _ hs
      | pi _ _ _ => exact ihf _ _ _ hs
      | letE _ _ _ _ _ _ => exact ihf _ _ _ hs
      | proj _ _ _ => exact ihf _ _ _ hs
      | natLit _ => exact ihf _ _ _ hs
      | strLit _ => exact ihf _ _ _ hs
    obtain ⟨σ', rfl, hc⟩ := mem_appRes hτ
    rcases hc with ⟨hr, rfl⟩ | ⟨hr, ha⟩
    · exact .appIrr hr hf
    · exact .app hr hf (iha _ _ _ (of_decide_eq_true ha))
  | lam b d body _ ihb =>
    intro Γ e σ h
    cases e with
    | none => simp [synth] at h
    | dom σ' =>
      simp only [synth] at h
      split at h
      · rename_i hb
        obtain ⟨τ', hbody, rfl⟩ := List.mem_map.1 h
        exact .lam hb (ihb _ _ _ hbody)
      · simp at h
    | full s =>
      cases s with
      | fn σ' τ' =>
        simp only [synth] at h
        split at h
        · rename_i hb
          split at h
          · rename_i hbody
            simp only [List.mem_singleton] at h
            subst h
            exact .lam hb (ihb _ _ _ hbody)
          · simp at h
        · simp at h
      | nat => simp [synth] at h
      | data _ => simp [synth] at h
      | enum _ => simp [synth] at h
      | irr => simp [synth] at h
  | pi b d c _ _ =>
    intro Γ e σ h
    simp [synth] at h
    subst h
    exact .pi
  | letE nonDep lm r ty v body _ ihv ihb =>
    intro Γ e σ h
    simp only [synth] at h
    split at h
    · rename_i hr
      exact .letIrr hr (ihb _ _ _ h)
    · rename_i hr
      obtain ⟨σ', hv, hb⟩ := List.mem_flatMap.1 h
      exact .letE (by simpa using hr) (ihv _ _ _ hv) (ihb _ _ _ hb)
  | proj s i e' ihe =>
    intro Γ e σ h
    simp only [synth] at h
    obtain ⟨σ', hs, hτ⟩ := List.mem_flatMap.1 h
    obtain ⟨d, D, c, fl, rfl, hD, hst, hind, hct, hi⟩ := mem_projRes hτ
    exact .proj (ihe _ _ _ hs) hD hst hind hct hi
  | natLit n =>
    intro Γ e σ h
    simp [synth] at h
    subst h
    exact .natLit
  | strLit s =>
    intro Γ e σ h
    simp [synth] at h

/-! ## Reading a shape apart (unproved helpers; the checks compare afterwards) -/

/-- The `n`-th argument shape, or `irr`. -/
def argAt : Nat → Shape → Shape
  | 0, .fn a _ => a
  | n + 1, .fn _ b => argAt n b
  | _, _ => .irr

/-- What is left after `n` arrows. -/
def resAfter : Nat → Shape → Shape
  | n + 1, .fn _ b => resAfter n b
  | _, τ => τ

/-- The first `n` argument shapes. -/
def argsUpTo : Nat → Shape → List Shape
  | n + 1, .fn a b => a :: argsUpTo n b
  | _, _ => []

/-! ## Special heads -/

/-- The parameter count and the field shapes of the constructors of what a recursor of
`ind` scrutinises at shape `σ`. -/
def fldsOf (p : Program) (cert : Cert) (ind : CId) : Shape → Option (Nat × List (List Shape))
  | .nat => if (some ind == p.known.nat) then some (0, [[], [.nat]]) else none
  | .enum I =>
    if I = ind then (lookupEnum cert.enums I).map fun cs => (0, cs.map fun _ => []) else none
  | .data d =>
    match cert.datas[d]? with
    | some D => if D.ind = ind then some (D.params.length, D.ctors.map fun e => e.2) else none
    | none => none
  | _ => none

theorem fldsOf_sound {p : Program} {cert : Cert} {ind : CId} {σ : Shape} {np : Nat}
    {flds : List (List Shape)} (h : fldsOf p cert ind σ = some (np, flds)) :
    ScrutOk p cert.sig σ ind np flds := by
  cases σ with
  | nat =>
    simp only [fldsOf] at h
    split at h
    · rename_i hN
      cases h
      exact .nat hN
    · cases h
  | enum I =>
    simp only [fldsOf] at h
    split at h
    · rename_i hI
      subst hI
      cases he : lookupEnum cert.enums I with
      | none =>
        rw [he] at h
        cases h
      | some cs =>
        rw [he] at h
        cases h
        exact .enum (sig := cert.sig) he
    · cases h
  | data d =>
    simp only [fldsOf] at h
    cases hD : cert.datas[d]? with
    | none => simp [hD] at h
    | some D =>
      simp only [hD] at h
      split at h
      · rename_i hI
        subst hI
        cases h
        exact .data (sig := cert.sig) hD
      · cases h
  | irr => simp [fldsOf] at h
  | fn _ _ => simp [fldsOf] at h

def isOrdinary : Option RecKind → Bool
  | some .ordinary => true
  | _ => false

theorem isOrdinary_sound {k : Option RecKind} (h : isOrdinary k = true) : k = some .ordinary := by
  cases k with
  | none => simp [isOrdinary] at h
  | some kind =>
    cases kind with
    | ordinary => rfl
    | subsingleton _ _ => simp [isOrdinary] at h
    | empty => simp [isOrdinary] at h

/-- A `Bool`-valued primitive: its result is an enumeration of the certificate that
lists both pinned `Bool` constructors. -/
def predOk (p : Program) (cert : Cert) (op : PrimOp) (σ : Shape) : Bool :=
  cert.enums.any fun e =>
    decide (lookupEnum cert.enums e.1 = some e.2) &&
      decide (σ = arrows (List.replicate op.arity .nat) (.enum e.1)) &&
      decide (p.known.boolTrue ∈ e.2.map some) && decide (p.known.boolFalse ∈ e.2.map some)

theorem predOk_sound {p : Program} {cert : Cert} {op : PrimOp} {σ : Shape} {ls : Levels}
    (hp : op.isPredicate = true) (h : predOk p cert op σ = true) :
    ∃ σs τ, HeadOk p cert.sig (.prim op) ls σs τ ∧ σ = arrows σs τ := by
  obtain ⟨⟨B, cs⟩, -, he⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨⟨⟨hB, hσ⟩, ht⟩, hf⟩ := he
  obtain ⟨t, htm, ht'⟩ := List.mem_map.1 ht
  obtain ⟨f, hfm, hf'⟩ := List.mem_map.1 hf
  exact ⟨_, _, .pred op ls B t f cs hp ht'.symm hf'.symm hB htm hfm, hσ⟩

/-- A `case` entry at an instance `params → irr → σ₁ → minors → τ`. -/
def casesOk (p : Program) (cert : Cert) (σ : Shape) (ind : CId) (np nmin ni : Nat) : Bool :=
  match fldsOf p cert ind (argAt (np + 1) σ) with
  | some (np', flds) =>
    decide (np' = (argsUpTo np σ).length) && decide ((argsUpTo np σ).length = np) &&
      decide (ni = 0) && decide (nmin = flds.length) &&
      decide (σ = arrows (argsUpTo np σ ++ (.irr :: argAt (np + 1) σ :: flds.map fun fl =>
        arrows fl (resAfter (np + 2 + flds.length) σ))) (resAfter (np + 2 + flds.length) σ))
  | none => false

theorem casesOk_sound {p : Program} {cert : Cert} {ls : Levels} {σ : Shape} {c r : CId}
    {s kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hres : p.table.resolveOf c = some (.case r))
    (hdecl : p.decl? r = some (.recr s kk lv np nmot nmin ni ind rules ty))
    (hkind : p.table.recKindOf r = some .ordinary)
    (h : casesOk p cert σ ind np nmin ni = true) :
    ∃ σs τ, HeadOk p cert.sig (.cases c) ls σs τ ∧ σ = arrows σs τ := by
  unfold casesOk at h
  cases hf : fldsOf p cert ind (argAt (np + 1) σ) with
  | none => simp [hf] at h
  | some pr =>
    obtain ⟨np', flds⟩ := pr
    simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hnp', hlen⟩, hni⟩, hnm⟩, hσ⟩ := h
    have hsc := fldsOf_sound hf
    rw [hnp'] at hsc
    rw [hni, hnm, ← hlen] at hdecl
    exact ⟨_, _, .cases c r ls (argsUpTo np σ) _ ind flds _ s kk lv nmot rules ty hres hdecl
      hkind hsc, hσ⟩

/-- Each rule of a recursor peels its λs and its body has the result shape in the
environment F2 builds, from rule `j` on. -/
def rulesOk (insts : List (CId × Levels × Shape)) (datas : List DataDecl) (ls : Levels)
    (rules : List Rule)
    (ms : List Shape) (τ : Shape) : Nat → List (List Shape) → Bool
  | _, [] => true
  | j, fl :: rest =>
    (match rules[j]? with
      | some rule =>
        match peelLams (1 + ms.length + fl.length) rule.rhs with
        | some body =>
          decide (τ ∈ synth insts datas ls (fl.reverse ++ (ms.reverse ++ [.irr])) body (.full τ))
        | none => false
      | none => false) && rulesOk insts datas ls rules ms τ (j + 1) rest

theorem rulesOk_sound {cert : Cert} {ls : Levels} {rules : List Rule} {ms : List Shape}
    {τ : Shape} : ∀ (flds : List (List Shape)) (j0 : Nat),
    rulesOk cert.insts cert.datas ls rules ms τ j0 flds = true →
    ∀ (i : Nat) (fl : List Shape), flds[i]? = some fl → ∃ (rule : Rule) (body : Term),
      rules[j0 + i]? = some rule ∧ peelLams (1 + ms.length + fl.length) rule.rhs = some body ∧
      HasShape cert.sig ls (fl.reverse ++ (ms.reverse ++ [.irr])) body τ
  | [], _, _, i, fl, hi => by simp at hi
  | fl0 :: rest, j0, h, i, fl, hi => by
    simp only [rulesOk, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      cases hr : rules[j0]? with
      | none => simp [hr] at h1
      | some rule =>
        cases hp : peelLams (1 + ms.length + fl0.length) rule.rhs with
        | none => simp [hr, hp] at h1
        | some body =>
          simp only [hr, hp, decide_eq_true_eq] at h1
          exact ⟨rule, body, rfl, hp, synth_sound cert ls _ _ _ _ h1⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨rule, body, hr, hp, hb⟩ := rulesOk_sound rest (j0 + 1) h2 i fl hi
      have e : j0 + (i + 1) = j0 + 1 + i := by omega
      rw [e]
      exact ⟨rule, body, hr, hp, hb⟩

/-- A recursor at an instance `irr → minors → σ₁ → τ`. -/
def recrOk (p : Program) (cert : Cert) (ls : Levels) (σ : Shape) (ind : CId)
    (np nmot nmin ni : Nat) (rules : List Rule) : Bool :=
  match fldsOf p cert ind (argAt (1 + nmin) σ) with
  | some (np', flds) =>
    decide (np' = 0) && decide (np = 0) && decide (nmot = 1) && decide (ni = 0) &&
      decide ((argsUpTo nmin (resAfter 1 σ)).length = nmin) &&
      decide (σ = arrows (.irr :: (argsUpTo nmin (resAfter 1 σ) ++ [argAt (1 + nmin) σ]))
        (resAfter (2 + nmin) σ)) &&
      rulesOk cert.insts cert.datas ls rules (argsUpTo nmin (resAfter 1 σ))
        (resAfter (2 + nmin) σ) 0 flds
  | none => false

theorem recrOk_sound {p : Program} {cert : Cert} {ls : Levels} {σ : Shape} {r : CId}
    {s kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hdecl : p.decl? r = some (.recr s kk lv np nmot nmin ni ind rules ty))
    (hkind : p.table.recKindOf r = some .ordinary)
    (h : recrOk p cert ls σ ind np nmot nmin ni rules = true) :
    ∃ σs τ, HeadOk p cert.sig (.recr r) ls σs τ ∧ σ = arrows σs τ := by
  unfold recrOk at h
  cases hf : fldsOf p cert ind (argAt (1 + nmin) σ) with
  | none => simp [hf] at h
  | some pr =>
    obtain ⟨np', flds⟩ := pr
    simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hnp', hnp⟩, hnm⟩, hni⟩, hlen⟩, hσ⟩, hrules⟩ := h
    have hsc := fldsOf_sound hf
    rw [hnp'] at hsc
    rw [hnp, hnm, hni, ← hlen] at hdecl
    refine ⟨_, _, .recr r ls _ ind flds (argsUpTo nmin (resAfter 1 σ)) _ s kk lv rules ty hdecl
      hkind hsc ?_, hσ⟩
    intro j fl hfl
    obtain ⟨rule, body, hr, hp, hb⟩ := rulesOk_sound flds 0 hrules j fl hfl
    rw [Nat.zero_add] at hr
    exact ⟨rule, body, hr, hp, hb⟩

/-! ## Constructors -/

def zeroOk (p : Program) (c : CId) (np nf : Nat) (σ : Shape) : Bool :=
  decide (np = 0) && decide (nf = 0) && (some c == p.known.natZero) && decide (σ = .nat)

def succOk (p : Program) (c : CId) (np nf : Nat) (σ : Shape) : Bool :=
  decide (np = 0) && decide (nf = 1) && (some c == p.known.natSucc) &&
    !(some c == p.known.natZero) && decide (σ = .fn .nat .nat)

def enumCtorOk (cert : Cert) (c : CId) (σ : Shape) : Bool :=
  cert.enums.any fun e =>
    decide (lookupEnum cert.enums e.1 = some e.2) && decide (c ∈ e.2) && decide (σ = .enum e.1)

/-- A constructor of a data entry, at the instance `params → fields → data d`. -/
def dataCtorOk (cert : Cert) (c : CId) (σ : Shape) : Bool :=
  (List.range cert.datas.length).any fun d =>
    match cert.datas[d]? with
    | some D => D.ctors.any fun e =>
        decide (e.1 = c) && decide ((argsUpTo D.params.length σ).length = D.params.length) &&
          decide (σ = arrows (argsUpTo D.params.length σ ++ e.2) (.data d))
    | none => false

theorem dataCtorOk_sound {p : Program} {cert : Cert} {c : CId} {σ : Shape} {ls : Levels}
    (h : dataCtorOk cert c σ = true) :
    ∃ σs τ, HeadOk p cert.sig (.ctor c) ls σs τ ∧ σ = arrows σs τ := by
  obtain ⟨d, -, hd⟩ := List.any_eq_true.1 h
  cases hD : cert.datas[d]? with
  | none => simp [hD] at hd
  | some D =>
    simp only [hD] at hd
    obtain ⟨⟨c', fl⟩, hmem, he⟩ := List.any_eq_true.1 hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨hc, hlen⟩, hσ⟩ := he
    subst hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
    exact ⟨_, _, .ctor c' ls d D j _ fl hD hj hlen, hσ⟩

/-- A data entry's constructors are constructors of its inductive, from index `j`
on, with the entry's parameter count and their own field counts. -/
def ctorsOk (p : Program) (D : DataDecl) : Nat → List (CId × List Shape) → Bool
  | _, [] => true
  | j, e :: rest =>
    (match p.decl? e.1 with
      | some (.ctor _ _ ind cidx np nf _) =>
        decide (ind = D.ind) && decide (cidx = j) && decide (np = D.params.length) &&
          decide (nf = e.2.length) && !(some e.1 == p.known.natZero) &&
          !(some e.1 == p.known.natSucc)
      | _ => false) && ctorsOk p D (j + 1) rest

theorem ctorsOk_sound {p : Program} {D : DataDecl} : ∀ (cs : List (CId × List Shape)) (j0 : Nat),
    ctorsOk p D j0 cs = true → ∀ (j : Nat) (c : CId) (fl : List Shape), cs[j]? = some (c, fl) →
    ∃ s lv ty, p.decl? c = some (.ctor s lv D.ind (j0 + j) D.params.length fl.length ty) ∧
      (some c == p.known.natZero) = false ∧ (some c == p.known.natSucc) = false
  | [], _, _, j, c, fl, hj => by simp at hj
  | e0 :: cs, j0, h, j, c, fl, hj => by
    simp only [ctorsOk, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      cases hd : p.decl? c with
      | none => simp [hd] at h1
      | some d =>
        cases d with
        | ctor s lv ind cidx np nf ty =>
          simp only [hd, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
          obtain ⟨⟨⟨⟨⟨h1a, h1b⟩, h1c⟩, h1d⟩, hz⟩, hs⟩ := h1
          exact ⟨s, lv, ty, by rw [h1a, h1b, h1c, h1d, Nat.add_zero], hz, hs⟩
        | _ => simp [hd] at h1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      obtain ⟨s, lv, ty, hd, hz, hs⟩ := ctorsOk_sound cs (j0 + 1) h2 j c fl hj
      have e : j0 + 1 + j = j0 + (j + 1) := by omega
      rw [e] at hd
      exact ⟨s, lv, ty, hd, hz, hs⟩

/-- An entry E6 may project is of an inductive with exactly its one constructor. -/
def structOk (p : Program) (D : DataDecl) : Bool :=
  !D.struct ||
    (match D.ctors, p.decl? D.ind with
      | [e], some (.induct _ _ _ _ _ [c']) => decide (c' = e.1)
      | _, _ => false)

theorem structOk_sound {p : Program} {D : DataDecl} (h : structOk p D = true)
    (hst : D.struct = true) (c : CId) (fl : List Shape) (hct : D.ctors = [(c, fl)]) :
    ∃ s lv np ni ty, p.decl? D.ind = some (.induct s lv np ni ty [c]) := by
  unfold structOk at h
  rw [hst, hct] at h
  cases hd : p.decl? D.ind with
  | none => simp [hd] at h
  | some dd =>
    cases dd with
    | induct s lv np ni ty ctors =>
      cases ctors with
      | nil => simp [hd] at h
      | cons c' rest =>
        cases rest with
        | cons _ _ => simp [hd] at h
        | nil =>
          simp [hd] at h
          subst h
          exact ⟨s, lv, np, ni, ty, by first | exact hd | rfl⟩
    | _ => simp [hd] at h

/-- An enumeration's listed constructors are its constructors, from index `i` on. -/
def enumOk (p : Program) (I : CId) : Nat → List CId → Bool
  | _, [] => true
  | i, c :: cs =>
    (match p.decl? c with
      | some (.ctor _ _ ind cidx np nf _) =>
        decide (ind = I) && decide (cidx = i) && decide (np = 0) && decide (nf = 0) &&
          !(some c == p.known.natZero) && !(some c == p.known.natSucc)
      | _ => false) && enumOk p I (i + 1) cs

theorem enumOk_sound {p : Program} {I : CId} : ∀ (cs : List CId) (i0 : Nat),
    enumOk p I i0 cs = true → ∀ (i : Nat) (c : CId), cs[i]? = some c →
    ∃ s lv ty, p.decl? c = some (.ctor s lv I (i0 + i) 0 0 ty) ∧
      (some c == p.known.natZero) = false ∧ (some c == p.known.natSucc) = false
  | [], _, _, i, c, hi => by simp at hi
  | c0 :: cs, i0, h, i, c, hi => by
    simp only [enumOk, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      cases hd : p.decl? c0 with
      | none => simp [hd] at h1
      | some d =>
        cases d with
        | ctor s lv ind cidx np nf ty =>
          simp only [hd, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
          obtain ⟨⟨⟨⟨⟨h1a, h1b⟩, h1c⟩, h1d⟩, hz⟩, hs⟩ := h1
          exact ⟨s, lv, ty, by rw [h1a, h1b, h1c, h1d, Nat.add_zero], hz, hs⟩
        | _ => simp [hd] at h1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨s, lv, ty, hd, hz, hs⟩ := enumOk_sound cs (i0 + 1) h2 i c hi
      have e : i0 + 1 + i = i0 + (i + 1) := by omega
      rw [e] at hd
      exact ⟨s, lv, ty, hd, hz, hs⟩

/-! ## One instance, and the certificate -/

/-- **One instance resolves in the program as its shape says** (`ConstOk`, decided). -/
def entryOk (p : Program) (cert : Cert) (c : CId) (ls : Levels) (σ : Shape) : Bool :=
  match p.table.resolveOf c with
  | some (.prim op) =>
    if op.isPredicate then predOk p cert op σ
    else decide (σ = arrows (List.replicate op.arity .nat) .nat)
  | some (.eqn _ body) => decide (σ ∈ synth cert.insts cert.datas ls [] body (.full σ))
  | some (.csimp g us _) => decide ((g, us.map (evalUniv ls), σ) ∈ cert.insts)
  | some (.case r) =>
    match p.decl? r with
    | some (.recr _ _ _ np _ nmin ni ind _ _) =>
      isOrdinary (p.table.recKindOf r) && casesOk p cert σ ind np nmin ni
    | _ => false
  | some (.word _ _ _) => false
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) => decide (σ ∈ synth cert.insts cert.datas ls [] v (.full σ))
    | some (.ctor _ _ _ _ np nf _) =>
      zeroOk p c np nf σ || succOk p c np nf σ || enumCtorOk cert c σ || dataCtorOk cert c σ
    | some (.recr _ _ _ np nmot nmin ni ind rules _) =>
      isOrdinary (p.table.recKindOf c) && recrOk p cert ls σ ind np nmot nmin ni rules
    | _ => false

theorem entryOk_sound {p : Program} {cert : Cert} {c : CId} {ls : Levels} {σ : Shape}
    (h : entryOk p cert c ls σ = true) : ConstOk p cert.sig c ls σ := by
  unfold entryOk at h
  cases hres : p.table.resolveOf c with
  | some res =>
    cases res with
    | prim op =>
      simp only [hres] at h
      by_cases hp : op.isPredicate = true
      · simp only [hp, ↓reduceIte] at h
        obtain ⟨σs, τ, hh, rfl⟩ := predOk_sound (ls := ls) hp h
        exact .head (.prim hres) hh
      · have hp' : op.isPredicate = false := by simpa using hp
        simp only [hp', Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h
        subst h
        exact .head (.prim hres) (.prim op ls hp')
    | csimp g us thm =>
      simp only [hres, decide_eq_true_eq] at h
      exact .body (.csimp hres) (.const h)
    | eqn thm body =>
      simp only [hres, decide_eq_true_eq] at h
      exact .body (.eqn hres) (synth_sound cert ls _ _ _ _ h)
    | case r =>
      simp only [hres] at h
      cases hd : p.decl? r with
      | none => simp [hd] at h
      | some d =>
        cases d with
        | recr s kk lv np nmot nmin ni ind rules ty =>
          simp only [hd, Bool.and_eq_true] at h
          obtain ⟨hk, hc⟩ := h
          obtain ⟨σs, τ, hh, rfl⟩ :=
            casesOk_sound (ls := ls) hres hd (isOrdinary_sound hk) hc
          exact .head (.cases hres) hh
        | _ => simp [hd] at h
    | word w op thm => simp [hres] at h
  | none =>
    simp only [hres] at h
    cases hd : p.decl? c with
    | none => simp [hd] at h
    | some d =>
      cases d with
      | defn kind safety lvls ty v =>
        cases kind <;> cases safety <;>
          simp only [hd, Bool.false_eq_true, decide_eq_true_eq] at h
        exact .body (.defn hres hd) (synth_sound cert ls _ _ _ _ h)
      | ctor s lv ind cidx np nf ty =>
        simp only [hd, Bool.or_eq_true] at h
        rcases h with ((hz | hs) | he) | hdt
        · simp only [zeroOk, Bool.and_eq_true, decide_eq_true_eq] at hz
          obtain ⟨⟨⟨h1, h2⟩, hz'⟩, h3⟩ := hz
          rw [h1, h2] at hd
          subst h3
          exact .zero hres hd hz'
        · simp only [succOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hs
          obtain ⟨⟨⟨⟨h1, h2⟩, hs'⟩, hz'⟩, h3⟩ := hs
          rw [h1, h2] at hd
          subst h3
          exact .head (.ctor hres hd) (.succ c ls s lv ind cidx ty hd hz' hs')
        · obtain ⟨⟨I, cs⟩, -, he'⟩ := List.any_eq_true.1 he
          simp only [Bool.and_eq_true, decide_eq_true_eq] at he'
          obtain ⟨⟨hI, hc⟩, h3⟩ := he'
          subst h3
          exact .enumCtor hres hI hc
        · obtain ⟨σs, τ, hh, rfl⟩ := dataCtorOk_sound (p := p) (ls := ls) hdt
          exact .head (.ctor hres hd) hh
      | recr s kk lv np nmot nmin ni ind rules ty =>
        simp only [hd, Bool.and_eq_true] at h
        obtain ⟨hk, hr⟩ := h
        obtain ⟨σs, τ, hh, rfl⟩ := recrOk_sound (ls := ls) hd (isOrdinary_sound hk) hr
        exact .head (.recr hres hd) hh
      | _ => simp [hd] at h

/-- **The check**: every instance resolves as its shape says, and every enumeration's
constructors are as listed. -/
def certOk (p : Program) (cert : Cert) : Bool :=
  (cert.insts.all fun e => entryOk p cert e.1 e.2.1 e.2.2) &&
    (cert.enums.all fun e => enumOk p e.1 0 e.2) &&
    (cert.datas.all fun D => ctorsOk p D 0 D.ctors && structOk p D)

theorem sigOk_of_cert {p : Program} {cert : Cert} (h : certOk p cert = true) :
    SigOk p cert.sig := by
  unfold certOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hi, he⟩, hdt⟩ := h
  have hD : ∀ (d : Nat) (D : DataDecl), cert.datas[d]? = some D →
      ctorsOk p D 0 D.ctors = true ∧ structOk p D = true := by
    intro d D hd
    have := List.all_eq_true.1 hdt D (List.mem_iff_getElem?.2 ⟨d, hd⟩)
    simpa using this
  refine ⟨fun c ls σ hc => entryOk_sound (List.all_eq_true.1 hi (c, ls, σ) hc),
    fun I cs hI i c hic => ?_, fun d D hd j c fl hj => ?_,
    fun d D hd hst c fl hct => structOk_sound (hD d D hd).2 hst c fl hct⟩
  · have hmem := mem_of_lookupEnum _ _ _ hI
    obtain ⟨s, lv, ty, hd, hz, hs⟩ :=
      enumOk_sound cs 0 (List.all_eq_true.1 he (I, cs) hmem) i c hic
    rw [Nat.zero_add] at hd
    exact ⟨s, lv, ty, hd, hz, hs⟩
  · obtain ⟨s, lv, ty, hdc, hz, hs⟩ := ctorsOk_sound D.ctors 0 (hD d D hd).1 j c fl hj
    rw [Nat.zero_add] at hdc
    exact ⟨s, lv, ty, hdc, hz, hs⟩

/-! ## The discharge, from the decision -/

/-- **M1 as a decision, at a `Nat` root.** A certificate that passes `certOk` on the
checked source and lists the instance `Nat → … → Nat → Nat` for root `r`'s constant,
at a root read back as `Nat` (or not read back): the viewed source goes wrong at no
clock on the root's inputs. -/
theorem neverWrong_of_cert_nat {f : Recheck.Front} {cert : Cert}
    (h : certOk f.src cert = true) {r : Nat} {addr : Ixon.Address} {c : CId}
    (hroot : f.src.roots[r]? = some (addr, c)) (ns : List Nat)
    (hc : (c, ([] : Levels), arrows (List.replicate ns.length .nat) .nat) ∈ cert.insts)
    (hty : f.tys r = none ∨ f.tys r = some ({}, .nat)) :
    NeverWrong f.source (r, ns) :=
  neverWrong_of_shape (sig := cert.sig) (ρ := .nat) (sigOk_of_cert h) hroot ns hc (view_nat_ok hty)

/-- **M1 as a decision, at an enumeration root.** As `neverWrong_of_cert_nat`, with
the root's result an enumeration of the certificate each of whose constructors the
root's view reads back (finitely many evaluations of the view). -/
theorem neverWrong_of_cert_enum {f : Recheck.Front} {cert : Cert}
    (h : certOk f.src cert = true) {r : Nat} {addr : Ixon.Address} {c : CId}
    (hroot : f.src.roots[r]? = some (addr, c)) (ns : List Nat) {B : CId} {cs : List CId}
    (hc : (c, ([] : Levels), arrows (List.replicate ns.length .nat) (.enum B)) ∈ cert.insts)
    (hB : lookupEnum cert.enums B = some cs)
    (hcs : ∀ c', c' ∈ cs → (IxCC.Lam.Erase.Input.ofProgram f.src f.checked).lvls c' = 0 ∧
      f.view r (Lang.obs (S := CheckedProgram)
        ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, Value.con c' [] [] []) :
          Lang.Val CheckedProgram)) ≠ none) :
    NeverWrong f.source (r, ns) :=
  neverWrong_of_shape (sig := cert.sig) (ρ := .enum B) (sigOk_of_cert h) hroot ns hc
    (view_enum_ok (sig := cert.sig) hB hcs)

end IxCC.Correct.Shape2
