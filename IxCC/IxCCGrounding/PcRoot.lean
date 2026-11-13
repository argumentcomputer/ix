import IxCCGrounding.WordRoot

/-!
# The Pc family (`IxCCGrounding.PcRoot`, step Pc): `PUnit.casesOn` at its ordinary instances

Every family landed before step Pc refuses a `case` entry whose recursor is of kind
`subsingleton w srcs` (the conjunct `caseRec` admits `ordinary` and `empty` only), and its shape
check asks the family to be never a proposition (`CaseWF.indSort`, `NeverProp`). SrcEval fires such
an entry by its kind **at the instance's levels** (`RecKind.atLevels`): where `w` fails it is
`ordinary` (F5: the major forced, the rule selected by its constructor), where `w` holds it is the
subsingleton branch (the minor selected without forcing the major).

**The Pc family's check `groundCheckWP`** is the word family's (`checkPartsW`) with two conjuncts
replaced: `caseRec` by `caseRecP` (`caseRecPB`: at a `subsingleton`-kind entry, the PUnit shape
`punitShapeB`) and `caseShape` by `caseShapeP` (`caseShapePB`: the landed shape check, without the
sort clause at a `subsingleton`-kind entry). The landed `caseProg` stays: it already reads the shape
at every entry not of kind `empty`. Beside the check, the decided instance condition **`pcInstB`**:
at every instance of the verified instance set whose `case` recursor is of kind `subsingleton w _`,
`w` fails at the instance's levels. So the proposition instance (SrcEval's subsingleton branch) is
refused, never proved; every instance the theorem speaks of fires F5 as an `ordinary` entry does,
and F5's meaning there is the canonicity-free route's (`caseFires_of_agreeWK`: ι at the constructor's
own parameters, agreement from `InstUniform`), which reads no sort clause. No new law.

**The PUnit shape is a restriction, not a premise.** `punitShapeB` asks: no field sources, no
parameter (in the declaration and the shape), no index, one constructor without fields, `w` exactly
the zero condition of the family's stored final sort at the shape's levels (`pwNamed`), and each
constructor's annotation class exactly its stored sort's zero condition. The proof reads none of it
(only that the kind is `ordinary`, `empty` or `subsingleton` with no field source, `KindsP`): the
clauses keep the admitted fragment to the shape measured (`PUnit.casesOn`), narrower than what the
proof covers.

**`rootSound_678AGpWP_of_check`**: `rootSound_678AGpW_of_check`'s statement with `groundCheckWP` for
`groundCheckW` and one more hypothesis, `pcInstB p Inst = true`; the conclusion word for word. The
chain is the word family's over `FundHypsK` (the kind read per instance, `kindAt`):
`rootSound_678ASWP` → `rootSound_678AGWP` → `rootSound_678AGWP_of_check` →
`rootSound_678AGpWP_of_check`. The landed links are untouched.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

/-! ## The check -/

/-- A Src zero condition over positions, read as the kernel's datum over the parameter names `lps`
(`none` when a position is out of range). Both sides of a comparison with `zeronessOf` are then the
kernel's canonical sets, so `==` is agreement at every assignment. -/
def pwNamed (lps : List Nat) : IxCC.Src.PropWhen → Option PropWhen
  | .never => some .never
  | .allZero ps => (ps.mapM fun q => lps[q]?).map PropWhen.ifAllZero

/-- The family's level-parameter names and its stored final sort. -/
def famSort? (env : KEnv) (ind : KKey) : Option (List Nat × Level) :=
  match env.find? ind with
  | some (.indInfo cvD _) => (finalSort cvD.type).map (cvD.levelParams, ·)
  | _ => none

/-- **The PUnit shape's clauses**, by name, at a `case` entry `c` whose recursor `r` is of kind
`subsingleton w srcs`: no field source; no parameter; no index; one constructor without fields;
`w` the family's zero condition at the shape's levels; every constructor of the family in `Sl`
annotated `proof` exactly at its stored sort's zero condition. -/
def punitClauses (p : Program) (env : KEnv) (κ : CId → KKey) (ann : IxCC.Src.Relevance.Ann)
    (Sl : List CId) (c r : CId) (w : IxCC.Src.PropWhen) (srcs : List IxCC.Src.FieldSrc) :
    List (String × Bool) :=
  [("srcs", srcs.isEmpty)] ++
  match caseShape? env (κ c) (κ r), p.decl? r with
  | some sh, some (.recr _ _ _ np _ _ ni ind _ _) =>
    let fam := famSort? env sh.ind
    [("np", np == 0 && sh.nP == 0),
     ("ni", ni == 0),
     ("oneCtorNoField", sh.ctors.map (·.nF) == [0]),
     ("w", match fam with
       | some (fl, s) => pwNamed sh.lps w == some (Level.zeronessOf (Level.subst fl sh.indLevels s))
       | none => false),
     ("class", match fam with
       | some (fl, s) => Sl.all fun c' => match p.decl? c' with
         | some (.ctor _ _ ind' _ _ _ _) => ind' != ind ||
           match constClass ann c', env.find? (κ c') with
           | some (.proof w'), some (.ctorInfo cvC _ _) =>
             pwNamed cvC.levelParams w' ==
               some (Level.zeronessOf (Level.subst fl (cvC.levelParams.map .param) s))
           | _, _ => false
         | _ => true
       | none => false)]
  | none, _ => [("shapeRead", false)]
  | _, _ => [("recrDecl", false)]

/-- **The PUnit shape**: every clause of `punitClauses`. -/
def punitShapeB (p : Program) (env : KEnv) (κ : CId → KKey) (ann : IxCC.Src.Relevance.Ann)
    (Sl : List CId) (c r : CId) (w : IxCC.Src.PropWhen) (srcs : List IxCC.Src.FieldSrc) : Bool :=
  (punitClauses p env κ ann Sl c r w srcs).all (·.2)

/-- **`caseRecP`**: a `case` entry's recursor is of kind `ordinary` or `empty`, or of kind
`subsingleton` in the PUnit shape; and the stored constant has a binder for every argument. -/
def caseRecPB (p : Program) (env : KEnv) (κ : CId → KKey) (ann : IxCC.Src.Relevance.Ann)
    (Sl : List CId) (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    (match p.table.recKindOf r with
      | some .ordinary => true
      | some .empty => true
      | some (.subsingleton w srcs) => punitShapeB p env κ ann Sl c r w srcs
      | none => false) &&
    (match env.find? (κ c) with
      | some ci => decide (p.headArity (.cases c) ≤ kPis ci.toConstantVal.type)
      | none => false)
  | _ => true

/-- **`caseShapeP`**: a `case` entry's stored shape (`caseShapeB`), without the sort clause at an
entry of kind `subsingleton` (`caseStoredWithB` at the clause `true`: the PUnit shape's `w` clause
reads the family's sort instead). -/
def caseShapePB (p : Program) (env : KEnv) (κ : CId → KKey) (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.table.recKindOf r with
    | some .empty => true
    | some (.subsingleton _ _) =>
      match caseShape? env (κ c) (κ r) with
      | some sh => caseStoredWithB (fun _ _ => true) env (κ c) (κ r) sh
      | none => false
    | _ =>
      match caseShape? env (κ c) (κ r) with
      | some sh => caseStoredB env (κ c) (κ r) sh
      | none => false
  | _ => true

/-- **The conjuncts of the Pc family's check**: the word family's, `caseRec` replaced by `caseRecP`
and `caseShape` by `caseShapeP`. -/
def checkPartsWP (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : List (String × Bool) :=
  (checkPartsW p env κ lpsOf ann Sl).map fun nb =>
    if nb.1 = "caseRec" then ("caseRecP", Sl.all (caseRecPB p env κ ann Sl))
    else if nb.1 = "caseShape" then ("caseShapeP", Sl.all (caseShapePB p env κ))
    else nb

/-- **The Pc family's check.** -/
def groundCheckWP (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  (checkPartsWP p env κ lpsOf ann Sl).all (·.2)

/-- **The instance condition**: at every instance of `Inst` whose `case` recursor is of kind
`subsingleton w _`, `w` fails at the instance's levels (the kind there is `ordinary`). -/
def pcInstB (p : Program) (Inst : List (CId × Levels)) : Bool :=
  Inst.all fun x => match p.table.resolveOf x.1 with
    | some (.case r) => match p.table.recKindOf r with
      | some (.subsingleton w _) => !w.holds x.2
      | _ => true
    | _ => true

/-! ## What the check and the instance condition give -/

/-- The kinds the Pc family admits at a `case` entry's recursor: `ordinary`, `empty`, or
`subsingleton` with no field source. -/
def KindsP (p : Program) (r : CId) : Prop :=
  p.table.recKindOf r = some .ordinary ∨ p.table.recKindOf r = some .empty ∨
    ∃ w, p.table.recKindOf r = some (.subsingleton w [])

/-- **The checked shapes of the `case` entries** of `S` not of kind `empty`, at the shape the check
reads, at any sort clause (`True`: the canonicity-free route reads none). -/
def CaseFactsReadP (p : Program) (env : KEnv) (κ : CId → KKey) (S : CId → Prop) : Prop :=
  ∀ c r, S c → p.table.resolveOf c = some (.case r) → p.table.recKindOf r ≠ some .empty →
    ∃ sh, caseShape? env (κ c) (κ r) = some sh ∧
      CaseStoredWith (fun _ _ => True) env (κ c) (κ r) sh ∧ CaseProg p κ S r sh

/-- **The instance condition, stated.** -/
def PcInst (p : Program) (Inst : List (CId × Levels)) : Prop :=
  ∀ c r ls, (c, ls) ∈ Inst → p.table.resolveOf c = some (.case r) →
    ∀ w srcs, p.table.recKindOf r = some (.subsingleton w srcs) → w.holds ls = false

/-- A weaker sort clause. -/
theorem CaseStoredWith.mono {Srt Srt' : KEnv → KKey → Prop} {env : KEnv} {kc kr : KKey}
    {sh : CaseShape} (h : ∀ e D, Srt e D → Srt' e D) (hS : CaseStoredWith Srt env kc kr sh) :
    CaseStoredWith Srt' env kc kr sh :=
  { hS with wf := { hS.wf with indSort := h _ _ hS.wf.indSort } }

section Check

variable {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat}
  {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}

/-- A conjunct of the check other than `noWord`, `caseRec` and `caseShape` is the Pc family's. -/
theorem mem_checkPartsWP {name : String} {b : Bool}
    (hm : (name, b) ∈ checkParts p env κ lpsOf ann Sl)
    (hn : name ≠ "noWord" ∧ name ≠ "caseRec" ∧ name ≠ "caseShape") :
    (name, b) ∈ checkPartsWP p env κ lpsOf ann Sl := by
  obtain ⟨h1, h2, h3⟩ := hn
  exact List.mem_map.mpr ⟨(name, b), List.mem_map.mpr ⟨(name, b), hm, by simp [h1]⟩, by simp [h2, h3]⟩

/-- Every conjunct of the check but `noWord`, `caseRec` and `caseShape` holds where the Pc family's
check does. -/
theorem sansK_of_checkWP (h : groundCheckWP p env κ lpsOf ann Sl = true) :
    CheckSansK p env κ lpsOf ann Sl :=
  fun _ _ hm hn => List.all_eq_true.mp h _ (mem_checkPartsWP hm hn)

/-- The word conjunct holds where the Pc family's check does. -/
theorem word_of_checkWP (h : groundCheckWP p env κ lpsOf ann Sl = true) :
    wordB p env κ lpsOf Sl = true := by
  have hm : ("word", wordB p env κ lpsOf Sl) ∈ checkPartsWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("word", wordB p env κ lpsOf Sl),
      List.mem_map.mpr ⟨("noWord", Sl.all (noWordB p)), by simp [checkParts, checkPartsWith],
        by simp⟩, by simp⟩
  exact List.all_eq_true.mp h _ hm

theorem caseRecP_of_checkWP (h : groundCheckWP p env κ lpsOf ann Sl = true) :
    ∀ c, c ∈ Sl → caseRecPB p env κ ann Sl c = true := by
  have hm : ("caseRecP", Sl.all (caseRecPB p env κ ann Sl)) ∈ checkPartsWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("caseRec", Sl.all (caseRecB p env κ)),
      List.mem_map.mpr ⟨("caseRec", Sl.all (caseRecB p env κ)), by simp [checkParts, checkPartsWith],
        by simp⟩, by simp⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp h _ hm)

theorem caseShapeP_of_checkWP (h : groundCheckWP p env κ lpsOf ann Sl = true) :
    ∀ c, c ∈ Sl → caseShapePB p env κ c = true := by
  have hm : ("caseShapeP", Sl.all (caseShapePB p env κ)) ∈ checkPartsWP p env κ lpsOf ann Sl :=
    List.mem_map.mpr ⟨("caseShape", Sl.all (caseShapeB p env κ)),
      List.mem_map.mpr ⟨("caseShape", Sl.all (caseShapeB p env κ)),
        by simp [checkParts, checkPartsWith], by simp⟩, by simp⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp h _ hm)

/-- The PUnit shape has no field source. -/
theorem srcs_nil_of_punit {c r : CId} {w : IxCC.Src.PropWhen} {srcs : List IxCC.Src.FieldSrc}
    (h : punitShapeB p env κ ann Sl c r w srcs = true) : srcs = [] := by
  have := List.all_eq_true.mp h ("srcs", srcs.isEmpty) (by simp [punitClauses])
  simpa using this

/-- **`caseRecP` is sound**: the `case` clause at the kinds `KindsP`. -/
theorem caseRecK_of_checkWP (h : groundCheckWP p env κ lpsOf ann Sl = true) :
    CaseRecK (KindsP p) p env κ (· ∈ Sl) := by
  intro c r hc hr
  have h0 := caseRecP_of_checkWP h c hc
  simp only [caseRecPB, hr, Bool.and_eq_true] at h0
  obtain ⟨h1, h2⟩ := h0
  refine ⟨?_, ?_⟩
  · split at h1
    · rename_i hk; exact .inl hk
    · rename_i hk; exact .inr (.inl hk)
    · rename_i w srcs hk
      exact .inr (.inr ⟨w, by rw [hk, srcs_nil_of_punit h1]⟩)
    · cases h1
  · split at h2
    · rename_i ci hf
      exact ⟨ci, hf, of_decide_eq_true h2⟩
    · cases h2

/-- **`caseShapeP` and `caseProg` are sound**: the shapes at every entry not of kind `empty`. -/
theorem caseFactsReadP_of_checkWP (h : groundCheckWP p env κ lpsOf ann Sl = true) :
    CaseFactsReadP p env κ (· ∈ Sl) := by
  intro c r hc hr hk
  have h1 := caseShapeP_of_checkWP h c hc
  have h2 : caseProgOkB p env κ Sl c = true :=
    List.all_eq_true.mp (List.all_eq_true.mp h _ (mem_checkPartsWP (name := "caseProg")
      (by simp [checkParts, checkPartsWith]) (by decide))) c hc
  obtain ⟨sh, hsh, hst⟩ : ∃ sh, caseShape? env (κ c) (κ r) = some sh ∧
      CaseStoredWith (fun _ _ => True) env (κ c) (κ r) sh := by
    simp only [caseShapePB, hr] at h1
    split at h1
    · rename_i he; exact absurd he hk
    · split at h1
      · rename_i sh hsh
        exact ⟨sh, hsh, caseStoredWith_of_check (fun _ => trivial) h1⟩
      · cases h1
    · split at h1
      · rename_i sh hsh
        exact ⟨sh, hsh, CaseStoredWith.mono (fun _ _ _ => trivial) (caseStored_of_check h1)⟩
      · cases h1
  refine ⟨sh, hsh, hst, ?_⟩
  simp only [caseProgOkB, hr, hsh] at h2
  exact caseProg_of_check h2

/-- **The Pc family's check is sound**: every fact `GroundFactsW` names, at the kinds `KindsP`, with
the word clause `WordFacts`. -/
theorem groundFactsWP_of_check (h : groundCheckWP p env κ lpsOf ann Sl = true) :
    GroundFactsWithK (RecFacts p env κ lpsOf (· ∈ Sl)) (WordFacts p env κ lpsOf (· ∈ Sl)) (KindsP p)
      p env κ lpsOf ann (· ∈ Sl) :=
  groundFactsWK_of_sansK (sansK_of_checkWP h) (wordFacts_of_check (word_of_checkWP h))
    (caseRecK_of_checkWP h)

end Check

/-- **`pcInstB` is sound.** -/
theorem pcInst_of_check {p : Program} {Inst : List (CId × Levels)} (h : pcInstB p Inst = true) :
    PcInst p Inst := by
  intro c r ls hm hr w srcs hk
  have h1 := List.all_eq_true.mp h (c, ls) hm
  simp only [hr, hk, Bool.not_eq_true'] at h1
  exact h1

/-! ## The root theorem -/

section Root

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- **F5 at every `case` entry of `S` not of kind `empty`, at `OkIn`**: from the shapes the check
reads, `NoCanonA` and uniformity, by the canonicity-free route (no sort clause read). -/
theorem caseFires_of_instWP (hδ : DefnValue M) (hι : IotaLawG M.cval env) (hcv : CvalParams M)
    {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
    {ann : IxCC.Src.Relevance.Ann} {Inst : List (CId × Levels)} {R Wd : Prop} {Kd : CId → Prop}
    (hF : FaithWithK R Wd Kd p env κ lpsOf S) (hN : NatBasis env) (hC : CaseFactsReadP p env κ S)
    (hNC : NoCanonA p env κ S) (hU : InstUniform p env κ lpsOf Inst) :
    ∀ c r, S c → p.table.resolveOf c = some (.case r) → p.table.recKindOf r ≠ some .empty →
      CaseFires M p κ lpsOf S (OkIn p ann Inst) c := by
  intro c r hc hr hk
  obtain ⟨sh, hsh, hst, hpr⟩ := hC c r hc hr hk
  exact caseFires_of_agreeWK hδ hι hcv hF hN hc hr hst hpr (hNC.cases c r hc hr)
    (fun _ _ _ _ _ _ _ _ _ _ hd => caseLevelAgree_of_inst hU hr hsh hd)

/-- **The fundamental lemma's hypotheses at `OkIn`, the kind read per instance** (step Pc): at an
instance of `Inst` the kind is `ordinary` at its levels (`PcInst` at a `subsingleton`-kind entry)
or `empty`. -/
theorem fundHypsK_of_instWP (hL : LawsCore M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop}
    {Inst : List (CId × Levels)} {Wd : Prop}
    (hcanon : CtorCanon M ∨ ∀ r, S r →
      (recClassB p env κ r = some .flat ∨ recClassB p env κ r = some .noParams) →
        RecNoLevels env (κ r))
    (hG : GroundFactsWithK (RecFacts p env κ lpsOf S) Wd (KindsP p) p env κ lpsOf ann S)
    (hT : SitesOk M p κ lpsOf ann S) (hI : InstClosed p Inst) (hP : PcInst p Inst)
    (hcases : ∀ c r, S c → p.table.resolveOf c = some (.case r) →
      p.table.recKindOf r ≠ some .empty → CaseFires M p κ lpsOf S (OkIn p ann Inst) c)
    (hW : WordFires M p κ lpsOf S (OkIn p ann Inst)) :
    FundHypsK M p κ lpsOf S (OkIn p ann Inst) where
  laws := hL
  canon := hcanon
  natBasis := hG.natBasis
  faith := (hG.faith.monoW fun _ => trivial).monoK fun _ _ => trivial
  words := hW
  kindAt := fun c r ls hS hr hOk => by
    rcases (hG.faith.caseRec c r hS hr).1 with hk | hk | ⟨w, hk⟩
    · exact .inl (by rw [hk]; rfl)
    · exact .inr hk
    · refine .inl ?_
      rw [hk]
      simp [IxCC.Src.RecKind.atLevels, hP c r ls hOk.2 hr w [] hk]
  cases := fun c r hS hr ⟨ls, _, hk⟩ => hcases c r hS hr fun he => by
    rw [he] at hk
    simp [IxCC.Src.RecKind.atLevels] at hk
  eqn := fun c thm body hS hr => by
    obtain ⟨⟨d, hsh⟩, _⟩ := hG.eqns c thm body hS hr
    exact ⟨d.body, fun φ ρ X hX => Denotes_functional (eqn_den M hsh φ ρ) hX,
      fun ls φ hOk hlv => runs_of_sitesInWK hL hG hT hI hS hOk (.eqn hr hsh) hlv⟩
  value := fun c ls _ _ _ _ _ _ hS hOk hr hd hf φ hlv =>
    runs_of_sitesInWK hL hG hT hI hS hOk (.value hr hd hf) hlv

/-- `rootSound_678ASW` with the Pc family's facts: the kinds `KindsP`, the shapes `CaseFactsReadP`,
and the instance condition `PcInst`. -/
theorem rootSound_678ASWP (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFactsWithK (RecFacts p env κ lpsOf (· ∈ Sl)) (WordFacts p env κ lpsOf (· ∈ Sl))
      (KindsP p) p env κ lpsOf ann (· ∈ Sl))
    (hC : CaseFactsReadP p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hP : PcInst p Inst)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  have hLN := lawsNoCanon_of_678 hL hLD
  rootSound_coreWK hLN.core hG hR
    (allPK (fundHypsK_of_instWP hLN.core (.inr hNC.recs) hG hT hI hP
      (caseFires_of_instWP hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hG.natBasis hC
        hNC hU)
      (wordFires_of_facts hLN.core hL.proj_law hgr hG.natBasis hG.faith.words)))
    ⟨hR.ok, hroot⟩ hA hrun hrb hRT hO φ ρ X hX

/-- `rootSound_678ASWP` with every site typed from `graded`. -/
theorem rootSound_678AGWP (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFactsWithK (RecFacts p env κ lpsOf (· ∈ Sl)) (WordFacts p env κ lpsOf (· ∈ Sl))
      (KindsP p) p env κ lpsOf ann (· ∈ Sl))
    (hC : CaseFactsReadP p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hP : PcInst p Inst)
    (hH : HeadRegime p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678ASWP hL hgr hG hC hNC hLD hI hU hroot hP hR
    (sitesOk_of_headRegime hL.defnValue hgr hH) hA hrun hrb hRT hO φ ρ X hX

/-- `rootSound_678AGW_of_check` with the Pc family's check `groundCheckWP` for `groundCheckW` and the
instance condition `pcInstB`. -/
theorem rootSound_678AGWP_of_check (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheckWP p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hpc : pcInstB p Inst = true)
    (hhr : headRegimeSB p env κ lpsOf ann Sl = true)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  obtain ⟨hseeds, hI, hU⟩ := instFacts_of_check hinst
  exact rootSound_678AGWP hL hgr (groundFactsWP_of_check hchk) (caseFactsReadP_of_checkWP hchk)
    (noCanonA_of_check hnc) (litDefs_of_check hld) hI hU (hseeds root (List.mem_singleton_self _))
    (pcInst_of_check hpc) (headRegimeS_of_sansK (sansK_of_checkWP hchk) hhr) hR hA hrun hrb hRT hO
    φ ρ X hX

/-- **The Pc family's root theorem**: `rootSound_678AGpW_of_check`'s statement with the Pc family's
check `groundCheckWP` for `groundCheckW` and one more hypothesis, the instance condition
`pcInstB p Inst = true` (no instance at which a `subsingleton`-kind entry is a proposition): every
check on `selEnv`, the conclusion for the reading. -/
theorem rootSound_678AGpWP_of_check (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheckWP p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hnc : noCanonAB p (selEnv p env κ Sl) κ Sl = true)
    (hld : litDefsB (selEnv p env κ Sl) = true)
    (hinst : instCheckB p (selEnv p env κ Sl) κ lpsOf [root] Inst = true)
    (hpc : pcInstB p Inst = true)
    (hhr : headRegimeSB p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hR : RootFacts p (selEnv p env κ Sl) κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o)
    (hRT : ResultTag p (selEnv p env κ Sl) κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  have hS := selRetype_selEnv p env κ Sl
  obtain ⟨M', hc⟩ := model_selRetype M hL.defnValue hgr hS
  have hden := denotes_selRetype hS M.cval φ
  have h := rootSound_678AGWP_of_check (M := M') (laws678_selRetype hL hS hc)
    (hc ▸ gradedLaw_selRetype hL.defnValue hgr hS) hchk hnc hld hinst hpc hhr hR hA hrun hrb hRT
    hO φ ρ X (by rw [hc, hden]; exact hX)
  rw [hc, hden] at h
  exact h

end Root

end IxCC.Grounding
