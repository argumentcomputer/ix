import IxCCGrounding.Graded

/-!
# Typing at every run-term site from `graded` (`IxCCGrounding.GradedHead`)

`IxCCGrounding.Graded` (1a) closes the `r ≠ 0` gap of #678's `graded` field at the sites the direct
route refuses, reading the head constant's stored type **as written**. Here (1b) the head's type is
read through **δ and β**, so that `graded` and one decided fact type **every** site SrcEval may
evaluate in a run term, and the root theorem uses no direct route at run-term sites.

**The reading.** The head of a site's function `f = h a₁ … aₙ` is read as a value spine
(`SpineRead`): a constant reads its stored type at its levels; a bound variable its context type
(binder data are level-only, so no lifting); a λ its own datum and, applied, continues into its
body's spine in the context extended by its domain (the outer arguments lifted past it). A type is
read (`TyRead`) one `∀` per argument, then one more `∀` (the site's own); where it is not a `∀`:

* an application `D.{vs} b₁ … bₖ` of a stored definition whose value is `λ x₁ … xₖ. body` unfolds
  (**δ**, `defn_value`) and **β**-reduces (`k` λs consumed; each argument's membership in its λ's
  domain comes from `graded` at the type's own application nodes: the λ's datum not holding, it is
  a graph, whose domain is any product's it lies in, `piR_dom_unique`); the walk continues on
  `body`;
* an application of a bound variable that stands for an argument of the site (a type variable the
  reading consumed at a `∀`) reads that argument the same way, at the site's own assignment.

Every datum read (each `∀`'s, each consumed λ's) is read through the chain of level instantiations
(`pwChain`) down to the enclosing constant's parameters, at its `Ok` profiles (`headRegimeSB`): at
every profile, universe-polymorphic code would be read at `u = 0`, where the annotation classifies the
constant as a proof or a type and SrcEval never runs it.

**The decision is per maximal spine** (`headRegimeSB`, linear in the run terms times the `Ok`
profiles): a site's data are a prefix of the longest site's on the same spine (`spineRead_prefix`), and
every evaluated site lies on a listed spine at the same profiles (`spinesPs_cover`). `HeadRegime` and
the root theorems stay per site. The per-site reading (`headRegimeGB`, quadratic in a spine's length)
is kept as the reference the suite compares the per-spine verdicts with.

**Fail closed** (completeness limits, each refused): a type headed by a bound variable that stands
for no site argument; a definition applied to more arguments than its value has λs; projection
heads; a β-redex inside a type; more than `headFuel` (16) δ, bound-variable and λ steps per spine;
a constant with more than `maxDirectParams` (8) level parameters.

**Scope.** The recursor rule-body sites (`RecSites`, inside the check's `recShape` conjunct) stay with
the direct route: `graded` speaks of stored types and definition values, not of recursor rules.
`GradedLaw` is a separate hypothesis beside `Laws678`: the root theorems here assume six of #678's
fields.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

/-! ## Level chains -/

/-- Level instantiations, innermost first: `(ks, vs)` reads a datum over `ks` at `vs`. -/
abbrev LChain := List (List LevelParam × List Level)

/-- The assignment a chain induces from the enclosing constant's `φ`. -/
def chainFn (φ : LevelParam → Nat) : LChain → LevelParam → Nat
  | [] => φ
  | (ks, vs) :: ch => Level.substFn (chainFn φ ch) ks vs

/-- A datum read through the chain, down to the enclosing constant's parameters. -/
def pwChain : LChain → PropWhen → PropWhen
  | [], pw => pw
  | (ks, vs) :: ch, pw => pwChain ch (Level.substPW ks vs pw)

theorem holds_pwChain (φ : LevelParam → Nat) :
    ∀ (ch : LChain) (pw : PropWhen), (pwChain ch pw).holds φ = pw.holds (chainFn φ ch)
  | [], _ => rfl
  | (ks, vs) :: ch, pw => by
    simp only [pwChain, chainFn]
    rw [holds_pwChain φ ch, holds_substPW]

/-! ## Reading a type, and a value spine, through δ and β -/

/-- Peel `k` λs, with their data. -/
def lamPeel : Nat → KExpr → Option (List PropWhen × KExpr)
  | 0, e => some ([], e)
  | k + 1, .lam _ b m => (lamPeel k b).map fun r => (m.pw :: r.1, r.2)
  | _ + 1, _ => none

/-- What a type's bound variables stand for, innermost first: an argument of the site (a term of
the site's context) the reading consumed at a `∀`, or nothing known (`none`, or past the end). -/
abbrev Bnd := List (Option KExpr)

/-- **Reading a type through δ and β against the site's arguments** `as` (terms of the site's
context, one consumed per `∀`), then one more `∀` (the site's own); `ds` the data read (each `∀`'s,
each consumed λ's), through the chain. Where the type is not a `∀`: an application of a stored
definition unfolds (δ, β with its λs); an application of a bound variable that stands for an
argument of the site reads that argument (a λ-telescope, β, at the site's own assignment). -/
inductive TyRead (env : KEnv) : List KExpr → LChain → Bnd → KExpr → List PropWhen → Prop
  | last {ch : LChain} {bnd : Bnd} {d b : KExpr} {m : BinderMeta} :
      TyRead env [] ch bnd (.forallE d b m) [pwChain ch m.pw]
  | pi {a : KExpr} {as : List KExpr} {ch : LChain} {bnd : Bnd} {d b : KExpr} {m : BinderMeta}
      {ds : List PropWhen} :
      TyRead env as ch (some a :: bnd) b ds →
      TyRead env (a :: as) ch bnd (.forallE d b m) (pwChain ch m.pw :: ds)
  | delta {as : List KExpr} {ch : LChain} {bnd : Bnd} {T : KExpr} {D : KKey} {vs : List Level}
      {cv : ConstantVal .anon} {val : KExpr} {hint : ReducibilityHint} {lds : List PropWhen}
      {body : KExpr} {ds : List PropWhen} :
      T.getAppFn = .const D vs → env.find? D = some (.defnInfo cv val hint) →
      vs.length = cv.levelParams.length →
      lamPeel T.getAppArgs.length val = some (lds, body) →
      TyRead env as ((cv.levelParams, vs) :: ch) [] body ds →
      TyRead env as ch bnd T (lds.map (pwChain ((cv.levelParams, vs) :: ch)) ++ ds)
  | bvar {as : List KExpr} {ch : LChain} {bnd : Bnd} {T : KExpr} {i : Nat} {a : KExpr}
      {lds : List PropWhen} {body : KExpr} {ds : List PropWhen} :
      T.getAppFn = .bvar i → bnd[i]? = some (some a) →
      lamPeel T.getAppArgs.length a = some (lds, body) →
      TyRead env as [] [] body ds →
      TyRead env as ch bnd T (lds ++ ds)

/-- **Reading a value spine**: head `h` applied to the arguments `as` in context `Γ`: its type (a
constant's stored type at its levels, a bound variable's context type) read against `as`; or a λ
head's own datum, then its body's spine with the arguments left (lifted past the λ). -/
inductive SpineRead (env : KEnv) : List KExpr → KExpr → List KExpr → List PropWhen → Prop
  | const {Γ : List KExpr} {k : KKey} {us : List Level} {ci : ConstantInfo .anon} {as : List KExpr}
      {ds : List PropWhen} :
      env.find? k = some ci → us.length = ci.toConstantVal.levelParams.length →
      TyRead env as [(ci.toConstantVal.levelParams, us)] [] ci.toConstantVal.type ds →
      SpineRead env Γ (.const k us) as ds
  | bvar {Γ : List KExpr} {i : Nat} {T : KExpr} {as : List KExpr} {ds : List PropWhen} :
      Γ[i]? = some T → TyRead env as [] [] T ds → SpineRead env Γ (.bvar i) as ds
  | lam0 {Γ : List KExpr} {d b : KExpr} {m : BinderMeta} : SpineRead env Γ (.lam d b m) [] [m.pw]
  | lam {Γ : List KExpr} {d b : KExpr} {m : BinderMeta} {a : KExpr} {as : List KExpr}
      {ds : List PropWhen} :
      SpineRead env (d :: Γ) b.getAppFn (b.getAppArgs ++ as.map (·.liftLooseBVars 1 0)) ds →
      SpineRead env Γ (.lam d b m) (a :: as) (m.pw :: ds)

/-- **The head's regime at a site's function `f`, through δ and β**: `f`'s spine reads, and no
datum read holds at `φ`. -/
def HeadReadAt (env : KEnv) (φ : LevelParam → Nat) (Γ : List KExpr) (f : KExpr) : Prop :=
  ∃ ds, SpineRead env Γ f.getAppFn f.getAppArgs ds ∧ ∀ pw ∈ ds, pw.holds φ = false

/-- **`HeadRegime`**: at every site SrcEval may evaluate in a run term of an `Ok` instance. -/
def HeadRegime (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop :=
  ∀ c ls t e, S c → Ok p ann c ls → RunPair p env κ c t e →
    ∀ φ, LvAt φ (lpsOf c) ls → ∀ s ∈ evalSites ls [] t e, HeadReadAt env φ s.1 s.2.1

/-! ## The decision -/

/-- The bound on δ steps, bound-variable steps and λ steps per site. -/
def headFuel : Nat := 16

/-- `TyRead`, decided (the producer: whatever it returns is checked by `tyRead_of_check`). -/
def tyReadB (tab : KTab) : Nat → List KExpr → LChain → Bnd → KExpr → Option (List PropWhen)
  | _, [], ch, _, .forallE _ _ m => some [pwChain ch m.pw]
  | fuel, a :: as, ch, bnd, .forallE _ b m =>
    (tyReadB tab fuel as ch (some a :: bnd) b).map (pwChain ch m.pw :: ·)
  | 0, _, _, _, _ => none
  | fuel + 1, as, ch, bnd, T =>
    match T.getAppFn with
    | .const D vs =>
      match tab[D]? with
      | some (.defnInfo cv val _) =>
        if vs.length = cv.levelParams.length then
          match lamPeel T.getAppArgs.length val with
          | some (lds, body) =>
            (tyReadB tab fuel as ((cv.levelParams, vs) :: ch) [] body).map
              (lds.map (pwChain ((cv.levelParams, vs) :: ch)) ++ ·)
          | none => none
        else none
      | _ => none
    | .bvar i =>
      match bnd[i]? with
      | some (some a) =>
        match lamPeel T.getAppArgs.length a with
        | some (lds, body) => (tyReadB tab fuel as [] [] body).map (lds ++ ·)
        | none => none
      | _ => none
    | _ => none
termination_by fuel as => (fuel, as.length)

/-- `SpineRead`, decided. -/
def spineReadB (tab : KTab) : Nat → List KExpr → KExpr → List KExpr → Option (List PropWhen)
  | fuel, _, .const k us, as =>
    match tab[k]? with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        tyReadB tab fuel as [(ci.toConstantVal.levelParams, us)] [] ci.toConstantVal.type
      else none
    | none => none
  | fuel, Γ, .bvar i, as =>
    match Γ[i]? with
    | some T => tyReadB tab fuel as [] [] T
    | none => none
  | _, _, .lam _ _ m, [] => some [m.pw]
  | fuel + 1, Γ, .lam d b m, _ :: as =>
    (spineReadB tab fuel (d :: Γ) b.getAppFn (b.getAppArgs ++ as.map (·.liftLooseBVars 1 0))).map
      (m.pw :: ·)
  | _, _, _, _ => none

/-- `evalSites`, each site with the profiles (of `P`) at which it is evaluated. -/
def evalSitesPs : List IxCC.Src.Profile → List KExpr → Term → KExpr →
    List (Site × List IxCC.Src.Profile)
  | P, Γ, .app f a _ r, .app f' a' =>
    let P' := P.filter fun prof => !r.irrP prof
    ((Γ, f', a'), P) :: (evalSitesPs P Γ f f' ++ (if P'.isEmpty then [] else evalSitesPs P' Γ a a'))
  | P, Γ, .lam _ _ body, .lam d' body' _ => evalSitesPs P (d' :: Γ) body body'
  | P, Γ, .proj _ _ e, .proj _ _ e' => evalSitesPs P Γ e e'
  | P, Γ, .letE _ r _ v b, e =>
    (match zcopy b e with
      | some v' =>
        if !subAt0B v' e then [] else
          let P' := P.filter fun prof => !r.irrP prof
          if P'.isEmpty then [] else evalSitesPs P' Γ v v'
      | none => []) ++
    ((match cloSite? b e with
      | some (A, cp) =>
        let P' := P.filter fun prof => !r.irrP prof
        if P'.isEmpty then [] else evalSitesPs P' (A :: Γ) v cp
      | none => []) ++
    ((match witSite? b e with
      | some (Δ, cp) =>
        let P' := P.filter fun prof => !r.irrP prof
        if P'.isEmpty then [] else evalSitesPs P' (Δ.reverse ++ Γ) v cp
      | none => []) ++ evalSitesPs P Γ b e))
  | _, _, _, _ => []

/-- `headRegimeGB` at one constant, its level parameters `lps` computed once (an `lpsOf` that
searches the reading costs the reading's length per call). -/
def headRegimeGB1 (tab : KTab) (lps : List Nat) (p : Program) (env : KEnv) (κ : CId → KKey)
    (ann : IxCC.Src.Relevance.Ann) (c : CId) : Bool :=
  decide (lvlsOf p c ≤ maxDirectParams) && (runPairsB p env κ c).all fun x =>
    (evalSitesPs (okProfiles p ann c) [] x.1 x.2).all fun sP =>
      match spineReadB tab headFuel sP.1.1 sP.1.2.1.getAppFn sP.1.2.1.getAppArgs with
      | some ds => sP.2.all fun prof => ds.all fun pw => pwAt lps prof pw == some false
      | none => false

/-- **`HeadRegime`, decided per site** (the reference reading, quadratic in a spine's length): every
site of every run pair of `Sl`, its data read once, each datum false at every `Ok` profile the site
is evaluated at; a constant with more than `maxDirectParams` level parameters refused. -/
def headRegimeGB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  let tab := KTab.of env
  Sl.all fun c => headRegimeGB1 tab (lpsOf c) p env κ ann c

/-- A maximal application spine of a run term: its context, its kernel head, its arguments (each
site of the spine is the head applied to a proper prefix of them), and the profiles at which
SrcEval evaluates it. -/
structure SpineAt where
  ctx : List KExpr
  head : KExpr
  args : List KExpr
  profs : List IxCC.Src.Profile

/-- The spine ending at `e` with the arguments `acc` peeled above it (none when `acc` is empty: no
site): its head is `e`'s, its arguments `e`'s then `acc`. -/
def spineHere (P : List IxCC.Src.Profile) (Γ : List KExpr) (e : KExpr) (acc : List KExpr) :
    List SpineAt :=
  if acc.isEmpty then [] else [⟨Γ, e.getAppFn, e.getAppArgs ++ acc, P⟩]

/-- **The maximal spines SrcEval may evaluate**, with their profiles, `acc` the arguments already
peeled above `e` (each evaluated spine once; walked as `evalSites`: through a `let`, its value's spines at its copy when the value is relevant and the copy sits at depth 0, then its body's against the same kernel term, the arguments peeled above carried on, since the reduct is that term). -/
def spinesPs : List IxCC.Src.Profile → List KExpr → Term → KExpr → List KExpr → List SpineAt
  | P, Γ, .app f a _ r, .app f' a', acc =>
    spinesPs P Γ f f' (a' :: acc) ++
      (let P' := P.filter fun prof => !r.irrP prof
       if P'.isEmpty then [] else spinesPs P' Γ a a' [])
  | P, Γ, .lam _ _ body, .lam d' body' m, acc =>
    spineHere P Γ (.lam d' body' m) acc ++ spinesPs P (d' :: Γ) body body' []
  | P, Γ, .proj _ _ x, .proj s i x', acc =>
    spineHere P Γ (.proj s i x') acc ++ spinesPs P Γ x x' []
  | P, Γ, .letE _ r _ v b, e, acc =>
    (match zcopy b e with
      | some v' =>
        if !subAt0B v' e then [] else
          let P' := P.filter fun prof => !r.irrP prof
          if P'.isEmpty then [] else spinesPs P' Γ v v' []
      | none => []) ++
    ((match cloSite? b e with
      | some (A, cp) =>
        let P' := P.filter fun prof => !r.irrP prof
        if P'.isEmpty then [] else spinesPs P' (A :: Γ) v cp []
      | none => []) ++
    ((match witSite? b e with
      | some (Δ, cp) =>
        let P' := P.filter fun prof => !r.irrP prof
        if P'.isEmpty then [] else spinesPs P' (Δ.reverse ++ Γ) v cp []
      | none => []) ++ spinesPs P Γ b e acc))
  | P, Γ, _, e, acc => spineHere P Γ e acc

/-- `headRegimeSB` at one constant, its level parameters `lps` computed once (an `lpsOf` that
searches the reading costs the reading's length per call). -/
def headRegimeSB1 (tab : KTab) (lps : List Nat) (p : Program) (env : KEnv) (κ : CId → KKey)
    (ann : IxCC.Src.Relevance.Ann) (c : CId) : Bool :=
  decide (lvlsOf p c ≤ maxDirectParams) && (runPairsB p env κ c).all fun x =>
    (spinesPs (okProfiles p ann c) [] x.1 x.2 []).all fun sp =>
      match spineReadB tab headFuel sp.ctx sp.head sp.args.dropLast with
      | some ds => sp.profs.all fun prof => ds.all fun pw => pwAt lps prof pw == some false
      | none => false

/-- **`HeadRegime`, decided per maximal spine** (the decision the root theorem reads): each spine
of each run pair of `Sl` read once, against its arguments less the last (the longest site's
function), each datum false at every `Ok` profile the spine is evaluated at; a constant with more
than `maxDirectParams` level parameters refused. Linear in the run terms times the profiles. -/
def headRegimeSB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  let tab := KTab.of env
  Sl.all fun c => headRegimeSB1 tab (lpsOf c) p env κ ann c

/-! ## The decision's soundness -/

theorem tyRead_of_check {env : KEnv} :
    ∀ (fuel : Nat) (as : List KExpr) (ch : LChain) (bnd : Bnd) (T : KExpr) {ds : List PropWhen},
      tyReadB (KTab.of env) fuel as ch bnd T = some ds → TyRead env as ch bnd T ds := by
  intro fuel as ch bnd T
  fun_induction tyReadB (KTab.of env) fuel as ch bnd T
  case case1 => intro ds h; cases h; exact .last
  case case2 ih =>
    intro ds h
    obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact .pi (ih h')
  case case4 hfn _ _ _ hD hl _ _ hp ih =>
    intro ds h
    obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [KTab.get_of] at hD
    exact .delta hfn hD hl hp (ih h')
  case case8 hfn _ hbi _ _ hp ih =>
    intro ds h
    obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact .bvar hfn hbi hp (ih h')
  all_goals intro ds h; cases h

theorem spineRead_of_check {env : KEnv} :
    ∀ (fuel : Nat) (Γ : List KExpr) (h : KExpr) (as : List KExpr) {ds : List PropWhen},
      spineReadB (KTab.of env) fuel Γ h as = some ds → SpineRead env Γ h as ds := by
  intro fuel Γ h as
  fun_induction spineReadB (KTab.of env) fuel Γ h as
  case case1 hk hl =>
    intro ds hc
    rw [KTab.get_of] at hk
    exact .const hk hl (tyRead_of_check _ _ _ _ _ hc)
  case case4 hT =>
    intro ds hc
    exact .bvar hT (tyRead_of_check _ _ _ _ _ hc)
  case case6 => intro ds hc; cases hc; exact .lam0
  case case7 ih =>
    intro ds hc
    obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp hc
    exact .lam (ih h')
  all_goals intro ds hc; cases hc

/-- A reading's head is a constant, a bound variable or a λ: never an application. -/
theorem SpineRead.head_getApp {env : KEnv} {Γ : List KExpr} {h : KExpr} {as : List KExpr}
    {ds : List PropWhen} (hr : SpineRead env Γ h as ds) : h.getAppFn = h ∧ h.getAppArgs = [] := by
  cases hr <;> exact ⟨rfl, rfl⟩

/-- **The reading is monotone**: reading a prefix of the arguments reads a prefix of the data. -/
theorem tyRead_prefix {env : KEnv} :
    ∀ {as : List KExpr} {ch : LChain} {bnd : Bnd} {T : KExpr} {ds : List PropWhen},
      TyRead env as ch bnd T ds → ∀ (xs ys : List KExpr), as = xs ++ ys →
        ∃ ds', TyRead env xs ch bnd T ds' ∧ ds' <+: ds := by
  intro as ch bnd T ds hr
  induction hr with
  | last =>
    intro xs ys h
    cases xs with
    | nil => exact ⟨_, .last, [], rfl⟩
    | cons x xs => simp at h
  | @pi a as ch bnd d b m ds _ ih =>
    intro xs ys h
    cases xs with
    | nil => exact ⟨_, .last, ds, rfl⟩
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ds', hr', t, rfl⟩ := ih xs ys rfl
      exact ⟨_, .pi hr', t, rfl⟩
  | delta hfn hfind hlen hpeel _ ih =>
    intro xs ys h
    obtain ⟨ds', hr', t, rfl⟩ := ih xs ys h
    exact ⟨_, .delta hfn hfind hlen hpeel hr', t, by simp⟩
  | bvar hfn hbi hpeel _ ih =>
    intro xs ys h
    obtain ⟨ds', hr', t, rfl⟩ := ih xs ys h
    exact ⟨_, .bvar hfn hbi hpeel hr', t, by simp⟩

/-- **A value spine's reading is monotone** in its arguments. -/
theorem spineRead_prefix {env : KEnv} :
    ∀ {Γ : List KExpr} {h : KExpr} {as : List KExpr} {ds : List PropWhen},
      SpineRead env Γ h as ds → ∀ (xs ys : List KExpr), as = xs ++ ys →
        ∃ ds', SpineRead env Γ h xs ds' ∧ ds' <+: ds := by
  intro Γ h as ds hr
  induction hr with
  | const hfind hlen hty =>
    intro xs ys h
    obtain ⟨ds', hr', hp⟩ := tyRead_prefix hty xs ys h
    exact ⟨ds', .const hfind hlen hr', hp⟩
  | bvar hget hty =>
    intro xs ys h
    obtain ⟨ds', hr', hp⟩ := tyRead_prefix hty xs ys h
    exact ⟨ds', .bvar hget hr', hp⟩
  | lam0 =>
    intro xs ys h
    cases xs with
    | nil => exact ⟨_, .lam0, [], rfl⟩
    | cons x xs => simp at h
  | @lam Γ d b m a as ds _ ih =>
    intro xs ys h
    cases xs with
    | nil => exact ⟨_, .lam0, ds, rfl⟩
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ds', hr', t, rfl⟩ := ih (b.getAppArgs ++ xs.map (·.liftLooseBVars 1 0))
        (ys.map (·.liftLooseBVars 1 0)) (by simp)
      exact ⟨_, .lam hr', t, rfl⟩

/-- An argument relevant at `ls`: its profile survives the relevance filter, which is not empty. -/
theorem mem_filter_irr {ls : Levels} {P : List IxCC.Src.Profile} {r : IxCC.Src.Rel}
    (hP : IxCC.Src.profileOf ls ∈ P) (hirr : ¬ r.irrAt ls = true) :
    IxCC.Src.profileOf ls ∈ P.filter (fun prof => !r.irrP prof) ∧
      (P.filter fun prof => !r.irrP prof).isEmpty = false := by
  have hP' : IxCC.Src.profileOf ls ∈ P.filter (fun prof => !r.irrP prof) := by
    simp [List.mem_filter, hP, ← irrAt_profile, hirr]
  refine ⟨hP', ?_⟩
  cases hq : (P.filter fun prof => !r.irrP prof) with
  | nil => rw [hq] at hP'; simp at hP'
  | cons _ _ => rfl

/-- Every site `evalSites` lists at `Ok` levels is listed at their profile. -/
theorem mem_evalSitesPs {ls : Levels} :
    ∀ (t : Term) (P : List IxCC.Src.Profile) (Γ : List KExpr) (e : KExpr) (s : Site),
      IxCC.Src.profileOf ls ∈ P → s ∈ evalSites ls Γ t e →
      ∃ Ps, (s, Ps) ∈ evalSitesPs P Γ t e ∧ IxCC.Src.profileOf ls ∈ Ps := by
  intro t
  induction t with
  | app f a md r ihf iha =>
    intro P Γ e s hP hs
    cases e with
    | app f' a' =>
      simp only [evalSites, List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | hs | hs
      · exact ⟨P, by simp [evalSitesPs], hP⟩
      · obtain ⟨Ps, h1, h2⟩ := ihf P Γ f' s hP hs
        refine ⟨Ps, ?_, h2⟩
        simp only [evalSitesPs, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl h1)
      · by_cases hirr : r.irrAt ls = true
        · simp [hirr] at hs
        · simp only [hirr, Bool.false_eq_true, ↓reduceIte] at hs
          have hP' : IxCC.Src.profileOf ls ∈ P.filter (fun prof => !r.irrP prof) := by
            simp [List.mem_filter, hP, ← irrAt_profile, hirr]
          have hne : (P.filter fun prof => !r.irrP prof).isEmpty = false := by
            cases hq : (P.filter fun prof => !r.irrP prof) with
            | nil => rw [hq] at hP'; simp at hP'
            | cons _ _ => rfl
          obtain ⟨Ps, h1, h2⟩ := iha _ Γ a' s hP' hs
          refine ⟨Ps, ?_, h2⟩
          simp only [evalSitesPs, List.mem_cons, List.mem_append, hne, Bool.false_eq_true,
            ↓reduceIte]
          exact Or.inr (Or.inr h1)
    | _ => simp [evalSites] at hs
  | lam b d body _ ihb =>
    intro P Γ e s hP hs
    cases e with
    | lam d' body' mb =>
      simp only [evalSites] at hs
      obtain ⟨Ps, h1, h2⟩ := ihb P (d' :: Γ) body' s hP hs
      exact ⟨Ps, by simpa only [evalSitesPs] using h1, h2⟩
    | _ => simp [evalSites] at hs
  | proj s0 i x ih =>
    intro P Γ e s hP hs
    cases e with
    | proj _ _ x' =>
      simp only [evalSites] at hs
      obtain ⟨Ps, h1, h2⟩ := ih P Γ x' s hP hs
      exact ⟨Ps, by simpa only [evalSitesPs] using h1, h2⟩
    | _ => simp [evalSites] at hs
  | letE c r ty v b _ ihv ihb =>
    intro P Γ e s hP hs
    simp only [evalSites, List.mem_append] at hs
    rcases hs with hs | hs
    · cases hz : zcopy b e with
      | none => simp [hz] at hs
      | some v' =>
        simp only [hz] at hs
        cases hsub : subAt0B v' e
        · simp [hsub] at hs
        · simp only [hsub, Bool.not_true, Bool.or_false] at hs
          split at hs
          · simp at hs
          · rename_i hirr
            obtain ⟨hP', hne⟩ := mem_filter_irr hP hirr
            obtain ⟨Ps, h1, h2⟩ := ihv _ Γ v' s hP' hs
            refine ⟨Ps, ?_, h2⟩
            simp only [evalSitesPs, List.mem_append, hz, hsub, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, hne]
            exact Or.inl h1
    · rcases hs with hs | hs
      · -- the closure-capture shape (step C)
        cases hc : cloSite? b e with
        | none => simp [hc] at hs
        | some p =>
          obtain ⟨A, cp⟩ := p
          simp only [hc] at hs
          split at hs
          · simp at hs
          · rename_i hirr
            obtain ⟨hP', hne⟩ := mem_filter_irr hP hirr
            obtain ⟨Ps, h1, h2⟩ := ihv _ (A :: Γ) cp s hP' hs
            refine ⟨Ps, ?_, h2⟩
            simp only [evalSitesPs, List.mem_append, hc, Bool.false_eq_true, ↓reduceIte, hne]
            exact Or.inr (Or.inl h1)
      · rcases hs with hs | hs
        · -- the witness shape
          cases hw : witSite? b e with
          | none => simp [hw] at hs
          | some p =>
            obtain ⟨Δ, cp⟩ := p
            simp only [hw] at hs
            split at hs
            · simp at hs
            · rename_i hirr
              obtain ⟨hP', hne⟩ := mem_filter_irr hP hirr
              obtain ⟨Ps, h1, h2⟩ := ihv _ (Δ.reverse ++ Γ) cp s hP' hs
              refine ⟨Ps, ?_, h2⟩
              simp only [evalSitesPs, List.mem_append, hw, Bool.false_eq_true, ↓reduceIte, hne]
              exact Or.inr (Or.inr (Or.inl h1))
        · obtain ⟨Ps, h1, h2⟩ := ihb P Γ e s hP hs
          refine ⟨Ps, ?_, h2⟩
          simp only [evalSitesPs, List.mem_append]
          exact Or.inr (Or.inr (Or.inr h1))
  | _ => intro P Γ e s _ hs; cases e <;> simp [evalSites] at hs

/-- An `Ok` instance's profile is among the `Ok` profiles. -/
theorem profileOf_mem_okProfiles {p : Program} {ann : IxCC.Src.Relevance.Ann} {c : CId}
    {ls : Levels} (h : Ok p ann c ls) : IxCC.Src.profileOf ls ∈ okProfiles p ann c := by
  obtain ⟨hlen, r, hr, hirr⟩ := h
  simp only [okProfiles, hr, List.mem_filter]
  refine ⟨mem_profiles _ _ (by simp [IxCC.Src.profileOf, hlen]), ?_⟩
  rw [← irrAt_profile, hirr]
  rfl

/-- **`headRegimeGB` is sound** (with the check, which puts each run pair among those the decision
enumerates and gives the level count). -/
theorem headRegime_of_check {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (h : headRegimeGB p env κ lpsOf ann Sl = true) : HeadRegime p env κ lpsOf ann (· ∈ Sl) := by
  intro c ls t e hS hOk hrp φ hlv s hs
  have hpair := runPair_mem_of_check hchk hS hrp
  have hG := groundFacts_of_check hchk
  have hlen : ls.length = (lpsOf c).length := hOk.1.trans (hG.faith.lvls c hS)
  obtain ⟨Ps, hsP, hprof⟩ := mem_evalSitesPs t _ [] e s (profileOf_mem_okProfiles hOk) hs
  simp only [headRegimeGB, headRegimeGB1, List.all_eq_true, Bool.and_eq_true] at h
  have h1 := (h c hS).2 (t, e) hpair (s, Ps) hsP
  split at h1
  · rename_i ds hds
    refine ⟨ds, spineRead_of_check _ _ _ _ hds, fun pw hpw => ?_⟩
    have h2 := List.all_eq_true.mp h1 _ hprof
    have h3 := List.all_eq_true.mp h2 pw hpw
    exact holds_of_pwAt (profAt_of_lvAt hlv hlen) (beq_iff_eq.mp h3)
  · cases h1

theorem mem_spineHere {P : List IxCC.Src.Profile} {Γ : List KExpr} {e : KExpr} {acc : List KExpr}
    (h : acc ≠ []) : (⟨Γ, e.getAppFn, e.getAppArgs ++ acc, P⟩ : SpineAt) ∈ spineHere P Γ e acc := by
  cases acc with
  | nil => exact absurd rfl h
  | cons a acc => simp [spineHere]

/-- **Some listed spine ends with the arguments `acc` peeled above `e`**, at the same context and
profiles, its head applied to what precedes `acc` being `e`. -/
theorem spinesPs_tail : ∀ (t : Term) (P : List IxCC.Src.Profile) (Γ : List KExpr) (e : KExpr)
    (acc : List KExpr), acc ≠ [] →
    ∃ sp ∈ spinesPs P Γ t e acc, sp.ctx = Γ ∧ sp.profs = P ∧
      ∃ pre, sp.args = pre ++ acc ∧ Expr.mkAppN sp.head pre = e := by
  have here : ∀ (P : List IxCC.Src.Profile) (Γ : List KExpr) (e : KExpr) (acc : List KExpr),
      acc ≠ [] → ∃ sp ∈ spineHere P Γ e acc, sp.ctx = Γ ∧ sp.profs = P ∧
        ∃ pre, sp.args = pre ++ acc ∧ Expr.mkAppN sp.head pre = e :=
    fun P Γ e acc h => ⟨_, mem_spineHere h, rfl, rfl, e.getAppArgs, rfl, mkAppN_getApp e⟩
  intro t
  induction t with
  | app f a md r ihf _ =>
    intro P Γ e acc hacc
    cases e with
    | app f' a' =>
      obtain ⟨sp, hsp, h1, h2, pre, h3, h4⟩ := ihf P Γ f' (a' :: acc) (by simp)
      refine ⟨sp, ?_, h1, h2, pre ++ [a'], by rw [h3]; simp, by rw [mkAppN_append, h4]⟩
      simp only [spinesPs, List.mem_append]
      exact Or.inl hsp
    | _ =>
      obtain ⟨sp, hsp, h⟩ := here P Γ _ acc hacc
      exact ⟨sp, by simpa only [spinesPs] using hsp, h⟩
  | lam b d body _ _ =>
    intro P Γ e acc hacc
    cases e with
    | lam d' body' mb =>
      obtain ⟨sp, hsp, h⟩ := here P Γ _ acc hacc
      exact ⟨sp, by simp only [spinesPs, List.mem_append]; exact Or.inl hsp, h⟩
    | _ =>
      obtain ⟨sp, hsp, h⟩ := here P Γ _ acc hacc
      exact ⟨sp, by simpa only [spinesPs] using hsp, h⟩
  | proj s0 i x _ =>
    intro P Γ e acc hacc
    cases e with
    | proj _ _ x' =>
      obtain ⟨sp, hsp, h⟩ := here P Γ _ acc hacc
      exact ⟨sp, by simp only [spinesPs, List.mem_append]; exact Or.inl hsp, h⟩
    | _ =>
      obtain ⟨sp, hsp, h⟩ := here P Γ _ acc hacc
      exact ⟨sp, by simpa only [spinesPs] using hsp, h⟩
  | letE c r ty v b _ _ ihb =>
    intro P Γ e acc hacc
    obtain ⟨sp, hsp, h⟩ := ihb P Γ e acc hacc
    exact ⟨sp, by simp only [spinesPs, List.mem_append]; exact Or.inr (Or.inr (Or.inr hsp)), h⟩
  | _ =>
    intro P Γ e acc hacc
    obtain ⟨sp, hsp, h⟩ := here P Γ e acc hacc
    exact ⟨sp, by cases e <;> simpa only [spinesPs] using hsp, h⟩

/-- **Every evaluated site lies on a listed spine**, at the same profiles: in its context, its
function the spine's head applied to a proper prefix of the spine's arguments. -/
theorem spinesPs_cover {ls : Levels} : ∀ (t : Term) (P : List IxCC.Src.Profile) (Γ : List KExpr)
    (e : KExpr) (acc : List KExpr), IxCC.Src.profileOf ls ∈ P → ∀ s ∈ evalSites ls Γ t e,
    ∃ sp ∈ spinesPs P Γ t e acc, IxCC.Src.profileOf ls ∈ sp.profs ∧ s.1 = sp.ctx ∧
      ∃ j < sp.args.length, s.2.1 = Expr.mkAppN sp.head (sp.args.take j) := by
  intro t
  induction t with
  | app f a md r ihf iha =>
    intro P Γ e acc hP s hs
    cases e with
    | app f' a' =>
      simp only [evalSites, List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | hs | hs
      · obtain ⟨sp, hsp, h1, h2, pre, h3, h4⟩ := spinesPs_tail f P Γ f' (a' :: acc) (by simp)
        refine ⟨sp, ?_, by rw [h2]; exact hP, h1.symm, pre.length, by rw [h3]; simp, ?_⟩
        · simp only [spinesPs, List.mem_append]
          exact Or.inl hsp
        · simp [h3, h4]
      · obtain ⟨sp, hsp, h⟩ := ihf P Γ f' (a' :: acc) hP s hs
        refine ⟨sp, ?_, h⟩
        simp only [spinesPs, List.mem_append]
        exact Or.inl hsp
      · by_cases hirr : r.irrAt ls = true
        · simp [hirr] at hs
        · simp only [hirr, Bool.false_eq_true, ↓reduceIte] at hs
          have hP' : IxCC.Src.profileOf ls ∈ P.filter (fun prof => !r.irrP prof) := by
            simp [List.mem_filter, hP, ← irrAt_profile, hirr]
          have hne : (P.filter fun prof => !r.irrP prof).isEmpty = false := by
            cases hq : (P.filter fun prof => !r.irrP prof) with
            | nil => rw [hq] at hP'; simp at hP'
            | cons _ _ => rfl
          obtain ⟨sp, hsp, h⟩ := iha _ Γ a' [] hP' s hs
          refine ⟨sp, ?_, h⟩
          simp only [spinesPs, List.mem_append, hne, Bool.false_eq_true, ↓reduceIte]
          exact Or.inr hsp
    | _ => simp [evalSites] at hs
  | lam b d body _ ihb =>
    intro P Γ e acc hP s hs
    cases e with
    | lam d' body' mb =>
      simp only [evalSites] at hs
      obtain ⟨sp, hsp, h⟩ := ihb P (d' :: Γ) body' [] hP s hs
      refine ⟨sp, ?_, h⟩
      simp only [spinesPs, List.mem_append]
      exact Or.inr hsp
    | _ => simp [evalSites] at hs
  | proj s0 i x ih =>
    intro P Γ e acc hP s hs
    cases e with
    | proj _ _ x' =>
      simp only [evalSites] at hs
      obtain ⟨sp, hsp, h⟩ := ih P Γ x' [] hP s hs
      refine ⟨sp, ?_, h⟩
      simp only [spinesPs, List.mem_append]
      exact Or.inr hsp
    | _ => simp [evalSites] at hs
  | letE c r ty v b _ ihv ihb =>
    intro P Γ e acc hP s hs
    simp only [evalSites, List.mem_append] at hs
    rcases hs with hs | hs
    · cases hz : zcopy b e with
      | none => simp [hz] at hs
      | some v' =>
        simp only [hz] at hs
        cases hsub : subAt0B v' e
        · simp [hsub] at hs
        · simp only [hsub, Bool.not_true, Bool.or_false] at hs
          split at hs
          · simp at hs
          · rename_i hirr
            obtain ⟨hP', hne⟩ := mem_filter_irr hP hirr
            obtain ⟨sp, hsp, h⟩ := ihv _ Γ v' [] hP' s hs
            refine ⟨sp, ?_, h⟩
            simp only [spinesPs, List.mem_append, hz, hsub, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, hne]
            exact Or.inl hsp
    · rcases hs with hs | hs
      · -- the closure-capture shape (step C)
        cases hc : cloSite? b e with
        | none => simp [hc] at hs
        | some p =>
          obtain ⟨A, cp⟩ := p
          simp only [hc] at hs
          split at hs
          · simp at hs
          · rename_i hirr
            obtain ⟨hP', hne⟩ := mem_filter_irr hP hirr
            obtain ⟨sp, hsp, h⟩ := ihv _ (A :: Γ) cp [] hP' s hs
            refine ⟨sp, ?_, h⟩
            simp only [spinesPs, List.mem_append, hc, Bool.false_eq_true, ↓reduceIte, hne]
            exact Or.inr (Or.inl hsp)
      · rcases hs with hs | hs
        · -- the witness shape
          cases hw : witSite? b e with
          | none => simp [hw] at hs
          | some p =>
            obtain ⟨Δ, cp⟩ := p
            simp only [hw] at hs
            split at hs
            · simp at hs
            · rename_i hirr
              obtain ⟨hP', hne⟩ := mem_filter_irr hP hirr
              obtain ⟨sp, hsp, h⟩ := ihv _ (Δ.reverse ++ Γ) cp [] hP' s hs
              refine ⟨sp, ?_, h⟩
              simp only [spinesPs, List.mem_append, hw, Bool.false_eq_true, ↓reduceIte, hne]
              exact Or.inr (Or.inr (Or.inl hsp))
        · obtain ⟨sp, hsp, h⟩ := ihb P Γ e acc hP s hs
          refine ⟨sp, ?_, h⟩
          simp only [spinesPs, List.mem_append]
          exact Or.inr (Or.inr (Or.inr hsp))
  | _ => intro P Γ e acc _ s hs; cases e <;> simp [evalSites] at hs

theorem take_dropLast {α : Type _} {l : List α} {j : Nat} (h : j < l.length) :
    l.dropLast.take j = l.take j := by
  rw [List.dropLast_eq_take, List.take_take]
  congr 1
  omega

/-- **`headRegimeSB` is sound** with every conjunct of the check but `noWord` (`CheckSans`; step W
reads it through `groundCheckW`). -/
theorem headRegimeS_of_sans {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : CheckSans p env κ lpsOf ann Sl)
    (h : headRegimeSB p env κ lpsOf ann Sl = true) : HeadRegime p env κ lpsOf ann (· ∈ Sl) := by
  intro c ls t e hS hOk hrp φ hlv s hs
  have hpair := runPair_mem_of_sans hchk hS hrp
  have hG := groundFactsW_of_sans hchk (Wd := True) trivial
  have hlen : ls.length = (lpsOf c).length := hOk.1.trans (hG.faith.lvls c hS)
  obtain ⟨sp, hsp, hP, hctx, j, hj, hfe⟩ :=
    spinesPs_cover t (okProfiles p ann c) [] e [] (profileOf_mem_okProfiles hOk) s hs
  simp only [headRegimeSB, headRegimeSB1, List.all_eq_true, Bool.and_eq_true] at h
  have h1 := (h c hS).2 (t, e) hpair sp hsp
  split at h1
  · rename_i ds hds
    have hr := spineRead_of_check _ _ _ _ hds
    obtain ⟨hfn, hargs⟩ := hr.head_getApp
    obtain ⟨ds', hr', hpre⟩ := spineRead_prefix hr (sp.args.take j) (sp.args.dropLast.drop j)
      (by rw [← take_dropLast hj, List.take_append_drop])
    refine ⟨ds', ?_, fun pw hpw => ?_⟩
    · rw [hfe, getAppFn_mkAppN, hfn, getAppArgs_mkAppN, hargs, List.nil_append, hctx]
      exact hr'
    · have h2 := List.all_eq_true.mp h1 _ hP
      have h3 := List.all_eq_true.mp h2 pw (hpre.subset hpw)
      exact holds_of_pwAt (profAt_of_lvAt hlv hlen) (beq_iff_eq.mp h3)
  · cases h1

/-- **`headRegimeSB` is sound**: the per-spine decision gives the per-site `HeadRegime` (with the
check, which puts each run pair among those the decision enumerates and gives the level count). -/
theorem headRegimeS_of_check {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (h : headRegimeSB p env κ lpsOf ann Sl = true) : HeadRegime p env κ lpsOf ann (· ∈ Sl) :=
  headRegimeS_of_sans (sans_of_check hchk) h

/-! ## The semantics -/

section Walk

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **Spine memberships**: along `F` applied to `Xs`, each partial application lies in a product
whose domain holds the next argument (what `graded` gives at a spine's nodes). -/
def SpineMem (F : V) (Xs : List V) : Prop :=
  ∀ j (hj : j < Xs.length), ∃ (r : Nat) (A : V) (B : V → V),
    (Xs.take j).foldl app F ∈ˢ piR r A B ∧ Xs[j] ∈ˢ A

/-- `GradedBy` of an application spine gives `GradedBy` of its head and of each argument. -/
theorem gradedBy_mkAppN {D : (BVarIdx → V) → KExpr → V → Prop} {ρ : BVarIdx → V} :
    ∀ (args : List KExpr) {h : KExpr}, GradedBy D ρ (Expr.mkAppN h args) →
      GradedBy D ρ h ∧ ∀ a ∈ args, GradedBy D ρ a
  | [], _, hg => ⟨hg, fun a ha => by simp at ha⟩
  | a :: args, h, hg => by
    obtain ⟨h1, h2⟩ := gradedBy_mkAppN args (h := .app h a) hg
    simp only [GradedBy] at h1
    refine ⟨h1.1, fun a' ha' => ?_⟩
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact h1.2.1
    · exact h2 a' ha'

theorem spineMem_of_graded (M : Model V env) {φ : LevelParam → Nat} {ρ : BVarIdx → V} :
    ∀ (args : List KExpr) {h : KExpr} {F : V} {Xs : List V},
      GradedBy (Denotes M.cval env φ) ρ (Expr.mkAppN h args) → Denotes M.cval env φ ρ h F →
      DenotesList M.cval env φ ρ args Xs → SpineMem F Xs := by
  intro args
  generalize hn : args.length = n
  induction n generalizing args with
  | zero =>
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    intro h F Xs _ _ hXs
    cases hXs
    intro j hj
    simp at hj
  | succ n ih =>
    have hne : args ≠ [] := by rintro rfl; simp at hn
    obtain ⟨xs, x, rfl⟩ := exists_snoc args hne
    intro h F Xs hg hF hXs
    obtain ⟨Ys, Zs, rfl, hYs, hZs⟩ := denotesList_append_inv hXs
    cases hZs with
    | @cons _ _ X _ hx hnil =>
      cases hnil
      rw [mkAppN_append] at hg
      simp only [GradedBy] at hg
      obtain ⟨hgf, -, r, A, F', X', B, hF', hX', hmem, hXA, -⟩ := hg
      have hfold : Denotes M.cval env φ ρ (Expr.mkAppN h xs) (Ys.foldl app F) :=
        (den_mkAppN xs).mpr ⟨F, Ys, hF, hYs, rfl⟩
      rw [Denotes_functional hF' hfold] at hmem
      rw [Denotes_functional hX' hx] at hXA
      have ihS := ih xs (by simpa using hn) hgf hF hYs
      have hlY : Ys.length = xs.length := denotesList_length hYs
      intro j hj
      have hj' : j < Ys.length + 1 := by simpa using hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
      · obtain ⟨r', A', B', h1, h2⟩ := ihS j hlt
        refine ⟨r', A', B', ?_, ?_⟩
        · rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)]
        · simpa [List.getElem_append_left hlt] using h2
      · exact ⟨r, A, B, by simpa using hmem, by simpa using hXA⟩

/-- **β along a λ-telescope** in the graph regime: the λs' data not holding, each argument in
its λ's domain by the spine memberships (a positive-regime λ is a graph whose domain is any
product's it lies in), the telescope applied is its body at the arguments, still graded. -/
theorem beta_peel (M : Model V env) {ψ : LevelParam → Nat} :
    ∀ (k : Nat) (val body : KExpr) (lds : List PropWhen) (τ : BVarIdx → V) (G : V) (Xs : List V),
      lamPeel k val = some (lds, body) → (∀ pw ∈ lds, pw.holds ψ = false) → Xs.length = k →
      Denotes M.cval env ψ τ val G → GradedBy (Denotes M.cval env ψ) τ val → SpineMem G Xs →
      Denotes M.cval env ψ (pushAll Xs τ) body (Xs.foldl app G) ∧
        GradedBy (Denotes M.cval env ψ) (pushAll Xs τ) body := by
  intro k
  induction k with
  | zero =>
    intro val body lds τ G Xs hp _ hlen hG hg _
    simp only [lamPeel, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    rw [pushAll_nil]
    exact ⟨hG, hg⟩
  | succ k ih =>
    intro val body lds τ G Xs hp hds hlen hG hg hS
    cases val
    case lam d b m =>
      simp only [lamPeel, Option.map_eq_some_iff, Prod.mk.injEq] at hp
      obtain ⟨⟨l, bd⟩, h1, rfl, rfl⟩ := hp
      obtain ⟨X, Xs', rfl⟩ : ∃ X Xs', Xs = X :: Xs' := by
        cases Xs with
        | nil => simp at hlen
        | cons X Xs' => exact ⟨X, Xs', rfl⟩
      have hpw : m.pw.holds ψ = false := hds _ (by simp)
      have hv : regime ψ m.pw ≠ 0 := by simp [regime, hpw]
      obtain ⟨Ad, F, hAd, hF, -, rfl⟩ := den_lam.mp hG
      obtain ⟨r, A, B, hmem, hXA⟩ := hS 0 (by simp)
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hmem hXA
      have hr : r ≠ 0 := by
        rintro rfl
        exact lamR_ne_pt hv (eq_pt_of_mem_piR_zero hmem)
      have hdom : Ad = A := piR_dom_unique hv hr
        (lamR_mem (B := fun x => sing (F x)) (fun x _ => mem_sing.mpr rfl)) hmem
      rw [← hdom] at hXA
      have happ : app (lamR (regime ψ m.pw) Ad F) X = F X := app_lamR_pos hv hXA
      simp only [GradedBy] at hg
      have hS' : SpineMem (F X) Xs' := by
        intro j hj
        obtain ⟨r', A', B', h1', h2'⟩ := hS (j + 1) (by simpa using hj)
        refine ⟨r', A', B', ?_, ?_⟩
        · simpa [List.take_succ_cons, List.foldl_cons, happ] using h1'
        · simpa using h2'
      have := ih b bd l (push X τ) (F X) Xs' h1 (fun pw hpw => hds pw (by simp [hpw]))
        (by simpa using hlen) (hF X hXA) (hg.2 Ad hAd X hXA) hS'
      rw [pushAll_cons, List.foldl_cons, happ]
      exact this
    all_goals simp [lamPeel] at hp

/-- `GradedBy` under a lift: the lifted term read in `ρ` is the term read with the inserted indices
skipped (from `den_lift`). -/
theorem gradedBy_lift (M : Model V env) {φ : LevelParam → Nat} (k : Nat) :
    ∀ (e : KExpr) (c : Nat) (ρ : BVarIdx → V),
      GradedBy (Denotes M.cval env φ) ρ (e.liftLooseBVars k c) ↔
        GradedBy (Denotes M.cval env φ) (skipEnv ρ k c) e := by
  intro e
  induction e with
  | bvar i =>
    intro c ρ
    simp only [Expr.liftLooseBVars]
    split <;> simp [GradedBy]
  | fvar _ _ _ => intro c ρ; simp [Expr.liftLooseBVars, GradedBy]
  | sort _ => intro c ρ; simp [Expr.liftLooseBVars, GradedBy]
  | const _ _ => intro c ρ; simp [Expr.liftLooseBVars, GradedBy]
  | app f a ihf iha =>
    intro c ρ
    simp only [Expr.liftLooseBVars, GradedBy, ihf, iha, den_lift]
  | lam ty b m iht ihb =>
    intro c ρ
    simp only [Expr.liftLooseBVars, GradedBy, iht, ihb, den_lift, skipEnv_push]
  | forallE ty b m iht ihb =>
    intro c ρ
    simp only [Expr.liftLooseBVars, GradedBy, iht, ihb, den_lift, skipEnv_push]
  | letE _ _ _ _ _ _ _ => intro c ρ; simp [Expr.liftLooseBVars, GradedBy]
  | lit _ => intro c ρ; simp [Expr.liftLooseBVars, GradedBy]
  | proj s i x ih =>
    intro c ρ
    simp only [Expr.liftLooseBVars, GradedBy, ih]

/-- Lifting past a binder keeps a graded reading (from `den_lift`). -/
theorem gradedBy_lift1 (M : Model V env) {φ : LevelParam → Nat} {ρ : BVarIdx → V} {a : KExpr}
    (X : V) (h : GradedBy (Denotes M.cval env φ) ρ a) :
    GradedBy (Denotes M.cval env φ) (push X ρ) (a.liftLooseBVars 1 0) := by
  rw [gradedBy_lift M 1 a 0 (push X ρ), skipEnv_push_one]
  exact h

theorem denotesList_lift1 {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} (X : V) :
    ∀ {as : List KExpr} {Xs : List V}, DenotesList cval env φ ρ as Xs →
      DenotesList cval env φ (push X ρ) (as.map (·.liftLooseBVars 1 0)) Xs
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by
    cases h with
    | cons ha hs =>
      refine .cons ?_ (denotesList_lift1 X hs)
      rw [den_lift, skipEnv_push_one]
      exact ha

/-- **A type read through δ and β puts the spine in a positive-regime product** (laws:
`defn_value` at each δ step, `graded` of each unfolded value). The site's arguments `as` denote `Xs`
at the site's environment `ρs` (assignment `φ`) and are graded there; each type variable `bnd`
knows stands for the argument's denotation. -/
theorem tyRead_pos (M : Model V env) (hδ : DefnValue M) (hgr : GradedLaw M.cval env)
    {φ : LevelParam → Nat} {ρs : BVarIdx → V} :
    ∀ {as : List KExpr} {ch : LChain} {bnd : Bnd} {T : KExpr} {ds : List PropWhen},
      TyRead env as ch bnd T ds → (∀ pw ∈ ds, pw.holds φ = false) →
      ∀ (σ : BVarIdx → V) (TT F : V) (Xs : List V),
        DenotesList M.cval env φ ρs as Xs → (∀ a ∈ as, GradedBy (Denotes M.cval env φ) ρs a) →
        (∀ i a, bnd[i]? = some (some a) →
          Denotes M.cval env φ ρs a (σ i) ∧ GradedBy (Denotes M.cval env φ) ρs a) →
        Denotes M.cval env (chainFn φ ch) σ T TT →
        GradedBy (Denotes M.cval env (chainFn φ ch)) σ T → F ∈ˢ TT → SpineMem F Xs →
        ∃ (v : Nat) (A : V) (B : V → V), v ≠ 0 ∧ Xs.foldl app F ∈ˢ piR v A B := by
  intro as ch bnd T ds hr
  induction hr with
  | @last ch bnd d b m =>
    intro hds σ TT F Xs hXs _ _ hT _ hF _
    cases hXs
    have hpw : m.pw.holds (chainFn φ ch) = false := by
      rw [← holds_pwChain]; exact hds _ (by simp)
    obtain ⟨Ad, Bf, -, -, -, rfl⟩ := den_pi.mp hT
    exact ⟨_, Ad, Bf, by simp [regime, hpw], hF⟩
  | @pi a as ch bnd d b m ds _ ih =>
    intro hds σ TT F Xs hXs hga hbnd hT hgT hF hS
    cases hXs with
    | @cons _ _ X Xs' hX hXs' =>
      have hpw : m.pw.holds (chainFn φ ch) = false := by
        rw [← holds_pwChain]; exact hds _ (by simp)
      have hv : regime (chainFn φ ch) m.pw ≠ 0 := by simp [regime, hpw]
      obtain ⟨Ad, Bf, hAd, hBf, -, rfl⟩ := den_pi.mp hT
      obtain ⟨r, A, B, hmem, hXA⟩ := hS 0 (by simp)
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hmem hXA
      have hr : r ≠ 0 := by
        rintro rfl
        exact not_pt_mem_piR_pos hv (eq_pt_of_mem_piR_zero hmem ▸ hF)
      have hdom : A = Ad := piR_dom_unique hr hv hmem hF
      rw [hdom] at hXA
      simp only [GradedBy] at hgT
      have hS' : SpineMem (app F X) Xs' := by
        intro j hj
        obtain ⟨r', A', B', h1', h2'⟩ := hS (j + 1) (by simpa using hj)
        exact ⟨r', A', B', by simpa [List.take_succ_cons, List.foldl_cons] using h1',
          by simpa using h2'⟩
      have hbnd' : ∀ i a', (some a :: bnd)[i]? = some (some a') →
          Denotes M.cval env φ ρs a' (push X σ i) ∧ GradedBy (Denotes M.cval env φ) ρs a' := by
        intro i a' hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          exact ⟨hX, hga _ (by simp)⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          exact hbnd i a' hi
      have := ih (fun pw hpw => hds pw (by simp [hpw])) (push X σ) (Bf X) (app F X) Xs' hXs'
        (fun a' ha' => hga a' (by simp [ha'])) hbnd' (hBf X hXA) (hgT.2 Ad hAd X hXA)
        (app_mem_piR_pos hv hF hXA) hS'
      simpa using this
  | @delta as ch bnd T D vs cv val hint lds body ds hfn hfind hlen hpeel _ ih =>
    intro hds σ TT F Xs hXs hga _ hT hgT hF hS
    have hlds : ∀ pw ∈ lds, pw.holds (chainFn φ ((cv.levelParams, vs) :: ch)) = false := by
      intro pw hpw
      rw [← holds_pwChain]
      exact hds _ (List.mem_append_left _ (List.mem_map_of_mem hpw))
    have hds' : ∀ pw ∈ ds, pw.holds φ = false := fun pw hpw => hds pw (List.mem_append_right _ hpw)
    have hTe : Expr.mkAppN (.const D vs) T.getAppArgs = T := by
      rw [← hfn]; exact mkAppN_getApp T
    rw [← hTe] at hT hgT
    obtain ⟨G0, Ys, hG0, hYs, rfl⟩ := (den_mkAppN _).mp hT
    have hG0e : G0 = M.cval D (Level.substFn (chainFn φ ch) cv.levelParams vs) := by
      cases hG0 with
      | const hf _ => rw [hfind] at hf; cases hf; rfl
    have hname : cv.name = D := find_name hfind
    have hval := hδ cv val hint (find_mem hfind) (chainFn φ ((cv.levelParams, vs) :: ch)) σ
    rw [hname] at hval
    have hgval := (hgr _ (find_mem hfind) (chainFn φ ((cv.levelParams, vs) :: ch)) σ).2 cv val
      hint rfl
    have hSY : SpineMem G0 Ys := spineMem_of_graded M _ hgT hG0 hYs
    have hlenY : Ys.length = T.getAppArgs.length := denotesList_length hYs
    obtain ⟨hbody, hgbody⟩ := beta_peel M _ val body lds σ G0 Ys hpeel hlds hlenY
      (by rw [hG0e]; exact hval) hgval hSY
    exact ih hds' (pushAll Ys σ) (Ys.foldl app G0) F Xs hXs hga (fun i a h => by simp at h)
      hbody hgbody hF hS
  | @bvar as ch bnd T i a lds body ds hfn hbi hpeel _ ih =>
    intro hds σ TT F Xs hXs hga hbnd hT hgT hF hS
    have hlds : ∀ pw ∈ lds, pw.holds φ = false := fun pw h => hds pw (List.mem_append_left _ h)
    have hds' : ∀ pw ∈ ds, pw.holds φ = false := fun pw h => hds pw (List.mem_append_right _ h)
    have hTe : Expr.mkAppN (.bvar i) T.getAppArgs = T := by
      rw [← hfn]; exact mkAppN_getApp T
    rw [← hTe] at hT hgT
    obtain ⟨G0, Ys, hG0, hYs, rfl⟩ := (den_mkAppN _).mp hT
    have hG0e : G0 = σ i := den_bvar.mp hG0
    obtain ⟨ha, hga'⟩ := hbnd i a hbi
    have hSY : SpineMem G0 Ys := spineMem_of_graded M _ hgT hG0 hYs
    have hlenY : Ys.length = T.getAppArgs.length := denotesList_length hYs
    obtain ⟨hbody, hgbody⟩ := beta_peel M (ψ := φ) _ a body lds ρs G0 Ys hpeel hlds hlenY
      (by rw [hG0e]; exact ha) hga' hSY
    exact ih hds' (pushAll Ys ρs) (Ys.foldl app G0) F Xs hXs hga (fun i a h => by simp at h)
      hbody hgbody hF hS

/-- The context's types are graded, each in the environment its binder sees. -/
def GradedCtx (M : Model V env) (φ : LevelParam → Nat) : List KExpr → (BVarIdx → V) → Prop
  | [], _ => True
  | A :: Γ, ρ => GradedBy (Denotes M.cval env φ) (fun i => ρ (i + 1)) A ∧
      GradedCtx M φ Γ (fun i => ρ (i + 1))

theorem gradedCtx_get {M : Model V env} {φ : LevelParam → Nat} :
    ∀ {Γ : List KExpr} {ρ : BVarIdx → V} {i : Nat} {A : KExpr},
      GradedCtx M φ Γ ρ → Γ[i]? = some A →
        GradedBy (Denotes M.cval env φ) (fun j => ρ (j + (i + 1))) A
  | [], _, _, _, _, h => by simp at h
  | _ :: _, _, 0, _, hs, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [GradedCtx] at hs
    exact hs.1
  | _ :: _, _, _ + 1, _, hs, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [GradedCtx] at hs
    have h' := gradedCtx_get hs.2 h
    exact h'

/-- **The context and the copy stay graded down a witness path** (the witness shape): below a term
graded with its context in every environment satisfying `Γ`, in every environment satisfying the
path's λs over `Γ` the extended context is graded (`GradedBy`'s λ clause grades each domain) and so
is the copy. -/
theorem gradedCtx_under (M : Model V env) {φ : LevelParam → Nat} {cp : KExpr} :
    ∀ {Δ : List KExpr} {e : KExpr}, UnderLams cp Δ e → ∀ {Γ : List KExpr},
      (∀ ρ, CtxSat M φ Γ ρ → GradedCtx M φ Γ ρ ∧ GradedBy (Denotes M.cval env φ) ρ e) →
      ∀ ρ, CtxSat M φ (Δ.reverse ++ Γ) ρ →
        GradedCtx M φ (Δ.reverse ++ Γ) ρ ∧ GradedBy (Denotes M.cval env φ) ρ cp := by
  intro Δ e h
  induction h with
  | here hs =>
    intro Γ hg ρ hρ
    have h1 := hg ρ (by simpa using hρ)
    exact ⟨by simpa using h1.1, gradedBy_of_subAt0 hs h1.2⟩
  | appL _ ih =>
    intro Γ hg
    exact ih fun ρ hρ => by
      obtain ⟨h0, h1⟩ := hg ρ hρ
      simp only [GradedBy] at h1
      exact ⟨h0, h1.1⟩
  | appR _ ih =>
    intro Γ hg
    exact ih fun ρ hρ => by
      obtain ⟨h0, h1⟩ := hg ρ hρ
      simp only [GradedBy] at h1
      exact ⟨h0, h1.2.1⟩
  | proj _ ih =>
    intro Γ hg
    exact ih fun ρ hρ => by
      obtain ⟨h0, h1⟩ := hg ρ hρ
      simp only [GradedBy] at h1
      exact ⟨h0, h1⟩
  | @lam Δ' A b m _ ih =>
    intro Γ hg ρ hρ
    have hg' : ∀ ρ, CtxSat M φ (A :: Γ) ρ →
        GradedCtx M φ (A :: Γ) ρ ∧ GradedBy (Denotes M.cval env φ) ρ b := by
      intro ρ hρ
      cases hρ with
      | cons hΓ hX hmem =>
        obtain ⟨h0, h1⟩ := hg _ hΓ
        simp only [GradedBy] at h1
        have h2 := h1.2 _ hX _ hmem
        have hpush : push (ρ 0) (fun i => ρ (i + 1)) = ρ := by funext i; cases i <;> rfl
        rw [hpush] at h2
        refine ⟨?_, h2⟩
        simp only [GradedCtx]
        exact ⟨h1.1, h0⟩
    have h3 := ih hg' ρ (by simpa only [List.reverse_cons, List.append_assoc,
      List.singleton_append] using hρ)
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h3

/-- **`graded_sites` with the context**: below a graded term, at every evaluated site, the context's
types are graded too (`GradedBy`'s λ clause grades the domain). -/
theorem graded_sites_ctx (M : Model V env) {φ : LevelParam → Nat} {ls : Levels} :
    ∀ (t : Term) (Γ : List KExpr) (e : KExpr),
      (∀ ρ, CtxSat M φ Γ ρ → GradedCtx M φ Γ ρ ∧ GradedBy (Denotes M.cval env φ) ρ e) →
      ∀ s ∈ evalSites ls Γ t e, ∀ ρ, CtxSat M φ s.1 ρ →
        GradedCtx M φ s.1 ρ ∧ GradedBy (Denotes M.cval env φ) ρ (.app s.2.1 s.2.2) := by
  intro t
  induction t with
  | app f a md r ihf iha =>
    intro Γ e hg s hs
    cases e with
    | app f' a' =>
      simp only [evalSites, List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | hs | hs
      · exact hg
      · exact ihf Γ f' (fun ρ hρ => by
          obtain ⟨h0, h1⟩ := hg ρ hρ
          simp only [GradedBy] at h1
          exact ⟨h0, h1.1⟩) s hs
      · by_cases hirr : r.irrAt ls = true
        · simp [hirr] at hs
        · simp [hirr] at hs
          exact iha Γ a' (fun ρ hρ => by
            obtain ⟨h0, h1⟩ := hg ρ hρ
            simp only [GradedBy] at h1
            exact ⟨h0, h1.2.1⟩) s hs
    | _ => simp [evalSites] at hs
  | lam b d body ihd ihb =>
    intro Γ e hg s hs
    cases e with
    | lam d' body' mb =>
      simp only [evalSites] at hs
      refine ihb (d' :: Γ) body' (fun ρ hρ => ?_) s hs
      cases hρ with
      | cons hΓ hX hmem =>
        obtain ⟨h0, h1⟩ := hg _ hΓ
        simp only [GradedBy] at h1
        have h2 := h1.2 _ hX _ hmem
        have hpush : push (ρ 0) (fun i => ρ (i + 1)) = ρ := by funext i; cases i <;> rfl
        rw [hpush] at h2
        refine ⟨?_, h2⟩
        simp only [GradedCtx]
        exact ⟨h1.1, h0⟩
    | _ => simp [evalSites] at hs
  | proj s0 i e0 ih =>
    intro Γ e hg s hs
    cases e with
    | proj _ _ e' =>
      simp only [evalSites] at hs
      exact ih Γ e' (fun ρ hρ => by
        obtain ⟨h0, h1⟩ := hg ρ hρ
        simp only [GradedBy] at h1
        exact ⟨h0, h1⟩) s hs
    | _ => simp [evalSites] at hs
  | letE c r ty v b _ ihv ihb =>
    intro Γ e hg s hs
    simp only [evalSites, List.mem_append] at hs
    rcases hs with hs | hs
    · cases hz : zcopy b e with
      | none => simp [hz] at hs
      | some v' =>
        simp only [hz] at hs
        cases hsub : subAt0B v' e
        · simp [hsub] at hs
        · simp only [hsub, Bool.not_true, Bool.or_false] at hs
          split at hs
          · simp at hs
          · exact ihv Γ v' (fun ρ hρ => ⟨(hg ρ hρ).1,
              gradedBy_of_subAt0 (subAt0_of_check hsub) (hg ρ hρ).2⟩) s hs
    · rcases hs with hs | hs
      · -- the closure-capture shape (step C): as at a λ, then through the copy
        cases hc : cloSite? b e with
        | none => simp [hc] at hs
        | some p =>
          obtain ⟨A, cp⟩ := p
          simp only [hc] at hs
          split at hs
          · simp at hs
          · obtain ⟨b', m, rfl, hsub⟩ := cloSite?_spec hc
            refine ihv (A :: Γ) cp (fun ρ hρ => ?_) s hs
            cases hρ with
            | cons hΓ hX hmem =>
              obtain ⟨h0, h1⟩ := hg _ hΓ
              simp only [GradedBy] at h1
              have h2 := h1.2 _ hX _ hmem
              have hpush : push (ρ 0) (fun i => ρ (i + 1)) = ρ := by funext i; cases i <;> rfl
              rw [hpush] at h2
              refine ⟨?_, gradedBy_of_subAt0 hsub h2⟩
              simp only [GradedCtx]
              exact ⟨h1.1, h0⟩
      · rcases hs with hs | hs
        · -- the witness shape: as at each λ of the path, then through the copy
          cases hw : witSite? b e with
          | none => simp [hw] at hs
          | some p =>
            obtain ⟨Δ, cp⟩ := p
            simp only [hw] at hs
            split at hs
            · simp at hs
            · obtain ⟨_, _, _, _, _, hu, _⟩ := witSite?_spec hw
              exact ihv (Δ.reverse ++ Γ) cp (gradedCtx_under M hu hg) s hs
        · exact ihb Γ e hg s hs
  | _ => intro Γ e _ s hs; cases e <;> simp [evalSites] at hs

/-- **A value spine read through δ and β lies in a positive-regime product** (a constant by `mem`,
a bound variable by `CtxSat`, a λ by β with its own datum). -/
theorem spineRead_pos (M : Model V env) (hδ : DefnValue M) (hgr : GradedLaw M.cval env)
    {φ : LevelParam → Nat} :
    ∀ {Γ : List KExpr} {h : KExpr} {as : List KExpr} {ds : List PropWhen},
      SpineRead env Γ h as ds → (∀ pw ∈ ds, pw.holds φ = false) →
      ∀ (ρ : BVarIdx → V) (H : V) (Xs : List V), CtxSat M φ Γ ρ → GradedCtx M φ Γ ρ →
        DenotesList M.cval env φ ρ as Xs → (∀ a ∈ as, GradedBy (Denotes M.cval env φ) ρ a) →
        Denotes M.cval env φ ρ h H → GradedBy (Denotes M.cval env φ) ρ h → SpineMem H Xs →
        ∃ (v : Nat) (A : V) (B : V → V), v ≠ 0 ∧ Xs.foldl app H ∈ˢ piR v A B := by
  intro Γ h as ds hr
  induction hr with
  | @const Γ k us ci as ds hfind hlen hty =>
    intro hds ρ H Xs _ _ hXs hga hH _ hS
    have hHe : H = M.cval k (Level.substFn φ ci.toConstantVal.levelParams us) := by
      cases hH with
      | const hf _ => rw [hfind] at hf; cases hf; rfl
    obtain ⟨TT, hTT, hmem⟩ := mem_key M hfind (Level.substFn φ ci.toConstantVal.levelParams us) ρ
    have hgT := (hgr _ (find_mem hfind) (Level.substFn φ ci.toConstantVal.levelParams us) ρ).1
    exact tyRead_pos M hδ hgr (ρs := ρ) hty hds ρ TT H Xs hXs hga (fun i a h => by simp at h)
      hTT hgT (by rw [hHe]; exact hmem) hS
  | @bvar Γ i T as ds hget hty =>
    intro hds ρ H Xs hρ hΓ hXs hga hH _ hS
    have hHe : H = ρ i := den_bvar.mp hH
    obtain ⟨TT, hTT, hmem⟩ := ctxSat_get hρ hget
    exact tyRead_pos M hδ hgr (ρs := ρ) hty hds (fun j => ρ (j + (i + 1))) TT H Xs hXs hga
      (fun i a h => by simp at h) hTT (gradedCtx_get hΓ hget) (by rw [hHe]; exact hmem) hS
  | @lam0 Γ d b m =>
    intro hds ρ H Xs _ _ hXs _ hH _ _
    cases hXs
    have hpw : m.pw.holds φ = false := hds _ (by simp)
    have hv : regime φ m.pw ≠ 0 := by simp [regime, hpw]
    obtain ⟨Ad, F, -, -, -, rfl⟩ := den_lam.mp hH
    exact ⟨_, Ad, fun x => sing (F x), hv, lamR_mem (fun x _ => mem_sing.mpr rfl)⟩
  | @lam Γ d b m a as ds _ ih =>
    intro hds ρ H Xs hρ hΓ hXs hga hH hgH hS
    cases hXs with
    | @cons _ _ X Xs' hX hXs' =>
      have hpw : m.pw.holds φ = false := hds _ (by simp)
      have hv : regime φ m.pw ≠ 0 := by simp [regime, hpw]
      obtain ⟨Ad, F, hAd, hF, -, rfl⟩ := den_lam.mp hH
      obtain ⟨r, A, B, hmem, hXA⟩ := hS 0 (by simp)
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hmem hXA
      have hr : r ≠ 0 := by
        rintro rfl
        exact lamR_ne_pt hv (eq_pt_of_mem_piR_zero hmem)
      have hdom : Ad = A := piR_dom_unique hv hr
        (lamR_mem (B := fun x => sing (F x)) (fun x _ => mem_sing.mpr rfl)) hmem
      rw [← hdom] at hXA
      have happ : app (lamR (regime φ m.pw) Ad F) X = F X := app_lamR_pos hv hXA
      simp only [GradedBy] at hgH
      obtain ⟨hgd, hgb⟩ := hgH
      have hgb' := hgb Ad hAd X hXA
      have hFX := hF X hXA
      have hbe : Expr.mkAppN b.getAppFn b.getAppArgs = b := mkAppN_getApp b
      rw [← hbe] at hFX hgb'
      obtain ⟨Hb, Zs, hHb, hZs, hFXe⟩ := (den_mkAppN _).mp hFX
      have hgp := gradedBy_mkAppN _ hgb'
      have hSZ : SpineMem Hb Zs := spineMem_of_graded M _ hgb' hHb hZs
      have hga' : ∀ a' ∈ b.getAppArgs ++ as.map (·.liftLooseBVars 1 0),
          GradedBy (Denotes M.cval env φ) (push X ρ) a' := by
        intro a' ha'
        rcases List.mem_append.mp ha' with h1 | h2
        · exact hgp.2 a' h1
        · obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp h2
          exact gradedBy_lift1 M X (hga a0 (by simp [ha0]))
      have hS' : SpineMem Hb (Zs ++ Xs') := by
        intro j hj
        by_cases hjz : j < Zs.length
        · obtain ⟨r', A', B', h1, h2⟩ := hSZ j hjz
          refine ⟨r', A', B', ?_, ?_⟩
          · rwa [List.take_append_of_le_length (Nat.le_of_lt hjz)]
          · simpa [List.getElem_append_left hjz] using h2
        · obtain ⟨j', rfl⟩ : ∃ j', j = Zs.length + j' := ⟨j - Zs.length, by omega⟩
          have hj' : j' < Xs'.length := by simp at hj; omega
          obtain ⟨r', A', B', h1, h2⟩ := hS (j' + 1) (by simpa using hj')
          refine ⟨r', A', B', ?_, ?_⟩
          · have htk : (Zs ++ Xs').take (Zs.length + j') = Zs ++ Xs'.take j' :=
              List.take_length_add_append j'
            simp only [List.take_succ_cons, List.foldl_cons, happ] at h1
            rw [htk, List.foldl_append, ← hFXe]
            exact h1
          · simpa [List.getElem_append_right] using h2
      obtain ⟨v, A', B', hv', hm'⟩ := ih (fun pw h => hds pw (by simp [h])) (push X ρ) Hb
        (Zs ++ Xs') (ctxSat_push hρ hAd hXA) (by simp only [GradedCtx]; exact ⟨hgd, hΓ⟩)
        (denotesList_append hZs (denotesList_lift1 X hXs')) hga' hHb hgp.1 hS'
      refine ⟨v, A', B', hv', ?_⟩
      rw [List.foldl_cons, happ, hFXe, ← List.foldl_append]
      exact hm'

/-- **The head's regime through δ and β puts a site's function in a positive-regime product.** -/
theorem head_posG (M : Model V env) (hδ : DefnValue M) (hgr : GradedLaw M.cval env)
    {φ : LevelParam → Nat} {Γ : List KExpr} {ρ : BVarIdx → V} {f : KExpr} {F : V}
    (hH : HeadReadAt env φ Γ f) (hρ : CtxSat M φ Γ ρ) (hΓ : GradedCtx M φ Γ ρ)
    (hF : Denotes M.cval env φ ρ f F) (hg : GradedBy (Denotes M.cval env φ) ρ f) :
    ∃ (v : Nat) (A : V) (B : V → V), v ≠ 0 ∧ F ∈ˢ piR v A B := by
  obtain ⟨ds, hr, hds⟩ := hH
  have hfe : Expr.mkAppN f.getAppFn f.getAppArgs = f := mkAppN_getApp f
  rw [← hfe] at hF hg
  obtain ⟨H, Xs, hH0, hXs, rfl⟩ := (den_mkAppN _).mp hF
  have hgp := gradedBy_mkAppN _ hg
  exact spineRead_pos M hδ hgr hr hds ρ H Xs hρ hΓ hXs hgp.2 hH0 hgp.1
    (spineMem_of_graded M _ hg hH0 hXs)

/-- **`SitesOk` from `graded`** (laws: `graded`, `defn_value`, and `Model.mem`): every evaluated
site, not only those the direct route refuses. -/
theorem sitesOk_of_headRegime {M : Model V env} (hδ : DefnValue M) (hgr : GradedLaw M.cval env)
    {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann}
    {S : CId → Prop} (hH : HeadRegime p env κ lpsOf ann S) : SitesOk M p κ lpsOf ann S := by
  intro c ls t e hS hOk hrp φ hlv s hs ρ hρ
  obtain ⟨hgc, hg⟩ := graded_sites_ctx M t [] e
    (fun ρ' _ => ⟨by simp [GradedCtx], runPair_graded M hgr hrp φ ρ'⟩) s hs ρ hρ
  simp only [GradedBy] at hg
  obtain ⟨hgf, -, r, A, F, X, B, hF, hX, hmem, hXA, -⟩ := hg
  obtain ⟨v, A', B', hv, hFv⟩ :=
    head_posG M hδ hgr (hH c ls t e hS hOk hrp φ hlv s hs) hρ hgc hF hgf
  have hr : r ≠ 0 := by
    rintro rfl
    exact not_pt_mem_piR_pos hv (eq_pt_of_mem_piR_zero hmem ▸ hFv)
  exact ⟨F, X, r, A, B, hF, hX, hr, hmem, hXA⟩

end Walk

/-! ## The root theorem with no typing hypothesis and without the direct route -/

section Root

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- `rootSound_678A` with `SitesOk` in place of `SitesOkRes` (no `sitesOk_of_res`): proved here, as
`rootSound_678A` is, from the landed pieces. -/
theorem rootSound_678AS (hL : Laws678 M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFactsRead p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  have hLN := lawsNoCanon_of_678 hL hLD
  rootSound_core hLN.core hG hR
    (allP (fundHyps_of_inst hLN.core (.inr hNC.recs) hG hT hI
      (caseFires_of_inst hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hG.natBasis hC hNC
        hU)))
    ⟨hR.ok, hroot⟩ hA hrun hrb hRT hO φ ρ X hX

/-- **The root theorem over #678's six fields with every site typed from `graded`**: `rootSound_678G`
with `HeadRegime` (every site, δ and β at the head's type) for `HeadRegimeRes` (the refused sites, as
written). Its conclusion is `rootSound_678`'s word for word. -/
theorem rootSound_678AG (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFactsRead p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hH : HeadRegime p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678AS hL hG hC hNC hLD hI hU hroot hR
    (sitesOk_of_headRegime hL.defnValue hgr hH) hA hrun hrb hRT hO φ ρ X hX

/-- **The same from the Boolean checks**: `groundCheck`, `noCanonAB`, `litDefsB`, `instCheckB` with
the root as its seed, `headRegimeSB` (the per-spine decision), and the root's facts; no typing
hypothesis. -/
theorem rootSound_678AG_of_check (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p env κ lpsOf ann Sl = true)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  obtain ⟨hseeds, hI, hU⟩ := instFacts_of_check hinst
  exact rootSound_678AG hL hgr (groundFacts_of_check hchk) (caseFactsRead_of_check hchk)
    (noCanonA_of_check hnc) (litDefs_of_check hld) hI hU (hseeds root (List.mem_singleton_self _))
    (headRegimeS_of_check hchk hhr) hR hA hrun hrb hRT hO φ ρ X hX

end Root

end IxCC.Grounding
