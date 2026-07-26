import Ix.Tc.Env
import Lean4Lean.Theory.Typing.Env

/-!
# Non-circular verification worlds

This is the additive G1a model.  It separates four things which the old
whole-`KEnv` relation conflates:

* `Catalog`: immutable ghost input, including pending and unrelated
  declarations;
* `VerifyWorld.trusted`: the ghost index intended to track declarations
  already admitted to the semantic world;
* `VerifyWorld.venv`: the well-formed Lean4Lean environment for that trusted
  world;
* `LoadedAgrees`: the one-way relation from the concrete lazy-load cache to
  the catalog.

Crucially, being catalogued is not a typing fact.  `VerifyWorld.ofCatalog`
accepts an arbitrary catalog while trusting nothing, and `LoadedAgrees` does
not require every catalog entry to be loaded.  The trusted-catalog semantic
log is deliberately not faked as a bare structure field: G1c's
`TrustedCatalogRel` in `Verify/Env.lean` is an explicit proof object connecting
`trusted` to `venv`.  Consumers must carry that relation before treating
trusted membership as a WF witness.

This module was introduced beside the old whole-`KEnv` relation in G1a.
`Verify/State.lean` now uses it for `TcInv`, and G2b consumers resolve exact
constants through `TrustedConstRel`. The legacy `TrKEnv` remains only as a
quarantined compatibility proof interface.
-/

namespace Ix.Tc

open Lean4Lean (VEnv)

/-- Immutable ghost input.  A catalog entry says which concrete declaration
is committed at an id; it says nothing about that declaration's typing. -/
abbrev Catalog := KId .anon → Option (KConst .anon)

namespace Catalog

/-- The empty declaration catalog. -/
def empty : Catalog := fun _ => none

/-- `id` has a concrete declaration in the catalog. -/
def Contains (catalog : Catalog) (id : KId .anon) : Prop :=
  ∃ c, catalog id = some c

@[simp] theorem empty_apply (id : KId .anon) : empty id = none := rfl

end Catalog

/-- Ghost semantic state for verification.

`trustedCatalogued` is representation coherence only.  It prevents the
trusted index from naming a declaration absent from the immutable input, but
does not assert `KConst`/`VConstant` translation or any WF judgment.  Those
semantic witnesses belong to `TrustedCatalogRel`. -/
structure VerifyWorld where
  catalog : Catalog
  trusted : KId .anon → Prop
  venv : VEnv
  nameOf : Address → Option Lean.Name
  venvWF : venv.WF
  trustedCatalogued : ∀ {id}, trusted id → Catalog.Contains catalog id

namespace VerifyWorld

/-- An arbitrary immutable catalog with no trusted declarations and an empty
semantic environment.  No premise asks the catalog declarations to be
well-typed. -/
def ofCatalog (catalog : Catalog) : VerifyWorld where
  catalog := catalog
  trusted := fun _ => False
  venv := .empty
  nameOf := fun _ => none
  venvWF := ⟨[], .empty⟩
  trustedCatalogued := fun {_} h => False.elim h

/-- The completely empty verification world. -/
def empty : VerifyWorld := ofCatalog Catalog.empty

@[simp] theorem ofCatalog_catalog (catalog : Catalog) :
    (ofCatalog catalog).catalog = catalog := rfl

@[simp] theorem ofCatalog_trusted (catalog : Catalog) (id : KId .anon) :
    ¬(ofCatalog catalog).trusted id := fun h => h

@[simp] theorem ofCatalog_venv (catalog : Catalog) :
    (ofCatalog catalog).venv = .empty := rfl

/-- Adversarial sanity check for the new boundary: a declaration can be
catalogued without becoming trusted.  There is intentionally no WF premise. -/
theorem ofCatalog_catalogued_not_trusted {catalog : Catalog}
    {id : KId .anon} {c : KConst .anon} (h : catalog id = some c) :
    Catalog.Contains (ofCatalog catalog).catalog id ∧
      ¬(ofCatalog catalog).trusted id :=
  ⟨⟨c, h⟩, ofCatalog_trusted _ _⟩

/-- World extension keeps immutable input and address-to-name assignment
fixed, while allowing the trusted index and its well-formed semantic
environment to grow.  Concrete lazy-loaded entries are related separately
by `LoadedExtension` below because they live in `KEnv`, not `VerifyWorld`. -/
protected structure LE (before after : VerifyWorld) : Prop where
  catalog : before.catalog = after.catalog
  nameOf : before.nameOf = after.nameOf
  trusted : ∀ {id}, before.trusted id → after.trusted id
  venv : before.venv ≤ after.venv

instance : LE VerifyWorld := ⟨VerifyWorld.LE⟩

namespace LE

theorem rfl {world : VerifyWorld} : world ≤ world :=
  ⟨Eq.refl _, Eq.refl _, fun {_} h => h, VEnv.LE.rfl⟩

theorem trans {a b c : VerifyWorld} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  ⟨hab.catalog.trans hbc.catalog,
    hab.nameOf.trans hbc.nameOf,
    fun {_} h => hbc.trusted (hab.trusted h),
    hab.venv.trans hbc.venv⟩

/-- Catalog membership is invariant under world extension. -/
theorem catalogued_iff {before after : VerifyWorld} (h : before ≤ after)
    {id : KId .anon} :
    Catalog.Contains before.catalog id ↔
      Catalog.Contains after.catalog id := by
  rw [h.catalog]

end LE

end VerifyWorld

/-- Every concrete constant currently loaded in `env` is exactly the entry
committed by `catalog`.  The implication is intentionally one-way: catalog
entries may remain unloaded under lazy ingress. -/
def LoadedAgrees (catalog : Catalog) (env : KEnv .anon) : Prop :=
  ∀ {id c}, env.get? id = some c → catalog id = some c

namespace LoadedAgrees

theorem lookup {catalog : Catalog} {env : KEnv .anon}
    (h : LoadedAgrees catalog env) {id : KId .anon} {c : KConst .anon}
    (hget : env.get? id = some c) : catalog id = some c :=
  h hget

/-- Empty concrete state agrees with every catalog, including a nonempty or
ill-typed one.  This is the lazy-load direction of the relation. -/
theorem empty (catalog : Catalog) :
    LoadedAgrees catalog ({} : KEnv .anon) := by
  intro id c hget
  simp [KEnv.get?] at hget

/-- Since world extension fixes the catalog, loaded agreement is invariant
under it. -/
theorem world_iff {before after : VerifyWorld} (h : before ≤ after)
    {env : KEnv .anon} :
    LoadedAgrees before.catalog env ↔ LoadedAgrees after.catalog env := by
  rw [h.catalog]

section Insert

variable [LawfulBEq (KId .anon)] [LawfulHashable (KId .anon)]

/-- A lazy-load insertion preserves agreement when the inserted declaration
is the catalog entry.  The lawfulness instances are hypotheses here; G1a
does not move the existing global instances out of `Verify/Env.lean`. -/
theorem insert {catalog : Catalog} {env : KEnv .anon}
    (h : LoadedAgrees catalog env) {id : KId .anon} {c : KConst .anon}
    (hc : catalog id = some c) : LoadedAgrees catalog (env.insert id c) := by
  intro j d hget
  simp only [KEnv.get?, KEnv.insert, Std.HashMap.getElem?_insert] at hget
  split at hget
  · next heq =>
    cases hget
    have hij : id = j := eq_of_beq heq
    subst j
    exact hc
  · exact h hget

end Insert

end LoadedAgrees

/-- The loaded-constant portion of a concrete environment only grows.  Cache,
intern-table, block, and fuel evolution are intentionally outside this
relation and will be conjoined by the later state invariant. -/
structure LoadedExtension (before after : KEnv .anon) : Prop where
  consts : ∀ {id c}, before.get? id = some c → after.get? id = some c

namespace LoadedExtension

theorem rfl {env : KEnv .anon} : LoadedExtension env env :=
  ⟨fun {_ _} h => h⟩

theorem trans {a b c : KEnv .anon} (hab : LoadedExtension a b)
    (hbc : LoadedExtension b c) : LoadedExtension a c :=
  ⟨fun {_ _} h => hbc.consts (hab.consts h)⟩

end LoadedExtension

/-- Agreement of a larger loaded cache implies agreement of every earlier
loaded-cache prefix. -/
theorem LoadedAgrees.of_extension {catalog : Catalog} {before after : KEnv .anon}
    (hext : LoadedExtension before after) (h : LoadedAgrees catalog after) :
    LoadedAgrees catalog before :=
  fun {_ _} hget => h (hext.consts hget)

/-- `ofCatalog` is inhabited together with an empty concrete load cache for
every catalog, without a declaration-WF premise. -/
theorem VerifyWorld.ofCatalog_loaded (catalog : Catalog) :
    LoadedAgrees (VerifyWorld.ofCatalog catalog).catalog ({} : KEnv .anon) :=
  LoadedAgrees.empty catalog

section CataloguedLoaded

variable [LawfulBEq (KId .anon)] [LawfulHashable (KId .anon)]

/-- Stronger adversarial fixture: an arbitrary catalog declaration may be
present in the concrete lazy-load cache while remaining untrusted.  The
construction needs exact catalog agreement, but deliberately no translation
or declaration-WF witness. -/
theorem VerifyWorld.ofCatalog_loaded_not_trusted {catalog : Catalog}
    {id : KId .anon} {c : KConst .anon} (hcat : catalog id = some c) :
    LoadedAgrees (VerifyWorld.ofCatalog catalog).catalog
        (({} : KEnv .anon).insert id c) ∧
      ¬(VerifyWorld.ofCatalog catalog).trusted id :=
  ⟨LoadedAgrees.insert (LoadedAgrees.empty catalog) hcat,
    VerifyWorld.ofCatalog_trusted _ _⟩

end CataloguedLoaded

end Ix.Tc
