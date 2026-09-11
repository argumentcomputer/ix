/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Typing.Env
import Ix.Theory.Named.Typing.Meta

namespace Ix.Theory.Named
namespace VEnv

theorem addQuot_WF (henv : Ordered env) (hq : QuotReady env) :
    addQuot env = some env' → Ordered env' := by
  refine with_addConst (cis := [.const _ eqConst]) (hcis := ⟨hq, ⟨⟩⟩) henv
    (fun _ => ⟨_, by type_tac⟩) fun henv => ?_
  refine with_addConst henv (fun ⟨quot, _⟩ => ⟨_, by type_tac⟩) fun henv => ?_
  refine with_addConst henv (fun ⟨_, quot, eq, _⟩ => ⟨_, by type_tac⟩) fun henv => ?_
  refine with_addConst henv (fun ⟨_, _, quot, _⟩ => ⟨_, by type_tac⟩) fun henv => ?_
  rintro ⟨_, _, _, _, eq, _⟩ ⟨⟩; exact .defeq henv ⟨by type_tac, by type_tac⟩

section
variable (henv : addQuot env = some env') include henv

theorem addQuot_objs : env'.HasObjects [.defeq quotDefEq, .const `Quot.ind quotIndConst,
    .const `Quot.lift quotLiftConst, .const `Quot.mk quotMkConst, .const `Quot quotConst] := by
  let ⟨env, h, henv⟩ := HasObjects.bind_const (ls := []) trivial henv
  let ⟨env, h, henv⟩ := HasObjects.bind_const h henv
  let ⟨env, h, henv⟩ := HasObjects.bind_const h henv
  obtain ⟨env, h, ⟨⟩⟩ := HasObjects.bind_const h henv
  exact HasObjects.defeq (df := quotDefEq) h

theorem addQuot_quot : env'.constants ``Quot = quotConst := (addQuot_objs henv).2.2.2.2.1
theorem addQuot_quotMk : env'.constants ``Quot.mk = quotMkConst := (addQuot_objs henv).2.2.2.1
theorem addQuot_quotLift : env'.constants ``Quot.lift = quotLiftConst := (addQuot_objs henv).2.2.1
theorem addQuot_quotInd : env'.constants ``Quot.ind = quotIndConst := (addQuot_objs henv).2.1
theorem addQuot_defeq : env'.defeqs quotDefEq := (addQuot_objs henv).1

end
