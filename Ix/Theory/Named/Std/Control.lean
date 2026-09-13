/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/


instance [Alternative m] : MonadLift Option m := ⟨fun | none => failure | some a => pure a⟩
