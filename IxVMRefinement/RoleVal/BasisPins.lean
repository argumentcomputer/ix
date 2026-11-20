import IxVMRefinement.Obs.KernelRoles
import IxVMRefinement.RoleVal.CommittedBase
import IxVMRefinement.Roles.Tables
import IxVMRefinement.Core.Seams

/-! # The committed address returned by a successful basis pin lookup -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core

private theorem addr_snoc (h : Heap F) (bs : List UInt8) (hlen : bs.length = 32) :
    BaseSeams.addr (h ++ [.tuple (bs.map fun b => .field (b.toNat : F))])
      (.ptr addrTy h.length) (mkAddr bs) := by
  let a : Bytes.Address := ⟨bs.toArray, by simpa using hlen⟩
  refine ⟨a, ?_, ?_⟩
  · refine ⟨h.length, .tuple (bs.map fun b => .field (b.toNat : F)), rfl, ?_, ?_⟩
    · simp
    · simp [Bytes.RepAddress, a]
  · simp [ixAddr, mkAddr, a]

/-- If a role lookup returns the pinned flag, its address is the committed table's address. -/
theorem basis_pin_bound {ro : Ix.Kernel.Role} {ptr : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelRoles::basis_pin" [.field (roleNum ro)] h
      (.tuple [.field 1, ptr]) h' calls) :
    ∃ a, committedDefaultRoleTable.addressOf? ro = some a ∧ BaseSeams.addr h' ptr a := by
  match Obs.«KernelRoles::basis_pin».obs ev with
  | .n0 (hv14 := hi) (he19 := hp) (hm35 := hm) (he262 := hh) .. =>
    have hr : ro = .nat := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [238, 93, 66, 79, 111, 187, 84, 16,
       206, 130, 164, 101, 124, 88, 110, 216,
       220, 87, 235, 37, 136, 148, 117, 120,
       99, 102, 118, 228, 46, 208, 7, 43]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n1 (hv268 := hi) (he273 := hp) (hm289 := hm) (he516 := hh) .. =>
    have hr : ro = .natZero := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [9, 133, 26, 4, 34, 161, 136, 34,
       68, 125, 151, 133, 18, 59, 70, 190,
       29, 83, 241, 162, 208, 19, 121, 146,
       254, 22, 174, 105, 60, 179, 240, 125]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n2 (hv522 := hi) (he527 := hp) (hm543 := hm) (he770 := hh) .. =>
    have hr : ro = .natSucc := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [117, 124, 169, 221, 187, 253, 252, 185,
       57, 164, 44, 22, 76, 67, 93, 237,
       230, 214, 210, 52, 39, 159, 137, 225,
       209, 54, 104, 243, 239, 77, 137, 29]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n3 (hv776 := hi) (he781 := hp) (hm797 := hm) (he1024 := hh) .. =>
    have hr : ro = .natRec := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [163, 125, 40, 162, 42, 2, 205, 51,
       179, 200, 115, 128, 244, 92, 137, 144,
       201, 92, 206, 83, 241, 84, 173, 51,
       42, 156, 181, 249, 177, 99, 135, 83]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n4 (hv1030 := hi) (he1035 := hp) (hm1051 := hm) (he1278 := hh) .. =>
    have hr : ro = .bool := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [119, 219, 130, 215, 5, 42, 96, 110,
       170, 243, 36, 137, 49, 97, 214, 152,
       144, 73, 239, 78, 15, 57, 62, 47,
       233, 237, 175, 82, 244, 34, 94, 216]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n5 (hv1284 := hi) (he1289 := hp) (hm1305 := hm) (he1532 := hh) .. =>
    have hr : ro = .boolFalse := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [165, 252, 133, 109, 230, 53, 207, 196,
       10, 183, 3, 238, 165, 28, 183, 4,
       220, 230, 152, 95, 215, 222, 146, 31,
       148, 184, 214, 53, 233, 211, 102, 127]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n6 (hv1538 := hi) (he1543 := hp) (hm1559 := hm) (he1786 := hh) .. =>
    have hr : ro = .boolTrue := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [239, 21, 100, 99, 165, 39, 191, 210,
       54, 71, 46, 96, 107, 44, 205, 223,
       115, 244, 88, 81, 149, 227, 101, 224,
       67, 14, 227, 194, 9, 33, 216, 204]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n7 (hv1792 := hi) (he1797 := hp) (hm1813 := hm) (he2040 := hh) .. =>
    have hr : ro = .boolRec := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [105, 227, 8, 65, 57, 249, 243, 250,
       1, 156, 179, 44, 24, 138, 218, 4,
       211, 81, 151, 146, 93, 220, 117, 105,
       96, 210, 5, 213, 12, 84, 42, 232]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n8 (hv2046 := hi) (he2051 := hp) (hm2067 := hm) (he2294 := hh) .. =>
    have hr : ro = .eq := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [157, 60, 123, 207, 204, 143, 31, 22,
       97, 188, 232, 125, 55, 26, 93, 160,
       213, 24, 140, 27, 192, 93, 239, 33,
       212, 170, 23, 97, 56, 201, 27, 16]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n9 (hv2300 := hi) (he2305 := hp) (hm2321 := hm) (he2548 := hh) .. =>
    have hr : ro = .eqRefl := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [84, 176, 61, 237, 207, 208, 182, 145,
       14, 4, 235, 6, 228, 2, 238, 40,
       90, 218, 207, 207, 56, 139, 44, 249,
       36, 171, 227, 178, 8, 224, 123, 72]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n10 (hv2554 := hi) (he2559 := hp) (hm2575 := hm) (he2802 := hh) .. =>
    have hr : ro = .eqRec := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [11, 185, 20, 221, 56, 223, 206, 142,
       218, 164, 35, 44, 84, 144, 92, 161,
       94, 163, 132, 193, 4, 35, 226, 129,
       206, 110, 93, 243, 84, 210, 150, 92]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n11 (hv2808 := hi) (he2813 := hp) (hm2829 := hm) (he3056 := hh) .. =>
    have hr : ro = .punit := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [31, 36, 179, 69, 4, 94, 131, 3,
       61, 197, 115, 66, 205, 211, 189, 40,
       66, 209, 195, 162, 192, 75, 25, 60,
       64, 152, 115, 190, 203, 117, 180, 20]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n12 (hv3062 := hi) (he3067 := hp) (hm3083 := hm) (he3310 := hh) .. =>
    have hr : ro = .punitUnit := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [165, 137, 154, 97, 138, 94, 199, 185,
       223, 6, 178, 217, 209, 13, 236, 115,
       250, 96, 253, 212, 189, 170, 89, 32,
       77, 138, 76, 107, 19, 234, 34, 114]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n13 (hv3316 := hi) (he3321 := hp) (hm3337 := hm) (he3564 := hh) .. =>
    have hr : ro = .punitRec := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [87, 47, 254, 188, 254, 189, 72, 56,
       51, 201, 149, 128, 54, 93, 108, 173,
       90, 250, 184, 223, 112, 92, 21, 17,
       238, 40, 132, 68, 173, 198, 118, 185]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n14 (hv3570 := hi) (he3575 := hp) (hm3591 := hm) (he3818 := hh) .. =>
    have hr : ro = .empty := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [200, 113, 200, 114, 197, 245, 219, 243,
       3, 43, 90, 178, 28, 85, 22, 57,
       207, 18, 171, 217, 210, 225, 77, 69,
       114, 78, 185, 122, 89, 117, 251, 147]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n15 (hv3824 := hi) (he3829 := hp) (hm3845 := hm) (he4072 := hh) .. =>
    have hr : ro = .emptyRec := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [57, 63, 142, 173, 104, 3, 131, 19,
       190, 209, 138, 152, 17, 87, 178, 136,
       107, 194, 182, 227, 228, 243, 172, 224,
       55, 218, 36, 125, 73, 53, 42, 76]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n16 (hv4078 := hi) (he4083 := hp) (hm4099 := hm) (he4326 := hh) .. =>
    have hr : ro = .false := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [206, 119, 72, 125, 84, 147, 216, 231,
       36, 239, 3, 103, 125, 170, 235, 93,
       68, 4, 9, 15, 124, 18, 184, 239,
       203, 85, 124, 147, 163, 107, 207, 82]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n17 (hv4332 := hi) (he4337 := hp) (hm4353 := hm) (he4580 := hh) .. =>
    have hr : ro = .falseRec := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [12, 157, 146, 76, 234, 173, 212, 107,
       126, 17, 75, 35, 40, 118, 116, 246,
       227, 27, 176, 15, 223, 134, 180, 250,
       183, 250, 183, 104, 40, 4, 200, 178]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n20 (hv4586 := hi) (he4591 := hp) (hm4607 := hm) (he4834 := hh) .. =>
    have hr : ro = .and := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [79, 73, 42, 148, 176, 248, 146, 206,
       220, 196, 157, 44, 13, 99, 43, 181,
       15, 235, 246, 253, 120, 231, 192, 166,
       136, 97, 1, 152, 204, 20, 142, 49]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n21 (hv4840 := hi) (he4845 := hp) (hm4861 := hm) (he5088 := hh) .. =>
    have hr : ro = .andIntro := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [151, 147, 60, 16, 155, 196, 138, 178,
       82, 58, 77, 177, 251, 237, 119, 99,
       199, 144, 50, 83, 95, 255, 228, 135,
       178, 205, 121, 139, 40, 161, 234, 95]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n22 (hv5094 := hi) (he5099 := hp) (hm5115 := hm) (he5342 := hh) .. =>
    have hr : ro = .andRec := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [244, 229, 147, 204, 38, 9, 152, 78,
       207, 107, 4, 110, 217, 122, 66, 240,
       236, 218, 251, 48, 24, 221, 169, 240,
       209, 155, 178, 125, 218, 110, 223, 3]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n32 (hv5348 := hi) (he5353 := hp) (hm5369 := hm) (he5596 := hh) .. =>
    have hr : ro = .quot := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [200, 123, 41, 147, 28, 228, 224, 2,
       66, 95, 133, 102, 209, 203, 240, 18,
       203, 149, 56, 63, 126, 124, 195, 83,
       63, 87, 99, 214, 59, 63, 32, 96]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n33 (hv5602 := hi) (he5607 := hp) (hm5623 := hm) (he5850 := hh) .. =>
    have hr : ro = .quotMk := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [179, 142, 110, 198, 61, 58, 198, 202,
       164, 86, 175, 105, 143, 250, 248, 102,
       225, 146, 189, 62, 132, 216, 9, 42,
       132, 21, 183, 147, 167, 171, 181, 152]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n34 (hv5856 := hi) (he5861 := hp) (hm5877 := hm) (he6104 := hh) .. =>
    have hr : ro = .quotLift := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [171, 187, 156, 7, 178, 196, 102, 237,
       99, 0, 135, 132, 40, 68, 234, 4,
       100, 185, 92, 160, 33, 139, 42, 30,
       230, 121, 7, 84, 45, 68, 48, 132]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n35 (hv6110 := hi) (he6115 := hp) (hm6131 := hm) (he6358 := hh) .. =>
    have hr : ro = .quotInd := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [44, 5, 242, 131, 164, 80, 160, 87,
       187, 103, 160, 180, 66, 37, 244, 120,
       194, 208, 15, 187, 253, 151, 40, 180,
       248, 206, 246, 192, 243, 85, 60, 253]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .n36 (hv6364 := hi) (he6369 := hp) (hm6385 := hm) (he6612 := hh) .. =>
    have hr : ro = .quotSound := RolesAux.roleNum_inj (Value.field.inj hi)
    subst ro
    have hp' : ptr = .ptr addrTy h.length := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true, true_and, Core.addrTy, List.replicate_succ, List.replicate_zero] using hp
    subst ptr
    let bs : List UInt8 :=
      [132, 246, 186, 212, 18, 241, 180, 234,
       67, 150, 160, 196, 209, 94, 239, 194,
       141, 48, 120, 82, 27, 240, 6, 33,
       207, 187, 250, 91, 47, 228, 57, 207]
    refine ⟨mkAddr bs, by decide, ?_⟩
    rw [hh, hm]
    exact addr_snoc h bs (by decide)
  | .other (he6622 := hp) .. =>
    have hbad : (1 : F) = 0 := Value.field.inj (List.cons.inj (Value.tuple.inj hp)).1
    exact (one_ne_zero hbad).elim


/-- Select the tail of a tuple whose leading literal is the pinned flag. -/
private def pinFlagArm (k : Nat) :
    List (Generic.Pattern F × Generic.Expr F) → Option (List (Generic.Expr F))
  | (.literal c, .tuple (.literal tag :: tail)) :: rest =>
      if k == ZMod.val c then if tag == 1 then some tail else none else pinFlagArm k rest
  | (.wildcard, .tuple (.literal tag :: tail)) :: _ =>
      if tag == 1 then some tail else none
  | _ => none

private def pinArms : List (Generic.Pattern F × Generic.Expr F) :=
  match IxVM.KernelRoles.basis_pin.body with
  | .matchValue _ arms => arms
  | _ => []

private theorem pinFlagArm_select {arms : List (Generic.Pattern F × Generic.Expr F)}
    {x : F} {tail : List (Generic.Expr F)}
    (ht : pinFlagArm (ZMod.val x) arms = some tail)
    {h : Heap F} {bs : Environment F Nat} {body : Generic.Expr F}
    (hs : selectArm Obs.W [] h (.field x) arms = .ok (some (bs, body))) :
    bs = [] ∧ body = .tuple (.literal 1 :: tail) := by
  induction arms with
  | nil => simp [pinFlagArm] at ht
  | cons arm rest ih =>
    rcases arm with ⟨pat, expr⟩
    cases pat <;> try (solve | simp [pinFlagArm] at ht)
    case literal c =>
      cases expr <;> try (solve | simp [pinFlagArm] at ht)
      case tuple es =>
        cases es with
        | nil => simp [pinFlagArm] at ht
        | cons e es =>
          cases e <;> try (solve | simp [pinFlagArm] at ht)
          case literal tag =>
            simp only [pinFlagArm] at ht
            by_cases he : (ZMod.val x == ZMod.val c) = true
            · rw [ite_eq_left he] at ht
              by_cases htag : (tag == 1) = true
              · rw [ite_eq_left htag] at ht
                injection ht with htail
                subst tail
                have hx : x = c := ZMod.val_injective _ (beq_iff_eq.mp he)
                have ht1 : tag = 1 := beq_iff_eq.mp htag
                subst c tag
                rcases selectArm_cons_inv hs with ⟨hm, rfl⟩ | ⟨hn, _⟩
                · exact ⟨(MatchesConst.some_inv (MatchesConst.literal x) hm).2, rfl⟩
                · exact (MatchesConst.none_inv (MatchesConst.literal x) hn rfl).elim
              · rw [ite_eq_right htag] at ht
                cases ht
            · rw [ite_eq_right he] at ht
              have hne : x ≠ c := fun hxc => he (beq_iff_eq.mpr (congrArg ZMod.val hxc))
              rcases selectArm_cons_inv hs with ⟨hm, _⟩ | ⟨_, hs'⟩
              · exact (hne (Value.field.inj
                  (MatchesConst.some_inv (MatchesConst.literal c) hm).1)).elim
              · exact ih ht hs'
    case wildcard =>
      cases expr <;> try (solve | simp [pinFlagArm] at ht)
      case tuple es =>
        cases es with
        | nil => simp [pinFlagArm] at ht
        | cons e es =>
          cases e <;> try (solve | simp [pinFlagArm] at ht)
          case literal tag =>
            simp only [pinFlagArm] at ht
            by_cases htag : (tag == 1) = true
            · rw [ite_eq_left htag] at ht
              injection ht with htail
              subst tail
              have ht1 : tag = 1 := beq_iff_eq.mp htag
              subst tag
              rcases selectArm_cons_inv hs with ⟨hm, rfl⟩ | ⟨hn, _⟩
              · exact ⟨matchPattern_wildcard_inv hm, rfl⟩
              · exact (matchPattern_wildcard_none hn).elim
            · rw [ite_eq_right htag] at ht
              cases ht

private theorem pinFlagArm_prelude (ro : Ix.Kernel.Role)
    (hr : ro ∈ Ix.Kernel.preludeShape.flatMap id) :
    (pinFlagArm ro.idx pinArms).isSome = true := by
  cases ro <;> simp [Ix.Kernel.preludeShape] at hr
  all_goals decide +kernel

/-- Every prelude role actually takes a pinned branch, including in an assumed role context. -/
theorem basis_pin_prelude_flag {ro : Ix.Kernel.Role}
    (hr : ro ∈ Ix.Kernel.preludeShape.flatMap id)
    {flag ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelRoles::basis_pin" [.field (roleNum ro)] h
      (.tuple [flag, ptr]) h' calls) : flag = .field 1 := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoles.basis_pin.lookup
    (by simp [IxVM.KernelRoles.basis_pin, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoles.basis_pin.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoles.basis_pin.body = .matchValue (.var "r") pinArms := rfl
  rw [hp, hb] at d0
  obtain ⟨_, _, _, _, _, _, dv, hs, db, _⟩ := d0.matchValue_inv
  obtain ⟨lookup, rfl, rfl⟩ := dv.var_inv
  simp at lookup
  subst lookup
  have hsome := pinFlagArm_prelude ro hr
  cases he : pinFlagArm ro.idx pinArms with
  | none => rw [he] at hsome; cases hsome
  | some tail =>
    have he' : pinFlagArm (ZMod.val (roleNum ro)) pinArms = some tail := by
      simpa only [RolesAux.val_roleNum] using he
    obtain ⟨rfl, rfl⟩ := pinFlagArm_select he' hs
    obtain ⟨vs, args, hout⟩ := db.tuple_inv
    obtain ⟨v, rest, _, _, _, hvs, literal, _, _⟩ := args.cons_inv
    obtain ⟨rfl, rfl, rfl⟩ := literal.literal_inv
    simp_all only [Value.tuple.injEq, List.cons.injEq]

/-- A prelude lookup returns exactly the committed address, with no external flag premise. -/
theorem basis_pin_prelude {ro : Ix.Kernel.Role}
    (hr : ro ∈ Ix.Kernel.preludeShape.flatMap id)
    {flag ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelRoles::basis_pin" [.field (roleNum ro)] h
      (.tuple [flag, ptr]) h' calls) :
    flag = .field 1 ∧
      ∃ a, committedDefaultRoleTable.addressOf? ro = some a ∧ BaseSeams.addr h' ptr a := by
  have hf := basis_pin_prelude_flag hr ev
  subst flag
  exact ⟨rfl, basis_pin_bound ev⟩

end IxVM.Refinement.RoleVal
