/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import FinitePerm.Cast

@[expose] public section

namespace PermVector

def hmul {m n : Nat} (a : PermVector m) (b : PermVector n) : PermVector (max m n) :=
  a.castGE (Nat.le_max_left m n) * b.castGE (Nat.le_max_right m n)

section HMul

variable {m n : Nat} (a : PermVector m) (b : PermVector n)

theorem getElem_hmul {i : Nat} (hi : i < max m n) :
    (a.hmul b)[i] =
    if hn : i < n then if hm : b[i] < m then a[b[i]] else b[i]
    else a[i]'(by omega) := by
  simp only [hmul, getElem_mul, getElem_castGE]
  grind

theorem getElem_inv_hmul {i : Nat} (hi : i < max m n) :
    (a.hmul b)⁻¹[i] = if hn : i < m then if hm : a⁻¹[i] < n then b⁻¹[a⁻¹[i]] else a⁻¹[i]
      else b⁻¹[i]'(by omega) := by
  simp only [hmul, PermVector.mul_inv_rev, getElem_mul, getElem_inv_castGE]
  grind

@[simp, grind =] theorem one_hmul : (1 : PermVector n).hmul a = a.castGE (by omega) := by
  simp only [hmul, one_castGE, Std.LawfulLeftIdentity.left_id]

@[simp, grind =] theorem hmul_one : a.hmul (1 : PermVector n) = a.castGE (by omega) := by
  simp only [hmul, one_castGE, Std.LawfulRightIdentity.right_id]


@[simp, grind =] theorem inv_hmul_cancel : a⁻¹.hmul a = 1 := by
  simp only [hmul, Std.le_refl, Nat.max_eq_right, castGE_eq_cast, cast_inv,
    PermVector.inv_mul_cancel]

@[simp, grind =] theorem hmul_inv_cancel : a.hmul a⁻¹ = 1 := by
  simp only [hmul, Std.le_refl, Nat.max_eq_right, castGE_eq_cast, cast_inv,
    PermVector.mul_inv_cancel]

@[simp, grind =] theorem inv_hmul : (a.hmul b)⁻¹ = (b⁻¹.hmul a⁻¹).cast (Nat.max_comm n m) := by
  simp only [hmul, PermVector.mul_inv_rev, castGE_inv, cast_mul, cast_inv, cast_castGE]

@[simp, grind =]
theorem hmul_eq_mul_cast {a b : PermVector n} : a.hmul b = (a * b).cast (Nat.max_self n).symm := by
  simp only [hmul, Nat.max_self, castGE_eq_cast, cast_mul]

theorem hmul_castGE_left {k : Nat} (h : m ≤ k) :
    (a.castGE h).hmul b = (a.hmul b).castGE (by omega) := by
  simp only [hmul, castGE_mul, castGE_castGE]

theorem hmul_castGE_right {k : Nat} (h : n ≤ k) :
    a.hmul (b.castGE h) = (a.hmul b).castGE (by omega) := by
  simp only [hmul, castGE_mul, castGE_castGE]

@[grind =]
theorem hmul_assoc {c : PermVector l} : (a.hmul b).hmul c =
    (a.hmul (b.hmul c)).cast (Nat.max_assoc m n l).symm := by
  simp only [hmul, castGE_mul, castGE_castGE, Std.Associative.assoc, cast_mul, cast_castGE]

end HMul

end PermVector
