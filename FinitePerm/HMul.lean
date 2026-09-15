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

@[simp, grind =] theorem getElem_hmul {i : Nat} (hi : i < max m n) :
    (a.hmul b)[i] = if hn : i < n then if hm : b[i] < m then a[b[i]] else b[i]
    else a[i]'(by omega) := by
  simp only [hmul, getElem_mul, getElem_castGE]
  grind

theorem getElem_inv_hmul {i : Nat} (hi : i < max m n) :
    (a.hmul b)⁻¹[i] = if hn : i < m then if hm : a⁻¹[i] < n then b⁻¹[a⁻¹[i]] else a⁻¹[i]
      else b⁻¹[i]'(by omega) := by
  simp only [hmul, inv_mul_rev, getElem_mul, getElem_inv_castGE]
  grind

@[simp, grind =] theorem inv_hmul : (a.hmul b)⁻¹ = (b⁻¹.hmul a⁻¹).cast (Nat.max_comm n m) := by
  grind [getElem_inv_hmul]

@[simp, grind =]
theorem hmul_eq_mul {a b : PermVector n} : a.hmul b = (a * b).cast (Nat.max_self n).symm := by
  ext
  simp only [getElem_hmul, getElem_lt, getElem_cast]
  grind

@[grind =]
theorem hmul_castGE_left {k : Nat} (h : m ≤ k) :
    (a.castGE h).hmul b = (a.hmul b).castGE (by omega) := by
  ext
  simp only [getElem_hmul, getElem_castGE]
  grind

@[grind =]
theorem hmul_castGE_right {k : Nat} (h : n ≤ k) :
    a.hmul (b.castGE h) = (a.hmul b).castGE (by omega) := by
  ext
  simp only [getElem_hmul, getElem_castGE]
  grind

end HMul

end PermVector
