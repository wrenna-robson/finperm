/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import Finperm.Basic
public import Finperm.HMul
public import Batteries.Data.Fin.Basic

@[expose] public section

namespace Finperm

@[irreducible] def minLen {n : Nat} (a : Finperm n) : Nat :=
  ((Fin.findRev? (fun i : Fin n => (a[i.1] != i.1))).map (·.val.succ)).getD 0

section MinLen

variable {n j : Nat} (a b : Finperm n)

@[simp] theorem minLen_eq_zero_iff : a.minLen = 0 ↔ a = 1 := by
  simp [minLen, Option.getD_eq_iff, Fin.forall_iff, Finperm.ext_iff]

@[simp] theorem minLen_eq_succ_iff : a.minLen = j + 1 ↔
    (∃ (hj : j < n), a[j] ≠ j) ∧ (∀ (i : Nat) (h : i < n), j < i → a[i] = i) := by
  simp [minLen, Option.getD_eq_iff, Fin.exists_iff, Fin.forall_iff, and_assoc]

theorem minLen_ne_one : a.minLen ≠ 1 := by
  simp only [ne_eq, minLen_eq_succ_iff, not_and, Classical.not_forall, forall_exists_index]
  grind

@[simp, grind =] theorem minLen_one : (1 : Finperm n).minLen = 0 := by simp

@[simp, grind =] theorem minLen_zero_perm {a} : (a : Finperm 0).minLen = 0 := by simp [unique_zero]
@[simp, grind =] theorem minLen_one_perm {a} : (a : Finperm 1).minLen = 0 := by simp [unique_one]

theorem minLen_ne_zero_iff : a.minLen ≠ 0 ↔ a ≠ 1 := by simp

@[simp] theorem minLen_pos_iff : 0 < a.minLen ↔ a ≠ 1 := by simp [Nat.pos_iff_ne_zero]

@[grind .] theorem minLen_eq_iff_getElem_ne : a.minLen = n ↔ ∀ (hn : n ≠ 0), a[n - 1] ≠ n - 1 := by
  cases n with | zero => simp | succ j => simp only [minLen_eq_succ_iff]; grind

theorem minLen_le_iff {m : Nat} : a.minLen ≤ m ↔ ∀ i, m ≤ i → (hi : i < n) → a[i] = i := by
  cases h : a.minLen with | zero => _ | succ j => _
  · rw [minLen_eq_zero_iff] at h
    grind
  · rw [minLen_eq_succ_iff] at h
    grind

@[simp, grind .] theorem minLen_le : a.minLen ≤ n := by simp only [minLen_le_iff]; grind

theorem lt_minLen_iff {m : Nat} : m < a.minLen ↔
    ∃ i, m ≤ i ∧ ∃ (hi : i < n), a[i] ≠ i := by simp [← Nat.not_le, minLen_le_iff]

@[grind =]
theorem minLen_le_iff_getElem_eq {j : Nat} (hj : j < n) (hle : a.minLen ≤ j + 1) :
    a.minLen ≤ j ↔ a[j] = j := by grind [minLen_le_iff]

@[grind <=]
theorem getElem_eq_self_of_minLen_le (i : Nat) (hi : i < n) (hle : a.minLen ≤ i) :
    a[i] = i := by grind

@[grind =>]
theorem exists_getElem_ne_of_lt_minLen {m : Nat} (h : m < a.minLen) :
    ∃ i, m ≤ i ∧ ∃ (hi : i < n), a[i] ≠ i := a.lt_minLen_iff.mp h

theorem lt_minLen_of_getElem_ne {i : Nat} (h : i < n) (hi : a[i] ≠ i) : i < a.minLen := by grind

theorem minLen_mul_le : (a * b).minLen ≤ max a.minLen b.minLen := by grind [Nat.max_le]

@[simp] theorem minLen_inv : a⁻¹.minLen = a.minLen :=
  Nat.le_antisymm (by grind [minLen_le_iff]) (by grind [minLen_le_iff])

theorem minLen_transpose {i j : Nat} (hi : i < n) (hj : j < n) :
    (transpose i j hi hj).minLen = if i = j then 0 else max i j + 1 := by
  split
  · simpa only [minLen_eq_zero_iff, transpose_eq_one_iff]
  · simp only [minLen_eq_succ_iff, getElem_transpose]
    grind

end MinLen

def minPerm {n : Nat} (a : Finperm n) : Finperm a.minLen := let m := a.minLen; {
  toVector := (a.toVector.take m).cast (by grind)
  invVector := (a.invVector.take m).cast (by grind)
  getElem_invVector_getElem_toVector := by
    simp only [Vector.getElem_cast, Vector.getElem_take, getElem_invVector,
      getElem_toVector, getElem_inv_getElem, exists_prop, and_true]
    grind }

section MinPerm

variable {n : Nat} (a : Finperm n)

@[simp, grind =]
theorem getElem_minPerm {i : Nat} (hi : i < a.minLen) :
    (a.minPerm)[i] = a[i]'(by grind) := by
  simp only [minPerm, Vector.getElem_cast, Vector.getElem_take, getElem_toVector, getElem_mk]

@[simp, grind =]
theorem getElem_inv_minPerm {i : Nat} (hi : i < a.minLen) :
    (a.minPerm)⁻¹[i] = a⁻¹[i]'(by grind) := by
  simp only [minPerm, Vector.getElem_cast, Vector.getElem_take, getElem_invVector, inv_mk,
    getElem_mk]

@[simp] theorem minPerm_eq_one_iff : a.minPerm = 1 ↔ a = 1 := by
  simp only [Finperm.ext_iff, getElem_minPerm] <;> grind

theorem minLen_minPerm : a.minPerm.minLen = a.minLen := by grind

@[simp] theorem inv_minPerm : (a.minPerm)⁻¹ = a⁻¹.minPerm.cast a.minLen_inv := by grind

@[simp, grind =] theorem castGE_minPerm : a.minPerm.castGE a.minLen_le = a := by
  grind

theorem hmul_minPerm {m : Nat} (b : Finperm m) :
    (a.minPerm.hmul b.minPerm).castGE (by grind) = a.hmul b := by
  conv => rhs; rw [← a.castGE_minPerm, ← b.castGE_minPerm]
  rw [hmul_castGE_left, hmul_castGE_right, castGE_castGE]

end MinPerm

end Finperm
