/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import FinitePerm.Basic

@[expose] public section

namespace PermVector

/-- `a.cast h` is `a`, reinterpreted (via `h : n = m`) as a permutation of the same size but
with a different (defeq-via-`h`) index. -/
def cast {n m : Nat} (a : PermVector n) (h : n = m) : PermVector m where
  toVector := a.toVector.cast h
  invVector := a.invVector.cast h
  getElem_invVector_getElem_toVector := fun i hi => by subst h; grind [Vector.getElem_cast]

section Cast

variable {n m : Nat} (a : PermVector n) (h : n = m)

@[simp] theorem getElem_cast {i : Nat} (hi : i < m) :
    (a.cast h)[i] = a[i]'(by omega) := by subst h; rfl

grind_pattern getElem_cast => (a.cast h)[i]

@[simp] theorem getElem_inv_cast {i : Nat} (hi : i < m) :
    (a.cast h)⁻¹[i] = a⁻¹[i]'(by omega) := by subst h; rfl

grind_pattern getElem_inv_cast => (a.cast h)⁻¹[i]

@[simp] theorem cast_rfl : a.cast rfl = a := rfl

@[simp] theorem cast_cast {k : Nat} (h' : m = k) : (a.cast h).cast h' = a.cast (h.trans h') := by
  subst h; subst h'; rfl

@[simp, grind =] theorem cast_inv : a⁻¹.cast h = (a.cast h)⁻¹ := by grind

@[simp, grind =] theorem mul_cast {b : PermVector n} : a.cast h * b.cast h = (a * b).cast h := by
  ext
  simp only [getElem_mul, getElem_cast]

@[simp, grind =] theorem one_cast : (1 : PermVector n).cast h = 1 := by
  ext
  simp only [getElem_one, getElem_cast]

@[simp, grind =] theorem cast_eq_one : a.cast h = 1 ↔ a = 1 := by
  simp only [PermVector.ext_iff, getElem_one, getElem_cast]
  grind

end Cast

/-- `a.castGE h` is `a`, reinterpreted as a permutation of the larger domain `PermVector k`
(`h : m ≤ k`) by fixing every point outside `a`'s original domain. -/
def castGE {m : Nat} (a : PermVector m) {k : Nat} (h : m ≤ k) : PermVector k where
  toVector := (a.toVector ++ Vector.range' m (k - m)).cast (by omega)
  invVector := (a.invVector ++ Vector.range' m (k - m)).cast (by omega)
  getElem_invVector_getElem_toVector := fun i hi => by
    grind [Vector.getElem_cast]

section CastGE

variable {m k : Nat} (a : PermVector m) {h : m ≤ k}

@[simp] theorem getElem_castGE {i : Nat} (hi : i < k) :
    (a.castGE h)[i] = if hi' : i < m then a[i] else i := by
  simp only [castGE, getElem_mk]
  grind [Vector.getElem_cast]

grind_pattern getElem_castGE => (a.castGE h)[i]

@[simp, grind =] theorem getElem_inv_castGE {i : Nat} (hi : i < k) :
    (a.castGE h)⁻¹[i] = if hi' : i < m then a⁻¹[i] else i := by
  simp only [castGE, inv_mk, getElem_mk]
  grind [Vector.getElem_cast]

grind_pattern getElem_inv_castGE => (a.castGE h)⁻¹[i]

@[simp, grind =] theorem castGE_inv : a⁻¹.castGE h = (a.castGE h)⁻¹ := by grind

@[simp] theorem castGE_eq_cast (h : m = n) :
    a.castGE (Nat.le_of_eq h) = a.cast h := by grind

theorem castGE_refl : a.castGE (Nat.le_refl _) = a := by simp

@[simp, grind =] theorem castGE_castGE {l : Nat} (h' : k ≤ l) :
    (a.castGE h).castGE h' = a.castGE (Nat.le_trans h h') := by grind

theorem castGE_inj {x y : PermVector m} : x.castGE h = y.castGE h ↔ x = y := by
  simp only [PermVector.ext_iff, getElem_castGE]
  grind

@[simp, grind =]
theorem mul_castGE {a b : PermVector n} (h : n ≤ m) :
    a.castGE h * b.castGE h = (a * b).castGE h := by
  ext
  simp only [getElem_mul, getElem_castGE]
  grind

@[simp, grind =] theorem one_castGE : (1 : PermVector m).castGE h = 1 := by
  ext
  simp only [getElem_one, getElem_castGE]
  grind

@[simp, grind =] theorem castGE_eq_one : a.castGE h = 1 ↔ a = 1 := by
  simp only [PermVector.ext_iff, getElem_one, getElem_castGE]
  grind

end CastGE

end PermVector
