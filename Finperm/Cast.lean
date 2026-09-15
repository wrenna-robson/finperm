/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import Finperm.Basic

@[expose] public section

namespace Finperm

/-- `a.cast h` is `a`, reinterpreted (via `h : n = m`) as a permutation of the same size but
with a different (defeq-via-`h`) index. -/
def cast {n m : Nat} (a : Finperm n) (h : n = m) : Finperm m where
  toVector := a.toVector.cast h
  invVector := a.invVector.cast h
  getElem_invVector_getElem_toVector := fun i hi => by subst h; grind [Vector.getElem_cast]

section Cast

variable {n m : Nat} (a : Finperm n) (h : n = m)

@[simp] theorem getElem_cast {i : Nat} (hi : i < m) :
    (a.cast h)[i] = a[i]'(by omega) := by subst h; rfl

grind_pattern getElem_cast => (a.cast h)[i]

theorem getElem_inv_cast {i : Nat} (hi : i < m) :
    (a.cast h)⁻¹[i] = a⁻¹[i]'(by omega) := by subst h; rfl

@[simp] theorem cast_rfl : a.cast rfl = a := rfl

@[simp] theorem cast_cast {k : Nat} (h' : m = k) : (a.cast h).cast h' = a.cast (h.trans h') := by
  subst h; subst h'; rfl

@[simp, grind =] theorem inv_cast : (a.cast h)⁻¹ = a⁻¹.cast h := by
  grind [getElem_cast, getElem_inv_cast]

end Cast

/-- `a.castGE h` is `a`, reinterpreted as a permutation of the larger domain `Finperm k`
(`h : m ≤ k`) by fixing every point outside `a`'s original domain. -/
def castGE {m : Nat} (a : Finperm m) {k : Nat} (h : m ≤ k) : Finperm k where
  toVector := (a.toVector ++ (Vector.range (k - m)).map (· + m)).cast (by omega)
  invVector := (a.invVector ++ (Vector.range (k - m)).map (· + m)).cast (by omega)
  getElem_invVector_getElem_toVector := fun i hi => by
    grind [Vector.getElem_cast]

section CastGE

variable {m k : Nat} (a : Finperm m) (h : m ≤ k)

@[simp, grind =] theorem getElem_castGE {i : Nat} (hi : i < k) :
    (a.castGE h)[i] = if hi' : i < m then a[i] else i := by
  simp only [castGE, getElem_mk]
  grind [Vector.getElem_cast]

theorem getElem_inv_castGE {i : Nat} (hi : i < k) :
    (a.castGE h)⁻¹[i] = if hi' : i < m then a⁻¹[i] else i := by
  simp only [castGE, inv_mk, getElem_mk]
  grind [Vector.getElem_cast]

@[simp, grind =] theorem inv_castGE : (a.castGE h)⁻¹ = a⁻¹.castGE h := by grind [getElem_inv_castGE]

@[simp, grind =] theorem castGE_castGE {l : Nat} (h' : k ≤ l) :
    (a.castGE h).castGE h' = a.castGE (Nat.le_trans h h') := by grind

@[simp, grind =] theorem mul_castGE (b : Finperm m) :
    a.castGE h * b.castGE h = (a * b).castGE h := by
  ext
  simp only [getElem_mul, getElem_castGE]
  grind

end CastGE

end Finperm
