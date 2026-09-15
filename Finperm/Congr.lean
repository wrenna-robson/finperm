/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import Finperm.HMul
public import Finperm.MinPerm

@[expose] public section

namespace Finperm

@[irreducible] def IsCongr {n m : Nat} (a : Finperm n) (b : Finperm m) : Prop :=
  (∀ i (hin : i < n) (him : i < m), a[i] = b[i]) ∧
    (∀ i, ∀ (hi : i < n), m ≤ i → a[i] = i) ∧
    (∀ i, ∀ (hi : i < m), n ≤ i → b[i] = i)

section IsCongr

variable {n m l i : Nat} {a : Finperm n} {b : Finperm m} {c : Finperm l}

unseal IsCongr in theorem isCongr_def :
    a.IsCongr b ↔ (∀ i (hin : i < n) (him : i < m), a[i] = b[i]) ∧
    (∀ i, ∀ (hi : i < n), m ≤ i → a[i] = i) ∧
    (∀ i, ∀ (hi : i < m), n ≤ i → b[i] = i) := Iff.rfl

instance {a : Finperm n} {b : Finperm m} : Decidable (a.IsCongr b) :=
  decidable_of_decidable_of_iff isCongr_def.symm

@[simp, grind =] theorem isCongr_iff_eq {a' : Finperm n} : a.IsCongr a' ↔ a = a' := by
  grind [isCongr_def]

@[grind →] theorem IsCongr.symm : a.IsCongr b → b.IsCongr a := by grind [isCongr_def]

@[grind →] theorem IsCongr.trans : a.IsCongr b → b.IsCongr c → a.IsCongr c := by
  grind [isCongr_def]

@[simp, grind =] theorem isCongr_one_iff : a.IsCongr (1 : Finperm m) ↔ a = 1 := by
  grind [isCongr_def]

@[grind →] theorem IsCongr.inv_inv : a.IsCongr b → a⁻¹.IsCongr b⁻¹ := by grind [isCongr_def]

theorem IsCongr.mul_mul {a' : Finperm n} {b' : Finperm m} (hab : a.IsCongr b)
    (hab' : a'.IsCongr b') : (a * a').IsCongr (b * b') := by grind [isCongr_def]

grind_pattern IsCongr.mul_mul => a * a', b * b'

theorem IsCongr.eq {a' : Finperm n} (h : a.IsCongr a') : a = a' := by grind

@[simp] theorem isCongr_refl (a : Finperm n) : a.IsCongr a := by grind

theorem isCongr_rfl : a.IsCongr a := isCongr_refl a

theorem isCongr_comm : a.IsCongr b ↔ b.IsCongr a := by grind

theorem IsCongr.congr (hab : a.IsCongr a') (hab' : b.IsCongr b') :
    a.IsCongr b ↔ a'.IsCongr b' := by grind

theorem IsCongr.congrLeft (hab : a.IsCongr b) : a.IsCongr c ↔ b.IsCongr c := by grind

theorem IsCongr.congrRight (hab : a.IsCongr b) : c.IsCongr a ↔ c.IsCongr b := by grind

@[simp] theorem one_isCongr_iff : (1 : Finperm m).IsCongr a ↔ a = 1 := by grind

theorem isCongr_one_one : (1 : Finperm n).IsCongr (1 : Finperm m) := by grind

theorem IsCongr.inv_right (hab : a.IsCongr b⁻¹) : a⁻¹.IsCongr b := by grind

theorem IsCongr.inv_left (hab : a⁻¹.IsCongr b) : a.IsCongr b⁻¹ := by grind

theorem inv_isCongr_iff_isCongr_inv : a⁻¹.IsCongr b ↔ a.IsCongr b⁻¹ := by grind

@[simp] theorem inv_isCongr_inv_iff : a⁻¹.IsCongr b⁻¹ ↔ a.IsCongr b := by grind


@[simp] theorem isCongr_cast {h : n = m} : a.IsCongr (a.cast h) := by subst h; simp

grind_pattern isCongr_cast => a.cast h

@[simp] theorem cast_isCongr {h : n = m} : (a.cast h).IsCongr a := a.isCongr_cast.symm

grind_pattern cast_isCongr => a.cast h

@[simp] theorem isCongr_castGE {h : n ≤ k} : a.IsCongr (a.castGE h) := by grind [isCongr_def]

grind_pattern isCongr_castGE => a.castGE h

@[simp] theorem castGE_isCongr {h : n ≤ k} : (a.castGE h).IsCongr a := a.isCongr_castGE.symm

grind_pattern castGE_isCongr => a.castGE h

theorem IsCongr.hmul_hmul {a' : Finperm n'} {b' : Finperm m'} (hab : a.IsCongr b)
    (hab' : a'.IsCongr b') : (a.hmul a').IsCongr (b.hmul b') :=
  IsCongr.mul_mul (by grind) (by grind)

grind_pattern IsCongr.hmul_hmul => a.hmul a', b.hmul b'

instance : Setoid (Σ n, Finperm n) where
  r a b := a.2.IsCongr b.2
  iseqv := by grind [Equivalence]

section MinPerm

variable {n m : Nat} (a : Finperm n) (b : Finperm m)

@[grind →] theorem IsCongr.minLen_eq (hab : a.IsCongr b) :
    a.minLen = b.minLen := Nat.le_antisymm (by grind [isCongr_def]) (by grind [isCongr_def])

@[simp] theorem isCongr_minPerm : a.IsCongr a.minPerm := by
  simp only [isCongr_def, getElem_minPerm, implies_true, true_and]
  exact ⟨a.getElem_eq_self_of_minLen_le, have := a.minLen_le; by omega⟩

grind_pattern isCongr_minPerm => a.minPerm

@[simp] theorem minPerm_isCongr : a.minPerm.IsCongr a := by grind

grind_pattern minPerm_isCongr => a.minPerm

@[simp] theorem isCongr_minPerm_left : a.minPerm.IsCongr b ↔ a.IsCongr b := by grind
@[simp] theorem isCongr_minPerm_right : a.IsCongr b.minPerm ↔ a.IsCongr b := by grind
theorem isCongr_minPerm_minPerm : a.minPerm.IsCongr b.minPerm ↔ a.IsCongr b := by simp

theorem inv_minPerm_isCongr_inv : (a.minPerm)⁻¹.IsCongr a⁻¹ := (a.minPerm_isCongr).inv_inv

end MinPerm

end IsCongr

end Finperm
