/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import FinitePerm.HMul
public import FinitePerm.MinPerm

@[expose] public section

namespace PermVector

def IsCongr {n m : Nat} (a : PermVector n) (b : PermVector m) : Prop :=
  (∃ (h : n ≤ m), a.castGE h = b) ∨ (∃ (h : m ≤ n), b.castGE h = a)

section IsCongr

variable {n m l i : Nat} {a : PermVector n} {b : PermVector m} {c : PermVector l}

@[simp] theorem isCongr_refl (a : PermVector n) : a.IsCongr a := .inl ⟨n.le_refl, a.castGE_refl⟩

theorem isCongr_rfl : a.IsCongr a := isCongr_refl a

@[grind →] theorem IsCongr.symm (hab : a.IsCongr b) : b.IsCongr a := hab.elim Or.inr Or.inl

theorem isCongr_comm : a.IsCongr b ↔ b.IsCongr a := by grind

theorem isCongr_pointwise :
    a.IsCongr b ↔ (∀ i (hin : i < n) (him : i < m), a[i] = b[i]) ∧
    (∀ i, ∀ (hi : i < n), m ≤ i → a[i] = i) ∧
    (∀ i, ∀ (hi : i < m), n ≤ i → b[i] = i) := by
  unfold IsCongr
  simp only [PermVector.ext_iff, getElem_castGE]
  grind

theorem IsCongr.eq_castGE_of_le (h : n ≤ m) (hab : a.IsCongr b) : a.castGE h = b :=
  hab.elim (fun ⟨_, h⟩ => h) (fun ⟨hnm, h⟩ => h ▸ by simp)

theorem IsCongr.eq_castGE_of_ge (h : m ≤ n) (hab : a.IsCongr b) : b.castGE h = a :=
  hab.elim (fun ⟨hnm, h⟩ => h ▸ by simp) (fun ⟨_, h⟩ => h)

theorem isCongr_of_castGE_eq_right (h : n ≤ m) (hab : a.castGE h = b) : a.IsCongr b :=
  Or.inl ⟨_, hab⟩

theorem isCongr_of_castGE_eq_left (h : m ≤ n) (hab : b.castGE h = a) : a.IsCongr b :=
  Or.inr ⟨_, hab⟩

@[simp] theorem isCongr_castGE {h : n ≤ k} : a.IsCongr (a.castGE h) := Or.inl ⟨h, rfl⟩

grind_pattern isCongr_castGE => a.castGE h

@[simp] theorem castGE_isCongr {h : n ≤ k} : (a.castGE h).IsCongr a := Or.inr ⟨h, rfl⟩

grind_pattern castGE_isCongr => a.castGE h

@[simp, grind =] theorem castGE_eq_iff {h : n ≤ k} {h'} :
    a.castGE h = b.castGE h' ↔ a.IsCongr b := by
  unfold IsCongr
  simp only [PermVector.ext_iff, getElem_castGE]
  rcases Nat.lt_trichotomy n m with hnm | rfl | hnm <;> grind

@[simp, grind =] theorem isCongr_castGE_castGE_iff {h : n ≤ k} {h' : m ≤ o} :
    (a.castGE h).IsCongr (b.castGE h') ↔ a.IsCongr b := by
  rw [IsCongr]
  simp only [castGE_castGE, castGE_eq_iff, exists_prop]
  grind

instance {a : PermVector n} {b : PermVector m} : Decidable (a.IsCongr b) :=
  decidable_of_decidable_of_iff isCongr_pointwise.symm

theorem IsCongr.eq {a' : PermVector n} (h : a.IsCongr a') : a = a' :=
  (h.eq_castGE_of_ge n.le_refl).symm.trans a'.castGE_refl



@[simp, grind =] theorem isCongr_iff_eq {a' : PermVector n} : a.IsCongr a' ↔ a = a' :=
  ⟨IsCongr.eq, Eq.rec a.isCongr_refl⟩


@[grind →] theorem IsCongr.trans (hab : a.IsCongr b) (hbc : b.IsCongr c) : a.IsCongr c := by
  rcases hab <;> rcases hbc <;> grind

@[grind →] theorem IsCongr.inv_inv : a.IsCongr b → a⁻¹.IsCongr b⁻¹ :=
  Or.imp (Exists.imp <| by simp) (Exists.imp <| by simp)

theorem IsCongr.mul_mul {a' : PermVector n} {b' : PermVector m} (hab : a.IsCongr b)
    (hab' : a'.IsCongr b') : (a * a').IsCongr (b * b') := by
  rcases hab  <;> rcases hab' <;> grind

grind_pattern IsCongr.mul_mul => a * a', b * b'

theorem IsCongr.congr (hab : a.IsCongr a') (hab' : b.IsCongr b') :
    a.IsCongr b ↔ a'.IsCongr b' := by grind

theorem IsCongr.congrLeft (hab : a.IsCongr b) : a.IsCongr c ↔ b.IsCongr c := by grind

theorem IsCongr.congrRight (hab : a.IsCongr b) : c.IsCongr a ↔ c.IsCongr b := by grind

@[grind .]
theorem isCongr_one_one : (1 : PermVector n).IsCongr (1 : PermVector m) :=
  (Nat.le_or_ge n m).elim (fun _ => .inl (by grind)) (fun _ => .inr (by grind))

@[grind =>] theorem IsCongr.eq_one (ha : a.IsCongr (1 : PermVector m)) : a = 1 := by
  rcases ha <;> grind

@[grind =>] theorem IsCongr.one_eq (ha : (1 : PermVector m).IsCongr a) : 1 = a := by
  rcases ha <;> grind

@[simp] theorem isCongr_one_iff : a.IsCongr (1 : PermVector m) ↔ a = 1 := by grind

@[simp] theorem one_isCongr_iff : (1 : PermVector m).IsCongr a ↔ a = 1 := by grind

theorem IsCongr.inv_right (hab : a.IsCongr b⁻¹) : a⁻¹.IsCongr b := by grind

theorem IsCongr.inv_left (hab : a⁻¹.IsCongr b) : a.IsCongr b⁻¹ := by grind

theorem inv_isCongr_iff_isCongr_inv : a⁻¹.IsCongr b ↔ a.IsCongr b⁻¹ := by grind

@[simp] theorem inv_isCongr_inv_iff : a⁻¹.IsCongr b⁻¹ ↔ a.IsCongr b := by grind

@[simp] theorem isCongr_cast {h : n = m} : a.IsCongr (a.cast h) := by subst h; simp

grind_pattern isCongr_cast => a.cast h

@[simp] theorem cast_isCongr {h : n = m} : (a.cast h).IsCongr a := a.isCongr_cast.symm

grind_pattern cast_isCongr => a.cast h

theorem IsCongr.hmul_hmul {a' : PermVector n'} {b' : PermVector m'} (hab : a.IsCongr b)
    (hab' : a'.IsCongr b') : (a.hmul a').IsCongr (b.hmul b') :=
  IsCongr.mul_mul (by simp [hab]) (by simp [hab'])

grind_pattern IsCongr.hmul_hmul => a.hmul a', b.hmul b'

def sigmaSetoid : Setoid (Σ n, PermVector n) where
  r a b := a.2.IsCongr b.2
  iseqv := by grind [Equivalence]

section MinPerm

variable {n m : Nat} (a : PermVector n) (b : PermVector m)

@[grind →] theorem IsCongr.minLen_eq (hab : a.IsCongr b) :
    a.minLen = b.minLen := by rcases hab <;> grind

@[simp] theorem isCongr_minPerm : a.IsCongr a.minPerm := .inr ⟨a.minLen_le, a.minPerm_castGE⟩

grind_pattern isCongr_minPerm => a.minPerm

@[simp] theorem minPerm_isCongr : a.minPerm.IsCongr a := by grind

grind_pattern minPerm_isCongr => a.minPerm

@[simp] theorem isCongr_minPerm_left : a.minPerm.IsCongr b ↔ a.IsCongr b := by grind
@[simp] theorem isCongr_minPerm_right : a.IsCongr b.minPerm ↔ a.IsCongr b := by grind

theorem isCongr_minPerm_minPerm : a.minPerm.IsCongr b.minPerm ↔ a.IsCongr b := by simp

theorem inv_minPerm_isCongr_inv : (a.minPerm)⁻¹.IsCongr a⁻¹ := (a.minPerm_isCongr).inv_inv

theorem minPerm_hmul_minPerm_isCongr_hmul : (a.minPerm.hmul b.minPerm).IsCongr (a.hmul b) :=
  a.minPerm_isCongr.hmul_hmul b.minPerm_isCongr

end MinPerm

end IsCongr

end PermVector

def FinitePerm := Quotient PermVector.sigmaSetoid
