/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Finperm.Vector.Nodup
import Finperm.Function.Fin

/--
A `Finperm n` is a permutation on `n` elements represented by two vectors, which we can
think of as an array of values and a corresponding array of indexes which are inverse to
one another. (One can flip the interpretation of indexes and values, and this is essentially
the inversion operation).
-/
structure Finperm (n : Nat) where
  /--
  Gives the `Finperm` as an vector of size `n`.
  -/
  protected toVector : Vector Nat n
  /--
  Gives the inverse of the `Finperm` as a vector of size `n`.
  -/
  protected invVector : Vector Nat n
  getElem_invVector_getElem_toVector :
      ∀ i, (hi : i < n) → ∃ (hi' : toVector[i] < n), invVector[toVector[i]] = i := by decide

namespace Finperm


instance : GetElem (Finperm n) Nat Nat fun _ i => i < n where
  getElem a i h := a.toVector[i]

@[simp, grind =]
theorem getElem_mk (a b : Vector Nat n) {hab} {i : Nat} (hi : i < n) :
  (Finperm.mk a b hab)[i]'hi = a[i]'hi := rfl

@[simp, grind =]
theorem getElem_toVector {i : Nat} {hi : i < n} {a : Finperm n} : a.toVector[i] = a[i] := rfl

@[simp]
theorem getElem_lt (a : Finperm n) (i : Nat) (hi : i < n) : a[i] < n :=
  (a.getElem_invVector_getElem_toVector _ _).1

grind_pattern getElem_lt => a[i]

theorem getElem_ne (a : Finperm n) {i : Nat} {hi : i < n} : a[i] ≠ n := by grind

grind_pattern getElem_ne => a[i]

theorem eq_of_getElem_eq (a : Finperm n) (hi : i < n) (hj : j < n)
    (hij : a[i] = a[j]) : i = j := by
  grind [=_ getElem_toVector, getElem_invVector_getElem_toVector]

@[simp, grind =] theorem getElem_inj (a : Finperm n) (hi : i < n) (hj : j < n) :
    a[i] = a[j] ↔ i = j := by grind [eq_of_getElem_eq]

theorem getElem_ne_iff (a : Finperm n) {i : Nat} (hi : i < n) {j : Nat} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := by grind

theorem getElem_toVector_getElem_invVector {n} (a : Finperm n) (i : Nat) (hi : i < n) :
    ∃ hi' : a.invVector[i] < n, a.toVector[a.invVector[i]] = i := by
  let f : Fin n → Fin n :=
    fun x => ⟨a.toVector[x.1], (a.getElem_invVector_getElem_toVector x.1 x.2).choose⟩
  have hspec : ∀ x : Fin n, a.invVector[a.toVector[x.1]]'(f x).2 = x.1 :=
    fun x => (a.getElem_invVector_getElem_toVector x.1 x.2).choose_spec
  have hfinj : f.Injective := fun x y hxy => Fin.ext <| (hspec x).symm.trans <|
    (getElem_congr_idx (c := a.invVector) (w := (f x).2) (congrArg Fin.val hxy)).trans (hspec y)
  obtain ⟨x, hx⟩ := hfinj.surjectiveOfFin ⟨i, hi⟩
  have heq : a.toVector[x.1] = i := congrArg Fin.val hx
  have hspec2 : a.invVector[i] = x.1 :=
    (getElem_congr_idx (c := a.invVector) (w := (f x).2) heq).symm.trans (hspec x)
  exact ⟨hspec2 ▸ x.2, (getElem_congr_idx (c := a.toVector) (w := hspec2 ▸ x.2) hspec2).trans heq⟩

theorem getElem_surjective (a : Finperm n) (i : Nat) (hi : i < n) :
    ∃ (j : Nat) (hj : j < n), a[j] = i := ⟨a.invVector[i], a.getElem_toVector_getElem_invVector _ _⟩

instance : Inv (Finperm n) where
  inv a := ⟨a.invVector, a.toVector, a.getElem_toVector_getElem_invVector⟩

@[simp, grind =]
theorem inv_mk (a b : Vector Nat n) {hab} : (Finperm.mk a b hab)⁻¹ =
    Finperm.mk b a (Finperm.mk a b hab).getElem_toVector_getElem_invVector := rfl


theorem getElem_inv_mk (a b : Vector Nat n) {hab} (hi : i < n) :
  (Finperm.mk a b hab)⁻¹[i] = b[i] := by grind

@[simp, grind =]
theorem getElem_invVector  (a : Finperm n) {i} (hi : i < n) : a.invVector[i] = a⁻¹[i] := rfl

@[simp, grind =]
theorem getElem_inv_getElem (a : Finperm n) {i} (hi : i < n) :
    a⁻¹[a[i]] = i := (a.getElem_invVector_getElem_toVector _ _).2

@[simp, grind =]
theorem getElem_getElem_inv (a : Finperm n) {i} (hi : i < n) :
  a[a⁻¹[i]] = i := (a.getElem_toVector_getElem_invVector _ _).2

theorem eq_getElem_inv_iff (a : Finperm n) {i} (hi : i < n) (hj : j < n) :
    i = a⁻¹[j] ↔ a[i] = j := by grind

theorem ne_getElem_inv_iff (a : Finperm n) {i} (hi : i < n) (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := by grind

theorem getElem_inv_eq_iff (a : Finperm n) {i} (hi : i < n) (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by grind

theorem getElem_inv_ne_iff (a : Finperm n) {i} (hi : i < n) (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := by grind

theorem nodup_toVector (a : Finperm n) : a.toVector.Nodup := by
  simp [Vector.nodup_iff_eq_of_getElem_eq]

theorem nodup_invVector (a : Finperm n) : a.invVector.Nodup := by
  simp [Vector.nodup_iff_eq_of_getElem_eq]

@[grind =]
theorem mem_toVector_iff_lt (a : Finperm n) {i : Nat} : i ∈ a.toVector ↔ i < n :=
  a.toVector.mem_iff_getElem.trans ⟨by grind, a.getElem_surjective _⟩

@[grind =]
theorem mem_invVector_iff_lt (a : Finperm n) {i : Nat} : i ∈ a.invVector ↔ i < n :=
  a.invVector.mem_iff_getElem.trans ⟨by grind, a⁻¹.getElem_surjective _⟩

theorem mem_toVector_of_lt (a : Finperm n) : ∀ i < n, i ∈ a.toVector := by grind

theorem mem_invVector_of_lt (a : Finperm n) : ∀ i < n, i ∈ a.invVector := by grind

theorem lt_of_mem_toVector (a : Finperm n) : ∀ i ∈ a.toVector, i < n := by grind

theorem lt_of_mem_invVector (a : Finperm n) : ∀ i ∈ a.invVector, i < n := by grind

@[ext, grind ext]
theorem ext (a b : Finperm n)  (h : ∀ (i : Nat) (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.toVector = b.toVector ∧ a.invVector = b.invVector by grind [cases Finperm]
  grind

theorem extInv (a b : Finperm n)  (h : ∀ (i : Nat) (hi : i < n), a⁻¹[i] = b⁻¹[i]) : a = b := by
  suffices h : a.toVector = b.toVector ∧ a.invVector = b.invVector by grind [cases Finperm]
  grind

instance : DecidableEq (Finperm n) :=
  fun _ _ => decidable_of_decidable_of_iff Finperm.ext_iff.symm

instance : Subsingleton (Finperm 0) where allEq a b := by grind

instance : Subsingleton (Finperm 1) where allEq a b := by grind

instance : One (Finperm n) where
  one := Finperm.mk (Vector.range n) (Vector.range n) (by grind)

@[simp, grind =]
theorem getElem_one {i : Nat} (hi : i < n) : (1 : Finperm n)[i] = i := Vector.getElem_range _

instance : Inhabited (Finperm n) := ⟨1⟩

@[simp]
theorem default_eq : (default : Finperm n) = 1 := rfl

theorem unique_zero : ∀ a : Finperm 0, a = 1 := by grind

theorem unique_one : ∀ a : Finperm 1, a = 1 := by grind

instance : Mul (Finperm n) where
  mul a b := {
    toVector := a.toVector.mapFinIdx fun i _ hi => a[b[i]]
    invVector := b.toVector.mapFinIdx fun i _ hi => b⁻¹[a⁻¹[i]]
    getElem_invVector_getElem_toVector := by grind }

@[simp, grind =] theorem getElem_mul (a b : Finperm n) {i : Nat} (hi : i < n) :
    (a * b)[i] = a[b[i]] := Vector.getElem_mapFinIdx _

instance : Std.Associative (α := Finperm n) (· * ·) where
  assoc := by grind

instance : Std.LawfulIdentity (α := Finperm n) (· * ·) 1 where
  left_id := by grind
  right_id := by grind

@[simp, grind =] theorem inv_mul_cancel : ∀ a : Finperm n, a⁻¹ * a = 1 := by grind
@[simp, grind =] theorem mul_inv_cancel : ∀ a : Finperm n, a * a⁻¹ = 1 := by grind

end Finperm

namespace Vector

def Nodup.toFinperm (v : Vector Nat n) (h₁ : v.Nodup := by decide)
    (h₂ : ∀ i (hi : i < n), v[i] < n := by decide) : Finperm n where
  toVector := v
  invVector := (Vector.range n).map v.toList.idxOf
  getElem_invVector_getElem_toVector := by
    simp only [Vector.getElem_map, Vector.getElem_range, h₂, exists_const]
    intros; apply List.Nodup.idxOf_getElem h₁

def toFinperm (v : Vector Nat n) (h : ∀ i < n, i ∈ v := by decide) : Finperm n where
  toVector := (Vector.range n).map v.toList.idxOf
  invVector := v
  getElem_invVector_getElem_toVector := by
    simp only [Vector.getElem_map, Vector.getElem_range]
    intros i hi; rcases (Vector.mem_iff_getElem.mp (h i hi)) with ⟨j, hj, rfl⟩
    exact ⟨lt_of_lt_of_eq (List.idxOf_lt_length_of_mem (List.mem_of_getElem rfl))
    length_toList, List.getElem_idxOf _⟩

theorem inv_toFinPerm (v : Vector Nat n) (h : ∀ i < n, i ∈ v) : (v.toFinperm h)⁻¹ =
    (v.toFinperm h).nodup_invVector.toFinperm v (v.toFinperm h)⁻¹.getElem_lt := rfl

theorem Nodup.inv_toFinPerm (v : Vector Nat n) (h₁ : v.Nodup) (h₂ : ∀ i (hi : i < n), v[i] < n) :
    (h₁.toFinperm v h₂)⁻¹ = v.toFinperm (h₁.toFinperm v h₂).mem_toVector_of_lt := rfl

def shuffle (v : Vector α n) (a : Finperm n) : Vector α n := v.mapFinIdx fun i _ hi => v[a[i]]

@[simp, grind =] theorem getElem_shuffle (v : Vector α n) (a : Finperm n) {i : Nat}
    (hi : i < n) : (v.shuffle a)[i] = v[a[i]] := Vector.getElem_mapFinIdx _

@[simp]
theorem range_shuffle (a : Finperm n) :
    (Vector.range n).shuffle a = a.toVector := by grind

@[simp] theorem shuffle_one (v : Vector α n) :
    v.shuffle (1 : (Finperm n)) = v := by grind

@[simp] theorem shuffle_inv_shuffle (v : Vector α n) (a : Finperm n) :
    (v.shuffle a⁻¹).shuffle a = v := by grind

@[simp] theorem shuffle_shuffle_inv (v : Vector α n) (a : Finperm n) :
    (v.shuffle a).shuffle a⁻¹ = v := by grind

theorem shuffle_range_inv :
    (Vector.range n).shuffle a⁻¹ = a.invVector := by grind

@[simp] theorem shuffle_mul (v : Vector α n) (a b : Finperm n) :
    v.shuffle (a * b) = (v.shuffle a).shuffle b := by grind

theorem shuffle_toVector (a b : Finperm n) :
    a.toVector.shuffle b = (a * b).toVector := by grind

end Vector
