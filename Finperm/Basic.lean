/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import Finperm.Vector.Nodup
public import Finperm.Function.Fin
import Finperm.Logic.Basic

@[expose] public section

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

open Function

def get (a : Finperm n) (i : Fin n) : Fin n :=
  ⟨a.toVector.get i, (a.getElem_invVector_getElem_toVector i.1 i.2).choose⟩

theorem bijective_get (a : Finperm n) : a.get.Bijective := Injective.bijective_fin <|
    fun i j h => Fin.ext <| by
  have hget : ∀ i : Fin n, i = a.invVector[a.get i] :=
    fun x => (a.getElem_invVector_getElem_toVector x.1 x.2).choose_spec.symm
  rw [hget i, hget j, getElem_congr_idx h]

theorem injective_get (a : Finperm n) : a.get.Injective := a.bijective_get.injective
theorem surjective_get (a : Finperm n) : a.get.Surjective := a.bijective_get.surjective

theorem getElem_toVector_getElem_invVector {n} (a : Finperm n) (i : Nat) (hi : i < n) :
    ∃ hi' : a.invVector[i] < n, a.toVector[a.invVector[i]] = i := by
  obtain ⟨j, _, hj⟩ := a.surjective_get ⟨i, hi⟩
  have h := (a.getElem_invVector_getElem_toVector j j.isLt).choose_spec
  exact ⟨h ▸ j.isLt, getElem_congr_idx h⟩

instance : Inv (Finperm n) where
  inv a := ⟨a.invVector, a.toVector, a.getElem_toVector_getElem_invVector⟩

@[simp, grind =] theorem toVector_inv (a : Finperm n) : a⁻¹.toVector = a.invVector := rfl
@[simp, grind =] theorem invVector_inv (a : Finperm n) : a⁻¹.invVector = a.toVector := rfl

@[simp, grind =] theorem inv_inv (a : Finperm n) : a⁻¹⁻¹ = a := rfl

@[simp, grind =] theorem inv_inj  (a b : Finperm n) : a⁻¹ = b⁻¹ ↔ a = b :=
  ⟨fun h => a.inv_inv ▸ h ▸ b.inv_inv, fun h => h ▸ rfl⟩

theorem isEquiv_get_getInv (a : Finperm n) : a.get.IsEquiv a⁻¹.get :=
    IsSplitting.isEquiv_fin <| fun _ => Fin.ext <| (a.getElem_toVector_getElem_invVector _ _).2

@[simp]
theorem inv_mk (a b : Vector Nat n) {hab} : (Finperm.mk a b hab)⁻¹ =
    Finperm.mk b a (Finperm.mk a b hab).getElem_toVector_getElem_invVector := rfl

instance : GetElem (Finperm n) Nat Nat fun _ i => i < n where
  getElem a i h := a.toVector[i]

@[simp, grind =]
theorem getElem_toVector {i : Nat} {hi : i < n} {a : Finperm n} : a.toVector[i] = a[i] := rfl

grind_pattern getElem_toVector => a.toVector[i]

@[simp, grind =]
theorem getElem_invVector  (a : Finperm n) {i} (hi : i < n) : a.invVector[i] = a⁻¹[i] := rfl

@[simp] theorem getElem_lt (a : Finperm n) (i : Nat) (hi : i < n) : a[i] < n :=
  (a.getElem_invVector_getElem_toVector _ _).1

grind_pattern getElem_lt => a[i]

@[simp, grind =] theorem getElem_mk (a b : Vector Nat n) {hab} {i : Nat} (hi : i < n) :
  (Finperm.mk a b hab)[i]'hi = a[i]'hi := rfl

@[grind =>]
theorem eq_of_getElem_eq (a : Finperm n) (hi : i < n) (hj : j < n)
    (hij : a[i] = a[j]) : i = j := congrArg Fin.val (a.injective_get <| Fin.ext hij)

@[simp] theorem getElem_eq_iff (a : Finperm n) (hi : i < n) (hj : j < n) :
    a[i] = a[j] ↔ i = j := by grind

theorem getElem_ne_of_ne (a : Finperm n) (hi : i < n) (hj : j < n)
    (hij : i ≠ j) : a[i] ≠ a[j] := by grind

theorem getElem_ne_iff (a : Finperm n) {i : Nat} (hi : i < n) {j : Nat} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := by grind

theorem exists_getElem_eq_of_lt (a : Finperm n) (i : Nat) (hi : i < n) :
    ∃ (j : Nat) (hj : j < n), a[j] = i :=
  (Fin.exists_iff.mp ((a.surjective_get ⟨i, hi⟩).imp (fun _ => congrArg Fin.val)))

@[simp] theorem getElem_getElem_inv (a : Finperm n) {i} (hi : i < n) :
  a[a⁻¹[i]] = i := congrArg Fin.val (a.isEquiv_get_getInv.isSplitting_left _)

grind_pattern getElem_getElem_inv => a[a⁻¹[i]]

@[simp] theorem getElem_inv_getElem (a : Finperm n) {i} (hi : i < n) :
  a⁻¹[a[i]] = i := congrArg Fin.val (a.isEquiv_get_getInv.isSplitting_right _)

grind_pattern getElem_inv_getElem => a⁻¹[a[i]]

@[simp]
theorem getElem_inv_eq_self_iff (a : Finperm n) {i : Nat} (hi : i < n) :
    a⁻¹[i] = i ↔ a[i] = i := by grind

theorem eq_of_toVector_eq (a b : Finperm n) (h : a.toVector = b.toVector) : a = b := by
  suffices h : a.toVector = b.toVector ∧ a.invVector = b.invVector by grind [cases Finperm]
  simp only [Vector.ext_iff, getElem_toVector, getElem_invVector] at h ⊢
  grind

theorem eq_of_invVector_eq (a b : Finperm n) (h : a.invVector = b.invVector) : a = b := by
  suffices h : a.toVector = b.toVector ∧ a.invVector = b.invVector by grind [cases Finperm]
  simp only [Vector.ext_iff, getElem_toVector, getElem_invVector] at h ⊢
  grind

@[ext, grind ext]
theorem ext (a b : Finperm n) (h : ∀ (i : Nat) (hi : i < n), a[i] = b[i]) : a = b :=
  a.eq_of_toVector_eq b (Vector.ext h)

theorem extInv (a b : Finperm n)  (h : ∀ (i : Nat) (hi : i < n), a⁻¹[i] = b⁻¹[i]) : a = b :=
  a.eq_of_invVector_eq b (Vector.ext h)

instance : DecidableEq (Finperm n) :=
  fun _ _ => decidable_of_decidable_of_iff Finperm.ext_iff.symm

instance : Subsingleton (Finperm 0) where allEq a b := by grind

instance : Subsingleton (Finperm 1) where allEq a b := by grind

theorem nodup_toVector (a : Finperm n) : a.toVector.Nodup := by
  simp [Vector.nodup_iff_eq_of_getElem_eq]

theorem nodup_invVector (a : Finperm n) : a.invVector.Nodup := by
  simp [Vector.nodup_iff_eq_of_getElem_eq]

@[grind =]
theorem mem_toVector_iff_lt (a : Finperm n) {i : Nat} : i ∈ a.toVector ↔ i < n :=
  a.toVector.mem_iff_getElem.trans ⟨by grind, a.exists_getElem_eq_of_lt _⟩

@[grind =]
theorem mem_invVector_iff_lt (a : Finperm n) {i : Nat} : i ∈ a.invVector ↔ i < n :=
  a.invVector.mem_iff_getElem.trans ⟨by grind, a⁻¹.exists_getElem_eq_of_lt _⟩

theorem mem_toVector_of_lt (a : Finperm n) : ∀ i < n, i ∈ a.toVector := by grind

theorem mem_invVector_of_lt (a : Finperm n) : ∀ i < n, i ∈ a.invVector := by grind

theorem lt_of_mem_toVector (a : Finperm n) : ∀ i ∈ a.toVector, i < n := by grind

theorem lt_of_mem_invVector (a : Finperm n) : ∀ i ∈ a.invVector, i < n := by grind

instance : One (Finperm n) where
  one := Finperm.mk (Vector.range n) (Vector.range n) (by simp)

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

theorem mul_inv_eq_iff {a b c : Finperm n} : a * b⁻¹ = c ↔ a = c * b := by grind
theorem inv_mul_eq_iff {a b c : Finperm n} : a⁻¹ * b = c ↔ b = a * c := by grind
theorem eq_mul_inv_iff {a b c : Finperm n} : c = a * b⁻¹ ↔ c * b = a := by grind
theorem eq_inv_mul_iff {a b c : Finperm n} : c = a⁻¹ * b ↔ a * c = b := by grind

@[simp, grind =] theorem inv_mul_rev {a b : Finperm n} : (a * b)⁻¹ = b⁻¹ * a ⁻¹ := by
  simp [eq_mul_inv_iff, inv_mul_eq_iff]

@[simp, grind =]
theorem swap_same {xs : Vector α n} {i : Nat} {hi} : xs.swap i i hi hi = xs := by grind


/--
For `a` an `Finperm n`, `a.swap i j hi hj` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : Finperm n) (i j : Nat)
    (hi : i < n := by get_elem_tactic) (hj : j < n := by get_elem_tactic) : Finperm n where
  toVector := a.toVector.swap i j
  invVector := a.invVector.swap a[i] a[j]
  getElem_invVector_getElem_toVector := fun k hk => by
    simp only [Vector.getElem_swap, ite_getElem]
    grind

section Swap

variable (a : Finperm n) (hi : i < n) (hj : j < n) (hk : k < n)

@[simp, grind =] theorem inv_swap : (a.swap i j hi hj)⁻¹ = a⁻¹.swap a[i] a[j] := by
  apply eq_of_toVector_eq
  simp only [swap, inv_mk, toVector_inv, invVector_inv, getElem_inv_getElem]

@[simp, grind =]
theorem getElem_swap : (a.swap i j)[k] = a[swapVal i j k]'(by grind) := by
  dsimp [swap]; grind

@[grind =]
theorem getElem_inv_swap : (a.swap i j hi hj)⁻¹[k] = a⁻¹[swapVal a[i] a[j] k]'(by grind) := by simp

@[simp]
theorem swap_self (i : Nat) (hi hi' : i < n) : a.swap i i hi hi' = a := by grind

@[simp]
theorem swap_swap (i j : Nat) (hi hi' : i < n) (hj hj' : j < n) :
    (a.swap i j hi hj).swap i j hi' hj' = a := by ext; simp

end Swap

def transpose (i j : Nat) (hi : i < n := by get_elem_tactic)
    (hj : j < n := by get_elem_tactic) := swap 1 i j hi hj

section Transpose

variable (a : Finperm n) (hi : i < n) (hj : j < n) (hk : k < n)

@[simp, grind =]
theorem getElem_transpose : (transpose i j hi hj)[k] = swapVal i j k := by grind [transpose]

@[simp, grind =]
theorem getElem_inv_transpose : (transpose i j hi hj)⁻¹[k] = swapVal i j k := by grind [transpose]

@[simp, grind =] theorem transpose_self : transpose i i hi hi = 1 := by grind

theorem transpose_mul_self : transpose i j hi hj * transpose i j hi hj = 1 := by grind

theorem inv_transpose : (transpose i j hi hj)⁻¹ = transpose i j hi hj := by grind

theorem mul_transpose : a * transpose i j hi hj = a.swap i j hi hj := by grind

theorem transpose_mul : transpose i j hi hj * a = a.swap a⁻¹[i] a⁻¹[j] (by grind) (by grind) := by
  rw (occs := .pos [1, 2]) [← a.inv_inv, ← inv_swap, ← inv_transpose, ← inv_mul_rev, mul_transpose]

theorem transpose_conj : a * transpose i j hi hj * a⁻¹ =
    transpose a[i] a[j] (by grind) (by grind) := by
  simp [mul_transpose, transpose_mul, mul_inv_eq_iff]

@[simp] theorem swap_transpose : (transpose i j hi hj).swap i j hi' hj' = 1 := by
  ext; simp

@[simp, grind =] theorem transpose_eq_one_iff : transpose i j hi hj = 1 ↔ i = j := by
  simp only [Finperm.ext_iff]; grind

end Transpose

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

theorem Nodup.inv_toFinPerm (v : Vector Nat n) (h₁ : v.Nodup) (h₂ : ∀ i (hi : i < n), v[i] < n) :
    (h₁.toFinperm v h₂)⁻¹ = v.toFinperm (h₁.toFinperm v h₂).mem_toVector_of_lt := rfl

theorem inv_toFinPerm (v : Vector Nat n) (h : ∀ i < n, i ∈ v) : (v.toFinperm h)⁻¹ =
    (v.toFinperm h).nodup_invVector.toFinperm v (v.toFinperm h)⁻¹.getElem_lt := rfl

def shuffle (v : Vector α n) (a : Finperm n) : Vector α n := v.mapFinIdx fun i _ hi => v[a[i]]

@[simp, grind =] theorem getElem_shuffle (v : Vector α n) (a : Finperm n) {i : Nat}
    (hi : i < n) : (v.shuffle a)[i] = v[a[i]] := Vector.getElem_mapFinIdx _

@[simp]
theorem range_shuffle (a : Finperm n) :
    (Vector.range n).shuffle a = a.toVector := by grind

theorem shuffle_range_inv :
    (Vector.range n).shuffle a⁻¹ = a.invVector := by grind

@[simp] theorem shuffle_one (v : Vector α n) :
    v.shuffle (1 : (Finperm n)) = v := by grind

@[simp] theorem shuffle_inv_shuffle (v : Vector α n) (a : Finperm n) :
    (v.shuffle a⁻¹).shuffle a = v := by grind

@[simp] theorem shuffle_shuffle_inv (v : Vector α n) (a : Finperm n) :
    (v.shuffle a).shuffle a⁻¹ = v := by grind

@[simp] theorem shuffle_mul (v : Vector α n) (a b : Finperm n) :
    v.shuffle (a * b) = (v.shuffle a).shuffle b := by grind

theorem shuffle_toVector (a b : Finperm n) :
    a.toVector.shuffle b = (a * b).toVector := by grind

end Vector
