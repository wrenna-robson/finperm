/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Batteries.Data.Fin.Lemmas
public import FinitePerm.Function.Swap

@[expose] public section

namespace Function

open Fin in
@[grind =>]
theorem Injective.bijective_of_ge_fin {f : Fin n → Fin m} (hf : f.Injective) (h : m ≤ n) :
    f.Bijective ∧ n = m := by
  induction m generalizing n with
  | zero =>
    exact ⟨hf.bijective_of_surjective
      (·.elim0), Nat.eq_zero_of_not_pos fun hf => (f ⟨0, hf⟩).elim0⟩
  | succ m IH =>
    rcases Nat.exists_eq_add_of_lt h with ⟨k, rfl⟩
    let g := swapVal (last m) (f (last (m + k)))
    let F (j : Fin (m + k)) : Fin m := ((g ∘ f) j.castSucc).castLT (val_lt_last <| by grind)
    have hF : F.Injective := by grind [Function.Injective]
    obtain ⟨hFbij, hmk⟩ := IH hF (Nat.le_add_right _ _)
    have hgf : Surjective (g ∘ f) := by
      apply Fin.lastCases
      · exact ⟨last _, swapVal_apply_right _ _⟩
      · intro i
        rcases hFbij.surjective i with ⟨t, rfl⟩
        exact ⟨t.castSucc, Fin.ext rfl⟩
    exact ⟨hf.bijective_of_surjective
      (fun a => (hgf (g a)).imp fun _ hx => swapVal_bijective.injective hx), by omega⟩

theorem Injective.bijective_fin {f : Fin n → Fin n} (hf : f.Injective) : f.Bijective :=
  (hf.bijective_of_ge_fin (Nat.le_refl _)).1

@[grind =>]
theorem Surjective.bijective_of_le_fin {f : Fin n → Fin m} (hf : f.Surjective)
    (h : n ≤ m) : f.Bijective ∧ n = m := by
  let g (y : Fin m) : Fin n := (hf y).choose
  have hg : f.LeftInverse g := fun y => (hf y).choose_spec
  grind

theorem Surjective.bijective_fin {f : Fin n → Fin n} (hf : f.Surjective) : f.Bijective := by
  grind

@[simp] theorem injective_iff_bijective_fin {f : Fin n → Fin n} : f.Injective ↔ f.Bijective := by
  grind

@[simp] theorem surjective_iff_bijective_fin {f : Fin n → Fin n} :
    f.Surjective ↔ f.Bijective := by grind

theorem LeftInverse.leftInverse_fin {f g : Fin n → Fin n} (h : f.LeftInverse g) :
    g.LeftInverse f := by grind

theorem LeftInverse.inverse_fin {f g : Fin n → Fin n} (hf : f.LeftInverse g) : f.Inverse g := by
  grind

@[simp] theorem leftInverse_iff_inverse_fin {f g : Fin n → Fin n} :
    f.LeftInverse g ↔ f.Inverse g := by grind

def finInv (f : Fin n → Fin n) : Fin n → Fin n := fun i => (Fin.find? (f · == i)).getD i

@[grind .]
theorem Surjective.inverse_finInv {f : Fin n → Fin n} (hf : f.Surjective) :
    f.Inverse (finInv f) := LeftInverse.inverse_fin <| fun i => by
  have h : (Fin.find? (f · == i)).isSome :=
    Fin.isSome_find?_of_eq_true (beq_of_eq (hf i).choose_spec)
  exact eq_of_beq <| (congrArg (f · == i) (Option.get_eq_getD _).symm).trans
    (Fin.get_find?_eq_true h)

theorem findSome?_false : Fin.findSome? (α := α) (fun (_ : Fin n) => none) = none := by
  simp

theorem find?_false : Fin.find? (fun (_ : Fin n) => false) = none := findSome?_false

theorem findSomeRev?_false : Fin.findSomeRev? (α := α) (fun (_ : Fin n) => none) = none := by
  simp only [Fin.findSomeRev?_eq_none_iff, implies_true]

theorem findRev?_false : Fin.findRev? (fun (_ : Fin n) => false) = none := findSome?_false

end Function
