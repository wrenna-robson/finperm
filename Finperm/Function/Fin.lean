/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Batteries.Data.Fin.Lemmas
public import Finperm.Function.Swap

@[expose] public section

namespace Function

open Fin in
theorem Injective.bijective_of_ge_fin {f : Fin n → Fin m} (hf : f.Injective) (h : m ≤ n) :
    f.Bijective ∧ n = m := by
  induction m generalizing n with
  | zero => exact ⟨⟨hf, (·.elim0)⟩, Nat.eq_zero_of_not_pos fun hf => (f ⟨0, hf⟩).elim0⟩
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
    exact ⟨⟨hf, fun a => (hgf (g a)).imp fun _ hx => swapVal_bijective.injective hx⟩, by omega⟩

theorem Injective.bijective_fin {f : Fin n → Fin n} (hf : f.Injective) : f.Bijective :=
  (hf.bijective_of_ge_fin (Nat.le_refl _)).1

theorem Surjective.bijective_of_le_fin {f : Fin n → Fin m} (hf : f.Surjective)
    (h : n ≤ m) : f.Bijective ∧ n = m := by
  let g (y : Fin m) : Fin n := (hf y).choose
  have hg : f.IsSplitting g := fun y => (hf y).choose_spec
  obtain ⟨hgBij, hmn⟩ := hg.injective.bijective_of_ge_fin h
  exact ⟨⟨(hg.isSplitting_of_surjective hgBij.surjective).injective, hf⟩, hmn.symm⟩

theorem Surjective.bijective_fin {f : Fin n → Fin n} (hf : f.Surjective) : f.Bijective :=
  (hf.bijective_of_le_fin (Nat.le_refl _)).1

@[simp] theorem injective_iff_bijective_fin {f : Fin n → Fin n} : f.Injective ↔ f.Bijective :=
  ⟨Injective.bijective_fin, Bijective.injective⟩

@[simp] theorem surjective_iff_bijective_fin {f : Fin n → Fin n} : f.Surjective ↔ f.Bijective :=
  ⟨Surjective.bijective_fin, Bijective.surjective⟩

theorem IsSplitting.isSplitting_fin {f g : Fin n → Fin n} (h : f.IsSplitting g) :
    g.IsSplitting f := h.isSplitting_of_surjective h.injective.bijective_fin.surjective

theorem IsSplitting.isEquiv_fin {f g : Fin n → Fin n} (hf : f.IsSplitting g) : f.IsEquiv g :=
  hf.isEquiv_of_injective hf.surjective.bijective_fin.injective

@[simp] theorem isSplitting_iff_isEquiv_fin {f g : Fin n → Fin n} :
    f.IsSplitting g ↔ f.IsEquiv g := (and_iff_left_of_imp IsSplitting.isSplitting_fin).symm

def finInv (f : Fin n → Fin n) : Fin n → Fin n := fun i => (Fin.find? (f · == i)).getD i

theorem Bijective.isEquiv_finInv {f : Fin n → Fin n} (hf : f.Bijective) :
    f.IsEquiv (finInv f) := IsSplitting.isEquiv_fin <| fun i => by
  have h : (Fin.find? (f · == i)).isSome :=
    Fin.isSome_find?_of_eq_true (beq_of_eq (hf.surjective i).choose_spec)
  exact eq_of_beq <| (congrArg (f · == i) (Option.get_eq_getD _).symm).trans
    (Fin.get_find?_eq_true h)

end Function
