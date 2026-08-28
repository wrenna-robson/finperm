/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Batteries.Data.Fin.Lemmas
import Finperm.Function.Swap

@[expose] public section

namespace Function

theorem RightInverse.leftInverse_of_surjective {f : α → β} {g : β → α} :
    RightInverse f g → Surjective f → LeftInverse f g :=
  fun h hg x ↦ let ⟨y, hy⟩ := hg x; hy ▸ congrArg f (h y)

def finInv (f : Fin n → Fin n) : Fin n → Fin n := fun i => (Fin.find? (f · == i)).getD i

theorem apply_finInv_eq_of_apply_eq {f : Fin n → Fin n} (hf : f j = i) :
    f (finInv f i) = i := by
  have h : (Fin.find? (f · == i)).isSome := Fin.isSome_find?_of_eq_true (beq_of_eq hf)
  rw [finInv, ← beq_iff_eq, ← Option.get_eq_getD (Fin.find? (f · == i)) (h := h),
    Fin.get_find?_eq_true h]

theorem Surjective.rightInverse_finInv {f : Fin n → Fin n} (hf : f.Surjective) :
    (finInv f).RightInverse f := fun i => apply_finInv_eq_of_apply_eq (hf i).choose_spec

theorem Injective.leftInverse_finInv {f : Fin n → Fin n} (hf : f.Injective) :
    (finInv f).LeftInverse f := fun _ => hf (apply_finInv_eq_of_apply_eq rfl)

theorem Surjective.injective_finInv {f : Fin n → Fin n} (hf : f.Surjective) :
    (finInv f).Injective := hf.rightInverse_finInv.injective

theorem Injective.surjective_finInv {f : Fin n → Fin n} (hf : f.Injective) :
    (finInv f).Surjective := RightInverse.surjective hf.leftInverse_finInv

open Fin in
theorem Injective.surjectiveOfFin {f : Fin n → Fin n} (hf : f.Injective) : f.Surjective := by
  induction n with
  | zero => exact (·.elim0)
  | succ n IH =>
    let g := swapVal (last n) (f (last n))
    have hgf : Surjective (g ∘ f) := by
      apply Fin.lastCases
      · exact ⟨last n, swapVal_apply_right _ _⟩
      · intro i
        let F (j : Fin n) : Fin n := ((g ∘ f) j.castSucc).castLT (val_lt_last <| by grind)
        have hF : F.Injective := by grind [Function.Injective]
        exact (IH hF i).imp' Fin.castSucc (fun _ => Fin.ext ∘ congrArg (@Fin.val n))
    exact fun a => (hgf (g a)).imp fun _ hx => swapVal_injective hx

theorem Injective.rightInverse_finInv {f : Fin n → Fin n} (hf : f.Injective) :
    (finInv f).RightInverse f := hf.surjectiveOfFin.rightInverse_finInv

theorem Surjective.surjective_finInv {f : Fin n → Fin n} (hf : f.Surjective) :
    (finInv f).Surjective := hf.injective_finInv.surjectiveOfFin

theorem Surjective.leftInverse_finInv {f : Fin n → Fin n} (hf : f.Surjective) :
    (finInv f).LeftInverse f :=
  hf.rightInverse_finInv.leftInverse_of_surjective hf.surjective_finInv

theorem Surjective.injectiveOfFin {f : Fin n → Fin n} (hf : f.Surjective) : f.Injective :=
  hf.leftInverse_finInv.injective

theorem Injective.injective_finInv {f : Fin n → Fin n} (hf : f.Injective) :
    (finInv f).Injective := hf.surjective_finInv.injectiveOfFin

end Function
