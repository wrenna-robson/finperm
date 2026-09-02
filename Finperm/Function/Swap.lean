/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

module

public import Finperm.Function.Basic

@[expose] public section

namespace Function

def swapVal [BEq α] (a b x : α) : α := bif x == a then b else bif x == b then a else x

section SwapVal

variable [BEq α] {a b x : α}

@[grind =] theorem swapVal_apply_def (a b x : α) : swapVal a b x =
    bif x == a then b else bif x == b then a else x := rfl

@[simp]
theorem swapVal_apply_left [ReflBEq α] (a b : α) : swapVal a b a = b := by grind

@[simp]
theorem swapVal_apply_right [LawfulBEq α] (a b : α) : swapVal a b b = a := by grind

@[simp]
theorem swapVal_apply_of_ne_of_ne [LawfulBEq α] (ha : x ≠ a) (hb : x ≠ b) :
    swapVal a b x = x :=  by grind

@[simp, grind =] theorem swapVal_self [LawfulBEq α] : swapVal a a = id := by grind

@[grind =] theorem swapVal_eq_id [LawfulBEq α] : swapVal a b = id ↔ a = b :=
  ⟨fun h => (swapVal_apply_right a b).symm.trans (h ▸ rfl), fun h => h ▸ swapVal_self⟩

theorem swapVal_flip [h : BEq β] [LawfulBEq β] : flip (@swapVal β h) = @swapVal β h := by
  unfold flip; grind

theorem swapVal_comm [LawfulBEq α] (a b : α) : swapVal a b = swapVal b a := by grind

@[simp] theorem swapVal_comp_flip [LawfulBEq α] : swapVal a b ∘ swapVal b a = id := by grind

@[simp] theorem swapVal_comp_self [LawfulBEq α] : swapVal a b ∘ swapVal a b = id := by grind

@[simp] theorem swapVal_apply_flip [LawfulBEq α] : swapVal a b (swapVal b a x) = x := by grind

@[simp] theorem swapVal_apply_self [LawfulBEq α] : swapVal a b (swapVal a b x) = x := by grind

@[simp] theorem swapVal_swapVal [LawfulBEq α] : swapVal a b (swapVal a b x) = x := by grind

theorem isEquiv_swapVal_swapVal [LawfulBEq α] :
    IsEquiv (swapVal a b) (swapVal a b) :=
⟨fun _ => swapVal_apply_self, fun _ => swapVal_apply_self⟩

theorem isEquiv_swapVal_swapVal_flip [LawfulBEq α] :
    IsEquiv (swapVal a b) (swapVal b a) :=
  ⟨fun _ => swapVal_apply_flip, fun _ => by rw [swapVal_comm]; exact swapVal_apply_self⟩

theorem swapVal_bijective [LawfulBEq α] :
    (swapVal a b).Bijective := isEquiv_swapVal_swapVal.bijective_left

theorem swapVal_apply_eq_iff [LawfulBEq α] : swapVal a b x = y ↔ x = swapVal a b y := by grind
theorem eq_swapVal_apply_iff [LawfulBEq α] : x = swapVal a b y ↔ swapVal a b x = y := by grind

theorem swapVal_injective_of_left [LawfulBEq α] :
    (swapVal a ·).Injective := fun c d h ↦ (swapVal_apply_left a c).symm.trans
  ((congrFun h a).trans (swapVal_apply_left a d))

theorem swapVal_injective_of_right [LawfulBEq α] :
    (swapVal · b).Injective := fun c d h ↦ (swapVal_apply_right c b).symm.trans
  ((congrFun h b).trans (swapVal_apply_right d b))

@[simp] theorem swapVal_eq_left_iff [LawfulBEq α] : swapVal a b x = a ↔ x = b := by grind
@[simp] theorem swapVal_eq_right_iff [LawfulBEq α] : swapVal a b x = b ↔ x = a := by grind
theorem swapVal_ne_left_iff [LawfulBEq α] : swapVal a b x ≠ a ↔ x ≠ b := by grind
theorem swapVal_ne_right_iff [LawfulBEq α] : swapVal a b x ≠ b ↔ x ≠ a := by grind

theorem swapVal_eq_iff [LawfulBEq α] : swapVal a b = swapVal c d ↔
    a = c ∧ b = d ∨ a = d ∧ b = c ∨ a = b ∧ c = d := by
  constructor
  · intro h
    have H1 := congrFun h a
    have H2 := congrFun h c
    clear h
    simp at H1 H2
    subst H2
    simp [eq_swapVal_apply_iff] at H1
    grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩| ⟨rfl, rfl⟩)
    · rfl
    · exact swapVal_comm a b
    · exact swapVal_self.trans swapVal_self.symm

end SwapVal
