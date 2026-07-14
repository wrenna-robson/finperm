/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public section

namespace List

theorem Nodup.perm_of_subset_of_length_le {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h : l₁ ⊆ l₂)
    (h' : l₂.length ≤ l₁.length) : l₁.Perm l₂ := by induction h₁ generalizing l₂ with
  | nil => simp_all
  | cons hal₁ hl₁ ih =>
    rw [List.cons_subset] at h
    classical
    rw [List.cons_perm_iff_perm_erase]
    have H1 b hb := (mem_erase_of_ne (hal₁ b hb).symm).mpr (h.2 hb)
    have H2 := length_erase_of_mem h.1 ▸ Nat.sub_le_of_le_add h'
    exact ⟨h.1, ih H1 H2⟩
