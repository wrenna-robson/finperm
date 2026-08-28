/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
namespace Vector

def Nodup (v : Vector α n) : Prop := v.toList.Nodup

theorem nodup_iff_toList_nodup {v : Vector α n} : v.Nodup ↔ v.toList.Nodup := Iff.rfl

theorem nodup_iff_eq_of_getElem_eq {v : Vector α n} : v.Nodup ↔
    ∀ (i j : Nat) (_hi : i < n) (_hj : j < n), v[i] = v[j] → i = j :=
  v.nodup_iff_toList_nodup.trans <| List.nodup_iff_eq_of_getElem_eq.trans <| by simp

theorem Nodup.eq_of_getElem_eq {v : Vector α n} (h : Nodup v) (hi : i < n)
    (hj : j < n) : v[i] = v[j] → i = j := nodup_iff_eq_of_getElem_eq.mp h _ _ _ _

theorem Nodup.eq_of_getElem?_eq {v : Vector α n} (h : Nodup v) (hi : i < n)
    (hij : v[i]? = v[j]?) : i = j := by
  simp [getElem?_def, hi] at hij
  rcases hij with ⟨hj, hij⟩
  exact h.eq_of_getElem_eq hi hj hij

@[simp, grind =] theorem Nodup.getElem_inj {v : Vector α n} (h : Nodup v) {hi : i < n}
    {hj : j < n} : v[i] = v[j] ↔ i = j := ⟨h.eq_of_getElem_eq hi hj, (getElem_congr rfl · hi)⟩

theorem Nodup.getElem?_inj {v : Vector α n} (h₀ : i < n) (h₁ : v.Nodup) :
    v[i]? = v[j]? ↔ i = j := by
  simp [h₀, getElem?_eq_some_iff, h₁.getElem_inj, eq_comm]
  exact fun h => h ▸ h₀

theorem Nodup.getD_inj {v : Vector α n}
    (h₀ : i < n) (h₁ : j < n) (h₂ : Nodup v) :
    v.getD i fallback = v.getD j fallback ↔ i = j := by
  simp [getD, h₀, h₁, h₂.getElem_inj]

theorem Nodup.getElem!_inj [Inhabited α] {v : Vector α n}
    (h₀ : i < n) (h₁ : j < n) (h₂ : Nodup v) : v[i]! = v[j]! ↔ i = j := by
  simp [h₀, h₁, h₂.getElem_inj]
