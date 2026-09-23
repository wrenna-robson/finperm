/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
import Batteries.Tactic.Alias

public section

variable {α : Sort u} {β : Sort v} {γ : Sort w}

namespace Function

section Injective

variable {f : α → β} {g g' : γ → α}

@[grind =>]
theorem Injective.eq_of_comp_left_eq (hf : f.Injective) : f ∘ g = f ∘ g' → g = g' := by
  simp only [funext_iff, comp_apply, hf.eq_iff, imp_self]

@[simp] theorem Injective.comp_left_cancel (hf : f.Injective) :
    f ∘ g = f ∘ g' ↔ g = g' := ⟨hf.eq_of_comp_left_eq, Eq.rec rfl⟩

end Injective

section Surjective

variable {f : α → β} {g g' : β → γ}

protected theorem Surjective.forall (hf : Surjective f) {p : β → Prop} :
    (∀ y, p y) ↔ ∀ x, p (f x) :=
  ⟨fun h x => h (f x), fun h y => let ⟨x, hx⟩ := hf y; hx ▸ h x⟩

protected theorem Surjective.exists (hf : Surjective f) {p : β → Prop} :
    (∃ y, p y) ↔ ∃ x, p (f x) :=
  ⟨fun ⟨y, hy⟩ => let ⟨x, hx⟩ := hf y; ⟨x, hx ▸ hy⟩, fun ⟨x, hx⟩ => ⟨f x, hx⟩⟩

@[grind =>]
theorem Surjective.eq_of_comp_right_eq (hf : f.Surjective) : g ∘ f = g' ∘ f → g = g' := by
  simp only [funext_iff, comp_apply, hf.forall, imp_self]

@[simp] theorem Surjective.comp_right_cancel (hf : f.Surjective) :
    g ∘ f = g' ∘ f ↔ g = g' := ⟨hf.eq_of_comp_right_eq, Eq.rec rfl⟩

theorem Surjective.nonempty_fun (h : f.Surjective) : Nonempty (β → α) :=
  ⟨(Exists.choose <| h ·)⟩

theorem Surjective.nonempty (h : f.Surjective) [Nonempty β] :
    Nonempty α := ⟨Exists.choose (h Classical.ofNonempty)⟩

end Surjective

/-- A function is *bijective* just when it is both injective and surjective. -/
structure Bijective (f : α → β) where private mk ::
  protected injective : Injective f
  protected surjective : Surjective f

/-- A pair of functions `(f, g)` form an equivalence when they are mutual two-sided inverses,
i.e. `f ∘ g = id` and `g ∘ f = id`. -/
structure Inverse (f : α → β) (g : β → α) where private mk ::
  protected leftInverse : f.LeftInverse g
  protected rightInverse : f.RightInverse g

@[expose] def HasInverse {α β} (f : α → β) : Prop := Exists fun finv : β → α => Inverse finv f

@[expose, grind, implicit_reducible] def Idempotent (f : α → α) : Prop := ∀ i, f (f i) = f i

def inclusion (f : α → β) : Subtype (∃ a, f a = ·) → β := Subtype.val
@[expose, grind] def restrict (f : α → β) : α → Subtype (∃ a, f a = ·) := fun i => ⟨f i, ⟨i, rfl⟩⟩

section Restrict

variable {f : α → β}

@[simp] theorem val_restrict : (f.restrict i).val = f i := rfl

@[simp, grind =] theorem val_comp_restrict : Subtype.val ∘ f.restrict = f := rfl

end Restrict

section Bijective

attribute [grind =>] Bijective.injective Bijective.surjective

variable {f : α → β}

@[grind =>]
theorem bijective_of_injective_of_surjective (hi : f.Injective) (hs : f.Surjective) :
  f.Bijective := ⟨hi, hs⟩

protected alias Injective.bijective_of_surjective := bijective_of_injective_of_surjective

protected alias Surjective.bijective_of_injective := bijective_of_injective_of_surjective

theorem bijective_iff_injective_surjective : Bijective f ↔ f.Injective ∧ f.Surjective :=
  ⟨fun h => And.intro h.injective h.surjective, fun ⟨hi, hs⟩ => hi.bijective_of_surjective hs⟩

@[simp] theorem Bijective.comp_left_cancel (hf : f.Bijective) :
    f ∘ g = f ∘ g' ↔ g = g' := hf.injective.comp_left_cancel

@[simp] theorem Bijective.comp_right_cancel (hf : f.Bijective) :
    g ∘ f = g' ∘ f ↔ g = g' := hf.surjective.comp_right_cancel

@[grind =>]
theorem Bijective.eq_of_comp_left_eq (hf : f.Bijective) : f ∘ g = f ∘ g' → g = g' :=
  hf.injective.eq_of_comp_left_eq

@[grind =>]
theorem Bijective.eq_of_comp_right_eq (hf : f.Bijective) : g ∘ f = g' ∘ f → g = g' :=
  hf.surjective.eq_of_comp_right_eq

end Bijective

section LeftInverse

variable {α : Sort u} {β : Sort v} {f : α → β} {g g' : β → α}

theorem LeftInverse.apply_apply (h : f.LeftInverse g) (i : β) : f (g i) = i := h i

theorem leftInverse_def : f.LeftInverse g ↔ ∀ i, f (g i) = i := Iff.rfl

@[grind =>] theorem LeftInverse.comp_eq_id (h : f.LeftInverse g) : f ∘ g = id := funext h

@[grind =>]
theorem LeftInverse.comp_rev_idempotent (h : f.LeftInverse g) : (g ∘ f).Idempotent :=
  (congrArg g <| h.apply_apply <| f ·)

theorem leftInverse_iff_comp_eq_id : f.LeftInverse g ↔ f ∘ g = id :=
  ⟨LeftInverse.comp_eq_id, fun h => congrFun h⟩

attribute [grind =>] LeftInverse.injective

@[grind =>] theorem LeftInverse.surjective : f.LeftInverse g → Surjective f := fun h i => ⟨g i, h i⟩

@[grind =>] theorem leftInverse_of_leftInverse_of_injective (h : f.LeftInverse g)
    (hf : Injective f) : LeftInverse g f := by
  simp only [LeftInverse, hf.eq_iff.symm, h.apply_apply, implies_true]

alias LeftInverse.leftInverse_of_injective := leftInverse_of_leftInverse_of_injective
alias Injective.leftInverse_of_leftInverse := leftInverse_of_leftInverse_of_injective

@[grind =>] theorem leftInverse_of_leftInverse_of_surjective (h : f.LeftInverse g)
    (hg : Surjective g) : LeftInverse g f := by
  simp only [LeftInverse, hg.forall, h.apply_apply, implies_true]

alias LeftInverse.leftInverse_of_surjective := leftInverse_of_leftInverse_of_surjective
alias Surjective.leftInverse_of_leftInverse := leftInverse_of_leftInverse_of_surjective

theorem eq_of_leftInverse_of_leftInverse_of_injective_left (hfg : f.LeftInverse g)
    (hfg' : f.LeftInverse g') (hf : f.Injective) : g = g' := by grind

theorem eq_of_leftInverse_of_leftInverse_of_surjective_right (hfg : g.LeftInverse f)
    (hfg' : g'.LeftInverse f) (hf : f.Surjective) : g = g' := by grind

alias Injective.eq_of_leftInverse_of_leftInverse :=
  eq_of_leftInverse_of_leftInverse_of_injective_left
alias LeftInverse.eq_of_leftInverse_of_injective :=
  eq_of_leftInverse_of_leftInverse_of_injective_left

alias Surjective.eq_of_leftInverse_of_leftInverse :=
  eq_of_leftInverse_of_leftInverse_of_surjective_right
alias LeftInverse.eq_of_leftInverse_of_surjective :=
  eq_of_leftInverse_of_leftInverse_of_surjective_right

theorem isBijective_of_leftInverse_of_bijective_right (hfg : f.LeftInverse g) (hg : g.Bijective) :
    f.Bijective := by grind

alias LeftInverse.bijective_left_of_bijective_right := isBijective_of_leftInverse_of_bijective_right
alias Bijective.bijective_left_of_leftInverse := isBijective_of_leftInverse_of_bijective_right

theorem isBijective_of_leftInverse_of_bijective_left (hfg : f.LeftInverse g) (hg : f.Bijective) :
    g.Bijective := by grind

alias LeftInverse.bijective_right_of_bijective_left := isBijective_of_leftInverse_of_bijective_left
alias Bijective.bijective_right_of_leftInverse := isBijective_of_leftInverse_of_bijective_left

end LeftInverse

section Inverse

variable {f : α → β} {g : β → α}

attribute [grind =>] Inverse.leftInverse Inverse.rightInverse

theorem Inverse.bijective_right (h : Inverse f g) : Bijective g := by grind

theorem Inverse.bijective_left (h : Inverse f g) : Bijective f := by grind

@[grind =>]
theorem inverse_of_leftInverse_of_leftInverse (hfg : f.LeftInverse g)
    (hgf : g.LeftInverse f) : f.Inverse g := ⟨hfg, hgf⟩

alias LeftInverse.inverse_of_leftInverse := inverse_of_leftInverse_of_leftInverse

theorem inverse_iff_leftInverse_rightInverse : f.Inverse g ↔ f.LeftInverse g ∧ g.LeftInverse f := by
  grind

theorem Inverse.symm : Inverse f g → Inverse g f := by grind
theorem inverse_comm : Inverse f g ↔ Inverse g f := by grind

theorem inverse_of_leftInverse_of_surjective : f.LeftInverse g → Surjective g ->
    Inverse f g := by grind

theorem inverse_of_leftInverse_of_injective : f.LeftInverse g → Injective f ->
    Inverse f g := by grind

alias LeftInverse.inverse_of_surjective := inverse_of_leftInverse_of_surjective
alias Surjective.inverse_of_leftInverse := inverse_of_leftInverse_of_surjective
alias LeftInverse.inverse_of_injective := inverse_of_leftInverse_of_injective
alias Injective.inverse_of_leftInverse := inverse_of_leftInverse_of_injective

theorem Inverse.eq_of_rightInverse (h : f.Inverse g) (h' : f.LeftInverse g') :
    g = g' := by grind

alias LeftInverse.eq_of_inverse_right := Inverse.eq_of_rightInverse

theorem Inverse.eq_of_leftInverse (h : f.Inverse g) (h' : g'.LeftInverse f) :
    g = g' := by grind

alias LeftInverse.eq_of_inverse_left := Inverse.eq_of_leftInverse

@[grind =>] theorem Inverse.comp_eq_id_left (h : f.Inverse g) : f ∘ g = id :=
  h.leftInverse.comp_eq_id
@[grind =>] theorem Inverse.comp_eq_id_right (h : f.Inverse g) : g ∘ f = id :=
  h.rightInverse.comp_eq_id

theorem inverse_iff_comps_eq_id : f.Inverse g ↔ f ∘ g = id  ∧ g ∘ f = id := by
  rw [inverse_iff_leftInverse_rightInverse, leftInverse_iff_comp_eq_id, leftInverse_iff_comp_eq_id]

end Inverse

section HasRightInverse

variable {f : α → β} {g : β → α}

theorem hasRightInverse_iff_exists_leftInverse : HasRightInverse f ↔ ∃ g : β → α, f.LeftInverse g :=
  Iff.rfl

theorem LeftInverse.hasRightInverse (h : f.LeftInverse g) : HasRightInverse f := ⟨_, h⟩

theorem HasRightInverse.exists_leftInverse : HasRightInverse f → ∃ g : β → α, f.LeftInverse g := id

noncomputable def HasRightInverse.inv (h : HasRightInverse f) : β → α := h.exists_leftInverse.choose

theorem HasRightInverse.leftInverse_inv (h : HasRightInverse f) : f.LeftInverse h.inv :=
  h.exists_leftInverse.choose_spec

theorem inverse_inv_of_hasRightInverse_of_injective (h : HasRightInverse f) (hs : f.Injective) :
    f.Inverse h.inv := h.leftInverse_inv.inverse_of_injective hs

alias HasRightInverse.inverse_inv_of_injective := inverse_inv_of_hasRightInverse_of_injective
alias Injective.inverse_inv_of_hasRightInverse := inverse_inv_of_hasRightInverse_of_injective

theorem Surjective.hasRightInverse (hf : f.Surjective) : f.HasRightInverse :=
  ⟨_, fun b => (hf b).choose_spec⟩

theorem surjective_iff_hasRightInverse : f.Surjective ↔ f.HasRightInverse :=
  ⟨Surjective.hasRightInverse, HasRightInverse.surjective⟩

@[simp, grind =>] theorem HasRightInverse.comp_inv (h : HasRightInverse f) : f ∘ h.inv = id :=
  h.leftInverse_inv.comp_eq_id

end HasRightInverse

section HasLeftInverse

variable {f : α → β} {g : β → α}

theorem hasLeftInverse_iff_exists_leftInverse : HasLeftInverse f ↔ ∃ g : β → α, g.LeftInverse f :=
  Iff.rfl

theorem LeftInverse.hasLeftInverse (h : f.LeftInverse g) : HasLeftInverse g := ⟨_, h⟩

theorem HasLeftInverse.exists_leftInverse : HasLeftInverse f → ∃ g : β → α, g.LeftInverse f := id

noncomputable def HasLeftInverse.inv (h : HasLeftInverse f) : β → α := h.exists_leftInverse.choose

theorem HasLeftInverse.inv_leftInverse (h : HasLeftInverse f) : h.inv.LeftInverse f :=
  h.exists_leftInverse.choose_spec

theorem inverse_inv_of_hasLeftInverse_of_surjective (h : HasLeftInverse f) (hs : f.Surjective) :
    f.Inverse h.inv := (h.inv_leftInverse.inverse_of_surjective hs).symm

alias HasLeftInverse.inverse_inv_of_surjective := inverse_inv_of_hasLeftInverse_of_surjective
alias Surjective.inverse_inv_of_hasLeftInverse := inverse_inv_of_hasLeftInverse_of_surjective

open Classical in theorem injective_iff_hasLeftInverse [Nonempty (β → α)] :
    f.Injective ↔ f.HasLeftInverse :=
  ⟨fun hf => ⟨fun b => if h : ∃ a, f a = b then h.choose else (ofNonempty : β → α) b,
      (fun a => (dite_eq_left ⟨a, rfl⟩).trans (hf (Exists.choose_spec (p := (f · = f a)) _)))⟩,
  fun ⟨_, h⟩ => h.injective⟩

@[simp, grind =>] theorem HasLeftInverse.inv_comp (h : HasLeftInverse f) : h.inv ∘ f  = id :=
  h.inv_leftInverse.comp_eq_id

end HasLeftInverse

section HasInverse

variable {f : α → β} {g : β → α}

theorem hasInverse_iff_exists_inverse : HasInverse f ↔ ∃ g : β → α, g.Inverse f := Iff.rfl

theorem Inverse.hasInverse_left (h : f.Inverse g) : f.HasInverse := ⟨_, h.symm⟩
theorem Inverse.hasInverse_right (h : f.Inverse g) : g.HasInverse := ⟨_, h⟩

theorem HasInverse.exists_leftinverse : HasInverse f → ∃ g : β → α, g.Inverse f := id
theorem HasInverse.exists_rightInverse : HasInverse f → ∃ g : β → α, f.Inverse g :=
  Exists.imp (fun _ => Inverse.symm)

noncomputable def HasInverse.inv (h : HasInverse f) : β → α := h.choose

@[grind =>]
theorem HasInverse.inv_inverse (h : HasInverse f) : h.inv.Inverse f := h.choose_spec

@[grind =>]
theorem HasInverse.inverse_inv (h : HasInverse f) : f.Inverse h.inv := h.choose_spec.symm
theorem HasInverse.hasInverse_inv (h : HasInverse f) : HasInverse h.inv := ⟨_, h.inverse_inv⟩

@[grind =>]
theorem HasInverse.hasLeftInverse (h : HasInverse f) : HasLeftInverse f :=
  h.imp (fun _ => Inverse.leftInverse)

@[grind =>]
theorem HasInverse.hasRightInverse (h : HasInverse f) : HasRightInverse f :=
  h.imp (fun _ => Inverse.rightInverse)

@[grind =>]
theorem inverse_of_hasLeftInverse_of_hasRightInverse (hl : HasLeftInverse f)
    (hr : HasRightInverse f) : HasInverse f :=
  hl.imp fun _ h => h.inverse_of_surjective hr.surjective

alias HasLeftInverse.hasInverse_of_hasRightInverse := inverse_of_hasLeftInverse_of_hasRightInverse
alias HasRightInverse.hasInverse_of_hasLeftInverse := inverse_of_hasLeftInverse_of_hasRightInverse

@[grind =>]
theorem HasInverse.bijective (h : HasInverse f) : f.Bijective :=
  h.inverse_inv.bijective_left

@[grind =>]
theorem Bijective.hasInverse (hf : f.Bijective) : f.HasInverse :=
    (hf.surjective.hasRightInverse.leftInverse_inv.inverse_of_injective
    hf.injective).hasInverse_left

@[simp, grind =>] theorem HasInverse.comp_inv (h : HasInverse f) : f ∘ h.inv = id :=
  h.inverse_inv.comp_eq_id_left

@[simp, grind =>] theorem HasInverse.inv_comp (h : HasInverse f) : h.inv ∘ f  = id :=
  h.inverse_inv.comp_eq_id_right

@[simp] theorem HasInverse.hasRightInverse_inv (h : HasInverse f) : h.hasRightInverse.inv = h.inv :=
  h.bijective.eq_of_comp_left_eq (by simp)

@[simp] theorem HasInverse.hasLeftInverse_inv (h : HasInverse f) : h.hasLeftInverse.inv = h.inv :=
  h.bijective.eq_of_comp_right_eq (by simp)

theorem bijective_iff_hasInverse : f.Bijective ↔ f.HasInverse :=
  ⟨Bijective.hasInverse, HasInverse.bijective⟩

theorem hasInverse_iff_hasRightInverse_hasLeftInverse :
    HasInverse f ↔ HasLeftInverse f ∧ HasRightInverse f :=
  ⟨fun h => And.intro h.hasLeftInverse h.hasRightInverse,
  fun ⟨hi, hs⟩ => hi.hasInverse_of_hasRightInverse hs⟩

end HasInverse

section Idempotent

variable {f : α → α}

theorem Idempotent.apply_apply (hf : f.Idempotent) (i) : f (f i) = f i := hf i
theorem Idempotent.apply_of_exists_apply (hf : f.Idempotent) {i : α} (hi : ∃ a, f a = i) :
    f i = i := hi.choose_spec ▸ hf.apply_apply _

@[simp, grind =>]
theorem Idempotent.restrict_leftInverse_val (hf : f.Idempotent) :
    f.restrict.LeftInverse Subtype.val := fun ⟨_, hi⟩ => Subtype.ext (hf.apply_of_exists_apply hi)

theorem idempotent_iff : f.Idempotent ↔
    ∃ (β : Sort (max 1 u)) (p : α → β) (q : β → α), p.LeftInverse q ∧ q ∘ p = f := by grind

end Idempotent
