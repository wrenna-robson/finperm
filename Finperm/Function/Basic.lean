/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
import Batteries.Tactic.Alias

@[expose] public section

namespace Function

/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f

protected theorem Bijective.injective : Bijective f → Injective f := And.left
protected theorem Bijective.surjective : Bijective f → Surjective f := And.right

theorem bijective_of_injective_of_surjective : Injective f → Surjective f → Bijective f :=
  And.intro

protected alias Injective.bijective_of_surjective := bijective_of_injective_of_surjective

protected alias Surjective.bijective_of_injective := bijective_of_injective_of_surjective

/-- A pair of functions `(f, g)` is a *splitting* (implicitly, of the identity) when `f` is a left
inverse to`g`, i.e. `f ∘ g = id`. -/
def IsSplitting (f : α → β) (g : β → α) := ∀ i, f (g i) = i

theorem IsSplitting.comp_eq_id (h : IsSplitting f g) : f ∘ g = id := funext h

theorem IsSplitting.injective : IsSplitting f g → Injective g := fun h i j hij =>
  (h i).symm.trans <| (congrArg f hij).trans (h j)

theorem IsSplitting.surjective : IsSplitting f g → Surjective f := fun h i => ⟨g i, h i⟩

theorem isSplitting_of_isSplitting_of_injective :
    IsSplitting f g → Injective f → IsSplitting g f := fun h => (· <| h <| f <| ·)

theorem isSplitting_of_isSplitting_of_surjective :
    IsSplitting f g → Surjective g → IsSplitting g f :=
  fun h => (let ⟨y, hy⟩ := · ·; hy ▸ congrArg g (h y))

alias IsSplitting.isSplitting_of_surjective := isSplitting_of_isSplitting_of_surjective
alias IsSplitting.isSplitting_of_injective := isSplitting_of_isSplitting_of_injective
alias Injective.isSplitting_of_isSplitting := isSplitting_of_isSplitting_of_injective
alias Surjective.isSplitting_of_isSplitting := isSplitting_of_isSplitting_of_surjective

/-- A pair of functions `(f, g)` form an equivalence when they are mutual two-sided inverses,
i.e. `f ∘ g = id` and `g ∘ f = id`. -/
def IsEquiv (f : α → β) (g : β → α) := IsSplitting f g ∧ IsSplitting g f

theorem IsEquiv.symm : IsEquiv f g → IsEquiv g f := And.symm
theorem isEquiv_comm : IsEquiv f g ↔ IsEquiv g f := And.comm

protected theorem IsEquiv.isSplitting_left : IsEquiv f g → IsSplitting f g := And.left
protected theorem IsEquiv.isSplitting_right : IsEquiv f g → IsSplitting g f := And.right

theorem isEquiv_of_isSplitting_of_isSplitting :
    IsSplitting f g → IsSplitting g f → IsEquiv f g := And.intro

protected alias IsSplitting.isEquiv_of_isSplitting := isEquiv_of_isSplitting_of_isSplitting

theorem isEquiv_of_isSplitting_of_surjective : IsSplitting f g → Surjective g ->
    IsEquiv f g := fun hfg => hfg.isEquiv_of_isSplitting ∘ hfg.isSplitting_of_surjective

theorem isEquiv_of_isSplitting_of_injective : IsSplitting f g → Injective f ->
    IsEquiv f g := fun hfg => hfg.isEquiv_of_isSplitting ∘ hfg.isSplitting_of_injective

alias IsSplitting.isEquiv_of_surjective := isEquiv_of_isSplitting_of_surjective
alias Surjective.isEquiv_of_isSplitting := isEquiv_of_isSplitting_of_surjective
alias IsSplitting.isEquiv_of_injective := isEquiv_of_isSplitting_of_injective
alias Injective.isEquiv_of_isSplitting := isEquiv_of_isSplitting_of_injective

theorem IsEquiv.bijective_right : IsEquiv f g → Bijective g :=
  And.imp LeftInverse.injective RightInverse.surjective

theorem IsEquiv.bijective_left : IsEquiv f g → Bijective f :=
  IsEquiv.bijective_right ∘ And.symm
