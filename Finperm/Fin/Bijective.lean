module

public import Finperm.List.Perm

theorem Function.Surjective.of_comp_left {g : γ → α} (S : Surjective (f ∘ g))
    (hf : Injective f) : Surjective g := fun a ↦ (S (f a)).imp (fun i => @hf (g i) a)
    --fun a ↦ let ⟨c, hc⟩ := S (f a); ⟨c, hf hc⟩
theorem Fin.forall_fin_succ' {P : Fin (n + 1) → Prop} :
    (∀ i, P i) ↔ (∀ i : Fin n, P i.castSucc) ∧ P (.last _) :=
  ⟨fun H => ⟨fun _ => H _, H _⟩, fun ⟨H0, H1⟩ i => Fin.lastCases H1 H0 i⟩
theorem Fin.exists_fin_succ' {P : Fin (n + 1) → Prop} :
    (∃ i, P i) ↔ (∃ i : Fin n, P i.castSucc) ∨ P (.last _) :=
  ⟨fun ⟨i, h⟩ => Fin.lastCases Or.inr (fun i hi => Or.inl ⟨i, hi⟩) i h,
   fun h => h.elim (fun ⟨i, hi⟩ => ⟨i.castSucc, hi⟩) (fun h => ⟨.last _, h⟩)⟩

namespace Fin

theorem blahj {i : Fin n} {j : Fin (n + 1)} : j = i.castSucc ↔
    ∃ (h : j ≠ last n), j.castLT (by grind) = i := by
  simp [Fin.ext_iff]
  grind


theorem surjective_of_injective (f : Fin n → Fin n) (hf : f.Injective) : f.Surjective := by
  induction n with | zero => exact (·.elim0) | succ n IH =>
  let g i := if i = f (last n) then last n else if i = last n then f (last n) else i
  have hg : g.Injective := by
    intro a b
    apply Decidable.not_imp_not (a := a = b).mp
    intro hab hg
    simp [Fin.ext_iff, g, apply_ite Fin.val] at hg
    grind?
    simp [g, ite_eq_iff] at hab
    grind [Function.Injective]

  intro a
  refine Exists.imp (fun i hi => @hg (f i) a hi) ?_
  cases ha : g a using lastCases with | last | cast i
  · exact ⟨last n, if_pos rfl⟩
  · let F (i : Fin n) : Fin n := ((g ∘ f) (i.castSucc)).castLT (by grind)
    have h_Finj : F.Injective := by grind [Function.Injective]
    exact (IH F h_Finj i).imp' Fin.castSucc (fun _ => Fin.ext ∘ congrArg (@Fin.val n))
