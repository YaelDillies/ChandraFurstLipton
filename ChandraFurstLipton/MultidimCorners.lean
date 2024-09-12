import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Fin.Basic

namespace NOF
variable {ι G : Type*}  {d : ℕ} [Fintype ι]
  {a : Fin d → Fin d → G} {v : Fin d → G}

def forget (i : ι) (x : ι → G) (j : {j : ι // j ≠ i}) : G := x j

def IsForbiddenPatternWithTip (a : ι → ι → G) (v : ι → G) : Prop := ∀ ⦃i j⦄, i ≠ j → a i j = v j

def IsForbiddenPattern (a : ι → ι → G) : Prop := ∃ v, IsForbiddenPatternWithTip a v

lemma isForbiddenPatternWithTip_iff_forget :
    IsForbiddenPatternWithTip a v ↔ ∀ i, forget i v = forget i (a i) := by
  simp [Function.funext_iff, IsForbiddenPatternWithTip, eq_comm, forget]

protected alias ⟨IsForbiddenPatternWithTip.forget, IsForbiddenPatternWithTip.of_forget⟩ :=
  isForbiddenPatternWithTip_iff_forget

variable [AddCommGroup G]

structure IsMultidimCorner (a : ι → ι → G) (b : ι → G): Prop where
  sum_eq_sum : ∀ i j, ∑ k, a i k = ∑ k, a j k
  isForbiddenPatternWithTip : IsForbiddenPatternWithTip a b

variable [DecidableEq ι]

lemma isMultidimCorner_forget_of_isForbiddenPattern (a : ι → ι → G) (h : IsForbiddenPattern a)
    (hS : ∀ i, ∑ j, a i j = 0) (i : ι) :
    IsMultidimCorner (fun j => forget i (a j)) (forget i (a i)) := by
    rw [IsForbiddenPattern] at h
    obtain ⟨v, hv⟩ := h
    refine ⟨fun k l => ?_, fun k l hneq => ?_⟩
    · rw [← sub_eq_zero]
      calc
        ∑ j : { j // j ≠ i }, a k j - ∑ j : { j // j ≠ i }, a l j
          = ∑ j : {j // j ≠ i}, (a k j - a l j) := by rw [Finset.sum_sub_distrib]
        _ = ∑ j ∈ {i}ᶜ, (a k j - a l j) := (Finset.sum_subtype _ (by simp) (a k - a l)).symm
        _ = ∑ j ∈ {i}ᶜ, (a k j - a l j) + (a k i - a l i) := by simp [hv k.2, hv l.2]
        _ = ∑ j : ι, (a k j - a l j) := by rw [← Fintype.sum_eq_sum_compl_add]
        _ = 0 := by rw [Finset.sum_sub_distrib, sub_eq_zero, hS k, hS l]
    · rw [forget, forget, hv, hv l.2.symm]
      aesop

end NOF
