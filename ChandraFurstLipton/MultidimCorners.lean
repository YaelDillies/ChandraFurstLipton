import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Fin.Basic

namespace NOF
variable {ι G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {d : ℕ} [NeZero d] [Fintype ι]
  {a : Fin d → Fin d → G} {v : Fin d → G}

def forget (i : ι) (x : ι → G) (j : {j : ι // j ≠ i}) : G := x j

def IsForbiddenPatternWithTip (a : ι → ι → G) (v : ι → G) : Prop := ∀ ⦃i j⦄, i ≠ j → a i j = v j

def IsForbiddenPattern (a : ι → ι → G) : Prop := ∃ v, IsForbiddenPatternWithTip a v

lemma isForbiddenPatternWithTip_iff_forget :
    IsForbiddenPatternWithTip a v ↔ ∀ i, forget i v = forget i (a i) := by
  simp [Function.funext_iff, IsForbiddenPatternWithTip, eq_comm, forget]

protected alias ⟨IsForbiddenPatternWithTip.forget, IsForbiddenPatternWithTip.of_forget⟩ :=
  isForbiddenPatternWithTip_iff_forget

structure IsMultidimCorner (a : ι → ι → G) (b : ι → G): Prop where
  sum_eq_sum : ∀ i j, ∑ k, a i k = ∑ k, a j k
  isForbiddenPatternWithTip : IsForbiddenPatternWithTip a b

end NOF
