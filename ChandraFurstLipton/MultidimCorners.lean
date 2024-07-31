
import ChandraFurstLipton.NOFModel
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Fin.Basic

namespace NOF

variable {ι G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {d : ℕ} [NeZero d] [Fintype ι]

structure IsMultidimCorner (a : ι → ι → G) (b : ι → G): Prop where
  sum_eq_sum : ∀ i j, ∑ k, a i k = ∑ k, a j k
  isForbiddenPatternWithTip : IsForbiddenPatternWithTip a b
