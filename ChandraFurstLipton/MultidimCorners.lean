
import ChandraFurstLipton.NOFModel
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Fin.Basic

namespace NOF

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {d : ℕ} [NeZero d]
variable (i : Fin d)

structure IsCorner (A : Set (G × G)) (x₁ y₁ x₂ y₂ : G) : Prop where
  fst_fst_mem : (x₁, y₁) ∈ A
  fst_snd_mem : (x₁, y₂) ∈ A
  snd_fst_mem : (x₂, y₁) ∈ A
  add_eq_add : x₁ + y₂ = x₂ + y₁

structure IsMultidimCorner (a : Fin d → Fin d → G) (b : Fin d → G) : Prop where
  sum_eq_sum : ∀ i j, ∑ k, a i k = ∑ k, a j k
  isForbiddenPatternWithTip : IsForbiddenPatternWithTip a b
