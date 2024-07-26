import Mathlib.Algebra.BigOperators.Group.Finset

namespace NOF
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {d : ℕ} [NeZero d]

def forget (i : Fin d) (x : Fin d → G) (j : {j : Fin d // j ≠ i}) : G :=
  x j

variable (G d) in
structure Strategy where
  nextBit (i : Fin d) : ({j : Fin d // j ≠ i} → G) → List Bool → Bool
  guess (i : Fin d) : ({j : Fin d // j ≠ i} → G) → List Bool → G

namespace Strategy

def broadcast (S : Strategy G d) (x : Fin d → G) : ℕ → List Bool
  | 0 => []
  | t + 1 => S.nextBit t (forget t x) (broadcast S x t) :: broadcast S x t

lemma broadcast_zero (S : Strategy G d) (x : Fin d → G) : broadcast S x 0 = [] :=
  rfl

lemma broadcast_succ (S : Strategy G d) (x : Fin d → G) (t : ℕ) :
  broadcast S x (t + 1) = S.nextBit t (forget t x) (broadcast S x t) :: broadcast S x t :=
  rfl

def IsValid (S : Strategy G d) (F : (Fin d → G) → G) (t : ℕ) : Prop :=
  ∀ x : Fin d → G, ∀ i : Fin d, S.guess i (forget i x) (broadcast S x t) = F x

theorem length_broadcast (S : Strategy G d) (x : Fin d → G) (t : ℕ) : (broadcast S x t).length = t := by
  induction' t with t ih
  · simp [broadcast_zero S x]
  · simp [broadcast_succ S x t]
    exact ih

end NOF.Strategy
