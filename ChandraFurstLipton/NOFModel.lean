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

def broadcast (S : Strategy G d) (x : Fin d → G) (i : Fin d) : ℕ → List Bool
  | 0 => []
  | t + 1 => S.nextBit i (forget i x) (broadcast S x i t) :: (broadcast S x i t)

def IsValid (S : Strategy G d) (F : (Fin d → G) → G) (t : ℕ) : Prop :=
  ∀ x : Fin d → G, ∀ i : Fin d, S.guess i (forget i x) (broadcast S x i t) = F x

end NOF.Strategy
