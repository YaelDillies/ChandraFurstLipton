

import Mathlib

namespace NOF

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {d : ℕ} [NeZero d]

def eval (x : Fin d → G) : Bool :=
  ∑ i, x i == 0

def forget (i : Fin d) (x : Fin d → G) (j : {j : Fin d // j ≠ i}) : G :=
  x j

variable (G d) in
structure Strategy where
  nextBit (i : Fin d) : ({j : Fin d // j ≠ i} → G) → List Bool → Bool
  guess (i : Fin d) : ({j : Fin d // j ≠ i} → G) → List Bool → G

def broadcast (S : Strategy G d) (x : Fin d → G) (i : Fin d) : ℕ → List Bool
  | 0 => []
  | t + 1 => S.nextBit i (forget i x) (broadcast S x i t) :: (broadcast S x i t)

def Strategy.IsValid (S : Strategy G d) (F : (Fin d → G) → G) (t : ℕ) : Prop :=
  ∀ x : Fin d → G, ∀ i : Fin d, S.guess i (forget i x) (broadcast S x i t) = F x
