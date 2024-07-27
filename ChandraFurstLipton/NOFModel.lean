
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Bits
import Init.Data.BitVec.Basic

namespace NOF

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {d : ℕ} [NeZero d]

def forget (i : Fin d) (x : Fin d → G) (j : {j : Fin d // j ≠ i}) : G :=
  x j

variable (G d) in
structure Strategy where
  nextBit (i : Fin d) : ({j : Fin d // j ≠ i} → G) → List Bool → Bool
  guess (i : Fin d) : ({j : Fin d // j ≠ i} → G) → List Bool → Bool

namespace Strategy

def getBits (B : List Bool) (i : ℕ) (d : ℕ) : List Bool := Id.run do
  let mut L := []
  for j in [0:B.length] do
    L := L ++ [B.getI ((i - 1) % d + j)]
  pure L

noncomputable
def trivial (hd : 3 ≤ d) (F : (Fin d → G) → Bool) : Strategy G d where
  nextBit i x B := by
    refine (Nat.bits (Fintype.equivFin G (x ⟨i + 1, ?_ ⟩))).getI (B.length / d)
    rw [Ne, add_right_eq_self, ← Nat.cast_one, Fin.natCast_eq_zero, Nat.dvd_one]
    omega
  guess i x B := F fun j => if h : j = i then (Fintype.equivFin G).invFun (BitVec.toNat (BitVec.ofBoolListLE (getBits B i d))) else x ⟨j, h⟩

def broadcast (S : Strategy G d) (x : Fin d → G) : ℕ → List Bool
  | 0 => []
  | t + 1 => S.nextBit t (forget t x) (broadcast S x t) :: broadcast S x t

@[simp]
lemma broadcast_zero (S : Strategy G d) (x : Fin d → G) : broadcast S x 0 = [] :=
  rfl

lemma broadcast_succ (S : Strategy G d) (x : Fin d → G) (t : ℕ) :
  broadcast S x (t + 1) = S.nextBit t (forget t x) (broadcast S x t) :: broadcast S x t :=
  rfl

@[simp]
def IsValid (S : Strategy G d) (F : (Fin d → G) → Bool) (t : ℕ) : Prop :=
  ∀ x : Fin d → G, ∀ i : Fin d, S.guess i (forget i x) (broadcast S x t) = F x

@[simp]
theorem length_broadcast (S : Strategy G d) (x : Fin d → G) (t : ℕ) : (broadcast S x t).length = t := by
  induction' t with t ih
  · simp [broadcast_zero S x]
  · simp [broadcast_succ S x t]
    exact ih

noncomputable
def complexity (S : Strategy G d) (F : (Fin d → G) → Bool) : ENat :=
  ⨅ (t : ℕ) (_ : IsValid S F t), t

lemma le_complexity {t : ℕ} {F : (Fin d → G) → Bool} {S : Strategy G d} :
    t ≤ Strategy.complexity S F ↔ ∀ r : ℕ, S.IsValid F r → t ≤ r := by
  simp [Strategy.complexity]

end Strategy

noncomputable
def funComplexity (F : (Fin d → G) → Bool) :=
  ⨅ (S : Strategy G d), S.complexity F

lemma le_funComplexity {t : ℕ} {F : (Fin d → G) → Bool} :
    t ≤ funComplexity F ↔ ∀ S : Strategy G d, t ≤ S.complexity F := by
  simp [funComplexity]

def IsForbiddenPatternWithTip (a : Fin d → Fin d → G) (v : Fin d → G) : Prop :=
  ∀ i j, i ≠ j → a i j = v j

def IsForbiddenPattern (a : Fin d → Fin d → G) : Prop :=
  ∃ v : Fin d → G, IsForbiddenPatternWithTip a v
