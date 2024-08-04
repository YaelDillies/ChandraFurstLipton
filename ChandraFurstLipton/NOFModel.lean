import Init.Data.BitVec.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Bits
import ChandraFurstLipton.MultidimCorners

namespace NOF

variable {ι G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {d : ℕ} [NeZero d] [Fintype ι]

variable (G d) in
structure Protocol where
  nextBit (i : Fin d) : ({j : Fin d // j ≠ i} → G) → List Bool → Bool
  guess (i : Fin d) : ({j : Fin d // j ≠ i} → G) → List Bool → Bool

variable {F : (Fin d → G) → Bool} {P : Protocol G d} {a : Fin d → Fin d → G} {v : Fin d → G}
  {B : List Bool} {t : ℕ}

namespace Protocol

def getBits (B : List Bool) (i : ℕ) (d : ℕ) : List Bool := Id.run do
  let mut L := []
  for j in [0:B.length] do
    L := L ++ [B.getI ((i - 1) % d + j)]
  pure L

noncomputable
def trivial (hd : 3 ≤ d) (F : (Fin d → G) → Bool) : Protocol G d where
  nextBit i x B := by
    refine (Nat.bits (Fintype.equivFin G (x ⟨i + 1, ?_ ⟩))).getI (B.length / d)
    rw [Ne, add_right_eq_self, ← Nat.cast_one, Fin.natCast_eq_zero, Nat.dvd_one]
    omega
  guess i x B := F fun j ↦
    if h : j = i then
      (Fintype.equivFin G).symm (BitVec.toNat (BitVec.ofBoolListLE (getBits B i d)))
    else
      x ⟨j, h⟩

def broadcast (P : Protocol G d) (x : Fin d → G) : ℕ → List Bool
  | 0 => []
  | t + 1 => P.nextBit t (forget (t : Fin d) x) (broadcast P x t) :: broadcast P x t

@[simp] lemma broadcast_zero (P : Protocol G d) (x : Fin d → G) : broadcast P x 0 = [] := rfl

lemma broadcast_succ (P : Protocol G d) (x : Fin d → G) (t : ℕ) :
    broadcast P x (t + 1)
      = P.nextBit t (forget (t : Fin d) x) (broadcast P x t) :: broadcast P x t := rfl

def IsValid (P : Protocol G d) (F : (Fin d → G) → Bool) (t : ℕ) : Prop :=
  ∀ x i, P.guess i (forget i x) (broadcast P x t) = F x

@[simp]
lemma length_broadcast (P : Protocol G d) (x : Fin d → G) : ∀ t, (broadcast P x t).length = t
  | 0 => rfl
  | t + 1 => by simpa [broadcast_succ] using length_broadcast _ _ _

noncomputable
def complexity (P : Protocol G d) (F : (Fin d → G) → Bool) : ENat :=
  ⨅ (t : ℕ) (_ : IsValid P F t), t

@[simp] lemma le_complexity : t ≤ Protocol.complexity P F ↔ ∀ r : ℕ, P.IsValid F r → t ≤ r := by
  simp [complexity]

end Protocol

noncomputable def funComplexity (F : (Fin d → G) → Bool) := ⨅ P : Protocol G d, P.complexity F

@[simp] lemma le_funComplexity : t ≤ funComplexity F ↔ ∀ P : Protocol G d, t ≤ P.complexity F := by
  simp [funComplexity]

lemma IsForbiddenPatternWithTip.broadcast_eq (hF : IsForbiddenPatternWithTip a v)
    (hB : ∀ i, P.broadcast (a i) t = B) : P.broadcast v t = B := by
  induction' t with t ih generalizing B
  · simpa using hB 0
  simp_rw [Protocol.broadcast_succ] at *
  obtain _ | ⟨b, B⟩ := B
  · cases hB 0
  simp [forall_and] at hB
  specialize ih hB.2
  subst ih
  have h₁ : forget (t : Fin d) v =  forget (t : Fin d) (a t) := hF.forget t
  have h₂ : P.broadcast v t = P.broadcast (a t) t := (hB.2 t).symm
  rw [h₁, h₂, hB.1]

end NOF
