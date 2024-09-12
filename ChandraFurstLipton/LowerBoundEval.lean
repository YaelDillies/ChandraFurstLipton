import ChandraFurstLipton.NOFModel
import ChandraFurstLipton.MultidimCorners
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Algebra.Group.Defs

namespace NOF
variable {ι G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ} [NeZero d]
  {P : Protocol G d} {t : ℕ} {B : List Bool} {a : Fin d → Fin d → G} [Fintype ι]

def eval (x : ι → G) : Bool :=
  ∑ i, x i == 0

@[simp] lemma eval_eq_true {x : ι → G} : eval x = true ↔ ∑ i, x i = 0 := by simp [eval]

variable [DecidableEq ι]

lemma trivial_of_isForbiddenPattern_of_isValid_eval (ha : IsForbiddenPattern a)
    (hP : P.IsValid eval t) (hE : ∀ i, eval (a i) = true) (hB : ∀ i, P.broadcast (a i) t = B) :
    ∀ i j, a i = a j := by
  obtain ⟨v, ha⟩ := ha
  have : P.broadcast v t = B := ha.broadcast_eq hB
  have h i : eval (a i) = eval v :=
    calc
      _ = P.guess i (forget i (a i)) (P.broadcast (a i) t) := by rw [hP]
      _ = P.guess i (forget i v) (P.broadcast v t) := by rw [hB, ha.broadcast_eq hB, ha.forget]
      _ = eval v := by rw [hP]
  suffices h : ∀ i, a i = v by simp [h]
  intro i
  ext j
  obtain hij | rfl := ne_or_eq i j
  · exact ha hij
  simp [hE] at h
  rw [← sub_eq_zero]
  calc
    a i i - v i = ∑ j, (a i j - v j) := by
      rw [Fintype.sum_eq_single]; simpa [eq_comm, sub_eq_zero] using @ha i
    _ = ∑ j, a i j - ∑ j, v j := by rw [Finset.sum_sub_distrib]
    _ = 0 := by simpa [h] using hE i

def getBits (B : List Bool) (i : ℕ) (d : ℕ) : List Bool := Id.run do
  let mut L := []
  for j in [0:B.length] do
    L := L ++ [B.getI ((i - 1) % d + j)]
  pure L

variable [Fintype G]

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

end NOF
