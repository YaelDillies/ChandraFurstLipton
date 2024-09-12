import ChandraFurstLipton.NOFModel
import ChandraFurstLipton.MultidimCorners
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Algebra.Group.Defs

namespace NOF
variable {ι G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {d : ℕ} [NeZero d]
  {P : Protocol G d} {t : ℕ} {B : List Bool} {a : Fin d → Fin d → G} [Fintype ι] [DecidableEq ι]

def eval (x : ι → G) : Bool :=
  ∑ i, x i == 0

@[simp] lemma beq_eq_beq {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {a₁ a₂ : α}
  {b₁ b₂ : β} : (a₁ == a₂) = (b₁ == b₂) ↔ (a₁ = a₂ ↔ b₁ = b₂) := by rw [Bool.eq_iff_iff]; simp

@[simp] lemma eval_eq_true {x : Fin d → G} : eval x = true ↔ ∑ i, x i = 0 := by simp [eval]

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
