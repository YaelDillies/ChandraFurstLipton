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
    rw [IsForbiddenPatternWithTip] at hv
    have (i : ι) : v i = a i i + ∑ j, v j :=
    calc
       v i = ∑ j, a i j + v i := by simp [zero_add, hS]
       _ = a i i + ∑ j ∈ Finset.univ \ {i}, a i j + v i := by simp
       _ = a i i + ∑ j ∈ Finset.univ \ {i}, v j + v i := by
        have (j : ι) : j ∈ Finset.univ \ {i} → a i j - v j = 0 := by
          simp [hv, ← ne_eq, eq_comm]
          intro hne
          rw [sub_eq_zero]
          exact hv hne
        have (j : ι) : ∑ j ∈ Finset.univ \ {i}, a i j = ∑ j ∈ Finset.univ \ {i}, v j := by
          rw [← sub_eq_zero, ← Finset.sum_sub_distrib, Finset.sum_eq_zero]
          exact this
        rw [this]
        exact i
       _ = a i i + ∑ j, v j := sorry
    refine ⟨?_, ?_⟩
    · intro hn _
      sorry
    rw [IsForbiddenPatternWithTip]
    intros hn hn' hp
    exfalso
    sorry

end NOF
