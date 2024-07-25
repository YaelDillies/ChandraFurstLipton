import ChandraFurstLipton.NOFModel

namespace NOF
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {d : ℕ} [NeZero d]

def eval (x : Fin d → G) : Bool :=
  ∑ i, x i == 0

end NOF
