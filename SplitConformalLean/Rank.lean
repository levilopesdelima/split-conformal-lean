import Mathlib

namespace SplitConformalLean

/--
A finite family of real numbers has no ties if the map assigning
a value to each index is injective.
-/
def NoTies {n : ℕ} (r : Fin n → ℝ) : Prop :=
  Function.Injective r

/--
The rank of `r i` among the finite family `r : Fin n → ℝ`.

The smallest observation has rank `1`.
-/
noncomputable def rank {n : ℕ} (r : Fin n → ℝ) (i : Fin n) : ℕ :=
  1 + (Finset.univ.filter (fun j => r j < r i)).card


theorem rank_pos {n : ℕ} (r : Fin n → ℝ) (i : Fin n) :
    0 < rank r i := by
  simp [rank]

end SplitConformalLean
