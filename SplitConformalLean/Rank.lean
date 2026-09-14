
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

/--
Strictly smaller observations have strictly smaller ranks.
-/
theorem rank_lt_of_lt {n : ℕ} (r : Fin n → ℝ) {i j : Fin n}
    (hij : r i < r j) :
    rank r i < rank r j := by
  classical

  have hsub :
      Finset.univ.filter (fun k => r k < r i) ⊆
        Finset.univ.filter (fun k => r k < r j) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_trans hk hij

  have hnot :
      ¬ Finset.univ.filter (fun k => r k < r j) ⊆
        Finset.univ.filter (fun k => r k < r i) := by
    intro hrev
    have hi_big :
        i ∈ Finset.univ.filter (fun k => r k < r j) := by
      simp [hij]
    have hi_small := hrev hi_big
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi_small
    exact (lt_irrefl (r i)) hi_small

  have hproper :
      Finset.univ.filter (fun k => r k < r i) ⊂
        Finset.univ.filter (fun k => r k < r j) := by
    exact Finset.ssubset_def.mpr ⟨hsub, hnot⟩

  unfold rank
  exact Nat.add_lt_add_left (Finset.card_lt_card hproper) 1

/--
If a finite family has no ties, then distinct indices have distinct ranks.
Equivalently, the rank map is injective.
-/
theorem rank_injective_of_no_ties {n : ℕ} (r : Fin n → ℝ)
    (hNoTies : NoTies r) :
    Function.Injective (rank r) := by
  intro i j hRank

  rcases lt_trichotomy (r i) (r j) with hlt | heq | hgt

  · have hRankLt : rank r i < rank r j :=
      rank_lt_of_lt r hlt
    exact (Nat.ne_of_lt hRankLt hRank).elim

  · exact hNoTies heq

  · have hRankLt : rank r j < rank r i :=
      rank_lt_of_lt r hgt
    exact (Nat.ne_of_lt hRankLt hRank.symm).elim

end SplitConformalLean
