
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

/--
The rank of any observation in a family indexed by `Fin n`
is at most `n`.
-/
theorem rank_le {n : ℕ} (r : Fin n → ℝ) (i : Fin n) :
    rank r i ≤ n := by
  classical

  have hsub :
      Finset.univ.filter (fun j => r j < r i) ⊆
        (Finset.univ : Finset (Fin n)) := by
    intro j hj
    simp

  have hnot :
      ¬ (Finset.univ : Finset (Fin n)) ⊆
        Finset.univ.filter (fun j => r j < r i) := by
    intro hrev
    have hi_univ : i ∈ (Finset.univ : Finset (Fin n)) := by
      simp
    have hi_filter := hrev hi_univ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi_filter
    exact (lt_irrefl (r i)) hi_filter

  have hproper :
      Finset.univ.filter (fun j => r j < r i) ⊂
        (Finset.univ : Finset (Fin n)) := by
    exact Finset.ssubset_def.mpr ⟨hsub, hnot⟩

  have hcard :
      (Finset.univ.filter (fun j => r j < r i)).card < n := by
    simpa using Finset.card_lt_card hproper

  unfold rank
  omega

/--
The zero-based rank of an observation, regarded as an element of `Fin n`.

Thus `rankIndex r i = rank r i - 1`.
-/
noncomputable def rankIndex {n : ℕ} (r : Fin n → ℝ) (i : Fin n) : Fin n :=
  ⟨rank r i - 1, by
    have hpos : 0 < rank r i := rank_pos r i
    have hle : rank r i ≤ n := rank_le r i
    omega⟩

@[simp]
theorem rankIndex_val {n : ℕ} (r : Fin n → ℝ) (i : Fin n) :
    (rankIndex r i).val = rank r i - 1 := by
  rfl

/--
The ordinary rank is one plus the zero-based rank.
-/
theorem rank_eq_rankIndex_add_one {n : ℕ} (r : Fin n → ℝ) (i : Fin n) :
    rank r i = (rankIndex r i).val + 1 := by
  rw [rankIndex_val]
  have hpos : 0 < rank r i := rank_pos r i
  omega

/--
If there are no ties, the zero-based rank map is injective.
-/
theorem rankIndex_injective_of_no_ties {n : ℕ} (r : Fin n → ℝ)
    (hNoTies : NoTies r) :
    Function.Injective (rankIndex r) := by
  intro i j hij

  apply rank_injective_of_no_ties r hNoTies

  have hval :
      (rankIndex r i).val = (rankIndex r j).val :=
    congrArg (fun x : Fin n => x.val) hij

  rw [rankIndex_val, rankIndex_val] at hval

  have hi : 0 < rank r i := rank_pos r i
  have hj : 0 < rank r j := rank_pos r j

  omega

 /--
If there are no ties, the zero-based rank map is a bijection
of `Fin n`.
-/
theorem rankIndex_bijective_of_no_ties {n : ℕ} (r : Fin n → ℝ)
    (hNoTies : NoTies r) :
    Function.Bijective (rankIndex r) := by
  exact
    (Nat.bijective_iff_injective_and_card (rankIndex r)).2
      ⟨rankIndex_injective_of_no_ties r hNoTies, rfl⟩

/--
If there are no ties, every zero-based rank occurs.
-/
theorem rankIndex_surjective_of_no_ties {n : ℕ} (r : Fin n → ℝ)
    (hNoTies : NoTies r) :
    Function.Surjective (rankIndex r) := by
  exact (rankIndex_bijective_of_no_ties r hNoTies).2

/--
If there are no ties, every rank from `1` to `n`
is attained by exactly one observation.
-/
theorem exists_unique_rank {n : ℕ} (r : Fin n → ℝ)
    (hNoTies : NoTies r) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃! i : Fin n, rank r i = k := by
  let q : Fin n := ⟨k - 1, by omega⟩

  obtain ⟨i, hi⟩ :=
    rankIndex_surjective_of_no_ties r hNoTies q

  have hirank : rank r i = k := by
    have hval : (rankIndex r i).val = k - 1 := by
      have h :=
        congrArg (fun x : Fin n => x.val) hi
      simpa [q] using h

    rw [rank_eq_rankIndex_add_one r i, hval]
    omega

  refine ⟨i, hirank, ?_⟩

  intro j hj

  apply rank_injective_of_no_ties r hNoTies

  exact hj.trans hirank.symm

end SplitConformalLean
