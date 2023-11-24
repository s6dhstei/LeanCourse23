import LeanCourse.Common
set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.

* You can use any lemmas or tactics from mathlib.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ x in range (n + 1), x : ℚ) ^ 2 := by {
      induction n
      case zero => simp
      case succ k ih =>
      rw[sum_range_succ, ih]
      symm
      rw[sum_range_succ, pow_two, add_mul_self_eq]
      rw[←pow_two]
      have sum_id (m : ℕ) : (∑ i in range (m + 1), (i : ℚ)) = m * (m + 1) / 2 := by {
        symm
        norm_num
        symm
        induction m
        case zero => simp
        case succ k ih =>
          rw [sum_range_succ]
          norm_cast
          rw [add_mul, ih]
          push_cast
          ring
        }
      norm_cast at sum_id
      rw[sum_id]
      push_cast
      ring

    }

example (a b : ℝ) : (a + b) * (a + b) * (a + b) = a * a * a + 3 * a* a * b + 3 * a * b * b + b* b * b := by sorry
example (a b c : ℝ) : (a + b = a + c) → (b = c) := by exact (add_right_inj a).1

open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min
  constructor
  · rw[Pairwise]
    intro n m hnm
    unfold Disjoint
    simp
    rw [@onFun_apply]
    intro x hxn hxm
    rw [@subset_empty_iff]
    ext y
    constructor
    · intro hy
      have z : y ∈ C n := hxn hy
      rw[hC n] at hxn
      sorry
    · exact fun a => a.elim
  · ext x
    constructor
    · have g : ∀ (i : ι), C i ⊆ A i := by {
        intro i
        rw[hC i]
        apply diff_subset}
      apply iUnion_mono g
    · intro hx
      obtain ⟨j, hj⟩ := h {i : ι | x ∈ A i} (mem_iUnion.mp hx)
      rw[mem_iUnion]
      use j
      rw[hC]
      simp
      simp at hj
      simp[hj]
      intro x_1 hx1 h2
      have c := hj.2 x_1 h2
      apply not_le.mpr hx1 c
}





/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers.

Note: any field mentioning `div`, `npow` or `zpow` are fields that you don't have to give when
defining a group. These are operations defined in terms of the group structure. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h

lemma exercise4_3 : Group PosReal := sorry

/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  rw[Nat.Prime]
  symm
  rw[←iff_not_comm]
  constructor
  · intro h
    rw[not_or, not_or]
    constructor
    · exact Nat.Prime.ne_zero h
    · constructor
      · exact Nat.Prime.ne_one h
      · push_neg
        intro a b ha hb hn
        obtain g1|g2 := h.2 a b hn
        · exact lt_le_antisymm (one_lt_succ_succ 0) (Eq.trans_ge (Nat.isUnit_iff.mp g1) ha)
        · exact lt_le_antisymm (one_lt_succ_succ 0) (Eq.trans_ge (Nat.isUnit_iff.mp g2) hb)
  · intro h
    rw[not_or, not_or] at h
    constructor
    · rw[Nat.isUnit_iff]
      exact (h.2).1
    · intro a b hn
      have g := (h.2).2
      push_neg at g
      specialize g a b
      by_contra hab
      push_neg at hab
      rw[Nat.isUnit_iff, Nat.isUnit_iff] at hab
      have f : a * b ≠ 0 := by {
        rw[hn] at h
        exact h.1}
      rw[mul_ne_zero_iff] at f
      have e : 1 ≤ a ∧ 1 ≤ b := by sorry
      have d : 2 ≤ a ∧ 2 ≤ b := by sorry
      exact g d.1 d.2 hn
}

lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · sorry
  · sorry
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
  have h2 : 2 ^ 2 ≤ 2 ^ a := by sorry
  have h3 : 1 ≤ 2 ^ a := by sorry
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    sorry
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by sorry
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  sorry


/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/
lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
      rw[←not_and_or]
      rw[IsSquare]
      intro ⟨h₁, h₂⟩
      obtain ⟨c, hc⟩ := h₁
      have e1 : b = c * c - a ^ 2 := by apply?
      have e2 : c ^ 2 - a ^ 2 = (c + a) * (c - a) := by apply?
      have g : c - a ≥ 1 := by sorry
      have f : 2 * b + 1 > a := by {
        calc 2 * b + 1
        = 2 * (c + a) * (c - a) + 1 := by apply?
      _ ≥ 2 * (c + a) + 1 := by {apply?}
      _ > 2 * (c + a) := by _?
      _ = 2 * c + 2 * a := by _?
      _ ≥ 2 * a := by _?
      _ ≥ a := by _?
      }

    }
example  (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by exact not_and_or
