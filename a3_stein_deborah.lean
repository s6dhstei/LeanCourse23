import LeanCourse.Common
import LeanCourse.MIL.C03_Logic.solutions.Solutions_S06_Sequences_and_Convergence
set_option linter.unusedVariables false
open Nat Real Function Set

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 3 and 6
  Read chapter 4, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 3.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


/- Prove the law of excluded middle without using `by_cases` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  by_contra h
  push_neg at h
  apply h.1 h.2
}






/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_2 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
      intro ε h₀
      obtain ⟨m, hm⟩ := hs ε h₀
      obtain ⟨N, hN⟩ := hr m
      use N
      intro n hn
      have hrn : r n ≥ m  := hN n hn
      rw [@comp_apply]
      apply hm (r n)
      exact hrn
    }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma exercise3_3 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
      rw[SequentialLimit]
      intro ε h₀
      obtain ⟨N₁, h₁⟩ := hs₁ ε h₀
      obtain ⟨N₃, h₃⟩ := hs₃ ε h₀
      use max N₁ N₃
      intro n hn
      rw [@abs_sub_lt_iff]
      have hnN₃ : n ≥ N₃ := le_of_max_le_right hn
      have hnN₁ : n ≥ N₁ := le_of_max_le_left hn
      constructor
      · calc s₂ n - a
           ≤ s₃ n - a := by simp[hs₂s₃]
         _ ≤ |s₃ n - a| := le_abs_self (s₃ n - a)
         _ < ε := by exact h₃ n hnN₃
      · calc a - s₂ n
           ≤ a - s₁ n := sub_le_sub_left (hs₁s₂ n) a
         _ ≤ |a - s₁ n| := le_abs_self (a - s₁ n)
         _ = |s₁ n - a| := abs_sub_comm a (s₁ n)
         _ < ε := by exact h₁ n hnN₁
    }


/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)

lemma exercise3_4 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by {
  rw[SequentialLimit]
  intro ε h₀
  use ⌈1/ε⌉₊
  intro n hn
  rw[sub_zero]
  rw[abs_div]
  refine lt_of_one_div_lt_one_div h₀ ?h.h
  simp
  have g : 0 < (n : ℝ) + 1 := by exact cast_add_one_pos n
  rw[abs_of_pos g]
  have h : (n : ℝ) ≥ (⌈1/ε⌉₊ : ℝ) := by exact cast_le.mpr hn
  have j : (0 : ℝ) < (1 : ℝ) := by exact Real.zero_lt_one
  calc ε⁻¹
     = 1/ε := inv_eq_one_div ε
   _ ≤ ⌈1/ε⌉₊ := le_ceil (1 / ε)
   _ < n + 1  := by {
    refine lt_add_of_le_of_pos h ?ha
    exact Real.zero_lt_one
    }
}


/- Use the previous exercises to prove that `n ↦ sin n / (n + 1)` converges to 0.
  I will prove for you that `n ↦ -1 / (n + 1)` also converges to `0`. -/

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel' ε ?hb; positivity

lemma use_me : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by
  have : SequentialLimit (fun n ↦ (-1) * (1 / (n+1))) (-1 * 0) :=
    convergesTo_mul_const (-1) exercise3_4
  simp at this
  simp [neg_div, this]

lemma exercise3_5 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by {
  intro ε h₀
  have hs : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := exercise3_4
  obtain ⟨N, hN⟩ := hs ε (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  simp at hN
  have h : |sin n| ≤ 1 := by exact abs_sin_le_one ↑n
  calc |sin ↑n / (↑n + 1)|
      = |sin ↑n| / |(n + 1 : ℝ)| := by rw[abs_div]
    _ ≤ 1 / |(n + 1 : ℝ)| := by {
      refine div_le_div_of_le ?hc h
      exact abs_nonneg (n + 1: ℝ)
      }
    _ < ε := sorry
}

/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_6 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by sorry

/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/


lemma exercise3_7 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by sorry

lemma exercise3_8 :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by sorry

/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses.
  Remember: you can use `simp [hyp]` to simplify using hypothesis `hyp`. -/
lemma exercise3_9 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
  have h1' : ∀ x y, f x ≠ g y
  · intro x y h
    apply h1.subset
    exact ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
  have h1'' : ∀ y x, g y ≠ f x
  · intro x y
    symm
    apply h1'
  have h2' : ∀ x, x ∈ range f ∪ range g := eq_univ_iff_forall.1 h2
  have hf' : ∀ x x', f x = f x' ↔ x = x' := fun x x' ↦ hf.eq_iff
  let L : Set α × Set β → Set γ :=
    fun (s, t) ↦ sorry
  let R : Set γ → Set α × Set β :=
    fun s ↦ sorry
  sorry
