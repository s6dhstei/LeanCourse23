import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Minpoly.Basic
set_option linter.unusedVariables false
noncomputable section
open Real Function BigOperators
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 17.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


section LinearMap

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
  [Module R M₁] [Module R M₂] [Module R N]

/- Define the coproduct of two linear maps that send (x, y) ↦ f x + g y. -/

def exercise5_1 (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun := by {
    intro ⟨m₁, m₂⟩
    use f m₁ + g m₂
  }
  map_add' := by {
    intro x y
    simp
    have h : f x.1 + f y.1 = f (x.1 + y.1) := by exact (LinearMap.map_add f x.1 y.1).symm
    rw[←add_assoc, ←add_assoc]
    rw[add_assoc (f x.1) (f y.1) (g x.2)]
    rw[add_comm (f y.1) (g x.2)]
    simp[add_assoc]
  }
  map_smul' := by {
    simp
  }



example (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  exercise5_1 f g (x, y) = f x + g y := rfl -- should be rfl


end LinearMap

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
  prove that the units of a ring form a group.
  Hint: I recommend that you first prove that the product of two units is again a unit,
  and that you define the inverse of a unit separately using `Exists.choose`.
  Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
  (`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

instance exercise5_2 : Group {x : R // IsAUnit x} := by {
--  refine groupOfIsUnit ?h
  sorry
}

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by {
  sorry
}

end Ring



/- The Frobenius morphism in a field of characteristic p is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. -/
#check CharP.cast_eq_zero_iff
#check Finset.sum_congr
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] in
open Nat Finset in
lemma exercise5_3 (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have h2 : p.Prime := hp.out
  have h3 : 0 < p := h2.pos
  have h4 : range p = insert 0 (Ioo 0 p)
  · ext (_|_) <;> simp [h3]
  have h5 : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by {
    intro i hi
    have j : i < p := by exact (mem_Ioo.mp hi).2
    have g : _ := ascFactorial_eq_factorial_mul_choose
    specialize g (p - i) i
    rw[Nat.sub_add_cancel (le_of_lt j)] at g
    have notpdivi : ¬ p ∣ i ! := by {
      intro f
      exact (Nat.not_le.mpr j) ((Prime.dvd_factorial h2).1 f)
    }
    have irreddiv : ∀ (a b : ℕ), p ∣ (a * b) → (p ∣ a ∨ p ∣ b) := by {
      apply fun a b a_1 ↦ (fun {p m n} pp ↦ (Nat.Prime.dvd_mul pp).mp) h2 a_1
      exact fun a b ↦ K
      exact fun a b {p} ↦ K
      exact fun a b {p m} ↦ K
      exact fun a b ↦ x
      exact fun a b ↦ x
      exact fun a b ↦ x
    }
    have g₀ : p ∣ ascFactorial (p - i) i := by {
      have g₁ : (p - i).ascFactorial (i - 1).succ = ((p - i) + (i - 1) + 1) * (p - i).ascFactorial (i - 1) := rfl
      have g₂ : ∀ (n : ℕ), succ n = n + 1 := by exact fun n ↦ rfl
      rw[g₂] at g₁
      have g₃ : ∀ (a b : ℕ), a - b + b = a := by {
        intro a b
        rw[add_comm]
--        rw[add_sub] (what's the problem here? maybe subtraction in ℕ ?)
        sorry
      }
      rw[g₃] at g₁
      rw[add_assoc] at g₁
      rw[g₃, g₃] at g₁
      rw[g₁]
      use ascFactorial (p - i) (i - 1)
    }
    have pdivprod : p ∣ i ! * Nat.choose p i := by exact
      (ModEq.dvd_iff (congrFun (congrArg HMod.hMod (id g.symm)) (ascFactorial (p - i) i)) g₀).mpr g₀
    specialize irreddiv (i !) (Nat.choose p i) pdivprod
    rw[or_iff_right] at irreddiv
    exact irreddiv
    exact notpdivi
  }
  have pchooseizero : ∀ (i : ℕ), (i ∈ Ioo 0 p) → ((Nat.choose p i) : K) = 0 := by {
    intro i hi
    have charp : ∀ (x : _),  p ∣ x → (x : K)  = 0 := by exact fun x a ↦
      (fun R [AddMonoidWithOne R] p [CharP R p] x ↦ (CharP.cast_eq_zero_iff R p x).mpr) K p x a
    apply charp
    exact h5 i hi
  }
--  have pchooseizero2 : ∀ (i : ℕ) [i ∈ Ioo 0 p], ((Nat.choose p i) : K) = 0 := by apply?
--    have pfun : fun i ↦ Nat.choose p i :=
  have sumfun : ∀ (f₁ f₂ g : ℕ → ℕ) (n : ℕ), (h : ∀ k ∈ Ioo 0 n, f₁ n = f₂ n) → ∑ k in Ioo 0 n, g (f₁ k) = ∑ k in Ioo 0 n, g (f₂ k) := by {
    intro f₁ f₂ g n h
    induction n
    case zero => simp
    case succ k ih => sorry
--      rw[sum_range_succ]
  }
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ = ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * ((Nat.choose p i) : K) := rfl
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by sorry

--      rw[pchooseizero ?_ ?_]
--      apply sumfun (fun i ↦ Nat.choose p i) (fun i ↦ 0) (fun a ↦  x ^ i * y ^ (p - i) * a)


    _ = 0 := by sorry
  sorry


/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).
-/
#check exists_ne
lemma exercise5_4 {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by {
  sorry
}
