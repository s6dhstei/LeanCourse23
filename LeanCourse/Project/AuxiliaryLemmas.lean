import LeanCourse.Common
import Mathlib.AlgebraicTopology.Quasicategory


open CategoryTheory Simplicial
open SSet
open SimplexCategory
open Simplicial
open Opposite


noncomputable section
set_option maxHeartbeats 0

lemma temp02 {n} : @OfNat.ofNat (Fin (n + 1)) 0 Fin.instOfNatFin ≤ 2 := by exact Fin.zero_le 2
lemma temp03 {n} : @OfNat.ofNat (Fin (n + 1)) 0 Fin.instOfNatFin ≤ 3 := by exact Fin.zero_le 3
lemma temp12 {n} : @OfNat.ofNat (Fin (n + 1)) 1 Fin.instOfNatFin ≤ 2 := by
  norm_num
  sorry
--  calc 1 = 0 + 1 := sorry
--    _ ≤ 1 + 1 := sorry
--    _ = 2 := sorry
lemma temp13 {n} : @OfNat.ofNat (Fin (n + 1)) 1 Fin.instOfNatFin ≤ 3 := sorry
lemma temp23 {n} : @OfNat.ofNat (Fin (n + 1)) 2 Fin.instOfNatFin ≤ 3 := sorry

lemma neq01 {n} : @OfNat.ofNat (Fin (n + 1)) 0 Fin.instOfNatFin ≠ 1 := sorry
lemma neq12 {n} : @OfNat.ofNat (Fin (n + 1)) 1 Fin.instOfNatFin ≠ 2 := sorry
lemma neq13 {n} : @OfNat.ofNat (Fin (n + 1)) 1 Fin.instOfNatFin ≠ 3 := sorry

-- Note : these should not be so hard, but none of the tactics I know are working

lemma eq_if_op_eq {n m : SimplexCategory} (a b : SimplexCategory.Hom n m) : a = b → op a = op b := by {
  exact fun a_1 ↦ congrArg op a_1
}

lemma id_2_S {S : SSet} : S.map (op (SimplexCategory.Hom.id [2])) = 𝟙 (S _[2]) := by
  calc S.map (op (Hom.id [2])) = S.map (op (𝟙 ([2] : SimplexCategory))) := rfl
    _ = S.map (𝟙 ((op [2]) : SimplexCategoryᵒᵖ)) := rfl
    _ = 𝟙 (S.obj (op [2] : SimplexCategoryᵒᵖ)) := by exact CategoryTheory.Functor.map_id S (op [2])
    _ = 𝟙 (S _[2]) := rfl




lemma standard_simplex_naturality {S : SSet} {n : ℕ} ⦃X Y : SimplexCategoryᵒᵖ⦄ (f : X ⟶ Y)  (a : Δ[n] ⟶ S) (x : Δ[n].obj X) : S.map f (a.app X x) = a.app Y (Δ[n].map f x) := by exact
  (FunctorToTypes.naturality Δ[n] S a f x).symm

-- the following are sometimes more precisely what I want than `simp[δ]` or `simp[σ]`

lemma delta_is {S : SSet} {n} (i : Fin (n + 2)) : (SimplicialObject.δ S i : S _[n + 1] ⟶ S _[n]) = S.map (SimplexCategory.δ i).op := rfl
lemma sigma_is {S : SSet} {n} (i : Fin (n + 2)) : (SimplicialObject.σ S i : S _[n + 1] ⟶ S _[n + 1 + 1]) = S.map (SimplexCategory.σ i).op := rfl

lemma composition_gg_is_comp {S : SSet} {n m k : SimplexCategoryᵒᵖ } (a : n ⟶ m) (b : m ⟶ k): S.map a ≫ S.map b = S.map b ∘ S.map a := by exact rfl
lemma composition_functoriality {S : SSet} {n m k : SimplexCategoryᵒᵖ } (a : n ⟶ m) (b : m ⟶ k): S.map a ≫ S.map b = S.map (a ≫ b) := by exact (Functor.map_comp S a b).symm
lemma composition_functoriality_applied {S : SSet} {n m k : SimplexCategoryᵒᵖ } (a : n ⟶ m) (b : m ⟶ k) (f : S _[len n.unop]) : (S.map a ≫ S.map b) f = S.map (a ≫ b) f := by rw[composition_functoriality a b]
lemma composition_applied {S : SSet} {m n : ℕ} (d1 : S _[m] ⟶ S _[n]) (s1 : S _[n] ⟶ S _[m]) (f : S _[n]) : d1 (s1 f) = (d1 ∘ s1) f := rfl
lemma composition_op {n m k : SimplexCategory} (a : n ⟶ m) (b : m ⟶ k) : (a ≫ b).op = b.op ≫ a.op := by exact rfl


-- some helpful standardSimplex calculations to use for rewriting:

lemma d0_123_is_23 : SimplicialObject.δ Δ[3] 0 (standardSimplex.triangle 1 2 3 (temp12) (temp23)) = standardSimplex.edge 3 2 3 (temp23) := rfl
lemma d1_123_is_13 : SimplicialObject.δ Δ[3] 1 (standardSimplex.triangle 1 2 3 (temp12) (temp23)) = standardSimplex.edge 3 1 3 (temp13) := by {
  rw[delta_is]
  simp[standardSimplex.triangle, standardSimplex.edge]
  sorry
}
lemma d2_123_is_12 : SimplicialObject.δ Δ[3] 2 (standardSimplex.triangle 1 2 3 (temp12) (temp23)) = standardSimplex.edge 3 1 2 (temp12) := by sorry
lemma d0_023_is_23 : SimplicialObject.δ Δ[3] 0 (standardSimplex.triangle 0 2 3 (temp02) (temp23)) = standardSimplex.edge 3 2 3 (temp23) := rfl
lemma d1_023_is_03 : SimplicialObject.δ Δ[3] 1 (standardSimplex.triangle 0 2 3 (temp02) (temp23)) = standardSimplex.edge 3 0 3 (temp03) := by sorry
lemma d2_023_is_02 : SimplicialObject.δ Δ[3] 2 (standardSimplex.triangle 0 2 3 (temp02) (temp23)) = standardSimplex.edge 3 0 2 (temp02) := by sorry

-- Note: Why is `rfl` enough for some and the others seem to be so hard to prove?


lemma hornincl_23 : (standardSimplex.edge 3 2 3 (temp23)) = (hornInclusion _ _).app (op [1]) (horn.edge 3 1 2 3 temp23 Finset.card_le_three) := by exact d0_123_is_23
lemma hornincl_03 : (standardSimplex.edge 3 0 3 (temp03)) = (hornInclusion _ _).app (op [1]) (horn.edge 3 1 0 3 temp03 Finset.card_le_three) := by exact rfl
lemma hornincl_02 : (standardSimplex.edge 3 0 2 (temp02)) = (hornInclusion _ _).app (op [1]) (horn.edge 3 1 0 2 temp02 Finset.card_le_three) := by exact rfl

lemma hornedge23_is_d0_hornface_0 : horn.edge 3 1 2 3 (temp23) (Finset.card_le_three) = SimplicialObject.δ Λ[3,1] 0 (horn.face 1 0 neq01) := by {
  let temp1 := (horn.edge 3 1 2 3 (temp23) (Finset.card_le_three)).val
  let temp2 := (SimplicialObject.δ Λ[3, 1] 0 (horn.face 1 0 (neq01))).val
  have temp3 : temp1 = temp2 := sorry
  sorry
}
lemma hornedge03_is_d1_hornface_2 : horn.edge 3 1 0 3 (temp03) (Finset.card_le_three) = SimplicialObject.δ Λ[3,1] 1 (horn.face 1 2 neq12.symm) := by {
  sorry
}
lemma hornedge02_is_d1_hornface_3 : horn.edge 3 1 0 2 (temp02) (Finset.card_le_three) = SimplicialObject.δ Λ[3,1] 1 (horn.face 1 3 neq13.symm) := by {
  sorry
}

-- Note: the problem here is that the definition of horn.edge is complicated





/-
Note about the sorry's in the other files:
- naturality in the definition of `hom_by_faces_1th_3horn`, `hom_by_faces_2th_3horn` and `hom_by_faces` is missing, because it is hard.
- in the `hom_by_faces_13_works_fine_i` lemmas, the `ji` for `i = 0, 2, 3` are missing.
-/
