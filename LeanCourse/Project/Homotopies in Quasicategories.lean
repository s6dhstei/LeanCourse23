import LeanCourse.Common
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.Quasicategory
import LeanCourse.Project.HornMorphisms



open CategoryTheory Simplicial
open SSet
open SimplexCategory
open Simplicial
open Opposite

variable (S : SSet) [Quasicategory S]
variable (n : Nat)
variable (f g : S _[1])

noncomputable section
set_option maxHeartbeats 2000000


/-
# Homotopies in Quasicategories
In this file, we define the notion of left homotopy and right homotopy between two arrows in a Quasi-Category, and prove that they are equivalent.
I only managed to fully prove one implication, namely that left homotopy implies right homotopy. The converse would be very similar; part of the proof is given.
We define that `f` and `g` are *homotopic* in a Quasi-Category if they are left homotopic or (equivalently) right homotopic.

For two elements `f, g` in `S _[1]` with same startpoint `(S.δ 1) f = (S.δ 1) g` and  same endpoint  `(S.δ 0) f = (S.δ 0) g`, we say `f` and `g` are *left homotopic* if there exists `σ : S _[2]` such that `(S.δ 0) σ = f`, `(S.δ 1) σ = g` and `(S.δ 2) σ = (S.σ 0) ((S.δ 1) f)`. Figuratively, `g` is a composition of `f` and the identity on the start point.
The definition of *right homotopic* is similar, but with the identity on the end point.
-/

structure htpy {S : SSet} [Quasicategory S] (f g : S _[1]) where
  same_start : (S.δ 1) f = (S.δ 1) g
  same_end : (S.δ 0) f = (S.δ 0) g
  right_filler : ∃ σ : S _[2], S.δ 0 σ = S.σ 0 (S.δ 1 f) ∧ S.δ 1 σ = f ∧ S.δ 2 σ = g
  left_filler :  ∃ σ : S _[2], S.δ 0 σ = f ∧ S.δ 1 σ = g ∧ S.δ 2 σ = S.σ 0 (S.δ 1 f)


def left_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := by{
  exact ((S.δ 1) f = (S.δ 1) g ∧ (S.δ 0) f = (S.δ 0) g) ∧ ∃ σ : S _[2], S.δ 0 σ = f ∧ S.δ 1 σ = g ∧ S.δ 2 σ = S.σ 0 (S.δ 1 f)
}
def right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := by{
  exact ((S.δ 1) f = (S.δ 1) g ∧ (S.δ 0) f = (S.δ 0) g) ∧ ∃ σ : S _[2], S.δ 0 σ = S.σ 0 (S.δ 0 f) ∧ S.δ 1 σ = f ∧ S.δ 2 σ = g
}


-- ## left_homotopic and right_homotopic are equivalent


-- If f and g are left homotopic, then they are right homotopic.

lemma left_homotopic_implies_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : left_homotopic f g → right_homotopic f g := by{
  intro hleft
  rw[left_homotopic] at hleft
  obtain ⟨σ, hσ⟩ := hleft.2
  obtain ⟨hleft1, hleft2, hleft3⟩ := hσ
  constructor
  · exact hleft.1
  · let s : Fin 4 → (S _[2])
      | 0 => (SimplicialObject.σ S 1 f)
      | 1 => σ
      | 2 => (SimplicialObject.σ S 0 f)
      | 3 => σ
    have s0_s0 : s 0 = (SimplicialObject.σ S 1 f) := rfl
    have s2_s2 : s 2 = (SimplicialObject.σ S 0 f) := rfl
    have s3_s3 : s 3 = σ := rfl
    have compatible_s : horn1_compatible (s 0) (s 2) (s 3) := by{
      constructor
      · -- the 01-edge is (σ 0) ((δ 1) f)
        rewrite[s3_s3, s2_s2, ← delta_is, hleft3, composition_applied (SimplicialObject.σ S 0) (SimplicialObject.δ S 1)]
        rewrite[delta_is, delta_is, sigma_is]
        simp[SimplicialObject.σ]
        rewrite[composition_applied (S.map (SimplexCategory.σ 0).op) (S.map (SimplexCategory.δ 1).op), ← composition_gg_is_comp (SimplexCategory.δ 1).op (SimplexCategory.σ 0).op, composition_functoriality_applied (δ 1).op (SimplexCategory.σ 0).op]
        rewrite[composition_applied (S.map (SimplexCategory.δ 2).op) (S.map (SimplexCategory.σ 0).op), ← composition_gg_is_comp (SimplexCategory.σ 0).op (SimplexCategory.δ 2).op, composition_functoriality_applied (SimplexCategory.σ 0).op (δ 2).op]
        rewrite[← composition_op, ← composition_op]
        rewrite[← δ_comp_σ_of_gt _]
        simp
        exact Fin.coe_sub_iff_lt.mp rfl
      · constructor
        · -- the 12-edge is f
          rewrite[s3_s3, s0_s0, ← delta_is, hleft1, ← delta_is, composition_applied (SimplicialObject.δ S 2) (SimplicialObject.σ S 1), delta_is, sigma_is, ← composition_gg_is_comp (SimplexCategory.σ 1).op (SimplexCategory.δ 2).op, composition_functoriality_applied (SimplexCategory.σ 1).op (δ 2).op]
          rewrite[← composition_op]
          rewrite[δ_comp_σ_succ' _]
          rewrite[op_id, FunctorToTypes.map_id_apply S f]
          exact rfl
          exact rfl
        · -- the 13-edge is f = (δ 0) ((σ 0) f) = (δ 1) ((σ 1) f)
          rewrite[s0_s0, s2_s2, ← delta_is, composition_applied (SimplicialObject.δ S 0) (SimplicialObject.σ S 0)]
          rewrite[sigma_is]
          simp[SimplicialObject.σ]
          rewrite[composition_applied (S.map (SimplexCategory.δ 1).op) (S.map (SimplexCategory.σ 1).op), ← composition_gg_is_comp (SimplexCategory.σ 1).op (SimplexCategory.δ 1).op, composition_functoriality_applied (SimplexCategory.σ 1).op (δ 1).op]
          rewrite[delta_is, composition_applied (S.map (SimplexCategory.δ 0).op) (S.map (SimplexCategory.σ 0).op), ← composition_gg_is_comp (SimplexCategory.σ 0).op (SimplexCategory.δ 0).op, composition_functoriality_applied (SimplexCategory.σ 0).op (δ 0).op]
          rewrite[← composition_op, ← composition_op]
          rewrite[δ_comp_σ_self' _, δ_comp_σ_self' _]
          exact rfl
          exact rfl
          exact rfl
    }
    let a : Λ[3,1] ⟶ S := by {
      use fun m ↦ ((hom_by_faces_1th_3horn (s : Fin 4 → S _[2]) compatible_s).app m)
      apply (hom_by_faces_1th_3horn (s : Fin 4 → S _[2]) compatible_s).naturality}
    have temp_a0 : a.app (op [2]) (horn.face 1 0 neq01) = SimplicialObject.σ S 1 f := by {
      apply hom_by_faces_13_works_fine_0
      exact compatible_s
    }
    have temp_a2 : a.app (op [2]) (horn.face 1 2 neq12.symm) = SimplicialObject.σ S 0 f := by {
      apply hom_by_faces_13_works_fine_2
      exact compatible_s
    }
    have temp_a3 : a.app (op [2]) (horn.face 1 3 neq13.symm) = σ := by {
      apply hom_by_faces_13_works_fine_3
      exact compatible_s
    }
    obtain ⟨b, hb⟩ := Quasicategory.hornFilling Fin.one_pos (Fin.lt_last_iff_coe_castPred.mpr temp11) a
    let B := b.app (op [2]) (standardSimplex.triangle 0 2 3 (temp02) (temp23))
    use B
    constructor
    · have dS0_B_is_b_23 : SimplicialObject.δ S 0 B = b.app (op [1]) (standardSimplex.edge 3 2 3 (temp23)) := by {
        rewrite[d0_023_is_23.symm]
        simp[B]
        rewrite[delta_is, delta_is]
        exact standard_simplex_naturality (δ 0).op b (standardSimplex.triangle 0 2 3 temp02 temp23)
      }
      rewrite[dS0_B_is_b_23]
      have b_hornincl31_x_is_a_x : ∀ x, b.app (op [1]) ((hornInclusion 3 1).app (op [1]) x) = a.app (op [1]) x := by {
        intro x
        rewrite[← congrFun (congrArg NatTrans.app (id hb.symm)) (op [1])]
        exact rfl
      }
      have b_23_is_a_23 : b.app (op [1]) (standardSimplex.edge 3 2 3 (_ : OfNat.ofNat 2 ≤ 3)) = a.app (op [1]) (horn.edge 3 1 2 3 temp23 Finset.card_le_three) := by {
        rewrite[hornincl_23]
        exact b_hornincl31_x_is_a_x (horn.edge 3 1 2 3 temp23 Finset.card_le_three)
      }
      rewrite[b_23_is_a_23]
      have a_23_is_dS0_a_face0 : a.app (op [1]) (horn.edge 3 1 2 3 (temp23) (Finset.card_le_three)) = SimplicialObject.δ S 0 (a.app (op [2]) (horn.face 1 0 neq01)) := by{
        rewrite[hornedge23_is_d0_hornface_0]
        apply (FunctorToTypes.naturality Λ[3,1] S a (δ 0).op (horn.face 1 0 neq01))
      }
      rewrite[a_23_is_dS0_a_face0, temp_a0, delta_is, delta_is]
      simp[SimplicialObject.σ]
      rewrite[composition_applied (S.map (δ 0).op) (S.map (SimplexCategory.σ 1).op), composition_applied (S.map (SimplexCategory.σ 0).op) (S.map (δ 0).op)]
      rewrite[← composition_gg_is_comp _ _, ← composition_gg_is_comp _ _]
      rewrite[composition_functoriality _ _, composition_functoriality _ _]
      rewrite[← composition_op _ _, ← composition_op _ _]
      rewrite[← δ_comp_σ_of_le (Fin.zero_le (Fin.castSucc 0))]
      simp
    · constructor
      · have dS1_B_is_b_03 : SimplicialObject.δ S 1 B = b.app (op [1]) (standardSimplex.edge 3 0 3 (temp03)) := by {
          rewrite[d1_023_is_03.symm]
          simp[B]
          rewrite[delta_is, delta_is]
          exact standard_simplex_naturality (δ 1).op b (standardSimplex.triangle 0 2 3 temp02 temp23)
        }
        rewrite[dS1_B_is_b_03]
        have b_hornincl31_x_is_a_x : ∀ x, b.app (op [1]) ((hornInclusion 3 1).app (op [1]) x) = a.app (op [1]) x := by {
          intro x
          rewrite[← congrFun (congrArg NatTrans.app (id hb.symm)) (op [1])]
          exact rfl
        }
        have b_03_is_a_03 : b.app (op [1]) (standardSimplex.edge 3 0 3 (_ : OfNat.ofNat 0 ≤ 3)) = a.app (op [1]) (horn.edge 3 1 0 3 temp03 Finset.card_le_three) := by {
          rewrite[hornincl_03]
          exact b_hornincl31_x_is_a_x (horn.edge 3 1 0 3 temp03 Finset.card_le_three)
        }
        rewrite[b_03_is_a_03]
        have a_03_is_dS1_a_face2 : a.app (op [1]) (horn.edge 3 1 0 3 (temp03) (Finset.card_le_three)) = SimplicialObject.δ S 1 (a.app (op [2]) (horn.face 1 2 neq12.symm)) := by{
          rewrite[hornedge03_is_d1_hornface_2]
          apply (FunctorToTypes.naturality Λ[3,1] S a (δ 1).op (horn.face 1 2 neq12.symm))
        }
        rewrite[a_03_is_dS1_a_face2, temp_a2, delta_is]
        simp[SimplicialObject.σ]
        rewrite[composition_applied (S.map (δ 1).op) (S.map (SimplexCategory.σ 0).op)]
        rewrite[← composition_gg_is_comp _ _]
        rewrite[composition_functoriality _ _]
        rewrite[← composition_op _ _]
        rewrite[δ_comp_σ_succ' _]
        rewrite[op_id, FunctorToTypes.map_id_apply S f]
        exact rfl
        exact rfl
      · have dS2_B_is_b_02 : SimplicialObject.δ S 2 B = b.app (op [1]) (standardSimplex.edge 3 0 2 (temp02)) := by {
          rewrite[d2_023_is_02.symm]
          simp[B]
          rewrite[delta_is, delta_is]
          exact standard_simplex_naturality (δ 2).op b (standardSimplex.triangle 0 2 3 temp02 temp23)
        }
        rewrite[dS2_B_is_b_02]
        have b_hornincl31_x_is_a_x : ∀ x, b.app (op [1]) ((hornInclusion 3 1).app (op [1]) x) = a.app (op [1]) x := by {
          intro x
          rewrite[← congrFun (congrArg NatTrans.app (id hb.symm)) (op [1])]
          exact rfl
        }
        have b_02_is_a_02 : b.app (op [1]) (standardSimplex.edge 3 0 2 (_ : OfNat.ofNat 0 ≤ 2)) = a.app (op [1]) (horn.edge 3 1 0 2 temp02 Finset.card_le_three) := by {
          rewrite[hornincl_02]
          exact b_hornincl31_x_is_a_x (horn.edge 3 1 0 2 temp02 Finset.card_le_three)
        }
        rewrite[b_02_is_a_02]
        have a_02_is_dS1_a_face3 : a.app (op [1]) (horn.edge 3 1 0 2 (temp02) (Finset.card_le_three)) = SimplicialObject.δ S 1 (a.app (op [2]) (horn.face 1 3 neq13.symm)) := by{
          rewrite[hornedge02_is_d1_hornface_3]
          apply (FunctorToTypes.naturality Λ[3,1] S a (δ 1).op (horn.face 1 3 neq13.symm))
        }
        rw[a_02_is_dS1_a_face3, temp_a3, hleft2]
        }


-- The other direction: right homotopic implies left homotopic. The calculations are omitted because I don't have enough time left

lemma right_homotopic_implies_left_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : right_homotopic f g → left_homotopic f g := by{
  intro hright
  rw[right_homotopic] at hright
  obtain ⟨σ, hσ⟩ := hright.2
  obtain ⟨hright1, hright2, hright3⟩ := hσ
  constructor
  · exact hright.1
  · let s : Fin 4 → (S _[2])
      | 0 => σ
      | 1 => (SimplicialObject.σ S 1 g)
      | 2 => σ
      | 3 => (SimplicialObject.σ S 0 g)
    have compatible_s : horn2_compatible (s 0) (s 1) (s 3) := sorry
    let a : Λ[3,2] ⟶ S := by {
      use fun m ↦ ((hom_by_faces_2th_3horn (s : Fin 4 → S _[2]) compatible_s).app m)
      apply (hom_by_faces_2th_3horn (s : Fin 4 → S _[2]) compatible_s).naturality}
    obtain ⟨b, hb⟩ := Quasicategory.hornFilling (temp0lt2) (sorry) a
    let B := b.app (op [2]) (standardSimplex.triangle 0 1 3 (Fin.zero_le 1) (temp13))
    use B
    sorry
}


-- `f` and `g` are left homotopic if and only if they are right homotopic:

lemma left_homotopic_iff_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : right_homotopic f g ↔ left_homotopic f g := by {
  constructor
  · exact fun a ↦ right_homotopic_implies_left_homotopic f g a
  · exact fun a ↦ left_homotopic_implies_right_homotopic f g a
}


-- Definition of 'homotopic' in Quasicategories:

def qc_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := left_homotopic f g ∨ right_homotopic f g

#check (qc_homotopic f g)
