import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_18
/-
In quadrilateral $ABCD$, $DA \parallel BC$, $E$ lies on the diagonal $BD$, $\angle BAD = - \angle CEB$, $AD = BE$.

Prove that $\triangle ABD \cong_a \triangle ECB$.
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- construct quadrilateral $ABCD$
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  A_ne_B : PtNe A B
  A_ne_C : PtNe A C
  A_ne_D : PtNe A D
  B_ne_C : PtNe B C
  B_ne_D : PtNe B D
  C_ne_D : PtNe C D
  ABD_nd : ¬ colinear A B D
  AC_opposite : IsOnOppositeSide A C (SEG_nd D B)
  -- $DA \parallel BC$
  DA_para_BC : (SEG_nd D A) ∥ (SEG_nd B C)
  -- $E$ lies on the diagonal $BD$
  E : Plane
  E_int : E LiesInt (SEG_nd B D)
  -- We have $E, C, B$ are not collinear, so $B \neq E$ and $C \neq E$
  ECB_nd : ¬ colinear E C B := sorry
  B_ne_E : PtNe B E := sorry
  C_ne_E : PtNe C E := sorry
  -- $\angle BAD = - \angle CEB$
  BAD_eq_neg_CEB : ∠ B A D = - (∠ C E B)
  -- $AD = BE$
  AD_eq_BE : (SEG A D).length = (SEG B E).length

attribute [instance] Setting.B_ne_C
attribute [instance] Setting.A_ne_B
attribute [instance] Setting.C_ne_D
attribute [instance] Setting.A_ne_C
attribute [instance] Setting.A_ne_D
attribute [instance] Setting.B_ne_D
attribute [instance] Setting.B_ne_E
attribute [instance] Setting.C_ne_E

-- Prove that $\triangle ABD \cong_a \triangle ECB$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (TRI_nd e.A e.B e.D e.ABD_nd) ≅ₐ (TRI_nd e.E e.C e.B e.ECB_nd) := by
  have : IsAlternateIntAng (ANG e.A e.D e.B) (ANG e.C e.B e.D) := by
    constructor
    · show (RAY e.D e.A).toDir = - (RAY e.B e.C).toDir
      apply neg_toDir_of_parallel_and_opposite_side (A := e.D) (B := e.B) (C := e.A) (D := e.C)
      · exact e.B_ne_D.out.symm
      · exact e.A_ne_D.out
      · exact e.B_ne_C.out.symm
      · exact e.DA_para_BC
      · exact e.AC_opposite
    · show (DLIN e.D e.B) = (DLIN e.B e.D).reverse
      exact DirLine.pt_pt_rev_eq_rev
  have BAD_acongr_CEB : (TRI_nd e.B e.A e.D (flip_colinear_fst_snd.mt e.ABD_nd)) ≅ₐ (TRI_nd e.C e.E e.B (flip_colinear_fst_snd.mt e.ECB_nd)) := by
    apply TriangleND.acongr_of_ASA
    calc
      _ = - ∠ e.B e.A e.D := neg_value_of_rev_ang
      _ = ∠ e.C e.E e.B := by simp [e.BAD_eq_neg_CEB]
      _ = _ := neg_value_of_rev_ang
    calc
      _ = (SEG e.B e.E).length := e.AD_eq_BE
      _ = _ := length_of_rev_eq_length'
    calc
       _ = - ∠ e.A e.D e.B := neg_value_of_rev_ang
       _ = - ∠ e.C e.B e.D := by simp only [value_eq_of_isalternateintang this]
       _ = _ := by
        have : ∠ e.C e.B e.D = ∠ e.C e.B e.E := by
          apply eq_ang_val_of_liesint_liesint
          exact Ray.snd_pt_lies_int_mk_pt_pt e.B e.C
          exact SegND.lies_int_toRay_of_lies_int e.E_int
        rw [this]
        rfl
  exact BAD_acongr_CEB.perm_acongr.flip_acongr

end Problem_18
end Congruence_Exercise_ygr
