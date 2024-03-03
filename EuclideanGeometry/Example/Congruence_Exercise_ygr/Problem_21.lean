import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_21
/-
$AC$ bisects $\angle BAD$, $CE \perp AB$ intersects line $AB$ at $E$, $CF \perp AD$ intersects line $AD$ at $F$, and $BC = CD$. $E$ lies on $AB$, $D$ lieson $AF$.

(1) Prove that $\triangle BCE \cong \triangle DCF$.
(2) Prove that $AB + AD = 2AE$.
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- construct points $A, B, C, D$
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
  BAD_nd : ¬ colinear B A D
  -- $AC$ bisects $\angle BAD$
  AC_bisec : ∠ C A B = (∠ D A C)
  E : Plane
  A_ne_E : PtNe A E
  C_ne_E : PtNe C E
  B_ne_E : PtNe B E
  -- $CE \perp AB$ intersects line $AB$ at $E$
  E_perp_foot : E = perp_foot C (LIN A B)
  -- $E$ lies on $AB$
  E_int : E LiesInt (SEG A B)
  F : Plane
  A_ne_F : PtNe A F
  C_ne_F : PtNe C F
  D_ne_F : PtNe D F
  -- $CF \perp AD$ intersects line $AD$ at $F$
  F_perp_foot : F = perp_foot C (LIN A D)
  -- $D$ lieson $AF$
  D_int : D LiesInt (SEG A F)
  -- $BC = CD$
  BC_eq_CD : (SEG B C).length = (SEG C D).length
  BCE_nd : ¬ colinear B C E
  DCF_nd : ¬ colinear D C F


attribute [instance] Setting.B_ne_C
attribute [instance] Setting.A_ne_B
attribute [instance] Setting.C_ne_D
attribute [instance] Setting.A_ne_C
attribute [instance] Setting.A_ne_D
attribute [instance] Setting.B_ne_D
attribute [instance] Setting.A_ne_E
attribute [instance] Setting.B_ne_E
attribute [instance] Setting.C_ne_E
attribute [instance] Setting.A_ne_F
attribute [instance] Setting.C_ne_F
attribute [instance] Setting.D_ne_F

-- Prove that $\triangle BCE \cong \triangle DCF$.
theorem Result1 {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (TRI_nd e.B e.C e.E e.BCE_nd) ≅ (TRI_nd e.D e.C e.F e.DCF_nd) := by
  -- We have $E, A, C$ are not collinear.
  have EAC_nd : ¬ colinear e.E e.A e.C := by sorry
  -- We have $F, A, C$ are not collinear
  have FAC_nd : ¬ colinear e.F e.A e.C := by sorry
  -- We have $\angle AEC \equiv \frac{\pi}{2} (\mod \pi)$ because $E$ is the foot of perpendicular from $C$ to $AB$.
  have AEC_is_right_angle : (ANG e.A e.E e.C).dvalue = ↑(π / 2) := by
    sorry -- apply angle_dval_eq_pi_div_two_at_perp_foot
  -- We have $\angle AFC \equiv \frac{\pi}{2} (\mod \pi)$ because $F$ is the foot of perpendicular from $C$ to $AD$.
  have AFC_is_right_angle : (ANG e.A e.F e.C).dvalue = ↑(π / 2) := by
    sorry -- apply angle_dval_eq_pi_div_two_at_perp_foot
  -- $\triangle EAC \cong_a \triangle FAC$ (by AAS)
  have EAC_acongr_FAC : (TRI_nd e.E e.A e.C EAC_nd) ≅ₐ (TRI_nd e.F e.A e.C FAC_nd) := by
    apply acongr_of_AAS_variant
    -- $\angle AEC \equiv - \angle AFC (\mod \pi)$
    · calc
      -- $\angle AEC \equiv \frac{\pi}{2} (\mod \pi)$ is proven.
      _ = ↑(π / 2) := AEC_is_right_angle
      -- $\frac{\pi}{2} \equiv - \frac{\pi}{2} (\mod \pi)$ is trivial.
      _ = - ↑(π / 2) := by norm_num
      -- $- \frac{\pi}{2} \equiv - \angle AFC (\mod \pi)$ is proven.
      _ = _ := neg_inj.mpr AFC_is_right_angle.symm
    -- $\angle CAE = - \angle CAF$
    · calc
      -- $\angle CAE = \angle CAB$ because they are the same angle.
      _ = ∠ e.C e.A e.B := by
        show ∠ e.C e.A e.E = (∠ e.C e.A e.B)
        apply (eq_ang_val_of_liesint_liesint _ _).symm
        · exact Ray.snd_pt_lies_int_mk_pt_pt e.A e.C
        · show e.E LiesInt (SEG_nd e.A e.B).toRay
          exact SegND.lies_int_toRay_of_lies_int e.E_int
      -- $\angle CAB = \angle DAC$ because $AC$ bisects $\angle BAD$.
      _ = ∠ e.D e.A e.C := e.AC_bisec
      -- $\angle DAC = \angle FAC$ because they are the same angle
      _ = ∠ e.F e.A e.C := by
        apply (eq_ang_val_of_liesint_liesint _ _).symm
        · show e.D LiesInt (SEG_nd e.A e.F).toRay
          exact SegND.lies_int_toRay_of_lies_int e.D_int
        · exact Ray.snd_pt_lies_int_mk_pt_pt e.A e.C
      -- $\angle FAC = - \angle CAF$ by symmetry
      _ = _ := neg_value_of_rev_ang
    -- $AC = AC$ is trivial.
    · rfl
  -- $\triangle EBC \cong \triangle FDC$ (by HL)
  have EBC_congr_FDC : (TRI_nd e.E e.B e.C (perm_colinear_snd_trd_fst.mt e.BCE_nd)) ≅ (TRI_nd e.F e.D e.C (perm_colinear_snd_trd_fst.mt e.DCF_nd)) := by
    apply TriangleND.congr_of_HL_variant
    -- $\angle BEC \equiv \frac{\pi}{2} (\mod \pi)$.
    · calc
      -- $\angle BEC \equiv \angle BEA - \angle CEA (\mod \pi)$ is trivial.
      _ = (ANG e.B e.E e.A).dvalue - (ANG e.C e.E e.A).dvalue := by
        rw [ang_dval_eq_ang_dval_add_ang_dval (O := e.E) (A := e.B) (C := e.A) (B := e.C)]
        simp
        rfl
      -- $\angle BEA - \angle CEA \equiv \angle CEA (\mod \pi)$ because $E$ lies on $AB$ and $\angle BEA \equiv 0 (\mod \pi)$.
      _ = - (ANG e.C e.E e.A).dvalue := by
        rw [dval_eq_zero_of_liesint $ Seg.lies_int_rev_iff_lies_int.mp e.E_int]
        norm_num
      -- $- \angle CEA \equiv \angle AEC (\mod \pi)$ by symmetry.
      _ = (ANG e.A e.E e.C).dvalue := neg_dvalue_of_rev_ang.symm
      -- $\angle AEC \equiv \frac{\pi}{2} (\mod \pi)$ is proven.
      _ = _ := AEC_is_right_angle
    -- $\angle DFC = \angle BEC$
    · calc
      -- $\angle DFC = \angle AFC$ because they are the same angle.
      _ = ∠ e.A e.F e.C := by
        show ∠ e.D e.F e.C = (∠ e.A e.F e.C)
        apply (eq_ang_val_of_liesint_liesint _ _).symm
        · show e.D LiesInt (SEG_nd e.F e.A).toRay
          exact SegND.lies_int_toRay_of_lies_int (Seg.lies_int_rev_iff_lies_int.mpr e.D_int)
        · exact (Ray.snd_pt_lies_int_mk_pt_pt e.F e.C)
      -- $\angle AFC = - \angle AEC$ because they are the corresponding angle of $\triangle EAC$ and $\triangle FAC$.
      _ = - ∠ e.A e.E e.C := by
        have : ∠ e.A e.E e.C = - ∠ e.A e.F e.C := EAC_acongr_FAC.angle₁
        simp [this]
      -- $- \angle AEC = \angle BEC$ because $E$ is the foot of perpendicular from $C$ to $AB$.
      _ = _ := by
        simp [angle_eq_neg_angle_at_perp_foot e.E_perp_foot e.E_int]
        rfl
    -- $BC = DC$
    · calc
      -- $BC = CD$ is given in the condition.
      _ = (SEG e.C e.D).length := e.BC_eq_CD
      -- $CD = DC$ by symmetry.
      _ = _ := length_of_rev_eq_length'
    -- $CE = CF$ because they are the corresponding edges of the congruent triangles $\triangle EAC$ and $\triangle FAC$.
    · exact EAC_acongr_FAC.edge₂
  -- $\triangle BCE \cong \triangle DCF$ because $\triangle EBC \cong \triangle FDC$.
  exact EBC_congr_FDC.perm_congr
-- Prove that $AB + AD = 2AE$.
theorem Result2 {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (SEG e.A e.B).length + (SEG e.A e.D).length = 2 * (SEG e.A e.E).length := by
  -- $\triangle BCE \cong \triangle DCF$ by the result of the first question.
  have BCE_congr_DCF : (TRI_nd e.B e.C e.E e.BCE_nd) ≅ (TRI_nd e.D e.C e.F e.DCF_nd) := Result1
  -- $AF = AD + DF$ because $D$ lies on $AF$.
  have AF_eq_AD_add_DF : (SEG e.A e.F).length = (SEG e.A e.D).length + (SEG e.D e.F).length := length_eq_length_add_length e.D_int
  -- $AB = AE + EB$ because $E$ lies on $AB$.
  have AB_eq_AE_add_EB : (SEG e.A e.B).length = (SEG e.A e.E).length + (SEG e.E e.B).length := length_eq_length_add_length e.E_int
  -- $EB = DF$ because $\triangle BCE \cong \triangle DCF$
  have EB_eq_DF : (SEG e.E e.B).length = (SEG e.D e.F).length := by
    calc
      -- $EB = FD$ because they are the corresponding edges of the congruent triangles $\triangle BCE$ and $\triangle DCF$.
      _ = (SEG e.F e.D).length := BCE_congr_DCF.edge₂
      -- $FD = DF$ by symmetry.
      _ = _ := length_of_rev_eq_length'

  -- $\triangle EAC = \triangle FAC$ is obtained during the proof of the first question, here we prove it again.

  -- We have $E, A, C$ are not collinear.
  have EAC_nd : ¬ colinear e.E e.A e.C := by sorry
  -- We have $F, A, C$ are not collinear
  have FAC_nd : ¬ colinear e.F e.A e.C := by sorry
  -- We have $\angle AEC \equiv \frac{\pi}{2} (\mod \pi)$ because $E$ is the foot of perpendicular from $C$ to $AB$.
  have AEC_is_right_angle : (ANG e.A e.E e.C).dvalue = ↑(π / 2) := by
    sorry -- apply angle_dval_eq_pi_div_two_at_perp_foot
  -- We have $\angle AFC \equiv \frac{\pi}{2} (\mod \pi)$ because $F$ is the foot of perpendicular from $C$ to $AD$.
  have AFC_is_right_angle : (ANG e.A e.F e.C).dvalue = ↑(π / 2) := by
    sorry -- apply angle_dval_eq_pi_div_two_at_perp_foot
  -- $\triangle EAC \cong_a \triangle FAC$ (by AAS)
  have EAC_acongr_FAC : (TRI_nd e.E e.A e.C EAC_nd) ≅ₐ (TRI_nd e.F e.A e.C FAC_nd) := by
    apply acongr_of_AAS_variant
    -- $\angle AEC \equiv - \angle AFC (\mod \pi)$
    · calc
      -- $\angle AEC \equiv \frac{\pi}{2} (\mod \pi)$ is proven.
      _ = ↑(π / 2) := AEC_is_right_angle
      -- $\frac{\pi}{2} \equiv - \frac{\pi}{2} (\mod \pi)$ is trivial.
      _ = - ↑(π / 2) := by norm_num
      -- $- \frac{\pi}{2} \equiv - \angle AFC (\mod \pi)$ is proven.
      _ = _ := neg_inj.mpr AFC_is_right_angle.symm
    -- $\angle CAE = - \angle CAF$
    · calc
      -- $\angle CAE = \angle CAB$ because they are the same angle.
      _ = ∠ e.C e.A e.B := by
        show ∠ e.C e.A e.E = (∠ e.C e.A e.B)
        apply (eq_ang_val_of_liesint_liesint _ _).symm
        · exact Ray.snd_pt_lies_int_mk_pt_pt e.A e.C
        · show e.E LiesInt (SEG_nd e.A e.B).toRay
          exact SegND.lies_int_toRay_of_lies_int e.E_int
      -- $\angle CAB = \angle DAC$ because $AC$ bisects $\angle BAD$.
      _ = ∠ e.D e.A e.C := e.AC_bisec
      -- $\angle DAC = \angle FAC$ because they are the same angle
      _ = ∠ e.F e.A e.C := by
        apply (eq_ang_val_of_liesint_liesint _ _).symm
        · show e.D LiesInt (SEG_nd e.A e.F).toRay
          exact SegND.lies_int_toRay_of_lies_int e.D_int
        · exact Ray.snd_pt_lies_int_mk_pt_pt e.A e.C
      -- $\angle FAC = - \angle CAF$ by symmetry
      _ = _ := neg_value_of_rev_ang
    -- $AC = AC$ is trivial.
    · rfl

  -- From EAC_nd to EAC_acongr_FAC is duplicative (proven in Result1)

  -- $AE = AF$
  have AE_eq_AF : (SEG e.A e.E).length = (SEG e.A e.F).length := by
    calc
      -- $AE = EA$ by symmetry
      _ = (SEG e.E e.A).length := length_of_rev_eq_length'
      -- $EA = FA$ because of the congruence
      _ = (SEG e.F e.A).length := EAC_acongr_FAC.edge₃
      -- $FA = AF$ by symmetry
      _ = _ := length_of_rev_eq_length'
  -- Plugging all equations above into the expression and simplifying finishes the proof.
  rw [AB_eq_AE_add_EB, EB_eq_DF, AE_eq_AF, AF_eq_AD_add_DF]
  ring

end Problem_21
end Congruence_Exercise_ygr
