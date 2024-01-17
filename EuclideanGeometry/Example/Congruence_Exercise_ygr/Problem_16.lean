import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_16
/-
Let $D$ be a point inside $\triangle ABC$, $\angle CBD = \angle DCB$, $\angle ADB = - \angle ADC$.

Prove that $AB = AC$.
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- construct $\triangle ABC$
  A : Plane
  B : Plane
  C : Plane
  ABC_nd : ¬ colinear A B C
  -- $D$ is inside $\triangle ABC$ implies that $D$ is not collinear with any side of $\triangle ABC$
  D : Plane
  ABD_nd : ¬ colinear A B D
  ACD_nd : ¬ colinear A C D
  BCD_nd : ¬ colinear B C D
  -- and $A, B, C, D$ are pairwise distinct
  B_ne_C : PtNe B C := ⟨(ne_of_not_colinear ABC_nd).1.symm⟩
  B_ne_D : PtNe B D := ⟨(ne_of_not_colinear ABD_nd).1.symm⟩
  C_ne_D : PtNe C D := ⟨(ne_of_not_colinear ACD_nd).1.symm⟩
  A_ne_B : PtNe A B := ⟨(ne_of_not_colinear ABC_nd).2.2.symm⟩
  A_ne_C : PtNe A C := ⟨(ne_of_not_colinear ABC_nd).2.1⟩
  A_ne_D : PtNe A D := ⟨(ne_of_not_colinear ABD_nd).2.1⟩
  -- $\angle CBD = \angle DCB$
  CBD_eq_DCB : ∠ C B D = (∠ D C B)
  -- $\angle ADB = - \angle ADC$
  ADB_eq_neg_ADC : ∠ A D B = - ∠ A D C

attribute [instance] Setting.B_ne_C
attribute [instance] Setting.A_ne_B
attribute [instance] Setting.C_ne_D
attribute [instance] Setting.A_ne_C
attribute [instance] Setting.A_ne_D
attribute [instance] Setting.B_ne_D

-- Prove that $AB = AC$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (SEG e.A e.B).length = (SEG e.A e.C).length := by
  -- In $\triangle DAB$ and $\triangle DAC$,
  have DAB_acongr_DAC : (TRI_nd e.D e.A e.B (perm_colinear_snd_trd_fst.mt e.ABD_nd)) ≅ₐ (TRI_nd e.D e.A e.C (perm_colinear_snd_trd_fst.mt e.ACD_nd)) := by
    apply TriangleND.acongr_of_SAS
    -- $BD = CD$ because $\triangle DBC$ is isoceles by $\angle CBD = \angle DCB$.
    calc
      -- $BD = DB$ by symmetry
      _ = (SEG e.D e.B).length := length_of_rev_eq_length'
      -- $DB = CD$ because $\triangle DBC$ is isoceles
      _ = (SEG e.C e.D).length := ((is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := (TRI_nd e.D e.B e.C (perm_colinear_snd_trd_fst.mt e.BCD_nd)))).mpr e.CBD_eq_DCB).symm
    -- $\angle ADB = - \angle ADC$ is given in the condition
    exact e.ADB_eq_neg_ADC
    -- $DA = DA$ is obvious
    rfl
  -- thus $\triangle DAB \cong \triangle DAC$
  -- $BD = CD$ follows
  exact DAB_acongr_DAC.edge₁

end Problem_16
end Congruence_Exercise_ygr
