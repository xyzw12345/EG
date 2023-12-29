import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section property_nd

variable {A B C D : P}
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type _} [EuclideanPlane P] (prg_nd : Parallelogram_nd P)

-- or is this theorem supposed to belong to section property_para?
theorem nd_eq_int_angle_value_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (ANG A B D ((nd₁₂_of_is_prg_nd_variant h).symm) (nd₂₄_of_is_prg_nd_variant h)).value = (ANG C D B ((nd₃₄_of_is_prg_nd_variant h).symm) ((nd₂₄_of_is_prg_nd_variant h).symm)).value := by sorry
-- ShenZiJun

end property_nd

section criteria' -- different from section criteria, not needing ABCD is convex (I don't know if it should be merged into criteria)

-- the existing theorem is_prg_of_diag_inx_eq_mid_eq_mid_variant should be renamed as is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant or some similar things
theorem is_prg_of_diag_inx_eq_mid_eq_mid (A B C D : P) (h : (SEG A B).midpoint = (SEG C D).midpoint) : (QDR A B C D) IsParallelogram := by sorry
-- ShenZiJun

theorem vec_eq_of_eq_dir_and_eq_length {A B C D : P} (h1 : B ≠ A) (h2 : D ≠ C) (h3 : (SEG_nd A B h1).toDir = (SEG_nd C D h2).toDir) (h4 : (SEG A B).length = (SEG C D).length) : VEC A B = VEC C D := by sorry

theorem is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant_1 {A B C D : P} (h : (QDR A B C D).IsConvex) (h' : (SEG A C).midpoint = (SEG B D).midpoint) : ((QDR_cvx A B C D sorry sorry).toQuadrilateral).IsParallelogram_nd := by sorry

theorem is_prg_of_is_prg_nd (A B C D : P) (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D).IsParallelogram := by sorry

theorem todir_eq_of_is_prg_nd (A B C D : P) (h : (QDR A B C D).IsParallelogram_nd) (h1 : B ≠ A) (h2 : C ≠ D): (SEG_nd A B h1).toDir = (SEG_nd D C h2).toDir := by sorry

theorem todir_eq_of_is_prg_nd_variant (A B C D : P) (h : (QDR A B C D).IsParallelogram_nd) (h1 : D ≠ A) (h2 : C ≠ B): (SEG_nd A D h1).toDir = (SEG_nd B C h2).toDir := by sorry
