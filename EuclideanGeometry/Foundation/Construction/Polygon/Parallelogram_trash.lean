import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram


noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section criteria' -- different from section criteria, not needing ABCD is convex (I don't know if it should be merged into criteria)

-- the existing theorem is_prg_of_diag_inx_eq_mid_eq_mid_variant should be renamed as is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant or some similar thing
theorem is_prg_of_diag_inx_eq_mid_eq_mid (A B C D : P) (h : (SEG A B).midpoint = (SEG C D).midpoint) : (QDR A B C D IsPRG) := by sorry
