import data.set.intervals.basic
import topology.instances.real

open set 

--  Propriétés de base sur l'ensemble [0,1]
def I := Icc (0 : ℝ) (1 : ℝ)
instance : has_zero I := ⟨⟨0, and.intro (le_refl 0) (zero_le_one)⟩⟩
instance : has_one I := ⟨⟨1, and.intro (zero_le_one) (le_refl 1)⟩⟩
instance : has_coe I ℝ := ⟨λ x,x⟩
