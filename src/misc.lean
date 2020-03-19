import data.set.intervals.basic
import data.real.basic
import topology.instances.real
import tactic.suggest

open set 

--  Propriétés de base sur l'ensemble [0,1]

abbreviation I := Icc (0 : ℝ) (1 : ℝ)


instance : has_zero I := ⟨⟨ (0 : ℝ), and.intro (le_refl 0) (zero_le_one)⟩⟩
instance : has_one I := ⟨⟨1, and.intro (zero_le_one) (le_refl 1)⟩⟩
noncomputable def real_to_I (x : ℝ) : I := if h : x≥0 ∧ x≤1 then ⟨x, h⟩ else (0 : I)
instance : has_coe I ℝ := ⟨subtype.val⟩
instance : has_le I := ⟨λ r s, (r:ℝ) ≤ s⟩
instance : inhabited I := ⟨0⟩ 

--instance : has_div I := ⟨λ x y, real_to_I (x/y) ⟩
noncomputable instance : has_sub I := ⟨λ a b, real_to_I (a-b)⟩ 

lemma oneminus (t : I) : 1-t.val ≥ 0 ∧ 1-t.val ≤ 1 :=
begin
  simp,
  split,
  exact t.property.right,
  ring,
  apply add_le_iff_nonpos_left.mpr,
  apply neg_le.mp,
  simp,
  exact t.property.1,
end

lemma oneminuscont : continuous (λ t:I, (⟨1-t, oneminus t⟩:I)) := sorry

lemma twotimes (t:I) : t.val ≤ 0.5 -> 2*t.val ≥ 0 ∧ 2*t.val ≤ 1  := 
begin
    intro h,
    simp,
    sorry,
end

lemma twotimesminus1 (t:I) : t.val > 0.5 -> 2*t.val-1 ≥ 0 ∧ 2*t.val-1 ≤ 1  := 
begin
    intro h,
    simp,
    sorry,
end

lemma em_I (t : I) :¬t.val ≤ 1 / 2 -> t.val > 1 / 2 := sorry


@[simp] lemma coe_of_0 : (0 : I).val = (0 : ℝ ) := rfl
@[simp] lemma one_minus_one_coe : (1:ℝ) - (1 : I).val = (0 : ℝ ) := sub_self 1