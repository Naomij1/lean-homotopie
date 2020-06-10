import data.set.intervals.basic
import data.real.basic
import topology.instances.real
import tactic.suggest
import tactics

open set 
open classical
--  Propriétés de base sur l'ensemble [0,1]

abbreviation I := Icc (0 : ℝ) (1 : ℝ)


instance : has_zero I := ⟨⟨ (0 : ℝ), and.intro (le_refl 0) (zero_le_one)⟩⟩
instance : has_one I := ⟨⟨1, and.intro (zero_le_one) (le_refl 1)⟩⟩
noncomputable def real_to_I (x : ℝ) : I := if h : x≥0 ∧ x≤1 then ⟨x, h⟩ else (0 : I)
instance : has_coe I ℝ := ⟨subtype.val⟩
instance : has_le I := ⟨λ r s, (r:ℝ) ≤ s⟩
noncomputable instance : has_sub I := ⟨λ a b, real_to_I (a-b)⟩ 

lemma oneminus (t : I) : 1-t.val ≥ 0 ∧ 1-t.val ≤ 1 :=
begin
  simp,
  split,
  exact t.property.2,
  ring,
  apply add_le_iff_nonpos_left.mpr,
  apply neg_le.mp,
  simp,
  exact t.property.1,
end


lemma twotimes (t:I) : t.val ≤ 0.5 -> 2*t.val ≥ 0 ∧ 2*t.val ≤ 1  := 
begin
    intro h,
    simp,
    sorry,
    --apply (le_div_iff zero_lt_two).mp,
end

lemma twotimesminus1 (t:I) : t.val > 0.5 -> 2*t.val-1 ≥ 0 ∧ 2*t.val-1 ≤ 1  := 
begin
    intro h,
    simp,
    split,
    linarith,
    have h2 : t.val ≤ 1, from t.property.2,
    linarith,
end


@[simp] lemma coe_of_0 : (0 : I).val = (0 : ℝ ) := rfl
@[simp] lemma coe_of_1 : (1 : I).val = (1 : ℝ ) := rfl
@[simp] lemma one_minus_one_coe : (1:ℝ) - (1 : I).val = (0 : ℝ ) := sub_self 1

lemma not_2_lt_0 : ¬((2:ℝ)<(0:ℝ)) := by {intro,  linarith}
lemma not_1_lt_half: ¬ ((1 : ℝ) ≤ 2⁻¹) :=  by sorry


lemma invtwo : (2:ℝ)*(1/2)=1 := by ring
lemma invtwo'  (x:ℝ) :((2:ℝ)*x)/2=x := by ring

@[simp] lemma oneisone : (⟨(1:ℝ),sorry⟩:I)=(1:I):=rfl
@[simp] lemma zeroiszero : (⟨(0:ℝ),sorry⟩:I)=(0:I):=rfl


lemma frontieronI' : frontier {a : ↥I | a.val ≤ 1 / 2} = {a : I | a.val=1/2}  := by sorry
lemma frontieronI : frontier  ({a : I × I | a.fst.val ≤ 2⁻¹} : set (I×I)) = {a : I×I | a.fst.val=1/2} := 
begin
  have  test : is_closed {a : I × I | a.fst.val ≤ 2⁻¹}, from sorry,
  have interior2 : interior {a : I × I | a.fst.val ≤ 2⁻¹} = {a : I × I | a.fst.val < 2⁻¹} , from sorry,
  simp [test, is_closed.frontier_eq, interior2],
  ext,
  split,
  intro h,
  cases h with h1 h2,
  simp [mem_def] at h1,
  simp [mem_def] at h2,
  simp *,
  linarith,

  intro h,
  simp *,
  simp [mem_def] at h,
  split,
  linarith,
  linarith,
end

lemma in_I_const_comp  (x : I×I) : 0≤(2-x.1.val)*x.2.val-1 + x.1.val ∧ (2-x.1.val)*x.2.val-1 + x.1.val≤1:= 
begin
 sorry
end

lemma in_I_comp_const  (x : I×I) : 0≤(2-x.1.val)*x.2.val ∧ (2-x.1.val)*x.2.val ≤ 1 := by sorry

lemma one_half : (1 + 1) / (4:ℝ) = 1/2 := by ring
lemma one_quarter : (1 + 0) / (4:ℝ) = 1/4 := by ring