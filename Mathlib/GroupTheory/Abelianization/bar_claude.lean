import Mathlib

/-!-/
noncomputable section

open Matrix

namespace FreeGroup

variable {n : Type*} [DecidableEq n]

/-- The vector of exponent sums of the generators in an element of a free group, i.e., its image
in the abelianization `n → ℤ`. -/
def exponentSums : FreeGroup n →* Multiplicative (n → ℤ) :=
  lift fun i ↦ .ofAdd (Pi.single i 1)

@[simp]
lemma exponentSums_of (i : n) : exponentSums (of i) = .ofAdd (Pi.single i 1) :=
  lift_apply_of

end FreeGroup

variable {n : Type*} [DecidableEq n] [Fintype n]
  (l : List (FreeGroup n))

/-- The matrix whose `j`-th column is the vector of exponent sums of the `j`-th relator. -/
def relatorMatrix : Matrix n (Fin l.length) ℤ :=
  .of fun i j ↦ (l.get j).exponentSums.toAdd i

omit [Fintype n] in
lemma relatorMatrix_col (j : Fin l.length) :
    (relatorMatrix l).col j = (l.get j).exponentSums.toAdd :=
  rfl

namespace Key

omit [Fintype n] in
lemma lift_eq (N : Submodule ℤ (n → ℤ)) (w : FreeGroup n) :
    FreeGroup.lift (fun i ↦ Multiplicative.ofAdd (N.mkQ (Pi.single i 1))) w =
      .ofAdd (N.mkQ w.exponentSums.toAdd) := by
  induction w with
  | one => simp
  | of i => simp
  | inv_of i h => simp_all
  | mul x y hx hy => simp_all

lemma linearCombination_exponentSums (rels : Set (FreeGroup n)) (w : FreeGroup n) :
    Fintype.linearCombination ℤ (fun i ↦ Additive.ofMul (Abelianization.of
      (PresentedGroup.of (rels := rels) i))) w.exponentSums.toAdd =
      .ofMul (.of (PresentedGroup.mk _ w)) := by
  induction w with
  | one => simp
  | of i => simp [Fintype.linearCombination_apply_single]; rfl
  | inv_of i h => simp_all
  | mul x y hx hy => simp_all

/-- The map from the abelianization of the presented group to the cokernel of the relator
matrix. -/
def toCoker :
    Additive (Abelianization (PresentedGroup (l.toFinset : Set (FreeGroup n)))) →ₗ[ℤ]
      (n → ℤ) ⧸ (relatorMatrix l).toLin'.range :=
  AddMonoidHom.toIntLinearMap <| MonoidHom.toAdditiveLeft <| Abelianization.lift <|
    PresentedGroup.toGroup (f := fun i ↦ .ofAdd (Submodule.mkQ _ (Pi.single i 1))) <| by
      intro r hr
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hr)
      rw [lift_eq, ← relatorMatrix_col, ← mulVec_single_one, ← Matrix.toLin'_apply,
        Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)]
      rfl

omit [Fintype n] in
lemma toCoker_mk (w : FreeGroup n) :
    toCoker l (.ofMul (.of (PresentedGroup.mk _ w))) =
      Submodule.Quotient.mk w.exponentSums.toAdd :=
  congr_arg Multiplicative.toAdd (lift_eq _ w)

omit [Fintype n] in
@[simp]
lemma toCoker_of (i : n) :
    toCoker l (.ofMul (.of (PresentedGroup.of i))) = Submodule.Quotient.mk (Pi.single i 1) :=
  (toCoker_mk l (.of i)).trans <| by simp

/-- The map from the cokernel of the relator matrix to the abelianization of the presented
group. -/
def ofCoker :
    (n → ℤ) ⧸ (relatorMatrix l).toLin'.range →ₗ[ℤ]
      Additive (Abelianization (PresentedGroup (l.toFinset : Set (FreeGroup n)))) :=
  Submodule.liftQ _ (Fintype.linearCombination ℤ fun i ↦ .ofMul (.of (.of i))) <| by
    rw [LinearMap.range_le_ker_iff]
    ext j
    simp [relatorMatrix_col, linearCombination_exponentSums, PresentedGroup.one_of_mem]

lemma ofCoker_mk (v : n → ℤ) :
    ofCoker l (Submodule.Quotient.mk v) =
      Fintype.linearCombination ℤ (fun i ↦ .ofMul (.of (.of i))) v :=
  rfl

end Key

def key' :
    Additive (Abelianization (PresentedGroup (l.toFinset : Set (FreeGroup n)))) ≃+
      (n → ℤ) ⧸ (relatorMatrix l).toLin'.range :=
  LinearEquiv.toAddEquiv <| .ofLinearMap (Key.toCoker l) (Key.ofCoker l)
    (by ext i; simp [Key.ofCoker_mk, Fintype.linearCombination_apply_single])
    (by
      refine LinearMap.ext fun x ↦ ?_
      obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
      obtain ⟨x, rfl⟩ : ∃ y, Abelianization.of y = x := QuotientGroup.mk_surjective x
      obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ x
      simp [Key.toCoker_mk, Key.ofCoker_mk, Key.linearCombination_exponentSums])
