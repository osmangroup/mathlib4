import Mathlib

-- TODO We should add `to_additive` to `PresentedGroup` so that
-- we obtain `PresentedAddGroup` and can avoid `Additive` below.
/-!-/
noncomputable section

section MoreGeneral

-- @[to_additive]  -- (to_additive gives an error for now; to be investigated.)
structure AddGroup.FinitePresentation {G α : Type*}
    [Finite α] [AddGroup G] where
  π : FreeAddGroup α →+ G
  rels : Set (FreeAddGroup α)
  surj : Function.Surjective π
  rels_finite : rels.Finite
  π_ker : π.ker = AddSubgroup.normalClosure rels

variable {n m : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
  (l : m → FreeAddGroup n)

-- Null hypothesis: use this instead of `Group.FinitePresentation` above
-- Fewer ways to spell the same thing means less API to write + maintain
#check PresentedAddGroup (Set.range l : Set (FreeAddGroup n))

def relatorMatrix : Matrix n m ℤ :=
  .of fun i j ↦ FreeAddGroup.lift (fun k ↦ (Pi.single k 1 : n → ℤ)) (l j) i

-- test cases
def x : FreeAddGroup (Fin 2) := FreeAddGroup.of 0
def y : FreeAddGroup (Fin 2) := FreeAddGroup.of 1
def testRelations : Fin 2 → FreeAddGroup (Fin 2)
  | 0 => 3 • x + (-2 : ℤ) • y
  | 1 => x + y - x - y
#eval relatorMatrix testRelations
-- Expected Output: !![3, 0; -2, 0]

open QuotientGroup

def key' :
    AddAbelianization (PresentedAddGroup (Set.range l : Set (FreeAddGroup n))) ≃+
      (n → ℤ) ⧸ (relatorMatrix l).toLin'.range := by
  let F := FreeAddGroup n
  let R : Set F := Set.range l
  let S := LinearMap.range (relatorMatrix l).toLin'

  -- The abelianization map sending each generator of `F` to its corresponding unit vector
  let ab : F →+ (n → ℤ) := FreeAddGroup.lift fun i ↦ Pi.single i 1

  -- column j of `relatorMatrix l` is ab (l j)
  have h_col (j : m) : (relatorMatrix l).toLin' (Pi.single j 1) = ab (l j) := by
    ext i
    simp only [relatorMatrix, Matrix.toLin'_apply, Matrix.mulVec_single, MulOpposite.op_one,
      Pi.smul_apply, Matrix.col_apply, Matrix.of_apply, one_smul, ab]

  -- map from `F` to `ℤ^n ⧸ S` that descends to the isomorphism
  let freeToCoker : F →+ (n → ℤ) ⧸ S :=
    FreeAddGroup.lift fun i ↦ Submodule.Quotient.mk (Pi.single i 1)

  -- Decompose `freeToCoker` into `S.mkQ ∘ ab`
  have h_fac (x : F) : freeToCoker x = Submodule.Quotient.mk (ab x) := by
    have : freeToCoker = S.mkQ.toAddMonoidHom.comp ab := by
      ext i
      simp only [FreeAddGroup.lift_apply_of, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe,
        Function.comp_apply, Submodule.mkQ_apply, freeToCoker, ab]
    rw [this]
    rfl

  -- Relators map to `0` under `freeToCoker`
  have h_rels (r : F) (hr : r ∈ R) : freeToCoker r = 0 := by
    rcases hr with ⟨j, rfl⟩
    rw [h_fac, Submodule.Quotient.mk_eq_zero, ← h_col]
    exact LinearMap.mem_range_self _ _

  -- The isomorphism form `F` to `ℤ^n ⧸ S`
  let presentationToCoker : AddAbelianization (PresentedAddGroup R) →+ (n → ℤ) ⧸ S :=
    AddAbelianization.lift (PresentedAddGroup.toAddGroup h_rels)

  let φ : (n → ℤ) →ₗ[ℤ] AddAbelianization (PresentedAddGroup R) :=
    Fintype.linearCombination ℤ fun i ↦ AddAbelianization.of (PresentedAddGroup.of i)

  -- φ ∘ ab = of ∘ mk
  have h_φab (x : F) :
      φ (ab x) = AddAbelianization.of (PresentedAddGroup.mk R x) := by
    have : φ.toAddMonoidHom.comp ab =
        AddAbelianization.of.comp (PresentedAddGroup.mk R) := by
      ext i
      simp [φ, ab, Fintype.linearCombination_apply_single]; rfl
    exact DFunLike.congr_fun this x

  have h_range : S ≤ LinearMap.ker φ := by
    rw [LinearMap.range_le_ker_iff]
    ext j
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearMap.zero_apply]
    rw [h_col, h_φab]
    -- relator is zero in the presented group
    have : PresentedAddGroup.mk R (l j) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_normalClosure ⟨j, rfl⟩)
    simp [this]

  let CokertoPresentationLin : (n → ℤ) ⧸ S →ₗ[ℤ] AddAbelianization (PresentedAddGroup R) :=
    S.liftQ φ h_range

  exact AddMonoidHom.toAddEquiv presentationToCoker CokertoPresentationLin.toAddMonoidHom
    (by -- back ∘ forth = id on the abelianized presentation
      apply AddAbelianization.hom_ext
      apply PresentedAddGroup.ext
      intro i
      simp [presentationToCoker, CokertoPresentationLin, φ, freeToCoker,
        Fintype.linearCombination_apply_single])
    (by -- forth ∘ back = id on the cokernel
      ext i   -- quotient ext, then pi ext, then ℤ ext: reduces to mk (single i 1)
      simp [presentationToCoker, CokertoPresentationLin, φ]
      sorry)

end MoreGeneral

section ToAdditiveExamples


#check Group
#check AddGroup

example {G : Type*} [Group G] (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ := sorry
example {G : Type*} [AddGroup G] (x y : G) : -(x + y) = -y + -x := sorry

example {G : Type*} [AddGroup G] : G ≃+ ℤ := sorry
example {G : Type*} [Group G] : Additive G ≃+ ℤ := sorry

variable {G : Type*} [Group G]

#synth Mul G
#synth Add (Additive G)

#check FreeAddGroup

end ToAdditiveExamples

variable {m n : Type*} [Fintype n] (v : m → n → ℤ)

def rel (i : m) : FreeGroup n :=
  ((Finset.univ : Finset n).toList.map fun j ↦ FreeGroup.of j ^ v i j).prod

def key :
    Additive (Abelianization (PresentedGroup <| Set.range <| rel v)) ≃+
      (n → ℤ) ⧸ (Submodule.span ℤ (Set.range v)) :=
  sorry -- Claude can fill this in ~25 lines.

-- The Abelianization of the group with presentation `⟨a, b | a⁴b⁶, a⁶b⁸⟩` has order 4
-- (in fact it is `(ℤ / 2ℤ) × (ℤ / 2ℤ)`)
example :
    letI A : Matrix _ _ ℤ := !![4, 6; 6, 8]
    Nat.card (Abelianization (PresentedGroup <| Set.range <| rel A)) = 4 := by
  sorry -- TODO prove in one line using new tactic.

-- The group with presentation `⟨a, b | a³ = b⁵ = (ab)²⟩` is perfect
-- (in fact it is the binary icosahedral group of order 120).
example :
    letI A : Matrix _ _ ℤ := !![1, -2; -2, 3]
    Group.IsPerfect (PresentedGroup <| Set.range <| rel A) := by
  sorry -- TODO prove in one line using new tactic.
