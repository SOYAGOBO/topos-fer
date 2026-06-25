import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory
open CategoryTheory.Limits

universe v u

-- Let C be a Category acting as our Topos.
-- A Topos has all finite limits, which means it has a Terminal object (1, denoted ⊤_ C)
-- and an Initial object (0, denoted ⊥_ C).
variable {C : Type u} [Category.{v} C]
variable [HasTerminal C] [HasInitial C]

-- The Subobject Classifier (Ω) and the 'truth' morphism from 1 to Ω
variable (Ω : C) (truth : ⊤_ C ⟶ Ω)

/--
  Theorem: If the subobject classifier Ω is isomorphic to the initial object (0),
  then the topos is degenerate. Specifically, the terminal object (1) is 
  isomorphic to the initial object (0).
-/
def degenerate_of_classifier_zero (iso : Ω ≅ ⊥_ C) : ⊤_ C ≅ ⊥_ C where
  -- The forward map (1 ⟶ 0) is the composition of truth (1 ⟶ Ω) and iso.hom (Ω ⟶ 0)
  hom := truth ≫ iso.hom
  
  -- The inverse map (0 ⟶ 1) is the unique map from the initial object
  inv := initial.to (⊤_ C)
  
  -- Proof that hom ≫ inv = 𝟙 1 (Any endomorphism on the terminal object is the identity)
  hom_inv_id := Subsingleton.elim _ _
  
  -- Proof that inv ≫ hom = 𝟙 0 (Any endomorphism on the initial object is the identity)
  inv_hom_id := Subsingleton.elim _ _

section Tests

-- Let's test the implications of this degeneracy.
variable (X Y : C)

/-- 
  Test 1: If 1 ≅ 0, we can construct a canonical zero morphism between any two objects X and Y.
  This map goes: X ⟶ 1 ⟶ 0 ⟶ Y.
-/
def zero_map_of_degenerate (deg : ⊤_ C ≅ ⊥_ C) : X ⟶ Y :=
  terminal.from X ≫ deg.hom ≫ initial.to Y

/-- 
  Test 2: Prove that if Ω ≅ 0, there exists a canonical map between ANY two spaces X and Y.
-/
example (iso : Ω ≅ ⊥_ C) : X ⟶ Y :=
  zero_map_of_degenerate X Y (degenerate_of_classifier_zero Ω truth iso)

/--
  Test 3: The composition of the unique map 0 ⟶ 1 and 1 ⟶ 0 is the identity on 0.
-/
example (iso : Ω ≅ ⊥_ C) : 
  initial.to (⊤_ C) ≫ (truth ≫ iso.hom) = 𝟙 (⊥_ C) := 
  (degenerate_of_classifier_zero Ω truth iso).inv_hom_id

/--
  Test 4: The composition of 1 ⟶ 0 and 0 ⟶ 1 is the identity on 1.
-/
example (iso : Ω ≅ ⊥_ C) : 
  (truth ≫ iso.hom) ≫ initial.to (⊤_ C) = 𝟙 (⊤_ C) := 
  (degenerate_of_classifier_zero Ω truth iso).hom_inv_id

end Tests
