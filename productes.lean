-- Anem a estudiar i comprovar que existeix el límit producte en la categoria de Tipus

namespace producte

-- Definim un tipus I que farà d'índex
variable (I : Type)
-- Llavors una família de tipus indexada per I és una variable
variable (𝕏 : I → Type)

-- Donat un element del producte podem considerar la projecció a la component i-èssima
def π {I : Type} {𝕏 : I → Type} (i : I) : (∀(i:I), 𝕏 i) → 𝕏 i := by
  intro 𝕗
  exact 𝕗 i

-- En la categoria de Tipus, el producte verifica la Propietat Universal
def PUniv {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), Z → 𝕏 i ) : Z → (∀(i:I), 𝕏 i) := by
  intro z
  intro i
  exact 𝕗 i z

-- Comprovem que l'aplicació està ben definida i fa que el diagrama commute
theorem TComm {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), Z → 𝕏 i ) (i : I) : (π i)∘(PUniv 𝕗) = 𝕗 i := by
  apply funext
  intro z
  exact rfl

-- Comprovem que l'aplicació PUniv és la única que satisfà les condicions anteriors per a tot i en I
theorem TUniv {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), Z → 𝕏 i ) (h : Z → (∀(i:I), 𝕏 i)) (hi : ∀(i:I) , (π i)∘h = 𝕗 i) : h = PUniv 𝕗 := by
  apply funext
  intro z
  apply funext
  intro i
  specialize hi i
  calc
    h z i = (π i ∘ h) z := by exact rfl
    _ = (𝕗 i) z := by exact congrFun hi z
    _ = PUniv 𝕗 z i := by exact rfl

-- Així, hem comprovat que el producte és un límit en la categoria de Tipus (el límit és el parell
-- format per el producte i l'aplicació π).
end producte
