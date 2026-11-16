import Mathlib

/-!
# Chinukwe.Domains

Index type for the five-domain application. The core results are stated for an arbitrary
finite index type `ι`; naming and interpreting the five domains belongs to the applications
paper, so no names are assigned here.
-/

namespace Chinukwe

abbrev Domain : Type := Fin 5

example : Nonempty Domain := ⟨0⟩

end Chinukwe
