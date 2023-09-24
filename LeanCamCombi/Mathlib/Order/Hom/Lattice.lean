import Mathlib.Order.Hom.Lattice

namespace LatticeHom
variable (α β : Type*) [Lattice α] [Lattice β]

/-- Natural projection homomorphism from `α × β` to `α`. -/
def fst : LatticeHom (α × β) α where
  toFun := Prod.fst
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/-- Natural projection homomorphism from `α × β` to `β`. -/
def snd : LatticeHom (α × β) β where
  toFun := Prod.snd
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

@[simp, norm_cast] lemma coe_fst : ⇑(fst α β) = Prod.fst := rfl
@[simp, norm_cast] lemma coe_snd : ⇑(snd α β) = Prod.snd := rfl
lemma fst_apply (x : α × β) : fst α β x = x.fst := rfl
lemma snd_apply (x : α × β) : snd α β x = x.snd := rfl

end LatticeHom
