import Mathlib.Data.ZMod.Defs

#align_import mathlib.data.zmod.defs

instance : Unique (ZMod 1) :=
  Fin.unique
