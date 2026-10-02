import VerifiedGarbage.Proof.Argon2.X86_64.Initialize

/-! A single matrix or scratch block word write as a vector update. -/

namespace VG.Proof.Argon2.X86_64

open VG VG.Spec.Argon2

theorem blockAt_write (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    blockAt (m.writeW (off p (8 * i.val)) v) p = (blockAt m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases eq : i.val = j
  · subst j
    simp only [ite_true]
    change (m.writeW (off p (8 * i.val)) v).readW (off p (8 * i.val)) 64 = v
    exact Mem.readW_writeW_self64 _ _ _
  · simp only [eq, ite_false]
    change (m.writeW (off p (8 * i.val)) v).readW (off p (8 * j)) 64 =
      m.readW (off p (8 * j)) 64
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem blockAt_write_nat (m : Mem) (p : Addr) (i : Nat) (hi : i < 128) (v : Word) :
    blockAt (m.writeW (off p (8 * i)) v) p = (blockAt m p).set i v hi :=
  blockAt_write m p ⟨i, hi⟩ v

end VG.Proof.Argon2.X86_64
