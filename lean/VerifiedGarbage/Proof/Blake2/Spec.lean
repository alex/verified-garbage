import VerifiedGarbage.Spec.Blake2

/-!
# Facts about the BLAKE2 specification

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2

variable {w : Nat} (P : Params w)

/-- The four words `G` computes from `v[a], v[b], v[c], v[d]` and the message
words `x, y`, in the order of the RFC's steps. -/
def mix (va vb vc vd x y : BitVec w) : BitVec w × BitVec w × BitVec w × BitVec w :=
  let a := va + vb + x
  let d := (vd ^^^ a).rotateRight P.R1
  let c := vc + d
  let b := (vb ^^^ c).rotateRight P.R2
  let a := a + b + y
  let d := (d ^^^ a).rotateRight P.R3
  let c := c + d
  let b := (b ^^^ c).rotateRight P.R4
  (a, b, c, d)

theorem set_get (v : Work w) (a : Fin 16) (x : BitVec w) (k : Nat) (hk : k < 16) :
    (v.set a x)[k] = if a.1 = k then x else v[k] := by
  simp [Vector.getElem_set]

theorem set_get_fin (v : Work w) (a b : Fin 16) (x : BitVec w) :
    (v.set a x)[b] = if a.1 = b.1 then x else v[b] := by
  simp [Vector.getElem_set]

/-- Word `k` after `G` on four distinct words. -/
theorem G_get (v : Work w) {a b c d : Fin 16} (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1)
    (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1) (x y : BitVec w)
    (k : Nat) (hk : k < 16) :
    (G P v a b c d x y)[k] =
      if b.1 = k then (mix P v[a] v[b] v[c] v[d] x y).2.1
      else if c.1 = k then (mix P v[a] v[b] v[c] v[d] x y).2.2.1
      else if d.1 = k then (mix P v[a] v[b] v[c] v[d] x y).2.2.2
      else if a.1 = k then (mix P v[a] v[b] v[c] v[d] x y).1 else v[k] := by
  simp only [G, set_get, set_get_fin, hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac,
    Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd, ite_true, ite_false]
  by_cases eb : b.1 = k
  · subst eb; simp only [ite_true, hab, hbc.symm, hbd.symm, ite_false, mix]
  by_cases ec : c.1 = k
  · subst ec; simp only [ite_true, eb, hac, hcd.symm, ite_false, mix]
  by_cases ed : d.1 = k
  · subst ed; simp only [ite_true, eb, ec, had, ite_false, mix]
  by_cases ea : a.1 = k
  · subst ea; simp only [ite_true, eb, ec, ed, ite_false, mix]
  simp only [eb, ec, ed, ea, ite_false]

/-- `compressBlocks` on `n + 1` blocks: `n` blocks, then the last. -/
theorem compressBlocks_succ (h : HashValue w) (m : Mem) (p : Addr) (n t : Nat) (f : Bool) :
    compressBlocks P h m p (n + 1) t f =
      F P (compressBlocks P h m p n t f) (blockAt w m (p + BitVec.ofNat 64 (blockBytes w * n)))
        (t + n * blockBytes w) f := by
  simp only [compressBlocks, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem compressBlocks_zero (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 0 t f = h := rfl

/-! ## Words of a block in memory -/

/-- A little-endian read is `leBytes` of the bytes. -/
theorem read_eq_leBytes (m : Mem) (a : Addr) (n : Nat) :
    m.read a n = leBytes n (fun i => m (a + BitVec.ofNat 64 i)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    show (m.read (a + 1) n ++ m a : BitVec (8 * n + 8)) = (leBytes n _ ++ _ : BitVec (8 * n + 8))
    rw [ih]
    have e : (fun i => m (a + 1 + BitVec.ofNat 64 i)) = fun i => m (a + BitVec.ofNat 64 (i + 1)) := by
      funext i; congr 1
      rw [BitVec.add_assoc, BitVec.add_comm 1, ← BitVec.ofNat_add_ofNat]; rfl
    rw [e]
    simp

/-- Word `j` of the block at `p` is the little-endian word at `p + (w/8)·j`. -/
theorem blockAt_word (m : Mem) (p : Addr) (j : Nat) (hj : j < 16) :
    blockAt w m p ⟨j, hj⟩ = m.readW (p + BitVec.ofNat 64 (w / 8 * j)) w := by
  simp only [blockAt, parseBlock, leWord, Mem.readW, read_eq_leBytes]
  congr 2
  funext i
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

end VG.Proof.Blake2
