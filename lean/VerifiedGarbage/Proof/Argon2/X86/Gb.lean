import VerifiedGarbage.Proof.Argon2.X86.Mix
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Argon2 on x86 (32-bit): GB on the permuted block

The permuted block in `scratch[1024, 2048)` as a vector of words
(`working`), and `gbAt_ok`: one GB updates it as `Proof.Argon2.mixWords`, and
writes nothing else.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Impl.Argon2.X86 (wOff gb gbAt)
open VG.Proof.Sha512.X86 (Acc rd64 write64 rd64_write64_self rd64_write64_ne)

/-- The permuted block, at `B + 1024`. -/
def working (m : Mem) (B : BitVec 32) : Block := Vector.ofFn fun i => rd64 m B (wOff i.val)

theorem working_get (m : Mem) (B : BitVec 32) (i : Fin 128) :
    (working m B)[i] = rd64 m B (wOff i.val) := by
  simp only [working, Fin.getElem_fin, Vector.getElem_ofFn]

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

theorem working_write (m : Mem) (i : Fin 128) (v : Word) :
    working (write64 m B (wOff i.val) v) B = (working m B).set i v := by
  apply Vector.ext
  intro j hj
  simp only [working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true]
    exact rd64_write64_self m v (by simp only [wOff]; omega)
  · simp only [h, ite_false]
    exact rd64_write64_ne m v (by simp only [wOff]; omega) (by simp only [wOff]; omega)
      (by simp only [wOff]; omega)

/-- The permuted block's region. -/
abbrev permR (B : BitVec 32) : Region := ⟨addr B 1024, 1024⟩

theorem addr_off {d : Nat} (hd : d < 4096) : addr B d = B.setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by omega)

/-- A write to a word of the permuted block stays in its region. -/
theorem frame_write (m m' : Mem) (hf : Frame [permR B] m m') (i : Fin 128) (v : Word) :
    Frame [permR B] m (write64 m' B (wOff i.val) v) := by
  have c : ∀ e, e + 4 ≤ 1024 → (permR B).Contains (addr B (1024 + e)) (32 / 8) := fun e he => by
    show (⟨addr B 1024, 1024⟩ : Region).Contains _ _
    rw [addr_off hfit (by omega), addr_off hfit (by omega)]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  have m₁ := List.mem_singleton_self (permR B)
  have := i.isLt
  exact (hf.writeW m₁ _ (c (8 * i.val) (by omega))).writeW m₁ _
    (by rw [show wOff i.val + 4 = 1024 + (8 * i.val + 4) by simp only [wOff]; omega]
        exact c _ (by omega))

end

/-- `v[a] := addMul(v[a], v[b])` -/
def am {n : Nat} (a b : Fin n) (v : Vector Word n) : Vector Word n := v.set a (addMul v[a] v[b])

/-- `v[d] := (v[d] ^ v[a]) >>> r` -/
def xr {n : Nat} (d a : Fin n) (r : Nat) (v : Vector Word n) : Vector Word n :=
  v.set d ((v[d] ^^^ v[a]).rotateRight r)

/-- GB on any vector of words: `Spec.Argon2.GB`'s updates. -/
def gbV {n : Nat} (v : Vector Word n) (a b c d : Fin n) : Vector Word n :=
  xr b c 63 (am c d (xr d a 16 (am a b (xr b c 24 (am c d (xr d a 32 (am a b v)))))))

set_option linter.unusedSimpArgs false in
theorem gbV_eq {n : Nat} (v : Vector Word n) {a b c d : Fin n} (hab : a.val ≠ b.val)
    (hac : a.val ≠ c.val) (had : a.val ≠ d.val) (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val)
    (hcd : c.val ≠ d.val) : gbV v a b c d = Proof.Argon2.mixWords v a b c d := by
  apply Vector.ext
  intro j hj
  simp only [gbV, am, xr, Proof.Argon2.mixWords, Proof.Argon2.mix, Fin.getElem_fin, Vector.getElem_set,
    hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc,
    Ne.symm hbd, Ne.symm hcd, ite_true, ite_false]
  have nb := Ne.symm hab; have nc := Ne.symm hac; have nd := Ne.symm had
  have nc' := Ne.symm hbc; have nd' := Ne.symm hbd; have nd'' := Ne.symm hcd
  by_cases eb : b.val = j
  · subst j
    simp only [hab, hac, had, hbc, hbd, hcd, nb, nc, nd, nc', nd', nd'', ite_true, ite_false]
  by_cases ec : c.val = j
  · subst j
    simp only [hab, hac, had, hbc, hbd, hcd, nb, nc, nd, nc', nd', nd'', eb, ite_true, ite_false]
  by_cases ed : d.val = j
  · subst j
    simp only [hab, hac, had, hbc, hbd, hcd, nb, nc, nd, nc', nd', nd'', eb, ec, ite_true, ite_false]
  by_cases ea : a.val = j
  · subst j
    simp only [hab, hac, had, hbc, hbd, hcd, nb, nc, nd, nc', nd', nd'', eb, ec, ed, ite_true, ite_false]
  simp only [eb, ec, ed, ea, ite_false]

/-! ## GB -/

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)

/-- What a step of GB leaves: the registers but GB's, and the memory at `B`
with the permuted block `v` in place of the old one, `Frame [permR B]`. -/
structure Step (B : BitVec 32) (s : State) (v : Block) (t : State) : Prop where
  keep : Keep s t
  working : working t.mem B = v
  frame : Frame [permR B] s.mem t.mem

theorem Step.trans {s t u : State} {v w : Block} (h : Step B s v t) (h' : Step B t w u) :
    Step B s w u := ⟨h.keep.trans h'.keep, h'.working, h.frame.trans h'.frame⟩

include hfit

theorem step_write {s t : State} (k : Keep s t) {i : Fin 128} {x : Word}
    (hm : t.mem = write64 s.mem B (wOff i.val) x) :
    Step B s ((working s.mem B).set i x) t :=
  ⟨k, by rw [hm, working_write hfit], by rw [hm]; exact frame_write hfit _ _ (Frame.refl _ _) i x⟩

theorem Step.am {s t t' : State} {v : Block} (S : Step B s v t) (k : Keep t t') {a b : Fin 128}
    (m : t'.mem = write64 t.mem B (wOff a.val)
      (Spec.Argon2.addMul (rd64 t.mem B (wOff a.val)) (rd64 t.mem B (wOff b.val)))) :
    Step B s (am a b v) t' := by
  have st := step_write hfit k m
  rw [← working_get, ← working_get, S.working] at st
  exact S.trans st

theorem Step.xr {s t t' : State} {v : Block} (S : Step B s v t) (k : Keep t t') {d a : Fin 128} {r : Nat}
    (m : t'.mem = write64 t.mem B (wOff d.val)
      ((rd64 t.mem B (wOff d.val) ^^^ rd64 t.mem B (wOff a.val)).rotateRight r)) :
    Step B s (xr d a r v) t' := by
  have st := step_write hfit k m
  rw [← working_get, ← working_get, S.working] at st
  exact S.trans st

theorem gbAt_ok {s : State} (h0 : s.gpr .esi = B) (hA : Acc s.wr B 4096) (a b c d : Fin 128) :
    WP isa (gbAt a.val b.val c.val d.val) s (Step B s (gbV (working s.mem B) a b c d)) := by
  have o : ∀ i : Fin 128, wOff i.val + 8 ≤ 4096 := fun i => by
    have := i.isLt; simp only [wOff]; omega
  have S₀ : Step B s (working s.mem B) s := ⟨.refl s, rfl, Frame.refl _ _⟩
  have e : ∀ {t : State} {v : Block}, Step B s v t → t.gpr .esi = B := fun S => S.keep.esi.trans h0
  have A : ∀ {t : State} {v : Block}, Step B s v t → Acc t.wr B 4096 := fun S => S.keep.wr ▸ hA
  unfold gbAt gb
  refine WP.block_append ((addMul_ok (o a) (o b) (e S₀) (A S₀)).mono fun s₁ ⟨k₁, m₁⟩ => ?_)
  have S₁ := S₀.am hfit k₁ m₁
  refine WP.block_append ((xorRot32_ok (o d) (o a) (e S₁) (A S₁)).mono fun s₂ ⟨k₂, m₂⟩ => ?_)
  have S₂ := S₁.xr hfit k₂ m₂
  refine WP.block_append ((addMul_ok (o c) (o d) (e S₂) (A S₂)).mono fun s₃ ⟨k₃, m₃⟩ => ?_)
  have S₃ := S₂.am hfit k₃ m₃
  refine WP.block_append ((xorRot_ok (by decide) (by decide) (o b) (o c) (e S₃) (A S₃)).mono
    fun s₄ ⟨k₄, m₄⟩ => ?_)
  have S₄ := S₃.xr hfit k₄ m₄
  refine WP.block_append ((addMul_ok (o a) (o b) (e S₄) (A S₄)).mono fun s₅ ⟨k₅, m₅⟩ => ?_)
  have S₅ := S₄.am hfit k₅ m₅
  refine WP.block_append ((xorRot_ok (by decide) (by decide) (o d) (o a) (e S₅) (A S₅)).mono
    fun s₆ ⟨k₆, m₆⟩ => ?_)
  have S₆ := S₅.xr hfit k₆ m₆
  refine WP.block_append ((addMul_ok (o c) (o d) (e S₆) (A S₆)).mono fun s₇ ⟨k₇, m₇⟩ => ?_)
  have S₇ := S₆.am hfit k₇ m₇
  exact (xorRot63_ok (o b) (o c) (e S₇) (A S₇)).mono fun s₈ ⟨k₈, m₈⟩ => S₇.xr hfit k₈ m₈

end

end VG.Proof.Argon2.X86
