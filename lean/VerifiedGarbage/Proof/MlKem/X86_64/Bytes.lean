import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-KEM on x86-64: values and bytes

* shifts left by rotating a value whose top bits are zero (`rotr_toNat`),
  logical shifts right, and the byte a `store8` stores (`b8_eq`);
* `Written m m' o c v`: `m'` is `m` with the `c` bytes at `o` replaced by
  `v 0, …, v (c - 1)`, built one byte store at a time
  (`Written.first`, `Written.snoc`), and how a loop that writes its output
  `c` bytes at a time extends what it has written (`Written.extend`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-! ## Values -/

/-- Rotating right by `r` a value less than `2ʳ` shifts it left by `w - r`. -/
theorem rotr_toNat {w r : Nat} (x : BitVec w) (hr : r < w) (hx : x.toNat < 2 ^ r) :
    (x.rotateRight r).toNat = x.toNat * 2 ^ (w - r) := by
  rw [BitVec.toNat_rotateRight, Nat.mod_eq_of_lt hr, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx,
    Nat.zero_or, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  calc x.toNat * 2 ^ (w - r) < 2 ^ r * 2 ^ (w - r) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
    _ = 2 ^ w := by rw [← Nat.pow_add]; congr 1; omega

theorem shr_toNat {w : Nat} (x : BitVec w) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The byte a `store8` stores of a 32-bit value. -/
theorem b8_eq (x : BitVec 32) : BitVec.setWidth 8 (BitVec.setWidth 64 x) = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The byte a `store8` stores of a 64-bit value. -/
theorem b8_eq64 (x : BitVec 64) : BitVec.setWidth 8 x = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem toNat_setWidth64 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

theorem toNat_setWidth64_8 (x : BitVec 8) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

theorem toNat_setWidth32_8 (x : BitVec 8) : (BitVec.setWidth 32 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

theorem toNat_setWidth32_64 {x : BitVec 64} (h : x.toNat < 2 ^ 32) : (BitVec.setWidth 32 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

/-! ## Regions -/

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  exact h

theorem sub_offset' {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (hl : len' < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have e : a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off := by bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- Two ranges at offsets of the same pointer, one below the other. -/
theorem off_disj {p : Addr} {a n b m : Nat} (h : a + n ≤ b) (hb : b + m < 2 ^ 64) :
    Region.Disjoint ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p + BitVec.ofNat 64 b, m⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

/-! ## Bytes written -/

/-- `m'` is `m` with the `c` bytes at `o` replaced by `v 0, …, v (c - 1)`. -/
def Written (m m' : Mem) (o : Addr) (c : Nat) (v : Nat → Byte) : Prop :=
  ∀ x, m' x = if (x - o).toNat < c then v (x - o).toNat else m x

theorem Written.nil (m : Mem) (o : Addr) (v : Nat → Byte) : Written m m o 0 v := fun x => by
  rw [ifn (Nat.not_lt_zero _)]

theorem Written.first (m : Mem) (o : Addr) (b : Byte) : Written m (m.writeW o b) o 1 fun _ => b := by
  intro x
  rw [writeW8_apply]
  by_cases h : x = o
  · subst h; simp
  · have : (x - o).toNat ≠ 0 := fun e => h (by bv_omega)
    simp only [h, ↓reduceIte]
    rw [ifn (by omega)]

theorem Written.snoc {m m' : Mem} {o : Addr} {c : Nat} {v : Nat → Byte} (h : Written m m' o c v)
    (hc : c + 1 < 2 ^ 64) (b : Byte) :
    Written m (m'.writeW (o + BitVec.ofNat 64 c) b) o (c + 1) fun j => if j = c then b else v j := by
  intro x
  rw [writeW8_apply, h x]
  by_cases hx : x = o + BitVec.ofNat 64 c
  · subst hx
    have : (o + BitVec.ofNat 64 c - o).toNat = c := by
      rw [show o + BitVec.ofNat 64 c - o = BitVec.ofNat 64 c by bv_omega, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    simp [this]
  · have : (x - o).toNat ≠ c := fun e => hx (by bv_omega)
    simp only [hx, ↓reduceIte, this]
    by_cases hl : (x - o).toNat < c
    · rw [ifp hl, ifp (by omega)]
    · rw [ifn hl, ifn (by omega)]

/-- Writing `c` bytes within the region `R`. -/
theorem Written.frame {m m' : Mem} {o : Addr} {c : Nat} {v : Nat → Byte} (h : Written m m' o c v)
    {R : Region} (hR : R.Contains o c) : Frame [R] m m' := by
  intro x hx
  rw [h x]
  split
  · rename_i hlt
    exact absurd (hR.byte hlt) (hx R (List.mem_singleton_self _))
  · rfl

theorem Written.congr {m m' : Mem} {o : Addr} {c : Nat} {v v' : Nat → Byte} (h : Written m m' o c v)
    (hv : ∀ j < c, v j = v' j) : Written m m' o c v' := by
  intro x
  rw [h x]
  split
  · rename_i hl; exact hv _ hl
  · rfl

/-- A loop that has written the first `a` bytes of its output, `val 0, …,
val (a - 1)`, then writes the next `c`. -/
theorem Written.extend {m m' : Mem} {out : Addr} {a c : Nat} {val : Nat → Byte}
    (hd : ∀ k < a, m (out + BitVec.ofNat 64 k) = val k)
    (hw : Written m m' (out + BitVec.ofNat 64 a) c fun j => val (a + j)) (hlen : a + c < 2 ^ 64) :
    ∀ k < a + c, m' (out + BitVec.ofNat 64 k) = val k := by
  intro k hk
  rw [hw]
  by_cases h : k < a
  · have : ¬ (out + BitVec.ofNat 64 k - (out + BitVec.ofNat 64 a)).toNat < c := by
      rw [show out + BitVec.ofNat 64 k - (out + BitVec.ofNat 64 a) =
        BitVec.ofNat 64 k - BitVec.ofNat 64 a by bv_omega]
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [ifn this, hd k h]
  · have e : (out + BitVec.ofNat 64 k - (out + BitVec.ofNat 64 a)).toNat = k - a := by
      rw [show out + BitVec.ofNat 64 k - (out + BitVec.ofNat 64 a) = BitVec.ofNat 64 (k - a) by
        rw [show k = a + (k - a) by omega, BitVec.ofNat_add]; bv_omega]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e, ifp (by omega)]
    exact congrArg val (by omega)

/-- The loop's output so far, and the frame, one step further. -/
theorem Written.step {m₀ m m' : Mem} {out : Addr} {a c len : Nat} {val : Nat → Byte}
    (hf : Frame [⟨out, len⟩] m₀ m) (hd : ∀ k < a, m (out + BitVec.ofNat 64 k) = val k)
    (hw : Written m m' (out + BitVec.ofNat 64 a) c fun j => val (a + j)) (hac : a + c ≤ len)
    (hlen : len < 2 ^ 64) :
    Frame [⟨out, len⟩] m₀ m' ∧ ∀ k < a + c, m' (out + BitVec.ofNat 64 k) = val k := by
  refine ⟨hf.trans (hw.frame ?_), Written.extend hd hw (by omega)⟩
  simp only [Region.Contains]
  rw [show out + BitVec.ofNat 64 a - out = BitVec.ofNat 64 a by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  exact hac

end VG.Proof.MlKem.X86_64
