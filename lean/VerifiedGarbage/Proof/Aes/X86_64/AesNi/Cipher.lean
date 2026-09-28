import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Gcm.X86_64.Rev

/-!
# AES-NI: the instructions are FIPS 197's rounds

Untrusted: everything here is checked by Lean. An SSE register holds an
AES state as its 16 bytes in memory order (`st`): byte `r + 4c` is
`s[r, c]`, as FIPS 197 §3.4 lays the state out and as the SDM's AES
instructions read it. On such registers `pxor`, `aesenc` and `aesenclast`
are `AddRoundKey`, a full round and the last round of `Spec.Aes.cipher`
(`pxor_st`, `aesenc_st`, `aesenclast_st`); the S-box of the ISA model,
computed by repeated squaring, is the one of `Spec/Aes.lean` (`sbox_eq`).
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey sbox roundKey cipher bytesAt)

/-! ## GF(2⁸) -/

theorem mul_eq : aesMul = Spec.Aes.mul := rfl

/-- Both square and multiply `b²`, `b⁴`, …, `b¹²⁸` in the same order: unfolded
to the same term (no evaluation left for the kernel). -/
theorem inv_eq (b : BitVec 8) : aesInv b = Spec.Aes.inv b := by
  simp (config := {decide := true}) only [aesInv, Spec.Aes.inv, Spec.Aes.pow, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, mul_eq,
    ite_true, ite_false]

theorem sbox_eq : aesSbox = sbox := by
  funext b
  simp only [aesSbox, sbox, inv_eq, ofBits8]

theorem mul_one' : ∀ b : BitVec 8, Spec.Aes.mul 1 b = b := by decide

/-! ## States in registers -/

/-- The AES state held by a register. -/
def st (v : BitVec 128) : Spec.Aes.State := Vector.ofFn fun i => byte v i

theorem getD_ofFn {f : Fin 16 → Byte} {i : Nat} (h : i < 16) :
    (Vector.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Vector.getD, h]

theorem getD_st (v : BitVec 128) {i : Nat} (h : i < 16) : (st v).getD i 0 = byte v i := by
  rw [st, getD_ofFn h]

theorem st_ext {s t : Spec.Aes.State} (h : ∀ i < 16, s.getD i 0 = t.getD i 0) : s = t := by
  apply Vector.ext; intro i hi
  have := h i hi
  simpa [Vector.getD, hi] using this

theorem st_inj {a b : BitVec 128} (h : st a = st b) : a = b :=
  VG.Proof.Gcm.X86_64.ext_byte fun i hi => by rw [← getD_st a hi, ← getD_st b hi, h]

theorem byte_xor (a b : BitVec 128) (i : Nat) : byte (a ^^^ b) i = byte a i ^^^ byte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hj, decide_true, Bool.true_and]

/-! ## FIPS 197's transformations, byte by byte -/

theorem getD_addRoundKey (s : Spec.Aes.State) (rk : List Byte) {i : Nat} (h : i < 16) :
    (addRoundKey s rk).getD i 0 = s.getD i 0 ^^^ rk.getD i 0 := by
  rw [addRoundKey, getD_ofFn h]

theorem getD_subBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (subBytes s).getD i 0 = sbox (s.getD i 0) := by
  simp [subBytes, Vector.getD, h]

theorem getD_shiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (shiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + i % 4) % 4)) 0 := by
  rw [shiftRows, getD_ofFn h]

theorem getD_mixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (mixColumns s).getD i 0 =
      Spec.Aes.mul 0x02 (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x03 (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0 ^^^ s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0 := by
  rw [mixColumns, getD_ofFn h]

theorem byte_mapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesMapBytes f x) i = f (byte x i) := by
  rw [aesMapBytes, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

theorem byte_shiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesShiftRows x) i = byte x (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  rw [aesShiftRows, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

theorem byte_mixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesMixColumns x) i =
      aesMul 0x02 (byte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x03 (byte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (byte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (byte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesMixColumns, aesMixWith, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

/-! ## The instructions -/

/-- `pxor` with a round key is `AddRoundKey`. -/
theorem pxor_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    st (XBinOp.eval .pxor v k) = addRoundKey (st v) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, getD_st _ hi, ← hk i hi]
  exact byte_xor v k i

/-- `aesenc` is a round. -/
theorem aesenc_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    st (XBinOp.eval .aesenc v k) = addRoundKey (mixColumns (shiftRows (subBytes (st v)))) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, getD_mixColumns _ hi, ← hk i hi]
  simp only [XBinOp.eval, byte_xor]
  rw [byte_mixColumns _ hi]
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  simp only [byte_mapBytes _ _ (hr _), getD_shiftRows _ (hr _), byte_shiftRows _ (hr _), sbox_eq,
    mul_eq, mul_one', getD_subBytes _ (hs _), getD_st _ (hs _)]

/-- `aesenclast` is the last round. -/
theorem aesenclast_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    st (XBinOp.eval .aesenclast v k) = addRoundKey (shiftRows (subBytes (st v))) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, ← hk i hi]
  simp only [XBinOp.eval, byte_xor]
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  simp only [byte_mapBytes _ _ hi, getD_shiftRows _ hi, byte_shiftRows _ hi, sbox_eq,
    getD_subBytes _ (hs _), getD_st _ (hs _)]

/-! ## The cipher -/

/-- The state after `AddRoundKey` and `k` full rounds. -/
def rnds (w : List Byte) (x : Spec.Aes.State) (k : Nat) : Spec.Aes.State :=
  (List.range k).foldl
    (fun s j => addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey w (j + 1)))
    (addRoundKey x (roundKey w 0))

theorem rnds_zero (w : List Byte) (x : Spec.Aes.State) :
    rnds w x 0 = addRoundKey x (roundKey w 0) := rfl

theorem rnds_succ (w : List Byte) (x : Spec.Aes.State) (k : Nat) :
    rnds w x (k + 1) =
      addRoundKey (mixColumns (shiftRows (subBytes (rnds w x k)))) (roundKey w (k + 1)) := by
  simp only [rnds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem cipher_eq (nr : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher nr w x = addRoundKey (shiftRows (subBytes (rnds w x (nr - 1)))) (roundKey w nr) := rfl

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem roundKey_getD (m : Mem) (p : Addr) {L j i : Nat} (hi : i < 16) (hj : 16 * j + 16 ≤ L) :
    (roundKey (bytesAt m p L) j).getD i 0 = m (p + BitVec.ofNat 64 (16 * j + i)) := by
  simp [roundKey, bytesAt, List.getD, hi, show 16 * j + i < L by omega]

/-- Round key `j`, loaded from the schedule. -/
theorem byte_roundKey (m : Mem) (p : Addr) {L j : Nat} (hj : 16 * j + 16 ≤ L) :
    ∀ i < 16, byte (m.readW (p + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128) i =
      (roundKey (bytesAt m p L) j).getD i 0 := by
  intro i hi
  rw [VG.Proof.Gcm.X86_64.byte_readW _ _ hi, roundKey_getD _ _ hi hj, ofInt_natCast,
    BitVec.add_assoc, BitVec.ofNat_add]

theorem st_toList (r : BitVec 128) : (st r).toList = (List.range 16).map (byte r) := by
  apply List.ext_getElem <;> simp [st]

/-- `CIPH_K` of a block, as `Spec.Gcm.aesWith` states it, from the register
`r` that encrypting the block's bytes left. -/
theorem aesWith_eq (nr : Nat) (w : List Byte) (x r : BitVec 128)
    (h : st r = cipher nr w (st (XBinOp.eval .pshufb x VG.Proof.Gcm.X86_64.revMask))) :
    Spec.Gcm.aesWith nr w x = XBinOp.eval .pshufb r VG.Proof.Gcm.X86_64.revMask := by
  have e : (Vector.ofFn fun i => (Spec.Gcm.toBytes x).getD i 0) =
      st (XBinOp.eval .pshufb x VG.Proof.Gcm.X86_64.revMask) := by
    apply st_ext; intro i hi
    rw [getD_ofFn hi, getD_st _ hi, VG.Proof.Gcm.X86_64.byte_pshufb_rev _ hi]
    simp [Spec.Gcm.toBytes, List.getD, hi, byte]
  rw [Spec.Gcm.aesWith, e, ← h, st_toList, VG.Proof.Gcm.X86_64.gcmOfBytes_eq,
    VG.Proof.Gcm.X86_64.pshufb_rev]

end VG.Proof.Aes.X86_64.AesNi
