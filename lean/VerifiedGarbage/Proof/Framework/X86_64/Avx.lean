import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.TCB.X86_64.Avx

/-!
# x86-64: AVX registers lane by lane

Untrusted: everything here is checked by Lean. The AVX instructions of the
model, stated on one 128-bit lane of their operands (`State.lane`) and on the
doublewords of a lane; and little-endian reads and writes of any width, as
the words and bytes they contain.
-/

namespace VG.X86_64

/-! ## What an AVX instruction leaves alone -/

@[simp] theorem State.setV_gpr (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) :
    (s.setV len r lo hi).gpr = s.gpr := by
  cases s; rfl
@[simp] theorem State.setV_mem (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) :
    (s.setV len r lo hi).mem = s.mem := by
  cases s; rfl
@[simp] theorem State.setV_rd (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) :
    (s.setV len r lo hi).rd = s.rd := by
  cases s; rfl
@[simp] theorem State.setV_wr (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) :
    (s.setV len r lo hi).wr = s.wr := by
  cases s; rfl
@[simp] theorem State.setV_ea (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) (m : MemOp) :
    (s.setV len r lo hi).ea m = s.ea m := by
  cases s; rfl

@[simp] theorem VOp.exec_gpr (o : VOp) (s : State) : (o.exec s).gpr = s.gpr := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
@[simp] theorem VOp.exec_mem (o : VOp) (s : State) : (o.exec s).mem = s.mem := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
@[simp] theorem VOp.exec_rd (o : VOp) (s : State) : (o.exec s).rd = s.rd := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
@[simp] theorem VOp.exec_wr (o : VOp) (s : State) : (o.exec s).wr = s.wr := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
@[simp] theorem VOp.exec_ea (o : VOp) (s : State) (m : MemOp) : (o.exec s).ea m = s.ea m := by
  simp only [State.ea, VOp.exec_gpr]

/-! ## Stores

A store's result, `{ s with mem := … }`, would spell out every field of `s`
as a projection; `State.setMem` keeps it folded. -/

/-- `s` with its memory replaced. -/
def State.setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem State.store128_eq (s : State) (a : Addr) (v : BitVec 128) :
    s.store128 a v = if InRegions s.wr a 16 then some (s.setMem (s.mem.writeW a v)) else none := by
  rw [State.store128]; rfl
theorem State.store256_eq (s : State) (a : Addr) (v : BitVec 256) :
    s.store256 a v = if InRegions s.wr a 32 then some (s.setMem (s.mem.writeW a v)) else none := by
  rw [State.store256]; rfl

@[simp] theorem State.setMem_gpr (s : State) (m : Mem) : (s.setMem m).gpr = s.gpr := by
  cases s; rfl
@[simp] theorem State.setMem_mem (s : State) (m : Mem) : (s.setMem m).mem = m := by
  cases s; rfl
@[simp] theorem State.setMem_rd (s : State) (m : Mem) : (s.setMem m).rd = s.rd := by
  cases s; rfl
@[simp] theorem State.setMem_wr (s : State) (m : Mem) : (s.setMem m).wr = s.wr := by
  cases s; rfl
@[simp] theorem State.setMem_ea (s : State) (m : Mem) (o : MemOp) : (s.setMem m).ea o = s.ea o := by
  cases s; rfl
@[simp] theorem State.setMem_lane (s : State) (m : Mem) (r : XReg) (l : Nat) :
    (s.setMem m).lane r l = s.lane r l := by
  cases s; rfl
@[simp] theorem State.setMem_xmm (s : State) (m : Mem) : (s.setMem m).xmm = s.xmm := by
  cases s; rfl
@[simp] theorem State.setMem_ymmHi (s : State) (m : Mem) : (s.setMem m).ymmHi = s.ymmHi := by
  cases s; rfl

/-! ## Lanes -/

theorem State.lane_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) (l : Nat) :
    (s.setV .l256 d lo hi).lane r l = if r = d then (if l = 0 then lo else hi) else s.lane r l := by
  simp only [State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

theorem State.lane_setV128 (s : State) (d r : XReg) (lo hi : BitVec 128) (l : Nat) :
    (s.setV .l128 d lo hi).lane r l = if r = d then (if l = 0 then lo else 0) else s.lane r l := by
  simp only [State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

@[simp] theorem lane_vbin256 (op : VBinOp) (d a b : XReg) (s : State) (r : XReg) (l : Nat) :
    ((VOp.vbin op .l256 d a b).exec s).lane r l =
      if r = d then op.sse.eval (s.lane a l) (s.lane b l) else s.lane r l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

@[simp] theorem lane_vshift256 (op : XShiftOp) (d a : XReg) (n : BitVec 8) (s : State) (r : XReg)
    (l : Nat) : ((VOp.vshift op .l256 d a n).exec s).lane r l =
      if r = d then op.eval (s.lane a l) n else s.lane r l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

@[simp] theorem lane_vpshufd256 (d a : XReg) (o : BitVec 8) (s : State) (r : XReg) (l : Nat) :
    ((VOp.vpshufd .l256 d a o).exec s).lane r l =
      if r = d then shufDwords (s.lane a l) o else s.lane r l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

@[simp] theorem lane_vbin128 (op : VBinOp) (d a b : XReg) (s : State) (r : XReg) (l : Nat) :
    ((VOp.vbin op .l128 d a b).exec s).lane r l =
      if r = d then (if l = 0 then op.sse.eval (s.lane a 0) (s.lane b 0) else 0) else s.lane r l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

@[simp] theorem lane_vextracti128_1 (d a : XReg) (s : State) (r : XReg) (l : Nat) :
    ((VOp.vextracti128 d a 1).exec s).lane r l =
      if r = d then (if l = 0 then s.lane a 1 else 0) else s.lane r l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

theorem State.ymm_eq (s : State) (r : XReg) : s.ymm r = s.lane r 1 ++ s.lane r 0 := rfl

/-! ## Doublewords -/

theorem dword_eq (x : BitVec 128) (i : Nat) : dword x i = x.extractLsb' (32 * i) 32 := rfl

theorem cases4 {i : Nat} (hi : i < 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

theorem dword_paddd (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .paddd a b) i = dword a i + dword b i := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XBinOp.eval]

theorem dword_pxor (a b : BitVec 128) (i : Nat) :
    dword (XBinOp.eval .pxor a b) i = dword a i ^^^ dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem dword_por (a b : BitVec 128) (i : Nat) :
    dword (XBinOp.eval .por a b) i = dword a i ||| dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem dword_pslld (a : BitVec 128) (n : BitVec 8) (hn : n.toNat < 32) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld a n) i = dword a i <<< n.toNat := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega, ite_false]
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp

theorem dword_psrld (a : BitVec 128) (n : BitVec 8) (hn : n.toNat < 32) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld a n) i = dword a i >>> n.toNat := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega, ite_false]
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp

theorem dword_shufDwords (a : BitVec 128) (o : BitVec 8) {i : Nat} (hi : i < 4) :
    dword (shufDwords a o) i = dword a (o.extractLsb' (2 * i) 2).toNat := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [shufDwords]

/-- `vpshufd` with `0x55 * k` broadcasts doubleword `k`. -/
theorem dword_shufDwords_bcast (a : BitVec 128) {k i : Nat} (hk : k < 4) (hi : i < 4) :
    dword (shufDwords a (BitVec.ofNat 8 (0x55 * k))) i = dword a k := by
  rw [dword_shufDwords _ _ hi]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

theorem dword_punpckldq (a b : BitVec 128) :
    XBinOp.eval .punpckldq a b = ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1) := rfl

theorem dword_punpckhdq (a b : BitVec 128) :
    XBinOp.eval .punpckhdq a b = ofDwords (dword a 2) (dword b 2) (dword a 3) (dword b 3) := rfl

/-- Bit `m` of doubleword `i` of `ofBytes f`. -/
theorem getLsbD_dword_ofBytes (f : Nat → BitVec 8) {i m : Nat} (hi : i < 4) (hm : m < 32) :
    (dword (ofBytes f) i).getLsbD m = (f (4 * i + m / 8)).getLsbD (m % 8) := by
  rw [getLsbD_dword, decide_eq_true hm, Bool.true_and,
    show 32 * i + m = 8 * (4 * i + m / 8) + m % 8 by omega,
    getLsbD_ofBytes _ (by omega) (Nat.mod_lt _ (by omega))]

/-- The `vpshufb` mask rotating each doubleword left by 16 bits. -/
abbrev rot16Mask : BitVec 128 := 0x0d0c0f0e09080b0a0504070601000302#128
/-- The `vpshufb` mask rotating each doubleword left by 8 bits. -/
abbrev rot8Mask : BitVec 128 := 0x0e0d0c0f0a09080b0605040702010003#128

theorem pshufb_rot16_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a rot16Mask = ofBytes fun j => byte a (4 * (j / 4) + (j % 4 + 2) % 4) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_rot8_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a rot8Mask = ofBytes fun j => byte a (4 * (j / 4) + (j % 4 + 3) % 4) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem dword_pshufb_rot16 (a : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb a rot16Mask) i = (dword a i).rotateLeft 16 := by
  rw [pshufb_rot16_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_dword_ofBytes _ hi hm, BitVec.getLsbD_rotateLeft]
  have h8 : m % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [byte, BitVec.getLsbD_extractLsb', getLsbD_dword, h8, decide_true, Bool.true_and,
    show 16 % 32 = 16 from rfl]
  by_cases h : m < 16
  · have h' : 32 - 16 + m < 32 := by omega
    simp only [h, h', ite_true, decide_true, Bool.true_and]
    exact congrArg _ (by omega)
  · have h' : m - 16 < 32 := by omega
    simp only [h, h', hm, ite_false, decide_true, Bool.true_and]
    exact congrArg _ (by omega)

theorem dword_pshufb_rot8 (a : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb a rot8Mask) i = (dword a i).rotateLeft 8 := by
  rw [pshufb_rot8_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_dword_ofBytes _ hi hm, BitVec.getLsbD_rotateLeft]
  have h8 : m % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [byte, BitVec.getLsbD_extractLsb', getLsbD_dword, h8, decide_true, Bool.true_and,
    show 8 % 32 = 8 from rfl]
  by_cases h : m < 8
  · have h' : 32 - 8 + m < 32 := by omega
    simp only [h, h', ite_true, decide_true, Bool.true_and]
    exact congrArg _ (by omega)
  · have h' : m - 8 < 32 := by omega
    simp only [h, h', hm, ite_false, decide_true, Bool.true_and]
    exact congrArg _ (by omega)

/-- A rotation as two shifts. -/
theorem shr_or_shl (x : BitVec 32) {k : Nat} (hk : 0 < k) (hk' : k < 32) :
    x >>> (32 - k) ||| x <<< k = x.rotateLeft k := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hk']
  by_cases h : m < k
  · simp [h, hm]
  · rw [BitVec.getLsbD_of_ge x (32 - k + m) (by omega)]
    simp [h, hm]

/-! ## Little-endian reads and writes, word by word -/

theorem readW_extract (m : Mem) (a : Addr) {w k n : Nat} (h : 8 * (k + n) ≤ w) :
    (m.readW a w).extractLsb' (8 * k) (8 * n) = m.readW (a + BitVec.ofNat 64 k) (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and, decide_eq_true (show 8 * k + i < w by omega)]
  rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]
  rw [show a + BitVec.ofNat 64 ((8 * k + i) / 8) = a + BitVec.ofNat 64 k + BitVec.ofNat 64 (i / 8) by
    rw [show (8 * k + i) / 8 = k + i / 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]]
  exact congrArg _ (by omega)

theorem readW_writeW_inside (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) {k n : Nat}
    (h : 8 * (k + n) ≤ w) (hw : w < 2 ^ 64) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 k) (8 * n) = v.extractLsb' (8 * k) (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega)]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 k + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (k + i / 8) by
    rw [BitVec.ofNat_add]; bv_omega]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show k + i / 8 < w / 8 by omega, ite_true, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by omega), decide_eq_true (by omega), Bool.true_and, Bool.true_and]
  exact congrArg _ (by omega)

/-- A read of `n` bytes at `p + d` after a write of `w'` bits at `p + e`, elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) {w' : Nat} (v : BitVec w') {d e n : Nat}
    (hd : d + n < 2 ^ 63) (he : e + w' / 8 < 2 ^ 63) (h : d + n ≤ e ∨ e + w' / 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) (8 * n) =
      m.readW (p + BitVec.ofNat 64 d) (8 * n) := by
  refine Mem.readW_writeW_sep (fun x hx hy => ?_) (by omega)
  rw [show 8 * n / 8 = n by omega] at hx
  bv_omega

theorem readW_8 (m : Mem) (a : Addr) : m.readW a 8 = m a := by
  simp only [Mem.readW, Mem.read]
  ext i hi; simp only [BitVec.getElem_setWidth]; rw [BitVec.getLsbD_append]; simp [hi]

/-- Byte `k` of a read. -/
theorem byte_readW (m : Mem) (a : Addr) {w k : Nat} (h : 8 * (k + 1) ≤ w) :
    (m.readW a w).extractLsb' (8 * k) 8 = m (a + BitVec.ofNat 64 k) := by
  have e := readW_extract m a (k := k) (n := 1) h
  rw [Nat.mul_one] at e
  rw [e, readW_8]

/-- Byte `k` of a write. -/
theorem writeW_byte (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) {k : Nat} (h : 8 * (k + 1) ≤ w)
    (hw : w < 2 ^ 64) : (m.writeW a v) (a + BitVec.ofNat 64 k) = v.extractLsb' (8 * k) 8 := by
  have e := readW_writeW_inside m a v (k := k) (n := 1) h hw
  rw [Nat.mul_one, readW_8] at e
  exact e

/-- A byte outside a write. -/
theorem writeW_byte_off (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (x : Addr)
    (h : w / 8 ≤ (x - a).toNat) : (m.writeW a v) x = m x := by
  simp only [Mem.writeW, Mem.write, show ¬ (x - a).toNat < w / 8 by omega, ite_false]

theorem extract_extract {w : Nat} (x : BitVec w) (a b c d : Nat) (h : c + d ≤ b) :
    (x.extractLsb' a b).extractLsb' c d = x.extractLsb' (a + c) d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true hi, decide_eq_true (show c + i < b by omega),
    Bool.true_and, Nat.add_assoc]

/-- Doubleword `i` of lane `l` of a 256-bit load. -/
theorem dword_load256 (m : Mem) (a : Addr) {l i : Nat} (hl : l < 2) (hi : i < 4) :
    dword (if l = 0 then (m.readW a 256).extractLsb' 0 128 else (m.readW a 256).extractLsb' 128 128) i =
      m.readW (a + BitVec.ofNat 64 (16 * l + 4 * i)) 32 := by
  have e : (if l = 0 then (m.readW a 256).extractLsb' 0 128 else (m.readW a 256).extractLsb' 128 128) =
      (m.readW a 256).extractLsb' (128 * l) 128 := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  rw [e, dword_eq, extract_extract _ _ _ _ _ (by omega),
    show 128 * l + 32 * i = 8 * (16 * l + 4 * i) by omega]
  exact readW_extract m a (k := 16 * l + 4 * i) (n := 4) (by omega)

/-- Doubleword `i` of lane `l` of a 256-bit register, as a stored value. -/
theorem extract_ymm (s : State) (r : XReg) {l i : Nat} (hl : l < 2) (hi : i < 4) :
    (s.ymm r).extractLsb' (8 * (16 * l + 4 * i)) (8 * 4) = dword (s.lane r l) i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simp only [show 8 * (16 * 0 + 4 * i) + j < 128 by omega, ite_true]
    exact congrArg _ (by omega)
  · simp only [show ¬ 8 * (16 * 1 + 4 * i) + j < 128 by omega, ite_false, show (1 : Nat) ≠ 0 by omega]
    exact congrArg _ (by omega)

end VG.X86_64
