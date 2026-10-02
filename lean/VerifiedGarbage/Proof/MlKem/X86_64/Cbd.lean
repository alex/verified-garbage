import VerifiedGarbage.Impl.MlKem.X86_64.Cbd
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: `vg_mlkem_cbd2`

What the code computes of each byte in a word is checked for each of the 256
bytes by the kernel (`cbd_vals`); the words of the registers after the nibbles
are split (`front_ok`), and the doublewords stored from them (`grp_ok`), are
proven lane by lane.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Cbd

/-! ## One byte -/

/-- The pair sums of the byte in the word `c`. -/
def cbdT (c : BitVec 16) : BitVec 16 := (c &&& 0x55#16) + ((c >>> 1) &&& 0x55#16)

/-- `e` of the byte in the word `c`: `x₀ - y₀ + 2` and `x₁ - y₁ + 2` in its nibbles. -/
def cbdE (c : BitVec 16) : BitVec 16 := ((cbdT c &&& 0x33#16) + 0x22#16) - ((cbdT c >>> 2) &&& 0x33#16)

/-- Nibble `h` of a word `e`. -/
def nib (h : Nat) (e : BitVec 16) : BitVec 16 := if h = 0 then e &&& 0x0F#16 else e >>> 4

/-- A coefficient from its word `w = v + 2`: `v mod q`. -/
def cbdFix (w : BitVec 16) : BitVec 32 := cadd32 (w.setWidth 32 - 2#32)

theorem cbd_vals : ∀ v < 256, (cbdFix (nib 0 (cbdE (BitVec.ofNat 16 v)))).toNat = (cbdX v + 3329 - cbdY v) % 3329 ∧
    (cbdFix (nib 1 (cbdE (BitVec.ofNat 16 v)))).toNat = (cbdX (v / 16) + 3329 - cbdY (v / 16)) % 3329 := by
  decide +kernel

/-! ## Lanes -/

theorem word_psrlw (a : BitVec 128) (n : BitVec 8) (hn : n.toNat ≤ 15) {i : Nat} (hi : i < 8) :
    word (XShiftOp.eval .psrlw a n) i = word a i >>> n.toNat := by
  simp only [XShiftOp.eval, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 15 < n.toNat by omega))]
  exact word_ofWords _ hi

/-- The even byte of a word read from memory. -/
theorem word_lo (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    word (m.readW a 128) i &&& 0x00FF#16 = (m (a + BitVec.ofNat 64 (2 * i))).setWidth 16 := by
  rw [word_readW _ _ hi]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_and, Mem.readW, BitVec.getLsbD_setWidth]
  by_cases h : j < 8
  · rw [getLsbD_read _ _ (by omega), show j / 8 = 0 by omega, show j % 8 = j by omega, BitVec.add_zero,
      show (0x00FF#16).getLsbD j = true by revert j; decide]
    simp [h]
  · rw [show (0x00FF#16).getLsbD j = false by revert h hj; revert j; decide]
    rw [BitVec.getLsbD_of_ge (m (a + BitVec.ofNat 64 (2 * i))) j (by omega)]; simp

/-- The odd byte of a word read from memory. -/
theorem word_hi (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    word (m.readW a 128) i >>> 8 = (m (a + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 := by
  rw [word_readW _ _ hi]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, Mem.readW, BitVec.getLsbD_setWidth]
  by_cases h : j < 8
  · rw [getLsbD_read _ _ (by omega), show (8 + j) / 8 = 1 by omega, show (8 + j) % 8 = j by omega,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    simp [show 8 + j < 16 by omega, hj]
  · simp only [show ¬ 8 + j < 16 by omega, decide_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge (m (a + BitVec.ofNat 64 (2 * i + 1))) j (by omega), Bool.and_false]

theorem dword_punpcklwd0' (a : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpcklwd a 0) j = (word a j).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [dword_punpcklwd0 _ hj, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (word a j).isLt; omega)]

theorem dword_punpckhwd0' (a : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpckhwd a 0) j = (word a (4 + j)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [dword_punpckhwd0 _ hj, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (word a (4 + j)).isLt; omega)]

theorem dword_punpcklqdq (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpcklqdq a b) j = if j < 2 then dword a j else dword b (j - 2) := by
  rw [punpcklqdq_eq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.reduceLT, Nat.reduceSub, ite_true, ite_false, dword_ofDwords_0,
      dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem dword_punpckhqdq (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpckhqdq a b) j = if j < 2 then dword a (2 + j) else dword b j := by
  rw [punpckhqdq_eq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.reduceLT, Nat.reduceAdd, ite_true, ite_false, dword_ofDwords_0,
      dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

/-! ## The constants -/

def m8V : BitVec 128 := 0x00FF00FF00FF00FF00FF00FF00FF00FF#128
def m9V : BitVec 128 := 0x00550055005500550055005500550055#128
def m10V : BitVec 128 := 0x00330033003300330033003300330033#128
def m11V : BitVec 128 := 0x00220022002200220022002200220022#128
def m12V : BitVec 128 := 0x000F000F000F000F000F000F000F000F#128
/-- `2` in each doubleword. -/
def twoD : BitVec 128 := 0x00000002000000020000000200000002#128

theorem word_m {i : Nat} (hi : i < 8) : word m8V i = 0x00FF#16 ∧ word m9V i = 0x55#16 ∧
    word m10V i = 0x33#16 ∧ word m11V i = 0x22#16 ∧ word m12V i = 0x0F#16 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem dword_twoD {j : Nat} (hj : j < 4) : dword twoD j = 2#32 := by
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> decide

/-- The constants in their registers. -/
structure Consts (s : State) : Prop where
  m8 : s.xmm .xmm8 = m8V
  m9 : s.xmm .xmm9 = m9V
  m10 : s.xmm .xmm10 = m10V
  m11 : s.xmm .xmm11 = m11V
  m12 : s.xmm .xmm12 = m12V
  two : s.xmm .xmm13 = twoD
  z : s.xmm .xmm14 = 0
  q : s.xmm .xmm15 = qD

theorem consts_iff (s : State) : Consts s ↔ s.xmm .xmm8 = m8V ∧ s.xmm .xmm9 = m9V ∧ s.xmm .xmm10 = m10V ∧
    s.xmm .xmm11 = m11V ∧ s.xmm .xmm12 = m12V ∧ s.xmm .xmm13 = twoD ∧ s.xmm .xmm14 = 0 ∧ s.xmm .xmm15 = qD :=
  ⟨fun h => ⟨h.m8, h.m9, h.m10, h.m11, h.m12, h.two, h.z, h.q⟩,
    fun ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩ => ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩⟩

/-! ## The nibbles -/

/-- `e` of byte `b` of the sixteen at `p`. -/
abbrev eB (m : Mem) (p : Addr) (b : Nat) : BitVec 16 := cbdE ((m (p + BitVec.ofNat 64 b)).setWidth 16)

theorem front_ok {s : State} (hc : Consts s) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16) :
    WP isa (.block cbdFront) s fun s' =>
      Consts s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ k < 8, word (s'.xmm .xmm4) k = nib (k % 2) (eB s.mem (s.gpr .rdi) (2 * (k / 2))) ∧
        word (s'.xmm .xmm0) k = nib (k % 2) (eB s.mem (s.gpr .rdi) (2 * (4 + k / 2))) ∧
        word (s'.xmm .xmm2) k = nib (k % 2) (eB s.mem (s.gpr .rdi) (2 * (k / 2) + 1)) ∧
        word (s'.xmm .xmm1) k = nib (k % 2) (eB s.mem (s.gpr .rdi) (2 * (4 + k / 2) + 1)) := by
  simp only [cbdFront, cbdNib]
  vrunm [h1, eval_movdqa]
  refine ⟨⟨hc.m8, hc.m9, hc.m10, hc.m11, hc.m12, hc.two, hc.z, hc.q⟩, fun k hk => ?_⟩
  have hk2 : k / 2 < 8 := by omega
  have h42 : 4 + k / 2 < 8 := by omega
  obtain ⟨a8, a9, a10, a11, a12⟩ := word_m hk2
  obtain ⟨b8, b9, b10, b11, b12⟩ := word_m h42
  simp (disch := first | omega | decide) only [word_punpcklwd, word_punpckhwd, word_pand, word_paddw,
    word_psubw, word_psrlw, hc.m8, hc.m9, hc.m10, hc.m11, hc.m12, a8, a9, a10, a11, a12, b8, b9,
    b10, b11, b12, show (1 : BitVec 8).toNat = 1 from rfl, show (2 : BitVec 8).toNat = 2 from rfl,
    show (4 : BitVec 8).toNat = 4 from rfl, show (8 : BitVec 8).toNat = 8 from rfl, word_lo _ _ hk2,
    word_lo _ _ h42, word_hi _ _ hk2, word_hi _ _ h42]
  simp only [nib, eB, cbdE, cbdT]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-! ## Sixteen coefficients -/

/-- The value stored for lane `j` of store `k` of a group: the low doublewords
of `A` (low and high nibble of an even byte) and then of `B` (an odd byte). -/
def grpV (A B : BitVec 128) (k j : Nat) : BitVec 32 :=
  cbdFix (if j < 2 then word A (2 * k + j) else word B (2 * k + j - 2))

/-- `cbdOut` on a register holding `D`. -/
def outV (D : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddd (XBinOp.eval .psubd D twoD)
    (XBinOp.eval .pand (XShiftOp.eval .psrad (XBinOp.eval .psubd D twoD) 31) qD)

/-- The low (`h = 0`) or high doublewords of `A` and `B`, zero-extended. -/
def ext2 (h : Nat) (A B : BitVec 128) : BitVec 128 × BitVec 128 :=
  if h = 0 then (XBinOp.eval .punpcklwd A 0, XBinOp.eval .punpcklwd B 0)
  else (XBinOp.eval .punpckhwd A 0, XBinOp.eval .punpckhwd B 0)

/-- Store `k` of a group. -/
def grpX (A B : BitVec 128) (k : Nat) : BitVec 128 :=
  outV (if k % 2 = 0 then XBinOp.eval .punpcklqdq (ext2 (k / 2) A B).1 (ext2 (k / 2) A B).2
    else XBinOp.eval .punpckhqdq (ext2 (k / 2) A B).1 (ext2 (k / 2) A B).2)

theorem dword_grpX (A B : BitVec 128) {k j : Nat} (hk : k < 4) (hj : j < 4) :
    dword (grpX A B k) j = grpV A B k j := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [grpX, outV, ext2, grpV, cbdFix, cadd32, Nat.reduceMod, Nat.reduceDiv,
      Nat.reduceEqDiff, ↓reduceIte, dword_paddd,
      dword_psubd, dword_pand,
      dword_psrad31, dword_punpcklqdq, dword_punpckhqdq, dword_punpcklwd0', dword_punpckhwd0', dword_twoD, dword_qD,
      Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]

/-- Memory after the stores of a group at `p`. -/
def wr4 (m : Mem) (p : Addr) (off : Nat) (X : Nat → BitVec 128) : Mem :=
  (((m.writeW (p + BitVec.ofNat 64 off) (X 0)).writeW (p + BitVec.ofNat 64 (off + 16)) (X 1)).writeW
    (p + BitVec.ofNat 64 (off + 32)) (X 2)).writeW (p + BitVec.ofNat 64 (off + 48)) (X 3)

theorem grp_ok {a b : XReg} {off : Nat}
    (hab : (a, b, off) = (.xmm4, .xmm2, 0) ∨ (a, b, off) = (.xmm0, .xmm1, 64)) {s : State} (hc : Consts s)
    (hw : ∀ k < 4, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (off + 16 * k)) 16) :
    WP isa (.block (cbdGrp a b off)) s fun s' =>
      Consts s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (off = 0 → s'.xmm .xmm0 = s.xmm .xmm0 ∧ s'.xmm .xmm1 = s.xmm .xmm1) ∧
      s'.mem = wr4 s.mem (s.gpr .rsi) off (grpX (s.xmm a) (s.xmm b)) := by
  have w0 := hw 0 (by decide)
  have w1 := hw 1 (by decide)
  have w2 := hw 2 (by decide)
  have w3 := hw 3 (by decide)
  rcases hab with h | h <;> cases h <;>
  · simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, add_ofNat_zero] at w0 w1 w2 w3 ⊢
    simp only [cbdGrp, cbdOut, dcadd, wr4, grpX, outV, ext2, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff,
      ite_true, ite_false]
    vrunm [w0, w1, w2, w3, eval_movdqa, consts_iff, hc.m8, hc.m9, hc.m10, hc.m11, hc.m12, hc.two, hc.z, hc.q,
      false_implies]

/-! ## Sixteen bytes -/

theorem sx128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide

/-- The words of the nibbles of the sixteen bytes at `p`: `A₀`, `A₁` of the
even bytes (0–6, 8–14), `B₀`, `B₁` of the odd ones. -/
structure Nibs (m : Mem) (p : Addr) (A₀ B₀ A₁ B₁ : BitVec 128) : Prop where
  a0 : ∀ k < 8, word A₀ k = nib (k % 2) (eB m p (2 * (k / 2)))
  a1 : ∀ k < 8, word A₁ k = nib (k % 2) (eB m p (2 * (4 + k / 2)))
  b0 : ∀ k < 8, word B₀ k = nib (k % 2) (eB m p (2 * (k / 2) + 1))
  b1 : ∀ k < 8, word B₁ k = nib (k % 2) (eB m p (2 * (4 + k / 2) + 1))

theorem body_ok {s : State} (hc : Consts s) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16)
    (hw : ∀ k < 8, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (16 * k)) 16) :
    WP isa (.block cbd2Body) s fun s' => Consts s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 128 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rdi, .rsi, .rcx] s s' ∧
      ∃ A₀ B₀ A₁ B₁, Nibs s.mem (s.gpr .rdi) A₀ B₀ A₁ B₁ ∧
        s'.mem = wr4 (wr4 s.mem (s.gpr .rsi) 0 (grpX A₀ B₀)) (s.gpr .rsi) 64 (grpX A₁ B₁) := by
  unfold cbd2Body
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (front_ok hc h1) fun s₁ ⟨hc₁, m₁, g₁, rd₁, wr₁, hn⟩ => ?_
  have hw₁ : ∀ off, off = 0 ∨ off = 64 → ∀ k < 4, InRegions s₁.wr (s₁.gpr .rsi + BitVec.ofNat 64 (off + 16 * k)) 16 :=
    fun off ho k hk => by
      rw [wr₁, g₁, show off + 16 * k = 16 * (off / 16 + k) by omega]; exact hw _ (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (grp_ok (Or.inl rfl) hc₁ (hw₁ 0 (.inl rfl))) fun s₂ ⟨hc₂, g₂, rd₂, wr₂, x₂, m₂⟩ => ?_
  obtain ⟨x0, x1⟩ := x₂ rfl
  have hw₂ : ∀ k < 4, InRegions s₂.wr (s₂.gpr .rsi + BitVec.ofNat 64 (64 + 16 * k)) 16 := fun k hk => by
    rw [wr₂, g₂]; exact hw₁ 64 (.inr rfl) k hk
  rw [WP.block_append_iff]
  refine WP.mono (grp_ok (Or.inr rfl) hc₂ hw₂) fun s₃ ⟨hc₃, g₃, rd₃, wr₃, _, m₃⟩ => ?_
  vrunm [sx128, consts_iff, hc₃.m8, hc₃.m9, hc₃.m10, hc₃.m11, hc₃.m12, hc₃.two, hc₃.z, hc₃.q, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.xmm_setReg, RegUpd.gpr_setReg, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.xmm_setFlags, RegUpd.gpr_setFlags]
  have hg : s₃.gpr = s.gpr := by rw [g₃, g₂, g₁]
  refine ⟨by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [hg], by rw [hg], by rw [hg], by rw [hg],
    ⟨fun r hr => ?_, ?_, ?_⟩, s₁.xmm .xmm4, s₁.xmm .xmm2, s₁.xmm .xmm0, s₁.xmm .xmm1,
    ⟨fun k hk => (hn k hk).1, fun k hk => (hn k hk).2.1, fun k hk => (hn k hk).2.2.1, fun k hk => (hn k hk).2.2.2⟩,
    by rw [m₃, m₂, m₁, g₂, g₁, x0, x1]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, hg]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, rd₃, rd₂, rd₁]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, wr₃, wr₂, wr₁]

/-! ## The coefficients -/

/-- The coefficients a group writes: sixteen from `c₀ + off / 4`. -/
theorem coeffAt_wr4 (m : Mem) (p : Addr) {c₀ off : Nat} (hoff : off = 0 ∨ off = 64) (hc : c₀ + off / 4 + 16 ≤ 256)
    (X : Nat → BitVec 128) {k : Nat} (hk : k < 256) :
    coeffAt (wr4 m (coeffAddr p c₀) off X) p k =
      if c₀ + off / 4 ≤ k ∧ k < c₀ + off / 4 + 16 then
        dword (X ((k - (c₀ + off / 4)) / 4)) ((k - (c₀ + off / 4)) % 4)
      else coeffAt m p k := by
  have ha : ∀ d, 4 ∣ d → coeffAddr p c₀ + BitVec.ofNat 64 d = coeffAddr p (c₀ + d / 4) := fun d hd => by
    rw [show d = 4 * (d / 4) from (Nat.mul_div_cancel' hd).symm, coeffAddr_off, Nat.mul_div_cancel_left _ (by decide)]
  simp only [wr4]
  rw [ha off (by omega), ha (off + 16) (by omega), ha (off + 32) (by omega), ha (off + 48) (by omega),
    coeffAt_write128 _ _ (by omega) _ hk, coeffAt_write128 _ _ (by omega) _ hk, coeffAt_write128 _ _ (by omega) _ hk,
    coeffAt_write128 _ _ (by omega) _ hk]
  generalize hb : c₀ + off / 4 = b at *
  have e16 : (off + 16) / 4 = off / 4 + 4 := by omega
  have e32 : (off + 32) / 4 = off / 4 + 8 := by omega
  have e48 : (off + 48) / 4 = off / 4 + 12 := by omega
  rw [e16, e32, e48, ← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc, hb]
  by_cases hin : b ≤ k ∧ k < b + 16
  · rw [ite_eq_left hin]
    rcases (by omega : (k - b) / 4 = 0 ∨ (k - b) / 4 = 1 ∨ (k - b) / 4 = 2 ∨ (k - b) / 4 = 3) with h | h | h | h <;>
      rw [h] <;> simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> congr 1 <;> omega
  · rw [ite_eq_right hin]
    simp (disch := omega) only [ite_eq_right]

/-- A coefficient from nibble `h` of byte `b` at `p`. -/
theorem nib_val (m : Mem) (p : Addr) {h : Nat} (hh : h < 2) (b : Nat) :
    (cbdFix (nib h (eB m p b))).toNat =
      (cbdX ((m (p + BitVec.ofNat 64 b)).toNat / 16 ^ h) + 3329 -
        cbdY ((m (p + BitVec.ofNat 64 b)).toNat / 16 ^ h)) % 3329 := by
  have hv := cbd_vals _ (m (p + BitVec.ofNat 64 b)).isLt
  rw [BitVec.ofNat_toNat] at hv
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · rw [Nat.pow_zero, Nat.div_one]; exact hv.1
  · rw [Nat.pow_one]; exact hv.2

/-- The value of lane `j` of store `t` of group `g`: from nibble `j mod 2` of
byte `8 g + 2 t + ⌊j / 2⌋`. -/
theorem grp_val {m : Mem} {p : Addr} {A₀ B₀ A₁ B₁ : BitVec 128} (hn : Nibs m p A₀ B₀ A₁ B₁) {g t j : Nat}
    (hg : g < 2) (ht : t < 4) (hj : j < 4) :
    (grpV (if g = 0 then A₀ else A₁) (if g = 0 then B₀ else B₁) t j).toNat =
      (cbdX ((m (p + BitVec.ofNat 64 (8 * g + 2 * t + j / 2))).toNat / 16 ^ (j % 2)) + 3329 -
        cbdY ((m (p + BitVec.ofNat 64 (8 * g + 2 * t + j / 2))).toNat / 16 ^ (j % 2))) % 3329 := by
  unfold grpV
  by_cases hj2 : j < 2
  · rw [ite_eq_left hj2]
    rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
    · rw [ite_eq_left rfl, hn.a0 _ (by omega), show (2 * t + j) % 2 = j % 2 by omega,
        show 2 * ((2 * t + j) / 2) = 8 * 0 + 2 * t + j / 2 by omega]
      exact nib_val m p (by omega) _
    · rw [ite_eq_right (by decide), hn.a1 _ (by omega), show (2 * t + j) % 2 = j % 2 by omega,
        show 2 * (4 + (2 * t + j) / 2) = 8 * 1 + 2 * t + j / 2 by omega]
      exact nib_val m p (by omega) _
  · rw [ite_eq_right hj2]
    rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
    · rw [ite_eq_left rfl, hn.b0 _ (by omega), show (2 * t + j - 2) % 2 = j % 2 by omega,
        show 2 * ((2 * t + j - 2) / 2) + 1 = 8 * 0 + 2 * t + j / 2 by omega]
      exact nib_val m p (by omega) _
    · rw [ite_eq_right (by decide), hn.b1 _ (by omega), show (2 * t + j - 2) % 2 = j % 2 by omega,
        show 2 * (4 + (2 * t + j - 2) / 2) + 1 = 8 * 1 + 2 * t + j / 2 by omega]
      exact nib_val m p (by omega) _

/-! ## The loop -/

/-- The groups' stores lie in the polynomial. -/
theorem wr4_frame {m : Mem} {P : Addr} {c₀ off : Nat} (hoff : off = 0 ∨ off = 64) (hc : c₀ + off / 4 + 16 ≤ 256)
    (X : Nat → BitVec 128) : Frame [pR P] m (wr4 m (coeffAddr P c₀) off X) := by
  have ha : ∀ d, 4 ∣ d → coeffAddr P c₀ + BitVec.ofNat 64 d = coeffAddr P (c₀ + d / 4) := fun d hd => by
    rw [show d = 4 * (d / 4) from (Nat.mul_div_cancel' hd).symm, coeffAddr_off, Nat.mul_div_cancel_left _ (by decide)]
  simp only [wr4]
  rw [ha off (by omega), ha (off + 16) (by omega), ha (off + 32) (by omega), ha (off + 48) (by omega)]
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (polyR_contains _ (by omega))).writeW
    (List.mem_singleton_self _) _ (polyR_contains _ (by omega))).writeW (List.mem_singleton_self _) _
    (polyR_contains _ (by omega))).writeW (List.mem_singleton_self _) _ (polyR_contains _ (by omega))

section
variable (s₀ : State)
abbrev bP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rsi
/-- The value of coefficient `k`. -/
abbrev val (k : Nat) : Nat := ((samplePolyCBD 2 (bytesAt s₀.mem (bP s₀) 128))[k]!).val
end

/-- After `i` groups of sixteen bytes. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = bP s₀ + BitVec.ofNat 64 (16 * i)
  rsi : s.gpr .rsi = coeffAddr (fP s₀) (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : Consts s
  frame : Frame [pR (fP s₀)] s₀.mem s.mem
  coeff : ∀ k < 32 * i, (coeffAt s.mem (fP s₀) k).toNat = val s₀ k

section
variable {s₀ : State} (hp : cbd2K.pre s₀)
include hp

/-- Coefficient `k` from its byte in the state `s`, read at `rdi`. -/
theorem val_eq {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ i s) {g t j : Nat} (hg : g < 2) (ht : t < 4)
    (hj : j < 4) :
    (cbdX ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (8 * g + 2 * t + j / 2))).toNat / 16 ^ (j % 2)) + 3329 -
        cbdY ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (8 * g + 2 * t + j / 2))).toNat / 16 ^ (j % 2))) % 3329 =
      val s₀ (32 * i + 16 * g + 4 * t + j) := by
  have hb : s.mem (s.gpr .rdi + BitVec.ofNat 64 (8 * g + 2 * t + j / 2)) =
      (bytesAt s₀.mem (bP s₀) 128).getD ((32 * i + 16 * g + 4 * t + j) / 2) 0 := by
    rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add, bytesAt_getD _ _ (by omega),
      show 16 * i + (8 * g + 2 * t + j / 2) = (32 * i + 16 * g + 4 * t + j) / 2 by omega]
    exact bytes_frame hI.frame (by simpa using hp.2.2.1) (by decide) _ (by omega)
  rw [val, samplePolyCBD2_val _ (by rw [n_eq]; omega), nibble, q_eq, ← hb,
    show (32 * i + 16 * g + 4 * t + j) % 2 = j % 2 by omega]

theorem step {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block cbd2Body) s fun s' => Inv s₀ (i + 1) s' ∧
      s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hrd : s.rd ++ s.wr = [⟨bP s₀, 128⟩, pR (fP s₀)] := by rw [hI.rd, hI.wr, hp.1, hp.2.1]; rfl
  have hwr : s.wr = [pR (fP s₀)] := by rw [hI.wr, hp.2.1]
  refine WP.mono (body_ok hI.c (by rw [hrd, hI.rdi]; exact ⟨⟨bP s₀, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun k hk => by
      rw [hwr, hI.rsi, show 16 * k = 4 * (4 * k) by omega, coeffAddr_off]
      exact ⟨_, List.mem_singleton_self _, polyR_contains _ (by omega)⟩))
    fun s' ⟨hc', rd', wr', di', si', cx', z', _, A₀, B₀, A₁, B₁, hn, hm⟩ => ⟨?_, cx', z'⟩
  refine ⟨?_, ?_, rd'.trans hI.rd, wr'.trans hI.wr, hc', ?_, fun k hk => ?_⟩
  · rw [di', hI.rdi, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.mul_succ]
  · rw [si', hI.rsi, show (128 : BitVec 64) = BitVec.ofNat 64 (4 * 32) from rfl, coeffAddr_off, Nat.mul_succ]
  · rw [hm, hI.rsi]
    exact hI.frame.trans ((wr4_frame (.inl rfl) (by omega) _).trans (wr4_frame (.inr rfl) (by omega) _))
  · rw [hm, hI.rsi, coeffAt_wr4 _ _ (.inr rfl) (by omega) _ (by omega),
      coeffAt_wr4 _ _ (.inl rfl) (by omega) _ (by omega)]
    by_cases hlo : k < 32 * i
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact hI.coeff k hlo
    · obtain ⟨g, hg, t, ht, j, hj, rfl⟩ : ∃ g < 2, ∃ t < 4, ∃ j < 4, k = 32 * i + 16 * g + 4 * t + j :=
        ⟨(k - 32 * i) / 16, by omega, (k - 32 * i) % 16 / 4, by omega, (k - 32 * i) % 4, by omega, by omega⟩
      have hv := grp_val hn hg ht hj
      rw [val_eq hp hi hI hg ht hj] at hv
      rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
      · rw [ite_eq_left rfl, ite_eq_left rfl] at hv
        rw [ite_eq_right (by omega), ite_eq_left (by omega),
          show (32 * i + 16 * 0 + 4 * t + j - (32 * i + 0 / 4)) / 4 = t by omega,
          show (32 * i + 16 * 0 + 4 * t + j - (32 * i + 0 / 4)) % 4 = j by omega, dword_grpX _ _ ht hj, hv]
      · rw [ite_eq_right (by decide), ite_eq_right (by decide)] at hv
        rw [ite_eq_left (by omega),
          show (32 * i + 16 * 1 + 4 * t + j - (32 * i + 64 / 4)) / 4 = t by omega,
          show (32 * i + 16 * 1 + 4 * t + j - (32 * i + 64 / 4)) % 4 = j by omega, dword_grpX _ _ ht hj, hv]

theorem correct : ∃ t s', Exec isa Impl.MlKem.X86_64.cbd2 s₀ t s' ∧ abiPreserved s₀ s' ∧ cbd2K.post s₀ s' := by
  have hL : WP isa Impl.MlKem.X86_64.cbd2 s₀ (Inv s₀ 8) := by
    unfold Impl.MlKem.X86_64.cbd2
    refine WP.seq (WP.mono (Q := fun (s : State) => Consts s ∧ s.gpr .rcx = BitVec.ofNat 64 8 ∧
        s.mem = s₀.mem ∧ Keep [.rax, .rcx] s₀ s) (by
          simp only [cbdConsts, bcast, dconsts]
          vrunm [consts_iff]
          refine ⟨pxor_self _, fun r hr => ?_, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]) fun s ⟨hc, hcx, hm0, k0⟩ => ?_)
    refine wp_countdown (cnt := .rcx) (N := 8) (by decide) (by decide) (Inv s₀)
      (fun i hi s hI _ => step hp hi hI) (fun _ h => h)
      ⟨?_, ?_, k0.2.1, k0.2.2, hc, by rw [hm0]; exact Frame.refl _ _, fun k hk => absurd hk (by omega)⟩ hcx
    · rw [k0.gpr (by decide)]; exact (BitVec.add_zero _).symm
    · rw [k0.gpr (by decide)]; exact (BitVec.add_zero _).symm
  obtain ⟨t, s', he, hI, hk⟩ := WP.keep [.rax, .rdi, .rsi, .rcx] hL (by decide)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hI.frame
    (by simpa using hp.2.2.2.2)), polyIs_of_toNat fun k hk => ?_⟩
  exact hI.coeff k (by rw [n_eq] at hk; omega)

end

end Cbd

theorem cbd2_correct (s : State) (hs : cbd2K.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.cbd2 s t s' ∧ abiPreserved s s' ∧ cbd2K.post s s' :=
  Cbd.correct hs

theorem cbd2_ct : ConstantTime isa cbd2K.pre cbd2K.pub Impl.MlKem.X86_64.cbd2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def cbd2Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1024⟩]

theorem cbd2_verified :
    Verified X86_64.target Impl.MlKem.X86_64.cbd2 (Spec.MlKem.cbd2Contract X86_64.abi) :=
  Verified.of_correct cbd2_correct cbd2_ct (by
    mlkem_implies [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, cbd2K, X86_64.abi,
      X86_64.argRegs] [cbd2Sat] using cbd2Sat)

end VG.Proof.MlKem.X86_64
