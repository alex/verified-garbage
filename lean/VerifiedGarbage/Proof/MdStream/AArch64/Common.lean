import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.MdStream.AArch64
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming Merkle–Damgård hash functions on AArch64: common lemmas

The contracts the generic proofs are written against, what they need of a hash
function's parameters (`Shape`) and of its compression function (`CalleeOk`),
the call of the compression function (`compressAt`), saving and restoring the
caller's registers, and weakest-precondition rules for the instruction forms
used (which the proofs of other AArch64 code use too).
-/

namespace VG.Proof.MdStream.AArch64

open VG VG.AArch64 VG.Impl.MdStream.AArch64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    Upd s (s.write sz d v) d (v.setWidth 64) :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

theorem Upd.write64 (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write .x d v) d v := by
  simpa using Upd.write s .x d v

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_mov {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (mov d n :: is)) s Q :=
  wp_addImm (by decide) fun s' u => k s' (by simpa using u)

theorem wp_subImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  WP.cons (s' := s.write .x d (imm.setWidth 64)) (by simp [exec]) (k _ (Upd.write64 _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n &&& s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n >>> sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n <<< sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_rev {d n : Reg}
    (k : ∀ s', Upd s s' d (rev64 (s.gpr n)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d n :: is)) s Q :=
  WP.cons (s' := s.write .x d (rev64 (s.gpr n))) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_rev32 {d n : Reg}
    (k : ∀ s', Upd s s' d ((rev32 ((s.gpr n).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev32 d n :: is)) s Q :=
  WP.cons rfl (k _ (Upd.write s .w d _))

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (((s.mem a).setWidth 32))) ?_ (k _ ?_)
  · simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
      Option.bind_some, State.load, hin, Option.map_some, read_one]
  · have := Upd.write s .w t ((s.mem a).setWidth 32)
    have e : ((s.mem a).setWidth 32).setWidth 64 = (s.mem a).setWidth 64 := by
      ext i hi; simp
    rwa [e] at this

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_str32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .x t (s.mem.readW a 64)) ?_ (k _ (Upd.write64 _ _ _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_ldr32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (s.mem.readW a 32)) ?_ (k _ (Upd.write s .w t _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

end

/-! ## Arithmetic -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

/-- `x >>> n`, of a number below 2⁶⁴. -/
theorem ofNat_shr {a n : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> n = BitVec.ofNat 64 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

/-- `x <<< n`, of a number whose product with `2 ^ n` is below 2⁶⁴. -/
theorem ofNat_shl {a n : Nat} (h : 2 ^ n * a < 2 ^ 64) :
    BitVec.ofNat 64 a <<< n = BitVec.ofNat 64 (2 ^ n * a) := by
  have ha : a ≤ 2 ^ n * a := Nat.le_mul_of_pos_left a (Nat.two_pow_pos n)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mul_comm, Nat.mod_eq_of_lt h]

/-- `x &&& (2 ^ n - 1)`. -/
theorem and_mask {n : Nat} (hn : n ≤ 16) (x : BitVec 64) :
    x &&& BitVec.setWidth 64 (BitVec.ofNat 16 (2 ^ n - 1)) = BitVec.ofNat 64 (x.toNat % 2 ^ n) := by
  have hp : 2 ^ n ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hn
  have h1 : 1 ≤ 2 ^ n := Nat.two_pow_pos n
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ n - 1 < 2 ^ 16 by omega), Nat.mod_eq_of_lt (show 2 ^ n - 1 < 2 ^ 64 by omega),
    Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt x.toNat (Nat.two_pow_pos n)
  omega

/-- A 16-bit immediate, zero-extended. -/
theorem setWidth_ofNat16 {n : Nat} (h : n < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega)]

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-- `eval` of the branch conditions. -/
theorem eval_zero (s : State) (r : Reg) : eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

/-! ## Memory and registers -/

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, toNat_ofNat_lt (by omega)]
  omega

/-- Registers that no instruction writes keep their values, as a postcondition. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-- The callee-saved registers our code never touches (but for `x30`, which
our calls change and the frame restores). -/
def untouched : List Reg := [.x25, .x26, .x27, .x28]

/-- A byte of a region disjoint from a frame is unchanged by the push. -/
theorem write_frame_apply {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) {x : Addr} (hx : R.Contains x 1) :
    m.write (sp - 16) 8 v x = m x :=
  Mem.write_apply fun h => hd x (by simp only [Region.Contains]; omega) hx

/-- The bytes of a region disjoint from a frame are unchanged by the push. -/
theorem write_frame_bytes {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m.write (sp - 16) 8 v (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  write_frame_apply hd (by
    simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega)

/-! ## Sizes -/

/-- The sizes the generic proofs support, checked for each hash function by
`decide`. -/
structure Dims (P : Params) : Prop where
  N : 0 < P.N ∧ P.N ≤ 64
  so : P.so % 8 = 0 ∧ P.so ≤ 256
  B : P.B = 64 ∨ P.B = 128
  L : 0 < P.L ∧ P.L ≤ 16

theorem Dims.pos {P : Params} (hd : Dims P) : 0 < P.B := by rcases hd.B with h | h <;> omega

/-- The shift count of the block size. -/
theorem Dims.log {P : Params} (hd : Dims P) :
    1 ≤ Impl.MdStream.AArch64.lg P ∧ Impl.MdStream.AArch64.lg P ≤ 7 ∧ 2 ^ Impl.MdStream.AArch64.lg P = P.B := by
  unfold Impl.MdStream.AArch64.lg
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

/-- `x >>> log₂ B`. -/
theorem Dims.shr {P : Params} (hd : Dims P) {a : Nat} (h : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> Impl.MdStream.AArch64.lg P = BitVec.ofNat 64 (a / P.B) := by
  rw [ofNat_shr h, hd.log.2.2]

/-- `x <<< log₂ B`. -/
theorem Dims.shl {P : Params} (hd : Dims P) {a : Nat} (h : P.B * a < 2 ^ 64) :
    BitVec.ofNat 64 a <<< Impl.MdStream.AArch64.lg P = BitVec.ofNat 64 (P.B * a) := by
  rw [ofNat_shl (by rw [hd.log.2.2]; exact h), hd.log.2.2]

/-- `x &&& (B - 1)`. -/
theorem Dims.and {P : Params} (hd : Dims P) (x : BitVec 64) :
    x &&& BitVec.setWidth 64 (BitVec.ofNat 16 (P.B - 1)) = BitVec.ofNat 64 (x.toNat % P.B) := by
  have := and_mask (n := Impl.MdStream.AArch64.lg P) (by have := hd.log; omega) x
  rwa [hd.log.2.2] at this

/-- `movz` of the block size. -/
theorem Dims.movB {P : Params} (hd : Dims P) :
    BitVec.setWidth 64 (BitVec.ofNat 16 P.B) = BitVec.ofNat 64 P.B :=
  setWidth_ofNat16 (by rcases hd.B with h | h <;> omega)

theorem Dims.mod {P : Params} (hd : Dims P) (n : Nat) : n % 2 ^ 64 % P.B = n % P.B := by
  rcases hd.B with h | h <;> rw [h] <;> omega

/-! ## Saving the caller's registers -/

theorem save_sep (b : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) : Mem.Sep (b + BitVec.ofNat 64 d) 8 (b + BitVec.ofNat 64 e) 8 := by
  exact Offset.sep _ h (by omega) (by omega)

theorem readW_writeW_save (m : Mem) (b : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (save_sep b hd he h) (by decide)

/-! Saves at `so + d`, with the conditions on the literal offsets `d`, `e`
alone, which `decide` discharges. -/
theorem readW_writeW_save_so {so : Nat} (hso : so ≤ 256) (m : Mem) (b : Addr) (v : BitVec 64)
    {d e : Nat} (hd : d ≤ 64) (he : e ≤ 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (b + BitVec.ofNat 64 (so + e)) v).readW (b + BitVec.ofNat 64 (so + d)) 64 =
      m.readW (b + BitVec.ofNat 64 (so + d)) 64 :=
  readW_writeW_save m b v (by omega) (by omega) (by omega)

theorem readW_writeW_save_so_l {so : Nat} (hso : so ≤ 256) (m : Mem) (b : Addr) (v : BitVec 64)
    {e : Nat} (he : e ≤ 64) (h : 8 ≤ e) :
    (m.writeW (b + BitVec.ofNat 64 (so + e)) v).readW (b + BitVec.ofNat 64 so) 64 =
      m.readW (b + BitVec.ofNat 64 so) 64 :=
  readW_writeW_save m b v (by omega) (by omega) (by omega)


section
variable (P : Params)

/-- The caller's callee-saved registers `g` are saved in the scratch space at `b`. -/
def Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (b + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The memory after saving `x19`–`x24` (values `g`) at `b + so …`. -/
def saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem :=
  (((((m.writeW (b + BitVec.ofNat 64 P.so) (g .x19)).writeW (b + BitVec.ofNat 64 (P.so + 8)) (g .x20)).writeW
    (b + BitVec.ofNat 64 (P.so + 16)) (g .x21)).writeW (b + BitVec.ofNat 64 (P.so + 24)) (g .x22)).writeW
    (b + BitVec.ofNat 64 (P.so + 32)) (g .x23)).writeW (b + BitVec.ofNat 64 (P.so + 40)) (g .x24)

theorem save_eq (b : Reg) : save P b = [.str .x .x19 b P.so, .str .x .x20 b (P.so + 8),
    .str .x .x21 b (P.so + 16), .str .x .x22 b (P.so + 24), .str .x .x23 b (P.so + 32),
    .str .x .x24 b (P.so + 40)] := rfl

end

section
variable {P : Params}

theorem saveMem_saved (hd : Dims P) (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Saved P b g (saveMem P m b g) := by
  have := hd.so
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [saveMem, Mem.readW_writeW_self64,
    readW_writeW_save_so this.2, readW_writeW_save_so_l this.2]

theorem saveMem_frame (hd : Dims P) (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b, P.so + 48⟩] m (saveMem P m b g) := by
  have := hd.so
  have c : ∀ d : Nat, d + 8 ≤ P.so + 48 → (⟨b, P.so + 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => contains_offset hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega))).writeW (List.mem_singleton_self _) _
    (c _ (by omega))).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c _ (by omega))

/-- The saved registers are outside the part of the scratch space the
compression function uses. -/
theorem saved_offset (hd : Dims P) {p : Reg × Nat} (hp : p ∈ saved P) : P.so ≤ p.2 ∧ p.2 + 8 ≤ P.so + 48 := by
  have := hd.so
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- Saving `x19`–`x24` with the scratch pointer in `b`. -/
theorem save_ok (hd : Dims P) {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hin : ∀ d, P.so ≤ d → d + 8 ≤ P.so + 48 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem P s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save P b ++ rest)) s Q := by
  have := hd.so
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_str (by omega) rfl (hin _ (by omega) (by omega)) fun s₁ g₁ => ?_
  refine wp_str (by omega) (by rw [g₁.gpr]) (by rw [g₁.wr]; exact hin _ (by omega) (by omega))
    fun s₂ g₂ => ?_
  refine wp_str (by omega) (by rw [g₂.gpr, g₁.gpr])
    (by rw [g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₃ g₃ => ?_
  refine wp_str (by omega) (by rw [g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₄ g₄ => ?_
  refine wp_str (by omega) (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₅ g₅ => ?_
  refine wp_str (by omega) (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₆ g₆ => ?_
  refine k s₆ (by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd]) (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr])
    (by rw [g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp]) ?_
  rw [g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem]
  simp only [saveMem, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]

/-- Restoring `x19`–`x24` from the save area at `scr`. -/
theorem restore_ok (hd : Dims P) {s : State} {scr : Addr} (h20 : s.gpr .x20 = scr)
    (hin : ∀ d, P.so ≤ d → d + 8 ≤ P.so + 48 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : Saved P scr g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved P, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ (saved P).map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (restore P)) s Q := by
  have := hd.so
  have v : ∀ r d, (r, d) ∈ saved P → s.mem.readW (scr + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  unfold restore
  refine wp_ldr (by omega) (by rw [h20]) (hin _ (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (by omega) (by rw [u₁.other _ (by decide), h20])
    (by rw [u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_ldr (by omega) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_ldr (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_ldr (by omega)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h20])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine wp_ldr (by omega)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin _ (by omega) (by omega))
    fun s₆ u₆ => WP.block_nil ?_
  have m5 : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₆ (fun p hp => ?_) (fun r hr => ?_) (by rw [u₆.mem, m5]) (by rw [u₆.rd, u₅.rd, u₄.rd,
    u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, v .x19 _ (by simp [saved])]
    · rw [u₆.gpr, m5, v .x20 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, v .x21 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        v .x22 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem,
        v .x23 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v .x24 _ (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other _ h2, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3, u₁.other _ h1]

/-- The callee-saved registers but `x30` are the caller's again once `restore`
has run and `untouched` were never written. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1)
    (hu : ∀ r ∈ untouched, s'.gpr r = s₀.gpr r) : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r := by
  intro r hr h30
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.x19, P.so) (by simp [saved])
  · exact hsv (.x20, P.so + 8) (by simp [saved])
  · exact hsv (.x21, P.so + 16) (by simp [saved])
  · exact hsv (.x22, P.so + 24) (by simp [saved])
  · exact hsv (.x23, P.so + 32) (by simp [saved])
  · exact hsv (.x24, P.so + 40) (by simp [saved])
  all_goals first | exact absurd rfl h30 | exact hu _ (by simp [untouched])

end

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The contract of the compression function: updates the hash value at
`x0` with the `x2` blocks at `x1`, with scratch space `x3` (`so` bytes). -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, P.N⟩
    let blocks : Region := ⟨s.gpr .x1, P.B * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, P.so⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    H.stateAt s'.mem (s.gpr .x0) =
      H.compressBlocks (H.stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- The contract of `update`: if the state at `x0` represents a message of
`x1` bytes (modulo 2⁶⁴) from any initial hash value, it then represents that
message followed by the `x3` bytes at `x2`. -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, P.N + P.B⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, P.so + 48⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- The contract of `finalize`: if the state at `x0` represents a message of
`x1` bytes, writes its final hash value to `x2` (`N` bytes). -/
def finK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, P.N + P.B⟩
    let out : Region := ⟨s.gpr .x2, P.N⟩
    let scratch : Region := ⟨s.gpr .x3, P.so + 48⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .x0) m → H.lenOk m.length →
    s.gpr .x1 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .x2) P.N = H.hash iv m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end

/-! ## What each hash function's own code must do -/

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `x22` at `x19 + N + B - L`, writing only `x9` and `x12`, and
`P.out` writes the digest of the hash value at `x19` to `x21`, writing only
`x9`. -/
structure Shape {P : Params} (H : Md P.B P.N P.L) : Prop where
  lenKeepsV : P.len.all VG.AArch64.keepsV = true
  outKeepsV : P.out.all VG.AArch64.keepsV = true
  len : ∀ s : State, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) (H.lenOf (s.gpr .x22))
  out : ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .x19) P.N → InRegions s.wr (s.gpr .x21) P.N →
    Region.Disjoint ⟨s.gpr .x19, P.N⟩ ⟨s.gpr .x21, P.N⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .x21) (H.digest (H.stateAt s.mem (s.gpr .x19)))

/-- What `compressAt` needs of the compression function it calls: that it is
correct, and pushes no frames. -/
structure CalleeOk {P : Params} (H : Md P.B P.N P.L) (code : Prog isa) : Prop where
  verified : ∀ s, (compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressK H).post s s'
  noFrames : code.noFrames = true
  keepsV : code.allInstrs VG.AArch64.keepsV = true

/-- The stream wrapper itself writes no vector registers. -/
theorem update_keepsV {P : Params} {name : String} {code : Prog isa}
    (h : code.allInstrs VG.AArch64.keepsV = true) :
    (update P name code).allInstrs VG.AArch64.keepsV = true := by
  simp [update, updateMain, updateStart, updateBody, fill, copyBody, direct, lg,
    compressN, compressWith, save, saved, restore, mov, Code.allInstrs,
    VG.AArch64.keepsV, vdstOf, h]

/-- The finalizer adds only the parameterized length and digest stores. -/
theorem finalize_keepsV {P : Params} {H : Md P.B P.N P.L} {name : String} {code : Prog isa}
    (hs : Shape H) (h : code.allInstrs VG.AArch64.keepsV = true) :
    (finalize P name code).allInstrs VG.AArch64.keepsV = true := by
  rw [Code.allInstrs_eq] at h ⊢
  simp [finalize, finalizeMain, finalizeStart, finalizeBody, zeroBody, lg,
    compressAt, compressWith, save, saved, restore, mov, instrs,
    VG.AArch64.keepsV, vdstOf, h, hs.lenKeepsV, hs.outKeepsV]

/-! ## The compression function -/

theorem one_toNat : (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 := rfl

/-- `n` sets `x2` to `v`, given that only `x0` changed since the state `s`. -/
def SetsN (n : Instr) (s : State) (v : BitVec 64) : Prop :=
  ∀ (s₁ : State) (is : List Instr) (Q : State → Prop), (∀ r, r ≠ .x0 → s₁.gpr r = s.gpr r) →
    (∀ s', Upd s₁ s' .x2 v → WP isa (.block is) s' Q) → WP isa (.block (n :: is)) s₁ Q

theorem setsN_one (s : State) : SetsN (.movz .x .x2 1 0) s (BitVec.setWidth 64 (1 : BitVec 16)) :=
  fun _ _ _ _ k => wp_movz k

theorem setsN_x10 (s : State) : SetsN (mov .x2 .x10) s (s.gpr .x10) :=
  fun _ _ _ he k => wp_mov fun s' u => k s' (by rwa [he _ (by decide)] at u)

/-- Compressing the `k` blocks at `x1` (their number set in `x2` by `n`) into
the hash value at `x19`, with scratch space at `x20`: the callee-saved
registers other than `x30` are kept. -/
theorem compressWith_ok {P : Params} {H : Md P.B P.N P.L} {n : Instr} {s : State} {v : BitVec 64}
    (hn : SetsN n s v) {k : Nat} (hk : v.toNat = k) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {st scr src : Addr}
    (h19 : s.gpr .x19 = st) (h20 : s.gpr .x20 = scr) (h1 : s.gpr .x1 = src)
    (d₁ : Region.Disjoint ⟨st, P.N⟩ ⟨scr, P.so⟩) (d₂ : Region.Disjoint ⟨src, P.B * k⟩ ⟨st, P.N⟩)
    (d₃ : Region.Disjoint ⟨src, P.B * k⟩ ⟨scr, P.so⟩)
    (hc : Covers [⟨src, P.B * k⟩, ⟨st, P.N⟩, ⟨scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, P.N⟩, ⟨scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compressBlocks (H.stateAt s.mem st) s.mem src k → Q s') :
    WP isa (compressWith n name code) s Q := by
  unfold compressWith
  refine WP.seq (wp_mov fun s₁ u₁ => hn s₁ _ _ u₁.other fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have e0 : s₃.gpr .x0 = st := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h19]
  have e1 : s₃.gpr .x1 = src := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h1]
  have e2 : s₃.gpr .x2 = v := by
    rw [u₃.other _ (by decide), u₂.gpr]
  have e3 : s₃.gpr .x3 = scr := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h20]
  have keep : ∀ r ∈ preserved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have c0 : s₃.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans e0
  have c1 : s₃.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans e1
  have c2 : s₃.callEntry.gpr .x2 = v := (State.callEntry_gpr _ (by decide)).trans e2
  have c3 : s₃.callEntry.gpr .x3 = scr := (State.callEntry_gpr _ (by decide)).trans e3
  refine WP.call (k := compressK H) hf.verified
    (rd := [⟨src, P.B * k⟩]) (wr := [⟨st, P.N⟩, ⟨scr, P.so⟩]) ?_ ?_ ?_ ?_ hf.noFrames
  · simp only [compressK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, hk]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₃, wr₃]; simpa using hc
  · rw [wr₃]; exact hw
  · intro s' hrd hwr hsp hf' hcs _ hpost
    simp only [compressK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, hk, m₃] at hpost
    exact hQ s' (hrd.trans rd₃) (hwr.trans wr₃) (fun r hr h30 => (hcs r hr h30).trans (keep r hr))
      (hsp.trans sp₃) (m₃ ▸ hf') hpost

/-- Compressing the block at `x1` into the hash value at `x19`, with scratch
space at `x20`: the callee-saved registers other than `x30` are kept. -/
theorem compressAt_ok {P : Params} {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s : State} {st scr src : Addr}
    (h19 : s.gpr .x19 = st) (h20 : s.gpr .x20 = scr) (h1 : s.gpr .x1 = src)
    (d₁ : Region.Disjoint ⟨st, P.N⟩ ⟨scr, P.so⟩) (d₂ : Region.Disjoint ⟨src, P.B⟩ ⟨st, P.N⟩)
    (d₃ : Region.Disjoint ⟨src, P.B⟩ ⟨scr, P.so⟩)
    (hc : Covers [⟨src, P.B⟩, ⟨st, P.N⟩, ⟨scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, P.N⟩, ⟨scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) → Q s') :
    WP isa (compressAt name code) s Q :=
  compressWith_ok (setsN_one s) one_toNat hf h19 h20 h1 d₁ (by rwa [Nat.mul_one]) (by rwa [Nat.mul_one])
    (by rwa [Nat.mul_one]) hw
    fun s' hrd hwr hcs hsp hf' hs => hQ s' hrd hwr hcs hsp hf' (by rw [hs, Md.compressBlocks_one])

end VG.Proof.MdStream.AArch64
