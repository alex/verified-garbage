import VerifiedGarbage.Proof.Blake2.Arm.Stream.Call
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Streaming BLAKE2 on ARMv7: common lemmas

The contracts the proofs of `init`, `update` and `finalize` are written
against (for any word size, as on AArch64:
`Proof/Blake2/AArch64/Stream/Common.lean`), weakest-precondition rules for the
instructions the MD streaming proofs do not cover, 64-bit counts in register
pairs, the number of buffered bytes, the loops copying bytes into the buffer
and zeroing it, and saving and restoring the caller's registers.
-/

namespace VG.Proof.Blake2

open VG.Arm VG.Spec.Blake2

/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

section
variable {w : Nat} (P : Params w)

/-- ARMv7 contract for `init(state = r0, outlen = r1, key = r2, keylen =
r3)`. -/
def initArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩
    let key : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    s.rd = [key] ∧ s.wr = [state] ∧ key.Disjoint state ∧
    (s.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ P.maxBytes ∧ (s.gpr .r3).toNat ≤ P.maxBytes
  post s s' := Spec.Blake2.Repr P (Spec.Blake2.init P (s.gpr .r1).toNat (s.gpr .r3).toNat) s'.mem
    (State.addr (s.gpr .r0)) (keyBlock w (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

/-- ARMv7 contract for `update(state = r0, count = r2:r3, data = [sp],
len = [sp, #4], scratch = [sp, #8])`, which pushes 16 bytes of stack. -/
def updateArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 576⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (Arm.Stream.below s).Disjoint state ∧ (Arm.Stream.below s).Disjoint data ∧
    (Arm.Stream.below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 576 ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (State.addr (s.gpr .r0)) d →
    countArm s = BitVec.ofNat 64 d.length → d.length + (stackArg s 1).toNat < 2 ^ 64 →
    Spec.Blake2.Repr P h0 s'.mem (State.addr (s.gpr .r0))
      (d ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

/-- ARMv7 contract for `finalize(state = r0, count = r2:r3, out = [sp],
scratch = [sp, #4])`, which pushes 16 bytes of stack. -/
def finalizeArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩
    let out : Region := ⟨State.addr (stackArg s 0), bufOff w⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 576⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (Arm.Stream.below s).Disjoint state ∧ (Arm.Stream.below s).Disjoint out ∧
    (Arm.Stream.below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + bufOff w ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 576 ≤ 2 ^ 32 ∧ 16 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (State.addr (s.gpr .r0)) d → d.length < 2 ^ 64 →
    countArm s = BitVec.ofNat 64 d.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) (bufOff w) = finalHash P h0 d
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end

namespace Arm.Stream

open VG.Impl.Blake2.Arm.Stream (N B lbb saved save restore)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd WP.cons op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub
  wp_and wp_orr wp_subs wp_cmp wp_ldr wp_str wp_ldrb wp_strb wp_ldrSp ofNat_beq_zero sub_ofNat cmp0 eval_eq
  eval_ne)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

variable {w : Nat} {P : Params w}

/-! ## Sizes -/

/-- The word sizes, and keys fitting a block. -/
structure Ok (P : Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega

/-- The sizes, all small. -/
theorem Ok.len (h : Ok P) : bufOff w + blockBytes w ≤ 192 ∧ bufOff w ≤ 64 ∧ 32 ≤ bufOff w ∧
    bufOff w % 4 = 0 ∧ 64 ≤ blockBytes w := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.lbb (h : Ok P) : 1 ≤ lbb w ∧ lbb w ≤ 31 ∧ 2 ^ lbb w = blockBytes w := by
  rcases h.w with rfl | rfl <;> decide

theorem N_eq : N w = bufOff w := rfl
theorem B_eq : B w = blockBytes w := rfl

theorem Ok.encB (h : Ok P) : encodable (BitVec.ofNat 32 (B w)) = true := by
  rcases h.w with rfl | rfl <;> decide
theorem Ok.encB1 (h : Ok P) : encodable (BitVec.ofNat 32 (B w - 1)) = true := by
  rcases h.w with rfl | rfl <;> decide
theorem Ok.encN (h : Ok P) : encodable (BitVec.ofNat 32 (N w)) = true := by
  rcases h.w with rfl | rfl <;> decide

/-! ## Instructions the MD streaming proofs do not cover -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem Upd.adds (s : State) (d : Reg) (x y v : BitVec 32) : Upd s ((addFlags s x y).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, addFlags, h], rfl, rfl, rfl, rfl⟩

theorem wp_adds {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → s'.c = decide (2 ^ 32 ≤ (s.gpr n).toNat + y.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.adds d n o :: is)) s Q :=
  WP.cons (s' := (addFlags s (s.gpr n) y).setReg d (s.gpr n + y)) (by simp [exec, ho])
    (k _ (Upd.adds _ _ _ _ _) rfl)

theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → s'.c = s.c → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0))) (by simp [exec, ho])
    (k _ (MdStream.Arm.Upd.setReg _ _ _) rfl)

theorem wp_eor {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (MdStream.Arm.Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  WP.cons (s' := s.setReg d (imm.setWidth 32)) rfl (k _ (MdStream.Arm.Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl
    (k _ (MdStream.Arm.Upd.setReg _ _ _))

end

theorem op2_ror {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .ror n).eval s = some ((s.gpr r).rotateRight n) := by
  simp [Op2.eval, h]

/-! ## 64-bit counts in register pairs -/

theorem toNat_append32 (hi lo : BitVec 32) : (hi ++ lo : BitVec 64).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- `adds lo, lo, y` then `adc hi, hi, #0` adds `y` to `hi:lo`. -/
theorem add64 (lo hi y : BitVec 32) :
    ((hi + 0 + (if decide (2 ^ 32 ≤ lo.toNat + y.toNat) = true then 1 else 0)) ++ (lo + y) : BitVec 64) =
      (hi ++ lo) + y.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have hl := lo.isLt; have hh := hi.isLt; have hy := y.isLt
  rw [show hi + 0 = hi from BitVec.add_zero _]
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  have e0 : (0 : BitVec 32).toNat = 0 := rfl
  by_cases hc : 2 ^ 32 ≤ lo.toNat + y.toNat
  · simp only [hc, decide_true, ite_true, toNat_append32, BitVec.toNat_add, BitVec.toNat_setWidth, e1]
    omega
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false, toNat_append32, BitVec.toNat_add,
      BitVec.toNat_setWidth, e0]
    omega

/-- The low word of a 64-bit number. -/
def lo32 (x : Nat) : BitVec 32 := BitVec.ofNat 32 x
/-- The high word of a 64-bit number (below 2⁶⁴). -/
def hi32 (x : Nat) : BitVec 32 := BitVec.ofNat 32 (x / 2 ^ 32)

/-- Adding `y < 2³²` to a count `x` (modulo 2⁶⁴) in a register pair. -/
theorem add64_ofNat {lo hi : BitVec 32} {x y : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hy : y < 2 ^ 32) :
    ((hi + 0 + (if decide (2 ^ 32 ≤ lo.toNat + (BitVec.ofNat 32 y).toNat) = true then 1 else 0)) ++
      (lo + BitVec.ofNat 32 y) : BitVec 64) = BitVec.ofNat 64 (x + y) := by
  rw [add64, h, BitVec.ofNat_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The low word of a count in a register pair. -/
theorem lo_of_pair {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x) :
    lo = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat] at e
  rw [BitVec.toNat_ofNat]
  have := lo.isLt; have := hi.isLt
  omega

/-- A count in a register pair is zero iff the OR of its words is. -/
theorem or_beq_zero {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) : ((lo ||| hi) - 0 == 0) = decide (x = 0) := by
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
  rw [show (lo ||| hi) - 0 = lo ||| hi from BitVec.sub_zero _]
  by_cases hx0 : x = 0
  · have h1 : lo = 0 := BitVec.eq_of_toNat_eq (by show lo.toNat = 0; omega)
    have h2 : hi = 0 := BitVec.eq_of_toNat_eq (by show hi.toNat = 0; omega)
    simp [h1, h2, hx0]
  · rw [decide_eq_false hx0, beq_eq_false_iff_ne]
    intro h0
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h0
    rw [h1, h2] at e
    rw [BitVec.toNat_zero] at e
    omega

/-! ## The number of bytes in the buffer -/

/-- `x & (B - 1)`: the remainder modulo the block size. -/
theorem mask_mod (hP : Ok P) (x : BitVec 32) :
    x &&& BitVec.ofNat 32 (B w - 1) = BitVec.ofNat 32 (x.toNat % blockBytes w) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  rcases hP.w with rfl | rfl
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (B 64 - 1) % 2 ^ 32 = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 64 = 2 ^ 7 from rfl]
    omega
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (B 32 - 1) % 2 ^ 32 = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 32 = 2 ^ 6 from rfl]
    omega

/-- `x >>> lbb`: division by the block size. -/
theorem shr_ofNat (hP : Ok P) {m : Nat} (h : m < 2 ^ 32) :
    BitVec.ofNat 32 m >>> lbb w = BitVec.ofNat 32 (m / blockBytes w) := by
  rw [MdStream.Arm.ofNat_shr h, hP.lbb.2.2]

/-- `((count - 1) mod B) + 1`, from the low word of the count. -/
theorem bufLen_lo (hP : Ok P) {x : Nat} (hx : x ≠ 0) :
    ((BitVec.ofNat 32 x - 1) &&& BitVec.ofNat 32 (B w - 1)) + 1 = BitVec.ofNat 32 (bufLen w x) := by
  have hd : blockBytes w ∣ 2 ^ 32 := by rcases hP.w with rfl | rfl <;> decide
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), mask_mod hP,
    BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hd, ← BitVec.ofNat_add]
  simp only [bufLen, hx, ite_false]

/-- A pointer plus an offset that does not wrap. -/
theorem toNat_add_ofNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) :
    (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

/-! ## Copying bytes into the buffer -/

/-- The copy loop's state after `j` of `k` bytes, from `s₀`: the bytes go from
`src` to `dst`. -/
structure CopyI (s₀ : State) (dst : Addr) (src : BitVec 32) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  r6 : s.gpr .r6 = src + BitVec.ofNat 32 j
  r8 : s.gpr .r8 = BitVec.ofNat 32 (r + j)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .r12 → x ≠ .r1 → x ≠ .r6 → x ≠ .r8 → x ≠ .r11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem (State.addr src) k).take j)

theorem setWidth_byte (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  ext i hi; simp

theorem ne_iff (s : State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k == 0)) (hk : k < 2 ^ 32) :
    isa.eval .ne s = some (decide (k ≠ 0)) := by
  show VG.Arm.eval .ne s = _
  rw [eval_ne, h, ofNat_beq_zero hk]
  simp

theorem eq_iff (s : State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k == 0)) (hk : k < 2 ^ 32) :
    isa.eval .eq s = some (decide (k = 0)) := by
  show VG.Arm.eval .eq s = _
  rw [eval_eq, h, ofNat_beq_zero hk]

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-- The loop copying `k ≥ 1` bytes from `src` (at `r6`) to the buffer of the
state at `st` (in `r4`), from byte `r` on (in `r8`). -/
theorem copyLoop_ok {s₀ : State} {st src : BitVec 32} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hfit : st.toNat + bufOff w + r + k ≤ 2 ^ 32) (hsfit : src.toNat + k ≤ 2 ^ 32)
    (hr4 : s₀.gpr .r4 = st) (hr6 : s₀.gpr .r6 = src) (hr8 : s₀.gpr .r8 = BitVec.ofNat 32 r)
    (hr11 : s₀.gpr .r11 = BitVec.ofNat 32 k)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (State.addr src + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr st + BitVec.ofNat 64 (bufOff w + r), k⟩)
    {Q : State → Prop}
    (hQ : ∀ s, CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k k s → Q s) :
    WP isa (Impl.Blake2.Arm.Stream.copyLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hr6], by rw [hr8, Nat.add_zero], by rw [hr11, Nat.sub_zero],
      fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (State.addr src + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (State.addr src + BitVec.ofNat 64 j) = s₀.mem (State.addr src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (contains_prefix (k := k) _ (by simp; omega))).bytes
      (R := ⟨State.addr src, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  -- The byte written.
  have hout : InRegions s.wr (State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  have hr4' : s.gpr .r4 = st := by
    rw [h.other .r4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4]
  refine wp_ldrb (a := State.addr src + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r6, BitVec.add_zero, addr_add (by omega)]) hin fun s₁ u₁ => ?_
  refine wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [N_eq]; omega) ?_ (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hr4', h.r8, N_eq, BitVec.add_assoc,
      ← BitVec.ofNat_add, addr_add (by omega), Offset.add_add]
    congr 2; omega
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have hr11' : s₆.gpr .r11 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r11, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega),
      Nat.sub_sub]
  have hI : CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k (j + 1) s₆ := by
    refine ⟨by omega, ?_, ?_, hr11', fun x h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.r6, BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        ← BitVec.ofNat_add]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.r8, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add,
        Nat.add_assoc]
    · rw [u₆.other x h5, u₅.other x h4, u₄.other x h3, g₃.gpr, u₂.other x h2, u₁.other x h1,
        h.other x h1 h2 h3 h4 h5]
    · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
    · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
    · have hj' : j < (bytesAt s₀.mem (State.addr src) k).length := by rw [bytesAt_length]; omega
      have hl : (List.take j (bytesAt s₀.mem (State.addr src) k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, setWidth_byte]
      congr 1
      simp [bytesAt]
  have hz : isa.eval .ne s₆ = some (decide (k - (j + 1) ≠ 0)) :=
    ne_iff s₆ (by rw [z₆, ← u₆.gpr, hr11']) (by omega)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## Zeroing the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (q : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  r8 : s.gpr .r8 = BitVec.ofNat 32 (r + j)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .r1 → x ≠ .r8 → x ≠ .r11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem q (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes of the buffer of the state at `st` (in
`r4`), from byte `r` on (in `r8`), with `r12 = 0`. -/
theorem zeroLoop_ok {s₀ : State} {st : BitVec 32} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hfit : st.toNat + bufOff w + r + k ≤ 2 ^ 32)
    (hr4 : s₀.gpr .r4 = st) (hr8 : s₀.gpr .r8 = BitVec.ofNat 32 r) (hr11 : s₀.gpr .r11 = BitVec.ofNat 32 k)
    (hr12 : s₀.gpr .r12 = 0)
    (hdst : ∀ i < k, InRegions s₀.wr (State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop}
    (hQ : ∀ s, ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k k s → Q s) :
    WP isa (Impl.Blake2.Arm.Stream.zeroLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by rw [hr8, Nat.add_zero], by rw [hr11, Nat.sub_zero],
      fun _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.replicate_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hr4' : s.gpr .r4 = st := by rw [h.other .r4 (by decide) (by decide) (by decide), hr4]
  refine wp_add (op2_reg _ _) fun s₁ u₁ =>
    wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [N_eq]; omega) ?_ (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hr4', h.r8, N_eq, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega), Offset.add_add]
    congr 2; omega
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ =>
    WP.block_nil ?_
  have hr11' : s₄.gpr .r11 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r11,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have hI : ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k (j + 1) s₄ := by
    refine ⟨by omega, ?_, hr11', fun x h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r8,
        show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3]
    · rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide),
        h.other .r12 (by decide) (by decide) (by decide), hr12, h.mem,
        List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate]
      rfl
  have hz : isa.eval .ne s₄ = some (decide (k - (j + 1) ≠ 0)) :=
    ne_iff s₄ (by rw [z₄, ← u₄.gpr, hr11']) (by omega)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## Saving and restoring the caller's registers -/

/-- The caller's registers `g` are saved in the scratch space at `b`. -/
def Saved (b : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (b + BitVec.ofNat 64 p.2) 32 = g p.1

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 4 ≤ 548 := by decide

theorem saved_nodup : (saved.map Prod.fst).Nodup := by decide

set_option simprocs false in
theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 32) :
    Saved b g (MdStream.Arm.saveMem m b g saved) := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [saved, MdStream.Arm.saveMem, Mem.readW_writeW_self32,
    MdStream.Arm.readW_writeW_save]

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 32) :
    Frame [⟨b, 576⟩] m (MdStream.Arm.saveMem m b g saved) :=
  MdStream.Arm.saveMem_frame m b g (by decide) saved fun p hp => by
    have := saved_bound p hp; omega

/-- Saving `r4`–`r11` and `lr` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + 576 ≤ 2 ^ 32)
    (hin : ∀ d, 512 ≤ d → d + 4 ≤ 548 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = MdStream.Arm.saveMem s.mem (State.addr (s.gpr b)) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  refine MdStream.Arm.saveList_ok saved s Q (fun p hp => ?_) k
  have := saved_bound p hp
  exact ⟨by omega, by omega, hin _ this.1 this.2⟩

/-- Restoring `r4`–`r11` and `lr` from the save area at `scratch` (in `r5`). -/
theorem restore_ok {s : State} {scr : BitVec 32} (h5 : s.gpr .r5 = scr) (hfit : scr.toNat + 576 ≤ 2 ^ 32)
    (hin : ∀ d, 512 ≤ d → d + 4 ≤ 548 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
    (g : Reg → BitVec 32) (hsv : Saved (State.addr scr) g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  unfold restore
  rw [← List.append_nil (saved.map _)]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have h3 : s₁.gpr .r3 = scr := by rw [u₁.gpr, h5]
  refine MdStream.Arm.restoreList_ok saved s₁ Q saved_nodup (fun p hp => ?_)
    fun s' ho _ hm hrd hwr hsp => WP.block_nil (k s' (fun p hp => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd)
      (hwr.trans u₁.wr) (hsp.trans u₁.sp))
  · have := saved_bound p hp
    have hne : p.1 ≠ .r3 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h3, u₁.rd, u₁.wr]
    exact ⟨hne, by omega, by omega, hin _ this.1 this.2⟩
  · rw [ho p hp, h3, u₁.mem, hsv p hp]

/-- The callee-saved registers are the caller's again once `restore` has run. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) :
    ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.r4, 512) (by simp [saved])
  · exact hsv (.r5, 516) (by simp [saved])
  · exact hsv (.r6, 520) (by simp [saved])
  · exact hsv (.r7, 524) (by simp [saved])
  · exact hsv (.r8, 528) (by simp [saved])
  · exact hsv (.r9, 532) (by simp [saved])
  · exact hsv (.r10, 536) (by simp [saved])
  · exact hsv (.r11, 540) (by simp [saved])
  · exact hsv (.lr, 544) (by simp [saved])

/-! ## The streaming state -/

/-- `Repr` depends only on the bytes of the streaming state. -/
theorem repr_congr (hP : Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  rw [repr_iff P hP.pos] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega), ?_⟩
  rw [← h5]
  refine bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega)

/-- `ReprR` depends only on the bytes of the streaming state. -/
theorem reprR_congr {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte} {r : Nat}
    (hs : stateAt w mem' p = stateAt w mem p)
    (hb : ∀ i < r, mem' (p + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) =
      mem (p + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i))
    (h : ReprR P h0 mem p d r) : ReprR P h0 mem' p d r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, by rw [hs, h4], by rw [← h5]; exact bytesAt_congr hb⟩

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact WriteBytes.writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

end Arm.Stream

end VG.Proof.Blake2
