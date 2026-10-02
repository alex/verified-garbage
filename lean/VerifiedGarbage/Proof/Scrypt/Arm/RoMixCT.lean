import VerifiedGarbage.Proof.Scrypt.RoMix
import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Scrypt.Arm.BlockMixVerified
import Mathlib.Tactic.DefEqTransformations
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.Arm.Lit

/-!
# scryptROMix on 32-bit ARM: the precondition

The regions the function works on, and `BlockMixSpec`: what a call of
`vg_scrypt_blockmix` does (the verified one meets it:
`Proof/Scrypt/Arm/RoMixCT.lean`). As on AArch64
(`Proof/Scrypt/AArch64/RoMixCT.lean`), with 32-bit pointers, whose zero
extensions (`State.addr`) address memory and do not wrap.
-/

namespace VG.Proof.Scrypt.Arm.RoMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt blockMix integerify leNat)
open VG.Proof.Scrypt (bytesAt_add' bytesAt_length' leNat_append leNat_bytesAt blk_bytesAt')
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem)

/-! ## What a call of `vg_scrypt_blockmix` does -/

/-- A call of `c` writes scryptBlockMix of the `128 r` bytes at `r0` to `r2`,
with the 128 bytes at the stack argument as working space. -/
def BlockMixSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (src dst scr : BitVec 32) (r : Nat), s.gpr .r0 = src →
    s.gpr .r1 = BitVec.ofNat 32 r → s.gpr .r2 = dst → s.gpr .r3 = BitVec.ofNat 32 r →
    stackArg s 0 = scr → 0 < r → 128 * r < 2 ^ 32 →
    Region.Disjoint ⟨State.addr dst, 128 * r⟩ ⟨State.addr scr, 128⟩ →
    Region.Disjoint ⟨State.addr src, 128 * r⟩ ⟨State.addr dst, 128 * r⟩ →
    Region.Disjoint ⟨State.addr src, 128 * r⟩ ⟨State.addr scr, 128⟩ →
    Region.Disjoint ⟨stackArgAddr s 0, 4⟩ ⟨State.addr dst, 128 * r⟩ →
    Region.Disjoint ⟨stackArgAddr s 0, 4⟩ ⟨State.addr scr, 128⟩ →
    src.toNat + 128 * r ≤ 2 ^ 32 → dst.toNat + 128 * r ≤ 2 ^ 32 → scr.toNat + 128 ≤ 2 ^ 32 →
    s.sp.toNat + 4 ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) (State.addr src) (128 * r) →
    InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 → InRegions s.wr (State.addr dst) (128 * r) →
    InRegions s.wr (State.addr scr) 128 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
        (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
        Frame [⟨State.addr dst, 128 * r⟩, ⟨State.addr scr, 128⟩] s.mem s'.mem →
        bytesAt s'.mem (State.addr dst) (128 * r) =
          blockMix r (bytesAt s.mem (State.addr src) (128 * r)) → Q s') →
    WP isa (.call "vg_scrypt_blockmix" c) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : BitVec 32 := s₀.gpr .r0
abbrev rr : Nat := (s₀.gpr .r1).toNat
abbrev vP : BitVec 32 := s₀.gpr .r2
abbrev vl : Nat := (s₀.gpr .r3).toNat
abbrev sc : BitVec 32 := stackArg s₀ 0
/-- `N`. -/
abbrev NN : Nat := vl s₀ / rr s₀
abbrev bA : Addr := State.addr (bP s₀)
abbrev vA : Addr := State.addr (vP s₀)
abbrev scA : Addr := State.addr (sc s₀)
abbrev bR : Region := ⟨bA s₀, rr s₀ * 128⟩
abbrev vR : Region := ⟨vA s₀, vl s₀ * 128⟩
abbrev scR : Region := ⟨scA s₀, (rr s₀ + 2) * 128⟩
/-- The stack arguments. -/
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) (128 * rr s₀)
/-- `V[i]`. -/
abbrev vAt (i : Nat) : Addr := vA s₀ + BitVec.ofNat 64 (128 * rr s₀ * i)
/-- `V[i]`, as the pointer the code computes. -/
abbrev vAt32 (i : Nat) : BitVec 32 := vP s₀ + BitVec.ofNat 32 (128 * rr s₀ * i)
/-- `T`. -/
abbrev tP : Addr := scA s₀ + BitVec.ofNat 64 192
abbrev tP32 : BitVec 32 := sc s₀ + BitVec.ofNat 32 192

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ rmSaved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [bR s₀, vR s₀, scR s₀]
  b_v : (bR s₀).Disjoint (vR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  v_s : (vR s₀).Disjoint (scR s₀)
  a_b : (argR s₀).Disjoint (bR s₀)
  a_v : (argR s₀).Disjoint (vR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  v_nw : (vP s₀).toNat + vl s₀ * 128 ≤ 2 ^ 32
  s_nw : (sc s₀).toNat + (rr s₀ + 2) * 128 ≤ 2 ^ 32
  sp_nw : s₀.sp.toNat + 8 ≤ 2 ^ 32
  pos : 0 < rr s₀
  vl_eq : vl s₀ = rr s₀ * NN s₀
  pow : (NN s₀).isPowerOfTwo

theorem pre_of {s₀ : State} (h : Proof.Scrypt.roMixArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp only [h16] at h2 h4 h5 h8 h11
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ?_, h15⟩
  exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h14)).symm

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem NN_pos : 0 < NN s₀ := by
  obtain ⟨e, he⟩ := hp.pow
  rw [he]; exact Nat.two_pow_pos _

theorem vl_mul : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by
  rw [hp.vl_eq, Nat.mul_comm, ← Nat.mul_assoc]

/-- `v` is not the whole address space, since `scratch` is not in it. -/
theorem v_lt : 128 * rr s₀ * NN s₀ < 2 ^ 32 := by
  rw [← vl_mul hp]
  by_contra hc
  have hv : vA s₀ = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_toNat]; show _ = 0; have := hp.v_nw; omega
  have hs : (scA s₀).toNat < 2 ^ 32 := by rw [addr_toNat]; exact (sc s₀).isLt
  refine hp.v_s (scA s₀) ?_ ?_
  · show (scA s₀ - vA s₀).toNat + 1 ≤ vl s₀ * 128
    rw [hv, show (0 : Addr) = 0#64 from rfl, BitVec.sub_zero]; omega
  · show (scA s₀ - scA s₀).toNat + 1 ≤ (rr s₀ + 2) * 128
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega

theorem r_lt : 128 * rr s₀ < 2 ^ 32 := by
  have := v_lt hp
  have := NN_pos hp
  have : 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem NN_lt : NN s₀ < 2 ^ 32 := by
  have := v_lt hp
  have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
  omega

omit hp in
theorem v_le {i : Nat} (hi : i < NN s₀) : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-- `V[i]` is in `v`. -/
theorem vAt_sub {i : Nat} (hi : i < NN s₀) : Region.Sub ⟨vAt s₀ i, 128 * rr s₀⟩ (vR s₀) := by
  have := v_lt hp
  have := v_le hi
  show Region.Sub ⟨vA s₀ + BitVec.ofNat 64 (128 * rr s₀ * i), 128 * rr s₀⟩ ⟨vA s₀, vl s₀ * 128⟩
  exact sub_off (by rw [vl_mul hp]; omega) (by omega)

theorem vAt_disj {i k : Nat} (hi : i < NN s₀) (hk : k < NN s₀) (hik : i ≠ k) :
    Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ ⟨vAt s₀ k, 128 * rr s₀⟩ := by
  have := v_lt hp
  have h1 := v_le hi
  have h2 := v_le hk
  refine disj_off _ ?_ (by omega) (by omega) (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · left; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
  · right; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h

/-- `V[i]` as an address. -/
theorem vAt_addr {i : Nat} (hi : i < NN s₀) : State.addr (vAt32 s₀ i) = vAt s₀ i := by
  have := v_lt hp
  have := v_le hi
  have := hp.v_nw
  have := vl_mul hp
  have := hp.pos
  exact addr_add (by omega)

theorem vAt_nw {i : Nat} (hi : i < NN s₀) : (vAt32 s₀ i).toNat + 128 * rr s₀ ≤ 2 ^ 32 := by
  have := v_lt hp
  have := v_le hi
  have := hp.v_nw
  have := vl_mul hp
  have := hp.pos
  rw [toNat_add32 (by omega)]
  omega

/-- `T` is in `scratch`. -/
theorem t_sub : Region.Sub ⟨tP s₀, 128 * rr s₀⟩ (scR s₀) := by
  have := hp.s_nw
  exact sub_off (by omega) (by omega)

theorem t_addr : State.addr (tP32 s₀) = tP s₀ := addr_add (by have := hp.s_nw; omega)

theorem t_nw : (tP32 s₀).toNat + 128 * rr s₀ ≤ 2 ^ 32 := by
  have := hp.s_nw
  rw [toNat_add32 (by omega)]
  omega

omit hp in
/-- The block-mix working space is in `scratch`. -/
theorem w_sub : Region.Sub ⟨scA s₀, 128⟩ (scR s₀) := Region.sub_prefix (by omega)

theorem t_w : Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨scA s₀, 128⟩ := by
  have := hp.s_nw
  have := hp.pos
  have := disj_off (scA s₀) (o₁ := 192) (n₁ := 128 * rr s₀) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    (scR s₀).Contains (scA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off (by omega) (by omega)

/-! ## What stays in `scratch`: the caller's registers and `N` -/

/-- Bytes `[128, 192)` of `scratch`. -/
abbrev keepR (s₀ : State) : Region := ⟨scA s₀ + BitVec.ofNat 64 128, 64⟩

def Kept (s₀ : State) (m : Mem) : Prop :=
  Saved s₀ m ∧ m.readW (scA s₀ + BitVec.ofNat 64 156) 32 = BitVec.ofNat 32 (NN s₀)

theorem word_sub (s₀ : State) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 4 ≤ 192) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 d, 4⟩ (keepR s₀) := by
  rw [show d = 128 + (d - 128) by omega, ← add_ofNat]
  exact sub_off (by omega) (by omega)

theorem saved_offs : ∀ p ∈ rmSaved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 156 ∧ p.1 ≠ .r12 := by decide

theorem Kept.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Kept s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (keepR s₀).Disjoint r) : Kept s₀ m' := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have ho := saved_offs p hp
    rw [← h.1 p hp]
    exact hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ ho.1 (by omega))) (by decide)
  · rw [← h.2]
    exact hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 156, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ (by omega) (by omega))) (by decide)

theorem keep_sub (s₀ : State) : Region.Sub (keepR s₀) (scR s₀) := s_sub s₀ (by omega)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem keep_b : (keepR s₀).Disjoint (bR s₀) := hp.b_s.symm.sub_left (keep_sub s₀)
theorem keep_v : (keepR s₀).Disjoint (vR s₀) := hp.v_s.symm.sub_left (keep_sub s₀)

omit hp in
theorem keep_w : (keepR s₀).Disjoint ⟨scA s₀, 128⟩ := by
  have := disj_off (scA s₀) (o₁ := 128) (n₁ := 64) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

theorem keep_t : (keepR s₀).Disjoint ⟨tP s₀, 128 * rr s₀⟩ := by
  have := hp.s_nw
  have := hp.pos
  exact disj_off (scA s₀) (o₁ := 128) (n₁ := 64) (o₂ := 192) (n₂ := 128 * rr s₀) (by omega)
    (by omega) (by omega) (by omega) (by omega)

omit hp in
theorem b_sub' : Region.Sub ⟨bA s₀, 128 * rr s₀⟩ (bR s₀) := by
  rw [Nat.mul_comm]; exact fun _ h => h

/-- The stack arguments are kept by anything that writes only our regions. -/
theorem arg_keep {m : Mem} (hf : Frame [bR s₀, vR s₀, scR s₀] s₀.mem m) {s : State}
    (hsp : s.sp = s₀.sp) (hm : s.mem = m) : stackArg s 0 = sc s₀ := by
  show s.mem.readW (stackArgAddr s 0) 32 = s₀.mem.readW (stackArgAddr s₀ 0) 32
  rw [stackArgAddr, hsp, hm]
  refine hf.readW (r := argR s₀) (by
    show (stackArgAddr s₀ 0 - stackArgAddr s₀ 0).toNat + 32 / 8 ≤ 8
    rw [BitVec.sub_self, BitVec.toNat_zero]; decide) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_b
  · exact hp.a_v
  · exact hp.a_s

end

theorem shr_ofNat32 {a : Nat} (n : Nat) (h : a < 2 ^ 32) :
    BitVec.ofNat 32 a >>> n = BitVec.ofNat 32 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

/-! ## `Integerify`, from a 32-bit word -/

theorem leNat_bytesAt32_mod (m : Mem) (a : Addr) {e : Nat} (he : e ≤ 32) :
    leNat (bytesAt m a 64) % 2 ^ e = (m.readW a 32).toNat % 2 ^ e := by
  rw [show (64 : Nat) = 4 + 60 from rfl, bytesAt_add', leNat_append, bytesAt_length',
    show (256 : Nat) ^ 4 = 2 ^ e * 2 ^ (32 - e) by rw [← Nat.pow_add, Nat.add_sub_cancel' he],
    Nat.mul_assoc, Nat.add_mul_mod_self_left, leNat_bytesAt]
  simp only [Mem.readW, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- `Integerify (X) mod 2^e`, for `e ≤ 32`, is the first 4 bytes of `X`'s last
64-byte block, read little-endian, mod `2^e`. -/
theorem integerify_mod32 (m : Mem) (p : Addr) {r e : Nat} (hr : 0 < r) (he : e ≤ 32) :
    integerify r (bytesAt m p (128 * r)) % 2 ^ e =
      (m.readW (p + BitVec.ofNat 64 (128 * r - 64)) 32).toNat % 2 ^ e := by
  rw [integerify, blk_bytesAt' _ _ (by omega), show 64 * (2 * r - 1) = 128 * r - 64 by omega,
    leNat_bytesAt32_mod _ _ he]

theorem and_mask32 (w : BitVec 32) {e : Nat} (he : e ≤ 32) :
    (w &&& BitVec.ofNat 32 (2 ^ e - 1)).toNat = w.toNat % 2 ^ e := by
  have := Nat.pow_le_pow_right (by omega : 0 < 2) he
  have := Nat.one_le_two_pow (n := e)
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]

end VG.Proof.Scrypt.Arm.RoMix

/-!
# scryptROMix on 32-bit ARM: the small loops

The word copy (`copyLoop`), the word exclusive-or (`xorLoop`), the
multiplication by shifts and adds (`mulLoop`, as on x86-64: the model has no
multiplication) and the computation of `2 N` by doubling (`nLoop`). Words are
4 bytes, and pointers 32 bits, which address memory by their zero extensions.
-/

namespace VG.Proof.Scrypt.Arm.RoMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_and wp_subs wp_cmp wp_ldr wp_str op2_reg
  op2_imm op2_lsr eval_ne ofNat_beq_zero sub_beq)
open VG.Proof.Hmac.Arm.Init (wp_eor)
open VG.Proof.Scrypt.Memory (sub_off bytesAt_add bytesAt_length bytesAt_writeBytes_sep
  xorBytes_length)

/-! ## Arithmetic -/

theorem add_zero32 (p : BitVec 32) : p + BitVec.ofNat 32 0 = p := BitVec.add_zero _

/-- A pointer advanced by one word. -/
theorem next32 (p : BitVec 32) (k : Nat) :
    p + BitVec.ofNat 32 (4 * k) + 4 = p + BitVec.ofNat 32 (4 * (k + 1)) := by
  rw [add32_lit, Nat.mul_succ]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 32 (n - k) - 1 = BitVec.ofNat 32 (n - (k + 1)) := by
  rw [ofNat_pred32 (by omega), Nat.sub_sub]

theorem dec_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - k) - 1 == 0) = decide (k + 1 = n) := by
  rw [dec_count hk, ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

theorem cmp0 {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 32 a - 0 == 0) = decide (a = 0) := by
  rw [show BitVec.ofNat 32 a - 0 = BitVec.ofNat 32 a from BitVec.sub_zero _]
  exact ofNat_beq_zero h

theorem ofNat_zero_add32 (p : BitVec 32) : p + BitVec.ofNat 32 (4 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-- A word of a region, as an address. -/
theorem word_addr {p : BitVec 32} {n k : Nat} (hp : p.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) :
    State.addr (p + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) =
      State.addr p + BitVec.ofNat 64 (4 * k) := by
  rw [add_zero32, addr_add (by omega)]

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with Z set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.z = decide (k + 1 = n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by rw [← hz]; exact eval_ne s'
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## `copyLoop` -/

/-- After `k` words of `copyLoop`. -/
structure CopyInv (s : State) (src dst : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r
  r0 : t.gpr .r0 = src + BitVec.ofNat 32 (4 * k)
  r1 : t.gpr .r1 = dst + BitVec.ofNat 32 (4 * k)
  r2 : t.gpr .r2 = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem (State.addr dst) (bytesAt s.mem (State.addr src) (4 * k))

theorem copy_step {s : State} {src dst : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fs : src.toNat + 4 * n ≤ 2 ^ 32) (fd : dst.toNat + 4 * n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr src + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (State.addr dst + BitVec.ofNat 64 (4 * k)) 4)
    (hsep : Region.Disjoint ⟨State.addr src, 4 * n⟩ ⟨State.addr dst, 4 * n⟩) {k : Nat} (hk : k < n)
    {t : State} (h : CopyInv s src dst n k t) :
    WP isa (.block [.ldr .r3 .r0 0, .str .r3 .r1 0, .dp .add .r0 .r0 (.imm 4),
      .dp .add .r1 .r1 (.imm 4), .subs .r2 .r2 (.imm 1)]) t
      fun t' => CopyInv s src dst n (k + 1) t' ∧ t'.z = decide (k + 1 = n) := by
  refine wp_ldr (a := State.addr src + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [h.r0, word_addr fs hk]) (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_str (a := State.addr dst + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, word_addr fd hk])
    (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r3 → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.gpr, u₁.other r hr]
  have e2 : t₄.gpr .r2 = BitVec.ofNat 32 (n - k) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.r2]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp], fun r h0 h1 h2 h3 => ?_, ?_, ?_,
    by rw [u₅.gpr, e2, dec_count hk], ?_⟩, by rw [z₅, e2, dec_z hk hn]⟩
  · rw [u₅.other r h2, u₄.other r h1, u₃.other r h0, g r h3, h.other r h0 h1 h2 h3]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide), h.r0, next32]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide), h.r1, next32]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, h.mem, Nat.mul_succ]
    exact Proof.Scrypt.Memory.copy_mem s.mem _ _ k 4
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)) (by omega)

/-- `copyLoop` copies `4 n` bytes from `r0` to `r1` (`r2 = n > 0` words). -/
theorem copyLoop_ok {s : State} {src dst : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fs : src.toNat + 4 * n ≤ 2 ^ 32) (fd : dst.toNat + 4 * n ≤ 2 ^ 32)
    (h0 : s.gpr .r0 = src) (h1 : s.gpr .r1 = dst) (h2 : s.gpr .r2 = BitVec.ofNat 32 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr src + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (State.addr dst + BitVec.ofNat 64 (4 * k)) 4)
    (hsep : Region.Disjoint ⟨State.addr src, 4 * n⟩ ⟨State.addr dst, 4 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (State.addr dst) (bytesAt s.mem (State.addr src) (4 * n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt fs fd hin hout hsep hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add32, h0],
    by rw [ofNat_zero_add32, h1], by rw [h2, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- One more word of `[d] ← [x] xor [y]`. -/
theorem xor_mem4 (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 4 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 4 * n⟩ ⟨x, 4 * n⟩) (hdy : Region.Disjoint ⟨d, 4 * n⟩ ⟨y, 4 * n⟩) :
    (writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).writeW
      (d + BitVec.ofNat 64 (4 * k))
      ((writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).readW
          (x + BitVec.ofNat 64 (4 * k)) 32 ^^^
        (writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).readW
          (y + BitVec.ofNat 64 (4 * k)) 32) =
      writeBytes m d (xorBytes (bytesAt m x (4 * (k + 1))) (bytesAt m y (4 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length = 4 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (4 * k), 4⟩
      ⟨d, (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (4 * k), 4⟩
      ⟨d, (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [writeW_xor32, bytesAt_writeBytes_sep _ _ sx (by omega),
    bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (4 * k)) 4)
    (bytesAt m (y + BitVec.ofNat 64 (4 * k)) 4))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

/-- After `k` words of `xorLoop`. -/
structure XorInv (s : State) (x y d : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → t.gpr r = s.gpr r
  r0 : t.gpr .r0 = x + BitVec.ofNat 32 (4 * k)
  r1 : t.gpr .r1 = y + BitVec.ofNat 32 (4 * k)
  r2 : t.gpr .r2 = d + BitVec.ofNat 32 (4 * k)
  r3 : t.gpr .r3 = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem (State.addr d)
    (xorBytes (bytesAt s.mem (State.addr x) (4 * k)) (bytesAt s.mem (State.addr y) (4 * k)))

theorem xor_step {s : State} {x y d : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fx : x.toNat + 4 * n ≤ 2 ^ 32) (fy : y.toNat + 4 * n ≤ 2 ^ 32) (fd : d.toNat + 4 * n ≤ 2 ^ 32)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (4 * k)) 4)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr y + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (State.addr d + BitVec.ofNat 64 (4 * k)) 4)
    (hdx : Region.Disjoint ⟨State.addr d, 4 * n⟩ ⟨State.addr x, 4 * n⟩)
    (hdy : Region.Disjoint ⟨State.addr d, 4 * n⟩ ⟨State.addr y, 4 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block [.ldr .r12 .r0 0, .ldr .lr .r1 0, .dp .eor .r12 .r12 (.reg .lr), .str .r12 .r2 0,
      .dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 4),
      .subs .r3 .r3 (.imm 1)]) t
      fun t' => XorInv s x y d n (k + 1) t' ∧ t'.z = decide (k + 1 = n) := by
  refine wp_ldr (a := State.addr x + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [h.r0, word_addr fx hk]) (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ u₁ => ?_
  refine wp_ldr (a := State.addr y + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, word_addr fy hk])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun t₃ u₃ => ?_
  refine wp_str (a := State.addr d + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r2,
      word_addr fd hk])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ u₄ => ?_
  refine wp_add (op2_imm (by decide)) fun t₅ u₅ => wp_add (op2_imm (by decide)) fun t₆ u₆ =>
    wp_add (op2_imm (by decide)) fun t₇ u₇ => wp_subs (op2_imm (by decide)) fun t₈ u₈ z₈ =>
    WP.block_nil ?_
  have g : ∀ r, r ≠ .r12 → r ≠ .lr → t₄.gpr r = t.gpr r := fun r h12 hlr => by
    rw [u₄.gpr, u₃.other r h12, u₂.other r hlr, u₁.other r h12]
  have e3 : t₇.gpr .r3 = BitVec.ofNat 32 (n - k) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      g _ (by decide) (by decide), h.r3]
  refine ⟨⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r h0 h1 h2 h3 h12 hlr => ?_, ?_, ?_, ?_, by rw [u₈.gpr, e3, dec_count hk], ?_⟩,
    by rw [z₈, e3, dec_z hk hn]⟩
  · rw [u₈.other r h3, u₇.other r h2, u₆.other r h1, u₅.other r h0, g r h12 hlr,
      h.other r h0 h1 h2 h3 h12 hlr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      g _ (by decide) (by decide), h.r0, next32]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      g _ (by decide) (by decide), h.r1, next32]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      g _ (by decide) (by decide), h.r2, next32]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.other .r12 (by decide), u₂.gpr,
      u₂.mem, u₁.gpr, u₁.mem, h.mem]
    exact xor_mem4 s.mem hk (by omega) hdx hdy

/-- `xorLoop` writes `[r0] xor [r1]` to `r2`, `4 n` bytes (`r3 = n > 0` words). -/
theorem xorLoop_ok {s : State} {x y d : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fx : x.toNat + 4 * n ≤ 2 ^ 32) (fy : y.toNat + 4 * n ≤ 2 ^ 32) (fd : d.toNat + 4 * n ≤ 2 ^ 32)
    (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = d)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (4 * k)) 4)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr y + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (State.addr d + BitVec.ofNat 64 (4 * k)) 4)
    (hdx : Region.Disjoint ⟨State.addr d, 4 * n⟩ ⟨State.addr x, 4 * n⟩)
    (hdy : Region.Disjoint ⟨State.addr d, 4 * n⟩ ⟨State.addr y, 4 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (State.addr d)
        (xorBytes (bytesAt s.mem (State.addr x) (4 * n)) (bytesAt s.mem (State.addr y) (4 * n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt fx fy fd hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add32, h0],
    by rw [ofNat_zero_add32, h1], by rw [ofNat_zero_add32, h2], by rw [h3, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `mulLoop` -/

/-- `r0 = m`, and `r1 + r0 * r2` is still `a + j c`. -/
structure MulInv (s : State) (j c : Nat) (a : BitVec 32) (m : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r
  lt : m < 2 ^ 32
  r0 : t.gpr .r0 = BitVec.ofNat 32 m
  sum : t.gpr .r1 + BitVec.ofNat 32 m * t.gpr .r2 = a + BitVec.ofNat 32 (j * c)

theorem and_one_z {m : Nat} (h : m < 2 ^ 32) :
    ((BitVec.ofNat 32 m &&& 1) - 0 == 0) = decide (m % 2 = 0) := by
  have e : BitVec.ofNat 32 m &&& 1 = BitVec.ofNat 32 (m % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : m % 2 < 2 ^ 32), show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod]
  rw [e, cmp0 (by omega)]

/-- The invariant across one iteration: `r1` gains `r2` if `m` is odd. -/
theorem mul_sum (d r : BitVec 32) (m : Nat) :
    (d + (if m % 2 = 1 then r else 0)) + BitVec.ofNat 32 (m / 2) * (r + r) =
      d + BitVec.ofNat 32 m * r := by
  have e : BitVec.ofNat 32 m = BitVec.ofNat 32 (m / 2) + BitVec.ofNat 32 (m / 2) +
      BitVec.ofNat 32 (m % 2) := by
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]; exact congrArg (BitVec.ofNat _) (by omega)
  by_cases h : m % 2 = 1
  · simp only [h, ↓reduceIte]
    rw [e, h, show BitVec.ofNat 32 1 = 1 from rfl]; grind
  · simp only [h, ↓reduceIte]
    rw [e, show m % 2 = 0 by omega, show BitVec.ofNat 32 0 = 0 from rfl]; grind

/-- The conditional add: `r1 ← r1 + r2` if `r0` is odd. -/
theorem mul_ite {m : Nat} {t : State} (hz : t.z = decide (m % 2 = 0)) :
    WP isa (.ite .ne (.block [.dp .add .r1 .r1 (.reg .r2)]) (.block [])) t fun t' =>
      Upd t t' .r1 (t.gpr .r1 + if m % 2 = 1 then t.gpr .r2 else 0) := by
  refine WP.ite (!decide (m % 2 = 0)) (by rw [← hz]; exact eval_ne t)
    (fun hb => wp_add (op2_reg _ _) fun t₁ u₁ => WP.block_nil ?_) (fun hb => WP.block_nil ?_)
  · have : m % 2 = 1 := by
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hb; omega
    simp only [this, ↓reduceIte]; exact u₁
  · have : ¬ m % 2 = 1 := by
      simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hb; omega
    simp only [this, ↓reduceIte]
    rw [show t.gpr .r1 + 0 = t.gpr .r1 from BitVec.add_zero _]
    exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem mul_step {s : State} {j c : Nat} {a : BitVec 32} {m : Nat} {t : State}
    (h : MulInv s j c a m t) :
    WP isa (.seq (.block [.dp .and .r3 .r0 (.imm 1), .cmp .r3 (.imm 0)]) <|
      .seq (.ite .ne (.block [.dp .add .r1 .r1 (.reg .r2)]) (.block []))
        (.block [.dp .add .r2 .r2 (.reg .r2), .mov .r0 (.shifted .r0 .lsr 1), .cmp .r0 (.imm 0)])) t
      fun t' => MulInv s j c a (m / 2) t' ∧ t'.z = decide (m / 2 = 0) := by
  refine WP.seq (wp_and (op2_imm (by decide)) fun t₁ u₁ =>
    wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_)
  have hz : t₂.z = decide (m % 2 = 0) := by
    rw [z₂, u₁.gpr, h.r0, and_one_z h.lt]
  refine WP.seq (WP.mono (mul_ite hz) fun t₃ u₃ => ?_)
  refine wp_add (op2_reg _ _) fun t₄ u₄ => wp_mov (op2_lsr (by decide)) fun t₅ u₅ =>
    wp_cmp (op2_imm (by decide)) fun t₆ f₆ z₆ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .r3 → t₂.gpr r = t.gpr r := fun r hr => by rw [f₂.gpr, u₁.other r hr]
  have ax₄ : t₄.gpr .r0 = BitVec.ofNat 32 m := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), h.r0]
  have e0 : t₆.gpr .r0 = BitVec.ofNat 32 (m / 2) := by
    rw [f₆.gpr, u₅.gpr, ax₄, shr_ofNat32 _ h.lt, Nat.pow_one]
  refine ⟨⟨by rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, f₂.rd, u₁.rd, h.rd],
    by rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, f₂.wr, u₁.wr, h.wr],
    by rw [f₆.sp, u₅.sp, u₄.sp, u₃.sp, f₂.sp, u₁.sp, h.sp],
    by rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, f₂.mem, u₁.mem, h.mem],
    fun r h0 h1 h2 h3 => ?_, by have := h.lt; omega, e0, ?_⟩, ?_⟩
  · rw [f₆.gpr, u₅.other r h0, u₄.other r h2, u₃.other r h1, g₂ r h3, h.other r h0 h1 h2 h3]
  · rw [f₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₄.other _ (by decide),
      u₃.gpr, u₃.other _ (by decide), g₂ _ (by decide), g₂ _ (by decide), mul_sum, h.sum]
  · rw [z₆, u₅.gpr, ax₄, shr_ofNat32 _ h.lt, Nat.pow_one, cmp0 (by have := h.lt; omega)]

/-- `mulLoop` adds `r0 * r2` to `r1` (modulo 2^32), for any `r0`. -/
theorem mulLoop_ok {s : State} {j c : Nat} {a : BitVec 32} (hj : j < 2 ^ 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 j) (h1 : s.gpr .r1 = a) (h2 : s.gpr .r2 = BitVec.ofNat 32 c) :
    WP isa mulLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r1 = a + BitVec.ofNat 32 (j * c) := by
  refine WP.loop (M := isa) (MulInv s j c a) ?_ j s
    ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, hj, h0, by rw [h1, h2, BitVec.ofNat_mul]⟩
  intro m t h
  refine WP.mono (mul_step h) fun t' ⟨h', hz⟩ => ?_
  have he : isa.eval .ne t' = some (!decide (m / 2 = 0)) := by rw [← hz]; exact eval_ne t'
  by_cases hl : m / 2 = 0
  · refine .inl ⟨by rw [he]; simp [hl], h'.rd, h'.wr, h'.sp, h'.mem, h'.other, ?_⟩
    have := h'.sum
    rwa [hl, BitVec.zero_mul, BitVec.add_zero] at this
  · exact .inr ⟨by rw [he]; simp [hl], m / 2, by omega, h'⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .r0 → r' ≠ .r1 → t.gpr r' = s.gpr r'
  r0 : t.gpr .r0 = BitVec.ofNat 32 (r * 2 ^ k)
  r1 : t.gpr .r1 = BitVec.ofNat 32 (2 ^ k)

theorem dbl_pow32 (x k : Nat) : BitVec.ofNat 32 (x * 2 ^ k) + BitVec.ofNat 32 (x * 2 ^ k) =
    BitVec.ofNat 32 (x * 2 ^ (k + 1)) := by
  rw [← BitVec.ofNat_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : NInv s r k t) :
    WP isa (.block [.dp .add .r0 .r0 (.reg .r0), .dp .add .r1 .r1 (.reg .r1), .cmp .r0 (.reg .r2)]) t
      fun t' => NInv s r (k + 1) t' ∧ t'.z = decide (k + 1 = e + 1) := by
  refine wp_add (op2_reg _ _) fun t₁ u₁ => wp_add (op2_reg _ _) fun t₂ u₂ =>
    wp_cmp (op2_reg _ _) fun t₃ f₃ z₃ => WP.block_nil ?_
  have ax : t₂.gpr .r0 = BitVec.ofNat 32 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.r0, dbl_pow32]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨by rw [f₃.rd, u₂.rd, u₁.rd, h.rd], by rw [f₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [f₃.sp, u₂.sp, u₁.sp, h.sp], by rw [f₃.mem, u₂.mem, u₁.mem, h.mem],
    fun r' h0 h1 => ?_, by rw [f₃.gpr, ax], ?_⟩, ?_⟩
  · rw [f₃.gpr, u₂.other r' h1, u₁.other r' h0, h.other r' h0 h1]
  · rw [f₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r1, ← Nat.one_mul (2 ^ k), dbl_pow32, Nat.one_mul]
  · rw [z₃, ax, u₂.other _ (by decide), u₁.other _ (by decide),
      h.other _ (by decide) (by decide), h2, sub_beq (by omega) hlt]
    by_cases hh : k + 1 = e + 1
    · simp [hh]
    · have : r * 2 ^ (k + 1) ≠ r * 2 ^ (e + 1) := fun h' =>
        hh ((Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr h'))
      simp only [this, decide_false, hh]

/-- `nLoop` doubles `r0` (from `r`) and `r1` (from 1) until `r0 = r2 = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 r) (h1 : s.gpr .r1 = 1)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .r0 → r' ≠ .r1 → s'.gpr r' = s.gpr r') ∧
      s'.gpr .r1 = BitVec.ofNat 32 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt h2 hk h) ?_) fun t h => ⟨h.rd, h.wr, h.sp, h.mem, h.other, h.r1⟩
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl, by rw [h0, Nat.pow_zero, Nat.mul_one],
    by rw [h1]; rfl⟩

end VG.Proof.Scrypt.Arm.RoMix

/-!
# scryptROMix on 32-bit ARM: correctness

The prologue loads the scratch pointer from the stack, saves our caller's
registers and our return address in `scratch` and computes `N`; step 2 and
step 3 are loops whose bodies call `vg_scrypt_blockmix` (through
`BlockMixSpec`), with our own stack argument as its scratch space; the
epilogue restores the registers. As on AArch64
(`Proof/Scrypt/AArch64/RoMixCT.lean`).
-/

namespace VG.Proof.Scrypt.Arm.RoMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_sub wp_and wp_subs wp_ldr wp_str wp_ldrSp
  op2_reg op2_imm op2_lsl op2_lsr saveMem saveList_ok readW_writeW_save)
open VG.Proof.Scrypt (vList vList_getD roMix_eq roMixIndices_eq mixLoop_succ_fst mixLoop_succ_snd)
open VG.Proof.Scrypt.Memory (add_ofNat contains_off sub_off InRegions.of_mem InRegions.right
  frame_bytesAt bytesAt_writeBytes_self bytesAt_writeBytes_sep bytesAt_length xorBytes_length)

/-! ## Arithmetic -/

theorem dbl32 (x : BitVec 32) : x + x = BitVec.ofNat 32 (2 * x.toNat) := by
  conv_lhs => rw [ofNat_toNat32 x]
  rw [← BitVec.ofNat_add, Nat.two_mul]

theorem stackArgAddr_eq {s s₀ : State} (h : s.sp = s₀.sp) : stackArgAddr s 0 = stackArgAddr s₀ 0 := by
  rw [stackArgAddr, stackArgAddr, h]

/-! ## The prologue -/

theorem prologue_eq : rmPrologue =
    .ldrSp .r12 0 :: (rmSaved.map (fun p => Instr.str p.1 .r12 p.2) ++
      ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r2), .mov .r6 (.reg .r12),
       .mov .r7 (.shifted .r1 .lsl 7), .mov .r0 (.reg .r1), .mov .r1 (.imm 1),
       .dp .add .r2 .r3 (.reg .r3)] : List Instr)) := rfl

theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ rmSaved, (saveMem m B g rmSaved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 :=
  Spill.saveMem_saved (lo := 128) (hi := 156) B g m rmSaved (by decide)

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, (∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r) → s₁.gpr .r12 = sc s₀ → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → s₁.sp = s₀.sp → Frame [scR s₀] s₀.mem s₁.mem → Saved s₀ s₁.mem →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (.ldrSp .r12 0 :: (rmSaved.map (fun p => Instr.str p.1 .r12 p.2) ++ rest)))
      s₀ Q := by
  have hs := hp.s_nw
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl ?_ fun s₁ u₁ => ?_
  · rw [hp.rd]
    refine InRegions.of_mem (R := argR s₀) (by simp) ?_
    show (stackArgAddr s₀ 0 - stackArgAddr s₀ 0).toNat + 4 ≤ 8
    rw [BitVec.sub_self, BitVec.toNat_zero]; decide
  have e12 : s₁.gpr .r12 = sc s₀ := u₁.gpr
  refine saveList_ok rmSaved s₁ Q (fun p hp' => ?_) fun s₂ g rd wr sp m => ?_
  · obtain ⟨h1, h2, -⟩ := saved_offs p hp'
    rw [e12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, InRegions.of_mem (by simp) (in_s s₀ (by omega))⟩
  refine k s₂ (fun r hr => by rw [g, u₁.other r hr]) (by rw [g, e12]) (by rw [rd, u₁.rd])
    (by rw [wr, u₁.wr]) (by rw [sp, u₁.sp]) ?_ ?_
  · rw [m, e12, u₁.mem]
    exact saveMem_frame' _ _ _ fun p hp' => in_s s₀ (by have := saved_offs p hp'; omega)
  · intro p hp'
    rw [m, e12, saveMem_saved, u₁.other _ (saved_offs p hp').2.2]
    exact hp'

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r0 : s.gpr .r0 = BitVec.ofNat 32 (rr s₀)
  r1 : s.gpr .r1 = 1
  r2 : s.gpr .r2 = BitVec.ofNat 32 (2 * vl s₀)

theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : ∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r)
    (g12 : s₁.gpr .r12 = sc s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp)
    (hf : Frame [scR s₀] s₀.mem s₁.mem) (hsv : Saved s₀ s₁.mem) :
    WP isa (.block [.mov .r4 (.reg .r0), .mov .r5 (.reg .r2), .mov .r6 (.reg .r12),
       .mov .r7 (.shifted .r1 .lsl 7), .mov .r0 (.reg .r1), .mov .r1 (.imm 1),
       .dp .add .r2 .r3 (.reg .r3)]) s₁ (P1 s₀) := by
  have lt := r_lt hp
  have hr : rr s₀ = (s₀.gpr .r1).toNat := rfl
  refine wp_mov (op2_reg _ _) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_reg _ _) fun c uc => wp_mov (op2_lsl (by decide)) fun d ud =>
    wp_mov (op2_reg _ _) fun e ue => wp_mov (op2_imm (by decide)) fun f uf =>
    wp_add (op2_reg _ _) fun h uh => WP.block_nil ?_
  have hm : h.mem = s₁.mem := by rw [uh.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  have x1 : d.gpr .r1 = s₀.gpr .r1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g _ (by decide)]
  refine ⟨?_, ?_, ?_, by rw [hm]; exact hf, by rw [hm]; exact hsv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uh.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [uh.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [uh.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr,
      g _ (by decide)]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.other _ (by decide),
      g _ (by decide)]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.other _ (by decide), ua.other _ (by decide), g12]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide), ud.gpr,
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g _ (by decide),
      shl32 (by omega)]
    congr 1; omega
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.gpr, x1]
    exact ofNat_toNat32 _
  · rw [uh.other _ (by decide), uf.gpr]
  · rw [uh.gpr, uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g _ (by decide),
      dbl32]

/-! ## Computing `N` -/

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (2 * NN s₀)

theorem nloop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) : WP isa nLoop s (N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := v_lt hp
  have e2 : rr s₀ * 2 ^ (e + 1) = 2 * vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_left_comm]
  have hNe : 2 * vl s₀ < 2 ^ 32 := by have := vl_mul hp; omega
  refine WP.mono (nLoop_ok (r := rr s₀) (e := e) hp.pos (by omega) h.r0 h.r1
    (by rw [h.r2, e2])) fun t ⟨rd, wr, sp, mem, oth, r1⟩ => ?_
  exact ⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [sp, h.sp], by rw [mem]; exact h.frame,
    by rw [mem]; exact h.saved,
    by rw [oth _ (by decide) (by decide), h.r4], by rw [oth _ (by decide) (by decide), h.r5],
    by rw [oth _ (by decide) (by decide), h.r6], by rw [oth _ (by decide) (by decide), h.r7],
    by rw [r1, he, Nat.pow_succ, Nat.mul_comm]⟩

/-! ## Step 2 -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (NN s₀ - i)
  r9 : s.gpr .r9 = vAt32 s₀ i
  frame : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  x : bytesAt s.mem (bA s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)

set_option simprocs false in
theorem setupMem_kept (s₀ : State) {m : Mem} (h : Saved s₀ m) :
    Kept s₀ (m.writeW (scA s₀ + BitVec.ofNat 64 156) (BitVec.ofNat 32 (NN s₀))) := by
  refine ⟨fun p hp => ?_, Mem.readW_writeW_self32 _ _ _⟩
  have ho := saved_offs p hp
  rw [readW_writeW_save _ _ _ (by omega) (by decide) (by omega)]
  exact h p hp

theorem setup2_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : N1 s₀ s) :
    WP isa (.block rmSetup) s (Inv2 s₀ 0) := by
  have lt := v_lt hp
  have n1 := NN_pos hp
  have hs := hp.s_nw
  have : 2 * NN s₀ < 2 ^ 32 := by
    have : 2 * NN s₀ ≤ 128 * rr s₀ * NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * rr s₀ := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  unfold rmSetup
  refine wp_mov (op2_lsr (by decide)) fun t1 u1 => ?_
  have hd : t1.gpr .r1 = BitVec.ofNat 32 (NN s₀) := by
    rw [u1.gpr, h.r1, shr_ofNat32 _ (by omega), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  refine wp_str (a := scA s₀ + BitVec.ofNat 64 156) (by decide)
    (by rw [u1.other _ (by decide), h.r6, addr_add (by omega)])
    (by rw [u1.wr, h.wr, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by omega)))
    fun t2 u2 => wp_mov (op2_reg _ _) fun t3 u3 => wp_mov (op2_reg _ _) fun t4 u4 => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r8 → r ≠ .r9 → t4.gpr r = s.gpr r := fun r b c d => by
    rw [u4.other _ d, u3.other _ c, u2.gpr, u1.other _ b]
  have hm : t4.mem = s.mem.writeW (scA s₀ + BitVec.ofNat 64 156) (BitVec.ofNat 32 (NN s₀)) := by
    rw [u4.mem, u3.mem, u2.mem, hd, u1.mem]
  have fr : Frame [scR s₀] s₀.mem t4.mem := by
    rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (in_s s₀ (by omega))
  refine ⟨Nat.zero_le _, by rw [u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr], by rw [u4.sp, u3.sp, u2.sp, u1.sp, h.sp],
    by rw [g _ (by decide) (by decide) (by decide), h.r4],
    by rw [g _ (by decide) (by decide) (by decide), h.r5],
    by rw [g _ (by decide) (by decide) (by decide), h.r6],
    by rw [g _ (by decide) (by decide) (by decide), h.r7], ?_, ?_,
    fr.mono (by simp), by rw [hm]; exact setupMem_kept s₀ h.saved, ?_,
    fun k hk => absurd hk (by omega)⟩
  · rw [u4.other _ (by decide), u3.gpr, u2.gpr, hd, Nat.sub_zero]
  · rw [u4.gpr, u3.other _ (by decide), u2.gpr, u1.other _ (by decide), h.r5]
    simp
  · refine frame_bytesAt fr (fun r hr => ?_) (by have := r_lt hp; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub' (s₀ := s₀))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

/-- The instructions before the call, after `r0` is set. -/
abbrev bmTail : List Instr := [.mov .r1 (.shifted .r7 .lsr 7), .mov .r2 (.reg .r4), .mov .r3 (.reg .r1)]

theorem blockMixTo_eq (c : Prog isa) (src : List Instr) :
    blockMixTo c src = .seq (.block (src ++ bmTail)) (.call "vg_scrypt_blockmix" c) := rfl

theorem b_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (bA s₀) (128 * rr s₀) := by
  rw [hp.wr]
  refine InRegions.of_mem (R := bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem w_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (scA s₀) 128 := by
  rw [hp.wr]
  refine InRegions.of_mem (R := scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem arg_in {s₀ : State} (hp : Pre s₀) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 := by
  rw [hp.rd]
  refine InRegions.of_mem (R := argR s₀) (by simp) ?_
  show (stackArgAddr s₀ 0 - stackArgAddr s₀ 0).toNat + 4 ≤ 8
  rw [BitVec.sub_self, BitVec.toNat_zero]; decide

theorem arg4_sub (s₀ : State) : Region.Sub ⟨stackArgAddr s₀ 0, 4⟩ (argR s₀) :=
  Region.sub_prefix (by decide)

/-- The registers our loops keep are not the call's arguments. -/
theorem pres_ne : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by decide

/-- A block that may be the source of a call of `vg_scrypt_blockmix` into `b`. -/
structure SrcOK (s₀ : State) (A : BitVec 32) : Prop where
  b : Region.Disjoint ⟨State.addr A, 128 * rr s₀⟩ ⟨bA s₀, 128 * rr s₀⟩
  w : Region.Disjoint ⟨State.addr A, 128 * rr s₀⟩ ⟨scA s₀, 128⟩
  nw : A.toNat + 128 * rr s₀ ≤ 2 ^ 32
  inr : InRegions (s₀.rd ++ s₀.wr) (State.addr A) (128 * rr s₀)

/-- Making the call with the arguments set: its precondition. -/
theorem bm_call {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    {A : BitVec 32} (hA : SrcOK s₀ A) (h0 : s.gpr .r0 = A)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 (rr s₀)) (h2 : s.gpr .r2 = bP s₀)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 (rr s₀)) (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] s.mem s'.mem →
      bytesAt s'.mem (bA s₀) (128 * rr s₀) =
        blockMix (rr s₀) (bytesAt s.mem (State.addr A) (128 * rr s₀)) → Q s') :
    WP isa (.call "vg_scrypt_blockmix" c) s Q := by
  have lt := r_lt hp
  have ea := stackArgAddr_eq hsp
  exact hS s A (bP s₀) (sc s₀) (rr s₀) h0 h1 h2 h3 (arg_keep hp hm hsp rfl) hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [ea]; exact (hp.a_b.sub_left (arg4_sub s₀)).sub_right (b_sub' (s₀ := s₀)))
    (by rw [ea]; exact (hp.a_s.sub_left (arg4_sub s₀)).sub_right (w_sub (s₀ := s₀)))
    hA.nw (by have := hp.b_nw; omega) (by have := hp.s_nw; omega)
    (by rw [hsp]; have := hp.sp_nw; omega)
    (by rw [hrd, hwr]; exact hA.inr) (by rw [ea, hrd, hwr]; exact arg_in hp)
    (by rw [hwr]; exact b_in hp) (by rw [hwr]; exact w_in hp) Q hQ

/-- Setting up and making the call, from `r0 = A`. -/
theorem bm_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    {A : BitVec 32} (hA : SrcOK s₀ A) (h0 : s.gpr .r0 = A) (h4 : s.gpr .r4 = bP s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] s.mem s'.mem →
      bytesAt s'.mem (bA s₀) (128 * rr s₀) =
        blockMix (rr s₀) (bytesAt s.mem (State.addr A) (128 * rr s₀)) → Q s') :
    WP isa (.block bmTail) s fun s' => WP isa (.call "vg_scrypt_blockmix" c) s' Q := by
  have lt := r_lt hp
  refine wp_mov (op2_lsr (by decide)) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_reg _ _) fun d ud => WP.block_nil ?_
  have k : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have h1 : a.gpr .r1 = BitVec.ofNat 32 (rr s₀) := by
    rw [ua.gpr, h7, shr_ofNat32 _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  have em : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  refine bm_call hS hp hA (by rw [k _ (by decide) (by decide) (by decide), h0])
    (by rw [ud.other _ (by decide), ub.other _ (by decide), h1])
    (by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h4])
    (by rw [ud.gpr, ub.other _ (by decide), h1]) (by rw [ud.sp, ub.sp, ua.sp, hsp])
    (by rw [ud.rd, ub.rd, ua.rd, hrd]) (by rw [ud.wr, ub.wr, ua.wr, hwr]) (by rw [em]; exact hm)
    fun s' rd' wr' sp' cs' f' b' => hQ s' (by rw [rd', ud.rd, ub.rd, ua.rd])
      (by rw [wr', ud.wr, ub.wr, ua.wr]) (by rw [sp', ud.sp, ub.sp, ua.sp])
      (fun r hr hlr => by
        obtain ⟨-, n1, n2, n3⟩ := pres_ne r hr
        rw [cs' r hr hlr, k r n1 n2 n3])
      (by rw [em] at f'; exact f') (by rw [b', em])

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem vAt_in {i : Nat} (hi : i < NN s₀) : InRegions s₀.wr (vAt s₀ i) (128 * rr s₀) := by
  rw [hp.wr]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

/-- `V[i]` and the parts of `scratch` we use. -/
theorem vAt_b {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (bR s₀) :=
  hp.b_v.symm.sub_left (vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (scR s₀) :=
  hp.v_s.sub_left (vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] m m') :
    Frame [bR s₀, vR s₀, scR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bR s₀, by simp, b_sub'⟩
    · exact ⟨scR s₀, by simp, w_sub⟩

/-- What a call writing `b` keeps: `V[k]`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] m m')
    {k : Nat} (hk : k < NN s₀) :
    bytesAt m' (vAt s₀ k) (128 * rr s₀) = bytesAt m (vAt s₀ k) (128 * rr s₀) := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (vAt_b hp hk).sub_right b_sub'
  · exact (vAt_s hp hk).sub_right w_sub

theorem call_kept {m m' : Mem} (hf : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] m m')
    (h : Kept s₀ m) : Kept s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (keep_b hp).sub_right b_sub'
    · exact keep_w

theorem srcOK_v {i : Nat} (hi : i < NN s₀) : SrcOK s₀ (vAt32 s₀ i) := by
  have e := vAt_addr hp hi
  exact ⟨by rw [e]; exact (vAt_b hp hi).sub_right b_sub', by rw [e]; exact (vAt_s hp hi).sub_right w_sub,
    vAt_nw hp hi, by rw [e]; exact InRegions.right (vAt_in hp hi)⟩

theorem t_b : Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨bA s₀, 128 * rr s₀⟩ :=
  (hp.b_s.symm.sub_left (t_sub hp)).sub_right b_sub'

theorem t_in : InRegions s₀.wr (tP s₀) (128 * rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem srcOK_t : SrcOK s₀ (tP32 s₀) := by
  have e := t_addr hp
  exact ⟨by rw [e]; exact t_b hp, by rw [e]; exact t_w hp, t_nw hp,
    by rw [e]; exact InRegions.right (t_in hp)⟩

/-- The memory after iteration `i` of step 2. -/
theorem mem2_ok {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) {m₃ : Mem}
    (f₃ : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩]
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) m₃)
    (b₃ : bytesAt m₃ (bA s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) (vAt s₀ i)
        (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀] s₀.mem m₃ ∧ Kept s₀ m₃ ∧
    bytesAt m₃ (bA s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) (i + 1) (B s₀) ∧
    ∀ k < i + 1, bytesAt m₃ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) := by
  have lt := r_lt hp
  have hl : (bytesAt s.mem (bA s₀) (128 * rr s₀)).length = 128 * rr s₀ := bytesAt_length _ _ _
  have hself : bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) (vAt s₀ i)
      (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀) := by
    have := bytesAt_writeBytes_self s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))
      (by rw [hl]; omega)
    rw [hl] at this
    rw [this, h.x]
  have f₂ : Frame [⟨vAt s₀ i, 128 * rr s₀⟩] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  refine ⟨(h.frame.trans f₂').trans (call_frame f₃), call_kept hp f₃ (h.kept.frame f₂ fun r hr => ?_),
    by rw [b₃, hself]; rfl, fun k hk => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (keep_v hp).sub_right (vAt_sub hp hi)
  · rw [call_keeps_v hp f₃ (by omega)]
    by_cases hki : k = i
    · subst hki; exact hself
    · rw [bytesAt_writeBytes_sep _ _ (by rw [hl]; exact vAt_disj hp (by omega) hi hki) (by omega)]
      exact h.done k (by omega)

end

theorem vAt_succ (s₀ : State) (i : Nat) :
    vAt32 s₀ i + BitVec.ofNat 32 (128 * rr s₀) = vAt32 s₀ (i + 1) := by
  show _ = vP s₀ + BitVec.ofNat 32 (128 * rr s₀ * (i + 1))
  rw [add32, Nat.mul_succ]

theorem b_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 32 * rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  have := r_lt hp
  rw [hp.rd, hp.wr]
  exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega))

theorem v_word {s₀ : State} (hp : Pre s₀) {i k : Nat} (hi : i < NN s₀) (hk : k < 32 * rr s₀) :
    InRegions s₀.wr (State.addr (vAt32 s₀ i) + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [hp.wr, vAt_addr hp hi]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  show InRegions _ (vA s₀ + BitVec.ofNat 64 (128 * rr s₀ * i) + BitVec.ofNat 64 (4 * k)) 4
  rw [add_ofNat]
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

theorem t_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 32 * rr s₀) :
    InRegions s₀.wr (State.addr (tP32 s₀) + BitVec.ofNat 64 (4 * k)) 4 := by
  have := hp.s_nw
  rw [hp.wr, t_addr hp, add_ofNat]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem sh2 {s₀ : State} (hp : Pre s₀) :
    BitVec.ofNat 32 (128 * rr s₀) >>> 2 = BitVec.ofNat 32 (32 * rr s₀) := by
  rw [shr_ofNat32 _ (r_lt hp)]; exact congrArg (BitVec.ofNat _) (by omega)

/-- One iteration of step 2. -/
theorem step2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) :
    WP isa (step2 c) s fun s' => Inv2 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  have hb := hp.b_nw
  unfold step2
  refine WP.seq (wp_mov (op2_reg _ _) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_lsr (by decide)) fun d ud => WP.block_nil ?_)
  have ke : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have erd : d.rd = s₀.rd := by rw [ud.rd, ub.rd, ua.rd, h.rd]
  have ewr : d.wr = s₀.wr := by rw [ud.wr, ub.wr, ua.wr, h.wr]
  have esp : d.sp = s₀.sp := by rw [ud.sp, ub.sp, ua.sp, h.sp]
  have hme : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  have e4 : 4 * (32 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.seq (WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt32 s₀ i) (n := 32 * rr s₀)
    (by omega) (by omega) (by omega) (by rw [e4]; exact vAt_nw hp hi)
    (by rw [ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.r4])
    (by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.r9])
    (by rw [ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r7, sh2 hp])
    (fun k hk => by rw [erd, ewr]; exact b_word hp hk)
    (fun k hk => by rw [ewr]; exact v_word hp hi hk)
    (by rw [e4, vAt_addr hp hi]; exact (vAt_b hp hi).symm.sub_left b_sub'))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [hme, e4, vAt_addr hp hi] at mt
  have kt : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h0, h1, h2, h3⟩ := pres_ne r hr
    rw [gt r h0 h1 h2 h3, ke r h0 h1 h2]
  have ft : Frame [bR s₀, vR s₀, scR s₀] s₀.mem t.mem := by
    rw [mt]
    refine h.frame.trans (Proof.Sha256.Stream.writeBytes_frame (R := ⟨vAt s₀ i, 128 * rr s₀⟩)
      _ _ _ ?_ |>.sub fun r hr => ?_)
    · rw [bytesAt_length]; exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov (op2_reg _ _) fun f uf => ?_))
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    rw [uf.other _ (pres_ne r hr).1, kt r hr]
  refine bm_ok hS hp (srcOK_v hp hi) (by rw [uf.gpr, kt _ (by decide), h.r9])
    (by rw [kf _ (by decide), h.r4]) (by rw [kf _ (by decide), h.r7]) (by rw [uf.sp, spt, esp])
    (by rw [uf.rd, rdt, erd]) (by rw [uf.wr, wrt, ewr]) (by rw [uf.mem]; exact ft)
    fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [uf.mem, mt] at f4 b4
  rw [vAt_addr hp hi] at b4
  obtain ⟨F, K, X, D⟩ := mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, r ≠ .lr → s4.gpr r = s.gpr r := fun r hr hlr => by
    rw [cs4 r hr hlr, kf r hr]
  refine wp_add (op2_reg _ _) fun s5 u5 => wp_subs (op2_imm (by decide)) fun s6 u6 z6 =>
    WP.block_nil ?_
  have k6 : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r8 → r ≠ .r9 → s6.gpr r = s.gpr r :=
    fun r hr hlr h1 h2 => by rw [u6.other _ h1, u5.other _ h2, k4 r hr hlr]
  have e8 : s5.gpr .r8 = BitVec.ofNat 32 (NN s₀ - i) := by
    rw [u5.other _ (by decide), k4 _ (by decide) (by decide), h.r8]
  refine ⟨⟨by omega, by rw [u6.rd, u5.rd, rd4, uf.rd, rdt, erd], by rw [u6.wr, u5.wr, wr4, uf.wr, wrt, ewr],
    by rw [u6.sp, u5.sp, sp4, uf.sp, spt, esp],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.r4],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.r5],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.r7],
    by rw [u6.gpr, e8, dec_count hi], ?_,
    by rw [u6.mem, u5.mem]; exact F, by rw [u6.mem, u5.mem]; exact K,
    by rw [u6.mem, u5.mem]; exact X, by rw [u6.mem, u5.mem]; exact D⟩, by rw [z6, e8, dec_z hi hN]⟩
  rw [u6.other _ (by decide), u5.gpr, k4 _ (by decide) (by decide), k4 _ (by decide) (by decide),
    h.r9, h.r7, vAt_succ]

theorem loop2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv2 s₀ 0 s) : WP isa (.loop (step2 c) .ne) s (Inv2 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv2 s₀) (fun _ hi _ h => step2_ok hS hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (NN s₀ - i)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (NN s₀ - 1)
  frame : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  v : ∀ k < NN s₀, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)
  x : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bA s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bA s₀) (128 * rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i

theorem mid_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv2 s₀ (NN s₀) s) :
    WP isa (.block rmMid) s (Inv3 s₀ 0) := by
  have n1 := NN_pos hp
  have hs := hp.s_nw
  unfold rmMid
  refine wp_ldr (a := scA s₀ + BitVec.ofNat 64 156) (by decide) (by rw [h.r6, addr_add (by omega)])
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ (by omega)))
    fun a ua => wp_sub (op2_imm (by decide)) fun b ub => WP.block_nil ?_
  have ka : a.gpr .r8 = BitVec.ofNat 32 (NN s₀) := by rw [ua.gpr, h.kept.2]
  have k : ∀ r, r ≠ .r8 → r ≠ .r9 → b.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ub.other _ h2, ua.other _ h1]
  have hm : b.mem = s.mem := by rw [ub.mem, ua.mem]
  refine ⟨Nat.zero_le _, by rw [ub.rd, ua.rd, h.rd], by rw [ub.wr, ua.wr, h.wr],
    by rw [ub.sp, ua.sp, h.sp], by rw [k _ (by decide) (by decide), h.r4],
    by rw [k _ (by decide) (by decide), h.r5], by rw [k _ (by decide) (by decide), h.r6],
    by rw [k _ (by decide) (by decide), h.r7], by rw [ub.other _ (by decide), ka]; rfl,
    by rw [ub.gpr, ka, ofNat_pred32 n1],
    by rw [hm]; exact h.frame, by rw [hm]; exact h.kept, fun k hk => by rw [hm]; exact h.done k hk,
    ?_, ?_⟩
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (rr s₀) (bytesAt m (bA s₀) (128 * rr s₀)) % NN s₀

theorem jOf_lt {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < NN s₀ :=
  Nat.mod_lt _ (NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {s₀ : State} (hp : Pre s₀) (m : Mem) :
    m.readW (bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 32 &&& BitVec.ofNat 32 (NN s₀ - 1) =
      BitVec.ofNat 32 (jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  have hN := NN_lt hp
  have he' : e ≤ 32 := by
    by_contra hc
    have : 2 ^ 32 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := jOf_lt hp m; omega), he, and_mask32 _ he',
    jOf, he, integerify_mod32 _ _ hp.pos he']

theorem jOf_lt32 {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < 2 ^ 32 := by
  have := jOf_lt hp m; have := NN_lt hp; omega

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s)
    {m₄ : Mem}
    (f₄ : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩]
      (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bA s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (bA s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bA s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) (tP s₀) (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀] s₀.mem m₄ ∧ Kept s₀ m₄ ∧
    (∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bA s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bA s₀) (128 * rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop (i + 1) := by
  have lt := r_lt hp
  have hj := jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (bA s₀) (128 * rr s₀))
    (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)) with hT
  have hl : T.length = 128 * rr s₀ := by
    rw [hT, xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have hself : bytesAt (writeBytes s.mem (tP s₀) T) (tP s₀) (128 * rr s₀) = T := by
    have := bytesAt_writeBytes_self s.mem (tP s₀) T (by rw [hl]; omega)
    rwa [hl] at this
  have f₂ : Frame [⟨tP s₀, 128 * rr s₀⟩] s.mem (writeBytes s.mem (tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀] s.mem (writeBytes s.mem (tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  have hv : ∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) :=
    fun k hk => by
      rw [call_keeps_v hp f₄ hk, bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (vAt_s hp hk).sub_right (t_sub hp)) (by omega)]
      exact h.v k hk
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  refine ⟨(h.frame.trans f₂').trans (call_frame f₄),
    call_kept hp f₄ (h.kept.frame f₂ fun r hr => ?_), hv, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact keep_t hp
  · rw [← h.x, e, mixLoop_succ_fst, b₄, hself, hT, vList_getD _ hj, h.v _ hj]
  · have hs := h.js
    rw [e, mixLoop_succ_snd, vList_getD _ hj, ← h.v _ hj] at hs
    rw [← List.tail_drop, ← hs, b₄, hself, hT]
    rfl

/-- `jBlock`: `r0 = j`. -/
theorem j_ok {s₀ : State} (hp : Pre s₀) {s : State} (h4 : s.gpr .r4 = bP s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)) (h9 : s.gpr .r9 = BitVec.ofNat 32 (NN s₀ - 1))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block jBlock) s fun s' => Upd s s' .r0 (BitVec.ofNat 32 (jOf s₀ s.mem)) := by
  have lt := r_lt hp
  have := hp.pos
  have hb := hp.b_nw
  unfold jBlock
  refine wp_add (op2_reg _ _) fun a ua => wp_sub (op2_imm (by decide)) fun b ub => ?_
  refine wp_ldr (a := bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) (by decide)
    (by rw [ub.gpr, ua.gpr, h4, h7, sub32 _ (by omega), add_zero32,
      addr_add (by omega)])
    (by rw [ub.rd, ub.wr, ua.rd, ua.wr, hrd, hwr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega)))
    fun d ud => wp_and (op2_reg _ _) fun e ue => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [ue.mem, ud.mem, ub.mem, ua.mem], by rw [ue.rd, ud.rd, ub.rd, ua.rd],
    by rw [ue.wr, ud.wr, ub.wr, ua.wr], by rw [ue.sp, ud.sp, ub.sp, ua.sp]⟩
  · rw [ue.gpr, ud.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h9,
      ub.mem, ua.mem, jOf_eq hp]
  · rw [ue.other _ hr, ud.other _ hr, ub.other _ hr, ua.other _ hr]

/-- The address of `V[j]`, as `mulLoop` computes it. -/
theorem vAt_mul (s₀ : State) (j : Nat) :
    vP s₀ + BitVec.ofNat 32 (j * (128 * rr s₀)) = vAt32 s₀ j := by
  rw [Nat.mul_comm]

/-- One iteration of step 3. -/
theorem step3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    WP isa (step3 c) s fun s' => Inv3 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  have hj := jOf_lt hp s.mem
  have hb := hp.b_nw
  have e4 : 4 * (32 * rr s₀) = 128 * rr s₀ := by omega
  unfold step3
  refine WP.seq (WP.mono (j_ok hp h.r4 h.r7 h.r9 h.rd h.wr) fun a ua => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun b ub => wp_mov (op2_reg _ _) fun b' ub' =>
    WP.block_nil ?_)
  refine WP.seq (WP.mono (mulLoop_ok (j := jOf s₀ s.mem) (c := 128 * rr s₀) (a := vP s₀)
    (jOf_lt32 hp s.mem)
    (by rw [ub'.other _ (by decide), ub.other _ (by decide), ua.gpr])
    (by rw [ub'.other _ (by decide), ub.gpr, ua.other _ (by decide), h.r5])
    (by rw [ub'.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r7]))
    fun m ⟨rdm, wrm, spm, memm, om, m1⟩ => ?_)
  rw [vAt_mul] at m1
  have km : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → m.gpr r = s.gpr r := fun r h0 h1 h2 h3 => by
    rw [om r h0 h1 h2 h3, ub'.other r h2, ub.other r h1, ua.other r h0]
  refine WP.seq (wp_mov (op2_reg _ _) fun d ud => wp_add (op2_imm (by decide)) fun e ue =>
    wp_mov (op2_lsr (by decide)) fun f uf => WP.block_nil ?_)
  have rdf : f.rd = s₀.rd := by rw [uf.rd, ue.rd, ud.rd, rdm, ub'.rd, ub.rd, ua.rd, h.rd]
  have wrf : f.wr = s₀.wr := by rw [uf.wr, ue.wr, ud.wr, wrm, ub'.wr, ub.wr, ua.wr, h.wr]
  have spf : f.sp = s₀.sp := by rw [uf.sp, ue.sp, ud.sp, spm, ub'.sp, ub.sp, ua.sp, h.sp]
  have mf : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, memm, ub'.mem, ub.mem, ua.mem]
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h0, h1, h2, h3⟩ := pres_ne r hr
    rw [uf.other _ h3, ue.other _ h2, ud.other _ h0, km r h0 h1 h2 h3]
  refine WP.seq (WP.mono (xorLoop_ok (x := bP s₀) (y := vAt32 s₀ (jOf s₀ s.mem)) (d := tP32 s₀)
    (n := 32 * rr s₀) (by omega) (by omega) (by omega)
    (by rw [e4]; exact vAt_nw hp hj) (by rw [e4]; exact t_nw hp)
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, km _ (by decide) (by decide)
      (by decide) (by decide), h.r4])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), m1])
    (by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), km _ (by decide) (by decide)
      (by decide) (by decide), h.r6]; rfl)
    (by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), km _ (by decide) (by decide)
      (by decide) (by decide), h.r7, sh2 hp])
    (fun k hk => by rw [rdf, wrf]; exact b_word hp hk)
    (fun k hk => by rw [rdf, wrf]; exact InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [wrf]; exact t_word hp hk)
    (by rw [e4, t_addr hp]; exact t_b hp)
    (by rw [e4, t_addr hp, vAt_addr hp hj]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [mf, e4, t_addr hp, vAt_addr hp hj] at mt
  have kt : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r := fun r hr hlr => by
    obtain ⟨h0, h1, h2, h3⟩ := pres_ne r hr
    rw [gt r h0 h1 h2 h3 (by rintro rfl; simp [preserved] at hr) hlr, kf r hr]
  have ft : Frame [bR s₀, vR s₀, scR s₀] s₀.mem t.mem := by
    rw [mt]
    refine h.frame.trans (Proof.Sha256.Stream.writeBytes_frame (R := ⟨tP s₀, 128 * rr s₀⟩)
      _ _ _ ?_ |>.sub fun r hr => ?_)
    · rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
      exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_add (op2_imm (by decide)) fun q1 v1 => ?_))
  have kq : ∀ r ∈ preserved, r ≠ .lr → q1.gpr r = s.gpr r := fun r hr hlr => by
    rw [v1.other _ (pres_ne r hr).1, kt r hr hlr]
  refine bm_ok hS hp (srcOK_t hp) (by rw [v1.gpr, kt _ (by decide) (by decide), h.r6]; rfl)
    (by rw [kq _ (by decide) (by decide), h.r4]) (by rw [kq _ (by decide) (by decide), h.r7])
    (by rw [v1.sp, spt, spf]) (by rw [v1.rd, rdt, rdf]) (by rw [v1.wr, wrt, wrf])
    (by rw [v1.mem]; exact ft) fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [v1.mem, mt] at f4 b4
  rw [t_addr hp] at b4
  obtain ⟨F, K, V, X, J⟩ := mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, r ≠ .lr → s4.gpr r = s.gpr r := fun r hr hlr => by
    rw [cs4 r hr hlr, kq r hr hlr]
  refine wp_subs (op2_imm (by decide)) fun s5 u5 z5 => WP.block_nil ?_
  have k5 : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r8 → s5.gpr r = s.gpr r := fun r hr hlr h1 => by
    rw [u5.other _ h1, k4 r hr hlr]
  have e8 : s4.gpr .r8 = BitVec.ofNat 32 (NN s₀ - i) := by
    rw [k4 _ (by decide) (by decide), h.r8]
  refine ⟨⟨by omega, by rw [u5.rd, rd4, v1.rd, rdt, rdf], by rw [u5.wr, wr4, v1.wr, wrt, wrf],
    by rw [u5.sp, sp4, v1.sp, spt, spf],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r4],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r5],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r6],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r7], by rw [u5.gpr, e8, dec_count hi],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r9],
    by rw [u5.mem]; exact F, by rw [u5.mem]; exact K, by rw [u5.mem]; exact V,
    by rw [u5.mem]; exact X, by rw [u5.mem]; exact J⟩, by rw [z5, e8, dec_z hi hN]⟩

theorem loop3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv3 s₀ 0 s) : WP isa (.loop (step3 c) .ne) s (Inv3 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv3 s₀) (fun _ hi _ h => step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem epilogue_eq : rmEpilogue =
    (rmSaved.take 6).map (fun p => Instr.ldr p.1 .r6 p.2) ++ ([.ldr .r6 .r6 152] : List Instr) := rfl

theorem rmSaved_r6 : ∀ p ∈ rmSaved.take 6, p.1 ≠ .r6 := by decide

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv3 s₀ (NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) := by
  have hs := hp.s_nw
  have hin : ∀ d, d + 4 ≤ 256 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (scA s₀ + BitVec.ofNat 64 d) 4 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]
    exact InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ hd)
  have sv : ∀ p ∈ rmSaved, s.mem.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1 := h.kept.1
  rw [epilogue_eq]
  refine restoreList_ok _ s _ (by decide) (fun p hp' => ?_) fun s₁ hl ho hm hrd hwr hsp => ?_
  · have hb := saved_offs p (List.mem_of_mem_take hp')
    rw [h.r6]
    exact ⟨rmSaved_r6 p hp', by omega, by omega, hin _ (by omega) _ rfl rfl⟩
  have e6 : s₁.gpr .r6 = sc s₀ := by rw [ho _ (by decide), h.r6]
  refine wp_ldr (a := scA s₀ + BitVec.ofNat 64 152) (by decide) (by rw [e6, addr_add (by omega)])
    (hin _ (by omega) _ hrd hwr) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨by rw [u₂.mem, hm], by rw [u₂.sp, hsp], fun p hp' => ?_⟩
  by_cases h6 : p.1 = .r6
  · have : p = (.r6, 152) := by
      revert h6; revert hp'; revert p; decide
    subst this
    rw [u₂.gpr, hm, sv (.r6, 152) (by decide)]
  · have hp6 : p ∈ rmSaved.take 6 := by
      revert h6; revert hp'; revert p; decide
    rw [u₂.other _ h6, hl p hp6, h.r6]
    exact sv p hp'

/-! ## The whole function -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block rmPrologue) s₀ (P1 s₀) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g g12 hrd hwr hsp hf hsv => setup_ok hp g g12 hrd hwr hsp hf hsv

theorem correct {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (roMixWith c) s₀ fun s' => (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧
      Proof.Scrypt.roMixArm.post s₀ s' := by
  unfold roMixWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (nloop_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup2_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop2_ok hS hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (loop3_ok hS hp h₅) fun s₆ h₆ => ?_)
  refine WP.mono (restore_ok hp h₆) fun s' ⟨hm', hsp', hg'⟩ => ⟨hg', hsp'.trans h₆.sp, ?_⟩
  show bytesAt s'.mem (bA s₀) (128 * rr s₀) = roMix (rr s₀) (NN s₀) (B s₀)
  rw [hm', ← h₆.x, Nat.sub_self]
  rfl

end VG.Proof.Scrypt.Arm.RoMix

/-!
# scryptROMix on 32-bit ARM: verified

`BlockMixSpec` of the verified `vg_scrypt_blockmix`, from its `Verified` proof
by `WP.callCalls`; then constant time, up to the indices `j`, as on AArch64
(`Proof/Scrypt/AArch64/RoMixCT.lean`): we relate two runs (`RelCT`).
Correctness determines our registers from the public arguments, so they agree
between the calls, where the taint analysis proves each piece constant time;
the calls are constant time by scryptBlockMix's own proof. In step 3, the
address of `V[j]` depends on `j`, which the contract declares public: the two
runs compute the same `j`, since both compute their indices in order
(`Inv3.js`) and agree on the whole list.
-/

namespace VG.Proof.Scrypt.Arm.RoMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm op2_lsr eval_ne)
open VG.Proof.Scrypt.Arm.BlockMix (covers_of_in)
open VG.Proof.Scrypt.Memory (InRegions.right)

/-! ## The call of `vg_scrypt_blockmix` -/

theorem covers_of_all {rs rs' : List Region} (h : ∀ R ∈ rs, Covers [R] rs') : Covers rs rs' :=
  fun x n ⟨r, hr, hc⟩ => h r hr x n ⟨_, List.mem_singleton_self _, hc⟩

theorem stackArg_entry (s : State) (rd wr : List Region) :
    stackArg (s.callEntry.withRegions rd wr) 0 = stackArg s 0 := rfl

theorem stackArgAddr_entry (s : State) (rd wr : List Region) :
    stackArgAddr (s.callEntry.withRegions rd wr) 0 = stackArgAddr s 0 := rfl

theorem bm_pre {s : State} {src dst scr : BitVec 32} {r : Nat} (h0 : s.gpr .r0 = src)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 r) (h2 : s.gpr .r2 = dst) (h3 : s.gpr .r3 = BitVec.ofNat 32 r)
    (h4 : stackArg s 0 = scr) (hr : 0 < r) (hlt : 128 * r < 2 ^ 32)
    (hds : Region.Disjoint ⟨State.addr dst, 128 * r⟩ ⟨State.addr scr, 128⟩)
    (hsd : Region.Disjoint ⟨State.addr src, 128 * r⟩ ⟨State.addr dst, 128 * r⟩)
    (hss : Region.Disjoint ⟨State.addr src, 128 * r⟩ ⟨State.addr scr, 128⟩)
    (had : Region.Disjoint ⟨stackArgAddr s 0, 4⟩ ⟨State.addr dst, 128 * r⟩)
    (has : Region.Disjoint ⟨stackArgAddr s 0, 4⟩ ⟨State.addr scr, 128⟩)
    (nsrc : src.toNat + 128 * r ≤ 2 ^ 32) (ndst : dst.toNat + 128 * r ≤ 2 ^ 32)
    (nscr : scr.toNat + 128 ≤ 2 ^ 32) (nsp : s.sp.toNat + 4 ≤ 2 ^ 32)
    (isrc : InRegions (s.rd ++ s.wr) (State.addr src) (128 * r))
    (iarg : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4)
    (idst : InRegions s.wr (State.addr dst) (128 * r)) (iscr : InRegions s.wr (State.addr scr) 128) :
    Proof.Scrypt.blockMixArm.pre (s.callEntry.withRegions
      [⟨State.addr src, 128 * r⟩, ⟨stackArgAddr s 0, 4⟩]
      [⟨State.addr dst, 128 * r⟩, ⟨State.addr scr, 128⟩]) ∧
    Covers ([⟨State.addr src, 128 * r⟩, ⟨stackArgAddr s 0, 4⟩] ++
      [⟨State.addr dst, 128 * r⟩, ⟨State.addr scr, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨State.addr dst, 128 * r⟩, ⟨State.addr scr, 128⟩] s.wr := by
  have tr : (BitVec.ofNat 32 r).toNat = r := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  refine ⟨?_, covers_of_all fun R hR => ?_, covers_of_all fun R hR => ?_⟩
  · simp only [Proof.Scrypt.blockMixArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, stackArg_entry,
      stackArgAddr_entry,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3, h4, tr, c128]
    exact ⟨trivial, trivial, hds, hsd, hss, had, has, nsrc, ndst, nscr, nsp, trivial, hr⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · exact covers_of_in isrc
    · exact covers_of_in iarg
    · intro a n h
      obtain ⟨R', hR', hc'⟩ := covers_of_in idst a n h
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
    · intro a n h
      obtain ⟨R', hR', hc'⟩ := covers_of_in iscr a n h
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact covers_of_in idst
    · exact covers_of_in iscr

theorem blockMixSpec : BlockMixSpec Impl.Scrypt.Arm.blockMix := by
  intro s src dst scr r h0 h1 h2 h3 h4 hr hlt hds hsd hss had has nsrc ndst nscr nsp isrc iarg
    idst iscr Q hQ
  have tr : (BitVec.ofNat 32 r).toNat = r := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨p, c₁, c₂⟩ := bm_pre h0 h1 h2 h3 h4 hr hlt hds hsd hss had has nsrc ndst nscr nsp isrc
    iarg idst iscr
  refine WP.callCalls (k := Proof.Scrypt.blockMixArm) BlockMix.blockMix_correct p c₁ c₂ ?_
  intro s₂ hrd hwr hsp' hf hcs _ hpost
  simp only [Proof.Scrypt.blockMixArm, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, tr] at hpost
  exact hQ s₂ hrd hwr hsp' hcs hf hpost

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  sp : s₀.sp = s₀'.sp
  a0 : stackArg s₀ 0 = stackArg s₀' 0

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.rr : rr s₀ = rr s₀' := by simp only [RoMix.rr, hq.r1]
theorem PubEq.NN : NN s₀ = NN s₀' := by simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.r1, hq.r3]
theorem PubEq.vAt32 (i : Nat) : vAt32 s₀ i = vAt32 s₀' i := by
  simp only [RoMix.vAt32, RoMix.vP, RoMix.rr, hq.r1, hq.r2]
theorem PubEq.tP32 : tP32 s₀ = tP32 s₀' := by simp only [RoMix.tP32, RoMix.sc, hq.a0]

end

/-- The registers the loops keep, with `r9 = bp` and `r8 = q`, and the
memory outside our regions (the stack arguments). -/
structure KR (s₀ : State) (bp q : BitVec 32) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r8 : s.gpr .r8 = q
  r9 : s.gpr .r9 = bp
  frame : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9]

theorem kRegs_ne : ∀ r ∈ kRegs, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by decide

theorem kRegs_pres : ∀ r ∈ kRegs, r ∈ preserved ∧ r ≠ .lr ∧ r ∉ linkRegs := by decide

theorem KR.keep {s₀ : State} {bp q : BitVec 32} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hk : ∀ r ∈ kRegs, s'.gpr r = s.gpr r) (hf : Frame [bR s₀, vR s₀, scR s₀] s.mem s'.mem) :
    KR s₀ bp q s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hk _ (by decide)).trans h.r4,
    (hk _ (by decide)).trans h.r5, (hk _ (by decide)).trans h.r6, (hk _ (by decide)).trans h.r7,
    (hk _ (by decide)).trans h.r8, (hk _ (by decide)).trans h.r9, h.frame.trans hf⟩

/-- Whether an instruction writes none of `kRegs`. -/
def kFree (i : Instr) : Bool := kRegs.all fun r => dstOf i != some r

/-- `KR` survives code that writes none of its registers. -/
theorem KR.exec {c : Prog isa} (hc : c.allInstrs kFree = true) (hn : c.noFrames = true)
    {s₀ : State} (hw : s₀.wr = [bR s₀, vR s₀, scR s₀]) {bp q : BitVec 32} {s s' : State}
    {t : List Leak} (he : Exec isa c s t s') (h : KR s₀ bp q s) : KR s₀ bp q s' := by
  obtain ⟨rd, wr, sp, f⟩ := Exec.regions he hn
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  refine h.keep rd wr sp (fun r hr => Exec.gpr (fun i hi => ?_) he (.inr (kRegs_pres r hr).2.2)) ?_
  · have := hc i hi
    simp only [kFree, List.all_eq_true, bne_iff_ne, ne_eq] at this
    exact this r hr
  · rw [h.wr, hw] at f; exact f

theorem Inv2.kr {s₀ : State} {i : Nat} {s : State} (h : Inv2 s₀ i s) :
    KR s₀ (vAt32 s₀ i) (BitVec.ofNat 32 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.r4, h.r5, h.r6, h.r7, h.r8, h.r9, h.frame⟩

theorem Inv3.kr {s₀ : State} {i : Nat} {s : State} (h : Inv3 s₀ i s) :
    KR s₀ (BitVec.ofNat 32 (NN s₀ - 1)) (BitVec.ofNat 32 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.r4, h.r5, h.r6, h.r7, h.r8, h.r9, h.frame⟩

/-- The registers `KR` fixes agree in two runs. -/
theorem agree_K {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : BitVec 32} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') {extra : List Reg}
    (hx : ∀ r ∈ extra, s.gpr r = s'.gpr r) :
    VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs (extra ++ kRegs)) s s' := by
  refine Taint.agree_ofRegs fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r4, h'.r4, bP, bP, hq.r0]
  · rw [h.r5, h'.r5, vP, vP, hq.r2]
  · rw [h.r6, h'.r6, sc, sc, hq.a0]
  · rw [h.r7, h'.r7, hq.rr]
  · rw [h.r8, h'.r8, hq']
  · rw [h.r9, h'.r9, hbp]

/-- The arguments of a call of `vg_scrypt_blockmix` from `A` into `b`. -/
structure Args (s₀ : State) (A : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = A
  r1 : s.gpr .r1 = BitVec.ofNat 32 (rr s₀)
  r2 : s.gpr .r2 = bP s₀
  r3 : s.gpr .r3 = BitVec.ofNat 32 (rr s₀)

theorem call_pre {s₀ : State} (hp : Pre s₀) {A : BitVec 32} (hA : SrcOK s₀ A) {bp q : BitVec 32}
    {s : State} (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    Proof.Scrypt.blockMixArm.pre (s.callEntry.withRegions
      [⟨State.addr A, 128 * rr s₀⟩, ⟨stackArgAddr s 0, 4⟩]
      [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩]) ∧
    Covers ([⟨State.addr A, 128 * rr s₀⟩, ⟨stackArgAddr s 0, 4⟩] ++
      [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] s.wr := by
  have lt := r_lt hp
  have ea := stackArgAddr_eq h.sp
  exact bm_pre ha.r0 ha.r1 ha.r2 ha.r3 (arg_keep hp h.frame h.sp rfl) hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [ea]; exact (hp.a_b.sub_left (arg4_sub s₀)).sub_right (b_sub' (s₀ := s₀)))
    (by rw [ea]; exact (hp.a_s.sub_left (arg4_sub s₀)).sub_right (w_sub (s₀ := s₀)))
    hA.nw (by have := hp.b_nw; omega) (by have := hp.s_nw; omega)
    (by rw [h.sp]; have := hp.sp_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr)
    (by rw [ea, h.rd, h.wr]; exact arg_in hp) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp)

theorem call_wp {s₀ : State} (hp : Pre s₀) {A : BitVec 32} (hA : SrcOK s₀ A) {bp q : BitVec 32}
    {s : State} (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    WP isa (.call "vg_scrypt_blockmix" Impl.Scrypt.Arm.blockMix) s (KR s₀ bp q) :=
  bm_call blockMixSpec hp hA ha.r0 ha.r1 ha.r2 ha.r3 h.sp h.rd h.wr h.frame
    fun _ rd wr sp cs f _ => h.keep rd wr sp
      (fun r hr => cs r (kRegs_pres r hr).1 (kRegs_pres r hr).2.1) (call_frame f)

theorem call_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
    {A A' : BitVec 32} (hA : SrcOK s₀ A) (hA' : SrcOK s₀' A') (hAA : A = A')
    {bp q bp' q' : BitVec 32} :
    RelCT isa (fun s s' => (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A' s'))
      (.call "vg_scrypt_blockmix" Impl.Scrypt.Arm.blockMix)
      fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' := by
  subst hAA
  have eb : bP s₀' = bP s₀ := hq.r0.symm
  have es : sc s₀' = sc s₀ := hq.a0.symm
  have er : rr s₀' = rr s₀ := hq.rr.symm
  have call := RelCT.call (n := "vg_scrypt_blockmix") (P := fun s s' =>
      (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A s'))
    BlockMix.blockMix_correct BlockMix.blockMix_ct
    [⟨State.addr A, 128 * rr s₀⟩, ⟨stackArgAddr s₀ 0, 4⟩]
    [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] fun s s' ⟨⟨h, ha⟩, ⟨h', ha'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_pre hp hA h ha
      obtain ⟨p₂, c₂, w₂⟩ := call_pre hp' hA' h' ha'
      rw [stackArgAddr_eq h.sp] at p₁ c₁
      have ea : stackArgAddr s₀' 0 = stackArgAddr s₀ 0 := by
        rw [stackArgAddr, stackArgAddr, hq.sp]
      rw [stackArgAddr_eq h'.sp, ea] at p₂ c₂
      simp only [bA, scA, eb, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂⟩
      simp only [Proof.Scrypt.blockMixArm, State.withRegions_gpr, State.withRegions_sp,
        State.callEntry_sp, stackArg_entry,
        State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), ha.r0, ha.r1, ha.r2, ha.r3,
        ha'.r0, ha'.r1, ha'.r2, ha'.r3, eb, er, h.sp, h'.sp, hq.sp,
        arg_keep hp h.frame h.sp rfl, arg_keep hp' h'.frame h'.sp rfl, es]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun s s' h => ⟨call_wp hp hA h.1.1 h.1.2, call_wp hp' hA' h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## Relating pieces of code -/

/-- Code that writes none of `kRegs` keeps `KR` in both runs. -/
theorem RelCT.keepK {P : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True)
    (hc : c.allInstrs kFree = true) (hn : c.noFrames = true) {s₀ s₀' : State}
    (hw : s₀.wr = [bR s₀, vR s₀, scR s₀]) (hw' : s₀'.wr = [bR s₀', vR s₀', scR s₀'])
    {bp q bp' q' : BitVec 32} (hk : ∀ s s', P s s' → KR s₀ bp q s ∧ KR s₀' bp' q' s') :
    RelCT isa P c fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' :=
  fun _ _ _ _ _ _ hp e e' =>
    ⟨(h _ _ _ _ _ _ hp e e').1, KR.exec hc hn hw e (hk _ _ hp).1, KR.exec hc hn hw' e' (hk _ _ hp).2⟩

theorem RelCT.assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ bc₁ =>
    cases bc₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ bc₂ =>
        cases bc₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          simp only [List.append_assoc] at ht
          exact ⟨ht, hq⟩

theorem RelCT.assoc4 {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ r₁ =>
    cases r₁ with
    | seq b₁ r₁ =>
      cases r₁ with
      | seq c₁ r₁ =>
        cases r₁ with
        | seq d₁ f₁ =>
          cases e₂ with
          | seq a₂ r₂ =>
            cases r₂ with
            | seq b₂ r₂ =>
              cases r₂ with
              | seq c₂ r₂ =>
                cases r₂ with
                | seq d₂ f₂ =>
                  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) f₁)
                    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) f₂)
                  simp only [List.append_assoc] at ht
                  exact ⟨ht, hq⟩

theorem RelCT.exists' {α : Type} {P : α → State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a, RelCT isa (P a) c Q) :
    RelCT isa (fun s s' => ∃ a, P a s s') c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e e' => h a _ _ _ _ _ _ hp e e'

/-! ## Setting up the calls -/

theorem tail_wp {s₀ : State} (hp : Pre s₀) {bp q A : BitVec 32} {s : State} (h : KR s₀ bp q s)
    (hA : s.gpr .r0 = A) :
    WP isa (.block bmTail) s fun s' => KR s₀ bp q s' ∧ Args s₀ A s' := by
  have lt := r_lt hp
  refine wp_mov (op2_lsr (by decide)) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_reg _ _) fun d ud => WP.block_nil ⟨?_, ?_⟩
  · exact h.keep (by rw [ud.rd, ub.rd, ua.rd]) (by rw [ud.wr, ub.wr, ua.wr])
      (by rw [ud.sp, ub.sp, ua.sp]) (fun r hr => by
        obtain ⟨-, h1, h2, h3⟩ := kRegs_ne r hr
        rw [ud.other _ h3, ub.other _ h2, ua.other _ h1])
      (by rw [ud.mem, ub.mem, ua.mem]; exact Frame.refl _ _)
  have h1 : a.gpr .r1 = BitVec.ofNat 32 (rr s₀) := by
    rw [ua.gpr, h.r7, shr_ofNat32 _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  exact ⟨by rw [ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), hA],
    by rw [ud.other _ (by decide), ub.other _ (by decide), h1],
    by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.r4],
    by rw [ud.gpr, ub.other _ (by decide), h1]⟩

theorem x2_wp {s₀ : State} (hp : Pre s₀) {bp q : BitVec 32} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block (([.mov .r0 (.reg .r9)] : List Instr) ++ bmTail)) s fun s' => KR s₀ bp q s' ∧ Args s₀ bp s' :=
  wp_mov (op2_reg _ _) fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp (fun r hr => ua.other r (kRegs_ne r hr).1)
      (by rw [ua.mem]; exact Frame.refl _ _)) (by rw [ua.gpr, h.r9])

theorem x3_wp {s₀ : State} (hp : Pre s₀) {bp q : BitVec 32} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block (([.dp .add .r0 .r6 (.imm 192)] : List Instr) ++ bmTail)) s
      fun s' => KR s₀ bp q s' ∧ Args s₀ (tP32 s₀) s' :=
  wp_add (op2_imm (by decide)) fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp (fun r hr => ua.other r (kRegs_ne r hr).1)
      (by rw [ua.mem]; exact Frame.refl _ _)) (by rw [ua.gpr, h.r6]; rfl)

/-! ## Step 2, in two runs -/

theorem eval_z {s : State} {b : Bool} (h : s.z = b) : isa.eval .ne s = some !b := by
  rw [← h]; exact eval_ne s

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s') (step2 Impl.Scrypt.Arm.blockMix)
      fun s s' => (Inv2 s₀ (i + 1) s ∧ s.z = decide (i + 1 = NN s₀)) ∧
        (Inv2 s₀' (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev : vAt32 s₀ i = vAt32 s₀' i := hq.vAt32 i
  have e15 : BitVec.ofNat 32 (NN s₀ - i) = BitVec.ofNat 32 (NN s₀' - i) := by rw [hq.NN]
  let K (t₀ t : State) : Prop := KR t₀ (vAt32 t₀ i) (BitVec.ofNat 32 (NN t₀ - i)) t
  have ac : RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s')
      (.seq (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r9), .mov .r2 (.shifted .r7 .lsr 2)])
        copyLoop)
      fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.kr h.2.kr ev e15 (by simp)) (by taint_decide))
      (by decide +kernel) (by decide +kernel) hp.wr hp'.wr fun _ _ h => ⟨h.1.kr, h.2.kr⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.mov .r0 (.reg .r9)] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (vAt32 s₀ i) s) ∧ (K s₀' s' ∧ Args s₀' (vAt32 s₀' i) s') :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x2_wp hp h.1, x2_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_v hp hi) (srcOK_v hp' hi') ev
    (bp := vAt32 s₀ i) (q := BitVec.ofNat 32 (NN s₀ - i)) (bp' := vAt32 s₀' i)
    (q' := BitVec.ofNat 32 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block [.dp .add .r9 .r9 (.reg .r7), .subs .r8 .r8 (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)
  have body := RelCT.assoc (ac.seq ((x.seq cl).seq e))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step2_ok blockMixSpec hp hi h.1, step2_ok blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s')
      (.loop (step2 Impl.Scrypt.Arm.blockMix) .ne)
      fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 Impl.Scrypt.Arm.blockMix)
    (c := .ne) (Q := fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv2 s₀ i s ∧ Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_z z, eval_z z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3 -/

theorem j_wp {s₀ : State} (hp : Pre s₀) {q : BitVec 32} {s : State}
    (h : KR s₀ (BitVec.ofNat 32 (NN s₀ - 1)) q s) {j : Nat} (hj : jOf s₀ s.mem = j) :
    WP isa (.block jBlock) s fun s' =>
      KR s₀ (BitVec.ofNat 32 (NN s₀ - 1)) q s' ∧ s'.gpr .r0 = BitVec.ofNat 32 j :=
  WP.mono (j_ok hp h.r4 h.r7 h.r9 h.rd h.wr) fun _ u =>
    ⟨h.keep u.rd u.wr u.sp (fun r hr => u.other r (kRegs_ne r hr).1)
      (by rw [u.mem]; exact Frame.refl _ _), by rw [u.gpr, hj]⟩

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i = jOf s₀ s.mem :: rest := by
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < NN s₀) (j : Nat) :
    RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧ (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j))
      (step3 Impl.Scrypt.Arm.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.z = decide (i + 1 = NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have e1 : BitVec.ofNat 32 (NN s₀ - 1) = BitVec.ofNat 32 (NN s₀' - 1) := by rw [hq.NN]
  have e15 : BitVec.ofNat 32 (NN s₀ - i) = BitVec.ofNat 32 (NN s₀' - i) := by rw [hq.NN]
  -- The registers `KR` fixes, in step 3's iteration `i`.
  let K (t₀ t : State) : Prop :=
    KR t₀ (BitVec.ofNat 32 (NN t₀ - 1)) (BitVec.ofNat 32 (NN t₀ - i)) t
  have jb : RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧
        (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j)) (.block jBlock) fun s s' =>
        (K s₀ s ∧ s.gpr .r0 = BitVec.ofNat 32 j) ∧ (K s₀' s' ∧ s'.gpr .r0 = BitVec.ofNat 32 j) :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1.kr h.2.1.kr e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨j_wp hp h.1.1.kr h.1.2, j_wp hp' h.2.1.kr h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have mx : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .r0 = BitVec.ofNat 32 j) ∧
        (K s₀' s' ∧ s'.gpr .r0 = BitVec.ofNat 32 j))
      (.seq (.block [.mov .r1 (.reg .r5), .mov .r2 (.reg .r7)]) <| .seq mulLoop <|
        .seq (.block [.mov .r0 (.reg .r4), .dp .add .r2 .r6 (.imm 192),
          .mov .r3 (.shifted .r7 .lsr 2)]) xorLoop) fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([.r0] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) (by taint_decide))
      (by decide +kernel) (by decide +kernel) hp.wr hp'.wr fun _ _ h => ⟨h.1.1, h.2.1⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.dp .add .r0 .r6 (.imm 192)] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (tP32 s₀) s) ∧ (K s₀' s' ∧ Args s₀' (tP32 s₀') s') :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x3_wp hp h.1, x3_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_t hp) (srcOK_t hp') hq.tP32
    (bp := BitVec.ofNat 32 (NN s₀ - 1)) (q := BitVec.ofNat 32 (NN s₀ - i))
    (bp' := BitVec.ofNat 32 (NN s₀' - 1)) (q' := BitVec.ofNat 32 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block [.subs .r8 .r8 (.imm 1)])
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)
  have body := jb.seq (RelCT.assoc4 (mx.seq ((x.seq cl).seq e)))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step3_ok blockMixSpec hp hi h.1.1,
    step3_ok blockMixSpec hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv3 s₀ i s ∧ Inv3 s₀' i s') (step3 Impl.Scrypt.Arm.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.z = decide (i + 1 = NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists' fun (j : Nat) => body3_rel_j hp hp' hq hi j).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := drop_js hi h
  obtain ⟨r', hr'⟩ := drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨jOf s₀ s.mem, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s')
      (.loop (step3 Impl.Scrypt.Arm.blockMix) .ne)
      fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 Impl.Scrypt.Arm.blockMix)
    (c := .ne) (Q := fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv3 s₀ i s ∧ Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_z z, eval_z z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

/-- The prologue's taint: the argument registers and the stack arguments are public. -/
def τPro : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, argLen := 4 }

omit hp' hq hL in
theorem wfPro : VG.Arm.Taint.Wf τPro s₀ := by
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by show s₀.sp.toNat + 4 ≤ 2 ^ 32; have := hp.sp_nw; omega, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  have e : (⟨State.addr s₀.sp, 4⟩ : Region) = ⟨stackArgAddr s₀ 0, 4⟩ := by simp [stackArgAddr]
  simp only [τPro, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.a_b.sub_left (arg4_sub s₀)
  · exact hp.a_v.sub_left (arg4_sub s₀)
  · exact hp.a_s.sub_left (arg4_sub s₀)

omit hL in
theorem agreePro : VG.Arm.Taint.Agree τPro s₀ s₀' := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wfPro hp, wfPro hp',
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hq.sp,
    fun k hk => ?_⟩
  · simp only [τPro, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hq.r0
    · exact hq.r1
    · exact hq.r2
    · exact hq.r3
  · simp only [τPro] at hk
    rw [BlockMix.argByte_eq, BlockMix.argByte_eq, Mem.readW_byte s₀.mem _ hk,
      Mem.readW_byte s₀'.mem _ hk]
    exact congrArg _ hq.a0

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.Arm.roMix fun _ _ => True := by
  show RelCT isa _ (roMixWith Impl.Scrypt.Arm.blockMix) _
  unfold roMixWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => P1 s₀ s ∧ P1 s₀' s' :=
    ((RelCT.taint (A := taint) τPro (P := fun s s' => s = s₀ ∧ s' = s₀')
      (fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact agreePro hp hp' hq)
      (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := P1 s₀) (F₂ := P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => P1 s₀ s ∧ P1 s₀' s') nLoop fun s s' => N1 s₀ s ∧ N1 s₀' s' :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r0, .r1, .r2])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.r0, h'.r0, hq.rr]
        · rw [h.r1, h'.r1]
        · rw [h.r2, h'.r2, RoMix.vl, RoMix.vl, hq.r3]) (c := nLoop) (by taint_decide)).wp
      fun _ _ h => ⟨nloop_ok hp h.1, nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => N1 s₀ s ∧ N1 s₀' s') (.block rmSetup)
      fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r1, .r5, .r6])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.r1, h'.r1, hq.NN]
        · rw [h.r5, h'.r5, vP, vP, hq.r2]
        · rw [h.r6, h'.r6, sc, sc, hq.a0]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨setup2_ok hp h.1, setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s') (.block rmMid)
      fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r6])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.r6, h'.r6, sc, sc, hq.a0]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok hp h.1, mid_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r6])
      (fun _ _ h => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.r6, h.2.r6, sc, sc, hq.a0]) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((loop2_rel hp hp' hq).seq
    (md.seq ((loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixArm.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.1, h.2.2.2.2.2.1⟩

/-- No instruction of ROMix, or of the functions it calls, writes `r10` or `r11`. -/
theorem others_kept :
    (instrs Impl.Scrypt.Arm.roMix).all
      (fun i => [Reg.r10, .r11].all fun r => dstOf i != some r) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem preserved_cases :
    ∀ r ∈ preserved, r ∈ rmSaved.map Prod.fst ∨ r ∈ [Reg.r10, .r11] := by
  decide

/-- A state satisfying the precondition: `b` at `0x1000`, `v` at `0x2000`
(`N = 1`) and the scratch space at `0x3000` (384 bytes), passed on the stack
at `0x5000` with its length in 128-byte blocks. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x30 else if a = 0x5004 then 3 else 0
  rd := [⟨0x5000, 8⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩]

theorem roMix_correct (s : State) (hs : Proof.Scrypt.roMixArm.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.Arm.roMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.roMixArm.post s s' := by
  obtain ⟨t, s', he, hk, hsp, hpost⟩ := correct blockMixSpec (pre_of hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, hpost⟩
  rcases preserved_cases r hr with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact hk p hp
  · have hc := others_kept
    rw [List.all_eq_true] at hc
    refine Exec.gpr (fun i hi => ?_) he (.inr (by revert h; revert r; decide))
    have := hc i hi
    simp only [List.all_eq_true, bne_iff_ne, ne_eq] at this
    exact this r h

theorem roMix_ct : ConstantTime isa Proof.Scrypt.roMixArm.pre Proof.Scrypt.roMixArm.pub
    Impl.Scrypt.Arm.roMix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (roMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hpub.2.2.2.2.2.2.2
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem roMix_verified :
    Verified Arm.target Impl.Scrypt.Arm.roMix (Spec.Scrypt.roMixContract Arm.abi) :=
  Verified.of_correct roMix_correct roMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      post := by
        sig_implies_post [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      pub := by
        sig_implies_pub [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      sat := by
        implies_sat [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
          [Proof.Scrypt.Arm.RoMix.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
          using Proof.Scrypt.Arm.RoMix.satState }

end VG.Proof.Scrypt.Arm.RoMix
