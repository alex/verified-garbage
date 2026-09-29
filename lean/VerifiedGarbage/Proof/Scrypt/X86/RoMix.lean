import VerifiedGarbage.Proof.Scrypt.X86.Common
import VerifiedGarbage.Proof.Scrypt.RoMix
import VerifiedGarbage.Impl.Scrypt.X86.RoMix

/-!
# scryptROMix on x86 (32-bit): the precondition

Untrusted: everything here is checked by Lean. The regions the function
works on, and `BlockMixSpec`: what a call of `vg_scrypt_blockmix` in a frame
of its arguments does (the verified one meets it:
`Proof/Scrypt/X86/RoMixCT.lean`). As on 32-bit ARM
(`Proof/Scrypt/Arm/RoMix.lean`), with the pointers and lengths read from the
arguments on the stack, which nothing writes, and the calls using the 36
bytes below `esp` (`stkR`), which the memory frames include.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blockMix integerify leNat)
open VG.Proof.Scrypt (bytesAt_add' bytesAt_length' leNat_append leNat_bytesAt blk_bytesAt')
open VG.Proof.Sha256.X86.Stream (addr_toNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off
  disj_off InRegions.of_mem)

/-! ## What a call of `vg_scrypt_blockmix` does -/

/-- A call of `c`, in a frame of its arguments pushed from `esi`, `ecx`,
`edx`, `ecx` and `eax`, writes scryptBlockMix of the `128 r` bytes at `esi`
to `edx`, with the 128 bytes at `eax` as working space, using the 36 bytes
below `esp`. -/
def BlockMixSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (src dst scr : BitVec 32) (r : Nat), s.gpr .esi = src →
    s.gpr .ecx = BitVec.ofNat 32 r → s.gpr .edx = dst → s.gpr .eax = scr → 0 < r → 128 * r < 2 ^ 32 →
    Region.Disjoint ⟨dst.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩ →
    Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨dst.setWidth 64, 128 * r⟩ →
    Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩ →
    src.toNat + 128 * r ≤ 2 ^ 32 → dst.toNat + 128 * r ≤ 2 ^ 32 → scr.toNat + 128 ≤ 2 ^ 32 →
    36 ≤ (s.gpr .esp).toNat →
    (below (s.gpr .esp) 36).Disjoint ⟨src.setWidth 64, 128 * r⟩ →
    (below (s.gpr .esp) 36).Disjoint ⟨dst.setWidth 64, 128 * r⟩ →
    (below (s.gpr .esp) 36).Disjoint ⟨scr.setWidth 64, 128⟩ →
    InRegions (s.rd ++ s.wr) (src.setWidth 64) (128 * r) → InRegions s.wr (dst.setWidth 64) (128 * r) →
    InRegions s.wr (scr.setWidth 64) 128 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨dst.setWidth 64, 128 * r⟩, ⟨scr.setWidth 64, 128⟩, below (s.gpr .esp) 36] s.mem s'.mem →
        bytesAt s'.mem (dst.setWidth 64) (128 * r) =
          blockMix r (bytesAt s.mem (src.setWidth 64) (128 * r)) → Q s') →
    WP isa (.frame (.push [.eax, .ecx, .edx, .ecx, .esi]) (.call "vg_scrypt_blockmix" c) (.pop .eax 5)) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev bP : BitVec 32 := arg s₀ 0
abbrev rr : Nat := (arg s₀ 1).toNat
abbrev vP : BitVec 32 := arg s₀ 2
abbrev vl : Nat := (arg s₀ 3).toNat
abbrev sc : BitVec 32 := arg s₀ 4
/-- `N`. -/
abbrev NN : Nat := vl s₀ / rr s₀
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev vA : Addr := (vP s₀).setWidth 64
abbrev scA : Addr := (sc s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, rr s₀ * 128⟩
abbrev vR : Region := ⟨vA s₀, vl s₀ * 128⟩
abbrev scR : Region := ⟨scA s₀, (rr s₀ + 2) * 128⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The stack the calls use. -/
abbrev stkR : Region := below (esp₀ s₀) 36
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) (128 * rr s₀)
/-- `V[i]`. -/
abbrev vAt (i : Nat) : Addr := vA s₀ + BitVec.ofNat 64 (128 * rr s₀ * i)
/-- `V[i]`, as the pointer the code computes. -/
abbrev vAt32 (i : Nat) : BitVec 32 := vP s₀ + BitVec.ofNat 32 (128 * rr s₀ * i)
/-- `T`. -/
abbrev tP : Addr := scA s₀ + BitVec.ofNat 64 192
abbrev tP32 : BitVec 32 := sc s₀ + BitVec.ofNat 32 192

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ rmSaved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

/-- The regions the function writes, and the stack its calls use. -/
abbrev frs : List Region := [bR s₀, vR s₀, scR s₀, stkR s₀]

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
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_v : (retR s₀).Disjoint (vR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_v : (stkR s₀).Disjoint (vR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  v_nw : (vP s₀).toNat + vl s₀ * 128 ≤ 2 ^ 32
  s_nw : (sc s₀).toNat + (rr s₀ + 2) * 128 ≤ 2 ^ 32
  sp_lo : 36 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32
  pos : 0 < rr s₀
  vl_eq : vl s₀ = rr s₀ * NN s₀
  pow : (NN s₀).isPowerOfTwo

/-- The 36 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 36 ≤ E.toNat) : below E 36 = ⟨E.setWidth 64 - 36, 36⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem pre_of {s₀ : State} (h : Proof.Scrypt.roMixX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23⟩ := h
  have e := stk_eq h18
  simp only [h23] at h2 h4 h5 h8 h11 h14 h17
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by rw [stkR, e]; exact h12,
    by rw [stkR, e]; exact h13, by rw [stkR, e]; exact h14, h15, h16, h17, h18, h19, h20, ?_, h22⟩
  exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h21)).symm

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
theorem vAt_addr {i : Nat} (hi : i < NN s₀) : (vAt32 s₀ i).setWidth 64 = vAt s₀ i := by
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

theorem t_addr : (tP32 s₀).setWidth 64 = tP s₀ := addr_add (by have := hp.s_nw; omega)

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

/-- The argument words are in the arguments' region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) :
    Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    addr_eq (by omega)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) :
    InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 := by
  have hs := hp.sp_fit
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  show (addr (esp₀ s₀) d - addr (esp₀ s₀) 4).toNat + 4 ≤ 24
  rw [addr_eq (by omega), addr_eq (by omega),
    show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains, argAddr] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₁
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    addr_eq (by omega)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The arguments are kept by anything that writes only our regions and the
stack below `esp`. -/
theorem arg_keep {m : Mem} (hf : Frame (frs s₀) s₀.mem m) {d : Nat} (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ 28) : m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.a_b.sub_left (arg_sub hp hd₁ hd)
  · exact hp.a_v.sub_left (arg_sub hp hd₁ hd)
  · exact hp.a_s.sub_left (arg_sub hp hd₁ hd)
  · exact (stk_arg hp).symm.sub_left (arg_sub hp hd₁ hd)

/-- Argument `i`, read from memory that differs from the initial one only in
our regions and the stack below `esp`. -/
theorem arg_read {m : Mem} (hf : Frame (frs s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i :=
  arg_keep hp hf (by omega) (by omega)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    (scR s₀).Contains (scA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off (by omega) (by omega)

/-! ## What stays in `scratch`: our caller's registers -/

/-- Bytes `[128, 192)` of `scratch`. -/
abbrev keepR (s₀ : State) : Region := ⟨scA s₀ + BitVec.ofNat 64 128, 64⟩

theorem word_sub (s₀ : State) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 4 ≤ 192) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 d, 4⟩ (keepR s₀) := by
  rw [show d = 128 + (d - 128) by omega, ← add_ofNat]
  exact sub_off (by omega) (by omega)

theorem saved_offs : ∀ p ∈ rmSaved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 144 ∧ p.1 ≠ .eax := by decide

theorem Saved.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (keepR s₀).Disjoint r) : Saved s₀ m' := by
  intro p hp
  have ho := saved_offs p hp
  rw [← h p hp]
  exact hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (word_sub s₀ ho.1 (by omega))) (by decide)

theorem keep_sub (s₀ : State) : Region.Sub (keepR s₀) (scR s₀) := s_sub s₀ (by omega)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem keep_b : (keepR s₀).Disjoint (bR s₀) := hp.b_s.symm.sub_left (keep_sub s₀)
theorem keep_v : (keepR s₀).Disjoint (vR s₀) := hp.v_s.symm.sub_left (keep_sub s₀)
theorem keep_stk : (keepR s₀).Disjoint (stkR s₀) := hp.stk_s.symm.sub_left (keep_sub s₀)

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

end

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

theorem shr_ofNat32 {a : Nat} (n : Nat) (h : a < 2 ^ 32) :
    BitVec.ofNat 32 a >>> n = BitVec.ofNat 32 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

end VG.Proof.Scrypt.X86.RoMix
