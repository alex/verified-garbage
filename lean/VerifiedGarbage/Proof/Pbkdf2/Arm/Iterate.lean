import VerifiedGarbage.Proof.Pbkdf2.Hmac
import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.Arm.Contract
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Hmac.Arm.Init
import VerifiedGarbage.Impl.Pbkdf2.Arm
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Spec.Pbkdf2.Contract
import VerifiedGarbage.Proof.Pbkdf2.Arm.Lit

/-!
# PBKDF2-HMAC-SHA-256's iteration on ARMv7: the parts of a step

The same structure as the x86-64 and AArch64 proofs
(`Proof/Pbkdf2/X86_64/Iterate.lean`, `VG.Proof.Pbkdf2.AArch64`), with the same
target-independent memory lemmas (`VG.Proof.Pbkdf2.Memory`). Each step is two
calls of `vg_sha256_compress`, used as a black box through its proof
(`compressAt_ok`, from the streaming SHA-256 proof). The hash value being
compressed is `t`, and `T` is kept in `scratch[160..192)`.
-/

namespace VG.Proof.Pbkdf2

open Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open Spec.Sha256 (Repr bytesAt)

open VG.Arm in
/-- 32-bit ARM contract for `vg_pbkdf2_hmac_sha256_iterate(key: *const [u8;
192], u: *const [u8; 32], n: u32, t: *mut [u8; 32], scratch: *mut [u64; 48])`:
if, for a 64-byte key `K₀`, the streaming state at `key` represents `K₀ ⊕ ipad`
and the one at `key + 96` represents `K₀ ⊕ opad`, runs `n` steps `U ←
HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` from the `U` at `u` and the `T` at `t`,
leaving the final `T` at `t`.

Under AAPCS, `key`, `u`, `n` and `t` are in `r0`–`r3`, and `scratch` is the
stack argument 0. The code may read that argument (4 bytes at `sp`), `key`
(192 bytes) and `u` (32 bytes), and read and write `t` (32 bytes) and
`scratch` (384 bytes, whose contents on exit are unspecified). The written
regions may not overlap each other, the read ones or the argument; and
nothing may wrap around the end of the (32-bit) address space. `sp`, the
pointers and `n` are public; the key, `U` and `T` are secret. -/
def iterateSha256Arm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 192⟩
    let u : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let t : Region := ⟨State.addr (s.gpr .r3), 32⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 384⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, u, args] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    args.Disjoint t ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 32 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 384 ≤ 2 ^ 32 ∧
    s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' := ∀ k0, k0.length = 64 →
    Repr s.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad) →
    Repr s.mem (State.addr (s.gpr .r0) + 96) (xorPad k0 opad) →
    bytesAt s'.mem (State.addr (s.gpr .r3)) 32 =
      Spec.Pbkdf2.iterate (hmacBlockKey sha256 k0) (s.gpr .r2).toNat
        (bytesAt s.mem (State.addr (s.gpr .r1)) 32) (bytesAt s.mem (State.addr (s.gpr .r3)) 32)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Pbkdf2

namespace VG.Proof.Pbkdf2.Arm

open VG VG.Arm VG.Impl.Pbkdf2.Arm
open VG.Impl.Sha256.Arm.Stream (save restore compressAt saved)
open VG.Impl.Hmac.Arm (cp)
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd Mupd wp_add wp_ldr wp_str wp_rev op2_imm op2_reg sub_offset)
open VG.Proof.Sha256.Arm.Stream (compressAt_ok)
open VG.Proof.Sha256.Arm.Stream.Finalize (writeW_rev flat_length)
open VG.Proof.Hmac.Arm (copy_ok add_off)
open VG.Proof.Hmac.Arm.Init (wp_eor)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_sep bytesAt_add extractLsb'_read)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append writeBytes_nil write_eq_writeBytes)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base off_contains sep_after xorBytes_length
  add_ofNat stateAt_copy)
open VG.Spec.Sha256 (bytesAt stateAt blockAt compress HashValue wordBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev key : BitVec 32 := s₀.gpr .r0
abbrev uP : BitVec 32 := s₀.gpr .r1
/-- The number of steps. -/
abbrev nn : Nat := (s₀.gpr .r2).toNat
abbrev tP : BitVec 32 := s₀.gpr .r3
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev kA : Addr := State.addr (key s₀)
abbrev uA : Addr := State.addr (uP s₀)
abbrev tA : Addr := State.addr (tP s₀)
abbrev scA : Addr := State.addr (scr s₀)
abbrev keyR : Region := ⟨kA s₀, 192⟩
abbrev uR : Region := ⟨uA s₀, 32⟩
abbrev tR : Region := ⟨tA s₀, 32⟩
abbrev scR : Region := ⟨scA s₀, 384⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

/-- A part of the scratch space. -/
abbrev sR (o n : Nat) : Region := ⟨scA s₀ + BitVec.ofNat 64 o, n⟩
/-- `vg_sha256_compress`'s scratch space. -/
abbrev cmpR : Region := ⟨scA s₀, 112⟩
/-- `T`. -/
abbrev TA : Addr := scA s₀ + BitVec.ofNat 64 160
/-- The block. -/
abbrev blkA : Addr := scA s₀ + BitVec.ofNat 64 192

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, uR s₀, argR s₀]
  wr : s₀.wr = [tR s₀, scR s₀]
  k_t : (keyR s₀).Disjoint (tR s₀)
  k_s : (keyR s₀).Disjoint (scR s₀)
  u_t : (uR s₀).Disjoint (tR s₀)
  u_s : (uR s₀).Disjoint (scR s₀)
  t_s : (tR s₀).Disjoint (scR s₀)
  a_t : (argR s₀).Disjoint (tR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  key_fit : (key s₀).toNat + 192 ≤ 2 ^ 32
  u_fit : (uP s₀).toNat + 32 ≤ 2 ^ 32
  t_fit : (tP s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 384 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 4 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Pbkdf2.iterateSha256Arm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-! ## Regions -/

theorem toNat_ofNat_lt {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Two parts of the scratch space at offsets `a` and `b` do not overlap. -/
theorem scr_disj (s₀ : State) {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 384) (hb : b + n ≤ 384) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

theorem scr_disj0 (s₀ : State) {a m n : Nat} (h : n ≤ a) (ha : a + m ≤ 384) :
    Region.Disjoint (sR s₀ a m) ⟨scA s₀, n⟩ := by
  have := scr_disj s₀ (a := a) (m := m) (b := 0) (n := n) (by omega) ha (by omega)
  simp only [sR] at this
  simpa using this

theorem scr_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 384) : Region.Sub (sR s₀ o n) (scR s₀) :=
  sub_offset h (by omega)

theorem cmp_sub (s₀ : State) : Region.Sub (cmpR s₀) (scR s₀) := Region.sub_prefix (by omega)

theorem ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

section
variable {s₀ : State} (hp : Pre s₀) {s : State}
include hp

theorem in_scr (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 384) :
    InRegions s.wr (scA s₀ + BitVec.ofNat 64 a) n :=
  ⟨scR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩

theorem in_t (hwr : s.wr = s₀.wr) {b n : Nat} (h : b + n ≤ 32) :
    InRegions s.wr (tA s₀ + BitVec.ofNat 64 b) n :=
  ⟨tR s₀, by simp [hwr, hp.wr], contains_offset (by omega) (by omega)⟩

theorem in_key (hrd : s.rd = s₀.rd) {a n : Nat} (h : a + n ≤ 192) :
    InRegions (s.rd ++ s.wr) (kA s₀ + BitVec.ofNat 64 a) n :=
  ⟨keyR s₀, by simp [hrd, hp.rd], contains_offset h (by omega)⟩

end

theorem InRegions.right {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem key_disj {s₀ : State} (hp : Pre s₀) : ∀ r ∈ [tR s₀, scR s₀], Region.Disjoint (keyR s₀) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.k_t
  · exact hp.k_s

/-- The scratch pointer plus an offset, as an address. -/
theorem scr_add {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 384) :
    State.addr (scr s₀ + BitVec.ofNat 32 k) = scA s₀ + BitVec.ofNat 64 k := by
  have := hp.scr_fit
  exact addr_add (by omega)

/-! ## The registers and memory during a step -/

/-- The registers the body keeps. -/
def kept : List Reg := [.r0, .r3, .r4, .r5]

/-- From `s` to `s'`, only `t` (the hash value being compressed) and the
compression's part of the scratch space changed. -/
structure Keep (s₀ s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  gpr : ∀ r ∈ kept, s'.gpr r = s.gpr r
  frame : Frame [tR s₀, cmpR s₀] s.mem s'.mem

theorem Keep.trans {s₀ s₁ s₂ s₃ : State} (h₁ : Keep s₀ s₁ s₂) (h₂ : Keep s₀ s₂ s₃) : Keep s₀ s₁ s₃ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr),
    h₁.frame.trans h₂.frame⟩

/-- The registers and memory at the start of each step. -/
structure Regs (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = tP s₀
  r3 : s.gpr .r3 = scr s₀
  r4 : s.gpr .r4 = key s₀
  frame : Frame [tR s₀, scR s₀] s₀.mem s.mem

theorem Regs.keep {s₀ s s' : State} (h : Regs s₀ s) (hk : Keep s₀ s s') : Regs s₀ s' where
  rd := hk.rd.trans h.rd
  wr := hk.wr.trans h.wr
  sp := hk.sp.trans h.sp
  r0 := (hk.gpr _ (by simp [kept])).trans h.r0
  r3 := (hk.gpr _ (by simp [kept])).trans h.r3
  r4 := (hk.gpr _ (by simp [kept])).trans h.r4
  frame := h.frame.trans (hk.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨tR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, cmp_sub s₀⟩)

theorem Regs.write {s₀ s s' : State} (h : Regs s₀ s) (hg : ∀ r ∈ [Reg.r0, .r3, .r4], s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) {R : Region} (hR : R ∈ [tR s₀, scR s₀])
    (hm : Frame [R] s.mem s'.mem) : Regs s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r0 := (hg _ (by simp)).trans h.r0
  r3 := (hg _ (by simp)).trans h.r3
  r4 := (hg _ (by simp)).trans h.r4
  frame := h.frame.trans (hm.mono (by simpa using hR))

/-- The key's bytes are as on entry. -/
theorem Regs.key_bytes {s₀ s : State} (hp : Pre s₀) (h : Regs s₀ s) {i : Nat} (hi : i < 192) :
    s.mem (kA s₀ + BitVec.ofNat 64 i) = s₀.mem (kA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := keyR s₀) (key_disj hp) (by simp) hi

/-! ## Loading a hash value of the key into `t` -/

/-- Loading the hash value at `key + o` into `t`. -/
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) {o : Nat} (ho : o + 32 ≤ 192)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' → stateAt s'.mem (tA s₀) = stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (load o ++ rest)) s Q := by
  have := hp.key_fit; have := hp.t_fit
  unfold load
  refine copy_ok (t := .r12) (src := .r4) (dst := .r0) (by decide) (by decide) o 0 8 ⟨by omega, by omega⟩
    rest s Q (by rw [h.r4]; omega) (by rw [h.r0]; omega)
    (fun j hj => by rw [h.r4, add_ofNat]; exact in_key hp h.rd (by omega))
    (fun j hj => by rw [h.r0, add_ofNat]; exact in_t hp h.wr (by omega))
    ?_ fun s' g' rd' wr' sp' m' => k s' ⟨rd', wr', sp', fun r hr => g' r (by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide), ?_⟩ ?_
  · rw [h.r4, h.r0]
    exact Region.Disjoint.sep hp.k_t (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  · rw [m', h.r0]
    refine writeBytes_frame _ _ _ (R := tR s₀) ?_ |>.mono (by simp)
    rw [bytesAt_length, ofNat_zero]; exact contains_base (Nat.le_refl _)
  · rw [m', h.r0, h.r4, ofNat_zero, show 4 * 8 = 32 from rfl, stateAt_copy]
    apply Proof.Sha256.Stream.stateAt_congr
    intro i hi
    rw [add_ofNat]
    exact h.key_bytes hp (by omega)

/-! ## A call of `vg_sha256_compress` on the block -/

/-- `r1` at the block. -/
theorem atBlock_ok {s₀ : State} {s : State} (h : Regs s₀ s) {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' → s'.mem = s.mem → s'.gpr .r1 = scr s₀ + BitVec.ofNat 32 192 → Q s') :
    WP isa (.block [atBlock]) s Q := by
  refine wp_add (op2_imm (by decide)) fun s' u => WP.block_nil (k s' ⟨u.rd, u.wr, u.sp, fun r hr => u.other r ?_,
    by rw [u.mem]; exact Frame.refl _ _⟩ u.mem (by rw [u.gpr, h.r3]; rfl))
  simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

/-- Compressing the block into the hash value in `t`. -/
theorem cmp_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) (h1 : s.gpr .r1 = scr s₀ + BitVec.ofNat 32 192)
    {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' →
      stateAt s'.mem (tA s₀) = compress (stateAt s.mem (tA s₀)) (blockAt s.mem (blkA s₀)) → Q s') :
    WP isa compressAt s Q := by
  have := hp.scr_fit; have := hp.t_fit
  have ea : State.addr (scr s₀ + BitVec.ofNat 32 192) = blkA s₀ := scr_add hp (by omega)
  have et : (scr s₀ + BitVec.ofNat 32 192).toNat = (scr s₀).toNat + 192 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsc : scR s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  have htr : tR s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  refine compressAt_ok (st := tP s₀) (scr := scr s₀) (src := scr s₀ + BitVec.ofNat 32 192) h.r0 h.r3 h1
    (by omega) (by rw [et]; omega) (by omega) (hp.t_s.sub_right (cmp_sub s₀))
    (by rw [ea]; exact (hp.t_s.sub_right (scr_sub s₀ (o := 192) (n := 64) (by omega))).symm)
    (by rw [ea]; exact scr_disj0 s₀ (a := 192) (by omega) (by omega)) ?_ ?_
    fun s' hrd hwr hcs hr0 hr3 hsp hf hst => k s' ⟨hrd, hwr, hsp, fun r hr => ?_, hf⟩ (by rw [hst, ea])
  · rw [ea]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s₀, List.mem_append_right _ hsc, 192, rfl, by simp⟩
    · exact ⟨tR s₀, List.mem_append_right _ htr, 0, by simp, by simp⟩
    · exact ⟨scR s₀, List.mem_append_right _ hsc, 0, by simp, by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨tR s₀, htr, 0, by simp, by simp⟩
    · exact ⟨scR s₀, hsc, 0, by simp, by simp⟩
  · simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [hr0, h.r0]
    · rw [hr3, h.r3]
    · exact hcs _ (by simp [preserved]) (by decide)
    · exact hcs _ (by simp [preserved]) (by decide)

/-! ## The digest into the block -/

/-- The first `n` words of the digest of the hash value at `r0` (`p0`) into
the block at `r3 + 192` (`p3 + 192`). -/
theorem out_ok {p0 p3 : BitVec 32} (f0 : p0.toNat + 32 ≤ 2 ^ 32) (f3 : p3.toNat + 224 ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨State.addr p0, 32⟩ ⟨State.addr p3 + BitVec.ofNat 64 192, 32⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r0 = p0 → s.gpr .r3 = p3 →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (State.addr p0 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 8, InRegions s.wr (State.addr p3 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr p3 + BitVec.ofNat 64 192)
        (((stateAt s.mem (State.addr p0)).toList.take n).flatMap wordBytes) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap outW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q h0 h3 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q h0 h3 hin hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    have hP := flat_length (stateAt s.mem (State.addr p0)) n (by omega)
    simp only [outW, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr p0 + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [g₁ _ (by decide), h0, addr_add (by omega)])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_rev fun s₃ u₃ => wp_str (a := State.addr p3 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n))
      (by omega) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), h3,
        addr_add (by omega), add_off])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₄ g₄ => k s₄ (fun r hr => by rw [g₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [g₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hread : s₁.mem.readW (State.addr p0 + BitVec.ofNat 64 (4 * n)) 32 =
        (stateAt s.mem (State.addr p0))[n] := by
      rw [m₁, (writeBytes_frame s.mem (State.addr p3 + BitVec.ofNat 64 192) _
        (R := ⟨State.addr p3 + BitVec.ofNat 64 192, 32⟩) (contains_base (by rw [hP]; omega))).readW
        (r := ⟨State.addr p0 + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (sub_offset (by omega) (by omega))
    rw [g₄.mem, u₃.mem, u₂.mem, u₃.gpr, u₂.gpr, hread, m₁, writeW_rev,
      show State.addr p3 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n) = State.addr p3 + BitVec.ofNat 64 192 +
        BitVec.ofNat 64 (((stateAt s.mem (State.addr p0)).toList.take n).flatMap wordBytes).length by rw [hP]]
    rw [writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem digest_eq (H : HashValue) : (H.toList.take 8).flatMap wordBytes = Pbkdf2.digest H := by
  rw [List.take_of_length_le (by simp)]; rfl

/-- The digest of the hash value in `t` into the block. -/
theorem digest_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Regs s₀ s' → (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → Frame [sR s₀ 192 32] s.mem s'.mem →
      s'.mem = writeBytes s.mem (blkA s₀) (Pbkdf2.digest (stateAt s.mem (tA s₀))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.Arm.digest ++ rest)) s Q := by
  have := hp.scr_fit; have := hp.t_fit
  unfold Impl.Pbkdf2.Arm.digest
  refine out_ok (p0 := tP s₀) (p3 := scr s₀) (by omega) (by omega)
    (hp.t_s.sub_right (scr_sub s₀ (o := 192) (n := 32) (by omega))) 8 (Nat.le_refl _) rest s Q h.r0 h.r3
    (fun j hj => InRegions.right (in_t hp h.wr (by omega)))
    (fun j hj => by rw [add_ofNat]; exact in_scr hp h.wr (a := 192 + 4 * j) (by omega))
    fun s' g' rd' wr' sp' m' => ?_
  rw [digest_eq] at m'
  have hf : Frame [sR s₀ 192 32] s.mem s'.mem := by
    rw [m']; exact writeBytes_frame _ _ _ (contains_base (by rw [Pbkdf2.digest_length]))
  exact k s' (h.write (fun r hr => g' r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) rd' wr' sp' (R := scR s₀) (by simp) (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)) g' hf m'

/-! ## `T ← T ⊕ U` -/

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' a 4) (bytesAt m' b 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, extractLsb'_read _ _ h₁, extractLsb'_read _ _ h₁]

/-- `T ← T ⊕ U` for the first `n` words of `T` at `p3 + 160` and `U` at `p3 + 192`. -/
theorem xor_ok {p3 : BitVec 32} (f3 : p3.toNat + 224 ≤ 2 ^ 32) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r3 = p3 →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (State.addr p3 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 8, InRegions s.wr (State.addr p3 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .r12 → r ≠ .r1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr p3 + BitVec.ofNat 64 160)
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr p3 + BitVec.ofNat 64 160) (4 * n))
          (bytesAt s.mem (State.addr p3 + BitVec.ofNat 64 192) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q h3 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q h3 hin hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    have hw := hout n (by omega)
    have e3 : s₁.gpr .r3 = p3 := by rw [g₁ _ (by decide) (by decide), h3]
    refine wp_ldr (a := State.addr p3 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [e3, addr_add (by omega), add_off]) (by rw [rd₁, wr₁]; exact InRegions.right hw)
      fun s₂ u₂ => ?_
    refine wp_ldr (a := State.addr p3 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₂.other _ (by decide), e3, addr_add (by omega), add_off])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hin n (by omega)) fun s₃ u₃ => ?_
    refine wp_eor (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_str (a := State.addr p3 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), e3,
        addr_add (by omega), add_off])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₅ g₅ => k s₅ (fun r h12 h1 => by
          rw [g₅.gpr, u₄.other r h12, u₃.other r h1, u₂.other r h12, g₁ r h12 h1])
        (by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr p3 + BitVec.ofNat 64 160) (4 * n))
        (bytesAt s.mem (State.addr p3 + BitVec.ofNat 64 192) (4 * n))).length = 4 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have v : s₄.gpr .r12 = s₁.mem.readW (State.addr p3 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n)) 32 ^^^
        s₁.mem.readW (State.addr p3 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n)) 32 := by
      rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₂.mem]
    rw [g₅.mem, u₄.mem, u₃.mem, u₂.mem, v, writeW_xor32, m₁,
      bytesAt_writeBytes_sep (p := State.addr p3 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := State.addr p3 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n))]
    · have e := writeBytes_append s.mem (State.addr p3 + BitVec.ofNat 64 160) _
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr p3 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n)) 4)
          (bytesAt s.mem (State.addr p3 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro x h₁ h₂
      rw [hl] at h₂
      have := toNat_ofNat_lt (k := 4 * n) (by omega)
      have := VG.Proof.MdStream.Arm.addr_toNat p3
      bv_omega
    · omega
    · intro x h₁ h₂
      rw [hl] at h₂
      exact sep_after h₁ h₂ (by omega)
    · omega

end VG.Proof.Pbkdf2.Arm

/-!
# PBKDF2-HMAC-SHA-256's iteration on ARMv7: the loop

One step is HMAC-SHA-256 of `U` as two compressions
(`VG.Proof.Pbkdf2.hmac_step`), then `T ← T ⊕ U`.
-/

namespace VG.Proof.Pbkdf2.Arm

open VG VG.Arm VG.Impl.Pbkdf2.Arm
open VG.Impl.Sha256.Arm.Stream (saved)
open VG.Proof.MdStream.Arm (wp_subs op2_imm eval_eq eval_ne ofNat_beq_zero sub_ofNat)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base blockAt_eq xorBytes_length add_ofNat
  digest_self)
open VG.Spec.Sha256 (bytesAt stateAt blockAt compress HashValue)

section
variable (s₀ : State)

/-- The key's inner and outer hash values. -/
abbrev Hi : HashValue := stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 0)
abbrev Ho : HashValue := stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 96)

/-- A step, as the code computes it. -/
def stepM (u : List Byte) : List Byte :=
  Pbkdf2.digest (compress (Ho s₀) (block96 (Pbkdf2.digest (compress (Hi s₀) (block96 u)))))

/-- Our caller's registers and our return address, saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

/-- What the body writes: `t`, the compression's part of the scratch space,
`T` and the block's first 32 bytes. -/
abbrev bodyR : List Region := [tR s₀, cmpR s₀, sR s₀ 160 32, sR s₀ 192 32]

end

/-- Parts of the scratch space that the body leaves: the saved registers
(`[112..160)`) and the padding (from 224). -/
theorem body_disj {s₀ : State} (hp : Pre s₀) {o n : Nat} (h₁ : (112 ≤ o ∧ o + n ≤ 160) ∨ 224 ≤ o)
    (h₂ : o + n ≤ 384) : ∀ r ∈ bodyR s₀, Region.Disjoint (sR s₀ o n) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.t_s.sub_right (scr_sub s₀ h₂)).symm
  · exact scr_disj0 s₀ (by omega) h₂
  · exact scr_disj s₀ (b := 160) (n := 32) (by omega) h₂ (by omega)
  · exact scr_disj s₀ (b := 192) (n := 32) (by omega) h₂ (by omega)

/-- The block's first 32 bytes are neither `t` nor the compression's scratch. -/
theorem blk_disj {s₀ : State} (hp : Pre s₀) : ∀ r ∈ [tR s₀, cmpR s₀], Region.Disjoint (sR s₀ 192 32) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.t_s.sub_right (scr_sub s₀ (by omega))).symm
  · exact scr_disj0 s₀ (by omega) (by omega)

/-- `T` is none of the other parts the body writes. -/
theorem T_disj {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [tR s₀, cmpR s₀, sR s₀ 192 32], Region.Disjoint (sR s₀ 160 32) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.t_s.sub_right (scr_sub s₀ (by omega))).symm
  · exact scr_disj0 s₀ (by omega) (by omega)
  · exact scr_disj s₀ (by omega) (by omega) (by omega)

theorem Saved.frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m) (hf : Frame (bodyR s₀) m m') :
    Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 160 := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact hf.readW (r := sR s₀ p.2 4) (Region.contains_self _ _) (body_disj hp (.inl hd) (by omega)) (by decide)

theorem frame_body {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, r ∈ bodyR s₀) :
    Frame (bodyR s₀) m m' := hf.mono hs

/-- The loop invariant, with `r` steps left. -/
structure Inv (s₀ : State) (r : Nat) (s : State) : Prop extends Regs s₀ s where
  r5 : s.gpr .r5 = BitVec.ofNat 32 r
  saved : Saved s₀ s.mem
  pad : bytesAt s.mem (scA s₀ + BitVec.ofNat 64 224) 32 = pad96
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM s₀) (nn s₀) (bytesAt s₀.mem (uA s₀) 32) (bytesAt s₀.mem (tA s₀) 32) =
    Spec.Pbkdf2.iterate (stepM s₀) r (bytesAt s.mem (blkA s₀) 32) (bytesAt s.mem (TA s₀) 32)

theorem body_ok {s₀ : State} (hp : Pre s₀) {r : Nat} {s : State} (h : Inv s₀ (r + 1) s) :
    WP isa body s fun s' => VG.Arm.eval .ne s' = some (r != 0) ∧ Inv s₀ r s' := by
  have := hp.scr_fit
  unfold body
  have hU : ∀ {m : Mem}, Frame [tR s₀, cmpR s₀] s.mem m → bytesAt m (blkA s₀) 32 = bytesAt s.mem (blkA s₀) 32 :=
    fun hf => frame_bytesAt hf (blk_disj hp) (by omega)
  have hpad : ∀ {m : Mem}, Frame (bodyR s₀) s.mem m → bytesAt m (blkA s₀ + 32) 32 = pad96 := by
    intro m hf
    rw [show blkA s₀ + 32 = scA s₀ + BitVec.ofNat 64 224 by bv_omega, ← h.pad]
    exact frame_bytesAt hf (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  -- The inner hash.
  refine WP.seq ?_
  refine load_ok hp h.toRegs (o := 0) (by omega) fun s₁ k₁ e₁ => ?_
  refine atBlock_ok (h.toRegs.keep k₁) fun s₂ k₂ m₂ x1₂ => ?_
  have h₂ := (h.toRegs.keep k₁).keep k₂
  refine WP.seq (cmp_ok hp h₂ x1₂ fun s₃ k₃ e₃ => ?_)
  rw [m₂, e₁, blockAt_eq (hpad (frame_body k₁.frame (by simp))), hU k₁.frame] at e₃
  -- The outer hash.
  have h₃ := h₂.keep k₃
  refine WP.seq ?_
  refine digest_ok hp h₃ fun s₄ h₄ g₄ f₄ m₄ => ?_
  refine load_ok hp h₄ (o := 96) (by omega) fun s₅ k₅ e₅ => ?_
  refine atBlock_ok (h₄.keep k₅) fun s₆ k₆ m₆ x1₆ => ?_
  have h₆ := (h₄.keep k₅).keep k₆
  have f₃₄ : Frame (bodyR s₀) s.mem s₄.mem :=
    (frame_body ((k₁.trans k₂).trans k₃).frame (by simp)).trans (frame_body f₄ (by simp))
  refine WP.seq (cmp_ok hp h₆ x1₆ fun s₇ k₇ e₇ => ?_)
  have hX : bytesAt s₅.mem (blkA s₀) 32 = Pbkdf2.digest (stateAt s₃.mem (tA s₀)) := by
    rw [frame_bytesAt (p := blkA s₀) (n := 32) k₅.frame (blk_disj hp) (by omega), m₄, digest_self]
  rw [m₆, e₅, blockAt_eq (hpad (f₃₄.trans (frame_body k₅.frame (by simp)))), hX, e₃] at e₇
  -- The digest, `T ← T ⊕ U` and the count.
  have h₇ := h₆.keep k₇
  refine digest_ok hp h₇ fun s₈ h₈ g₈ f₈ m₈ => ?_
  refine xor_ok (p3 := scr s₀) (by omega) 8 (Nat.le_refl _) _ s₈ _ h₈.r3
    (fun j hj => InRegions.right (by rw [add_ofNat]; exact in_scr hp h₈.wr (a := 192 + 4 * j) (n := 4) (by omega)))
    (fun j hj => by rw [add_ofNat]; exact in_scr hp h₈.wr (a := 160 + 4 * j) (n := 4) (by omega))
    fun s₉ g₉ rd₉ wr₉ sp₉ m₉ => ?_
  rw [show 4 * 8 = 32 from rfl] at m₉
  have f₉ : Frame [sR s₀ 160 32] s₈.mem s₉.mem := by
    rw [m₉]
    exact writeBytes_frame _ _ _ (contains_base (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]))
  have h₉ := h₈.write (fun r hr => g₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) rd₉ wr₉ sp₉ (R := scR s₀) (by simp)
    (f₉.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)
  refine wp_subs (op2_imm (by decide)) fun s₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  have h₁₀ := h₉.write (fun r hr => u₁₀.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) u₁₀.rd u₁₀.wr u₁₀.sp (R := tR s₀) (by simp)
    (by rw [u₁₀.mem]; exact Frame.refl _ _)
  have x5 : s₉.gpr .r5 = BitVec.ofNat 32 (r + 1) := by
    rw [g₉ _ (by decide) (by decide), g₈ _ (by decide), k₇.gpr _ (by simp [kept]), k₆.gpr _ (by simp [kept]),
      k₅.gpr _ (by simp [kept]), g₄ _ (by decide), k₃.gpr _ (by simp [kept]), k₂.gpr _ (by simp [kept]),
      k₁.gpr _ (by simp [kept]), h.r5]
  have hlt : r + 1 < 2 ^ 32 := by have := h.le; have := (s₀.gpr .r2).isLt; simp only [nn] at *; omega
  have e₁₀ : s₉.gpr .r5 - 1 = BitVec.ofNat 32 r := by
    rw [x5, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.add_sub_cancel]
  have fb : Frame (bodyR s₀) s.mem s₁₀.mem := by
    rw [u₁₀.mem]
    exact f₃₄.trans (frame_body ((k₅.trans k₆).trans k₇).frame (by simp)) |>.trans (frame_body f₈ (by simp))
      |>.trans (frame_body f₉ (by simp))
  have f₈' : Frame [tR s₀, cmpR s₀, sR s₀ 192 32] s.mem s₈.mem :=
    (((k₁.trans k₂).trans k₃).frame.mono (by simp)) |>.trans (f₄.mono (by simp))
      |>.trans ((((k₅.trans k₆).trans k₇).frame).mono (by simp)) |>.trans (f₈.mono (by simp))
  have hT : bytesAt s₈.mem (TA s₀) 32 = bytesAt s.mem (TA s₀) 32 :=
    frame_bytesAt f₈' (T_disj hp) (by omega)
  have hU₈ : bytesAt s₈.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [m₈, digest_self, e₇]; rfl
  have hsep : Mem.Sep (blkA s₀) 32 (TA s₀)
      (Spec.Pbkdf2.xorBytes (bytesAt s₈.mem (TA s₀) 32) (bytesAt s₈.mem (blkA s₀) 32)).length := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    exact Region.Disjoint.sep (scr_disj s₀ (a := 192) (m := 32) (b := 160) (n := 32) (by omega) (by omega)
      (by omega)) (contains_base (Nat.le_refl _)) (contains_base (Nat.le_refl _))
  have hU₁₀ : bytesAt s₁₀.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [u₁₀.mem, m₉, bytesAt_writeBytes_sep _ _ hsep (by omega), hU₈]
  have hT₁₀ : bytesAt s₁₀.mem (TA s₀) 32 =
      Spec.Pbkdf2.xorBytes (bytesAt s.mem (TA s₀) 32) (stepM s₀ (bytesAt s.mem (blkA s₀) 32)) := by
    have := bytesAt_writeBytes_self s₈.mem (TA s₀)
      (Spec.Pbkdf2.xorBytes (bytesAt s₈.mem (TA s₀) 32) (bytesAt s₈.mem (blkA s₀) 32))
      (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length] at this
    rw [u₁₀.mem, m₉, this, hT, hU₈]
  have hle : r ≤ nn s₀ := by have := h.le; omega
  refine ⟨?_, { h₁₀ with r5 := ?_, saved := h.saved.frame hp fb, pad := ?_, le := hle, val := ?_ }⟩
  · rw [eval_ne, z₁₀, e₁₀, ofNat_beq_zero (by omega)]
    cases r <;> rfl
  · rw [u₁₀.gpr, e₁₀]
  · rw [← h.pad]
    exact frame_bytesAt fb (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  · rw [h.val, hU₁₀, hT₁₀]; rfl

theorem loop_ok {s₀ : State} (hp : Pre s₀) {n : Nat} {s : State} (h : Inv s₀ n s) (hz : s.z = decide (n = 0)) :
    WP isa (.ite .eq (.block []) (.loop body .ne)) s (Inv s₀ 0) := by
  refine WP.ite (decide (n = 0)) (by show VG.Arm.eval .eq s = _; rw [eval_eq, hz]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => Inv s₀ (m + 1) s) (fun m s hs => WP.mono (body_ok hp hs) fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end VG.Proof.Pbkdf2.Arm

/-!
# PBKDF2-HMAC-SHA-256's iteration on ARMv7

The prologue, the epilogue, and `Verified`. Constant time is proven by the
taint analysis: `t` (in `r0` around the calls) and the scratch space (in `r3`)
are the bases of the two writable regions, so the registers
`vg_sha256_compress` saves in its scratch space and restores are known to keep
their public values.
-/

namespace VG.Proof.Pbkdf2.Arm

open VG VG.Arm VG.Impl.Pbkdf2.Arm
open VG.Impl.Sha256.Arm.Stream (saved restore save)
open VG.Impl.Hmac.Arm (cp)
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_str wp_ldrSp wp_cmp op2_imm op2_reg saveMem)
open VG.Proof.Sha256.Arm.Stream (save_ok restore_ok saveMem_saved saveMem_frame saved_bound)
open VG.Proof.MdStream.Arm (addr_toNat)
open VG.Proof.Hmac.Arm (copy_ok)
open VG.Proof.Hmac.Arm.Init (beq_zero_toNat)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_nil)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base writeW_bytes writeBytes_append' iterate_congr
  add_ofNat)
open VG.Spec.Sha256 (bytesAt stateAt Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)

/-! ## The padding -/

/-- A word stored right after bytes written before. -/
theorem writeW_append (m : Mem) (q : Addr) (xs ys : List Byte) (v : BitVec 32) {a : Addr}
    (ha : a = q + BitVec.ofNat 64 xs.length)
    (hv : ((List.range (32 / 8)).map fun j => (v.setWidth (8 * (32 / 8))).extractLsb' (8 * j) 8) = ys)
    (hl : xs.length + ys.length < 2 ^ 64) :
    (writeBytes m q xs).writeW a v = writeBytes m q (xs ++ ys) := by
  rw [writeW_bytes _ _ v ys hv, writeBytes_append' _ _ _ ha hl]

/-- A store of `r12` at `[r3, #d]`, within the scratch space. -/
theorem str_ok {s₀ : State} (hp : Pre s₀) {s : State} (h3 : s.gpr .r3 = scr s₀) (hwr : s.wr = s₀.wr)
    {d : Nat} (hd : d + 4 ≤ 384) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (scA s₀ + BitVec.ofNat 64 d) (s.gpr .r12)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.str .r12 .r3 d :: rest)) s Q :=
  wp_str (by omega) (by rw [h3]; exact scr_add hp (by omega)) (in_scr hp hwr hd) k

/-- The padding into `scratch[224..256)`. -/
theorem padding_ok {s₀ : State} (hp : Pre s₀) {s : State} (h3 : s.gpr .r3 = scr s₀) (hwr : s.wr = s₀.wr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (scA s₀ + BitVec.ofNat 64 224) pad96 → WP isa (.block rest) s' Q) :
    WP isa (.block (padding ++ rest)) s Q := by
  simp only [padding, List.cons_append, List.nil_append]
  let P := scA s₀ + BitVec.ofNat 64 224
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have c₁ : s₁.gpr .r3 = scr s₀ := by rw [u₁.other _ (by decide), h3]
  refine str_ok hp c₁ (u₁.wr.trans hwr) (d := 224) (by omega) fun s₂ g₂ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  have c₃ : s₃.gpr .r3 = scr s₀ := by rw [u₃.other _ (by decide), g₂.gpr, c₁]
  have w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, g₂.wr, u₁.wr, hwr]
  have z₃ : s₃.gpr .r12 = 0 := u₃.gpr
  refine str_ok hp c₃ w₃ (d := 228) (by omega) fun s₄ g₄ => ?_
  refine str_ok hp (by rw [g₄.gpr, c₃]) (by rw [g₄.wr, w₃]) (d := 232) (by omega) fun s₅ g₅ => ?_
  refine str_ok hp (by rw [g₅.gpr, g₄.gpr, c₃]) (by rw [g₅.wr, g₄.wr, w₃]) (d := 236) (by omega) fun s₆ g₆ => ?_
  refine str_ok hp (by rw [g₆.gpr, g₅.gpr, g₄.gpr, c₃]) (by rw [g₆.wr, g₅.wr, g₄.wr, w₃]) (d := 240) (by omega)
    fun s₇ g₇ => ?_
  refine str_ok hp (by rw [g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, c₃]) (by rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, w₃])
    (d := 244) (by omega) fun s₈ g₈ => ?_
  refine str_ok hp (by rw [g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, c₃])
    (by rw [g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, w₃]) (d := 248) (by omega) fun s₉ g₉ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ => ?_
  refine str_ok hp (by rw [u₁₀.other _ (by decide), g₉.gpr, g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, c₃])
    (by rw [u₁₀.wr, g₉.wr, g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, w₃]) (d := 252) (by omega) fun s₁₁ g₁₁ => ?_
  have G : ∀ r, r ≠ .r12 → s₁₁.gpr r = s.gpr r := fun r hr => by
    rw [g₁₁.gpr, u₁₀.other r hr, g₉.gpr, g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, u₃.other r hr, g₂.gpr,
      u₁.other r hr]
  refine k s₁₁ G (by rw [g₁₁.rd, u₁₀.rd, g₉.rd, g₈.rd, g₇.rd, g₆.rd, g₅.rd, g₄.rd, u₃.rd, g₂.rd, u₁.rd])
    (by rw [g₁₁.wr, u₁₀.wr, g₉.wr, g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, u₃.wr, g₂.wr, u₁.wr])
    (by rw [g₁₁.sp, u₁₀.sp, g₉.sp, g₈.sp, g₇.sp, g₆.sp, g₅.sp, g₄.sp, u₃.sp, g₂.sp, u₁.sp]) ?_
  have e : ∀ o : Nat, scA s₀ + BitVec.ofNat 64 (224 + o) = P + BitVec.ofNat 64 o := fun o => (add_ofNat _ _ _).symm
  have e₂ : s₂.mem = writeBytes s.mem P ([] ++ [0x80, 0, 0, 0]) := by
    rw [g₂.mem, u₁.gpr, u₁.mem, ← writeBytes_nil s.mem P]
    exact writeW_append _ _ _ _ _ (by simp [P]) (by decide) (by decide)
  have e₄ : s₄.mem = writeBytes s.mem P ([0x80, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₄.mem, z₃, u₃.mem, e₂]; exact writeW_append _ _ _ _ _ (e 4) (by decide) (by decide)
  have e₅ : s₅.mem = writeBytes s.mem P ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₅.mem, g₄.gpr, z₃, e₄]; exact writeW_append _ _ _ _ _ (e 8) (by decide) (by decide)
  have e₆ : s₆.mem = writeBytes s.mem P ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₆.mem, g₅.gpr, g₄.gpr, z₃, e₅]; exact writeW_append _ _ _ _ _ (e 12) (by decide) (by decide)
  have e₇ : s₇.mem = writeBytes s.mem P ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₇.mem, g₆.gpr, g₅.gpr, g₄.gpr, z₃, e₆]; exact writeW_append _ _ _ _ _ (e 16) (by decide) (by decide)
  have e₈ : s₈.mem = writeBytes s.mem P
      ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₈.mem, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, z₃, e₇]
    exact writeW_append _ _ _ _ _ (e 20) (by decide) (by decide)
  have e₉ : s₉.mem = writeBytes s.mem P
      ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₉.mem, g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, z₃, e₈]
    exact writeW_append _ _ _ _ _ (e 24) (by decide) (by decide)
  rw [g₁₁.mem, u₁₀.gpr, u₁₀.mem, e₉]
  exact writeW_append _ _ _ _ _ (e 28) (by decide) (by decide)

/-! ## The prologue -/

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ (fun s => Inv s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0)) := by
  have := hp.scr_fit; have := hp.t_fit; have := hp.u_fit
  unfold prologue
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl ⟨argR s₀, by simp [hp.rd], Region.contains_self _ _⟩
    fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok (b := .r12) (by rw [h12]; omega) (fun d _ hd₂ => by
    rw [h12, u₁.wr]; exact in_scr hp rfl (by omega)) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  have G : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂, u₁.other r h]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  have M₆ : s₆.mem = saveMem s₀.mem (scA s₀) s₁.gpr saved := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, h12, u₁.mem]
  have r0₆ : s₆.gpr .r0 = tP s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), G _ (by decide)]
  have r1₆ : s₆.gpr .r1 = uP s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      G _ (by decide)]
  have r3₆ : s₆.gpr .r3 = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, h12]
  have r4₆ : s₆.gpr .r4 = key s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, G _ (by decide)]
  have r5₆ : s₆.gpr .r5 = s₀.gpr .r2 := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), G _ (by decide)]
  have F₆ : Frame [⟨scA s₀, 160⟩] s₀.mem s₆.mem := by
    rw [M₆]; exact saveMem_frame _ _ _ saved fun p hp' => (saved_bound p hp').1
  have sc160 : ∀ r ∈ [(⟨scA s₀, 160⟩ : Region)], r ∈ [tR s₀, scR s₀] ∨ Region.Sub r (scR s₀) :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (Region.sub_prefix (by omega))
  -- `U` into the block.
  refine copy_ok (t := .r12) (src := .r1) (dst := .r3) (by decide) (by decide) 0 192 8 ⟨by omega, by omega⟩ _ s₆ _
    (by rw [r1₆]; omega) (by rw [r3₆]; omega)
    (fun j hj => by
      rw [r1₆, rd₆, wr₆, add_ofNat]
      exact ⟨uR s₀, by simp [hp.rd], contains_offset (by omega) (by omega)⟩)
    (fun j hj => by rw [r3₆, wr₆, add_ofNat]; exact in_scr hp rfl (by omega)) ?_
    fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  · rw [r1₆, r3₆]
    exact Region.Disjoint.sep hp.u_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  -- `T` into the scratch space.
  refine copy_ok (t := .r12) (src := .r0) (dst := .r3) (by decide) (by decide) 0 160 8 ⟨by omega, by omega⟩ _ s₇ _
    (by rw [g₇ _ (by decide), r0₆]; omega) (by rw [g₇ _ (by decide), r3₆]; omega)
    (fun j hj => by
      rw [g₇ _ (by decide), r0₆, rd₇, wr₇, wr₆, add_ofNat]
      exact InRegions.right (in_t hp rfl (by omega)))
    (fun j hj => by rw [g₇ _ (by decide), r3₆, wr₇, wr₆, add_ofNat]; exact in_scr hp rfl (by omega)) ?_
    fun s₈ g₈ rd₈ wr₈ sp₈ m₈ => ?_
  · rw [g₇ _ (by decide), g₇ _ (by decide), r0₆, r3₆]
    exact Region.Disjoint.sep hp.t_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  refine padding_ok hp (by rw [g₈ _ (by decide), g₇ _ (by decide), r3₆]) (by rw [wr₈, wr₇, wr₆])
    fun s₉ g₉ rd₉ wr₉ sp₉ m₉ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₁₀ f₁₀ z₁₀ => WP.block_nil ?_
  have G₁₀ : ∀ r, r ≠ .r12 → s₁₀.gpr r = s₆.gpr r := fun r h => by rw [f₁₀.gpr, g₉ r h, g₈ r h, g₇ r h]
  simp only [g₇ _ (show Reg.r0 ≠ .r12 by decide), g₇ _ (show Reg.r3 ≠ .r12 by decide), r1₆, r0₆, r3₆,
    ofNat_zero] at m₇ m₈
  rw [show 4 * 8 = 32 from rfl] at m₇ m₈
  have hm : s₁₀.mem = writeBytes (writeBytes (writeBytes s₆.mem (blkA s₀) (bytesAt s₆.mem (uA s₀) 32))
      (TA s₀) (bytesAt s₇.mem (tA s₀) 32)) (scA s₀ + BitVec.ofNat 64 224) pad96 := by
    rw [f₁₀.mem, m₉, m₈, m₇]
  have fU : Frame [sR s₀ 192 32, sR s₀ 160 32, sR s₀ 224 32] s₆.mem s₁₀.mem := by
    rw [hm]
    exact (((writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))).mono (by simp)).trans
      ((writeBytes_frame _ _ _ (R := sR s₀ 160 32) (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))).mono
        (by simp))).trans
      ((writeBytes_frame _ _ _ (R := sR s₀ 224 32) (contains_base (by decide))).mono (by simp))
  have F' : Frame [scR s₀] s₀.mem s₁₀.mem :=
    (F₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩).trans
    (fU.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)
  have s160 : Region.Sub ⟨scA s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hU₆ : bytesAt s₆.mem (uA s₀) 32 = bytesAt s₀.mem (uA s₀) 32 :=
    frame_bytesAt F₆ (by simpa using hp.u_s.sub_right s160) (by omega)
  have hT₇ : bytesAt s₇.mem (tA s₀) 32 = bytesAt s₀.mem (tA s₀) 32 := by
    rw [m₇, bytesAt_writeBytes_sep _ _ (Region.Disjoint.sep (hp.t_s.sub_right (scr_sub s₀ (o := 192) (n := 32)
      (by omega))) (contains_base (Nat.le_refl _)) (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))) (by omega)]
    exact frame_bytesAt F₆ (by simpa using hp.t_s.sub_right s160) (by omega)
  have sep : ∀ {a b : Nat}, a + 32 ≤ b ∨ b + 32 ≤ a → a + 32 ≤ 384 → b + 32 ≤ 384 → ∀ xs : List Byte,
      xs.length = 32 → Mem.Sep (scA s₀ + BitVec.ofNat 64 a) 32 (scA s₀ + BitVec.ofNat 64 b) xs.length :=
    fun h ha hb xs hx => Region.Disjoint.sep (scr_disj s₀ h ha hb) (contains_base (Nat.le_refl _))
      (by rw [hx]; exact contains_base (Nat.le_refl _))
  have hB : bytesAt s₁₀.mem (blkA s₀) 32 = bytesAt s₀.mem (uA s₀) 32 := by
    rw [hm, bytesAt_writeBytes_sep _ _ (sep (a := 192) (b := 224) (by omega) (by omega) (by omega) _ rfl) (by omega),
      bytesAt_writeBytes_sep _ _ (sep (a := 192) (b := 160) (by omega) (by omega) (by omega) _ (bytesAt_length _ _ _))
        (by omega)]
    have := bytesAt_writeBytes_self s₆.mem (blkA s₀) (bytesAt s₆.mem (uA s₀) 32) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at this
    rw [this, hU₆]
  have hT : bytesAt s₁₀.mem (TA s₀) 32 = bytesAt s₀.mem (tA s₀) 32 := by
    rw [hm, bytesAt_writeBytes_sep _ _ (sep (a := 160) (b := 224) (by omega) (by omega) (by omega) _ rfl) (by omega)]
    have := bytesAt_writeBytes_self (writeBytes s₆.mem (blkA s₀) (bytesAt s₆.mem (uA s₀) 32)) (TA s₀)
      (bytesAt s₇.mem (tA s₀) 32) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at this
    rw [this, hT₇]
  have hS : ∀ p ∈ saved, s₁₀.mem.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have hb := saved_bound p hp'
    rw [fU.readW (r := sR s₀ p.2 4) (Region.contains_self _ _) ?_ (by decide), M₆,
      saveMem_saved _ _ _ p hp', u₁.other]
    · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact scr_disj s₀ (by omega) (by omega) (by omega)
  refine ⟨⟨⟨by rw [f₁₀.rd, rd₉, rd₈, rd₇, rd₆], by rw [f₁₀.wr, wr₉, wr₈, wr₇, wr₆],
    by rw [f₁₀.sp, sp₉, sp₈, sp₇, sp₆], by rw [G₁₀ _ (by decide), r0₆], by rw [G₁₀ _ (by decide), r3₆],
    by rw [G₁₀ _ (by decide), r4₆], F'.mono (by simp)⟩, by rw [G₁₀ _ (by decide), r5₆, ofNat_toNat32], hS, ?_,
    (Nat.le_refl _), by rw [hB, hT]⟩, ?_⟩
  · rw [hm]
    exact bytesAt_writeBytes_self _ (scA s₀ + BitVec.ofNat 64 224) pad96 (by decide)
  · rw [z₁₀, g₉ _ (by decide), g₈ _ (by decide), g₇ _ (by decide), r5₆, beq_zero_toNat]

/-! ## The epilogue -/

/-- The postcondition. -/
def Post (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ Proof.Pbkdf2.iterateSha256Arm.post s₀ s'

/-- With the key's streaming states as the contract requires, a step is HMAC-SHA-256. -/
theorem stepM_eq {s₀ : State} {k0 : List Byte} (hk : k0.length = 64)
    (hi : Repr s₀.mem (kA s₀) (xorPad k0 ipad)) (ho : Repr s₀.mem (kA s₀ + 96) (xorPad k0 opad))
    {u : List Byte} (hu : u.length = 32) :
    hmacBlockKey sha256 k0 u = stepM s₀ u := by
  have li : (xorPad k0 ipad).length = 64 := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = 64 := by simp [xorPad, hk]
  have ho1 : stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 96) = _ := ho.1
  rw [hmac_step hk hu, stepM, Hi, Ho, ofNat_zero, hi.1, ho1, li, lo]

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ 0 s) :
    WP isa (.block epilogue) s (Post s₀) := by
  have := hp.scr_fit; have := hp.t_fit
  unfold epilogue
  refine copy_ok (t := .r12) (src := .r3) (dst := .r0) (by decide) (by decide) 160 0 8 ⟨by omega, by omega⟩ _ s _
    (by rw [h.r3]; omega) (by rw [h.r0]; omega)
    (fun j hj => by rw [h.r3, add_ofNat]; exact InRegions.right (in_scr hp h.wr (by omega)))
    (fun j hj => by rw [h.r0, add_ofNat]; exact in_t hp h.wr (by omega)) ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · rw [h.r3, h.r0]
    exact Region.Disjoint.sep hp.t_s.symm (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  simp only [h.r3, h.r0, ofNat_zero] at m₁
  rw [show 4 * 8 = 32 from rfl] at m₁
  have fT : Frame [tR s₀] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))
  refine restore_ok (scr := scr s₀) (by rw [g₁ _ (by decide), h.r3]) (by omega)
    (fun d _ hd₂ => by rw [rd₁, wr₁]; exact InRegions.right (in_scr hp h.wr (by omega))) s₀.gpr
    (fun p hp' => ?_) fun s' hs _ hmem _ _ hsp => ⟨⟨fun r hr => ?_, by rw [hsp, sp₁, h.sp]⟩, fun k0 hk hi ho => ?_⟩
  · rw [← h.saved p hp']
    have hb := saved_bound p hp'
    exact fT.readW (r := sR s₀ p.2 4) (Region.contains_self _ _)
      (by simpa using (hp.t_s.sub_right (scr_sub s₀ (o := p.2) (n := 4) (by omega))).symm) (by decide)
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs (.r4, 112) (by simp [saved])
    · exact hs (.r5, 116) (by simp [saved])
    · exact hs (.r6, 120) (by simp [saved])
    · exact hs (.r7, 124) (by simp [saved])
    · exact hs (.r8, 128) (by simp [saved])
    · exact hs (.r9, 132) (by simp [saved])
    · exact hs (.r10, 136) (by simp [saved])
    · exact hs (.r11, 140) (by simp [saved])
    · exact hs (.lr, 144) (by simp [saved])
  · have := h.val
    simp only [Spec.Pbkdf2.iterate] at this
    have e : bytesAt s'.mem (tA s₀) 32 = bytesAt s.mem (TA s₀) 32 := by
      have := bytesAt_writeBytes_self s.mem (tA s₀) (bytesAt s.mem (TA s₀) 32) (by rw [bytesAt_length]; omega)
      rw [bytesAt_length] at this
      rw [hmem, m₁, this]
    show bytesAt s'.mem (tA s₀) 32 = _
    rw [e, ← this]
    exact (iterate_congr (fun u hu => stepM_eq hk hi ho hu) (fun u => Pbkdf2.digest_length _) _ _ _
      (bytesAt_length _ _ _)).symm

/-! ## Correctness -/

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa iterate s₀ (Post s₀) := by
  unfold iterate
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hp h₁ z₁) fun s₂ h₂ => epilogue_ok hp h₂)

/-! ## `Verified` -/

/-- The initial taint: `r0`–`r3` (`key`, `u`, `n`, `t`) are public, `r3`
points at `t`, and the 4 bytes of stack arguments are public, pointing at
the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [32, 384], bases := [(.r3, 0)],
    argLen := 4, argBases := [(0, 1)] }

theorem wf₀ {s : State} (h : Proof.Pbkdf2.iterateSha256Arm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have ht := hp.t_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.t_s, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_t
    · exact hp.a_s
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem argByte_eq (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Pbkdf2.iterateSha256Arm.pre s₁)
    (h₂ : Proof.Pbkdf2.iterateSha256Arm.pre s₂) (hpub : Proof.Pbkdf2.iterateSha256Arm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [tR, scR, tA, scA, tP, scr, p3, a0]
  · simp only [τ₀] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

/-- A state satisfying the precondition: `key` at `0x1000`, `u` at `0x2000`,
`t` at `0x3000` and the scratch space at `0x4000`, passed on the stack at
`0x5000`. -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x40 else 0
  rd := [⟨0x1000, 192⟩, ⟨0x2000, 32⟩, ⟨0x5000, 4⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 384⟩]

theorem iterate_correct (s : State) (hs : Proof.Pbkdf2.iterateSha256Arm.pre s) :
    ∃ t s', Exec isa iterate s t s' ∧ abiPreserved s s' ∧ Proof.Pbkdf2.iterateSha256Arm.post s s' :=
      by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, h⟩

theorem iterate_ct : ConstantTime isa Proof.Pbkdf2.iterateSha256Arm.pre
    Proof.Pbkdf2.iterateSha256Arm.pub iterate := by
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide)

/-- `iterateSha256Arm` with the 832 bytes of scratch of the shared contract
(sized for the x86-64 AVX2 compression function), of which the code uses 384. -/
def iterateWide : Contract isa :=
  { Proof.Pbkdf2.iterateSha256Arm with
    pre := fun s =>
      let key : Region := ⟨State.addr (s.gpr .r0), 192⟩
      let u : Region := ⟨State.addr (s.gpr .r1), 32⟩
      let t : Region := ⟨State.addr (s.gpr .r3), 32⟩
      let scratch : Region := ⟨State.addr (stackArg s 0), 832⟩
      let args : Region := ⟨stackArgAddr s 0, 4⟩
      s.rd = [key, u, args] ∧ s.wr = [t, scratch] ∧
      key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧
      t.Disjoint scratch ∧ args.Disjoint t ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 32 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 832 ≤ 2 ^ 32 ∧
      s.sp.toNat + 4 ≤ 2 ^ 32 }

/-- The regions `iterateSha256Arm` lets the code write. -/
def narrowWr (s : State) : List Region :=
  [⟨State.addr (s.gpr .r3), 32⟩, ⟨State.addr (stackArg s 0), 384⟩]

/-- Rewrites the contracts at a narrowed state (`stackArg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Pbkdf2.iterateSha256Arm, VG.Proof.Pbkdf2.Arm.iterateWide, VG.Proof.Pbkdf2.Arm.narrowWr, VG.Arm.stackArg_withRegions, VG.Arm.stackArgAddr_withRegions,
    VG.Arm.State.withRegions_gpr, VG.Arm.State.withRegions_sp, VG.Arm.State.withRegions_mem,
    VG.Arm.State.withRegions_rd, VG.Arm.State.withRegions_wr] $(loc)?)

theorem iterateWide_pre (s : State) (h : iterateWide.pre s) :
    Proof.Pbkdf2.iterateSha256Arm.pre (s.withRegions s.rd (narrowWr s)) := by
  obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ := h
  narrow
  exact ⟨h₁, trivial, h₃, h₄.sub_right (Region.sub_of_ble rfl), h₅,
    h₆.sub_right (Region.sub_of_ble rfl), h₇.sub_right (Region.sub_of_ble rfl), h₈,
    h₉.sub_right (Region.sub_of_ble rfl), h₁₀, h₁₁, h₁₂, Region.end_le_of_ble rfl h₁₃, h₁₄⟩

/-- A state satisfying `iterateWide.pre`. -/
def wideSat : State := { sat with wr := [⟨0x3000, 32⟩, ⟨0x4000, 832⟩] }

theorem iterateWide_implies : iterateWide.Implies (Spec.Pbkdf2.iterateSha256Contract Arm.abi) := by
  sig_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig, iterateWide,
    Proof.Pbkdf2.iterateSha256Arm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [wideSat, sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using wideSat

/-- The proof is written against `iterateSha256Arm`, widened to the shared
contract's scratch. -/
theorem iterate_verified :
    Verified Arm.target Impl.Pbkdf2.Arm.iterate (Spec.Pbkdf2.iterateSha256Contract Arm.abi) :=
  have hsat := iterateWide_implies.sat_left
  (Verified.widen (Verified.of_correct iterate_correct iterate_ct
    (.refl (hsat.elim fun s hs => ⟨_, iterateWide_pre s hs⟩)))
    narrowWr iterateWide_pre
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies iterateWide_implies

end VG.Proof.Pbkdf2.Arm
