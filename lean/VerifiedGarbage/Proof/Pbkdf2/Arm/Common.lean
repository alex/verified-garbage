import VerifiedGarbage.Proof.Pbkdf2.Hmac
import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.Arm.Contract
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Iterate
import VerifiedGarbage.Proof.Hmac.Arm.Init
import VerifiedGarbage.Impl.Pbkdf2.Arm

/-!
# PBKDF2-HMAC-SHA-256's iteration on ARMv7: the parts of a step

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 and AArch64 proofs (`VG.Proof.Pbkdf2.X86_64.Iterate`,
`VG.Proof.Pbkdf2.AArch64`), whose target-independent memory lemmas are
reused. Each step is two calls of `vg_sha256_compress`, used as a black box
through its proof (`compressAt_ok`, from the streaming SHA-256 proof). The
hash value being compressed is `t`, and `T` is kept in `scratch[160..192)`.
-/

namespace VG.Proof.Pbkdf2

open Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open Spec.Sha256 (Repr bytesAt)

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
32-bit ARM contract for
`vg_pbkdf2_hmac_sha256_iterate(key: *const [u8; 192], u: *const [u8; 32], n: u32, t: *mut [u8; 32], scratch: *mut [u64; 48])`:
if, for a 64-byte key `K₀`, the streaming state at `key` represents
`K₀ ⊕ ipad` and the one at `key + 96` represents `K₀ ⊕ opad`, runs `n` steps
`U ← HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` from the `U` at `u` and the `T` at
`t`, leaving the final `T` at `t`.

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
open VG.Proof.Sha256.Arm.Stream (Upd Mupd wp_add wp_ldr wp_str wp_rev op2_imm op2_reg compressAt_ok sub_offset)
open VG.Proof.Sha256.Arm.Stream.Finalize (writeW_rev flat_length)
open VG.Proof.Hmac.Arm (copy_ok add_off)
open VG.Proof.Hmac.Arm.Init (wp_eor)
open VG.Proof.Hmac.X86_64 (bytesAt_length bytesAt_writeBytes_sep bytesAt_add extractLsb'_read)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append writeBytes_nil write_eq_writeBytes)
open VG.Proof.Pbkdf2.X86_64.Iterate (frame_bytesAt contains_base off_contains sep_after xorBytes_length
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
      have := VG.Proof.Sha256.Arm.Stream.Update.addr_toNat p3
      bv_omega
    · omega
    · intro x h₁ h₂
      rw [hl] at h₂
      exact sep_after h₁ h₂ (by omega)
    · omega

end VG.Proof.Pbkdf2.Arm
