import VerifiedGarbage.Proof.Pbkdf2.Hmac
import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.AArch64.Contract
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Hmac.AArch64.Common
import VerifiedGarbage.Impl.Pbkdf2.AArch64

/-!
# PBKDF2-HMAC-SHA-256's iteration on AArch64: the parts of a step

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Pbkdf2.X86_64.Iterate`), with the same
target-independent memory lemmas (`VG.Proof.Pbkdf2.Memory`). Each step is two calls of `vg_sha256_compress`,
used as a black box through its proof (`compressAt_ok`, from the streaming
SHA-256 proof).

The lemmas here are about `main`, which runs once `n` is zero-extended: its
entry state `s₀` has `n` as the whole of `x2`.
-/

namespace VG.Proof.Pbkdf2

open Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open Spec.Sha256 (Repr bytesAt)

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for
`vg_pbkdf2_hmac_sha256_iterate(key: *const [u8; 192], u: *const [u8; 32], n: u32, t: *mut [u8; 32], scratch: *mut [u64; 48])`:
if, for a 64-byte key `K₀`, the streaming state at `key` represents
`K₀ ⊕ ipad` and the one at `key + 96` represents `K₀ ⊕ opad`, runs `n` steps
`U ← HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` from the `U` at `u` and the `T` at
`t`, leaving the final `T` at `t`.

The code may read `key` (192 bytes) and `u` (32 bytes), and read and write
`t` (32 bytes) and `scratch` (384 bytes, whose contents on exit are
unspecified). The written regions may not overlap each other or the read
ones. The return address is in `x30` and saved in `scratch`, so no stack is
used. The pointers and `n` are public (`n` only in the low 32 bits of `x2`);
the key, `U` and `T` are secret. -/
def iterateSha256AArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 192⟩
    let u : Region := ⟨s.gpr .x1, 32⟩
    let t : Region := ⟨s.gpr .x3, 32⟩
    let scratch : Region := ⟨s.gpr .x4, 384⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch
  post s s' := ∀ k0, k0.length = 64 →
    Repr s.mem (s.gpr .x0) (xorPad k0 ipad) → Repr s.mem (s.gpr .x0 + 96) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3) 32 =
      Spec.Pbkdf2.iterate (hmacBlockKey sha256 k0) ((s.gpr .x2).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .x1) 32) (bytesAt s.mem (s.gpr .x3) 32)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Pbkdf2

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov save restore compressAt saved)
open VG.Proof.Hmac.X86_64 (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep bytesAt_add)
open VG.Proof.Hmac.AArch64 (add_off)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append writeBytes_nil)
open VG.Proof.Sha256.AArch64 (contains_offset sub_offset toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_addImm wp_ldr wp_str wp_ldr32 wp_str32 wp_rev32)
open VG.Proof.Sha256.AArch64.Stream (compressAt_ok)
open VG.Proof.Sha256.AArch64.Stream.Finalize (writeW_rev32 sw32 flat_length)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base off_contains sep_after writeW_xor
  xorBytes_length add_ofNat stateAt_copy)
open VG.Spec.Sha256 (bytesAt stateAt blockAt compress HashValue wordBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev key : Addr := s₀.gpr .x0
abbrev uP : Addr := s₀.gpr .x1
/-- The number of steps. -/
abbrev nn : Nat := (s₀.gpr .x2).toNat
abbrev tP : Addr := s₀.gpr .x3
abbrev scr : Addr := s₀.gpr .x4
abbrev keyR : Region := ⟨key s₀, 192⟩
abbrev uR : Region := ⟨uP s₀, 32⟩
abbrev tR : Region := ⟨tP s₀, 32⟩
abbrev scR : Region := ⟨scr s₀, 384⟩

/-- A part of the scratch space. -/
abbrev sR (o n : Nat) : Region := ⟨scr s₀ + BitVec.ofNat 64 o, n⟩
/-- `vg_sha256_compress`'s scratch space. -/
abbrev cmpR : Region := ⟨scr s₀, 112⟩
/-- The hash value being compressed. -/
abbrev stA : Addr := scr s₀ + BitVec.ofNat 64 160
abbrev stR : Region := ⟨stA s₀, 32⟩
/-- The block. -/
abbrev blkA : Addr := scr s₀ + BitVec.ofNat 64 192

end

/-- The precondition of `main`: the contract's, with `n` zero-extended. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, uR s₀]
  wr : s₀.wr = [tR s₀, scR s₀]
  k_t : (keyR s₀).Disjoint (tR s₀)
  k_s : (keyR s₀).Disjoint (scR s₀)
  u_t : (uR s₀).Disjoint (tR s₀)
  u_s : (uR s₀).Disjoint (scR s₀)
  t_s : (tR s₀).Disjoint (scR s₀)
  n32 : nn s₀ < 2 ^ 32

/-! ## Regions -/

/-- Two parts of the scratch space at offsets `a` and `b` do not overlap. -/
theorem scr_disj (s₀ : State) {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 384) (hb : b + n ≤ 384) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

theorem scr_disj0 (s₀ : State) {a m n : Nat} (h : n ≤ a) (ha : a + m ≤ 384) :
    Region.Disjoint (sR s₀ a m) ⟨scr s₀, n⟩ := by
  have := scr_disj s₀ (a := a) (m := m) (b := 0) (n := n) (by omega) ha (by omega)
  simp only [sR] at this
  simpa using this

theorem scr_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 384) : Region.Sub (sR s₀ o n) (scR s₀) :=
  sub_offset h (by omega)

theorem cmp_sub (s₀ : State) : Region.Sub (cmpR s₀) (scR s₀) := Region.sub_prefix (by omega)

section
variable {s₀ : State} (hp : Pre s₀) {s : State}
include hp

theorem in_scr (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 384) :
    InRegions s.wr (scr s₀ + BitVec.ofNat 64 a) n :=
  ⟨scR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩

theorem in_t (hwr : s.wr = s₀.wr) {b n : Nat} (h : b + n ≤ 32) :
    InRegions s.wr (tP s₀ + BitVec.ofNat 64 b) n :=
  ⟨tR s₀, by simp [hwr, hp.wr], contains_offset (by omega) (by omega)⟩

theorem in_key (hrd : s.rd = s₀.rd) {a n : Nat} (h : a + n ≤ 192) :
    InRegions (s.rd ++ s.wr) (key s₀ + BitVec.ofNat 64 a) n :=
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

/-! ## The registers and memory during a step -/

/-- The registers the body keeps. -/
def kept : List Reg := [.x19, .x20, .x21, .x22, .x23]

/-- From `s` to `s'`, only the compression's part of the scratch space and
the hash value being compressed changed. -/
structure Keep (s₀ s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  gpr : ∀ r ∈ kept, s'.gpr r = s.gpr r
  frame : Frame [stR s₀, cmpR s₀] s.mem s'.mem

theorem Keep.trans {s₀ s₁ s₂ s₃ : State} (h₁ : Keep s₀ s₁ s₂) (h₂ : Keep s₀ s₂ s₃) : Keep s₀ s₁ s₃ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr),
    h₁.frame.trans h₂.frame⟩

/-- The registers and memory at the start of each step. -/
structure Regs (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = stA s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = key s₀
  x22 : s.gpr .x22 = tP s₀
  frame : Frame [tR s₀, scR s₀] s₀.mem s.mem

theorem Regs.keep {s₀ s s' : State} (h : Regs s₀ s) (hk : Keep s₀ s s') : Regs s₀ s' where
  rd := hk.rd.trans h.rd
  wr := hk.wr.trans h.wr
  sp := hk.sp.trans h.sp
  x19 := (hk.gpr _ (by simp [kept])).trans h.x19
  x20 := (hk.gpr _ (by simp [kept])).trans h.x20
  x21 := (hk.gpr _ (by simp [kept])).trans h.x21
  x22 := (hk.gpr _ (by simp [kept])).trans h.x22
  frame := h.frame.trans (hk.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scR s₀, by simp, scr_sub s₀ (o := 160) (by omega)⟩
    · exact ⟨scR s₀, by simp, cmp_sub s₀⟩)

theorem Regs.write {s₀ s s' : State} (h : Regs s₀ s) (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) {R : Region} (hR : R ∈ [tR s₀, scR s₀])
    (hm : Frame [R] s.mem s'.mem) : Regs s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  x19 := (hg _ (by simp)).trans h.x19
  x20 := (hg _ (by simp)).trans h.x20
  x21 := (hg _ (by simp)).trans h.x21
  x22 := (hg _ (by simp)).trans h.x22
  frame := h.frame.trans (hm.mono (by simpa using hR))

/-- The key's bytes are as on entry. -/
theorem Regs.key_bytes {s₀ s : State} (hp : Pre s₀) (h : Regs s₀ s) {i : Nat} (hi : i < 192) :
    s.mem (key s₀ + BitVec.ofNat 64 i) = s₀.mem (key s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := keyR s₀) (key_disj hp) (by simp) hi

/-! ## Loading a hash value of the key -/

/-- Loading the hash value at `key + o` into `scratch[160..192)`. -/
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) {o : Nat} (ho : o + 32 ≤ 192)
    (ho8 : o % 8 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' → stateAt s'.mem (stA s₀) = stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (load o ++ rest)) s Q := by
  unfold load
  have e0 : stA s₀ + BitVec.ofNat 64 0 = stA s₀ := by simp
  refine Proof.Hmac.AArch64.copy64_ok (by decide) (by decide) o 0 4 ⟨ho8, rfl⟩ ⟨by omega, by omega⟩ rest s Q
    (fun j hj => by rw [h.x21, add_ofNat]; exact in_key hp h.rd (by omega))
    (fun j hj => by rw [h.x19, e0, add_ofNat]; exact in_scr hp h.wr (a := 160 + 8 * j) (by omega))
    ?_ fun s' g' rd' wr' sp' m' => k s' ⟨rd', wr', sp', fun r hr => g' r (by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩ ?_
  · rw [h.x21, h.x19, e0]
    exact Region.Disjoint.sep hp.k_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  · rw [m', h.x19, e0]
    refine (writeBytes_frame _ _ _ (R := stR s₀) ?_).mono (by simp)
    rw [bytesAt_length]; exact contains_base (Nat.le_refl _)
  · rw [m', h.x19, h.x21, e0, stateAt_copy]
    apply Proof.Sha256.Stream.stateAt_congr
    intro i hi
    rw [add_ofNat]
    exact h.key_bytes hp (by omega)

/-! ## A call of `vg_sha256_compress` on the block -/

/-- `x1` at the block. -/
theorem atBlock_ok {s₀ : State} {s : State} (h : Regs s₀ s) {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' → s'.mem = s.mem → s'.gpr .x1 = blkA s₀ → Q s') :
    WP isa (.block [atBlock]) s Q := by
  refine wp_addImm (by omega) fun s' u => WP.block_nil (k s' ⟨u.rd, u.wr, u.sp, fun r hr => u.other r ?_,
    by rw [u.mem]; exact Frame.refl _ _⟩ u.mem (by rw [u.gpr, h.x20]))
  simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Compressing the block into the hash value, in the loop. -/
theorem cmp_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) (h1 : s.gpr .x1 = blkA s₀)
    {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' →
      stateAt s'.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (blockAt s.mem (blkA s₀)) → Q s') :
    WP isa compressAt s Q := by
  have hsc : (scR s₀) ∈ s.wr := by simp [h.wr, hp.wr]
  refine compressAt_ok h.x19 h.x20 h1 (scr_disj0 s₀ (a := 160) (by omega) (by omega))
    (scr_disj s₀ (a := 192) (b := 160) (by omega) (by omega) (by omega))
    (scr_disj0 s₀ (a := 192) (by omega) (by omega)) ?_ ?_
    fun s' hrd hwr hcs hsp hf hst => k s' ⟨hrd, hwr, hsp, fun r hr => hcs r (by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [preserved]) (by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), hf⟩ hst
  · refine Covers.of_sub fun r hr => ⟨scR s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨192, rfl, by simp⟩
    · exact ⟨160, rfl, by simp⟩
    · exact ⟨0, by simp, by simp⟩
  · refine Covers.of_sub fun r hr => ⟨scR s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨160, rfl, by simp⟩
    · exact ⟨0, by simp, by simp⟩

/-! ## The digest into the block -/

/-- The first `n` words of the digest of the hash value at `st` into the
block at `sc + 192`. -/
theorem out_ok {st sc : Addr} (hd : Region.Disjoint ⟨st, 32⟩ ⟨sc + BitVec.ofNat 64 192, 32⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .x19 = st → s.gpr .x20 = sc →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 8, InRegions s.wr (sc + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (sc + BitVec.ofNat 64 192) (((stateAt s.mem st).toList.take n).flatMap wordBytes) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap outW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q h19 h20 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q h19 h20 hin hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    have hP := flat_length (stateAt s.mem st) n (by omega)
    simp only [outW, List.cons_append, List.nil_append]
    refine wp_ldr32 (a := st + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩ (by rw [g₁ _ (by decide), h19])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_rev32 fun s₃ u₃ => wp_str32 (a := sc + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n))
      ⟨by omega, by omega⟩ (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), h20, add_off])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₄ g₄ => k s₄ (fun r hr => by rw [g₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [g₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hread : s₁.mem.readW (st + BitVec.ofNat 64 (4 * n)) 32 = (stateAt s.mem st)[n] := by
      rw [m₁, (writeBytes_frame s.mem (sc + BitVec.ofNat 64 192) _ (R := ⟨sc + BitVec.ofNat 64 192, 32⟩)
        (contains_base (by rw [hP]; omega))).readW
        (r := ⟨st + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (sub_offset (by omega) (by omega))
    rw [g₄.mem, u₃.mem, u₂.mem, u₃.gpr, u₂.gpr, sw32, sw32, hread, m₁, writeW_rev32,
      show sc + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n) = sc + BitVec.ofNat 64 192 + BitVec.ofNat 64
        (((stateAt s.mem st).toList.take n).flatMap wordBytes).length by rw [hP]]
    rw [writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem digest_eq (H : HashValue) : (H.toList.take 8).flatMap wordBytes = Pbkdf2.digest H := by
  rw [List.take_of_length_le (by simp)]; rfl

/-- The digest of the hash value in the scratch space into the block. -/
theorem digest_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Regs s₀ s' → (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → Frame [sR s₀ 192 32] s.mem s'.mem →
      s'.mem = writeBytes s.mem (blkA s₀) (Pbkdf2.digest (stateAt s.mem (stA s₀))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.AArch64.digest ++ rest)) s Q := by
  unfold Impl.Pbkdf2.AArch64.digest
  refine out_ok (st := stA s₀) (sc := scr s₀) (scr_disj s₀ (a := 160) (b := 192) (by omega) (by omega)
    (by omega)) 8 (Nat.le_refl _) rest s Q h.x19 h.x20
    (fun j hj => InRegions.right (by rw [add_ofNat]; exact in_scr hp h.wr (a := 160 + 4 * j) (n := 4) (by omega)))
    (fun j hj => by rw [add_ofNat]; exact in_scr hp h.wr (a := 192 + 4 * j) (by omega)) fun s' g' rd' wr' sp' m' => ?_
  rw [digest_eq] at m'
  have hf : Frame [sR s₀ 192 32] s.mem s'.mem := by
    rw [m']; exact writeBytes_frame _ _ _ (contains_base (by rw [Pbkdf2.digest_length]))
  exact k s' (h.write (fun r hr => g' r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd' wr' sp' (R := scR s₀) (by simp) (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)) g' hf m'

/-! ## `T ← T ⊕ U` -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

/-- `T ← T ⊕ U` for the first `n` 64-bit words of `T` at `tp` and `U` at `sc + 192`. -/
theorem xor_ok {tp sc : Addr} (hd : Region.Disjoint ⟨tp, 32⟩ ⟨sc + BitVec.ofNat 64 192, 32⟩) :
    ∀ n ≤ 4, ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .x22 = tp → s.gpr .x20 = sc →
    (∀ k < 4, InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 192 + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 4, InRegions s.wr (tp + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem tp
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (8 * n)) (bytesAt s.mem (sc + BitVec.ofNat 64 192) (8 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q h22 h20 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q h22 h20 hin hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    have hw := hout n (by omega)
    refine wp_ldr (a := sc + BitVec.ofNat 64 192 + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ (by decide) (by decide), h20, add_off]) (by rw [rd₁, wr₁]; exact hin n (by omega))
      fun s₂ u₂ => ?_
    refine wp_ldr (a := tp + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h22])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact InRegions.right hw) fun s₃ u₃ => ?_
    refine wp_eor fun s₄ u₄ => ?_
    refine wp_str (a := tp + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide), h22])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₅ g₅ => k s₅ (fun r h9 h10 => by rw [g₅.gpr, u₄.other r h9, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (8 * n)) (bytesAt s.mem (sc + BitVec.ofNat 64 192) (8 * n))).length =
        8 * n := by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have v : s₄.gpr .x9 = s₁.mem.readW (sc + BitVec.ofNat 64 192 + BitVec.ofNat 64 (8 * n)) 64 ^^^
        s₁.mem.readW (tp + BitVec.ofNat 64 (8 * n)) 64 := by
      rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₂.mem]
    rw [g₅.mem, u₄.mem, u₃.mem, u₂.mem, v, writeW_xor, m₁,
      bytesAt_writeBytes_sep (p := tp + BitVec.ofNat 64 (8 * n)),
      bytesAt_writeBytes_sep (p := sc + BitVec.ofNat 64 192 + BitVec.ofNat 64 (8 * n))]
    · have e := writeBytes_append s.mem tp _ (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp + BitVec.ofNat 64 (8 * n)) 8)
        (bytesAt s.mem (sc + BitVec.ofNat 64 192 + BitVec.ofNat 64 (8 * n)) 8))
        (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro x h₁ h₂
      rw [hl] at h₂
      exact hd x (by simp only [Region.Contains]; omega) (off_contains h₁ (by omega) (by omega))
    · omega
    · intro x h₁ h₂
      rw [hl] at h₂
      exact sep_after h₁ h₂ (by omega)
    · omega

end VG.Proof.Pbkdf2.AArch64
