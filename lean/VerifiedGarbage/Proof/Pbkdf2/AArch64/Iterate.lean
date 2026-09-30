import VerifiedGarbage.Proof.Pbkdf2.Hmac
import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.AArch64.Contract
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Hmac.AArch64.Common
import VerifiedGarbage.Impl.Pbkdf2.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Spec.Pbkdf2.Contract
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Lit

/-!
# PBKDF2-HMAC-SHA-256's iteration on AArch64: the parts of a step

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`Proof/Pbkdf2/X86_64/Iterate.lean`), with the same
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
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep
  bytesAt_add)
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

/-!
# PBKDF2-HMAC-SHA-256's iteration on AArch64: the loop

Untrusted: everything here is checked by Lean. One step is HMAC-SHA-256 of
`U` as two compressions (`VG.Proof.Pbkdf2.hmac_step`), then `T ← T ⊕ U`.
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Impl.Sha256.AArch64.Stream (saved)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.AArch64 (wp_subImm eval_zero eval_nonzero ofNat_beq_zero ofNat_pred)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base blockAt_eq xorBytes_length add_ofNat
  digest_self)
open VG.Spec.Sha256 (bytesAt stateAt blockAt compress HashValue)

section
variable (s₀ : State)

/-- The key's inner and outer hash values. -/
abbrev Hi : HashValue := stateAt s₀.mem (key s₀ + BitVec.ofNat 64 0)
abbrev Ho : HashValue := stateAt s₀.mem (key s₀ + BitVec.ofNat 64 96)

/-- A step, as the code computes it. -/
def stepM (u : List Byte) : List Byte :=
  Pbkdf2.digest (compress (Ho s₀) (block96 (Pbkdf2.digest (compress (Hi s₀) (block96 u)))))

/-- Our caller's registers and our return address, saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  (∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1) ∧
  m.readW (scr s₀ + BitVec.ofNat 64 256) 64 = s₀.gpr .x30

/-- What the body writes: the compression's part of the scratch space, the
hash value being compressed, the block's first 32 bytes and `T`. -/
abbrev bodyR : List Region := [stR s₀, cmpR s₀, sR s₀ 192 32, tR s₀]

end

/-- Parts of the scratch space that the body leaves: the saved registers
(`[112..160)`), the padding and the saved return address (from 224). -/
theorem body_disj {s₀ : State} (hp : Pre s₀) {o n : Nat} (h₁ : (112 ≤ o ∧ o + n ≤ 160) ∨ 224 ≤ o)
    (h₂ : o + n ≤ 384) : ∀ r ∈ bodyR s₀, Region.Disjoint (sR s₀ o n) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact scr_disj s₀ (b := 160) (n := 32) (by omega) h₂ (by omega)
  · exact scr_disj0 s₀ (by omega) h₂
  · exact scr_disj s₀ (b := 192) (n := 32) (by omega) h₂ (by omega)
  · exact (hp.t_s.sub_right (scr_sub s₀ h₂)).symm

/-- The block's first 32 bytes are neither the hash value nor the compression's scratch. -/
theorem blk_disj (s₀ : State) : ∀ r ∈ [stR s₀, cmpR s₀], Region.Disjoint (sR s₀ 192 32) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact scr_disj s₀ (b := 160) (n := 32) (by omega) (by omega) (by omega)
  · exact scr_disj0 s₀ (by omega) (by omega)

theorem Saved.frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m) (hf : Frame (bodyR s₀) m m') :
    Saved s₀ m' := by
  refine ⟨fun p hp' => ?_, ?_⟩
  · rw [← h.1 p hp']
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact hf.readW (r := sR s₀ p.2 8) (Region.contains_self _ _) (body_disj hp (.inl hd) (by omega)) (by decide)
  · rw [← h.2]
    exact hf.readW (r := sR s₀ 256 8) (Region.contains_self _ _) (body_disj hp (.inr (by omega)) (by omega))
      (by decide)

theorem frame_body {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, r ∈ bodyR s₀) :
    Frame (bodyR s₀) m m' := hf.mono hs

/-- The loop invariant, with `r` steps left. -/
structure Inv (s₀ : State) (r : Nat) (s : State) : Prop extends Regs s₀ s where
  x23 : s.gpr .x23 = BitVec.ofNat 64 r
  saved : Saved s₀ s.mem
  pad : bytesAt s.mem (scr s₀ + BitVec.ofNat 64 224) 32 = pad96
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM s₀) (nn s₀) (bytesAt s₀.mem (uP s₀) 32) (bytesAt s₀.mem (tP s₀) 32) =
    Spec.Pbkdf2.iterate (stepM s₀) r (bytesAt s.mem (blkA s₀) 32) (bytesAt s.mem (tP s₀) 32)

theorem body_ok {s₀ : State} (hp : Pre s₀) {r : Nat} {s : State} (h : Inv s₀ (r + 1) s) :
    WP isa body s fun s' => eval (.nonzero .x .x23) s' = some (r != 0) ∧ Inv s₀ r s' := by
  unfold body
  have hU : ∀ {m : Mem}, Frame [stR s₀, cmpR s₀] s.mem m → bytesAt m (blkA s₀) 32 = bytesAt s.mem (blkA s₀) 32 :=
    fun hf => frame_bytesAt hf (blk_disj s₀) (by omega)
  have hpad : ∀ {m : Mem}, Frame (bodyR s₀) s.mem m → bytesAt m (blkA s₀ + 32) 32 = pad96 := by
    intro m hf
    rw [show blkA s₀ + 32 = scr s₀ + BitVec.ofNat 64 224 by bv_omega, ← h.pad]
    exact frame_bytesAt hf (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  -- The inner hash.
  refine WP.seq ?_
  refine load_ok hp h.toRegs (o := 0) (by omega) (by decide) fun s₁ k₁ e₁ => ?_
  refine atBlock_ok (h.toRegs.keep k₁) fun s₂ k₂ m₂ x1₂ => ?_
  have h₂ := (h.toRegs.keep k₁).keep k₂
  refine WP.seq (cmp_ok hp h₂ x1₂ fun s₃ k₃ e₃ => ?_)
  rw [m₂, e₁, blockAt_eq (hpad (frame_body k₁.frame (by simp))), hU k₁.frame] at e₃
  -- The outer hash.
  have h₃ := h₂.keep k₃
  refine WP.seq ?_
  refine digest_ok hp h₃ fun s₄ h₄ g₄ f₄ m₄ => ?_
  refine load_ok hp h₄ (o := 96) (by omega) (by decide) fun s₅ k₅ e₅ => ?_
  refine atBlock_ok (h₄.keep k₅) fun s₆ k₆ m₆ x1₆ => ?_
  have h₆ := (h₄.keep k₅).keep k₆
  have f₃₄ : Frame (bodyR s₀) s.mem s₄.mem :=
    (frame_body ((k₁.trans k₂).trans k₃).frame (by simp)).trans (frame_body f₄ (by simp))
  refine WP.seq (cmp_ok hp h₆ x1₆ fun s₇ k₇ e₇ => ?_)
  have hX : bytesAt s₅.mem (blkA s₀) 32 = Pbkdf2.digest (stateAt s₃.mem (stA s₀)) := by
    rw [frame_bytesAt (p := blkA s₀) (n := 32) k₅.frame (blk_disj s₀) (by omega), m₄, digest_self]
  rw [m₆, e₅, blockAt_eq (hpad (f₃₄.trans (frame_body k₅.frame (by simp)))), hX, e₃] at e₇
  -- The digest, `T ← T ⊕ U` and the count.
  have h₇ := h₆.keep k₇
  refine digest_ok hp h₇ fun s₈ h₈ g₈ f₈ m₈ => ?_
  have hd : Region.Disjoint (tR s₀) ⟨scr s₀ + BitVec.ofNat 64 192, 32⟩ :=
    hp.t_s.sub_right (scr_sub s₀ (o := 192) (by omega))
  refine xor_ok (tp := tP s₀) (sc := scr s₀) hd 4 (Nat.le_refl _) _ s₈ _ h₈.x22 h₈.x20
    (fun j hj => InRegions.right (by rw [add_ofNat]; exact in_scr hp h₈.wr (a := 192 + 8 * j) (n := 8) (by omega)))
    (fun j hj => in_t hp h₈.wr (b := 8 * j) (n := 8) (by omega)) fun s₉ g₉ rd₉ wr₉ sp₉ m₉ => ?_
  rw [show 8 * 4 = 32 from rfl] at m₉
  have f₉ : Frame [tR s₀] s₈.mem s₉.mem := by
    rw [m₉]; exact writeBytes_frame _ _ _ (contains_base (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]))
  have h₉ := h₈.write (fun r hr => g₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₉ wr₉ sp₉ (R := tR s₀) (by simp) f₉
  refine wp_subImm (by omega) fun s₁₀ u₁₀ => WP.block_nil ?_
  have h₁₀ := h₉.write (fun r hr => u₁₀.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) u₁₀.rd u₁₀.wr u₁₀.sp (R := tR s₀) (by simp)
    (by rw [u₁₀.mem]; exact Frame.refl _ _)
  have x23 : s₉.gpr .x23 = BitVec.ofNat 64 (r + 1) := by
    rw [g₉ _ (by decide) (by decide), g₈ _ (by decide), k₇.gpr _ (by simp [kept]), k₆.gpr _ (by simp [kept]),
      k₅.gpr _ (by simp [kept]), g₄ _ (by decide), k₃.gpr _ (by simp [kept]), k₂.gpr _ (by simp [kept]),
      k₁.gpr _ (by simp [kept]), h.x23]
  have hlt : r + 1 < 2 ^ 64 := by have := h.le; have := hp.n32; omega
  have e₁₀ : s₉.gpr .x23 - BitVec.ofNat 64 1 = BitVec.ofNat 64 r := by
    rw [x23, show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega)]; rfl
  have fb : Frame (bodyR s₀) s.mem s₁₀.mem := by
    rw [u₁₀.mem]
    exact f₃₄.trans (frame_body ((k₅.trans k₆).trans k₇).frame (by simp)) |>.trans (frame_body f₈ (by simp))
      |>.trans (frame_body f₉ (by simp))
  have f₈' : Frame [stR s₀, cmpR s₀, sR s₀ 192 32] s.mem s₈.mem :=
    (((k₁.trans k₂).trans k₃).frame.mono (by simp)) |>.trans (f₄.mono (by simp))
      |>.trans ((((k₅.trans k₆).trans k₇).frame).mono (by simp)) |>.trans (f₈.mono (by simp))
  have hT : bytesAt s₈.mem (tP s₀) 32 = bytesAt s.mem (tP s₀) 32 := by
    refine frame_bytesAt f₈' (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.t_s.sub_right (scr_sub s₀ (o := 160) (by omega))
    · exact hp.t_s.sub_right (cmp_sub s₀)
    · exact hd
  have hU₈ : bytesAt s₈.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [m₈, digest_self, e₇]; rfl
  have hU₁₀ : bytesAt s₁₀.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [u₁₀.mem, m₉, bytesAt_writeBytes_sep _ _ (fun x h₁ h₂ => hd x ?_ ?_) (by omega), hU₈]
    · simp only [Region.Contains]; rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length] at h₂; omega
    · simp only [Region.Contains, blkA] at h₁ ⊢; omega
  have hT₁₀ : bytesAt s₁₀.mem (tP s₀) 32 =
      Spec.Pbkdf2.xorBytes (bytesAt s.mem (tP s₀) 32) (stepM s₀ (bytesAt s.mem (blkA s₀) 32)) := by
    have := bytesAt_writeBytes_self s₈.mem (tP s₀)
      (Spec.Pbkdf2.xorBytes (bytesAt s₈.mem (tP s₀) 32) (bytesAt s₈.mem (scr s₀ + BitVec.ofNat 64 192) 32))
      (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length] at this
    rw [u₁₀.mem, m₉, this, hT, hU₈]
  have hle : r ≤ nn s₀ := by have := h.le; omega
  refine ⟨?_, { h₁₀ with x23 := ?_, saved := h.saved.frame hp fb, pad := ?_, le := hle, val := ?_ }⟩
  · rw [eval_nonzero, u₁₀.gpr, e₁₀]
    simp only [bne, ofNat_beq_zero (by omega : r < 2 ^ 64)]
    cases r <;> rfl
  · rw [u₁₀.gpr, e₁₀]
  · rw [← h.pad]
    exact frame_bytesAt fb (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  · rw [h.val, hU₁₀, hT₁₀]; rfl

theorem loop_ok {s₀ : State} (hp : Pre s₀) {n : Nat} {s : State} (h : Inv s₀ n s) :
    WP isa (.ite (.zero .x .x23) (.block []) (.loop body (.nonzero .x .x23))) s (Inv s₀ 0) := by
  have hn : n < 2 ^ 64 := by have := h.le; have := hp.n32; omega
  refine WP.ite (decide (n = 0))
    (by show VG.AArch64.eval (.zero .x .x23) s = _
        rw [eval_zero, h.x23, ofNat_beq_zero hn]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => Inv s₀ (m + 1) s) (fun m s hs => WP.mono (body_ok hp hs) fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end VG.Proof.Pbkdf2.AArch64

/-!
# PBKDF2-HMAC-SHA-256's iteration on AArch64

Untrusted: everything here is checked by Lean. The prologue, the epilogue,
and `Verified`. The first instruction zero-extends `n`, of which only the low
32 bits are public; `main` runs from there, with all of `x2` public, so its
constant time is proven by the taint analysis from that state.
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Impl.Sha256.AArch64.Stream (saved restore)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.AArch64 (contains_offset)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_movz wp_addImm wp_ldr wp_str readW_writeW_save
  untouched)
open VG.Proof.Sha256.AArch64.Stream (save_ok restore_ok saveMem saveMem_saved saveMem_frame)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base writeW_bytes writeBytes_append' iterate_congr)
open VG.Spec.Sha256 (bytesAt stateAt Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)

/-! ## The prologue -/

theorem wp_movz3 {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 64 <<< 48) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 3 :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (imm.setWidth 64 <<< 48)) (by simp [exec, Size.bits])
    (k _ (Upd.write64 _ _ _))

/-- The padding into `scratch[224..256)`. -/
theorem padding_ok {s₀ : State} (hp : Pre s₀) {s : State} (h20 : s.gpr .x20 = scr s₀) (hwr : s.wr = s₀.wr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 224) pad96 → WP isa (.block rest) s' Q) :
    WP isa (.block (padding ++ rest)) s Q := by
  simp only [padding, List.cons_append, List.nil_append]
  refine wp_movz fun s₁ u₁ => ?_
  have c₁ : s₁.gpr .x20 = scr s₀ := by rw [u₁.other _ (by decide), h20]
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 224) (by decide) (by rw [c₁])
    (in_scr hp (u₁.wr.trans hwr) (by omega)) fun s₂ g₂ => ?_
  refine wp_movz fun s₃ u₃ => ?_
  have c₃ : s₃.gpr .x20 = scr s₀ := by rw [u₃.other _ (by decide), g₂.gpr, c₁]
  have w₃ : s₃.wr = s.wr := by rw [u₃.wr, g₂.wr, u₁.wr]
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 232) (by decide) (by rw [c₃])
    (in_scr hp (w₃.trans hwr) (by omega)) fun s₄ g₄ => ?_
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 240) (by decide) (by rw [g₄.gpr, c₃])
    (by rw [g₄.wr]; exact in_scr hp (w₃.trans hwr) (by omega)) fun s₅ g₅ => ?_
  refine wp_movz3 fun s₆ u₆ => ?_
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 248) (by decide) (by rw [u₆.other _ (by decide), g₅.gpr, g₄.gpr, c₃])
    (by rw [u₆.wr, g₅.wr, g₄.wr]; exact in_scr hp (w₃.trans hwr) (by omega)) fun s₇ g₇ => ?_
  refine k s₇ (fun r hr => ?_) (by rw [g₇.rd, u₆.rd, g₅.rd, g₄.rd, u₃.rd, g₂.rd, u₁.rd])
    (by rw [g₇.wr, u₆.wr, g₅.wr, g₄.wr, w₃]) (by rw [g₇.sp, u₆.sp, g₅.sp, g₄.sp, u₃.sp, g₂.sp, u₁.sp]) ?_
  · rw [g₇.gpr, u₆.other r hr, g₅.gpr, g₄.gpr, u₃.other r hr, g₂.gpr, u₁.other r hr]
  · have e₂ : s₂.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 224) [0x80, 0, 0, 0, 0, 0, 0, 0] := by
      rw [g₂.mem, u₁.gpr, u₁.mem]; exact writeW_bytes _ _ _ _ (by decide)
    have e₄ : s₄.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 224)
        ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]) := by
      rw [g₄.mem, u₃.gpr, u₃.mem, e₂, writeW_bytes _ _ _ [0, 0, 0, 0, 0, 0, 0, 0] (by decide)]
      exact writeBytes_append' _ _ _ (by simp only [List.length_cons, List.length_nil]; bv_omega) (by simp)
    have e₅ : s₅.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 224)
        ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]) := by
      rw [g₅.mem, g₄.gpr, u₃.gpr, e₄, writeW_bytes _ _ _ [0, 0, 0, 0, 0, 0, 0, 0] (by decide)]
      exact writeBytes_append' _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; bv_omega)
        (by simp)
    rw [g₇.mem, u₆.gpr, u₆.mem, e₅, writeW_bytes _ _ _ [0, 0, 0, 0, 0, 0, 3, 0] (by decide),
      writeBytes_append' _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; bv_omega)
        (by simp)]
    rfl

theorem readW_writeW_ne (m : Mem) {a b : Addr} (v : BitVec 64) (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  (Frame.writeW (Frame.refl [⟨b, 8⟩] m) (r := ⟨b, 8⟩) (List.mem_singleton_self _) v
    (contains_base (by decide))).readW (r := ⟨a, 8⟩)
    (contains_base (by decide)) (by simpa using h) (by decide)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ (Inv s₀ (nn s₀)) := by
  unfold prologue
  refine save_ok (fun d _ hd₂ => in_scr hp rfl (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  -- The return address.
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 256) (by decide) (by rw [g₁])
    (by rw [wr₁]; exact in_scr hp rfl (by omega)) fun s₂ g₂ => ?_
  -- Our registers.
  refine wp_addImm (by omega) fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ =>
    wp_mov fun s₇ u₇ => ?_
  have G : ∀ r, s₂.gpr r = s₀.gpr r := fun r => by rw [g₂.gpr, g₁]
  have hr : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s₇.gpr r = s₀.gpr r := by
    intro r h₁ h₂ h₃ h₄ h₅
    rw [u₇.other r h₅, u₆.other r h₄, u₅.other r h₃, u₄.other r h₂, u₃.other r h₁, G]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, rd₁]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, wr₁]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, g₂.sp, sp₁]
  have M₇ : s₇.mem = (saveMem s₀.mem (scr s₀) s₀.gpr).writeW (scr s₀ + BitVec.ofNat 64 256) (s₀.gpr .x30) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, m₁, g₁]
  have x19₇ : s₇.gpr .x19 = stA s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, G]
  have x20₇ : s₇.gpr .x20 = scr s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), G]
  have x21₇ : s₇.gpr .x21 = key s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), G]
  have x22₇ : s₇.gpr .x22 = tP s₀ := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), G]
  have x23₇ : s₇.gpr .x23 = s₀.gpr .x2 := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), G]
  have x1₇ : s₇.gpr .x1 = uP s₀ := hr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  -- `U` and the padding.
  refine Proof.Hmac.AArch64.copy64_ok (by decide) (by decide) 0 192 4 ⟨rfl, rfl⟩ ⟨by omega, by omega⟩ _ s₇ _
    (fun j hj => by
      rw [x1₇, rd₇, wr₇, Proof.Pbkdf2.Memory.add_ofNat]
      exact ⟨uR s₀, by simp [hp.rd], contains_offset (by omega) (by omega)⟩)
    (fun j hj => by rw [x20₇, wr₇, Proof.Pbkdf2.Memory.add_ofNat]; exact in_scr hp rfl (by omega)) ?_
    fun s₈ g₈ rd₈ wr₈ sp₈ m₈ => ?_
  · rw [x1₇, x20₇]
    exact Region.Disjoint.sep hp.u_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  refine padding_ok hp (by rw [g₈ _ (by decide), x20₇]) (wr₈.trans wr₇) fun s₉ g₉ rd₉ wr₉ sp₉ m₉ => WP.block_nil ?_
  have G₉ : ∀ r, r ≠ .x9 → s₉.gpr r = s₇.gpr r := fun r h => by rw [g₉ r h, g₈ r h]
  have e0 : uP s₀ + BitVec.ofNat 64 0 = uP s₀ := by simp
  have hm : s₉.mem = writeBytes (writeBytes s₇.mem (blkA s₀) (bytesAt s₇.mem (uP s₀) 32))
      (scr s₀ + BitVec.ofNat 64 224) pad96 := by
    rw [m₉, m₈, x20₇, x1₇, e0]
  have inS : ∀ d n : Nat, d + n ≤ 384 → (scR s₀).Contains (scr s₀ + BitVec.ofNat 64 d) n :=
    fun d n h => contains_offset h (by omega)
  have F₇ : Frame [scR s₀] s₀.mem s₇.mem := by
    rw [M₇]
    exact ((saveMem_frame s₀.mem (scr s₀) s₀.gpr).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (inS 256 8 (by omega))
  have fU : Frame [sR s₀ 192 32, sR s₀ 224 32] s₇.mem s₉.mem := by
    rw [hm]
    exact ((writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))).mono (by simp)).trans
      ((writeBytes_frame _ _ _ (R := sR s₀ 224 32) (contains_base (by decide))).mono (by simp))
  have F' : Frame [scR s₀] s₀.mem s₉.mem :=
    F₇.trans (fU.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩
      · exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)
  have F : Frame [tR s₀, scR s₀] s₀.mem s₉.mem := F'.mono (by simp)
  have hsep : Mem.Sep (blkA s₀) 32 (scr s₀ + BitVec.ofNat 64 224) pad96.length :=
    Region.Disjoint.sep (scr_disj s₀ (a := 192) (m := 32) (b := 224) (n := 32) (by omega) (by omega) (by omega))
      (contains_base (Nat.le_refl _)) (contains_base (Nat.le_refl _))
  have hU : bytesAt s₉.mem (blkA s₀) 32 = bytesAt s₀.mem (uP s₀) 32 := by
    have := bytesAt_writeBytes_self s₇.mem (blkA s₀) (bytesAt s₇.mem (uP s₀) 32) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at this
    rw [hm, bytesAt_writeBytes_sep _ _ hsep (by omega), this]
    exact frame_bytesAt F₇ (by simpa using hp.u_s) (by omega)
  have hT : bytesAt s₉.mem (tP s₀) 32 = bytesAt s₀.mem (tP s₀) 32 :=
    frame_bytesAt F' (by simpa using hp.t_s) (by omega)
  have hS : ∀ {d : Nat}, (112 ≤ d ∧ d + 8 ≤ 160) ∨ 256 ≤ d → d + 8 ≤ 384 →
      s₉.mem.readW (scr s₀ + BitVec.ofNat 64 d) 64 = s₇.mem.readW (scr s₀ + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    refine fU.readW (r := sR s₀ d 8) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_disj s₀ (by omega) (by omega) (by omega)
    · exact scr_disj s₀ (by omega) (by omega) (by omega)
  refine ⟨⟨by rw [rd₉, rd₈, rd₇], by rw [wr₉, wr₈, wr₇], by rw [sp₉, sp₈, sp₇], by rw [G₉ _ (by decide), x19₇],
    by rw [G₉ _ (by decide), x20₇], by rw [G₉ _ (by decide), x21₇], by rw [G₉ _ (by decide), x22₇], F⟩,
    ?_, ⟨fun p hp' => ?_, ?_⟩, ?_, (Nat.le_refl _), by rw [hU, hT]⟩
  · rw [G₉ _ (by decide), x23₇]; simp [nn]
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    rw [hS (.inl hd) (by omega), M₇, readW_writeW_save _ _ _ (by omega) (by omega) (by omega)]
    exact saveMem_saved _ _ _ p (by simp only [saved, List.mem_cons, List.not_mem_nil, or_false]; exact hp')
  · rw [hS (.inr (Nat.le_refl _)) (by omega), M₇, Mem.readW_writeW_self64]
  · rw [hm]
    exact bytesAt_writeBytes_self _ (scr s₀ + BitVec.ofNat 64 224) pad96 (by decide)

/-! ## The epilogue -/

/-- The postcondition of `main`. -/
def Post (s₀ s' : State) : Prop :=
  ∀ k0, k0.length = 64 → Repr s₀.mem (key s₀) (xorPad k0 ipad) → Repr s₀.mem (key s₀ + 96) (xorPad k0 opad) →
    bytesAt s'.mem (tP s₀) 32 =
      Spec.Pbkdf2.iterate (hmacBlockKey sha256 k0) (nn s₀) (bytesAt s₀.mem (uP s₀) 32) (bytesAt s₀.mem (tP s₀) 32)

/-- With the key's streaming states as the contract requires, a step is HMAC-SHA-256. -/
theorem stepM_eq {s₀ : State} {k0 : List Byte} (hk : k0.length = 64)
    (hi : Repr s₀.mem (key s₀) (xorPad k0 ipad)) (ho : Repr s₀.mem (key s₀ + 96) (xorPad k0 opad))
    {u : List Byte} (hu : u.length = 32) :
    hmacBlockKey sha256 k0 u = stepM s₀ u := by
  have li : (xorPad k0 ipad).length = 64 := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = 64 := by simp [xorPad, hk]
  have e0 : key s₀ + BitVec.ofNat 64 0 = key s₀ := by simp
  have ho1 : stateAt s₀.mem (key s₀ + BitVec.ofNat 64 96) = _ := ho.1
  rw [hmac_step hk hu, stepM, Hi, Ho, e0, hi.1, ho1, li, lo]

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ 0 s) :
    WP isa (.block epilogue) s fun s' => (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧
      s'.gpr .x30 = s₀.gpr .x30 ∧ s'.sp = s₀.sp ∧ Post s₀ s' := by
  unfold epilogue
  refine wp_ldr (a := scr s₀ + BitVec.ofNat 64 256) (by decide) (by rw [h.x20])
    (InRegions.right (in_scr hp h.wr (by omega))) fun s₁ u₁ => ?_
  refine restore_ok (scr := scr s₀) (by rw [u₁.other _ (by decide), h.x20])
    (fun d _ hd₂ => by rw [u₁.wr]; exact InRegions.right (in_scr hp h.wr (by omega))) s₀.gpr
    (fun p hp' => by rw [u₁.mem]; exact h.saved.1 p hp')
    fun s' hs hother hmem _ _ hsp => ⟨hs, by rw [hother .x30 (by simp [saved]), u₁.gpr, h.saved.2],
      by rw [hsp, u₁.sp, h.sp], fun k0 hk hi ho => ?_⟩
  have := h.val
  simp only [Spec.Pbkdf2.iterate] at this
  rw [hmem, u₁.mem, ← this]
  exact (iterate_congr (fun u hu => stepM_eq hk hi ho hu) (fun u => Pbkdf2.digest_length _) _ _ _
    (bytesAt_length _ _ _)).symm

/-! ## Correctness -/

/-- No instruction of `main` writes the callee-saved registers it does not save. -/
theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs main, dstOf i ≠ some r := by
  have : ((instrs main).all fun i => untouched.all fun r => dstOf i != some r) = true :=
    instrs_keeps (by decide +kernel)
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

theorem correctMain {s₀ : State} (hp : Pre s₀) :
    WP isa main s₀ fun s' => abiPreserved s₀ s' ∧ Post s₀ s' := by
  refine WP.mono (Proof.MdStream.AArch64.WP.gprs (Q := fun s' => (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧
      s'.gpr .x30 = s₀.gpr .x30 ∧ s'.sp = s₀.sp ∧ Post s₀ s') ?_ untouched_ok)
    fun s' ⟨⟨hsv, h30, hsp, hpost⟩, hu⟩ => ⟨⟨fun r hr => ?_, hsp⟩, hpost⟩
  · unfold main
    refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
    exact WP.seq (WP.mono (loop_ok hp h₁) fun s₂ h₂ => epilogue_ok hp h₂)
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv (.x19, 112) (by simp [saved])
    · exact hsv (.x20, 120) (by simp [saved])
    · exact hsv (.x21, 128) (by simp [saved])
    · exact hsv (.x22, 136) (by simp [saved])
    · exact hsv (.x23, 144) (by simp [saved])
    · exact hsv (.x24, 152) (by simp [saved])
    all_goals first | exact h30 | exact hu _ (by simp [untouched])

/-- The state after the first instruction, which zero-extends `n`. -/
def zext (s : State) : State := s.write .w .x2 (s.read .w .x2 + BitVec.ofNat 32 0)

theorem zext_exec (s : State) : Exec isa (.block [.addImm .w .x2 .x2 0]) s [] (zext s) := .block rfl

theorem zext_other (s : State) {r : Reg} (h : r ≠ .x2) : (zext s).gpr r = s.gpr r :=
  (Upd.write s .w .x2 _).other r h

theorem zext_x2 (s : State) : (zext s).gpr .x2 = ((s.gpr .x2).setWidth 32).setWidth 64 := by
  rw [zext, (Upd.write s .w .x2 _).gpr]; simp [State.read]

theorem pre_of {s : State} (h : Proof.Pbkdf2.iterateSha256AArch64.pre s) : Pre (zext s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e0 : (zext s).gpr .x0 = s.gpr .x0 := zext_other s (by decide)
  have e1 : (zext s).gpr .x1 = s.gpr .x1 := zext_other s (by decide)
  have e3 : (zext s).gpr .x3 = s.gpr .x3 := zext_other s (by decide)
  have e4 : (zext s).gpr .x4 = s.gpr .x4 := zext_other s (by decide)
  have hn : nn (zext s) < 2 ^ 32 := by
    simp only [nn, zext_x2, BitVec.toNat_setWidth]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hn⟩ <;>
    simp only [keyR, uR, tR, scR, key, uP, tP, scr, e0, e1, e3, e4] <;> assumption

theorem correct {s : State} (hs : Proof.Pbkdf2.iterateSha256AArch64.pre s) :
    ∃ t s', Exec isa iterate s t s' ∧ abiPreserved s s' ∧ Proof.Pbkdf2.iterateSha256AArch64.post s s' := by
  obtain ⟨t, s', he, ⟨habi, hsp⟩, hpost⟩ := correctMain (pre_of hs)
  refine ⟨[] ++ t, s', .seq (zext_exec s) he, ⟨fun r hr => ?_, hsp⟩, fun k0 hk hi ho => ?_⟩
  · have hne : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [habi r hr, zext_other s hne]
  · have e0 : (zext s).gpr .x0 = s.gpr .x0 := zext_other s (by decide)
    have e1 : (zext s).gpr .x1 = s.gpr .x1 := zext_other s (by decide)
    have e3 : (zext s).gpr .x3 = s.gpr .x3 := zext_other s (by decide)
    have e : nn (zext s) = ((s.gpr .x2).setWidth 32).toNat := by
      simp only [nn, zext_x2, BitVec.toNat_setWidth]
      omega
    have hi' : Repr (zext s).mem (key (zext s)) (xorPad k0 ipad) := by simp only [key, e0]; exact hi
    have ho' : Repr (zext s).mem (key (zext s) + 96) (xorPad k0 opad) := by simp only [key, e0]; exact ho
    have := hpost k0 hk hi' ho'
    simp only [tP, uP, e1, e3, e] at this
    exact this

/-! ## Constant time -/

theorem ct_of {τ : VG.AArch64.Taint.T}
    (hτ : ∀ s₁ s₂, Proof.Pbkdf2.iterateSha256AArch64.pub s₁ s₂ → VG.AArch64.Taint.Agree τ (zext s₁) (zext s₂))
    {hc : VG.Taint.Hint taint.T} (h : (taint.check τ main hc).isSome = true) :
    ConstantTime isa Proof.Pbkdf2.iterateSha256AArch64.pre Proof.Pbkdf2.iterateSha256AArch64.pub iterate := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hp e₁ e₂
  obtain ⟨τ', hc'⟩ := Option.isSome_iff_exists.mp h
  unfold iterate at e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      obtain ⟨rfl, rfl⟩ := Exec.det a₁ (zext_exec s₁)
      obtain ⟨rfl, rfl⟩ := Exec.det a₂ (zext_exec s₂)
      rw [(VG.Taint.check_sound (A := taint) hc' (hτ _ _ hp) b₁ b₂).1]

/-- The initial taint of `main`: the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Pbkdf2.iterateSha256AArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (zext s₁) (zext s₂) := by
  obtain ⟨p0, p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [zext_other _ (by decide), zext_other _ (by decide), p0]
  · rw [zext_other _ (by decide), zext_other _ (by decide), p1]
  · rw [zext_x2, zext_x2, p2]
  · rw [zext_other _ (by decide), zext_other _ (by decide), p3]
  · rw [zext_other _ (by decide), zext_other _ (by decide), p4]

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 192⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 384⟩]

theorem iterate_ct : ConstantTime isa Proof.Pbkdf2.iterateSha256AArch64.pre
    Proof.Pbkdf2.iterateSha256AArch64.pub iterate :=
  ct_of (τ := VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (fun _ _ hp => agree₀ hp)
    (by taint_decide)

/-- `iterateSha256AArch64` with the 832 bytes of scratch of the shared
contract (sized for the x86-64 AVX2 compression function), of which the code
uses 384. -/
def iterateWide : Contract isa :=
  { Proof.Pbkdf2.iterateSha256AArch64 with
    pre := fun s =>
      let key : Region := ⟨s.gpr .x0, 192⟩
      let u : Region := ⟨s.gpr .x1, 32⟩
      let t : Region := ⟨s.gpr .x3, 32⟩
      let scratch : Region := ⟨s.gpr .x4, 832⟩
      s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
      key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧
      t.Disjoint scratch }

/-- The regions `iterateSha256AArch64` lets the code write. -/
def narrowWr (s : State) : List Region := [⟨s.gpr .x3, 32⟩, ⟨s.gpr .x4, 384⟩]

theorem iterateWide_pre (s : State) (h : iterateWide.pre s) :
    Proof.Pbkdf2.iterateSha256AArch64.pre (s.withRegions s.rd (narrowWr s)) :=
  let ⟨h₁, _, h₃, h₄, h₅, h₆, h₇⟩ := h
  ⟨h₁, rfl, h₃, h₄.sub_right (Region.sub_of_ble rfl), h₅, h₆.sub_right (Region.sub_of_ble rfl),
    h₇.sub_right (Region.sub_of_ble rfl)⟩

/-- A state satisfying `iterateWide.pre`. -/
def wideSat : State := { sat with wr := [⟨0x3000, 32⟩, ⟨0x4000, 832⟩] }

theorem iterateWide_implies :
    iterateWide.Implies (Spec.Pbkdf2.iterateSha256Contract AArch64.abi) := by
  sig_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig, iterateWide,
    Proof.Pbkdf2.iterateSha256AArch64, AArch64.abi, AArch64.argRegs] [wideSat, sat] using wideSat

/-- The proof is written against `iterateSha256AArch64`, widened to the
shared contract's scratch. -/
theorem iterate_verified :
    Verified AArch64.target Impl.Pbkdf2.AArch64.iterate
      (Spec.Pbkdf2.iterateSha256Contract AArch64.abi) :=
  have hsat := iterateWide_implies.sat_left
  (Verified.widen (Verified.of_correct (fun _ hs => correct hs) iterate_ct
    (.refl (hsat.elim fun s hs => ⟨_, iterateWide_pre s hs⟩)))
    narrowWr iterateWide_pre
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat).of_implies iterateWide_implies

end VG.Proof.Pbkdf2.AArch64
