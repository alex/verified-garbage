import VerifiedGarbage.Proof.Pbkdf2.Hmac
import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Hmac.X86.Finalize
import VerifiedGarbage.Impl.Pbkdf2.X86

/-!
# PBKDF2-HMAC-SHA-256's iteration on x86 (32-bit): the parts of a step

Untrusted: everything here is checked by Lean. The same structure as the
ARMv7 proof (`VG.Proof.Pbkdf2.Arm`), with the same target-independent memory
lemmas (`VG.Proof.Pbkdf2.Memory`). Each step is two calls
of `vg_sha256_compress`, used as a black box through its proof
(`compressAt_ok`, from the streaming SHA-256 proof), each using the 20 bytes
below `esp`. The hash value being compressed is `t`, and `T` is kept in
`scratch[160..192)`.
-/

namespace VG.Proof.Pbkdf2

open Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open Spec.Sha256 (Repr bytesAt)

open VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for
`vg_pbkdf2_hmac_sha256_iterate(key: *const [u8; 192], u: *const [u8; 32], n: u32, t: *mut [u8; 32], scratch: *mut [u64; 32])`,
whose arguments are on the stack (cdecl): if, for a 64-byte key `K₀`, the
streaming state at `key` represents `K₀ ⊕ ipad` and the one at `key + 96`
represents `K₀ ⊕ opad`, runs `n` steps `U ← HMAC-SHA-256 (K₀, U)`,
`T ← T ⊕ U` from the `U` at `u` and the `T` at `t`, leaving the final `T` at
`t`.

The code may read the arguments (20 bytes above the return address), `key`
(192 bytes) and `u` (32 bytes), and read and write `t` (32 bytes) and
`scratch` (256 bytes, whose contents on exit are unspecified). The written
regions may not overlap each other, the read ones or the return address;
none of the buffers may overlap the 20 bytes of stack below the return
address (where the code calls the compression function); and nothing may
wrap around the end of the (32-bit) address space. `esp`, the pointers and
`n` are public; the key, `U` and `T` are secret. -/
def iterateSha256X86 : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 192⟩
    let u : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let t : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 256⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [key, u, args] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    args.Disjoint t ∧ args.Disjoint scratch ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 256 ≤ 2 ^ 32 ∧
    20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ k0, k0.length = 64 →
    Repr s.mem ((arg s 0).setWidth 64) (xorPad k0 ipad) →
    Repr s.mem ((arg s 0).setWidth 64 + 96) (xorPad k0 opad) →
    bytesAt s'.mem ((arg s 3).setWidth 64) 32 =
      Spec.Pbkdf2.iterate (hmacBlockKey sha256 k0) (arg s 2).toNat
        (bytesAt s.mem ((arg s 1).setWidth 64) 32) (bytesAt s.mem ((arg s 3).setWidth 64) 32)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Pbkdf2

namespace VG.Proof.Pbkdf2.X86

open VG VG.X86 VG.Impl.Pbkdf2.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (compressAt saved)
open VG.Impl.Hmac.X86 (bswapWord copyWord)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi ea_at sub_offset
  addr_toNat compressAt_ok stk_eq)
open VG.Proof.Hmac.X86 (copyWords_ok bswapWords_ok)
open VG.Proof.Hmac.X86.Finalize (beWords_stateAt)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_sep bytesAt_add extractLsb'_read)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append writeBytes_nil write_eq_writeBytes)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base sep_after xorBytes_length add_ofNat
  stateAt_copy)
open VG.Spec.Sha256 (bytesAt stateAt blockAt compress HashValue wordBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev key : BitVec 32 := arg s₀ 0
abbrev uP : BitVec 32 := arg s₀ 1
/-- The number of steps. -/
abbrev nn : Nat := (arg s₀ 2).toNat
abbrev tP : BitVec 32 := arg s₀ 3
abbrev scr : BitVec 32 := arg s₀ 4
abbrev kA : Addr := (key s₀).setWidth 64
abbrev uA : Addr := (uP s₀).setWidth 64
abbrev tA : Addr := (tP s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev keyR : Region := ⟨kA s₀, 192⟩
abbrev uR : Region := ⟨uA s₀, 32⟩
abbrev tR : Region := ⟨tA s₀, 32⟩
abbrev scR : Region := ⟨scA s₀, 256⟩
abbrev argR : Region := ⟨addr (esp₀ s₀) 4, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (esp₀ s₀) 20

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
  ret_t : (retR s₀).Disjoint (tR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_u : (stkR s₀).Disjoint (uR s₀)
  stk_t : (stkR s₀).Disjoint (tR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  key_fit : (key s₀).toNat + 192 ≤ 2 ^ 32
  u_fit : (uP s₀).toNat + 32 ≤ 2 ^ 32
  t_fit : (tP s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 256 ≤ 2 ^ 32
  sp_lo : 20 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Pbkdf2.iterateSha256X86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  have e := stk_eq h20
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    by show (below _ _).Disjoint _; rw [e]; exact h12, by show (below _ _).Disjoint _; rw [e]; exact h13,
    by show (below _ _).Disjoint _; rw [e]; exact h14, by show (below _ _).Disjoint _; rw [e]; exact h15,
    h16, h17, h18, h19, h20, h21⟩

/-! ## Regions -/

theorem toNat_ofNat_lt {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Two parts of the scratch space at offsets `a` and `b` do not overlap. -/
theorem scr_disj (s₀ : State) {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 256) (hb : b + n ≤ 256) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

theorem scr_disj0 (s₀ : State) {a m n : Nat} (h : n ≤ a) (ha : a + m ≤ 256) :
    Region.Disjoint (sR s₀ a m) ⟨scA s₀, n⟩ := by
  have := scr_disj s₀ (a := a) (m := m) (b := 0) (n := n) (by omega) ha (by omega)
  simp only [sR] at this
  simpa using this

theorem scr_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) : Region.Sub (sR s₀ o n) (scR s₀) :=
  sub_offset h (by omega)

theorem cmp_sub (s₀ : State) : Region.Sub (cmpR s₀) (scR s₀) := Region.sub_prefix (by omega)

theorem ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

/-- `[x + d]`, as an address, for `x` a pointer to a region of `len ≥ d` bytes. -/
theorem addr_off {x : BitVec 32} {d len : Nat} (hx : x.toNat + len ≤ 2 ^ 32) (hd : d < len) :
    addr x d = x.setWidth 64 + BitVec.ofNat 64 d := addr_eq (by omega)

section
variable {s₀ : State} (hp : Pre s₀) {s : State}
include hp

theorem in_scr (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 256) :
    InRegions s.wr (scA s₀ + BitVec.ofNat 64 a) n :=
  ⟨scR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩

theorem in_t (hwr : s.wr = s₀.wr) {b n : Nat} (h : b + n ≤ 32) :
    InRegions s.wr (tA s₀ + BitVec.ofNat 64 b) n :=
  ⟨tR s₀, by simp [hwr, hp.wr], contains_offset (by omega) (by omega)⟩

theorem in_key (hrd : s.rd = s₀.rd) {a n : Nat} (h : a + n ≤ 192) :
    InRegions (s.rd ++ s.wr) (kA s₀ + BitVec.ofNat 64 a) n :=
  ⟨keyR s₀, by simp [hrd, hp.rd], contains_offset h (by omega)⟩

theorem in_u (hrd : s.rd = s₀.rd) {a n : Nat} (h : a + n ≤ 32) :
    InRegions (s.rd ++ s.wr) (uA s₀ + BitVec.ofNat 64 a) n :=
  ⟨uR s₀, by simp [hrd, hp.rd], contains_offset h (by omega)⟩

end

theorem InRegions.right {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem key_disj {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [tR s₀, scR s₀, stkR s₀], Region.Disjoint (keyR s₀) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.k_t
  · exact hp.k_s
  · exact hp.stk_k.symm

/-! ## The registers and memory during a step -/

/-- The registers the body keeps. -/
def kept : List Reg := [.ebx, .ebp, .esi, .edi, .esp]

/-- From `s` to `s'`, only `t` (the hash value being compressed), the
compression's part of the scratch space and the stack below `esp` changed. -/
structure Keep (s₀ s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  gpr : ∀ r ∈ kept, s'.gpr r = s.gpr r
  frame : Frame [tR s₀, cmpR s₀, stkR s₀] s.mem s'.mem

theorem Keep.trans {s₀ s₁ s₂ s₃ : State} (h₁ : Keep s₀ s₁ s₂) (h₂ : Keep s₀ s₂ s₃) : Keep s₀ s₁ s₃ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr),
    h₁.frame.trans h₂.frame⟩

/-- The registers and memory at the start of each step. -/
structure Regs (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = esp₀ s₀
  ebx : s.gpr .ebx = tP s₀
  ebp : s.gpr .ebp = scr s₀
  esi : s.gpr .esi = key s₀
  frame : Frame [tR s₀, scR s₀, stkR s₀] s₀.mem s.mem

theorem Regs.keep {s₀ s s' : State} (h : Regs s₀ s) (hk : Keep s₀ s s') : Regs s₀ s' where
  rd := hk.rd.trans h.rd
  wr := hk.wr.trans h.wr
  esp := (hk.gpr _ (by simp [kept])).trans h.esp
  ebx := (hk.gpr _ (by simp [kept])).trans h.ebx
  ebp := (hk.gpr _ (by simp [kept])).trans h.ebp
  esi := (hk.gpr _ (by simp [kept])).trans h.esi
  frame := h.frame.trans (hk.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨tR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, cmp_sub s₀⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

theorem Regs.write {s₀ s s' : State} (h : Regs s₀ s) (hg : ∀ r ∈ [Reg.ebx, .ebp, .esi, .esp], s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {R : Region} (hR : R ∈ [tR s₀, scR s₀])
    (hm : Frame [R] s.mem s'.mem) : Regs s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  esp := (hg _ (by simp)).trans h.esp
  ebx := (hg _ (by simp)).trans h.ebx
  ebp := (hg _ (by simp)).trans h.ebp
  esi := (hg _ (by simp)).trans h.esi
  frame := h.frame.trans (hm.mono (by simp at hR ⊢; rcases hR with rfl | rfl <;> simp))

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
  refine copyWords_ok (src := .esi) (dst := .ebx) (by decide) (by decide) (o₁ := o) (o₂ := 0) 8
    rest s Q h.esi h.ebx (by omega) (by omega)
    (fun j hj => by rw [addr_off (len := 192) hp.key_fit (by omega)]; exact in_key hp h.rd (by omega))
    (fun j hj => by rw [addr_off (len := 32) hp.t_fit (by omega)]; exact in_t hp h.wr (by omega))
    ?_ fun s' g' rd' wr' m' => k s' ⟨rd', wr', fun r hr => g' r (by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩ ?_
  · exact Region.Disjoint.sep hp.k_t (contains_offset (by omega) (by omega))
      (contains_offset (by omega) (by omega))
  · rw [m']
    refine writeBytes_frame _ _ _ (R := tR s₀) ?_ |>.mono (by simp)
    rw [bytesAt_length, ofNat_zero]; exact contains_base (Nat.le_refl _)
  · rw [m', ofNat_zero, show 4 * 8 = 32 from rfl, stateAt_copy]
    apply Proof.Sha256.Stream.stateAt_congr
    intro i hi
    rw [add_ofNat]
    exact h.key_bytes hp (by omega)

/-! ## A call of `vg_sha256_compress` on the block -/

/-- `eax` at the block. -/
theorem atBlock_ok {s₀ : State} {s : State} (h : Regs s₀ s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' → s'.mem = s.mem → s'.gpr .eax = scr s₀ + BitVec.ofNat 32 192 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (atBlock ++ rest)) s Q := by
  have ne : ∀ r ∈ kept, r ≠ .eax := by
    intro r hr
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => k s₂ ⟨by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr],
    fun r hr => by rw [u₂.other r (ne r hr), u₁.other r (ne r hr)], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.gpr, u₁.gpr, h.ebp]; rfl)

/-- Compressing the block into the hash value in `t`. -/
theorem cmp_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s)
    (hax : s.gpr .eax = scr s₀ + BitVec.ofNat 32 192) {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' →
      stateAt s'.mem (tA s₀) = compress (stateAt s.mem (tA s₀)) (blockAt s.mem (blkA s₀)) → Q s') :
    WP isa (compressAt .ebx .ebp) s Q := by
  have := hp.scr_fit; have := hp.t_fit
  have ea : (scr s₀ + BitVec.ofNat 32 192).setWidth 64 = blkA s₀ := addr_off (len := 256) hp.scr_fit (by omega)
  have et : (scr s₀ + BitVec.ofNat 32 192).toNat = (scr s₀).toNat + 192 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsc : scR s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  have htr : tR s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  have b64 : Region.Sub ⟨(scr s₀ + BitVec.ofNat 32 192).setWidth 64, 64⟩ (sR s₀ 192 64) := by
    rw [ea]; exact fun _ h => h
  refine compressAt_ok (st := tP s₀) (scr := scr s₀) (blk := scr s₀ + BitVec.ofNat 32 192) (E := esp₀ s₀)
    (by decide) (by decide) (by decide) (by decide) h.esp h.ebx h.ebp hax hp.sp_lo (by omega)
    (by rw [et]; omega) (by omega) (hp.t_s.sub_right (cmp_sub s₀))
    ((hp.t_s.sub_right (scr_sub s₀ (o := 192) (n := 64) (by omega))).symm.sub_left b64)
    ((scr_disj0 s₀ (a := 192) (m := 64) (by omega) (by omega)).sub_left b64)
    hp.stk_t (hp.stk_s.sub_right (cmp_sub s₀)) (hp.stk_s.sub_right fun a ha => scr_sub s₀ (o := 192) (n := 64) (by omega) a (b64 a ha)) ?_ ?_
    fun s' hrd hwr hcs hf hst => k s' ⟨hrd, hwr, fun r hr => hcs r (by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved]), hf⟩ (by rw [hst, ea])
  · rw [ea]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨scR s₀, List.mem_append_right _ hsc, 192, rfl, by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨tR s₀, htr, 0, by simp, by simp⟩
    · exact ⟨scR s₀, hsc, 0, by simp, by simp⟩

/-! ## The digest into the block -/

/-- The digest of the hash value in `t` into the block. -/
theorem digest_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Regs s₀ s' → (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → Frame [sR s₀ 192 32] s.mem s'.mem →
      s'.mem = writeBytes s.mem (blkA s₀) (Pbkdf2.digest (stateAt s.mem (tA s₀))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.X86.digest ++ rest)) s Q := by
  have := hp.scr_fit; have := hp.t_fit
  unfold Impl.Pbkdf2.X86.digest
  refine bswapWords_ok (src := .ebx) (dst := .ebp) (by decide) (by decide) (o₁ := 0) (o₂ := 192) 8 rest s Q
    h.ebx h.ebp (by omega) (by omega)
    (fun j hj => by rw [addr_off (len := 32) hp.t_fit (by omega)]; exact InRegions.right (in_t hp h.wr (by omega)))
    (fun j hj => by rw [addr_off (len := 256) hp.scr_fit (by omega)]; exact in_scr hp h.wr (by omega))
    (Region.Disjoint.sep (hp.t_s.sub_right (scr_sub s₀ (o := 192) (n := 32) (by omega)))
      (by rw [ofNat_zero]; exact contains_base (Nat.le_refl _)) (contains_base (Nat.le_refl _)))
    fun s' g' rd' wr' m' => ?_
  rw [beWords_stateAt _ hp.t_fit] at m'
  change s'.mem = writeBytes s.mem (blkA s₀) (Pbkdf2.digest (stateAt s.mem (tA s₀))) at m'
  have hf : Frame [sR s₀ 192 32] s.mem s'.mem := by
    rw [m']; exact writeBytes_frame _ _ _ (contains_base (by rw [Pbkdf2.digest_length]))
  exact k s' (h.write (fun r hr => g' r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd' wr' (R := scR s₀) (by simp) (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)) g' hf m'

/-! ## `T ← T ⊕ U` -/

/-- `xor d, [m]` -/
theorem wp_xorm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine VG.Proof.Sha256.X86.Stream.WP.cons
    (s' := (arithFlags s (s.gpr d ^^^ s.mem.readW a 32) false false).setReg d (s.gpr d ^^^ s.mem.readW a 32))
    ?_ (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load32, ha, hin]

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

theorem add_off (a : Addr) (o j : Nat) :
    a + BitVec.ofNat 64 (o + j) = a + BitVec.ofNat 64 o + BitVec.ofNat 64 j := (add_ofNat a o j).symm

/-- `T ← T ⊕ U` for the first `n` words of `T` at `p + 160` and `U` at `p + 192`. -/
theorem xor_ok {p : BitVec 32} (fp : p.toNat + 224 ≤ 2 ^ 32) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ebp = p →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 8, InRegions s.wr (p.setWidth 64 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (p.setWidth 64 + BitVec.ofNat 64 160)
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (p.setWidth 64 + BitVec.ofNat 64 160) (4 * n))
          (bytesAt s.mem (p.setWidth 64 + BitVec.ofNat 64 192) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hb hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hb hin hout fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    have hw := hout n (by omega)
    have eb : s₁.gpr .ebp = p := by rw [g₁ _ (by decide), hb]
    have eT : addr p (160 + 4 * n) = p.setWidth 64 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n) := by
      rw [addr_eq (by omega), add_off]
    have eU : addr p (192 + 4 * n) = p.setWidth 64 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n) := by
      rw [addr_eq (by omega), add_off]
    refine wp_movm (a := p.setWidth 64 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, eb, eT]) (by rw [rd₁, wr₁]; exact InRegions.right hw) fun s₂ u₂ => ?_
    refine wp_xorm (a := p.setWidth 64 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, u₂.other _ (by decide), eb, eU])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hin n (by omega)) fun s₃ u₃ => ?_
    refine wp_store (a := p.setWidth 64 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), eb, eT])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₄ g₄ => k s₄ (fun r hr => by
          rw [g₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [g₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem (p.setWidth 64 + BitVec.ofNat 64 160) (4 * n))
        (bytesAt s.mem (p.setWidth 64 + BitVec.ofNat 64 192) (4 * n))).length = 4 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have v : s₃.gpr .ecx =
        s₁.mem.readW (p.setWidth 64 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n)) 32 ^^^
        s₁.mem.readW (p.setWidth 64 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n)) 32 := by
      rw [u₃.gpr, u₂.gpr, u₂.mem]
    have hpT := addr_toNat p
    rw [g₄.mem, u₃.mem, u₂.mem, v, writeW_xor32, m₁,
      bytesAt_writeBytes_sep (p := p.setWidth 64 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := p.setWidth 64 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n))]
    · have e := writeBytes_append s.mem (p.setWidth 64 + BitVec.ofNat 64 160) _
        (Spec.Pbkdf2.xorBytes
          (bytesAt s.mem (p.setWidth 64 + BitVec.ofNat 64 160 + BitVec.ofNat 64 (4 * n)) 4)
          (bytesAt s.mem (p.setWidth 64 + BitVec.ofNat 64 192 + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro x h₁ h₂
      rw [hl] at h₂
      have := toNat_ofNat_lt (k := 4 * n) (by omega)
      bv_omega
    · omega
    · intro x h₁ h₂
      rw [hl] at h₂
      exact sep_after h₁ h₂ (by omega)
    · omega

end VG.Proof.Pbkdf2.X86
