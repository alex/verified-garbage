import VerifiedGarbage.Proof.Pbkdf2.MdStep
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Compress
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Copy
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Impl.Pbkdf2.AArch64

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on AArch64

The same proof as on x86-64 (`Proof/Pbkdf2/X86_64/Iterate.lean`): the
iteration (`Impl/Pbkdf2/AArch64.lean`) is correct for any hash function the
generic streaming proofs describe (`Md`), whose code stores the length field
and writes the digest as `Shape` says, with any correct compression function
(`CompOk`), used as a black box through its proof; `Md.hmac_step` says that
its two compressions per step compute HMAC.

The first instruction zero-extends `n`; the rest (`main`) runs from that
state, `zext s₀`, and the lemmas describe it in terms of the entry state
`s₀`.
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64
open VG.Impl.Pbkdf2.AArch64 (Params raO hvO blkO loadKey padFrom xorW compressBlock body prologue epilogue
  main iterate)
open VG.Impl.MdStream.AArch64 (mov save restore saved)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.AArch64 (Dims Upd Mupd wp_mov wp_movz wp_addImm wp_subImm wp_str wp_str32 wp_ldr
  wp_ldr32 Saved saveMem saveMem_saved saveMem_frame saved_offset save_ok restore_ok preserved_of untouched
  ofNat_pred ofNat_beq_zero add_ofNat setWidth32 eval_zero eval_nonzero)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame writeBytes_append)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep bytesAt_writeBytes_self
  writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self')
open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

/-! ## The contract -/

/-- The contract the proof is written against: `VG.Spec.Pbkdf2.iterateContract`
of the streaming hash function `S` with `W` words of scratch space, on
AArch64. The function uses no stack. -/
def iterK (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 2 * S.stateBytes⟩
    let u : Region := ⟨s.gpr .x1, S.digestBytes⟩
    let t : Region := ⟨s.gpr .x3, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    (s.gpr .x0).toNat + 2 * S.stateBytes ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem (s.gpr .x0) (xorPad k0 ipad) →
    S.Repr s.mem (s.gpr .x0 + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) ((s.gpr .x2).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .x1) S.digestBytes) (bytesAt s.mem (s.gpr .x3) S.digestBytes)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- What `P.len` and `P.out` must do: `P.len` stores the length field for the
byte count in `x22` at `x19 + N + B - L`, writing only `x9` and `x12`, and
`P.out` writes the digest of the hash value at `x19` to `x21`, writing only
`x9`. -/
structure Shape {P : Params} (H : Md P.B P.N P.L) : Prop where
  lenKeepsV : P.len.all keepsV = true
  outKeepsV : P.out.all keepsV = true
  len : ∀ s : State, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) (H.lenOf (s.gpr .x22))
  out : ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .x19) P.N → InRegions s.wr (s.gpr .x21) P.N →
    Region.Disjoint ⟨s.gpr .x19, P.N⟩ ⟨s.gpr .x21, P.N⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .x21) (H.digest (H.stateAt s.mem (s.gpr .x19)))

/-- The streaming proofs' `Shape`. -/
theorem Shape.ofMd {P : VG.Impl.MdStream.AArch64.Params} {H : Md P.B P.N P.L} (h : MdStream.AArch64.Shape H) :
    Shape (P := Impl.Pbkdf2.AArch64.ofMd P) H :=
  ⟨h.lenKeepsV, h.outKeepsV, h.len, h.out⟩

/-- The sizes the proof supports, checked for each hash function by `decide`:
words of 4 bytes, a digest of at most the hash value, room for the padding
in the block after the digest and after the hash value, and room in the
scratch space for the compression function's, our caller's registers, our
return address, the hash value and the block. -/
structure Sizes (P : Params) (D W : Nat) : Prop where
  dims : Dims P.md
  B : P.B = 64 ∨ P.B = 128
  N4 : P.N % 4 = 0
  D4 : D % 4 = 0
  L4 : P.L % 4 = 0
  D0 : 0 < D
  DN : D ≤ P.N
  NL : P.N + P.L ≤ P.B
  pad : D + 4 ≤ P.B - P.L
  fits : P.so + 56 + P.N + P.B ≤ 8 * W
  W : W ≤ 1024

/-! ## The precondition -/

section
variable (P : Params) (D W : Nat) (s₀ : State)

abbrev key : Addr := s₀.gpr .x0
abbrev up : Addr := s₀.gpr .x1
abbrev tp : Addr := s₀.gpr .x3
abbrev scr : Addr := s₀.gpr .x4
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .x2).setWidth 32).toNat
abbrev keyR : Region := ⟨key s₀, 2 * (P.N + P.B)⟩
abbrev uR : Region := ⟨up s₀, D⟩
abbrev tR : Region := ⟨tp s₀, D⟩
abbrev scR : Region := ⟨scr s₀, 8 * W⟩
/-- The hash value being compressed, and the block. -/
abbrev hv : Addr := scr s₀ + BitVec.ofNat 64 (P.so + 56)
abbrev blk : Addr := scr s₀ + BitVec.ofNat 64 (P.so + 56 + P.N)

end

structure Pre (P : Params) (D W : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR P s₀, uR D s₀]
  wr : s₀.wr = [tR D s₀, scR W s₀]
  k_t : (keyR P s₀).Disjoint (tR D s₀)
  k_s : (keyR P s₀).Disjoint (scR W s₀)
  u_t : (uR D s₀).Disjoint (tR D s₀)
  u_s : (uR D s₀).Disjoint (scR W s₀)
  t_s : (tR D s₀).Disjoint (scR W s₀)

theorem pre_of {P : Params} {D W : Nat} {S : StreamingHash} (hS : S.stateBytes = P.N + P.B)
    (hD : S.digestBytes = D) {s₀ : State} (h : (iterK S W).pre s₀) : Pre P D W s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -, -⟩ := h
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-! ## The parts of the scratch space -/

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W)
include hz

theorem so_le : P.so ≤ 256 := hz.dims.so.2
theorem so8 : P.so % 8 = 0 ∧ P.so ≤ 256 := hz.dims.so
theorem saved_off {q : Reg × Nat} (hq : q ∈ saved P.md) : P.so ≤ q.2 ∧ q.2 + 8 ≤ P.so + 48 :=
  saved_offset hz.dims hq
theorem N_le : P.N ≤ 64 := hz.dims.N.2
theorem B_le : P.B ≤ 128 := by rcases hz.B with h | h <;> omega
theorem B_ge : 64 ≤ P.B := by rcases hz.B with h | h <;> omega

omit hz in
theorem scr_sub (s₀ : State) {a n : Nat} (h : a + n ≤ 8 * W) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 a, n⟩ (scR W s₀) :=
  Offset.sub_base _ h

end

theorem md_so (P : Params) : P.md.so = P.so := rfl

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## The registers during a step -/

/-- The registers `main` keeps between its pieces: ours but the count, and
the callee-saved ones it never writes. -/
abbrev kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem ne9 : ∀ r ∈ kept, r ≠ .x9 := by decide
theorem ne10 : ∀ r ∈ kept, r ≠ .x10 := by decide
theorem ne12 : ∀ r ∈ kept, r ≠ .x12 := by decide
theorem ne1 : ∀ r ∈ kept, r ≠ .x1 := by decide
theorem ne24 : ∀ r ∈ kept, r ≠ .x24 := by decide
theorem kept_preserved : ∀ r ∈ kept, r ∈ preserved ∧ r ≠ .x30 := by decide
theorem untouched_kept : ∀ r ∈ untouched, r ∈ kept := by decide
theorem untouched_ne22 : ∀ r ∈ untouched, r ≠ .x22 := by decide
theorem untouched_ne30 : ∀ r ∈ untouched, r ≠ .x30 := by decide
theorem untouched_not_saved (P : VG.Impl.MdStream.AArch64.Params) : ∀ r ∈ untouched, r ∉ (saved P).map Prod.fst := by
  simp only [saved, List.map_cons, List.map_nil]; decide

/-- What holds between the pieces of a step: the regions, our registers, the
callee-saved registers we never write, the stack pointer, and memory outside
the scratch space and `T` as on entry. -/
structure Regs (P : Params) (D W : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = hv P s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = blk P s₀
  x22 : s.gpr .x22 = key s₀
  x23 : s.gpr .x23 = tp s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  frame : Frame [tR D s₀, scR W s₀] s₀.mem s.mem

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀)

/-- `Regs` after code that keeps our registers and writes only memory in the
regions it allows. -/
theorem Regs.write {s s' : State} (h : Regs P D W s₀ s) (hg : ∀ r ∈ kept, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hm : Frame [tR D s₀, scR W s₀] s.mem s'.mem) : Regs P D W s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := (hg _ (by decide)).trans h.x19
  x20 := (hg _ (by decide)).trans h.x20
  x21 := (hg _ (by decide)).trans h.x21
  x22 := (hg _ (by decide)).trans h.x22
  x23 := (hg _ (by decide)).trans h.x23
  cs := fun r hr => (hg r (untouched_kept r hr)).trans (h.cs r hr)
  sp := hsp.trans h.sp
  frame := h.frame.trans hm

omit hp in
/-- A part of the scratch space, as a frame of `Regs`. -/
theorem frame_scr {m m' : Mem} {a n : Nat} (h : a + n ≤ 8 * W)
    (hf : Frame [⟨scr s₀ + BitVec.ofNat 64 a, n⟩] m m') : Frame [tR D s₀, scR W s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR W s₀, by simp, scr_sub s₀ h⟩

include hz hp

theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * W) :
    InRegions s.wr (scr s₀ + BitVec.ofNat 64 a) n :=
  ⟨scR W s₀, by simp [hwr, hp.wr], Offset.contains_base _ h (by have := hz.W; omega)⟩

theorem in_blk {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ P.B) :
    InRegions s.wr (blk P s₀ + BitVec.ofNat 64 a) n := by
  have := hz.fits
  rw [add_ofNat]; exact in_scr hz hp hwr (by omega)

theorem in_scr' {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * W) :
    InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofNat 64 a) n := by
  obtain ⟨r, hr, hc⟩ := in_scr hz hp hwr h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The hash value at `key + o` into the scratch space. -/
theorem load_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {s : State} (h : Regs P D W s₀ s) {o : Nat}
    (ho : o + P.N ≤ 2 * (P.N + P.B)) (ho4 : o % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨hv P s₀, P.N⟩] s.mem s'.mem →
      H.stateAt s'.mem (hv P s₀) = H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loadKey P o ++ rest)) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.dims.N; have := hz.N4; have := hz.fits
  have hn : 4 * (P.N / 4) = P.N := by omega
  unfold loadKey
  refine copy32_ok (by decide) (by decide) o 0 (P.N / 4) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ rest s Q
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s' g' rd' wr' sp' m' => ?_
  · rw [h.x22, h.rd, hp.rd, add_ofNat]
    exact ⟨keyR P s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.x19, h.wr, hp.wr, add_ofNat, add_ofNat]
    exact ⟨scR W s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.x22, h.x19, hn, add_ofNat, Nat.add_zero]
    exact hp.k_s.sep (Offset.contains_base _ (by omega) (by omega))
      (Offset.contains_base _ (by omega) (by omega))
  rw [h.x19, h.x22, hn, add_ofNat, Nat.add_zero] at m'
  refine k s' g' rd' wr' sp' (by rw [m']; exact writeBytes_frame _ _ _ (by
    rw [bytesAt_length]; exact Region.contains_self _ _)) ?_
  refine hR _ _ _ _ fun i hi => ?_
  rw [m', writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi, add_ofNat]
  exact h.frame.bytes (R := keyR P s₀) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.k_t
    · exact hp.k_s) (by show 2 * (P.N + P.B) ≤ 2 ^ 64; omega) (by show o + i < 2 * (P.N + P.B); omega)

/-- What the call of the compression function needs, with the block's address in `x1`. -/
theorem callOk_of {s : State} (h : Regs P D W s₀ s) (h1 : s.gpr .x1 = blk P s₀) :
    CallOk s P.N P.B P.so (hv P s₀) (scr s₀) (blk P s₀) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits
  have hsc : scR W s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  refine ⟨h.x19, h.x20, h1, Offset.disjoint_base _ (by omega) (by omega),
    Offset.disjoint _ (.inr (by omega)) (by omega) (by omega), Offset.disjoint_base _ (by omega) (by omega),
    ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ⟨scR W s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩
  · refine Covers.of_sub fun r hr => ⟨scR W s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩

/-- A call of the compression function on the block. -/
theorem cmp_ok {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : CompOk H P.so code) {s : State}
    (h : Regs P D W s₀ s) {Q : State → Prop}
    (k : ∀ s', Regs P D W s₀ s' → s'.gpr .x24 = s.gpr .x24 →
      Frame [⟨hv P s₀, P.N⟩, ⟨scr s₀, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem (hv P s₀) = H.compress (H.stateAt s.mem (hv P s₀)) (H.blockAt s.mem (blk P s₀)) →
      Q s') :
    WP isa (compressBlock name code) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits
  unfold compressBlock
  refine WP.seq (wp_mov fun s₁ u₁ => WP.block_nil ?_)
  have h₁ := h.write (fun r hr => u₁.other r (ne1 r hr)) u₁.rd u₁.wr u₁.sp (by rw [u₁.mem]; exact Frame.refl _ _)
  refine compressAt_ok hf (callOk_of hz hp h₁ (by rw [u₁.gpr, h.x21])) fun s' hrd hwr hcs hsp hfr hst => ?_
  have cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r := fun r hr h30 => by
    rw [hcs r hr h30, u₁.other r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  rw [u₁.mem] at hfr hst
  refine k s' (h.write (fun r hr => cs r (kept_preserved r hr).1 (kept_preserved r hr).2)
    (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp) (hfr.sub fun r hr => ?_))
    (cs _ (by decide) (by decide)) hfr hst
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨scR W s₀, by simp, scr_sub s₀ (by omega)⟩
  · exact ⟨scR W s₀, by simp, Region.sub_prefix (by omega)⟩

end

/-! ## Words of the block and of `T` -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem xor_setWidth (a b : BitVec 32) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 32 = a ^^^ b := by
  rw [BitVec.setWidth_xor, setWidth32, setWidth32]

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 4) (bytesAt m' a 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    VG.WriteBytes.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

/-- `T ← T ⊕ U` for the first `n` 32-bit words of `T` at `tp` and `U` at `bp`. -/
theorem xor_ok {tp bp : Addr} {D : Nat} (hd : Region.Disjoint ⟨tp, D⟩ ⟨bp, D⟩) (hD : D ≤ 4096) :
    ∀ n, 4 * n ≤ D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .x21 = bp → s.gpr .x23 = tp →
    (∀ k < n, InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (tp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem tp
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hbp h23 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hbp h23 (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    have hw := hout n (by omega)
    refine wp_ldr32 (a := bp + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ (by decide) (by decide), hbp]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_ldr32 (a := tp + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h23])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩)
      fun s₃ u₃ => ?_
    refine wp_eor fun s₄ u₄ => ?_
    refine wp_str32 (a := tp + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide), h23])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₅ g₅ => k s₅ (fun r h9 h10 => by
          rw [g₅.gpr, u₄.other r h9, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))).length = 4 * n := by
      rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    rw [g₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₃.mem, u₂.gpr, u₂.mem, xor_setWidth,
      writeW_xor32, m₁,
      bytesAt_writeBytes_sep (p := tp + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := bp + BitVec.ofNat 64 (4 * n))]
    · have e := writeBytes_append s.mem tp _ (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp + BitVec.ofNat 64 (4 * n)) 4)
        (bytesAt s.mem (bp + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro x h₁ h₂
      rw [hl] at h₂
      exact hd x (by simp only [Region.Contains]; omega) (Memory.off_contains h₁ (by omega) (by omega))
    · omega
    · intro x h₁ h₂
      rw [hl] at h₂
      exact Memory.sep_after h₁ h₂ (by omega)
    · omega

/-- Stores of zero (the low 32 bits of `x9`) at `x21 + a + 4 + 4 k`, for `k < n`. -/
theorem zeros_ok {a : Nat} {p : Addr} (ha4 : a % 4 = 0) : ∀ n, a + 4 + 4 * n ≤ 4096 * 4 →
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .x21 = p → (s.gpr .x9).setWidth 32 = 0 →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 (a + 4)) (List.replicate (4 * n) 0) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.str .w .x9 .x21 (a + 4 + 4 * k)) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro ha rest s Q hbp hax hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hbp hax (fun j hj => hout j (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_str32 (a := p + BitVec.ofNat 64 (a + 4 + 4 * n)) ⟨by omega, by omega⟩ (by rw [g₁, hbp])
      (by rw [wr₁]; exact hout n (by omega)) fun s₂ g₂ =>
        k s₂ (by rw [g₂.gpr, g₁]) (by rw [g₂.rd, rd₁]) (by rw [g₂.wr, wr₁]) (by rw [g₂.sp, sp₁]) ?_
    rw [g₂.mem, g₁, hax, m₁, Memory.writeW_bytes _ _ (0 : BitVec 32) [0, 0, 0, 0] (by decide),
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate, add_ofNat]) (by simp; omega), Nat.mul_succ,
      ← List.replicate_append_replicate]
    rfl

/-- `padFrom a b` writes `0x80` and zeros from byte `a` to byte `b` of the block at `x21`. -/
theorem padFrom_ok {a b : Nat} (hab : a + 4 ≤ b) (h4 : (b - a) % 4 = 0) (ha4 : a % 4 = 0) (hb : b ≤ 4096 * 4)
    {s : State} {p : Addr}
    (hbp : s.gpr .x21 = p) (hout : ∀ k < (b - a) / 4, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 * k)) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 a) ([0x80] ++ List.replicate (b - a - 1) 0) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (padFrom a b ++ rest)) s Q := by
  unfold padFrom
  simp only [List.cons_append, List.nil_append]
  refine wp_movz fun s₁ u₁ => ?_
  refine wp_str32 (a := p + BitVec.ofNat 64 a) ⟨ha4, by omega⟩ (by rw [u₁.other _ (by decide), hbp])
    (by rw [u₁.wr]; simpa using hout 0 (by omega)) fun s₂ g₂ => ?_
  refine wp_movz fun s₃ u₃ => ?_
  refine zeros_ok (a := a) ha4 ((b - a) / 4 - 1) (by omega) rest s₃ Q
    (by rw [u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), hbp]) (by rw [u₃.gpr]; rfl)
    (fun j hj => by
      rw [u₃.wr, g₂.wr, u₁.wr, show a + 4 + 4 * j = a + 4 * (j + 1) by omega]; exact hout (j + 1) (by omega))
    fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => k s₄ (fun r hr => by
      rw [g₄, u₃.other r hr, g₂.gpr, u₁.other r hr]) (by rw [rd₄, u₃.rd, g₂.rd, u₁.rd])
      (by rw [wr₄, u₃.wr, g₂.wr, u₁.wr]) (by rw [sp₄, u₃.sp, g₂.sp, u₁.sp]) ?_
  rw [m₄, u₃.mem, g₂.mem, u₁.gpr, u₁.mem,
    show ((BitVec.setWidth 64 (0x80 : BitVec 16)).setWidth 32 : BitVec 32) = 0x80 from rfl,
    Memory.writeW_bytes _ _ (0x80 : BitVec 32) [0x80, 0, 0, 0] (by decide),
    Memory.writeBytes_append' _ _ _ (by rw [List.length_cons, List.length_cons, List.length_cons,
      List.length_singleton, add_ofNat]) (by simp; omega),
    show b - a - 1 = 3 + 4 * ((b - a) / 4 - 1) by omega, ← List.replicate_append_replicate]
  rfl

/-! ## The digest into the block -/

theorem blk_sep (P : Params) (s₀ : State) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ 2 ^ 32)
    (hb : b + k ≤ 2 ^ 32) (hN : P.so + 56 + P.N ≤ 2 ^ 32) :
    Mem.Sep (blk P s₀ + BitVec.ofNat 64 a) n (blk P s₀ + BitVec.ofNat 64 b) k := by
  rw [add_ofNat, add_ofNat]
  exact Offset.sep _ (by omega) (by omega) (by omega)

theorem blk0 (P : Params) (s₀ : State) : blk P s₀ + BitVec.ofNat 64 0 = blk P s₀ := add0 _

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀)
include hz hp

/-- The digest of the hash value into the block's first `D` bytes, the padding after them as it was. -/
theorem digest_ok {H : Md P.B P.N P.L} (hs : Shape H) {s : State} (h : Regs P D W s₀ s)
    (hpad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨blk P s₀, P.N⟩] s.mem s'.mem →
      bytesAt s'.mem (blk P s₀) D = (H.digest (H.stateAt s.mem (hv P s₀))).take D →
      bytesAt s'.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.AArch64.digest P D ++ rest)) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.NL
  have := hz.D4; have := hz.N4; have := hz.pad
  unfold Impl.Pbkdf2.AArch64.digest
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (hs.out s ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
  · rw [h.x19]; exact in_scr' hz hp h.wr (a := P.so + 56) (n := P.N) (by omega)
  · rw [h.x21]; exact in_scr hz hp h.wr (by omega)
  · rw [h.x19, h.x21]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  rw [h.x21, h.x19] at m₁
  have hdl := H.digest_length (H.stateAt s.mem (hv P s₀))
  have f₁ : Frame [⟨blk P s₀, P.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
  have b₁ : bytesAt s₁.mem (blk P s₀) D = (H.digest (H.stateAt s.mem (hv P s₀))).take D := by
    rw [bytesAt_take _ _ (Nat.le_of_lt_succ (Nat.lt_succ_of_le hz.DN)), m₁, bytesAt_writeBytes_self' hdl (by omega)]
  have r₁ : bytesAt s₁.mem (blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) =
      bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) := by
    rw [m₁]
    refine bytesAt_writeBytes_sep _ _ ?_ (by omega)
    have := blk_sep P s₀ (a := P.N) (n := P.B - P.N) (b := 0) (k := P.N) (.inr (by omega)) (by omega) (by omega)
      (by omega)
    rw [blk0] at this; rw [hdl]; exact this
  have hsplit : ∀ m : Mem, bytesAt m (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) =
      bytesAt m (blk P s₀ + BitVec.ofNat 64 D) (P.N - D) ++ bytesAt m (blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) := by
    intro m
    rw [show P.B - D = (P.N - D) + (P.B - P.N) by omega, bytesAt_add, add_ofNat (blk P s₀),
      show D + (P.N - D) = P.N by omega]
  have hY : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) = (H.tailPad D).drop (P.N - D) := by
    rw [← hpad, hsplit, List.drop_left' (bytesAt_length _ _ _)]
  by_cases hDN : D < P.N
  · simp only [hDN, ↓reduceIte]
    refine padFrom_ok (a := D) (b := P.N) (by omega) (by omega) (by omega) (by omega) (s := s₁) (p := blk P s₀)
      (by rw [g₁ _ (by decide), h.x21]) (fun j hj => in_blk hz hp (wr₁.trans h.wr) (by omega))
      fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => k s₂ (fun r hr => (g₂ r hr).trans (g₁ r hr)) (rd₂.trans rd₁) (wr₂.trans wr₁)
        (sp₂.trans sp₁) ?_ ?_ ?_
    · rw [m₂]
      refine f₁.trans (writeBytes_frame _ _ _ ?_)
      simp only [List.length_append, List.length_singleton, List.length_replicate]
      exact Offset.contains_base _ (by omega) (by omega)
    · rw [m₂, bytesAt_writeBytes_sep _ _ ?_ (by omega), b₁]
      have := blk_sep P s₀ (a := 0) (n := D) (b := D) (k := P.N - D) (.inl (by omega)) (by omega) (by omega)
        (by omega)
      rw [blk0] at this
      have e : ([0x80] ++ List.replicate (P.N - D - 1) 0 : List Byte).length = P.N - D := by simp; omega
      rw [e]; exact this
    · have hfix : [(0x80 : Byte)] ++ List.replicate (P.N - D - 1) 0 = (H.tailPad D).take (P.N - D) :=
        (H.tailPad_take (by omega) (by omega)).symm
      have hfl : ((H.tailPad D).take (P.N - D)).length = P.N - D := by
        rw [List.length_take, H.tailPad_length (by omega)]; omega
      rw [hsplit, m₂, hfix, bytesAt_writeBytes_self' hfl (by omega),
        bytesAt_writeBytes_sep _ _ ?_ (by omega), r₁, hY, List.take_append_drop]
      have := blk_sep P s₀ (a := P.N) (n := P.B - P.N) (b := D) (k := P.N - D) (.inr (by omega)) (by omega)
        (by omega) (by omega)
      rw [hfl]; exact this
  · simp only [hDN, ↓reduceIte, List.nil_append]
    obtain rfl : D = P.N := by omega
    refine k s₁ g₁ rd₁ wr₁ sp₁ f₁ b₁ ?_
    rw [r₁, hY, Nat.sub_self, List.drop_zero]

end

/-! ## A step -/

/-- The block, of `D` bytes of message and the padding after them. -/
theorem blockAt_eq {P : Params} {D : Nat} {H : Md P.B P.N P.L} {m : Mem} {p : Addr} (hD : D ≤ P.B)
    (h : bytesAt m (p + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) :
    H.blockAt m p = H.tailBlock D (bytesAt m p D) := by
  simp only [Md.blockAt, Md.tailBlock]
  refine H.parse_congr fun k hk => ?_
  have e := bytesAt_add m p D (P.B - D)
  rw [h, show D + (P.B - D) = P.B by omega] at e
  rw [← e, bytesAt_getD' _ _ hk]

section
variable (P : Params) (D : Nat) (H : Md P.B P.N P.L) (s₀ : State)

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM : List Byte → List Byte :=
  H.step D (H.stateAt s₀.mem (key s₀)) (H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 (P.N + P.B)))

/-- What the body writes: the compression function's scratch space, the hash
value and the block, and `T`. -/
abbrev bodyR : List Region := [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N + P.B⟩, tR D s₀]

/-- Our caller's registers and our return address, saved in the scratch space. -/
def SavedAll (m : Mem) : Prop :=
  Saved P.md (scr s₀) s₀.gpr m ∧ m.readW (scr s₀ + BitVec.ofNat 64 (raO P)) 64 = s₀.gpr .x30

end

/-- The loop invariant, with `r` steps left. -/
structure Inv (P : Params) (D W : Nat) (H : Md P.B P.N P.L) (s₀ : State) (r : Nat) (s : State) : Prop
    extends Regs P D W s₀ s where
  x24 : s.gpr .x24 = BitVec.ofNat 64 r
  saved : SavedAll P s₀ s.mem
  pad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM P D H s₀) (nn s₀) (bytesAt s₀.mem (up s₀) D) (bytesAt s₀.mem (tp s₀) D) =
    Spec.Pbkdf2.iterate (stepM P D H s₀) r (bytesAt s.mem (blk P s₀) D) (bytesAt s.mem (tp s₀) D)

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀)
include hz hp

/-- The saved registers are outside what the body writes. -/
theorem saved_frame {m m' : Mem} (h : SavedAll P s₀ m) (hf : Frame (bodyR P D s₀) m m') : SavedAll P s₀ m' := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits
  have rd : ∀ d, P.so ≤ d → d + 8 ≤ P.so + 56 →
      m'.readW (scr s₀ + BitVec.ofNat 64 d) 64 = m.readW (scr s₀ + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    · exact (hp.t_s.sub_right (scr_sub s₀ (by omega))).symm
  refine ⟨fun q hq => ?_, ?_⟩
  · have hd := saved_off hz hq
    rw [← h.1 q hq]
    exact rd _ hd.1 (by show q.2 + 8 ≤ P.so + 56; omega)
  · rw [← h.2]; exact rd _ (by simp only [raO]; omega) (by simp only [raO]; omega)

omit hz hp in
/-- A range of the scratch space from `hv` on, within what the body writes. -/
theorem sub_body {a n : Nat} (h₁ : P.so + 56 ≤ a) (h₂ : a + n ≤ P.so + 56 + P.N + P.B) :
    ∃ r' ∈ bodyR P D s₀, Region.Sub ⟨scr s₀ + BitVec.ofNat 64 a, n⟩ r' :=
  ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ h₁ (by omega)⟩

omit hp in
/-- A range of the block disjoint from what the compression and loading the hash value write. -/
theorem blk_disj {a n : Nat} (h : a + n ≤ P.B) :
    ∀ r ∈ [⟨hv P s₀, P.N⟩, ⟨scr s₀, P.so⟩], Region.Disjoint ⟨blk P s₀ + BitVec.ofNat 64 a, n⟩ r := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [add_ofNat]
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- Loading the key's hash value at `key + o` and compressing the block into it. -/
theorem lc_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CompOk H P.so code)
    {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) (ho4 : o % 4 = 0) {s : State} (h : Regs P D W s₀ s)
    (hpad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {c : Prog isa}
    {Q : State → Prop}
    (k : ∀ s', Regs P D W s₀ s' → s'.gpr .x24 = s.gpr .x24 → Frame (bodyR P D s₀) s.mem s'.mem →
      Frame [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N⟩] s.mem s'.mem →
      bytesAt s'.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (blk P s₀) D = bytesAt s.mem (blk P s₀) D →
      H.stateAt s'.mem (hv P s₀) =
        H.compress (H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o)) (H.tailBlock D (bytesAt s.mem (blk P s₀) D)) →
      WP isa c s' Q) :
    WP isa (.block (loadKey P o)) s fun s' => WP isa (.seq (compressBlock name code) c) s' Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  rw [← List.append_nil (loadKey P o)]
  refine load_ok hz hp hR h (o := o) ho ho4 fun s₁ g₁ rd₁ wr₁ sp₁ f₁ e₁ => WP.block_nil ?_
  have h₁ := h.write (fun r hr => g₁ r (ne9 r hr)) rd₁ wr₁ sp₁ (frame_scr (a := P.so + 56) (by omega) f₁)
  refine WP.seq (cmp_ok hz hp hf h₁ fun s₂ h₂ x24₂ f₂ e₂ => ?_)
  have fh₁ : ∀ {a n : Nat}, a + n ≤ P.B → ∀ r ∈ [(⟨hv P s₀, P.N⟩ : Region)],
      Region.Disjoint ⟨blk P s₀ + BitVec.ofNat 64 a, n⟩ r :=
    fun h' r hr => blk_disj hz h' r (by simp at hr; simp [hr])
  have p₁ : bytesAt s₁.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D :=
    (Memory.frame_bytesAt f₁ (fh₁ (by omega)) (by omega)).trans hpad
  have u₁ : bytesAt s₁.mem (blk P s₀) D = bytesAt s.mem (blk P s₀) D := by
    have := Memory.frame_bytesAt f₁ (fh₁ (a := 0) (n := D) (by omega)) (by omega); rwa [blk0] at this
  have u₂ : bytesAt s₂.mem (blk P s₀) D = bytesAt s₁.mem (blk P s₀) D := by
    have := Memory.frame_bytesAt f₂ (blk_disj hz (a := 0) (n := D) (by omega)) (by omega); rwa [blk0] at this
  rw [e₁, blockAt_eq (by omega) p₁, u₁] at e₂
  have f : Frame [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N⟩] s.mem s₂.mem :=
    (f₁.mono (by simp)).trans (f₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  refine k s₂ h₂ (x24₂.trans (g₁ _ (by decide))) (f.sub fun r hr => ?_) f
    ((Memory.frame_bytesAt f₂ (blk_disj hz (by omega)) (by omega)).trans p₁) (u₂.trans u₁) e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨scr s₀, P.so⟩, by simp, fun _ h => h⟩
  · exact sub_body (by omega) (by omega)

/-- The end of a step: the digest into the block, `T ← T ⊕ U` and the count. -/
theorem tail_ok {H : Md P.B P.N P.L} (hs : Shape H) {s : State} (h : Regs P D W s₀ s)
    (hpad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {Q : State → Prop}
    (k : ∀ s', Regs P D W s₀ s' → s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 1 →
      Frame (bodyR P D s₀) s.mem s'.mem →
      bytesAt s'.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (blk P s₀) D = (H.digest (H.stateAt s.mem (hv P s₀))).take D →
      bytesAt s'.mem (tp s₀) D =
        Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp s₀) D) ((H.digest (H.stateAt s.mem (hv P s₀))).take D) → Q s') :
    WP isa (.block (Impl.Pbkdf2.AArch64.digest P D ++ (List.range (D / 4)).flatMap xorW ++
      ([.subImm .x .x24 .x24 1] : List Instr))) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.D4; have := hz.W
  have := hz.pad; have := hz.NL
  rw [List.append_assoc]
  refine digest_ok hz hp hs h hpad fun s₆ g₆ rd₆ wr₆ sp₆ f₆ b₆ p₆ => ?_
  have h₆ := h.write (fun r hr => g₆ r (ne9 r hr)) rd₆ wr₆ sp₆ (frame_scr (a := P.so + 56 + P.N) (by omega) f₆)
  have hd : Region.Disjoint (tR D s₀) ⟨blk P s₀, D⟩ := hp.t_s.sub_right (scr_sub s₀ (by omega))
  have hD4 : 4 * (D / 4) = D := by omega
  refine xor_ok hd (by omega) (D / 4) (by omega) _ s₆ _ h₆.x21 h₆.x23
    (fun j hj => by
      obtain ⟨r, hr, hc⟩ := in_blk hz hp h₆.wr (a := 4 * j) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun j hj => ⟨tR D s₀, by simp [h₆.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  rw [hD4] at m₇
  have hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₆.mem (tp s₀) D) (bytesAt s₆.mem (blk P s₀) D)).length = D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have f₇ : Frame [tR D s₀] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  have h₇ := h₆.write (fun r hr => g₇ r (ne9 r hr) (ne10 r hr)) rd₇ wr₇ sp₇ (f₇.mono (by simp))
  refine wp_subImm (by decide) fun s₈ u₈ => WP.block_nil ?_
  have h₈ := h₇.write (fun r hr => u₈.other r (ne24 r hr)) u₈.rd u₈.wr u₈.sp (by rw [u₈.mem]; exact Frame.refl _ _)
  have x24₇ : s₇.gpr .x24 = s.gpr .x24 := by rw [g₇ _ (by decide) (by decide), g₆ _ (by decide)]
  have hT₆ : bytesAt s₆.mem (tp s₀) D = bytesAt s.mem (tp s₀) D :=
    Memory.frame_bytesAt f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.sub_right (scr_sub s₀ (a := P.so + 56 + P.N) (n := P.N) (by omega))) (by omega)
  refine k s₈ h₈ (by rw [u₈.gpr, x24₇]) ?_ ?_ ?_ ?_
  · rw [u₈.mem]
    refine (f₆.sub fun r hr => ?_).trans (f₇.mono (by simp))
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_body (by omega) (by omega)
  · rw [u₈.mem]
    exact (Memory.frame_bytesAt f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.t_s.sub_right (by rw [add_ofNat]; exact scr_sub s₀ (by omega))).symm) (by omega)).trans p₆
  · rw [u₈.mem, m₇, bytesAt_writeBytes_sep _ _ (hd.symm.sep (Region.contains_self _ _) (by
      rw [hxl]; exact Region.contains_self _ _)) (by omega), b₆]
  · rw [u₈.mem, m₇, bytesAt_writeBytes_self' hxl (by omega), hT₆, b₆]

omit hz hp in
theorem iterate_succ (f : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    Spec.Pbkdf2.iterate f (n + 1) u t = Spec.Pbkdf2.iterate f n (f u) (Spec.Pbkdf2.xorBytes t (f u)) := rfl

theorem body_ok {H : Md P.B P.N P.L} (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa}
    (hf : CompOk H P.so code) {r : Nat} {s : State} (h : Inv P D W H s₀ (r + 1) s) :
    WP isa (body P D name code) s fun s' =>
      eval (.nonzero .x .x24) s' = some (r != 0) ∧ Inv P D W H s₀ r s' := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  unfold body
  refine WP.seq (lc_ok hz hp hR hf (o := 0) (by omega) rfl h.toRegs h.pad fun s₂ h₂ x24₂ f₂ g₂ p₂ _ e₂ => ?_)
  refine WP.seq (digest_ok hz hp hs h₂ p₂ fun s₃ g₃ rd₃ wr₃ sp₃ f₃ b₃ p₃ => ?_)
  have h₃ := h₂.write (fun r hr => g₃ r (ne9 r hr)) rd₃ wr₃ sp₃ (frame_scr (a := P.so + 56 + P.N) (by omega) f₃)
  refine lc_ok hz hp hR hf (o := P.N + P.B) (by omega) (by have := hz.N4; rcases hz.B with h | h <;> omega) h₃ p₃ fun s₅ h₅ x24₅ f₅ g₅ p₅ _ e₅ => ?_
  refine tail_ok hz hp hs h₅ p₅ fun s₈ h₈ x24₈ f₈ p₈ b₈ t₈ => ?_
  rw [e₅, b₃, e₂, add0] at b₈ t₈
  have x24₅' : s₅.gpr .x24 = BitVec.ofNat 64 (r + 1) := by
    rw [x24₅, g₃ _ (by decide), x24₂, h.x24]
  have hlt : r + 1 < 2 ^ 64 := by
    have := h.le; have := ((s₀.gpr .x2).setWidth 32).isLt; simp at *; omega
  have e₈ : s₅.gpr .x24 - BitVec.ofNat 64 1 = BitVec.ofNat 64 r := by
    rw [x24₅', show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega)]; rfl
  have fb : Frame (bodyR P D s₀) s.mem s₈.mem :=
    ((f₂.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_body (by omega) (by omega))).trans f₅).trans f₈
  have hT₅ : bytesAt s₅.mem (tp s₀) D = bytesAt s.mem (tp s₀) D := by
    refine Memory.frame_bytesAt (rs := [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N + P.B⟩])
      (((g₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)).trans (g₅.sub fun r hr => ?_)) (fun r hr => ?_) (by omega)
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (by omega)⟩
    · subst hr; exact ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ (by omega) (by omega)⟩
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (by omega)⟩
    · rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
      · exact hp.t_s.sub_right (scr_sub s₀ (by omega))
  rw [hT₅] at t₈
  refine ⟨?_, h₈, by rw [x24₈, e₈], saved_frame hz hp h.saved fb, p₈, by have := h.le; omega, ?_⟩
  · simp only [eval_nonzero, x24₈, e₈, bne, ofNat_beq_zero (by omega : r < 2 ^ 64)]
    cases r <;> rfl
  · rw [h.val, iterate_succ, b₈, t₈]; rfl

theorem loop_ok {H : Md P.B P.N P.L} (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa}
    (hf : CompOk H P.so code) {n : Nat} {s : State} (h : Inv P D W H s₀ n s) :
    WP isa (.ite (.zero .x .x24) (.block []) (.loop (body P D name code) (.nonzero .x .x24))) s
      (Inv P D W H s₀ 0) := by
  have hlt : n < 2 ^ 64 := by
    have := h.le; have := ((s₀.gpr .x2).setWidth 32).isLt; simp at *; omega
  refine WP.ite (decide (n = 0)) (by change eval (.zero .x .x24) s = _; rw [eval_zero, h.x24, ofNat_beq_zero hlt]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => Inv P D W H s₀ (m + 1) s)
      (fun m s hs' => WP.mono (body_ok hz hp hs hR hf hs') fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end

/-! ## The prologue -/

/-- The memory after saving our caller's registers and our return address. -/
def saveAll (P : Params) (s₀ : State) : Mem :=
  (saveMem P.md s₀.mem (scr s₀) s₀.gpr).writeW (scr s₀ + BitVec.ofNat 64 (raO P)) (s₀.gpr .x30)

/-- The state after the first instruction, which zero-extends `n`. -/
def zext (s : State) : State := s.write .w .x2 (s.read .w .x2 + BitVec.ofNat 32 0)

theorem zext_exec (s : State) : exec (.addImm .w .x2 .x2 0) s = some (zext s) := rfl

theorem zext_upd (s : State) : Upd s (zext s) .x2 (((s.gpr .x2).setWidth 32).setWidth 64) := by
  have := Upd.write s .w .x2 (s.read .w .x2 + BitVec.ofNat 32 0)
  simpa [zext, State.read, Size.bits] using this

theorem zext_x2 (s : State) : (zext s).gpr .x2 = BitVec.ofNat 64 (nn s) := by
  rw [(zext_upd s).gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, nn]

/-- After saving our caller's registers and our return address and setting
up our registers. -/
structure Setup (P : Params) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = hv P s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = blk P s₀
  x23 : s.gpr .x23 = tp s₀
  x24 : s.gpr .x24 = BitVec.ofNat 64 (nn s₀)
  x0 : s.gpr .x0 = key s₀
  x1 : s.gpr .x1 = up s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = saveAll P s₀

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀)
include hz hp

theorem setup_ok {rest : List Instr} {Q : State → Prop} (k : ∀ s, Setup P s₀ s → WP isa (.block rest) s Q) :
    WP isa (.block (save P.md .x4 ++
      ([.str .x .x30 .x4 (raO P), .addImm .x .x19 .x4 (hvO P), mov .x20 .x4, .addImm .x .x21 .x4 (blkO P),
        mov .x23 .x3, mov .x24 .x2] : List Instr) ++ rest)) (zext s₀) Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.W; have := so8 hz
  have u := zext_upd s₀
  have zg : ∀ r, r ≠ .x2 → (zext s₀).gpr r = s₀.gpr r := u.other
  simp only [List.append_assoc]
  refine save_ok hz.dims (b := .x4) (fun d h₁ h₂ => by
    rw [zg _ (by decide), u.wr]; exact in_scr hz hp rfl (by have := md_so P; omega))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 (raO P)) ⟨by simp only [raO]; omega, by simp only [raO]; omega⟩
    (by rw [g₁, zg _ (by decide)]) (by rw [wr₁, u.wr]; exact in_scr hz hp rfl (by simp only [raO]; omega))
    fun s₂ g₂ => ?_
  refine wp_addImm (by simp only [hvO]; omega) fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_addImm (by simp only [blkO]; omega) fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => ?_
  have G : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x23 → r ≠ .x24 → s₇.gpr r = s₁.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.other r h2, u₃.other r h1, g₂.gpr]
  have g0 : ∀ r, r ≠ .x2 → s₁.gpr r = s₀.gpr r := fun r h => by rw [g₁, zg r h]
  refine k s₇ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, rd₁, u.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, wr₁, u.wr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      g₂.gpr, g0 _ (by decide), hvO]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      g₂.gpr, g0 _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      g₂.gpr, g0 _ (by decide), blkO]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂.gpr, g0 _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂.gpr, g₁, zext_x2]
  · rw [G _ (by decide) (by decide) (by decide) (by decide) (by decide), g0 _ (by decide)]
  · rw [G _ (by decide) (by decide) (by decide) (by decide) (by decide), g0 _ (by decide)]
  · have : r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x2 := by
      simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [G r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1, g0 r this.2.2.2.2.2]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, g₂.sp, sp₁, u.sp]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, m₁, g₁, zg _ (by decide), zg _ (by decide), u.mem, saveAll]
    congr 1

omit hp in
theorem saveAll_frame : Frame [⟨scr s₀, P.so + 56⟩] s₀.mem (saveAll P s₀) := by
  have := so8 hz
  refine ((saveMem_frame hz.dims s₀.mem (scr s₀) s₀.gpr).sub fun r hr => ?_).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by simp only [raO]; omega) (by simp only [raO]; omega))
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by have := md_so P; omega)⟩

omit hp in
theorem saveAll_saved : SavedAll P s₀ (saveAll P s₀) := by
  have := so8 hz
  refine ⟨fun q hq => ?_, Mem.readW_writeW_self64 _ _ _⟩
  have hd := saved_off hz hq
  rw [saveAll, Mem.readW_writeW_sep (Offset.sep _ (.inl (by simp only [raO]; omega))
    (by omega) (by simp only [raO]; omega)) (by decide)]
  exact saveMem_saved hz.dims _ _ _ q hq

/-- Writing `U`, the padding and the length field into the block. -/
theorem fill_ok {H : Md P.B P.N P.L} (hs : Shape H) (hok : H.lenOk (P.B + D)) {s : State}
    (h : Setup P s₀ s) :
    WP isa (.block ((List.range (D / 4)).flatMap (Impl.Pbkdf2.AArch64.cp32 .x1 .x21 0 0) ++
      padFrom D (P.B - P.L) ++ ([.movz .x .x22 (BitVec.ofNat 16 (P.B + D)) 0] : List Instr) ++ P.len ++
      ([mov .x22 .x0] : List Instr))) s (Inv P D W H s₀ (nn s₀)) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL; have := hz.D4; have := hz.L4; have := hz.W; have := B_ge hz
  have : P.B % 4 = 0 := by rcases hz.B with h | h <;> omega
  have hD4 : 4 * (D / 4) = D := by omega
  simp only [List.append_assoc]
  refine copy32_ok (by decide) (by decide) 0 0 (D / 4) ⟨rfl, by omega⟩ ⟨rfl, by omega⟩ _ s _
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · rw [h.x1, h.rd, hp.rd, add0]
    exact ⟨uR D s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.x21, blk0]; exact in_blk hz hp h.wr (by omega)
  · rw [h.x1, h.x21, blk0, add0, hD4]
    exact hp.u_s.sep (Region.contains_self _ _) (Offset.contains_base _ (by omega) (by omega))
  rw [h.x21, h.x1, blk0, add0, hD4] at m₁
  refine padFrom_ok (a := D) (b := P.B - P.L) (by omega) (by omega) (by omega) (by omega) (s := s₁)
    (p := blk P s₀) (by rw [g₁ _ (by decide), h.x21]) (fun j hj => in_blk hz hp (wr₁.trans h.wr) (by omega))
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  refine wp_movz fun s₃ u₃ => ?_
  have x19₃ : s₃.gpr .x19 = hv P s₀ := by rw [u₃.other _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.x19]
  have ea : hv P s₀ + BitVec.ofNat 64 (P.N + P.B - P.L) = blk P s₀ + BitVec.ofNat 64 (P.B - P.L) := by
    rw [add_ofNat, add_ofNat, show P.so + 56 + (P.N + P.B - P.L) = P.so + 56 + P.N + (P.B - P.L) by omega]
  change WP isa (.block (P.len ++ [mov .x22 .x0])) s₃ _
  rw [WP.block_append_iff]
  refine WP.mono (hs.len s₃ ?_) fun s₄ ⟨g₄, rd₄, wr₄, sp₄, m₄⟩ => ?_
  · rw [x19₃, ea]; exact in_blk hz hp (u₃.wr.trans (wr₂.trans (wr₁.trans h.wr))) (by omega)
  refine wp_mov fun s₅ u₅ => WP.block_nil ?_
  have zx : (BitVec.ofNat 16 (P.B + D)).setWidth 64 = BitVec.ofNat 64 (P.B + D) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [x19₃, ea, u₃.gpr, zx, H.lenOf_eq _ hok] at m₄
  -- The memory.
  have hM : s₅.mem = writeBytes (writeBytes (writeBytes (saveAll P s₀) (blk P s₀)
      (bytesAt (saveAll P s₀) (up s₀) D)) (blk P s₀ + BitVec.ofNat 64 D)
      ([0x80] ++ List.replicate (P.B - P.L - D - 1) 0)) (blk P s₀ + BitVec.ofNat 64 (P.B - P.L))
      (H.lenBytes (P.B + D)) := by
    rw [u₅.mem, m₄, u₃.mem, m₂, m₁, h.mem]
  have hG : ∀ r ∈ kept, r ≠ .x22 → s₅.gpr r = s.gpr r := fun r hr h2 => by
    rw [u₅.other r h2, g₄ r (ne9 r hr) (ne12 r hr), u₃.other r h2, g₂ r (ne9 r hr), g₁ r (ne9 r hr)]
  have lpz : ([0x80] ++ List.replicate (P.B - P.L - D - 1) 0 : List Byte).length = P.B - P.L - D := by simp; omega
  have fM : Frame [⟨blk P s₀, P.B⟩] s.mem s₅.mem := by
    rw [hM, ← h.mem]
    refine ((writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)).trans (writeBytes_frame _ _ _ ?_)
    · rw [bytesAt_length]
      have := Offset.contains_base (blk P s₀) (d := 0) (n := D) (k := P.B) (by omega) (by omega)
      rwa [blk0] at this
    · rw [lpz]; exact Offset.contains_base _ (by omega) (by omega)
    · rw [H.lenBytes_length]; exact Offset.contains_base _ (by omega) (by omega)
  have fB : Frame (bodyR P D s₀) s.mem s₅.mem := fM.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_body (by omega) (by omega)
  have S1 : Mem.Sep (blk P s₀) D (blk P s₀ + BitVec.ofNat 64 D) (P.B - P.L - D) := by
    have := blk_sep P s₀ (a := 0) (n := D) (b := D) (k := P.B - P.L - D) (.inl (by omega)) (by omega)
      (by omega) (by omega)
    rwa [blk0] at this
  have S2 : ∀ {a n : Nat}, a + n ≤ P.B - P.L →
      Mem.Sep (blk P s₀ + BitVec.ofNat 64 a) n (blk P s₀ + BitVec.ofNat 64 (P.B - P.L)) P.L :=
    fun h' => blk_sep P s₀ (.inl h') (by omega) (by omega) (by omega)
  have fS : Frame [tR D s₀, scR W s₀] s₀.mem s.mem := by
    rw [h.mem]; exact saveAll_frame hz |>.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR W s₀, by simp, Region.sub_prefix (by omega)⟩
  refine ⟨⟨by rw [u₅.rd, rd₄, u₃.rd, rd₂, rd₁, h.rd], by rw [u₅.wr, wr₄, u₃.wr, wr₂, wr₁, h.wr],
    by rw [hG _ (by decide) (by decide), h.x19], by rw [hG _ (by decide) (by decide), h.x20],
    by rw [hG _ (by decide) (by decide), h.x21],
    by rw [u₅.gpr, g₄ _ (by decide) (by decide), u₃.other _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.x0],
    by rw [hG _ (by decide) (by decide), h.x23],
    fun r hr => by rw [hG _ (untouched_kept r hr) (untouched_ne22 r hr), h.cs r hr],
    by rw [u₅.sp, sp₄, u₃.sp, sp₂, sp₁, h.sp],
    fS.trans (frame_scr (a := P.so + 56 + P.N) (by omega) fM)⟩,
    by rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide), u₃.other _ (by decide), g₂ _ (by decide),
      g₁ _ (by decide), h.x24],
    saved_frame hz hp (h.mem ▸ saveAll_saved hz) fB, ?_, Nat.le_refl _, ?_⟩
  · -- The padding and the length field.
    rw [show P.B - D = (P.B - P.L - D) + P.L by omega, bytesAt_add, add_ofNat (blk P s₀),
      show D + (P.B - P.L - D) = P.B - P.L by omega, hM,
      bytesAt_writeBytes_self' (H.lenBytes_length _) (by omega),
      bytesAt_writeBytes_sep _ _ (by rw [H.lenBytes_length]; exact S2 (by omega)) (by omega),
      bytesAt_writeBytes_self' lpz (by omega), Md.tailPad, show P.B - P.L - 1 - D = P.B - P.L - D - 1 by omega]
  · -- `U` and `T`.
    have hU : bytesAt s₅.mem (blk P s₀) D = bytesAt s₀.mem (up s₀) D := by
      rw [hM, bytesAt_writeBytes_sep _ _ (by
          rw [H.lenBytes_length]; have := S2 (a := 0) (n := D) (by omega); rwa [blk0] at this) (by omega),
        bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (by omega),
        bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
      refine Memory.frame_bytesAt (saveAll_frame hz) (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.u_s.sub_right (Region.sub_prefix (by omega))
    have hT : bytesAt s₅.mem (tp s₀) D = bytesAt s₀.mem (tp s₀) D := by
      refine Memory.frame_bytesAt ((saveAll_frame hz).mono
        (rs' := [⟨scr s₀, P.so + 56⟩, ⟨blk P s₀, P.B⟩]) (by simp) |>.trans
        ((h.mem ▸ fM).mono (by simp))) (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
      · exact hp.t_s.sub_right (scr_sub s₀ (by omega))
    rw [hU, hT]

theorem prologue_ok {H : Md P.B P.N P.L} (hs : Shape H) (hok : H.lenOk (P.B + D)) :
    WP isa (.block (prologue P D)) (zext s₀) (Inv P D W H s₀ (nn s₀)) := by
  have := setup_ok hz hp (rest := (List.range (D / 4)).flatMap (Impl.Pbkdf2.AArch64.cp32 .x1 .x21 0 0) ++
    padFrom D (P.B - P.L) ++ [.movz .x .x22 (BitVec.ofNat 16 (P.B + D)) 0] ++ P.len ++
    [mov .x22 .x0]) fun s h => fill_ok hz hp hs hok h
  unfold prologue
  simpa only [List.append_assoc] using this

omit hz hp in
/-- The final `T` is PBKDF2's, for a key as the contract requires. -/
theorem post_eq {H : Md P.B P.N P.L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv D) {m : Mem}
    (hT : bytesAt m (tp s₀) D =
      Spec.Pbkdf2.iterate (stepM P D H s₀) (nn s₀) (bytesAt s₀.mem (up s₀) D) (bytesAt s₀.mem (tp s₀) D))
    {k0 : List Byte} (hk : k0.length = S.H.blockSize) (hi : S.Repr s₀.mem (key s₀) (xorPad k0 ipad))
    (ho : S.Repr s₀.mem (key s₀ + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad)) :
    bytesAt m (tp s₀) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (nn s₀) (bytesAt s₀.mem (up s₀) S.digestBytes)
        (bytesAt s₀.mem (tp s₀) S.digestBytes) := by
  have hB : 0 < P.B := by have := hl.DL; omega
  rw [hl.hB] at hk
  rw [hl.hS] at ho
  have li : (xorPad k0 ipad).length = P.B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = P.B := by simp [xorPad, hk]
  have ei := Md.stateAt_of_repr hB li (hl.repr _ _ _ hi)
  have eo := Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)
  rw [hl.hD]
  refine hT.trans (Md.iterate_congr (fun u hu => ?_) (fun u => Md.step_length H hl.DN _ _ u) _ _ _
    (bytesAt_length _ _ _)).symm
  rw [Md.hmac_step hl hk hu, ei, eo]

theorem epilogue_ok {H : Md P.B P.N P.L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv D) {s : State}
    (h : Inv P D W H s₀ 0 s) :
    WP isa (.block (epilogue P)) s fun s' => GprAbi s₀ s' ∧ (iterK S W).post s₀ s' := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.W; have := so8 hz
  unfold epilogue
  refine wp_ldr (a := scr s₀ + BitVec.ofNat 64 (raO P)) ⟨by simp only [raO]; omega, by simp only [raO]; omega⟩
    (by rw [h.x20]) (in_scr' hz hp h.wr (by simp only [raO]; omega)) fun s₁ u₁ => ?_
  refine restore_ok hz.dims (scr := scr s₀) (by rw [u₁.other _ (by decide), h.x20])
    (fun d _ hd₂ => by rw [u₁.rd, u₁.wr]; exact in_scr' hz hp h.wr (by have := md_so P; omega))
    s₀.gpr (by rw [u₁.mem]; exact h.saved.1)
    fun s' hsv hother hmem _ _ hsp => ⟨⟨fun r hr => ?_, by rw [hsp, u₁.sp, h.sp]⟩, fun k0 hk hi ho => ?_⟩
  · by_cases h30 : r = .x30
    · subst h30; rw [hother _ (by simp [saved]), u₁.gpr, h.saved.2]
    · refine preserved_of (P := P.md) hsv (fun r hr => ?_) r hr h30
      rw [hother r (untouched_not_saved _ r hr), u₁.other r (untouched_ne30 r hr),
        h.cs r hr]
  · rw [hmem, u₁.mem]; exact post_eq hl h.val.symm hk hi ho

end

/-! ## Correctness -/

/-- What the proof needs of a hash function, with its code's `Params`, a
`D`-byte digest and `W` words of scratch space: the sizes, the length field
and digest of its code, that its hash value depends only on the bytes it is
stored in, that the length field of a `B + D`-byte message is its byte
count's, and that it is the hash function `S` of the specification. -/
structure HashOk (P : Params) (D W : Nat) (S : StreamingHash) (H : Md P.B P.N P.L) (iv : H.HV) : Prop where
  sizes : Sizes P D W
  shape : Shape H
  reloc : H.Reloc
  lenOk : H.lenOk (P.B + D)
  link : H.Link S iv D

theorem main_ok {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : CompOk H P.so code) {s₀ : State}
    (hp : Pre P D W s₀) :
    WP isa (main P D name code) (zext s₀) fun s' => GprAbi s₀ s' ∧ (iterK S W).post s₀ s' := by
  unfold main
  refine WP.seq (WP.mono (prologue_ok ho.sizes hp ho.shape ho.lenOk) fun s₁ h => ?_)
  exact WP.seq (WP.mono (loop_ok ho.sizes hp ho.shape ho.reloc hf h) fun s₂ h₂ =>
    epilogue_ok ho.sizes hp ho.link h₂)

/-- The wrapper adds scalar instructions and checked length/digest code. -/
theorem iterate_keepsV {P : Params} {D : Nat} {H : Md P.B P.N P.L}
    (hs : Shape H) {name : String} {code : Prog isa} (hc : code.allInstrs keepsV = true) :
    (iterate P D name code).allInstrs keepsV = true := by
  rw [Code.allInstrs_eq] at hc ⊢
  by_cases hDN : D < P.N <;>
  simp [iterate, main, prologue, epilogue, body, loadKey, compressBlock,
    Impl.Pbkdf2.AArch64.digest, padFrom, Impl.Pbkdf2.AArch64.cp32, xorW, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, Impl.MdStream.AArch64.save,
    Impl.MdStream.AArch64.saved, Impl.MdStream.AArch64.restore, Impl.MdStream.AArch64.mov,
    instrs, keepsV, vdstOf, hc, hs.lenKeepsV, hs.outKeepsV, hDN]

theorem correct {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : CompOk H P.so code) {s₀ : State}
    (hp : Pre P D W s₀) :
    WP isa (iterate P D name code) s₀ fun s' => abiPreserved s₀ s' ∧ (iterK S W).post s₀ s' :=
  WP.withPreservedV
    (WP.seq (MdStream.AArch64.WP.cons (zext_exec s₀) (WP.block_nil (main_ok ho hf hp))))
    (iterate_keepsV ho.shape hf.keepsV)

/-- `iterate` is correct and keeps what the calling convention requires. -/
theorem iterate_ok {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : CompOk H P.so code)
    (s : State) (hs : (iterK S W).pre s) :
    ∃ t s', Exec isa (iterate P D name code) s t s' ∧ abiPreserved s s' ∧ (iterK S W).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct ho hf (pre_of ho.link.hS ho.link.hD hs)
  exact ⟨t, s', he, h⟩

end VG.Proof.Pbkdf2.AArch64
