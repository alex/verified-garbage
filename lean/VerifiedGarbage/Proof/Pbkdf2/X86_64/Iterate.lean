import VerifiedGarbage.Proof.Pbkdf2.MdStep
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Hmac.X86_64.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Impl.Pbkdf2.X86_64

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86-64

Untrusted: everything here is checked by Lean. The iteration
(`Impl/Pbkdf2/X86_64.lean`) is correct for any hash function the generic
streaming proofs describe (`Md`), whose code stores the length field and
writes the digest as `Shape` says, with any correct compression function
(`CalleeOk`), used as a black box through its proof; `Md.hmac_step` says that
its two compressions per step compute HMAC.
-/

namespace VG.Proof.Pbkdf2.X86_64

open VG VG.X86_64
open VG.Impl.MdStream.X86_64 (Params at_ save restore saved)
open VG.Impl.Pbkdf2.X86_64 (hvO blkO loadKey padFrom xorW compressBlock body prologue iterate)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.X86_64 (Dims Shape CalleeOk CallOk compressAt_ok Upd wp_mov wp_mov32i wp_addi wp_subi
  wp_test wp_mov32m wp_store32 wp_store wp_movm ea_at ofInt_natCast Saved saveMem saveMem_saved saveMem_frame
  saved_offset save_eq restore_eq sx_ofNat zx_ofNat ofNat_pred ofNat_beq_zero add_ofNat setWidth32)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame writeBytes_append)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep bytesAt_writeBytes_self
  writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.X86_64 (copy32_ok ea_off)
open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

/-! ## The contract -/

/-- The contract the proof is written against: `VG.Spec.Pbkdf2.iterateContract`
of the streaming hash function `S` with `W` words of scratch space, on
x86-64, with the 8 bytes of stack below the return address that the calls
of the compression function use. -/
def iterK (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 2 * S.stateBytes⟩
    let u : Region := ⟨s.gpr .rsi, S.digestBytes⟩
    let t : Region := ⟨s.gpr .rcx, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    ret.Disjoint key ∧ ret.Disjoint u ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 2 * S.stateBytes ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem (s.gpr .rdi) (xorPad k0 ipad) →
    S.Repr s.mem (s.gpr .rdi + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) ((s.gpr .rdx).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .rsi) S.digestBytes) (bytesAt s.mem (s.gpr .rcx) S.digestBytes)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The sizes the proof supports, checked for each hash function by `decide`:
words of 4 bytes, a digest of at most the hash value, room for the padding
in the block after the digest and after the hash value, and room in the
scratch space for the compression function's, our caller's registers, the
hash value and the block. -/
structure Sizes (P : Params) (D W : Nat) : Prop where
  dims : Dims P
  N4 : P.N % 4 = 0
  D4 : D % 4 = 0
  L4 : P.L % 4 = 0
  D0 : 0 < D
  DN : D ≤ P.N
  NL : P.N + P.L ≤ P.B
  pad : D + 4 ≤ P.B - P.L
  fits : P.so + 48 + P.N + P.B ≤ 8 * W
  W : W ≤ 1024

/-! ## The precondition -/

section
variable (P : Params) (D W : Nat) (s₀ : State)

abbrev key : Addr := s₀.gpr .rdi
abbrev up : Addr := s₀.gpr .rsi
abbrev tp : Addr := s₀.gpr .rcx
abbrev scr : Addr := s₀.gpr .r8
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .rdx).setWidth 32).toNat
abbrev keyR : Region := ⟨key s₀, 2 * (P.N + P.B)⟩
abbrev uR : Region := ⟨up s₀, D⟩
abbrev tR : Region := ⟨tp s₀, D⟩
abbrev scR : Region := ⟨scr s₀, 8 * W⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The hash value being compressed, and the block. -/
abbrev hv : Addr := scr s₀ + BitVec.ofNat 64 (P.so + 48)
abbrev blk : Addr := scr s₀ + BitVec.ofNat 64 (P.so + 48 + P.N)

end

structure Pre (P : Params) (D W : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR P s₀, uR D s₀]
  wr : s₀.wr = [tR D s₀, scR W s₀]
  k_t : (keyR P s₀).Disjoint (tR D s₀)
  k_s : (keyR P s₀).Disjoint (scR W s₀)
  u_t : (uR D s₀).Disjoint (tR D s₀)
  u_s : (uR D s₀).Disjoint (scR W s₀)
  t_s : (tR D s₀).Disjoint (scR W s₀)
  ret_k : (retR s₀).Disjoint (keyR P s₀)
  ret_u : (retR s₀).Disjoint (uR D s₀)
  ret_t : (retR s₀).Disjoint (tR D s₀)
  ret_s : (retR s₀).Disjoint (scR W s₀)
  stk_k : (stkR s₀).Disjoint (keyR P s₀)
  stk_u : (stkR s₀).Disjoint (uR D s₀)
  stk_t : (stkR s₀).Disjoint (tR D s₀)
  stk_s : (stkR s₀).Disjoint (scR W s₀)

theorem pre_of {P : Params} {D W : Nat} {S : StreamingHash} (hS : S.stateBytes = P.N + P.B)
    (hD : S.digestBytes = D) {s₀ : State} (h : (iterK S W).pre s₀) : Pre P D W s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -⟩ := h
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- The return address and the 8 bytes below it. -/
theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

/-! ## The parts of the scratch space -/

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀)
include hz

theorem so_le : P.so ≤ 2048 := hz.dims.so
theorem N_le : P.N ≤ 64 := hz.dims.N.2
theorem B_le : P.B ≤ 128 := by rcases hz.dims.B with h | h <;> omega
theorem B_ge : 64 ≤ P.B := by rcases hz.dims.B with h | h <;> omega

omit hz in
theorem scr_sub (s₀ : State) {a n : Nat} (h : a + n ≤ 8 * W) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 a, n⟩ (scR W s₀) :=
  Offset.sub_base _ h

end

/-! ## The registers during a step -/

/-- What holds between the pieces of a step: the regions, our registers, and
memory outside the scratch space, `T` and the stack as on entry. -/
structure Regs (P : Params) (D W : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = hv P s₀
  rbp : s.gpr .rbp = blk P s₀
  r12 : s.gpr .r12 = key s₀
  r13 : s.gpr .r13 = tp s₀
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [tR D s₀, scR W s₀, stkR s₀] s₀.mem s.mem

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀)

/-- `Regs` after code that keeps our registers and writes only memory in the
regions it allows. -/
theorem Regs.write {s s' : State} (h : Regs P D W s₀ s)
    (hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .r14 → s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hm : Frame [tR D s₀, scR W s₀, stkR s₀] s.mem s'.mem) :
    Regs P D W s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.rbx
  rbp := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.rbp
  r12 := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r12
  r13 := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r13
  r15 := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r15
  rsp := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.rsp
  frame := h.frame.trans hm

omit hp in
/-- A part of the scratch space, as a frame of `Regs`. -/
theorem frame_scr {m m' : Mem} {a n : Nat} (h : a + n ≤ 8 * W)
    (hf : Frame [⟨scr s₀ + BitVec.ofNat 64 a, n⟩] m m') : Frame [tR D s₀, scR W s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR W s₀, by simp, scr_sub s₀ h⟩

include hz hp

/-- The hash value at `key + o` into the scratch space. -/
theorem load_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {s : State} (h : Regs P D W s₀ s) {o : Nat}
    (ho : o + P.N ≤ 2 * (P.N + P.B)) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨hv P s₀, P.N⟩] s.mem s'.mem →
      H.stateAt s'.mem (hv P s₀) = H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loadKey P o ++ rest)) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.N4; have := hz.fits
  have hn : 4 * (P.N / 4) = P.N := by omega
  unfold loadKey
  refine copy32_ok (by decide) (by decide) o 0 (P.N / 4) rest s Q (fun j hj => ?_) (fun j hj => ?_) ?_
    (by omega) fun s' g' rd' wr' m' => ?_
  · rw [h.r12, h.rd, hp.rd, add_ofNat]
    exact ⟨keyR P s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.rbx, h.wr, hp.wr, add_ofNat, add_ofNat]
    exact ⟨scR W s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.r12, h.rbx, hn, add_ofNat, Nat.add_zero]
    exact hp.k_s.sep (Offset.contains_base _ (by omega) (by omega))
      (Offset.contains_base _ (by omega) (by omega))
  rw [h.rbx, h.r12, hn, add_ofNat, Nat.add_zero] at m'
  refine k s' g' rd' wr' (by rw [m']; exact writeBytes_frame _ _ _ (by
    rw [bytesAt_length]; exact Region.contains_self _ _)) ?_
  refine hR _ _ _ _ fun i hi => ?_
  rw [m', writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi, add_ofNat]
  exact h.frame.bytes (R := keyR P s₀) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.k_t
    · exact hp.k_s
    · exact hp.stk_k.symm) (by show 2 * (P.N + P.B) ≤ 2 ^ 64; omega) (by show o + i < 2 * (P.N + P.B); omega)

/-- What the call of the compression function needs, with the block's address in `rsi`. -/
theorem callOk_of {s : State} (h : Regs P D W s₀ s) (hsi : s.gpr .rsi = blk P s₀) :
    CallOk P s (hv P s₀) (scr s₀) (blk P s₀) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits
  have hsc : scR W s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  have stk : ∀ {a n : Nat}, a + n ≤ 8 * W →
      (below (s.gpr .rsp) 8).Disjoint ⟨scr s₀ + BitVec.ofNat 64 a, n⟩ :=
    fun h' => by rw [h.rsp]; exact hp.stk_s.sub_right (scr_sub s₀ h')
  refine ⟨h.rbx, h.r15, hsi, Offset.disjoint_base _ (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega), Offset.disjoint_base _ (by omega) (by omega),
    stk (by omega), by simpa using stk (a := 0) (n := P.so) (by omega), stk (by omega), ?_, ?_⟩
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
theorem cmp_ok {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : CalleeOk H code) {s : State}
    (h : Regs P D W s₀ s) {Q : State → Prop}
    (k : ∀ s', Regs P D W s₀ s' → s'.gpr .r14 = s.gpr .r14 →
      Frame [⟨hv P s₀, P.N⟩, ⟨scr s₀, P.so⟩, stkR s₀] s.mem s'.mem →
      H.stateAt s'.mem (hv P s₀) = H.compress (H.stateAt s.mem (hv P s₀)) (H.blockAt s.mem (blk P s₀)) →
      Q s') :
    WP isa (compressBlock name code) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits
  unfold compressBlock
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => WP.block_nil ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [u₁.other _ (by decide), h.rsp]
  have h₁ := h.write (fun r _ _ _ hr _ _ => u₁.other r hr) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _)
  refine compressAt_ok H hf (callOk_of hz hp h₁ (by rw [u₁.gpr, h.rbp])) (by omega) (by omega)
    fun s' hrd hwr hcs hfr hst _ _ => ?_
  have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := fun r hr => by
    rw [hcs r hr, u₁.other r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  rw [hsp, u₁.mem] at hfr
  rw [u₁.mem] at hst
  refine k s' ⟨hrd.trans (u₁.rd.trans h.rd), hwr.trans (u₁.wr.trans h.wr),
    (cs _ (by simp [calleeSaved])).trans h.rbx, (cs _ (by simp [calleeSaved])).trans h.rbp,
    (cs _ (by simp [calleeSaved])).trans h.r12, (cs _ (by simp [calleeSaved])).trans h.r13,
    (cs _ (by simp [calleeSaved])).trans h.r15, (cs _ (by simp [calleeSaved])).trans h.rsp,
    h.frame.trans (hfr.sub fun r hr => ?_)⟩ (cs _ (by simp [calleeSaved])) hfr hst
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨scR W s₀, by simp, scr_sub s₀ (by omega)⟩
  · exact ⟨scR W s₀, by simp, Region.sub_prefix (by omega)⟩
  · exact ⟨stkR s₀, by simp, fun _ h => h⟩

end

/-! ## Words of the block and of `T` -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor32m {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d ((((s.gpr d).setWidth 32) ^^^ s.mem.readW a 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.mem m) :: is)) s Q := by
  refine MdStream.X86_64.WP.cons
    (s' := (arithFlags s (((s.gpr d).setWidth 32) ^^^ s.mem.readW a 32) false false).setReg d _) ?_
    (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu32, readSrc32, State.load32, State.setReg32, ha, hin]

theorem wp_mov32r {d r : Reg} (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  MdStream.X86_64.WP.cons rfl (k _ (Upd.setReg _ _ _))

end

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
theorem xor_ok {tp bp : Addr} {D : Nat} (hd : Region.Disjoint ⟨tp, D⟩ ⟨bp, D⟩) (hD : D < 2 ^ 32) :
    ∀ n, 4 * n ≤ D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .rbp = bp → s.gpr .r13 = tp →
    (∀ k < n, InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (tp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem tp
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hbp h13 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hbp h13 (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_mov32m (a := bp + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, g₁ _ (by decide), hbp, ofInt_natCast]) (by rw [rd₁, wr₁]; exact hin n (by omega))
      fun s₂ u₂ => ?_
    have hw := hout n (by omega)
    refine wp_xor32m (a := tp + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, u₂.other _ (by decide), g₁ _ (by decide), h13, ofInt_natCast])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩)
      fun s₃ u₃ => ?_
    refine wp_store32 (a := tp + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), h13, ofInt_natCast])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ (fun r hr => by rw [g₄, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [rd₄, u₃.rd, u₂.rd, rd₁]) (by rw [wr₄, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))).length = 4 * n := by
      rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    rw [m₄, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, setWidth32, setWidth32, writeW_xor32, m₁,
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

/-- Stores of zero (the low 32 bits of `rax`) at `rbp + a + 4 + 4 k`, for `k < n`. -/
theorem zeros_ok {a : Nat} {p : Addr} : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .rbp = p → (s.gpr .rax).setWidth 32 = 0 →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 + 4 * k)) 4) → 4 * n < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 (a + 4)) (List.replicate (4 * n) 0) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.store32 (at_ .rbp (a + 4 + 4 * k)) .rax) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hbp hax hout hn k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hbp hax (fun j hj => hout j (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_store32 (a := p + BitVec.ofNat 64 (a + 4 + 4 * n)) (by rw [ea_at, g₁, hbp, ofInt_natCast])
      (by rw [wr₁]; exact hout n (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ =>
        k s₂ (by rw [g₂, g₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) ?_
    rw [m₂, g₁, hax, m₁, Memory.writeW_bytes _ _ (0 : BitVec 32) [0, 0, 0, 0] (by decide),
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate, add_ofNat]) (by simp; omega), Nat.mul_succ,
      ← List.replicate_append_replicate]
    rfl

/-- `padFrom a b` writes `0x80` and zeros from byte `a` to byte `b` of the block at `rbp`. -/
theorem padFrom_ok {a b : Nat} (hab : a + 4 ≤ b) (h4 : (b - a) % 4 = 0) (hb : b < 2 ^ 31) {s : State} {p : Addr}
    (hbp : s.gpr .rbp = p) (hout : ∀ k < (b - a) / 4, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 * k)) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 a) ([0x80] ++ List.replicate (b - a - 1) 0) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (padFrom a b ++ rest)) s Q := by
  unfold padFrom
  simp only [List.cons_append, List.nil_append]
  refine wp_mov32i fun s₁ u₁ _ _ => ?_
  refine wp_store32 (a := p + BitVec.ofNat 64 a) (by rw [ea_at, u₁.other _ (by decide), hbp, ofInt_natCast])
    (by rw [u₁.wr]; simpa using hout 0 (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_mov32i fun s₃ u₃ _ _ => ?_
  refine zeros_ok (a := a) ((b - a) / 4 - 1) rest s₃ Q (by rw [u₃.other _ (by decide), g₂, u₁.other _ (by decide),
    hbp]) (by rw [u₃.gpr, setWidth32]) (fun j hj => by
      rw [u₃.wr, wr₂, u₁.wr, show a + 4 + 4 * j = a + 4 * (j + 1) by omega]; exact hout (j + 1) (by omega))
    (by omega) fun s₄ g₄ rd₄ wr₄ m₄ => k s₄ (fun r hr => by
      rw [g₄, u₃.other r hr, g₂, u₁.other r hr]) (by rw [rd₄, u₃.rd, rd₂, u₁.rd]) (by rw [wr₄, u₃.wr, wr₂, u₁.wr]) ?_
  rw [m₄, u₃.mem, m₂, u₁.gpr, u₁.mem, setWidth32,
    Memory.writeW_bytes _ _ (0x80 : BitVec 32) [0x80, 0, 0, 0] (by decide),
    Memory.writeBytes_append' _ _ _ (by rw [List.length_cons, List.length_cons, List.length_cons,
      List.length_singleton, add_ofNat]) (by simp; omega),
    show b - a - 1 = 3 + 4 * ((b - a) / 4 - 1) by omega, ← List.replicate_append_replicate]
  rfl

/-! ## The digest into the block -/

theorem blk_sep (P : Params) (s₀ : State) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ 2 ^ 32)
    (hb : b + k ≤ 2 ^ 32) (hN : P.so + 48 + P.N ≤ 2 ^ 32) :
    Mem.Sep (blk P s₀ + BitVec.ofNat 64 a) n (blk P s₀ + BitVec.ofNat 64 b) k := by
  rw [add_ofNat, add_ofNat]
  exact Offset.sep _ (by omega) (by omega) (by omega)

theorem blk0 (P : Params) (s₀ : State) : blk P s₀ + BitVec.ofNat 64 0 = blk P s₀ := by simp

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀)
include hz hp

theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * W) :
    InRegions s.wr (scr s₀ + BitVec.ofNat 64 a) n :=
  ⟨scR W s₀, by simp [hwr, hp.wr], Offset.contains_base _ h (by have := hz.W; omega)⟩

theorem in_blk {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ P.B) :
    InRegions s.wr (blk P s₀ + BitVec.ofNat 64 a) n := by
  have := hz.fits
  rw [add_ofNat]; exact in_scr hz hp hwr (by omega)

/-- The digest of the hash value into the block's first `D` bytes, the padding after them as it was. -/
theorem digest_ok {H : Md P.B P.N P.L} (hs : Shape H) {s : State} (h : Regs P D W s₀ s)
    (hpad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨blk P s₀, P.N⟩] s.mem s'.mem →
      bytesAt s'.mem (blk P s₀) D = (H.digest (H.stateAt s.mem (hv P s₀))).take D →
      bytesAt s'.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.X86_64.digest P D ++ rest)) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.NL
  have := hz.D4; have := hz.N4; have := hz.pad
  unfold Impl.Pbkdf2.X86_64.digest
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (hs.out s ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  · rw [h.rbx]
    obtain ⟨r, hr, hc⟩ := in_scr hz hp h.wr (a := P.so + 48) (n := P.N) (by omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [h.rbp]; exact in_scr hz hp h.wr (by omega)
  · rw [h.rbx, h.rbp]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  rw [h.rbp, h.rbx] at m₁
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
    refine padFrom_ok (a := D) (b := P.N) (by omega) (by omega) (by omega) (s := s₁) (p := blk P s₀)
      (by rw [g₁ _ (by decide), h.rbp]) (fun j hj => in_blk hz hp (wr₁.trans h.wr) (by omega))
      fun s₂ g₂ rd₂ wr₂ m₂ => k s₂ (fun r hr => (g₂ r hr).trans (g₁ r hr)) (rd₂.trans rd₁) (wr₂.trans wr₁) ?_ ?_ ?_
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
    refine k s₁ g₁ rd₁ wr₁ f₁ b₁ ?_
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
value and the block, `T` and the stack. -/
abbrev bodyR : List Region := [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N + P.B⟩, tR D s₀, stkR s₀]

end

/-- The loop invariant, with `r` steps left. -/
structure Inv (P : Params) (D W : Nat) (H : Md P.B P.N P.L) (s₀ : State) (r : Nat) (s : State) : Prop
    extends Regs P D W s₀ s where
  r14 : s.gpr .r14 = BitVec.ofNat 64 r
  saved : Saved P s₀ .r8 s.mem
  pad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM P D H s₀) (nn s₀) (bytesAt s₀.mem (up s₀) D) (bytesAt s₀.mem (tp s₀) D) =
    Spec.Pbkdf2.iterate (stepM P D H s₀) r (bytesAt s.mem (blk P s₀) D) (bytesAt s.mem (tp s₀) D)

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀)
include hz hp

/-- The saved registers are outside what the body writes. -/
theorem saved_frame {m m' : Mem} (h : Saved P s₀ .r8 m) (hf : Frame (bodyR P D s₀) m m') : Saved P s₀ .r8 m' := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits
  intro q hq
  rw [← h q hq]
  have hd := saved_offset hz.dims hq
  rw [ofInt_natCast]
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 q.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact (hp.t_s.sub_right (scr_sub s₀ (by omega))).symm
  · exact (hp.stk_s.sub_right (scr_sub s₀ (by omega))).symm

omit hz hp in
/-- A range of the scratch space from `hv` on, within what the body writes. -/
theorem sub_body {a n : Nat} (h₁ : P.so + 48 ≤ a) (h₂ : a + n ≤ P.so + 48 + P.N + P.B) :
    ∃ r' ∈ bodyR P D s₀, Region.Sub ⟨scr s₀ + BitVec.ofNat 64 a, n⟩ r' :=
  ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ h₁ (by omega)⟩

/-- A range of the block disjoint from what the compression and loading the hash value write. -/
theorem blk_disj {a n : Nat} (h : a + n ≤ P.B) :
    ∀ r ∈ [⟨hv P s₀, P.N⟩, ⟨scr s₀, P.so⟩, stkR s₀], Region.Disjoint ⟨blk P s₀ + BitVec.ofNat 64 a, n⟩ r := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [add_ofNat]
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact (hp.stk_s.sub_right (scr_sub s₀ (by omega))).symm

/-- Loading the key's hash value at `key + o` and compressing the block into it. -/
theorem lc_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) {s : State} (h : Regs P D W s₀ s)
    (hpad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {c : Prog isa}
    {Q : State → Prop}
    (k : ∀ s', Regs P D W s₀ s' → s'.gpr .r14 = s.gpr .r14 → Frame (bodyR P D s₀) s.mem s'.mem →
      Frame [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (blk P s₀) D = bytesAt s.mem (blk P s₀) D →
      H.stateAt s'.mem (hv P s₀) =
        H.compress (H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o)) (H.tailBlock D (bytesAt s.mem (blk P s₀) D)) →
      WP isa c s' Q) :
    WP isa (.block (loadKey P o)) s fun s' => WP isa (.seq (compressBlock name code) c) s' Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  rw [← List.append_nil (loadKey P o)]
  refine load_ok hz hp hR h (o := o) ho fun s₁ g₁ rd₁ wr₁ f₁ e₁ => WP.block_nil ?_
  have h₁ := h.write (fun r hr _ _ _ _ _ => g₁ r hr) rd₁ wr₁ (frame_scr (a := P.so + 48) (by omega) f₁)
  refine WP.seq (cmp_ok hz hp hf h₁ fun s₂ h₂ r14₂ f₂ e₂ => ?_)
  have fh₁ : ∀ {a n : Nat}, a + n ≤ P.B → ∀ r ∈ [(⟨hv P s₀, P.N⟩ : Region)],
      Region.Disjoint ⟨blk P s₀ + BitVec.ofNat 64 a, n⟩ r :=
    fun h' r hr => blk_disj hz hp h' r (by simp at hr; simp [hr])
  have p₁ : bytesAt s₁.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D :=
    (Memory.frame_bytesAt f₁ (fh₁ (by omega)) (by omega)).trans hpad
  have u₁ : bytesAt s₁.mem (blk P s₀) D = bytesAt s.mem (blk P s₀) D := by
    have := Memory.frame_bytesAt f₁ (fh₁ (a := 0) (n := D) (by omega)) (by omega); rwa [blk0] at this
  have u₂ : bytesAt s₂.mem (blk P s₀) D = bytesAt s₁.mem (blk P s₀) D := by
    have := Memory.frame_bytesAt f₂ (blk_disj hz hp (a := 0) (n := D) (by omega)) (by omega); rwa [blk0] at this
  rw [e₁, blockAt_eq (by omega) p₁, u₁] at e₂
  have f : Frame [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N⟩, stkR s₀] s.mem s₂.mem :=
    (f₁.mono (by simp)).trans (f₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)
  refine k s₂ h₂ (r14₂.trans (g₁ _ (by decide))) (f.sub fun r hr => ?_) f
    ((Memory.frame_bytesAt f₂ (blk_disj hz hp (by omega)) (by omega)).trans p₁) (u₂.trans u₁) e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨scr s₀, P.so⟩, by simp, fun _ h => h⟩
  · exact sub_body (by omega) (by omega)
  · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- The end of a step: the digest into the block, `T ← T ⊕ U` and the count. -/
theorem tail_ok {H : Md P.B P.N P.L} (hs : Shape H) {s : State} (h : Regs P D W s₀ s)
    (hpad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {Q : State → Prop}
    (k : ∀ s', Regs P D W s₀ s' → s'.gpr .r14 = s.gpr .r14 - (1 : BitVec 32).signExtend 64 →
      s'.zf = some (s.gpr .r14 - (1 : BitVec 32).signExtend 64 == 0) →
      Frame (bodyR P D s₀) s.mem s'.mem →
      bytesAt s'.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (blk P s₀) D = (H.digest (H.stateAt s.mem (hv P s₀))).take D →
      bytesAt s'.mem (tp s₀) D =
        Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp s₀) D) ((H.digest (H.stateAt s.mem (hv P s₀))).take D) → Q s') :
    WP isa (.block (Impl.Pbkdf2.X86_64.digest P D ++ (List.range (D / 4)).flatMap xorW ++
      ([.alu .sub .r14 (.imm 1)] : List Instr))) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.D4; have := hz.W
  have := hz.pad; have := hz.NL
  rw [List.append_assoc]
  refine digest_ok hz hp hs h hpad fun s₆ g₆ rd₆ wr₆ f₆ b₆ p₆ => ?_
  have h₆ := h.write (fun r hr _ _ _ _ _ => g₆ r hr) rd₆ wr₆ (frame_scr (a := P.so + 48 + P.N) (by omega) f₆)
  have hd : Region.Disjoint (tR D s₀) ⟨blk P s₀, D⟩ := hp.t_s.sub_right (scr_sub s₀ (by omega))
  have hD4 : 4 * (D / 4) = D := by omega
  refine xor_ok hd (by omega) (D / 4) (by omega) _ s₆ _ h₆.rbp h₆.r13
    (fun j hj => by
      obtain ⟨r, hr, hc⟩ := in_blk hz hp h₆.wr (a := 4 * j) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun j hj => ⟨tR D s₀, by simp [h₆.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  rw [hD4] at m₇
  have hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₆.mem (tp s₀) D) (bytesAt s₆.mem (blk P s₀) D)).length = D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have f₇ : Frame [tR D s₀] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  have h₇ := h₆.write (fun r hr _ _ _ _ _ => g₇ r hr) rd₇ wr₇ (f₇.mono (by simp))
  refine wp_subi fun s₈ u₈ z₈ => WP.block_nil ?_
  have h₈ := h₇.write (fun r _ _ _ _ _ hr => u₈.other r hr) u₈.rd u₈.wr (by rw [u₈.mem]; exact Frame.refl _ _)
  have r14₇ : s₇.gpr .r14 = s.gpr .r14 := by rw [g₇ _ (by decide), g₆ _ (by decide)]
  have hT₆ : bytesAt s₆.mem (tp s₀) D = bytesAt s.mem (tp s₀) D :=
    Memory.frame_bytesAt f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.sub_right (scr_sub s₀ (a := P.so + 48 + P.N) (n := P.N) (by omega))) (by omega)
  refine k s₈ h₈ (by rw [u₈.gpr, r14₇]) (by rw [z₈, r14₇]) ?_ ?_ ?_ ?_
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
    (hf : CalleeOk H code) {r : Nat} {s : State} (h : Inv P D W H s₀ (r + 1) s) :
    WP isa (body P D name code) s fun s' => eval .ne s' = some (r != 0) ∧ Inv P D W H s₀ r s' := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  unfold body
  refine WP.seq (lc_ok hz hp hR hf (o := 0) (by omega) h.toRegs h.pad fun s₂ h₂ r14₂ f₂ g₂ p₂ _ e₂ => ?_)
  refine WP.seq (digest_ok hz hp hs h₂ p₂ fun s₃ g₃ rd₃ wr₃ f₃ b₃ p₃ => ?_)
  have h₃ := h₂.write (fun r hr _ _ _ _ _ => g₃ r hr) rd₃ wr₃ (frame_scr (a := P.so + 48 + P.N) (by omega) f₃)
  refine lc_ok hz hp hR hf (o := P.N + P.B) (by omega) h₃ p₃ fun s₅ h₅ r14₅ f₅ g₅ p₅ _ e₅ => ?_
  refine tail_ok hz hp hs h₅ p₅ fun s₈ h₈ r14₈ z₈ f₈ p₈ b₈ t₈ => ?_
  rw [e₅, b₃, e₂, show key s₀ + BitVec.ofNat 64 0 = key s₀ by simp] at b₈ t₈
  have r14₅' : s₅.gpr .r14 = BitVec.ofNat 64 (r + 1) := by
    rw [r14₅, g₃ _ (by decide), r14₂, h.r14]
  have hlt : r + 1 < 2 ^ 64 := by
    have := h.le; have := ((s₀.gpr .rdx).setWidth 32).isLt; simp at *; omega
  have e₈ : s₅.gpr .r14 - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 r := by
    rw [r14₅', show (1 : BitVec 32).signExtend 64 = 1 from rfl, ofNat_pred (by omega)]; rfl
  have fb : Frame (bodyR P D s₀) s.mem s₈.mem :=
    ((f₂.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_body (by omega) (by omega))).trans f₅).trans f₈
  have hT₅ : bytesAt s₅.mem (tp s₀) D = bytesAt s.mem (tp s₀) D := by
    refine Memory.frame_bytesAt (rs := [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N + P.B⟩, stkR s₀])
      (((g₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)).trans (g₅.sub fun r hr => ?_)) (fun r hr => ?_) (by omega)
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · subst hr; exact ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ (by omega) (by omega)⟩
    · rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · rcases hr with rfl | rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
      · exact hp.t_s.sub_right (scr_sub s₀ (by omega))
      · exact hp.stk_t.symm
  rw [hT₅] at t₈
  refine ⟨?_, h₈, by rw [r14₈, e₈], saved_frame hz hp h.saved fb, p₈, by have := h.le; omega, ?_⟩
  · simp only [eval, z₈, e₈, Option.map_some, ofNat_beq_zero (by omega : r < 2 ^ 64)]
    cases r <;> rfl
  · rw [h.val, iterate_succ, b₈, t₈]; rfl
theorem loop_ok {H : Md P.B P.N P.L} (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa}
    (hf : CalleeOk H code) {n : Nat} {s : State} (h : Inv P D W H s₀ n s) (hz' : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop (body P D name code) .ne)) s (Inv P D W H s₀ 0) := by
  refine WP.ite (decide (n = 0)) hz' (fun hb => ?_) (fun hb => ?_)
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

/-- After saving our caller's registers and setting up ours. -/
structure Setup (P : Params) (D W : Nat) (s₀ s : State) : Prop extends Regs P D W s₀ s where
  r14 : s.gpr .r14 = BitVec.ofNat 64 (nn s₀)
  rdi : s.gpr .rdi = key s₀
  rsi : s.gpr .rsi = up s₀
  mem : s.mem = saveMem P s₀ .r8

section
variable {P : Params} {D W : Nat} (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀)
include hz hp

theorem setup_ok {rest : List Instr} {Q : State → Prop} (k : ∀ s, Setup P D W s₀ s → WP isa (.block rest) s Q) :
    WP isa (.block (save P .r8 ++
      ([.mov .r15 (.reg .r8), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rcx), .mov32 .r14 (.reg .rdx),
        .mov .rbx (.reg .r8), .alu .add .rbx (.imm (BitVec.ofNat 32 (hvO P))),
        .mov .rbp (.reg .r8), .alu .add .rbp (.imm (BitVec.ofNat 32 (blkO P)))] : List Instr) ++ rest)) s₀ Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.W
  have o : ∀ d : Nat, d + 8 ≤ 8 * W → InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => by rw [ofInt_natCast]; exact in_scr hz hp rfl hd
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so : Nat) : Int)) rfl (o _ (by omega))
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) (by simp only [State.ea, at_, g₁])
    (by rw [wr₁]; exact o _ (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int))
    (by simp only [State.ea, at_, g₂, g₁]) (by rw [wr₂, wr₁]; exact o _ (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int))
    (by simp only [State.ea, at_, g₃, g₂, g₁]) (by rw [wr₃, wr₂, wr₁]; exact o _ (by omega))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int))
    (by simp only [State.ea, at_, g₄, g₃, g₂, g₁])
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int))
    (by simp only [State.ea, at_, g₅, g₄, g₃, g₂, g₁])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have hg₆ : s₆.gpr = s₀.gpr := by rw [g₆, g₅, g₄, g₃, g₂, g₁]
  have hm₆ : s₆.mem = saveMem P s₀ .r8 := by
    rw [m₆, m₅, m₄, m₃, m₂, m₁]; simp only [saveMem, g₅, g₄, g₃, g₂, g₁]
  refine wp_mov fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ => wp_mov fun s₉ u₉ _ _ => wp_mov32r fun s₁₀ u₁₀ =>
    wp_mov fun s₁₁ u₁₁ _ _ => wp_addi fun s₁₂ u₁₂ => wp_mov fun s₁₃ u₁₃ _ _ => wp_addi fun s₁₄ u₁₄ => ?_
  have G : ∀ r, r ≠ .r15 → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .rbx → r ≠ .rbp → s₁₄.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [u₁₄.other r h6, u₁₃.other r h6, u₁₂.other r h5, u₁₁.other r h5, u₁₀.other r h4, u₉.other r h3,
        u₈.other r h2, u₇.other r h1, hg₆]
  have hm : s₁₄.mem = saveMem P s₀ .r8 := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]
  refine k s₁₄ ⟨⟨by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁], ?_, ?_,
    ?_, ?_, ?_, G _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩, ?_,
    G _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    G _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hm⟩
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), hg₆, hvO, sx_ofNat (by omega)]
  · rw [u₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), hg₆, blkO, sx_ofNat (by omega)]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), hg₆]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, hg₆]
  · rw [hm]; exact (saveMem_frame hz.dims).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR W s₀, by simp, Region.sub_prefix (by omega)⟩
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
    apply BitVec.eq_of_toNat_eq
    have := ((s₀.gpr .rdx).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, nn]

/-- Writing `U`, the padding and the length field into the block. -/
theorem fill_ok {H : Md P.B P.N P.L} (hs : Shape H) (hok : H.lenOk (P.B + D)) {s : State}
    (h : Setup P D W s₀ s) :
    WP isa (.block ((List.range (D / 4)).flatMap (Impl.Hmac.X86_64.cp32 .rsi .rbp 0 0) ++
      padFrom D (P.B - P.L) ++ ([.mov32 .r12 (.imm (BitVec.ofNat 32 (P.B + D)))] : List Instr) ++ P.len ++
      ([.mov .r12 (.reg .rdi), .alu .test .r14 (.reg .r14)] : List Instr))) s
      fun s' => Inv P D W H s₀ (nn s₀) s' ∧ s'.zf = some (decide (nn s₀ = 0)) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL; have := hz.D4; have := hz.L4; have := hz.W; have := B_ge hz
  have : P.B % 4 = 0 := by rcases hz.dims.B with h | h <;> omega
  have hD4 : 4 * (D / 4) = D := by omega
  have u0 : up s₀ + BitVec.ofNat 64 0 = up s₀ := by simp
  simp only [List.append_assoc]
  refine copy32_ok (by decide) (by decide) 0 0 (D / 4) _ s _ (fun j hj => ?_) (fun j hj => ?_) ?_ (by omega)
    fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · rw [h.rsi, h.rd, hp.rd, u0]
    exact ⟨uR D s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.rbp, blk0]; exact in_blk hz hp h.wr (by omega)
  · rw [h.rsi, h.rbp, blk0, u0, hD4]
    exact hp.u_s.sep (Region.contains_self _ _) (Offset.contains_base _ (by omega) (by omega))
  rw [h.rbp, h.rsi, blk0, u0, hD4] at m₁
  refine padFrom_ok (a := D) (b := P.B - P.L) (by omega) (by omega) (by omega) (s := s₁) (p := blk P s₀)
    (by rw [g₁ _ (by decide), h.rbp]) (fun j hj => in_blk hz hp (wr₁.trans h.wr) (by omega))
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  refine wp_mov32i fun s₃ u₃ _ _ => ?_
  have rbx₃ : s₃.gpr .rbx = hv P s₀ := by rw [u₃.other _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.rbx]
  have ea : hv P s₀ + BitVec.ofNat 64 (P.N + P.B - P.L) = blk P s₀ + BitVec.ofNat 64 (P.B - P.L) := by
    rw [add_ofNat, add_ofNat, show P.so + 48 + (P.N + P.B - P.L) = P.so + 48 + P.N + (P.B - P.L) by omega]
  change WP isa (.block (P.len ++ [.mov .r12 (.reg .rdi), .alu .test .r14 (.reg .r14)])) s₃ _
  rw [WP.block_append_iff]
  refine WP.mono (hs.len s₃ ?_) fun s₄ ⟨g₄, rd₄, wr₄, m₄⟩ => ?_
  · rw [rbx₃, ea]; exact in_blk hz hp (u₃.wr.trans (wr₂.trans (wr₁.trans h.wr))) (by omega)
  refine wp_mov fun s₅ u₅ _ _ => wp_test fun s₆ g₆ m₆ rd₆ wr₆ z₆ => WP.block_nil ?_
  rw [rbx₃, ea, u₃.gpr, zx_ofNat (by omega), H.lenOf_eq _ hok] at m₄
  -- The memory.
  have hM : s₆.mem = writeBytes (writeBytes (writeBytes (saveMem P s₀ .r8) (blk P s₀)
      (bytesAt (saveMem P s₀ .r8) (up s₀) D)) (blk P s₀ + BitVec.ofNat 64 D)
      ([0x80] ++ List.replicate (P.B - P.L - D - 1) 0)) (blk P s₀ + BitVec.ofNat 64 (P.B - P.L))
      (H.lenBytes (P.B + D)) := by
    rw [m₆, u₅.mem, m₄, u₃.mem, m₂, m₁, h.mem]
  have hG : ∀ r, r ≠ .rax → r ≠ .r12 → s₆.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₆, u₅.other r h2, g₄ r h1, u₃.other r h2, g₂ r h1, g₁ r h1]
  have lpz : ([0x80] ++ List.replicate (P.B - P.L - D - 1) 0 : List Byte).length = P.B - P.L - D := by simp; omega
  have fM : Frame [⟨blk P s₀, P.B⟩] s.mem s₆.mem := by
    rw [hM, ← h.mem]
    refine ((writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)).trans (writeBytes_frame _ _ _ ?_)
    · rw [bytesAt_length]
      have := Offset.contains_base (blk P s₀) (d := 0) (n := D) (k := P.B) (by omega) (by omega)
      rwa [blk0] at this
    · rw [lpz]; exact Offset.contains_base _ (by omega) (by omega)
    · rw [H.lenBytes_length]; exact Offset.contains_base _ (by omega) (by omega)
  have fB : Frame (bodyR P D s₀) s.mem s₆.mem := fM.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_body (by omega) (by omega)
  have S1 : Mem.Sep (blk P s₀) D (blk P s₀ + BitVec.ofNat 64 D) (P.B - P.L - D) := by
    have := blk_sep P s₀ (a := 0) (n := D) (b := D) (k := P.B - P.L - D) (.inl (by omega)) (by omega)
      (by omega) (by omega)
    rwa [blk0] at this
  have S2 : ∀ {a n : Nat}, a + n ≤ P.B - P.L →
      Mem.Sep (blk P s₀ + BitVec.ofNat 64 a) n (blk P s₀ + BitVec.ofNat 64 (P.B - P.L)) P.L :=
    fun h' => blk_sep P s₀ (.inl h') (by omega) (by omega) (by omega)
  refine ⟨⟨⟨by rw [rd₆, u₅.rd, rd₄, u₃.rd, rd₂, rd₁, h.rd], by rw [wr₆, u₅.wr, wr₄, u₃.wr, wr₂, wr₁, h.wr],
    by rw [hG _ (by decide) (by decide), h.rbx], by rw [hG _ (by decide) (by decide), h.rbp],
    by rw [g₆, u₅.gpr, g₄ _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.rdi],
    by rw [hG _ (by decide) (by decide), h.r13], by rw [hG _ (by decide) (by decide), h.r15],
    by rw [hG _ (by decide) (by decide), h.rsp], h.frame.trans (frame_scr (a := P.so + 48 + P.N) (by omega) fM)⟩,
    by rw [hG _ (by decide) (by decide), h.r14], saved_frame hz hp (h.mem ▸ saveMem_saved hz.dims) fB, ?_,
    Nat.le_refl _, ?_⟩, ?_⟩
  · -- The padding and the length field.
    rw [show P.B - D = (P.B - P.L - D) + P.L by omega, bytesAt_add, add_ofNat (blk P s₀),
      show D + (P.B - P.L - D) = P.B - P.L by omega, hM,
      bytesAt_writeBytes_self' (H.lenBytes_length _) (by omega),
      bytesAt_writeBytes_sep _ _ (by rw [H.lenBytes_length]; exact S2 (by omega)) (by omega),
      bytesAt_writeBytes_self' lpz (by omega), Md.tailPad, show P.B - P.L - 1 - D = P.B - P.L - D - 1 by omega]
  · -- `U` and `T`.
    have hU : bytesAt s₆.mem (blk P s₀) D = bytesAt s₀.mem (up s₀) D := by
      rw [hM, bytesAt_writeBytes_sep _ _ (by
          rw [H.lenBytes_length]; have := S2 (a := 0) (n := D) (by omega); rwa [blk0] at this) (by omega),
        bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (by omega),
        bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
      refine Memory.frame_bytesAt (saveMem_frame hz.dims) (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.u_s.sub_right (Region.sub_prefix (by omega))
    have hT : bytesAt s₆.mem (tp s₀) D = bytesAt s₀.mem (tp s₀) D := by
      refine Memory.frame_bytesAt (((saveMem_frame (s₀ := s₀) (b := .r8) hz.dims).mono
        (rs' := [⟨scr s₀, P.so + 48⟩, ⟨blk P s₀, P.B⟩]) (by simp)).trans
        ((h.mem ▸ fM).mono (by simp))) (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
      · exact hp.t_s.sub_right (scr_sub s₀ (by omega))
    rw [hU, hT]
  · have r14₅ : s₅.gpr .r14 = BitVec.ofNat 64 (nn s₀) := by
      rw [u₅.other _ (by decide), g₄ _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), g₁ _ (by decide),
        h.r14]
    rw [z₆, r14₅, BitVec.and_self, ofNat_beq_zero (by have := ((s₀.gpr .rdx).setWidth 32).isLt; simp [nn]; omega)]
theorem prologue_ok {H : Md P.B P.N P.L} (hs : Shape H) (hok : H.lenOk (P.B + D)) :
    WP isa (.block (prologue P D)) s₀ fun s => Inv P D W H s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)) := by
  have := setup_ok hz hp (rest := (List.range (D / 4)).flatMap (Impl.Hmac.X86_64.cp32 .rsi .rbp 0 0) ++
    padFrom D (P.B - P.L) ++ [.mov32 .r12 (.imm (BitVec.ofNat 32 (P.B + D)))] ++ P.len ++
    [.mov .r12 (.reg .rdi), .alu .test .r14 (.reg .r14)]) fun s h => fill_ok hz hp hs hok h
  unfold prologue
  simpa only [List.append_assoc] using this

set_option simprocs false in
/-- Restoring our caller's registers from the scratch space. -/
theorem restore_ok {s : State} (hwr : s.wr = s₀.wr) (h15 : s.gpr .r15 = scr s₀)
    (hsv : Saved P s₀ .r8 s.mem) :
    WP isa (.block (restore P)) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .rsp = s.gpr .rsp ∧ ∀ r ∈ calleeSaved, r ≠ .rsp → s'.gpr r = s₀.gpr r := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.W
  have i : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => by
      rw [ofInt_natCast]
      obtain ⟨r, hr, hc⟩ := in_scr hz hp hwr (a := d) (n := 8) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have sv : ∀ r d, (r, d) ∈ saved P →
      s.mem.readW (scr s₀ + BitVec.ofInt 64 ((d : Nat) : Int)) 64 = s₀.gpr r :=
    fun r d hrd => hsv (r, d) hrd
  have i0 := i P.so (by omega); have i1 := i (P.so + 8) (by omega); have i2 := i (P.so + 16) (by omega)
  have i3 := i (P.so + 24) (by omega); have i4 := i (P.so + 32) (by omega); have i5 := i (P.so + 40) (by omega)
  have g0 := sv .rbx P.so (by simp only [saved, List.mem_cons, true_or]); have g1 := sv .rbp (P.so + 8) (by simp only [saved, List.mem_cons, true_or, or_true])
  have g2 := sv .r12 (P.so + 16) (by simp only [saved, List.mem_cons, true_or, or_true]); have g3 := sv .r13 (P.so + 24) (by simp only [saved, List.mem_cons, true_or, or_true])
  have g4 := sv .r14 (P.so + 32) (by simp only [saved, List.mem_cons, true_or, or_true]); have g5 := sv .r15 (P.so + 40) (by simp only [saved, List.mem_cons, true_or, or_true])
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, h15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, by simp (config := {decide := true}), fun r hr hne => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) at hne ⊢

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
    WP isa (.block (restore P)) s fun s' => gprPreserved s₀ s' ∧ (iterK S W).post s₀ s' := by
  refine WP.mono (restore_ok hz hp h.wr h.r15 h.saved) fun s' ⟨hm, hsp, hcs⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun k0 hk hi ho => ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [hsp, h.rsp]
    · exact hcs r hr hr'
  · rw [hm]
    exact h.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_t, hp.ret_s, ret_stk s₀⟩) (by decide)
  · rw [hm]; exact post_eq hl h.val.symm hk hi ho
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

theorem correct {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P D W s₀) :
    WP isa (iterate P D name code) s₀ fun s' => gprPreserved s₀ s' ∧ (iterK S W).post s₀ s' := by
  unfold iterate
  refine WP.seq (WP.mono (prologue_ok ho.sizes hp ho.shape ho.lenOk) fun s₁ ⟨h, hz'⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok ho.sizes hp ho.shape ho.reloc hf h hz') fun s₂ h₂ =>
    epilogue_ok ho.sizes hp ho.link h₂)

/-- `iterate` is correct and keeps what the calling convention requires, if it
never loads MXCSR. -/
theorem iterate_ok {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (iterate P D name code).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (iterK S W).pre s) :
    ∃ t s', Exec isa (iterate P D name code) s t s' ∧ abiPreserved s s' ∧ (iterK S W).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct ho hf (pre_of ho.link.hS ho.link.hD hs)
  exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2⟩

end VG.Proof.Pbkdf2.X86_64
