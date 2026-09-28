import VerifiedGarbage.Proof.Sha256.Arm.Stream.Update
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common

/-!
# Streaming SHA-256 on ARMv7: `finalize`

Untrusted: everything here is checked by Lean. The same structure as the
AArch64 proof (`VG.Proof.Sha256.AArch64.Stream.Finalize`), with `state` in
`r0`, `scratch` in `r3`, `out` in `r6`, `count` in `r4:r5` (low, high), the
buffered bytes in `r7`, and whether the block is not the last in `r8`.
-/

namespace VG.Proof.Sha256.Arm.Stream.Finalize

open VG VG.Arm VG.Impl.Sha256.Arm.Stream
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.Sha256.Arm.Stream
open VG.Proof.Sha256.Arm.Stream.Update (addr_off addr_toNat cmp0)
open VG.Proof.Sha256.Stream
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes countArm)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev cnt : Nat := (countArm s₀).toNat
abbrev out : BitVec 32 := stackArg s₀ 0
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev stA : Addr := State.addr (st s₀)
abbrev outA : Addr := State.addr (out s₀)
abbrev scA : Addr := State.addr (scr s₀)
abbrev stR : Region := ⟨stA s₀, 96⟩
abbrev outR : Region := ⟨outA s₀, 32⟩
abbrev scR : Region := ⟨scA s₀, 160⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩

/-- The messages the initial state represents. -/
def R₀ (m : List Byte) : Prop :=
  Spec.Sha256.Repr s₀.mem (stA s₀) m ∧ countArm s₀ = BitVec.ofNat 64 m.length

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

/-- The digest, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (compress (stateAt mem (stA s₀))
    (parseBlock fun t => (bytesAt mem (stA s₀ + 32) n ++ List.replicate (64 - n) 0).getD t 0))
    (parseBlock fun t => (List.replicate 56 0 ++ lenBytes m).getD t 0)

/-- The digest, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (stateAt mem (stA s₀))
    (parseBlock fun t => (bytesAt mem (stA s₀ + 32) n ++ List.replicate (56 - n) 0 ++ lenBytes m).getD t 0)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀, outR s₀, scR s₀]
  st_out : (stR s₀).Disjoint (outR s₀)
  st_scr : (stR s₀).Disjoint (scR s₀)
  out_scr : (outR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_out : (argR s₀).Disjoint (outR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 96 ≤ 2 ^ 32
  out_fit : (out s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 160 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Spec.Sha256.finalizeArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem cnt_mod (s₀ : State) : cnt s₀ % 64 = (s₀.gpr .r2).toNat % 64 := by
  simp only [cnt, countArm]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {m : List Byte} (h : R₀ s₀ m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem st_add (s₀ : State) (n : Nat) :
    stA s₀ + 32 + BitVec.ofNat 64 n = stA s₀ + BitVec.ofNat 64 (32 + n) := by
  simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

/-! ## Invariants -/

structure Common (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  r6 : s.gpr .r6 = out s₀
  r4 : s.gpr .r4 = s₀.gpr .r2
  r5 : s.gpr .r5 = s₀.gpr .r3
  lr : s.gpr .lr = s₀.gpr .lr
  sp : s.sp = s₀.sp
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (s₀ : State) (k n : Nat) (s : State) : Prop extends Common s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 56 + 8 * k
  r7 : s.gpr .r7 = BitVec.ofNat 32 n
  r8 : s.gpr .r8 = BitVec.ofNat 32 k
  hash : ∀ m, R₀ s₀ m → Spec.Sha256.hash m =
    (if k = 1 then Fin1 s₀ s.mem n m else Fin0 s₀ s.mem n m).toList.flatMap wordBytes

/-- All blocks are compressed. -/
def Done (s₀ : State) (s : State) : Prop :=
  Common s₀ s ∧ ∀ m, R₀ s₀ m → Spec.Sha256.hash m = (stateAt s.mem (stA s₀)).toList.flatMap wordBytes

def keepRegs : List Reg := [.r0, .r3, .r6, .r4, .r5, .lr]

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common s₀ s)
    (hg : ∀ r ∈ keepRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r0 := by rw [hg _ (by simp [keepRegs])]; exact h.r0
  r3 := by rw [hg _ (by simp [keepRegs])]; exact h.r3
  r6 := by rw [hg _ (by simp [keepRegs])]; exact h.r6
  r4 := by rw [hg _ (by simp [keepRegs])]; exact h.r4
  r5 := by rw [hg _ (by simp [keepRegs])]; exact h.r5
  lr := by rw [hg _ (by simp [keepRegs])]; exact h.lr
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Common.of_upd {s₀ : State} {s s' : State} (h : Common s₀ s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ keepRegs) : Common s₀ s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Common.of_flags {s₀ : State} {s s' : State} (h : Common s₀ s) (u : Fupd s s') : Common s₀ s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- Where the caller's registers are saved. -/
theorem saved_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (scR s₀) := by
  simp only [Impl.Sha256.Arm.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact sub_offset (by omega) (by omega)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf {s₀ : State} (hp : Pre s₀) {s : State} (h : Common s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ 64) :
    Frame [stR s₀] s.mem (writeBytes s.mem (stA s₀ + 32 + BitVec.ofNat 64 n) xs) ∧
      Frame [stR s₀, scR s₀] s₀.mem (writeBytes s.mem (stA s₀ + 32 + BitVec.ofNat 64 n) xs) ∧
      Saved s₀ (writeBytes s.mem (stA s₀ + 32 + BitVec.ofNat 64 n) xs) := by
  have hf : Frame [stR s₀] s.mem (writeBytes s.mem (stA s₀ + 32 + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [st_add]
    exact contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (saved_sub hp')

/-- Byte `k` of the buffer, addressed as `[r0 + k, #32]`. -/
theorem buf_addr {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 64) :
    State.addr (st s₀ + BitVec.ofNat 32 k + BitVec.ofNat 32 32) = stA s₀ + 32 + BitVec.ofNat 64 k := by
  have := hp.st_fit
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_off (by omega), Nat.add_comm, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  rfl

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ .r8 :: keepRegs, s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  r12 : s.gpr .r12 = 0
  r7 : s.gpr .r7 = BitVec.ofNat 32 (n + j)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (stA s₀ + 32 + BitVec.ofNat 64 n) (List.replicate j 0)

/-- The zeroing loop's body. -/
def zeroBody : List Instr :=
  [.dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 32, .dp .add .r7 .r7 (.imm 1), .subs .r9 .r9 (.imm 1)]

theorem zero_step {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ 64) (hj : j < lim - n) {s : State} (h : Zero s₀ sI n lim j s) :
    WP isa (.block zeroBody) s fun s' =>
      Zero s₀ sI n lim (j + 1) s' ∧ s'.z = (BitVec.ofNat 32 (lim - n - (j + 1)) == 0) := by
  have hr0 : s.gpr .r0 = st s₀ := by rw [h.keep _ (by simp [keepRegs]), hC.r0]
  have hout : InRegions s.wr (stA s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [show stA s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j = stA s₀ + BitVec.ofNat 64 (32 + n + j) by
      simp only [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  unfold zeroBody
  refine wp_add (op2_reg _ _) fun s₁ u₁ =>
    wp_strb (a := stA s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by omega) ?_
      (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hr0, h.r7, buf_addr hp (by omega)]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ =>
    WP.block_nil ⟨⟨by omega, fun r hr => ?_, by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd],
    by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr], by rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .r9 ∧ r ≠ .r7 ∧ r ≠ .r1 := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other r this.1, u₃.other r this.2.1, g₂.gpr, u₁.other r this.2.2, h.keep r hr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r12]
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r9,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide), h.r12, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [z₄, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r9,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) {n lim : Nat}
    (hlim : lim ≤ 64) (hn : n ≤ lim) {s : State} (h : Zero s₀ sI n lim 0 s)
    (hz : s.z = decide (lim - n = 0)) :
    WP isa (.ite .eq (.block []) (.loop (.block zeroBody) .ne)) s (Zero s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) (by show VG.Arm.eval .eq s = _; rw [eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hp hC hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    have hz'' : isa.eval .ne s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
      show VG.Arm.eval .ne s' = _
      rw [eval_ne, hz', ofNat_beq_zero (by omega)]
      simp
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by rw [hz'', decide_eq_false fun h => h hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by rw [hz'', decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The inlined compression of the buffer. -/
theorem compress_buf {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s)
    (hr1 : s.gpr .r1 = st s₀ + BitVec.ofNat 32 32) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      stateAt s'.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (blockAt s.mem (stA s₀ + 32)) → Q s') :
    WP isa compressAt s Q := by
  have hst := hp.st_fit; have hsc := hp.scr_fit
  have e32 : Region.Sub ⟨stA s₀, 32⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e112 : Region.Sub ⟨scA s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  have ha : State.addr (st s₀ + BitVec.ofNat 32 32) = stA s₀ + 32 := addr_off (by omega)
  have eb : Region.Sub ⟨stA s₀ + 32, 64⟩ (stR s₀) := sub_offset (off := 32) (by omega) (by omega)
  have d₂ : Region.Disjoint ⟨State.addr (st s₀ + BitVec.ofNat 32 32), 64⟩ ⟨stA s₀, 32⟩ := by
    rw [ha]; intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  have d₃ : Region.Disjoint ⟨State.addr (st s₀ + BitVec.ofNat 32 32), 64⟩ ⟨scA s₀, 112⟩ := by
    rw [ha]; exact (hp.st_scr.sub_left eb).sub_right e112
  refine compressAt_ok hC.r0 hC.r3 hr1 (by omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by omega) ((hp.st_scr.sub_left e32).sub_right e112) d₂ d₃
    ?_ ?_ fun s' hrd hwr hcs h0 h3 hsp hf hstate => hQ s' ?_ hcs (by rw [hstate, ha])
  · rw [hC.rd, hC.wr, hp.rd, hp.wr, ha]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 32, rfl, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, h0, h3, by rw [hcs _ (by decide)]; exact hC.r6,
      by rw [hcs _ (by decide)]; exact hC.r4, by rw [hcs _ (by decide)]; exact hC.r5,
      by rw [hcs _ (by decide)]; exact hC.lr, hsp.trans hC.sp, hC.frame.trans (hf.sub ?_), fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e112⟩
    · rw [← hC.saved p hp']
      refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hp')).sub_right e32
      · simp only [Impl.Sha256.Arm.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · intro a h₁ h₂; simp only [Region.Contains, scA] at h₁ h₂; bv_omega


/-! ## The message length -/

theorem writeW_rev (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (rev w) = writeBytes m a (wordBytes w) := by
  rw [Mem.writeW, write_eq_writeBytes, ← X86_64.Stream.bswap32_bytes']; rfl

/-! ## One block -/

/-- The loop's postcondition for one iteration. -/
def Step (s₀ : State) (k : Nat) (s : State) : Prop :=
  (VG.Arm.eval .eq s = some false ∧ Done s₀ s) ∨ (VG.Arm.eval .eq s = some true ∧ k = 1 ∧ LInv s₀ 0 0 s)

theorem body_eq : finalizeBody =
    .seq (.block [.mov .r9 (.imm 64), .cmp .r8 (.imm 0)])
    (.seq (.ite .eq (.block [.mov .r9 (.imm 56)]) (.block []))
    (.seq (.block [.mov .r12 (.imm 0), .subs .r9 .r9 (.reg .r7)])
    (.seq (.ite .eq (.block []) (.loop (.block zeroBody) .ne))
    (.seq (.block [.cmp .r8 (.imm 0)])
    (.seq (.ite .eq
        (.block [.mov .r9 (.shifted .r5 .lsl 3), .dp .orr .r9 .r9 (.shifted .r4 .lsr 29), .rev .r9 .r9,
          .str .r9 .r0 88, .mov .r9 (.shifted .r4 .lsl 3), .rev .r9 .r9, .str .r9 .r0 92])
        (.block []))
    (.seq (.block [.dp .add .r1 .r0 (.imm 32)])
    (.seq compressAt (.block [.mov .r7 (.imm 0), .subs .r8 .r8 (.imm 1)])))))))) := rfl

set_option maxHeartbeats 4000000 in
theorem body_ok {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) :
    WP isa finalizeBody s (Step s₀ k) := by
  have hk := h.k_le; have hn := h.n_le; have hst := hp.st_fit
  have hC := h.toCommon
  rw [body_eq]
  -- `r9 := 64` or `56`: the end of the zeros.
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  have hz₂ : s₂.z = decide (k = 0) := by rw [z₂, u₁.other _ (by decide), h.r8, cmp0 (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .r9 = BitVec.ofNat 32 (56 + 8 * k) ∧
      (∀ r, r ≠ .r9 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.sp = s.sp) ?_ fun s₃ ⟨h9₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show VG.Arm.eval .eq s₂ = _; rw [eval_eq, hz₂])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr]; rfl, fun r hr => ?_,
        by rw [u₃.mem, f₂.mem, u₁.mem], by rw [u₃.rd, f₂.rd, u₁.rd], by rw [u₃.wr, f₂.wr, u₁.wr],
        by rw [u₃.sp, f₂.sp, u₁.sp]⟩
      rw [u₃.other r hr, f₂.gpr, u₁.other r hr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [f₂.gpr, u₁.gpr, show k = 1 by omega]; rfl, fun r hr => ?_,
        by rw [f₂.mem, u₁.mem], by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr], by rw [f₂.sp, u₁.sp]⟩
      rw [f₂.gpr, u₁.other r hr]
  -- Zero the rest of the buffer, up to `lim`.
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_subs (op2_reg _ _) fun s₅ u₅ z₅ =>
    WP.block_nil ?_)
  have h9₅ : s₅.gpr .r9 = BitVec.ofNat 32 (56 + 8 * k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), h9₃, u₄.other _ (by decide), g₃ _ (by decide), h.r7,
      sub_ofNat (by omega)]
  have hZ : Zero s₀ s n (56 + 8 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃],
      by rw [u₅.sp, u₄.sp, sp₃], ?_, ?_, by rw [h9₅, Nat.sub_zero], ?_⟩
    · have : r ≠ .r9 ∧ r ≠ .r12 := by
        simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.r7, Nat.add_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, writeBytes_nil]
  have hz₅ : s₅.z = decide (56 + 8 * k - n - 0 = 0) := by
    rw [z₅, ← u₅.gpr, h9₅, ofNat_beq_zero (by omega), Nat.sub_zero]
  refine WP.seq (WP.mono (zero_ok hp hC (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hp (n := n) (xs := List.replicate (56 + 8 * k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : Common s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r0],
      by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r3], by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r6],
      by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r4], by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r5],
      by rw [hZ₆.keep _ (by simp [keepRegs]), hC.lr], hZ₆.sp.trans hC.sp,
      by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : stateAt s₆.mem (stA s₀) = stateAt s.mem (stA s₀) := by
    rw [hZ₆.mem]
    apply stateAt_congr
    intro i hi
    rw [st_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (stA s₀ + 32) (56 + 8 * k) =
      bytesAt s.mem (stA s₀ + 32) n ++ List.replicate (56 + 8 * k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h8₆ : s₆.gpr .r8 = BitVec.ofNat 32 k := by rw [hZ₆.keep _ (by simp [keepRegs]), h.r8]
  -- In the last block, the length.
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_)
  have hC₇ := hC₆.of_flags f₇
  have h8₇ : s₇.gpr .r8 = BitVec.ofNat 32 k := by rw [f₇.gpr, h8₆]
  have hz₇ : s₇.z = decide (k = 0) := by rw [z₇, h8₆, cmp0 (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common s₀ s₈ ∧ s₈.gpr .r8 = BitVec.ofNat 32 k ∧
      stateAt s₈.mem (stA s₀) = stateAt s.mem (stA s₀) ∧
      ∀ m, R₀ s₀ m → bytesAt s₈.mem (stA s₀ + 32) 64 = bytesAt s.mem (stA s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)) ?_
    fun s₈ ⟨hC₈, h8₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show VG.Arm.eval .eq s₇ = _; rw [eval_eq, hz₇])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have hout : ∀ o, o + 4 ≤ 96 → InRegions s₇.wr (stA s₀ + BitVec.ofNat 64 o) 4 := fun o ho =>
        ⟨stR s₀, by simp [hC₇.wr, hp.wr], contains_offset (by omega) (by omega)⟩
      refine wp_mov (op2_lsl (by decide)) fun s₈ u₈ => wp_orr (op2_lsr (by decide)) fun s₉ u₉ =>
        wp_rev fun s₁₀ u₁₀ => wp_str (a := stA s₀ + BitVec.ofNat 64 88) (by decide) ?_ ?_ fun s₁₁ g₁₁ =>
        wp_mov (op2_lsl (by decide)) fun s₁₂ u₁₂ => wp_rev fun s₁₃ u₁₃ =>
        wp_str (a := stA s₀ + BitVec.ofNat 64 92) (by decide) ?_ ?_ fun s₁₄ g₁₄ => WP.block_nil ?_
      · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), hC₇.r0,
          addr_off (by omega)]
      · rw [u₁₀.wr, u₉.wr, u₈.wr]; exact hout 88 (by omega)
      · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), g₁₁.gpr, u₁₀.other _ (by decide),
          u₉.other _ (by decide), u₈.other _ (by decide), hC₇.r0, addr_off (by omega)]
      · rw [u₁₃.wr, u₁₂.wr, g₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr]; exact hout 92 (by omega)
      have keep : ∀ r, r ≠ .r9 → s₁₄.gpr r = s₇.gpr r := fun r h => by
        rw [g₁₄.gpr, u₁₃.other r h, u₁₂.other r h, g₁₁.gpr, u₁₀.other r h, u₉.other r h, u₈.other r h]
      have hi : s₁₀.gpr .r9 = rev ((s₀.gpr .r3 <<< 3) ||| (s₀.gpr .r2 >>> 29)) := by
        rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₈.other _ (by decide), hC₇.r5, hC₇.r4]
      have hl : s₁₃.gpr .r9 = rev (s₀.gpr .r2 <<< 3) := by
        rw [u₁₃.gpr, u₁₂.gpr, g₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
          u₈.other _ (by decide), hC₇.r4]
      let L := wordBytes ((s₀.gpr .r3 <<< 3) ||| (s₀.gpr .r2 >>> 29)) ++ wordBytes (s₀.gpr .r2 <<< 3)
      have hw : s₁₄.mem = writeBytes s₇.mem (stA s₀ + 32 + BitVec.ofNat 64 56) L := by
        rw [g₁₄.mem, u₁₃.mem, u₁₂.mem, g₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, hl, hi, writeW_rev,
          writeW_rev, show stA s₀ + BitVec.ofNat 64 92 = stA s₀ + BitVec.ofNat 64 88 +
            BitVec.ofNat 64 (wordBytes ((s₀.gpr .r3 <<< 3) ||| (s₀.gpr .r2 >>> 29))).length by
            rw [BitVec.add_assoc]; rfl, writeBytes_append _ _ _ _ (by simp [wordBytes]),
          show stA s₀ + 32 + BitVec.ofNat 64 56 = stA s₀ + BitVec.ofNat 64 88 by rw [BitVec.add_assoc]; rfl]
      obtain ⟨-, hfr, hsv⟩ := hC₇.writeBuf hp (n := 56) (xs := L) (by simp [L, wordBytes])
      have kr : ∀ r ∈ keepRegs, s₁₄.gpr r = s₇.gpr r := fun r hr => keep r (by
        simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      have hC₁₄ : Common s₀ s₁₄ :=
        ⟨by rw [g₁₄.rd, u₁₃.rd, u₁₂.rd, g₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, hC₇.rd],
          by rw [g₁₄.wr, u₁₃.wr, u₁₂.wr, g₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, hC₇.wr],
          by rw [kr _ (by simp [keepRegs]), hC₇.r0], by rw [kr _ (by simp [keepRegs]), hC₇.r3],
          by rw [kr _ (by simp [keepRegs]), hC₇.r6], by rw [kr _ (by simp [keepRegs]), hC₇.r4],
          by rw [kr _ (by simp [keepRegs]), hC₇.r5], by rw [kr _ (by simp [keepRegs]), hC₇.lr],
          by rw [g₁₄.sp, u₁₃.sp, u₁₂.sp, g₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, hC₇.sp],
          by rw [hw]; exact hfr, by rw [hw]; exact hsv⟩
      refine ⟨hC₁₄, by rw [keep _ (by decide), h8₇], ?_, fun m hm => ?_⟩
      · rw [hw, ← hst₆, ← f₇.mem]
        apply stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by simp [L, wordBytes])
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        have e := bytesAt_writeBytes s₇.mem (stA s₀ + 32) 56 L (by simp [L, wordBytes])
        simp only [L, List.length_append, show ∀ w, (wordBytes w).length = 4 from fun _ => rfl] at e
        rw [hw, e, f₇.mem, hby₆, ← Proof.Sha256.Stream.lenBytes_halves _ _ m hm.2]
        simp [List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, h8₇, by rw [f₇.mem, hst₆], fun m _ => ?_⟩
      rw [f₇.mem, hby₆]; simp
  -- Compress the block.
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₉ u₉ => WP.block_nil ?_)
  have hC₉ : Common s₀ s₉ := hC₈.of_upd u₉ (by decide)
  have hr1 : s₉.gpr .r1 = st s₀ + BitVec.ofNat 32 32 := by rw [u₉.gpr, hC₈.r0]; rfl
  refine WP.seq (compress_buf hp hC₉ hr1 fun s₁₁ hC₁₁ cs₁₁ hst₁₁ => ?_)
  have h8₁₁ : s₁₁.gpr .r8 = BitVec.ofNat 32 k := by
    rw [cs₁₁ _ (by decide), u₉.other _ (by decide), h8₈]
  have hblk : ∀ m, R₀ s₀ m → blockAt s₉.mem (stA s₀ + 32) = parseBlock fun t =>
      (bytesAt s.mem (stA s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0 := by
    intro m hm
    apply parseBlock_congr
    intro t ht
    rw [u₉.mem]
    exact bytesAt_getD (hby₈ m hm) ht
  -- Next block, if any.
  refine wp_mov (op2_imm (by decide)) fun s₁₂ u₁₂ => wp_subs (op2_imm (by decide)) fun s₁₃ u₁₃ z₁₃ =>
    WP.block_nil ?_
  have hC₁₃ : Common s₀ s₁₃ := (hC₁₁.of_upd u₁₂ (by decide)).of_upd u₁₃ (by decide)
  have h8₁₃ : s₁₃.gpr .r8 = BitVec.ofNat 32 k - 1 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), h8₁₁]
  have hz : VG.Arm.eval .eq s₁₃ = some (decide (k = 1)) := by
    rw [eval_eq, z₁₃, u₁₂.other _ (by decide), h8₁₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by omega)]
  have hst : ∀ m, R₀ s₀ m → stateAt s₁₃.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (parseBlock fun t =>
      (bytesAt s.mem (stA s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0) := by
    intro m hm
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₉.mem, hst₈, ← hblk m hm, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by rw [hz]; simp, rfl, ⟨hC₁₃, by omega, by omega, ?_, ?_, fun m hm => ?_⟩⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]; rfl
    · rw [h8₁₃]; rfl
    · rw [h.hash m hm]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst m hm]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by rw [hz]; simp, hC₁₃, fun m hm => ?_⟩
    rw [h.hash m hm, hst m hm]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

/-! ## Prologue -/

/-- The prologue after saving. -/
def prologue : List Instr :=
  [.mov .r4 (.reg .r2), .mov .r5 (.reg .r3), .mov .r3 (.reg .r12), .ldrSp .r6 0, .dp .and .r7 .r4 (.imm 63),
    .mov .r12 (.imm 0x80), .dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 32, .dp .add .r7 .r7 (.imm 1),
    .dp .add .r8 .r7 (.imm 7), .mov .r8 (.shifted .r8 .lsr 6)]

/-- Word `k` of the digest. -/
def outW (k : Nat) : List Instr := [.ldr .r9 .r0 (4 * k), .rev .r9 .r9, .str .r9 .r6 (4 * k)]

theorem finalize_eq : finalize = .seq (.block ([.ldrSp .r12 4] ++ save .r12 ++ prologue))
    (.seq (.loop finalizeBody .eq) (.block ((List.range 8).flatMap outW ++ restore))) := rfl

theorem argAddr_eq {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_off (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_offset (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact sub_offset (by omega) (by omega)

set_option maxHeartbeats 4000000 in
theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ([.ldrSp .r12 4] ++ save .r12 ++ prologue)) s₀
      fun s => ∃ k, LInv s₀ k (cnt s₀ % 64 + 1) s := by
  have hr : cnt s₀ % 64 < 64 := Nat.mod_lt _ (by omega)
  have hsc := hp.scr_fit; have hst := hp.st_fit
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact contains_offset (by omega) (by omega)⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  have hframe : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]
    exact saveMem_frame _ _ _ saved fun p hp' => (saved_bound p hp').1
  unfold prologue
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide))
    fun s₆ u₆ => wp_and (op2_imm (by decide)) fun s₇ u₇ => ?_
  have hm₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have g₇ : ∀ r, r ∉ [Reg.r3, .r4, .r5, .r6, .r7, .r12] → s₇.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other r hr.2.2.2.2.1, u₆.other r hr.2.2.2.1, u₅.other r hr.1, u₄.other r hr.2.2.1,
      u₃.other r hr.2.1, g₂, u₁.other r hr.2.2.2.2.2]
  have hC₇ : Common s₀ s₇ := by
    refine ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
      g₇ _ (by decide), ?_, ?_, ?_, ?_, g₇ _ (by decide), by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp],
      by rw [hm₇]; exact hframe.mono (by simp), fun p hp' => ?_⟩
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        g₂, h12]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem]
      exact hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (arg_sub hp (by decide))))
        (by decide)
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, g₂, u₁.other _ (by decide)]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        g₂, u₁.other _ (by decide)]
    · rw [hm₇, m₂, u₁.mem, h12, saveMem_saved _ _ _ p hp', u₁.other]
      simp only [Impl.Sha256.Arm.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr7 : s₇.gpr .r7 = BitVec.ofNat 32 (cnt s₀ % 64) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂,
      u₁.other _ (by decide), and63, cnt_mod]
  -- The `0x80` byte.
  have hout : InRegions s₇.wr (stA s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) 1 := by
    refine ⟨stR s₀, by simp [hC₇.wr, hp.wr], ?_⟩
    rw [st_add]; exact contains_offset (by omega) (by omega)
  refine wp_mov (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_reg _ _) fun s₉ u₉ =>
    wp_strb (a := stA s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) (by omega) ?_
      (by rw [u₉.wr, u₈.wr]; exact hout) fun s₁₀ g₁₀ => ?_
  · rw [u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), hC₇.r0, hr7, buf_addr hp hr]
  obtain ⟨-, hfr, hsv⟩ := hC₇.writeBuf hp (n := cnt s₀ % 64) (xs := [0x80]) (by simp; omega)
  have hm₁₀ : s₁₀.mem = writeBytes s₇.mem (stA s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) [0x80] := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₉.other _ (by decide), u₈.gpr, ← List.nil_append [(0x80 : Byte)],
      writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  refine wp_add (op2_imm (by decide)) fun s₁₁ u₁₁ => wp_add (op2_imm (by decide)) fun s₁₂ u₁₂ =>
    wp_mov (op2_lsr (by decide)) fun s₁₃ u₁₃ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → r ≠ .r1 → s₁₃.gpr r = s₇.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₃.other r h2, u₁₂.other r h2, u₁₁.other r h1, g₁₀.gpr, u₉.other r h4, u₈.other r h3]
  have hm₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hC₁₃ : Common s₀ s₁₃ :=
    ⟨by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, hC₇.rd],
      by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, hC₇.wr],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r0],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r3],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r6],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r4],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r5],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.lr],
      by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, hC₇.sp],
      by rw [hm₁₃, hm₁₀]; exact hfr, by rw [hm₁₃, hm₁₀]; exact hsv⟩
  have hr7' : s₁₃.gpr .r7 = BitVec.ofNat 32 (cnt s₀ % 64 + 1) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), hr7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  have hr8 : s₁₃.gpr .r8 = BitVec.ofNat 32 ((cnt s₀ % 64 + 8) / 64) := by
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hr7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, show (7 : BitVec 32) = BitVec.ofNat 32 7 from rfl,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, Update.shr6 (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ m, R₀ s₀ m → bytesAt s₁₃.mem (stA s₀ + 32) (cnt s₀ % 64 + 1) = rest m ++ [0x80] := by
    intro m hm
    have e := bytesAt_writeBytes s₇.mem (stA s₀ + 32) (cnt s₀ % 64) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₃, hm₁₀, e, hm₇]
    congr 1
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := frame_bytes hframe (R := stR s₀) (by simpa using hp.st_scr) (by simp) (i := 32 + i)
      (by show 32 + i < 96; omega)
    rwa [← st_add] at this
  have hstate : stateAt s₁₃.mem (stA s₀) = stateAt s₀.mem (stA s₀) := by
    apply stateAt_congr
    intro i hi
    rw [hm₁₃, hm₁₀, st_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₇]
    exact frame_bytes hframe (R := stR s₀) (by simpa using hp.st_scr) (by simp) (by show i < 96; omega)
  by_cases hb : 57 ≤ cnt s₀ % 64 + 1
  · have hk : (cnt s₀ % 64 + 8) / 64 = 1 := by omega
    refine ⟨1, hC₁₃, le_rfl, by omega, hr7', by rw [hr8, hk], fun m hm => ?_⟩
    simp only [↓reduceIte]
    rw [hash_two (by rw [← hm.length]; omega), Fin1, hbytes m hm, hstate, hm.1.1,
      ← hm.length, show 64 - (cnt s₀ % 64 + 1) = 63 - cnt s₀ % 64 by omega]
  · have hk : (cnt s₀ % 64 + 8) / 64 = 0 := by omega
    refine ⟨0, hC₁₃, by omega, by omega, hr7', by rw [hr8, hk], fun m hm => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [hash_one (by rw [← hm.length]; omega), Fin0, hbytes m hm, hstate, hm.1.1,
      ← hm.length, show 56 - (cnt s₀ % 64 + 1) = 55 - cnt s₀ % 64 by omega]

/-! ## Output and epilogue -/

/-- `k` words of the digest are written. -/
structure Out (s₀ sD : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ keepRegs, s.gpr r = sD.gpr r
  sp : s.sp = sD.sp
  mem : s.mem = writeBytes sD.mem (outA s₀) (((stateAt sD.mem (stA s₀)).toList.take k).flatMap wordBytes)

theorem flat_length (H : HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap wordBytes).length = 4 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (wordBytes w).length = 4 := fun w _ => rfl
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, List.length_take]
  simp; omega

theorem out_frame (s₀ : State) (m : Mem) (xs : List Byte) (hx : xs.length ≤ 32) :
    Frame [outR s₀] m (writeBytes m (outA s₀) xs) :=
  writeBytes_frame _ _ _ (by
    rw [show outA s₀ = outA s₀ + BitVec.ofNat 64 0 by simp]
    exact contains_offset (by omega) (by omega))

set_option maxHeartbeats 1000000 in
theorem out_step {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {k : Nat} (hk : k < 8)
    {s : State} (h : Out s₀ sD k s) {rest : List Instr} {Q : State → Prop}
    (hnext : ∀ s', Out s₀ sD (k + 1) s' → WP isa (.block rest) s' Q) :
    WP isa (.block (outW k ++ rest)) s Q := by
  have hC := hD.1
  have hst := hp.st_fit; have ho := hp.out_fit
  have hr0 : s.gpr .r0 = st s₀ := by rw [h.keep _ (by simp [keepRegs]), hC.r0]
  have hr6 : s.gpr .r6 = out s₀ := by rw [h.keep _ (by simp [keepRegs]), hC.r6]
  have hP := flat_length (stateAt sD.mem (stA s₀)) k hk.le
  simp only [outW, List.cons_append, List.nil_append]
  refine wp_ldr (a := stA s₀ + BitVec.ofNat 64 (4 * k)) (by omega) (by rw [hr0, addr_off (by omega)])
    ⟨stR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_rev fun s₂ u₂ => wp_str (a := outA s₀ + BitVec.ofNat 64 (4 * k)) (by omega)
    (by rw [u₂.other .r6 (by decide), u₁.other .r6 (by decide), hr6, addr_off (by omega)])
    (by rw [u₂.wr, u₁.wr]; exact ⟨outR s₀, by simp [h.wr, hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₃ g₃ => hnext s₃ ⟨by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, u₂.wr, u₁.wr, h.wr],
      fun r hr => ?_, by rw [g₃.sp, u₂.sp, u₁.sp, h.sp], ?_⟩
  · have : r ≠ .r9 := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h <;> subst h <;> decide
    rw [g₃.gpr, u₂.other r this, u₁.other r this, h.keep r hr]
  · have hread : s.mem.readW (stA s₀ + BitVec.ofNat 64 (4 * k)) 32 = (stateAt sD.mem (stA s₀))[k] := by
      rw [h.mem, (out_frame s₀ sD.mem _ (by omega)).readW
        (r := ⟨stA s₀ + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hp.st_out.sub_left (sub_offset (by omega) (by omega))
    rw [g₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hread, h.mem, writeW_rev, ← hP]
    rw [writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ Spec.Sha256.finalizeArm.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {s : State}
    (h : Out s₀ sD 8 s) : WP isa (.block restore) s (Post s₀) := by
  have hC := hD.1
  have hfo := out_frame s₀ sD.mem (((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes)
    (by rw [flat_length _ _ le_rfl])
  refine restore_ok (scr := scr s₀) (by rw [h.keep _ (by simp [keepRegs]), hC.r3]) hp.scr_fit
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset (by omega) (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hs ho hmem _ _ hsp =>
      ⟨⟨fun r hr => ?_, by rw [hsp, h.sp, hC.sp]⟩, fun m hr hc => ?_⟩
  · rw [h.mem, ← hC.saved p hp']
    refine hfo.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.out_scr.symm.sub_left (saved_sub hp')
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
    · rw [ho _ (by decide), h.keep _ (by simp [keepRegs]), hC.lr]
  · have e := bytesAt_writeBytes sD.mem (outA s₀) 0 (((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes)
      (by rw [flat_length _ _ le_rfl]; omega)
    have e' : bytesAt (writeBytes sD.mem (outA s₀) (((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes))
        (outA s₀) 32 = ((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes := by
      rw [flat_length _ _ le_rfl, show outA s₀ + BitVec.ofNat 64 0 = outA s₀ by simp,
        show bytesAt sD.mem (outA s₀) 0 = [] from rfl, List.nil_append] at e
      exact e
    rw [← h.mem, ← hmem] at e'
    show bytesAt s'.mem (outA s₀) 32 = _
    rw [e', hD.2 m ⟨hr, hc⟩, List.take_of_length_le (by simp)]

theorem out_all {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) :
    ∀ j ≤ 8, ∀ s, Out s₀ sD (8 - j) s →
      WP isa (.block (((List.range 8).drop (8 - j)).flatMap outW ++ restore)) s (Post s₀) := by
  intro j
  induction j with
  | zero =>
    intro _ s h
    rw [show (List.range 8).drop (8 - 0) = [] from rfl, List.flatMap_nil, List.nil_append]
    exact epilogue_ok hp hD h
  | succ j ih =>
    intro hj s h
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.append_assoc,
      List.getElem_range]
    refine out_step hp hD (by omega) h fun s' h' => ?_
    rw [show 8 - (j + 1) + 1 = 8 - j by omega]
    exact ih (by omega) s' (by rwa [show 8 - (j + 1) + 1 = 8 - j by omega] at h')

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa finalize s₀ (Post s₀) := by
  rw [finalize_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := Done s₀) ?_ fun sD hD => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, LInv s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (body_ok hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have := out_all hp hD 8 le_rfl sD ⟨hD.1.rd, hD.1.wr, fun _ _ => rfl, rfl, by simp [writeBytes_nil]⟩
    rw [show 8 - 8 = 0 from rfl, List.drop_zero] at this
    exact this

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 8 bytes of stack arguments are public, the
second one pointing at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := [.r0, .r2, .r3], flags := false, lens := [96, 32, 160], bases := [(.r0, 0)], argLen := 8,
    argBases := [(4, 2)] }

theorem argByte_eq {s : State} (hsp : s.sp.toNat + 8 ≤ 2 ^ 32) {k : Nat} (hk : k < 8) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_off (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem wf₀ {s : State} (h : Spec.Sha256.finalizeArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hst := hp.st_fit; have ho := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_out, hp.st_scr⟩, hp.out_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_st
    · exact hp.a_out
    · exact hp.a_scr
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Spec.Sha256.finalizeArm.pre s₁) (h₂ : Spec.Sha256.finalizeArm.pre s₂)
    (hpub : Spec.Sha256.finalizeArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, outR, scR, stA, outA, scA, st, out, scr, p0, a0, a1]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- A state satisfying the precondition: `out` at `0x2000` and the scratch
space at `0x3000`, passed on the stack at `0x5000`. -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x20 else if a = 0x5005 then 0x30 else 0
  rd := [⟨0x5000, 8⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 160⟩]

set_option maxHeartbeats 0 in
theorem finalize_verified : Verified Arm.target finalize Spec.Sha256.finalizeArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
  · have e0 : stackArg sat 0 = 0x2000 := by decide
    have e1 : stackArg sat 1 = 0x3000 := by decide
    refine ⟨sat, ?_⟩
    simp only [Spec.Sha256.finalizeArm, e0, e1]
    refine ⟨by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat, stackArgAddr, State.addr] at h₁ h₂
      bv_omega

end VG.Proof.Sha256.Arm.Stream.Finalize
