import VerifiedGarbage.Proof.MdStream.Arm.Common

/-!
# Streaming Merkle–Damgård hash functions on ARMv7: `finalize`

Untrusted: everything here is checked by Lean. The functional correctness of
`finalize`, for any hash function (`Md`) whose code stores the length field
and writes the digest as `Shape` says, and any correct compression function
(`CalleeOk`). The same structure as the AArch64 proof
(`VG.Proof.MdStream.AArch64.Finalize`), with `state` in `r0`, `scratch` in
`r3`, `out` in `r6`, `count` in `r4:r5` (low, high), the buffered bytes in
`r7`, and whether the block is not the last in `r8`. Constant time is proven
for each hash function's code by the taint analysis, calls included, from
the initial taint `τ₀`.
-/

namespace VG.Proof.MdStream.Arm.Finalize

open VG VG.Arm VG.Impl.MdStream.Arm
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev cnt : Nat := (count s₀).toNat
abbrev out : BitVec 32 := stackArg s₀ 0
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev stA : Addr := State.addr (st s₀)
abbrev outA : Addr := State.addr (out s₀)
abbrev scA : Addr := State.addr (scr s₀)
abbrev stR : Region := ⟨stA s₀, P.N + 64⟩
abbrev outR : Region := ⟨outA s₀, P.N⟩
abbrev scR : Region := ⟨scA s₀, P.so + 48⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The buffer. -/
abbrev buf : Addr := stA s₀ + BitVec.ofNat 64 P.N

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

end

section
variable {P : Params} (H : Md 64 P.N 8) (s₀ : State)

/-- The messages the initial state represents, from `iv`. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (stA s₀) m ∧ count s₀ = BitVec.ofNat 64 m.length

/-- The final hash value, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (stA s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ List.replicate (64 - n) 0).getD t 0))
    (H.parse fun t => (List.replicate 56 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (stA s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ List.replicate (56 - n) 0 ++ H.lenBytes m.length).getD t 0)

end

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR P s₀, outR P s₀, scR P s₀]
  st_out : (stR P s₀).Disjoint (outR P s₀)
  st_scr : (stR P s₀).Disjoint (scR P s₀)
  out_scr : (outR P s₀).Disjoint (scR P s₀)
  a_st : (argR s₀).Disjoint (stR P s₀)
  a_out : (argR s₀).Disjoint (outR P s₀)
  a_scr : (argR s₀).Disjoint (scR P s₀)
  st_fit : (st s₀).toNat + (P.N + 64) ≤ 2 ^ 32
  out_fit : (out s₀).toNat + P.N ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + (P.so + 48) ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem pre_of {P : Params} {H : Md 64 P.N 8} {s₀ : State} (h : (finK H).pre s₀) : Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ## Invariants -/

structure Common (P : Params) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  r6 : s.gpr .r6 = out s₀
  r4 : s.gpr .r4 = s₀.gpr .r2
  r5 : s.gpr .r5 = s₀.gpr .r3
  sp : s.sp = s₀.sp
  frame : Frame [stR P s₀, scR P s₀] s₀.mem s.mem
  saved : Saved P s₀ s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv {P : Params} (H : Md 64 P.N 8) (s₀ : State) (k n : Nat) (s : State) : Prop
    extends Common P s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 56 + 8 * k
  r7 : s.gpr .r7 = BitVec.ofNat 32 n
  r8 : s.gpr .r8 = BitVec.ofNat 32 k
  hash : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then Fin1 H s₀ s.mem n m else Fin0 H s₀ s.mem n m)

/-- All blocks are compressed. -/
def Done {P : Params} (H : Md 64 P.N 8) (s₀ : State) (s : State) : Prop :=
  Common P s₀ s ∧ ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (stA s₀))

def keepRegs : List Reg := [.r0, .r3, .r6, .r4, .r5, .lr]

section
variable {P : Params} {H : Md 64 P.N 8}

theorem cnt_mod (s₀ : State) : cnt s₀ % 64 = (s₀.gpr .r2).toNat % 64 := by
  simp only [cnt, count]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem buf_add (s₀ : State) (n : Nat) : buf P s₀ + BitVec.ofNat 64 n = stA s₀ + BitVec.ofNat 64 (P.N + n) :=
  add_ofNat _ _ _

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common P s₀ s)
    (hg : ∀ r ∈ keepRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common P s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r0 := by rw [hg _ (by simp [keepRegs])]; exact h.r0
  r3 := by rw [hg _ (by simp [keepRegs])]; exact h.r3
  r6 := by rw [hg _ (by simp [keepRegs])]; exact h.r6
  r4 := by rw [hg _ (by simp [keepRegs])]; exact h.r4
  r5 := by rw [hg _ (by simp [keepRegs])]; exact h.r5
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Common.of_upd {s₀ : State} {s s' : State} (h : Common P s₀ s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ keepRegs) : Common P s₀ s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Common.of_flags {s₀ : State} {s s' : State} (h : Common P s₀ s) (u : Fupd s s') : Common P s₀ s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- Where the caller's registers are saved. -/
theorem saved_sub (hd : Dims P) {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved P) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (scR P s₀) := by
  have := saved_bound hd p hp; have := hd.so
  exact sub_offset (by omega) (by omega)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {s : State} (h : Common P s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ 64) :
    Frame [stR P s₀] s.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Frame [stR P s₀, scR P s₀] s₀.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Saved P s₀ (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) := by
  have := hd.N
  have hf : Frame [stR P s₀] s.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [buf_add]
    exact contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (saved_sub hd hp')

/-- Byte `k` of the buffer, addressed as `[r0 + k, #N]`. -/
theorem buf_addr {s₀ : State} (hp : Pre P s₀) {k : Nat} (hk : k < 64) :
    State.addr (st s₀ + BitVec.ofNat 32 k + BitVec.ofNat 32 P.N) = buf P s₀ + BitVec.ofNat 64 k := by
  have := hp.st_fit
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_off (by omega), add_ofNat, Nat.add_comm]

end

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (P : Params) (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ .r8 :: keepRegs, s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  r12 : s.gpr .r12 = 0
  r7 : s.gpr .r7 = BitVec.ofNat 32 (n + j)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (buf P s₀ + BitVec.ofNat 64 n) (List.replicate j 0)

/-- The zeroing loop's body. -/
def zeroBody (P : Params) : List Instr :=
  [.dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 P.N, .dp .add .r7 .r7 (.imm 1), .subs .r9 .r9 (.imm 1)]

section
variable {P : Params} {H : Md 64 P.N 8}

theorem zero_step (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {sI : State} (hC : Common P s₀ sI)
    {n lim j : Nat} (hlim : lim ≤ 64) (hj : j < lim - n) {s : State} (h : Zero P s₀ sI n lim j s) :
    WP isa (.block (zeroBody P)) s fun s' =>
      Zero P s₀ sI n lim (j + 1) s' ∧ s'.z = (BitVec.ofNat 32 (lim - n - (j + 1)) == 0) := by
  have := hd.N; have := hp.st_fit
  have hr0 : s.gpr .r0 = st s₀ := by rw [h.keep _ (by simp [keepRegs]), hC.r0]
  have hout : InRegions s.wr (buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [buf_add, add_ofNat]
    exact contains_offset (by omega) (by omega)
  unfold zeroBody
  refine wp_add (op2_reg _ _) fun s₁ u₁ =>
    wp_strb (a := buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by omega) ?_
      (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hr0, h.r7, buf_addr hp (by omega), buf]
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
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

theorem zero_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {sI : State} (hC : Common P s₀ sI) {n lim : Nat}
    (hlim : lim ≤ 64) (hn : n ≤ lim) {s : State} (h : Zero P s₀ sI n lim 0 s)
    (hz : s.z = decide (lim - n = 0)) :
    WP isa (.ite .eq (.block []) (.loop (.block (zeroBody P)) .ne)) s (Zero P s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) (by show VG.Arm.eval .eq s = _; rw [eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero P s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hd hp hC hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    have hz'' : isa.eval .ne s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
      show VG.Arm.eval .ne s' = _
      rw [eval_ne, hz', ofNat_beq_zero (by omega)]
      simp
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by rw [hz'', decide_eq_false fun h => h hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by rw [hz'', decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The compression of the buffer. -/
theorem compress_buf (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) {s : State} (hC : Common P s₀ s)
    (hr1 : s.gpr .r1 = st s₀ + BitVec.ofNat 32 P.N) {Q : State → Prop}
    (hQ : ∀ s', Common P s₀ s' → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (stA s₀) = H.compress (H.stateAt s.mem (stA s₀)) (H.blockAt s.mem (buf P s₀)) → Q s') :
    WP isa (compressAt name code) s Q := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have := hd.N; have := hd.so
  have eN : Region.Sub ⟨stA s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scA s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega)
  have ha : State.addr (st s₀ + BitVec.ofNat 32 P.N) = buf P s₀ := addr_off (by omega)
  have eb : Region.Sub ⟨buf P s₀, 64⟩ (stR P s₀) := sub_offset (by omega) (by omega)
  have d₂ : Region.Disjoint ⟨State.addr (st s₀ + BitVec.ofNat 32 P.N), 64⟩ ⟨stA s₀, P.N⟩ := by
    rw [ha]; intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  have d₃ : Region.Disjoint ⟨State.addr (st s₀ + BitVec.ofNat 32 P.N), 64⟩ ⟨scA s₀, P.so⟩ := by
    rw [ha]; exact (hp.st_scr.sub_left eb).sub_right eso
  refine compressAt_ok hf hC.r0 hC.r3 hr1 (by omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by omega) ((hp.st_scr.sub_left eN).sub_right eso) d₂ d₃
    ?_ ?_ fun s' hrd hwr hcs h0 h3 hsp hf' hstate => hQ s' ?_ hcs (by rw [hstate, ha])
  · rw [hC.rd, hC.wr, hp.rd, hp.wr, ha]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR P s₀, by simp, P.N, rfl, by simp⟩
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, h0, h3, by rw [hcs _ (by decide) (by decide)]; exact hC.r6,
      by rw [hcs _ (by decide) (by decide)]; exact hC.r4, by rw [hcs _ (by decide) (by decide)]; exact hC.r5,
      hsp.trans hC.sp, hC.frame.trans (hf'.sub ?_), fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR P s₀, by simp, eN⟩
      · exact ⟨scR P s₀, by simp, eso⟩
    · rw [← hC.saved p hp']
      have := saved_bound hd p hp'
      refine hf'.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hd hp')).sub_right eN
      · have hA : (scA s₀).toNat = (scr s₀).toNat := addr_toNat _
        have hB : (scA s₀ + BitVec.ofNat 64 p.2).toNat = (scr s₀).toNat + p.2 := by
          rw [BitVec.toNat_add, hA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂
        rw [BitVec.toNat_sub, hB] at h₁; rw [BitVec.toNat_sub, hA] at h₂
        have := a.isLt; omega

/-- The loop's postcondition for one iteration. -/
def Step {P : Params} (H : Md 64 P.N 8) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (VG.Arm.eval .eq s = some false ∧ Done H s₀ s) ∨ (VG.Arm.eval .eq s = some true ∧ k = 1 ∧ LInv H s₀ 0 0 s)

theorem body_eq (name : String) (code : Prog isa) : finalizeBody P name code =
    .seq (.block [.mov .r9 (.imm 64), .cmp .r8 (.imm 0)])
    (.seq (.ite .eq (.block [.mov .r9 (.imm 56)]) (.block []))
    (.seq (.block [.mov .r12 (.imm 0), .subs .r9 .r9 (.reg .r7)])
    (.seq (.ite .eq (.block []) (.loop (.block (zeroBody P)) .ne))
    (.seq (.block [.cmp .r8 (.imm 0)])
    (.seq (.ite .eq (.block P.len) (.block []))
    (.seq (.block [.dp .add .r1 .r0 (.imm (BitVec.ofNat 32 P.N))])
    (.seq (compressAt name code) (.block [.mov .r7 (.imm 0), .subs .r8 .r8 (.imm 1)])))))))) := rfl

theorem body_ok (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) {k n : Nat} {s : State} (h : LInv H s₀ k n s) :
    WP isa (finalizeBody P name code) s (Step H s₀ k) := by
  have hk := h.k_le; have hn := h.n_le; have hst := hp.st_fit; have := hd.N
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
  have hZ : Zero P s₀ s n (56 + 8 * k) 0 s₅ := by
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
  refine WP.seq (WP.mono (zero_ok hd hp hC (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hd hp (n := n) (xs := List.replicate (56 + 8 * k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : Common P s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r0],
      by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r3], by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r6],
      by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r4], by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r5],
      hZ₆.sp.trans hC.sp, by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : H.stateAt s₆.mem (stA s₀) = H.stateAt s.mem (stA s₀) := by
    rw [hZ₆.mem]
    apply H.stateAt_congr
    intro i hi
    rw [buf_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (buf P s₀) (56 + 8 * k) =
      bytesAt s.mem (buf P s₀) n ++ List.replicate (56 + 8 * k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h8₆ : s₆.gpr .r8 = BitVec.ofNat 32 k := by rw [hZ₆.keep _ (by simp [keepRegs]), h.r8]
  -- In the last block, the length field.
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_)
  have hC₇ := hC₆.of_flags f₇
  have h8₇ : s₇.gpr .r8 = BitVec.ofNat 32 k := by rw [f₇.gpr, h8₆]
  have hz₇ : s₇.z = decide (k = 0) := by rw [z₇, h8₆, cmp0 (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common P s₀ s₈ ∧ s₈.gpr .r8 = BitVec.ofNat 32 k ∧
      H.stateAt s₈.mem (stA s₀) = H.stateAt s.mem (stA s₀) ∧
      ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → bytesAt s₈.mem (buf P s₀) 64 = bytesAt s.mem (buf P s₀) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)) ?_
    fun s₈ ⟨hC₈, h8₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show VG.Arm.eval .eq s₇ = _; rw [eval_eq, hz₇])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have hout : InRegions s₇.wr (State.addr (s₇.gpr .r0) + BitVec.ofNat 64 (P.N + 56)) 8 :=
        ⟨stR P s₀, by simp [hC₇.wr, hp.wr], by rw [hC₇.r0]; exact contains_offset (by omega) (by omega)⟩
      refine WP.mono (hs.len s₇ (by rw [hC₇.r0]; omega) hout) fun s₈ ⟨g₈, rd₈, wr₈, sp₈, m₈⟩ => ?_
      have e : stA s₀ + BitVec.ofNat 64 (P.N + 56) = buf P s₀ + BitVec.ofNat 64 56 := (buf_add _ _).symm
      rw [hC₇.r0, hC₇.r5, hC₇.r4, e, f₇.mem] at m₈
      have hlen := H.lenOf_length (s₀.gpr .r3 ++ s₀.gpr .r2)
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hd hp (n := 56) (xs := H.lenOf (s₀.gpr .r3 ++ s₀.gpr .r2))
        (by omega)
      refine ⟨⟨rd₈.trans hC₇.rd, wr₈.trans hC₇.wr, by rw [g₈ _ (by decide), hC₇.r0],
        by rw [g₈ _ (by decide), hC₇.r3], by rw [g₈ _ (by decide), hC₇.r6],
        by rw [g₈ _ (by decide), hC₇.r4], by rw [g₈ _ (by decide), hC₇.r5], sp₈.trans hC₇.sp,
        by rw [m₈]; exact hfr, by rw [m₈]; exact hsv⟩,
        by rw [g₈ _ (by decide), h8₇], ?_, fun iv m hm hok => ?_⟩
      · rw [m₈, ← hst₆]
        apply H.stateAt_congr
        intro i hi
        rw [buf_add]
        exact writeBytes_before _ _ _ (by omega) (by omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        rw [show s₀.gpr .r3 ++ s₀.gpr .r2 = count s₀ from rfl, hm.2, H.lenOf_eq _ hok] at m₈
        have e := bytesAt_writeBytes s₆.mem (buf P s₀) 56 (H.lenBytes m.length)
          (by rw [H.lenBytes_length]; omega)
        rw [H.lenBytes_length] at e
        rw [m₈, e, hby₆, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, h8₇, by rw [f₇.mem, hst₆], fun iv m _ _ => ?_⟩
      rw [f₇.mem, hby₆]; simp
  -- Compress the block.
  refine WP.seq (wp_add (op2_imm hd.enc) fun s₉ u₉ => WP.block_nil ?_)
  have hC₉ : Common P s₀ s₉ := hC₈.of_upd u₉ (by decide)
  have hr1 : s₉.gpr .r1 = st s₀ + BitVec.ofNat 32 P.N := by rw [u₉.gpr, hC₈.r0]
  refine WP.seq (compress_buf hd hf hp hC₉ hr1 fun s₁₁ hC₁₁ cs₁₁ hst₁₁ => ?_)
  have h8₁₁ : s₁₁.gpr .r8 = BitVec.ofNat 32 k := by
    rw [cs₁₁ _ (by decide) (by decide), u₉.other _ (by decide), h8₈]
  have hblk : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.blockAt s₉.mem (buf P s₀) = H.parse fun t =>
      (bytesAt s.mem (buf P s₀) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
    intro iv m hm hok
    apply H.parse_congr
    intro t ht
    rw [u₉.mem]
    exact bytesAt_getD (hby₈ iv m hm hok) ht
  -- Next block, if any.
  refine wp_mov (op2_imm (by decide)) fun s₁₂ u₁₂ => wp_subs (op2_imm (by decide)) fun s₁₃ u₁₃ z₁₃ =>
    WP.block_nil ?_
  have hC₁₃ : Common P s₀ s₁₃ := (hC₁₁.of_upd u₁₂ (by decide)).of_upd u₁₃ (by decide)
  have h8₁₃ : s₁₃.gpr .r8 = BitVec.ofNat 32 k - 1 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), h8₁₁]
  have hz : VG.Arm.eval .eq s₁₃ = some (decide (k = 1)) := by
    rw [eval_eq, z₁₃, u₁₂.other _ (by decide), h8₁₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by omega)]
  have hst : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length →
      H.stateAt s₁₃.mem (stA s₀) = H.compress (H.stateAt s.mem (stA s₀)) (H.parse fun t =>
        (bytesAt s.mem (buf P s₀) n ++
          (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
    intro iv m hm hok
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₉.mem, hst₈, ← hblk iv m hm hok, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by rw [hz]; simp, rfl, ⟨hC₁₃, by omega, by omega, ?_, ?_, fun iv m hm hok => ?_⟩⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]; rfl
    · rw [h8₁₃]; rfl
    · rw [h.hash iv m hm hok]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst iv m hm hok]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by rw [hz]; simp, hC₁₃, fun iv m hm hok => ?_⟩
    rw [h.hash iv m hm hok, hst iv m hm hok]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

end

/-! ## Prologue -/

/-- The prologue after saving. -/
def prologue (P : Params) : List Instr :=
  [.mov .r4 (.reg .r2), .mov .r5 (.reg .r3), .mov .r3 (.reg .r12), .ldrSp .r6 0, .dp .and .r7 .r4 (.imm 63),
    .mov .r12 (.imm 0x80), .dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 P.N, .dp .add .r7 .r7 (.imm 1),
    .dp .add .r8 .r7 (.imm 7), .mov .r8 (.shifted .r8 .lsr 6)]

section
variable {P : Params} {H : Md 64 P.N 8}

theorem finalize_eq (name : String) (code : Prog isa) : finalize P name code =
    .seq (.block (([.ldrSp .r12 4] : List Instr) ++ save P .r12 ++ prologue P))
    (.seq (.loop (finalizeBody P name code) .eq) (.block (P.out ++ restore P))) := rfl

theorem argAddr_eq {s₀ : State} (hp : Pre P s₀) {k : Nat} (hk : k < 2) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_off (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : Pre P s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_offset (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : Pre P s₀) {k : Nat} (hk : k < 2) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact sub_offset (by omega) (by omega)

theorem prologue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) :
    WP isa (.block (([.ldrSp .r12 4] : List Instr) ++ save P .r12 ++ prologue P)) s₀
      fun s => ∃ k, LInv H s₀ k (cnt s₀ % 64 + 1) s := by
  have hr : cnt s₀ % 64 < 64 := Nat.mod_lt _ (by omega)
  have hsc := hp.scr_fit; have hst := hp.st_fit; have := hd.so; have := hd.N
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok hd (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact contains_offset (by omega) (by omega)⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  have hframe : Frame [scR P s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]
    exact saveMem_frame _ _ _ (by omega) _ fun p hp' => by have := saved_bound hd p hp'; omega
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
  have hC₇ : Common P s₀ s₇ := by
    refine ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
      by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
      g₇ _ (by decide), ?_, ?_, ?_, ?_, by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp],
      by rw [hm₇]; exact hframe.mono (by simp), fun p hp' => ?_⟩
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), g₂, h12]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem]
      exact hframe.readW (Region.contains_self _ _)
        (by simpa using (hp.a_scr.sub_left (arg_sub hp (by decide)))) (by decide)
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, g₂, u₁.other _ (by decide)]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
    · rw [hm₇, m₂, u₁.mem, h12, saveMem_saved hd _ _ _ p hp', u₁.other _ (Ne.symm ?_)]
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have hr7 : s₇.gpr .r7 = BitVec.ofNat 32 (cnt s₀ % 64) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂,
      u₁.other _ (by decide), and63, cnt_mod]
  -- The `0x80` byte.
  have hout : InRegions s₇.wr (buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64)) 1 := by
    refine ⟨stR P s₀, by simp [hC₇.wr, hp.wr], ?_⟩
    rw [buf_add]; exact contains_offset (by omega) (by omega)
  refine wp_mov (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_reg _ _) fun s₉ u₉ =>
    wp_strb (a := buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64)) (by omega) ?_
      (by rw [u₉.wr, u₈.wr]; exact hout) fun s₁₀ g₁₀ => ?_
  · rw [u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), hC₇.r0, hr7, buf_addr hp hr]
  obtain ⟨-, hfr, hsv⟩ := hC₇.writeBuf hd hp (n := cnt s₀ % 64) (xs := [0x80]) (by simp; omega)
  have hm₁₀ : s₁₀.mem = writeBytes s₇.mem (buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64)) [0x80] := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₉.other _ (by decide), u₈.gpr, ← List.nil_append [(0x80 : Byte)],
      writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  refine wp_add (op2_imm (by decide)) fun s₁₁ u₁₁ => wp_add (op2_imm (by decide)) fun s₁₂ u₁₂ =>
    wp_mov (op2_lsr (by decide)) fun s₁₃ u₁₃ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → r ≠ .r1 → s₁₃.gpr r = s₇.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₃.other r h2, u₁₂.other r h2, u₁₁.other r h1, g₁₀.gpr, u₉.other r h4, u₈.other r h3]
  have hm₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hC₁₃ : Common P s₀ s₁₃ :=
    ⟨by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, hC₇.rd],
      by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, hC₇.wr],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r0],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r3],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r6],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r4],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r5],
      by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, hC₇.sp],
      by rw [hm₁₃, hm₁₀]; exact hfr, by rw [hm₁₃, hm₁₀]; exact hsv⟩
  have hr7' : s₁₃.gpr .r7 = BitVec.ofNat 32 (cnt s₀ % 64 + 1) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), hr7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  have hr8 : s₁₃.gpr .r8 = BitVec.ofNat 32 ((cnt s₀ % 64 + 8) / 64) := by
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hr7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, show (7 : BitVec 32) = BitVec.ofNat 32 7 from rfl,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, shr6 (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, R₀ H s₀ iv m → bytesAt s₁₃.mem (buf P s₀) (cnt s₀ % 64 + 1) =
      Md.rest 64 m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes s₇.mem (buf P s₀) (cnt s₀ % 64) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₃, hm₁₀, e, hm₇]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := frame_bytes hframe (R := stR P s₀) (by simpa using hp.st_scr)
      (by show P.N + 64 ≤ 2 ^ 64; omega) (i := P.N + i) (by show P.N + i < P.N + 64; omega)
    rwa [← buf_add] at this
  have hstate : H.stateAt s₁₃.mem (stA s₀) = H.stateAt s₀.mem (stA s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₁₃, hm₁₀, buf_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₇]
    exact frame_bytes hframe (R := stR P s₀) (by simpa using hp.st_scr)
      (by show P.N + 64 ≤ 2 ^ 64; omega) (by show i < P.N + 64; omega)
  by_cases hb : 57 ≤ cnt s₀ % 64 + 1
  · have hk : (cnt s₀ % 64 + 8) / 64 = 1 := by omega
    refine ⟨1, hC₁₃, (Nat.le_refl _), by omega, hr7', by rw [hr8, hk], fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [Md.hash_two H (by decide) (by decide) (by rw [← hm.length]; omega), Fin1, hbytes iv m hm, hstate,
      hm.1.1, ← hm.length, show 64 - (cnt s₀ % 64 + 1) = 64 - 1 - cnt s₀ % 64 by omega]
  · have hk : (cnt s₀ % 64 + 8) / 64 = 0 := by omega
    refine ⟨0, hC₁₃, by omega, by omega, hr7', by rw [hr8, hk], fun iv m hm _ => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [Md.hash_one H (by decide) (by rw [← hm.length]; omega), Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length, show 56 - (cnt s₀ % 64 + 1) = 64 - 8 - 1 - cnt s₀ % 64 by omega]

/-! ## Output and epilogue -/

/-- The epilogue's postcondition. -/
def Post (P : Params) (H : Md 64 P.N 8) (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ (finK H).post s₀ s'

theorem epilogue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {sD : State} (hD : Done H s₀ sD) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hkeep : ∀ r, r ≠ .r9 → s.gpr r = sD.gpr r)
    (hsp : s.sp = sD.sp) (hm : s.mem = writeBytes sD.mem (outA s₀) (H.digest (H.stateAt sD.mem (stA s₀)))) :
    WP isa (.block (restore P)) s (Post P H s₀) := by
  have := hd.N; have := hd.so
  have hC := hD.1
  have hdl := H.digest_length (H.stateAt sD.mem (stA s₀))
  have hfo : Frame [outR P s₀] sD.mem (writeBytes sD.mem (outA s₀) (H.digest (H.stateAt sD.mem (stA s₀)))) :=
    writeBytes_frame _ _ _ (by
      rw [show outA s₀ = outA s₀ + BitVec.ofNat 64 0 by simp]
      exact contains_offset (by omega) (by omega))
  refine restore_ok hd (scr := scr s₀) (by rw [hkeep _ (by decide), hC.r3]) hp.scr_fit
    (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [hrd, hwr, hp.wr], contains_offset (by omega) (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hs _ hmem _ _ hsp' => ⟨⟨preserved_of hs, by rw [hsp', hsp, hC.sp]⟩, ?_⟩
  · rw [hm, ← hC.saved p hp']
    refine hfo.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.out_scr.symm.sub_left (saved_sub hd hp')
  · intro iv m hr hok hc
    have e := bytesAt_writeBytes sD.mem (outA s₀) 0 (H.digest (H.stateAt sD.mem (stA s₀))) (by omega)
    rw [hdl, show outA s₀ + BitVec.ofNat 64 0 = outA s₀ by simp, Nat.zero_add,
      show bytesAt sD.mem (outA s₀) 0 = [] from rfl, List.nil_append] at e
    rw [hmem, hm, e]
    exact (hD.2 iv m ⟨hr, hc⟩ hok).symm

theorem correct (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) : WP isa (finalize P name code) s₀ (Post P H s₀) := by
  have := hd.N
  rw [finalize_eq]
  refine WP.seq (WP.mono (prologue_ok (H := H) hd hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := Done H s₀) ?_ fun sD hD => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, LInv H s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (body_ok hd hs hf hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have hC := hD.1
    have hst := hp.st_fit; have ho := hp.out_fit
    rw [WP.block_append_iff]
    refine WP.mono (hs.out sD (by rw [hC.r0]; omega) (by rw [hC.r6]; omega) ?_ ?_ ?_)
      fun s ⟨g, rd, wr, sp, m⟩ =>
        epilogue_ok hd hp hD (rd.trans hC.rd) (wr.trans hC.wr) g sp (by rw [m, hC.r6, hC.r0])
    · refine ⟨stR P s₀, by simp [hC.rd, hC.wr, hp.wr, hp.rd], ?_⟩
      rw [hC.r0]; simpa using contains_offset (base := stA s₀) (off := 0) (n := P.N) (len := P.N + 64)
        (by omega) (by omega)
    · refine ⟨outR P s₀, by simp [hC.wr, hp.wr], ?_⟩
      rw [hC.r6]; simpa using contains_offset (base := outA s₀) (off := 0) (n := P.N) (len := P.N)
        (by omega) (by omega)
    · rw [hC.r0, hC.r6]
      exact hp.st_out.sub_left (Region.sub_prefix (by omega))

end

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 8 bytes of stack arguments are public, the
second one pointing at the scratch space. -/
def τ₀ (P : Params) : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r2, .r3], flags := false, lens := [P.N + 64, P.N, P.so + 48], bases := [(.r0, 0)],
    argLen := 8, argBases := [(4, 2)] }

section
variable {P : Params} {H : Md 64 P.N 8}

theorem wf₀ {s : State} (h : (finK H).pre s) : VG.Arm.Taint.Wf (τ₀ P) s := by
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
    refine ⟨Nat.le_refl 8, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : (finK H).pre s₁) (h₂ : (finK H).pre s₂)
    (hpub : (finK H).pub s₁ s₂) : VG.Arm.Taint.Agree (τ₀ P) s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, outR, scR, stA, outA, scA, st, out, scr, p0, a0, a1]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

end

/-- The stack arguments of `sat`: `out` at `0x2000` and the scratch space at
`0x3000`, passed on the stack at `0x5000`. -/
def satBase : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x20 else if a = 0x5005 then 0x30 else 0
  rd := [⟨0x5000, 8⟩]
  wr := []

/-- A state satisfying the precondition. -/
def sat (P : Params) : State :=
  { satBase with wr := [⟨0x1000, P.N + 64⟩, ⟨0x2000, P.N⟩, ⟨0x3000, P.so + 48⟩] }

/-- `finalize` is verified, given that it is constant time (which the taint
analysis proves of each hash function's code). -/
theorem verified {P : Params} {H : Md 64 P.N 8} (hd : Dims P) (hs : Shape H) {name : String}
    {code : Prog isa} (hf : CalleeOk H code)
    (hct : ConstantTime isa (finK H).pre (finK H).pub (finalize P name code)) :
    Verified Arm.target (finalize P name code) (finK H) := by
  have := hd.N; have := hd.so
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct hd hs hf (pre_of hs')
    exact ⟨t, s', he, h⟩
  · have e0 : stackArg (sat P) 0 = 0x2000 := by show stackArg satBase 0 = _; decide
    have e1 : stackArg (sat P) 1 = 0x3000 := by show stackArg satBase 1 = _; decide
    refine ⟨sat P, ?_⟩
    simp only [finK, e0, e1]
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [sat, satBase, stackArgAddr, State.addr]; done)
      | (simp [sat, satBase]; omega)
      | (intro a h₁ h₂
         simp only [Region.Contains, sat, satBase, stackArgAddr, State.addr] at h₁ h₂
         bv_omega)

end VG.Proof.MdStream.Arm.Finalize
