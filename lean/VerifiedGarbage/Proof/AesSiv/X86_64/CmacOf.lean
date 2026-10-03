import VerifiedGarbage.Proof.AesSiv.X86_64.Env
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# AES-SIV on x86-64: the CMAC of the data (`cmacOf`)

`cmacOf` computes the CMAC of the data with the context's PRF into the state
at `W + 128`: the code zeroes the state, computes `16 nb`, the bytes of the
whole blocks before the last 1 to 16 (`Spec.Cmac.chainedLen`), stores it at
`W + 144`, chains the `nb` blocks with `vg_cmac_aes_update` and finalizes the
rest with `vg_cmac_aes_finalize` (`Siv.cmacWith_chained`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs UPost FArgs upd_call upd_rel fin_rel toNat_ofNat beq_zero_iff)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## The length of the whole blocks -/

/-- `chainedLen 16 L` as the code computes it: `(L − 1) − ((L − 1) & 15)`. -/
theorem chained_bv {L : Nat} (h0 : 0 < L) (hL : L < 2 ^ 64) :
    BitVec.ofNat 64 L - BitVec.signExtend 64 (BitVec.ofNat 32 1) -
        ((BitVec.ofNat 64 L - BitVec.signExtend 64 (BitVec.ofNat 32 1)) &&&
          BitVec.signExtend 64 (BitVec.ofNat 32 15)) =
      BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) := by
  rw [sx_ofNat (by decide), sx_ofNat (by decide)]
  have e1 : BitVec.ofNat 64 L - BitVec.ofNat 64 1 = BitVec.ofNat 64 (L - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e1]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_ofNat, Spec.Cmac.chainedLen]
  rw [show (15 % 2 ^ 64 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem chainedLen_le (L : Nat) : Spec.Cmac.chainedLen 16 L ≤ L := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_rest (L : Nat) : L - Spec.Cmac.chainedLen 16 L ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_div (L : Nat) : 16 * (Spec.Cmac.chainedLen 16 L / 16) = Spec.Cmac.chainedLen 16 L := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_zero : Spec.Cmac.chainedLen 16 0 = 0 := rfl

/-! ## Before the update -/

theorem cmacA_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) :
    ∃ s', runBlock isa (zero16 .r15 stOff ++ [.mov32 .rcx (.imm 0), .alu .test .r14 (.reg .r14)]) s = some s' ∧
      Regs s₀ C D P W R L s' ∧ s'.gpr .rcx = 0 ∧ s'.zf = some (decide (L = 0)) ∧
      s'.mem = zero2 s.mem (W + BitVec.ofNat 64 128) := by
  have w₀ := h.inW hr.wr (d := 128) (n := 8) (by decide)
  have w₁ := h.inW hr.wr (d := 136) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [zero16, stOff, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, State.store64,
      State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, ite_true, ite_false, hr.r15, w₀, w₁]
    rfl, ?_⟩
  refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, rfl, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · simp only [zf_arithFlags, hr.r14, BitVec.and_self, beq_zero_iff, toNat_ofNat h.lt]
  · simp only [mem_arithFlags, mem_setReg, zero2, Offset.add_add]

theorem cmacB_ok {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (h0 : 0 < L) (hL : L < 2 ^ 64) :
    ∃ s', runBlock isa [.mov .rcx (.reg .r14), .alu .sub .rcx (imm 1), .mov .rax (.reg .rcx),
        .alu .and .rax (imm 15), .alu .sub .rcx (.reg .rax)] s = some s' ∧
      s'.gpr .rcx = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h14, chained_bv h0 hL]
  refine ⟨trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem shr4 {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c >>> 4 = BitVec.ofNat 64 (c / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem cmacC_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {c : Nat}
    (hc : c < 2 ^ 64) (hrcx : s.gpr .rcx = BitVec.ofNat 64 c) :
    ∃ s', runBlock isa [.mov .r8 (.reg .rcx), .shift .shr .r8 4, .store (at_ .r15 dbOff) .rcx,
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm stOff),
        .mov .rcx (.reg .r13), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)] s = some s' ∧
      Regs s₀ C D P W R L s' ∧ s'.gpr .rdi = C ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = W + BitVec.ofNat 64 128 ∧ s'.gpr .rcx = P ∧ s'.gpr .r8 = BitVec.ofNat 64 (c / 16) ∧
      s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧ s'.mem = s.mem.writeW (W + BitVec.ofNat 64 144) (BitVec.ofNat 64 c) := by
  have w := h.inW hr.wr (d := 144) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [imm, dbOff, stOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, execAlu, execShift, State.store64, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
      mem_setFlags, rd_setReg, rd_setFlags, wr_setReg, wr_setFlags, ite_true, ite_false, hr.r15, w]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, ite_true, ite_false, hr.rbx, hr.rbp, hr.r13, hrcx, shr4 hc,
    sx_ofNat (show 128 < 2 ^ 31 by decide), sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags]

/-- What `cmacPre` leaves: the arguments of `vg_cmac_aes_update` for the
whole blocks before the last bytes, the zero state, and their length at
`W + 144`. -/
theorem cmacPre_wp (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) :
    WP isa (cmacPre stOff) s fun s' => Regs s₀ C D P W R L s' ∧
      UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
      s'.mem = (zero2 s.mem (W + BitVec.ofNat 64 128)).writeW (W + BitVec.ofNat 64 144)
        (BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) := by
  obtain ⟨s₁, run₁, hr₁, rcx₁, zf₁, m₁⟩ := cmacA_ok h hr
  have hcl := chainedLen_le L
  have hlt := h.lt
  have last (s₂ : State) (hr₂ : Regs s₀ C D P W R L s₂) (rcx₂ : s₂.gpr .rcx =
      BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) (m₂ : s₂.mem = s₁.mem) :
      WP isa (.block [.mov .r8 (.reg .rcx), .shift .shr .r8 4, .store (at_ .r15 dbOff) .rcx,
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm stOff),
        .mov .rcx (.reg .r13), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)]) s₂ fun s' =>
        Regs s₀ C D P W R L s' ∧
        UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
        s'.mem = (zero2 s.mem (W + BitVec.ofNat 64 128)).writeW (W + BitVec.ofNat 64 144)
          (BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) := by
    obtain ⟨s', run, hr', rdi, rsi, rdx, rcx, r8, r9, m'⟩ := cmacC_ok h hr₂ (by omega) rcx₂
    refine WP.of_runBlock ⟨s', run, hr', h.uargs hr'.rd hr'.wr hr'.rsp (by decide)
      (by rw [chainedLen_div]; exact h.srcData₀ (by decide) hcl) (by rw [chainedLen_div]; omega)
      rdi rsi rdx rcx r8 r9, by rw [m', m₂, m₁]⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.ite (decide (L = 0)) zf₁ (fun hz => ?_) (fun hz => ?_))
  · have hL0 : L = 0 := of_decide_eq_true hz
    refine WP.block_nil ?_
    refine last s₁ hr₁ ?_ rfl
    rw [rcx₁, hL0]; rfl
  · have hL0 : 0 < L := Nat.pos_of_ne_zero (of_decide_eq_false hz)
    obtain ⟨s₂, run₂, rcx₂, g₂, m₂, rd₂, wr₂⟩ := cmacB_ok hr₁.r14 hL0 hlt
    exact WP.of_runBlock ⟨s₂, run₂, last s₂ (hr₁.keep g₂ rd₂ wr₂) rcx₂ (by rw [m₂])⟩

/-! ## Between the calls -/

theorem cmacMid_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {c : Nat}
    (hc : c ≤ L) (hm : s.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 c) :
    ∃ s', runBlock isa (cmacMid stOff) s = some s' ∧ Regs s₀ C D P W R L s' ∧ s'.gpr .rdi = C ∧
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = W + BitVec.ofNat 64 128 ∧
      s'.gpr .rcx = P + BitVec.ofNat 64 c ∧ s'.gpr .r8 = BitVec.ofNat 64 (L - c) ∧
      s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧ s'.mem = s.mem := by
  have r := h.inRW hr.rd hr.wr (d := 144) (n := 8) (by decide)
  have hlt := h.lt
  refine ⟨_, by
    simp (config := {decide := true}) only [cmacMid, imm, dbOff, stOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.ea, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hr.r15, r]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    ite_true, ite_false, hr.rbx, hr.rbp, hr.r13, hr.r14, hm,
    sx_ofNat (show 128 < 2 ^ 31 by decide), sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, trivial, trivial, trivial, trivial, ?_, trivial⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show L - c < 2 ^ 64 by omega)]
    omega

/-! ## The whole -/

/-- What `cmacOf` leaves: the CMAC of the data with the context's PRF in the
state at `W + 128`. -/
structure CPost (s₀ : State) (C D P W : Addr) (R L : Nat) (s s' : State) : Prop where
  regs : Regs s₀ C D P W R L s'
  frame : Frame [⟨W, 160⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 128) 16 =
    Spec.Siv.ctxMac s.mem C R (Spec.Aes.bytesAt s.mem P L)

theorem cmacOf_wp (v : Ctr32Impl) (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) :
    WP isa (cmacOf v.callee v.suffix stOff) s (CPost s₀ C D P W R L s) := by
  have hcl := chainedLen_le L
  have hrest := chainedLen_rest L
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (cmacPre_wp h hr) fun s₁ ⟨hr₁, hu₁, m₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call v _ hu₁) fun s₂ h₂ => ?_)
  have hr₂ := hr₁.keep h₂.saved h₂.rd h₂.wr
  have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₁.mem s₂.mem := by rw [← hr₁.rsp]; exact h₂.frame
  have hm₂ : s₂.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) := by
    rw [f₂.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint W (by omega) (by omega) (by omega)
        · exact Offset.disjoint W (by omega) (by omega) (by omega)
        · exact (h.stk_w.sub_right (h.sW (by decide))).symm) (by decide), m₁,
      Mem.readW_writeW_self64]
  obtain ⟨s₃, run₃, hr₃, rdi₃, rsi₃, rdx₃, rcx₃, r8₃, r9₃, m₃⟩ := cmacMid_ok h hr₂ hcl hm₂
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.mono (finr_call v _ (h.fargs hr₃.rd hr₃.wr hr₃.rsp (by decide)
    (h.srcData (o := 128) (by decide) (show Spec.Cmac.chainedLen 16 L + (L - Spec.Cmac.chainedLen 16 L) ≤ L by
      omega)) hrest rdi₃ rsi₃ rdx₃ rcx₃ r8₃ r9₃)) fun s₄ h₄ => ?_
  have f₄ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₃.mem s₄.mem := by rw [← hr₃.rsp]; exact h₄.frame
  -- What the code before the update writes.
  have f₁ : Frame [⟨W, 160⟩] s.mem s₁.mem := by
    have c₀ := Offset.contains_base W (d := 128) (n := 8) (k := 160) (by decide) (by decide)
    have c₁ : (⟨W, 160⟩ : Region).Contains (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8) 8 := by
      rw [Offset.add_add]; exact Offset.contains_base W (d := 136) (n := 8) (k := 160) (by decide) (by decide)
    have c₂ := Offset.contains_base W (d := 144) (n := 8) (k := 160) (by decide) (by decide)
    rw [m₁, zero2]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₀).writeW
      (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂
  have sub3 (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩,
      below (s₀.gpr .rsp) 16]) : ∃ r' ∈ [(⟨W, 160⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩,
      below (s₀.gpr .rsp) 16], Region.Sub r r' := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W, 160⟩, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have frame : Frame [⟨W, 160⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16] s.mem s₄.mem :=
    ((f₁.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₂.sub sub3)).trans
      (by rw [← m₃]; exact f₄.sub sub3)
  refine ⟨hr₃.keep h₄.saved h₄.rd h₄.wr, frame, ?_⟩
  -- The bytes the calls read are those at the start.
  have dRead {Q : Addr} {n : Nat} (hd : ∀ r ∈ [(⟨W, 160⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩,
      below (s₀.gpr .rsp) 16], (⟨Q, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
      Spec.Aes.bytesAt s₁.mem Q n = Spec.Aes.bytesAt s.mem Q n ∧
        Spec.Aes.bytesAt s₃.mem Q n = Spec.Aes.bytesAt s.mem Q n := by
    have e₁ := bytesAt_frame f₁ (fun r hr => hd r (by simp_all)) hn
    refine ⟨e₁, ?_⟩
    rw [m₃, bytesAt_frame f₂ (fun r hr => by
      obtain ⟨r', hr', hs⟩ := sub3 r hr; exact (hd r' hr').sub_right hs) hn, e₁]
  have hlt := h.lt
  have dC {d n : Nat} (hd : d + n ≤ 512) := dRead (Q := C + BitVec.ofNat 64 d) (n := n) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (h.c_w.sub_left (h.sC hd)).sub_right (Region.sub_prefix (by decide))
    · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))
    · exact (h.stk_c.sub_right (h.sC hd)).symm) (by omega)
  have dP {d n : Nat} (hd : d + n ≤ L) := dRead (Q := P + BitVec.ofNat 64 d) (n := n) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (h.p_w.sub_left (h.sP hd)).sub_right (Region.sub_prefix (by decide))
    · exact (h.p_w.sub_left (h.sP hd)).sub_right (h.sW (by decide))
    · exact (h.stk_p.sub_right (h.sP hd)).symm) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := (dC (d := 240) (n := 16) (by decide)).2
  have k2 := (dC (d := 256) (n := 16) (by decide)).2
  have pre := (dP (d := 0) (n := Spec.Cmac.chainedLen 16 L) (by omega)).1
  have rest := (dP (d := Spec.Cmac.chainedLen 16 L) (n := L - Spec.Cmac.chainedLen 16 L) (by omega)).2
  rw [k0] at sch pre
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 128) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, bytesAt_frame (rs := [⟨W + BitVec.ofNat 64 144, 8⟩]) ((Frame.refl _ _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide), zero2_bytes]
  have hS : (Spec.Aes.bytesAt s.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have hsplit : L = Spec.Cmac.chainedLen 16 L + (L - Spec.Cmac.chainedLen 16 L) := by omega
  rw [h₄.out, mn, sch.2, k1, k2, rest, m₃, h₂.out, Proof.Cmac.Stream.blocksAt_eq, chainedLen_div, sch.1, hz, pre,
    Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.cmacWith_chained, hS]
  have tk : (Spec.Aes.bytesAt s.mem P L).take (Spec.Cmac.chainedLen 16 L) =
      Spec.Aes.bytesAt s.mem P (Spec.Cmac.chainedLen 16 L) := by
    have := take_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 L) (b := L - Spec.Cmac.chainedLen 16 L)
    rwa [← hsplit] at this
  have dr : (Spec.Aes.bytesAt s.mem P L).drop (Spec.Cmac.chainedLen 16 L) =
      Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) (L - Spec.Cmac.chainedLen 16 L) := by
    have := drop_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 L) (b := L - Spec.Cmac.chainedLen 16 L)
    rwa [← hsplit] at this
  rw [tk, dr]
  rw [Proof.Cmac.xor_comm]
  rfl

end VG.Proof.AesSiv.X86_64
