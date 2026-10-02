import VerifiedGarbage.Proof.MlKem.Arm.Reduce
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Impl.MlKem.Arm.Sample

/-!
# ML-KEM on 32-bit ARM: calling the SHA-3 sponge

The calls of `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` in
their frames (`absorbCall`, `padCall`, `squeezeCall`), from the callees'
proofs (`WP.callCalls`, with the per-target contracts `Proof.Sha3.absorbArm`,
…): what each needs of the state it is called from (`AbsorbArgs`, …), and what
holds when it returns; and that two runs that call it with the same arguments
leak the same trace (`absorb_ct`, …, by `RelCT.frame` and `RelCT.call`). The
frame stores the stack arguments in the 8 bytes below the stack pointer, which
the callers' contracts reserve (`below`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.Sha3 (Repr stateAt squeezeFrom rates)

/-- The `n` bytes at the 32-bit pointer `b`. -/
abbrev regA (b : BitVec 32) (n : Nat) : Region := ⟨State.addr b, n⟩

/-- The `n` bytes below the stack pointer. -/
abbrev below (s : State) (n : Nat) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 n, n⟩

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `lr`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem rates_lt {rate : Nat} (h : rate ∈ rates) : rate ≤ 168 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem absorb_noFrames : Impl.Sha3.Arm.Stream.absorb.noFrames = true := by decide +kernel
theorem pad_noFrames : Impl.Sha3.Arm.Stream.pad.noFrames = true := by decide +kernel
theorem squeeze_noFrames : Impl.Sha3.Arm.Stream.squeeze.noFrames = true := by decide +kernel

/-! ## Frames -/

theorem addr_sub {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    State.addr (sp - BitVec.ofNat 32 n) = State.addr sp - BitVec.ofNat 64 n := by
  have := sp.isLt
  simp only [State.addr]; bv_omega

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = BitVec.ofNat 32 8 := rfl

theorem e4 : BitVec.ofNat 32 (4 * [Reg.lr].length) = BitVec.ofNat 32 4 := rfl

/-- A frame of two words: the stack pointer, the stack arguments and the
memory. -/
theorem push2_sp (s : State) : (pushed [.r12, .lr] s).sp = s.sp - BitVec.ofNat 32 8 := by
  rw [pushed_sp, e8]

theorem push2_mem {s : State} (hsp : 8 ≤ s.sp.toNat) : (pushed [.r12, .lr] s).mem =
    (s.mem.writeW (State.addr s.sp - BitVec.ofNat 64 8) (s.gpr .r12)).writeW
      (State.addr s.sp - BitVec.ofNat 64 8 + BitVec.ofNat 64 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)) [s.gpr .r12, s.gpr .lr] = _
  rw [e8]
  show (s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 8)) (s.gpr .r12)).writeW
    (State.addr (s.sp - BitVec.ofNat 32 8 + 4)) (s.gpr .lr) = _
  rw [addr_sub hsp, show s.sp - BitVec.ofNat 32 8 + 4 = s.sp - BitVec.ofNat 32 8 + BitVec.ofNat 32 4 from rfl,
    addr_add (by bv_omega), addr_sub hsp]

theorem push2_arg {s t : State} (hsp : 8 ≤ s.sp.toNat) (ht : t.sp = s.sp - BitVec.ofNat 32 8)
    (hm : t.mem = (pushed [.r12, .lr] s).mem) :
    stackArgAddr t 0 = State.addr s.sp - BitVec.ofNat 64 8 ∧ stackArg t 0 = s.gpr .r12 ∧
      stackArg t 1 = s.gpr .lr := by
  have a0 : stackArgAddr t 0 = State.addr s.sp - BitVec.ofNat 64 8 := by
    unfold stackArgAddr
    rw [ht, addr_add (by bv_omega), addr_sub hsp]; simp
  have a1 : stackArgAddr t 1 = State.addr s.sp - BitVec.ofNat 64 8 + BitVec.ofNat 64 4 := by
    unfold stackArgAddr; rw [ht, show 4 * 1 = 4 from rfl, addr_add (by bv_omega), addr_sub hsp]
  refine ⟨a0, ?_, ?_⟩
  · rw [stackArg, a0, hm, push2_mem hsp, Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide),
      Mem.readW_writeW_self32]
  · rw [stackArg, a1, hm, push2_mem hsp, Mem.readW_writeW_self32]

theorem push2_frame {s : State} (hsp : 8 ≤ s.sp.toNat) : Frame [below s 8] s.mem (pushed [.r12, .lr] s).mem := by
  rw [push2_mem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [show State.addr s.sp - BitVec.ofNat 64 8 + BitVec.ofNat 64 4 - (State.addr s.sp - BitVec.ofNat 64 8) =
      BitVec.ofNat 64 4 by bv_omega]; decide

/-- The stack arguments are the frame: the regions a callee is given within
those of the frame's state. -/
theorem cov_push {s : State} (hsp : 8 ≤ s.sp.toNat) {rs ws : List Region} {rr : Region} (hr : rr = below s 8)
    (hc : Covers rs (s.rd ++ s.wr)) (hw : Covers ws s.wr) (rs' : List Region) (hrs : rs' = rs ++ [rr]) :
    Covers (rs' ++ ws) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  subst hrs hr
  intro x n ⟨r, hr, hc'⟩
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | rfl) | hr
  · obtain ⟨r', hr', hc''⟩ := hc x n ⟨r, hr, hc'⟩
    refine ⟨r', ?_, hc''⟩
    rw [pushed_rd, pushed_wr]
    rcases List.mem_append.mp hr' with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rw [e8, addr_sub hsp]; exact hc'
  · obtain ⟨r', hr', hc''⟩ := hw x n ⟨r, hr, hc'⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc''⟩

/-! ## `vg_keccak_absorb` -/

/-- What a call of `vg_keccak_absorb` in its frame needs: the state at `st`,
the rate, the position, the data at `data`, its length and the working
space at `scr` in `r0`–`r3`, `r12` and `lr`; the buffers apart, and apart
from the 8 bytes below the stack pointer. -/
structure AbsorbArgs (s : State) (st scr data : BitVec 32) (rate pos len : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 pos
  r3 : s.gpr .r3 = data
  r12 : s.gpr .r12 = BitVec.ofNat 32 len
  lr : s.gpr .lr = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  hlen : len < 2 ^ 32
  sp : 8 ≤ s.sp.toNat
  fst : st.toNat + 200 ≤ 2 ^ 32
  fdata : data.toNat + len ≤ 2 ^ 32
  fscr : scr.toNat + 640 ≤ 2 ^ 32
  d_st_scr : (regA st 200).Disjoint (regA scr 640)
  d_data_st : (regA data len).Disjoint (regA st 200)
  d_data_scr : (regA data len).Disjoint (regA scr 640)
  b_st : (below s 8).Disjoint (regA st 200)
  b_scr : (below s 8).Disjoint (regA scr 640)
  b_data : (below s 8).Disjoint (regA data len)
  cw : Covers [regA st 200, regA scr 640] s.wr
  cr : Covers [regA data len] (s.rd ++ s.wr)

/-- The state `vg_keccak_absorb` runs from, with the permissions it is given. -/
abbrev absorbView (s : State) (st scr data : BitVec 32) (len : Nat) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions [regA data len, below s 8] [regA st 200, regA scr 640]

theorem view_gpr (rs : List Reg) (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    ((pushed rs s).callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem absorb_pre {s : State} {st scr data : BitVec 32} {rate pos len : Nat}
    (h : AbsorbArgs s st scr data rate pos len) : Proof.Sha3.absorbArm.pre (absorbView s st scr data len) := by
  obtain ⟨a0, a1, a2⟩ := push2_arg (t := absorbView s st scr data len) h.sp (push2_sp s) rfl
  have hr := rates_lt h.hrate
  have hp := h.hpos
  simp only [Proof.Sha3.absorbArm, view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, a0, a1, a2, h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, toNat_ofNat32 h.hlen,
    toNat_ofNat32 (show rate < 2 ^ 32 by omega), toNat_ofNat32 (show pos < 2 ^ 32 by omega),
    State.callEntry_sp, push2_sp]
  refine ⟨trivial, trivial, h.d_st_scr, h.d_data_st, h.d_data_scr, h.b_st, h.b_scr, h.fst, h.fdata, h.fscr, ?_,
    h.hrate, h.hpos⟩
  have := h.sp; have := s.sp.isLt; bv_omega

theorem absorb_ok {s : State} {st scr data : BitVec 32} {rate pos len : Nat}
    (h : AbsorbArgs s st scr data rate pos len) {Q : State → Prop}
    (hQ : ∀ s', Kept [regA st 200, regA scr 640, below s 8] s s' →
      (∀ msg, Repr s.mem (State.addr st) rate msg → pos = msg.length % rate →
        Repr s'.mem (State.addr st) rate (msg ++ Spec.Sha3.bytesAt s.mem (State.addr data) len)) →
      (s'.gpr .r0).toNat = (pos + len) % rate → Q s') :
    WP isa absorbCall s Q := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.sp) (by decide) ?_
  obtain ⟨a0, a1, a2⟩ := push2_arg (t := absorbView s st scr data len) h.sp (push2_sp s) rfl
  have hr := rates_lt h.hrate
  have hp := h.hpos
  have hl := h.hlen
  have fA := push2_frame h.sp
  refine WP.callCalls (k := Proof.Sha3.absorbArm) Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1
    (absorb_pre h) (cov_push h.sp rfl h.cr h.cw _ rfl)
    (fun x n hi => by
      obtain ⟨r', hr', hc'⟩ := h.cw x n hi
      exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩) ?_ absorb_noFrames
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  simp only [Proof.Sha3.absorbArm, view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_mem, State.withRegions_gpr,
    a1, h.r0, h.r1, h.r2, h.r3, h.r12, toNat_ofNat32 h.hlen, toNat_ofNat32 (show rate < 2 ^ 32 by omega),
    toNat_ofNat32 (show pos < 2 ^ 32 by omega), State.callEntry_mem] at hpost
  have hst : ∀ r ∈ [below s 8], (regA st 200).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact h.b_st.symm
  have hdat : ∀ r ∈ [below s 8], (regA data len).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact h.b_data.symm
  refine hQ _ ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ (fun msg hm hp => ?_) ?_
  · have hr12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr12, hcs r hr hl, pushed_gpr]
  · rw [popped_sp, hsp₂, push2_sp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_mem]
    refine (fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]
    have e := hpost.1 msg (by
      unfold Spec.Sha3.Repr at hm ⊢
      rw [Proof.Sha3.stateAt_congr (bytes_frame fA hst (by decide))]; exact hm) hp
    rwa [bytesAt_frame fA hdat (by omega)] at e
  · rw [popped_gpr (by decide), hpost.2]

theorem push_eq {rs : List Reg} {s a : State} (h : isa.push (.push rs) s = some a) : a = pushed rs s := by
  simp only [isa, push] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem absorb_ct {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∃ st scr data rate pos len,
      AbsorbArgs s₁ st scr data rate pos len ∧ AbsorbArgs s₂ st scr data rate pos len) :
    RelCT isa P absorbCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP s₁ s₂ h).1) ?_
  refine RelCT.mono (P := fun a b => ∃ x : BitVec 32 × BitVec 32 × BitVec 32 × Nat × Nat × Nat × BitVec 32,
      ∃ s₁ s₂, s₁.sp = x.2.2.2.2.2.2 ∧ s₂.sp = x.2.2.2.2.2.2 ∧
        AbsorbArgs s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 ∧
        AbsorbArgs s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 ∧
        a = pushed [.r12, .lr] s₁ ∧ b = pushed [.r12, .lr] s₂) ?_ ?_ (fun _ _ h => h)
  · refine RelCT.exists_ fun ⟨st, scr, data, rate, pos, len, sp⟩ => ?_
    refine RelCT.call (k := Proof.Sha3.absorbArm) Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1
      Proof.Sha3.Arm.Stream.Absorb.absorb_verified.2.1
      [regA data len, ⟨State.addr sp - BitVec.ofNat 64 8, 8⟩] [regA st 200, regA scr 640] ?_
    rintro a b ⟨s₁, s₂, e₁, e₂, h₁, h₂, rfl, rfl⟩
    dsimp only at e₁ e₂ h₁ h₂
    have v₁ : (pushed [.r12, .lr] s₁).callEntry.withRegions [regA data len, ⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
        [regA st 200, regA scr 640] = absorbView s₁ st scr data len := by simp only [absorbView, below, e₁]
    have v₂ : (pushed [.r12, .lr] s₂).callEntry.withRegions [regA data len, ⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
        [regA st 200, regA scr 640] = absorbView s₂ st scr data len := by simp only [absorbView, below, e₂]
    rw [v₁, v₂]
    obtain ⟨a₀, a₁, a₂⟩ := push2_arg (t := absorbView s₁ st scr data len) h₁.sp (push2_sp s₁) rfl
    obtain ⟨b₀, b₁, b₂⟩ := push2_arg (t := absorbView s₂ st scr data len) h₂.sp (push2_sp s₂) rfl
    refine ⟨absorb_pre h₁, absorb_pre h₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_sp, State.callEntry_sp, push2_sp, e₁, e₂]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r0, h₂.r0]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r1, h₂.r1]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r2, h₂.r2]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r3, h₂.r3]
    · rw [a₁, b₁, h₁.r12, h₂.r12]
    · rw [a₂, b₂, h₁.lr, h₂.lr]
    · exact cov_push h₁.sp (by simp only [below, e₁]) h₁.cr h₁.cw _ rfl
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₁.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
    · exact cov_push h₂.sp (by simp only [below, e₂]) h₂.cr h₂.cw _ rfl
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₂.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
  · rintro a b ⟨s₁, s₂, hp, pa, pb⟩
    obtain ⟨hsp, st, scr, data, rate, pos, len, h₁, h₂⟩ := hP s₁ s₂ hp
    exact ⟨⟨st, scr, data, rate, pos, len, s₁.sp⟩, s₁, s₂, rfl, hsp.symm, h₁, h₂, push_eq pa, push_eq pb⟩

/-! ## `vg_keccak_pad` -/

theorem push1_sp (s : State) : (pushed [.lr] s).sp = s.sp - BitVec.ofNat 32 4 := by
  rw [pushed_sp, e4]

theorem push1_mem {s : State} (hsp : 8 ≤ s.sp.toNat) : (pushed [.lr] s).mem =
    s.mem.writeW (State.addr s.sp - BitVec.ofNat 64 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.lr].length)) [s.gpr .lr] = _
  rw [e4]
  show s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 4)) (s.gpr .lr) = _
  rw [addr_sub (by omega)]

theorem push1_arg {s t : State} (hsp : 8 ≤ s.sp.toNat) (ht : t.sp = s.sp - BitVec.ofNat 32 4)
    (hm : t.mem = (pushed [.lr] s).mem) :
    stackArgAddr t 0 = State.addr s.sp - BitVec.ofNat 64 4 ∧ stackArg t 0 = s.gpr .lr := by
  have a0 : stackArgAddr t 0 = State.addr s.sp - BitVec.ofNat 64 4 := by
    unfold stackArgAddr
    rw [ht, addr_add (by bv_omega), addr_sub (by omega)]; simp
  refine ⟨a0, ?_⟩
  rw [stackArg, a0, hm, push1_mem hsp, Mem.readW_writeW_self32]

theorem push1_frame {s : State} (hsp : 8 ≤ s.sp.toNat) : Frame [below s 8] s.mem (pushed [.lr] s).mem := by
  rw [push1_mem hsp]
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains]
  rw [show State.addr s.sp - BitVec.ofNat 64 4 - (State.addr s.sp - BitVec.ofNat 64 8) = BitVec.ofNat 64 4 by
    bv_omega]; decide

theorem below4_sub (s : State) : Region.Sub (below s 4) (below s 8) := by
  intro a ha
  have := s.sp.isLt
  have e : (State.addr s.sp).toNat = s.sp.toNat := addr_toNat _
  simp only [Region.Contains] at ha ⊢
  bv_omega

theorem cov_push1 {s : State} (hsp : 8 ≤ s.sp.toNat) {ws : List Region} (hw : Covers ws s.wr) :
    Covers ([below s 4] ++ ws) ((pushed [.lr] s).rd ++ (pushed [.lr] s).wr) := by
  intro x n ⟨r, hr, hc'⟩
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with rfl | hr
  · refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rw [e4, addr_sub (by omega)]; exact hc'
  · obtain ⟨r', hr', hc''⟩ := hw x n ⟨r, hr, hc'⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc''⟩

/-- What a call of `vg_keccak_pad` in its frame needs. -/
structure PadArgs (s : State) (st scr : BitVec 32) (rate pos : Nat) (suffix : BitVec 32) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 pos
  r3 : s.gpr .r3 = suffix
  lr : s.gpr .lr = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  sp : 8 ≤ s.sp.toNat
  fst : st.toNat + 200 ≤ 2 ^ 32
  fscr : scr.toNat + 640 ≤ 2 ^ 32
  d_st_scr : (regA st 200).Disjoint (regA scr 640)
  b_st : (below s 8).Disjoint (regA st 200)
  b_scr : (below s 8).Disjoint (regA scr 640)
  cw : Covers [regA st 200, regA scr 640] s.wr

abbrev padView (s : State) (st scr : BitVec 32) : State :=
  (pushed [.lr] s).callEntry.withRegions [below s 4] [regA st 200, regA scr 640]

theorem pad_pre {s : State} {st scr : BitVec 32} {rate pos : Nat} {suffix : BitVec 32}
    (h : PadArgs s st scr rate pos suffix) : Proof.Sha3.padArm.pre (padView s st scr) := by
  obtain ⟨a0, a1⟩ := push1_arg (t := padView s st scr) h.sp (push1_sp s) rfl
  have hr := rates_lt h.hrate
  have hp := h.hpos
  have hs := below4_sub s
  simp only [Proof.Sha3.padArm, view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, a0, a1, h.r0, h.r1, h.r2, h.lr,
    toNat_ofNat32 (show rate < 2 ^ 32 by omega), toNat_ofNat32 (show pos < 2 ^ 32 by omega),
    State.callEntry_sp, push1_sp]
  refine ⟨trivial, trivial, h.d_st_scr, h.b_st.sub_left hs, h.b_scr.sub_left hs, h.fst, h.fscr, ?_, h.hrate,
    h.hpos⟩
  have := h.sp; have := s.sp.isLt; bv_omega

theorem pad_ok {s : State} {st scr : BitVec 32} {rate pos : Nat} {suffix : BitVec 32}
    (h : PadArgs s st scr rate pos suffix) {Q : State → Prop}
    (hQ : ∀ s', Kept [regA st 200, regA scr 640, below s 8] s s' →
      (∀ msg, Repr s.mem (State.addr st) rate msg → pos = msg.length % rate →
        stateAt s'.mem (State.addr st) = Spec.Sha3.absorb rate (Spec.Sha3.pad rate (suffix.setWidth 8) msg)) →
      Q s') :
    WP isa padCall s Q := by
  refine WP.frame (rs := [.lr]) (r := .r12) rfl (by simpa using (show 4 ≤ s.sp.toNat by have := h.sp; omega))
    (by decide) ?_
  have hr := rates_lt h.hrate
  have hp := h.hpos
  have fA := push1_frame h.sp
  refine WP.callCalls (k := Proof.Sha3.padArm) Proof.Sha3.Arm.Stream.Pad.pad_verified.1
    (pad_pre h) (cov_push1 h.sp h.cw)
    (fun x n hi => by
      obtain ⟨r', hr', hc'⟩ := h.cw x n hi
      exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩) ?_ pad_noFrames
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  simp only [Proof.Sha3.padArm, view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_mem,
    h.r0, h.r1, h.r2, h.r3, toNat_ofNat32 (show rate < 2 ^ 32 by omega),
    toNat_ofNat32 (show pos < 2 ^ 32 by omega), State.callEntry_mem] at hpost
  have hst : ∀ r ∈ [below s 8], (regA st 200).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact h.b_st.symm
  refine hQ _ ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ (fun msg hm hp => ?_)
  · have hr12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr12, hcs r hr hl, pushed_gpr]
  · rw [popped_sp, hsp₂, push1_sp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_mem]
    refine (fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]
    exact hpost msg (by
      unfold Spec.Sha3.Repr at hm ⊢
      rw [Proof.Sha3.stateAt_congr (bytes_frame fA hst (by decide))]; exact hm) hp

theorem pad_ct {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∃ st scr rate pos suffix,
      PadArgs s₁ st scr rate pos suffix ∧ PadArgs s₂ st scr rate pos suffix) :
    RelCT isa P padCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP s₁ s₂ h).1) ?_
  refine RelCT.mono (P := fun a b => ∃ x : BitVec 32 × BitVec 32 × Nat × Nat × BitVec 32 × BitVec 32,
      ∃ s₁ s₂, s₁.sp = x.2.2.2.2.2 ∧ s₂.sp = x.2.2.2.2.2 ∧
        PadArgs s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 ∧
        PadArgs s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 ∧
        a = pushed [.lr] s₁ ∧ b = pushed [.lr] s₂) ?_ ?_ (fun _ _ h => h)
  · refine RelCT.exists_ fun ⟨st, scr, rate, pos, suffix, sp⟩ => ?_
    refine RelCT.call (k := Proof.Sha3.padArm) Proof.Sha3.Arm.Stream.Pad.pad_verified.1
      Proof.Sha3.Arm.Stream.Pad.pad_verified.2.1
      [⟨State.addr sp - BitVec.ofNat 64 4, 4⟩] [regA st 200, regA scr 640] ?_
    rintro a b ⟨s₁, s₂, e₁, e₂, h₁, h₂, rfl, rfl⟩
    dsimp only at e₁ e₂ h₁ h₂
    have v₁ : (pushed [.lr] s₁).callEntry.withRegions [⟨State.addr sp - BitVec.ofNat 64 4, 4⟩]
        [regA st 200, regA scr 640] = padView s₁ st scr := by simp only [padView, below, e₁]
    have v₂ : (pushed [.lr] s₂).callEntry.withRegions [⟨State.addr sp - BitVec.ofNat 64 4, 4⟩]
        [regA st 200, regA scr 640] = padView s₂ st scr := by simp only [padView, below, e₂]
    rw [v₁, v₂]
    obtain ⟨a₀, a₁⟩ := push1_arg (t := padView s₁ st scr) h₁.sp (push1_sp s₁) rfl
    obtain ⟨b₀, b₁⟩ := push1_arg (t := padView s₂ st scr) h₂.sp (push1_sp s₂) rfl
    have c₁ := cov_push1 h₁.sp h₁.cw
    have c₂ := cov_push1 h₂.sp h₂.cw
    simp only [below, e₁, e₂] at c₁ c₂
    refine ⟨pad_pre h₁, pad_pre h₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, ?_, c₂, ?_⟩
    · simp only [State.withRegions_sp, State.callEntry_sp, push1_sp, e₁, e₂]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r0, h₂.r0]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r1, h₂.r1]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r2, h₂.r2]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r3, h₂.r3]
    · rw [a₁, b₁, h₁.lr, h₂.lr]
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₁.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₂.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
  · rintro a b ⟨s₁, s₂, hp, pa, pb⟩
    obtain ⟨hsp, st, scr, rate, pos, suffix, h₁, h₂⟩ := hP s₁ s₂ hp
    exact ⟨⟨st, scr, rate, pos, suffix, s₁.sp⟩, s₁, s₂, rfl, hsp.symm, h₁, h₂, push_eq pa, push_eq pb⟩

/-! ## `vg_keccak_squeeze` -/

/-- What a call of `vg_keccak_squeeze` in its frame needs. -/
structure SqueezeArgs (s : State) (st scr out : BitVec 32) (rate pos len : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 pos
  r3 : s.gpr .r3 = out
  r12 : s.gpr .r12 = BitVec.ofNat 32 len
  lr : s.gpr .lr = scr
  hrate : rate ∈ rates
  hpos : pos ≤ rate
  hlen : len < 2 ^ 32
  sp : 8 ≤ s.sp.toNat
  fst : st.toNat + 200 ≤ 2 ^ 32
  fout : out.toNat + len ≤ 2 ^ 32
  fscr : scr.toNat + 640 ≤ 2 ^ 32
  d_st_out : (regA st 200).Disjoint (regA out len)
  d_st_scr : (regA st 200).Disjoint (regA scr 640)
  d_out_scr : (regA out len).Disjoint (regA scr 640)
  b_st : (below s 8).Disjoint (regA st 200)
  b_out : (below s 8).Disjoint (regA out len)
  b_scr : (below s 8).Disjoint (regA scr 640)
  cw : Covers [regA st 200, regA out len, regA scr 640] s.wr

abbrev squeezeView (s : State) (st scr out : BitVec 32) (len : Nat) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions [below s 8] [regA st 200, regA out len, regA scr 640]

theorem squeeze_pre {s : State} {st scr out : BitVec 32} {rate pos len : Nat}
    (h : SqueezeArgs s st scr out rate pos len) : Proof.Sha3.squeezeArm.pre (squeezeView s st scr out len) := by
  obtain ⟨a0, a1, a2⟩ := push2_arg (t := squeezeView s st scr out len) h.sp (push2_sp s) rfl
  have hr := rates_lt h.hrate
  have hp := h.hpos
  simp only [Proof.Sha3.squeezeArm, view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, a0, a1, a2, h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, toNat_ofNat32 h.hlen,
    toNat_ofNat32 (show rate < 2 ^ 32 by omega), toNat_ofNat32 (show pos < 2 ^ 32 by omega),
    State.callEntry_sp, push2_sp]
  refine ⟨trivial, trivial, h.d_st_out, h.d_st_scr, h.d_out_scr, h.b_st, h.b_out, h.b_scr, h.fst, h.fout,
    h.fscr, ?_, h.hrate, h.hpos⟩
  have := h.sp; have := s.sp.isLt; bv_omega

theorem cov_squeeze {s : State} (hsp : 8 ≤ s.sp.toNat) {ws : List Region} (hw : Covers ws s.wr) :
    Covers ([below s 8] ++ ws) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) :=
  cov_push hsp rfl (rs := []) (fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil) hw _ rfl

theorem squeeze_ok {s : State} {st scr out : BitVec 32} {rate pos len : Nat}
    (h : SqueezeArgs s st scr out rate pos len) {Q : State → Prop}
    (hQ : ∀ s', Kept [regA st 200, regA out len, regA scr 640, below s 8] s s' →
      Spec.Sha3.bytesAt s'.mem (State.addr out) len = squeezeFrom rate (stateAt s.mem (State.addr st)) pos len →
      (s'.gpr .r0).toNat ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s'.mem (State.addr st)) (s'.gpr .r0).toNat d =
        squeezeFrom rate (stateAt s.mem (State.addr st)) (pos + len) d) → Q s') :
    WP isa squeezeCall s Q := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.sp) (by decide) ?_
  obtain ⟨a0, a1, a2⟩ := push2_arg (t := squeezeView s st scr out len) h.sp (push2_sp s) rfl
  have hr := rates_lt h.hrate
  have hp := h.hpos
  have hl := h.hlen
  have fA := push2_frame h.sp
  refine WP.callCalls (k := Proof.Sha3.squeezeArm) Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1
    (squeeze_pre h) (cov_squeeze h.sp h.cw)
    (fun x n hi => by
      obtain ⟨r', hr', hc'⟩ := h.cw x n hi
      exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩) ?_ squeeze_noFrames
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  simp only [Proof.Sha3.squeezeArm, view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_mem, State.withRegions_gpr,
    a1, h.r0, h.r1, h.r2, h.r3, h.r12, toNat_ofNat32 h.hlen, toNat_ofNat32 (show rate < 2 ^ 32 by omega),
    toNat_ofNat32 (show pos < 2 ^ 32 by omega), State.callEntry_mem] at hpost
  have hst : ∀ r ∈ [below s 8], (regA st 200).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact h.b_st.symm
  have est : stateAt (pushed [.r12, .lr] s).mem (State.addr st) = stateAt s.mem (State.addr st) :=
    Proof.Sha3.stateAt_congr (bytes_frame fA hst (by decide))
  rw [est] at hpost
  obtain ⟨p1, p2, p3⟩ := hpost
  refine hQ _ ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
  · have hr12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr12, hcs r hr hl, pushed_gpr]
  · rw [popped_sp, hsp₂, push2_sp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_mem]
    refine (fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact p1
  · rw [popped_gpr (by decide)]; exact p2
  · rw [popped_gpr (by decide), popped_mem]; exact p3

theorem squeeze_ct {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∃ st scr out rate pos len,
      SqueezeArgs s₁ st scr out rate pos len ∧ SqueezeArgs s₂ st scr out rate pos len) :
    RelCT isa P squeezeCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP s₁ s₂ h).1) ?_
  refine RelCT.mono (P := fun a b => ∃ x : BitVec 32 × BitVec 32 × BitVec 32 × Nat × Nat × Nat × BitVec 32,
      ∃ s₁ s₂, s₁.sp = x.2.2.2.2.2.2 ∧ s₂.sp = x.2.2.2.2.2.2 ∧
        SqueezeArgs s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 ∧
        SqueezeArgs s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 ∧
        a = pushed [.r12, .lr] s₁ ∧ b = pushed [.r12, .lr] s₂) ?_ ?_ (fun _ _ h => h)
  · refine RelCT.exists_ fun ⟨st, scr, out, rate, pos, len, sp⟩ => ?_
    refine RelCT.call (k := Proof.Sha3.squeezeArm) Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1
      Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.2.1
      [⟨State.addr sp - BitVec.ofNat 64 8, 8⟩] [regA st 200, regA out len, regA scr 640] ?_
    rintro a b ⟨s₁, s₂, e₁, e₂, h₁, h₂, rfl, rfl⟩
    dsimp only at e₁ e₂ h₁ h₂
    have v₁ : (pushed [.r12, .lr] s₁).callEntry.withRegions [⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
        [regA st 200, regA out len, regA scr 640] = squeezeView s₁ st scr out len := by
      simp only [squeezeView, below, e₁]
    have v₂ : (pushed [.r12, .lr] s₂).callEntry.withRegions [⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
        [regA st 200, regA out len, regA scr 640] = squeezeView s₂ st scr out len := by
      simp only [squeezeView, below, e₂]
    rw [v₁, v₂]
    obtain ⟨a₀, a₁, a₂⟩ := push2_arg (t := squeezeView s₁ st scr out len) h₁.sp (push2_sp s₁) rfl
    obtain ⟨b₀, b₁, b₂⟩ := push2_arg (t := squeezeView s₂ st scr out len) h₂.sp (push2_sp s₂) rfl
    have c₁ := cov_squeeze h₁.sp h₁.cw
    have c₂ := cov_squeeze h₂.sp h₂.cw
    simp only [below, e₁, e₂] at c₁ c₂
    refine ⟨squeeze_pre h₁, squeeze_pre h₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, ?_, c₂, ?_⟩
    · simp only [State.withRegions_sp, State.callEntry_sp, push2_sp, e₁, e₂]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r0, h₂.r0]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r1, h₂.r1]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r2, h₂.r2]
    · rw [view_gpr _ _ _ _ (by decide), view_gpr _ _ _ _ (by decide), h₁.r3, h₂.r3]
    · rw [a₁, b₁, h₁.r12, h₂.r12]
    · rw [a₂, b₂, h₁.lr, h₂.lr]
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₁.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₂.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
  · rintro a b ⟨s₁, s₂, hp, pa, pb⟩
    obtain ⟨hsp, st, scr, out, rate, pos, len, h₁, h₂⟩ := hP s₁ s₂ hp
    exact ⟨⟨st, scr, out, rate, pos, len, s₁.sp⟩, s₁, s₂, rfl, hsp.symm, h₁, h₂, push_eq pa, push_eq pb⟩

end VG.Proof.MlKem.Arm
