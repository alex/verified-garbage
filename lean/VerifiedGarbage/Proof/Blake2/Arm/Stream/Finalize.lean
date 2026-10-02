import VerifiedGarbage.Proof.Blake2.Arm.Stream.Update

/-!
# Streaming BLAKE2 on ARMv7: `finalize`

The functional correctness of `finalize`, for either word size and any correct
compression function (`CalleeOk`), piece by piece, as for `update`: the
prologue, which zeroes the rest of the buffer and sets up the call (`pro_ok`),
the call (`call_ok'`) and the end, which copies the hash value to `out`
(`end_ok`).
-/

namespace VG.Proof.Blake2.Arm.Stream.Finalize

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (N B lbb saved save restore call zeroLoop finalizePro finalizeEnd finalize)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldr wp_str
  wp_ldrSp sub_ofNat cmp0 eval_eq eval_ne)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (bufLen bufLen_le bufLen_le_self final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state bytesAt_words wordBytes_readW finalizeArm countArm)
open VG.Proof.Blake2.Arm.Stream.Update (bufLen_ok)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev stA : Addr := State.addr (st s₀)
abbrev out : BitVec 32 := stackArg s₀ 0
abbrev outA : Addr := State.addr (out s₀)
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev scA : Addr := State.addr (scr s₀)
abbrev cnt : Nat := (countArm s₀).toNat
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨outA s₀, bufOff w⟩
abbrev scR : Region := ⟨scA s₀, 576⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The buffer. -/
abbrev buf (w : Nat) : Addr := stA s₀ + BitVec.ofNat 64 (bufOff w)

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀ w, outR s₀ w, scR s₀]
  st_out : (stR s₀ w).Disjoint (outR s₀ w)
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  out_scr : (outR s₀ w).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  a_out : (argR s₀).Disjoint (outR s₀ w)
  a_scr : (argR s₀).Disjoint (scR s₀)
  w_st : (below s₀).Disjoint (stR s₀ w)
  w_out : (below s₀).Disjoint (outR s₀ w)
  w_scr : (below s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  out_fit : (out s₀).toNat + bufOff w ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (finalizeArm P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem cnt_lt (s₀ : State) : cnt s₀ < 2 ^ 64 := (countArm s₀).isLt

/-- What holds throughout. -/
structure Common (w : Nat) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = st s₀
  r5 : s.gpr .r5 = scr s₀
  r6 : s.gpr .r6 = out s₀
  cn : s.gpr .r10 ++ s.gpr .r9 = BitVec.ofNat 64 (cnt s₀)
  frame : Frame [stR s₀ w, scR s₀, below s₀] s₀.mem s.mem
  saved : Saved (scA s₀) s₀.gpr s.mem

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.r4, .r5, .r6, .r9, .r10]

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common w s₀ s)
    (hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common w s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r4 := by rw [hg _ (by simp)]; exact h.r4
  r5 := by rw [hg _ (by simp)]; exact h.r5
  r6 := by rw [hg _ (by simp)]; exact h.r6
  cn := by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact h.cn
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Common.of_upd {s₀ : State} {s s' : State} (h : Common w s₀ s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ commonRegs := by decide) : Common w s₀ s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem saved_frame {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved (scA s₀) s₀.gpr m)
    (hf : Frame [stR s₀ w, ⟨scA s₀, 512⟩, below s₀] m m') : Saved (scA s₀) s₀.gpr m' := by
  have := hp.scr_fit
  refine h.frame saved_slots hf fun r' hr' => ?_
  have e : Region.Sub ⟨scA s₀ + BitVec.ofNat 64 512, 548 - 512⟩ (scR s₀) := Offset.sub_base _ (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left e
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact hp.w_scr.symm.sub_left e

/-! ## The prologue -/

abbrev prologue : List Instr :=
  [.ldrSp .r12 4] ++ save .r12 ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r12), .ldrSp .r6 0,
    .mov .r9 (.reg .r2), .mov .r10 (.reg .r3)]

theorem argAddr_eq {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 2) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_off _ (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 2) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact Offset.sub_base _ (by omega)

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block prologue) s₀ fun s => Common w s₀ s ∧
      ∀ i < bufOff w + blockBytes w, s.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i) := by
  have hsc := hp.scr_fit
  simp only [prologue, List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact contains_off _ (by omega) (by omega)⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  have hframe : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]; exact saveMem_frame _ _ _
  have harg : ∀ k, k < 2 → s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := fun k hk =>
    hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (arg_sub hp hk))) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide)) fun s₅ u₅ => ?_
  refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have mm : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, g₂, u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), g₂, h12]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, harg 0 (by decide)]
  · have h9 : s₇.gpr .r9 = s₀.gpr .r2 := by
      rw [u₇.other .r9 (by decide), u₆.gpr, u₅.other .r2 (by decide), u₄.other .r2 (by decide),
        u₃.other .r2 (by decide), g₂, u₁.other .r2 (by decide)]
    have h10 : s₇.gpr .r10 = s₀.gpr .r3 := by
      rw [u₇.gpr, u₆.other .r3 (by decide), u₅.other .r3 (by decide), u₄.other .r3 (by decide),
        u₃.other .r3 (by decide), g₂, u₁.other .r3 (by decide)]
    rw [h9, h10, cnt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  · rw [mm]; exact hframe.mono (by simp)
  · intro p hp'
    rw [mm, m₂, u₁.mem, h12, saveMem_saved _ _ _ p hp', u₁.other _ (Ne.symm ?_)]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · intro i hi
    rw [mm]
    exact hframe.bytes (R := stR s₀ w) (by simpa using hp.st_scr)
      (by show bufOff w + blockBytes w ≤ 2 ^ 64; have := hp.st_fit; omega) hi

/-! ## Padding the buffer with zeros -/

/-- The state, with its buffer padded: the hash value and the first `r`
bytes of the buffer as on entry, then zeros. -/
structure Padded (w : Nat) (s₀ : State) (s : State) : Prop extends Common w s₀ s where
  st : stateAt w s.mem (stA s₀) = stateAt w s₀.mem (stA s₀)
  buf : bytesAt s.mem (buf s₀ w) (blockBytes w) =
    bytesAt s₀.mem (buf s₀ w) (bufLen w (cnt s₀)) ++ List.replicate (blockBytes w - bufLen w (cnt s₀)) 0

theorem pad_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ s)
    (hst : ∀ i < bufOff w + blockBytes w, s.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i))
    (h8 : s.gpr .r8 = BitVec.ofNat 32 (bufLen w (cnt s₀))) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t, Padded w s₀ t → WP isa rest t Q) :
    WP isa (.seq (.block [.mov .r12 (.imm 0), .mov .r11 (.imm (BitVec.ofNat 32 (B w))), .subs .r11 .r11 (.reg .r8)])
      (.seq (.ite .eq (.block []) (zeroLoop (w := w))) rest)) s Q := by
  have hl := hP.len
  have hst' := hp.st_fit
  have hr := bufLen_le (w := w) hP.pos (cnt s₀)
  obtain ⟨r, hrr⟩ : ∃ r, r = bufLen w (cnt s₀) := ⟨_, rfl⟩
  rw [← hrr] at h8 hr
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm hP.encB) fun s₂ u₂ =>
    wp_subs (op2_reg _ _) fun s₃ u₃ z₃ => WP.block_nil ?_)
  have hC₃ : Common w s₀ s₃ := ((hC.of_upd u₁).of_upd u₂).of_upd u₃
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have h11 : s₃.gpr .r11 = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h8, B_eq, sub_ofNat hr]
  have hz : isa.eval .eq s₃ = some (decide (blockBytes w - r = 0)) := by
    show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, ← u₃.gpr, h11, MdStream.Arm.ofNat_beq_zero (by omega)]
  -- The facts about the bytes, from the memory after zeroing `k` bytes.
  have hpad : ∀ m : Mem, m = writeBytes s.mem (buf s₀ w + BitVec.ofNat 64 r) (List.replicate (blockBytes w - r) 0) →
      Frame [stR s₀ w] s.mem m ∧ stateAt w m (stA s₀) = stateAt w s₀.mem (stA s₀) ∧
      bytesAt m (buf s₀ w) (blockBytes w) =
        bytesAt s₀.mem (buf s₀ w) r ++ List.replicate (blockBytes w - r) 0 := by
    intro m hm
    have hwf : Frame [stR s₀ w] s.mem m := by
      rw [hm, Offset.add_add]
      exact writeBytes_frame _ _ _ (by simp only [List.length_replicate]; exact contains_off _ (by omega) (by omega))
    refine ⟨hwf, ?_, ?_⟩
    · rw [hm, Offset.add_add]
      refine (stateAt_congr fun i hi => ?_).trans (stateAt_congr fun i hi => hst i (by omega))
      exact writeBytes_before _ _ _ (by omega) (by simp; omega)
    · have := Arm.Stream.bytesAt_writeBytes s.mem (buf s₀ w) r (List.replicate (blockBytes w - r) 0)
        (by simp; omega)
      simp only [List.length_replicate, show r + (blockBytes w - r) = blockBytes w by omega] at this
      rw [hm, this]
      refine congrArg (· ++ _) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]; exact hst _ (by omega)
  refine WP.seq (WP.mono (Q := Padded w s₀) (WP.ite _ hz (fun hb => ?_) (fun hb => ?_)) k)
  · simp only [decide_eq_true_eq] at hb
    obtain ⟨hwf, h1, h2⟩ := hpad s₃.mem (by rw [hm₃, hb, List.replicate_zero, WriteBytes.writeBytes_nil])
    exact WP.block_nil ⟨hC₃, h1, by rw [← hrr]; exact h2⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine zeroLoop_ok (st := st s₀) (r := r) (k := blockBytes w - r) hl.2.1 (by omega) (by omega) (hC₃.r4) (by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h8]) h11
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
      (fun i hi => ⟨stR s₀ w, by simp [hC₃.wr, hp.wr], by
        rw [Offset.add_add]; exact contains_off _ (by omega) (by omega)⟩) fun s' h => ?_
    have hm' : s'.mem = writeBytes s.mem (buf s₀ w + BitVec.ofNat 64 r) (List.replicate (blockBytes w - r) 0) := by
      rw [h.mem, hm₃, Offset.add_add]
    obtain ⟨hwf, h1, h2⟩ := hpad s'.mem hm'
    have hg : ∀ x ∈ commonRegs, s'.gpr x = s₃.gpr x := fun x hx => h.other x
      (fun e => by subst e; simp at hx) (fun e => by subst e; simp at hx) (fun e => by subst e; simp at hx)
    refine ⟨⟨h.rd.trans hC₃.rd, h.wr.trans hC₃.wr, h.sp.trans hC₃.sp, by rw [hg _ (by simp)]; exact hC₃.r4,
      by rw [hg _ (by simp)]; exact hC₃.r5, by rw [hg _ (by simp)]; exact hC₃.r6,
      by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact hC₃.cn,
      hC.frame.trans (hwf.mono (by simp)), saved_frame hp hC.saved (hwf.mono (by simp))⟩, h1,
      by rw [← hrr]; exact h2⟩

/-! ## Up to the call -/

/-- What holds before the call. -/
def PostPro (w : Nat) (s₀ s : State) : Prop :=
  Padded w s₀ s ∧
    CallArgs (w := w) s (st s₀) (scr s₀) (st s₀ + BitVec.ofNat 32 (bufOff w)) 1 (BitVec.ofNat 64 (cnt s₀)) 1

theorem pro_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) :
    WP isa (finalizePro (w := w)) s₀ (PostPro w s₀) := by
  have hl := hP.len
  have hst := hp.st_fit; have hsc := hp.scr_fit
  unfold finalizePro
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hstb⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_ok hP (cnt_lt s₀) hC.cn) fun s₂ ⟨h8, g, m, rd, wr, sp⟩ => ?_)
  have hC₂ := hC.of_gpr (fun r hr => g r (fun e => by subst e; simp at hr) (fun e => by subst e; simp at hr))
    m rd wr sp
  refine pad_ok hP hp hC₂ (fun i hi => by rw [m]; exact hstb i hi) h8 fun s₃ hP₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_add (op2_imm hP.encN) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ =>
    wp_mov (op2_reg _ _) fun s₈ u₈ => wp_mov (op2_imm (by decide)) fun s₉ u₉ =>
    wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => WP.block_nil ?_
  have hC' : Common w s₀ s₁₀ :=
    ((((((hP₃.toCommon.of_upd u₄).of_upd u₅).of_upd u₆).of_upd u₇).of_upd u₈).of_upd u₉).of_upd u₁₀
  have hm : s₁₀.mem = s₃.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  refine ⟨⟨hC', by rw [hm]; exact hP₃.st, by rw [hm]; exact hP₃.buf⟩, ?_⟩
  have eN : Region.Sub ⟨stA s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have eS : Region.Sub ⟨scA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  have eB : Region.Sub ⟨State.addr (st s₀ + BitVec.ofNat 32 (bufOff w)), blockBytes w * 1⟩ (stR s₀ w) := by
    rw [addr_add (by omega), Nat.mul_one]; exact Offset.sub_base _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by rw [hC'.sp]; exact hp.sp16, ?_, ?_,
    (hp.st_scr.sub_left eN).sub_right eS, ?_, (hp.st_scr.sub_left eB).sub_right eS, ?_, ?_, ?_, by omega,
    by rw [toNat_add_ofNat (by omega)]; omega, by omega⟩
  all_goals try simp only [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
    u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, ne_eq, reduceCtorEq, not_false_eq_true, hP₃.r4, hP₃.r5, N_eq]
  all_goals first | rfl | exact hP₃.cn | skip
  · rw [hC'.rd, hC'.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨stR s₀ w, by simp, bufOff w, addr_add (by omega), by dsimp only; omega⟩
  · rw [hC'.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [addr_add (by omega), Nat.mul_one]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · rw [below, hC'.sp]; exact hp.w_st.sub_right eN
  · rw [below, hC'.sp]; exact hp.w_st.sub_right eB
  · rw [below, hC'.sp]; exact hp.w_scr.sub_right eS

/-! ## The call -/

/-- What holds after the call. -/
def Mid (P : Params w) (s₀ s : State) : Prop :=
  Common w s₀ s ∧ ∀ h0 d, Spec.Blake2.Repr P h0 s₀.mem (stA s₀) d → d.length < 2 ^ 64 →
    countArm s₀ = BitVec.ofNat 64 d.length →
    (stateAt w s.mem (stA s₀)).toList.flatMap wordBytes = finalHash P h0 d

theorem call_ok' (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} (h : PostPro w s₀ s) : WP isa (call name code) s (Mid P s₀) := by
  have hl := hP.len
  have hst := hp.st_fit; have hsc := hp.scr_fit
  obtain ⟨hpd, hca⟩ := h
  refine call_ok hf hca fun s' ha hstate => ⟨?_, fun h0 d hr hl' hc => ?_⟩
  · have hf' : Frame [stR s₀ w, ⟨scA s₀, 512⟩, below s₀] s.mem s'.mem := by
      have := ha.frame
      rw [below, hpd.sp] at this
      exact this.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨⟨scA s₀, 512⟩, by simp, fun _ h => h⟩
        · exact ⟨below s₀, by simp, fun _ h => h⟩
    have hcp : ∀ r ∈ commonRegs, r ∈ preserved ∧ r ≠ .lr := by decide
    have hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r := fun r hr => ha.cs r (hcp r hr).1 (hcp r hr).2
    exact ⟨ha.rd.trans hpd.rd, ha.wr.trans hpd.wr, ha.sp.trans hpd.sp, by rw [hg _ (by simp)]; exact hpd.r4,
      by rw [hg _ (by simp)]; exact hpd.r5, by rw [hg _ (by simp)]; exact hpd.r6,
      by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact hpd.cn,
      hpd.frame.trans (hf'.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
        · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨below s₀, by simp, fun _ h => h⟩),
      saved_frame hp hpd.saved hf'⟩
  · have ecnt : cnt s₀ = d.length := by
      rw [cnt, hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl']
    rw [hstate, Update.compressBlocks_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (cnt_lt s₀), ecnt,
      addr_add (by omega)]
    refine final_eq P hP.pos hr hpd.st ?_
    rw [← ecnt]; exact hpd.buf

/-! ## The end -/

/-- Copying the first `n` words of the hash value to `out`. -/
structure CopyW (s₀ s : State) (n : Nat) (s' : State) : Prop where
  other : ∀ r, r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [outR s₀ w] s.mem s'.mem
  words : ∀ j < n, s'.mem.readW (outA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    s.mem.readW (stA s₀ + BitVec.ofNat 64 (4 * j)) 32

theorem copyW_all (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ s) :
    ∀ n ≤ bufOff w / 4, WP isa (.block ((List.range n).flatMap
      (fun k => [.ldr .r12 .r4 (4 * k), .str .r12 .r6 (4 * k)]))) s (CopyW (w := w) s₀ s n) := by
  have hl := hP.len
  have hst := hp.st_fit; have hof := hp.out_fit
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have h4 : t.gpr .r4 = st s₀ := by rw [h.other _ (by decide), hC.r4]
    have h6 : t.gpr .r6 = out s₀ := by rw [h.other _ (by decide), hC.r6]
    refine wp_ldr (a := stA s₀ + BitVec.ofNat 64 (4 * n)) (by omega) (by rw [h4, addr_add (by omega)])
      ⟨stR s₀ w, by simp [h.rd, h.wr, hC.rd, hC.wr, hp.wr], contains_off _ (by omega) (by omega)⟩
      fun t₁ u₁ => ?_
    refine wp_str (a := outA s₀ + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₁.other _ (by decide), h6, addr_add (by omega)])
      ⟨outR s₀ w, by simp [u₁.wr, h.wr, hC.wr, hp.wr], contains_off _ (by omega) (by omega)⟩
      fun t₂ u₂ => WP.block_nil ?_
    have hfw : Frame [outR s₀ w] t.mem t₂.mem := by
      rw [u₂.mem, u₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off _ (by omega) (by omega))
    -- The state is not in `out`.
    have hsb : ∀ j < bufOff w / 4, t.mem.readW (stA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
        s.mem.readW (stA s₀ + BitVec.ofNat 64 (4 * j)) 32 := fun j hj =>
      h.frame.readW (r := ⟨stA s₀ + BitVec.ofNat 64 (4 * j), 4⟩) (Region.contains_self _ _)
        (by simp only [List.mem_singleton]; rintro r rfl
            exact hp.st_out.sub_left (Offset.sub_base _ (by omega))) (by decide)
    refine ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr, h.other r hr], by rw [u₂.rd, u₁.rd, h.rd],
      by rw [u₂.wr, u₁.wr, h.wr], by rw [u₂.sp, u₁.sp, h.sp], h.frame.trans hfw, fun j hj => ?_⟩
    rw [u₂.mem, u₁.mem, u₁.gpr]
    by_cases e : j = n
    · subst e; rw [Mem.readW_writeW_self32, hsb j (by omega)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.words j (by omega)

theorem end_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (h : Mid P s₀ s) :
    WP isa (.block (finalizeEnd (w := w))) s fun s' => abiPreserved s₀ s' ∧ (finalizeArm P).post s₀ s' := by
  have hl := hP.len
  have hst := hp.st_fit; have hof := hp.out_fit; have hsc := hp.scr_fit
  obtain ⟨hC, hfin⟩ := h
  unfold finalizeEnd
  rw [WP.block_append_iff]
  refine WP.mono (copyW_all hP hp hC _ (Nat.le_refl _)) fun t ht => ?_
  have h5 : t.gpr .r5 = scr s₀ := by rw [ht.other _ (by decide), hC.r5]
  have hsv : Saved (scA s₀) s₀.gpr t.mem := by
    intro p hp'
    have hoff := saved_bound p hp'
    rw [← hC.saved p hp']
    refine ht.frame.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton]; rintro r rfl
    exact hp.out_scr.symm.sub_left (Offset.sub_base _ (by omega))
  refine restore_ok h5 hsc (fun d hd₁ hd₂ => ⟨scR s₀, by simp [ht.rd, ht.wr, hC.rd, hC.wr, hp.wr],
      contains_off _ (by omega) (by omega)⟩) s₀.gpr hsv
    fun s' hs hmem _ _ hsp => ⟨⟨preserved_of hs, by rw [hsp, ht.sp, hC.sp]⟩, fun h0 d hr hl' hc => ?_⟩
  rw [← hfin h0 d hr hl' hc, ← bytesAt_state _ _ (by rcases hP.w with h | h <;> simp [h]), hmem]
  -- The words of `out` are those of the hash value.
  have e4 : bufOff w = 4 * (bufOff w / 4) := by omega
  rw [e4, show (4 : Nat) = 32 / 8 from rfl, bytesAt_words, bytesAt_words]
  rw [List.flatMap, List.flatMap]
  refine congrArg _ (List.map_congr_left fun j hj => ?_)
  have hj := List.mem_range.mp hj
  rw [← wordBytes_readW _ _ (.inl rfl), ← wordBytes_readW _ _ (.inl rfl)]
  exact congrArg _ (ht.words j hj)

/-! ## `finalize` -/

theorem correct (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) :
    WP isa (finalize (w := w) name code) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeArm P).post s₀ s' :=
  WP.seq (WP.mono (pro_ok hP hp) fun _ h₁ => WP.seq (WP.mono (call_ok' hP hf hp h₁) fun _ h₂ =>
    end_ok hP hp h₂))

end VG.Proof.Blake2.Arm.Stream.Finalize
