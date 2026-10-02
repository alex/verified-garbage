import VerifiedGarbage.Proof.Blake2.Arm.Stream.Common

/-!
# Streaming BLAKE2 on ARMv7: `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`), piece by piece: the prologue, up to the
first call (`pro_ok`), the first call (`call₁_ok`), the code between the calls
(`mid_ok`), the second call (`call₂_ok`) and the end (`end_ok`). Each piece's
postcondition gives the registers the next one starts from as functions of the
arguments, which the constant-time proof (`CT.lean`) uses too.
-/

namespace VG.Proof.Blake2.Arm.Stream.Update

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (N B lbb saved save restore call copyLoop copy fill args updatePro
  updateMid updateEnd update)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_and wp_orr
  wp_subs wp_cmp wp_ldrSp ofNat_beq_zero sub_ofNat cmp0 eval_eq eval_ne)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen bufLen_le bufLen_le_self bufLen_pos repr_iff reprR_append reprR_flush
  reprR_blocks repr_of_reprR stateAt_congr bytesAt_congr bytesAt_add updateArm countArm compressBlocks_zero)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev stA : Addr := State.addr (st s₀)
abbrev dp : BitVec 32 := stackArg s₀ 0
abbrev dA : Addr := State.addr (dp s₀)
abbrev len : Nat := (stackArg s₀ 1).toNat
abbrev scr : BitVec 32 := stackArg s₀ 2
abbrev scA : Addr := State.addr (scr s₀)
abbrev cnt : Nat := (countArm s₀).toNat
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨scA s₀, 576⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 12⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dA s₀) c

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR s₀ w, scR s₀]
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀ w)
  d_scr : (dR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  a_scr : (argR s₀).Disjoint (scR s₀)
  w_st : (below s₀).Disjoint (stR s₀ w)
  w_d : (below s₀).Disjoint (dR s₀)
  w_scr : (below s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 12 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (updateArm P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (stackArg s₀ 1).isLt
theorem cnt_lt (s₀ : State) : cnt s₀ < 2 ^ 64 := (countArm s₀).isLt

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (stA s₀) d ∧ countArm s₀ = BitVec.ofNat 64 d.length ∧
    d.length + len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) :
    cnt s₀ = d.length := by
  rw [cnt, h.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.2.2; omega)]

theorem R₀.length {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) (c : Nat) :
    (d ++ D s₀ c).length = cnt s₀ + c := by
  rw [List.length_append, Arm.Stream.bytesAt_length, h.cnt_eq]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = st s₀
  r5 : s.gpr .r5 = scr s₀
  r6 : s.gpr .r6 = dp s₀ + BitVec.ofNat 32 c
  r7 : s.gpr .r7 = BitVec.ofNat 32 (len s₀ - c)
  cn : s.gpr .r10 ++ s.gpr .r9 = BitVec.ofNat 64 (cnt s₀ + c)
  frame : Frame [stR s₀ w, scR s₀, below s₀] s₀.mem s.mem
  saved : Saved (scA s₀) s₀.gpr s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends Common w s₀ c s where
  r8 : s.gpr .r8 = BitVec.ofNat 32 r
  repr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (stA s₀) (d ++ D s₀ c) r

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.r4, .r5, .r6, .r7, .r9, .r10]

theorem notC {r : Reg} (hr : r ∈ commonRegs) (x : Reg) (hx : x ∉ commonRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r4 := by rw [hg _ (by simp)]; exact h.r4
  r5 := by rw [hg _ (by simp)]; exact h.r5
  r6 := by rw [hg _ (by simp)]; exact h.r6
  r7 := by rw [hg _ (by simp)]; exact h.r7
  cn := by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact h.cn
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s)
    (hg : ∀ r ∈ .r8 :: commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv P s₀ c r s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_cons_of_mem _ hr)) hm hrd hwr hsp with
    r8 := by rw [hg _ (by simp)]; exact h.r8
    repr := by rw [hm]; exact h.repr }

/-- `Inv` after an instruction writing a register it is not about. -/
theorem Inv.of_upd {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ .r8 :: commonRegs := by decide) : Inv P s₀ c r s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Inv.of_flags {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s) (u : Fupd s s') :
    Inv P s₀ c r s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = s₀.mem (dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.w_d.symm⟩)
    (by show len s₀ ≤ 2 ^ 64; have := len_lt s₀; omega) hi

/-- Writes to the state, the compression function's scratch space and the
16 bytes below the stack pointer keep the saved registers. -/
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

/-- The prologue, but for `bufLen` and what follows it. -/
abbrev prologue : List Instr :=
  [.ldrSp .r12 8] ++ save .r12 ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r12), .ldrSp .r6 0, .ldrSp .r7 4,
    .mov .r9 (.reg .r2), .mov .r10 (.reg .r3)]

/-- The stack arguments, word by word. -/
theorem argAddr_eq {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 3) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 3) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_off _ (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 3) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact Offset.sub_base _ (by omega)

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block prologue) s₀ fun s => Common w s₀ 0 s ∧
      ∀ i < bufOff w + blockBytes w, s.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i) := by
  have hsc := hp.scr_fit
  simp only [prologue, List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact contains_off _ (by omega) (by omega)⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  -- The save writes only the scratch space.
  have hframe : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]; exact saveMem_frame _ _ _
  have harg : ∀ k, k < 3 → s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := fun k hk =>
    hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (arg_sub hp hk))) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide)) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide)
    (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide))
    fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ?_
  have mm : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨Nat.zero_le _, by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide)]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), g₂, h12]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem,
      harg 0 (by decide)]
    simp
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, harg 1 (by decide)]
    simp
  · have h9 : s₈.gpr .r9 = s₀.gpr .r2 := by
      rw [u₈.other .r9 (by decide), u₇.gpr, u₆.other .r2 (by decide), u₅.other .r2 (by decide),
        u₄.other .r2 (by decide), u₃.other .r2 (by decide), g₂, u₁.other .r2 (by decide)]
    have h10 : s₈.gpr .r10 = s₀.gpr .r3 := by
      rw [u₈.gpr, u₇.other .r3 (by decide), u₆.other .r3 (by decide), u₅.other .r3 (by decide),
        u₄.other .r3 (by decide), u₃.other .r3 (by decide), g₂, u₁.other .r3 (by decide)]
    rw [h9, h10, Nat.add_zero (cnt s₀), cnt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
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

/-! ## The number of bytes in the buffer -/

theorem bufLen_ok (hP : Ok P) {s : State} {x : Nat} (hx : x < 2 ^ 64)
    (hc : s.gpr .r10 ++ s.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa (Impl.Blake2.Arm.Stream.bufLen (w := w)) s fun s' =>
      s'.gpr .r8 = BitVec.ofNat 32 (bufLen w x) ∧
      (∀ r, r ≠ .r8 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold Impl.Blake2.Arm.Stream.bufLen
  have h9 : s.gpr .r9 = BitVec.ofNat 32 x := lo_of_pair hc
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_and (op2_imm hP.encB1) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_orr (op2_reg _ _) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .r8 → r ≠ .r12 → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [f₅.gpr, u₄.other r h2, u₃.other r h1, u₂.other r h1, u₁.other r h1]
  have hm : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₅.rd = s.rd := by rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₅.wr = s.wr := by rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hsp : s₅.sp = s.sp := by rw [f₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have hz : s₅.z = decide (x = 0) := by
    rw [z₅, u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide)]
    exact or_beq_zero hc hx
  refine WP.ite (decide (x = 0)) (by show VG.Arm.eval .eq s₅ = _; rw [eval_eq, hz]) (fun hb => ?_)
    (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ⟨?_, fun r h1 h2 => by
      rw [u₆.other r h1, g r h1 h2], by rw [u₆.mem, hm], by rw [u₆.rd, hrd], by rw [u₆.wr, hwr],
      by rw [u₆.sp, hsp]⟩
    rw [u₆.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil ⟨?_, g, hm, hrd, hwr, hsp⟩
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, h9]
    exact bufLen_lo hP hb

theorem bufLen_inv (hP : Ok P) {s₀ : State} {s : State} (hC : Common w s₀ 0 s)
    (hst : ∀ i < bufOff w + blockBytes w, s.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i)) :
    WP isa (Impl.Blake2.Arm.Stream.bufLen (w := w)) s (Inv P s₀ 0 (bufLen w (cnt s₀))) := by
  have hrepr : ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (stA s₀) (d ++ D s₀ 0) (bufLen w (cnt s₀)) := by
    intro h0 d hd
    have e : D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    exact repr_congr hP hst hd.1
  refine WP.mono (bufLen_ok hP (cnt_lt s₀) hC.cn) fun s' ⟨h8, g, m, rd, wr, sp⟩ => ?_
  exact { hC.of_gpr (fun r hr => g r (notC hr .r8) (notC hr .r12)) m rd wr sp with
    r8 := h8, repr := by rw [m]; exact hrepr }

/-! ## Copying data into the buffer -/

/-- `copy`: copying `k` bytes of data (none if `k = 0`), from byte `c` on,
into the buffer, from byte `r` on. -/
theorem copy_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r k : Nat} (hrk : r + k ≤ blockBytes w)
    (hck : c + k ≤ len s₀) {s : State} (hI : Inv P s₀ c r s) (h11 : s.gpr .r11 = BitVec.ofNat 32 k) :
    WP isa (copy (w := w)) s (Inv P s₀ (c + k) (r + k)) := by
  have hl := hP.len
  have hL := len_lt s₀
  have hst := hp.st_fit; have hdf := hp.d_fit
  unfold copy
  refine WP.seq (wp_sub (op2_reg _ _) fun s₁ u₁ => wp_adds (op2_reg _ _) fun s₂ u₂ c₂ =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ =>
    WP.block_nil ?_)
  have g₄ : ∀ x, x ≠ .r7 → x ≠ .r9 → x ≠ .r10 → s₄.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [f₄.gpr, u₃.other x h3, u₂.other x h2, u₁.other x h1]
  have h7 : s₄.gpr .r7 = BitVec.ofNat 32 (len s₀ - (c + k)) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.r7, h11, sub_ofNat (by omega),
      Nat.sub_sub]
  have hcn : s₄.gpr .r10 ++ s₄.gpr .r9 = BitVec.ofNat 64 (cnt s₀ + (c + k)) := by
    rw [f₄.gpr, u₃.gpr, u₃.other .r9 (by decide), u₂.gpr, u₂.other .r10 (by decide), c₂,
      u₁.other .r9 (by decide), u₁.other .r10 (by decide), u₁.other .r11 (by decide), h11,
      add64_ofNat hI.cn (by omega), Nat.add_assoc]
  have hm₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hsp₄ : s₄.sp = s.sp := by rw [f₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have h4 : s₄.gpr .r4 = st s₀ := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r4]
  have h5 : s₄.gpr .r5 = scr s₀ := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r5]
  have h6 : s₄.gpr .r6 = dp s₀ + BitVec.ofNat 32 c := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r6]
  have h8 : s₄.gpr .r8 = BitVec.ofNat 32 r := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r8]
  have h11' : s₄.gpr .r11 = BitVec.ofNat 32 k := by rw [g₄ _ (by decide) (by decide) (by decide), h11]
  have hz : isa.eval .eq s₄ = some (decide (k = 0)) := by
    show VG.Arm.eval .eq s₄ = _
    rw [eval_eq, z₄, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h11,
      cmp0 (by omega)]
  refine WP.ite (decide (k = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    simp only [Nat.add_zero] at hcn h7 ⊢
    exact WP.block_nil
      { c_le := hI.c_le
        rd := hrd₄.trans hI.rd
        wr := hwr₄.trans hI.wr
        sp := hsp₄.trans hI.sp
        r4 := h4
        r5 := h5
        r6 := h6
        r7 := h7
        cn := hcn
        frame := hm₄ ▸ hI.frame
        saved := hm₄ ▸ hI.saved
        r8 := h8
        repr := hm₄ ▸ hI.repr }
  · simp only [decide_eq_false_iff_not] at hb
    have hcl : c < len s₀ := by omega
    have hsrc : ∀ i < k, InRegions (s₄.rd ++ s₄.wr)
        (State.addr (dp s₀ + BitVec.ofNat 32 c) + BitVec.ofNat 64 i) 1 := fun i hi =>
      ⟨dR s₀, by simp [hrd₄, hI.rd, hp.rd], by
        rw [addr_add (by omega), Offset.add_add]; exact contains_off _ (by omega) (by omega)⟩
    have hdst : ∀ i < k, InRegions s₄.wr (stA s₀ + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1 :=
      fun i hi => ⟨stR s₀ w, by simp [hwr₄, hI.wr, hp.wr], by
        rw [Offset.add_add]; exact contains_off _ (by omega) (by omega)⟩
    have hd : Region.Disjoint ⟨State.addr (dp s₀ + BitVec.ofNat 32 c), k⟩
        ⟨stA s₀ + BitVec.ofNat 64 (bufOff w + r), k⟩ := by
      rw [addr_add (by omega)]
      exact (hp.d_st.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
    refine copyLoop_ok (st := st s₀) hl.2.1 (by omega) (by omega)
      (by rw [toNat_add_ofNat (by omega)]; omega) h4 h6 h8 h11' hsrc hdst hd fun s' h => ?_
    have hx : bytesAt s₄.mem (State.addr (dp s₀ + BitVec.ofNat 32 c)) k =
        bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k := by
      rw [addr_add (by omega), hm₄]
      exact bytesAt_congr fun i hi => by rw [Offset.add_add]; exact hI.data hp (by omega)
    have hmem : s'.mem = writeBytes s.mem (stA s₀ + BitVec.ofNat 64 (bufOff w + r))
        (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k) := by
      rw [h.mem, List.take_of_length_le (by rw [bytesAt_length]), hx, hm₄]
    have hfw : Frame [stR s₀ w] s.mem s'.mem := by
      rw [hmem]
      exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_off _ (by omega) (by omega))
    have g' : ∀ x, x ≠ .r12 → x ≠ .r1 → x ≠ .r6 → x ≠ .r8 → x ≠ .r11 → x ≠ .r7 → x ≠ .r9 → x ≠ .r10 →
        s'.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [h.other x h1 h2 h3 h4 h5, g₄ x h6 h7 h8]
    refine
      { c_le := by omega
        rd := h.rd.trans (hrd₄.trans hI.rd)
        wr := h.wr.trans (hwr₄.trans hI.wr)
        sp := h.sp.trans (hsp₄.trans hI.sp)
        r4 := by rw [g' .r4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hI.r4]
        r5 := by rw [g' .r5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hI.r5]
        r6 := by rw [h.r6, BitVec.add_assoc, ← BitVec.ofNat_add]
        r7 := by rw [h.other .r7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h7
        cn := by
          rw [h.other .r9 (by decide) (by decide) (by decide) (by decide) (by decide),
            h.other .r10 (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hcn
        frame := hI.frame.trans (hfw.mono (by simp))
        saved := saved_frame hp hI.saved (hfw.mono (by simp))
        r8 := h.r8
        repr := fun h0 d hd => ?_ }
    have e : d ++ D s₀ (c + k) = d ++ D s₀ c ++ bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k := by
      rw [D, bytesAt_add, List.append_assoc]
    rw [e]
    have := reprR_append P (hI.repr h0 d hd) (x := bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k)
      (mem' := s'.mem) (by rw [bytesAt_length]; exact hrk) ?_ ?_
    · rwa [bytesAt_length] at this
    · rw [hmem]
      exact stateAt_congr fun i hi => writeBytes_before _ _ _ (by omega) (by rw [bytesAt_length]; omega)
    · rw [hmem, ← Offset.add_add, bytesAt_writeBytes _ _ _ _ (by rw [bytesAt_length]; omega)]

/-- `fill`: copying `min(B - r, len - c)` bytes of data into the buffer. -/
theorem fill_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : Inv P s₀ c r s) :
    WP isa (fill (w := w)) s (Inv P s₀ (c + min (blockBytes w - r) (len s₀ - c))
      (r + min (blockBytes w - r) (len s₀ - c))) := by
  have hL := len_lt s₀
  have hc := hI.c_le
  have hpos := hP.pos
  have hl := hP.len
  have hbb : blockBytes w ≤ 128 := by rcases hP.bb with h | h <;> omega
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  have hlbb : 1 ≤ lbb w ∧ lbb w ≤ 31 := ⟨hP.lbb.1, hP.lbb.2.1⟩
  unfold fill
  refine WP.seq (wp_mov (op2_imm hP.encB) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_lsr hlbb) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  have hI₄ : Inv P s₀ c r s₄ := (((hI.of_upd u₁).of_upd u₂).of_upd u₃).of_flags f₄
  have h11 : s₄.gpr .r11 = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r8, B_eq,
      sub_ofNat hr]
  have hz : isa.eval .eq s₄ = some (decide ((len s₀ - c) / blockBytes w = 0)) := by
    show VG.Arm.eval .eq s₄ = _
    rw [eval_eq, z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r7,
      shr_ofNat hP (by omega), cmp0 (by have := Nat.div_le_self (len s₀ - c) (blockBytes w); omega)]
  refine WP.seq (WP.mono (Q := fun (t : State) => Inv P s₀ c r t ∧ t.gpr .r11 = BitVec.ofNat 32 a) ?_
    fun (t : State) (ht : Inv P s₀ c r t ∧ t.gpr .r11 = BitVec.ofNat 32 a) =>
      copy_ok hP hp (by omega) (by omega) ht.1 ht.2)
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    have hlt : len s₀ - c < blockBytes w := by
      refine Nat.lt_of_not_le fun h' => ?_
      have := Nat.div_pos h' hpos
      omega
    refine WP.seq (wp_add (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_lsr hlbb) fun s₆ u₆ =>
      wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_)
    have hI₇ : Inv P s₀ c r s₇ := ((hI₄.of_upd u₅).of_upd u₆).of_flags f₇
    have hz₇ : isa.eval .eq s₇ = some (decide ((len s₀ - c + r) / blockBytes w = 0)) := by
      show VG.Arm.eval .eq s₇ = _
      rw [eval_eq, z₇, u₆.gpr, u₅.gpr, hI₄.r7, hI₄.r8, ← BitVec.ofNat_add, shr_ofNat hP (by omega),
        cmp0 (by have := Nat.div_le_self (len s₀ - c + r) (blockBytes w); omega)]
    refine WP.ite _ hz₇ (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      have hlt' : len s₀ - c + r < blockBytes w := by
        refine Nat.lt_of_not_le fun h' => ?_
        have := Nat.div_pos h' hpos
        omega
      refine wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ⟨hI₇.of_upd u₈, ?_⟩
      rw [u₈.gpr, hI₇.r7, ha]
      congr 1; omega
    · simp only [decide_eq_false_iff_not] at hb'
      have hge : blockBytes w ≤ len s₀ - c + r := by
        refine Nat.le_of_not_lt fun h' => hb' (Nat.div_eq_of_lt h')
      refine WP.block_nil ⟨hI₇, ?_⟩
      rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), h11, ha]
      congr 1; omega
  · simp only [decide_eq_false_iff_not] at hb
    have hge : blockBytes w ≤ len s₀ - c := by
      refine Nat.le_of_not_lt fun h' => hb (Nat.div_eq_of_lt h')
    refine WP.block_nil ⟨hI₄, ?_⟩
    rw [h11, ha]
    congr 1; omega

/-! ## Up to the first call -/

section
variable (w : Nat) (s₀ : State)

/-- The bytes in the buffer on entry. -/
abbrev r₀ : Nat := bufLen w (cnt s₀)
/-- The bytes of data copied into a non-empty buffer. -/
def a₁ : Nat := if r₀ w s₀ = 0 then 0 else min (blockBytes w - r₀ w s₀) (len s₀)
/-- The blocks the first call compresses: the buffer, if it is not empty and
more data follows (it is then full). -/
def n₁ : Nat := if len s₀ - a₁ w s₀ ≠ 0 ∧ r₀ w s₀ + a₁ w s₀ ≠ 0 then 1 else 0

end

theorem a₁_le (s₀ : State) : a₁ w s₀ ≤ len s₀ := by
  unfold a₁; split <;> omega

theorem a₁_eq (s₀ : State) (h : r₀ w s₀ ≠ 0) : a₁ w s₀ = min (blockBytes w - r₀ w s₀) (len s₀) := by
  simp only [a₁, h, ite_false]

theorem a₁_zero (s₀ : State) (h : r₀ w s₀ = 0) : a₁ w s₀ = 0 := by
  simp only [a₁, h, ite_true]

theorem r₁_le (hP : Ok P) (s₀ : State) : r₀ w s₀ + a₁ w s₀ ≤ blockBytes w := by
  have hr : r₀ w s₀ ≤ blockBytes w := bufLen_le hP.pos _
  by_cases h0 : r₀ w s₀ = 0
  · rw [a₁_zero s₀ h0]; omega
  · rw [a₁_eq s₀ h0]; omega

/-- The first call compresses the buffer only when it is full. -/
theorem n₁_full (hP : Ok P) (s₀ : State) (h : n₁ w s₀ = 1) : r₀ w s₀ + a₁ w s₀ = blockBytes w := by
  have hr : r₀ w s₀ ≤ blockBytes w := bufLen_le hP.pos _
  simp only [n₁] at h
  split at h
  · rename_i hc
    by_cases h0 : r₀ w s₀ = 0
    · rw [a₁_zero s₀ h0] at hc; omega
    · rw [a₁_eq s₀ h0] at hc ⊢; omega
  · cases h

theorem n₁_le (s₀ : State) : n₁ w s₀ ≤ 1 := by unfold n₁; split <;> omega

theorem head_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hI : Inv P s₀ 0 (r₀ w s₀) s)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t, Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) t → WP isa rest t Q) :
    WP isa (.seq (.block [.cmp .r8 (.imm 0)]) (.seq (.ite .eq (.block []) (fill (w := w))) rest)) s Q := by
  have hr : r₀ w s₀ ≤ blockBytes w := bufLen_le hP.pos _
  have hB : blockBytes w ≤ 128 := by rcases hP.bb with h | h <;> omega
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_flags f₁
  have hz : isa.eval .eq s₁ = some (decide (r₀ w s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [eval_eq, z₁, hI.r8, cmp0 (by omega)]
  refine WP.seq (WP.mono (WP.ite _ hz (fun hb => ?_) (fun hb => ?_)) k)
  · simp only [decide_eq_true_eq] at hb
    rw [a₁_zero s₀ hb, Nat.add_zero]
    exact WP.block_nil hI₁
  · simp only [decide_eq_false_iff_not] at hb
    have h := fill_ok hP hp hr hI₁
    simp only [Nat.zero_add, Nat.sub_zero] at h
    rw [a₁_eq s₀ hb]
    exact h

/-! ## The arguments of a call -/

theorem common_sp {s₀ : State} {c : Nat} {s : State} (h : Common w s₀ c s) : below s = below s₀ := by
  rw [below, below, h.sp]

theorem cov_of {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {R : Region}
    (hR : (∃ off, R.base = stA s₀ + BitVec.ofNat 64 off ∧ off + R.len ≤ bufOff w + blockBytes w) ∨
      (∃ off, R.base = dA s₀ + BitVec.ofNat 64 off ∧ off + R.len ≤ len s₀)) :
    Covers [R] (s.rd ++ s.wr) := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  apply Covers.of_sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rcases hR with ⟨off, h1, h2⟩ | ⟨off, h1, h2⟩
  · exact ⟨stR s₀ w, by simp, off, h1, h2⟩
  · exact ⟨dR s₀, by simp, off, h1, h2⟩

/-- The arguments of a call, from the registers. -/
theorem callArgs_of (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s)
    {blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
    (hblk : (blk = st s₀ + BitVec.ofNat 32 (bufOff w) ∧ n ≤ 1) ∨
      (∃ c₀, blk = dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ < len s₀ ∧ c₀ + blockBytes w * n ≤ len s₀) ∨
      (blk = st s₀ ∧ n = 0))
    (h0 : s.gpr .r0 = st s₀) (h1 : s.gpr .r1 = blk) (h2 : s.gpr .r2 = BitVec.ofNat 32 n)
    (ht : s.gpr .r11 ++ s.gpr .r3 = t) (h12 : s.gpr .r12 = last) (hlr : s.gpr .lr = scr s₀) :
    CallArgs (w := w) s (st s₀) (scr s₀) blk n t last := by
  have hl := hP.len
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hdf := hp.d_fit
  have hL := len_lt s₀
  have eN : Region.Sub ⟨stA s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have eS : Region.Sub ⟨scA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  -- Where the blocks are.
  have hB : (State.addr blk = stA s₀ + BitVec.ofNat 64 (bufOff w) ∧ blockBytes w * n ≤ blockBytes w) ∨
      (∃ c₀, State.addr blk = dA s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + blockBytes w * n ≤ len s₀) ∨
      (State.addr blk = stA s₀ ∧ n = 0) := by
    rcases hblk with ⟨rfl, hn⟩ | ⟨c₀, rfl, hc₀, hc₁⟩ | ⟨rfl, hn⟩
    · refine .inl ⟨addr_add (by omega), ?_⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> omega
    · exact .inr (.inl ⟨c₀, addr_add (by omega), hc₁⟩)
    · exact .inr (.inr ⟨rfl, hn⟩)
  have hBn : blockBytes w * n ≤ 2 ^ 32 := by
    rcases hB with ⟨-, h⟩ | ⟨c₀, -, h⟩ | ⟨-, rfl⟩ <;> omega
  have hsub : Region.Sub ⟨State.addr blk, blockBytes w * n⟩ (stR s₀ w) ∨
      Region.Sub ⟨State.addr blk, blockBytes w * n⟩ (dR s₀) := by
    rcases hB with ⟨e, h⟩ | ⟨c₀, e, h⟩ | ⟨e, rfl⟩
    · exact .inl (e ▸ Offset.sub_base _ (by omega))
    · exact .inr (e ▸ Offset.sub_base _ (by omega))
    · exact .inl (by rw [e, Nat.mul_zero]; exact Region.sub_prefix (by omega))
  have hblkN : blk.toNat + blockBytes w * n ≤ 2 ^ 32 := by
    rcases hblk with ⟨rfl, hn⟩ | ⟨c₀, rfl, hc₀, hc₁⟩ | ⟨rfl, rfl⟩
    · rw [toNat_add_ofNat (by omega)]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> omega
    · rw [toNat_add_ofNat (by omega)]; omega
    · omega
  have hn : n < 2 ^ 32 := by
    have := hP.pos
    rcases Nat.lt_or_ge n (2 ^ 32) with h | h
    · exact h
    · exfalso; have := Nat.mul_le_mul_left (blockBytes w) h; omega
  refine ⟨h0, h1, h2, ht, h12, hlr, hn, by rw [h.sp]; exact hp.sp16, ?_, ?_, (hp.st_scr.sub_left eN).sub_right eS, ?_, ?_, ?_, ?_, ?_,
    by omega, hblkN, by omega⟩
  · refine cov_of hp h ?_
    rcases hB with ⟨e, h'⟩ | ⟨c₀, e, h'⟩ | ⟨e, rfl⟩
    · exact .inl ⟨bufOff w, e, by dsimp only; omega⟩
    · exact .inr ⟨c₀, e, h'⟩
    · exact .inl ⟨0, by rw [e]; simp, by dsimp only; omega⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rcases hB with ⟨e, h'⟩ | ⟨c₀, e, h'⟩ | ⟨e, rfl⟩
    · rw [e]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (e ▸ Offset.sub_base _ (by omega))).sub_right eN
    · intro a h₁ _; simp [Region.Contains] at h₁
  · rcases hsub with e | e
    · exact (hp.st_scr.sub_left e).sub_right eS
    · exact (hp.d_scr.sub_left e).sub_right eS
  · rw [common_sp h]; exact hp.w_st.sub_right eN
  · rw [common_sp h]
    rcases hsub with e | e
    · exact hp.w_st.sub_right e
    · exact hp.w_d.sub_right e
  · rw [common_sp h]; exact hp.w_scr.sub_right eS

/-- What a call leaves of `Common`. -/
theorem Common.after_call {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (ha : After s [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩] s') (hl : bufOff w ≤ bufOff w + blockBytes w) :
    Common w s₀ c s' := by
  have hf : Frame [stR s₀ w, ⟨scA s₀, 512⟩, below s₀] s.mem s'.mem := by
    have := ha.frame
    rw [common_sp h] at this
    exact this.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀ w, by simp, Region.sub_prefix hl⟩
      · exact ⟨⟨scA s₀, 512⟩, by simp, fun _ h => h⟩
      · exact ⟨below s₀, by simp, fun _ h => h⟩
  have hcp : ∀ r ∈ commonRegs, r ∈ preserved ∧ r ≠ .lr := by decide
  have hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r := fun r hr => ha.cs r (hcp r hr).1 (hcp r hr).2
  refine ⟨h.c_le, ha.rd.trans h.rd, ha.wr.trans h.wr, ha.sp.trans h.sp, by rw [hg _ (by simp)]; exact h.r4,
    by rw [hg _ (by simp)]; exact h.r5, by rw [hg _ (by simp)]; exact h.r6, by rw [hg _ (by simp)]; exact h.r7,
    by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact h.cn,
    h.frame.trans (hf.sub fun r hr => ?_), saved_frame hp h.saved hf⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
  · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
  · exact ⟨below s₀, by simp, fun _ h => h⟩

theorem r8_after {s s' : State} {ws : List Region} (ha : After s ws s') : s'.gpr .r8 = s.gpr .r8 :=
  ha.cs .r8 (by simp [preserved]) (by decide)

/-! ## The prologue, up to the first call -/

/-- What holds before the first call. -/
def PostPro (P : Params w) (s₀ : State) (s : State) : Prop :=
  Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) s ∧
    CallArgs (w := w) s (st s₀) (scr s₀) (st s₀ + BitVec.ofNat 32 (bufOff w)) (n₁ w s₀)
      (BitVec.ofNat 64 (cnt s₀ + a₁ w s₀)) 0

theorem args₁_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State}
    (hI : Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) s) :
    WP isa (.seq (.block [.mov .r2 (.imm 0), .cmp .r7 (.imm 0)])
      (.seq (.ite .eq (.block []) (.seq (.block [.cmp .r8 (.imm 0)])
        (.ite .eq (.block []) (.block [.mov .r2 (.imm 1)]))))
      (.block (args ++ ([.dp .add .r1 .r4 (.imm (BitVec.ofNat 32 (N w))), .mov .r3 (.reg .r9),
        .mov .r11 (.reg .r10)] : List Instr))))) s (PostPro P s₀) := by
  have hL := len_lt s₀
  have hr := r₁_le hP s₀
  have hl := hP.len
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  have hI₂ := (hI.of_upd u₁).of_flags f₂
  have hz : isa.eval .eq s₂ = some (decide (len s₀ - a₁ w s₀ = 0)) := by
    show VG.Arm.eval .eq s₂ = _
    rw [eval_eq, z₂, u₁.other _ (by decide), hI.r7, cmp0 (by omega)]
  -- `r2` := `n₁`.
  refine WP.seq (WP.mono (Q := fun (t : State) => Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) t ∧
      t.gpr .r2 = BitVec.ofNat 32 (n₁ w s₀)) ?_ fun t ⟨hIt, h2t⟩ => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.block_nil ⟨hI₂, ?_⟩
      rw [f₂.gpr, u₁.gpr]; simp [n₁, hb]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_)
      have hI₃ := hI₂.of_flags f₃
      have hz₃ : isa.eval .eq s₃ = some (decide (r₀ w s₀ + a₁ w s₀ = 0)) := by
        show VG.Arm.eval .eq s₃ = _
        rw [eval_eq, z₃, hI₂.r8, cmp0 (by omega)]
      refine WP.ite _ hz₃ (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        refine WP.block_nil ⟨hI₃, ?_⟩
        rw [f₃.gpr, f₂.gpr, u₁.gpr]; simp [n₁, hb']
      · simp only [decide_eq_false_iff_not] at hb'
        refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ⟨hI₃.of_upd u₄, ?_⟩
        rw [u₄.gpr]; simp only [n₁, ne_eq, hb, hb', not_false_eq_true, and_self, ite_true]; rfl
  · simp only [args, List.cons_append, List.nil_append]
    refine wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ =>
      wp_mov (op2_reg _ _) fun s₇ u₇ => wp_add (op2_imm hP.encN) fun s₈ u₈ =>
      wp_mov (op2_reg _ _) fun s₉ u₉ => wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => WP.block_nil ?_
    have hI' : Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) s₁₀ :=
      (((((hIt.of_upd u₅).of_upd u₆).of_upd u₇).of_upd u₈).of_upd u₉).of_upd u₁₀
    refine ⟨hI', callArgs_of hP hp hI'.toCommon (.inl ⟨rfl, n₁_le s₀⟩) ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
      simp only [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other,
        u₅.gpr, u₅.other, ne_eq, reduceCtorEq, not_false_eq_true, hIt.r4, hIt.r5, h2t, N_eq]
    exact hIt.cn

theorem pro_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) :
    WP isa (updatePro (w := w)) s₀ (PostPro P s₀) := by
  unfold updatePro
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hst⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_inv hP hC hst) fun s₂ hI₂ => ?_)
  exact head_ok hP hp hI₂ fun s₃ hI₃ => args₁_ok hP hp hI₃

/-! ## The first call -/

/-- What holds after the first call. -/
def Mid (P : Params w) (s₀ s : State) : Prop :=
  Common w s₀ (a₁ w s₀) s ∧ s.gpr .r8 = BitVec.ofNat 32 (r₀ w s₀ + a₁ w s₀) ∧
    ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (stA s₀) (d ++ D s₀ (a₁ w s₀))
      (if n₁ w s₀ = 1 then 0 else r₀ w s₀ + a₁ w s₀)

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

/-- The buffer's bytes are not among those a call may write. -/
theorem buf_after {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (ha : After s [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩] s') {i : Nat} (hi : i < blockBytes w) :
    s'.mem (stA s₀ + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) =
      s.mem (stA s₀ + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) := by
  have hst := hp.st_fit
  have eB : Region.Sub ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (stR s₀ w) :=
    Offset.sub_base _ (by omega)
  refine ha.frame.bytes (R := ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩) (fun r hr => ?_)
    (by show blockBytes w ≤ 2 ^ 64; omega) hi
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · exact (hp.st_scr.sub_left eB).sub_right (Region.sub_prefix (by omega))
  · rw [common_sp h]; exact (hp.w_st.sub_right eB).symm

theorem call₁_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} (h : PostPro P s₀ s) : WP isa (call name code) s (Mid P s₀) := by
  have hl := hP.len
  have hI := h.1
  refine call_ok hf h.2 fun s' ha hst => ⟨hI.toCommon.after_call hp ha (by omega),
    by rw [r8_after ha]; exact hI.r8, fun h0 d hd => ?_⟩
  have hr := hI.repr h0 d hd
  split
  · rename_i hn
    rw [n₁_full hP s₀ hn] at hr
    refine reprR_flush P hP.pos hr ?_
    have hlen := hd.2.2
    have ha₁ := a₁_le (w := w) s₀
    rw [hst, hn, compressBlocks_one, R₀.length hd _, addr_add (by have := hp.st_fit; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hd.cnt_eq] at hlen; omega)]
    rfl
  · rename_i hn
    have hn0 : n₁ w s₀ = 0 := by have := n₁_le (w := w) s₀; omega
    rw [hn0, compressBlocks_zero] at hst
    exact reprR_congr hst (fun i hi => buf_after hp hI.toCommon ha (by have := r₁_le hP s₀; omega)) hr

/-! ## Between the calls -/

section
variable (w : Nat) (s₀ : State)

/-- The bytes in the buffer before the second call. -/
def r₂ : Nat := if (len s₀ - a₁ w s₀) = 0 then r₀ w s₀ + a₁ w s₀ else 0
/-- The blocks the second call compresses. -/
def k₂ : Nat := if (len s₀ - a₁ w s₀) = 0 then 0 else ((len s₀ - a₁ w s₀) - 1) / blockBytes w
/-- Where they are. -/
def blk₂ : BitVec 32 := if (len s₀ - a₁ w s₀) = 0 then st s₀ else dp s₀ + BitVec.ofNat 32 (a₁ w s₀)

end

/-- What holds before the second call. -/
def PostMid (P : Params w) (s₀ s : State) : Prop :=
  Inv P s₀ (a₁ w s₀) (r₂ w s₀) s ∧
    CallArgs (w := w) s (st s₀) (scr s₀) (blk₂ w s₀) (k₂ w s₀)
      (BitVec.ofNat 64 (cnt s₀ + a₁ w s₀ + blockBytes w)) 0

theorem k₂_le (s₀ : State) : a₁ w s₀ + blockBytes w * k₂ w s₀ ≤ len s₀ := by
  have := a₁_le (w := w) s₀
  unfold k₂; split
  · rw [Nat.mul_zero, Nat.add_zero]; exact this
  · have := Nat.mul_div_le ((len s₀ - a₁ w s₀) - 1) (blockBytes w); omega

theorem mid_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (h : Mid P s₀ s) :
    WP isa (updateMid (w := w)) s (PostMid P s₀) := by
  obtain ⟨hC, h8, hrep⟩ := h
  have hL := len_lt s₀
  have ha₁ := a₁_le (w := w) s₀
  have hlbb : 1 ≤ lbb w ∧ lbb w ≤ 31 := ⟨hP.lbb.1, hP.lbb.2.1⟩
  unfold updateMid
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hz : isa.eval .eq s₁ = some (decide ((len s₀ - a₁ w s₀) = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [eval_eq, z₁, hC.r7, cmp0 (by omega)]
  have hC₁ := hC.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr f₁.sp
  refine WP.seq (WP.mono (Q := fun (t : State) => Inv P s₀ (a₁ w s₀) (r₂ w s₀) t ∧
      t.gpr .r2 = BitVec.ofNat 32 (k₂ w s₀) ∧ t.gpr .r1 = blk₂ w s₀) ?_ fun t ⟨hIt, h2, h1⟩ => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      have hn : n₁ w s₀ = 0 := by simp [n₁, hb]
      refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ?_
      have hg : ∀ r ∈ .r8 :: commonRegs, s₃.gpr r = s₁.gpr r := fun r hr => by
        rw [u₃.other r (fun e => by subst e; simp at hr), u₂.other r (fun e => by subst e; simp at hr)]
      refine ⟨{ hC₁.of_gpr (fun r hr => hg r (List.mem_cons_of_mem _ hr)) (by rw [u₃.mem, u₂.mem])
          (by rw [u₃.rd, u₂.rd]) (by rw [u₃.wr, u₂.wr]) (by rw [u₃.sp, u₂.sp]) with
        r8 := by rw [hg _ (by simp), f₁.gpr, h8]; simp [r₂, hb]
        repr := fun h0 d hd => by
          rw [u₃.mem, u₂.mem, f₁.mem]
          have := hrep h0 d hd
          simp only [hn] at this
          simpa [r₂, hb] using this }, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.gpr]; simp [k₂, hb]
      · rw [u₃.gpr, u₂.other _ (by decide), f₁.gpr, hC.r4]; simp [blk₂, hb]
    · simp only [decide_eq_false_iff_not] at hb
      refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_sub (op2_imm (by decide)) fun s₃ u₃ =>
        wp_mov (op2_lsr hlbb) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
      have hg : ∀ r ∈ commonRegs, s₅.gpr r = s₁.gpr r := fun r hr => by
        rw [u₅.other r (notC hr .r1), u₄.other r (notC hr .r2), u₃.other r (notC hr .r2),
          u₂.other r (notC hr .r8)]
      have hr0 : (if n₁ w s₀ = 1 then 0 else r₀ w s₀ + a₁ w s₀) = 0 := by
        simp only [n₁]; split
        · rfl
        · rename_i hc
          simp only [ne_eq, not_and, Decidable.not_not] at hc
          exact hc hb
      refine ⟨{ hC₁.of_gpr hg (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]) (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd])
          (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]) (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp]) with
        r8 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
                 simp [r₂, hb]
        repr := fun h0 d hd => by
          rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, f₁.mem]
          have := hrep h0 d hd
          rw [hr0] at this
          simpa [r₂, hb] using this }, ?_, ?_⟩
      · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), f₁.gpr, hC.r7,
          show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), shr_ofNat hP (by omega)]
        simp [k₂, hb]
      · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), f₁.gpr, hC.r6]
        simp [blk₂, hb]
  · simp only [args, List.cons_append, List.nil_append]
    refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ =>
      wp_mov (op2_reg _ _) fun s₈ u₈ => wp_adds (op2_imm hP.encB) fun s₉ u₉ c₉ =>
      wp_adc (op2_imm (by decide)) fun s₁₀ u₁₀ _ => WP.block_nil ?_
    have hI' : Inv P s₀ (a₁ w s₀) (r₂ w s₀) s₁₀ :=
      ((((hIt.of_upd u₆).of_upd u₇).of_upd u₈).of_upd u₉).of_upd u₁₀
    have hB : blockBytes w < 2 ^ 32 := by rcases hP.bb with h | h <;> omega
    refine ⟨hI', callArgs_of hP hp hI'.toCommon ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · by_cases hb : (len s₀ - a₁ w s₀) = 0
      · exact .inr (.inr ⟨by simp [blk₂, hb], by simp [k₂, hb]⟩)
      · refine .inr (.inl ⟨a₁ w s₀, by simp [blk₂, hb], by omega, k₂_le (w := w) s₀⟩)
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.gpr, ne_eq, reduceCtorEq, not_false_eq_true,
        hIt.r4]
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, ne_eq, reduceCtorEq, not_false_eq_true, h1]
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, ne_eq, reduceCtorEq, not_false_eq_true, h2]
    · simp only [u₁₀.gpr, u₁₀.other .r3 (by decide), u₉.gpr, u₉.other .r10 (by decide), c₉,
        u₈.other .r9 (by decide), u₈.other .r10 (by decide), u₇.other .r9 (by decide), u₇.other .r10 (by decide),
        u₆.other .r9 (by decide), u₆.other .r10 (by decide), B_eq]
      exact add64_ofNat hIt.cn hB
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.gpr, ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [u₁₀.other, u₉.other, u₈.gpr, u₇.other, u₆.other, ne_eq, reduceCtorEq, not_false_eq_true,
        hIt.r5]

/-! ## The second call -/

/-- What holds after the second call. -/
def End (P : Params w) (s₀ s : State) : Prop :=
  Common w s₀ (a₁ w s₀) s ∧ s.gpr .r8 = BitVec.ofNat 32 (r₂ w s₀) ∧
    ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (stA s₀) (d ++ D s₀ (a₁ w s₀ + blockBytes w * k₂ w s₀)) (r₂ w s₀)

theorem call₂_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} (h : PostMid P s₀ s) : WP isa (call name code) s (End P s₀) := by
  have hl := hP.len
  have hI := h.1
  have hL := len_lt s₀
  have ha₁ := a₁_le (w := w) s₀
  refine call_ok hf h.2 fun s' ha hst => ⟨hI.toCommon.after_call hp ha (by omega),
    by rw [r8_after ha]; exact hI.r8, fun h0 d hd => ?_⟩
  have hr := hI.repr h0 d hd
  by_cases hk : k₂ w s₀ = 0
  · rw [hk, compressBlocks_zero] at hst
    rw [hk, Nat.mul_zero, Nat.add_zero]
    exact reprR_congr hst (fun i hi => buf_after hp hI.toCommon ha (by
      have := bufLen_le (w := w) hP.pos (cnt s₀); have := r₁_le hP s₀
      unfold r₂ at hi; split at hi <;> omega)) hr
  · have hb : (len s₀ - a₁ w s₀) ≠ 0 := fun hb => hk (by simp [k₂, hb])
    have e2 : r₂ w s₀ = 0 := by simp [r₂, hb]
    rw [e2] at hr ⊢
    have hkl := k₂_le (w := w) s₀
    have hpos := hP.pos
    have hkB : blockBytes w ≤ blockBytes w * k₂ w s₀ := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)
    have hlt : a₁ w s₀ + blockBytes w * k₂ w s₀ < len s₀ := by
      have := Nat.div_mul_le_self ((len s₀ - a₁ w s₀) - 1) (blockBytes w)
      simp only [k₂, hb, ite_false] at hkB ⊢; rw [Nat.mul_comm]; omega
    have hlen := hd.2.2
    have ecn : (BitVec.ofNat 64 (cnt s₀ + a₁ w s₀ + blockBytes w)).toNat =
        (d ++ D s₀ (a₁ w s₀)).length + blockBytes w := by
      rw [R₀.length hd _, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hd.cnt_eq] at hlen; omega)]
    have eblk : State.addr (blk₂ w s₀) = dA s₀ + BitVec.ofNat 64 (a₁ w s₀) := by
      simp only [blk₂, hb, ite_false]; exact addr_add (by have := hp.d_fit; omega)
    rw [ecn, eblk] at hst
    have := reprR_blocks P hP.pos hr (mem' := s'.mem) (q := dA s₀ + BitVec.ofNat 64 (a₁ w s₀))
      (k := k₂ w s₀) (by rw [hst]; rfl)
    have e : bytesAt s.mem (dA s₀ + BitVec.ofNat 64 (a₁ w s₀)) (blockBytes w * k₂ w s₀) =
        bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 (a₁ w s₀)) (blockBytes w * k₂ w s₀) :=
      bytesAt_congr fun i hi => by rw [Offset.add_add]; exact hI.data hp (by omega)
    rw [e, List.append_assoc, ← bytesAt_add] at this
    exact this

/-! ## The end -/

theorem rem_eq (x : Nat) :
    x - ((x - 1) % blockBytes w + 1) = blockBytes w * ((x - 1) / blockBytes w) := by
  have := Nat.div_add_mod (x - 1) (blockBytes w); omega

/-- The final state of `Inv` is the streaming state of the data. -/
theorem final_repr (hP : Ok P) {s₀ : State} {h0 : HashValue w} {d : List Byte} (hd : R₀ P s₀ h0 d)
    {m : Mem} {rf : Nat} (hrf : rf = 0 → cnt s₀ + len s₀ = 0)
    (h : ReprR P h0 m (stA s₀) (d ++ D s₀ (len s₀)) rf) :
    Spec.Blake2.Repr P h0 m (stA s₀) (d ++ D s₀ (len s₀)) := by
  rcases Nat.eq_zero_or_pos rf with h0' | h0'
  · subst h0'
    have := hrf rfl
    have hl : (d ++ D s₀ (len s₀)).length = 0 := by rw [R₀.length hd _]; omega
    rw [repr_iff P hP.pos, hl]
    exact h
  · exact repr_of_reprR P hP.pos h h0'

theorem end_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (h : End P s₀ s) :
    WP isa (updateEnd (w := w)) s fun s' => abiPreserved s₀ s' ∧ (updateArm P).post s₀ s' := by
  obtain ⟨hC, h8, hrep⟩ := h
  have hL := len_lt s₀
  have ha₁ := a₁_le (w := w) s₀
  have hpos := hP.pos
  have hl := hP.len
  have hB : blockBytes w ≤ 128 := by rcases hP.bb with h | h <;> omega
  unfold updateEnd
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hz : isa.eval .eq s₁ = some (decide ((len s₀ - a₁ w s₀) = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [eval_eq, z₁, hC.r7, cmp0 (by omega)]
  have hC₁ := hC.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr f₁.sp
  -- Every byte of data is consumed.
  refine WP.seq (WP.mono (Q := fun (t : State) => ∃ rf, (rf = 0 → cnt s₀ + len s₀ = 0) ∧ Inv P s₀ (len s₀) rf t)
    ?_ fun t ⟨rf, hrf, hIt⟩ => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      have hk : k₂ w s₀ = 0 := by simp [k₂, hb]
      have e2 : r₂ w s₀ = r₀ w s₀ + a₁ w s₀ := by simp [r₂, hb]
      have ea : a₁ w s₀ = len s₀ := by omega
      refine WP.block_nil ⟨r₂ w s₀, fun h0 => ?_, ?_⟩
      · rw [e2] at h0
        have hr0 : r₀ w s₀ = 0 := by omega
        have : cnt s₀ = 0 := by
          by_contra hc; have := bufLen_pos (w := w) hc; simp only [r₀] at hr0; omega
        omega
      · rw [← ea]
        exact
          { hC₁ with
            r8 := by rw [f₁.gpr]; exact h8
            repr := fun h0 d hd => by
              rw [f₁.mem]; have := hrep h0 d hd; rwa [hk, Nat.mul_zero, Nat.add_zero] at this }
    · simp only [decide_eq_false_iff_not] at hb
      have e2 : r₂ w s₀ = 0 := by simp [r₂, hb]
      have ek : blockBytes w * k₂ w s₀ = (len s₀ - a₁ w s₀) - (((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1) := by
        rw [rem_eq _]; simp [k₂, hb]
      have hrem : ((len s₀ - a₁ w s₀) - 1) % blockBytes w < blockBytes w := Nat.mod_lt _ hpos
      refine WP.seq (wp_sub (op2_imm (by decide)) fun s₂ u₂ => wp_and (op2_imm hP.encB1) fun s₃ u₃ =>
        wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_sub (op2_reg _ _) fun s₅ u₅ =>
        wp_add (op2_reg _ _) fun s₆ u₆ => wp_sub (op2_reg _ _) fun s₇ u₇ =>
        wp_adds (op2_reg _ _) fun s₈ u₈ c₈ => wp_adc (op2_imm (by decide)) fun s₉ u₉ _ => WP.block_nil ?_)
      have h4 : s₄.gpr .r11 = BitVec.ofNat 32 (((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1) := by
        rw [u₄.gpr, u₃.gpr, u₂.gpr, f₁.gpr, hC.r7, bufLen_lo hP hb]
        simp only [bufLen, hb, ite_false]
      have h11 : s₉.gpr .r11 = BitVec.ofNat 32 (((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1) := by
        rw [u₉.other .r11 (by decide), u₈.other .r11 (by decide), u₇.other .r11 (by decide),
          u₆.other .r11 (by decide), u₅.other .r11 (by decide), h4]
      have hrem' : a₁ w s₀ + blockBytes w * k₂ w s₀ + (((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1) =
          len s₀ := by
        have := Nat.mod_le ((len s₀ - a₁ w s₀) - 1) (blockBytes w)
        rw [ek]; omega
      have h12 : s₅.gpr .r12 = BitVec.ofNat 32 (blockBytes w * k₂ w s₀) := by
        rw [u₅.gpr, h4, u₄.other .r7 (by decide), u₃.other .r7 (by decide), u₂.other .r7 (by decide), f₁.gpr,
          hC.r7, sub_ofNat (by have := Nat.mod_le ((len s₀ - a₁ w s₀) - 1) (blockBytes w); omega), ek]
      have hk := k₂_le (w := w) s₀
      have hBk : blockBytes w * k₂ w s₀ < 2 ^ 32 := by omega
      have g₉ : ∀ x, x ≠ .r11 → x ≠ .r12 → x ≠ .r6 → x ≠ .r7 → x ≠ .r9 → x ≠ .r10 → s₉.gpr x = s.gpr x :=
        fun x h1 h2 h3 h4 h5 h6 => by
          rw [u₉.other x h6, u₈.other x h5, u₇.other x h4, u₆.other x h3, u₅.other x h2, u₄.other x h1,
            u₃.other x h1, u₂.other x h1, f₁.gpr]
      have h6 : s₉.gpr .r6 = dp s₀ + BitVec.ofNat 32 (a₁ w s₀ + blockBytes w * k₂ w s₀) := by
        rw [u₉.other .r6 (by decide), u₈.other .r6 (by decide), u₇.other .r6 (by decide), u₆.gpr, h12,
          u₅.other .r6 (by decide), u₄.other .r6 (by decide), u₃.other .r6 (by decide),
          u₂.other .r6 (by decide), f₁.gpr, hC.r6, BitVec.add_assoc, ← BitVec.ofNat_add]
      have h7 : s₉.gpr .r7 = BitVec.ofNat 32 (len s₀ - (a₁ w s₀ + blockBytes w * k₂ w s₀)) := by
        rw [u₉.other .r7 (by decide), u₈.other .r7 (by decide), u₇.gpr, u₆.other .r7 (by decide),
          u₆.other .r12 (by decide), h12, u₅.other .r7 (by decide), u₄.other .r7 (by decide),
          u₃.other .r7 (by decide), u₂.other .r7 (by decide), f₁.gpr, hC.r7, sub_ofNat (by omega), Nat.sub_sub]
      have hcn : s₉.gpr .r10 ++ s₉.gpr .r9 = BitVec.ofNat 64 (cnt s₀ + (a₁ w s₀ + blockBytes w * k₂ w s₀)) := by
        rw [u₉.gpr, u₉.other .r9 (by decide), u₈.gpr, u₈.other .r10 (by decide), c₈, u₇.other .r9 (by decide),
          u₇.other .r10 (by decide), u₇.other .r12 (by decide), u₆.other .r9 (by decide),
          u₆.other .r10 (by decide), u₆.other .r12 (by decide), h12, u₅.other .r9 (by decide),
          u₅.other .r10 (by decide), u₄.other .r9 (by decide), u₄.other .r10 (by decide),
          u₃.other .r9 (by decide), u₃.other .r10 (by decide), u₂.other .r9 (by decide),
          u₂.other .r10 (by decide), f₁.gpr, add64_ofNat hC.cn hBk, Nat.add_assoc]
      have hm₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, f₁.mem]
      have hI₉ : Inv P s₀ (a₁ w s₀ + blockBytes w * k₂ w s₀) 0 s₉ :=
        { c_le := hk
          rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, f₁.rd, hC.rd]
          wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, f₁.wr, hC.wr]
          sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, f₁.sp, hC.sp]
          r4 := by rw [g₉ .r4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hC.r4]
          r5 := by rw [g₉ .r5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hC.r5]
          r6 := h6
          r7 := h7
          cn := hcn
          frame := hm₉ ▸ hC.frame
          saved := hm₉ ▸ hC.saved
          r8 := by rw [g₉ .r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h8, e2]
          repr := fun h0 d hd => by
            rw [hm₉]
            have := hrep h0 d hd
            rwa [e2] at this }
      refine WP.mono (copy_ok hP hp (by omega) (by omega) hI₉ h11)
        fun t ht => ⟨((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1, fun h => by omega, ?_⟩
      rw [Nat.zero_add, hrem'] at ht
      exact ht
  · have := hp.scr_fit
    refine restore_ok hIt.r5 hp.scr_fit
      (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hIt.rd, hIt.wr, hp.wr], contains_off _ (by omega) (by omega)⟩) s₀.gpr
      hIt.saved fun s' hs hmem _ _ hsp => ⟨⟨preserved_of hs, by rw [hsp, hIt.sp]⟩, fun h0 d hr hc hlt => ?_⟩
    have hd : R₀ P s₀ h0 d := ⟨hr, hc, hlt⟩
    rw [hmem]
    exact final_repr hP hd hrf (hIt.repr h0 d hd)

/-! ## `update` -/

theorem correct (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) :
    WP isa (update (w := w) name code) s₀ fun s' => abiPreserved s₀ s' ∧ (updateArm P).post s₀ s' :=
  WP.seq (WP.mono (pro_ok hP hp) fun _ h₁ => WP.seq (WP.mono (call₁_ok hP hf hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (mid_ok hP hp h₂) fun _ h₃ => WP.seq (WP.mono (call₂_ok hP hf hp h₃) fun _ h₄ =>
      end_ok hP hp h₄))))

end VG.Proof.Blake2.Arm.Stream.Update
