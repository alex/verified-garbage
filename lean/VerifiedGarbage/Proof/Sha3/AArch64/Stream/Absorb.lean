import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha3.Contract

/-!
# The SHA-3 sponge on AArch64: `absorb`

The same structure as the x86-64 proof (`VG.Proof.Sha3.X86_64.Stream.Absorb`),
inside the frame that saves `x30` (`WP.frameReg`).
-/

namespace VG.Proof.Sha3.AArch64.Stream.Absorb

open VG VG.AArch64 VG.Impl.Sha3.AArch64.Stream
open VG.Proof.Sha3.AArch64
open VG.Proof.Sha3 (Rep rep_snoc xorByte stateAt_xorByte ofNat_beq_zero sub_beq_zero sub_ofNat
  xor_setWidth writeW8_apply bytesAt_succ bytesAt_length xorAt xorAt_single byteOf_xorAt rep_append
  byteOf_stateAt writeW64_byte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev rt : Nat := (s₀.gpr .x1).toNat
abbrev pos : Nat := (s₀.gpr .x2).toNat
abbrev dp : Addr := s₀.gpr .x3
abbrev len : Nat := (s₀.gpr .x4).toNat
abbrev scr : Addr := s₀.gpr .x5
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 640⟩
/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 16, 16⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (st s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀)
  d : (stkR s₀).Disjoint (dR s₀)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbAArch64.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11⟩, ⟨h6, h7, h8, h9⟩⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have h := Proof.Sha3.rate_bounds hp.rate
  omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  sp : s.sp = s₀.sp
  x21 : s.gpr .x21 = s₀.gpr .x1
  x23 : s.gpr .x23 = dp s₀ + BitVec.ofNat 64 c
  x24 : s.gpr .x24 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved (scr s₀) s₀.gpr s.mem
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  untouched : ∀ r ∈ VG.Proof.Sha3.AArch64.untouched, s.gpr r = s₀.gpr r

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  x22 : s.gpr .x22 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ D s₀ c)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hv : s'.v = s.v) :
    Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  sp := hsp.trans h.sp
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x23 := by rw [hg _ (by simp)]; exact h.x23
  x24 := by rw [hg _ (by simp)]; exact h.x24
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  vcs := fun r hr => by rw [hv]; exact h.vcs r hr
  untouched := fun r hr => (hg r (by cases r <;> simp_all [VG.Proof.Sha3.AArch64.untouched])).trans (h.untouched r hr)

/-- A call of the permutation keeps what holds throughout. -/
theorem Common.after_call {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hf : Frame [stR s₀, ⟨scr s₀, 512⟩] s.mem s'.mem) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := by rw [hcs _ (by decide) (by decide)]; exact h.x19
  x20 := by rw [hcs _ (by decide) (by decide)]; exact h.x20
  sp := hsp.trans h.sp
  x21 := by rw [hcs _ (by decide) (by decide)]; exact h.x21
  x23 := by rw [hcs _ (by decide) (by decide)]; exact h.x23
  x24 := by rw [hcs _ (by decide) (by decide)]; exact h.x24
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩)
  saved := h.saved.permute hp.st_scr hf
  vcs := fun r hr => (hv r hr).trans (h.vcs r hr)
  untouched := fun r hr => (hcs r (by cases r <;> simp_all [VG.Proof.Sha3.AArch64.untouched, preserved])
    (by cases r <;> simp_all [VG.Proof.Sha3.AArch64.untouched])).trans (h.untouched r hr)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block setup) s₀ (Inv s₀ 0) := by
  unfold setup
  rw [WP.block_append_iff]
  refine WP.mono (saves_ok fun k hk => ⟨scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, hv₁, v₁⟩ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_nil ?_
  have hm : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hf : Frame [stR s₀, scR s₀] s₀.mem s₁.mem := f₁.mono (by simp)
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm]; exact hf, by rw [hm]; exact v₁, fun r _ => by
      rw [u₇.vec, u₆.vec, u₅.vec, u₄.vec, u₃.vec, u₂.vec, hv₁], fun r hr => by
      cases r <;> simp_all [VG.Proof.Sha3.AArch64.untouched]
      all_goals rw [u₇.other _ (by decide),u₆.other _ (by decide),u₅.other _ (by decide),u₄.other _ (by decide),u₃.other _ (by decide),u₂.other _ (by decide),g₁]⟩,
    ?_, fun msg ⟨hs, _⟩ => ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁, Nat.sub_zero]
    simp [len]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁, Nat.add_zero,
      Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [hm, show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      f₁.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi

/-! ## One iteration -/

/-- The block of the body: the byte at position `j` XORed in. -/
theorem body_byte {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block [.ldrb .x9 .x23 0, .add .x .x10 .x19 .x22, .ldrb .x11 .x10 0,
      .logic .eor .x .x9 .x9 .x11, .strb .x9 .x10 0, .addImm .x .x23 .x23 1,
      .addImm .x .x22 .x22 1, .subImm .x .x24 .x24 1, .sub .x .x9 .x22 .x21]) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .x22 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 1) ∧
      eval (.zero .x .x9) s' = some (decide ((pos s₀ + c) % rt s₀ + 1 = rt s₀)) ∧
      stateAt s'.mem (st s₀) = xorByte (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  have hr22 : s.gpr .x22 = BitVec.ofNat 64 j := by rw [hI.x22, hjd]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega) (by omega)⟩
  refine wp_ldrb (t := .x9) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.x23]; simp)
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  have ea : s₂.gpr .x10 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.x19, hr22]; simp
  refine wp_ldrb (t := .x11) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₃ u₃ => ?_
  refine wp_eor fun s₄ u₄ => ?_
  refine wp_strb (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₅ g₅ => ?_
  refine wp_addImm (by decide) fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ =>
    wp_subImm (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ => wp_nil ?_
  -- The byte stored.
  have hv : (s₄.gpr .x9).setWidth 8 =
      s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem,
      xor_setWidth, hI.data hp hc]
  have hm₉ : s₉.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₉.mem := by
    rw [hm₉]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x23 → r ≠ .x22 → r ≠ .x24 →
      s₉.gpr r = s.gpr r := fun r h9 h10 h11 h23 h22 h24 => by
    rw [u₉.other r h9, u₈.other r h24, u₇.other r h22, u₆.other r h23, g₅.gpr, u₄.other r h9,
      u₃.other r h11, u₂.other r h10, u₁.other r h9]
  have h22 : s₉.gpr .x22 = BitVec.ofNat 64 (j + 1) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr22, ← BitVec.ofNat_add]
  have h21 : s₉.gpr .x21 = s₀.gpr .x1 := by
    rw [g .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x21]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, h21, ?_, ?_, ?_, ?_, fun r hr => by
      rw [u₉.vec, u₈.vec, u₇.vec, u₆.vec, g₅.vec, u₄.vec, u₃.vec, u₂.vec, u₁.vec]; exact hI.vcs r hr, fun r hr => by
      have hne : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x23 ∧ r ≠ .x22 ∧ r ≠ .x24 := by
        cases r <;> simp_all [VG.Proof.Sha3.AArch64.untouched]
      rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
      exact hI.untouched r hr⟩, h22, ?_, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x19]
  · rw [g .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x20]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x23, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x24, sub_ofNat (by omega), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame hf fun k hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact hp.st_scr.symm.sub_left (slot_sub (scr s₀) hk)
  · rw [eval_zero, u₉.gpr, ← u₉.other .x22 (by decide),
      ← u₉.other .x21 (by decide), h22, h21, sub_beq_zero (by omega)]
  · refine stateAt_xorByte (by omega) ?_ fun i hi hij => ?_
    · rw [hm₉, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₉, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega) hij))]

/-- The bytes `c … c + n - 1` of the data follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, bytesAt_add m p c n, bytesAt_succ, List.append_assoc,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A lane of a state in memory written: its 8 bytes XORed with `bs`. -/
theorem stateAt_write_lane {m : Mem} {p : Addr} {j : Nat} (hj : j + 8 ≤ 200) {v : BitVec 64}
    {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (p + BitVec.ofNat 64 (j + d)) ^^^ bs.getD d 0) :
    stateAt (m.writeW (p + BitVec.ofNat 64 j) v) p = xorAt (stateAt m p) j bs :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi, hbs]
    by_cases c : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left c, show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1],
        writeW64_byte _ _ _ (by omega), hv _ (by omega), Nat.add_sub_cancel' c.1,
        show p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) = p + BitVec.ofNat 64 i by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1]]
    · rw [ite_eq_right c, Mem.writeW, Mem.write_apply]
      rw [show p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 j) = BitVec.ofNat 64 i - BitVec.ofNat 64 j by
        bv_omega, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega

/-- The block of the body: the lane of data at `c` XORed into the lane at
position `j`. -/
theorem body_word {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ len s₀) {s : State}
    (hI : Inv s₀ c s) (hj8 : (pos s₀ + c) % rt s₀ % 8 = 0) :
    WP isa (.block absorbWord) s fun s' =>
      Common s₀ (c + 8) s' ∧ s'.gpr .x22 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 8) ∧
      eval (.zero .x .x9) s' = some (decide ((pos s₀ + c) % rt s₀ + 8 = rt s₀)) ∧
      stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 8) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj hj8 ⊢
  have hj' : j + 8 ≤ rt s₀ := by omega
  have hr22 : s.gpr .x22 = BitVec.ofNat 64 j := by rw [hI.x22, hjd]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 8 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega) (by omega)⟩
  refine wp_ldr (t := .x9) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.x23]; simp)
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  have ea : s₂.gpr .x10 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.x19, hr22]; simp
  refine wp_ldr (t := .x11) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₃ u₃ => ?_
  refine wp_eor fun s₄ u₄ => ?_
  refine wp_str (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₅ g₅ => ?_
  refine wp_addImm (by decide) fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ =>
    wp_subImm (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ => wp_nil ?_
  have hv : s₄.gpr .x9 = s.mem.readW (dp s₀ + BitVec.ofNat 64 c) 64 ^^^
      s.mem.readW (st s₀ + BitVec.ofNat 64 j) 64 := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem]
  have hm₉ : s₉.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j) (s₄.gpr .x9) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₉.mem := by
    rw [hm₉]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x23 → r ≠ .x22 → r ≠ .x24 →
      s₉.gpr r = s.gpr r := fun r h9 h10 h11 h23 h22 h24 => by
    rw [u₉.other r h9, u₈.other r h24, u₇.other r h22, u₆.other r h23, g₅.gpr, u₄.other r h9,
      u₃.other r h11, u₂.other r h10, u₁.other r h9]
  have h22 : s₉.gpr .x22 = BitVec.ofNat 64 (j + 8) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr22, ← BitVec.ofNat_add]
  have h21 : s₉.gpr .x21 = s₀.gpr .x1 := by
    rw [g .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x21]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, h21, ?_, ?_, ?_, ?_, fun r hr => by
      rw [u₉.vec, u₈.vec, u₇.vec, u₆.vec, g₅.vec, u₄.vec, u₃.vec, u₂.vec, u₁.vec]; exact hI.vcs r hr, fun r hr => by
      have hne : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x23 ∧ r ≠ .x22 ∧ r ≠ .x24 := by
        cases r <;> simp_all [VG.Proof.Sha3.AArch64.untouched]
      rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
      exact hI.untouched r hr⟩, h22, ?_, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x19]
  · rw [g .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x20]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x23, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x24, sub_ofNat (by omega), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame hf fun k hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact hp.st_scr.symm.sub_left (slot_sub (scr s₀) hk)
  · rw [eval_zero, u₉.gpr, ← u₉.other .x22 (by decide),
      ← u₉.other .x21 (by decide), h22, h21, sub_beq_zero (by omega)]
  · rw [hm₉]
    refine stateAt_write_lane (by omega) (bytesAt_length _ _ _) fun d hd => ?_
    rw [hv, BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega), Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega),
      BitVec.xor_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd,
      Option.map_some, Option.getD_some]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hI.data hp (by omega)]

/-- After a lane or a byte of data: what the permutation, if the block is
complete, turns into the invariant. -/
structure After (s₀ : State) (s : State) (c n : Nat) (s' : State) : Prop where
  common : Common s₀ (c + n) s'
  x22 : s'.gpr .x22 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n)
  z : eval (.zero .x .x9) s' = some (decide ((pos s₀ + c) % rt s₀ + n = rt s₀))
  st : stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
    (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)

/-- The permutation if the block is complete. -/
theorem after_ok (v : Permutation) {s₀ : State} (hp : Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (pos s₀ + c) % rt s₀ + n ≤ rt s₀) {s s₁ : State} (hI : Inv s₀ c s) (h : After s₀ s c n s₁) :
    WP isa (.ite (.zero .x .x9) (.seq (.block [.movz .x .x22 0 0]) (permuteAtWith v.callee)) (.block [])) s₁
      (Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hC := h.common
  have hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  have hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega) _ _
      (by rw [bytesAt_length]; exact hn) (by rw [bytesAt_length, hlen msg hm]; exact hfit),
      hlen msg hm, bytesAt_length, h.st, hI.repr msg hm]
  have hpc : (pos s₀ + (c + n)) % rt s₀ = if (pos s₀ + c) % rt s₀ + n = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + n := by
    have e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + n) = (pos s₀ + c) + n by omega]
    generalize (pos s₀ + c) % rt s₀ = j at e hfit ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + n = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) h.z (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_movz fun s₂ u₂ => wp_nil ?_)
    have hC₂ := hC.of_gpr (fun r hr => u₂.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₂.mem u₂.rd u₂.wr u₂.sp u₂.vec
    refine permuteAt_ok v hC₂.x19 hC₂.x20 (hp.st_scr.sub_right (Region.sub_prefix (by omega)))
      ?_ fun s₃ rd₃ wr₃ sp₃ cs₃ vc₃ f₃ e₃ => ?_
    · rw [hC₂.wr, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
    · refine { hC₂.after_call hp rd₃ wr₃ sp₃ cs₃ vc₃ f₃ with x22 := ?_, repr := fun msg hm => ?_ }
      · rw [cs₃ _ (by decide) (by decide), u₂.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]; rfl
      · rw [e₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_nil { hC with x22 := ?_, repr := fun msg hm => ?_ }
    · rw [h.x22, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

/-- The whole body: a lane or a byte of data. -/
theorem body_ok (v : Permutation) {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa (absorbBodyWith v.callee) s fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧ Inv s₀ c' s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  unfold absorbBodyWith
  refine WP.seq (wp_movz fun s₃ u₃ => wp_and fun s₄ u₄ => wp_subImm (by decide) fun s₅ u₅ =>
    wp_lsr (by decide) fun s₆ u₆ => wp_orr fun s₇ u₇ => wp_nil ?_)
  have oth : ∀ r, r ≠ .x10 → r ≠ .x11 → s₇.gpr r = s.gpr r := fun r h10 h11 => by
    rw [u₇.other r h10, u₆.other r h11, u₅.other r h11, u₄.other r h10, u₃.other r h10]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have hI₇ : Inv s₀ c s₇ :=
    { hI.toCommon.of_gpr (fun r hr => oth r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) m₇
        (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr])
        (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp])
        (by rw [u₇.vec, u₆.vec, u₅.vec, u₄.vec, u₃.vec]) with
      x22 := by rw [oth _ (by decide) (by decide)]; exact hI.x22
      repr := fun msg hm => by rw [m₇]; exact hI.repr msg hm }
  have hx10 : s₇.gpr .x10 = 0 → (pos s₀ + c) % rt s₀ % 8 = 0 ∧ 8 ≤ len s₀ - c := fun h0 => by
    rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₃.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hI.x22, hI.x24] at h0
    have h0' := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat, BitVec.toNat_setWidth] at h0'
    have hpos : (pos s₀ + c) % rt s₀ < 2 ^ 64 := by have := (s₀.gpr .x1).isLt; omega
    simp only [show BitVec.toNat (7 : BitVec 16) = 2 ^ 3 - 1 from rfl,
      show (2 ^ 3 - 1) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
      Nat.or_eq_zero_iff] at h0'
    have hl := len_lt s₀
    omega
  refine WP.seq (WP.mono (Q := fun s₁ => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
      c + n ≤ len s₀ ∧ After s₀ s₇ c n s₁) ?_
    fun s₁ ⟨n, hn, hfit, hcn, hA⟩ => WP.mono ((after_ok v) hp hn hfit hI₇ hA)
      fun s' h => ⟨c + n, by omega, hcn, h⟩)
  refine WP.ite (s₇.gpr .x10 == 0) (eval_zero _ _) (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, l8⟩ := hx10 (by simpa using hb)
    exact WP.mono (body_word hp (by omega) hI₇ m8) fun s₁ ⟨hC, h22, hz, hst⟩ =>
      ⟨8, by decide, by omega, by omega, hC, h22, hz, hst⟩
  · refine WP.mono (body_byte hp hc hI₇) fun s₁ ⟨hC, h22, hz, hst⟩ =>
      ⟨1, by decide, by omega, by omega, hC, h22, hz, ?_⟩
    rw [hst]
    simp [bytesAt, xorAt_single]

/-! ## The epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ k < 6, s'.gpr (sv k) = s₀.gpr (sv k)) ∧ s'.sp = s₀.sp ∧
    (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧
    Proof.Sha3.absorbAArch64.post s₀ s' ∧
    (∀ r ∈ VG.Proof.Sha3.AArch64.untouched, s'.gpr r = s₀.gpr r)

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block (Impl.Sha3.AArch64.mov .x0 .x22 :: restore)) s (Post s₀) := by
  have ⟨hr₀, _⟩ := hp.rt_pos
  refine wp_mov fun s₁ u₁ => ?_
  refine WP.mono (restores_ok (scr := scr s₀) (by rw [u₁.other _ (by decide), hI.x20])
    fun k hk => ⟨scR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s' ⟨ax, sp, m, _, _, hv, other, v⟩ => ⟨fun k hk => ?_, by rw [sp, u₁.sp, hI.sp],
      (fun r hr => by rw [hv, u₁.vec]; exact hI.vcs r hr), ⟨fun msg hm hpm => ?_, ?_⟩, fun r hr => by
        have hne : r ≠ .x0 ∧ ∀ k < 6, r ≠ sv k := by
          exact ⟨by cases r <;> simp_all [VG.Proof.Sha3.AArch64.untouched],untouched_ne_sv r hr⟩
        rw [other r hne.2,u₁.other r hne.1]
        exact hI.untouched r hr⟩
  · rw [v k hk, u₁.mem]; exact hI.saved k hk
  · rw [Proof.Sha3.repr_iff, m, u₁.mem]
    exact hI.repr msg ⟨hm, hpm⟩
  · rw [ax, u₁.gpr, hI.x22, toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega)]

/-! ## The whole function -/

theorem absorb_eq (v : Permutation) : (absorbMainWith v.callee) = .seq (.block setup)
    (.seq (.ite (.zero .x .x24) (.block []) (.loop (absorbBodyWith v.callee) (.nonzero .x .x24)))
      (.block (Impl.Sha3.AArch64.mov .x0 .x22 :: restore))) := rfl

/-- `absorb` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (v : Permutation) {s₀ : State} (hp : Pre s₀) :
    WP isa (absorbMainWith v.callee) s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧
      Proof.Sha3.absorbAArch64.post s₀ s' := by
  have hl := len_lt s₀
  refine WP.mono (Q := Post s₀) ?_ fun s' ⟨hsv, hsp, hv, hpost, hu⟩ =>
    ⟨fun r hr h30 => ?_, hsp, hv, hpost⟩
  · rw [(absorb_eq v)]
    refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
    refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
    refine WP.ite (decide (len s₀ = 0))
      (by show VG.AArch64.eval (.zero .x .x24) s₁ = _
          rw [eval_zero, hI.x24, Nat.sub_zero, ofNat_beq_zero (by omega)])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact wp_nil (hb ▸ hI)
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
        ⟨0, rfl, by omega, hI⟩
      rintro n s ⟨c, rfl, hcl, hI⟩
      refine WP.mono ((body_ok v) hp hcl hI) fun s' ⟨c', hcc, hc', hI'⟩ => ?_
      have hz : isa.eval (.nonzero .x .x24) s' = some (decide (len s₀ - c' ≠ 0)) := by
        show VG.AArch64.eval (.nonzero .x .x24) s' = _
        rw [eval_nonzero, hI'.x24, bne, ofNat_beq_zero (by omega)]
        simp
      by_cases he : len s₀ - c' = 0
      · refine .inl ⟨by rw [hz]; simp [he], ?_⟩
        rwa [show c' = len s₀ by omega] at hI'
      · exact .inr ⟨by rw [hz]; simp [he], len s₀ - c', by omega, c', rfl, by omega, hI'⟩
  · rcases preserved_cases r hr h30 with ⟨k, hk, rfl⟩ | hu'
    · exact hsv k hk
    · exact hu r hu'

/-- The state `absorbMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (v : Permutation) {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa (absorbGenericWith v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.absorbAArch64.post s₀ s' := by
  have hpi : Pre (inner s₀) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr, hp.rate, hp.pos_lt⟩
  refine WP.frameReg (hn := by rw [v.absorbMain_depth]; decide) hs.sp16 (fun R hR => ?_) (WP.mono ((correctMain v) hpi) fun s' ⟨hk, hsp, hv, hpost⟩ => ?_)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl, hv⟩, fun msg hm hc => ?_, hpost.2⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : bytesAt (inner s₀).mem (dp s₀) (len s₀) = bytesAt s₀.mem (dp s₀) (len s₀) :=
        bytesAt_congr fun i hi => write_frame_bytes (R := dR s₀) hs.d (len_lt s₀) hi
      have := hpost.1 msg (by
        show stateAt (inner s₀).mem (st s₀) = _
        rw [write_frame_state hs.st]; exact hm) hc
      rw [e] at this
      exact this

/-! ## Constant time -/

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Sha3.absorbAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 72 | .x3 => 0x2000 | .x5 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem absorb_correct (v : Permutation) (s : State) (hs : Proof.Sha3.absorbAArch64.pre s) :
    ∃ t s', Exec isa (absorbWith v.callee) s t s' ∧ abiPreserved s s' ∧ Proof.Sha3.absorbAArch64.post s s' := by
  cases h : v.callee.absorbOverride with
  | none =>
    obtain ⟨t, s', he, hpost⟩ := (correct v) (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', by simpa only [absorbWith, h] using he, hpost⟩
  | some code =>
    simpa only [absorbWith, h] using v.absorbOverrideOk code h s hs

theorem absorb_ct (v : Permutation) : ConstantTime isa Proof.Sha3.absorbAArch64.pre Proof.Sha3.absorbAArch64.pub
    (absorbWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.absorbTaint
  exact VectorTaint.constantTime (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (fun _ _ _ _ hp => agree₀ hp) hhint

theorem absorb_verified (v : Permutation) :
    Verified AArch64.target (Impl.Sha3.AArch64.Stream.absorbWith v.callee) (Spec.Sha3.absorbContract AArch64.abi
      16) :=
  Verified.of_correct (absorb_correct v) (absorb_ct v) (by
    sig_implies [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Proof.Sha3.absorbAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Sha3.AArch64.Stream.Absorb.sat] using
      Proof.Sha3.AArch64.Stream.Absorb.sat)

end VG.Proof.Sha3.AArch64.Stream.Absorb
