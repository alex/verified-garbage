import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Impl.Sha256.X86_64
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Sha256.X86_64.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Bswap

/-!
# SHA-256 compression function on x86-64: the message schedule and the rounds
-/

namespace VG.Proof.Sha256.X86_64

open VG VG.X86_64 VG.Impl.Sha256.X86_64
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0].setWidth 64 ∧ s.gpr (var t 1) = v[1].setWidth 64 ∧
  s.gpr (var t 2) = v[2].setWidth 64 ∧ s.gpr (var t 3) = v[3].setWidth 64 ∧
  s.gpr (var t 4) = v[4].setWidth 64 ∧ s.gpr (var t 5) = v[5].setWidth 64 ∧
  s.gpr (var t 6) = v[6].setWidth 64 ∧ s.gpr (var t 7) = v[7].setWidth 64

/-- The registers that hold pointers and the count, and `rsp`: never written by the rounds. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega

/-- The registers a round reads are not those it writes after them (`T1`,
`T2`, `d`, `h`), nor are the others it keeps. In three parts: `decide` cannot
synthesize the instance of one long conjunction. -/
theorem round_ne₁ (t : Nat) :
    (¬var t 0 = .r14 ∧ ¬var t 0 = .r15 ∧ ¬var t 1 = .r14 ∧ ¬var t 1 = .r15 ∧
      ¬var t 2 = .r14 ∧ ¬var t 2 = .r15 ∧ ¬var t 3 = .r14 ∧ ¬var t 3 = .r15) ∧
    (¬var t 4 = .r14 ∧ ¬var t 4 = .r15 ∧ ¬var t 5 = .r14 ∧ ¬var t 5 = .r15 ∧
      ¬var t 6 = .r14 ∧ ¬var t 6 = .r15 ∧ ¬var t 7 = .r14 ∧ ¬var t 7 = .r15) := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

theorem round_ne₂ (t : Nat) :
    (¬var t 0 = var t 3 ∧ ¬var t 0 = var t 7 ∧ ¬var t 1 = var t 3 ∧ ¬var t 1 = var t 7 ∧
      ¬var t 2 = var t 3 ∧ ¬var t 2 = var t 7 ∧ ¬var t 3 = var t 7 ∧ ¬var t 4 = var t 3) ∧
    (¬var t 4 = var t 7 ∧ ¬var t 5 = var t 3 ∧ ¬var t 5 = var t 7 ∧ ¬var t 6 = var t 3 ∧
      ¬var t 6 = var t 7 ∧ ¬var t 7 = var t 3 ∧ ¬Reg.r13 = var t 7) := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

theorem round_ne₃ (t : Nat) :
    (¬Reg.rdi = var t 3 ∧ ¬Reg.rdi = var t 7 ∧ ¬Reg.rsi = var t 3 ∧ ¬Reg.rsi = var t 7) ∧
    (¬Reg.rdx = var t 3 ∧ ¬Reg.rdx = var t 7 ∧ ¬Reg.rcx = var t 3 ∧ ¬Reg.rcx = var t 7 ∧
      ¬Reg.rsp = var t 3 ∧ ¬Reg.rsp = var t 7) := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_ne₁ … round_ne₃` say are different where it matters), with
the register writes kept folded (`VG.X86_64.RegUpd`). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : s.gpr T0 = w.setWidth 64) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨⟨n0, n1, n2, n3, n4, n5, n6, n7⟩, ⟨n8, n9, n10, n11, n12, n13, n14, n15⟩⟩ := round_ne₁ t
  obtain ⟨⟨m0, m1, m2, m3, m4, m5, m6, m7⟩, ⟨m8, m9, m10, m11, m12, m13, m14⟩⟩ := round_ne₂ t
  obtain ⟨⟨p2, p3, p4, p5⟩, ⟨p6, p7, p8, p9, p10, p11⟩⟩ := round_ne₃ t
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.X86_64.round]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T0, T1, T2] at hw ⊢
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, execShift32, readSrc32, isa,
    State.setReg32, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, and_self, Nat.reduceLeDiff,
    Nat.reduceEqDiff, not_false_eq_true, reduceCtorEq,
    n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
    m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14,
    h0, h1, h2, h3, h4, h5, h6, h7, hw, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · have n : ¬r = .r14 ∧ ¬r = .r15 ∧ ¬r = d ∧ ¬r = h := by
      simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp only [p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, not_false_eq_true, and_self,
          reduceCtorEq]
    simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, n,
      not_false_eq_true]
  all_goals
    refine congrArg (BitVec.setWidth 64) ?_
    simp only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7, bsig1_eq, ch_eq, bsig0_eq, maj_eq, BitVec.add_assoc]

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofInt 64 ↑(4 * (j % 16))

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hrsi : s.gpr .rsi = bp) (hrcx : s.gpr .rcx = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ↑(4 * t)) 4)
    (hblk : t < 16 → bswap32 (s.mem.readW (bp + BitVec.ofInt 64 ↑(4 * t)) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.gpr T0 = (W M t).setWidth 64 ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha256.X86_64.schedule, ht, ite_true, slot, at_, T0, T1, T2]
    simp only [runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc32, isa, State.ea,
      State.load32, State.store32, State.setReg32, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne,
      RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, not_false_eq_true, reduceCtorEq,
      Nat.reduceLeDiff, hrsi, hrcx, hi, hout, ite_true,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, hb,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, trivial, fun r h0 _ _ => ?_⟩
    simp only [RegUpd.gpr_setReg_of_ne, h0, not_false_eq_true]
  · have hw := hwin (by omega)
    have e2 := hw (t - 2) (by omega) (by omega)
    have e7 := hw (t - 7) (by omega) (by omega)
    have e15 := hw (t - 15) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show (t - 2) % 16 = (t + 14) % 16 by omega] at e2
    rw [show (t - 7) % 16 = (t + 9) % 16 by omega] at e7
    rw [show (t - 15) % 16 = (t + 1) % 16 by omega] at e15
    rw [show (t - 16) % 16 = t % 16 by omega] at e16
    simp only [Impl.Sha256.X86_64.schedule, ht, ite_false, slot, at_, T0, T1, T2]
    simp only [runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu32, execShift32, readSrc32,
      isa, State.ea, State.load32, State.store32, State.setReg32, RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, Nat.reduceLeDiff,
      Nat.reduceEqDiff, and_self, not_false_eq_true, reduceCtorEq, hrcx, hin, hout, ite_true,
      ite_false, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq, e2, e7, e15, e16,
      Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
    have hW := W_ge M (t := t) (by omega)
    rw [ssig0_eq, ssig1_eq] at hW
    refine ⟨by rw [hW], by rw [hW], trivial, trivial, fun r h0 h1 h2 => ?_⟩
    simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h0,
      h1, h2, not_false_eq_true]

/-! ## The 64 rounds -/

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 := by
  simp only [work, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 := by
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  simp only [Region.Contains, slotAddr, ofInt_natCast]
  have : j % 16 < 16 := Nat.mod_lt _ (by omega)
  generalize j % 16 = p at *
  rw [Offset.add_sub_cancel_left]
  simp only [BitVec.toNat_ofNat]
  omega

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  simp only [slotAddr, ofInt_natCast]
  exact Offset.sep _ (by omega) (by omega) (by omega)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha256.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .rsi = bp) (hrcx : sB.gpr .rcx = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → bswap32 (m.readW (bp + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .rsi = bp := (hs.pub .rsi (by decide)).trans hrsi
    have hs_rcx : s.gpr .rcx = scr := (hs.pub .rcx (by decide)).trans hrcx
    refine WP.mono (schedule_ok t s M bp scr hs_rsi hs_rcx
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha256.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1 this.2.2
      simp only [Vars, e] at hv ⊢
      exact hv
    refine WP.mono (round_ok t s₁ _ _ hv₁ hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2.1 this.2.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha256.X86_64

/-!
# SHA-256 compression function on x86-64: the whole function
-/

namespace VG.Proof.Sha256.X86_64

open VG VG.X86_64 VG.Impl.Sha256.X86_64
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [ofInt_natCast]; exact contains_offset h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 4 (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
  rw [ofInt_natCast, ofInt_natCast]
  exact Offset.sep p (by omega) (by omega) (by omega)

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) v).readW
      (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 =
    m.readW (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← ofInt_natCast]; exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, ofInt_natCast]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev bp : Addr := s₀.gpr .rsi
abbrev nb : Nat := (s₀.gpr .rdx).toNat
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨st s₀, 32⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 560⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha256.compressX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 := by
  have := h.nb_lt
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (scr s₀) s₀.gpr saved

theorem saved_bound : ∀ p ∈ saved, 64 ≤ p.2 ∧ p.2 + 8 ≤ 112 := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rcx : s.gpr .rcx = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .mov32 .rax (.mem (at_ .rdi (4 * 0))), .mov32 .rbx (.mem (at_ .rdi (4 * 1))),
    .mov32 .rbp (.mem (at_ .rdi (4 * 2))), .mov32 .r8 (.mem (at_ .rdi (4 * 3))),
    .mov32 .r9 (.mem (at_ .rdi (4 * 4))), .mov32 .r10 (.mem (at_ .rdi (4 * 5))),
    .mov32 .r11 (.mem (at_ .rdi (4 * 6))), .mov32 .r12 (.mem (at_ .rdi (4 * 7)))] := by
  decide

theorem update_eq : update ++ advance = [
    .alu32 .add .rax (.mem (at_ .rdi (4 * 0))), .alu32 .add .rbx (.mem (at_ .rdi (4 * 1))),
    .alu32 .add .rbp (.mem (at_ .rdi (4 * 2))), .alu32 .add .r8 (.mem (at_ .rdi (4 * 3))),
    .alu32 .add .r9 (.mem (at_ .rdi (4 * 4))), .alu32 .add .r10 (.mem (at_ .rdi (4 * 5))),
    .alu32 .add .r11 (.mem (at_ .rdi (4 * 6))), .alu32 .add .r12 (.mem (at_ .rdi (4 * 7))),
    .store32 (at_ .rdi (4 * 0)) .rax, .store32 (at_ .rdi (4 * 1)) .rbx,
    .store32 (at_ .rdi (4 * 2)) .rbp, .store32 (at_ .rdi (4 * 3)) .r8,
    .store32 (at_ .rdi (4 * 4)) .r9, .store32 (at_ .rdi (4 * 5)) .r10,
    .store32 (at_ .rdi (4 * 6)) .r11, .store32 (at_ .rdi (4 * 7)) .r12,
    .alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .rax = v[0].setWidth 64 ∧ s.gpr .rbx = v[1].setWidth 64 ∧
    s.gpr .rbp = v[2].setWidth 64 ∧ s.gpr .r8 = v[3].setWidth 64 ∧
    s.gpr .r9 = v[4].setWidth 64 ∧ s.gpr .r10 = v[5].setWidth 64 ∧
    s.gpr .r11 = v[6].setWidth 64 ∧ s.gpr .r12 = v[7].setWidth 64 := Iff.rfl

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [load_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  simp only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at,
    State.load32, State.setReg32, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg,
    not_false_eq_true, reduceCtorEq, hrdi, h0, h1, h2, h3, h4, h5, h6, h7, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  refine ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, fun r hr => ?_,
    trivial, trivial, trivial⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [RegUpd.gpr_setReg_of_ne, not_false_eq_true, reduceCtorEq]

/-- Eight 32-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((((((m.writeW (p + BitVec.ofInt 64 ((4 * 0 : Nat) : Int)) v[0]).writeW
    (p + BitVec.ofInt 64 ((4 * 1 : Nat) : Int)) v[1]).writeW
    (p + BitVec.ofInt 64 ((4 * 2 : Nat) : Int)) v[2]).writeW
    (p + BitVec.ofInt 64 ((4 * 3 : Nat) : Int)) v[3]).writeW
    (p + BitVec.ofInt 64 ((4 * 4 : Nat) : Int)) v[4]).writeW
    (p + BitVec.ofInt 64 ((4 * 5 : Nat) : Int)) v[5]).writeW
    (p + BitVec.ofInt 64 ((4 * 6 : Nat) : Int)) v[6]).writeW
    (p + BitVec.ofInt 64 ((4 * 7 : Nat) : Int)) v[7])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
    fun k hk => contains_offset' (by omega) (by omega)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rdx = s.gpr .rdx - 1 ∧
      s'.zf = some (s.gpr .rdx - 1 == 0) ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 →
      InRegions s.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide); have i5 := hin 5 (by decide)
  have i6 := hin 6 (by decide); have i7 := hin 7 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide); have m5 := hH 5 (by decide)
  have m6 := hH 6 (by decide); have m7 := hH 7 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execAlu, readSrc32, readSrc,
    isa, ea_at, State.load32, State.store32, State.setReg32, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_setReg, RegUpd.zf_arithFlags, not_false_eq_true, reduceCtorEq, hrdi, i0, i1, i2, i3,
    i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true,
    RegUpd.setWidth_setWidth_32,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨?_, by rw [e64], by rw [e1], by rw [e1], trivial, trivial, trivial, trivial, trivial⟩
  simp only [writeState, Vector.getElem_zipWith]

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  rcases hf with hf | hf <;> refine Spill.Saved.frame h hf fun p hp' r hr => ?_ <;>
    rw [List.mem_singleton.mp hr] <;> have := saved_bound p hp'
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by omega))

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    bswap32 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) =
      W (blk s₀ i) t := by
  rw [W_lt _ ht, bswap32_readW, ofInt_natCast]
  simp only [blk, blockAt, parseBlock]
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) from
      Offset.add_add _ _ 1,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) from
      Offset.add_add _ _ 1,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 3) from
      Offset.add_add _ _ 1]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 560⟩ := Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.rdi hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      bswap32 (m.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hrsi₁ : s₁.gpr .rsi = blkAddr s₀ i := (hpub₁ .rsi (by decide)).trans hL.rsi
  have hrcx₁ : s₁.gpr .rcx = scr s₀ := (hpub₁ .rcx (by decide)).trans hL.rcx
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hrsi₁ hrcx₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have hrdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [hR.pub .rdi (by decide), hpub₁ .rdi (by decide), hL.rdi]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hrdi₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset' (by omega) (by omega)) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hrsi₃, hrdx₃, hzf₃, hrdi₃, hrcx₃, hrsp₃, hrd₃, hwr₃⟩ := h₃
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hrdx : s₂.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .rdx (by decide), hL.rdx]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hrdi₃, hrdi₂], by rw [hrcx₃, pub₂ .rcx (by decide), hL.rcx],
      by rw [hrsp₃, pub₂ .rsp (by decide), hL.rsp], by rw [hrd₃, hR.rd, hrd₁, hL.rd],
      by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_, ?_⟩
    · rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine saved_frame hp ?_ (.inr (frame_writeState (Frame.refl _ _) _))
      refine saved_frame hp ?_ (.inl hR.frame)
      rw [hm₁]; exact hL.saved
  have hev : eval .ne s₃ = some (!(s₂.gpr .rdx - 1 == 0)) := by
    simp [eval, hzf₃]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon _ rfl with rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrsi₃, pub₂ .rsi (by decide), hL.rsi]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by omega)))
    · rw [hrdx₃, hrdx]

/-! ## Prologue and epilogue -/

/-- The memory after the prologue. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (scr s₀) s₀.gpr saved

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_ok .rcx saved s₀ fun p hp' => ?_) fun s₁ ⟨hg, hrd, hwr, hm⟩ => ?_
  · have := saved_bound p hp'
    exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
      State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨hg, hrd, hwr, hm, by rw [hg]⟩

theorem saveMem_saved {s₀ : State} : Saved s₀ (saveMem s₀) :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame {s₀ : State} : Frame [scrR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := saved_bound p hp; omega) (by decide)

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], by rw [hg], hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (contains_offset' (off := 4 * k) (len := 32) (by omega) (by omega))
      (by simpa using hp.st_scr)
      (by decide), ← stateAt_get _ _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha256.compressX86_64.post s₀ s' := by
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  refine WP.mono (Spill.restore_ok .rcx saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [hc.rcx]; exact hc.saved)) fun s' ⟨h₁, h₂, hm, _⟩ => ?_
  · have := saved_bound p hp'
    rw [hc.rcx, hc.rd, hc.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) hc.rsp, by rw [hm]; exact hret⟩,
      by show stateAt _ _ = _; rw [hm]; exact hc.state⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha256.compressX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg]; simp [blkAddr]
        rdx := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 560⟩]

theorem compress_verified :
    Verified X86_64.target Impl.Sha256.X86_64.compress Proof.Sha256.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact Offset.disjoint_of_le (by decide) (by decide)
    | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

end VG.Proof.Sha256.X86_64
