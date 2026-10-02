import VerifiedGarbage.Impl.Rc4.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 RegUpd

/-- Only the first byte matters after UMOV and the mask. -/
theorem low_byte (v : BitVec 128) :
    (v.extractLsb' 0 32).setWidth 64 &&& 255#64 = (vbyte v 0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hmask : (255#64 : BitVec 64).getLsbD k = decide (k < 8) := by
    change Nat.testBit 255 k = decide (k < 8)
    exact Nat.testBit_two_pow_sub_one 8 k
  simp only [BitVec.getLsbD_and, hmask, BitVec.getLsbD_setWidth, vbyte,
    BitVec.getLsbD_extractLsb', Nat.mul_zero, Nat.zero_add]
  by_cases h8 : k < 8
  · simp only [h8, decide_true, Bool.and_true, show k < 32 by omega]
  · simp only [h8, decide_false, Bool.and_false, Bool.false_and]

theorem dup_byte (x : BitVec 32) : vbyte (ofVWords x x x x) 0 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [vbyte, ofVWords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth, Nat.mul_zero, Nat.zero_add, hk, decide_true, Bool.true_and,
    show k < 32 by omega, ite_true]

/-- TBL's result at byte zero, in the form the scalar accumulator uses. -/
theorem tbl_byte (s : BitVec 128) (x : BitVec 32) :
    ((ofVBytes fun i =>
      let idx := (vbyte (ofVWords x x x x) i).toNat
      if idx < 16 then vbyte s idx else 0#8).extractLsb' 0 32).setWidth 64 &&& 255#64 =
    (if (x.setWidth 8).toNat < 16 then vbyte s (x.setWidth 8).toNat else 0#8).setWidth 64 := by
  rw [low_byte, vbyte_ofVBytes _ (by decide), dup_byte]

/-- The byte selected from row `r`; all other rows return zero. -/
theorem row_byte (m : Mem) (p : Addr) (idx : Byte) (r : Nat) (hr : r < 16) :
    (if (((idx.setWidth 32) - BitVec.ofNat 32 (16 * r)).setWidth 8).toNat < 16 then
      vbyte (m.read (p + BitVec.ofNat 64 (16 * r)) 16)
        (((idx.setWidth 32) - BitVec.ofNat 32 (16 * r)).setWidth 8).toNat else 0#8) =
    if 16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1) then
      m (p + BitVec.ofNat 64 idx.toNat) else 0 := by
  have hcast : ((idx.setWidth 32 - BitVec.ofNat 32 (16 * r)).setWidth 8) =
      idx - BitVec.ofNat 8 (16 * r) := by
    bv_omega
  rw [hcast]
  have htest : (idx - BitVec.ofNat 8 (16 * r)).toNat < 16 ↔
      16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1) := by
    bv_omega
  by_cases h : (idx - BitVec.ofNat 8 (16 * r)).toNat < 16
  · rw [ite_eq_left h, ite_eq_left (htest.mp h)]
    have hoff : (idx - BitVec.ofNat 8 (16 * r)).toNat = idx.toNat - 16 * r := by bv_omega
    unfold vbyte
    rw [Mem.extractLsb'_read _ _ h, hoff, BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.add_sub_of_le (htest.mp h).1]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (htest.mpr hh))]
    rfl

def Clobbers : List Reg := [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x16]

def Keep (s t : State) : Prop :=
  (∀ r, r ∉ Clobbers → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem keep {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s Q)
    (hc : c.allInstrs (fun i => match dstOf i with
      | none => true | some r => Clobbers.contains r) = true)
    (hn : c.noCalls = true := by decide +kernel) :
    WP isa c s fun t => Q t ∧ Keep s t := by
  obtain ⟨tr, t, he, hq⟩ := h
  refine ⟨tr, t, he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn),
    (Exec.rdwr he).1, (Exec.rdwr he).2.1⟩
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have hh := hc i hi
  intro hd
  rw [hd] at hh
  exact hr (List.contains_iff_mem.mp hh)

theorem Keep.trans {a b c : State} (h : Keep a b) (k : Keep b c) : Keep a c :=
  ⟨fun r hr => (k.1 r hr).trans (h.1 r hr), k.2.1.trans h.2.1, k.2.2.trans h.2.2⟩

syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil,
        exec, State.read, addr, State.load, gpr_write, mem_write, rd_write, wr_write,
        v_write, gpr_setV, mem_setV, rd_setV, wr_setV, v_setV,
        VOp.eval, Size.bits, BitVec.setWidth_eq, BitVec.shiftLeft_zero,
        BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.zero_width_append,
        BitVec.cast_eq, Option.bind_some, Option.map_some, Option.some.injEq,
        exists_eq_left', ite_true, ite_false, reduceCtorEq,
        Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, true_and, and_true, $ls,*]))

def Acc (m : Mem) (p : Addr) (idx : Byte) (r : Nat) : BitVec 64 :=
  if idx.toNat < 16 * r then (m (p + BitVec.ofNat 64 idx.toNat)).setWidth 64 else 0

theorem acc_succ (m : Mem) (p : Addr) (idx : Byte) (r : Nat) :
    Acc m p idx r ||| (if 16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1) then
      m (p + BitVec.ofNat 64 idx.toNat) else 0#8).setWidth 64 = Acc m p idx (r + 1) := by
  by_cases h0 : idx.toNat < 16 * r
  · simp [Acc, h0, show idx.toNat < 16 * (r + 1) by omega,
      show ¬16 * r ≤ idx.toNat by omega]
  · by_cases h1 : idx.toNat < 16 * (r + 1)
    · simp [Acc, h0, h1, show 16 * r ≤ idx.toNat by omega]
    · simp [Acc, h0, h1]

def Inv (s₀ : State) (idx : Byte) (r : Nat) (s : State) : Prop :=
  Keep s₀ s ∧ s.mem = s₀.mem ∧ s.gpr .x5 = BitVec.ofNat 64 (16 * r) ∧
    s.gpr .x6 = Acc s₀.mem (s₀.gpr .x0) idx r ∧ s.gpr .x9 = 255

theorem lookup_step (s₀ s : State) (idx : Byte) (r : Nat) (hr : r < 16)
    (hidx : s₀.gpr .x4 = idx.setWidth 64)
    (hp : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0) 256)
    (h : Inv s₀ idx r s) :
    WP isa (.block lookupStep) s fun t => Inv s₀ idx (r + 1) t := by
  obtain ⟨hk, hm, hx, ha, hmask⟩ := h
  have h0 := hk.1 .x0 (by decide)
  have h4 := hk.1 .x4 (by decide)
  have hread : InRegions (s.rd ++ s.wr) (s₀.gpr .x0 + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [hk.2.1, hk.2.2]
    obtain ⟨region, hregion, hcontains⟩ := hp
    refine ⟨region, hregion, ?_⟩
    unfold Region.Contains at hcontains ⊢
    rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 16 * r < 2 ^ 64 by omega)]
    have hmod := Nat.mod_le ((s₀.gpr .x0 - region.base).toNat + 16 * r) (2 ^ 64)
    omega
  have hoff : BitVec.ofNat 64 (16 * r) + 16#64 = BitVec.ofNat 64 (16 * (r + 1)) := by
    bv_omega
  have h32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have hcast : (idx.setWidth 64).setWidth 32 = idx.setWidth 32 :=
    BitVec.setWidth_setWidth (by decide)
  have hrow : (BitVec.ofNat 64 (16 * r)).setWidth 32 = BitVec.ofNat 32 (16 * r) := by bv_omega
  unfold lookupStep
  refine WP.mono (keep (Q := fun t => t.mem = s₀.mem ∧
      t.gpr .x5 = BitVec.ofNat 64 (16 * (r + 1)) ∧
      t.gpr .x6 = Acc s₀.mem (s₀.gpr .x0) idx (r + 1) ∧ t.gpr .x9 = 255) ?_ (by rfl)) ?_
  · rrun [h0, h4, hidx, hm, hx, ha, hmask, hread, hcast, hrow, hoff,
      h32]
    rw [tbl_byte, row_byte _ _ _ _ hr]
    exact acc_succ _ _ _ _
  · intro t ⟨⟨hm', hx', ha', hmask'⟩, hk'⟩
    exact ⟨hk.trans hk', hm', hx', ha', hmask'⟩

theorem lookup_scan (s₀ s : State) (idx : Byte) (n r : Nat) (hr : r + n ≤ 16)
    (hidx : s₀.gpr .x4 = idx.setWidth 64)
    (hp : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0) 256) (h : Inv s₀ idx r s) :
    WP isa (scanRows lookupStep n) s (Inv s₀ idx (r + n)) := by
  induction n generalizing r s with
  | zero => exact WP.block_nil h
  | succ n ih =>
    unfold scanRows
    refine WP.seq (WP.mono (lookup_step s₀ s idx r (by omega) hidx hp h) fun t ht => ?_)
    have he : r + (n + 1) = (r + 1) + n := by omega
    rw [he]
    exact ih t (r + 1) (by omega) ht

theorem lookup_ok (s : State) (idx : Byte) (hidx : s.gpr .x4 = idx.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256) :
    WP isa lookup s fun t => Keep s t ∧ t.mem = s.mem ∧
      t.gpr .x6 = (s.mem (s.gpr .x0 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧ t.gpr .x9 = 255#64 := by
  have start : WP isa (.block [.movz .x .x5 0 0, .movz .x .x6 0 0, .movz .x .x9 255 0]) s
      (Inv s idx 0) := by
    refine WP.mono (keep (Q := fun t => t.mem = s.mem ∧ t.gpr .x5 = 0 ∧
        t.gpr .x6 = 0 ∧ t.gpr .x9 = 255) ?_ (by rfl)) ?_
    · rrun
    · intro t ⟨⟨hm, hx, ha, hmask⟩, hk⟩
      refine ⟨hk, hm, ?_, ?_, hmask⟩
      · simpa using hx
      · simpa [Acc] using ha
  unfold lookup
  refine WP.seq (WP.mono start fun t ht => ?_)
  refine WP.mono (lookup_scan s t idx 16 0 (by decide) hidx hp ht) fun u hu => ?_
  refine ⟨hu.1, hu.2.1, ?_, hu.2.2.2.2⟩
  simpa [Acc, idx.isLt] using hu.2.2.2.1

end VG.Proof.Rc4.AArch64

