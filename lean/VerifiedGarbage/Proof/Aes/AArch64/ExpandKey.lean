import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Impl.Aes.AArch64.ExpandKey
import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The AES key expansion on AArch64

Untrusted: everything here is checked by Lean.

`subAll` (`toBs`, the S-box, `fromBs`) applies the S-box to every byte of
the eight words (`subAll_wp`, from the bitsliced layers' lemmas); each
word of the schedule is then a few scalar instructions around it
(`word_ok`), and the loop over the words keeps the schedule's bytes so far
equal to the specification's (`WInv`).
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (sbox xtimes subBytes subWord rotWord rcon xorWord)

/-! ## The S-box on every byte -/

/-- The four states that the words hold, as `InRel` relates them. -/
def stOf (Q : Nat → BitVec 64) (b : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (b + 4 * (i.1 / 8))).extractLsb' (8 * (i.1 % 8)) 8

theorem inRel_stOf (Q : Nat → BitVec 64) : InRel Q (stOf Q) := by
  intro b hb i hi j hj
  rw [getD_eq _ hi, stOf, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb']
  simp [hj]

theorem subAll_wp {s : State} (hok : Ok linCfg s) {P : State → Prop}
    (h : ∀ s', (∀ k < 8, ∀ t < 8, (Q s' k).extractLsb' (8 * t) 8 = sbox ((Q s k).extractLsb' (8 * t) 8)) →
      s'.rd = s.rd → s'.wr = s.wr → (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) →
      Frame [⟨s.gpr sb, 8 * 48⟩] s.mem s'.mem → P s') :
    WP isa (.block subAll) s P := by
  simp only [subAll]
  repeat rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₁, hs₁, h₁, rd₁, wr₁, -, o₁, f₁⟩ := toBs_ok hok
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hb₁ : s₁.gpr sb = s.gpr sb := o₁ sb (by decide)
  have ok₁ : Ok linCfg s₁ := hok.congr hb₁ hb₁ rd₁ wr₁
  obtain ⟨s₂, hs₂, h₂, rd₂, wr₂, -, o₂, f₂⟩ := sbox_ok (s := s₁) ok₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have hb₂ : s₂.gpr sb = s.gpr sb := (o₂ sb (by decide)).trans hb₁
  have ok₂ : Ok linCfg s₂ := hok.congr hb₂ hb₂ (rd₂.trans rd₁) (wr₂.trans wr₁)
  obtain ⟨s₃, hs₃, h₃, rd₃, wr₃, -, o₃, f₃⟩ := fromBs_ok ok₂
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  have hin := in_of_bs h₃ (bs_subBytes h₂ (bs_of_in h₁ (inRel_stOf (Q s))))
  refine h s₃ (fun k hk t ht => ?_) (rd₃.trans (rd₂.trans rd₁)) (wr₃.trans (wr₂.trans wr₁))
    (fun r hr => (o₃ r hr).trans ((o₂ r hr).trans (o₁ r hr))) ?_
  · refine byte_ext fun j hj => ?_
    have := hin (k % 4) (by omega) (t + 8 * (k / 4)) (by omega) j hj
    rw [show k % 4 + 4 * ((t + 8 * (k / 4)) / 8) = k by omega,
      show 8 * ((t + 8 * (k / 4)) % 8) + j = 8 * t + j by omega] at this
    rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, this, getD_eq _ (by omega)]
    simp only [subBytes, Vector.getElem_map, stOf, Vector.getElem_ofFn]
    rw [show k % 4 + 4 * ((t + 8 * (k / 4)) / 8) = k by omega,
      show (t + 8 * (k / 4)) % 8 = t by omega]
  · have e₁ : slotRegion linCfg s = ⟨s.gpr sb, 8 * 48⟩ := rfl
    have e₂ : slotRegion sboxCfg s₁ = ⟨s.gpr sb, 8 * 48⟩ := by
      simp only [slotRegion, sboxCfg, hb₁]
    have e₃ : slotRegion linCfg s₂ = ⟨s.gpr sb, 8 * 48⟩ := by
      simp only [slotRegion, linCfg, hb₂]
    rw [e₁] at f₁; rw [e₂] at f₂; rw [e₃] at f₃
    exact (f₁.trans f₂).trans f₃

/-! ## The scalar blocks -/

/-- The round constant after one more round. -/
def rcNext (v : BitVec 64) : BitVec 64 :=
  ((v <<< 1) ^^^ (v >>> 7) * (BitVec.ofNat 16 0x1b).setWidth 64) &&& (BitVec.ofNat 16 0xff).setWidth 64

set_option simprocs false in
theorem rotTail_ok {s : State} {b : Addr} (hb : s.gpr .x5 = b)
    (hr : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (8 * 59)) 8)
    (hw : InRegions s.wr (b + BitVec.ofNat 64 (8 * 59)) 8) :
    ∃ s', runBlock isa rotTail s = some s' ∧
      s'.gpr (q 0) = (((s.gpr (q 0)).setWidth 32).rotateRight 8 ^^^
        (s.mem.readW (b + BitVec.ofNat 64 (8 * 59)) 64).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 59))
        (rcNext (s.mem.readW (b + BitVec.ofNat 64 (8 * 59)) 64)) ∧
      (∀ r, r ≠ q 0 → r ≠ q 1 → r ≠ q 2 → r ≠ q 3 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [rotTail, rconSlot, ldS, stS, lsrI, eorR, andR, q, sb,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bytes,
      Size.bits, State.read, State.write, hb, hr, hw, ite_true, ite_false, Option.map_some,
      Option.bind_some, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r h1 h2 h3 h4 => by simp [q] at h1 h2 h3 h4; simp [h1, h2, h3, h4], rfl, rfl⟩
  · simp (config := {decide := true}) [q, Mem.readW]
  · simp only [Mem.readW, Mem.writeW, rcNext]
    rfl

/-- `q 1 := (x1 − 4) ∨ (x3 − 8)`: zero exactly when `i mod Nk = 4` and `Nk = 8`. -/
theorem chk_ok (s : State) :
    ∃ s', runBlock isa [.subImm .x (q 1) .x1 4, .subImm .x (q 2) .x3 8, orrR (q 1) (q 1) (q 2)] s = some s' ∧
      s'.gpr (q 1) = (s.gpr .x1 - 4) ||| (s.gpr .x3 - 8) ∧
      (∀ r, r ≠ q 1 → r ≠ q 2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide),
      runStep_some, runBlock_cons, orrR]
    rfl, ?_⟩
  exact ⟨by simp [State.write, State.read, q], fun r h1 h2 => by simp [State.write, h1, h2], rfl, rfl, rfl⟩

/-- `w[i] := w[i − Nk] ⊕ temp`, and on to the next word. -/
def wordStore : List Instr :=
  [.ldr .w (q 1) .x0 0, .logic .eor .w (q 0) (q 0) (q 1), .str .w (q 0) .x2 0,
   .addImm .x .x0 .x0 4, .addImm .x .x2 .x2 4, .addImm .x .x1 .x1 1, .sub .x (q 1) .x1 .x3]

/-- The word stored. -/
abbrev newW (s : State) : BitVec 32 := (s.gpr (q 0)).setWidth 32 ^^^ s.mem.readW (s.gpr .x0) 32

set_option simprocs false in
theorem wordStore_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4)
    (hw : InRegions s.wr (s.gpr .x2) 4) :
    ∃ s', runBlock isa wordStore s = some s' ∧
      s'.gpr (q 0) = (newW s).setWidth 64 ∧ s'.mem = s.mem.writeW (s.gpr .x2) (newW s) ∧
      s'.gpr .x0 = s.gpr .x0 + 4 ∧ s'.gpr .x2 = s.gpr .x2 + 4 ∧ s'.gpr .x1 = s.gpr .x1 + 1 ∧
      s'.gpr (q 1) = s.gpr .x1 + 1 - s.gpr .x3 ∧
      (∀ r, r ≠ q 0 → r ≠ q 1 → r ≠ .x0 → r ≠ .x2 → r ≠ .x1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 : s.gpr .x0 + BitVec.ofNat 64 0 = s.gpr .x0 := BitVec.add_zero _
  have e2 : s.gpr .x2 + BitVec.ofNat 64 0 = s.gpr .x2 := BitVec.add_zero _
  refine ⟨_, by
    simp (config := {decide := true}) only [wordStore, q, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bytes, Size.bits, State.read, State.write, e0, e2, hr, hw,
      ite_true, ite_false, Option.map_some, Option.bind_some, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, ?_, by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}), by simp (config := {decide := true}) [q],
    fun r h1 h2 h3 h4 h5 => by simp [q] at h1 h2; simp [h1, h2, h3, h4, h5], rfl, rfl⟩
  · simp (config := {decide := true}) [q, Mem.readW]
  · simp only [Mem.writeW, Mem.readW, newW, q, sw_32]
    rfl

theorem movX1_ok (s : State) :
    ∃ s', runBlock isa [.movz .x .x1 0 0] s = some s' ∧ s'.gpr .x1 = 0 ∧
      (∀ r, r ≠ .x1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, exec]; rfl, ?_⟩
  exact ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl⟩

theorem decX4_ok (s : State) :
    ∃ s', runBlock isa [.subImm .x .x4 .x4 1] s = some s' ∧ s'.gpr .x4 = s.gpr .x4 - 1 ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [State.write, State.read], fun r h => by simp [State.write, h], rfl, rfl, rfl⟩

set_option simprocs false in
theorem copyBody_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 8)
    (hw : InRegions s.wr (s.gpr .x2) 8) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x2) (s.mem.readW (s.gpr .x0) 64) ∧
      s'.gpr (q 0) = s.mem.readW (s.gpr .x0) 64 ∧
      s'.gpr .x0 = s.gpr .x0 + 8 ∧ s'.gpr .x2 = s.gpr .x2 + 8 ∧ s'.gpr .x4 = s.gpr .x4 - 8 ∧
      (∀ r, r ≠ q 0 → r ≠ .x0 → r ≠ .x2 → r ≠ .x4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 : s.gpr .x0 + BitVec.ofNat 64 0 = s.gpr .x0 := BitVec.add_zero _
  have e2 : s.gpr .x2 + BitVec.ofNat 64 0 = s.gpr .x2 := BitVec.add_zero _
  refine ⟨_, by
    simp (config := {decide := true}) only [copyBody, q, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bytes, Size.bits, State.read, State.write, e0, e2, hr, hw,
      ite_true, ite_false, Option.map_some, Option.bind_some, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, ?_, by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}), fun r h1 h2 h3 h4 => by simp [q] at h1; simp [h1, h2, h3, h4],
    rfl, rfl⟩
  · simp only [Mem.writeW, Mem.readW]
    rfl
  · simp only [Mem.readW, q]
    rfl

set_option simprocs false in
theorem wordSetup_ok {s : State} {b : Addr} (hb : s.gpr .x5 = b)
    (hw : InRegions s.wr (b + BitVec.ofNat 64 (8 * 59)) 8) :
    ∃ s', runBlock isa wordSetup s = some s' ∧
      s'.gpr (q 0) = s.gpr (q 0) >>> 32 ∧ s'.gpr .x0 = s.gpr .x2 - s.gpr .x1 ∧
      s'.gpr .x3 = s.gpr .x1 >>> 2 ∧ s'.gpr .x1 = 0 ∧
      s'.gpr .x4 = (s.gpr .x1 >>> 2) + (s.gpr .x1 >>> 2) + (s.gpr .x1 >>> 2) + 28 ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 59)) (1 : BitVec 64) ∧
      (∀ r, r ≠ q 0 → r ≠ q 1 → r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [wordSetup, rconSlot, lsrI, stS, q, sb,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, State.write, hb, hw, ite_true, ite_false, Option.bind_some, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨by simp (config := {decide := true}) [q], by simp (config := {decide := true}),
    by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}), ?_,
    fun r h1 h2 h3 h4 h5 h6 => by simp [q] at h1 h2; simp [h1, h2, h3, h4, h5, h6], rfl, rfl⟩
  simp only [Mem.writeW]
  rfl

/-! ## Bytes -/

/-- The round constant slot's value: `x^k`. -/
def rcW (k : Nat) : BitVec 64 := (Nat.repeat xtimes k (1 : Byte)).setWidth 64

theorem rcNext_rcW : ∀ k < 10, rcNext (rcW k) = rcW (k + 1) := by decide

theorem rcW_zero : rcW 0 = 1 := by decide

theorem rcW_byte (k : Nat) {t : Nat} (ht : t < 4) :
    (rcW k).extractLsb' (8 * t) 8 = if t = 0 then Nat.repeat xtimes k 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [rcW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  split
  · subst_vars; simp [hj]; intro; omega
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp

theorem xor32_byte (x : BitVec 64) (y : BitVec 32) {t : Nat} (ht : t < 4) :
    (x.setWidth 32 ^^^ y).extractLsb' (8 * t) 8 = x.extractLsb' (8 * t) 8 ^^^ y.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  simp [hj, show 8 * t + j < 32 by omega]

theorem sw64_byte (v : BitVec 32) (t : Nat) :
    (v.setWidth 64).extractLsb' (8 * t) 8 = v.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  by_cases h : 8 * t + j < 32
  · simp [hj, h, show 8 * t + j < 64 by omega]
  · simp [hj, BitVec.getLsbD_of_ge v _ (Nat.le_of_not_lt h)]

theorem rot_byte (x c : BitVec 64) {t : Nat} (ht : t < 4) :
    ((((x.setWidth 32).rotateRight 8) ^^^ c.setWidth 32).setWidth 64).extractLsb' (8 * t) 8 =
      x.extractLsb' (8 * ((t + 1) % 4)) 8 ^^^ c.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateRight]
  simp only [hj, decide_true, Bool.true_and, show 8 * t + j < 64 by omega, show 8 * t + j < 32 by omega]
  by_cases h : t < 3
  · rw [ite_eq_left ((show 8 * t + j < 32 - 8 % 32 by omega)),
      show 8 % 32 + (8 * t + j) = 8 * ((t + 1) % 4) + j by omega]
    simp [show 8 * ((t + 1) % 4) + j < 32 by omega]
  · rw [ite_eq_right ((show ¬ 8 * t + j < 32 - 8 % 32 by omega)),
      show 8 * t + j - (32 - 8 % 32) = 8 * ((t + 1) % 4) + j by omega]
    simp [show 8 * ((t + 1) % 4) + j < 32 by omega]

theorem ld_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 4) :
    (m.readW a 32).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) :=
  (Mem.readW_byte m a ht).symm

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem lsr32_byte (x : BitVec 64) (t : Nat) :
    (x >>> 32).extractLsb' (8 * t) 8 = x.extractLsb' (8 * (t + 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  simp only [hj, decide_true, Bool.true_and]
  congr 1; omega

/-! ## Arithmetic -/

theorem ofNat_beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 x ≠ 0 := by
      intro h'; apply h
      have := congrArg BitVec.toNat h'
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simp only [h, decide_false, beq_eq_false_iff_ne]; exact this

theorem chk_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ((BitVec.ofNat 64 a - 4) ||| (BitVec.ofNat 64 b - 8) == 0) = decide (a = 4 ∧ b = 8) := by
  by_cases h : a = 4 ∧ b = 8
  · obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp heq
    apply h; constructor <;> bv_omega

theorem next_beq {a n : Nat} (ha : a < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 a + 1 - BitVec.ofNat 64 n == 0) = decide (a + 1 = n) := by
  by_cases h : a + 1 = n
  · simp only [h, decide_true, beq_iff_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; bv_omega

theorem off_step (S : Addr) (k : Nat) :
    S + BitVec.ofNat 64 (4 * k) + 4 = S + BitVec.ofNat 64 (4 * (k + 1)) := by
  rw [BitVec.add_assoc, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  rfl

theorem off_step8 (S : Addr) (k : Nat) :
    S + BitVec.ofNat 64 (8 * k) + 8 = S + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
  rfl

theorem ofNat_sub_eight {x : Nat} (h : 8 ≤ x) : BitVec.ofNat 64 x - 8 = BitVec.ofNat 64 (x - 8) := Offset.ofNat_sub_ofNat h

theorem div_pred_zero {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hi : nk ≤ i) (h : i % nk = 0) :
    (i - 1) / nk + 1 = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem div_pred_ne {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (h : i % nk ≠ 0) :
    (i - 1) / nk = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem rot_lt {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hn : i < 4 * (nk + 7)) (h : i % nk = 0) :
    (i - 1) / nk < 10 := by
  rcases h3 with rfl | rfl | rfl <;> omega

/-! ## One word -/

/-- The setting of the word loop: the schedule at `S`, the scratch buffer
at `B`, and the key `kl` of `nk` words. -/
structure WSetup (s₀ : State) (S B : Addr) (kl : List Byte) (nk : Nat) : Prop where
  nk3 : nk = 4 ∨ nk = 6 ∨ nk = 8
  len : kl.length = 4 * nk
  sch : (⟨S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨B, 512⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S, 240⟩ ⟨B, 512⟩

/-- Before word `i`. -/
structure WInv (s₀ : State) (S B : Addr) (kl : List Byte) (nk i : Nat) (s : State) : Prop where
  hi : nk ≤ i
  hn : i < 4 * (nk + 7)
  x2 : s.gpr .x2 = S + BitVec.ofNat 64 (4 * i)
  x0 : s.gpr .x0 = S + BitVec.ofNat 64 (4 * (i - nk))
  x3 : s.gpr .x3 = BitVec.ofNat 64 nk
  x1 : s.gpr .x1 = BitVec.ofNat 64 (i % nk)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (4 * (nk + 7) - i)
  x5 : s.gpr .x5 = B
  temp : ∀ t < 4, (s.gpr (q 0)).extractLsb' (8 * t) 8 = (kw kl nk (i - 1)).getD t 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sched : ∀ k < 4 * i, s.mem (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  rc : s.mem.readW (B + BitVec.ofNat 64 (8 * 59)) 64 = rcW ((i - 1) / nk)
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- After the last word. -/
structure WDone (s₀ : State) (S B : Addr) (kl : List Byte) (nk : Nat) (s : State) : Prop where
  x5 : s.gpr .x5 = B
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sched : ∀ k < 16 * (nk + 7), s.mem (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- `temp` computed (in the low 32 bits of `q 0`), from `s`. -/
structure Mid (B : Addr) (kl : List Byte) (nk i : Nat) (s s' : State) : Prop where
  temp : ∀ t < 4, (s'.gpr (q 0)).extractLsb' (8 * t) 8 = (kTemp nk i (kw kl nk (i - 1))).getD t 0
  keep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨B, 8 * 48⟩, ⟨B + BitVec.ofNat 64 (8 * 59), 8⟩] s.mem s'.mem
  rc : s'.mem.readW (B + BitVec.ofNat 64 (8 * 59)) 64 = rcW (i / nk)

theorem slot_disj (B : Addr) : Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * 59), 8⟩ ⟨B, 8 * 48⟩ :=
  Offset.disjoint_base B (by decide) (by decide)

theorem q_lw (r : Reg) (hr : r ∉ layerWrites) : r ≠ q 0 ∧ r ≠ q 1 ∧ r ≠ q 2 ∧ r ≠ q 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; exact hr (by decide))

theorem WInv.ok {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) : Ok linCfg s :=
  Ok.of_region (r := ⟨B, 512⟩) (by rw [hi.wr]; exact hs.scr) hi.x5.symm (by simp [linCfg])
    (by simp [linCfg]) rfl

/-- `SUBWORD(ROTWORD(temp)) ⊕ Rcon`, and the next round constant. -/
theorem rot_wp {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) (h0 : i % nk = 0) :
    WP isa (.block rotWordStep) s (Mid B kl nk i s) := by
  have h3 := hs.nk3
  have hi1 := hi.hi
  have hn := hi.hn
  have hlen := kw_length hs.len (by omega) (i - 1)
  simp only [rotWordStep]
  rw [WP.block_append_iff (M := isa)]
  refine subAll_wp (hi.ok hs) fun s₂ h₂ rd₂ wr₂ o₂ f₂ => ?_
  have hb₂ : s₂.gpr .x5 = B := (o₂ .x5 (by decide)).trans hi.x5
  have i59 : InRegions s₂.wr (B + BitVec.ofNat 64 (8 * 59)) 8 :=
    in_off (by rw [wr₂, hi.wr]; exact hs.scr) (by omega) (by omega)
  have r59 : InRegions (s₂.rd ++ s₂.wr) (B + BitVec.ofNat 64 (8 * 59)) 8 := by
    obtain ⟨r, hr, hc⟩ := i59; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨s₃, hs₃, q₃, m₃, o₃, rd₃, wr₃⟩ := rotTail_ok hb₂ r59 i59
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  have f₂' : Frame [⟨B, 8 * 48⟩] s.mem s₂.mem := by rw [← hi.x5]; exact f₂
  have rc₂ : s₂.mem.readW (B + BitVec.ofNat 64 (8 * 59)) 64 = rcW ((i - 1) / nk) := by
    rw [f₂'.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_disj B) (by decide), hi.rc]
  refine ⟨fun t ht => ?_, fun r hr => ?_, rd₃.trans rd₂, wr₃.trans wr₂, ?_, ?_⟩
  · rw [q₃, rot_byte _ _ ht, show s₂.gpr (q 0) = Q s₂ 0 from rfl, h₂ 0 (by omega) _ (by omega),
      show Q s 0 = s.gpr (q 0) from rfl, hi.temp _ (by omega), rc₂, rcW_byte _ ht]
    simp only [kTemp, h0, ite_true]
    rw [xorWord_getD (by simp [subWord, rotWord_length hlen]) (by rfl) ht,
      subWord_getD (by rw [rotWord_length hlen]; exact ht), rotWord_getD hlen ht, rcon_getD _ ht,
      ← div_pred_zero h3 hi1 h0, Nat.add_sub_cancel]
  · obtain ⟨a1, a2, a3, a4⟩ := q_lw r hr
    rw [o₃ r a1 a2 a3 a4, o₂ r hr]
  · rw [m₃]
    refine Frame.writeW (r := ⟨B + BitVec.ofNat 64 (8 * 59), 8⟩) ?_ (by simp) _ (Region.contains_self _ _)
    exact f₂'.mono (by simp)
  · rw [m₃, Mem.readW_writeW_self64, rc₂, rcNext_rcW _ (rot_lt h3 hn h0), div_pred_zero h3 hi1 h0]

theorem temp_wp {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) :
    WP isa (.ite (.zero .x .x1) (.block rotWordStep)
      (.seq (.block [.subImm .x (q 1) .x1 4, .subImm .x (q 2) .x3 8, orrR (q 1) (q 1) (q 2)])
        (.ite (.zero .x (q 1)) (.block subAll) (.block [])))) s (Mid B kl nk i s) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hmod := Nat.mod_lt i hnk
  have hlen := kw_length hs.len hnk (i - 1)
  have hev : AArch64.eval (.zero .x .x1) s = some (decide (i % nk = 0)) := by
    simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, hi.x1,
      ofNat_beq_zero (x := i % nk) (by omega)]
  refine WP.ite _ hev (fun hb => rot_wp hs hi (by simpa using hb)) (fun hb => ?_)
  have h0 : i % nk ≠ 0 := by simpa using hb
  obtain ⟨s₁, hs₁, q₁, o₁, m₁, rd₁, wr₁⟩ := chk_ok s
  refine WP.seq (WP.of_runBlock ⟨s₁, hs₁, ?_⟩)
  have hev₁ : AArch64.eval (.zero .x (q 1)) s₁ = some (decide (i % nk = 4 ∧ nk = 8)) := by
    simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, q₁, hi.x1, hi.x3]
    rw [chk_beq (by omega) (by omega)]
  have g₁ : ∀ r, r ∉ layerWrites → s₁.gpr r = s.gpr r := fun r hr =>
    o₁ r (q_lw r hr).2.1 (q_lw r hr).2.2.1
  have hq0 : s₁.gpr (q 0) = s.gpr (q 0) := o₁ _ (by decide) (by decide)
  refine WP.ite _ hev₁ (fun hb₁ => ?_) (fun hb₁ => ?_)
  · -- `SUBWORD(temp)`.
    have h8 : nk = 8 ∧ i % nk = 4 := by simp at hb₁; omega
    have ok₁ : Ok linCfg s₁ := Ok.of_region (r := ⟨B, 512⟩) (by rw [wr₁, hi.wr]; exact hs.scr)
      (by rw [show linCfg.base = .x5 from rfl, o₁ _ (by decide) (by decide), hi.x5]) (by simp [linCfg])
      (by simp [linCfg]) rfl
    refine subAll_wp ok₁ fun s₂ h₂ rd₂ wr₂ o₂ f₂ => ?_
    have f₂' : Frame [⟨B, 8 * 48⟩] s.mem s₂.mem := by
      rw [← m₁, ← hi.x5, ← o₁ .x5 (by decide) (by decide)]; exact f₂
    refine ⟨fun t ht => ?_, fun r hr => (o₂ r hr).trans (g₁ r hr), rd₂.trans rd₁, wr₂.trans wr₁,
      f₂'.mono (by simp), ?_⟩
    · rw [show s₂.gpr (q 0) = Q s₂ 0 from rfl, h₂ 0 (by omega) _ (by omega),
        show Q s₁ 0 = s.gpr (q 0) from hq0, hi.temp _ ht]
      rw [kTemp, ite_eq_right h0, ite_eq_left (show nk > 6 ∧ i % nk = 4 by omega),
        subWord_getD (by rw [hlen]; exact ht)]
    · rw [f₂'.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_disj B) (by decide), hi.rc,
        div_pred_ne h3 h0]
  · have h8 : ¬ (nk > 6 ∧ i % nk = 4) := by simp at hb₁; omega
    refine WP.block_nil ⟨fun t ht => ?_, g₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_⟩
    · rw [hq0, hi.temp _ ht, kTemp, ite_eq_right h0, ite_eq_right h8]
    · rw [m₁, hi.rc, div_pred_ne h3 h0]

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply (out_of_disj h (Region.contains_self _ _) (Region.contains_self _ _))

/-- The memory after word `i` is stored. -/
def storeMem (s₂ : State) (S : Addr) (nk i : Nat) : Mem :=
  s₂.mem.writeW (S + BitVec.ofNat 64 (4 * i))
    ((s₂.gpr (q 0)).setWidth 32 ^^^ s₂.mem.readW (S + BitVec.ofNat 64 (4 * (i - nk))) 32)

theorem store_facts {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s s₂ : State} (hi : WInv s₀ S B kl nk i s) (hm : Mid B kl nk i s s₂) :
    (∀ k < 4 * (i + 1), storeMem s₂ S nk i (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0) ∧
    Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem (storeMem s₂ S nk i) ∧ Saved s₀ B (storeMem s₂ S nk i) ∧
    (storeMem s₂ S nk i).readW (B + BitVec.ofNat 64 (8 * 59)) 64 = rcW (i / nk) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have fS : ∀ k < 240, s₂.mem (S + BitVec.ofNat 64 k) = s.mem (S + BitVec.ofNat 64 k) := fun k hk =>
    hm.frame.bytes (R := ⟨S, 240⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.sep.sub_right (Region.sub_prefix (by decide))
      · exact hs.sep.sub_right (Offset.sub_base B (by decide))) (by simp) hk
  have sched' : ∀ k < 4 * (i + 1),
      storeMem s₂ S nk i (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0 := by
    intro k hk
    unfold storeMem
    by_cases hki : k < 4 * i
    · rw [writeW32_other _ (Offset.disjoint S (Or.inl (by omega)) (by omega) (by omega)), fS k (by omega),
        hi.sched k hki]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 4 ∧ k = 4 * i + t := ⟨k - 4 * i, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht, xor32_byte _ _ ht, hm.temp t ht,
        ← Mem.readW_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, fS _ (by omega),
        hi.sched _ (by omega), show (4 * (i - nk) + t) / 4 = i - nk by omega,
        show (4 * (i - nk) + t) % 4 = t by omega, show (4 * i + t) / 4 = i by omega,
        show (4 * i + t) % 4 = t by omega, kw_step kl hnk hi1,
        xorWord_getD (kw_length hs.len hnk _) (kTemp_length (kw_length hs.len hnk _)) ht, BitVec.xor_comm]
  have fr : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem (storeMem s₂ S nk i) := by
    unfold storeMem
    refine Frame.writeW (hi.frame.trans (hm.frame.sub fun r hr => ?_)) (r := ⟨S, 240⟩) (by simp) _
      (c_off S (by omega) (by omega))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨B, 512⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨B, 512⟩, by simp, Offset.sub_base B (by decide)⟩
  have hdS : ∀ r ∈ [(⟨S + BitVec.ofNat 64 (4 * i), 4⟩ : Region)],
      Region.Disjoint ⟨B + BitVec.ofNat 64 384, 88⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have d1 : Region.Disjoint ⟨S, 240⟩ ⟨B + BitVec.ofNat 64 384, 88⟩ :=
      hs.sep.sub_right (Offset.sub_base B (d := 384) (n := 88) (k := 512) (by decide))
    have d2 : Region.Disjoint ⟨S + BitVec.ofNat 64 (4 * i), 4⟩ ⟨B + BitVec.ofNat 64 384, 88⟩ :=
      d1.sub_left (Offset.sub_base S (d := 4 * i) (n := 4) (k := 240) (by omega))
    exact d2.symm
  have sv : Saved s₀ B (storeMem s₂ S nk i) := by
    unfold storeMem
    refine saved_frame (saved_frame hi.saved hm.frame fun r hr => ?_)
      (Frame.writeW (Frame.refl [⟨S + BitVec.ofNat 64 (4 * i), 4⟩] _) (by simp) _
        (Region.contains_self _ _)) hdS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base B (by decide) (by decide)
    · exact Offset.disjoint B (Or.inl (by decide)) (by decide) (by decide)
  have rc : (storeMem s₂ S nk i).readW (B + BitVec.ofNat 64 (8 * 59)) 64 = rcW (i / nk) := by
    rw [storeMem, Mem.readW_writeW_sep ((hs.sep.sub_right (Offset.sub_base B (by decide))).symm.sep
      (Region.contains_self _ _) (c_off S (by omega) (by omega))) (by decide), hm.rc]
  exact ⟨sched', fr, sv, rc⟩

theorem ofNat_bne_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = !decide (x = 0) := by
  rw [bne, ofNat_beq_zero hx]

theorem word_ok {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) :
    WP isa wordBody s fun s' =>
      (AArch64.eval (.nonzero .x .x4) s' = some false ∧ WDone s₀ S B kl nk s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧ WInv s₀ S B kl nk (i + 1) s') := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have hmod := Nat.mod_lt i hnk
  unfold wordBody
  refine WP.seq (WP.mono (temp_wp hs hi) fun s₂ hm => ?_)
  have k₂ : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5], s₂.gpr r = s.gpr r := fun r hr =>
    hm.keep r (fun h => by revert hr; revert h; revert r; decide)
  have x0₂ := (k₂ .x0 (by simp)).trans hi.x0
  have x1₂ := (k₂ .x1 (by simp)).trans hi.x1
  have x2₂ := (k₂ .x2 (by simp)).trans hi.x2
  have x3₂ := (k₂ .x3 (by simp)).trans hi.x3
  have hwS : (⟨S, 240⟩ : Region) ∈ s₂.wr := by rw [hm.wr, hi.wr]; exact hs.sch
  -- `w[i] := w[i − Nk] ⊕ temp`.
  refine WP.seq ?_
  obtain ⟨s₃, hs₃, q0₃, m₃, x0₃, x2₃, x1₃, q1₃, o₃, rd₃, wr₃⟩ := wordStore_ok (s := s₂)
    (by rw [x0₂]; exact in_off (List.mem_append_right _ hwS) (by omega) (by omega))
    (by rw [x2₂]; exact in_off hwS (by omega) (by omega))
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  have hev₃ : AArch64.eval (.zero .x (q 1)) s₃ = some (decide (i % nk + 1 = nk)) := by
    simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, q1₃, x1₂, x3₂]
    rw [next_beq hmod (by omega)]
  -- `x1 := (i + 1) mod Nk`.
  refine WP.seq (WP.mono (Q := fun (s₄ : State) =>
      s₄.gpr .x1 = BitVec.ofNat 64 ((i + 1) % nk) ∧
      (∀ r, r ≠ .x1 → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr) ?_
    fun s₄ ⟨x1₄, o₄, m₄, rd₄, wr₄⟩ => ?_)
  · refine WP.ite _ hev₃ (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨s₄, hs₄, x1₄, o₄, m₄, rd₄, wr₄⟩ := movX1_ok s₃
      refine WP.of_runBlock ⟨s₄, hs₄, ?_, o₄, m₄, rd₄, wr₄⟩
      have h1 : (i + 1) % nk = 0 := by
        have : i % nk + 1 = nk := by simpa using hb
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), this, Nat.mod_self]
      rw [x1₄, h1]; rfl
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      have h1 : (i + 1) % nk = i % nk + 1 := by
        have : i % nk + 1 < nk := by simp at hb; omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), Nat.mod_eq_of_lt this]
      rw [x1₃, x1₂, h1, BitVec.ofNat_add]
      rfl
  -- `x4 := x4 − 1`.
  obtain ⟨s₅, hs₅, x4₅, o₅, m₅, rd₅, wr₅⟩ := decX4_ok s₄
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  have g₃ : ∀ r ∈ [Reg.x3, .x5], s₅.gpr r = s.gpr r := fun r hr => by
    rw [o₅ r (by revert hr; revert r; decide), o₄ r (by revert hr; revert r; decide),
      o₃ r (by revert hr; revert r; decide) (by revert hr; revert r; decide)
        (by revert hr; revert r; decide) (by revert hr; revert r; decide)
        (by revert hr; revert r; decide), k₂ r (by revert hr; revert r; decide)]
  have x4₄ : s₄.gpr .x4 = BitVec.ofNat 64 (4 * (nk + 7) - i) := by
    rw [o₄ .x4 (by decide), o₃ .x4 (by decide) (by decide) (by decide) (by decide) (by decide),
      k₂ .x4 (by simp), hi.x4]
  rw [x4₄, ofNat_sub_one (by omega)] at x4₅
  have hev : AArch64.eval (.nonzero .x .x4) s₅ = some (!decide (4 * (nk + 7) - i - 1 = 0)) := by
    simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, x4₅]
    rw [ofNat_bne_zero (by omega)]
  have mem₅ : s₅.mem = storeMem s₂ S nk i := by rw [m₅, m₄, m₃, storeMem, newW, x2₂, x0₂]
  obtain ⟨sched', fr, sv, rc⟩ := store_facts hs hi hm
  rw [← mem₅] at sched' fr sv rc
  have x5₅ : s₅.gpr .x5 = B := (g₃ .x5 (by simp)).trans hi.x5
  have rd : s₅.rd = s₀.rd := by rw [rd₅, rd₄, rd₃, hm.rd, hi.rd]
  have wr : s₅.wr = s₀.wr := by rw [wr₅, wr₄, wr₃, hm.wr, hi.wr]
  by_cases hl : 4 * (nk + 7) - i - 1 = 0
  · refine .inl ⟨hev.trans (by rw [hl]; rfl), x5₅, rd, wr, fun k hk => sched' k (by omega), sv, fr⟩
  · refine .inr ⟨hev.trans (by simp [hl]), ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, x5₅, ?_, rd, wr,
      sched', by rw [Nat.add_sub_cancel]; exact rc, sv, fr⟩⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), x2₃, x2₂, off_step]
    · rw [o₅ _ (by decide), o₄ _ (by decide), x0₃, x0₂, off_step, show i - nk + 1 = i + 1 - nk by omega]
    · exact (g₃ .x3 (by simp)).trans hi.x3
    · rw [o₅ _ (by decide), x1₄]
    · rw [x4₅, Nat.sub_sub]
    · intro t ht
      have := sched' (4 * i + t) (by omega)
      rw [mem₅, storeMem, BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht,
        show (4 * i + t) / 4 = i by omega, show (4 * i + t) % 4 = t by omega] at this
      rw [o₅ _ (by decide), o₄ _ (by decide), q0₃, sw64_byte, newW, x0₂, this, Nat.add_sub_cancel]

/-! ## The loop over the words -/

theorem words_ok {s₀ : State} {S B : Addr} {kl : List Byte} {nk : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk nk s) :
    WP isa (.loop wordBody (.nonzero .x .x4)) s (WDone s₀ S B kl nk) := by
  refine WP.loop (M := isa) (fun k s => ∃ i, k = 4 * (nk + 7) - i ∧ WInv s₀ S B kl nk i s)
    (fun k s ⟨i, hk, hi⟩ => WP.mono (word_ok hs hi) fun s' h => ?_) _ s ⟨nk, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, _, by have := hi.hn; omega, i + 1, rfl, d⟩

/-! ## Copying the key -/

theorem st64_byte (m : Mem) (a : Addr) (v : BitVec 64) {t : Nat} (ht : t < 8) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show t < 2 ^ 64 by omega),
    show t < 64 / 8 by omega, ite_true, BitVec.setWidth_eq]

theorem ld64_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 8) :
    (m.readW a 64).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) := by
  rw [← Mem.extractLsb'_read m a (n := 8) ht]
  rfl

theorem writeW64_other {m : Mem} {a x : Addr} (v : BitVec 64) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 8⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply (out_of_disj h (Region.contains_self _ _) (Region.contains_self _ _))

/-- The key's bytes. -/
theorem bytesAt_getD (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (Spec.Aes.bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, hk]

/-- During the copy, after `c` words. -/
structure CInv (s₀ : State) (S B P : Addr) (K c : Nat) (s : State) : Prop where
  hc : 8 * c < K
  x0 : s.gpr .x0 = P + BitVec.ofNat 64 (8 * c)
  x2 : s.gpr .x2 = S + BitVec.ofNat 64 (8 * c)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (K - 8 * c)
  x1 : s.gpr .x1 = BitVec.ofNat 64 K
  x5 : s.gpr .x5 = B
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  copied : ∀ k < 8 * c, s.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k)
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- After the copy: the last 8 bytes of the key are in `q 0`. -/
structure CDone (s₀ : State) (S B P : Addr) (K : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = S + BitVec.ofNat 64 K
  x1 : s.gpr .x1 = BitVec.ofNat 64 K
  x5 : s.gpr .x5 = B
  last : ∀ t < 8, (s.gpr (q 0)).extractLsb' (8 * t) 8 = s₀.mem (P + BitVec.ofNat 64 (K - 8 + t))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  copied : ∀ k < K, s.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k)
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- The setting of the copy: the key (`K` bytes at `P`) is outside what is written. -/
structure CSetup (s₀ : State) (S B P : Addr) (K : Nat) : Prop where
  hK : K = 16 ∨ K = 24 ∨ K = 32
  key : (⟨P, K⟩ : Region) ∈ s₀.rd
  sch : (⟨S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨B, 512⟩ : Region) ∈ s₀.wr
  dS : Region.Disjoint ⟨P, K⟩ ⟨S, 240⟩
  dB : Region.Disjoint ⟨P, K⟩ ⟨B, 512⟩
  sep : Region.Disjoint ⟨S, 240⟩ ⟨B, 512⟩

theorem copy_ok {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K) {c : Nat} {s : State}
    (hi : CInv s₀ S B P K c s) :
    WP isa (.block copyBody) s fun s' =>
      (AArch64.eval (.nonzero .x .x4) s' = some false ∧ CDone s₀ S B P K s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧ CInv s₀ S B P K (c + 1) s') := by
  have hK := hs.hK
  have hc := hi.hc
  have hc8 : 8 * c + 8 ≤ K := by rcases hK with rfl | rfl | rfl <;> omega
  obtain ⟨s', hs', m', q0', x0', x2', x4', o', rd', wr'⟩ := copyBody_ok (s := s)
    (by rw [hi.x0]; exact in_off (List.mem_append_left _ (by rw [hi.rd]; exact hs.key)) hc8 (by omega))
    (by rw [hi.x2]; exact in_off (by rw [hi.wr]; exact hs.sch) (by omega) (by omega))
  refine WP.of_runBlock ⟨s', hs', ?_⟩
  rw [hi.x4, ofNat_sub_eight (show 8 ≤ K - 8 * c by omega)] at x4'
  have hev : AArch64.eval (.nonzero .x .x4) s' = some (!decide (K - 8 * c - 8 = 0)) := by
    simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, x4']
    rw [ofNat_bne_zero (by omega)]
  rw [hi.x0, hi.x2] at m'
  rw [hi.x0] at q0'
  have hkey : ∀ t < 8, s.mem (P + BitVec.ofNat 64 (8 * c + t)) = s₀.mem (P + BitVec.ofNat 64 (8 * c + t)) :=
    fun t ht => hi.frame.bytes (R := ⟨P, K⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.dS
      · exact hs.dB) (by simp only; omega) (show 8 * c + t < K by omega)
  have copied : ∀ k < 8 * (c + 1), s'.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k) := by
    intro k hk
    rw [m']
    by_cases hkc : k < 8 * c
    · rw [writeW64_other _ (Offset.disjoint S (Or.inl (by omega)) (by omega) (by omega)), hi.copied k hkc]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 8 ∧ k = 8 * c + t := ⟨k - 8 * c, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st64_byte _ _ _ ht, ld64_byte _ _ ht, BitVec.add_assoc,
        ← BitVec.ofNat_add]
      exact hkey t ht
  have fr : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s'.mem := by
    rw [m']
    exact Frame.writeW hi.frame (r := ⟨S, 240⟩) (by simp) _ (c_off S (by omega) (by omega))
  have sv : Saved s₀ B s'.mem := by
    rw [m']
    refine saved_frame hi.saved (Frame.writeW (Frame.refl [⟨S + BitVec.ofNat 64 (8 * c), 8⟩] _) (by simp) _
      (Region.contains_self _ _)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have d1 : Region.Disjoint ⟨S, 240⟩ ⟨B + BitVec.ofNat 64 384, 88⟩ :=
      hs.sep.sub_right (Offset.sub_base B (d := 384) (n := 88) (k := 512) (by decide))
    exact (d1.sub_left (Offset.sub_base S (d := 8 * c) (n := 8) (k := 240) (by omega))).symm
  have x1' : s'.gpr .x1 = BitVec.ofNat 64 K := by
    rw [o' _ (by decide) (by decide) (by decide) (by decide), hi.x1]
  have x5' : s'.gpr .x5 = B := by rw [o' _ (by decide) (by decide) (by decide) (by decide), hi.x5]
  by_cases hl : K - 8 * c - 8 = 0
  · refine .inl ⟨hev.trans (by rw [hl]; rfl), ?_, x1', x5', fun t ht => ?_, rd'.trans hi.rd,
      wr'.trans hi.wr, fun k hk => copied k (by omega), sv, fr⟩
    · rw [x2', hi.x2, off_step8, show 8 * (c + 1) = K by omega]
    · rw [q0', ld64_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, hkey t ht,
        show K - 8 + t = 8 * c + t by omega]
  · refine .inr ⟨hev.trans (by simp [hl]), ⟨by omega, ?_, ?_, ?_, x1', x5', rd'.trans hi.rd,
      wr'.trans hi.wr, copied, sv, fr⟩⟩
    · rw [x0', hi.x0, off_step8]
    · rw [x2', hi.x2, off_step8]
    · rw [x4', show K - 8 * (c + 1) = K - 8 * c - 8 by omega]

theorem copyLoop_ok {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K) {s : State}
    (hi : CInv s₀ S B P K 0 s) :
    WP isa (.loop (.block copyBody) (.nonzero .x .x4)) s (CDone s₀ S B P K) := by
  refine WP.loop (M := isa) (fun k s => ∃ c, k = K - 8 * c ∧ CInv s₀ S B P K c s)
    (fun k s ⟨c, hk, hc⟩ => WP.mono (copy_ok hs hc) fun s' h => ?_) _ s ⟨0, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, _, by have := hc.hc; omega, c + 1, rfl, d⟩

/-! ## Setting up the word loop -/

theorem kw_getD_key (kl : List Byte) {nk k : Nat} (hk : k < 4 * nk) :
    (kw kl nk (k / 4)).getD (k % 4) 0 = kl.getD k 0 := by
  rw [kw_key kl (show k / 4 < nk by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp [show k % 4 < 4 by omega, Nat.div_add_mod]

theorem x3_setup {K : Nat} (hK : K = 16 ∨ K = 24 ∨ K = 32) :
    BitVec.ofNat 64 K >>> 2 = BitVec.ofNat 64 (K / 4) := by
  rcases hK with rfl | rfl | rfl <;> decide

theorem x4_setup {K : Nat} (hK : K = 16 ∨ K = 24 ∨ K = 32) :
    (BitVec.ofNat 64 K >>> 2) + (BitVec.ofNat 64 K >>> 2) + (BitVec.ofNat 64 K >>> 2) + 28 =
      BitVec.ofNat 64 (4 * (K / 4 + 7) - K / 4) := by
  rcases hK with rfl | rfl | rfl <;> decide

/-! ## The prologue -/

theorem movR_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [movR d r] s = some s' ∧ s'.gpr d = s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by rw [movR, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [State.write, State.read], fun r h => by simp [State.write, h], rfl, rfl, rfl⟩

theorem sreg_ne_x5 : ∀ i < 10, sreg i ≠ .x5 := by decide

theorem prologue_wp {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K)
    (hS : s₀.gpr .x2 = S) (hB : s₀.gpr .x3 = B) (hP : s₀.gpr .x0 = P)
    (hKr : s₀.gpr .x1 = BitVec.ofNat 64 K) :
    WP isa (.block ([movR sb .x3] ++ saveRegs ++ [movR .x4 .x1])) s₀ (CInv s₀ S B P K 0) := by
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  obtain ⟨s₁, h₁, x5₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .x3
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (s := s₁) (b := B) (n := 512)
    (by rw [wr₁]; exact hs.scr) (x5₁.trans hB) (by decide)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain ⟨s₃, h₃, x4₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .x4 .x1
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  have g : ∀ r, r ≠ .x4 → r ≠ .x5 → s₃.gpr r = s₀.gpr r := fun r h4 h5 => by
    rw [o₃ r h4, g₂, o₁ r h5]
  have hK := hs.hK
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
    fun k hk => by omega, ?_, ?_⟩
  · rw [g _ (by decide) (by decide), hP]; simp
  · rw [g _ (by decide) (by decide), hS]; simp
  · rw [x4₃, g₂, o₁ _ (by decide), hKr]; simp
  · rw [g _ (by decide) (by decide), hKr]
  · rw [o₃ _ (by decide), g₂]; exact x5₁.trans hB
  · intro i hi
    rw [m₃, sv₂ i hi, o₁ _ (sreg_ne_x5 i hi)]
  · rw [m₃, ← m₁]
    exact f₂.sub fun r hr => ⟨⟨B, 512⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩

/-! ## The whole function -/

theorem ek_correct {s₀ : State} (hp : Proof.Aes.expandKeyAArch64.pre s₀) :
    WP isa Impl.Aes.AArch64.expandKey s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ Proof.Aes.expandKeyAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, hK⟩ := hp
  have hs : CSetup s₀ (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x0) (s₀.gpr .x1).toNat :=
    ⟨hK, by rw [hrd]; simp, by rw [hwr]; simp, by rw [hwr]; simp, dKS, dKB, dSB⟩
  generalize hS : s₀.gpr .x2 = S at hs dSB
  generalize hB : s₀.gpr .x3 = B at hs dSB
  generalize hP : s₀.gpr .x0 = P at hs dKS dKB
  generalize hK' : (s₀.gpr .x1).toNat = K at hs hK dKS dKB
  have hKr : s₀.gpr .x1 = BitVec.ofNat 64 K := by rw [← hK']; simp
  have hK4 : K = 4 * (K / 4) := by omega
  unfold Impl.Aes.AArch64.expandKey
  refine WP.seq (WP.mono (prologue_wp hs hS hB hP hKr) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (copyLoop_ok hs h₁) fun s₂ h₂ => ?_)
  refine WP.seq ?_
  obtain ⟨s₃, hs₃, q0₃, x0₃, x3₃, x1₃, x4₃, m₃, o₃, rd₃, wr₃⟩ := wordSetup_ok (s := s₂) (b := B)
    h₂.x5 (in_off (by rw [h₂.wr]; exact hs.scr) (by omega) (by omega))
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  have hlen : (Spec.Aes.bytesAt s₀.mem P K).length = K := by simp [Spec.Aes.bytesAt]
  have ws : WSetup s₀ S B (Spec.Aes.bytesAt s₀.mem P K) (K / 4) :=
    ⟨by omega, by rw [hlen]; exact hK4, hs.sch, hs.scr, dSB⟩
  have d59 : Region.Disjoint ⟨S, 240⟩ ⟨B + BitVec.ofNat 64 (8 * 59), 8⟩ :=
    dSB.sub_right (Offset.sub_base B (by decide))
  have wi : WInv s₀ S B (Spec.Aes.bytesAt s₀.mem P K) (K / 4) (K / 4) s₃ :=
    { hi := Nat.le_refl _
      hn := by omega
      x2 := by
        rw [o₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₂.x2, ← hK4]
      x0 := by rw [x0₃, h₂.x2, h₂.x1, BitVec.add_sub_cancel, Nat.sub_self, Nat.mul_zero]; simp
      x3 := by rw [x3₃, h₂.x1, x3_setup hK]
      x1 := by rw [x1₃, Nat.mod_self]; rfl
      x4 := by rw [x4₃, h₂.x1, x4_setup hK]
      x5 := by
        rw [o₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₂.x5]
      temp := fun t ht => by
        rw [q0₃, lsr32_byte, h₂.last (t + 4) (by omega), ← bytesAt_getD s₀.mem P (show K - 8 + (t + 4) < K by omega),
          ← kw_getD_key _ (show K - 8 + (t + 4) < 4 * (K / 4) by omega),
          show (K - 8 + (t + 4)) / 4 = K / 4 - 1 by omega, show (K - 8 + (t + 4)) % 4 = t by omega]
      rd := rd₃.trans h₂.rd
      wr := wr₃.trans h₂.wr
      sched := fun k hk => by
        rw [m₃, writeW64_other _ (d59.sub_left (Offset.sub_base S (by omega))),
          h₂.copied k (by omega), ← bytesAt_getD s₀.mem P (show k < K by omega),
          kw_getD_key _ (by omega)]
      rc := by
        rw [m₃, Mem.readW_writeW_self64, Nat.div_eq_of_lt (by omega), rcW_zero]
      saved := by
        rw [m₃]
        refine saved_frame h₂.saved (Frame.writeW (Frame.refl [⟨B + BitVec.ofNat 64 (8 * 59), 8⟩] _)
          (by simp) _ (Region.contains_self _ _)) fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint B (Or.inl (by decide)) (by decide) (by decide)
      frame := by
        rw [m₃]
        exact Frame.writeW h₂.frame (r := ⟨B, 512⟩) (by simp) _ (c_off B (by omega) (by omega)) }
  refine WP.seq (WP.mono (words_ok ws wi) fun s₄ h₄ => ?_)
  obtain ⟨s₅, hs₅, rg₅, f₅⟩ := restore_ok (s := s₄) (b := B) (n := 512)
    (by rw [h₄.wr]; exact hs.scr) h₄.x5 (by decide) h₄.saved
  refine WP.of_runBlock ⟨s₅, hs₅, rg₅, ?_⟩
  show Spec.Aes.bytesAt s₅.mem (s₀.gpr .x2) (16 * (Spec.Aes.rounds ((s₀.gpr .x1).toNat / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat)
  rw [hS, hP, hK']
  have lhs : ∀ n, Spec.Aes.bytesAt s₅.mem S n = (List.range n).map fun k => s₅.mem (S + BitVec.ofNat 64 k) :=
    fun _ => rfl
  rw [lhs, Spec.Aes.expandKey, hlen, Spec.Aes.rounds,
    show 16 * (K / 4 + 6 + 1) = 4 * (4 * (K / 4 + 6 + 1)) by omega]
  refine flatten_expandWords ws.len (by omega) _ _ fun k hk => ?_
  exact (f₅.bytes (R := ⟨S, 240⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dSB.sub_right (Region.sub_prefix (by decide))) (by simp) (show k < 240 by omega)).trans
    (h₄.sched k (by omega))

/-- A state satisfying the precondition. -/
def ekSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_correct (s : State) (hs : Proof.Aes.expandKeyAArch64.pre s) :
    ∃ t s', Exec isa Impl.Aes.AArch64.expandKey s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ :=
    WP.gprs (rs := [.x30]) (ek_correct hs) (by decide +kernel) (by decide +kernel)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₃ _ (by simp)

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyAArch64.pre
    Proof.Aes.expandKeyAArch64.pub Impl.Aes.AArch64.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem expandKey_verified :
    Verified AArch64.target Impl.Aes.AArch64.expandKey (Spec.Aes.expandKeyContract AArch64.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Proof.Aes.expandKeyAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Aes.AArch64.ekSatState] using
      Proof.Aes.AArch64.ekSatState)

end VG.Proof.Aes.AArch64
