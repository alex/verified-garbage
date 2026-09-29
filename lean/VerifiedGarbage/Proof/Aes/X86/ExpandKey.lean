import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.ExpandKeyCT
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Aes.Contract

/-!
# The AES key expansion on x86 (32-bit)

Untrusted: everything here is checked by Lean.

`subWordCode` (the word in slot 0, the other slots zero, `ortho`, the S-box,
`ortho`) applies the S-box to every byte of `eax` (`subWord_wp`, from the
bitsliced layers' lemmas); each word of the schedule is then a few scalar
instructions around it (`word_ok`), and the loop over the words keeps the
schedule's bytes so far equal to the specification's (`WInv`). Constant
time is `ExpandKeyCT.lean`.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.Spec.Aes (sbox xtimes subBytes subWord rotWord rcon xorWord)
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_addm wp_sub wp_subi wp_cmp wp_cmpi wp_test
  wp_ldm wp_xorm wp_stm wp_shr wp_ror wp_andi wp_xor sub_beq sub_ofNat toNat_ofNat_lt ofNat_pred
  ofNat_beq_zero)

/-! ## The S-box on every byte -/

/-- The two states that the words hold, as `InRel` relates them. -/
def stOf (Q : Nat → BitVec 32) (b : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (b + 2 * (i.1 / 4))).extractLsb' (8 * (i.1 % 4)) 8

theorem inRel_stOf (Q : Nat → BitVec 32) : InRel Q (stOf Q) := by
  intro b hb i hi j hj
  rw [getD_eq _ hi, stOf, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb']
  simp [hj]

theorem subWordCode_eq : subWordCode = ((([st 0 .eax, movI .eax 0, st 1 .eax, st 2 .eax, st 3 .eax,
    st 4 .eax, st 5 .eax, st 6 .eax, st 7 .eax] : List Instr) ++ ortho) ++ sboxCode) ++ ortho ++
    ([movS .eax 0] : List Instr) := by
  simp only [subWordCode, List.append_assoc]; rfl

/-- `SUBWORD` of `eax`. -/
theorem subWord_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (fit : B.toNat + 512 ≤ 2 ^ 32)
    (hw : reg32 B 512 ∈ s.wr) {P : State → Prop}
    (h : ∀ s', (∀ t < 4, (s'.gpr .eax).extractLsb' (8 * t) 8 = sbox ((s.gpr .eax).extractLsb' (8 * t) 8)) →
      s'.rd = s.rd → s'.wr = s.wr → (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) →
      Frame [reg32 B 256] s.mem s'.mem → P s') :
    WP isa (.block subWordCode) s P := by
  have hin : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 512 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hw fit ho (by decide)
  have hok : ∀ (t : State), t.gpr sb = B → t.wr = s.wr → t.rd = s.rd → Ok linCfg t := fun t hb' hw' hr' =>
    Ok.of_off (r := reg32 B 512) (r' := reg32 B 512) (b := B) (b' := B) (off := 0) (off' := 0)
      (n := 512) (n' := 512) (by rw [hw']; exact hw) rfl fit (Nat.le_refl _)
      (by show t.gpr sb = _; rw [hb']; simp) (by simp [linCfg])
      (by rw [hr', hw']; exact List.mem_append_right _ hw) rfl fit (Nat.le_refl _)
      (by show t.gpr sb = _; rw [hb']; simp) (by simp [linCfg]) (.inr (.inl rfl))
  rw [subWordCode_eq]
  repeat rw [WP.block_append_iff (M := isa)]
  have hm := List.mem_singleton_self (reg32 B 256)
  have c256 : ∀ k < 8, (reg32 B 256).Contains (addr B (4 * k)) (32 / 8) := fun k hk =>
    reg_contains (by omega) (by omega) (by decide)
  refine wp_stm hb (hin _ rfl 0 (by omega)) fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .edi = B := by rw [u₂.other _ (by decide), u₁.gpr]; exact hb
  have w₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  refine wp_stm b₂ (hin _ w₂ 4 (by omega)) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.gpr]; exact b₂) (hin _ (by rw [u₃.wr, w₂]) 8 (by omega)) fun s₄ u₄ => ?_
  refine wp_stm (by rw [u₄.gpr, u₃.gpr]; exact b₂) (hin _ (by rw [u₄.wr, u₃.wr, w₂]) 12 (by omega))
    fun s₅ u₅ => ?_
  refine wp_stm (by rw [u₅.gpr, u₄.gpr, u₃.gpr]; exact b₂) (hin _ (by rw [u₅.wr, u₄.wr, u₃.wr, w₂]) 16
    (by omega)) fun s₆ u₆ => ?_
  refine wp_stm (by rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr]; exact b₂)
    (hin _ (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂]) 20 (by omega)) fun s₇ u₇ => ?_
  refine wp_stm (by rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr]; exact b₂)
    (hin _ (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂]) 24 (by omega)) fun s₈ u₈ => ?_
  refine wp_stm (by rw [u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr]; exact b₂)
    (hin _ (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂]) 28 (by omega)) fun s₉ u₉ =>
    WP.block_nil ?_
  have g₉ : ∀ r, r ≠ .eax → s₉.gpr r = s.gpr r := fun r hr => by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.other r hr, u₁.gpr]
  have b₉ : s₉.gpr sb = B := by rw [g₉ _ (by decide)]; exact hb
  have e₂ : s₂.gpr .eax = 0 := u₂.gpr
  let M := ((((((((s.mem.writeW (addr B 0) (s.gpr .eax)).writeW (addr B 4) (0 : BitVec 32)).writeW
    (addr B 8) (0 : BitVec 32)).writeW (addr B 12) (0 : BitVec 32)).writeW (addr B 16) (0 : BitVec 32)).writeW
    (addr B 20) (0 : BitVec 32)).writeW (addr B 24) (0 : BitVec 32)).writeW (addr B 28) (0 : BitVec 32))
  have m₉ : s₉.mem = M := by
    simp only [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₈.gpr, u₇.gpr,
      u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, e₂, Nat.reduceMul]
    rw [u₁.mem]
  have q₉ : ∀ k < 8, Q s₉ k = if k = 0 then s.gpr .eax else 0 := by
    intro k hk
    simp only [Q, wordAddr, b₉, m₉]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [M, Nat.reduceMul, rd_wr_ne fit, Mem.readW_writeW_self32,
      ↓reduceIte, Nat.reduceEqDiff]
  have f₉ : Frame [reg32 B 256] s.mem s₉.mem := by
    rw [m₉]
    exact (((((((Frame.refl _ _).writeW hm _ (c256 0 (by omega))).writeW hm _ (c256 1 (by omega))).writeW
      hm _ (c256 2 (by omega))).writeW hm _ (c256 3 (by omega))).writeW hm _ (c256 4 (by omega))).writeW hm _
      (c256 5 (by omega))).writeW hm _ (c256 6 (by omega)) |>.writeW hm _ (c256 7 (by omega))
  have rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain ⟨s₁₀, hs₁₀, h₁₀, rd₁₀, wr₁₀, o₁₀, f₁₀⟩ := toBs_ok (hok s₉ b₉ wr₉ rd₉)
  refine WP.of_runBlock ⟨s₁₀, hs₁₀, ?_⟩
  have b₁₀ : s₁₀.gpr sb = B := (o₁₀ sb (by decide)).trans b₉
  obtain ⟨s₁₁, hs₁₁, h₁₁, rd₁₁, wr₁₁, o₁₁, f₁₁⟩ :=
    sbox_ok (hok s₁₀ b₁₀ (wr₁₀.trans wr₉) (rd₁₀.trans rd₉))
  refine WP.of_runBlock ⟨s₁₁, hs₁₁, ?_⟩
  have b₁₁ : s₁₁.gpr sb = B := (o₁₁ sb (by decide)).trans b₁₀
  obtain ⟨s₁₂, hs₁₂, h₁₂, rd₁₂, wr₁₂, o₁₂, f₁₂⟩ :=
    fromBs_ok (hok s₁₁ b₁₁ (wr₁₁.trans (wr₁₀.trans wr₉)) (rd₁₁.trans (rd₁₀.trans rd₉)))
  refine WP.of_runBlock ⟨s₁₂, hs₁₂, ?_⟩
  have b₁₂ : s₁₂.gpr sb = B := (o₁₂ sb (by decide)).trans b₁₁
  have hin' := in_of_bs h₁₂ (bs_subBytes h₁₁ (bs_of_in h₁₀ (inRel_stOf (Q s₉))))
  refine wp_ldm b₁₂ (in_rd (hin _ (wr₁₂.trans (wr₁₁.trans (wr₁₀.trans wr₉))) 0 (by omega)))
    fun s₁₃ u₁₃ => WP.block_nil ?_
  refine h s₁₃ (fun t ht => ?_) (by rw [u₁₃.rd, rd₁₂, rd₁₁, rd₁₀, rd₉])
    (by rw [u₁₃.wr, wr₁₂, wr₁₁, wr₁₀, wr₉]) (fun r hr => ?_) ?_
  · refine byte_ext fun j hj => ?_
    have := hin' 0 (by omega) t (by omega) j hj
    rw [show 0 + 2 * (t / 4) = 0 by omega, show t % 4 = t by omega] at this
    have e₁₃ : s₁₃.gpr .eax = Q s₁₂ 0 := by rw [u₁₃.gpr]; simp only [Q, wordAddr, b₁₂]
    rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, e₁₃, this, getD_eq _ (by omega)]
    simp only [subBytes, Vector.getElem_map, stOf, Vector.getElem_ofFn]
    rw [show 0 + 2 * (t / 4) = 0 by omega, show t % 4 = t by omega, q₉ 0 (by omega), ite_eq_left rfl]
  · have hne : r ≠ .eax := fun h => hr (h ▸ by decide)
    rw [u₁₃.other r hne, o₁₂ r hr, o₁₁ r hr, o₁₀ r hr, g₉ r hne]
  · rw [u₁₃.mem]
    have e₁ : slotRegion linCfg s₉ = reg32 B 256 := by simp only [slotRegion, linCfg, b₉]
    have e₂ : slotRegion linCfg s₁₀ = reg32 B 256 := by simp only [slotRegion, linCfg, b₁₀]
    have e₃ : slotRegion linCfg s₁₁ = reg32 B 256 := by simp only [slotRegion, linCfg, b₁₁]
    rw [e₁] at f₁₀; rw [e₂] at f₁₁; rw [e₃] at f₁₂
    exact ((f₉.trans f₁₀).trans f₁₁).trans f₁₂

/-! ## Bytes -/

/-- The round constant slot's value: `x^k`. -/
def rcW (k : Nat) : BitVec 32 := (Nat.repeat xtimes k (1 : Byte)).setWidth 32

/-- The round constant after one more round, as `rotTail` computes it. -/
def rcNext (v : BitVec 32) : BitVec 32 := ((v + v) ^^^ ((0 - (v >>> 7)) &&& 0x1b)) &&& 0xff

theorem rcNext_rcW : ∀ k < 10, rcNext (rcW k) = rcW (k + 1) := by decide

theorem rcW_byte (k : Nat) {t : Nat} (ht : t < 4) :
    (rcW k).extractLsb' (8 * t) 8 = if t = 0 then Nat.repeat xtimes k 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [rcW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  split
  · subst_vars; simp [hj]; intro; omega
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp

theorem xor_byte (x y : BitVec 32) (t : Nat) :
    (x ^^^ y).extractLsb' (8 * t) 8 = x.extractLsb' (8 * t) 8 ^^^ y.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor]
  cases decide (j < 8) <;> simp

theorem rot_byte (x : BitVec 32) {t : Nat} (ht : t < 4) :
    (x.rotateRight 8).extractLsb' (8 * t) 8 = x.extractLsb' (8 * ((t + 1) % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, hj, decide_true, Bool.true_and]
  by_cases h : t < 3
  · rw [ite_eq_left ((show 8 * t + j < 32 - 8 % 32 by omega)),
      show 8 % 32 + (8 * t + j) = 8 * ((t + 1) % 4) + j by omega]
  · rw [ite_eq_right ((show ¬ 8 * t + j < 32 - 8 % 32 by omega)),
      show 8 * t + j - (32 - 8 % 32) = 8 * ((t + 1) % 4) + j by omega]
    simp; omega

/-! ## `ROTWORD`, `Rcon` and the next round constant -/

theorem rotTail_eq : rotTail = ([rorI .eax 8, .alu .xor .eax (.mem ⟨.edi, rcOff⟩),
    .mov .ebx (.mem ⟨.edi, rcOff⟩), movR .ecx .ebx, shrI .ecx 7, movI .edx 0, subR .edx .ecx,
    andI .edx 0x1b, addR .ebx .ebx, xorR .ebx .edx, andI .ebx 0xff, .store ⟨.edi, rcOff⟩ .ebx] : List Instr) :=
  rfl

theorem rotTail_wp {s : State} {B : BitVec 32} (hb : s.gpr .edi = B) (fit : B.toNat + 512 ≤ 2 ^ 32)
    (hw : reg32 B 512 ∈ s.wr) {P : State → Prop}
    (h : ∀ s', s'.gpr .eax = (s.gpr .eax).rotateRight 8 ^^^ s.mem.readW (addr B rcOff) 32 →
      s'.mem = s.mem.writeW (addr B rcOff) (rcNext (s.mem.readW (addr B rcOff) 32)) →
      (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block rotTail) s P := by
  have hin : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → InRegions (t.rd ++ t.wr) (addr B rcOff) 4 :=
    fun t h1 h2 => by rw [h1, h2]; exact in_rd (in_reg hw fit (by simp only [rcOff]; omega) (by decide))
  rw [rotTail_eq]
  refine wp_ror (by decide) fun s₁ u₁ => ?_
  refine wp_xorm (by rw [u₁.other _ (by decide)]; exact hb) (hin _ u₁.rd u₁.wr) fun s₂ u₂ => ?_
  refine wp_ldm (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (hin _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])) fun s₃ u₃ => ?_
  refine wp_mov fun s₄ u₄ => wp_shr (by decide) fun s₅ u₅ _ => wp_movi fun s₆ u₆ => ?_
  refine wp_sub fun s₇ u₇ _ => wp_andi fun s₈ u₈ => wp_add fun s₉ u₉ _ => wp_xor fun s₁₀ u₁₀ => ?_
  refine wp_andi fun s₁₁ u₁₁ => ?_
  have hb₁₁ : s₁₁.gpr .edi = B := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb
  have rd₁₁ : s₁₁.rd = s.rd := by
    rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₁₁ : s₁₁.wr = s.wr := by
    rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have m₁₁ : s₁₁.mem = s.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_stm hb₁₁ (by rw [wr₁₁]; exact in_reg hw fit (by simp only [rcOff]; omega) (by decide))
    fun s₁₂ u₁₂ => WP.block_nil ?_
  have ebx₃ : s₃.gpr .ebx = s.mem.readW (addr B rcOff) 32 := by rw [u₃.gpr, u₂.mem, u₁.mem]
  have ecx₅ : s₅.gpr .ecx = s₃.gpr .ebx >>> 7 := by rw [u₅.gpr, u₄.gpr]
  have edx₈ : s₈.gpr .edx = (0 - (s₃.gpr .ebx >>> 7)) &&& 0x1b := by
    rw [u₈.gpr, u₇.gpr, u₆.gpr, u₆.other _ (by decide), ecx₅]; rfl
  have ebx₈ : s₈.gpr .ebx = s₃.gpr .ebx := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide)]
  have ebx₁₁ : s₁₁.gpr .ebx = rcNext (s.mem.readW (addr B rcOff) 32) := by
    rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), edx₈, ebx₈, ebx₃]; rfl
  refine h s₁₂ ?_ (by rw [u₁₂.mem, m₁₁, ebx₁₁]) (fun r hr => ?_) (by rw [u₁₂.rd, rd₁₁])
    (by rw [u₁₂.wr, wr₁₁])
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem]
  · have hq : r ≠ .eax ∧ r ≠ .ebx ∧ r ≠ .ecx ∧ r ≠ .edx := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; exact hr (by decide))
    rw [u₁₂.gpr, u₁₁.other _ hq.2.1, u₁₀.other _ hq.2.1, u₉.other _ hq.2.1, u₈.other _ hq.2.2.2,
      u₇.other _ hq.2.2.2, u₆.other _ hq.2.2.2, u₅.other _ hq.2.2.1, u₄.other _ hq.2.2.1,
      u₃.other _ hq.2.1, u₂.other _ hq.1, u₁.other _ hq.1]

/-! ## One word -/

theorem div_pred_zero {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hi : nk ≤ i) (h : i % nk = 0) :
    (i - 1) / nk + 1 = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem div_pred_ne {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (h : i % nk ≠ 0) :
    (i - 1) / nk = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem rot_lt {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hn : i < 4 * (nk + 7)) (h : i % nk = 0) :
    (i - 1) / nk < 10 := by
  rcases h3 with rfl | rfl | rfl <;> omega

/-- What the key expansion writes after the prologue: the schedule, the
S-box's slots, and the round constant and counters. -/
abbrev ekFrame (S B : BitVec 32) : List Region := [reg32 S 240, reg32 B 256, ⟨addr B rcOff, 16⟩]

/-- The setting of the word loop: the schedule at `S`, the scratch buffer
at `B`, and the key `kl` of `nk` words. -/
structure WSetup (s₁ : State) (S B : BitVec 32) (kl : List Byte) (nk : Nat) : Prop where
  nk3 : nk = 4 ∨ nk = 6 ∨ nk = 8
  len : kl.length = 4 * nk
  sch : reg32 S 240 ∈ s₁.wr
  scr : reg32 B 512 ∈ s₁.wr
  fS : S.toNat + 240 ≤ 2 ^ 32
  fB : B.toNat + 512 ≤ 2 ^ 32
  sep : (reg32 S 240).Disjoint (reg32 B 512)

/-- Before word `i`. -/
structure WInv (s₁ : State) (S B : BitVec 32) (kl : List Byte) (nk i : Nat) (s : State) : Prop where
  hi : nk ≤ i
  hn : i < 4 * (nk + 7)
  esi : s.gpr .esi = S + BitVec.ofNat 32 (4 * (i - 1))
  edi : s.gpr .edi = B
  esp : s.gpr .esp = s₁.gpr .esp
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  jm : s.mem.readW (addr B jmOff) 32 = BitVec.ofNat 32 (4 * (i % nk))
  nk4 : s.mem.readW (addr B nkOff) 32 = BitVec.ofNat 32 (4 * nk)
  left : s.mem.readW (addr B leftOff) 32 = BitVec.ofNat 32 (4 * (nk + 7) - i)
  rc : s.mem.readW (addr B rcOff) 32 = rcW ((i - 1) / nk)
  sched : ∀ j < i, ∀ t < 4,
    (s.mem.readW (addr S (4 * j)) 32).extractLsb' (8 * t) 8 = (kw kl nk j).getD t 0
  frame : Frame (ekFrame S B) s₁.mem s.mem

/-- After the last word. -/
structure WDone (s₁ : State) (S B : BitVec 32) (kl : List Byte) (nk : Nat) (s : State) : Prop where
  edi : s.gpr .edi = B
  esp : s.gpr .esp = s₁.gpr .esp
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sched : ∀ j < 4 * (nk + 7), ∀ t < 4,
    (s.mem.readW (addr S (4 * j)) 32).extractLsb' (8 * t) 8 = (kw kl nk j).getD t 0
  frame : Frame (ekFrame S B) s₁.mem s.mem

/-- `temp` computed (in `eax`), from `s`. -/
structure Mid (B : BitVec 32) (kl : List Byte) (nk i : Nat) (s s' : State) : Prop where
  temp : ∀ t < 4, (s'.gpr .eax).extractLsb' (8 * t) 8 = (kTemp nk i (kw kl nk (i - 1))).getD t 0
  keep : ∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [reg32 B 256, ⟨addr B rcOff, 4⟩] s.mem s'.mem
  rc : s'.mem.readW (addr B rcOff) 32 = rcW (i / nk)

theorem back_eq (S : BitVec 32) {i nk : Nat} (h1 : 1 ≤ nk) (h : nk ≤ i) (hi : 4 * i < 2 ^ 32) :
    S + BitVec.ofNat 32 (4 * (i - 1)) + 4 - BitVec.ofNat 32 (4 * nk) = S + BitVec.ofNat 32 (4 * (i - nk)) := by
  bv_omega

theorem add_four (x : BitVec 32) (a : Nat) : x + BitVec.ofNat 32 a + 4 = x + BitVec.ofNat 32 (a + 4) := by
  rw [BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]

theorem ofNat_add_four (a : Nat) : BitVec.ofNat 32 a + 4 = BitVec.ofNat 32 (a + 4) := by
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]

section
variable {s₁ : State} {S B : BitVec 32} {kl : List Byte} {nk : Nat} (hs : WSetup s₁ S B kl nk)
include hs

theorem WSetup.rcIn {s : State} (hw : s.wr = s₁.wr) {o : Nat} (ho : o + 4 ≤ 512) :
    InRegions (s.rd ++ s.wr) (addr B o) 4 := by
  rw [hw]; exact in_rd (in_reg hs.scr hs.fB ho (by decide))

/-- The rest of the scratch buffer's words are outside what `subWordCode` writes. -/
theorem WSetup.slot_disj {o : Nat} (h1 : 256 ≤ o) (h2 : o + 4 ≤ 512) :
    ∀ r ∈ [reg32 B 256], Region.Disjoint ⟨addr B o, 4⟩ r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
  rw [← addr_zero]; exact part_disj hs.fB h2 (by omega) (.inr (by omega))

/-- `temp` from `w[i − 1]`. -/
theorem temp_wp {i : Nat} {s : State} (hi : WInv s₁ S B kl nk i s) :
    WP isa (.block [.mov .eax (.mem (at_ .esi 0)), .mov .ecx (.mem (at_ .edi jmOff)),
        .alu .test .ecx (.reg .ecx)]) s fun s' =>
      WP isa (.ite .e (.block rotWordStep)
        (.seq (.block [.alu .cmp .ecx (.imm 16)])
          (.ite .e (.seq (.block [.mov .ecx (.mem (at_ .edi nkOff)), .alu .cmp .ecx (.imm 32)])
              (.ite .e (.block subWordCode) (.block [])))
            (.block [])))) s' (Mid B kl nk i s) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have hmod := Nat.mod_lt i hnk
  have fB := hs.fB
  have fS := hs.fS
  have hlen := kw_length hs.len hnk (i - 1)
  refine wp_ldm hi.esi (by
      rw [addr_add, hi.wr]; exact in_rd (in_reg hs.sch fS (by omega) (by decide))) fun s₁' u₁ => ?_
  refine wp_ldm (by rw [u₁.other _ (by decide)]; exact hi.edi) (hs.rcIn (by rw [u₁.wr, hi.wr])
    (by simp only [jmOff]; omega)) fun s₂ u₂ => wp_test fun s₃ u₃ z₃ => WP.block_nil ?_
  have ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (4 * (i % nk)) := by rw [u₂.gpr, u₁.mem, hi.jm]
  rw [ecx₂, BitVec.and_self, ofNat_beq_zero (by omega)] at z₃
  have g₃ : ∀ r, r ≠ .eax → r ≠ .ecx → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.gpr, u₂.other r h2, u₁.other r h1]
  have eax₃ : ∀ t < 4, (s₃.gpr .eax).extractLsb' (8 * t) 8 = (kw kl nk (i - 1)).getD t 0 := by
    intro t ht
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, addr_add, Nat.add_zero, hi.sched _ (by omega) t ht]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have edi₃ : s₃.gpr .edi = B := (g₃ _ (by decide) (by decide)).trans hi.edi
  have hwB : reg32 B 512 ∈ s₃.wr := by rw [wr₃, hi.wr]; exact hs.scr
  have keep₃ : ∀ r, r ∉ tmpRegs → s₃.gpr r = s.gpr r := fun r hr =>
    g₃ r (fun h => hr (h ▸ by decide)) (fun h => hr (h ▸ by decide))
  -- No transformation.
  have mid_of : ∀ s', s'.gpr .eax = s₃.gpr .eax → (∀ r, r ∉ tmpRegs → s'.gpr r = s₃.gpr r) →
      s'.mem = s.mem → s'.rd = s₃.rd → s'.wr = s₃.wr → i % nk ≠ 0 →
      kTemp nk i (kw kl nk (i - 1)) = kw kl nk (i - 1) → Mid B kl nk i s s' := by
    intro s' hrax hk hm hrd hwr hne ht
    refine ⟨fun t htt => by rw [hrax, eax₃ t htt, ht], fun r hr => (hk r hr).trans (keep₃ r hr),
      hrd.trans rd₃, hwr.trans wr₃, by rw [hm]; exact Frame.refl _ _, ?_⟩
    rw [hm, hi.rc, div_pred_ne h3 hne]
  refine WP.ite (decide (i % nk = 0)) (by simp only [X86.eval, z₃]; simp) (fun hb => ?_) (fun hb => ?_)
  · -- `SUBWORD(ROTWORD(temp)) ⊕ Rcon`.
    have h0 : i % nk = 0 := by simpa using hb
    rw [rotWordStep, WP.block_append_iff (M := isa)]
    refine subWord_wp edi₃ fB hwB fun s₄ h₄ rd₄ wr₄ o₄ f₄ => ?_
    have edi₄ : s₄.gpr .edi = B := (o₄ _ (by decide)).trans edi₃
    refine rotTail_wp edi₄ fB (by rw [wr₄]; exact hwB) fun s₅ eax₅ m₅ o₅ rd₅ wr₅ => ?_
    have rc₄ : s₄.mem.readW (addr B rcOff) 32 = rcW ((i - 1) / nk) := by
      rw [f₄.readW (Region.contains_self _ _) (hs.slot_disj (by simp only [rcOff]; omega)
        (by simp only [rcOff]; omega)) (by decide), m₃, hi.rc]
    refine ⟨fun t ht => ?_, fun r hr => (o₅ r hr).trans ((o₄ r hr).trans (keep₃ r hr)),
      by rw [rd₅, rd₄, rd₃], by rw [wr₅, wr₄, wr₃], ?_, ?_⟩
    · rw [eax₅, xor_byte, rot_byte _ ht, h₄ _ (by omega), eax₃ _ (by omega), rc₄, rcW_byte _ ht]
      simp only [kTemp, h0, ite_true]
      rw [xorWord_getD (by simp [subWord, rotWord_length hlen]) (by rfl) ht,
        subWord_getD (by rw [rotWord_length hlen]; exact ht), rotWord_getD hlen ht, rcon_getD _ ht,
        ← div_pred_zero h3 hi1 h0, Nat.add_sub_cancel]
    · rw [m₅, ← m₃]
      refine Frame.writeW (r := ⟨addr B rcOff, 4⟩) (f₄.mono (by simp)) (by simp) _ (Region.contains_self _ _)
    · rw [m₅, Mem.readW_writeW_self32, rc₄, rcNext_rcW _ (rot_lt h3 hn h0), div_pred_zero h3 hi1 h0]
  · have h0 : i % nk ≠ 0 := by simpa using hb
    refine WP.seq ?_
    refine wp_cmpi fun s₄ u₄ _ z₄ => WP.block_nil ?_
    rw [u₃.gpr, ecx₂, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, sub_beq (by omega) (by omega)]
      at z₄
    refine WP.ite (decide (4 * (i % nk) = 16)) (by simp only [X86.eval, z₄]) (fun hb₄ => ?_) (fun hb₄ => ?_)
    · have h4 : i % nk = 4 := by simp at hb₄; omega
      refine WP.seq ?_
      refine wp_ldm (by rw [u₄.gpr]; exact edi₃) (hs.rcIn (by rw [u₄.wr, wr₃, hi.wr])
        (by simp only [nkOff]; omega)) fun s₅ u₅ => wp_cmpi fun s₆ u₆ _ z₆ => WP.block_nil ?_
      rw [u₅.gpr, u₄.mem, m₃, hi.nk4, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
        sub_beq (by omega) (by omega)] at z₆
      have g₆ : ∀ r, r ≠ .ecx → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.gpr, u₅.other r h, u₄.gpr]
      have m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
      have rd₆ : s₆.rd = s₃.rd := by rw [u₆.rd, u₅.rd, u₄.rd]
      have wr₆ : s₆.wr = s₃.wr := by rw [u₆.wr, u₅.wr, u₄.wr]
      refine WP.ite (decide (4 * nk = 32)) (by simp only [X86.eval, z₆]) (fun hb₆ => ?_) (fun hb₆ => ?_)
      · -- `SUBWORD(temp)`.
        have h8 : nk = 8 := by simp at hb₆; omega
        refine subWord_wp (by rw [g₆ _ (by decide)]; exact edi₃) fB (by rw [wr₆]; exact hwB)
          fun s₇ h₇ rd₇ wr₇ o₇ f₇ => ?_
        refine ⟨fun t ht => ?_, fun r hr => ?_, by rw [rd₇, rd₆, rd₃], by rw [wr₇, wr₆, wr₃], ?_, ?_⟩
        · rw [h₇ _ ht, g₆ _ (by decide), eax₃ _ ht, kTemp, ite_eq_right h0,
            ite_eq_left (show nk > 6 ∧ i % nk = 4 by omega), subWord_getD (by rw [hlen]; exact ht)]
        · rw [o₇ r hr, g₆ r (fun h => hr (h ▸ by decide)), keep₃ r hr]
        · rw [m₆, m₃] at f₇; exact f₇.mono (by simp)
        · rw [f₇.readW (Region.contains_self _ _) (hs.slot_disj (by simp only [rcOff]; omega)
            (by simp only [rcOff]; omega)) (by decide), m₆, m₃, hi.rc, div_pred_ne h3 h0]
      · have h8 : nk ≠ 8 := by simp at hb₆; omega
        refine WP.block_nil (mid_of s₆ (g₆ _ (by decide)) (fun r hr => g₆ r (fun h => hr (h ▸ by decide)))
          (by rw [m₆, m₃]) rd₆ wr₆ h0 ?_)
        rw [kTemp, ite_eq_right h0, ite_eq_right (show ¬ (nk > 6 ∧ i % nk = 4) by omega)]
    · have h4 : i % nk ≠ 4 := by simp at hb₄; omega
      refine WP.block_nil (mid_of s₄ (by rw [u₄.gpr]) (fun r _ => by rw [u₄.gpr]) (by rw [u₄.mem, m₃])
        u₄.rd u₄.wr h0 ?_)
      rw [kTemp, ite_eq_right h0, ite_eq_right (show ¬ (nk > 6 ∧ i % nk = 4) by omega)]


theorem WSetup.frame_disj {o : Nat} (h1 : rcOff + 4 ≤ o) (h2 : o + 4 ≤ 512) :
    ∀ r ∈ [reg32 B 256, ⟨addr B rcOff, 4⟩], Region.Disjoint ⟨addr B o, 4⟩ r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.slot_disj (by simp only [rcOff] at h1; omega) h2 _ (List.mem_singleton_self _)
  · exact part_disj hs.fB h2 (by simp only [rcOff]; omega) (.inr h1)

theorem WSetup.sched_disj {o : Nat} (h : o + 4 ≤ 240) :
    ∀ r ∈ [reg32 B 256, ⟨addr B rcOff, 4⟩], Region.Disjoint ⟨addr S o, 4⟩ r := fun r hr => by
  have d : Region.Disjoint ⟨addr S o, 4⟩ (reg32 B 512) := hs.sep.sub_left (part_sub_reg hs.fS h)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact d.sub_right (Region.sub_prefix (by omega))
  · exact d.sub_right (part_sub_reg hs.fB (by simp only [rcOff]; omega))

/-- A word of the schedule, after a write to the scratch buffer. -/
theorem WSetup.rdS {m : Mem} {v : BitVec 32} {o e : Nat} (ho : o + 4 ≤ 240) (he : e + 4 ≤ 512) :
    (m.writeW (addr B e) v).readW (addr S o) 32 = m.readW (addr S o) 32 :=
  rd_wr_other hs.sep (reg_contains hs.fS ho (by decide)) (reg_contains hs.fB he (by decide))

/-- A word of the scratch buffer, after a write to the schedule. -/
theorem WSetup.rdB {m : Mem} {v : BitVec 32} {o e : Nat} (ho : o + 4 ≤ 512) (he : e + 4 ≤ 240) :
    (m.writeW (addr S e) v).readW (addr B o) 32 = m.readW (addr B o) 32 :=
  rd_wr_other hs.sep.symm (reg_contains hs.fB ho (by decide)) (reg_contains hs.fS he (by decide))

/-- `w[i] := w[i − Nk] ⊕ temp`, and the counters. -/
theorem store_wp {i : Nat} {s s₂ : State} (hi : WInv s₁ S B kl nk i s) (hm : Mid B kl nk i s s₂) :
    WP isa wordStore s₂ fun s' => (s'.zf = some false ∧ WInv s₁ S B kl nk (i + 1) s') ∨
      (s'.zf = some true ∧ WDone s₁ S B kl nk s') := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have hmod := Nat.mod_lt i hnk
  have fB := hs.fB
  have fS := hs.fS
  have k₂ : ∀ r, r ∉ tmpRegs → s₂.gpr r = s.gpr r := hm.keep
  have esi₂ : s₂.gpr .esi = S + BitVec.ofNat 32 (4 * (i - 1)) := (k₂ _ (by decide)).trans hi.esi
  have edi₂ : s₂.gpr .edi = B := (k₂ _ (by decide)).trans hi.edi
  have wr₂ : s₂.wr = s₁.wr := hm.wr.trans hi.wr
  have slot₂ : ∀ o, rcOff + 4 ≤ o → o + 4 ≤ 512 → s₂.mem.readW (addr B o) 32 = s.mem.readW (addr B o) 32 :=
    fun o h1 h2 => hm.frame.readW (Region.contains_self _ _) (hs.frame_disj h1 h2) (by decide)
  have sch₂ : ∀ j, 4 * j + 4 ≤ 240 → s₂.mem.readW (addr S (4 * j)) 32 = s.mem.readW (addr S (4 * j)) 32 :=
    fun j h => hm.frame.readW (Region.contains_self _ _) (hs.sched_disj h) (by decide)
  have inB : ∀ (t : State), t.wr = s₁.wr → ∀ o, o + 4 ≤ 512 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hs.scr fB ho (by decide)
  have inS : ∀ (t : State), t.wr = s₁.wr → ∀ o, o + 4 ≤ 240 → InRegions t.wr (addr S o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hs.sch fS ho (by decide)
  unfold wordStore
  refine WP.seq ?_
  refine wp_ldm edi₂ (hs.rcIn wr₂ (by simp only [nkOff]; omega)) fun s₃ u₃ => ?_
  refine wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_sub fun s₆ u₆ _ => ?_
  have ebx₆ : s₆.gpr .ebx = S + BitVec.ofNat 32 (4 * (i - nk)) := by
    rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₄.other _ (by decide), u₃.gpr,
      u₃.other _ (by decide), esi₂, slot₂ _ (by decide) (by decide), hi.nk4, back_eq S hnk hi1 (by omega)]
  have wr₆ : s₆.wr = s₁.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂]
  refine wp_xorm ebx₆ (by rw [addr_add]; exact in_rd (inS _ wr₆ _ (by omega))) fun s₇ u₇ => ?_
  have edi₇ : s₇.gpr .edi = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), edi₂]
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have wr₇ : s₇.wr = s₁.wr := by rw [u₇.wr, wr₆]
  refine wp_ldm edi₇ (hs.rcIn wr₇ (by simp only [jmOff]; omega)) fun s₈ u₈ => ?_
  refine wp_ldm (by rw [u₈.other _ (by decide)]; exact edi₇) (hs.rcIn (by rw [u₈.wr, wr₇])
    (by simp only [leftOff]; omega)) fun s₉ u₉ => ?_
  refine wp_ldm (by rw [u₉.other _ (by decide), u₈.other _ (by decide)]; exact edi₇)
    (hs.rcIn (by rw [u₉.wr, u₈.wr, wr₇]) (by simp only [nkOff]; omega)) fun s₁₀ u₁₀ => ?_
  have esi₁₀ : s₁₀.gpr .esi = S + BitVec.ofNat 32 (4 * (i - 1)) := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esi₂]
  have wr₁₀ : s₁₀.wr = s₁.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  refine wp_stm esi₁₀ (by rw [addr_add]; exact inS _ wr₁₀ _ (by omega)) fun s₁₁ u₁₁ => ?_
  refine wp_addi fun s₁₂ u₁₂ => wp_addi fun s₁₃ u₁₃ => wp_cmp fun s₁₄ u₁₄ _ z₁₄ => WP.block_nil ?_
  -- The registers.
  have m₁₀ : s₁₀.mem = s₂.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, m₇]
  have ecx₁₃ : s₁₃.gpr .ecx = BitVec.ofNat 32 (4 * (i % nk) + 4) := by
    rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.gpr, m₇, slot₂ _ (by decide) (by decide), hi.jm, ofNat_add_four]
  have ebp₁₃ : s₁₃.gpr .ebp = BitVec.ofNat 32 (4 * nk) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.mem, u₈.mem, m₇,
      slot₂ _ (by decide) (by decide), hi.nk4]
  have edx₁₃ : s₁₃.gpr .edx = BitVec.ofNat 32 (4 * (nk + 7) - i) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr,
      u₈.mem, m₇, slot₂ _ (by decide) (by decide), hi.left]
  have esi₁₃ : s₁₃.gpr .esi = S + BitVec.ofNat 32 (4 * (i + 1 - 1)) := by
    rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.gpr, esi₁₀, add_four]
    congr 2; omega
  rw [ecx₁₃, ebp₁₃, sub_beq (by omega) (by omega)] at z₁₄
  have edi₁₄ : s₁₄.gpr .edi = B := by
    rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), edi₇]
  have wr₁₄ : s₁₄.wr = s₁.wr := by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  have rd₁₄ : s₁₄.rd = s₁.rd := by
    rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, hm.rd, hi.rd]
  -- The new word.
  let v := s₂.gpr .eax ^^^ s₂.mem.readW (addr S (4 * (i - nk))) 32
  have m₁₄ : s₁₄.mem = s₂.mem.writeW (addr S (4 * i)) v := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, addr_add, show 4 * (i - 1) + 4 = 4 * i by omega, m₁₀,
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem,
      u₄.mem, u₃.mem, addr_add, Nat.add_zero, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]
  have hv : ∀ t < 4, v.extractLsb' (8 * t) 8 = (kw kl nk i).getD t 0 := by
    intro t ht
    rw [xor_byte, hm.temp t ht, sch₂ _ (by omega), hi.sched _ (by omega) t ht, kw_step kl hnk hi1,
      xorWord_getD (kw_length hs.len hnk _) (kTemp_length (kw_length hs.len hnk _)) ht, BitVec.xor_comm]
  have g₁₄ : ∀ r ∈ [Reg.esp], s₁₄.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ _ (by decide)]
  -- `4 ((i + 1) mod Nk)`, and the rest.
  have hq : ∀ s₁₅ : State, s₁₅.gpr .ecx = BitVec.ofNat 32 (4 * ((i + 1) % nk)) →
      (∀ r, r ≠ .ecx → s₁₅.gpr r = s₁₄.gpr r) → s₁₅.mem = s₁₄.mem → s₁₅.rd = s₁₄.rd → s₁₅.wr = s₁₄.wr →
      WP isa (.block [.store (at_ .edi jmOff) .ecx, .store (at_ .edi nkOff) .ebp, subI .edx 1,
        .store (at_ .edi leftOff) .edx]) s₁₅ fun s' => (s'.zf = some false ∧ WInv s₁ S B kl nk (i + 1) s') ∨
          (s'.zf = some true ∧ WDone s₁ S B kl nk s') := by
    intro s₁₅ ecx₁₅ o₁₅ m₁₅ rd₁₅ wr₁₅
    have edi₁₅ : s₁₅.gpr .edi = B := (o₁₅ _ (by decide)).trans edi₁₄
    refine wp_stm edi₁₅ (inB _ (by rw [wr₁₅, wr₁₄]) _ (by simp only [jmOff]; omega)) fun s₁₆ u₁₆ => ?_
    refine wp_stm (by rw [u₁₆.gpr]; exact edi₁₅) (inB _ (by rw [u₁₆.wr, wr₁₅, wr₁₄]) _
      (by simp only [nkOff]; omega)) fun s₁₇ u₁₇ => ?_
    refine wp_subi fun s₁₈ u₁₈ _ z₁₈ => ?_
    refine wp_stm (by rw [u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr]; exact edi₁₅)
      (inB _ (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, wr₁₅, wr₁₄]) _ (by simp only [leftOff]; omega))
      fun s₁₉ u₁₉ => WP.block_nil ?_
    have edx₁₅ : s₁₅.gpr .edx = BitVec.ofNat 32 (4 * (nk + 7) - i) := by
      rw [o₁₅ _ (by decide), u₁₄.gpr, edx₁₃]
    rw [u₁₇.gpr, u₁₆.gpr, edx₁₅, ofNat_pred (by omega), ofNat_beq_zero (by omega)] at z₁₈
    have ebp₁₅ : s₁₅.gpr .ebp = BitVec.ofNat 32 (4 * nk) := by rw [o₁₅ _ (by decide), u₁₄.gpr, ebp₁₃]
    have edx₁₈ : s₁₈.gpr .edx = BitVec.ofNat 32 (4 * (nk + 7) - (i + 1)) := by
      rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, edx₁₅, ofNat_pred (by omega), Nat.sub_sub]
    let M₁ := (s₂.mem.writeW (addr S (4 * i)) v).writeW (addr B jmOff) (BitVec.ofNat 32 (4 * ((i + 1) % nk)))
    let M := (M₁.writeW (addr B nkOff) (BitVec.ofNat 32 (4 * nk))).writeW (addr B leftOff)
      (BitVec.ofNat 32 (4 * (nk + 7) - (i + 1)))
    have m₁₉ : s₁₉.mem = M := by
      rw [u₁₉.mem, edx₁₈, u₁₈.mem, u₁₇.mem, u₁₆.gpr, ebp₁₅, u₁₆.mem, ecx₁₅, m₁₅, m₁₄]
    have fr : Frame (ekFrame S B) s₁.mem M := by
      have hS : reg32 S 240 ∈ ekFrame S B := List.mem_cons_self ..
      have hC : (⟨addr B rcOff, 16⟩ : Region) ∈ ekFrame S B := by simp
      have cC : ∀ o, rcOff ≤ o → o + 4 ≤ rcOff + 16 →
          (⟨addr B rcOff, 16⟩ : Region).Contains (addr B o) (32 / 8) :=
        fun o h1 h2 => part_contains fB (by simp only [rcOff]; omega) h1 h2 (by decide)
      have f₂ : Frame (ekFrame S B) s₁.mem s₂.mem := hi.frame.trans (hm.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨reg32 B 256, by simp, fun _ h => h⟩
        · exact ⟨⟨addr B rcOff, 16⟩, hC, Region.sub_prefix (by omega)⟩)
      exact (((f₂.writeW hS _ (reg_contains fS (by omega) (by decide))).writeW hC _
        (cC jmOff (by decide) (by decide))).writeW hC _ (cC nkOff (by decide) (by decide))).writeW hC _
        (cC leftOff (by decide) (by decide))
    have rdM : ∀ o, o + 4 ≤ 240 → M.readW (addr S o) 32 = (s₂.mem.writeW (addr S (4 * i)) v).readW (addr S o) 32 :=
      fun o ho => by
        simp only [M, M₁]
        rw [hs.rdS ho (by decide), hs.rdS ho (by decide), hs.rdS ho (by decide)]
    have sched : ∀ j < i + 1, ∀ t < 4,
        (M.readW (addr S (4 * j)) 32).extractLsb' (8 * t) 8 = (kw kl nk j).getD t 0 := by
      intro j hj t ht
      rw [rdM _ (by omega), rd_wr fS _ _ (by omega) (by omega) (by omega) (by omega)]
      split
      · obtain rfl : j = i := by omega
        exact hv t ht
      · rw [sch₂ _ (by omega)]; exact hi.sched j (by omega) t ht
    have esp₁₉ : s₁₉.gpr .esp = s₁.gpr .esp := by
      rw [u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, o₁₅ _ (by decide), g₁₄ _ (by simp), hi.esp]
    have edi₁₉ : s₁₉.gpr .edi = B := by rw [u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, edi₁₅]
    have rd₁₉ : s₁₉.rd = s₁.rd := by rw [u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, rd₁₅, rd₁₄]
    have wr₁₉ : s₁₉.wr = s₁.wr := by rw [u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, wr₁₅, wr₁₄]
    rw [← u₁₉.zf] at z₁₈
    rw [← m₁₉] at fr sched
    by_cases hl : 4 * (nk + 7) - i - 1 = 0
    · exact .inr ⟨by rw [z₁₈, hl]; rfl, edi₁₉, esp₁₉, rd₁₉, wr₁₉, fun j hj => sched j (by omega), fr⟩
    · refine .inl ⟨by rw [z₁₈]; simp [hl], ⟨by omega, by omega, ?_, edi₁₉, esp₁₉, rd₁₉, wr₁₉, ?_, ?_, ?_, ?_,
        sched, fr⟩⟩
      · rw [u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, o₁₅ _ (by decide), u₁₄.gpr, esi₁₃]
      · rw [m₁₉]; simp (disch := decide) only [M, M₁, rd_wr_ne fB, Mem.readW_writeW_self32]
      · rw [m₁₉]; simp (disch := decide) only [M, rd_wr_ne fB, Mem.readW_writeW_self32]
      · rw [m₁₉]; simp (disch := decide) only [M, Mem.readW_writeW_self32]
      · rw [m₁₉]
        simp (disch := decide) only [M, M₁, rd_wr_ne fB]
        rw [hs.rdB (by decide) (by omega), hm.rc, Nat.add_sub_cancel]
  refine WP.seq (WP.ite (decide (4 * (i % nk) + 4 = 4 * nk)) (by simp only [X86.eval, z₁₄])
    (fun hb => ?_) (fun hb => ?_))
  · have h1 : (i + 1) % nk = 0 := by
      have : i % nk + 1 = nk := by simp at hb; omega
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), this, Nat.mod_self]
    refine wp_movi fun s₁₅ u₁₅ => WP.block_nil (hq s₁₅ (by rw [u₁₅.gpr, h1]; rfl) u₁₅.other u₁₅.mem
      u₁₅.rd u₁₅.wr)
  · have h1 : (i + 1) % nk = i % nk + 1 := by
      have : i % nk + 1 < nk := by simp at hb; omega
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), Nat.mod_eq_of_lt this]
    refine WP.block_nil (hq s₁₄ (by rw [u₁₄.gpr, ecx₁₃, h1, Nat.mul_succ]) (fun _ _ => rfl) rfl rfl rfl)


theorem word_ok {i : Nat} {s : State} (hi : WInv s₁ S B kl nk i s) :
    WP isa wordBody s fun s' => (s'.zf = some false ∧ WInv s₁ S B kl nk (i + 1) s') ∨
      (s'.zf = some true ∧ WDone s₁ S B kl nk s') :=
  WP.seq (WP.mono (temp_wp hs hi) fun _ h => WP.seq (WP.mono h fun _ hm => store_wp hs hi hm))

/-! ## The loop over the words -/

theorem words_ok {s : State} (hi : WInv s₁ S B kl nk nk s) :
    WP isa (.loop wordBody .ne) s (WDone s₁ S B kl nk) := by
  refine WP.loop (M := isa) (fun k s => ∃ i, k = 4 * (nk + 7) - i ∧ WInv s₁ S B kl nk i s)
    (fun k s ⟨i, hk, hi⟩ => WP.mono (word_ok hs hi) fun s' h => ?_) _ s ⟨nk, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inr ⟨by simp [X86.eval, z], _, by have := hi.hn; omega, i + 1, rfl, d⟩
  · exact .inl ⟨by simp [X86.eval, z], d⟩

end

/-! ## Copying the key -/

/-- The setting of the copy: the key (`K` bytes at `P`) is outside the schedule. -/
structure CSetup (s₁ : State) (S P : BitVec 32) (K : Nat) : Prop where
  hK : K = 16 ∨ K = 24 ∨ K = 32
  key : reg32 P K ∈ s₁.rd
  sch : reg32 S 240 ∈ s₁.wr
  fK : P.toNat + K ≤ 2 ^ 32
  fS : S.toNat + 240 ≤ 2 ^ 32
  dKS : (reg32 P K).Disjoint (reg32 S 240)

/-- During the copy, after `c` words. -/
structure CInv (s₁ : State) (S P : BitVec 32) (K c : Nat) (s : State) : Prop where
  hc : 4 * c < K
  esi : s.gpr .esi = P + BitVec.ofNat 32 (4 * c)
  ebp : s.gpr .ebp = S + BitVec.ofNat 32 (4 * c)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (K - 4 * c)
  edi : s.gpr .edi = s₁.gpr .edi
  esp : s.gpr .esp = s₁.gpr .esp
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  copied : ∀ j < c, s.mem.readW (addr S (4 * j)) 32 = s₁.mem.readW (addr P (4 * j)) 32
  frame : Frame [reg32 S 240] s₁.mem s.mem

/-- After the copy. -/
structure CDone (s₁ : State) (S P : BitVec 32) (K : Nat) (s : State) : Prop where
  ebp : s.gpr .ebp = S + BitVec.ofNat 32 K
  edi : s.gpr .edi = s₁.gpr .edi
  esp : s.gpr .esp = s₁.gpr .esp
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  copied : ∀ j < K / 4, s.mem.readW (addr S (4 * j)) 32 = s₁.mem.readW (addr P (4 * j)) 32
  frame : Frame [reg32 S 240] s₁.mem s.mem

theorem copy_ok {s₁ : State} {S P : BitVec 32} {K : Nat} (hs : CSetup s₁ S P K) {c : Nat} {s : State}
    (hi : CInv s₁ S P K c s) :
    WP isa (.block copyBody) s fun s' =>
      (s'.zf = some false ∧ CInv s₁ S P K (c + 1) s') ∨ (s'.zf = some true ∧ CDone s₁ S P K s') := by
  have hK := hs.hK
  have hc := hi.hc
  have fK := hs.fK
  have fS := hs.fS
  have hc4 : 4 * c + 4 ≤ K := by rcases hK with rfl | rfl | rfl <;> omega
  refine wp_ldm hi.esi (by
      rw [addr_add]; exact in_rd_left (in_reg (by rw [hi.rd]; exact hs.key) fK (by omega) (by decide)))
    fun s₂ u₂ => ?_
  refine wp_stm (B := S + BitVec.ofNat 32 (4 * c)) (by rw [u₂.other _ (by decide)]; exact hi.ebp)
    (by rw [addr_add, u₂.wr, hi.wr]; exact in_reg hs.sch fS (by omega) (by decide)) fun s₃ u₃ => ?_
  refine wp_addi fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_subi fun s₆ u₆ _ z₆ => WP.block_nil ?_
  have ecx₅ : s₅.gpr .ecx = BitVec.ofNat 32 (K - 4 * c) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), hi.ecx]
  rw [ecx₅, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_ofNat (by omega),
    ofNat_beq_zero (by omega)] at z₆
  have m₆ : s₆.mem = s.mem.writeW (addr S (4 * c)) (s.mem.readW (addr P (4 * c)) 32) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, addr_add, Nat.add_zero, u₂.gpr, addr_add, Nat.add_zero, u₂.mem]
  have copied : ∀ j < c + 1, s₆.mem.readW (addr S (4 * j)) 32 = s₁.mem.readW (addr P (4 * j)) 32 := by
    intro j hj
    rw [m₆, rd_wr fS _ _ (by omega) (by omega) (by omega) (by omega)]
    split
    · obtain rfl : j = c := by omega
      exact hi.frame.readW (reg_contains fK (by omega) (by decide)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hs.dKS) (by decide)
    · exact hi.copied j (by omega)
  have fr : Frame [reg32 S 240] s₁.mem s₆.mem := by
    rw [m₆]; exact hi.frame.writeW (List.mem_singleton_self _) _ (reg_contains fS (by omega) (by decide))
  have g : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → r ≠ .ecx → s₆.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₆.other r h4, u₅.other r h3, u₄.other r h2, u₃.gpr, u₂.other r h1]
  have edi₆ : s₆.gpr .edi = s₁.gpr .edi := by
    rw [g _ (by decide) (by decide) (by decide) (by decide), hi.edi]
  have esp₆ : s₆.gpr .esp = s₁.gpr .esp := by
    rw [g _ (by decide) (by decide) (by decide) (by decide), hi.esp]
  have rd₆ : s₆.rd = s₁.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, hi.rd]
  have wr₆ : s₆.wr = s₁.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, hi.wr]
  have ebp₆ : s₆.gpr .ebp = S + BitVec.ofNat 32 (4 * (c + 1)) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), hi.ebp,
      add_four, Nat.mul_succ]
  by_cases hl : K - 4 * c - 4 = 0
  · refine .inr ⟨by rw [z₆, hl]; rfl, ?_, edi₆, esp₆, rd₆, wr₆, fun j hj => copied j (by omega), fr⟩
    rw [ebp₆, show 4 * (c + 1) = K by omega]
  · refine .inl ⟨by rw [z₆]; simp [hl], ⟨by omega, ?_, ebp₆, ?_, edi₆, esp₆, rd₆, wr₆, copied, fr⟩⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), hi.esi,
        add_four, Nat.mul_succ]
    · rw [u₆.gpr, ecx₅, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_ofNat (by omega)]
      congr 1

theorem copyLoop_ok {s₁ : State} {S P : BitVec 32} {K : Nat} (hs : CSetup s₁ S P K) {s : State}
    (hi : CInv s₁ S P K 0 s) :
    WP isa (.loop (.block copyBody) .ne) s (CDone s₁ S P K) := by
  refine WP.loop (M := isa) (fun k s => ∃ c, k = K - 4 * c ∧ CInv s₁ S P K c s)
    (fun k s ⟨c, hk, hc⟩ => WP.mono (copy_ok hs hc) fun s' h => ?_) _ s ⟨0, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inr ⟨by simp [X86.eval, z], _, by have := hc.hc; omega, c + 1, rfl, d⟩
  · exact .inl ⟨by simp [X86.eval, z], d⟩

/-! ## The prologue -/

/-- After the prologue. -/
structure EP1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  edi : s.gpr .edi = ekScrP s₀
  esi : s.gpr .esi = keyP s₀
  ebp : s.gpr .ebp = ekSchP s₀
  ecx : s.gpr .ecx = arg s₀ 1
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr (ekScrP s₀) 256, 16⟩] s₀.mem s.mem
  saved : ∀ p ∈ savedRegs, s.mem.readW (addr (ekScrP s₀) p.2) 32 = s₀.gpr p.1

theorem ekPrologue_eq : saveRegs 3 ++ copySetup = ([
    .mov .eax (.mem (at_ .esp 16)), .store (at_ .eax 256) .ebx, .store (at_ .eax 260) .esi,
    .store (at_ .eax 264) .edi, .store (at_ .eax 268) .ebp, .mov .edi (.reg .eax),
    .mov .esi (.mem (at_ .esp 4)), .mov .ebp (.mem (at_ .esp 12)), .mov .ecx (.mem (at_ .esp 8))] :
    List Instr) := rfl

theorem ekPrologue_ok {s₀ : State} (hp : EPre s₀) :
    WP isa (.block (saveRegs 3 ++ copySetup)) s₀ (EP1 s₀) := by
  have fB : (ekScrP s₀).toNat + 512 ≤ 2 ^ 32 := hp.fB
  have fSp := hp.fSp
  let B := ekScrP s₀
  let E := s₀.gpr .esp
  have hwB : reg32 B 512 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hrA : ekArgR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  have argC : ∀ i < 4, (ekArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 16⟩ : Region).Contains _ _
    exact part_contains (N := 20) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 4, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨ekArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  have bIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 512 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  have hm : (⟨addr B 256, 16⟩ : Region) ∈ [(⟨addr B 256, 16⟩ : Region)] := List.mem_singleton_self _
  have cB : ∀ o, 256 ≤ o → o + 4 ≤ 272 → (⟨addr B 256, 16⟩ : Region).Contains (addr B o) (32 / 8) :=
    fun o h1 h2 => part_contains fB (by omega) h1 (by omega) (by decide)
  rw [ekPrologue_eq]
  refine wp_ldm (B := E) (o := 16) rfl (argIn _ rfl 3 (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = B := by rw [u₁.gpr]; rfl
  refine wp_stm e₁ (bIn _ u₁.wr 256 (by omega)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (bIn _ (by rw [u₂.wr, u₁.wr]) 260 (by omega)) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁) (bIn _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 264 (by omega))
    fun s₄ u₄ => ?_
  refine wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁)
    (bIn _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 268 (by omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  have g₆ : ∀ r, r ≠ .eax → r ≠ .edi → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₆.other r h2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h1]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have edi₆ : s₆.gpr .edi = B := by rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁
  have esp₆ : s₆.gpr .esp = E := g₆ _ (by decide) (by decide)
  let M := (((s₀.mem.writeW (addr B 256) (s₀.gpr .ebx)).writeW (addr B 260) (s₀.gpr .esi)).writeW
    (addr B 264) (s₀.gpr .edi)).writeW (addr B 268) (s₀.gpr .ebp)
  have m₆ : s₆.mem = M := by
    simp only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr]
    rw [u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.mem]
  have f₆ : Frame [⟨addr B 256, 16⟩] s₀.mem s₆.mem := by
    rw [m₆]
    exact ((((Frame.refl _ _).writeW hm _ (cB 256 (by omega) (by omega))).writeW hm _
      (cB 260 (by omega) (by omega))).writeW hm _ (cB 264 (by omega) (by omega))).writeW hm _
      (cB 268 (by omega) (by omega))
  have arg₆ : ∀ i < 4, s₆.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    f₆.readW (argC i hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.aB.sub_right (part_sub_reg fB (by omega))) (by decide)
  refine wp_ldm (B := E) (o := 4) esp₆ (argIn _ rd₆ 0 (by omega)) fun s₇ u₇ => ?_
  refine wp_ldm (B := E) (o := 12) (by rw [u₇.other _ (by decide)]; exact esp₆)
    (argIn _ (by rw [u₇.rd, rd₆]) 2 (by omega)) fun s₈ u₈ => ?_
  refine wp_ldm (B := E) (o := 8) (by rw [u₈.other _ (by decide), u₇.other _ (by decide)]; exact esp₆)
    (argIn _ (by rw [u₈.rd, u₇.rd, rd₆]) 1 (by omega)) fun s₉ u₉ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, by rw [u₉.rd, u₈.rd, u₇.rd, rd₆], by rw [u₉.wr, u₈.wr, u₇.wr, wr₆],
    by rw [u₉.mem, u₈.mem, u₇.mem]; exact f₆, fun p hp' => ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), esp₆]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), edi₆]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]; exact arg₆ 0 (by omega)
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.mem]; exact arg₆ 2 (by omega)
  · rw [u₉.gpr, u₈.mem, u₇.mem]; exact arg₆ 1 (by omega)
  · have fB' : B.toNat + 512 ≤ 2 ^ 32 := fB
    rw [u₉.mem, u₈.mem, u₇.mem, m₆]
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> show M.readW (addr B _) 32 = _ <;>
    simp (disch := decide) only [M, rd_wr_ne fB', Mem.readW_writeW_self32]

/-! ## Setting up the word loop -/

theorem wordSetup_eq : wordSetup = ([movR .esi .ebp, subI .esi 4, movI .eax 0, .store (at_ .edi 276) .eax,
    .mov .eax (.mem (at_ .esp 8)), .store (at_ .edi 280) .eax, shrI .eax 2, movR .ebx .eax,
    addR .eax .eax, addR .eax .ebx, addI .eax 28, .store (at_ .edi 284) .eax, movI .eax 1,
    .store (at_ .edi 272) .eax] : List Instr) := rfl

theorem left_setup {K : Nat} (hK : K = 16 ∨ K = 24 ∨ K = 32) :
    (BitVec.ofNat 32 K >>> 2) + (BitVec.ofNat 32 K >>> 2) + (BitVec.ofNat 32 K >>> 2) + 28 =
      BitVec.ofNat 32 (4 * (K / 4 + 7) - K / 4) := by
  rcases hK with rfl | rfl | rfl <;> decide

theorem esi_setup (S : BitVec 32) {K : Nat} (hK : K = 16 ∨ K = 24 ∨ K = 32) :
    S + BitVec.ofNat 32 K - 4 = S + BitVec.ofNat 32 (4 * (K / 4 - 1)) := by
  rcases hK with rfl | rfl | rfl <;> bv_omega

/-- A word of the key, byte by byte. -/
theorem kw_getD_key {m : Mem} {P : BitVec 32} {K j t : Nat} (hP : P.toNat + K ≤ 2 ^ 32) (hj : j < K / 4)
    (ht : t < 4) :
    (kw (Spec.Aes.bytesAt m (P.setWidth 64) K) (K / 4) j).getD t 0 =
      (m.readW (addr P (4 * j)) 32).extractLsb' (8 * t) 8 := by
  rw [kw_key _ hj, ← Mem.readW_byte _ _ ht, addr_add64 (by omega), addr_eq (by omega)]
  simp only [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 4 * j + t < K by omega), ht, ite_true]
  rfl

/-! ## The whole function -/

theorem ek_correct {s₀ : State} (hp : EPre s₀) :
    WP isa Impl.Aes.X86.expandKey s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Aes.expandKeyX86.post s₀ s' := by
  let B := ekScrP s₀
  let S := ekSchP s₀
  let P := keyP s₀
  let K := keyLen s₀
  let E := s₀.gpr .esp
  have fB : B.toNat + 512 ≤ 2 ^ 32 := hp.fB
  have fS : S.toNat + 240 ≤ 2 ^ 32 := hp.fS
  have fK : P.toNat + K ≤ 2 ^ 32 := hp.fK
  have fSp : E.toNat + 20 ≤ 2 ^ 32 := hp.fSp
  have hK : K = 16 ∨ K = 24 ∨ K = 32 := hp.len
  have hK4 : K = 4 * (K / 4) := by omega
  let kl := Spec.Aes.bytesAt s₀.mem (P.setWidth 64) K
  have hlen : kl.length = K := by simp [kl, Spec.Aes.bytesAt]
  have hwB : reg32 B 512 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hwS : reg32 S 240 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self ..
  have hrA : ekArgR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  -- The prologue and the copy.
  unfold Impl.Aes.X86.expandKey
  refine WP.seq (WP.mono (ekPrologue_ok hp) fun s₁ h₁ => ?_)
  have hsC : CSetup s₁ S P K :=
    { hK, key := by rw [h₁.rd, hp.rd]; exact List.mem_cons_self .., sch := by rw [h₁.wr]; exact hwS, fK, fS,
      dKS := hp.dKS }
  have ci : CInv s₁ S P K 0 s₁ :=
    ⟨by omega, by rw [h₁.esi]; simp [P], by rw [h₁.ebp]; simp [S],
      by rw [h₁.ecx, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      rfl, rfl, rfl, rfl, fun j hj => absurd hj (by omega), Frame.refl _ _⟩
  refine WP.seq (WP.mono (copyLoop_ok hsC ci) fun s₂ h₂ => ?_)
  -- The regions written so far.
  have F₂ : Frame [reg32 S 240, reg32 B 512] s₀.mem s₂.mem :=
    (h₁.frame.sub fun r hr => ⟨reg32 B 512, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩).trans
    (h₂.frame.sub fun r hr => ⟨reg32 S 240, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  have argD : ∀ r ∈ [reg32 S 240, reg32 B 512], (ekArgR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.aS
    · exact hp.aB
  have argC : (ekArgR s₀).Contains (addr E 8) 4 := by
    show (⟨addr E 4, 16⟩ : Region).Contains _ _
    exact part_contains (N := 20) (by omega) (by omega) (by omega) (by omega) (by decide)
  -- `wordSetup`.
  refine WP.seq ?_
  rw [wordSetup_eq]
  have edi₂ : s₂.gpr .edi = B := h₂.edi.trans h₁.edi
  have wr₂ : s₂.wr = s₀.wr := h₂.wr.trans h₁.wr
  have inB : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 512 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  refine wp_mov fun s₃ u₃ => wp_subi fun s₄ u₄ _ _ => wp_movi fun s₅ u₅ => ?_
  have edi₅ : s₅.gpr .edi = B := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), edi₂]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, wr₂]
  refine wp_stm edi₅ (inB _ wr₅ _ (by omega)) fun s₆ u₆ => ?_
  have esp₆ : s₆.gpr .esp = E := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), h₂.esp, h₁.esp]
  refine wp_ldm (B := E) (o := 8) esp₆ ⟨ekArgR s₀, List.mem_append_left _ (by
      rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd, h₁.rd]; exact hrA), argC⟩ fun s₇ u₇ => ?_
  have eax₇ : s₇.gpr .eax = BitVec.ofNat 32 K := by
    have F₆ : Frame [reg32 S 240, reg32 B 512] s₀.mem s₆.mem := by
      rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
      exact F₂.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (reg_contains fB (by omega) (by decide))
    rw [u₇.gpr, F₆.readW argC argD (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  have edi₇ : s₇.gpr .edi = B := by rw [u₇.other _ (by decide), u₆.gpr, edi₅]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, wr₅]
  refine wp_stm edi₇ (inB _ wr₇ _ (by omega)) fun s₈ u₈ => ?_
  refine wp_shr (by decide) fun s₉ u₉ _ => wp_mov fun s₁₀ u₁₀ => wp_add fun s₁₁ u₁₁ _ => ?_
  refine wp_add fun s₁₂ u₁₂ _ => wp_addi fun s₁₃ u₁₃ => ?_
  have edi₁₃ : s₁₃.gpr .edi = B := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.gpr, edi₇]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  refine wp_stm edi₁₃ (inB _ wr₁₃ _ (by omega)) fun s₁₄ u₁₄ => wp_movi fun s₁₅ u₁₅ => ?_
  refine wp_stm (by rw [u₁₅.other _ (by decide), u₁₄.gpr, edi₁₃])
    (inB _ (by rw [u₁₅.wr, u₁₄.wr, wr₁₃]) _ (by omega)) fun s₁₆ u₁₆ => WP.block_nil ?_
  have ws : WSetup s₁ S B kl (K / 4) :=
    ⟨by omega, by rw [hlen]; exact hK4, by rw [h₁.wr]; exact hwS, by rw [h₁.wr]; exact hwB, fS, fB, hp.dSB⟩
  let L := BitVec.ofNat 32 (4 * (K / 4 + 7) - K / 4)
  let M := (((s₂.mem.writeW (addr B 276) (0 : BitVec 32)).writeW (addr B 280) (BitVec.ofNat 32 K)).writeW
    (addr B 284) L).writeW (addr B 272) (1 : BitVec 32)
  have eax₁₃ : s₁₃.gpr .eax = L := by
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, u₁₁.other _ (by decide), u₁₀.gpr, u₁₀.other _ (by decide), u₉.gpr,
      u₈.gpr, eax₇]
    exact left_setup hK
  have m₁₆ : s₁₆.mem = M := by
    rw [u₁₆.mem, u₁₅.gpr, u₁₅.mem, u₁₄.mem, eax₁₃, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem,
      eax₇, u₇.mem, u₆.mem, u₅.gpr, u₅.mem, u₄.mem, u₃.mem]
  have g₁₆ : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → s₁₆.gpr r = s₂.gpr r := fun r h1 h2 h3 => by
    rw [u₁₆.gpr, u₁₅.other r h1, u₁₄.gpr, u₁₃.other r h1, u₁₂.other r h1, u₁₁.other r h1, u₁₀.other r h2,
      u₉.other r h1, u₈.gpr, u₇.other r h1, u₆.gpr, u₅.other r h1, u₄.other r h3, u₃.other r h3]
  have wi : WInv s₁ S B kl (K / 4) (K / 4) s₁₆ :=
    { hi := Nat.le_refl _
      hn := by omega
      esi := by
        rw [u₁₆.gpr, u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide),
          u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
          u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, h₂.ebp]
        exact esi_setup S hK
      edi := by rw [g₁₆ _ (by decide) (by decide) (by decide), edi₂]
      esp := by rw [g₁₆ _ (by decide) (by decide) (by decide), h₂.esp]
      rd := by
        rw [u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd,
          u₄.rd, u₃.rd, h₂.rd]
      wr := by rw [u₁₆.wr, u₁₅.wr, u₁₄.wr, wr₁₃, h₁.wr]
      jm := by
        rw [m₁₆, Nat.mod_self, Nat.mul_zero]
        simp (disch := decide) only [M, rd_wr_ne fB, Mem.readW_writeW_self32, jmOff]; rfl
      nk4 := by
        rw [m₁₆, ← hK4]
        simp (disch := decide) only [M, rd_wr_ne fB, Mem.readW_writeW_self32, nkOff]
      left := by
        rw [m₁₆]; simp (disch := decide) only [M, rd_wr_ne fB, Mem.readW_writeW_self32, leftOff]; rfl
      rc := by
        rw [m₁₆, Nat.div_eq_of_lt (by omega)]
        simp (disch := decide) only [M, Mem.readW_writeW_self32, rcOff]; rfl
      sched := fun j hj t ht => by
        rw [m₁₆]
        simp only [M]
        rw [ws.rdS (by omega) (by decide), ws.rdS (by omega) (by decide), ws.rdS (by omega) (by decide),
          ws.rdS (by omega) (by decide), h₂.copied j hj,
          h₁.frame.readW (reg_contains fK (by omega) (by decide)) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hp.dKB.sub_right (part_sub_reg fB (by omega))) (by decide),
          kw_getD_key fK hj ht]
      frame := by
        have hC : (⟨addr B rcOff, 16⟩ : Region) ∈ ekFrame S B := by simp
        have cC : ∀ o, rcOff ≤ o → o + 4 ≤ rcOff + 16 →
            (⟨addr B rcOff, 16⟩ : Region).Contains (addr B o) (32 / 8) :=
          fun o h1 h2 => part_contains fB (by simp only [rcOff]; omega) h1 h2 (by decide)
        rw [m₁₆]
        exact ((((h₂.frame.sub fun r hr => ⟨r, by simp at hr; subst hr; simp, fun _ h => h⟩).writeW hC _
          (cC 276 (by decide) (by decide))).writeW hC _ (cC 280 (by decide) (by decide))).writeW hC _
          (cC 284 (by decide) (by decide))).writeW hC _ (cC 272 (by decide) (by decide)) }
  -- The words, and the epilogue.
  refine WP.seq (WP.mono (words_ok ws wi) fun s₁₇ h₁₇ => ?_)
  refine WP.mono (restore_ok h₁₇.edi fB (by rw [h₁₇.wr, h₁.wr]; exact hwB)) fun s₁₈ ⟨sv₁₈, o₁₈, m₁₈⟩ => ?_
  have F : Frame [reg32 S 240, reg32 B 512] s₀.mem s₁₇.mem :=
    (h₁.frame.sub fun r hr => ⟨reg32 B 512, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩).trans
    (h₁₇.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨reg32 S 240, by simp, fun _ h => h⟩
      · exact ⟨reg32 B 512, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨reg32 B 512, by simp, part_sub_reg fB (by simp only [rcOff]; omega)⟩)
  have saved : ∀ p ∈ savedRegs, s₁₇.mem.readW (addr B p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have h2 : 256 ≤ p.2 ∧ p.2 + 4 ≤ 272 := by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> decide
    rw [← h₁.saved p hp']
    exact h₁₇.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.dSB.sub_right (part_sub_reg fB (by omega))).symm
      · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
        rw [← addr_zero]; exact part_disj fB (by omega) (by omega) (.inr (by omega))
      · exact part_disj fB (by omega) (by simp only [rcOff]; omega) (.inl (by simp only [rcOff]; omega)))
      (by decide)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [sv₁₈ (.ebx, 256) (by simp [savedRegs]), saved (.ebx, 256) (by simp [savedRegs])]
    · rw [sv₁₈ (.esi, 260) (by simp [savedRegs]), saved (.esi, 260) (by simp [savedRegs])]
    · rw [sv₁₈ (.edi, 264) (by simp [savedRegs]), saved (.edi, 264) (by simp [savedRegs])]
    · rw [sv₁₈ (.ebp, 268) (by simp [savedRegs]), saved (.ebp, 268) (by simp [savedRegs])]
    · rw [o₁₈ _ (by simp), h₁₇.esp, h₁.esp]
  · rw [m₁₈]
    exact F.readW (r := ekRetR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.rS
      · exact hp.rB) (by decide)
  · show Spec.Aes.bytesAt s₁₈.mem (S.setWidth 64) (16 * (Spec.Aes.rounds (K / 4) + 1)) = Spec.Aes.expandKey kl
    have lhs : ∀ n, Spec.Aes.bytesAt s₁₈.mem (S.setWidth 64) n =
        (List.range n).map fun k => s₁₈.mem (S.setWidth 64 + BitVec.ofNat 64 k) := fun _ => rfl
    rw [lhs, Spec.Aes.expandKey, hlen, Spec.Aes.rounds,
      show 16 * (K / 4 + 6 + 1) = 4 * (4 * (K / 4 + 6 + 1)) by omega]
    refine flatten_expandWords ws.len (by omega) _ _ fun k hk => ?_
    have e : S.setWidth 64 + BitVec.ofNat 64 k = addr S (4 * (k / 4)) + BitVec.ofNat 64 (k % 4) := by
      rw [addr_add64 (by omega), Nat.div_add_mod, addr_eq (by omega)]
    rw [m₁₈, e, Mem.readW_byte s₁₇.mem _ (Nat.mod_lt _ (by omega)),
      h₁₇.sched _ (by omega) _ (Nat.mod_lt _ (by omega))]

/-- Memory holding the arguments `0x1000, 16, 0x2000, 0x3000` at `0x8004`. -/
def ekSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800D then 0x20
  else if a = 0x8011 then 0x30 else 0

/-- A state satisfying the precondition. -/
def ekSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ekSatMem
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_correct (s : State) (hs : Proof.Aes.expandKeyX86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.expandKey s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86.post s s' :=
  (ek_correct (EPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem expandKey_verified :
    Verified X86.target Impl.Aes.X86.expandKey (Spec.Aes.expandKeyContract X86.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct
    (by
      have a0 : arg ekSat 0 = 0x1000 := by decide
      have a1 : arg ekSat 1 = 16 := by decide
      have a2 : arg ekSat 2 = 0x2000 := by decide
      have a3 : arg ekSat 3 = 0x3000 := by decide
      have e : argAddr ekSat 0 = 0x8004 := by decide
      have esp : ekSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.expandKeyX86] [a0, a1, a2, a3, e, esp] using ekSat)

end VG.Proof.Aes.X86
