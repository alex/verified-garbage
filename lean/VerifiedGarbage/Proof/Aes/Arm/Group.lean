import VerifiedGarbage.Proof.Aes.Arm.Keys
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.MdStream.Arm.Common

/-!
# One group of counter-mode blocks on ARMv7

Untrusted: everything here is checked by Lean.

A group stores the data pointer, the blocks left and the first round key
in slots 45–47 of the scratch buffer (`groupSave`), `ctrBlocks` builds the
counter blocks `c + b` (`b < 2`) from the slots of the counter block
(`front_wp`, then `ctr_inRel` for `InRel`), `encrypt2` encrypts them
(`Encrypt.lean`), `groupLoad` loads the three values back, and `xorFull` or
`xorTail` XOR the keystream into the data, a word at a time. The
per-instruction rules are those of `Proof/MdStream/Arm/Common.lean`.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp wp_rev
  wp_ldr wp_str)
open VG.Proof.Aes (ctrState ctrBlock_byte toBytes_getD getD_eq byte_ext)

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2}
    {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

/-! ## Slots of the scratch buffer -/

/-- Slot `k` of the scratch buffer at `B`. -/
abbrev slotA (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (4 * k)

theorem slot_addr {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {k : Nat} (hk : k < 512) :
    State.addr (b + BitVec.ofNat 32 (4 * k)) = slotA (State.addr b) k := addr_add (by omega)

theorem slot_addr' {b : BitVec 32} {L : Nat} (hfit : b.toNat + L ≤ 2 ^ 32) {k : Nat} (hk : 4 * k + 4 ≤ L) :
    State.addr (b + BitVec.ofNat 32 (4 * k)) = slotA (State.addr b) k := addr_add (by omega)

theorem slot_in {rs : List Region} {b : BitVec 32} (hr : (⟨State.addr b, 2048⟩ : Region) ∈ rs)
    (hfit : b.toNat + 2048 ≤ 2 ^ 32) {k : Nat} (hk : k < 512) : InRegions rs (slotA (State.addr b) k) 4 := by
  rw [← slot_addr hfit hk]; exact in_off hr hfit (by omega) (by omega)

theorem slotA_sep (B : Addr) {j k : Nat} (hj : j < 512) (hk : k < 512) (h : j ≠ k) :
    Mem.Sep (slotA B j) (32 / 8) (slotA B k) (32 / 8) := by
  intro x h₁ h₂
  simp only [slotA] at h₁ h₂
  have : j < k ∨ k < j := by omega
  rcases this with h' | h' <;> bv_omega

theorem readW_writeW_slot (m : Mem) (B : Addr) {j k : Nat} (hj : j < 512) (hk : k < 512) (h : j ≠ k)
    (v : BitVec 32) : (m.writeW (slotA B k) v).readW (slotA B j) 32 = m.readW (slotA B j) 32 :=
  Mem.readW_writeW_sep (slotA_sep B hj hk h) (by decide)

section
variable {is : List Instr} {s : State} {Q : State → Prop} {b : BitVec 32}

theorem wp_ldS {t : Reg} {k : Nat} (hb : s.gpr sb = b) (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 2048 ≤ 2 ^ 32) (hk : k < 512)
    (c : ∀ s', Upd s s' t (s.mem.readW (slotA (State.addr b) k) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (ldS t k :: is)) s Q :=
  wp_ldr (by omega) (by rw [hb]; exact slot_addr hfit hk)
    (slot_in (List.mem_append_right _ hscr) hfit hk) c

theorem wp_stS {t : Reg} {k : Nat} (hb : s.gpr sb = b) (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 2048 ≤ 2 ^ 32) (hk : k < 512)
    (c : ∀ s', Mupd s s' (s.mem.writeW (slotA (State.addr b) k) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (stS k t :: is)) s Q :=
  wp_str (by omega) (by rw [hb]; exact slot_addr hfit hk) (slot_in hscr hfit hk) c

end

/-! ## The counter blocks -/

/-- The words of the counter block in the slots: words 0–2, and the counter. -/
abbrev cwW (m : Mem) (B : Addr) (k : Nat) : BitVec 32 := m.readW (slotA B (cW k)) 32
abbrev numW (m : Mem) (B : Addr) : BitVec 32 := m.readW (slotA B cNum) 32

theorem q_ctr : ∀ bb < 2, ∀ k < 4, q (2 * k + bb) ≠ sb ∧ q (2 * k + bb) ≠ t0 ∧ q (2 * k + bb) ≠ kp := by
  decide

theorem q_ne : ∀ a < 8, ∀ c < 8, a ≠ c → q a ≠ q c := by
  decide

theorem q_inj : ∀ bb < 2, ∀ j < 4, ∀ k < 4, j ≠ k → q (2 * j + bb) ≠ q (2 * k + bb) := by
  decide

theorem ctrBlock_wp {s : State} {b : BitVec 32} {bb : Nat} (hbb : bb < 2) (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', (∀ k < 3, s'.gpr (q (2 * k + bb)) = cwW s.mem (State.addr b) k) →
      s'.gpr (q (2 * 3 + bb)) = rev (numW s.mem (State.addr b) + BitVec.ofNat 32 bb) →
      (∀ r, (∀ k < 4, r ≠ q (2 * k + bb)) → r ≠ t0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (ctrBlock bb)) s P := by
  have qc := q_ctr bb hbb
  have e0 : q bb = q (2 * 0 + bb) := by simp
  have e1 : q (2 + bb) = q (2 * 1 + bb) := by congr 1
  have e2 : q (4 + bb) = q (2 * 2 + bb) := by congr 1
  have e3 : q (6 + bb) = q (2 * 3 + bb) := by congr 1
  simp only [ctrBlock, e0, e1, e2, e3]
  refine wp_ldS hb hscr hfit (by decide) fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr sb = b := (u₁.other _ (qc 0 (by omega)).1.symm).trans hb
  refine wp_ldS hb₁ (u₁.wr ▸ hscr) hfit (by decide) fun s₂ u₂ => ?_
  have hb₂ : s₂.gpr sb = b := (u₂.other _ (qc 1 (by omega)).1.symm).trans hb₁
  refine wp_ldS hb₂ (u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₃ u₃ => ?_
  have hb₃ : s₃.gpr sb = b := (u₃.other _ (qc 2 (by omega)).1.symm).trans hb₂
  refine wp_ldS hb₃ (u₃.wr ▸ u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by rcases (show bb = 0 ∨ bb = 1 by omega) with rfl | rfl <;> decide))
    fun s₅ u₅ => ?_
  refine wp_rev fun s₆ u₆ => ?_
  refine WP.block_nil (h s₆ (fun k hk => ?_) ?_ (fun r hr ht => ?_) ?_ ?_ ?_ ?_)
  · have hne : ∀ j < 4, j ≠ k → q (2 * k + bb) ≠ q (2 * j + bb) := fun j hj hjk =>
      q_inj bb hbb k (by omega) j hj (Ne.symm hjk)
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · rw [u₆.other _ (hne 3 (by omega) (by omega)), u₅.other _ (qc 0 (by omega)).2.1,
        u₄.other _ (qc 0 (by omega)).2.1, u₃.other _ (hne 2 (by omega) (by omega)),
        u₂.other _ (hne 1 (by omega) (by omega)), u₁.gpr]
    · rw [u₆.other _ (hne 3 (by omega) (by omega)), u₅.other _ (qc 1 (by omega)).2.1,
        u₄.other _ (qc 1 (by omega)).2.1, u₃.other _ (hne 2 (by omega) (by omega)), u₂.gpr,
        u₁.mem]
    · rw [u₆.other _ (hne 3 (by omega) (by omega)), u₅.other _ (qc 2 (by omega)).2.1,
        u₄.other _ (qc 2 (by omega)).2.1, u₃.gpr, u₂.mem, u₁.mem]
  · rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.other _ (hr 3 (by omega)), u₅.other _ ht, u₄.other _ ht, u₃.other _ (hr 2 (by omega)),
      u₂.other _ (hr 1 (by omega)), u₁.other _ (hr 0 (by omega))]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- The memory after `groupSave` and `ctrBlocks`. -/
def frontMem (m : Mem) (B : Addr) (d l f : BitVec 32) : Mem :=
  (((m.writeW (slotA B dSlot) d).writeW (slotA B lSlot) l).writeW (slotA B fkSlot) f).writeW
    (slotA B cNum) (numW m B + 2)

theorem q_other : ∀ r, r ∉ layerWrites → r ≠ kp → (∀ bb < 2, ∀ k < 4, r ≠ q (2 * k + bb)) ∧ r ≠ t0 := by
  intro r; cases r <;> decide

theorem gs_read (m : Mem) (B : Addr) (d l f : BitVec 32) {k : Nat} (hk : k < 45) :
    (((m.writeW (slotA B dSlot) d).writeW (slotA B lSlot) l).writeW (slotA B fkSlot) f).readW
      (slotA B k) 32 = m.readW (slotA B k) 32 := by
  rw [readW_writeW_slot _ _ (by omega) (by decide) (by simp [fkSlot]; omega),
    readW_writeW_slot _ _ (by omega) (by decide) (by simp [lSlot]; omega),
    readW_writeW_slot _ _ (by omega) (by decide) (by simp [dSlot]; omega)]

/-- `groupSave` and the two counter blocks, and `c := c + 2`. -/
theorem front_wp {s : State} {b : BitVec 32} (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', (∀ bb < 2, (∀ k < 3, s'.gpr (q (2 * k + bb)) = cwW s.mem (State.addr b) k) ∧
        s'.gpr (q (2 * 3 + bb)) = rev (numW s.mem (State.addr b) + BitVec.ofNat 32 bb)) →
      s'.gpr kp = s.gpr .r12 → (∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r) →
      s'.mem = frontMem s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (groupSave ++ ctrBlocks)) s P := by
  simp only [groupSave, List.cons_append, List.nil_append]
  refine wp_stS hb hscr hfit (by decide) fun s₁ u₁ => ?_
  refine wp_stS (u₁.gpr ▸ hb) (u₁.wr ▸ hscr) hfit (by decide) fun s₂ u₂ => ?_
  refine wp_stS (u₂.gpr ▸ u₁.gpr ▸ hb) (u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₃ u₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  have hb₄ : s₄.gpr sb = b := by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, hb]
  have hscr₄ : (⟨State.addr b, 2048⟩ : Region) ∈ s₄.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hscr
  have hm₄ : s₄.mem = ((s.mem.writeW (slotA (State.addr b) dSlot) (s.gpr .r10)).writeW
      (slotA (State.addr b) lSlot) (s.gpr .r11)).writeW (slotA (State.addr b) fkSlot) (s.gpr .r12) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
  simp only [ctrBlocks]
  repeat rw [WP.block_append_iff (M := isa)]
  refine ctrBlock_wp (bb := 0) (by omega) hb₄ hscr₄ hfit fun s₅ c₅ n₅ o₅ m₅ rd₅ wr₅ sp₅ => ?_
  have hb₅ : s₅.gpr sb = b := (o₅ _ (fun k hk => (q_ctr 0 (by omega) k hk).1.symm) (by decide)).trans hb₄
  refine ctrBlock_wp (bb := 1) (by omega) hb₅ (wr₅ ▸ hscr₄) hfit fun s₆ c₆ n₆ o₆ m₆ rd₆ wr₆ sp₆ => ?_
  have hb₆ : s₆.gpr sb = b := (o₆ _ (fun k hk => (q_ctr 1 (by omega) k hk).1.symm) (by decide)).trans hb₅
  refine wp_ldS hb₆ (wr₆ ▸ wr₅ ▸ hscr₄) hfit (by decide) fun s₇ u₇ => ?_
  refine wp_add (op2_imm (by decide)) fun s₈ u₈ => ?_
  have hb₈ : s₈.gpr sb = b := by rw [u₈.other _ (by decide), u₇.other _ (by decide), hb₆]
  refine wp_stS hb₈ (by rw [u₈.wr, u₇.wr, wr₆, wr₅]; exact hscr₄) hfit (by decide) fun s₉ u₉ => ?_
  have mnum : numW s₄.mem (State.addr b) = numW s.mem (State.addr b) := by
    rw [numW, hm₄, gs_read _ _ _ _ _ (by decide)]
  have mcw : ∀ k < 3, cwW s₄.mem (State.addr b) k = cwW s.mem (State.addr b) k := by
    intro k hk
    rw [cwW, hm₄, gs_read _ _ _ _ _ (by simp [cW]; omega)]
  refine WP.block_nil (h s₉ (fun bb hbb => ?_) ?_ (fun r h1 h2 => ?_) ?_ ?_ ?_ ?_)
  · have qo : ∀ k < 4, q (2 * k + bb) ≠ t0 := fun k hk => (q_ctr bb hbb k hk).2.1
    rcases (show bb = 0 ∨ bb = 1 by omega) with rfl | rfl
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [u₉.gpr, u₈.other _ (qo k (by omega)), u₇.other _ (qo k (by omega)),
          o₆ _ (fun j hj => q_ne _ (by omega) _ (by omega) (by omega)) (qo k (by omega)), c₅ k hk, mcw k hk]
      · rw [u₉.gpr, u₈.other _ (qo 3 (by omega)), u₇.other _ (qo 3 (by omega)),
          o₆ _ (fun j hj => q_ne _ (by omega) _ (by omega) (by omega)) (qo 3 (by omega)), n₅, mnum]
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [u₉.gpr, u₈.other _ (qo k (by omega)), u₇.other _ (qo k (by omega)), c₆ k hk, m₅, mcw k hk]
      · rw [u₉.gpr, u₈.other _ (qo 3 (by omega)), u₇.other _ (qo 3 (by omega)), n₆, m₅, mnum]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      o₆ _ (fun j hj => (q_ctr 1 (by omega) j hj).2.2.symm) (by decide),
      o₅ _ (fun j hj => (q_ctr 0 (by omega) j hj).2.2.symm) (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  · obtain ⟨hq, ht⟩ := q_other r h1 h2
    rw [u₉.gpr, u₈.other _ ht, u₇.other _ ht, o₆ _ (hq 1 (by omega)) ht, o₅ _ (hq 0 (by omega)) ht,
      u₄.other _ h2, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₉.mem, u₈.gpr, u₇.gpr, u₈.mem, u₇.mem, m₆, m₅, frontMem, ← mnum, hm₄]
  · rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₉.sp, u₈.sp, u₇.sp, sp₆, sp₅, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## The counter blocks as states -/

/-- The counter blocks `2g` and `2g + 1` in the words, as `InRel` has them. -/
theorem ctr_inRel {Q : Nat → BitVec 32} {icb : Spec.Gcm.Block} {W : Nat → BitVec 32} {C : BitVec 32}
    {g : Nat}
    (hw : ∀ k < 3, ∀ t < 4, ∀ j < 8, (W k).getLsbD (8 * t + j) = icb.getLsbD (8 * (15 - (4 * k + t)) + j))
    (hC : C = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g))
    (hQ : ∀ bb < 2, (∀ k < 3, Q (2 * k + bb) = W k) ∧ Q (2 * 3 + bb) = rev (C + BitVec.ofNat 32 bb)) :
    InRel Q (fun bb => ctrState icb (2 * g + bb)) := by
  intro bb hb i hi16 j hj
  obtain ⟨h0, h1⟩ := hQ bb hb
  simp only [ctrState, getD_eq _ hi16, Vector.getElem_ofFn]
  rw [ctrBlock_byte _ _ hi16]
  by_cases h12 : i < 12
  · rw [ite_eq_left h12, h0 _ (by omega), toBytes_getD _ hi16, BitVec.getLsbD_extractLsb',
      hw _ (by omega) _ (by omega) _ hj, show 4 * (i / 4) + i % 4 = i by omega]
    simp [hj]
  · rw [ite_eq_right h12, show i / 4 = 3 by omega, h1, rev_bit _ (by omega) hj, hC,
      BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.getLsbD_extractLsb']
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

/-! ## XOR into the data -/

/-- XOR `v` into the 4 bytes at `a`. -/
def xorW (m : Mem) (a : Addr) (v : BitVec 32) : Mem := m.writeW a (m.readW a 32 ^^^ v)

theorem xorW_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    xorW m a v x = if (x - a).toNat < 4 then m x ^^^ v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  unfold xorW Mem.writeW Mem.write
  split
  · rename_i h
    have hx : a + BitVec.ofNat 64 (x - a).toNat = x := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have := Mem.extractLsb'_read m a (n := 4) h
    rw [hx] at this
    rw [← this]
    ext t ht
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_xor, Mem.readW]
    simp
  · rfl

/-- The data after `k` words: the keystream `ks` XORed into the first `4 k`
of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < 4 * k then ks i else 0)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := by
  rw [← BitVec.sub_sub, BitVec.add_comm D, BitVec.add_sub_cancel, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  split
  · rw [show 2 ^ 64 - j + i = (i - j) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [show 2 ^ 64 - j + i = 2 ^ 64 + i - j by omega]; exact Nat.mod_eq_of_lt (by omega)

/-- One word of keystream XORed in. -/
theorem dataInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 32}
    (hn : 16 * n ≤ 2 ^ 32) (hk : k < 4 * n) (h : DataInv m₀ m D n k ks)
    (hks : ∀ t < 4, v.extractLsb' (8 * t) 8 = ks (4 * k + t)) :
    DataInv m₀ (xorW m (D + BitVec.ofNat 64 (4 * k)) v) D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m (xorW m (D + BitVec.ofNat 64 (4 * k)) v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [xorW_apply, off_toNat D (by omega) (by omega), h i hi]
    by_cases h1 : 4 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 4 * k < 4
      · rw [ite_eq_left h2, hks _ h2, ite_eq_right (show ¬ i < 4 * k by omega),
          ite_eq_left (show i < 4 * (k + 1) by omega), show 4 * k + (i - 4 * k) = i by omega]
        simp
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 4 * k by omega),
          ite_eq_right (show ¬ i < 4 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 4 * k < 4 by omega),
        ite_eq_left (show i < 4 * k by omega), ite_eq_left (show i < 4 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx _ (List.mem_singleton_self _)
    rw [xorW_apply, ite_eq_right]
    have : 4 * k < 2 ^ 64 := by omega
    have : (BitVec.ofNat 64 (4 * k)).toNat = 4 * k := by simp; omega
    bv_omega

theorem dataInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {ks : Nat → Byte} (h : DataInv m₀ m D n k ks)
    (hk : 4 * n ≤ k) (hk' : 4 * n ≤ k') : DataInv m₀ m D n k' ks := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 4 * k by omega), ite_eq_left (show i < 4 * k' by omega)]

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

theorem ks_of_inRel {Q : Nat → BitVec 32} {R g : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : InRel Q (fun bb => Spec.Aes.cipher R w (ctrState icb (2 * g + bb)))) {k t : Nat} (hk : k < 8)
    (ht : t < 4) :
    (Q (2 * (k % 4) + k / 4)).extractLsb' (8 * t) 8 = keyStream R w icb (4 * (8 * g + k) + t) := by
  apply byte_ext
  intro j hj
  have := h (k / 4) (by omega) (4 * (k % 4) + t) (by omega) j hj
  rw [show (4 * (k % 4) + t) / 4 = k % 4 by omega, show (4 * (k % 4) + t) % 4 = t by omega] at this
  rw [BitVec.getLsbD_extractLsb', this, keyStream,
    show (4 * (8 * g + k) + t) / 16 = 2 * g + k / 4 by omega,
    show (4 * (8 * g + k) + t) % 16 = 4 * (k % 4) + t by omega]
  simp [hj]

/-- Word `k` of a group of two blocks: `ldr`, `eor` with its keystream word, `str`. -/
def triple (k : Nat) : List Instr :=
  [.ldr .lr .r10 (4 * k), eorR .lr .lr (q (2 * (k % 4) + k / 4)), .str .lr .r10 (4 * k)]

theorem xorFull_eq : xorFull = triple 0 ++ triple 1 ++ triple 2 ++ triple 3 ++ triple 4 ++ triple 5 ++
    triple 6 ++ triple 7 ++ ([.dp .add .r10 .r10 (.imm 32), .dp .sub .r11 .r11 (.imm 2)] : List Instr) := rfl

theorem xorTail_eq : xorTail = triple 0 ++ triple 1 ++ triple 2 ++ triple 3 ++
    ([.mov .r11 (.imm 0)] : List Instr) := rfl

/-- After `k` words of the group have been XORed in, from `s₃`. -/
structure XS (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) (k : Nat) (s : State) :
    Prop where
  data : DataInv m₀ s.mem D n (8 * g + k) ks
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ .lr → r ≠ kp → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  sp : s.sp = s₃.sp

/-- Before the XOR phase of group `g`: the keystream is in the words. -/
structure XPre (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ : State) : Prop where
  hg : 2 * g < n
  fit : Dp.toNat + 16 * n ≤ 2 ^ 32
  dat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s₃.wr
  r10 : s₃.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)
  r11 : s₃.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  data : DataInv m₀ s₃.mem (State.addr Dp) n (8 * g) ks
  ks : ∀ k < 8, ∀ t < 4, (s₃.gpr (q (2 * (k % 4) + k / 4))).extractLsb' (8 * t) 8 = ks (4 * (8 * g + k) + t)

section Xor

variable {m₀ : Mem} {Dp : BitVec 32} {n g : Nat} {ks : Nat → Byte} {s₃ : State}

theorem xs_step (hp : XPre m₀ Dp n g ks s₃) {k : Nat} (hk : k < 8) (hkn : 8 * g + k < 4 * n) {s : State}
    (hs : XS m₀ (State.addr Dp) n g ks s₃ k s) {is : List Instr} {P : State → Prop}
    (h : ∀ s', XS m₀ (State.addr Dp) n g ks s₃ (k + 1) s' → WP isa (.block is) s' P) :
    WP isa (.block (triple k ++ is)) s P := by
  have hn := hp.fit
  have ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 (4 * k)) =
      State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k)) := by
    rw [hs.keep _ (by decide) (by decide), hp.r10, add_ofNat_ofNat, addr_add (by omega)]
    congr 2; omega
  have hin : InRegions s.wr (State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k))) 4 := by
    have := in_off (hs.wr ▸ hp.dat) hp.fit (off := 4 * (8 * g + k)) (n := 4) (by omega) (by omega)
    rwa [addr_add (by omega)] at this
  have hq : q (2 * (k % 4) + k / 4) ≠ .lr := by unfold q; split <;> decide
  have hqk : q (2 * (k % 4) + k / 4) ≠ kp := (q_ctr (k / 4) (by omega) (k % 4) (by omega)).2.2
  simp only [triple, List.cons_append, List.nil_append]
  refine wp_ldr (by omega) ha (by
    obtain ⟨r, hr, hc⟩ := hin; exact ⟨r, List.mem_append_right _ hr, hc⟩) fun s₁ u₁ => ?_
  refine wp_eor (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_str (a := State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k))) (by omega)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact ha)
    (by rw [u₂.wr, u₁.wr]; exact hin) fun s₃' u₃ => ?_
  have hst := dataInv_step (v := s.gpr (q (2 * (k % 4) + k / 4))) (by omega) hkn hs.data
    (fun t ht => by rw [hs.keep _ hq hqk]; exact hp.ks k hk t ht)
  have hm : s₃'.mem = xorW s.mem (State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k)))
      (s.gpr (q (2 * (k % 4) + k / 4))) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, u₁.other _ hq, xorW]
  rw [← hm] at hst
  refine h s₃' ⟨by rw [show 8 * g + (k + 1) = 8 * g + k + 1 by omega]; exact hst.1,
    hs.frame.trans hst.2, fun r hr hr' => ?_, ?_, ?_, ?_⟩
  · rw [u₃.gpr, u₂.other _ hr, u₁.other _ hr, hs.keep r hr hr']
  · rw [u₃.rd, u₂.rd, u₁.rd, hs.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, hs.wr]
  · rw [u₃.sp, u₂.sp, u₁.sp, hs.sp]

/-- After the XOR phase: `r11` is zero if no data is left. -/
def XDone (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop :=
  Frame [⟨State.addr Dp, 16 * n⟩] s₃.mem s.mem ∧
    (∀ r, r ≠ .lr → r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    ((s.gpr .r11 = 0 ∧ DataInv m₀ s.mem (State.addr Dp) n (4 * n) ks) ∨
     (2 * g + 2 < n ∧ DataInv m₀ s.mem (State.addr Dp) n (8 * (g + 1)) ks ∧
      s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      s.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1))))

theorem shr1_eq (x : Nat) (hx : x < 2 ^ 32) :
    (!(BitVec.ofNat 32 x >>> 1 - 0 == 0)) = decide (2 ≤ x) := by
  by_cases h : 2 ≤ x
  · have : BitVec.ofNat 32 x >>> 1 - 0 ≠ 0 := by bv_omega
    simpa [h] using this
  · have : BitVec.ofNat 32 x >>> 1 - 0 = 0 := by bv_omega
    rw [this]; simp [h]

theorem xorPhase_wp (hp : XPre m₀ Dp n g ks s₃) :
    WP isa (.block [.mov kp (lsrOp .r11 1), .cmp kp (.imm 0)]) s₃ fun s =>
      WP isa (.ite .ne (.block xorFull) (.block xorTail)) s (XDone m₀ Dp n g ks s₃) := by
  have hg := hp.hg
  have hn := hp.fit
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ =>
    WP.block_nil ?_
  have ev₅ : Arm.eval .ne s₅ = some (decide (2 ≤ n - 2 * g)) := by
    rw [Arm.eval, z₅, u₄.gpr, hp.r11, shr1_eq _ (by omega)]
  have g₅ : ∀ r, r ≠ kp → s₅.gpr r = s₃.gpr r := fun r hr => by rw [f₅.gpr, u₄.other r hr]
  have x₀ : XS m₀ (State.addr Dp) n g ks s₃ 0 s₅ :=
    ⟨by rw [f₅.mem, u₄.mem]; exact hp.data, by rw [f₅.mem, u₄.mem]; exact Frame.refl _ _,
      fun r _ hr => g₅ r hr, by rw [f₅.rd, u₄.rd], by rw [f₅.wr, u₄.wr], by rw [f₅.sp, u₄.sp]⟩
  refine WP.ite (decide (2 ≤ n - 2 * g)) ev₅ (fun hb => ?_) (fun hb => ?_)
  · -- Two blocks.
    have h2 : 2 ≤ n - 2 * g := by simpa using hb
    rw [xorFull_eq]
    simp only [List.append_assoc]
    refine xs_step hp (k := 0) (by omega) (by omega) x₀ fun s₆ x₆ => ?_
    refine xs_step hp (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine xs_step hp (k := 2) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    refine xs_step hp (k := 3) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
    refine xs_step hp (k := 4) (by omega) (by omega) x₉ fun s₁₀ x₁₀ => ?_
    refine xs_step hp (k := 5) (by omega) (by omega) x₁₀ fun s₁₁ x₁₁ => ?_
    refine xs_step hp (k := 6) (by omega) (by omega) x₁₁ fun s₁₂ x₁₂ => ?_
    refine xs_step hp (k := 7) (by omega) (by omega) x₁₂ fun s₁₃ x₁₃ => ?_
    refine wp_add (op2_imm (by decide)) fun s₁₄ u₁₄ => wp_sub (op2_imm (by decide)) fun s₁₅ u₁₅ =>
      WP.block_nil ⟨by rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.frame, fun r h1 h2 h3 h4 => ?_,
        by rw [u₁₅.rd, u₁₄.rd, x₁₃.rd], by rw [u₁₅.wr, u₁₄.wr, x₁₃.wr], by rw [u₁₅.sp, u₁₄.sp, x₁₃.sp], ?_⟩
    · rw [u₁₅.other _ h4, u₁₄.other _ h3, x₁₃.keep r h1 h2]
    have e₁₀ : s₁₅.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) := by
      rw [u₁₅.other _ (by decide), u₁₄.gpr, x₁₃.keep _ (by decide) (by decide), hp.r10]
      rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2
    have e₁₁ : s₁₅.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1)) := by
      rw [u₁₅.gpr, u₁₄.other _ (by decide), x₁₃.keep _ (by decide) (by decide), hp.r11]
      bv_omega
    have d : DataInv m₀ s₁₅.mem (State.addr Dp) n (8 * (g + 1)) ks := by
      rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.data
    by_cases hl : n - 2 * g = 2
    · refine .inl ⟨by rw [e₁₁, show n - 2 * (g + 1) = 0 by omega]; rfl,
        dataInv_mono d (by omega) (by omega)⟩
    · exact .inr ⟨by omega, d, e₁₀, e₁₁⟩
  · -- The last block.
    have h1 : n - 2 * g = 1 := by simp at hb; omega
    rw [xorTail_eq]
    simp only [List.append_assoc]
    refine xs_step hp (k := 0) (by omega) (by omega) x₀ fun s₆ x₆ => ?_
    refine xs_step hp (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine xs_step hp (k := 2) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    refine xs_step hp (k := 3) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ =>
      WP.block_nil ⟨by rw [u₁₀.mem]; exact x₉.frame, fun r h1 h2 _ h4 => ?_,
        by rw [u₁₀.rd, x₉.rd], by rw [u₁₀.wr, x₉.wr], by rw [u₁₀.sp, x₉.sp],
        .inl ⟨u₁₀.gpr, ?_⟩⟩
    · rw [u₁₀.other _ h4, x₉.keep r h1 h2]
    · rw [u₁₀.mem]; exact dataInv_mono x₉.data (by omega) (by omega)

end Xor

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `Dp` the data (`n` blocks, whose
bytes were `m₀`'s), `icb` the first counter block. -/
structure GSetup (s₂ : State) (b Dp : BitVec 32) (n R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) :
    Prop where
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s₂.wr
  fit : b.toNat + 2048 ≤ 2 ^ 32
  dat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s₂.wr
  fitD : Dp.toNat + 16 * n ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w
  words : ∀ k < 3, ∀ t < 4, ∀ j < 8,
    (cwW s₂.mem (State.addr b) k).getLsbD (8 * t + j) = icb.getLsbD (8 * (15 - (4 * k + t)) + j)

/-- The memory a group writes: the S-box's slots, slots 44–47 and the data. -/
abbrev gRegions (B D : Addr) (n : Nat) : List Region :=
  [⟨B, 128⟩, ⟨B + BitVec.ofNat 64 176, 16⟩, ⟨D, 16 * n⟩]

/-- Before group `g`. -/
structure GInv (m₀ : Mem) (s₂ : State) (b Dp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (g : Nat) (s : State) : Prop where
  hg : 2 * g < n
  r10 : s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  r12 : s.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R)
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s.mem
  num : numW s.mem (State.addr b) = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g)
  data : DataInv m₀ s.mem (State.addr Dp) n (8 * g) (keyStream R w icb)

/-- After the last group. -/
structure GDone (m₀ : Mem) (s₂ : State) (b Dp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (s : State) : Prop where
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s.mem
  data : DataInv m₀ s.mem (State.addr Dp) n (4 * n) (keyStream R w icb)

theorem scr_disj (B : Addr) {lx y ly : Nat} (h : lx ≤ y) (hy : y + ly ≤ 2048) :
    Region.Disjoint ⟨B, lx⟩ ⟨B + BitVec.ofNat 64 y, ly⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have : (BitVec.ofNat 64 y).toNat = y := by simp; omega
  bv_omega

theorem scr_sub (B : Addr) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Sub ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B, 2048⟩ := by
  intro a h₁
  simp only [Region.Contains] at h₁ ⊢
  have : (BitVec.ofNat 64 x).toNat = x := by simp; omega
  bv_omega

theorem keysAt_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {R : Nat}
    {w : List Byte} {rs : List Region} (hR : R ≤ 14) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr b + 1024, 1024⟩ r)
    (h : KeysAt m (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w) :
    KeysAt m' (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w :=
  fun j hj => keyRel_congr (h j hj) fun k hk => hf.readW (key_contains hfit hR hj hk) hd (by decide)

theorem dataInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInv m₀ m D n k ks) : DataInv m₀ m' D n k ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega) hi

theorem front_frame (m : Mem) (B : Addr) (d l f : BitVec 32) :
    Frame [⟨B + BitVec.ofNat 64 176, 16⟩] m (frontMem m B d l f) := by
  have c : ∀ k, 44 ≤ k → k < 48 →
      (⟨B + BitVec.ofNat 64 176, 16⟩ : Region).Contains (slotA B k) (32 / 8) := by
    intro k h1 h2
    simp only [Region.Contains, slotA]
    rw [show B + BitVec.ofNat 64 (4 * k) - (B + BitVec.ofNat 64 176) = BitVec.ofNat 64 (4 * k - 176) by
      bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  exact ((((Frame.refl _ m).writeW (List.mem_singleton_self _) _ (c 45 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (c 46 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (c 47 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (c 44 (by omega) (by omega))

theorem front_read (m : Mem) (B : Addr) (d l f : BitVec 32) :
    (frontMem m B d l f).readW (slotA B dSlot) 32 = d ∧
      (frontMem m B d l f).readW (slotA B lSlot) 32 = l ∧
      (frontMem m B d l f).readW (slotA B fkSlot) 32 = f ∧
      numW (frontMem m B d l f) B = numW m B + 2 := by
  simp only [frontMem, numW]
  refine ⟨?_, ?_, ?_, Mem.readW_writeW_self32 _ _ _⟩
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

theorem slot_disj_regions {b Dp : BitVec 32} {n : Nat}
    (hsep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩) {x lx : Nat}
    (h1 : 128 ≤ x) (h2 : x + lx ≤ 176 ∨ 192 ≤ x) (h3 : x + lx ≤ 2048) :
    ∀ r ∈ gRegions (State.addr b) (State.addr Dp) n,
      Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 x, lx⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (scr_disj _ h1 h3).symm
  · exact off_disjoint _ (by omega) (by omega) (by omega)
  · exact (hsep.sub_right (scr_sub _ h3)).symm

theorem keys_disj_regions {b Dp : BitVec 32} {n : Nat}
    (hsep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩) :
    ∀ r ∈ gRegions (State.addr b) (State.addr Dp) n,
      Region.Disjoint ⟨State.addr b + 1024, 1024⟩ r :=
  slot_disj_regions hsep (x := 1024) (lx := 1024) (by omega) (by omega) (by omega)

/-- One group: from before group `g`, to after the last group or before
group `g + 1`. -/
theorem group_ok {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup s₂ b Dp n R w icb) {g : Nat} {s : State}
    (hi : GInv m₀ s₂ b Dp n R w icb g s) :
    WP isa group s fun s' => (Arm.eval .ne s' = some false ∧ GDone m₀ s₂ b Dp n R w icb s') ∨
      (Arm.eval .ne s' = some true ∧ GInv m₀ s₂ b Dp n R w icb (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hfit := hs.fit
  have hfitD := hs.fitD
  have hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  unfold group
  refine WP.seq (front_wp hi.base hscr hfit fun s₁ hq₁ hkp₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_)
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hi.base
  have f₁ : Frame [⟨State.addr b + BitVec.ofNat 64 176, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact front_frame _ _ _ _ _
  have hf₁ : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  have hcw : ∀ k < 3, cwW s.mem (State.addr b) k = cwW s₂.mem (State.addr b) k := fun k hk =>
    hi.frame.readW (Region.contains_self _ _)
      (slot_disj_regions hs.sep (by simp [cW]; omega) (by simp [cW]; omega) (by simp [cW]; omega))
      (by decide)
  have hp : EncPre s₁ R w :=
    ⟨by rw [hb₁, wr₁, hi.wr]; exact hs.scr, by rw [hb₁]; exact hfit, hs.rounds,
      by rw [hkp₁, hi.r12, hb₁],
      by rw [hkp₁, hi.r12]; exact keysAt_frame hfit hR hf₁ (keys_disj_regions hs.sep) hs.keys⟩
  have hin : InRel (Q s₁) (fun bb => ctrState icb (2 * g + bb)) :=
    ctr_inRel (W := fun k => cwW s.mem (State.addr b) k)
      (fun k hk => by rw [hcw k hk]; exact hs.words k hk) hi.num
      (fun bb hbb => ⟨fun k hk => (hq₁ bb hbb).1 k hk, (hq₁ bb hbb).2⟩)
  refine WP.seq (WP.mono (encrypt2_ok hp hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₁] at fr₃
  have hb₃ : s₃.gpr sb = b := hc₃.base.trans hb₁
  have hscr₃ : (⟨State.addr b, 2048⟩ : Region) ∈ s₃.wr := by rw [hc₃.wr, wr₁]; exact hscr
  have mslot : ∀ k, 45 ≤ k → k < 48 → s₃.mem.readW (slotA (State.addr b) k) 32 =
      s₁.mem.readW (slotA (State.addr b) k) 32 := fun k h1 h2 =>
    fr₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (scr_disj _ (by omega) (by omega)).symm)
      (by decide)
  obtain ⟨rd10, rd11, rd12, rnum⟩ := front_read s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11)
    (s.gpr .r12)
  refine WP.seq ?_
  simp only [groupLoad, List.cons_append, List.nil_append]
  refine wp_ldS hb₃ hscr₃ hfit (by decide) fun s₄ u₄ => ?_
  refine wp_ldS (by rw [u₄.other _ (by decide), hb₃]) (by rw [u₄.wr]; exact hscr₃) hfit (by decide)
    fun s₅ u₅ => ?_
  refine wp_ldS (by rw [u₅.other _ (by decide), u₄.other _ (by decide), hb₃])
    (by rw [u₅.wr, u₄.wr]; exact hscr₃) hfit (by decide) fun s₆ u₆ => ?_
  have e10 : s₆.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, mslot dSlot (by decide) (by decide), m₁,
      rd10, hi.r10]
  have e11 : s₆.gpr .r11 = BitVec.ofNat 32 (n - 2 * g) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, mslot lSlot (by decide) (by decide), m₁, rd11, hi.r11]
  have e12 : s₆.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [u₆.gpr, u₅.mem, u₄.mem, mslot fkSlot (by decide) (by decide), m₁, rd12, hi.r12]
  have mm₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have gq₆ : ∀ i < 8, s₆.gpr (q i) = s₃.gpr (q i) := fun i hi' => by
    have : q i ≠ .r10 ∧ q i ≠ .r11 ∧ q i ≠ .r12 := by revert hi'; revert i; decide
    rw [u₆.other _ this.2.2, u₅.other _ this.2.1, u₄.other _ this.1]
  have d384 : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 128⟩ :=
    hs.sep.sub_right (Region.sub_prefix (by omega))
  have hx : XPre m₀ Dp n g (keyStream R w icb) s₆ :=
    { hg := hi.hg, fit := hfitD, dat := by rw [u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₁, hi.wr]; exact hs.dat
      r10 := e10, r11 := e11
      data := by
        rw [mm₆]
        refine dataInv_frame fr₃ (by simpa using d384) (by omega)
          (dataInv_frame f₁ (by simpa using hs.sep.sub_right (scr_sub _ (by omega))) (by omega) hi.data)
      ks := fun k hk t ht => by rw [gq₆ _ (by omega)]; exact ks_of_inRel hin₃ hk ht }
  refine WP.mono (xorPhase_wp hx) fun s₇ h₇ => WP.seq (WP.mono h₇ fun s₈ hd₈ => ?_)
  obtain ⟨f₈, o₈, rd₈, wr₈, sp₈, hz⟩ := hd₈
  refine wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  have keep : ∀ r, r ∉ layerWrites → r ≠ kp → s₉.gpr r = s.gpr r := by
    intro r h1 h2
    have : r ≠ .lr ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert h1 h2; cases r <;> decide
    rw [f₉.gpr, o₈ r this.1 h2 this.2.1 this.2.2.1, u₆.other _ this.2.2.2, u₅.other _ this.2.2.1,
      u₄.other _ this.2.1, hc₃.keep r h1 h2, o₁ r h1 h2]
  have base' : s₉.gpr sb = b := (keep sb (by decide) (by decide)).trans hi.base
  have rd' : s₉.rd = s₂.rd := by rw [f₉.rd, rd₈, u₆.rd, u₅.rd, u₄.rd, hc₃.rd, rd₁, hi.rd]
  have wr' : s₉.wr = s₂.wr := by rw [f₉.wr, wr₈, u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₁, hi.wr]
  have sp' : s₉.sp = s₂.sp := by rw [f₉.sp, sp₈, u₆.sp, u₅.sp, u₄.sp, hc₃.sp, sp₁, hi.sp]
  have frame' : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₉.mem := by
    rw [f₉.mem]
    refine hf₁.trans ((fr₃.mono fun r hr => by simp at hr; simp [hr]).trans ?_)
    rw [← mm₆]
    exact f₈.mono fun r hr => by simp at hr; simp [hr]
  have ev : Arm.eval .ne s₉ = some (!(s₈.gpr .r11 == 0)) := by
    have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    simp only [Arm.eval, z₉, e0]
  rcases hz with ⟨z, d⟩ | ⟨h4, d, x10, x11⟩
  · exact .inl ⟨by rw [ev, z]; rfl, base', rd', wr', sp', frame', by rw [f₉.mem]; exact d⟩
  · refine .inr ⟨?_, ⟨by omega, by rw [f₉.gpr]; exact x10, by rw [f₉.gpr]; exact x11,
      by rw [f₉.gpr, o₈ _ (by decide) (by decide) (by decide) (by decide), e12], base', rd', wr', sp',
      frame', ?_, by rw [f₉.mem]; exact d⟩⟩
    · have hne : BitVec.ofNat 32 (n - 2 * (g + 1)) ≠ 0 := by
        intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
      rw [ev, x11]; simpa using hne
    · have e₁ : numW s₈.mem (State.addr b) = numW s₆.mem (State.addr b) :=
        f₈.readW (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hs.sep.sub_right (scr_sub (x := 176) (lx := 4) _ (by decide))).symm) (by decide)
      rw [f₉.mem]
      have e₂ : numW s₃.mem (State.addr b) = numW s₁.mem (State.addr b) :=
        fr₃.readW (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (scr_disj (lx := 128) (y := 176) (ly := 4) _ (by omega) (by omega)).symm) (by decide)
      rw [e₁, mm₆, e₂, m₁, rnum, hi.num, BitVec.add_assoc]
      congr 1
      bv_omega

/-- The loop over the groups. -/
theorem groups_ok {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup s₂ b Dp n R w icb) {s : State}
    (hi : GInv m₀ s₂ b Dp n R w icb 0 s) :
    WP isa (.loop group .ne) s (GDone m₀ s₂ b Dp n R w icb) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ GInv m₀ s₂ b Dp n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (group_ok hs hg) fun s' h => ?_) n s ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 2 * (g + 1), by have := hg.hg; omega, g + 1, rfl, d⟩

end VG.Proof.Aes.Arm
