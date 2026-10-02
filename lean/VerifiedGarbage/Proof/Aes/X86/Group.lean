import VerifiedGarbage.Proof.Aes.X86.Keys
import VerifiedGarbage.Proof.Aes.Blocks
import Mathlib.Tactic.SplitIfs

/-!
# One group of counter-mode blocks on x86 (32-bit)

`ctrBlocks` builds the counter blocks `c` and `c + 1` from the words of the
counter block in the scratch buffer (`ctrBlocks_wp`, then `ctr_inRel` for
`InRel`), `encrypt2` encrypts them (`Encrypt.lean`), and `xorGroup` XORs the
keystream into the data, a word at a time.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_addm wp_sub wp_subi wp_cmp wp_cmpi wp_test
  wp_bswap wp_ldm wp_xorm wp_stm sub_beq sub_ofNat toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-! ## Words of the scratch buffer -/

/-! ## The counter blocks -/

/-- The words of the counter block in the scratch buffer at `B`. -/
abbrev cw (m : Mem) (B : BitVec 32) (w : Nat) : BitVec 32 := m.readW (addr B (cwOff w)) 32
abbrev cnum (m : Mem) (B : BitVec 32) : BitVec 32 := m.readW (addr B cNum) 32

/-- What `ctrBlocks` leaves in slot `k`. -/
def ctrSlot (m : Mem) (B : BitVec 32) (k : Nat) : BitVec 32 :=
  if k < 6 then cw m B (k / 2) else bswap (cnum m B + BitVec.ofNat 32 (k - 6))

theorem ctrBlocks_eq : ctrBlocks = ([
    .mov .eax (.mem (at_ .edi 272)), .store (at_ .edi 0) .eax,
    .mov .eax (.mem (at_ .edi 276)), .store (at_ .edi 8) .eax,
    .mov .eax (.mem (at_ .edi 280)), .store (at_ .edi 16) .eax,
    .mov .eax (.mem (at_ .edi 284)), .alu .add .eax (.imm 0), .bswap .eax, .store (at_ .edi 24) .eax,
    .mov .eax (.mem (at_ .edi 272)), .store (at_ .edi 4) .eax,
    .mov .eax (.mem (at_ .edi 276)), .store (at_ .edi 12) .eax,
    .mov .eax (.mem (at_ .edi 280)), .store (at_ .edi 20) .eax,
    .mov .eax (.mem (at_ .edi 284)), .alu .add .eax (.imm 1), .bswap .eax, .store (at_ .edi 28) .eax,
    .mov .eax (.mem (at_ .edi 284)), .alu .add .eax (.imm 2), .store (at_ .edi 284) .eax] :
    List Instr) := rfl

/-- The two counter blocks. -/
theorem ctrBlocks_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hfit : B.toNat + 2048 ≤ 2 ^ 32)
    (hw : reg32 B 2048 ∈ s.wr) {P : State → Prop}
    (h : ∀ s', (∀ k < 8, Q s' k = ctrSlot s.mem B k) → cnum s'.mem B = cnum s.mem B + 2 →
      Frame [reg32 B 32, ⟨addr B cNum, 4⟩] s.mem s'.mem →
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block ctrBlocks) s P := by
  rw [ctrBlocks_eq]
  have hin : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hw hfit ho (by decide)
  have hrd : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ o, o + 4 ≤ 2048 →
      InRegions (t.rd ++ t.wr) (addr B o) 4 :=
    fun t h1 h2 o ho => in_rd (hin t h2 o ho)
  refine wp_ldm hb (hrd _ rfl rfl 272 (by omega)) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .edi = B := (u₁.other _ (by decide)).trans hb
  refine wp_stm b₁ (hin _ u₁.wr 0 (by omega)) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .edi = B := by rw [u₂.gpr]; exact b₁
  refine wp_ldm b₂ (hrd _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 276 (by omega)) fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .edi = B := (u₃.other _ (by decide)).trans b₂
  refine wp_stm b₃ (hin _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 8 (by omega)) fun s₄ u₄ => ?_
  have b₄ : s₄.gpr .edi = B := by rw [u₄.gpr]; exact b₃
  refine wp_ldm b₄ (hrd _ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    280 (by omega)) fun s₅ u₅ => ?_
  have b₅ : s₅.gpr .edi = B := (u₅.other _ (by decide)).trans b₄
  refine wp_stm b₅ (hin _ (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 16 (by omega)) fun s₆ u₆ => ?_
  have b₆ : s₆.gpr .edi = B := by rw [u₆.gpr]; exact b₅
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_ldm b₆ (hrd _ rd₆ wr₆ 284 (by omega)) fun s₇ u₇ => ?_
  refine wp_addi fun s₈ u₈ => wp_bswap fun s₉ u₉ => ?_
  have b₉ : s₉.gpr .edi = B := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide)]; exact b₆
  have rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆]
  have wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆]
  refine wp_stm b₉ (hin _ wr₉ 24 (by omega)) fun s₁₀ u₁₀ => ?_
  have b₁₀ : s₁₀.gpr .edi = B := by rw [u₁₀.gpr]; exact b₉
  refine wp_ldm b₁₀ (hrd _ (by rw [u₁₀.rd, rd₉]) (by rw [u₁₀.wr, wr₉]) 272 (by omega)) fun s₁₁ u₁₁ => ?_
  have b₁₁ : s₁₁.gpr .edi = B := (u₁₁.other _ (by decide)).trans b₁₀
  refine wp_stm b₁₁ (hin _ (by rw [u₁₁.wr, u₁₀.wr, wr₉]) 4 (by omega)) fun s₁₂ u₁₂ => ?_
  have b₁₂ : s₁₂.gpr .edi = B := by rw [u₁₂.gpr]; exact b₁₁
  have rd₁₂ : s₁₂.rd = s.rd := by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, rd₉]
  have wr₁₂ : s₁₂.wr = s.wr := by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉]
  refine wp_ldm b₁₂ (hrd _ rd₁₂ wr₁₂ 276 (by omega)) fun s₁₃ u₁₃ => ?_
  have b₁₃ : s₁₃.gpr .edi = B := (u₁₃.other _ (by decide)).trans b₁₂
  refine wp_stm b₁₃ (hin _ (by rw [u₁₃.wr, wr₁₂]) 12 (by omega)) fun s₁₄ u₁₄ => ?_
  have b₁₄ : s₁₄.gpr .edi = B := by rw [u₁₄.gpr]; exact b₁₃
  refine wp_ldm b₁₄ (hrd _ (by rw [u₁₄.rd, u₁₃.rd, rd₁₂]) (by rw [u₁₄.wr, u₁₃.wr, wr₁₂]) 280 (by omega))
    fun s₁₅ u₁₅ => ?_
  have b₁₅ : s₁₅.gpr .edi = B := (u₁₅.other _ (by decide)).trans b₁₄
  refine wp_stm b₁₅ (hin _ (by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, wr₁₂]) 20 (by omega)) fun s₁₆ u₁₆ => ?_
  have b₁₆ : s₁₆.gpr .edi = B := by rw [u₁₆.gpr]; exact b₁₅
  have rd₁₆ : s₁₆.rd = s.rd := by rw [u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, rd₁₂]
  have wr₁₆ : s₁₆.wr = s.wr := by rw [u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, wr₁₂]
  refine wp_ldm b₁₆ (hrd _ rd₁₆ wr₁₆ 284 (by omega)) fun s₁₇ u₁₇ => ?_
  refine wp_addi fun s₁₈ u₁₈ => wp_bswap fun s₁₉ u₁₉ => ?_
  have b₁₉ : s₁₉.gpr .edi = B := by
    rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide)]; exact b₁₆
  have rd₁₉ : s₁₉.rd = s.rd := by rw [u₁₉.rd, u₁₈.rd, u₁₇.rd, rd₁₆]
  have wr₁₉ : s₁₉.wr = s.wr := by rw [u₁₉.wr, u₁₈.wr, u₁₇.wr, wr₁₆]
  refine wp_stm b₁₉ (hin _ wr₁₉ 28 (by omega)) fun s₂₀ u₂₀ => ?_
  have b₂₀ : s₂₀.gpr .edi = B := by rw [u₂₀.gpr]; exact b₁₉
  refine wp_ldm b₂₀ (hrd _ (by rw [u₂₀.rd, rd₁₉]) (by rw [u₂₀.wr, wr₁₉]) 284 (by omega))
    fun s₂₁ u₂₁ => wp_addi fun s₂₂ u₂₂ => ?_
  have b₂₂ : s₂₂.gpr .edi = B := by rw [u₂₂.other _ (by decide), u₂₁.other _ (by decide)]; exact b₂₀
  refine wp_stm b₂₂ (hin _ (by rw [u₂₂.wr, u₂₁.wr, u₂₀.wr, wr₁₉]) 284 (by omega)) fun s₂₃ u₂₃ =>
    WP.block_nil ?_
  -- The memory, store by store.
  let c : BitVec 32 := s.mem.readW (addr B 284) 32
  let M₂ := s.mem.writeW (addr B 0) (s.mem.readW (addr B 272) 32)
  let M₄ := M₂.writeW (addr B 8) (s.mem.readW (addr B 276) 32)
  let M₆ := M₄.writeW (addr B 16) (s.mem.readW (addr B 280) 32)
  let M₁₀ := M₆.writeW (addr B 24) (bswap (c + 0))
  let M₁₂ := M₁₀.writeW (addr B 4) (s.mem.readW (addr B 272) 32)
  let M₁₄ := M₁₂.writeW (addr B 12) (s.mem.readW (addr B 276) 32)
  let M₁₆ := M₁₄.writeW (addr B 20) (s.mem.readW (addr B 280) 32)
  let M₂₀ := M₁₆.writeW (addr B 28) (bswap (c + 1))
  let M₂₃ := M₂₀.writeW (addr B 284) (c + 2)
  have m₂ : s₂.mem = M₂ := by rw [u₂.mem, u₁.gpr, u₁.mem]
  have m₄ : s₄.mem = M₄ := by
    rw [u₄.mem, u₃.gpr, u₃.mem, m₂]
    simp (disch := decide) only [M₄, M₂, rd_wr_ne hfit]
  have m₆ : s₆.mem = M₆ := by
    rw [u₆.mem, u₅.gpr, u₅.mem, m₄]
    simp (disch := decide) only [M₆, M₄, M₂, rd_wr_ne hfit]
  have m₁₀ : s₁₀.mem = M₁₀ := by
    rw [u₁₀.mem, u₉.gpr, u₈.gpr, u₇.gpr, u₉.mem, u₈.mem, u₇.mem, m₆]
    simp (disch := decide) only [M₁₀, M₆, M₄, M₂, rd_wr_ne hfit]; rfl
  have m₁₂ : s₁₂.mem = M₁₂ := by
    rw [u₁₂.mem, u₁₁.gpr, u₁₁.mem, m₁₀]
    simp (disch := decide) only [M₁₂, M₁₀, M₆, M₄, M₂, rd_wr_ne hfit]
  have m₁₄ : s₁₄.mem = M₁₄ := by
    rw [u₁₄.mem, u₁₃.gpr, u₁₃.mem, m₁₂]
    simp (disch := decide) only [M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, rd_wr_ne hfit]
  have m₁₆ : s₁₆.mem = M₁₆ := by
    rw [u₁₆.mem, u₁₅.gpr, u₁₅.mem, m₁₄]
    simp (disch := decide) only [M₁₆, M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, rd_wr_ne hfit]
  have m₂₀ : s₂₀.mem = M₂₀ := by
    rw [u₂₀.mem, u₁₉.gpr, u₁₈.gpr, u₁₇.gpr, u₁₉.mem, u₁₈.mem, u₁₇.mem, m₁₆]
    simp (disch := decide) only [M₂₀, M₁₆, M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, rd_wr_ne hfit]; rfl
  have m₂₃ : s₂₃.mem = M₂₃ := by
    rw [u₂₃.mem, u₂₂.gpr, u₂₁.gpr, u₂₂.mem, u₂₁.mem, m₂₀]
    simp (disch := decide) only [M₂₃, M₂₀, M₁₆, M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, rd_wr_ne hfit]; rfl
  have b₂₃ : s₂₃.gpr .edi = B := by rw [u₂₃.gpr]; exact b₂₂
  refine h s₂₃ (fun k hk => ?_) ?_ ?_ (fun r hr => ?_) ?_ ?_
  · have e : Q s₂₃ k = M₂₃.readW (addr B (4 * k)) 32 := by
      simp only [Q, wordAddr]; rw [show s₂₃.gpr sb = B from b₂₃, m₂₃]
    rw [e]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [M₂₃, M₂₀, M₁₆, M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, rd_wr_ne hfit,
      Mem.readW_writeW_self32, ctrSlot, cw, cnum, cwOff, cNum, c] <;> rfl
  · simp only [cnum, cNum, m₂₃, M₂₃, Mem.readW_writeW_self32, c]
  · rw [m₂₃]
    have c32 : ∀ o, o + 4 ≤ 32 → (reg32 B 32).Contains (addr B o) (32 / 8) :=
      fun o ho => reg_contains (by omega) ho (by decide)
    have m1 : reg32 B 32 ∈ [reg32 B 32, ⟨addr B cNum, 4⟩] := by simp
    have m2 : (⟨addr B cNum, 4⟩ : Region) ∈ [reg32 B 32, ⟨addr B cNum, 4⟩] := by simp
    exact (((((((((Frame.refl _ _).writeW m1 _ (c32 0 (by omega))).writeW m1 _ (c32 8 (by omega))).writeW
      m1 _ (c32 16 (by omega))).writeW m1 _ (c32 24 (by omega))).writeW m1 _ (c32 4 (by omega))).writeW
      m1 _ (c32 12 (by omega))).writeW m1 _ (c32 20 (by omega))).writeW m1 _ (c32 28 (by omega))).writeW
      m2 _ (Region.contains_self _ _)
  · simp only [u₂₃.gpr, u₂₂.other r hr, u₂₁.other r hr, u₂₀.gpr, u₁₉.other r hr, u₁₈.other r hr,
      u₁₇.other r hr, u₁₆.gpr, u₁₅.other r hr, u₁₄.gpr, u₁₃.other r hr, u₁₂.gpr, u₁₁.other r hr,
      u₁₀.gpr, u₉.other r hr, u₈.other r hr, u₇.other r hr, u₆.gpr, u₅.other r hr, u₄.gpr,
      u₃.other r hr, u₂.gpr, u₁.other r hr]
  · rw [u₂₃.rd, u₂₂.rd, u₂₁.rd, u₂₀.rd, rd₁₉]
  · rw [u₂₃.wr, u₂₂.wr, u₂₁.wr, u₂₀.wr, wr₁₉]

/-! ## The counter blocks as states -/

/-- The counter blocks `2g` and `2g + 1` in the slots, as `InRel` has them. -/
theorem ctr_inRel {Q' : Nat → BitVec 32} {m : Mem} {B : BitVec 32} {icb : Spec.Gcm.Block} {g : Nat}
    (hq : ∀ k < 8, Q' k = ctrSlot m B k)
    (hcw : ∀ w < 3, ∀ i < 4, ∀ j < 8, (cw m B w).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - (4 * w + i)) + j))
    (hnum : cnum m B = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g)) :
    InRel Q' (fun b => ctrState icb (2 * g + b)) := by
  intro b hb i hi16 j hj
  simp only [ctrState, getD_eq _ hi16, Vector.getElem_ofFn]
  rw [ctrBlock_byte _ _ hi16, hq _ (by omega)]
  unfold ctrSlot
  by_cases h12 : i < 12
  · rw [ite_eq_left (by omega), ite_eq_left h12, toBytes_getD _ hi16, BitVec.getLsbD_extractLsb',
      show (b + 2 * (i / 4)) / 2 = i / 4 by omega, hcw (i / 4) (by omega) (i % 4) (by omega) j hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega
  · rw [ite_eq_right (by omega), ite_eq_right h12, show b + 2 * (i / 4) - 6 = b by omega,
      show 8 * (i % 4) + j = 8 * (i % 4) + j from rfl, bswap_bit _ (by omega) hj, hnum,
      BitVec.getLsbD_extractLsb', BitVec.add_assoc, ← BitVec.ofNat_add]
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

/-- The data after `d` bytes: the keystream `ks` XORed into the first `d`
of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n d : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < d then ks i else 0)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := by
  split <;> bv_omega

/-- One word of keystream XORed in. -/
theorem dataInv_word {m₀ m : Mem} {D : Addr} {n d : Nat} {ks : Nat → Byte} {v : BitVec 32}
    (hn : 16 * n < 2 ^ 64) (hd : d + 4 ≤ 16 * n) (h : DataInv m₀ m D n d ks)
    (hks : ∀ t < 4, v.extractLsb' (8 * t) 8 = ks (d + t)) :
    DataInv m₀ (xorW m (D + BitVec.ofNat 64 d) v) D n (d + 4) ks ∧
      Frame [⟨D, 16 * n⟩] m (xorW m (D + BitVec.ofNat 64 d) v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [xorW_apply, off_toNat D (by omega) (by omega), h i hi]
    by_cases h1 : d ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - d < 4
      · rw [ite_eq_left h2, hks _ h2, ite_eq_right (show ¬ i < d by omega),
          ite_eq_left (show i < d + 4 by omega), show d + (i - d) = i by omega]
        simp
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < d by omega),
          ite_eq_right (show ¬ i < d + 4 by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - d < 4 by omega),
        ite_eq_left (show i < d by omega), ite_eq_left (show i < d + 4 by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx _ (List.mem_singleton_self _)
    rw [xorW_apply, ite_eq_right]
    have : (BitVec.ofNat 64 d).toNat = d := by simp; omega
    bv_omega

theorem dataInv_frame {m₀ m m' : Mem} {D : Addr} {n d : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInv m₀ m D n d ks) : DataInv m₀ m' D n d ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega) hi

theorem dataInv_mono {m₀ m : Mem} {D : Addr} {n d d' : Nat} {ks : Nat → Byte}
    (h : DataInv m₀ m D n d ks) (hd : 16 * n ≤ d) (hd' : 16 * n ≤ d') : DataInv m₀ m D n d' ks := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < d by omega), ite_eq_left (show i < d' by omega)]

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

theorem ks_of_inRel {Q' : Nat → BitVec 32} {R g : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : InRel Q' (fun b => Spec.Aes.cipher R w (ctrState icb (2 * g + b)))) {b k t : Nat} (hb : b < 2)
    (hk : k < 4) (ht : t < 4) :
    (Q' (2 * k + b)).extractLsb' (8 * t) 8 = keyStream R w icb (16 * (2 * g + b) + 4 * k + t) := by
  apply byte_ext
  intro j hj
  have := h b hb (4 * k + t) (by omega) j hj
  rw [show b + 2 * ((4 * k + t) / 4) = 2 * k + b by omega, show (4 * k + t) % 4 = t by omega] at this
  rw [BitVec.getLsbD_extractLsb', this, keyStream,
    show (16 * (2 * g + b) + 4 * k + t) / 16 = 2 * g + b by omega,
    show (16 * (2 * g + b) + 4 * k + t) % 16 = 4 * k + t by omega]
  simp [hj]

/-- XOR word `k` of keystream block `b` into the data at `esi`. -/
def xw (b k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (16 * b + 4 * k))), xorS .eax (2 * k + b), .store (at_ .esi (16 * b + 4 * k)) .eax]

theorem xorBlock_eq (b : Nat) : xorBlock b = xw b 0 ++ (xw b 1 ++ (xw b 2 ++ xw b 3)) := by
  simp [xorBlock, xw, List.range, List.range.loop]

/-- The buffers the XOR phase uses. -/
structure XBufs (Dp B : BitVec 32) (n : Nat) (s : State) : Prop where
  fitD : Dp.toNat + 16 * n ≤ 2 ^ 32
  dat : reg32 Dp (16 * n) ∈ s.wr
  fitB : B.toNat + 2048 ≤ 2 ^ 32
  scr : reg32 B 2048 ∈ s.wr
  sep : (reg32 Dp (16 * n)).Disjoint (reg32 B 2048)

theorem XBufs.congr {Dp B : BitVec 32} {n : Nat} {s s' : State} (h : XBufs Dp B n s) (hwr : s'.wr = s.wr) :
    XBufs Dp B n s' := ⟨h.fitD, hwr ▸ h.dat, h.fitB, hwr ▸ h.scr, h.sep⟩

theorem xorWord_wp {s : State} {Dp B : BitVec 32} {n g b k : Nat} {m₀ : Mem} {ks : Nat → Byte}
    {rest : List Instr} {P : State → Prop} (hbuf : XBufs Dp B n s) (hb : b < 2) (hk : k < 4)
    (hn : 2 * g + b < n) (hesi : s.gpr .esi = Dp + BitVec.ofNat 32 (32 * g)) (hedi : s.gpr .edi = B)
    (hinv : DataInv m₀ s.mem (Dp.setWidth 64) n (16 * (2 * g + b) + 4 * k) ks)
    (hks : ∀ t < 4, (Q s (2 * k + b)).extractLsb' (8 * t) 8 = ks (16 * (2 * g + b) + 4 * k + t))
    (h : ∀ s', DataInv m₀ s'.mem (Dp.setWidth 64) n (16 * (2 * g + b) + 4 * k + 4) ks →
      Frame [reg32 Dp (16 * n)] s.mem s'.mem → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' P) :
    WP isa (.block (xw b k ++ rest)) s P := by
  have hfit := hbuf.fitD
  have ea : addr (Dp + BitVec.ofNat 32 (32 * g)) (16 * b + 4 * k) =
      Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g + b) + 4 * k) := by
    rw [addr_add, show 32 * g + (16 * b + 4 * k) = 16 * (2 * g + b) + 4 * k by omega]
    exact addr_eq (by omega)
  have hin : InRegions s.wr (addr (Dp + BitVec.ofNat 32 (32 * g)) (16 * b + 4 * k)) 4 := by
    rw [addr_add]; exact in_reg hbuf.dat hfit (by omega) (by decide)
  simp only [xw, List.cons_append, List.nil_append]
  refine wp_ldm hesi (in_rd hin) fun s₁ u₁ => ?_
  refine wp_xorm (B := B) (o := 4 * (2 * k + b)) (by rw [u₁.other _ (by decide)]; exact hedi)
    (by rw [u₁.rd, u₁.wr]; exact in_rd (in_reg hbuf.scr hbuf.fitB (by omega) (by decide))) fun s₂ u₂ => ?_
  refine wp_stm (B := Dp + BitVec.ofNat 32 (32 * g))
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hesi)
    (by rw [u₂.wr, u₁.wr]; exact hin) fun s₃ u₃ => ?_
  have hm : s₃.mem = xorW s.mem (Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g + b) + 4 * k))
      (Q s (2 * k + b)) := by
    have e : Q s (2 * k + b) = s.mem.readW (addr B (4 * (2 * k + b))) 32 := by
      simp only [Q, wordAddr]; rw [show s.gpr sb = B from hedi]
    rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, ea, xorW, e]
  have hst := dataInv_word (v := Q s (2 * k + b)) (by omega) (by omega) hinv hks
  rw [← hm] at hst
  refine h s₃ hst.1 hst.2 (fun r hr => ?_) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
  rw [u₃.gpr, u₂.other r hr, u₁.other r hr]

/-! ## The XOR phase of a group -/

/-- Before the XOR phase of group `g`: the keystream is in the slots. -/
structure XPre (m₀ : Mem) (Dp B : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ : State) : Prop where
  buf : XBufs Dp B n s₃
  hg : 2 * g < n
  edi : s₃.gpr .edi = B
  dslot : s₃.mem.readW (addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * g)
  nslot : s₃.mem.readW (addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * g)
  data : DataInv m₀ s₃.mem (Dp.setWidth 64) n (32 * g) ks
  ks : ∀ b < 2, ∀ k < 4, ∀ t < 4,
    (Q s₃ (2 * k + b)).extractLsb' (8 * t) 8 = ks (16 * (2 * g + b) + 4 * k + t)

/-- After `k` words of the group have been XORed in, from `s₃`. -/
structure XS (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ : State) (k : Nat)
    (s : State) : Prop where
  data : DataInv m₀ s.mem (Dp.setWidth 64) n (32 * g + 4 * k) ks
  frame : Frame [reg32 Dp (16 * n)] s₃.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr

section Xor

variable {m₀ : Mem} {Dp B : BitVec 32} {n g : Nat} {ks : Nat → Byte} {s₃ : State}

theorem XPre.qsame (hp : XPre m₀ Dp B n g ks s₃) {k : Nat} {s : State} (hs : XS m₀ Dp n g ks s₃ k s) (j : Nat)
    (hj : j < 8) : Q s j = Q s₃ j := by
  simp only [Q, wordAddr, hs.keep sb (by decide), show s₃.gpr sb = B from hp.edi]
  refine hs.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact (hp.buf.sep.sub_right (part_sub_reg hp.buf.fitB (by omega))).symm

theorem xs_step (hp : XPre m₀ Dp B n g ks s₃) (hesi₃ : s₃.gpr .esi = Dp + BitVec.ofNat 32 (32 * g))
    {b k : Nat} (hb : b < 2) (hk : k < 4) (hn : 2 * g + b < n) {s : State} (hs : XS m₀ Dp n g ks s₃ (4 * b + k) s) {rest : List Instr}
    {P : State → Prop} (h : ∀ s', XS m₀ Dp n g ks s₃ (4 * b + k + 1) s' → WP isa (.block rest) s' P) :
    WP isa (.block (xw b k ++ rest)) s P := by
  have hesi : s.gpr .esi = s₃.gpr .esi := hs.keep _ (by decide)
  refine xorWord_wp (m₀ := m₀) (ks := ks) (hp.buf.congr hs.wr) hb hk hn (Dp := Dp) (g := g) ?_ ?_ ?_ ?_
    fun s' d f o rd wr => h s' ⟨?_, hs.frame.trans f, fun r hr => (o r hr).trans (hs.keep r hr),
      rd.trans hs.rd, wr.trans hs.wr⟩
  · rw [hesi, hesi₃]
  · rw [hs.keep _ (by decide)]; exact hp.edi
  · have := hs.data; rwa [show 32 * g + 4 * (4 * b + k) = 16 * (2 * g + b) + 4 * k by omega] at this
  · intro t ht; rw [hp.qsame hs _ (by omega)]; exact hp.ks b hb k hk t ht
  · rwa [show 32 * g + 4 * (4 * b + k + 1) = 16 * (2 * g + b) + 4 * k + 4 by omega]

theorem xorTwo_eq : xorTwo = xw 0 0 ++ (xw 0 1 ++ (xw 0 2 ++ (xw 0 3 ++ (xw 1 0 ++ (xw 1 1 ++
    (xw 1 2 ++ (xw 1 3 ++ ([addI .esi 32, subI .ebp 2] : List Instr)))))))) := by
  simp only [xorTwo, xorBlock_eq, List.append_assoc]

theorem xorOne_eq : xorOne = xw 0 0 ++ (xw 0 1 ++ (xw 0 2 ++ (xw 0 3 ++
    ([subR .ebp .ebp] : List Instr)))) := by
  simp only [xorOne, xorBlock_eq, List.append_assoc]

/-- Between the two parts of the XOR phase. -/
structure XMid (m₀ : Mem) (Dp B : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop where
  frame : Frame [reg32 Dp (16 * n)] s₃.mem s.mem
  keep : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  post : (s.gpr .ebp = 0 ∧ DataInv m₀ s.mem (Dp.setWidth 64) n (16 * n) ks) ∨
    (s.gpr .ebp = BitVec.ofNat 32 (n - 2 * (g + 1)) ∧ 0 < n - 2 * (g + 1) ∧
      s.gpr .esi = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      DataInv m₀ s.mem (Dp.setWidth 64) n (32 * (g + 1)) ks)

/-- After the XOR phase: ZF is set if no data is left. -/
structure XDone (m₀ : Mem) (Dp B : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop where
  frame : Frame [reg32 Dp (16 * n), ⟨addr B dOff, 8⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  post : (s.zf = some true ∧ DataInv m₀ s.mem (Dp.setWidth 64) n (16 * n) ks) ∨
    (s.zf = some false ∧ 2 * g + 2 < n ∧ DataInv m₀ s.mem (Dp.setWidth 64) n (32 * (g + 1)) ks ∧
      s.mem.readW (addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      s.mem.readW (addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * (g + 1)))

theorem XPre.congr (hp : XPre m₀ Dp B n g ks s₃) {s : State} (hm : s.mem = s₃.mem) (hwr : s.wr = s₃.wr)
    (he : s.gpr .edi = s₃.gpr .edi) : XPre m₀ Dp B n g ks s :=
  have hq : Q s = Q s₃ := Q_congr he hm
  ⟨hp.buf.congr hwr, hp.hg, he.trans hp.edi, hm ▸ hp.dslot, hm ▸ hp.nslot, hm ▸ hp.data,
    fun b hb k hk t ht => by rw [hq]; exact hp.ks b hb k hk t ht⟩

theorem xorGroup_wp (hp : XPre m₀ Dp B n g ks s₃) : WP isa xorGroup s₃ (XDone m₀ Dp B n g ks s₃) := by
  have hg := hp.hg
  have hfitD := hp.buf.fitD
  have hin : ∀ (t : State), t.wr = s₃.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hp.buf.scr hp.buf.fitB ho (by decide)
  unfold xorGroup
  refine WP.seq ?_
  refine wp_ldm (B := B) (o := dOff) hp.edi (in_rd (hin _ rfl _ (by decide))) fun s₄ u₄ => ?_
  refine wp_ldm (B := B) (o := nOff) (by rw [u₄.other _ (by decide)]; exact hp.edi)
    (by rw [u₄.rd, u₄.wr]; exact in_rd (hin _ rfl _ (by decide))) fun s₅ u₅ => ?_
  refine wp_cmpi fun s₆ u₆ hcf _ => WP.block_nil ?_
  have hm₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have hwr₆ : s₆.wr = s₃.wr := by rw [u₆.wr, u₅.wr, u₄.wr]
  have hrd₆ : s₆.rd = s₃.rd := by rw [u₆.rd, u₅.rd, u₄.rd]
  have g₆ : ∀ r, r ≠ .esi → r ≠ .ebp → s₆.gpr r = s₃.gpr r := fun r h1 h2 => by
    rw [u₆.gpr, u₅.other r h2, u₄.other r h1]
  have hesi₆ : s₆.gpr .esi = Dp + BitVec.ofNat 32 (32 * g) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, hp.dslot]
  have hebp₆ : s₆.gpr .ebp = BitVec.ofNat 32 (n - 2 * g) := by
    rw [u₆.gpr, u₅.gpr, u₄.mem, hp.nslot]
  have hp₆ : XPre m₀ Dp B n g ks s₆ := hp.congr hm₆ hwr₆ (g₆ _ (by decide) (by decide))
  have x₀ : XS m₀ Dp n g ks s₆ 0 s₆ := ⟨by simpa using hp₆.data, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  rw [u₅.gpr, u₄.mem, hp.nslot, toNat_ofNat_lt (by omega)] at hcf
  refine WP.seq (WP.mono (Q := XMid m₀ Dp B n g ks s₆) ?_ fun s hs => ?_)
  · refine WP.ite (!decide (n - 2 * g < (2 : BitVec 32).toNat)) (by simp [X86.eval, hcf])
      (fun hb => ?_) (fun hb => ?_)
    · -- Two blocks.
      have h2 : 2 ≤ n - 2 * g := by simpa using hb
      rw [xorTwo_eq]
      refine xs_step hp₆ hesi₆ (b := 0) (k := 0) (by omega) (by omega) (by omega) x₀ fun s₇ x₇ => ?_
      refine xs_step hp₆ hesi₆ (b := 0) (k := 1) (by omega) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
      refine xs_step hp₆ hesi₆ (b := 0) (k := 2) (by omega) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
      refine xs_step hp₆ hesi₆ (b := 0) (k := 3) (by omega) (by omega) (by omega) x₉ fun s₁₀ x₁₀ => ?_
      refine xs_step hp₆ hesi₆ (b := 1) (k := 0) (by omega) (by omega) (by omega) x₁₀ fun s₁₁ x₁₁ => ?_
      refine xs_step hp₆ hesi₆ (b := 1) (k := 1) (by omega) (by omega) (by omega) x₁₁ fun s₁₂ x₁₂ => ?_
      refine xs_step hp₆ hesi₆ (b := 1) (k := 2) (by omega) (by omega) (by omega) x₁₂ fun s₁₃ x₁₃ => ?_
      refine xs_step hp₆ hesi₆ (b := 1) (k := 3) (by omega) (by omega) (by omega) x₁₃ fun s₁₄ x₁₄ => ?_
      refine wp_addi fun s₁₅ u₁₅ => wp_subi fun s₁₆ u₁₆ _ _ => WP.block_nil ?_
      have hd : DataInv m₀ s₁₆.mem (Dp.setWidth 64) n (32 * (g + 1)) ks := by
        rw [u₁₆.mem, u₁₅.mem]; have := x₁₄.data; rwa [show 32 * g + 4 * (4 * 1 + 3 + 1) = 32 * (g + 1) by omega] at this
      refine ⟨by rw [u₁₆.mem, u₁₅.mem]; exact x₁₄.frame, fun r h1 h2 h3 => ?_,
        by rw [u₁₆.rd, u₁₅.rd, x₁₄.rd], by rw [u₁₆.wr, u₁₅.wr, x₁₄.wr], ?_⟩
      · rw [u₁₆.other r h3, u₁₅.other r h2, x₁₄.keep r h1]
      · have eb : s₁₆.gpr .ebp = BitVec.ofNat 32 (n - 2 * (g + 1)) := by
          rw [u₁₆.gpr, u₁₅.other _ (by decide), x₁₄.keep _ (by decide), hebp₆]
          have : n ≤ 2 ^ 28 := by omega
          bv_omega
        by_cases hl : n - 2 * g = 2
        · refine .inl ⟨by rw [eb, show n - 2 * (g + 1) = 0 by omega]; rfl, dataInv_mono hd (by omega) (by omega)⟩
        · refine .inr ⟨eb, by omega, ?_, hd⟩
          rw [u₁₆.other _ (by decide), u₁₅.gpr, x₁₄.keep _ (by decide), hesi₆, BitVec.add_assoc,
            show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
          congr 2
    · -- The last block.
      have h1 : n - 2 * g = 1 := by simp at hb; omega
      rw [xorOne_eq]
      refine xs_step hp₆ hesi₆ (b := 0) (k := 0) (by omega) (by omega) (by omega) x₀ fun s₇ x₇ => ?_
      refine xs_step hp₆ hesi₆ (b := 0) (k := 1) (by omega) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
      refine xs_step hp₆ hesi₆ (b := 0) (k := 2) (by omega) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
      refine xs_step hp₆ hesi₆ (b := 0) (k := 3) (by omega) (by omega) (by omega) x₉ fun s₁₀ x₁₀ => ?_
      refine wp_sub fun s₁₁ u₁₁ _ => WP.block_nil ?_
      refine ⟨by rw [u₁₁.mem]; exact x₁₀.frame, fun r h1 _ h3 => by rw [u₁₁.other r h3, x₁₀.keep r h1],
        by rw [u₁₁.rd, x₁₀.rd], by rw [u₁₁.wr, x₁₀.wr], .inl ⟨by rw [u₁₁.gpr]; exact BitVec.sub_self _, ?_⟩⟩
      rw [u₁₁.mem]
      have := x₁₀.data
      rwa [show 32 * g + 4 * (4 * 0 + 3 + 1) = 16 * n by omega] at this
  · -- Store the pointer and the count.
    have hedi : s.gpr .edi = B := by rw [hs.keep _ (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide), hp.edi]
    refine wp_stm hedi (hin _ (by rw [hs.wr, hwr₆]) dOff (by decide)) fun s₇ u₇ => ?_
    refine wp_stm (by rw [u₇.gpr]; exact hedi) (hin _ (by rw [u₇.wr, hs.wr, hwr₆]) nOff (by decide))
      fun s₈ u₈ => wp_test fun s₉ u₉ hz => WP.block_nil ?_
    have hfitB := hp.buf.fitB
    have fr : Frame [⟨addr B dOff, 8⟩] s.mem s₉.mem := by
      rw [u₉.mem, u₈.mem, u₇.mem]
      have hm : (⟨addr B dOff, 8⟩ : Region) ∈ [⟨addr B dOff, 8⟩] := List.mem_singleton_self _
      exact ((Frame.refl _ _).writeW hm _ (part_contains hfitB (by decide) (by decide) (by decide) (by decide))).writeW
        hm _ (part_contains hfitB (by decide) (by decide) (by decide) (by decide))
    have dsj : ∀ r ∈ [(⟨addr B dOff, 8⟩ : Region)], Region.Disjoint (reg32 Dp (16 * n)) r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hp.buf.sep.sub_right (part_sub_reg hfitB (by decide))
    have hds : s₉.mem.readW (addr B dOff) 32 = s.gpr .esi := by
      rw [u₉.mem, u₈.mem, u₇.mem, u₇.gpr, rd_wr_ne hfitB _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide), Mem.readW_writeW_self32]
    have hns : s₉.mem.readW (addr B nOff) 32 = s.gpr .ebp := by
      rw [u₉.mem, u₈.mem, u₇.gpr, u₇.mem, Mem.readW_writeW_self32]
    refine ⟨?_, fun r h1 h2 h3 => ?_, by rw [u₉.rd, u₈.rd, u₇.rd, hs.rd, hrd₆],
      by rw [u₉.wr, u₈.wr, u₇.wr, hs.wr, hwr₆], ?_⟩
    · rw [← hm₆]
      exact (hs.frame.mono (by simp)).trans (fr.mono (by simp))
    · rw [u₉.gpr, u₈.gpr, u₇.gpr, hs.keep r h1 h2 h3, g₆ r h2 h3]
    · rw [hz, u₈.gpr, u₇.gpr]
      rcases hs.post with ⟨e, d⟩ | ⟨e, hpos, ei, d⟩
      · exact .inl ⟨by rw [e]; rfl, dataInv_frame fr dsj (by omega) d⟩
      · refine .inr ⟨?_, by omega, dataInv_frame fr dsj (by omega) d, by rw [hds, ei], by rw [hns, e]⟩
        rw [e, BitVec.and_self, ofNat_beq_zero (by omega)]
        simp only [Option.some.injEq, decide_eq_false_iff_not]; omega

end Xor


end VG.Proof.Aes.X86

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `B` the scratch buffer, `Dp` the data (`n` blocks), `icb`
the first counter block. -/
structure GSetup (s₂ : State) (B Dp : BitVec 32) (n R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) :
    Prop where
  scr : reg32 B 2048 ∈ s₂.wr
  fitB : B.toNat + 2048 ≤ 2 ^ 32
  dat : reg32 Dp (16 * n) ∈ s₂.wr
  fitD : Dp.toNat + 16 * n ≤ 2 ^ 32
  sep : (reg32 Dp (16 * n)).Disjoint (reg32 B 2048)
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  argIn : InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .esp) 8) 4
  argR : s₂.mem.readW (addr (s₂.gpr .esp) 8) 32 = BitVec.ofNat 32 R
  argSep : Region.Disjoint ⟨addr (s₂.gpr .esp) 8, 4⟩ (reg32 B 2048)
  argSepD : Region.Disjoint ⟨addr (s₂.gpr .esp) 8, 4⟩ (reg32 Dp (16 * n))
  keys : KeysAt s₂.mem B R w
  cw : ∀ v < 3, ∀ i < 4, ∀ j < 8,
    (cw s₂.mem B v).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - (4 * v + i)) + j)

/-- The memory the groups write: the layers' slots, the counter, the data
pointer and the count, and the data. -/
abbrev gRegions (B Dp : BitVec 32) (n : Nat) : List Region :=
  [reg32 B 256, ⟨addr B cNum, 12⟩, reg32 Dp (16 * n)]

/-- Before group `g`. -/
structure GInv (m₀ : Mem) (s₂ : State) (B Dp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (g : Nat) (s : State) : Prop where
  hg : 2 * g < n
  base : s.gpr sb = B
  esp : s.gpr .esp = s₂.gpr .esp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (gRegions B Dp n) s₂.mem s.mem
  num : cnum s.mem B = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g)
  dslot : s.mem.readW (addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * g)
  nslot : s.mem.readW (addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * g)
  data : DataInv m₀ s.mem (Dp.setWidth 64) n (32 * g) (keyStream R w icb)

/-- After the last group. -/
structure GDone (m₀ : Mem) (s₂ : State) (B Dp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (s : State) : Prop where
  base : s.gpr sb = B
  esp : s.gpr .esp = s₂.gpr .esp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (gRegions B Dp n) s₂.mem s.mem
  data : DataInv m₀ s.mem (Dp.setWidth 64) n (16 * n) (keyStream R w icb)

section
variable {s₂ : State} {B Dp : BitVec 32} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
  (hs : GSetup s₂ B Dp n R w icb)
include hs

/-- A part of the scratch buffer at offset `o` is apart from the regions the
groups write if it is beyond the slots and the counter. -/
theorem GSetup.gdisj {o l : Nat} (h1 : 256 ≤ o) (h2 : o + l ≤ cNum ∨ cNum + 12 ≤ o) (h3 : o + l ≤ 2048) :
    ∀ r ∈ gRegions B Dp n, Region.Disjoint ⟨addr B o, l⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
    rw [← addr_zero]; exact part_disj hs.fitB h3 (by omega) (.inr h1)
  · exact part_disj hs.fitB h3 (by simp only [cNum]; omega) h2
  · exact (hs.sep.sub_right (part_sub_reg hs.fitB h3)).symm

theorem GSetup.argDisj : ∀ r ∈ gRegions B Dp n, Region.Disjoint ⟨addr (s₂.gpr .esp) 8, 4⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.argSep.sub_right (Region.sub_prefix (by omega))
  · exact hs.argSep.sub_right (part_sub_reg hs.fitB (by simp only [cNum]; omega))
  · exact hs.argSepD

theorem GSetup.dataDisj {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r (reg32 B 2048)) :
    ∀ r ∈ rs, Region.Disjoint (reg32 Dp (16 * n)) r := fun r hr => hs.sep.sub_right (h r hr)

/-- One group: from before group `g`, to after the last group (ZF set) or
before group `g + 1`. -/
theorem group_ok {m₀ : Mem} {g : Nat} {s : State} (hi : GInv m₀ s₂ B Dp n R w icb g s) :
    WP isa group s fun s' => (s'.zf = some true ∧ GDone m₀ s₂ B Dp n R w icb s') ∨
      (s'.zf = some false ∧ GInv m₀ s₂ B Dp n R w icb (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hfitB := hs.fitB
  have hfitD := hs.fitD
  have hscr : reg32 B 2048 ∈ s.wr := hi.wr ▸ hs.scr
  unfold group
  refine WP.seq (ctrBlocks_wp hi.base hfitB hscr fun s₁ hq₁ hn₁ f₁ o₁ rd₁ wr₁ => ?_)
  have hb₁ : s₁.gpr sb = B := (o₁ sb (by decide)).trans hi.base
  have f₁sub : ∀ r ∈ [reg32 B 32, (⟨addr B cNum, 4⟩ : Region)], ∃ r' ∈ gRegions B Dp n, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨reg32 B 256, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨addr B cNum, 12⟩, by simp, Region.sub_prefix (by omega)⟩
  have hf₁ : Frame (gRegions B Dp n) s₂.mem s₁.mem := hi.frame.trans (f₁.sub f₁sub)
  have hesp₁ : s₁.gpr .esp = s₂.gpr .esp := (o₁ _ (by decide)).trans hi.esp
  have hp : EncPre s₁ R w :=
    { scr := by rw [hb₁, wr₁, hi.wr]; exact hs.scr
      fit := by rw [hb₁]; exact hfitB
      rounds := hs.rounds
      argIn := by rw [rd₁, wr₁, hi.rd, hi.wr, hesp₁]; exact hs.argIn
      argR := by
        rw [hesp₁, ← hs.argR]
        exact hf₁.readW (Region.contains_self _ _) hs.argDisj (by decide)
      argSep := by rw [hesp₁, hb₁]; exact hs.argSep.sub_right (Region.sub_prefix (by omega))
      keys := by
        rw [hb₁]
        intro j hj
        refine keyRel_congr (hs.keys j hj) fun k hk => ?_
        have := keyOff_le (j := j) hR
        exact hf₁.readW (Region.contains_self _ _)
          (hs.gdisj (by simp only [lastKey] at this; omega) (.inr (by simp only [cNum]; omega))
            (by simp only [lastKey] at this; omega)) (by decide) }
  have hcw : ∀ v < 3, ∀ i < 4, ∀ j < 8,
      (cw s.mem B v).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - (4 * v + i)) + j) := by
    intro v hv i hi' j hj
    have e : cw s.mem B v = cw s₂.mem B v :=
      hi.frame.readW (Region.contains_self _ _)
        (hs.gdisj (by simp only [cwOff]; omega) (.inl (by simp only [cwOff, cNum]; omega))
          (by simp only [cwOff]; omega)) (by decide)
    rw [e]; exact hs.cw v hv i hi' j hj
  have hin : InRel (Q s₁) (fun b => ctrState icb (2 * g + b)) := ctr_inRel hq₁ hcw hi.num
  refine WP.seq (WP.mono (encrypt2_ok hp hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₁] at fr₃
  have hb₃ : s₃.gpr .edi = B := hc₃.base.trans hb₁
  have d256 : ∀ r ∈ [reg32 B 256], Region.Disjoint (reg32 Dp (16 * n)) r :=
    hs.dataDisj fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
  have d32 : ∀ r ∈ [reg32 B 32, (⟨addr B cNum, 4⟩ : Region)], Region.Disjoint (reg32 Dp (16 * n)) r :=
    hs.dataDisj fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by omega)
      · exact part_sub_reg hfitB (by decide)
  have slot13 : ∀ o, 288 ≤ o → o + 4 ≤ 296 → s₃.mem.readW (addr B o) 32 = s.mem.readW (addr B o) 32 := by
    intro o h1 h2
    rw [fr₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
        rw [← addr_zero]; exact part_disj hfitB (by omega) (by omega) (.inr (by omega))) (by decide)]
    exact f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show Region.Disjoint _ ⟨B.setWidth 64, 32⟩
        rw [← addr_zero]; exact part_disj hfitB (by omega) (by omega) (.inr (by omega))
      · exact part_disj hfitB (by omega) (by decide) (.inr (by simp only [cNum]; omega))) (by decide)
  have hx : XPre m₀ Dp B n g (keyStream R w icb) s₃ :=
    { buf := ⟨hfitD, by rw [hc₃.wr, wr₁, hi.wr]; exact hs.dat, hfitB, by rw [hc₃.wr, wr₁, hi.wr]; exact hs.scr,
        hs.sep⟩
      hg := hi.hg
      edi := hb₃
      dslot := by rw [slot13 _ (by decide) (by decide)]; exact hi.dslot
      nslot := by rw [slot13 _ (by decide) (by decide)]; exact hi.nslot
      data := dataInv_frame fr₃ d256 (by omega) (dataInv_frame f₁ d32 (by omega) hi.data)
      ks := fun b hb k hk t ht => by
        rw [ks_of_inRel hin₃ hb hk ht] }
  refine WP.mono (xorGroup_wp hx) fun s' hd => ?_
  have keep : ∀ r, r ∉ tmpRegs → r ≠ .esi → s'.gpr r = s.gpr r := fun r h1 h2 =>
    (hd.keep r (fun h => h1 (h ▸ by decide)) h2 (fun h => h1 (h ▸ by decide))).trans
      ((hc₃.keep r h1 h2).trans (o₁ r (fun h => h1 (h ▸ by decide))))
  have base' : s'.gpr sb = B := (keep sb (by decide) (by decide)).trans hi.base
  have esp' : s'.gpr .esp = s₂.gpr .esp := (keep .esp (by decide) (by decide)).trans hi.esp
  have rd' : s'.rd = s₂.rd := by rw [hd.rd, hc₃.rd, rd₁, hi.rd]
  have wr' : s'.wr = s₂.wr := by rw [hd.wr, hc₃.wr, wr₁, hi.wr]
  have frame' : Frame (gRegions B Dp n) s₂.mem s'.mem := by
    refine hf₁.trans (Frame.trans (fr₃.sub fun r hr => ⟨reg32 B 256, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩) (hd.frame.sub fun r hr => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨reg32 Dp (16 * n), by simp, fun _ h => h⟩
    · exact ⟨⟨addr B cNum, 12⟩, by simp, part_sub hfitB (by simp only [cNum]; omega)
        (by simp only [dOff, cNum]; omega) (by simp only [dOff, cNum]; omega)⟩
  rcases hd.post with ⟨z, d⟩ | ⟨z, h4, d, ds, ns⟩
  · exact .inl ⟨z, base', esp', rd', wr', frame', d⟩
  · refine .inr ⟨z, ⟨by omega, base', esp', rd', wr', frame', ?_, ds, ns, d⟩⟩
    have e₁ : cnum s'.mem B = cnum s₃.mem B :=
      hd.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hs.sep.sub_right (part_sub_reg hfitB (by decide))).symm
        · exact part_disj hfitB (by decide) (by decide) (.inl (by decide))) (by decide)
    have e₂ : cnum s₃.mem B = cnum s₁.mem B :=
      fr₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
        rw [← addr_zero]; exact part_disj hfitB (by decide) (by omega) (.inr (by decide))) (by decide)
    rw [e₁, e₂, hn₁, hi.num, BitVec.add_assoc]
    congr 1
    have : n ≤ 2 ^ 28 := by omega
    bv_omega

/-- The loop over the groups. -/
theorem groups_ok {m₀ : Mem} {s : State} (hi : GInv m₀ s₂ B Dp n R w icb 0 s) :
    WP isa (.loop group .ne) s (GDone m₀ s₂ B Dp n R w icb) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ GInv m₀ s₂ B Dp n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (group_ok hs hg) fun s' h => ?_) n s ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86.eval, z], d⟩
  · exact .inr ⟨by simp [X86.eval, z], n - 2 * (g + 1), by have := hg.hg; omega, g + 1, rfl, d⟩

end

end VG.Proof.Aes.X86
