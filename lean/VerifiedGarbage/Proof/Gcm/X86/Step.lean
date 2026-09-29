import VerifiedGarbage.Impl.Gcm.X86
import VerifiedGarbage.Proof.Aes.X86.Common
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.Range

/-!
# GHASH on x86 (32-bit): one step of Algorithm 1

Untrusted: everything here is checked by Lean. What the instructions of a
step (`Impl.Gcm.X86.step`) compute on the four words of `V` (in registers)
and of `Z` (in the scratch buffer), stated on the whole 128-bit values, and
the 128 steps of a multiplication.
-/

namespace VG.Proof.Gcm.X86

open VG VG.X86 VG.Impl.Gcm.X86 VG.Proof.Gcm VG.Proof.Aes.X86
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_add wp_addi wp_subi wp_ldm wp_xorm wp_stm wp_shr wp_ror
  wp_and wp_andi wp_or wp_xor wp_sbb_self ofNat_pred ofNat_beq_zero)
open VG.Spec.Gcm (Block)

/-! ## 128-bit values as four words -/

/-- A block from four words, the first the most significant. -/
def cat4 (a b c d : BitVec 32) : Block := a ++ b ++ c ++ d

theorem getLsbD_cat4 (a b c d : BitVec 32) (i : Nat) :
    (cat4 a b c d).getLsbD i =
      if i < 32 then d.getLsbD i else if i < 64 then c.getLsbD (i - 32)
      else if i < 96 then b.getLsbD (i - 64) else a.getLsbD (i - 96) := by
  simp only [cat4, BitVec.getLsbD_append]
  by_cases h1 : i < 32
  · simp [h1]
  · by_cases h2 : i < 64
    · simp [h1, h2, show i - 32 < 32 by omega]
    · by_cases h3 : i < 96
      · simp [h1, h2, h3, show ¬ i - 32 < 32 by omega, show i - 32 - 32 = i - 64 by omega,
          show i - 64 < 32 by omega]
      · simp [h1, h2, h3, show ¬ i - 32 < 32 by omega, show i - 32 - 32 = i - 64 by omega,
          show ¬ i - 64 < 32 by omega, show i - 64 - 32 = i - 96 by omega]

/-- The mask `sbb r, r` makes from a carry. -/
abbrev msk (c : Bool) : BitVec 32 := if c then BitVec.allOnes 32 else 0

/-- `Z ^= V & m`, word by word. -/
theorem z_update (z0 z1 z2 z3 v0 v1 v2 v3 : BitVec 32) (c : Bool) :
    cat4 ((v0 &&& msk c) ^^^ z0) ((v1 &&& msk c) ^^^ z1) ((v2 &&& msk c) ^^^ z2) ((v3 &&& msk c) ^^^ z3) =
      if c then cat4 z0 z1 z2 z3 ^^^ cat4 v0 v1 v2 v3 else cat4 z0 z1 z2 z3 := by
  cases c
  · simp [msk]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [msk, ite_true, BitVec.and_allOnes, BitVec.getLsbD_xor, getLsbD_cat4]
    split <;> [exact Bool.xor_comm _ _; split <;> [exact Bool.xor_comm _ _; split <;> exact Bool.xor_comm _ _]]

theorem topBit_bit {i : Nat} (hi : i < 32) : topBit.getLsbD i = decide (i = 31) := by
  have h : ∀ i < 32, topBit.getLsbD i = decide (i = 31) := by decide
  exact h i hi

/-- The lowest bit of `p`, moved to the top. -/
theorem carry_bit (p : BitVec 32) {i : Nat} (hi : i < 32) :
    (p.rotateRight 1 &&& topBit).getLsbD i = (decide (i = 31) && p.getLsbD 0) := by
  rw [BitVec.getLsbD_and, topBit_bit hi, BitVec.getLsbD_rotateRight]
  by_cases h : i = 31
  · subst h; simp
  · simp [h]

/-- One word's lowest bit moved into the top of the next, and both shifted. -/
theorem shr1 {n : Nat} (x : BitVec n) (y p : BitVec 32) (hp : p.getLsbD 0 = x.getLsbD 0) :
    x >>> 1 ++ (y >>> 1 ||| (p.rotateRight 1 &&& topBit)) = (x ++ y) >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or]
  by_cases h1 : i < 32
  · rw [ite_eq_left h1, carry_bit p h1]
    by_cases h2 : i = 31
    · subst h2; simp only [BitVec.getLsbD_of_ge y 32 (by omega)]; simpa using hp
    · simp [h2, show 1 + i < 32 by omega]
  · rw [ite_eq_right h1, ite_eq_right (show ¬ 1 + i < 32 by omega)]
    congr 1; omega

theorem xor_top (a b c d m : BitVec 32) : cat4 (a ^^^ m) b c d = cat4 a b c d ^^^ cat4 m 0 0 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, getLsbD_cat4]
  split <;> [simp; split <;> [simp; split <;> simp]]

theorem R_eq : Spec.Gcm.R = cat4 rTop 0 0 0 := by decide

/-- `V := (V >> 1) ⊕ (R ∧ m)`, word by word. -/
theorem v_update (a b c d : BitVec 32) :
    cat4 ((a >>> 1) ^^^ (msk (d.getLsbD 0) &&& rTop)) ((b >>> 1) ||| (a.rotateRight 1 &&& topBit))
        ((c >>> 1) ||| (b.rotateRight 1 &&& topBit)) ((d >>> 1) ||| (c.rotateRight 1 &&& topBit)) =
      if (cat4 a b c d).getLsbD 0 then (cat4 a b c d >>> 1) ^^^ Spec.Gcm.R else cat4 a b c d >>> 1 := by
  have e : cat4 (a >>> 1) ((b >>> 1) ||| (a.rotateRight 1 &&& topBit))
      ((c >>> 1) ||| (b.rotateRight 1 &&& topBit)) ((d >>> 1) ||| (c.rotateRight 1 &&& topBit)) =
      cat4 a b c d >>> 1 := by
    unfold cat4
    rw [shr1 a b a rfl, shr1 (a ++ b) c b (by rw [BitVec.getLsbD_append]; rfl),
      shr1 (a ++ b ++ c) d c (by rw [BitVec.getLsbD_append]; rfl)]
  have h0 : (cat4 a b c d).getLsbD 0 = d.getLsbD 0 := by rw [getLsbD_cat4]; rfl
  rw [xor_top, e, h0, R_eq]
  cases d.getLsbD 0
  · simp only [msk, Bool.false_eq_true, ite_false]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_xor, getLsbD_cat4]
    split <;> [simp; split <;> [simp; split <;> simp]]
  · simp only [msk, ite_true, BitVec.allOnes_and]

/-! ## The bits of `X` -/

theorem add_self_carry (x : BitVec 32) : decide (2 ^ 32 ≤ x.toNat + x.toNat) = x.msb := by
  rw [BitVec.msb_eq_decide]
  simp only [Nat.add_one_sub_one, decide_eq_decide]
  omega

theorem add_self (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  congr 1; omega

/-- Word `w` of a block, the first the most significant. -/
def xw (x : Block) (w : Nat) : BitVec 32 := x.extractLsb' (32 * (3 - w)) 32

theorem msb_xw (x : Block) {w k : Nat} (hw : w < 4) (hk : k < 32) :
    ((xw x w) <<< k).msb = x.getMsbD (32 * w + k) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, xw, BitVec.getLsbD_extractLsb',
    BitVec.getMsbD]
  simp only [show 32 - 1 < 32 by omega, decide_true, Bool.true_and, show ¬ 32 - 1 < k by omega,
    decide_false, Bool.not_false, show 32 * w + k < 128 by omega, show 32 - 1 - k < 32 by omega]
  congr 1; omega

theorem cat4_xw (x : Block) : cat4 (xw x 0) (xw x 1) (xw x 2) (xw x 3) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_cat4, xw, BitVec.getLsbD_extractLsb']
  split <;> [simp_all; split <;> [simp_all; split <;> simp_all]] <;> omega

/-! ## The instructions of a step -/

/-- `V`, in `eax`, `ebx`, `ecx` and `edx`. -/
def vOf (s : State) : Block := cat4 (s.gpr .eax) (s.gpr .ebx) (s.gpr .ecx) (s.gpr .edx)

/-- Word `k` of `Z`, in the scratch buffer at `B`. -/
abbrev zw (m : Mem) (B : BitVec 32) (k : Nat) : BitVec 32 := m.readW (addr B (zOff k)) 32

/-- `Z`. -/
def zOf (m : Mem) (B : BitVec 32) : Block := cat4 (zw m B 0) (zw m B 1) (zw m B 2) (zw m B 3)

theorem vReg_ne_esi (k : Nat) : vReg k ≠ .esi := by unfold vReg; split <;> decide
theorem vReg_ne_ebp (k : Nat) : vReg k ≠ .ebp := by unfold vReg; split <;> decide
theorem vReg_ne_edi (k : Nat) : vReg k ≠ .edi := by unfold vReg; split <;> decide

section
variable {s : State} {B : BitVec 32} {P : State → Prop}

/-- `m := −xᵢ`, and the first word of `X` shifted left. -/
theorem head_wp (hb : s.gpr .edi = B) (fit : B.toNat + 256 ≤ 2 ^ 32) (hw : reg32 B 256 ∈ s.wr)
    (h : ∀ s', s'.mem = s.mem.writeW (addr B 0) (s.mem.readW (addr B 0) 32 <<< 1) →
      s'.gpr .ebp = msk (s.mem.readW (addr B 0) 32).msb →
      (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block [.mov .esi (.mem (at_ .edi 0)), .alu .add .esi (.reg .esi), .store (at_ .edi 0) .esi,
      .alu .sbb .ebp (.reg .ebp)]) s P := by
  refine wp_ldm hb (in_rd (in_reg hw fit (by omega) (by decide))) fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ c₂ => ?_
  refine wp_stm (B := B) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₂.wr, u₁.wr]; exact in_reg hw fit (by omega) (by decide)) fun s₃ u₃ => ?_
  have c₃ : s₃.cf = some (s.mem.readW (addr B 0) 32).msb := by
    rw [u₃.cf, c₂, u₁.gpr, add_self_carry]
  refine wp_sbb_self c₃ fun s₄ u₄ => WP.block_nil ?_
  refine h s₄ ?_ u₄.gpr (fun r h1 h2 => ?_) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, add_self, u₂.mem, u₁.mem]
  · rw [u₄.other r h2, u₃.gpr, u₂.other r h1, u₁.other r h1]

/-- `Z ^= V & m`, word `k`. -/
theorem zUpd_wp (k : Nat) (hk : k < 4) (hb : s.gpr .edi = B) (fit : B.toNat + 256 ≤ 2 ^ 32)
    (hw : reg32 B 256 ∈ s.wr)
    (h : ∀ s', s'.mem = s.mem.writeW (addr B (zOff k)) ((s.gpr (vReg k) &&& s.gpr .ebp) ^^^ zw s.mem B k) →
      (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (zUpd k)) s P := by
  have hz : zOff k + 4 ≤ 256 := by simp only [zOff]; omega
  refine wp_mov fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
  refine wp_xorm (B := B) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_rd (in_reg hw fit hz (by decide))) fun s₃ u₃ => ?_
  refine wp_stm (B := B) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact in_reg hw fit hz (by decide)) fun s₄ u₄ => WP.block_nil ?_
  refine h s₄ ?_ (fun r hr => ?_) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₄.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₁.other .ebp (by decide), u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.gpr, u₃.other r hr, u₂.other r hr, u₁.other r hr]

/-- `edx >>= 1`, and `m := −LSB₁(V)`. -/
theorem mid_wp
    (h : ∀ s', s'.gpr .edx = s.gpr .edx >>> 1 → s'.gpr .ebp = msk ((s.gpr .edx).getLsbD 0) →
      (∀ r, r ≠ .edx → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      P s') :
    WP isa (.block [.shift .shr .edx 1, .alu .sbb .ebp (.reg .ebp)]) s P := by
  refine wp_shr (by decide) fun s₁ u₁ c₁ => wp_sbb_self c₁ fun s₂ u₂ => WP.block_nil ?_
  refine h s₂ (by rw [u₂.other _ (by decide), u₁.gpr]) (by rw [u₂.gpr])
    (fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1]) (by rw [u₂.mem, u₁.mem])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])

theorem vReg_succ_ne {k : Nat} (hk : k < 3) : vReg (k + 1) ≠ vReg k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide

/-- Word `k + 1 := (word k + 1 >> 1) | (word k << 31)` (its shift is done
already), and `word k >>= 1`. -/
theorem vCarry_wp (k : Nat) (hk : k < 3)
    (h : ∀ s', s'.gpr (vReg (k + 1)) = s.gpr (vReg (k + 1)) ||| ((s.gpr (vReg k)).rotateRight 1 &&& topBit) →
      s'.gpr (vReg k) = s.gpr (vReg k) >>> 1 →
      (∀ r, r ≠ .esi → r ≠ vReg k → r ≠ vReg (k + 1) → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (vCarry k)) s P := by
  have n1 := vReg_succ_ne hk
  refine wp_mov fun s₁ u₁ => wp_ror (by decide) fun s₂ u₂ => wp_andi fun s₃ u₃ => wp_or fun s₄ u₄ => ?_
  refine wp_shr (by decide) fun s₅ u₅ _ => WP.block_nil ?_
  refine h s₅ ?_ ?_ (fun r h1 h2 h3 => ?_) (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₅.other _ n1, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₃.other _ (vReg_ne_esi _), u₂.other _ (vReg_ne_esi _),
      u₁.other _ (vReg_ne_esi _)]
  · rw [u₅.gpr, u₄.other _ n1.symm, u₃.other _ (vReg_ne_esi _), u₂.other _ (vReg_ne_esi _),
      u₁.other _ (vReg_ne_esi _)]
  · rw [u₅.other r h2, u₄.other r h3, u₃.other r h1, u₂.other r h1, u₁.other r h1]

/-- `V ^= R & m` (in its top word). -/
theorem tail_wp
    (h : ∀ s', s'.gpr .eax = s.gpr .eax ^^^ (s.gpr .ebp &&& rTop) → (∀ r, r ≠ .eax → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block [.alu .and .ebp (.imm rTop), .alu .xor .eax (.reg .ebp)]) s P := by
  refine wp_andi fun s₁ u₁ => wp_xor fun s₂ u₂ => WP.block_nil ?_
  refine h s₂ (by rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide)]) (fun r h1 h2 => by rw [u₂.other r h1, u₁.other r h2])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])

/-- What a step writes: the first word of `X`, and `Z`. -/
abbrev stepRegions (B : BitVec 32) : List Region := [⟨addr B 0, 4⟩, ⟨addr B 16, 16⟩]

theorem step_eq : step = ((((((((([.mov .esi (.mem (at_ .edi 0)), .alu .add .esi (.reg .esi),
    .store (at_ .edi 0) .esi, .alu .sbb .ebp (.reg .ebp)] : List Instr) ++ zUpd 0) ++ zUpd 1) ++ zUpd 2) ++
    zUpd 3) ++ ([.shift .shr .edx 1, .alu .sbb .ebp (.reg .ebp)] : List Instr)) ++ vCarry 2) ++ vCarry 1) ++
    vCarry 0) ++ ([.alu .and .ebp (.imm rTop), .alu .xor .eax (.reg .ebp)] : List Instr) := rfl

/-- One step of Algorithm 1: `Z` and `V` as `mulStep` updates them, for the
top bit of the first word of `X`, which is shifted out. -/
theorem step_ok (hb : s.gpr .edi = B) (fit : B.toNat + 256 ≤ 2 ^ 32) (hw : reg32 B 256 ∈ s.wr)
    (h : ∀ s', zOf s'.mem B = (if (s.mem.readW (addr B 0) 32).msb then zOf s.mem B ^^^ vOf s else zOf s.mem B) →
      vOf s' = (if (vOf s).getLsbD 0 then (vOf s >>> 1) ^^^ Spec.Gcm.R else vOf s >>> 1) →
      s'.mem.readW (addr B 0) 32 = s.mem.readW (addr B 0) 32 <<< 1 →
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → Frame (stepRegions B) s.mem s'.mem → P s') :
    WP isa (.block step) s P := by
  rw [step_eq]
  repeat rw [WP.block_append_iff (M := isa)]
  refine head_wp hb fit hw fun s₁ m₁ e₁ g₁ rd₁ wr₁ => ?_
  have b₁ : s₁.gpr .edi = B := (g₁ _ (by decide) (by decide)).trans hb
  refine zUpd_wp 0 (by omega) b₁ fit (wr₁ ▸ hw) fun s₂ m₂ g₂ rd₂ wr₂ => ?_
  have b₂ : s₂.gpr .edi = B := (g₂ _ (by decide)).trans b₁
  refine zUpd_wp 1 (by omega) b₂ fit (wr₂ ▸ wr₁ ▸ hw) fun s₃ m₃ g₃ rd₃ wr₃ => ?_
  have b₃ : s₃.gpr .edi = B := (g₃ _ (by decide)).trans b₂
  refine zUpd_wp 2 (by omega) b₃ fit (wr₃ ▸ wr₂ ▸ wr₁ ▸ hw) fun s₄ m₄ g₄ rd₄ wr₄ => ?_
  have b₄ : s₄.gpr .edi = B := (g₄ _ (by decide)).trans b₃
  refine zUpd_wp 3 (by omega) b₄ fit (wr₄ ▸ wr₃ ▸ wr₂ ▸ wr₁ ▸ hw) fun s₅ m₅ g₅ rd₅ wr₅ => ?_
  refine mid_wp fun s₆ edx₆ ebp₆ g₆ m₆ rd₆ wr₆ => ?_
  refine vCarry_wp 2 (by omega) fun s₇ edx₇ ecx₇ g₇ m₇ rd₇ wr₇ => ?_
  refine vCarry_wp 1 (by omega) fun s₈ ecx₈ ebx₈ g₈ m₈ rd₈ wr₈ => ?_
  refine vCarry_wp 0 (by omega) fun s₉ ebx₉ eax₉ g₉ m₉ rd₉ wr₉ => ?_
  refine tail_wp fun s₁₀ eax₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ => ?_
  -- The registers through the updates of `Z`.
  have g₅ : ∀ r, r ≠ .esi → r ≠ .ebp → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₅ r h1, g₄ r h1, g₃ r h1, g₂ r h1, g₁ r h1 h2]
  have ebp₅ : ∀ j ≤ 4, ∀ t : State, (∀ r, r ≠ .esi → t.gpr r = s₁.gpr r) → t.gpr .ebp =
      msk (s.mem.readW (addr B 0) 32).msb := fun _ _ t ht => by rw [ht _ (by decide), e₁]
  have x₁ : ∀ k, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) → s₁.gpr (vReg k) = s.gpr (vReg k) := fun k hk => by
    rcases hk with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)
  refine h s₁₀ ?_ ?_ ?_ ?_ (by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁])
    (by rw [wr₁₀, wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) ?_
  · have r₄ : ∀ r, r ≠ .esi → r ≠ .ebp → s₄.gpr r = s.gpr r := fun r h1 h2 => by
      rw [g₄ r h1, g₃ r h1, g₂ r h1, g₁ r h1 h2]
    have r₃ : ∀ r, r ≠ .esi → r ≠ .ebp → s₃.gpr r = s.gpr r := fun r h1 h2 => by
      rw [g₃ r h1, g₂ r h1, g₁ r h1 h2]
    have r₂ : ∀ r, r ≠ .esi → r ≠ .ebp → s₂.gpr r = s.gpr r := fun r h1 h2 => by
      rw [g₂ r h1, g₁ r h1 h2]
    have p₄ : s₄.gpr .ebp = msk (s.mem.readW (addr B 0) 32).msb := by rw [g₄ _ (by decide), g₃ _ (by decide),
      g₂ _ (by decide), e₁]
    have p₃ : s₃.gpr .ebp = msk (s.mem.readW (addr B 0) 32).msb := by rw [g₃ _ (by decide),
      g₂ _ (by decide), e₁]
    have p₂ : s₂.gpr .ebp = msk (s.mem.readW (addr B 0) 32).msb := by rw [g₂ _ (by decide), e₁]
    rw [m₁₀, m₉, m₈, m₇, m₆]
    have fit' := fit
    simp (disch := decide) only [zOf, zw, zOff, m₅, m₄, m₃, m₂, m₁, rd_wr_ne fit', Mem.readW_writeW_self32,
      Nat.reduceMul, Nat.reduceAdd, vReg, r₄, r₃, r₂, g₁, p₄, p₃, p₂, e₁]
    rw [z_update]; rfl
  · have eax₉' : s₉.gpr .eax = s₈.gpr .eax >>> 1 := eax₉
    have ebx₉' : s₉.gpr .ebx = s₈.gpr .ebx ||| ((s₈.gpr .eax).rotateRight 1 &&& topBit) := ebx₉
    have ebx₈' : s₈.gpr .ebx = s₇.gpr .ebx >>> 1 := ebx₈
    have ecx₈' : s₈.gpr .ecx = s₇.gpr .ecx ||| ((s₇.gpr .ebx).rotateRight 1 &&& topBit) := ecx₈
    have ecx₇' : s₇.gpr .ecx = s₆.gpr .ecx >>> 1 := ecx₇
    have edx₇' : s₇.gpr .edx = s₆.gpr .edx ||| ((s₆.gpr .ecx).rotateRight 1 &&& topBit) := edx₇
    have v₅ : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .edx → s₆.gpr r = s.gpr r := fun r h1 h2 h3 => by
      rw [g₆ r h3 h2, g₅ r h1 h2]
    have p₉ : s₉.gpr .ebp = msk ((s.gpr .edx).getLsbD 0) := by
      rw [g₉ _ (by decide) (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide),
        g₇ _ (by decide) (by decide) (by decide), ebp₆, g₅ _ (by decide) (by decide)]
    have e : vOf s₁₀ = cat4 ((s.gpr .eax >>> 1) ^^^ (msk ((s.gpr .edx).getLsbD 0) &&& rTop))
        ((s.gpr .ebx >>> 1) ||| ((s.gpr .eax).rotateRight 1 &&& topBit))
        ((s.gpr .ecx >>> 1) ||| ((s.gpr .ebx).rotateRight 1 &&& topBit))
        ((s.gpr .edx >>> 1) ||| ((s.gpr .ecx).rotateRight 1 &&& topBit)) := by
      unfold vOf
      rw [eax₁₀, g₁₀ .ebx (by decide) (by decide), g₁₀ .ecx (by decide) (by decide),
        g₁₀ .edx (by decide) (by decide), p₉, eax₉', ebx₉', g₉ .ecx (by decide) (by decide) (by decide),
        g₉ .edx (by decide) (by decide) (by decide), g₈ .eax (by decide) (by decide) (by decide), ebx₈', ecx₈',
        g₈ .edx (by decide) (by decide) (by decide), g₇ .eax (by decide) (by decide) (by decide),
        g₇ .ebx (by decide) (by decide) (by decide), ecx₇', edx₇', edx₆, v₅ .eax (by decide) (by decide)
        (by decide), v₅ .ebx (by decide) (by decide) (by decide), v₅ .ecx (by decide) (by decide) (by decide),
        g₅ .edx (by decide) (by decide)]
    rw [e, v_update]; rfl
  · rw [m₁₀, m₉, m₈, m₇, m₆]
    have fit' := fit
    simp (disch := decide) only [zOff, m₅, m₄, m₃, m₂, m₁, rd_wr_ne fit', Mem.readW_writeW_self32,
      Nat.reduceMul, Nat.reduceAdd]
  · intro r h1 h2 h3 h4 h5 h6
    rw [g₁₀ r h1 h6, g₉ r h5 h1 h2, g₈ r h5 h2 h3, g₇ r h5 h3 h4, g₆ r h4 h6, g₅ r h5 h6]
  · rw [m₁₀, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    have h0 : (⟨addr B 0, 4⟩ : Region) ∈ stepRegions B := List.mem_cons_self ..
    have hz : (⟨addr B 16, 16⟩ : Region) ∈ stepRegions B := by simp
    have c : ∀ k < 4, (⟨addr B 16, 16⟩ : Region).Contains (addr B (zOff k)) (32 / 8) := fun k hk =>
      part_contains fit (by omega) (by simp only [zOff]; omega) (by simp only [zOff]; omega) (by decide)
    exact (((((Frame.refl _ _).writeW h0 _ (Region.contains_self _ _)).writeW hz _ (c 0 (by omega))).writeW
      hz _ (c 1 (by omega))).writeW hz _ (c 2 (by omega))).writeW hz _ (c 3 (by omega))

end

/-! ## The 128 steps -/

/-- What a multiplication writes of the scratch buffer: `X`'s words, `Z`,
and the counters of words and steps. -/
abbrev mRegions (B : BitVec 32) : List Region := [reg32 B 32, ⟨addr B wcOff, 8⟩]

/-- After `k` steps of word `w` of `x • h`, from the state `sB`. -/
structure Inner (x h : Block) (B : BitVec 32) (sB : State) (w k : Nat) (s : State) : Prop where
  fit : B.toNat + 256 ≤ 2 ^ 32
  scr : reg32 B 256 ∈ sB.wr
  zv : (zOf s.mem B, vOf s) = mulSteps x h (32 * w + k)
  x0 : s.mem.readW (addr B 0) 32 = xw x w <<< k
  xs : ∀ j, 1 ≤ j → w + j ≤ 3 → s.mem.readW (addr B (4 * j)) 32 = xw x (w + j)
  wc : s.mem.readW (addr B wcOff) 32 = BitVec.ofNat 32 (4 - w)
  edi : s.gpr .edi = B
  esp : s.gpr .esp = sB.gpr .esp
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame (mRegions B) sB.mem s.mem

/-- After the 128 steps. -/
structure MDone (x h : Block) (B : BitVec 32) (sB : State) (s : State) : Prop where
  zv : (zOf s.mem B, vOf s) = mulSteps x h 128
  edi : s.gpr .edi = B
  esp : s.gpr .esp = sB.gpr .esp
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame (mRegions B) sB.mem s.mem

section
variable {x h : Block} {B : BitVec 32} {sB : State}

theorem Inner.stepFrame {w k : Nat} {s : State} (hi : Inner x h B sB w k s) {o : Nat} (ho : o + 4 ≤ 256)
    (h1 : 4 ≤ o) (h2 : o + 4 ≤ 16 ∨ 32 ≤ o) : ∀ r ∈ stepRegions B, Region.Disjoint ⟨addr B o, 4⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact part_disj hi.fit ho (by omega) (.inr (by omega))
  · exact part_disj hi.fit ho (by omega) (by omega)

theorem inner_step {w k : Nat} (hw : w < 4) (hk : k < 32) {s : State} (hi : Inner x h B sB w k s) :
    WP isa (.block step) s fun s' => Inner x h B sB w (k + 1) s' ∧
      s'.mem.readW (addr B scOff) 32 = s.mem.readW (addr B scOff) 32 := by
  have fit := hi.fit
  refine step_ok hi.edi fit (hi.wr ▸ hi.scr) fun s' hz hv hx g rd wr f => ?_
  have hm : (s.mem.readW (addr B 0) 32).msb = x.getMsbD (32 * w + k) := by rw [hi.x0, msb_xw x hw hk]
  refine ⟨⟨fit, hi.scr, ?_, ?_, fun j h1 h2 => ?_, ?_, (g _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hi.edi, (g _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans hi.esp, rd.trans hi.rd, wr.trans hi.wr, hi.frame.trans (f.sub fun r hr => ?_)⟩, ?_⟩
  · rw [show 32 * w + (k + 1) = 32 * w + k + 1 by omega, mulSteps_succ, ← hi.zv, hz, hv, hm]; rfl
  · rw [hx, hi.x0, ← BitVec.shiftLeft_add]
  · rw [f.readW (Region.contains_self _ _) (hi.stepFrame (by omega) (by omega) (.inl (by omega)))
      (by decide), hi.xs j h1 h2]
  · rw [f.readW (Region.contains_self _ _) (hi.stepFrame (by simp only [wcOff]; omega)
      (by simp only [wcOff]; omega) (.inr (by simp only [wcOff]; omega))) (by decide), hi.wc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨reg32 B 32, by simp, part_sub_reg (N := 32) (by omega) (by omega)⟩
    · exact ⟨reg32 B 32, by simp, part_sub_reg (N := 32) (by omega) (by omega)⟩
  · exact f.readW (Region.contains_self _ _) (hi.stepFrame (by simp only [scOff]; omega)
      (by simp only [scOff]; omega) (.inr (by simp only [scOff]; omega))) (by decide)

/-- A write to the step counter keeps the rest. -/
theorem Inner.sc {w k : Nat} {s s' : State} (hi : Inner x h B sB w k s) {v : BitVec 32}
    (hm : s'.mem = s.mem.writeW (addr B scOff) v) (hg : ∀ r, r ≠ .esi → s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inner x h B sB w k s' := by
  have fit := hi.fit
  have e : ∀ o, o + 4 ≤ 256 → o % 4 = 0 → o ≠ scOff → s'.mem.readW (addr B o) 32 = s.mem.readW (addr B o) 32 :=
    fun o h1 h2 h3 => by rw [hm, rd_wr_ne fit _ _ h1 (by decide) h2 (by decide) h3]
  refine ⟨fit, hi.scr, ?_, ?_, fun j h1 h2 => ?_, ?_, (hg _ (by decide)).trans hi.edi,
    (hg _ (by decide)).trans hi.esp, hrd.trans hi.rd, hwr.trans hi.wr, ?_⟩
  · have hv : vOf s' = vOf s := by
      simp only [vOf, hg .eax (by decide), hg .ebx (by decide), hg .ecx (by decide), hg .edx (by decide)]
    rw [← hi.zv, hv]
    simp only [zOf, zw, zOff]
    rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide),
      e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide)]
  · rw [e 0 (by decide) (by decide) (by decide), hi.x0]
  · rw [e (4 * j) (by omega) (by omega) (by simp only [scOff]; omega), hi.xs j h1 h2]
  · rw [e wcOff (by decide) (by decide) (by decide), hi.wc]
  · rw [hm]
    exact hi.frame.writeW (r := ⟨addr B wcOff, 8⟩) (by simp) _
      (part_contains fit (by simp only [wcOff]; omega) (by simp only [wcOff, scOff]; omega)
        (by simp only [wcOff, scOff]; omega) (by decide))

/-- `unroll` steps, and the count. -/
theorem steps_ok {w j : Nat} (hw : w < 4) (hj : j < 4) {s : State} (hi : Inner x h B sB w (8 * j) s)
    (hc : s.mem.readW (addr B scOff) 32 = BitVec.ofNat 32 (4 - j)) :
    WP isa (.block steps) s fun s' => Inner x h B sB w (8 * (j + 1)) s' ∧
      s'.mem.readW (addr B scOff) 32 = BitVec.ofNat 32 (4 - (j + 1)) ∧
      s'.zf = some (decide (4 - (j + 1) = 0)) := by
  have fit := hi.fit
  rw [steps, WP.block_append_iff (M := isa)]
  refine WP.mono (wp_range_flatMap (M := isa) (N := unroll)
    (fun k s' => Inner x h B sB w (8 * j + k) s' ∧
      s'.mem.readW (addr B scOff) 32 = s.mem.readW (addr B scOff) 32)
    (fun k s' hk ⟨hs', hc'⟩ => WP.mono (inner_step hw (by simp only [unroll] at hk; omega) hs')
      fun _ ⟨h₁, h₂⟩ => ⟨h₁, h₂.trans hc'⟩)
    unroll (Nat.le_refl _) s ⟨hi, rfl⟩) fun s₁ ⟨hs₁, hc₁⟩ => ?_
  rw [show 8 * j + unroll = 8 * (j + 1) by simp only [unroll]; omega] at hs₁
  have hin : InRegions s₁.wr (addr B scOff) 4 := by
    rw [hs₁.wr]; exact in_reg hs₁.scr fit (by simp only [scOff]; omega) (by decide)
  refine wp_ldm hs₁.edi (in_rd hin) fun s₂ u₂ => wp_subi fun s₃ u₃ _ z₃ => ?_
  refine wp_stm (B := B) (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact hs₁.edi)
    (by rw [u₃.wr, u₂.wr]; exact hin) fun s₄ u₄ => WP.block_nil ?_
  have v₃ : s₃.gpr .esi = BitVec.ofNat 32 (4 - (j + 1)) := by
    rw [u₃.gpr, u₂.gpr, hc₁, hc, ofNat_pred (by omega)]; rfl
  refine ⟨hs₁.sc (by rw [u₄.mem, u₃.mem, u₂.mem, v₃]) (fun r hr => by
      rw [u₄.gpr, u₃.other r hr, u₂.other r hr]) (by rw [u₄.rd, u₃.rd, u₂.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr]),
    by rw [u₄.mem, Mem.readW_writeW_self32, v₃], ?_⟩
  rw [u₄.zf, z₃, u₂.gpr, hc₁, hc, ofNat_pred (by omega), ofNat_beq_zero (by omega)]; rfl

/-- The 32 steps of a word. -/
theorem stepsLoop_ok {w : Nat} (hw : w < 4) {s : State} (hi : Inner x h B sB w 0 s)
    (hc : s.mem.readW (addr B scOff) 32 = BitVec.ofNat 32 4) :
    WP isa (.loop (.block steps) .ne) s (Inner x h B sB w 32) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = 4 - j ∧ j < 4 ∧ Inner x h B sB w (8 * j) s ∧
      s.mem.readW (addr B scOff) 32 = BitVec.ofNat 32 (4 - j))
    (fun m s ⟨j, hm, hj, hs, hc⟩ => WP.mono (steps_ok hw hj hs hc) fun s' ⟨hs', hc', z⟩ => ?_) _ s
    ⟨0, rfl, by omega, hi, hc⟩
  by_cases hl : j + 1 = 4
  · refine .inl ⟨by simp [X86.eval, z, hl], ?_⟩
    rw [hl] at hs'; exact hs'
  · exact .inr ⟨by simp [X86.eval, z]; omega, _, by omega, j + 1, rfl, by omega, hs', hc'⟩

theorem nextWord_eq : nextWord = [.mov .esi (.mem (at_ .edi 4)), .store (at_ .edi 0) .esi,
    .mov .esi (.mem (at_ .edi 8)), .store (at_ .edi 4) .esi,
    .mov .esi (.mem (at_ .edi 12)), .store (at_ .edi 8) .esi,
    .mov .esi (.mem (at_ .edi 56)), .alu .sub .esi (.imm 1), .store (at_ .edi 56) .esi] := rfl

/-- Move the next words of `X` down, and count the word. -/
theorem nextWord_ok {w : Nat} (hw : w < 4) {s : State} (hi : Inner x h B sB w 32 s) :
    WP isa (.block nextWord) s fun s' => (s'.zf = some false ∧ w + 1 < 4 ∧ Inner x h B sB (w + 1) 0 s') ∨
      (s'.zf = some true ∧ MDone x h B sB s') := by
  have fit := hi.fit
  have hin : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 256 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht, hi.wr]; exact in_reg hi.scr fit ho (by decide)
  rw [nextWord_eq]
  refine wp_ldm hi.edi (in_rd (hin _ rfl 4 (by omega))) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .edi = B := by rw [u₁.other _ (by decide)]; exact hi.edi
  refine wp_stm e₁ (hin _ u₁.wr 0 (by omega)) fun s₂ u₂ => ?_
  refine wp_ldm (by rw [u₂.gpr]; exact e₁) (in_rd (hin _ (by rw [u₂.wr, u₁.wr]) 8 (by omega))) fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .edi = B := by rw [u₃.other _ (by decide), u₂.gpr]; exact e₁
  refine wp_stm e₃ (hin _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 4 (by omega)) fun s₄ u₄ => ?_
  refine wp_ldm (by rw [u₄.gpr]; exact e₃) (in_rd (hin _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 12 (by omega)))
    fun s₅ u₅ => ?_
  have e₅ : s₅.gpr .edi = B := by rw [u₅.other _ (by decide), u₄.gpr]; exact e₃
  have w₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_stm e₅ (hin _ w₅ 8 (by omega)) fun s₆ u₆ => ?_
  refine wp_ldm (by rw [u₆.gpr]; exact e₅) (in_rd (hin _ (by rw [u₆.wr, w₅]) 56 (by omega))) fun s₇ u₇ => ?_
  refine wp_subi fun s₈ u₈ _ z₈ => ?_
  refine wp_stm (B := B) (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]; exact e₅)
    (hin _ (by rw [u₈.wr, u₇.wr, u₆.wr, w₅]) 56 (by omega)) fun s₉ u₉ => WP.block_nil ?_
  let m := s.mem
  let M := (((m.writeW (addr B 0) (m.readW (addr B 4) 32)).writeW (addr B 4) (m.readW (addr B 8) 32)).writeW
    (addr B 8) (m.readW (addr B 12) 32)).writeW (addr B 56) (m.readW (addr B 56) 32 - 1)
  have fit' := fit
  have m₉ : s₉.mem = M := by
    rw [u₉.mem, u₈.gpr, u₇.gpr, u₈.mem, u₇.mem, u₆.mem, u₅.gpr, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.mem,
      u₁.gpr, u₁.mem]
    simp (disch := decide) only [M, m, rd_wr_ne fit']
  have g₉ : ∀ r, r ≠ .esi → s₉.gpr r = s.gpr r := fun r hr => by
    rw [u₉.gpr, u₈.other r hr, u₇.other r hr, u₆.gpr, u₅.other r hr, u₄.gpr, u₃.other r hr, u₂.gpr,
      u₁.other r hr]
  have wc : s₉.mem.readW (addr B wcOff) 32 = BitVec.ofNat 32 (4 - (w + 1)) := by
    rw [m₉]; simp only [M, wcOff, Mem.readW_writeW_self32]
    rw [show (56 : Nat) = wcOff from rfl, hi.wc, ofNat_pred (by omega), Nat.sub_sub]
  have zf : s₉.zf = some (decide (4 - (w + 1) = 0)) := by
    have r56 : s₆.mem.readW (addr B 56) 32 = BitVec.ofNat 32 (4 - w) := by
      rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      simp (disch := decide) only [rd_wr_ne fit']
      exact hi.wc
    rw [u₉.zf, z₈, u₇.gpr, r56, ofNat_pred (by omega), ofNat_beq_zero (by omega), Nat.sub_sub]
  have zv : (zOf s₉.mem B, vOf s₉) = mulSteps x h (32 * (w + 1) + 0) := by
    have hv : vOf s₉ = vOf s := by
      simp only [vOf, g₉ .eax (by decide), g₉ .ebx (by decide), g₉ .ecx (by decide), g₉ .edx (by decide)]
    rw [show 32 * (w + 1) + 0 = 32 * w + 32 by omega, ← hi.zv, hv, m₉]
    simp (disch := decide) only [zOf, zw, zOff, M, rd_wr_ne fit', Nat.reduceMul, Nat.reduceAdd]
    rfl
  have fr : Frame (mRegions B) sB.mem s₉.mem := by
    rw [m₉]
    have h32 : reg32 B 32 ∈ mRegions B := List.mem_cons_self ..
    have hwc : (⟨addr B wcOff, 8⟩ : Region) ∈ mRegions B := by simp
    exact (((hi.frame.writeW h32 _ (reg_contains (by omega) (by omega) (by decide))).writeW h32 _
      (reg_contains (by omega) (by omega) (by decide))).writeW h32 _
      (reg_contains (by omega) (by omega) (by decide))).writeW hwc _
      (part_contains fit (by simp only [wcOff]; omega) (by simp only [wcOff]; omega)
        (by simp only [wcOff]; omega) (by decide))
  have edi₉ : s₉.gpr .edi = B := (g₉ _ (by decide)).trans hi.edi
  have esp₉ : s₉.gpr .esp = sB.gpr .esp := (g₉ _ (by decide)).trans hi.esp
  have rd₉ : s₉.rd = sB.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  have wr₉ : s₉.wr = sB.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅, hi.wr]
  by_cases hl : w + 1 = 4
  · refine .inr ⟨by rw [zf, hl]; rfl, ?_, edi₉, esp₉, rd₉, wr₉, fr⟩
    rw [zv, hl]
  · refine .inl ⟨by rw [zf]; simp; omega, by omega, fit, hi.scr, zv, ?_, fun j h1 h2 => ?_, wc, edi₉, esp₉, rd₉, wr₉, fr⟩
    · rw [m₉, BitVec.shiftLeft_zero]
      simp (disch := decide) only [M, rd_wr_ne fit', Mem.readW_writeW_self32]
      exact hi.xs 1 (by omega) (by omega)
    · rw [m₉]
      rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
      · simp (disch := decide) only [M, rd_wr_ne fit', Mem.readW_writeW_self32, Nat.reduceMul]
        rw [hi.xs 2 (by omega) (by omega)]
      · simp (disch := decide) only [M, rd_wr_ne fit', Mem.readW_writeW_self32, Nat.reduceMul]
        rw [hi.xs 3 (by omega) (by omega)]

/-- A word of `X`: 32 steps. -/
theorem word_ok {w : Nat} (hw : w < 4) {s : State} (hi : Inner x h B sB w 0 s) :
    WP isa word s fun s' => (s'.zf = some false ∧ w + 1 < 4 ∧ Inner x h B sB (w + 1) 0 s') ∨
      (s'.zf = some true ∧ MDone x h B sB s') := by
  have fit := hi.fit
  unfold word
  refine WP.seq ?_
  refine wp_movi fun s₁ u₁ => wp_stm (B := B) (by rw [u₁.other _ (by decide)]; exact hi.edi)
    (by rw [u₁.wr, hi.wr]; exact in_reg hi.scr fit (by simp only [scOff]; omega) (by decide))
    fun s₂ u₂ => WP.block_nil ?_
  have h₂ : Inner x h B sB w 0 s₂ := hi.sc (by rw [u₂.mem, u₁.mem]) (fun r hr => by rw [u₂.gpr, u₁.other r hr])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
  refine WP.seq (WP.mono (stepsLoop_ok hw h₂ (by rw [u₂.mem, Mem.readW_writeW_self32, u₁.gpr]; rfl))
    fun s₃ h₃ => nextWord_ok hw h₃)

/-- The four words: all 128 steps. -/
theorem mul_ok {s : State} (hi : Inner x h B sB 0 0 s) : WP isa (.loop word .ne) s (MDone x h B sB) := by
  refine WP.loop (M := isa) (fun m s => ∃ w, m = 4 - w ∧ w < 4 ∧ Inner x h B sB w 0 s)
    (fun m s ⟨w, hm, hw, hs⟩ => WP.mono (word_ok hw hs) fun s' hr => ?_) _ s ⟨0, rfl, by omega, hi⟩
  rcases hr with ⟨z, hl, d⟩ | ⟨z, d⟩
  · exact .inr ⟨by simp [X86.eval, z], _, by omega, w + 1, rfl, hl, d⟩
  · exact .inl ⟨by simp [X86.eval, z], d⟩

end

end VG.Proof.Gcm.X86
