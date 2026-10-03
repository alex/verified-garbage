import VerifiedGarbage.Proof.Argon2.X86.Derive.FillRef

/-!
# Argon2 on x86 (32-bit): the reference window's size

`countSelect_ok`: the number of eligible reference blocks, chosen between
the current lane's and another lane's by a mask (`sel`), to the locals.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

theorem sel (a c : BitVec 32) (b : Bool) :
    a ^^^ ((c ^^^ a) &&& (if b then BitVec.allOnes 32 else 0)) = if b then c else a := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem add_allOnes {x : Nat} (h : 1 ≤ x) (h' : x < 2 ^ 32) :
    BitVec.ofNat 32 x + BitVec.allOnes 32 = BitVec.ofNat 32 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Wp.toNat_ofNat_lt h', Wp.toNat_ofNat_lt (by omega), BitVec.toNat_allOnes]
  omega

theorem xor_lt_one {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    decide ((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b).toNat < (1 : BitVec 32).toNat) = decide (a = b) := by
  rw [show (1 : BitVec 32).toNat = 1 from rfl, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h
    have e : BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = 0#32 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
    have := congrArg (· ^^^ BitVec.ofNat 32 b) e
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor] at this
    have := congrArg BitVec.toNat this
    rwa [Wp.toNat_ofNat_lt ha, Wp.toNat_ofNat_lt hb] at this
  · rintro rfl; simp

theorem lt_one {n : Nat} (h : n < 2 ^ 32) :
    decide ((BitVec.ofNat 32 n).toNat < (1 : BitVec 32).toNat) = decide (n = 0) := by
  rw [Wp.toNat_ofNat_lt h]
  simp only [show (1 : BitVec 32).toNat = 1 from rfl, Nat.lt_one_iff]

/-- The window's size. -/
def countV (base index : Nat) (same : Bool) : Nat :=
  if same then base + index - 1 else base - (if index = 0 then 1 else 0)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countSelect`: the window's size, to the locals and `eax`. -/
theorem countSelect_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {base rl : Nat} (hb : base < 2 ^ 31)
    (hi : index < (prm s₀).segmentLen) (hl : lane < lanesN s₀) (hrl : rl < lanesN s₀)
    (ha : s.gpr .eax = BitVec.ofNat 32 base) (hr : lw s₀ s refLaneOff = BitVec.ofNat 32 rl)
    (hsame : rl = lane → 1 ≤ base + index) (hother : rl ≠ lane → index = 0 → 1 ≤ base)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      t.gpr .eax = BitVec.ofNat 32 (countV base index (rl == lane)) →
      lw s₀ t countOff = BitVec.ofNat 32 (countV base index (rl == lane)) →
      (∀ e, e + 4 ≤ 236 → (countOff + 4 ≤ e ∨ e + 4 ≤ countOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.countSelect ++ is)) s Q := by
  have sl := segLen_lt hp
  have lt := hp.lanes_lt
  unfold Impl.Argon2.X86.Derive.countSelect
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => ?_
  have h₁ := h.of_keep (Divide.Keep.of_upd u₁ (by simp))
  refine wp_addm h₁.fs.inv.ebp (loc_in' hp h₁.fs.inv (d := indexOff) (by decide)) fun s₂ u₂ =>
    wp_subi fun s₃ u₃ _ _ => ?_
  have K₃ : Divide.Keep s s₃ :=
    ((Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_upd u₂ (by simp))).trans (Divide.Keep.of_upd u₃ (by simp))
  refine wp_ldloc hp (h.of_keep K₃).fs.inv (d := indexOff) (by decide) fun s₄ u₄ => wp_subi fun s₅ u₅ c₅ _ =>
    wp_sbb_self c₅ fun s₆ u₆ => wp_add fun s₇ u₇ _ => ?_
  have K₇ : Divide.Keep s s₇ := (((K₃.trans (Divide.Keep.of_upd u₄ (by simp))).trans
    (Divide.Keep.of_upd u₅ (by simp))).trans (Divide.Keep.of_upd u₆ (by simp))).trans (Divide.Keep.of_upd u₇ (by simp))
  refine wp_ldloc hp (h.of_keep K₇).fs.inv (d := refLaneOff) (by decide) fun s₈ u₈ => ?_
  have K₈ := K₇.trans (Divide.Keep.of_upd u₈ (by simp))
  refine wp_xorm (h.of_keep K₈).fs.inv.ebp (loc_in' hp (h.of_keep K₈).fs.inv (d := laneOff) (by decide))
    fun s₉ u₉ => wp_subi fun s₁₀ u₁₀ c₁₀ _ => wp_sbb_self c₁₀ fun s₁₁ u₁₁ => wp_xor fun s₁₂ u₁₂ =>
    wp_and fun s₁₃ u₁₃ => wp_xor fun s₁₄ u₁₄ => ?_
  have K₁₄ : Divide.Keep s s₁₄ := ((((((K₈.trans (Divide.Keep.of_upd u₉ (by simp))).trans
    (Divide.Keep.of_upd u₁₀ (by simp))).trans (Divide.Keep.of_upd u₁₁ (by simp))).trans
    (Divide.Keep.of_upd u₁₂ (by simp))).trans (Divide.Keep.of_upd u₁₃ (by simp))).trans
    (Divide.Keep.of_upd u₁₄ (by simp)))
  have h₁₄ := h.of_keep K₁₄
  -- The value.
  have hix : lw s₀ s indexOff = BitVec.ofNat 32 index := h.fs.pos.index
  have hln : lw s₀ s laneOff = BitVec.ofNat 32 lane := h.fs.pos.lane
  have m : ∀ {t : State}, Divide.Keep s t → ∀ d, lw s₀ t d = lw s₀ s d := fun k d => lw_mem k.mem d
  have e₃ : s₃.gpr .ecx = BitVec.ofNat 32 base + BitVec.ofNat 32 index - 1 := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, ha, show s₁.mem.readW (addr (E s₀) indexOff) 32 = lw s₀ s₁ indexOff from rfl,
      m (Divide.Keep.of_upd u₁ (by simp)), hix]
  have e₇ : s₇.gpr .eax = BitVec.ofNat 32 base + (if decide (index = 0) then BitVec.allOnes 32 else 0) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .eax (by decide), u₅.other .eax (by decide), u₄.other .eax (by decide),
      u₃.other .eax (by decide), u₂.other .eax (by decide), u₁.other .eax (by decide), ha, u₄.gpr, m K₃, hix,
      lt_one (by omega)]
  have e₁₁ : s₁₁.gpr .edx = if decide (rl = lane) then BitVec.allOnes 32 else 0 := by
    rw [u₁₁.gpr, u₉.gpr, u₈.gpr, show s₈.mem.readW (addr (E s₀) laneOff) 32 = lw s₀ s₈ laneOff from rfl, m K₇, m K₈,
      hr, hln, xor_lt_one (by omega) (by omega)]
  have e₁₄ : s₁₄.gpr .eax = if decide (rl = lane) then s₃.gpr .ecx else s₇.gpr .eax := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₃.other .eax (by decide), u₁₂.gpr, u₁₂.other .eax (by decide), u₁₂.other .edx (by decide),
      e₁₁, u₁₁.other .eax (by decide), u₁₁.other .ecx (by decide), u₁₀.other .eax (by decide),
      u₁₀.other .ecx (by decide), u₉.other .eax (by decide), u₉.other .ecx (by decide), u₈.other .eax (by decide),
      u₈.other .ecx (by decide), u₇.other .ecx (by decide), u₆.other .ecx (by decide), u₅.other .ecx (by decide),
      u₄.other .ecx (by decide), sel]
  have val : s₁₄.gpr .eax = BitVec.ofNat 32 (countV base index (rl == lane)) := by
    rw [e₁₄, countV]
    by_cases hs : rl = lane
    · simp only [decide_eq_true hs, show (rl == lane) = true from beq_iff_eq.mpr hs, ↓reduceIte]
      rw [e₃, BitVec.ofNat_add_ofNat, Wp.ofNat_pred (hsame hs)]
    · simp only [decide_eq_false hs, show (rl == lane) = false from beq_eq_false_iff_ne.mpr hs, ↓reduceIte,
        Bool.false_eq_true]
      rw [e₇]
      by_cases hi0 : index = 0
      · rw [decide_eq_true hi0, ite_eq_left (rfl : true = true), ite_eq_left hi0,
          add_allOnes (hother hs hi0) (by omega)]
      · rw [decide_eq_false hi0, ite_eq_right (by decide : ¬(false = true)), ite_eq_right hi0, Nat.sub_zero]
        simp
  refine wp_stloc hp h₁₄.fs.inv (d := countOff) (by decide) fun t it vt ot gt mt => k t ?_ (by rw [gt, val])
    (by rw [vt, val]) (fun e he hd => by rw [ot e he hd, m K₁₄]) (fun r a b c => by rw [gt, K₁₄.other r a b c])
  exact h₁₄.store hp it (d := countOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt

end

end VG.Proof.Argon2.X86.Derive
