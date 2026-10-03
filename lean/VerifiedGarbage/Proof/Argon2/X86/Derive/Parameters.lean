import VerifiedGarbage.Proof.Argon2.X86.Derive.Locals

/-!
# Argon2 on x86 (32-bit): the parameters

`parameters_ok`: the body's first instructions point `ebp` to the locals and
store there `4 · lanes` (the divisor), the segment length (by the fixed-time
division), the lane length and its size in bytes (`Prm`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_add wp_addi wp_movi wp_mov)
open VG.Impl.Argon2.X86.Derive (parameters divisorOff segLenOff laneLenOff strideOff argOff)

/-- The parameters in the locals. -/
structure Prm (s₀ s : State) : Prop where
  divisor : lw s₀ s divisorOff = BitVec.ofNat 32 (4 * lanesN s₀)
  segLen : lw s₀ s segLenOff = BitVec.ofNat 32 (prm s₀).segmentLen
  laneLen : lw s₀ s laneLenOff = BitVec.ofNat 32 (prm s₀).laneLen
  stride : lw s₀ s strideOff = BitVec.ofNat 32 ((prm s₀).laneLen * 1024)

/-- `add ecx, ecx`, `n` times. -/
theorem dbl_ok {s : State} {is : List Instr} {Q : State → Prop} :
    ∀ n, (s.gpr .ecx).toNat * 2 ^ n < 2 ^ 32 →
      (∀ t, (t.gpr .ecx).toNat = (s.gpr .ecx).toNat * 2 ^ n → Divide.Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (List.replicate n (.alu .add .ecx (.reg .ecx)) ++ is)) s Q
  | 0, _, k => k s (by simp) (Divide.Keep.refl s)
  | n + 1, hn, k => by
    rw [List.replicate_succ, List.cons_append]
    have e : (s.gpr .ecx).toNat * 2 ^ (n + 1) = (s.gpr .ecx).toNat * 2 * 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
    have hx : (s.gpr .ecx).toNat ≤ (s.gpr .ecx).toNat * 2 ^ n :=
      Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
    have two : (s.gpr .ecx).toNat * 2 < 2 ^ 32 := by
      have := Nat.mul_le_mul_right 2 hx
      rw [Nat.mul_right_comm] at this
      rw [e] at hn
      omega
    refine wp_add fun s₁ u₁ _ => dbl_ok (s := s₁) n ?_ fun t ht kt => k t ?_
      ((Divide.Keep.of_upd u₁ (by simp)).trans kt)
    · rw [u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), ← Nat.two_mul, Nat.mul_comm 2]
      rw [e] at hn; exact hn
    · rw [ht, u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), ← Nat.two_mul, Nat.mul_comm 2, e]

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : lw s₀ t d = lw s₀ s d := by
  simp only [lw, h]

theorem Inv.keep {s₀ s t : State} (h : Inv s₀ s) (k : Divide.Keep s t) : Inv s₀ t :=
  h.step (k.other _ (by decide) (by decide) (by decide)) (k.other _ (by decide) (by decide) (by decide))
    k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem parameters_ok {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block ((.mov .ebp (.reg .esp) :: parameters) ++ is)) (entry s₀) Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hBl := hp.blocks_lt
  have hb := hp.blocks_eq
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, Impl.Argon2.X86.Derive.fr, List.cons_append, List.append_assoc]
  refine inv_start fun s₁ i₁ _ _ => ?_
  refine wp_ldarg hp i₁ (i := Impl.Argon2.X86.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => ?_
  have i₄ := (i₂.upd u₃ (by decide) (by decide)).upd u₄ (by decide) (by decide)
  have e₄ : (s₄.gpr .eax).toNat = 4 * lanesN s₀ := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr]
    simp only [BitVec.toNat_add]
    show (((arg s₀ 7).toNat + (arg s₀ 7).toNat) % 2 ^ 32 + ((arg s₀ 7).toNat + (arg s₀ 7).toNat) % 2 ^ 32)
      % 2 ^ 32 = 4 * (arg s₀ 7).toNat
    have : (arg s₀ 7).toNat < 2 ^ 24 := hL
    omega
  refine wp_stloc hp i₄ (d := divisorOff) (by decide) fun s₅ i₅ v₅ _ g₅ _ => ?_
  refine wp_ldarg hp i₅ (i := Impl.Argon2.X86.Derive.memoryCostArg) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide) (by decide)
  have d₆ : lw s₀ s₆ divisorOff = s₄.gpr .eax := by rw [lw_mem u₆.mem, v₅]
  refine Divide.code_ok (D := s₄.gpr .eax) (by rw [e₄]; omega) (by rw [e₄]; omega) i₆.ebp
    (loc_in' hp i₆ (by decide)) d₆ fun s₇ c₇ _ k₇ => ?_
  have i₇ := i₆.keep k₇
  rw [u₆.gpr, e₄] at c₇
  have c₇' : (s₇.gpr .ecx).toNat = (prm s₀).segmentLen := by rw [c₇, hseg]; rfl
  refine wp_stloc hp i₇ (d := segLenOff) (by decide) fun s₈ i₈ v₈ o₈ g₈ _ => ?_
  have hll : (prm s₀).laneLen ≤ blocksN s₀ :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)
  have hsegL : (prm s₀).laneLen * 1024 + 16384 ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 1024 hll) _) hBl
  refine wp_add fun s₉ u₉ _ => wp_add fun s₁₀ u₁₀ _ => ?_
  have i₁₀ := (i₈.upd u₉ (by decide) (by decide)).upd u₁₀ (by decide) (by decide)
  have e₁₀ : (s₁₀.gpr .ecx).toNat = (prm s₀).laneLen := by
    rw [u₁₀.gpr, u₉.gpr, g₈]
    simp only [BitVec.toNat_add, c₇']
    omega
  refine wp_stloc hp i₁₀ (d := laneLenOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ g₁₁ _ => ?_
  refine dbl_ok 10 (by rw [g₁₁, e₁₀]; omega) fun s₁₂ e₁₂ k₁₂ => ?_
  have i₁₂ := i₁₁.keep k₁₂
  refine wp_stloc hp i₁₂ (d := strideOff) (by decide) fun s₁₃ i₁₃ v₁₃ o₁₃ _ _ => k s₁₃ i₁₃ ⟨?_, ?_, ?_, ?_⟩
  · rw [o₁₃ _ (by decide) (by decide), lw_mem k₁₂.mem, o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem,
      lw_mem u₉.mem, o₈ _ (by decide) (by decide), lw_mem k₇.mem, lw_mem u₆.mem, v₅]
    exact BitVec.eq_of_toNat_eq (by rw [e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₃ _ (by decide) (by decide), lw_mem k₁₂.mem, o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem,
      lw_mem u₉.mem, v₈]
    exact BitVec.eq_of_toNat_eq (by rw [c₇', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₃ _ (by decide) (by decide), lw_mem k₁₂.mem, v₁₁]
    exact BitVec.eq_of_toNat_eq (by rw [e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [v₁₃]
    exact BitVec.eq_of_toNat_eq (by
      rw [e₁₂, g₁₁, e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])

end

end VG.Proof.Argon2.X86.Derive
