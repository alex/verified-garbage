import VerifiedGarbage.Proof.Ed25519.X86.Workspace
import VerifiedGarbage.Impl.Ed25519.X86.Field

/-! Full-width constants and field-slot copies. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86 VG.Spec.X25519
open VG.Proof.X25519

theorem slot_valid (o : Slot) : isSlot 64 (offset o) = true := (by decide : ∀ i : Slot, isSlot 64 (offset i) = true) o

theorem fill_step {x : BitVec 32} {s₀ s : State} (hc : Ctx x s) {o n : Nat} (ho : Below o) (hn : n < 8)
    (f : Nat → BitVec 32) (hk : Keep s₀ s) (hf : Frame [sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, wd s.mem x (o + 4 * j) = f j) :
    WP isa (.block [.mov .eax (.imm (f n)), .store (sc (o + 4 * n)) .eax]) s fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, wd s'.mem x (o + 4 * j) = f j := by
  simp only [Below, T] at ho
  have hfit := hc.fit
  refine Wp.wp_movi fun s₁ u₁ => ?_
  have c₁ := (updKeep u₁).ctx hc
  refine Wp.wp_stm c₁.edi (c₁.inW (by omega_using [ho, hn]) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨hk.trans ((updKeep u₁).trans ⟨by rw [u₂.gpr], by rw [u₂.gpr], by rw [u₂.gpr], u₂.rd, u₂.wr⟩),
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact frame_write1 (frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.mem]
    by_cases e : j = n
    · subst e; rw [wd_write_self, u₁.gpr]
    · rw [wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem fill_ok {x : BitVec 32} {s₀ : State} (hc₀ : Ctx x s₀) {o : Nat} (ho : Below o) (f : Nat → BitVec 32) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.imm (f k)), .store (sc (o + 4 * k)) .eax])) s₀ fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * n)] s₀.mem s'.mem ∧
        ∀ j < n, wd s'.mem x (o + 4 * j) = f j
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (fill_ok hc₀ ho f n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      fill_step (k₁.ctx hc₀) ho (by omega_using [hn]) f k₁ f₁ w₁)

theorem num_digits (v n : Nat) :
    num (fun k => v / (2 ^ 32) ^ k % 2 ^ 32) n = v % (2 ^ 32) ^ n := by
  induction n with
  | zero => simp only [num, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [num_succ, ih, Nat.pow_succ (2 ^ 32) n]
    exact Nat.mod_mul.symm

theorem constField_op {s : State} {x : BitVec 32} (hc : Ctx x s) (o : Slot) (v : Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Keep s t ∧ Frame [sub x (offset o) 32] s.mem t.mem ∧ F t.mem x (offset o) = v := by
  refine WP.mono (fill_ok hc (slot_below (slot_valid o))
    (fun k => BitVec.ofNat 32 (v.val / (2 ^ 32) ^ k)) 8 (Nat.le_refl _)) fun t ⟨hk, hf, hv⟩ => ?_
  refine ⟨hk, hf, ?_⟩
  have he : fe t.mem x (offset o) = v.val := by
    unfold fe
    rw [num_congr (g := fun k => v.val / (2 ^ 32) ^ k % 2 ^ 32) (fun k h => by
      rw [wv, hv k h, BitVec.toNat_ofNat]), num_digits]
    exact Nat.mod_eq_of_lt (by have h := v.isLt; simp only [P] at h; omega)
  rw [F, he, toFe_self]

end VG.Proof.Ed25519.X86
