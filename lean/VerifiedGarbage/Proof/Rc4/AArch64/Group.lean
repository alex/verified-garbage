import VerifiedGarbage.Proof.Rc4.AArch64.Lanes

/-!
# The groups

`group_ok`: sixteen lanes and the rotation take a group with base `B` that
starts after `p` bytes to the next group, with base `B + 16`, after
`min N (p + 16 - sk)` bytes and no lanes to skip. `loop_ok`: the groups run
until the data has ended.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem lanesFrom_ok (g : Glob) (hg : DataOk g) {B p sk : Nat} (hsk : sk ≤ 15) {n : Nat} (hn : n ≤ 16)
    {s : State} (h : LaneInv g B p sk 0 s) : WP isa (lanesFrom n) s (LaneInv g B p sk n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    exact WP.seq (WP.mono (ih (by omega)) fun t ht => lane_ok g hg hsk (by omega) ht)

theorem ofNat_wrap (B k : Nat) : BitVec.ofNat 8 (B + (k + 16) % 256) = BitVec.ofNat 8 (B + 16 + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem byte_shift (x : BitVec 8) (B : Nat) : x - bB B - 16 = x - bB (B + 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
  omega

theorem treg_step : ∀ a < 16, treg a ∈ stepRegs := by decide

theorem group_ok (g : Glob) (hg : DataOk g) {B p sk : Nat} (hsk : sk ≤ 15) {s : State}
    (h : LaneInv g B p sk 0 s) :
    WP isa group s (LaneInv g (B + 16) (doneAt g p sk 16) 0 0) := by
  apply WP.seq (WP.mono (lanesFrom_ok g hg hsk (Nat.le_refl 16) h) fun s₁ h₁ => ?_)
  refine WP.mono (rotate_ok true h₁.prga.consts h₁.prga.j fun _ => h₁.prga.nb) fun t ⟨tab, j, nb, x8, gg, vv, m, rd, wr, sp⟩ => ?_
  have hd0 : doneAt g (doneAt g p sk 16) 0 0 = doneAt g p sk 16 := by
    have := h₁.data.le; simp only [doneAt] at this ⊢; omega
  let q := doneAt g p sk 16
  have notRot : ∀ r, r ∉ rotRegs → r ∉ stepRegs ∨ r = negBase → True := fun _ _ _ => trivial
  exact {
    prga := by
      rw [hd0]
      refine ⟨fun k hk => ?_, ?_, ?_, ?_⟩
      · rw [tab k hk, h₁.prga.table _ (by omega), ofNat_wrap]
      · rw [j, byte_shift]
      · simp only [ite_true] at nb; rw [nb, byte_shift]
      · exact h₁.prga.consts.congr fun r hr => vv r (by
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    data := by
      rw [hd0]
      exact ⟨h₁.data.le, by rw [gg _ (by decide), h₁.data.x1], by rw [gg _ (by decide), h₁.data.x2],
        fun k hk => by rw [m]; exact h₁.data.bytes k hk, by rw [m]; exact h₁.data.frame⟩
    x5 := by rw [gg _ (by decide), h₁.x5]; congr 1; omega
    x8 := by
      rw [x8, h₁.x8, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
    next := by
      rw [hd0]
      intro hlt
      obtain ⟨hi, hsi⟩ := h₁.next hlt
      rw [show max 16 sk = 16 by omega] at hi hsi
      refine ⟨by rw [hi]; simp, ?_⟩
      rw [vv _ (by decide), hsi, show max 0 0 = 0 from rfl, tab 0 (by decide)]
    kept := ⟨fun r a b c d e f => by rw [gg r f, h₁.kept.gpr r a b c d e f], rd.trans h₁.kept.rd,
      wr.trans h₁.kept.wr, sp.trans h₁.kept.sp⟩
    vkept := fun r hr hn => by
      rw [vv r (by
        simp only [rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists, not_and]
        refine ⟨fun e => hr (by rw [e]; decide), fun e => hr (by rw [e]; decide), hn,
          fun a ha e => hr (e ▸ treg_step a ha)⟩), h₁.vkept r hr hn] }

/-- A group about to start, `m` bytes before the end. -/
def LoopInv (g : Glob) (m : Nat) (s : State) : Prop :=
  ∃ B p sk, B % 16 = 0 ∧ m = g.N - p ∧ p < g.N ∧ sk ≤ 15 ∧ LaneInv g B p sk 0 s

/-- The data has ended. -/
def LoopDone (g : Glob) (s : State) : Prop := ∃ B sk, B % 16 = 0 ∧ LaneInv g B g.N sk 0 s

theorem loop_ok (g : Glob) (hg : DataOk g) (m : Nat) {s : State} (h : LoopInv g m s) :
    WP isa (.loop group (.nonzero .x .x2)) s (LoopDone g) := by
  refine WP.loop (M := isa) (LoopInv g) ?_ m s h
  intro m s ⟨B, p, sk, hB, hm, hp, hsk, h⟩
  refine WP.mono (group_ok g hg hsk h) fun t ht => ?_
  have hfit := hg.fit
  let q := doneAt g p sk 16
  have hd0 : doneAt g q 0 0 = q := by
    have := ht.data.le; simp only [doneAt, q] at this ⊢; omega
  have hq : q ≤ g.N := by have := ht.data.le; rw [hd0] at this; exact this
  have x2 : t.gpr .x2 = BitVec.ofNat 64 (g.N - q) := by rw [ht.data.x2, hd0]
  have flag := eval_nonzero' t .x2 x2 (by omega)
  by_cases hend : q = g.N
  · left
    exact ⟨by rw [flag]; simp [hend], B + 16, 0, by omega, hend ▸ ht⟩
  · right
    exact ⟨by rw [flag]; simp; omega, g.N - q, by simp only [doneAt, q] at hend ⊢; omega,
      B + 16, q, 0, by omega, rfl, by omega, by decide, ht⟩

end VG.Proof.Rc4.AArch64
