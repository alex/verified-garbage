import VerifiedGarbage.Proof.X448.Arm.Field
import VerifiedGarbage.Proof.Framework.Range

/-!
# X448 on ARMv7: filling words with zero

Each store touches only its designated word in the working space.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

theorem storeOne_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) (r : Reg) : WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ Keeps [] s t := by
  refine store_ok hs hd fun t ht => WP.block_nil ⟨ht.mem, rest_keeps (ht.rest _)⟩

theorem zeroR3_ok (s : State) : WP isa (.block [.mov .r3 (.imm 0)]) s fun t =>
    t.gpr .r3 = 0 ∧ t.mem = s.mem ∧ Keeps [.r3] s t := by
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide))
    fun t ht => WP.block_nil ⟨ht.gpr, ht.mem, rest_keeps (ht.rest (by decide))⟩

theorem fill_ok {s : State} {base : Addr} (hs : Scr s base) {o n : Nat} (ho : o + 4 * n ≤ 4096)
    (hz : s.gpr .r3 = 0) :
    WP isa (.block ((List.range n).map (fun i => st .r3 (o + 4 * i)))) s fun t =>
      (∀ i < n, limbs t.mem base o i = 0) ∧ Outside base o (4 * n) s.mem t.mem ∧ Keeps [] s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, limbs t.mem base o i = 0) ∧ Outside base o (4 * n) s.mem t.mem ∧ Keeps [] s t
  have step : ∀ k t, k < n → inv k t →
      WP isa (.block [st .r3 (o + 4 * k)]) t (inv (k + 1)) := by
    intro k t hk ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (storeOne_ok ts (by omega) .r3) fun u ⟨um, uk⟩ => ?_
    rw [tk.1 .r3 (by decide), hz] at um
    have out : Outside base (o + 4 * k) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by omega) (by omega)]
    by_cases h : i = k
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := n) inv step n (by omega) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm
