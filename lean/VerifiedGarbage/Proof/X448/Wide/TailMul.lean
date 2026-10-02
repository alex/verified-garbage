import VerifiedGarbage.Proof.X448.Wide.TailSquare

/-! Untrusted: choose cached squaring from public, static field-slot indices. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem tailMul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.X448.AArch64.Tail.mul o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  rw [Impl.X448.AArch64.Tail.mul]
  by_cases h : a = b
  · rw [ite_eq_left h, ← h]
    exact tailSquare_ok hs ho ho8 ha ha8 ab
  · rw [ite_eq_right h]
    exact tailProduct_ok hs ho ho8 ha ha8 hb hb8 ab bb

end VG.Proof.X448.Wide
