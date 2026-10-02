import VerifiedGarbage.Proof.Ed25519.Arm.MulKeep

/-! The scalar input remains unchanged throughout table construction
and descending accumulation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem mulRegions_sub {b : BitVec 32} {o n : Nat} (hn : o + n ≤ 8192) :
    ∀ r ∈ mulRegions b o n, r.Sub ⟨State.addr b, 8192⟩ := by
  intro r hr
  simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.sub_base _ (by omega)

structure MulInput (b p : BitVec 32) (n scalar : Nat) (s : State) : Prop where
  bound : n ≤ 32
  fit : p.toNat + 2 * n ≤ 2 ^ 32
  readable : ∀ i < 2 * n, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1
  separate : (⟨State.addr p, 2 * n⟩ : Region).Disjoint ⟨State.addr b, 8192⟩
  pointer : s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p
  value : val16 (packedLimb s.mem (State.addr p)) n = scalar

theorem MulInput.keep {b p : BitVec 32} {n scalar o len : Nat} {s t : State}
    (h : MulInput b p n scalar s) (hk : MulKeep b o len s t)
    (ho : 1600 ≤ o) (hn : o + len ≤ 8192) : MulInput b p n scalar t := by
  refine ⟨h.bound, h.fit, ?_, h.separate, (hk.word ho hn 52 (.inr rfl)).trans h.pointer, ?_⟩
  · intro i hi
    rw [hk.rest.rd, hk.rest.wr]
    exact h.readable i hi
  · have hb : ∀ i < 2 * n, t.mem (State.addr p + BitVec.ofNat 64 i) =
        s.mem (State.addr p + BitVec.ofNat 64 i) :=
      fun i hi => hk.frame.bytes (fun r hr => h.separate.sub_right (mulRegions_sub hn r hr))
        (by have := h.bound; omega : 2 * n ≤ 2 ^ 64) hi
    refine (val16_congr fun j hj => ?_).trans h.value
    simp only [packedLimb, byteN, hb (2 * j) (by omega), hb (2 * j + 1) (by omega)]

end VG.Proof.Ed25519.Arm
