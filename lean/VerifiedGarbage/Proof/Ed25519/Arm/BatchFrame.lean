import VerifiedGarbage.Proof.Ed25519.Arm.BatchCounter

/-! Untrusted: the saved batch counter survives the table and bit operations. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem PowersKeep.counter {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by decide) (by omega)

theorem LoopKeep.counter {b : BitVec 32} {s t : State} (h : LoopKeep b s t) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

theorem bitsFrame_counter {b : BitVec 32} {m m' : Mem}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] m m') :
    m'.readW (State.addr b + BitVec.ofNat 64 56) 32 =
      m.readW (State.addr b + BitVec.ofNat 64 56) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)

theorem smallFrame_table {b : BitVec 32} {m m' : Mem} {o n d : Nat}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64)
    (hd : 1600 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' b d = tablePoint m b d := by
  refine tablePoint_frame h fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

end VG.Proof.Ed25519.Arm
