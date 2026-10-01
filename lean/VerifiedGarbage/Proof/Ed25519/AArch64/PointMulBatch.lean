import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCounter

/-! Untrusted: frames for the batches of the scalar multiplications. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem PowersKeep.of_keeps {base : Addr} {o n : Nat} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : PowersKeep base o n s t := by
  refine ⟨fun r hb hs hr => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hb h
    · exact hs h
    · exact hr h
  · rw [h.mem]; exact TableFrame.refl _ _ _ _

theorem PowersKeep.of_counter {base : Addr} {o n : Nat} {s t : State} (h : CounterKeep base s t) :
    PowersKeep base o n s t := ⟨fun r hb _ hr => h.gpr r hr hb, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

theorem header_env {base : Addr} {m m' : Mem} (h : Outside base 56 8 m m') : env m' base = env m base := by
  funext i
  exact Outside_F h (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

theorem TableFrame.bits {base : Addr} {m m' : Mem} (h : TableFrame base 5376 2048 m m')
    (i : Nat) (hi : i < 512) : m' (off base (768 + i)) = m (off base (768 + i)) := by
  apply h
  · rw [ofs_off' base (by omega)]; omega
  · rw [ofs_off' base (by omega)]; omega

end VG.Proof.Ed25519.AArch64
