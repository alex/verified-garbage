import VerifiedGarbage.Proof.Argon2.AArch64.FillBlock
import VerifiedGarbage.Proof.Argon2.AArch64.RandomSourceCounter

/-! Compression preserves the public cache counter selected by the random source. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

theorem counter_run {s t : State} {trace : List Leak} {p : Params} {pass lane slice index old : Nat}
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (run : Exec isa Impl.Argon2.AArch64.FillBlock.code s trace t) :
    t.mem.readW (off (t.gpr .x19) 8) 64 = RandomSource.counterValue p pass slice index old := by
  cases run with
  | seq sourceRun kernelRun =>
    obtain ⟨_, a', runA, source⟩ := RandomSource.code_ok s p pass lane slice index old h state represented
    obtain ⟨_, rfl⟩ := Exec.det sourceRun runA
    obtain ⟨_, a', counterRun, counter⟩ := RandomSource.counter_ok s p pass lane slice index old h
    obtain ⟨_, rfl⟩ := Exec.det sourceRun counterRun
    obtain ⟨_, ready⟩ := source.ready
    obtain ⟨_, t', runT, done⟩ := FillKernel.code_ok _ p pass lane slice index ready.filling
    obtain ⟨_, rfl⟩ := Exec.det kernelRun runT
    exact (done.frame_word ready.filling 8 (by decide) (by decide)).trans counter

end VG.Proof.Argon2.AArch64.FillBlock
