import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Sym
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Finish

/-!
# ChaCha20 on x86-64 with AVX-512: the sixteen input states

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word stateAt)
open VG.Proof.ChaCha20

/-- The counter increments `0, …, 15`, as doublewords at `buf + 128`. -/
def Incs (m : Mem) (buf : Addr) : Prop :=
  ∀ j < 16, m.readW (buf + BitVec.ofNat 64 (4 * (32 + j))) 32 = BitVec.ofNat 32 j

/-- Word `k` of block `p` after the setup: word `k` of the state, plus `p`
for the counter. -/
def setupT (k p : Nat) : T := if k = 12 then .add (.mem 0 12) (.mem 1 (32 + p)) else .mem 0 k

def setupCheck : Bool :=
  match Sym.init.run setup with
  | some σ => !σ.dirty && (List.range 16).all fun k => (List.range 16).all fun p => σ.reg k p == setupT k p
  | none => false

theorem setupCheck_eq : setupCheck = true := by decide +kernel

theorem setup_run : ∃ σ, Sym.init.run setup = some σ ∧ σ.dirty = false ∧
    ∀ k < 16, ∀ p < 16, σ.reg k p = setupT k p := by
  have e := setupCheck_eq
  unfold setupCheck at e
  split at e
  · rename_i σ h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, h, e.1, e.2⟩
  · cases e

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 16) :
    m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = (stateAt m p)[k] := by
  simp [stateAt]

theorem setup_ok {s : State} (hc : Ctx s) (hi : Incs s.mem (s.gpr .rcx)) :
    WP isa (.block setup) s fun s' =>
      ZH (fun j => ctr (stateAt s.mem (s.gpr .rdi)) j) s' ∧ s'.mem = s.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨σ, hr, hd, hk⟩ := setup_run
  refine WP.mono (srun_ok hc setup (SRel.init s) hr) fun s' h => ⟨fun r j hj => ?_,
    h.clean hd, h.gpr, h.rd, h.wr⟩
  rw [h.reg r j hj, hk _ (xidx_lt r) j hj, Avx2.ctr_get _ _ _ (xidx_lt r)]
  simp only [setupT]
  split
  · simp only [T.eval, regn, baseR]
    rw [stateAt_get _ _ (by decide), hi j hj]
  · simp only [T.eval, regn, baseR]
    exact stateAt_get _ _ (xidx_lt r)

end VG.Proof.ChaCha20.X86_64.Avx512
