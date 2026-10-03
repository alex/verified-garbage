import VerifiedGarbage.Proof.Argon2.AArch64.DeriveAbi
import VerifiedGarbage.Proof.Argon2.AArch64.DerivePrivatePrepare
import VerifiedGarbage.Proof.Argon2.AArch64.DeriveSaved

/-! Private frame permissions and caller argument values after the ABI prologue. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def prologueState (s : State) : State := frameStart s Impl.Argon2.AArch64.Derive.saved

theorem prologue_sp (s : State) : (prologueState s).sp = s.sp - BitVec.ofNat 64 384 :=
  frameStart_sp s _

theorem frameStart_locals (s : State) (rs : List Reg) :
    (⟨(frameStart s rs).sp, 272⟩ : Region) ∈ (frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => exact List.mem_cons_self ..
  | cons r rs ih => exact ih (pushed r s)

theorem prologue_locals (s : State) : Covers [⟨(prologueState s).sp, 272⟩] (prologueState s).wr := by
  intro p n ⟨region, member, contains⟩
  simp only [List.mem_singleton] at member; subst region
  exact ⟨_, frameStart_locals s _, contains⟩

theorem prologue_source (s : State) (j : Nat) :
    (prologueState s).sp + BitVec.ofNat 64 (copySource j) =
      s.sp + BitVec.ofNat 64 (8 * j) := by
  rw [prologue_sp]
  unfold copySource
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem prologue_reads {s : State} (h : AbiEnvironment s) :
    ∀ j < 10, InRegions ((prologueState s).rd ++ (prologueState s).wr)
      ((prologueState s).sp + BitVec.ofNat 64 (copySource j)) 8 := by
  intro j hj
  rw [prologue_source]
  refine ⟨abiArguments s, List.mem_append_left _ ?_, ?_⟩
  · change abiArguments s ∈ (frameStart s Impl.Argon2.AArch64.Derive.saved).rd
    rw [frameStart_rd, h.rd]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · unfold abiArguments
    exact Offset.contains_base _ (by omega) (by omega)

theorem prologue_word {s : State} (h : AbiEnvironment s) (j : Nat) (hj : j < 10) :
    (prologueState s).mem.readW ((prologueState s).sp + BitVec.ofNat 64 (copySource j)) 64 =
      abiWord s (8 * j) := by
  rw [prologue_source]
  have frame := frameStart_frame s Impl.Argon2.AArch64.Derive.saved (by
    have space := h.stack; change 384 ≤ s.sp.toNat; omega)
  apply frame.readW (r := abiArguments s) ?_ ?_ (by decide)
  · unfold abiArguments
    exact Offset.contains_base _ (by omega) (by omega)
  · intro region hr
    simp only [List.mem_singleton] at hr; subst region
    unfold abiArguments
    exact Offset.base_disjoint_below _ (by decide)

theorem prologue_prepare (s : State) (h : AbiEnvironment s) :
    WP isa Impl.Argon2.AArch64.Derive.prepare (prologueState s) (PrivatePrepared (prologueState s)) :=
  private_prepare_ok _ (prologue_locals s) (prologue_reads h)

end VG.Proof.Argon2.AArch64.Derive
