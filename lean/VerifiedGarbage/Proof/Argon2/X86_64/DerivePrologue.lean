import VerifiedGarbage.Proof.Argon2.X86_64.DeriveAbi
import VerifiedGarbage.Proof.Argon2.X86_64.DerivePrivatePrepare
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveSaved

/-! Private frame permissions and caller argument values after the ABI prologue. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def prologueState (s : State) : State := frameStart s Impl.Argon2.X86_64.Derive.saved

theorem prologue_sp (s : State) : (prologueState s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 320 :=
  frameStart_sp s _

theorem frameStart_locals (s : State) (rs : List Reg) :
    (⟨(frameStart s rs).gpr .rsp, 272⟩ : Region) ∈ (frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => rw [frameStart, pushed_wr, pushed_rsp]; exact List.mem_cons_self ..
  | cons r rs ih => exact ih (pushed [r] s)

theorem prologue_locals (s : State) : Covers [⟨(prologueState s).gpr .rsp, 272⟩] (prologueState s).wr := by
  intro p n ⟨region, member, contains⟩
  simp only [List.mem_singleton] at member; subst region
  exact ⟨_, frameStart_locals s _, contains⟩

theorem prologue_source (s : State) (j : Nat) :
    (prologueState s).gpr .rsp + BitVec.ofNat 64 (copySource j) =
      s.gpr .rsp + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [prologue_sp]
  unfold copySource
  rw [show 328 + 8 * j = 320 + 8 * (j + 1) by omega,
    BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem prologue_reads {s : State} (h : AbiEnvironment s) :
    ∀ j < 12, InRegions ((prologueState s).rd ++ (prologueState s).wr)
      ((prologueState s).gpr .rsp + BitVec.ofNat 64 (copySource j)) 8 := by
  intro j hj
  rw [prologue_source]
  refine ⟨abiArguments s, List.mem_append_left _ ?_, ?_⟩
  · change abiArguments s ∈ (frameStart s Impl.Argon2.X86_64.Derive.saved).rd
    rw [frameStart_rd, h.rd]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · unfold abiArguments
    rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.contains_base _ (by omega) (by omega)

theorem prologue_word {s : State} (h : AbiEnvironment s) (j : Nat) (hj : j < 12) :
    (prologueState s).mem.readW ((prologueState s).gpr .rsp + BitVec.ofNat 64 (copySource j)) 64 =
      abiWord s (8 * (j + 1)) := by
  rw [prologue_source]
  have frame := frameStart_frame s Impl.Argon2.X86_64.Derive.saved (by decide) (by
    have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega)
  apply frame.readW (r := abiArguments s) ?_ ?_ (by decide)
  · unfold abiArguments
    rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.contains_base _ (by omega) (by omega)
  · intro region hr
    simp only [List.mem_singleton] at hr; subst region
    unfold abiArguments
    exact Offset.disjoint_below _ (by decide)

theorem prologue_prepare (s : State) (h : AbiEnvironment s) :
    WP isa Impl.Argon2.X86_64.Derive.prepare (prologueState s) (PrivatePrepared (prologueState s)) :=
  private_prepare_ok _ (prologue_locals s) (prologue_reads h)

end VG.Proof.Argon2.X86_64.Derive
