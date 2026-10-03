import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Schedule
import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed5
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64
open VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Spec.ChaCha20 (innerBlock)

def scalarKeepsV : Bool := (VG.Impl.ChaCha20.AArch64.doubleRound.allInstrs fun i =>
  match vdstOf i with | none => true | _ => false)

theorem scalar_round_vectors {v : CState} {s : State} (h : VG.Proof.ChaCha20.AArch64.Holds v s) :
    WP isa VG.Impl.ChaCha20.AArch64.doubleRound s fun u =>
      VG.Proof.ChaCha20.AArch64.RI (innerBlock v) s u ∧ u.v = s.v ∧ u.sp = s.sp := by
  have hp := VG.Proof.ChaCha20.AArch64.doubleRound_ok (s₀ := s) ⟨h,rfl,rfl,rfl,fun _ _ => rfl⟩
  obtain ⟨t,u,he,hu⟩ := hp
  have hv : scalarKeepsV = true := by decide +kernel
  rw [scalarKeepsV, Code.allInstrs_eq] at hv
  refine ⟨t,u,he,hu,?_,Exec.sp he⟩
  apply funext
  intro r
  apply Exec.vec (c := VG.Impl.ChaCha20.AArch64.doubleRound) (r := r) ?_ he
  intro i hi
  have h' := List.all_eq_true.mp hv i hi
  cases hdst : vdstOf i <;> simp only [hdst, Bool.false_eq_true] at h'
  simp

theorem parallelRound_ok {vs : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hc : VG.Proof.ChaCha20.AArch64.Holds v s) :
    WP isa parallelRound s fun u =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => innerBlock (vs j)) u ∧ VG.Proof.ChaCha20.AArch64.Holds (innerBlock v) u ∧
      VG.Proof.ChaCha20.AArch64.RI (innerBlock v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  refine (Scheduled.ops_ok roundOps Scheduled.roundOps_valid hn ht hc).mono fun u ⟨hu,hr,hsp,hut⟩ => ?_
  simp only [roundOps, VG.Proof.ChaCha20.AArch64.Neon4.innerBlock_eq] at hu hr
  exact ⟨hu,hr.holds,hr,hsp,hut⟩

theorem rounds_ok {vs : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hc : VG.Proof.ChaCha20.AArch64.Holds v s) :
    ∀ n, WP isa (rounds n) s fun u =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock n (vs j)) u ∧
      VG.Proof.ChaCha20.AArch64.RI (Nat.repeat innerBlock n v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  | 0 => WP.block_nil ⟨hn,⟨hc,rfl,rfl,rfl,fun _ _ => rfl⟩,rfl,ht⟩
  | n + 1 => by
    apply WP.seq
    refine (rounds_ok hn ht hc n).mono fun a ⟨ha,hca,hsp,hat⟩ => ?_
    refine (parallelRound_ok ha hat hca.holds).mono fun b ⟨hb,_,hab,hsp',hbt⟩ =>
      ⟨hb,⟨hab.holds,hab.mem.trans hca.mem,hab.rd.trans hca.rd,hab.wr.trans hca.wr,
        fun r hr => (hab.keep r hr).trans (hca.keep r hr)⟩,hsp'.trans hsp,hbt⟩

end VG.Proof.ChaCha20.AArch64.Mixed5
