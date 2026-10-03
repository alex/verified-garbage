import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20 (xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre L)

variable {sve : Bool}

theorem nonzero_short {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 512 then 1 else 0)) :
    isa.eval (.nonzero .x .x5) s = some (decide (n < 512)) := by
  rw [show isa.eval (.nonzero .x .x5) s = some (!(s.gpr .x5 == 0)) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero s .x5,h]
  by_cases hn : n < 512 <;> simp [hn]

theorem correct_aux (s : State) (hs : xorAArch64.pre s) :
    WP isa (Impl.ChaCha20.AArch64.Mixed8.xor sve) s fun u => GprAbi s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 ∧
      (u.v .v8).extractLsb' 0 64 = (s.v .v8).extractLsb' 0 64 ∧
      (u.v .v9).extractLsb' 0 64 = (s.v .v9).extractLsb' 0 64 := by
  apply WP.seq
  refine (init_ok s).mono fun a ⟨hi,hcs,h5,hv⟩ => ?_
  apply WP.seq
  have hb : WP isa (.ite (.nonzero .x .x5) (.block [])
      (.seq (.block enter) (.seq (.loop (body sve) (.zero .x .x5)) (.block leave)))) a fun u =>
      ∃ t, LInv s t u ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧
        u.v .v8 = s.v .v8 ∧ u.v .v9 = s.v .v9 := by
    apply WP.ite (decide (L s < 512)) (nonzero_short h5)
    · intro _; exact WP.block_nil ⟨0,hi,hcs,congrFun hv .v8,congrFun hv .v9⟩
    · intro hshort
      have hge : 512 ≤ L s := by have hh := of_decide_eq_false hshort; omega
      apply WP.seq
      refine (enter_ok (XPre.of s hs) hi hcs hv).mono fun b hb => ?_
      apply WP.seq
      refine (bulk_ok (XPre.of s hs) hb hge).mono fun c ⟨t,_,hc⟩ => ?_
      exact (leave_ok (XPre.of s hs) hc).mono fun _ ⟨hd,hcs,h8,h9⟩ => ⟨t,hd,hcs,h8,h9⟩
  refine hb.mono fun u ⟨t,hu,hcs,h8,h9⟩ => ?_
  refine (WP.preservedV (tail_ok (XPre.of s hs) hu hcs) (hc := by lit_decide)).mono ?_
  intro v ⟨⟨ha,hp,h0,h1⟩,hvec⟩
  exact ⟨ha,hp,h0,h1,by rw [hvec .v8 (by decide),h8],by rw [hvec .v9 (by decide),h9]⟩

theorem correct (s : State) (hs : xorAArch64.pre s) :
    WP isa (Impl.ChaCha20.AArch64.Mixed8.xor sve) s fun u => abiPreserved s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 := by
  obtain ⟨t,u,he,ha,hp,h0,h1,h8,h9⟩ := correct_aux s hs
  refine ⟨t,u,he,⟨ha.1,ha.2,?_⟩,hp,h0,h1⟩
  intro r hr
  by_cases he8 : r = .v8
  · subst r; exact h8
  by_cases he9 : r = .v9
  · subst r; exact h9
  have hc : (Impl.ChaCha20.AArch64.Mixed8.xor sve).allInstrs Rows6.keepsOtherV = true := by cases sve <;> lit_decide
  rw [Exec.vec (fun i hi => Rows6.keepsOtherV_ne (List.all_eq_true.mp
    ((Code.allInstrs_eq Rows6.keepsOtherV (Impl.ChaCha20.AArch64.Mixed8.xor sve)) ▸ hc) i hi) hr he8 he9) he]

theorem xor_correct (s : State) (hs : xorAArch64.pre s) :
    ∃ t u, Exec isa (Impl.ChaCha20.AArch64.Mixed8.xor sve) s t u ∧ abiPreserved s u ∧ xorAArch64.post s u :=
  (correct s hs).imp fun _ ⟨u,he,ha,hp,_⟩ => ⟨u,he,ha,hp⟩

theorem xor_noFrames : (Impl.ChaCha20.AArch64.Mixed8.xor sve).noFrames = true := by cases sve <;> lit_decide

theorem xor_ct : ConstantTime isa xorAArch64.pre xorAArch64.pub (Impl.ChaCha20.AArch64.Mixed8.xor sve) := by
  cases sve <;>
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ hp => Xor.agree₀ hp) (by taint_decide)

theorem xor_verified : Verified AArch64.target (Impl.ChaCha20.AArch64.Mixed8.xor sve)
    (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract,Spec.ChaCha20.xorSig,AArch64.abi,AArch64.argRegs,
      xorAArch64] [Xor.sat] using Xor.sat)
end VG.Proof.ChaCha20.AArch64.Mixed8
