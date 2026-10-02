import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Lit

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20 (xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)
open VG.Spec.ChaCha20 (stateAt bytesAt)

/-- The six other callee-saved vectors are never destinations. -/
def keepsOtherV (i : Instr) : Bool :=
  match vdstOf i with
  | some .v10 | some .v11 | some .v12 | some .v13 | some .v14 | some .v15 => false
  | _ => true

theorem keepsOtherV_ne {i : Instr} (hi : keepsOtherV i = true) {r : VReg}
    (hr : r ∈ preservedV) (h8 : r ≠ .v8) (h9 : r ≠ .v9) : vdstOf i ≠ some r := by
  intro he
  unfold keepsOtherV at hi
  rw [he] at hi
  cases r <;> simp_all [preservedV]

theorem post_save {s a u : State} (hp : XPre s) (hg : a.gpr = s.gpr)
    (hf : Frame [bR s] s.mem a.mem) (hpost : xorAArch64.post a u) :
    xorAArch64.post s u := by
  have hs : stateAt a.mem (st s) = stateAt s.mem (st s) :=
    Xor.stateAt_frame hf (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hp.st_b)
  have hd : bytesAt a.mem (dp s) (L s) = bytesAt s.mem (dp s) (L s) := by
    unfold bytesAt
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    exact hf.bytes (R := dR s) (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hp.d_b)
      (by have := Xor.L_lt s; dsimp; omega) hk'
  simpa only [xorAArch64,hg,hs,hd] using hpost

theorem correct_aux (s : State) (hs : xorAArch64.pre s) :
    WP isa xor s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 ∧
      (u.v .v8).extractLsb' 0 64 = (s.v .v8).extractLsb' 0 64 ∧
      (u.v .v9).extractLsb' 0 64 = (s.v .v9).extractLsb' 0 64 := by
  let hp := XPre.of s hs
  apply WP.seq
  refine (save_ok s hp).mono fun a ⟨hag,hav,har,haw,has,haf,ha8,ha9⟩ => ?_
  have hpre : xorAArch64.pre a := by simpa only [xorAArch64,hag,har,haw] using hs
  let hap := XPre.of a hpre
  apply WP.seq
  have hb : WP isa bulk a fun v => ∃ t, LInv a t v := by
    apply WP.seq
    refine (init_ok a).mono fun b ⟨hi,h5⟩ => ?_
    exact (bulk_ok hap hi h5).mono fun v ⟨t,_,hv⟩ => ⟨t,hv⟩
  refine hb.mono fun v ⟨t,hv⟩ => ?_
  apply WP.seq
  have hdis : ∀ r ∈ [stR a,dR a], (bR a).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hap.st_b.symm
    · exact hap.d_b.symm
  have read_saved (d : Nat) (hd : d + 16 ≤ 320) :
      v.mem.read (v.gpr .x3 + BitVec.ofNat 64 d) 16 =
        a.mem.read (bp s + BitVec.ofNat 64 d) 16 := by
    rw [hv.x3,hv.frame.read (Offset.contains_base _ hd (by omega)) hdis (by decide)]
    rw [show bp a = bp s by simp only [bp,hag]]
  have hin (d : Nat) (hd : d + 16 ≤ 320) :
      InRegions (v.rd ++ v.wr) (v.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [hv.rd,hv.wr,hap.rd,hap.wr,hv.x3]
    exact ⟨bR a,by simp,Offset.contains_base _ hd (by omega)⟩
  refine (restore_ok (s.v .v8) (s.v .v9) (hin 256 (by decide)) (hin 272 (by decide))
    ((read_saved 256 (by decide)).trans ha8) ((read_saved 272 (by decide)).trans ha9)).mono
    fun w ⟨hw8,hw9,hg,hm,hr,hw,hsp⟩ => ?_
  have hwi : LInv a t w := by
    exact ⟨by rw [hg]; exact hv.x0,by rw [hg]; exact hv.x1,
      by rw [hg]; exact hv.x2,by rw [hg]; exact hv.x3,hv.le,
      by intro r h1 h2 h4 h5; rw [hg]; exact hv.keep r h1 h2 h4 h5,
      hr.trans hv.rd,hw.trans hv.wr,hsp.trans hv.sp,
      by rw [hm]; exact hv.cnt,by rw [hm]; exact hv.data,by rw [hm]; exact hv.frame⟩
  refine (WP.preservedV (tail_ok hap hwi) (hc := by lit_decide)).mono ?_
  intro u ⟨⟨ha,hpost,h0,h1⟩,hvec⟩
  refine ⟨⟨?_,ha.2.trans has⟩,post_save hp hag haf hpost,?_,?_,?_,?_⟩
  · intro r hr; rw [ha.1 r hr,hag]
  · exact h0.trans (congrFun hag .x0)
  · exact h1.trans (congrFun hag .x3)
  · rw [hvec .v8 (by decide),hw8]
  · rw [hvec .v9 (by decide),hw9]

theorem correct (s : State) (hs : xorAArch64.pre s) :
    WP isa xor s fun u => abiPreserved s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 := by
  obtain ⟨t,u,he,ha,hp,h0,h1,h8,h9⟩ := correct_aux s hs
  refine ⟨t,u,he,⟨ha.1,ha.2,?_⟩,hp,h0,h1⟩
  intro r hr
  by_cases he8 : r = .v8
  · subst r; exact h8
  by_cases he9 : r = .v9
  · subst r; exact h9
  have hc : xor.allInstrs keepsOtherV = true := by lit_decide
  rw [Exec.vec (fun i hi => keepsOtherV_ne (List.all_eq_true.mp
    ((Code.allInstrs_eq keepsOtherV xor) ▸ hc) i hi) hr he8 he9) he]

theorem xor_correct (s : State) (hs : xorAArch64.pre s) :
    ∃ t u, Exec isa xor s t u ∧ abiPreserved s u ∧ xorAArch64.post s u :=
  (correct s hs).imp fun _ ⟨u,he,ha,hp,_⟩ => ⟨u,he,ha,hp⟩

theorem xor_noFrames : xor.noFrames = true := by lit_decide

theorem xor_ct : ConstantTime isa xorAArch64.pre xorAArch64.pub xor := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ hp => Xor.agree₀ hp) (by taint_decide)

theorem xor_verified : Verified AArch64.target xor
    (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract,Spec.ChaCha20.xorSig,AArch64.abi,AArch64.argRegs,
      xorAArch64] [Xor.sat] using Xor.sat)

end VG.Proof.ChaCha20.AArch64.Rows6
