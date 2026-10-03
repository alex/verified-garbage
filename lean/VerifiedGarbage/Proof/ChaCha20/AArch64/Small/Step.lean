import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Small
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Spec.ChaCha20 (stateAt serialize block keystream)

structure Prefix (s₀ : State) (n : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (64*n)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀-64*n)
  x3 : s.gpr .x3 = bp s₀
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) n
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    s₀.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (if k < 64*n then (KS s₀).getD k 0 else 0)
  frame : Frame [stR s₀,dR s₀,bR s₀] s₀.mem s.mem

theorem next_ok (s : State) (n : Nat) (hn : n ≤ 4)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block (next n)) s fun u =>
      u.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (64*n) ∧
      u.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 (64*n) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) n ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  have hi : n < 4096 := by omega
  have hb : 64*n < 4096 := by omega
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next,runBlock_cons,runBlock_nil,exec,
    addr,Size.bytes,Size.bits,ite_true,ite_false,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,hi,hb,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,trivial,?_,?_,?_,trivial⟩
  · intro r h1 h2 h4; simp only [h1,h2,h4,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr s.mem (s.gpr .x0) n
    simp only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48+4 ≤ 64) (by decide))

theorem step_ok (s₀ : State) (hp : XPre s₀) (n : Nat) (hn : n ≤ 4) (hle : 64*n ≤ L s₀) :
    WP isa (step n) s₀ (Prefix s₀ n) := by
  have hl : L s₀ < 2^64 := (s₀.gpr .x2).isLt
  have hi : ∀ k : Fin 16, InRegions (s₀.rd ++ s₀.wr) (st s₀+BitVec.ofNat 64 (4*k)) 4 := by
    intro k; rw [hp.rd,hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  have ho : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s₀.wr
      (dp s₀+BitVec.ofNat 64 (64*j+16*r)) 16 := by
    intro r j hj
    have hjn : j.val < n := (List.mem_filter.mp hj).2 |> of_decide_eq_true
    rw [hp.wr]
    exact ⟨dR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  refine (chunk_ok n hn s₀ hi ho).mono fun a ⟨ha,hf,hk⟩ => ?_
  have ia : InRegions (a.rd ++ a.wr) (a.gpr .x0+BitVec.ofNat 64 48) 4 := by
    rw [hk.rd,hk.wr,hk.gpr .x0 (by decide),hp.rd,hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have oa : InRegions a.wr (a.gpr .x0+BitVec.ofNat 64 48) 4 := by
    rw [hk.wr,hk.gpr .x0 (by decide),hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have sub : Region.Sub ⟨dp s₀,64*n⟩ (dR s₀) := Region.sub_prefix hle
  refine (next_ok a n hn ia oa).mono fun u ⟨h1,h2,hg,hcnt,hf',hrd,hwr,hsp⟩ => ?_
  have h0 : u.gpr .x0 = st s₀ := (hg _ (by decide) (by decide) (by decide)).trans (hk.gpr _ (by decide))
  refine ⟨h0,?_,?_,?_,?_,hrd.trans hk.rd,hwr.trans hk.wr,hsp.trans hk.sp,?_,?_,?_⟩
  · rw [h1,hk.gpr _ (by decide)]
  · rw [h2,hk.gpr _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [L,BitVec.toNat_sub,BitVec.toNat_ofNat] at *
    omega
  · exact (hg _ (by decide) (by decide) (by decide)).trans (hk.gpr _ (by decide))
  · intro r hr
    have hne : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 := by revert hr; decide +revert
    exact (hg r hne.1 hne.2.1 hne.2.2).trans (hk.gpr r hne.2.2)
  ·
    rw [hk.gpr _ (by decide)] at hcnt
    rw [hcnt, VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hp.st_d.sub_right sub)]
  ·
    intro k hkl
    have inData : (dR s₀).Contains (dp s₀+BitVec.ofNat 64 k) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    have nd : ¬ (stR s₀).Contains (dp s₀+BitVec.ofNat 64 k) 1 := fun h => hp.st_d _ h inData
    have eu : u.mem (dp s₀+BitVec.ofNat 64 k) = a.mem (dp s₀+BitVec.ofNat 64 k) := by
      apply hf'; intro r hr
      simp only [List.mem_singleton] at hr; subst r
      rw [hk.gpr _ (by decide)]
      exact nd
    rw [eu]
    by_cases hk' : k < 64*n
    · rw [ha k hk',ite_eq_left hk',keystream_getD _ hkl]
    · rw [hf _ (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        simp only [Region.Contains,dp,Mem.sub_ofNat_toNat _ (by omega : k < 2^64)]
        omega),ite_eq_right hk']
      simp
  · exact (hf.sub (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨dR s₀,by simp,sub⟩)).trans (hf'.sub (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        rw [hk.gpr _ (by decide)]
        exact ⟨stR s₀,by simp,fun _ h => h⟩))

end VG.Proof.ChaCha20.AArch64.Small
