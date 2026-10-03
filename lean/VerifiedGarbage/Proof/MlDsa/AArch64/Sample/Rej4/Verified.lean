import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTTop
import VerifiedGarbage.Proof.MlDsa.Sample.Rej4

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.Sample (rnFold rejNTT_some rejNTT_none rej4Res)
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

def preProps (s : State) : Prop := s.rd = [seedsR s] ∧ s.wr = [aR s,scrR s] ∧
  (seedsR s).Disjoint (aR s) ∧ (seedsR s).Disjoint (scrR s) ∧ (aR s).Disjoint (scrR s)

theorem r4_pre : ∀ s, (Spec.MlDsa.rejNTT4Contract AArch64.abi).pre s → r4K.pre s := by
  have h : ∀ s,(Spec.MlDsa.rejNTT4Contract AArch64.abi).pre s → preProps s := by
    sig_implies_pre [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,preProps,
      seedsR,aR,scrR,seedP,aP,scr,AArch64.abi,AArch64.argRegs]
  intro s hs
  obtain ⟨hr,hw,hsa,hss,has⟩ := h s hs
  exact ⟨hr,hw,hsa,hss,has⟩

theorem mask_cast (s : State) : (mask s 4).setWidth 32 = rej4Res s.mem (seedP s) := by
  unfold mask rej4Res
  change (if (List.range 4).all (fun k => (L s k).length == 256) then (1 : BitVec 64) else 0).setWidth 32 = _
  split <;> rfl

theorem r4_post {s t : State} (h : r4K.post s t) :
    let r := (t.gpr .x0).setWidth 32
    (r = 1 → ∀ k < 4,Spec.MlDsa.Reduced t.mem (Spec.MlDsa.poly4 (aP s) k)) ∧
      ((r = 1 ∧ ∀ k < 4,∃ b : Spec.MlDsa.Bounds,Spec.MlDsa.rejNTTPoly b.rejNTT
          (Spec.MlDsa.seed4 s.mem (seedP s) k) = some (Spec.MlDsa.polyAt t.mem (Spec.MlDsa.poly4 (aP s) k))) ∨
        (r = 0 ∧ ∃ k < 4,Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
          (Spec.MlDsa.seed4 s.mem (seedP s) k) = none)) := by
  obtain ⟨hr,hp⟩ := h
  rw [mask_cast] at hr
  intro r
  by_cases hall : ((List.range 4).all fun k => (L s k).length == 256) = true
  · have hs : ∀ k < 4,(L s k).length = 256 := fun k hk => by
      simpa using List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    change r = (if (List.range 4).all (fun k => (L s k).length == 256) then 1 else 0) at hr
    rw [ite_eq_left hall] at hr
    refine ⟨fun _ k hk => (hp k hk (hs k hk)).1,.inl ⟨hr,fun k hk =>
      ⟨{ Spec.MlDsa.minBounds with rejNTT := 1008 },?_⟩⟩⟩
    show Spec.MlDsa.rejNTTPoly 1008 _ = _
    change Spec.MlDsa.rejNTTPoly 1008 (B s k) = some (Spec.MlDsa.polyAt t.mem (polyP s k))
    rw [rejNTT_some (hs k hk),(hp k hk (hs k hk)).2]
  · change r = (if (List.range 4).all (fun k => (L s k).length == 256) then 1 else 0) at hr
    rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),.inr ⟨hr,?_⟩⟩
    simp only [List.all_eq_true,List.mem_range,not_forall,beq_iff_eq] at hall
    obtain ⟨k,hk,hk'⟩ := hall
    exact ⟨k,hk,rejNTT_none (B := 1008) (by decide) (by decide) hk'⟩

def r4Sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,136⟩]
  wr := [⟨0x2000,4096⟩,⟨0x4000,8192⟩]

theorem verified (sha3 : Bool) : Verified AArch64.target (Impl.MlDsa.AArch64.Sample.Rej4.rejNTT4With sha3)
    (Spec.MlDsa.rejNTT4Contract AArch64.abi) :=
  Verified.of_correct (correct sha3) (ct sha3)
    { pre := r4_pre
      post := by
        intro s t _ h
        sig_post [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,AArch64.abi,AArch64.argRegs]
        exact r4_post h
      pub := by
        intro s t _ _ h
        sig_pub [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,AArch64.abi,AArch64.argRegs] at h
        obtain ⟨hsp,hb,h0,h1,h2⟩ := h
        exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
      sat := by
        sig_implies_sat [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,AArch64.abi,AArch64.argRegs]
          [r4Sat] using r4Sat }

theorem ret {sha3 : Bool} {s t : State} {tr : List Leak}
    (hp : (Spec.MlDsa.rejNTT4Contract AArch64.abi).pre s)
    (he : Exec isa (Impl.MlDsa.AArch64.Sample.Rej4.rejNTT4With sha3) s tr t) :
    (t.gpr .x0).setWidth 32 = rej4Res s.mem (seedP s) := by
  obtain ⟨_,_,he',_,hq⟩ := correct sha3 s (r4_pre s hp)
  obtain ⟨_,rfl⟩ := Exec.det he he'
  exact hq.1.trans (mask_cast s)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
