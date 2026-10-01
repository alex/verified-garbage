import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64
open VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Impl.ChaCha20.AArch64.Neon4 (vreg rowWord)
open VG.Proof.ChaCha20.AArch64.Neon4

/-- Only the first four slots of this data view have been written. -/
theorem Data.frame64 {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) (hd : ∀ k ∈ done, k < 4) : Frame [⟨p,64⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < 64 := by
    have hh := hx ⟨p,64⟩ (by simp)
    simp only [Region.Contains] at hh
    omega
  rw [h x,ite_eq_right]
  rintro ⟨hslot,hlt⟩
  have hs := hd _ hslot
  omega

theorem loadLast_ok (s : State) (r : Fin 4)
    (hi : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block [.ldrq (vreg (rowWord r 0)) .x3 (16 * r)]) s fun u =>
      u.v (vreg (rowWord r 0)) = s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 ∧
      Same s u := by
  have ha : (16 * r.val) % 16 = 0 ∧ 16 * r.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons,runBlock_nil,exec,addr,ha,and_self,ite_true,
    State.load,hi,Option.bind_some,Option.map_some,isa,runStep_some,Option.some.injEq,
    exists_eq_left',RegUpd.v_setV_self]
  exact ⟨trivial,rfl,rfl,rfl,rfl,rfl⟩

theorem xorLastRows_ok (rs : List (Fin 4)) (hn : rs.Nodup)
    {s : State} {m₀ : Mem} {p b : Addr} {v : CState} {done : List Nat}
    (hd : Data m₀ s.mem p (output (fun _ => v)) done)
    (hdone : ∀ k ∈ done, k < 4) (hp : s.gpr .x1 = p) (hb : s.gpr .x3 = b)
    (hbuf : ∀ r : Fin 4, s.mem.read (b + BitVec.ofNat 64 (16 * r)) 16 =
      output (fun _ => v) r)
    (hsep : (⟨b,64⟩ : Region).Disjoint ⟨p,64⟩)
    (hfresh : ∀ r ∈ rs, r.val ∉ done)
    (hin : ∀ r : Fin 4, InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (16 * r)) 16)
    (hout : ∀ r : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block (rs.flatMap xorLastRow)) s fun u =>
      Data m₀ u.mem p (output (fun _ => v)) (rs.map Fin.val ++ done) ∧
      Keep s u := by
  induction rs generalizing s done with
  | nil => exact WP.block_nil ⟨hd,⟨rfl,rfl,rfl,rfl⟩⟩
  | cons r rs ih =>
    apply WP.block_append
    apply WP.block_append
    have hi : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 := hb ▸ hin r
    refine (loadLast_ok s r hi).mono fun a ⟨ha,hsa⟩ => ?_
    have hda : Data m₀ a.mem p (output (fun _ => v)) done := hsa.mem ▸ hd
    have hpa : a.gpr .x1 = p := by rw [hsa.gpr,hp]
    have hva : a.v (vreg (rowWord r 0)) = output (fun _ => v) (slot r 0) := by
      simpa only [slot,Fin.val_zero,Nat.mul_zero,Nat.zero_add,hb,hbuf r] using ha
    have hoa : InRegions a.wr (p + BitVec.ofNat 64 (64 * (0 : Fin 4) + 16 * r)) 16 := by
      rw [hsa.wr]; simpa only [Fin.val_zero,Nat.mul_zero,Nat.zero_add] using hout r
    have hoa' : InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (64 * (0 : Fin 4) + 16 * r)) 16 := by
      rw [hpa]; exact hoa
    refine (xorRow_ok a r 0 hoa').mono fun u ⟨hm,hau⟩ => ?_
    have hu : Data m₀ u.mem p (output (fun _ => v)) (slot r 0 :: done) := by
      rw [hm,hpa,hva,show 64 * (0 : Fin 4).val + 16 * r.val = 16 * slot r 0 by simp [slot]]
      exact hda.store (slot_lt r 0) (by simpa [slot] using hfresh r (by simp))
    have hsu : Keep s u := ⟨hau.gpr.trans hsa.gpr,hau.rd.trans hsa.rd,
      hau.wr.trans hsa.wr,hau.sp.trans hsa.sp⟩
    have hdone' : ∀ k ∈ slot r 0 :: done, k < 4 := by
      intro k hk
      rcases List.mem_cons.mp hk with he | he
      · subst k; simp [slot]
      · exact hdone k he
    have hf := Data.frame64 hu hdone'
    have hf₀ := Data.frame64 hd hdone
    have hbu : ∀ q : Fin 4, u.mem.read (b + BitVec.ofNat 64 (16 * q)) 16 =
        output (fun _ => v) q := by
      intro q
      rw [hf.read (r := ⟨b,64⟩) (Offset.contains_base _ (by omega) (by omega))
        (by intro z hz; simpa using (List.mem_singleton.mp hz ▸ hsep)) (by decide), ← hf₀.read (r := ⟨b,64⟩) (Offset.contains_base _ (by omega) (by omega))
        (by intro z hz; simpa using (List.mem_singleton.mp hz ▸ hsep)) (by decide),hbuf q]
    have hpu : u.gpr .x1 = p := by rw [hsu.gpr,hp]
    have hpb : u.gpr .x3 = b := by rw [hsu.gpr,hb]
    have hiu : ∀ q : Fin 4, InRegions (u.rd ++ u.wr) (b + BitVec.ofNat 64 (16 * q)) 16 := by
      intro q; rw [hsu.rd,hsu.wr]; exact hin q
    have hou : ∀ q : Fin 4, InRegions u.wr (p + BitVec.ofNat 64 (16 * q)) 16 := by
      intro q; rw [hsu.wr]; exact hout q
    have hfr : ∀ q ∈ rs, q.val ∉ slot r 0 :: done := by
      intro q hq
      simp only [List.mem_cons,not_or]
      refine ⟨?_,hfresh q (by simp [hq])⟩
      intro he
      have hne := (List.nodup_cons.mp hn).1
      apply hne
      have eq : q = r := Fin.ext (by simpa [slot] using he)
      exact eq ▸ hq
    refine (ih (List.nodup_cons.mp hn).2 hu hdone' hpu hpb hbu hfr hiu hou).mono
      fun z ⟨hz,huz⟩ => ⟨?_,hsu.trans huz⟩
    intro x
    simpa only [Data,List.map_cons,List.mem_append,List.mem_cons,slot,Fin.val_zero,
      Nat.mul_zero,Nat.zero_add,or_assoc,or_left_comm] using hz x

theorem xorLast_ok (s : State) (v : CState)
    (hbuf : ∀ r : Fin 4, s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      output (fun _ => v) r)
    (hsep : (⟨s.gpr .x3,64⟩ : Region).Disjoint ⟨s.gpr .x1,64⟩)
    (hin : ∀ r : Fin 4, InRegions (s.rd ++ s.wr)
      (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16)
    (hout : ∀ r : Fin 4, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap xorLastRow)) s fun u =>
      (∀ k < 64, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^ (VG.Spec.ChaCha20.serialize v).getD k 0) ∧
      Frame [⟨s.gpr .x1,64⟩] s.mem u.mem ∧ Keep s u := by
  refine (xorLastRows_ok (List.finRange 4) (List.nodup_finRange 4)
    (Data.nil s.mem (s.gpr .x1) (output (fun _ => v))) (by simp) rfl rfl hbuf hsep
    (by simp) hin hout).mono fun u ⟨hd,hk⟩ => ⟨?_,?_,hk⟩
  · intro k hk
    have hm : k / 16 ∈ (List.finRange 4).map Fin.val ++ ([] : List Nat) := by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨⟨k / 16,by omega⟩,List.mem_finRange _,rfl⟩
    rw [hd _,Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64),ite_eq_left ⟨hm,by omega⟩,
      output_byte (fun _ => v) (by omega),Nat.mod_eq_of_lt hk]
  · apply Data.frame64 hd
    intro k hk
    simp only [List.append_nil,List.mem_map] at hk
    obtain ⟨r,_,rfl⟩ := hk
    exact r.isLt

end VG.Proof.ChaCha20.AArch64.Mixed5
