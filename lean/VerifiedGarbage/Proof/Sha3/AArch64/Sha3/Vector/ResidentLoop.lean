import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentSetup
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentControl

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (Rep)

theorem rate_bounds {b : State} (hp : BulkPre b) : 0 < rate b ∧ rate b ≤ 168 := by
  have h := hp.rate_mem
  simp only [Spec.Sha3.rates,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> omega

theorem input_bytes (b : State) (hp : BulkPre b) (m : Mem)
    (hf : Frame [stateR b,scratchR b] b.mem m) (c n : Nat) (hcn : c+n ≤ len b) :
    bytesAt m (data b + BitVec.ofNat 64 c) n = bytesAt b.mem (data b + BitVec.ofNat 64 c) n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [BitVec.add_assoc,← BitVec.ofNat_add]
  exact hf.bytes (R := dataR b) (by simpa using ⟨hp.d_st,hp.d_scr⟩)
    (Nat.le_of_lt (BitVec.isLt _)) (by change c+i < len b; omega)

theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c+n) = bytesAt m p c ++ bytesAt m (p+BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n+1 => by
    rw [← Nat.add_assoc,VG.Proof.Sha3.bytesAt_succ,bytesAt_add m p c n,
      VG.Proof.Sha3.bytesAt_succ,List.append_assoc,BitVec.add_assoc,← BitVec.ofNat_add]

structure LoopState (b : State) (m : Mem) (c : Nat) (A : Spec.Sha3.State) (s : State) : Prop where
  c_le : c ≤ len b
  aligned : c % rate b = 0
  mem : s.mem = m
  rd : s.rd = b.rd
  wr : s.wr = b.wr
  x3 : s.gpr .x3 = data b + BitVec.ofNat 64 c
  x4 : s.gpr .x4 = BitVec.ofNat 64 (len b-c)
  x6 : s.gpr .x6 = b.gpr .x6
  lanes : Lanes s A
  repr : ∀ msg, stateAt b.mem (st b) = Rep (rate b) msg → msg.length % rate b = 0 →
    A = Rep (rate b) (msg ++ bytesAt b.mem (data b) c)

theorem LoopState.input {b s : State} {m : Mem} {c : Nat} {A : Spec.Sha3.State}
    (hp : BulkPre b) (h : LoopState b m c A s) (hc : c+rate b ≤ len b) :
    Covers [⟨s.gpr .x3,rate b⟩] (s.rd ++ s.wr) := by
  rw [h.rd,h.wr,h.x3,hp.rd]
  apply Covers.of_sub
  intro r hr
  have he := List.mem_singleton.mp hr
  subst r
  exact ⟨dataR b,by simp,c,rfl,hc⟩

theorem body_ok (b : State) (hp : BulkPre b) (m : Mem)
    (hf : Frame [stateR b,scratchR b] b.mem m)
    (c : Nat) (A : Spec.Sha3.State) (s : State) (h : LoopState b m c A s)
    (hc : c+rate b ≤ len b) :
    WP isa body s fun s' => ∃ A', LoopState b m (c+rate b) A' s' ∧
      isa.eval (.zero .x .x7) s' = some (decide (rate b ≤ len b-(c+rate b))) := by
  unfold body
  apply WP.seq
  refine (xorRate_ok s A h.lanes (rate b) hp.rate_mem ?_ (h.input hp hc)).mono fun t ⟨hk,hl⟩ => ?_
  · rw [h.x6,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · rw [WP.block_append_iff,WP.block_append_iff]
    refine (rounds_ok t _ hl).mono fun u ⟨hu,hA⟩ => ?_
    have h3 : u.gpr .x3 = data b + BitVec.ofNat 64 c :=
      (hu.gpr _ (by decide)).trans ((hk.gpr _ (by decide) (by decide)).trans h.x3)
    have h4 : u.gpr .x4 = BitVec.ofNat 64 (len b-c) :=
      (hu.gpr _ (by decide)).trans ((hk.gpr _ (by decide) (by decide)).trans h.x4)
    have h6 : u.gpr .x6 = BitVec.ofNat 64 (rate b) := by
      rw [hu.gpr _ (by decide),hk.gpr _ (by decide) (by decide),h.x6,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    have ctl := advance_test_ok u (data b+BitVec.ofNat 64 c) (len b-c) (rate b)
      (by have hlen : len b < 2^64 := BitVec.isLt _; omega) (by omega) (rate_bounds hp).2
      (by have := hp.len_upper; omega) h3 h4 h6
    rw [← WP.block_append_iff]
    refine ctl.mono fun v ⟨hm,hr,hw,hsp,hv,h3',h4',h6',he⟩ => ?_
    refine ⟨Spec.Sha3.keccakF (Spec.Sha3.xorBytes A (bytesAt s.mem (s.gpr .x3) (rate b))),⟨by omega,?_,hm.trans (hu.mem.trans (hk.mem.trans h.mem)),
      hr.trans (hu.rd.trans (hk.rd.trans h.rd)),hw.trans (hu.wr.trans (hk.wr.trans h.wr)),
      ?_,?_,?_,?_,?_⟩,?_⟩
    · rw [Nat.add_mod,h.aligned,Nat.mod_self,Nat.zero_add,Nat.zero_mod]
    · simpa only [BitVec.add_assoc,← BitVec.ofNat_add] using h3'
    · simpa only [Nat.sub_sub] using h4'
    · exact h6'.trans ((hu.gpr _ (by decide)).trans ((hk.gpr _ (by decide) (by decide)).trans h.x6))
    · intro j hj
      change vdword (v.v (vreg j)) 0 = _
      rw [hv]
      exact hA j hj
    · intro msg hmsg halign
      rw [h.mem,h.x3,input_bytes b hp m hf c (rate b) hc,h.repr msg hmsg halign]
      have hal : (msg ++ bytesAt b.mem (data b) c).length % rate b = 0 := by
        simp only [List.length_append,VG.Proof.Sha3.bytesAt_length,Nat.add_mod,halign,
          h.aligned,Nat.zero_add,Nat.zero_mod]
      rw [← rep_whole (rate_bounds hp).1 (by have := (rate_bounds hp).2; omega)
        _ _ hal (VG.Proof.Sha3.bytesAt_length _ _ _),List.append_assoc,← bytesAt_add]
    · simpa only [Nat.sub_sub] using he

/-- The public remaining-byte count strictly decreases on each repeated body. -/
theorem loop_ok (b : State) (hp : BulkPre b) (s₀ : State) (hs : Setup b s₀) :
    WP isa (.loop body (.zero .x .x7)) s₀ fun s =>
      ∃ c A, LoopState b s₀.mem c A s := by
  let Inv : Nat → State → Prop := fun n s => ∃ c A, LoopState b s₀.mem c A s ∧
    n = len b-c ∧ c+rate b ≤ len b
  refine WP.loop (M := isa) Inv (fun n s ⟨c,A,h,hn,hc⟩ => ?_) (len b) s₀ ?_
  · refine (body_ok b hp s₀.mem hs.frame c A s h hc).mono fun s' ⟨A',h',he⟩ => ?_
    by_cases hk : rate b ≤ len b-(c+rate b)
    · right
      refine ⟨?_,len b-(c+rate b),?_,c+rate b,A',h',rfl,?_⟩
      · simpa only [hk,decide_true] using he
      · have := (rate_bounds hp).1
        omega
      · omega
    · left
      exact ⟨by simpa only [hk,decide_false] using he,c+rate b,A',h'⟩
  · refine ⟨0,stateAt b.mem (st b),⟨by omega,by simp,rfl,hs.rd,hs.wr,?_,?_,?_,hs.lanes,?_⟩,
      by omega,?_⟩
    · simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hs.gpr .x3 (by simp)
    · simpa only [Nat.sub_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using hs.gpr .x4 (by simp)
    · exact hs.gpr .x6 (by simp)
    · intro msg hm _
      simpa only [bytesAt,List.range_zero,List.map_nil,List.append_nil] using hm
    · simpa only [Nat.zero_add] using hp.enough

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
