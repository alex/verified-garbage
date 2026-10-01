import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.AbsorbBlock
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (laneAddr)

/-- Word-wise description of XORing a whole number of input words. -/
def xorWords (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n : Nat) : Spec.Sha3.State :=
  Vector.ofFn fun i => A[i] ^^^ (if i.val < n then m.readW (laneAddr p i.val) 64 else 0)

theorem xorWords_get (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n j : Nat) (hj : j < 25) :
    (xorWords A m p n)[j] = A[j] ^^^ (if j < n then m.readW (laneAddr p j) 64 else 0) := by
  simp only [xorWords, Vector.getElem_ofFn, Fin.getElem_fin]

theorem xorWords_eq (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n : Nat) :
    xorWords A m p n = Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt m p (8*n)) := by
  apply VG.Proof.Sha3.ext_bytes
  intro j hj
  rw [VG.Proof.Sha3.byteOf_xorBytes _ _ hj, VG.Proof.Sha3.byteOf_eq' _ hj,
    VG.Proof.Sha3.byteOf_eq' _ hj]
  simp only [xorWords,Vector.getElem_ofFn,BitVec.extractLsb'_xor]
  congr 1
  by_cases hn : j < 8*n
  · have hw : j/8 < n := by omega
    simp only [hw,ite_true,Mem.readW,BitVec.setWidth_eq]
    rw [Mem.extractLsb'_read _ _ (by omega : j%8 < 64/8)]
    simp only [Spec.Sha3.bytesAt,List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_range hn,Option.map_some,Option.getD_some,laneAddr,
      BitVec.add_assoc,← BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega]
  · have hw : ¬ j/8 < n := by omega
    have he : (List.range (8*n))[j]? = none := List.getElem?_eq_none (by rw [List.length_range]; omega)
    simp only [hw,ite_false,Spec.Sha3.bytesAt,
      List.getD_eq_getElem?_getD,List.getElem?_map,he,Option.map_none,Option.getD_none]
    exact BitVec.extractLsb'_zero

structure BlockKeep (s s' : VG.AArch64.State) : Prop where
  gpr : ∀ r, r ≠ .x17 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.block {s s' : VG.AArch64.State} (h : Keep s s') : BlockKeep s s' :=
  ⟨fun r _ => congrFun h.gpr r,h.mem,h.rd,h.wr,h.sp⟩

theorem BlockKeep.trans {s t u : VG.AArch64.State} (h : BlockKeep s t) (k : BlockKeep t u) :
    BlockKeep s u := ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr),k.mem.trans h.mem,
      k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩

theorem state_not_temps : ∀ i < 25, vreg i ≠ .v25 ∧ vreg i ≠ .v26 := by decide

theorem absorbPair_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 12)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (absorbPair i)) s fun s' => Keep s s' ∧ ∀ j < 25,
      low s' (vreg j) = if j = 2*i+1 then low s (vreg j) ^^^ s.mem.readW (laneAddr (s.gpr .x3) j) 64
        else if j = 2*i then low s (vreg j) ^^^ s.mem.readW (laneAddr (s.gpr .x3) j) 64 else low s (vreg j) := by
  unfold absorbPair
  refine WP.cons (exec_ldrq ⟨by omega,by omega⟩ hin)
    (WP.cons rfl (WP.cons rfl (WP.cons rfl (wp_nil ?_))))
  refine ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩
  have he := state_not_temps (2*i) (by omega)
  have ho := state_not_temps (2*i+1) (by omega)
  have hd : vreg (2*i+1) ≠ vreg (2*i) := by
    rw [ne_eq,vreg_inj _ (by omega) _ (by omega)]; omega
  have hde : vreg (2*i) ≠ vreg (2*i+1) := Ne.symm hd
  have hjt := state_not_temps j hj
  by_cases hjo : j = 2*i+1
  · subst j
    simp only [low,RegUpd.v_setV,ho.1,ho.2,he.1,he.2,Ne.symm he.2,hd,reduceCtorEq,ite_true,ite_false,low_xor]
    rw [low_ext8,pair_high]
  · by_cases hje : j = 2*i
    · subst j
      simp only [low,RegUpd.v_setV,ho.1,ho.2,he.1,he.2,hde,reduceCtorEq,hjo,
        ite_true,ite_false,low_xor]
      rw [pair_low]
    · have he' : vreg j ≠ vreg (2*i) := by rw [ne_eq,vreg_inj _ (by omega) _ (by omega)]; exact hje
      have ho' : vreg j ≠ vreg (2*i+1) := by rw [ne_eq,vreg_inj _ (by omega) _ (by omega)]; exact hjo
      simp only [low,RegUpd.v_setV,he',ho',hjt.1,hjt.2,hjo,hje,ite_false]

theorem absorbWord_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 25)
    (hin : InRegions (s.rd ++ s.wr) (laneAddr (s.gpr .x3) i) 8) :
    WP isa (.block (absorbWord i)) s fun s' => BlockKeep s s' ∧ ∀ j < 25,
      low s' (vreg j) = if j = i then low s (vreg j) ^^^ s.mem.readW (laneAddr (s.gpr .x3) j) 64
        else low s (vreg j) := by
  unfold absorbWord
  refine WP.cons (exec_ldr_x ⟨by omega,by omega⟩ hin) (WP.cons rfl (WP.cons rfl (wp_nil ?_)))
  refine ⟨⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩
  · simp only [RegUpd.gpr_setV,RegUpd.gpr_write,hr,ite_false]
  · have hn := (state_not_temps i hi).1
    have hjn := (state_not_temps j hj).1
    by_cases he : j = i
    · subst j
      simp only [low,RegUpd.v_setV,RegUpd.v_write,RegUpd.gpr_write_self,hn,ite_true,ite_false,
        Size.bits,BitVec.setWidth_eq,low_xor,vdword_ofVDwords_0]
    · have hr : vreg j ≠ vreg i := by rw [ne_eq,vreg_inj _ (by omega) _ (by omega)]; exact he
      simp only [low,RegUpd.v_setV,RegUpd.v_write,hr,hjn,he,ite_false]

structure AbsorbInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : Keep s₀ s
  lanes : ∀ j < 25, low s (vreg j) = if j < 2*k
    then low s₀ (vreg j) ^^^ s₀.mem.readW (laneAddr (s₀.gpr .x3) j) 64 else low s₀ (vreg j)

theorem absorbPairs_ok (s₀ : VG.AArch64.State) (k : Nat) (hk : k ≤ 12)
    (hin : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x3 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range k).flatMap absorbPair)) s₀ (AbsorbInv s₀ k) := by
  refine wp_range_flatMap (M := isa) (AbsorbInv s₀) (fun i s hi hs => ?_) k (Nat.le_refl _) s₀
    ⟨Keep.refl _,fun _ _ => by simp only [Nat.mul_zero,Nat.not_lt_zero,ite_false]⟩
  refine (absorbPair_ok s i (by omega) (by rw [hs.keep.rd,hs.keep.wr,hs.keep.gpr]; exact hin i hi)).mono
    fun s' ⟨hp,ha⟩ => ⟨hs.keep.trans hp,fun j hj => ?_⟩
  rw [ha j hj,hs.lanes j hj,hs.keep.mem,hs.keep.gpr]
  by_cases ho : j = 2*i+1
  · subst j
    simp only [ite_true,show ¬2*i+1 < 2*i by omega,show 2*i+1 < 2*(i+1) by omega,ite_false]
  · by_cases he : j = 2*i
    · subst j
      simp only [ho,ite_false,ite_true,Nat.lt_irrefl,show 2*i < 2*(i+1) by omega]
    · have hjk : j < 2*i ↔ j < 2*(i+1) := by omega
      simp only [ho,he,ite_false,hjk]

theorem absorbWords_ok (s₀ : VG.AArch64.State) (A : Spec.Sha3.State) (hA : Lanes s₀ A)
    (n : Nat) (hn : n ≤ 25)
    (hin : Covers [⟨s₀.gpr .x3,8*n⟩] (s₀.rd ++ s₀.wr)) :
    WP isa (.block (absorbWords n)) s₀ fun s' => BlockKeep s₀ s' ∧
      Lanes s' (xorWords A s₀.mem (s₀.gpr .x3) n) := by
  rw [absorbWords,WP.block_append_iff]
  refine (absorbPairs_ok s₀ (n/2) (by omega) (fun i hi => ?_)).mono fun s hs => ?_
  · exact hin _ _ ⟨⟨s₀.gpr .x3,8*n⟩,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  · by_cases ho : n%2=1
    · simp only [ho,ite_true]
      refine (absorbWord_ok s (n-1) (by omega) ?_).mono fun s' ⟨hb,hl⟩ => ?_
      · rw [hs.keep.rd,hs.keep.wr,hs.keep.gpr]
        exact hin _ _ ⟨⟨s₀.gpr .x3,8*n⟩,by simp,Offset.contains_base _ (by omega) (by omega)⟩
      · refine ⟨hs.keep.block.trans hb,fun j hj => ?_⟩
        rw [hl j hj,hs.lanes j hj,hs.keep.mem,hs.keep.gpr]
        rw [xorWords_get, hA j hj]
        by_cases he : j = n-1
        · subst j
          simp only [ite_true,show ¬n-1 < 2*(n/2) by omega,show n-1 < n by omega,ite_false]
        · have hjn : j < 2*(n/2) ↔ j < n := by omega
          simp only [he,ite_false,hjn]
          by_cases hjn' : j < n
          · simp only [hjn',ite_true]
          · simp only [hjn',ite_false]; exact BitVec.xor_zero.symm
    · simp only [ho,ite_false]
      refine wp_nil ⟨hs.keep.block,fun j hj => ?_⟩
      rw [hs.lanes j hj,show 2*(n/2)=n by omega,hA j hj]
      rw [xorWords_get]
      by_cases hjn : j < n
      · simp only [hjn,ite_true]
      · simp only [hjn,ite_false]; exact BitVec.xor_zero.symm

/-- XOR one complete rate block without serializing the SIMD state. -/
theorem absorbBlock_ok (s : VG.AArch64.State) (A : Spec.Sha3.State) (hA : Lanes s A)
    (rate : Nat) (hr : rate ∈ Spec.Sha3.rates)
    (hin : Covers [⟨s.gpr .x3,rate⟩] (s.rd ++ s.wr)) :
    WP isa (.block (absorbBlock rate)) s fun s' => BlockKeep s s' ∧
      Lanes s' (Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt s.mem (s.gpr .x3) rate)) := by
  have hb : rate/8 ≤ 25 ∧ 8*(rate/8)=rate := by
    simp only [Spec.Sha3.rates,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  refine (absorbWords_ok s A hA (rate/8) hb.1 ?_).mono fun s' h => ⟨h.1,?_⟩
  · rwa [hb.2]
  · simpa only [xorWords_eq,hb.2] using h.2

#assert_standard_axioms absorbBlock_ok

end VG.Proof.Sha3.AArch64.Sha3.Vector
