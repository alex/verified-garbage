import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.ResidentCore
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

structure RateKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x17 → r ≠ .x7 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem RateKeep.trans {s t u : State} (h : RateKeep s t) (k : RateKeep t u) : RateKeep s u :=
  ⟨fun r h₁ h₂ => (k.gpr r h₁ h₂).trans (h.gpr r h₁ h₂),k.mem.trans h.mem,
    k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
theorem BlockKeep.rate {s t : State} (h : BlockKeep s t) : RateKeep s t :=
  ⟨fun r hr _ => h.gpr r hr,h.mem,h.rd,h.wr,h.sp⟩
theorem RateKeep.write7 (s : State) (v : BitVec 64) : RateKeep s (s.write .x .x7 v) := by
  refine ⟨fun r _ hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [RegUpd.gpr_write,hr,ite_false]

def select (rs : List Nat) : Prog isa :=
  rs.foldr (fun r rest => .seq (.block [.subImm .x .x7 .x6 r])
    (.ite (.zero .x .x7) (.block (absorbBlock r)) rest)) (.block (absorbBlock 168))

theorem select_ok (rs : List Nat) (hsmall : ∀ r ∈ rs, r < 4096)
    (s : State) (A : Spec.Sha3.State) (hA : Lanes s A)
    (r : Nat) (hr : r ∈ Spec.Sha3.rates) (hrs : r ∈ rs ++ [168])
    (hv : s.gpr .x6 = BitVec.ofNat 64 r)
    (hin : Covers [⟨s.gpr .x3,r⟩] (s.rd ++ s.wr)) :
    WP isa (select rs) s fun s' => RateKeep s s' ∧
      Lanes s' (Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt s.mem (s.gpr .x3) r)) := by
  induction rs generalizing s with
  | nil =>
    have he : r = 168 := by simpa only [List.nil_append,List.mem_singleton] using hrs
    subst r
    exact (absorbBlock_ok s A hA 168 hr hin).mono fun _ h => ⟨BlockKeep.rate h.1,h.2⟩
  | cons x xs ih =>
    change WP isa (.seq (.block [.subImm .x .x7 .x6 x]) (.ite (.zero .x .x7) _ _)) s _
    apply WP.seq
    refine WP.cons (exec_subImm_x (hsmall x (by simp))) (wp_nil ?_)
    let t := s.write .x .x7 (s.read .x .x6 - BitVec.ofNat 64 x)
    have hvt : t.gpr .x6 = BitVec.ofNat 64 r := by
      simpa only [t,RegUpd.gpr_write,reduceCtorEq,ite_false] using hv
    have htA : Lanes t A := hA
    have htin : Covers [⟨t.gpr .x3,r⟩] (t.rd ++ t.wr) := hin
    have hk : RateKeep s t := RateKeep.write7 _ _
    by_cases he : r = x
    · subst x
      refine WP.ite true ?_ (fun _ => ?_) (fun h => by contradiction)
      · simp only [eval_zero, RegUpd.gpr_write_self, State.read, Size.bits,
          BitVec.setWidth_eq,hv,BitVec.sub_self]
        rfl
      · exact (absorbBlock_ok t A htA r hr htin).mono fun _ h => ⟨hk.trans (BlockKeep.rate h.1),h.2⟩
    · refine WP.ite false ?_ (fun h => by contradiction) (fun _ => ?_)
      · have hn : BitVec.ofNat 64 r - BitVec.ofNat 64 x ≠ 0 := by
          intro h
          have h' := BitVec.sub_eq_iff_eq_add.mp h
          have h : BitVec.ofNat 64 r = BitVec.ofNat 64 x := h'.trans (BitVec.zero_add _)
          have hrb : r < 4096 := by
            simp only [Spec.Sha3.rates,List.mem_cons,List.not_mem_nil,or_false] at hr
            rcases hr with rfl|rfl|rfl|rfl|rfl <;> omega
          have hx := hsmall x (by simp)
          have hh := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r < 2^64),
            Nat.mod_eq_of_lt (by omega : x < 2^64)] at hh
          exact he hh
        simpa only [eval_zero,t,RegUpd.gpr_write_self,State.read,Size.bits,
          BitVec.setWidth_eq,hv,beq_eq_false_iff_ne] using congrArg some (beq_eq_false_iff_ne.mpr hn)
      · have hrs' : r ∈ xs ++ [168] := by simpa only [List.cons_append,List.mem_cons,he,false_or] using hrs
        exact (ih (fun y hy => hsmall y (by simp [hy])) t htA hrs' hvt htin).mono
          fun _ h => ⟨hk.trans h.1,h.2⟩

theorem xorRate_ok (s : State) (A : Spec.Sha3.State) (hA : Lanes s A)
    (r : Nat) (hr : r ∈ Spec.Sha3.rates) (hv : s.gpr .x6 = BitVec.ofNat 64 r)
    (hin : Covers [⟨s.gpr .x3,r⟩] (s.rd ++ s.wr)) :
    WP isa xorRate s fun s' => RateKeep s s' ∧
      Lanes s' (Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt s.mem (s.gpr .x3) r)) :=
  select_ok [72,104,136,144] (by decide) s A hA r hr (by change r ∈ Spec.Sha3.rates; exact hr) hv hin

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
