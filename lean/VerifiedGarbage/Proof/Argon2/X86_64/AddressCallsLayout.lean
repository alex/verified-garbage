import VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsArgs
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCall

/-! Permissions and separation for either address-generation compression call. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64

structure Ready (s : State) : Prop where
  frameRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8
  workWrite : Covers [⟨work s, 8192⟩] s.wr
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨work s, 8192⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨work s, 8192⟩

theorem displacement_eq (n : Nat) (bound : n ≤ 8192) : displacement n = BitVec.ofNat 64 n := by
  have n32 : n < 2 ^ 32 := by omega
  have msb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n32]
    omega
  unfold displacement
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb,
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) n32]

theorem work_cover (s : State) (h : Ready s) (d n : Nat) (hd : d + n ≤ 8192) :
    Covers [⟨off (work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (work s) d, n⟩] [⟨work s, 8192⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨work s, 8192⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

structure Args (s a : State) (x y out : Nat) : Prop where
  scratch : a.gpr .rcx = work s
  left : a.gpr .rdi = off (work s) x
  right : a.gpr .rsi = off (work s) y
  output : a.gpr .rdx = off (work s) out
  keeps : Divide.Keeps [.rcx, .rdi, .rsi, .rdx] s a

theorem args_nat_ok (s : State) (h : Ready s) (x y out : Nat)
    (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192) :
    WP isa (.block (Impl.Argon2.X86_64.AddressCalls.args x y out)) s (Args s · x y out) := by
  refine (args_ok s x y out h.frameRead).mono ?_
  rintro a ⟨scratch, left, right, output, keeps⟩
  rw [displacement_eq x hx] at left
  rw [displacement_eq y hy] at right
  rw [displacement_eq out ho] at output
  exact ⟨scratch, left, right, output, keeps⟩

theorem args_call_ready (s a : State) (h : Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (args : Args s a x y out) : FillCompress.CallReady a := by
  have read (d : Nat) (hd : d + 1024 ≤ 8192) :
      Covers [⟨off (work s) d, 1024⟩] (a.rd ++ a.wr) := by
    rw [args.keeps.rd, args.keeps.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := work_cover s h d 1024 hd p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have sp : a.gpr .rsp = s.gpr .rsp := args.keeps.regs .rsp (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [args.left]; exact read x bx
  · rw [args.right]; exact read y by_
  · rw [args.output, args.keeps.wr]; exact work_cover s h out 1024 bo
  · rw [args.scratch, args.keeps.wr]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using work_cover s h 0 4096 (by decide)
  · rw [args.left, args.scratch]; exact Offset.disjoint_base _ hx (by omega)
  · rw [args.right, args.scratch]; exact Offset.disjoint_base _ hy (by omega)
  · rw [args.output, args.scratch]; exact Offset.disjoint_base _ ho (by omega)
  · rw [sp, args.left]; exact h.stackWork.sub_right (Offset.sub_base _ bx)
  · rw [sp, args.right]; exact h.stackWork.sub_right (Offset.sub_base _ by_)
  · rw [sp, args.output]; exact h.stackWork.sub_right (Offset.sub_base _ bo)
  · rw [sp, args.scratch]; exact h.stackWork.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Argon2.X86_64.AddressCalls
