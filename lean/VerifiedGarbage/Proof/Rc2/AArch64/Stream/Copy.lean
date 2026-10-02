import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Impl.Rc2.AArch64.Stream

/-!
# Streaming RC2-CBC on AArch64: the byte copy

`copy src so dst dd cnt` (`Impl/Rc2/AArch64/Stream.lean`) writes the `cnt`
bytes at `src + so` to `dst + dd` (`writeBytes`), advancing `src` and `dst` by
the count; the one lemma (`copy_ok`) every call site uses.
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64
open VG.Impl.Rc2.AArch64.Stream (copy copyBody)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_addImm wp_subImm wp_ldrb wp_strb eval_zero eval_nonzero
  ofNat_beq_zero sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

theorem setWidth_byte (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  ext i hi; simp

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [Spec.Rc2.bytesAt]
  · intro i h₁ h₂
    have hi : i < xs.length := h₂
    simp only [Spec.Rc2.bytesAt, List.getElem_map, List.getElem_range, writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi h), hi,
      ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- The copy's state after `j` of `k` bytes, from `s₀`. -/
structure CopyI (s₀ : State) (src dst cnt : Reg) (A B : Addr) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  psrc : s.gpr src = s₀.gpr src + BitVec.ofNat 64 j
  pdst : s.gpr dst = s₀.gpr dst + BitVec.ofNat 64 j
  pcnt : s.gpr cnt = BitVec.ofNat 64 (k - j)
  other : ∀ r, r ≠ .x9 → r ≠ src → r ≠ dst → r ≠ cnt → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem B ((Spec.Rc2.bytesAt s₀.mem A k).take j)

/-- What the copy leaves. -/
structure CopyPost (s₀ : State) (src dst cnt : Reg) (A B : Addr) (k : Nat) (s : State) : Prop where
  psrc : s.gpr src = s₀.gpr src + BitVec.ofNat 64 k
  pdst : s.gpr dst = s₀.gpr dst + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .x9 → r ≠ src → r ≠ dst → r ≠ cnt → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem B (Spec.Rc2.bytesAt s₀.mem A k)

theorem CopyI.post {s₀ s : State} {src dst cnt : Reg} {A B : Addr} {k : Nat}
    (h : CopyI s₀ src dst cnt A B k k s) : CopyPost s₀ src dst cnt A B k s := by
  refine ⟨h.psrc, h.pdst, h.other, h.rd, h.wr, h.sp, ?_⟩
  rw [h.mem, List.take_of_length_le (by simp [Spec.Rc2.bytesAt])]

/-- The registers the copy uses are distinct. -/
structure Regs (src dst cnt : Reg) : Prop where
  sd : src ≠ dst
  sc : src ≠ cnt
  dc : dst ≠ cnt
  s9 : src ≠ .x9
  d9 : dst ≠ .x9
  c9 : cnt ≠ .x9

/-- Copying `k` bytes from `A = src + so` to `B = dst + dd`, when they may be
read and written and do not overlap. -/
theorem copy_ok {src dst cnt : Reg} {so dd : Nat} (hso : so < 4096) (hdd : dd < 4096)
    (hr : Regs src dst cnt) {s₀ : State} {A B : Addr} {k : Nat}
    (hA : s₀.gpr src + BitVec.ofNat 64 so = A) (hB : s₀.gpr dst + BitVec.ofNat 64 dd = B)
    (hk : s₀.gpr cnt = BitVec.ofNat 64 k) (hk' : k < 2 ^ 64)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (B + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨A, k⟩ ⟨B, k⟩)
    {Q : State → Prop} (hQ : ∀ s, CopyPost s₀ src dst cnt A B k s → Q s) :
    WP isa (copy src so dst dd cnt) s₀ Q := by
  have hI₀ : CopyI s₀ src dst cnt A B k 0 s₀ :=
    ⟨Nat.zero_le _, by simp, by simp, by rw [hk, Nat.sub_zero], fun _ _ _ _ _ => rfl, rfl, rfl, rfl,
      by rw [List.take_zero, writeBytes_nil]⟩
  unfold copy
  refine WP.ite (decide (k = 0)) (by show VG.AArch64.eval (.zero .x cnt) s₀ = _; rw [eval_zero, hk, ofNat_beq_zero hk'])
    (fun hb => WP.block_nil (hQ _ ?_)) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact hI₀.post
  simp only [decide_eq_false_iff_not] at hb
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      CopyI s₀ src dst cnt A B k j s) ?_ k s₀ ⟨0, by omega, by omega, hI₀⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (A + BitVec.ofNat 64 j) = s₀.mem (A + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (R := ⟨B, k⟩)
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add,
        List.length_take, Spec.Rc2.bytesAt, List.length_map, List.length_range]; omega)).bytes
      (R := ⟨A, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  have hout : InRegions s.wr (B + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  unfold copyBody
  refine wp_ldrb (a := A + BitVec.ofNat 64 j) hso ?_ hin fun s₁ u₁ => ?_
  · rw [h.psrc, ← hA, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)]
  refine wp_strb (a := B + BitVec.ofNat 64 j) hdd ?_ (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.other _ hr.d9, h.pdst, ← hB, BitVec.add_assoc, BitVec.add_assoc,
      BitVec.add_comm (BitVec.ofNat 64 j)]
  refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have hcnt : s₅.gpr cnt = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ hr.dc.symm, u₃.other _ hr.sc.symm, g₂.gpr, u₁.other _ hr.c9, h.pcnt,
      sub_ofNat (by omega), Nat.sub_sub]
  have hI : CopyI s₀ src dst cnt A B k (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hcnt, fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ hr.sc, u₄.other _ hr.sd, u₃.gpr, g₂.gpr, u₁.other _ hr.s9, h.psrc,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other _ hr.dc, u₄.gpr, u₃.other _ hr.sd.symm, g₂.gpr, u₁.other _ hr.d9, h.pdst,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other x h4, u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3 h4]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · have hj' : j < (Spec.Rc2.bytesAt s₀.mem A k).length := by simp [Spec.Rc2.bytesAt]; omega
      have hl : (List.take j (Spec.Rc2.bytesAt s₀.mem A k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, setWidth_byte]
      congr 1
      simp [Spec.Rc2.bytesAt]
  have hne : isa.eval (.nonzero .x cnt) s₅ = some (decide (k - (j + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x cnt) s₅ = _
    rw [eval_nonzero, hcnt, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hne]; simp; omega, hQ _ (hjk ▸ hI).post⟩
  · exact .inr ⟨by rw [hne]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## The frame saving `x30` -/

theorem frame_push (s₀ : State) :
    Frame [⟨s₀.sp - 16, 16⟩] s₀.mem (s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30)) :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _ (by simp [Region.Contains])

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

/-- The state the frame's body starts in. -/
def inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem inner_mem (s₀ : State) : (inner s₀).mem = s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) := rfl

end VG.Proof.Rc2.AArch64.Stream
