import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Top
import VerifiedGarbage.Proof.MlKem.X86_64.FragBase

/-!
# ML-DSA signing on x86-64: the blocks between the calls

Untrusted: everything here is checked by Lean. What the function's own
instructions do, in its layout: copies (`copy_okB`), stores of a byte or of
8 bytes (`setB_okB`, `setQ_okB`), the AND of a result into `r15`
(`and15_ok`), the counters `κ` and `CNT` and the bytes of `κ + r` for
`ExpandMask` (`kapAdd_ok`, `cntDec_ok`, `setKappa_ok`), the sum of the 1s of
the hint (`onesAdd_ok`) and its check (`onesOk_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Spec.MlDsa (integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- What a block that writes only registers other than the callee-saved
ones, and memory within `W`, leaves. -/
theorem postB_of_keep {D : Nat} {rs : List Reg} {s s' : State} (k : Keep rs s s')
    (hcs : ∀ r ∈ calleeSaved, r ∉ rs) {W : List Region} (hf : Frame W s.mem s'.mem) :
    PostB D s s' W ∧ ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r :=
  ⟨⟨k.2.1, k.2.2, fun r hr => k.gpr (hcs r (bases_cs r hr)), k.gpr (hcs .rsp (by decide)),
    hf.mono fun r hr => List.mem_append_left _ hr⟩, fun r hr => k.gpr (hcs r hr)⟩

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s)
include L

/-! ## Copies -/

/-- What a copy of `n` bytes from `src` to `dst` needs of the layout. -/
def copyChk (bs wbs : List (Reg × Nat)) (dst src : Ptr) (n : Nat) : Bool :=
  inB wbs dst n && inB bs src n && sepB bs src n dst n && decide (0 < n) && decide (n < 2 ^ 31) &&
    decide (dst.2 < 2 ^ 31) && decide (src.2 < 2 ^ 31) && decide (src.1 ≠ .rdi)

omit L in
theorem copyChk_spec {bs wbs : List (Reg × Nat)} {dst src : Ptr} {n : Nat} (hc : copyChk bs wbs dst src n = true) :
    inB wbs dst n = true ∧ inB bs src n = true ∧ sepB bs src n dst n = true ∧ 0 < n ∧ n < 2 ^ 31 ∧
      dst.2 < 2 ^ 31 ∧ src.2 < 2 ^ 31 ∧ src.1 ≠ .rdi := by
  simp only [copyChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem copy_okB {dst src : Ptr} {n : Nat} (hc : copyChk (rbs ++ wbs) wbs dst src n = true) :
    WP isa (copy dst src n) s fun s' => PPostB D s s' [(dst, n)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n := by
  obtain ⟨w, i, d, h0, hn, od, os, sr⟩ := copyChk_spec hc
  exact WP.mono (VG.Proof.MlKem.X86_64.copy_ok dst src n h0 hn od os sr s (L.iR i) (L.iW w) (L.disj d))
    fun s' ⟨hb, hf, k⟩ => ⟨(postB_of_keep (D := D) k (by decide) hf).1, (postB_of_keep (D := D) k (by decide) hf).2, hb⟩

/-! ## Stores -/

theorem setB_okB {p : Ptr} {v : Nat} (hr : p.1 ≠ .rax) (hv : v < 256) (hc : inB wbs p 1 = true) :
    WP isa (.block (setB p v)) s fun s' => PPostB D s s' [(p, 1)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) := by
  refine WP.mono (VG.Proof.MlKem.X86_64.setB_ok p v hr hv s (L.iW hc)) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨pa s p, 1⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨(postB_of_keep (D := D) k (by decide) hf).1, (postB_of_keep (D := D) k (by decide) hf).2, hm⟩

omit L in
theorem setQ_ok (p : Ptr) (v : Nat) (hr : p.1 ≠ .rax) (hv : v < 2 ^ 31) (s : State)
    (hw : InRegions s.wr (pa s p) 8) :
    WP isa (.block (setQ p v)) s fun s' => s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 64 v) ∧ Keep [.rax] s s' := by
  refine WP.keep [.rax] ?_ (by rfl)
  unfold setQ
  xrun [hw, hr, sw_ofNat (show v < 2 ^ 32 by omega)]

theorem setQ_okB {p : Ptr} {v : Nat} (hr : p.1 ≠ .rax) (hv : v < 2 ^ 31) (hc : inB wbs p 8 = true) :
    WP isa (.block (setQ p v)) s fun s' => PPostB D s s' [(p, 8)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 64 v) := by
  refine WP.mono (setQ_ok p v hr hv s (L.iW hc)) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨pa s p, 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨(postB_of_keep (D := D) k (by decide) hf).1, (postB_of_keep (D := D) k (by decide) hf).2, hm⟩

end

/-! ## Results in `r15` -/

/-- A result (1 or 0) as a 64-bit register. -/
abbrev bit (b : Prop) [Decidable b] : BitVec 64 := if b then 1 else 0

theorem and15_ok (s : State) :
    WP isa (.block [.alu32 .and .r15 (.reg .rax)]) s fun s' =>
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧
        s'.mem = s.mem ∧ Keep [.r15] s s' := by
  refine WP.mono (WP.keep [.r15] (Q := fun s' =>
    s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem)
    (by xrun) (by decide)) fun s' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩

theorem bit_and {a b : Prop} [Decidable a] [Decidable b] {x y : BitVec 64} (hx : x = bit a)
    (hy : y.setWidth 32 = if b then 1 else 0) :
    BitVec.setWidth 64 (x.setWidth 32 &&& y.setWidth 32) = bit (a ∧ b) := by
  subst hx
  rw [hy]
  by_cases ha : a <;> by_cases hb : b <;> simp [bit, ha, hb]

theorem bit_setWidth {a : Prop} [Decidable a] : (bit a).setWidth 32 = if a then 1 else 0 := by
  by_cases ha : a <;> simp [bit, ha]

/-- A block that writes `r15` alone, and flags, leaves `PostB` but for `r15`. -/
theorem postB15 {D : Nat} {s s' : State} (k : Keep [.r15] s s') (hm : s'.mem = s.mem) (W : List Region) :
    PostB D s s' W ∧ ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r :=
  ⟨⟨k.2.1, k.2.2, fun r hr => k.gpr (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k.gpr (by decide),
      by rw [hm]; exact Frame.refl _ _⟩,
    fun r _ hne => k.gpr (by simpa using hne)⟩

/-! ## Counters -/

theorem ofNat64_add {a b : Nat} : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add]

/-- `[p] ← [p] + v`, through `rax`. -/
theorem addQ_ok (p : Ptr) (v : Nat) (hr : p.1 ≠ .rax) (hv : v < 2 ^ 31) (s : State) (hw : InRegions s.wr (pa s p) 8)
    (hrd : InRegions (s.rd ++ s.wr) (pa s p) 8) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ p.1 p.2)), .alu .add .rax (.imm (BitVec.ofNat 32 v)),
      .store (VG.Impl.MlKem.X86_64.at_ p.1 p.2) .rax]) s fun s' =>
      s'.mem = s.mem.writeW (pa s p) (s.mem.readW (pa s p) 64 + BitVec.ofNat 64 v) ∧ Keep [.rax] s s' := by
  refine WP.keep [.rax] ?_ (by rfl)
  xrun [hw, hrd, hr, sx_ofNat hv]

/-- `[p] ← [p] - 1`, through `rax`, and ZF set when it is 0. -/
theorem decQ_ok (p : Ptr) (hr : p.1 ≠ .rax) (s : State) (hw : InRegions s.wr (pa s p) 8)
    (hrd : InRegions (s.rd ++ s.wr) (pa s p) 8) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ p.1 p.2)), .alu .sub .rax (.imm 1),
      .store (VG.Impl.MlKem.X86_64.at_ p.1 p.2) .rax]) s fun s' =>
      (s'.mem = s.mem.writeW (pa s p) (s.mem.readW (pa s p) 64 - 1) ∧
        s'.zf = some (s.mem.readW (pa s p) 64 - 1 == 0)) ∧ Keep [.rax] s s' := by
  refine WP.keep [.rax] ?_ (by rfl)
  xrun [hw, hrd, hr]

end VG.Proof.MlDsa.X86_64.Sign
