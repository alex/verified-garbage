import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CallMore
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd
import VerifiedGarbage.Proof.MlKem.AArch64.KgA
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono

/-!
# ML-DSA signing on AArch64: the blocks between the calls

What the function's own instructions do, in its layout, besides those of
`Proof/MlDsa/AArch64/Call/Blocks.lean`: stores of 8 bytes (`setQ_ok`), copies
of any number of bytes, one at a time (`copy_ok`), the counters `κ` and `CNT`
and the bytes of `κ + r` for `ExpandMask` (`kapAdd_ok`, `cntDec_ok`,
`setKappa_ok`), the sum of the 1s of the hint (`onesAdd_ok`) and its check
(`onesOk_run`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strb wp_ldrb wp_ldrw wp_strw wp_ldrx wp_strx
  wp_addImm wp_subImm wp_lsr count_loop)
open VG.Spec.MlDsa (coeffAt integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-! ## 32-bit operations -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_add32 {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = ((s.gpr n).setWidth 32 + (s.gpr m).setWidth 32).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.add .w d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 + (s.gpr m).setWidth 32))
    (by simp [exec, State.read]) (k _ (only_write32 _ _ _) (write32_gpr _ _ _))

end

/-! ## Stores -/

theorem imm64 {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The 8 bytes `v` to `p`. -/
theorem setQ_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {p : Ptr} {v : Nat}
    (ho : p.2 % 8 = 0 ∧ p.2 < 4096 * 8) (hv : v < 65536) (hw : inB wbs p 8 = true) (hb : p.1 ∈ keptRegs) :
    WP isa (.block (setQ p v)) s fun s' => PPostB S s s' [(p, 8)] ∧ Keep [.x9] s s' ∧
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 64 v) := by
  have h9 := ne_x9 hb
  refine wp_movz fun s₁ h₁ e₁ => wp_strx (a := pa s p) ho (by rw [h₁.get p.1 (by simpa using h9)])
    (by rw [h₁.wr]; exact L.inW hw) fun s₂ h₂ => wp_nil ?_
  have m₂ : s₂.mem = s.mem.writeW (pa s p) (BitVec.ofNat 64 v) := by rw [h₂.mem, e₁, h₁.mem, imm64 hv]
  have k₂ : Keep [.x9] s s₂ := (h₁.keep.trans h₂.keep).mono (by simp)
  refine ⟨postB_of_keep k₂ (by decide) ?_, k₂, m₂⟩
  rw [m₂]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The AND of a result -/

/-- A result (1 or 0) as a 64-bit register. -/
abbrev bit (b : Prop) [Decidable b] : BitVec 64 := if b then 1 else 0

theorem bit_and {a b : Prop} [Decidable a] [Decidable b] {x y : BitVec 64} (hx : x = bit a)
    (hy : y.setWidth 32 = if b then 1 else 0) :
    BitVec.setWidth 64 (x.setWidth 32 &&& y.setWidth 32) = bit (a ∧ b) := by
  subst hx
  rw [hy]
  by_cases ha : a <;> by_cases hb : b <;> simp [bit, ha, hb]

theorem bit_setWidth {a : Prop} [Decidable a] : (bit a).setWidth 32 = if a then 1 else 0 := by
  by_cases ha : a <;> simp [bit, ha]

/-- A block that writes only `x24` keeps `PostB`. -/
theorem postB24 {S : Nat} {s s' : State} (k : Only [.x24] s s') (W : List Region) : PostB S s s' W :=
  postB_of_keep k.keep (by decide) (by rw [k.mem]; exact Frame.refl _ _)

/-! ## Copies, a byte at a time -/

theorem ne_x0 {r : Reg} (h : r ∈ keptRegs) : r ≠ .x0 := by
  intro e; rw [e] at h; revert h; decide

theorem ne_x1 {r : Reg} (h : r ∈ keptRegs) : r ≠ .x1 := by
  intro e; rw [e] at h; revert h; decide

theorem copyBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 1) (h1 : InRegions s.wr (s.gpr .x0) 1) :
    WP isa (.block copyBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x0) (s.mem (s.gpr .x1)) ∧ s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 1 ∧
        s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 1 ∧ s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x1, .x2, .x9] s s' := by
  have e1 : s.gpr .x1 + BitVec.ofNat 64 0 = s.gpr .x1 := BitVec.add_zero _
  have e0 : s.gpr .x0 + BitVec.ofNat 64 0 = s.gpr .x0 := BitVec.add_zero _
  refine wp_ldrb (a := s.gpr .x1) (by decide) e1 h0 fun s₁ h₁ v₁ =>
    wp_strb (a := s.gpr .x0) (by decide) (by rw [h₁.get .x0, e0]) (by rw [h₁.wr]; exact h1) fun s₂ h₂ =>
      wp_addImm (by decide) fun s₃ h₃ e₃ => wp_addImm (by decide) fun s₄ h₄ e₄ =>
        wp_subImm (by decide) fun s₅ h₅ e₅ => wp_nil ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).mono (by simp)⟩
  · rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, v₁, h₁.mem]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp
  · rw [h₅.get .x0, h₄.get .x0, e₃, show s₂.gpr .x0 = s₁.gpr .x0 by rw [h₂.gpr], h₁.get .x0]
  · rw [h₅.get .x1, e₄, h₃.get .x1, show s₂.gpr .x1 = s₁.gpr .x1 by rw [h₂.gpr], h₁.get .x1]
  · rw [e₅, h₄.get .x2, h₃.get .x2, show s₂.gpr .x2 = s₁.gpr .x2 by rw [h₂.gpr], h₁.get .x2]

theorem off_add1 (b : Addr) (i : Nat) : b + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = b + BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ofNat_sub_one {n i : Nat} (h : i < n) :
    BitVec.ofNat 64 (n - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The glue of a copy: `x0 ← dst`, `x1 ← src`, `x2 ← n`. -/
theorem copyGlue_ok {dst src : Ptr} {n : Nat} (hd : dst.1 ∈ keptRegs) (hs : src.1 ∈ keptRegs) (s : State) :
    WP isa (.block (lea .x0 dst.1 dst.2 ++ lea .x1 src.1 src.2 ++ movV .x2 n)) s fun s' =>
      (s'.gpr .x0 = pa s dst ∧ s'.gpr .x1 = pa s src ∧ s'.gpr .x2 = BitVec.ofNat 64 n) ∧ Only [.x0, .x1, .x2] s s' := by
  rw [List.append_assoc, ← List.append_nil (movV .x2 n)]
  refine lea_ok (ne_x0 hd).symm dst.2 fun s₁ h₁ e₁ => lea_ok (ne_x1 hs).symm src.2 fun s₂ h₂ e₂ =>
    movV_ok .x2 n fun s₃ h₃ e₃ => wp_nil ⟨⟨?_, ?_, e₃⟩, ((h₁.trans h₂).trans h₃).mono (by simp)⟩
  · rw [h₃.get .x0, h₂.get .x0, e₁]
  · rw [h₃.get .x1, e₂, h₁.get src.1 (by simpa using ne_x0 hs)]

/-- A copy of `n` bytes from `src` to `dst`, apart. -/
theorem copy_core {dst src : Ptr} {n : Nat} (h0 : 0 < n) (hn : n < 2 ^ 32) (hd : dst.1 ∈ keptRegs) (hs : src.1 ∈ keptRegs)
    (s : State) (hrd : InRegions (s.rd ++ s.wr) (pa s src) n) (hwr : InRegions s.wr (pa s dst) n)
    (hdj : Region.Disjoint ⟨pa s src, n⟩ ⟨pa s dst, n⟩) :
    WP isa (copy dst src n) s fun s' =>
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n ∧ Frame [⟨pa s dst, n⟩] s.mem s'.mem ∧
        Keep [.x0, .x1, .x2, .x9] s s' := by
  unfold copy
  refine WP.seq (WP.mono (copyGlue_ok hd hs s) fun s1 ⟨⟨a0, a1, a2⟩, k1⟩ => ?_)
  refine WP.mono (count_loop (cr := .x2) (n := n) h0 (fun k s' =>
      s'.gpr .x0 = pa s dst + BitVec.ofNat 64 k ∧ s'.gpr .x1 = pa s src + BitVec.ofNat 64 k ∧
      s'.gpr .x2 = BitVec.ofNat 64 (n - k) ∧ Keep [.x0, .x1, .x2, .x9] s s' ∧
      Frame [⟨pa s dst, n⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (pa s dst + BitVec.ofNat 64 j) = s.mem (pa s src + BitVec.ofNat 64 j)))
    (fun k hk s' ⟨e0, e1, e2, kk, hf, hc⟩ => ?_)
    ⟨by rw [a0, BitVec.add_zero], by rw [a1, BitVec.add_zero], by rw [a2, Nat.sub_zero], k1.keep.mono (by simp),
      by rw [k1.mem]; exact Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    fun s' ⟨_, _, _, kk, hf, hc⟩ => ⟨?_, hf, kk⟩
  · have hsrc : s'.mem (pa s src + BitVec.ofNat 64 k) = s.mem (pa s src + BitVec.ofNat 64 k) :=
      hf.bytes (R := ⟨pa s src, n⟩) (by simpa using hdj) (show n ≤ 2 ^ 64 by omega) hk
    refine WP.mono (copyBody_ok s' (by rw [kk.rd, kk.wr, e1]; exact inRegions_sub hrd (by omega) (by omega))
      (by rw [kk.wr, e0]; exact inRegions_sub hwr (by omega) (by omega))) fun s'' ⟨⟨hm, e0', e1', e2'⟩, k'⟩ =>
        ⟨⟨by rw [e0', e0, off_add1], by rw [e1', e1, off_add1], by rw [e2', e2, ofNat_sub_one hk],
          (kk.trans k').mono (by simp), ?_, fun j hj => ?_⟩, ?_⟩
    · rw [hm, e0]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [hm, e0, e1, Proof.MlKem.writeW8_apply]
      by_cases e : j = k
      · subst e; rw [Proof.MlDsa.KeyGen.ifp rfl, hsrc]
      · rw [Proof.MlDsa.KeyGen.ifn (fun h => e (by
          have h' := congrArg (fun x => x - pa s dst) h
          simp only [Offset.add_sub_cancel_left] at h'
          have := congrArg BitVec.toNat h'
          simp only [BitVec.toNat_ofNat] at this
          omega)), hc j (by omega)]
    · rw [e2', e2, ofNat_sub_one hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)

/-- What a copy of `n` bytes from `src` to `dst` needs of the layout. -/
def copyChk (rbs wbs : List (Reg × Nat)) (dst src : Ptr) (n : Nat) : Bool :=
  inB wbs dst n && inB (rbs ++ wbs) src n && sepB rbs wbs src n dst n && decide (0 < n) && decide (n < 2 ^ 32)

theorem copy_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {dst src : Ptr} {n : Nat}
    (hc : copyChk rbs wbs dst src n = true) :
    WP isa (copy dst src n) s fun s' => PPostB S s s' [(dst, n)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n := by
  simp only [copyChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨w, i⟩, d⟩, h0⟩, hn⟩ := hc
  have id := (sepB_spec d).2.1
  refine WP.mono (copy_core h0 hn (L.ptrBs id) (L.ptrBs i) s (L.inR i) (L.inW w) (L.disj d))
    fun s' ⟨hb, hf, k⟩ => ⟨postB_of_keep k (by decide) hf, k.get .x24, hb⟩

/-! ## Counters -/

theorem ofNat64_add {a b : Nat} : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add]

/-- `KAP ← KAP + ℓ`. -/
theorem kapAdd_ok (p : Spec.MlDsa.Params) (hl : p.ℓ < 4096) (s : State) (hw : InRegions s.wr (pa s (sc oKAP)) 8)
    (hrd : InRegions (s.rd ++ s.wr) (pa s (sc oKAP)) 8) :
    WP isa (.block (kapAdd p)) s fun s' =>
      s'.mem = s.mem.writeW (pa s (sc oKAP)) (s.mem.readW (pa s (sc oKAP)) 64 + BitVec.ofNat 64 p.ℓ) ∧
        Keep [.x9] s s' := by
  refine wp_ldrx (a := pa s (sc oKAP)) (by decide) rfl hrd fun s₁ h₁ e₁ => wp_addImm hl fun s₂ h₂ e₂ =>
    wp_strx (a := pa s (sc oKAP)) (by decide) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact hw)
      fun s₃ h₃ => wp_nil ⟨?_, ((h₁.keep.trans h₂.keep).trans h₃.keep).mono (by simp)⟩
  rw [h₃.mem, e₂, e₁, h₂.mem, h₁.mem]

/-- `CNT ← CNT - 1`, and `x9 = CNT`. -/
theorem cntDec_ok (s : State) (hw : InRegions s.wr (pa s (sc oCNT)) 8)
    (hrd : InRegions (s.rd ++ s.wr) (pa s (sc oCNT)) 8) :
    WP isa (.block cntDec) s fun s' =>
      (s'.mem = s.mem.writeW (pa s (sc oCNT)) (s.mem.readW (pa s (sc oCNT)) 64 - BitVec.ofNat 64 1) ∧
        s'.gpr .x9 = s.mem.readW (pa s (sc oCNT)) 64 - BitVec.ofNat 64 1) ∧ Keep [.x9] s s' := by
  refine wp_ldrx (a := pa s (sc oCNT)) (by decide) rfl hrd fun s₁ h₁ e₁ => wp_subImm (by decide) fun s₂ h₂ e₂ =>
    wp_strx (a := pa s (sc oCNT)) (by decide) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact hw)
      fun s₃ h₃ => wp_nil ⟨⟨?_, ?_⟩, ((h₁.keep.trans h₂.keep).trans h₃.keep).mono (by simp)⟩
  · rw [h₃.mem, e₂, e₁, h₂.mem, h₁.mem]
  · rw [show s₃.gpr .x9 = s₂.gpr .x9 by rw [h₃.gpr], e₂, e₁]

/-- The two bytes of `KAP + r` to `MS + 64`. -/
theorem setKappa_run (r : Nat) (hr : r < 4096) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (pa s (sc oKAP)) 8) (h2 : InRegions s.wr (pa s (sc (oMS + 64))) 1)
    (h3 : InRegions s.wr (pa s (sc (oMS + 65))) 1) :
    WP isa (.block (setKappa r)) s fun s' =>
      s'.mem = (s.mem.writeW (pa s (sc (oMS + 64)))
        ((s.mem.readW (pa s (sc oKAP)) 64 + BitVec.ofNat 64 r).setWidth 8)).writeW
        (pa s (sc (oMS + 65))) (((s.mem.readW (pa s (sc oKAP)) 64 + BitVec.ofNat 64 r) >>> 8).setWidth 8) ∧
        Keep [.x9] s s' := by
  refine wp_ldrx (a := pa s (sc oKAP)) (by decide) rfl h1 fun s₁ h₁ e₁ => wp_addImm hr fun s₂ h₂ e₂ =>
    wp_strb (a := pa s (sc (oMS + 64))) (by decide) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact h2)
      fun s₃ h₃ => wp_lsr (by decide) fun s₄ h₄ e₄ =>
        wp_strb (a := pa s (sc (oMS + 65))) (by decide) (by rw [h₄.get .x28, show s₃.gpr .x28 = s₂.gpr .x28 by
          rw [h₃.gpr], h₂.get .x28, h₁.get .x28]) (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact h3)
          fun s₅ h₅ => wp_nil ⟨?_, ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).mono
            (by simp)⟩
  rw [h₅.mem, e₄, h₄.mem, h₃.mem, show s₃.gpr .x9 = s₂.gpr .x9 by rw [h₃.gpr], e₂, e₁, h₂.mem, h₁.mem]

/-! ## The 1s of the hint -/

theorem onesAdd_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (pa s (sc oONES)) 8)
    (h2 : InRegions s.wr (pa s (sc oONES)) 8) :
    WP isa (.block onesAdd) s fun s' => s'.mem = s.mem.writeW (pa s (sc oONES))
      (BitVec.setWidth 64 ((s.mem.readW (pa s (sc oONES)) 64).setWidth 32 + (s.gpr .x0).setWidth 32)) ∧
      Keep [.x9] s s' := by
  refine wp_ldrx (a := pa s (sc oONES)) (by decide) rfl h1 fun s₁ h₁ e₁ => wp_add32 fun s₂ h₂ e₂ =>
    wp_strx (a := pa s (sc oONES)) (by decide) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact h2)
      fun s₃ h₃ => wp_nil ⟨?_, ((h₁.keep.trans h₂.keep).trans h₃.keep).mono (by simp)⟩
  rw [h₃.mem, e₂, e₁, h₂.mem, h₁.mem, h₁.get .x0]

theorem onesOk_run (p : Spec.MlDsa.Params) (hω : p.ω + 1 < 4096) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (pa s (sc oONES)) 8) :
    WP isa (.block (onesOk p)) s fun s' => (s'.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&&
      ((s.mem.readW (pa s (sc oONES)) 64 - BitVec.ofNat 64 (p.ω + 1)) >>> 63).setWidth 32) ∧
      s'.mem = s.mem) ∧ Keep [.x9, .x24] s s' := by
  refine wp_ldrx (a := pa s (sc oONES)) (by decide) rfl h1 fun s₁ h₁ e₁ => wp_subImm hω fun s₂ h₂ e₂ =>
    wp_lsr (by decide) fun s₃ h₃ e₃ => wp_and32 fun s₄ h₄ e₄ =>
      wp_nil ⟨⟨?_, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]⟩,
        ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep)).mono (by simp)⟩
  rw [e₄, e₃, e₂, e₁, h₃.get .x24, h₂.get .x24, h₁.get .x24]

end VG.Proof.MlDsa.AArch64.Sign
