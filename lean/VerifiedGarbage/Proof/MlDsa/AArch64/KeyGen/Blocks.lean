import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono

/-!
# ML-DSA on AArch64: the blocks between calls

The byte stores (`setB_ok`), the copies of 32 bytes (`copy_ok`, ML-KEM's), the
AND of a result into `x24` (`and24_ok`), and the masking of a sampled
polynomial by its sampler's result (`mask_ok`): kept if the sampler succeeded,
zero if it failed.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strb wp_ldrw wp_strw wp_addImm wp_subImm
  count_loop)
open VG.Spec.MlDsa (coeffAt)
open VG.Spec.Sha3 (bytesAt)

/-! ## 32-bit operations -/

theorem only_write32 (s : State) (d : Reg) (v : BitVec 32) : Only [d] s (s.write .w d v) :=
  ⟨fun r h => by simp only [List.mem_singleton] at h; simp [State.write, h], rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem write32_gpr (s : State) (d : Reg) (v : BitVec 32) : (s.write .w d v).gpr d = v.setWidth 64 := by
  simp [State.write]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_and32 {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = ((s.gpr n).setWidth 32 &&& (s.gpr m).setWidth 32).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .w d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 &&& (s.gpr m).setWidth 32))
    (by simp [exec, State.read]) (k _ (only_write32 _ _ _) (write32_gpr _ _ _))

theorem wp_sub32 {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = ((s.gpr n).setWidth 32 - (s.gpr m).setWidth 32).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.sub .w d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 - (s.gpr m).setWidth 32))
    (by simp [exec, State.read]) (k _ (only_write32 _ _ _) (write32_gpr _ _ _))

end

/-! ## Byte stores -/

theorem imm8 (v : Nat) : ((BitVec.ofNat 16 v).setWidth 64).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem bytesAt_one (m : Mem) (a : Addr) : bytesAt m a 1 = [m a] := by
  simp [Spec.Sha3.bytesAt, BitVec.add_zero]

theorem writeW8_self (m : Mem) (a : Addr) (b : Byte) : m.writeW a b a = b := by
  rw [Proof.MlKem.writeW8_apply, Proof.MlDsa.KeyGen.ifp rfl]

/-- The byte `v` to `p`. -/
theorem setB_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {p : Ptr} {v : Nat}
    (ho : p.2 < 4096) (hw : inB wbs p 1 = true) (hb : p.1 ∈ keptRegs) :
    WP isa (.block (setB p v)) s fun s' => PPostB S s s' [(p, 1)] ∧ Keep [.x9] s s' ∧
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) := by
  have h9 : p.1 ≠ .x9 := by
    intro e; rw [e] at hb; revert hb; decide
  refine wp_movz fun s₁ h₁ e₁ => wp_strb (a := pa s p) ho (by rw [h₁.get p.1 (by simpa using h9)])
    (by rw [h₁.wr]; exact L.inW hw) fun s₂ h₂ => wp_nil ?_
  have m₂ : s₂.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) := by rw [h₂.mem, e₁, h₁.mem, imm8 v]
  have k₂ : Keep [.x9] s s₂ := (h₁.keep.trans h₂.keep).mono (by simp)
  refine ⟨postB_of_keep k₂ (by decide) ?_, k₂, m₂⟩
  rw [m₂]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The AND of a result -/

theorem and24_ok (s : State) :
    WP isa (.block and24) s fun s' => Only [.x24] s s' ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 :=
  wp_and32 fun _ h e => wp_nil ⟨h, e⟩

/-! ## Masking a sampled polynomial -/

theorem coeffAt_writeW32 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

/-- The coefficients after masking with the 32 bits `r`, 0 or 1. -/
theorem and_mask {r : BitVec 32} (hr : r = 0 ∨ r = 1) (x : BitVec 32) :
    x &&& (BitVec.setWidth 64 (BitVec.setWidth 32 (0 : BitVec 64) - r)).setWidth 32 = if r = 1 then x else 0 := by
  rcases hr with rfl | rfl
  · simp
  · rw [Proof.MlDsa.KeyGen.ifp rfl, show (BitVec.setWidth 64 (BitVec.setWidth 32 (0 : BitVec 64) - (1 : BitVec 32))).setWidth 32 =
      BitVec.allOnes 32 by decide]
    exact BitVec.and_allOnes

abbrev maskBody : List Instr := [.ldr .w .x9 .x1 0, .logic .and .w .x9 .x9 .x8, .str .w .x9 .x1 0,
  .addImm .x .x1 .x1 4, .subImm .x .x2 .x2 1]

theorem maskBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 4) (h1 : InRegions s.wr (s.gpr .x1) 4) :
    WP isa (.block maskBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x1) (s.mem.readW (s.gpr .x1) 32 &&& (s.gpr .x8).setWidth 32) ∧
        s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧ s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 1) ∧
      Keep [.x1, .x2, .x9] s s' := by
  have e0 : s.gpr .x1 + BitVec.ofNat 64 0 = s.gpr .x1 := BitVec.add_zero _
  refine wp_ldrw (a := s.gpr .x1) (by decide) e0 h0 fun s₁ h₁ e₁ => wp_and32 fun s₂ h₂ e₂ =>
    wp_strw (a := s.gpr .x1) (by decide) (by rw [h₂.get .x1, h₁.get .x1, e0]) (by rw [h₂.wr, h₁.wr]; exact h1)
      fun s₃ h₃ => wp_addImm (by decide) fun s₄ h₄ e₄ => wp_subImm (by decide) fun s₅ h₅ e₅ => wp_nil ?_
  refine ⟨⟨?_, ?_, ?_⟩, ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).mono (by simp)⟩
  · rw [h₅.mem, h₄.mem, h₃.mem, e₂, h₂.mem, h₁.mem, e₁, h₁.get .x8]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and]
  · rw [h₅.get .x1, e₄, show s₃.gpr .x1 = s₂.gpr .x1 by rw [h₃.gpr], h₂.get .x1, h₁.get .x1]
  · rw [e₅, h₄.get .x2, show s₃.gpr .x2 = s₂.gpr .x2 by rw [h₃.gpr], h₂.get .x2, h₁.get .x2]

theorem off_add4 (b : Addr) (i : Nat) : b + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 4 = b + BitVec.ofNat 64 (4 * (i + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2

theorem ofNat_sub1 {i : Nat} (h : i < 256) : BitVec.ofNat 64 (256 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (256 - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem mask_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a : Ptr}
    (hw : inB wbs a 1024 = true) (hin : inB (rbs ++ wbs) a 1024 = true)
    (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1) :
    WP isa (mask a) s fun s' => PPostB S s s' [(a, 1024)] ∧ Keep [.x1, .x2, .x8, .x9] s s' ∧
      ∀ i < 256, coeffAt s'.mem (pa s a) i =
        if (s.gpr .x0).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  have hW : InRegions s.wr (pa s a) 1024 := L.inW hw
  have hn : (pa s a).toNat + 1024 ≤ 2 ^ 64 := L.nwp hin
  have hb : a.1 ∈ keptRegs := L.ptrBs hin
  have h1 : a.1 ≠ .x1 := by intro e; rw [e] at hb; revert hb; decide
  have h8 : a.1 ≠ .x8 := by intro e; rw [e] at hb; revert hb; decide
  unfold mask
  refine WP.seq ?_
  refine wp_movz fun s₁ h₁ e₁ => wp_sub32 fun s₂ h₂ e₂ => lea_ok h1.symm a.2 fun s₃ h₃ e₃ =>
    wp_movz fun s₄ h₄ e₄ => wp_nil ?_
  have k₄ : Keep [.x1, .x2, .x8, .x9] s s₄ := (((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).mono (by simp)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have x8 : s₄.gpr .x8 = BitVec.setWidth 64 (BitVec.setWidth 32 (0 : BitVec 64) - (s.gpr .x0).setWidth 32) := by
    rw [h₄.get .x8, h₃.get .x8, e₂, e₁, h₁.get .x0]; rfl
  have x1 : s₄.gpr .x1 = pa s a := by
    rw [h₄.get .x1, e₃, h₂.get a.1 (by simpa using h8), h₁.get a.1 (by simpa using h8)]
  refine WP.mono (count_loop (cr := .x2) (n := 256) (by decide) (fun i s' =>
      s'.gpr .x1 = pa s a + BitVec.ofNat 64 (4 * i) ∧ s'.gpr .x2 = BitVec.ofNat 64 (256 - i) ∧
      s'.gpr .x8 = s₄.gpr .x8 ∧ Keep [.x1, .x2, .x8, .x9] s s' ∧ Frame [⟨pa s a, 1024⟩] s.mem s'.mem ∧
      ∀ j < 256, coeffAt s'.mem (pa s a) j =
        if j < i then coeffAt s.mem (pa s a) j &&& (s₄.gpr .x8).setWidth 32 else coeffAt s.mem (pa s a) j)
    (fun i hi s' ⟨e1, e2, e8, kk, hf, hc⟩ => ?_)
    ⟨by rw [x1, Nat.mul_zero, BitVec.add_zero], by rw [e₄]; rfl, rfl, k₄, by rw [m₄]; exact Frame.refl _ _,
      fun j _ => by rw [Proof.MlDsa.KeyGen.ifn (Nat.not_lt_zero j), m₄]⟩)
    fun s' ⟨_, _, _, kk, hf, hc⟩ => ⟨postB_of_keep kk (by decide) hf, kk, fun j hj => ?_⟩
  · have hc4 : (⟨pa s a, 1024⟩ : Region).Contains (pa s a + BitVec.ofNat 64 (4 * i)) 4 :=
      Offset.contains_base _ (by omega) (by omega)
    have hinw : InRegions s'.wr (s'.gpr .x1) 4 := by
      rw [kk.wr, e1]; exact inRegions_sub hW (by omega) (by omega)
    have hin0 : InRegions (s'.rd ++ s'.wr) (s'.gpr .x1) 4 := VG.Proof.MlKem.AArch64.in_rd_wr hinw
    refine WP.mono (maskBody_ok s' hin0 hinw) fun s'' ⟨⟨hm, e1', e2'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [k'.get .x8, e8],
      (kk.trans k').mono (by simp), ?_, fun j hj => ?_⟩, ?_⟩
    · rw [e1', e1, off_add4]
    · rw [e2', e2, ofNat_sub1 hi]
    · rw [hm, e1]; exact hf.writeW (List.mem_singleton_self _) _ hc4
    · rw [hm, e1, coeffAt_writeW32 _ _ hj (by omega), e8]
      by_cases e : i = j
      · subst e
        rw [Proof.MlDsa.KeyGen.ifp rfl, Proof.MlDsa.KeyGen.ifp (Nat.lt_succ_self _)]
        have := hc i hj
        rw [Proof.MlDsa.KeyGen.ifn (Nat.lt_irrefl _)] at this
        rw [← this]; rfl
      · rw [Proof.MlDsa.KeyGen.ifn e, hc j hj]
        by_cases hji : j < i
        · rw [Proof.MlDsa.KeyGen.ifp hji, Proof.MlDsa.KeyGen.ifp (by omega)]
        · rw [Proof.MlDsa.KeyGen.ifn hji, Proof.MlDsa.KeyGen.ifn (by omega)]
    · rw [e2', e2, ofNat_sub1 hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [hc j hj, Proof.MlDsa.KeyGen.ifp hj, x8, and_mask hr]

/-! ## Copies of 32 bytes -/

/-- The 32 bytes at `src` can be copied to `dst`. -/
def copyChk (rbs wbs : List (Reg × Nat)) (dst src : Ptr) : Bool :=
  decide (src.2 % 8 = 0 ∧ src.2 + 32 ≤ 32768) && decide (dst.2 % 8 = 0 ∧ dst.2 + 32 ≤ 32768) &&
    sepB rbs wbs src 32 dst 32 && inB wbs dst 32

theorem copyP_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {dst src : Ptr}
    (hc : copyChk rbs wbs dst src = true) :
    WP isa (.block (Impl.MlKem.AArch64.copy32 src.1 src.2 dst.1 dst.2)) s fun s' =>
      PPostB S s s' [(dst, 32)] ∧ Keep [.x9] s s' ∧ bytesAt s'.mem (pa s dst) 32 = bytesAt s.mem (pa s src) 32 := by
  simp only [copyChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hso, hdo⟩, hsep⟩, hw⟩ := hc
  have i1 := (sepB_spec hsep).1
  have i2 := (sepB_spec hsep).2.1
  have n9 : ∀ r ∈ keptRegs, r ≠ .x9 := by decide
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr src.1) (D := s.gpr dst.1)
    (n9 _ (L.ptrBs i1)) (n9 _ (L.ptrBs i2)) hso hdo (L.disj hsep) rfl rfl (L.cR i1) (L.cW hw))
    fun s' ⟨k, f, b⟩ => ⟨postB_of_keep k (by decide) f, k, b⟩

/-! ## After a sampler -/

/-- The result `w0` of a sampler ANDed into `x24`, and its output masked with it. -/
theorem tail_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a : Ptr}
    (hw : inB wbs a 1024 = true) (hin : inB (rbs ++ wbs) a 1024 = true)
    (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1) :
    WP isa (.seq (.block and24) (mask a)) s fun s' => PPostB S s s' [(a, 1024)] ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 ∧
      ∀ i < 256, coeffAt s'.mem (pa s a) i = if (s.gpr .x0).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  refine WP.seq (WP.mono (and24_ok s) fun s₁ ⟨o₁, e₁⟩ => ?_)
  have P₁ : PostB S s s₁ [] := postB_of_keep o₁.keep (by decide) (by rw [o₁.mem]; exact Frame.refl _ _)
  have L₁ := L.post P₁
  have x0 : s₁.gpr .x0 = s.gpr .x0 := o₁.get .x0
  rw [← x0] at hr
  refine WP.mono (mask_ok L₁ hw hin hr) fun s' ⟨P', k', hc⟩ => ⟨?_, by rw [k'.get .x24, e₁], ?_⟩
  · refine PostB.trans P₁ ?_ (fun _ h => absurd h List.not_mem_nil) fun _ h => h
    have e : ([(a, 1024)] : List (Ptr × Nat)).map (toR s₁) = [(a, 1024)].map (toR s) :=
      map_toR_post P₁ (fun w hw => by rw [List.mem_singleton.mp hw]; exact L.ptrBs hin)
    rw [← e]; exact P'
  · intro i hi
    rw [← P₁.pa (L.ptrBs hin), hc i hi, x0, o₁.mem]

end VG.Proof.MlDsa.AArch64.KeyGen
