import VerifiedGarbage.Impl.MlKem.X86_64.Sample
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM on x86-64: the loop of `vg_mlkem_sample_ntt`

Untrusted: everything here is checked by Lean. An iteration of the loop
does what `sampleStepCap` does to the coefficients sampled so far, stored
at `a` (`Stored`) and counted in `rdi` (`snBody_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The values of an iteration -/

/-- `d₁` of the bytes `c₀`, `c₁`, as the code computes it. -/
def d1w (c0 c1 : Byte) : BitVec 32 :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 c1) &&& 15).rotateRight 24 + BitVec.setWidth 32 (BitVec.setWidth 64 c0)

/-- `d₂` of the bytes `c₁`, `c₂`, as the code computes it. -/
def d2w (c1 c2 : Byte) : BitVec 32 :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 c2)).rotateRight 28 + BitVec.setWidth 32 (BitVec.setWidth 64 c1) >>> 4

theorem b32 (c : Byte) : (BitVec.setWidth 32 (BitVec.setWidth 64 c)).toNat = c.toNat := by
  rw [BitVec.toNat_setWidth, toNat_setWidth64_8, Nat.mod_eq_of_lt (by have := c.isLt; omega)]

theorem d1w_toNat (c0 c1 : Byte) : (d1w c0 c1).toNat = c0.toNat + 256 * (c1.toNat % 16) := by
  have h0 := c0.isLt
  have e : (BitVec.setWidth 32 (BitVec.setWidth 64 c1) &&& 15).toNat = c1.toNat % 16 := by
    rw [BitVec.toNat_and, b32, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hr := rotr_toNat (BitVec.setWidth 32 (BitVec.setWidth 64 c1) &&& 15) (r := 24) (by decide)
    (by rw [e]; have := Nat.mod_lt c1.toNat (show 16 > 0 by decide); omega)
  rw [e] at hr
  have := Nat.mod_lt c1.toNat (show 16 > 0 by decide)
  rw [d1w, BitVec.toNat_add, hr, b32]
  rw [show 32 - 24 = 8 from rfl]; omega

theorem d2w_toNat (c1 c2 : Byte) : (d2w c1 c2).toNat = c1.toNat / 16 + 16 * c2.toNat := by
  have h1 := c1.isLt
  have h2 := c2.isLt
  have hr := rotr_toNat (BitVec.setWidth 32 (BitVec.setWidth 64 c2)) (r := 28) (by decide)
    (by rw [b32]; omega)
  rw [b32] at hr
  rw [d2w, BitVec.toNat_add, hr, shr_toNat, b32]
  rw [show 32 - 28 = 4 from rfl]; omega

theorem sx256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide

theorem snLoad_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1) :
    WP isa (.block snLoad) s fun s' =>
      (s'.gpr .r9 = BitVec.setWidth 64 (d1w (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))) ∧
        s'.gpr .r8 = BitVec.setWidth 64 (d2w (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
          (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))) ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi) ∧
      Keep [.rax, .rdx, .r8, .r9, .rdi] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold snLoad
  xrun [h0, h1, h2, sx256, d1w, d2w, show (256 : BitVec 64).toNat = 256 from rfl]

/-! ## Storing a coefficient -/

/-- The coefficients `L` are stored at `aP`. -/
def Stored (m : Mem) (aP : Addr) (L : List Zq) : Prop :=
  ∀ k < L.length, coeffAt m aP k = BitVec.ofNat 32 (L.getD k 0).val

theorem ea_aJ (s : State) {aP : Addr} {j : Nat} (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 j)
    (_hj : j < 256) : s.ea aJ = coeffAddr aP j := by
  simp only [State.ea, aJ, hbp, hdi]
  rw [coeffAddr, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem snTryCmp_ok (r : Reg) (s : State) :
    WP isa (.block [.alu32 .cmp r (.imm qImm)]) s fun s' =>
      s'.cf = some (decide (((s.gpr r).setWidth 32).toNat < 3329)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun [qImm_toNat]
  rfl

theorem snTryStore_ok (r : Reg) (s : State) {a : Addr} (ha : s.ea aJ = a) (hw : InRegions s.wr a 4) :
    WP isa (.block [.store32 aJ r, .alu .add .rdi (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW a ((s.gpr r).setWidth 32) ∧ s'.gpr .rdi = s.gpr .rdi + 1) ∧ Keep [.rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [ha, hw]

theorem stored_snoc {m : Mem} {aP : Addr} {L : List Zq} (h : Stored m aP L) (hL : L.length < 256) {v : BitVec 32}
    (hv : v.toNat < q) : Stored (m.writeW (coeffAddr aP L.length) v) aP (L ++ [ofNat v.toNat]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rw [coeffAt_writeW _ _ (show k < 256 by omega) hL]
  by_cases e : L.length = k
  · subst e
    rw [ifp rfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ofNat_of_lt hv, Nat.mod_eq_of_lt (by rw [q_eq] at hv; omega)]
  · rw [ifn e, h k (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]

theorem ofNat64_succ {j : Nat} (_h : j + 1 < 2 ^ 64) : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

/-- Store the value of `r` to `a[j]` if it is less than `q`. -/
theorem snTry_ok (r : Reg) (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length < 256) (hw : pR aP ∈ s.wr)
    (hst : Stored s.mem aP L) :
    WP isa (snTry r) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (if ((s.gpr r).setWidth 32).toNat < q
        then L ++ [ofNat ((s.gpr r).setWidth 32).toNat] else L).length ∧
      Stored s'.mem aP (if ((s.gpr r).setWidth 32).toNat < q
        then L ++ [ofNat ((s.gpr r).setWidth 32).toNat] else L) ∧
      Frame [pR aP] s.mem s'.mem ∧ Keep [.rdi] s s' := by
  refine WP.seq (WP.mono (snTryCmp_ok r s) fun s1 ⟨hc, hm, hg, hrd, hwr⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by rw [hg], hrd, hwr⟩
  have hr : s1.gpr r = s.gpr r := by rw [hg]
  refine WP.ite (decide (((s.gpr r).setWidth 32).toNat < q)) hc (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    simp only [hb, ite_true]
    refine WP.mono (snTryStore_ok r s1 (ea_aJ s1 (aP := aP) (by rw [k1.gpr (by simp), hbp]) (by rw [k1.gpr (by simp), hdi]) hL)
      (by rw [k1.2.2]; exact ⟨_, hw, coeff_contains _ hL⟩)) fun s2 ⟨⟨hm2, hdi2⟩, k2⟩ => ⟨?_, ?_, ?_, ?_⟩
    · rw [hdi2, k1.gpr (by simp), hdi, List.length_append, List.length_singleton]
      exact ofNat64_succ (by omega)
    · rw [hm2, hm, hr]; exact stored_snoc hst hL hb
    · rw [hm2, hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hL)
    · exact (k1.trans k2).mono (by simp)
  · simp only [decide_eq_false_iff_not] at hb
    simp only [hb, ite_false]
    refine WP.block_nil ⟨by rw [k1.gpr (by simp), hdi], by rw [hm]; exact hst, by rw [hm]; exact Frame.refl _ _,
      k1.mono (by simp)⟩


/-! ## An iteration -/

/-- Lines 5–15 of Algorithm 7 on the values `d₁`, `d₂`. -/
def stepD (L : List Zq) (d1 d2 : Nat) : List Zq :=
  let a := if d1 < q then L ++ [ofNat d1] else L
  if d2 < q ∧ a.length < n then a ++ [ofNat d2] else a

theorem sampleStep_eq (L : List Zq) (c0 c1 c2 : Byte) :
    sampleStep L c0 c1 c2 = stepD L (c0.toNat + 256 * (c1.toNat % 16)) (c1.toNat / 16 + 16 * c2.toNat) := rfl

theorem cmpRdi_ok (s : State) :
    WP isa (.block [.alu .cmp .rdi (.imm 256)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun [sx256, show (256 : BitVec 64).toNat = 256 from rfl]

theorem ofNat64_toNat {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The coefficients after an iteration, from `L` and the values `d₁`, `d₂`. -/
def midL (L : List Zq) (d1 d2 : Nat) : List Zq := if L.length < 256 then stepD L d1 d2 else L

/-- The two tries, if `j < 256`. -/
theorem snMid_ok (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : pR aP ∈ s.wr)
    (hst : Stored s.mem aP L) (hcf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))) :
    WP isa (.ite .b (.seq (snTry .r9) (.seq (.block [.alu .cmp .rdi (.imm 256)]) (.ite .b (snTry .r8) (.block []))))
        (.block [])) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (midL L ((s.gpr .r9).setWidth 32).toNat ((s.gpr .r8).setWidth 32).toNat).length ∧
        Stored s'.mem aP (midL L ((s.gpr .r9).setWidth 32).toNat ((s.gpr .r8).setWidth 32).toNat) ∧
        Frame [pR aP] s.mem s'.mem ∧ Keep [.rdi] s s' := by
  have hl : (s.gpr .rdi).toNat = L.length := by rw [hdi, ofNat64_toNat (by omega)]
  refine WP.ite (decide (L.length < 256)) (by rw [← hl]; exact hcf) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rw [midL, ifp hb]
    refine WP.seq (WP.mono (snTry_ok .r9 s hbp hdi hb hw hst) fun s2 ⟨hdi2, hst2, hf2, k2⟩ => ?_)
    refine WP.seq (WP.mono (cmpRdi_ok s2) fun s3 ⟨hc3, hm3, hg3, hrd3, hwr3⟩ => ?_)
    have h8 : s3.gpr .r8 = s.gpr .r8 := by rw [hg3, k2.gpr (by decide)]
    generalize hL1 : (if ((s.gpr .r9).setWidth 32).toNat < q then
      L ++ [ofNat ((s.gpr .r9).setWidth 32).toNat] else L) = L1 at hdi2 hst2
    have hL1len : L1.length ≤ 256 := by
      rw [← hL1]; split <;> (try simp only [List.length_append, List.length_singleton]) <;> omega
    have hl1 : (s3.gpr .rdi).toNat = L1.length := by rw [hg3, hdi2, ofNat64_toNat (by omega)]
    have hstep : stepD L ((s.gpr .r9).setWidth 32).toNat ((s.gpr .r8).setWidth 32).toNat =
        if L1.length < 256 then (if ((s.gpr .r8).setWidth 32).toNat < q then
          L1 ++ [ofNat ((s.gpr .r8).setWidth 32).toNat] else L1) else L1 := by
      simp only [stepD, hL1, n_eq]
      by_cases h1 : L1.length < 256
      · simp only [h1, ite_true, and_true]
      · simp only [h1, ite_false, and_false]
    rw [hstep]
    refine WP.ite (decide (L1.length < 256)) (by rw [← hl1]; show s3.cf = _; rw [hc3, hg3]) (fun hb' => ?_)
      (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      simp only [hb', ite_true]
      refine WP.mono (snTry_ok .r8 s3 (aP := aP) (by rw [hg3, k2.gpr (by decide), hbp]) (by rw [hg3, hdi2]) hb'
        (by rw [hwr3, k2.2.2]; exact hw) (by rw [hm3]; exact hst2)) fun s4 ⟨hdi4, hst4, hf4, k4⟩ => ?_
      rw [h8] at hdi4 hst4
      exact ⟨hdi4, hst4, hf2.trans (by rw [← hm3]; exact hf4),
        (k2.trans (⟨fun r _ => by rw [hg3], hrd3, hwr3⟩ : Keep [] s2 s3) |>.trans k4).mono (by simp)⟩
    · simp only [decide_eq_false_iff_not] at hb'
      simp only [hb', ite_false]
      refine WP.block_nil ⟨by rw [hg3, hdi2], by rw [hm3]; exact hst2, by rw [hm3]; exact hf2,
        (k2.trans (⟨fun r _ => by rw [hg3], hrd3, hwr3⟩ : Keep [] s2 s3)).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hb
    rw [midL, ifn hb]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, Keep.refl _ _⟩


theorem sw32_64 (x : BitVec 32) : (BitVec.setWidth 64 x).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, toNat_setWidth64, Nat.mod_eq_of_lt x.isLt]

theorem snStep_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.gpr .rsi = s.gpr .rsi + 3 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        s'.mem = s.mem) ∧ Keep [.rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- An iteration: what `sampleStepCap` does to the coefficients `L`. -/
theorem snBody_ok (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : pR aP ∈ s.wr)
    (hst : Stored s.mem aP L) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1) :
    WP isa snBody s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (sampleStepCap L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))).length ∧
      Stored s'.mem aP (sampleStepCap L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))) ∧
      Frame [pR aP] s.mem s'.mem ∧ s'.gpr .rsi = s.gpr .rsi + 3 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rax, .rdx, .r8, .r9, .rdi, .rdi, .rsi, .rcx] s s' := by
  have he : sampleStepCap L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2)) =
      midL L (d1w (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))).toNat
        (d2w (s.mem (s.gpr .rsi + BitVec.ofNat 64 1)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))).toNat := by
    rw [sampleStepCap, midL, sampleStep_eq, d1w_toNat, d2w_toNat]
    by_cases h : L.length < 256
    · rw [ifn (show ¬ L.length = n by rw [n_eq]; omega), ifp h]
    · rw [ifp (show L.length = n by rw [n_eq]; omega), ifn h]
  rw [he]
  refine WP.seq (WP.mono (snLoad_ok s h0 h1 h2) fun s1 ⟨⟨h9, h8, hcf, hm1, hdi1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (snMid_ok s1 (aP := aP) (L := L) (by rw [k1.gpr (by decide), hbp]) (by rw [hdi1, hdi]) hL
    (by rw [k1.2.2]; exact hw) (by rw [hm1]; exact hst) (by rw [hcf, hdi1])) fun s3 ⟨hdi3, hst3, hf3, k3⟩ => ?_)
  rw [h9, h8, sw32_64, sw32_64] at hdi3 hst3
  refine WP.mono (snStep_ok s3) fun s4 ⟨⟨hsi4, hcx4, hz4, hm4⟩, k4⟩ => ?_
  have hsi3 : s3.gpr .rsi = s.gpr .rsi := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  have hcx3 : s3.gpr .rcx = s.gpr .rcx := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  exact ⟨by rw [k4.gpr (by decide), hdi3], by rw [hm4]; exact hst3, by rw [hm4, ← hm1]; exact hf3,
    by rw [hsi4, hsi3], by rw [hcx4, hcx3], by rw [hz4, hcx3], ((k1.trans k3).trans k4).mono (by simp)⟩

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

end VG.Proof.MlKem.X86_64
