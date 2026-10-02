import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes

/-!
# ML-DSA on x86-64: the loop of `vg_mldsa_rej_ntt_poly`

An iteration of the loop does what `rnStep` does to the coefficients sampled
so far, stored at `a` (`Stored`) and counted in `rdi` (`rnBody_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)

theorem bw32 (c : Byte) : (BitVec.setWidth 32 (BitVec.setWidth 64 c)).toNat = c.toNat := by
  rw [BitVec.toNat_setWidth, toNat_setWidth64_8, Nat.mod_eq_of_lt (by have := c.isLt; omega)]

/-- The value of the bytes `b₀, b₁, b₂`, as the code computes it. -/
def rnw (b₀ b₁ b₂ : Byte) : BitVec 32 :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 b₂) &&& 127).rotateRight 16 +
    (BitVec.setWidth 32 (BitVec.setWidth 64 b₁)).rotateRight 24 + BitVec.setWidth 32 (BitVec.setWidth 64 b₀)

theorem rnw_toNat (b₀ b₁ b₂ : Byte) : (rnw b₀ b₁ b₂).toNat = rnZ b₀ b₁ b₂ := by
  have e2 : (BitVec.setWidth 32 (BitVec.setWidth 64 b₂) &&& 127).toNat = b₂.toNat % 128 := by
    rw [BitVec.toNat_and, bw32, show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have h0 := b₀.isLt
  have h1 := b₁.isLt
  have h2 := Nat.mod_lt b₂.toNat (show 128 > 0 by decide)
  have r2 := rotr_toNat (BitVec.setWidth 32 (BitVec.setWidth 64 b₂) &&& 127) (r := 16) (by decide)
    (by rw [e2]; omega)
  have r1 := rotr_toNat (BitVec.setWidth 32 (BitVec.setWidth 64 b₁)) (r := 24) (by decide) (by rw [bw32]; omega)
  rw [e2] at r2
  rw [bw32] at r1
  rw [rnw, BitVec.toNat_add, BitVec.toNat_add, r2, r1, bw32, rnZ]
  rw [show 32 - 16 = 16 from rfl, show 32 - 24 = 8 from rfl]
  omega

theorem rnLoad_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1) :
    WP isa (.block rnLoad) s fun s' =>
      (s'.gpr .r8 = BitVec.setWidth 64 (rnw (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
          (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))) ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi) ∧
      Keep [.rax, .rdx, .r8, .rdi] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold rnLoad
  xrun [h0, h1, h2, sx256, rnw, show (256 : BitVec 64).toNat = 256 from rfl]

/-! ## A try -/

theorem rnCmp_ok (s : State) :
    WP isa (.block [.alu32 .cmp .r8 (.imm qImm)]) s fun s' =>
      s'.cf = some (decide (((s.gpr .r8).setWidth 32).toNat < q)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun [show qImm.toNat = 8380417 from rfl]

theorem storeJ_ok (r : Reg) (s : State) {a : Addr} (ha : s.ea aJ = a) (hw : InRegions s.wr a 4) :
    WP isa (.block [.store32 aJ r, .alu .add .rdi (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW a ((s.gpr r).setWidth 32) ∧ s'.gpr .rdi = s.gpr .rdi + 1) ∧ Keep [.rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [ha, hw]

/-- Each coefficient of the polynomial at `aP` lies in one of the writable
regions `wr`. -/
def CoeffsWr (wr : List Region) (aP : Addr) : Prop := ∀ i < 256, InRegions wr (coeffAddr aP i) 4

theorem CoeffsWr.of_mem {wr : List Region} {aP : Addr} (h : pR aP ∈ wr) : CoeffsWr wr aP :=
  fun _ hi => ⟨_, h, coeff_contains _ hi⟩

/-- Storing the word `v` (less than `q`) as the next coefficient. -/
theorem store_next {s : State} {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length < 256) (hw : CoeffsWr s.wr aP)
    (hst : Stored s.mem aP L) (r : Reg) {v : BitVec 32} (hv : (s.gpr r).setWidth 32 = v) (hq : v.toNat < q) :
    WP isa (.block [.store32 aJ r, .alu .add .rdi (.imm 1)]) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (L ++ [Fin.ofNat q v.toNat]).length ∧
        Stored s'.mem aP (L ++ [Fin.ofNat q v.toNat]) ∧ Frame [pR aP] s.mem s'.mem ∧ Keep [.rdi] s s' := by
  refine WP.mono (storeJ_ok r s (ea_aJ s hbp hdi) (hw _ hL)) fun s' ⟨⟨hm, hdi'⟩, k⟩ => ?_
  have hz : zw (Fin.ofNat q v.toNat) = v := by
    apply BitVec.eq_of_toNat_eq
    rw [zw_toNat, Fin.val_ofNat, Nat.mod_eq_of_lt hq]
  refine ⟨by rw [hdi', hdi, List.length_append, List.length_singleton]; exact ofNat64_succ (by omega), ?_,
    by rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hL), k⟩
  have := stored_snoc hst hL (Fin.ofNat q v.toNat)
  rw [hz] at this
  rw [hm, hv]; exact this

/-- The hypotheses of a try. -/
structure TryPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length < 256
  wr : CoeffsWr s.wr aP
  st : Stored s.mem aP L

/-- The coefficients after a try of the value `v`. -/
def rnTryL (L : List Zq) (v : Nat) : List Zq := if v < q then L ++ [Fin.ofNat q v] else L

theorem rnTry_ok (s : State) {aP : Addr} {L : List Zq} (h : TryPre s aP L) :
    WP isa rnTry s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (rnTryL L ((s.gpr .r8).setWidth 32).toNat).length ∧
      Stored s'.mem aP (rnTryL L ((s.gpr .r8).setWidth 32).toNat) ∧ Frame [pR aP] s.mem s'.mem ∧
      Keep [.rdi] s s' := by
  refine WP.seq (WP.mono (rnCmp_ok s) fun s1 ⟨hc, hm, hg, hrd, hwr⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by rw [hg], hrd, hwr⟩
  refine WP.ite (decide (((s.gpr .r8).setWidth 32).toNat < q)) hc (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rw [rnTryL, ifT hb]
    refine WP.mono (store_next (s := s1) (by rw [hg, h.rbp]) (by rw [hg, h.rdi]) h.len (by rw [hwr]; exact h.wr)
      (by rw [hm]; exact h.st) .r8 (by rw [hg]) hb) fun s2 ⟨hdi, hst, hf, k2⟩ =>
      ⟨hdi, hst, by rw [← hm]; exact hf, (k1.trans k2).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hb
    rw [rnTryL, ifF hb]
    exact WP.block_nil ⟨by rw [hg, h.rdi], by rw [hm]; exact h.st, by rw [hm]; exact Frame.refl _ _,
      k1.mono (by simp)⟩

/-! ## An iteration -/

/-- The coefficients after an iteration, from the value `v`. -/
def rnMid (L : List Zq) (v : Nat) : List Zq := if L.length < 256 then rnTryL L v else L

theorem rnStep_eq (L : List Zq) (b₀ b₁ b₂ : Byte) : rnStep L b₀ b₁ b₂ = rnMid L (rnw b₀ b₁ b₂).toNat := by
  rw [rnStep, rnMid, rnw_toNat]; rfl

/-- The try, if `j < 256`. -/
theorem rnMid_ok (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : CoeffsWr s.wr aP)
    (hst : Stored s.mem aP L) (hcf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))) :
    WP isa (.ite .b rnTry (.block [])) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (rnMid L ((s.gpr .r8).setWidth 32).toNat).length ∧
        Stored s'.mem aP (rnMid L ((s.gpr .r8).setWidth 32).toNat) ∧ Frame [pR aP] s.mem s'.mem ∧
        Keep [.rdi] s s' := by
  have hl : (s.gpr .rdi).toNat = L.length := by rw [hdi, ofNat64_toNat (by omega)]
  refine WP.ite (decide (L.length < 256)) (by rw [← hl]; exact hcf) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rw [rnMid, ifT hb]
    exact rnTry_ok s ⟨hbp, hdi, hb, hw, hst⟩
  · simp only [decide_eq_false_iff_not] at hb
    rw [rnMid, ifF hb]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, Keep.refl _ _⟩

theorem sw32_64 (x : BitVec 32) : (BitVec.setWidth 64 x).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, toNat_setWidth64, Nat.mod_eq_of_lt x.isLt]

theorem sx3 : BitVec.signExtend 64 (3 : BitVec 32) = BitVec.ofNat 64 3 := by decide

/-- An iteration: what `rnStep` does to the coefficients `L`. -/
theorem rnBody_ok (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : CoeffsWr s.wr aP)
    (hst : Stored s.mem aP L) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1) :
    WP isa rnBody s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (rnStep L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))).length ∧
      Stored s'.mem aP (rnStep L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))) ∧
      Frame [pR aP] s.mem s'.mem ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 3 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx] s s' := by
  rw [rnStep_eq]
  refine WP.seq (WP.mono (rnLoad_ok s h0 h1 h2) fun s1 ⟨⟨h8, hcf, hm1, hdi1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (rnMid_ok s1 (aP := aP) (L := L) (by rw [k1.gpr (by decide), hbp]) (by rw [hdi1, hdi]) hL
    (by rw [k1.2.2]; exact hw) (by rw [hm1]; exact hst) (by rw [hcf, hdi1])) fun s3 ⟨hdi3, hst3, hf3, k3⟩ => ?_)
  rw [h8, sw32_64] at hdi3 hst3
  refine WP.mono (step_ok s3 3) fun s4 ⟨⟨hsi4, hcx4, hz4, hm4⟩, k4⟩ => ?_
  have hsi3 : s3.gpr .rsi = s.gpr .rsi := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  have hcx3 : s3.gpr .rcx = s.gpr .rcx := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  exact ⟨by rw [k4.gpr (by decide), hdi3], by rw [hm4]; exact hst3, by rw [hm4, ← hm1]; exact hf3,
    by rw [hsi4, hsi3, sx3], by rw [hcx4, hcx3], by rw [hz4, hcx3], ((k1.trans k3).trans k4).mono (by simp)⟩

end VG.Proof.MlDsa.X86_64.Sample
